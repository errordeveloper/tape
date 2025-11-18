package oci

import (
	"archive/tar"
	"bytes"
	"compress/gzip"
	"context"
	"encoding/hex"
	"fmt"
	"io"
	"maps"
	"os"
	"path/filepath"
	"strings"
	"time"

	"golang.org/x/mod/semver"

	ociclient "github.com/fluxcd/pkg/oci"
	"github.com/go-git/go-git/v5/utils/ioutil"
	"github.com/google/go-containerregistry/pkg/compression"
	"github.com/google/go-containerregistry/pkg/crane"
	"github.com/google/go-containerregistry/pkg/name"
	"github.com/google/go-containerregistry/pkg/v1/empty"
	"github.com/google/go-containerregistry/pkg/v1/mutate"
	"github.com/google/go-containerregistry/pkg/v1/remote"
	"github.com/google/go-containerregistry/pkg/v1/tarball"
	typesv1 "github.com/google/go-containerregistry/pkg/v1/types"

	"github.com/errordeveloper/tape/attest/manifest"
	attestTypes "github.com/errordeveloper/tape/attest/types"
	"github.com/errordeveloper/tape/attest/vcs/git"
	manifestTypes "github.com/errordeveloper/tape/manifest/types"
)

const (
	mediaTypePrefix            = "application/vnd.docker.tape"
	ConfigMediaType  MediaType = mediaTypePrefix + ".config.v1alpha1+json"
	ContentMediaType MediaType = mediaTypePrefix + ".content.v1alpha1.tar+gzip"
	AttestMediaType  MediaType = mediaTypePrefix + ".attest.v1alpha1.jsonl+gzip"

	ContentInterpreterAnnotation   = mediaTypePrefix + ".content-interpreter.v1alpha1"
	ContentInterpreterKubectlApply = mediaTypePrefix + ".kubectl-apply.v1alpha1.tar+gzip"

	AttestationsSummaryAnnotation = mediaTypePrefix + ".attestations-summary.v1alpha1"

	// TODO: content interpreter invocation with an image

	regularFileMode = 0o640

	OCIManifestSchema1 = typesv1.OCIManifestSchema1
)

type ArtefactInfo struct {
	io.ReadCloser

	MediaType   MediaType
	Annotations map[string]string
	Digest      string
}

type PackageRefs struct {
	Digest  string
	Primary string
	Short   string
	SemVer  []string
}

func (c *Client) Fetch(ctx context.Context, ref string, mediaTypes ...MediaType) ([]*ArtefactInfo, error) {
	imageIndex, indexManifest, image, err := c.GetIndexOrImage(ctx, ref)
	if err != nil {
		return nil, err
	}
	artefactInfo, _, err := c.FetchFromIndexOrImage(ctx, imageIndex, indexManifest, image, mediaTypes...)
	return artefactInfo, err
}

func (c *Client) FetchFromIndexOrImage(ctx context.Context, imageIndex ImageIndex, indexManifest *IndexManifest, image Image, mediaTypes ...MediaType) ([]*ArtefactInfo, map[Hash]*Manifest, error) {
	numMediaTypes := len(mediaTypes)

	selector := make(map[MediaType]struct{}, numMediaTypes)
	for _, mediaType := range mediaTypes {
		selector[mediaType] = struct{}{}
	}

	skip := func(mediaType MediaType) bool {
		if numMediaTypes > 0 {
			if _, ok := selector[mediaType]; !ok {
				return true
			}
		}
		return false
	}

	artefacts := []*ArtefactInfo{}
	manifests := map[Hash]*Manifest{}

	if indexManifest == nil {
		manifest, err := image.Manifest()
		if err != nil {
			return nil, nil, fmt.Errorf("failed to get manifest: %w", err)
		}

		imageDigest, err := image.Digest()
		if err != nil {
			return nil, nil, err
		}
		manifests[imageDigest] = manifest

		for j := range manifest.Layers {
			layerDescriptor := manifest.Layers[j]

			if skip(layerDescriptor.MediaType) {
				continue
			}

			info, err := newArtifcatInfoFromLayerDescriptor(image, layerDescriptor, manifest.Annotations)
			if err != nil {
				return nil, nil, err
			}
			artefacts = append(artefacts, info)
		}
		return artefacts, manifests, nil
	}

	for i := range indexManifest.Manifests {
		manifestDescriptor := indexManifest.Manifests[i]

		if skip(MediaType(manifestDescriptor.ArtifactType)) {
			continue
		}

		image, manifest, err := c.getImage(ctx, imageIndex, manifestDescriptor.Digest)
		if err != nil {
			return nil, nil, err
		}

		manifests[manifestDescriptor.Digest] = manifest

		for j := range manifest.Layers {
			layerDescriptor := manifest.Layers[j]

			if layerDescriptor.MediaType != MediaType(manifestDescriptor.ArtifactType) {
				return nil, nil, fmt.Errorf("media type mismatch between manifest and layer: %s != %s", manifestDescriptor.MediaType, layerDescriptor.MediaType)
			}

			info, err := newArtifcatInfoFromLayerDescriptor(image, layerDescriptor, manifest.Annotations)
			if err != nil {
				return nil, nil, err
			}
			artefacts = append(artefacts, info)
		}
	}

	return artefacts, manifests, nil
}

func (c *Client) GetSingleArtefact(ctx context.Context, ref string) (*ArtefactInfo, error) {
	image, layers, annotations, err := c.getFlatArtefactLayers(ctx, ref)
	if err != nil {
		return nil, err
	}
	if len(layers) != 1 {
		return nil, fmt.Errorf("multiple layers found in image %q", ref)
	}
	return newArtifcatInfoFromLayerDescriptor(image, layers[0], annotations)
}

func newArtifcatInfoFromLayerDescriptor(image Image, layerDecriptor Descriptor, annotations map[string]string) (*ArtefactInfo, error) {
	layer, err := image.LayerByDigest(layerDecriptor.Digest)
	if err != nil {
		return nil, fmt.Errorf("fetching artefact image failed: %w", err)
	}

	blob, err := layer.Compressed()
	if err != nil {
		return nil, fmt.Errorf("extracting compressed aretefact image failed: %w", err)
	}
	info := &ArtefactInfo{
		ReadCloser:  blob,
		MediaType:   layerDecriptor.MediaType,
		Annotations: annotations,
		Digest:      layerDecriptor.Digest.String(),
	}
	return info, nil
}

func (c *Client) getFlatArtefactLayers(ctx context.Context, ref string) (Image, []Descriptor, map[string]string, error) {
	imageIndex, indexManifest, image, err := c.GetIndexOrImage(ctx, ref)
	if err != nil {
		return nil, nil, nil, err
	}

	var manifest *Manifest

	if indexManifest != nil {
		if len(indexManifest.Manifests) != 1 {
			return nil, nil, nil, fmt.Errorf("multiple manifests found in image %q", ref)
		}

		image, manifest, err = c.getImage(ctx, imageIndex, indexManifest.Manifests[0].Digest)
		if err != nil {
			return nil, nil, nil, err
		}
	} else {
		manifest, err = image.Manifest()
		if err != nil {
			return nil, nil, nil, fmt.Errorf("failed to get manifest for %q: %w", ref, err)
		}
	}

	if len(manifest.Layers) < 1 {
		return nil, nil, nil, fmt.Errorf("no layers found in image %q", ref)
	}

	return image, manifest.Layers, manifest.Annotations, nil
}

func (c *Client) getImage(ctx context.Context, imageIndex ImageIndex, digest Hash) (Image, *Manifest, error) {
	image, err := imageIndex.Image(digest)
	if err != nil {
		return nil, nil, err
	}
	manifest, err := image.Manifest()
	if err != nil {
		return nil, nil, fmt.Errorf("failed to get manifest for %q: %w", digest.String(), err)
	}
	return image, manifest, nil
}

// based on https://github.com/fluxcd/pkg/blob/2a323d771e17af02dee2ccbbb9b445b78ab048e5/oci/client/push.go
func (c *Client) PushArtefact(ctx context.Context, destinationRef, sourceDir string, timestamp *time.Time, sourceAttestations ...attestTypes.Statement) (*PackageRefs, error) {
	tmpDir, err := os.MkdirTemp("", "bpt-oci-artefact-*")
	if err != nil {
		return nil, err
	}
	defer os.RemoveAll(tmpDir)

	tmpFile := filepath.Join(tmpDir, "artefact.tgz")

	outputFile, err := os.OpenFile(tmpFile, os.O_RDWR|os.O_CREATE|os.O_EXCL, regularFileMode)
	if err != nil {
		return nil, err
	}
	defer outputFile.Close()

	c.hash.Reset()

	output := io.MultiWriter(outputFile, c.hash)

	if err := c.BuildArtefact(tmpFile, sourceDir, output); err != nil {
		return nil, err
	}

	attestLayer, err := c.BuildAttestations(sourceAttestations)
	if err != nil {
		return nil, fmt.Errorf("failed to serialise attestations: %w", err)
	}

	craneOpts := crane.GetOptions(c.GetOptions()...)
	repo, err := name.NewRepository(destinationRef, craneOpts.Name...)
	if err != nil {
		return nil, fmt.Errorf("invalid URL: %w", err)
	}
	hash := hex.EncodeToString(c.hash.Sum(nil))
	tag := repo.Tag(manifestTypes.ConfigImageTagPrefix + hash)
	shortTag := tag.Context().Tag(manifestTypes.ConfigImageTagPrefix + hash[:7])
	semVerTags := SemVerTagsFromAttestations(ctx, tag, sourceAttestations...)

	if timestamp == nil {
		timestamp = new(time.Time)
		*timestamp = time.Now().UTC()
	}

	indexAnnotations := map[string]string{
		ociclient.CreatedAnnotation: timestamp.Format(time.RFC3339),
	}

	index := mutate.Annotations(
		empty.Index,
		indexAnnotations,
	).(ImageIndex)

	configAnnotations := maps.Clone(indexAnnotations)

	configAnnotations[ContentInterpreterAnnotation] = ContentInterpreterKubectlApply

	config := mutate.Annotations(
		mutate.ConfigMediaType(
			mutate.MediaType(empty.Image, OCIManifestSchema1),
			ContentMediaType,
		),
		configAnnotations,
	).(Image)

	// There is an option to use LayerFromReader which will avoid writing any files to disk,
	// albeit it might impact memory usage and there is no strict security requirement, and
	// manifests do get written out already anyway.
	configLayer, err := tarball.LayerFromFile(tmpFile,
		tarball.WithMediaType(ContentMediaType),
		tarball.WithCompression(compression.GZip),
		tarball.WithCompressedCaching,
	)
	if err != nil {
		return nil, fmt.Errorf("creating artefact content layer failed: %w", err)
	}

	config, err = mutate.Append(config, mutate.Addendum{Layer: configLayer})
	if err != nil {
		return nil, fmt.Errorf("appeding content to artifact failed: %w", err)
	}

	index = mutate.AppendManifests(index,
		mutate.IndexAddendum{
			Descriptor: makeDescriptorWithPlatform(),
			Add:        config,
		},
	)

	if attestLayer != nil {
		attestAnnotations := maps.Clone(indexAnnotations)

		summary, err := (attestTypes.Statements)(sourceAttestations).MarshalSummaryAnnotation()
		if err != nil {
			return nil, err
		}
		attestAnnotations[AttestationsSummaryAnnotation] = summary

		attest := mutate.Annotations(
			mutate.ConfigMediaType(
				mutate.MediaType(empty.Image, OCIManifestSchema1),
				AttestMediaType,
			),
			attestAnnotations,
		).(Image)

		attest, err = mutate.Append(attest, mutate.Addendum{Layer: attestLayer})
		if err != nil {
			return nil, fmt.Errorf("appeding attestations to artifact failed: %w", err)
		}

		index = mutate.AppendManifests(index,
			mutate.IndexAddendum{
				Descriptor: makeDescriptorWithPlatform(),
				Add:        attest,
			},
		)
	}

	digest, err := index.Digest()
	if err != nil {
		return nil, fmt.Errorf("parsing index digest failed: %w", err)
	}

	if err := remote.WriteIndex(tag, index, c.remoteWithContext(ctx)...); err != nil {
		return nil, fmt.Errorf("pushing index failed: %w", err)
	}

	refs := &PackageRefs{
		Digest:  digest.String(),
		Primary: tag.String(),
		Short:   shortTag.String(),
		SemVer:  make([]string, len(semVerTags)),
	}

	for i, tagAlias := range append(semVerTags, shortTag) {
		if err := remote.Tag(tagAlias, index, c.remoteWithContext(ctx)...); err != nil {
			return nil, fmt.Errorf("adding alias tagging failed: %w", err)
		}
		if i < len(semVerTags) {
			refs.SemVer[i] = tagAlias.String() + "@" + digest.String()
		}
	}
	return refs, nil
}

func (p *PackageRefs) String() string { return p.Short + "@" + p.Digest }

func SemVerTagsFromAttestations(ctx context.Context, tag name.Tag, sourceAttestations ...attestTypes.Statement) []name.Tag {
	statements := attestTypes.FilterByPredicateType(manifest.ManifestDirPredicateType, sourceAttestations)
	if len(statements) != 1 {
		return []name.Tag{}
	}

	entries := manifest.MakeDirContentsStatementFrom(statements[0]).GetUnderlyingPredicate().VCSEntries
	if len(entries.EntryGroups) != 1 && len(entries.Providers) != 1 ||
		entries.Providers[0] != git.ProviderName {
		return []name.Tag{}
	}
	if len(entries.EntryGroups[0]) == 0 {
		return []name.Tag{}
	}

	// TODO: try to use generics for this?
	groupSummary, ok := entries.EntryGroups[0][0].Full().(*git.Summary)
	if !ok {
		return []name.Tag{}
	}
	ref := groupSummary.Git.Reference
	numTags := len(ref.Tags)
	if numTags == 0 {
		return []name.Tag{}
	}
	tags := newTagtagSet(numTags)
	scopedTags := newTagtagSet(numTags)
	for i := range ref.Tags {
		t := ref.Tags[i].Name
		// this is accounts only for a simple case where tape is pointed at a dir
		// and a tags have prefix that matches it exactly, it won't work for cases
		// where tape is pointed at a subdir a parent of which has a scoped tag
		if strings.HasPrefix(t, groupSummary.Path+"/") {
			scopedTags.add(strings.TrimPrefix(t, groupSummary.Path+"/"), tag)
			continue
		}
		tags.add(t, tag)
	}
	if len(scopedTags.list) > 0 {
		return scopedTags.list
	}
	return tags.list
}

type tagSet struct {
	set  map[string]struct{}
	list []name.Tag
}

func newTagtagSet(c int) *tagSet {
	return &tagSet{
		set:  make(map[string]struct{}, c),
		list: make([]name.Tag, 0, c),
	}
}

func (s *tagSet) add(t string, image name.Tag) {
	if !strings.HasPrefix(t, "v") {
		t = "v" + t
	}
	if _, ok := s.set[t]; !ok {
		if semver.IsValid(t) {
			s.list = append(s.list, image.Context().Tag(t))
			s.set[t] = struct{}{}
		}
	}
}

func makeDescriptorWithPlatform() Descriptor {
	return Descriptor{
		Platform: &Platform{
			Architecture: "unknown",
			OS:           "unknown",
		},
	}
}

// based on https://github.com/fluxcd/pkg/blob/2a323d771e17af02dee2ccbbb9b445b78ab048e5/oci/client/build.go
func (c *Client) BuildArtefact(artifactPath,
	sourceDir string, output io.Writer) error {
	absDir, err := filepath.Abs(sourceDir)
	if err != nil {
		return err
	}

	dirStat, err := os.Stat(absDir)
	if os.IsNotExist(err) {
		return fmt.Errorf("invalid source dir path: %s", absDir)
	}

	gw := gzip.NewWriter(output)
	tw := tar.NewWriter(gw)
	if err := filepath.WalkDir(absDir, func(p string, di os.DirEntry, prevErr error) (err error) {
		if prevErr != nil {
			return prevErr
		}

		// Ignore anything that is not a file or directories e.g. symlinks
		ft := di.Type()
		if !(ft.IsRegular() || ft.IsDir()) {
			return nil
		}

		fi, err := di.Info()
		if err != nil {
			return err
		}

		header, err := tar.FileInfoHeader(fi, p)
		if err != nil {
			return err
		}
		if dirStat.IsDir() {
			// The name needs to be modified to maintain directory structure
			// as tar.FileInfoHeader only has access to the base name of the file.
			// Ref: https://golang.org/src/archive/tar/common.go?#L6264
			//
			// we only want to do this if a directory was passed in
			relFilePath, err := filepath.Rel(absDir, p)
			if err != nil {
				return err
			}
			// Normalize file path so it works on windows
			header.Name = filepath.ToSlash(relFilePath)
		}

		// Remove any environment specific data.
		header.Gid = 0
		header.Uid = 0
		header.Uname = ""
		header.Gname = ""
		header.ModTime = time.Time{}
		header.AccessTime = time.Time{}
		header.ChangeTime = time.Time{}

		if err := tw.WriteHeader(header); err != nil {
			return err
		}

		if !ft.IsRegular() {
			return nil
		}

		file, err := os.Open(p)
		if err != nil {
			return err
		}
		defer ioutil.CheckClose(file, &err)

		if _, err := io.Copy(tw, file); err != nil {
			return err
		}
		return nil
	}); err != nil {
		_ = tw.Close()
		_ = gw.Close()
		return err
	}

	if err := tw.Close(); err != nil {
		_ = gw.Close()
		return err
	}
	if err := gw.Close(); err != nil {
		return err
	}

	return nil
}

func (c *Client) BuildAttestations(statements []attestTypes.Statement) (Layer, error) {
	if len(statements) == 0 {
		return nil, nil
	}
	output := bytes.NewBuffer(nil)
	gw := gzip.NewWriter(output)

	if err := attestTypes.Statements(statements).Encode(gw); err != nil {
		return nil, err
	}

	if err := gw.Close(); err != nil {
		return nil, err
	}

	layer, err := tarball.LayerFromOpener(
		func() (io.ReadCloser, error) {
			// this doesn't copy data, it should re-use same undelying slice
			return io.NopCloser(bytes.NewReader(output.Bytes())), nil
		},
		tarball.WithMediaType(AttestMediaType),
		tarball.WithCompression(compression.GZip),
		tarball.WithCompressedCaching,
	)
	if err != nil {
		return nil, fmt.Errorf("creating attestations layer failed: %w", err)
	}

	return layer, nil
}
