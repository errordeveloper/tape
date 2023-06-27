package testdata

import (
	"crypto/sha256"
	"encoding/hex"
	"io"
	"os"
	"path/filepath"
	"testing"

	"github.com/docker/labs-brown-tape/manifest/types"
)

type TestCase struct {
	Description string
	Manifests   []string
	Expected    []types.Image
}

type TestCases []TestCase

func (tcs TestCases) Run(t *testing.T, doTest func(tc TestCase) func(t *testing.T)) {
	t.Helper()
	for i := range tcs {
		t.Run(tcs[i].Description, doTest(tcs[i]))
	}
}

func (tcs TestCases) RelocateFiles(t *testing.T) {
	tempDir := t.TempDir()
	hash := sha256.New()
	for i := range tcs {
		translator := map[string]string{}
		for m, manifest := range tcs[i].Manifests {
			hash.Reset()
			hash.Write([]byte(manifest))
			newName := hex.EncodeToString(hash.Sum(nil)) + filepath.Ext(manifest)
			newPath := filepath.Join(tempDir, newName)

			translator[manifest] = newPath

			newFile, err := os.Create(newPath)
			if err != nil {
				t.Fatal(err)
			}

			oldFile, err := os.Open(manifest)
			if err != nil {
				t.Fatal(err)
			}

			_, err = io.Copy(newFile, oldFile)
			if err != nil {
				t.Fatal(err)
			}

			tcs[i].Manifests[m] = newPath
		}
		for j := range tcs[i].Expected {
			tcs[i].Expected[j].Manifest = translator[tcs[i].Expected[j].Manifest]
		}

	}
}

func BasicJSONCases() TestCases {
	return []TestCase{{
		Description: "basic",
		Manifests: []string{
			"../testdata/basic/list.json",
			"../testdata/basic/deployment.json",
		},
		Expected: []types.Image{
			{
				Manifest:       "../testdata/basic/list.json",
				ManifestDigest: "577caeee80cfa690caf25bcdd4b1919b99d2860eb351c48e81b46b9e4b52aea5",
				NodePath:       []string{"spec", "containers", "image"},
				OriginalRef:    "nginx",
				OriginalName:   "nginx",
			},
			{
				Manifest:       "../testdata/basic/list.json",
				ManifestDigest: "577caeee80cfa690caf25bcdd4b1919b99d2860eb351c48e81b46b9e4b52aea5",
				NodePath:       []string{"spec", "template", "spec", "containers", "image"},
				OriginalRef:    "redis",
				OriginalName:   "redis",
			},
			{
				Manifest:       "../testdata/basic/list.json",
				ManifestDigest: "577caeee80cfa690caf25bcdd4b1919b99d2860eb351c48e81b46b9e4b52aea5",
				NodePath:       []string{"items", "spec", "containers", "image"},
				OriginalRef:    "redis",
				OriginalName:   "redis",
			},
			{
				Manifest:       "../testdata/basic/deployment.json",
				ManifestDigest: "8d85ce5a5de4085bb841cee0402022fcd03f86606a67d572e62012ce4420668c",
				NodePath:       []string{"spec", "template", "spec", "containers", "image"},
				OriginalRef:    "nginx:1.16.1",
				OriginalName:   "nginx",
				OriginalTag:    "1.16.1",
			},
		},
	}}
}

var baseYAMLCases = []TestCase{
	{
		Description: "contour",
		Manifests: []string{
			"../testdata/contour/00-common.yaml",
			"../testdata/contour/00-crds.yaml",
			"../testdata/contour/01-contour-config.yaml",
			"../testdata/contour/01-crds.yaml",
			"../testdata/contour/02-job-certgen.yaml",
			"../testdata/contour/02-rbac.yaml",
			"../testdata/contour/02-role-contour.yaml",
			"../testdata/contour/02-service-contour.yaml",
			"../testdata/contour/02-service-envoy.yaml",
			"../testdata/contour/03-contour.yaml",
			"../testdata/contour/03-envoy.yaml",
			"../testdata/contour/04-gatewayclass.yaml",
			"../testdata/contour/kustomization.yaml",
		},
		Expected: []types.Image{
			{
				Manifest:       "../testdata/contour/02-job-certgen.yaml",
				ManifestDigest: "ba03dc02890e0ca080f12f03fd06a1d4f6b76ff75be0346ee27c9aa73c6d1d31",
				NodePath:       []string{"spec", "template", "spec", "containers", "image"},
				OriginalRef:    "ghcr.io/projectcontour/contour:v1.24.1",
				OriginalName:   "ghcr.io/projectcontour/contour",
				OriginalTag:    "v1.24.1",
			},
			{
				Manifest:       "../testdata/contour/03-contour.yaml",
				ManifestDigest: "a9de49647bab938407cb76c29f6b9465690bedb0b99a10736136f982d349d928",
				NodePath:       []string{"spec", "template", "spec", "containers", "image"},
				OriginalRef:    "ghcr.io/projectcontour/contour:v1.24.1",
				OriginalName:   "ghcr.io/projectcontour/contour",
				OriginalTag:    "v1.24.1",
			},
			{
				Manifest:       "../testdata/contour/03-envoy.yaml",
				ManifestDigest: "e83cd3f98ddbbd91374511c8ce1e437d938ffc8ea8d50bc6d4ccdbf224e53ed4",
				NodePath:       []string{"spec", "template", "spec", "containers", "image"},
				OriginalRef:    "ghcr.io/projectcontour/contour:v1.24.1",
				OriginalName:   "ghcr.io/projectcontour/contour",
				OriginalTag:    "v1.24.1",
			},
			{
				Manifest:       "../testdata/contour/03-envoy.yaml",
				ManifestDigest: "e83cd3f98ddbbd91374511c8ce1e437d938ffc8ea8d50bc6d4ccdbf224e53ed4",
				NodePath:       []string{"spec", "template", "spec", "containers", "image"},
				OriginalRef:    "docker.io/envoyproxy/envoy:v1.25.1",
				OriginalName:   "docker.io/envoyproxy/envoy",
				OriginalTag:    "v1.25.1",
			},
			{
				Manifest:       "../testdata/contour/03-envoy.yaml",
				ManifestDigest: "e83cd3f98ddbbd91374511c8ce1e437d938ffc8ea8d50bc6d4ccdbf224e53ed4",
				NodePath:       []string{"spec", "template", "spec", "initContainers", "image"},
				OriginalRef:    "ghcr.io/projectcontour/contour:v1.24.1",
				OriginalName:   "ghcr.io/projectcontour/contour",
				OriginalTag:    "v1.24.1",
			},
		},
	},
	{
		Description: "flux",
		Manifests: []string{
			"../testdata/flux/flux.yaml",
			"../testdata/flux/kustomization.yaml",
		},
		Expected: []types.Image{
			{
				Manifest:       "../testdata/flux/flux.yaml",
				ManifestDigest: "39ad63101dbb2ead069ca6185bd44f99f52b8513682d6002109c9b0db23f73b5",
				NodePath:       []string{"spec", "template", "spec", "containers", "image"},
				OriginalRef:    "ghcr.io/fluxcd/kustomize-controller:v0.30.0",
				OriginalName:   "ghcr.io/fluxcd/kustomize-controller",
				OriginalTag:    "v0.30.0",
			},
			{
				Manifest:       "../testdata/flux/flux.yaml",
				ManifestDigest: "39ad63101dbb2ead069ca6185bd44f99f52b8513682d6002109c9b0db23f73b5",
				NodePath:       []string{"spec", "template", "spec", "containers", "image"},
				OriginalRef:    "ghcr.io/fluxcd/source-controller:v0.31.0",
				OriginalName:   "ghcr.io/fluxcd/source-controller",
				OriginalTag:    "v0.31.0",
			},
		},
	},
	{
		Description: "tekton",
		Manifests: []string{
			"../testdata/tekton/base/feature-flags.yaml",
			"../testdata/tekton/base/kustomization.yaml",
			"../testdata/tekton/base/tekton-base.yaml",
			"../testdata/tekton/webhooks/kustomization.yaml",
			"../testdata/tekton/webhooks/tekton-mutating-webhooks.yaml",
			"../testdata/tekton/webhooks/tekton-validating-webhooks.yaml",
		},
		Expected: []types.Image{
			{
				Manifest:       "../testdata/tekton/base/tekton-base.yaml",
				ManifestDigest: "c2cbc6d7a3c30f99e2e504d5758d8e0ce140a8f444c4d944d85c3f29800bf8c5",
				NodePath:       []string{"spec", "template", "spec", "containers", "image"},
				OriginalRef:    "gcr.io/tekton-releases/github.com/tektoncd/pipeline/cmd/controller:v0.40.2@sha256:dc7bc7d6607466b502d8dc22ba0598461d7477f608ab68aaff1ff4dedaa04f81",
				OriginalName:   "gcr.io/tekton-releases/github.com/tektoncd/pipeline/cmd/controller",
				OriginalTag:    "v0.40.2",
				Digest:         "sha256:dc7bc7d6607466b502d8dc22ba0598461d7477f608ab68aaff1ff4dedaa04f81",
			},
			{
				Manifest:       "../testdata/tekton/base/tekton-base.yaml",
				ManifestDigest: "c2cbc6d7a3c30f99e2e504d5758d8e0ce140a8f444c4d944d85c3f29800bf8c5",
				NodePath:       []string{"spec", "template", "spec", "containers", "image"},
				OriginalRef:    "gcr.io/tekton-releases/github.com/tektoncd/pipeline/cmd/webhook:v0.40.2@sha256:6b8aadbdcede63969ecb719e910b55b7681d87110fc0bf92ca4ee943042f620b",
				OriginalName:   "gcr.io/tekton-releases/github.com/tektoncd/pipeline/cmd/webhook",
				OriginalTag:    "v0.40.2",
				Digest:         "sha256:6b8aadbdcede63969ecb719e910b55b7681d87110fc0bf92ca4ee943042f620b",
			},
		},
	},
}

var baseCasesDigests = map[string]string{
	"ghcr.io/projectcontour/contour:v1.24.1":      "sha256:6c87d0bc19fcec5219107d4e153ea019febd8e03c505276383f4ee1df1d592d6",
	"docker.io/envoyproxy/envoy:v1.25.1":          "sha256:d988076dfe0c92d6c7b8dac20e6b278c8de6c2f374f0f2b90976b7886f9a2852",
	"ghcr.io/fluxcd/kustomize-controller:v0.30.0": "sha256:8c6952141b93764740c94aac02b21cc0630902176bdf07ab6b76970e3556a0d2",
	"ghcr.io/fluxcd/source-controller:v0.31.0":    "sha256:1e0b062d5129a462250eb03c5e8bd09b4cc42e88b25e39e35eee81d7ed2d15c0",
}

func BaseYAMLCases() TestCases {
	baseCases := make([]TestCase, len(baseYAMLCases))
	copy(baseCases, baseYAMLCases)
	return baseCases
}

func BaseYAMLCasesWithDigests(t *testing.T) TestCases {
	baseCases := make([]TestCase, len(baseYAMLCases))
	for i, c := range baseYAMLCases {
		for e := range c.Expected {
			if digest, ok := baseCasesDigests[c.Expected[e].OriginalRef]; ok {
				c.Expected[e].Digest = digest
			} else if c.Expected[e].Digest == "" {
				t.Logf("digest not found for %s", c.Expected[e].OriginalRef)
				t.FailNow()
			}
		}
		baseCases[i] = c
	}
	return baseCases
}