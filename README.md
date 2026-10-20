# Failure of semipositive metric extension in a smooth projective family

Lean supplementary materials for the paper by Xiangsen Qin.

## Read this first

These materials contain **12 independent, versioned proof snapshots**, not one
merged Lean project. Each has its own source closure and locked dependencies.
Two historically different versions of the same module are deliberately kept
separate. The root `lean-toolchain` only selects the compiler version; there is no root Lake project.
The common entry module and namespace are
`FailureOfSemipositiveMetricExtension`; the meaning of that entry is local to
its snapshot.

The verified source manuscript is
`failure_semipositive_metric_extension_final(1).tex`,
SHA-256 `dfba014b5838efd2bfb74994f2ca68113b285af56be6dd4356601e1a6e1014f9`.
This release accompanies that source version and its previously verified Lean
snapshots. The [paper–source correspondence table](docs/PAPER_SOURCE_MAP.md)
identifies the precise declarations, snapshot, and external dependencies for
each indexed item. The original 44-item inventory includes definitions and
non-proof items; it is not a count of 44 new theorems.

The paper-specific results are relative to explicitly stated classical inputs
and algebraic–analytic identifications. Read the [external-input and scope
register](docs/EXTERNAL_INPUTS.md) before using them. These sources do not
reconstruct every underlying analytic or algebraic theory inside Lean. The manuscript itself is not bundled; its version is identified by filename and checksum.

## Contents and snapshot identity

| Directory | Principal role |
|---|---|
| `snapshots/E01` | Broad earlier paper-specific baseline, including explicit geometry, metrics, and the obstruction construction |
| `snapshots/E02` | Projective-point and auxiliary-curve geometry, including the actual restricted pullback bundle |
| `snapshots/E03` | Nonzero transverse derivatives and surjectivity for the actual divided coefficients of Q |
| `snapshots/E04` | Fixed-fibre blowdown complement and biholomorphic identification |
| `snapshots/E05` | Four principal opens and local principality of the total centre ideal |
| `snapshots/E06` | Fixed-fibre projective inputs |
| `snapshots/E07` | Analytic assembly of the concrete Theorem A endpoint |
| `snapshots/E08` | Named paper divisor cocycles |
| `snapshots/E09_E10` | Strict-transform components and distinct central lines |
| `snapshots/E11` | The local observation concerning Hisamoto's first example |
| `snapshots/E12_E14` | Actual blowup graph and local four-to-one equivalence |
| `snapshots/E13` | Independent positive-current residual and minimal-singularity endpoint |
| `docs/` | Source-manuscript correspondence and exact external-input boundaries |
| `provenance/` | Source archive identities, namespace mapping and third-party license notices |
| `verification/` | Reviewer-facing build summary; reproduction writes new local results here |
| `scripts/` | Fresh-build driver and integrity checker |

Only proof sources, configurations, reviewer documentation and a newly prepared build summary are distributed. Reproduction generates fresh local logs; internal and historical execution records are not included.

## Requirements

- Lean **4.19.0**, official release, including Lake.
- Python 3.10 or later and Git. The recorded run used Linux; the driver uses
  symbolic links when augmenting the Mathlib cache. On Windows, use WSL or an
  environment with symbolic-link support.
- Mathlib at commit **c44e0c8ee63ca166450922a373c7409c5d26b00b**.
- Every additional package at its exact commit in the snapshot's
  `lake-manifest.json`. The reviewer build summary lists the actual checked commits.
- Sufficient space for the Lean toolchain and Mathlib caches. They are not
  bundled in this source archive.

Do not update the lockfiles to a newer Mathlib version merely to make setup
succeed. Missing network access or an unavailable pinned dependency is an
infrastructure limitation, not successful proof verification.

## Download, prepare dependencies, and run one snapshot

Unpack `Failure_of_Semipositive_Metric_Extension_Lean.zip`, enter its top-level
`failure-of-semipositive-metric-extension` directory, and check file integrity:

```sh
python3 scripts/check_integrity.py
```

Install Lean 4.19.0 using the [official Lean installation guide](https://lean-lang.org/install/)
or its [manual Elan instructions](https://lean-lang.org/install/manual/) if it is
not already available. With Elan installed, the toolchain command is:

```sh
elan toolchain install leanprover/lean4:v4.19.0
```

To obtain the dependencies and official compiled caches for a selected snapshot:

```sh
cd snapshots/E07
lake exe cache get
cd ../..
```

Lake reads the committed toolchain and dependency lockfile. This setup step
requires network access to the official repositories and cache host. It is not a
proof-checking step. The present verification used already available pinned
external dependencies, rather than testing a new network download.

Then, from the repository root:

```sh
python3 scripts/build_snapshot.py E07
```

A replay writes new local results and compiler logs under `verification/`. The driver requires the
exact toolchain and package commits. It discards this
snapshot's previous `.fresh-build` directory, recompiles all its paper-owned
modules in dependency order, and runs the snapshot's root entry and audit files.
It reuses the compiled external-package caches; if the pinned Mathlib
`ReesAlgebra` cache is missing, it compiles that module from its pinned source.
An exit code of zero and `"status": "passed"` in
`verification/E07/BUILD_RESULT.json` are the expected results. Warnings and
printed axiom lists can appear in logs; a compiler error is not a pass. For an existing shared dependency installation, use explicit paths:

```sh
python3 scripts/build_snapshot.py E07 \
  --lean /path/to/lean-4.19.0/bin/lean \
  --dependencies /path/to/pinned-packages
```

The dependency directory must contain the `mathlib`, `batteries`, and other
package directories named in the lockfile, with matching Git checkouts and
compiled caches. This is the mode actually used for the present verification.
The external dependency caches were not all rebuilt from source during this run.

## Run the collection, without pretending it is a merged project

```sh
python3 scripts/build_all.py
```

This is an **orchestration entry point**, not a theorem proving that the snapshots
form a single compatible project. It calls the per-snapshot builder separately.
For shared installed dependencies, the `--lean` and `--dependencies` options are
accepted as above. A completely fresh own-module build is the default.

For `build_all.py`, an optional `--round-cache /path/to/cache-base` can avoid
recompiling identical modules repeatedly within a single verification run. Each
invocation creates a new empty session subdirectory and uses a matching run
token; old cache sessions are not silently treated as new compilation. Its key contains the module
name, exact source hash, recursively keyed own imports, external revisions, full
Lean version and compilation options. Distinct historical source versions
therefore cannot share a key. A reused output must match the stored artifact
hash. The logs distinguish `fresh` from `reused-this-run` and identify the
producer snapshot. Root entries and audits are still loaded separately. This
optimization is not permission to reuse unverified historical paper `.olean`
files. See [the actual build record](verification/BUILD_SUMMARY.md) for what was
really done in this release.

Ordinary `lake build` is also a project entry for each renamed snapshot, but the
recorded verification command is the Python fresh-build driver. Do not describe
an unexecuted Lake build or a successful checksum as a newly compiled result.

## Names, provenance, and the three different checks

[Source identities and namespace mapping](provenance/SOURCE_VERSIONS.md) record the original archive identities and the mechanical renaming rules. Mathematical declarations retain their descriptive internal names. Paper labels and numbers are linked to exact declaration names in the correspondence table. Each snapshot has its own generated canonical import entry and updated project configuration.

1. **File integrity** checks bytes against hashes. It is not Lean compilation.
2. **Lean compilation** checks declarations relative to their actual axioms and
   imported dependencies. It does not establish that an informal sentence has
   precisely the same meaning as a formal statement.
3. **Correspondence review** compares the source manuscript with source types,
   hypotheses, objects and external inputs. These checks remain distinct even when the corresponding modules compile.

The prior source backup had SHA-256
`e3b02ee4429b150308542e35261b32c56f3349c4e6f6e3f0a581a579303e64f9`.
The per-snapshot archive identities are in
[source-version register](provenance/SOURCE_VERSIONS.md). The newly prepared reviewer build summary distinguishes fresh compilation from reuse within the same run.

## Publication and citation

Repository: [qinxiangsen/failure-of-semipositive-metric-extension](https://github.com/qinxiangsen/failure-of-semipositive-metric-extension).

Proof-source commit: [`e80dd4eaa2de87dc70902174cd371961d91bc1db`](https://github.com/qinxiangsen/failure-of-semipositive-metric-extension/commit/e80dd4eaa2de87dc70902174cd371961d91bc1db).

Version: **v1.0.0** ([release page](https://github.com/qinxiangsen/failure-of-semipositive-metric-extension/releases/tag/v1.0.0)). The release tag identifies the final distribution commit; the proof-source commit above identifies the verified source before this citation-metadata update.

Suggested supplementary-material sentence:

> The Lean supplementary material for this paper is available as version v1.0.0 at https://github.com/qinxiangsen/failure-of-semipositive-metric-extension/releases/tag/v1.0.0.

No open-source license has been selected on the author's behalf.

### Legacy informational diagnostic

The default verification includes the library sources, available endpoint and cumulative kernel audits, and the paper/source declaration checks. E01 `Audit.lean` is an optional legacy diagnostic containing 3,072 repeated `#print axioms` commands, not an additional theorem. It is excluded from the default driver; add `--full-legacy-audit` to `build_snapshot.py E01` to request it. In the recorded run this diagnostic was interrupted after the library compilation and is **not reported as passed**. The remaining endpoint/kernel checks were run separately against the freshly compiled library. See the build record for their actual outcomes.
