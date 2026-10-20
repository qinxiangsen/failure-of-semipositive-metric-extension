# Reviewer build summary

Prepared for this source distribution on 2026-10-20 (Asia/Shanghai, UTC+8). This document reports actual checks; it is not a raw execution log.

## Environment and command

Lean 4.19.0, Linux x86_64; pinned external dependencies and compiled external caches were available locally. All own-module compiler invocations used `lean -j1 -o OUTPUT SOURCE`. The equivalent reviewer command, from the repository root, is:

```sh
python3 scripts/build_snapshot.py E07 --lean /path/to/lean-4.19.0/bin/lean --dependencies /path/to/pinned-packages
```

Replace E07 with each snapshot identifier below, or use `scripts/build_all.py` with the same options. The supplied driver recreates the snapshot’s own output directory. A zero exit and `passed` result indicate success for its requested targets. Output is generated locally under `verification/`; no internal execution records are distributed.

## Actual results

| Snapshot | Fresh own modules and audits | Reused within this run | Required targets | Completion (UTC+8) |
|---|---:|---:|---|---|
| E01 | 297 | 0 | passed | 2026-10-20T16:56:26.105962+08:00 |
| E02 | 35 | 36 | passed | 2026-10-20T16:38:03.050370+08:00 |
| E03 | 30 | 33 | passed | 2026-10-20T16:35:48.179699+08:00 |
| E04 | 3 | 43 | passed | 2026-10-20T16:36:03.547230+08:00 |
| E05 | 10 | 0 | passed | 2026-10-20T16:31:43.467252+08:00 |
| E06 | 3 | 44 | passed | 2026-10-20T16:36:17.219712+08:00 |
| E07 | 202 | 0 | passed | 2026-10-20T16:45:15.465579+08:00 |
| E08 | 10 | 74 | passed | 2026-10-20T16:36:56.426498+08:00 |
| E09_E10 | 7 | 60 | passed | 2026-10-20T16:37:24.512073+08:00 |
| E11 | 25 | 80 | passed | 2026-10-20T16:47:35.098454+08:00 |
| E12_E14 | 23 | 37 | passed | 2026-10-20T16:36:15.549547+08:00 |
| E13 | 165 | 0 | passed | 2026-10-20T16:42:24.734478+08:00 |

E01’s optional legacy `Audit.lean`, containing 3,072 repeated `#print axioms` commands, was interrupted (exit 130) and is not counted as passed. Its library, `EndpointAudit`, `KernelAudit`, and original aggregate entry all completed successfully. The default driver omits only this optional diagnostic; use `--full-legacy-audit` to include it. No theorem or axiom was removed.

The source correspondence’s 242 declaration occurrences were checked by seven snapshot-specific `PaperSourceAudit.lean` files; all seven checks exited zero. Declaration type/name checks do not alone prove informal–formal semantic equivalence.

Fresh counts include import entries and diagnostic files, not numbers of new theorems. The 407 same-run reused module outputs were matched by source hashes, recursively keyed own imports, external versions, compiler version and options, and traced to successful fresh compilation in this run. No historical paper-owned binary was used. The public driver defaults to fresh own-module compilation; its optional collection cache creates a new session for each run.

The external dependency caches were reused, not rebuilt in full. Missing `Mathlib.RingTheory.ReesAlgebra` was compiled from the pinned source separately for each snapshot. Network bootstrap and a separate `lake build` were not executed in this verification. The instructions let reviewers perform their own reproducibility check rather than substituting supplied logs for a build.

## Pinned dependency revisions

| Package | Commit |
|---|---|
| mathlib | `c44e0c8ee63ca166450922a373c7409c5d26b00b` |
| plausible | `77e08eddc486491d7b9e470926b3dbe50319451a` |
| LeanSearchClient | `25078369972d295301f5a1e53c3e5850cf6d9d4c` |
| importGraph | `e6a9f0f5ee3ccf7443a0070f92b62f8db12ae82b` |
| proofwidgets | `c4919189477c3221e6a204008998b0d724f49904` |
| aesop | `5d50b08dedd7d69b3d9b3176e0d58a23af228884` |
| Qq | `fa4f7f15d97591a9cf3aa7724ba371c7fc6dda02` |
| batteries | `f5d04a9c4973d401c8c92500711518f7c656f034` |
| Cli | `02dbd02bc00ec4916e99b04b2245b30200e200d0` |

All listed dependency checkouts matched the committed lockfiles and had no tracked modifications when checked. File integrity (`scripts/check_integrity.py`), Lean compilation and manuscript/source correspondence are separate checks. The paper and proof sources were not changed when preparing this public-facing summary.
