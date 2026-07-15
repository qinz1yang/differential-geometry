# ArzelaAscoli

## Source

This file records the sequential Arzela-Ascoli wrapper used as MSM135 Lemma
3.14.  The proof uses Mathlib's compact-open Arzela-Ascoli theorem, metrizability
of `C(X, R)` for locally compact sigma-compact domains, and the compact-open
to uniform-on-compacts convergence equivalence.

## Definitions and theorems

- `arzelaAscoli_subseq_tendsto` extracts a subsequence converging in the bundled
  compact-open topology on `C(X, R)`.
- `arzelaAscoli_subseq_tendstoUniformlyOnCompacts` translates that convergence
  to `TendstoUniformlyOn` on every compact subset.

Vector-target generalization (2026-06-11, for the F8 AA-for-maps engine):

- `arzelaAscoli_isCompact_closure` — the compactness core for a target `V` with
  `[NormedAddCommGroup V] [ProperSpace V]` (covers every finite-dimensional real
  normed space, e.g. `ContinuousMultilinearMap` spaces): equicontinuous +
  pointwise norm-bounded sequence in `C(X, V)` has compact closure.  Needs only
  `[LocallyCompactSpace X]` (`omit [SigmaCompactSpace X] [T2Space X]`).  Proof is
  the scalar route verbatim with `Set.Icc (-M) M` replaced by
  `Metric.closedBall 0 M` (`isCompact_closedBall` from properness,
  `mem_closedBall_zero_iff`).
- `arzelaAscoli_subseq_vec` — sequential form: subsequence + limit in `C(X, V)`
  with `TendstoUniformlyOn` on every compact (uses metrizability of `C(X, V)`,
  hence the sigma-compact hypothesis again).

The scalar lemmas were intentionally left untouched (they could be re-derived
from the vector core, but they are settled API with downstream consumers).

## Frontier

No new analytic frontier is introduced here.  The deep compactness statement is
provided by Mathlib's Arzela-Ascoli theorem; this file only repackages it in the
sequential form needed by HCG compactness.

## Verification

Verification passed for the targeted Arzela-Ascoli module (including the vector
lemmas; all sorry-free, axiom-clean).  The local audit found no proof
placeholders in the Lean file.

## Lean gotchas

- `omit [...] in` must come *before* the doc comment, not between it and the
  theorem.
- The Mathlib AA core `ArzelaAscoli.isCompact_closure_of_isClosedEmbedding`,
  `ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact`,
  `range_toUniformOnFunIsCompact`, and `UniformOnFun.isClosed_setOf_continuous`
  are all generic in the (T2 uniform) target; the scalar proof generalizes with
  only the pointwise-compactness witness changed.
