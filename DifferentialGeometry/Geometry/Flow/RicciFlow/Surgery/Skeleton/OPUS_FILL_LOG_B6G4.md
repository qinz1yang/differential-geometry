# B6g4 — DESIGN_B6D_GLUE bricks B8, B9, B10, B11 (2026-09-26)

- Start. Read AGENTS.md (pc3), DESIGN_B6D_GLUE.md (whole), H7 digest, OPUS_FILL_LOG_B6D/B6G1/B6G2/B6G3,
  `AncientPointedFlowLimitTransfer.lean` (Part A :283, B6d transfer :1186, headline :1387).
- Transfer, B1 (`ExceptionalSetApproximation`) are committed (eee792ac9) with fresh oleans (09:40 >
  source 08:32): new file compiles in-repo with `lake env lean`, 2 threads.
- Plan: one new file `Surgery/Topology/AncientPointedFlowLimitShiftedTransfer.lean` (B8–B11: one
  development, transfer at shifted approximant times).

## DONE — all four bricks, one new file, compiled in-repo

File: `Surgery/Topology/AncientPointedFlowLimitShiftedTransfer.lean` (676 lines), namespace
`…Perelman.CanonicalNeighborhood.FiniteHorn`, imports Transfer (committed, olean), B1
(`Topology.Sequences.ExceptionalSetApproximation`), `Compactness.Metric.Canonical.ReferenceChange`,
`Metric.Convergence.DerivativeNorm.OpenEmbedding`, `Metric.BilinearPerturbation`,
`Metric.Convergence.Time.Lipschitz`. Transfer and every committed file untouched; root aggregate
untouched; nothing staged.

- **B8** `tendsto_metricDerivNormSupOn_localPull_shifted_of_time_lipschitz`. §2 statement plus
  THREE hypotheses: `(Cd : MetricConvergenceData F)`,
  `(hcan : ∀ n, Cd.domain n = CanonicalMetricCompactness.canonicalSourceData F n)`,
  `(hPc : MetricComplete P)`. Reason: the Lipschitz hypothesis only holds on the `(k+2)`-ball of
  `X.obj n`; without the metric convergence data nothing puts `φ(K)` there (F alone carries no
  metric information), and §2's own proof plan cites `F.eventually_image_closed_ball_subset`, which
  takes exactly these three. B11 (hence B13) has all three. They also give injectivity of `φ` on
  `V k` (`V k ⊆ F.source`), so no `hVF` is needed.
  Proof (review H7 (a)): triangle `φ*h(σₙ) → φ*h(s) → G s`; second term by `hconv` at `s`
  (`-k ≤ s` gives the time margin); first term: naturality of `metricDerivNorm` under the injective
  local pullback (private helper via `pullbackMetricOfInjectiveLocalDiffeomorph`), the pointwise
  Lipschitz bound with reference `h 0`, then reference change `φ*h(0) → P.metric` by
  `metricDerivNormSupOn_le_of_reference_swap_of_covDerivNorm` (eps = 1) fed by
  `eventually_metricDerivNorm_swap_le` on `hconv` at `t = 0` + `hG0` and
  `inner_bounds_of_metricDerivNorm_le`; constant `√(2^(2+p))(1 + D₂,ₚ(p+1))·max L 0`; `|σₙ − s| → 0`.
- **B9** `neck_alternatives_of_local_flow_limit_at_shifted_times`: exactly §2 (copy-edit of
  `neck_alternatives_of_local_flow_limit`; `hconv`/`hEreg` dropped, `σ`, `hconvσ`, `hσE` added; the
  approximant metric is `h k (fψi) (σ s (fψi))`, `σ s (fψi) ∈ Icc` read off `hconvσ` with `K = ∅`).
- **B10** `abs_derivWithin_scalar_le_of_local_flow_limit_of_shrinking_sliver`: exactly §2 (`hζ`,
  `hE : ∀ n, (E n \ Icc (-(ζ n)) 0).Finite`); eventually `ζ(fψi) < -(t+δ)`, so exceptional points in
  the window `[t−δ, t+δ]` lie in the finite set `E \ Icc (−ζ) 0`.
- **B11** `exists_scalar_bound_of_ancient_pointed_flow_limit_of_approximants_of_time_lipschitz`:
  exactly §2 (old `E`-line replaced by the Lipschitz block + `ζ`, `hζ`, `hE`; `hW`, `hderiv`
  unchanged; strict thresholds kept). Proof: `σ s` from B1 by `choose`, `hconvσ` from B8, B9, B10,
  then the old headline's slice-bound + Harnack steps verbatim. Old headline kept.
- Verification: in-repo `lake env lean` (2 threads, lakefile leanOptions passed): no output.
  Scratch copy outside the tree: `#print axioms` on all four public theorems
  `[propext, Classical.choice, Quot.sound]`; `#lint` 14 linters: 0 errors on 6 declarations.
  Copy removed. Lines ≤ 100 (imports excepted); no comments/docstrings; names unique library-wide.
- Note: a concurrent acceptance `lake build` in pc3 caused transient `failed to read file …olean`
  on two compiles; retried, clean.
- Deferred merges for the lead: the private `metricDerivNorm_localPullMetric_of_injective`
  (naturality of `metricDerivNorm` under an injective local pullback) belongs public in
  `Geometry/Metric/Convergence/DerivativeNorm/` next to
  `metricDerivNorm_pullbackMetricOfInjectiveLocalDiffeomorph`; the `opensSigmaCompact…` local
  instance is the fourth copy (Transfer has three). Register
  `…Surgery.Topology.AncientPointedFlowLimitShiftedTransfer` in the root aggregate at acceptance.
