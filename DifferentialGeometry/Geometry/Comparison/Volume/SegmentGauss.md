# SegmentGauss.lean — L6 step (a) core: Gauss endpoint block-determinant split

Brick B5d, step (a) of the A0′ `VolumeComparisonInput` lane
(`HCGCompactness/C4/A0PRIME_VOLUME_PLAN.md` §8).  New file; ADDs reusable lemmas,
touches no settled file.

## Status

- **GREEN, sorry-free, verified.**  Focused check + targeted build
  `+…Comparison.Volume.SegmentGauss` (3814 jobs).  `#print axioms` for both main
  theorems = `[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no
  HopfRinow taint.

## Public API

- `velJacFrame g hEnorm x u w` — the `Option (Fin d)`-indexed endpoint frame:
  `none` slot = the geodesic velocity field `t ↦ γ̇(t)` (`γ = intrinsicGeodesic x u`),
  `some i` slot = the transverse intrinsic Jacobi field `intrinsicJacobi x u (wᵢ)`.
  With `@[simp]` reduction lemmas `velJacFrame_none` / `velJacFrame_some`.
- `velJac_gram_split` (main): for `wᵢ ⊥ u` (`g.inner x u (wᵢ) = 0`),
  `det (curveGram … velJacFrame … 1) = g.inner x u u · det (curveGram … transverse … 1)`.
  The Gauss block-determinant factorization at the geodesic endpoint, GLOBAL
  (past the cut locus).
- `velJac_density_split`: `curveDensity … velJacFrame … 1
  = √(g.inner x u u) · curveDensity … transverse … 1`.  The density face.
- `radialJac_eq_vel` (**B5d2, step (i)**): `intrinsicJacobi x u u 1 = curveVelocity
  (intrinsicGeodesic x u) 1`.  Sorry-free.
- `curveGram_recomb` / `curveDensity_recomb` (**B5d2, step (a) glue**): if the
  endpoint values recombine linearly, `V' i t = ∑ k, C k i • V k t`, then
  `curveGram V' t = Cᵀ · curveGram V t · C` and `curveDensity V' t = |det C| ·
  curveDensity V t`.  Pure `g.inner` bilinearity + `det (Cᵀ G C) = (det C)² det G`.
- `curveDensity_reindex` (**B5d2, step (a) glue**): `curveDensity (V ∘ e) t =
  curveDensity V t` for a bijection `e : ι ≃ κ` (`det_submatrix_equiv_self`).
  Bridges the `Fin n` launch frame to the `Option`-indexed `velJacFrame`.

## Route (verified) — this is `endpoint_det_split` (RadialGram.lean, private,
chart-scale) redone globally with the **public** intrinsic Gauss/speed lemmas:

- radial diagonal `g(γ̇(1), γ̇(1)) = g_x(u,u)` from `intrinsicGeodesic_speedSq_eq`
  (`curveVelocity = mfderiv γ t 1`, so it matches the speedSq statement at `t=1`).
- off-diagonal `g(γ̇(1), Jᵢ(1)) = g_x(u, wᵢ) = 0` from the PUBLIC
  `intrinsicJacobi_perp` (`velocityLift.snd` is defeq `curveVelocity γ 1`).
- block det: reindex `Option (Fin d) ≃ Fin d ⊕ PUnit`
  (`Equiv.optionEquivSumPUnit`), `Matrix.fromBlocks … 0 0 D`,
  `Matrix.det_fromBlocks_zero₂₁`, `Matrix.det_reindex_self`, `Matrix.det_unique`.
- density: `curveDensity = √det`, `Real.sqrt_mul` with `0 ≤ g_x(u,u)`
  (`(g.pos x u hu).le` else `simp`).

## Lean lessons (durable)

- **Instance ORDER matters**: put `attribute [-instance]
  Tensor0SBundle.tangentSpace_normedAddCommGroup/normedSpace` BEFORE the
  `variable [RiemannianBundle …]` / `[PseudoEMetricSpace M] …` block (mirror
  `RadialLaplacian.lean`).  If the emetric variables are declared while the
  Tensor0S fibre instances are still active, `intrinsicGeodesic`'s
  `PseudoEMetricSpace M` fails to synth and every term shows `sorry` in the
  delaborator (a poisoned-term artifact, not a real `sorry`).
- **match-def reductions**: a `def foo | none => … | some i => …` does NOT reduce
  under `simp [foo]`.  Add `@[simp] theorem foo_none/foo_some … := rfl` and use
  THOSE in the block `ext`.
- Metric self-nonneg: `(g.pos x u hu).le` for `u ≠ 0`, `simp [hu]` for `u = 0`
  (there is no `g.posSemidef`).

## Step (i) `radialJac_eq_vel` — DONE (2026-07-26, B5d2), sorry-free.

`intrinsicJacobi x u u 1 = curveVelocity (intrinsicGeodesic x u) 1`.  Route
executed exactly as planned: reparametrize `u + r•u = (1+r)•u` (`add_smul`,
`one_smul`), rewrite the varied curve by spray homogeneity
`intrinsicGeodesic_smul` to `φ ∘ (1 + ·)`, then `HasMFDerivAt.comp 0 hshift` with
`hshift : HasMFDerivAt (fun r ↦ 1+r) 0 id` (from `hasMFDerivAt_iff_hasFDerivAt`
+ `(hasFDerivAt_id 0).const_add 1`).  The `mfderiv (1+·) 0 1 = 1` fiddle
DISSOLVED — no need to compute it directly; `HasMFDerivAt.comp` carries the `id`
differential and `HasMFDerivAt.mfderiv` + `rfl` finishes (NB the final `((mfderiv
φ 1).comp id) 1 = mfderiv φ 1 1` closes by `rfl`, not `simp` — `simp` reports "no
progress" on the CLM-coe form).  Focused check GREEN.

## What is NOT here (the remaining L6 frontier — see SegmentPolar.md)

The change-of-basis GLUE is now here (`curveGram_recomb`/`curveDensity_recomb`/
`curveDensity_reindex`) and `radialJac_eq_vel` (step i) is proved.  What is still
missing to close `segBall_vol_le` (B5d2 stopped here, failure-first):

1. **Step (a) assembly** (tractable, not started): construct the launch basis
   `b = {v} ∪ {gₓ-ON transverse}` as a `Fin n` `Module.Basis`, compute
   `|det C_b| = ℓ/√det gₓ` from its `gₓ`-Gram block `[[ℓ²,0],[0,I]]`
   (`velJac_gram_split`-style + `Cᵀ Gₓ C` congruence), reindex `Fin n ≃ Option
   (Fin (n-1))` (`curveDensity_reindex`) to identify `curveDensity({J(b)})1 =
   curveDensity(velJacFrame)1`, then combine with `velJac_density_split` +
   `radialJac_eq_vel` and `curveDensity_recomb` to land
   `expJacDensity v = √det gₓ · curveDensity(transverse gₓ-ON)1`.
2. **Step (c) SHARP `N=1`** — THE DECISIVE FRONTIER (missing API, confirmed
   2026-07-26).  `curveDensity(transverse gₓ-ON)1 ≤ hypSn(qℓ,1)^{n-1}` needs the
   pole ratio `curveDensity(transverse)(t)/hypDensity(qℓ,n-1)(t) → 1`.  The
   in-tree `intrPoleCap` (IntrinsicRatio.lean:205, private) is **NON-sharp**:
   `N = (normalChartDensity(0)+1)/c`, `c = ℓ/|det(B→model)|`; its own docstring
   flags sharp `N=1` as "not yet available".  Since `segBall_vol_le` is an
   EQUALITY on flat ℝ², a lossy `N>1` breaks it — the sharp pole normalization
   (essentially `normalChartDensity(0)·|det(B→model)|/ℓ = 1`, i.e. `mfderiv exp_x
   at 0 = id` pushed through the density) is a genuine ~200-line sub-project.
3. **Step (b)+(d)** (tractable, not started): `gₓ^{1/2}` linear CoV via
   `addHaar_image_linearMap` (`μ(f''s)=ofReal|det f|·μ s`), and the truncated
   E-polar identity assembled from `lintegral_polar` (`PolarEvaluation.lean:50`) +
   `toSphere_apply_univ` (σ) + `volumeIoiPow` (`r^{n-1}dr`) — no packaged
   truncated-ball radial lemma exists, but all blocks are present.
