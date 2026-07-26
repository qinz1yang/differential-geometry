# SegmentPolar.lean — B2 (α) polar-measure layer (THE frontier)

Polar-measure layer of brick B2 of the A0′ `VolumeComparisonInput` lane
(`HCGCompactness/C4/A0PRIME_VOLUME_PLAN.md` §5).  Consumes `SegmentDomain.lean`
(set layer, sorry-free) and states the two volume-comparison inputs B5 needs.

## Contents

- `segBall_vol_le` — absolute Bishop upper bound (deliverable B2(α)(1)):
  `V(x,R) ≤ σ · ofReal (hypRadVol q (n-1) R)`, with the **model sphere mass**
  `σ = (modelHaar E).toSphere Set.univ` (= `finrank · vol(unit ball)`).  **`sorry`.**
- `segBall_vol_fin` — B6-facing finiteness corollary `V(x,R) < ⊤`; **PROVED**
  from `segBall_vol_le` (`Measure.toSphere` is `IsFiniteMeasure`, so `σ < ⊤`;
  `ENNReal.mul_lt_top` + `measure_lt_top` + `ofReal_lt_top`).  Its only frontier
  dependency is `segBall_vol_le`'s `sorry`; interface stable for B6 regardless.
- `segBall_vol_rel` — capped relative Bishop–Gromov, multiplicative form
  (deliverable B2(α)(2), the B5 input): `V(x,R)·v(s) ≤ v(R)·V(x,s)`, `0 < s ≤ R`.
  **`sorry`.**  Normalization-independent: `σ` cancels across the ratio, so it
  carries NO sphere-mass factor.  UNCHANGED from the accepted version.

All stated in terms of `riemannianVolumeMeasure`, `hypRadVol`, and the
`toSphere` sphere mass (no exposed density / tangent-space measure) so B5/B6
consume them directly.

## Constant correction (2026-07-25, orchestrator review — do NOT re-drop `σ`)

The first draft of `segBall_vol_le` dropped the sphere-mass constant and was
**FALSE**.  Counterexample: `M = E = ℝ²` flat (complete, connected,
`RicciBoundedBelow g 0`, `q = 0`): `V(x,R) = πR²`, but
`hypRadVol 0 1 R = ∫₀ᴿ t dt = R²/2`, and `πR² > R²/2`.  `hypRadVol` is the
RADIAL model volume only; the polar decomposition (`normalBall_polar`,
`BishopPolar.lean:102`) integrates the radial density against
`Measure.volumeIoiPow (n-1)` over the sphere measure `(modelHaar E).toSphere`,
whose total mass `σ` multiplies the radial integral.  `toSphere_apply_univ`
(`Mathlib/…/HaarToSphere.lean:88`): `μ.toSphere univ = dim E · μ(ball 0 1)` —
so `σ = finrank · vol(unit ball)` (= `2π` in dim 2, `2` in dim 1).  Corrected
bound is an equality in the flat case: `πR² ≤ 2π·(R²/2)`; dim 1: `2R ≤ 2·R`.
The relative form `segBall_vol_rel` was and stays correct because `σ` cancels.

## The frontier (honest failure report)

The brick premise — that (α)(1) is a cheap `measure_image_le`-style change of
variables — is **incorrect as stated**.  Root cause:

- Mathlib `MeasureTheory.addHaar_image_le_lintegral_abs_det_fderiv`
  (`.lake/…/Mathlib/MeasureTheory/Function/Jacobian.lean:903`) is the correct
  non-injective `≤` area inequality, but it is `E → E` with an **additive-Haar
  target** measure.  It does NOT apply to `expMapIntrinsic x : T_xM → M` whose
  target carries `riemannianVolumeMeasure` (a manifold measure, not Haar on `E`).
- The in-tree change-of-variables `riemannianVolumeMeasure_image_param_eq`
  (`Analysis/Integration/Measure/ParamEvaluation.lean:1428`) and
  `normalChart_volume_eq` are **`PartialDiffeomorph`-only** (injective) — exactly
  what fails past the cut locus.
- Building the `E → M` non-injective bridge also needs differentiability of
  `v ↦ expMapIntrinsic x v` **past `v = 0`**.  In-tree only
  `mfderiv_expMapIntrinsic_at_zero` (at zero) and the variational
  `expMapIntrinsic_variation_contMDiff` exist for the INTRINSIC exp; the off-zero
  `C¹` lemma `expMap_contMDiffAt_of_ne_zero`
  (`Exponential/Smoothness/OffZero.lean`, sorry-free) is for the **chart-fixed**
  `expMap` (= `maximalGeodesic · 1`), and `expMap = expMapIntrinsic` globally is
  not recorded.

### Smallest unblocking lemma (next brick)

A reusable, canonical-home lemma in `Analysis/Integration/Measure/`:

    theorem riemannianVolume_image_le_lintegral_density
      (f : E → M) (hf : ∀ v ∈ A, HasFDerivWithinAt (chart∘f) … v) (hA : MeasurableSet A) :
        riemannianVolumeMeasure g (f '' A)
          ≤ ∫⁻ v in A, ENNReal.ofReal (density f v) ∂(modelHaar E)

— the manifold-valued non-injective area inequality, obtained by a countable
measurable chart partition of the σ-compact `M`, applying the Euclidean
`addHaar_image_le_lintegral_abs_det_fderiv` to `chartₙ ∘ f` on each piece, and
identifying `|det D(chartₙ∘f)| · chartDensityₙ` with the intrinsic radial Jacobi
density.  With `f = expMapIntrinsic x`, `A = SegDom ∩ gBall`, plus:
- differentiability of `expMapIntrinsic x` on `A \ {0}` (`{0}` is `modelHaar`-null),
- the (β) pointwise density bound `curveMean_le_hyp`/`exists_intrMean` (intrinsic,
  past the cut locus — already in-tree),
- the Euclidean polar integral of `hypDensity` = `hypRadVol` (model side),

`segBall_vol_le` follows (now with the `σ = toSphere Set.univ` factor — the
polar sphere integral — retained, per the constant correction above).
`segBall_vol_rel` additionally needs the truncated polar Fubini (per-direction
cut time `τ(θ)`) + the truncated ratio-of-integrals lemma (brick B4).

Obstruction class: **missing reusable API** (measure-theoretic area formula for
maps into a Riemannian manifold) + **missing regularity API** (off-zero
differentiability of the intrinsic exponential in the velocity).  NOT a local
proof-search gap, wrong statement, or typeclass issue.

## Status

- **2026-07-26 (B5d2) — steps (i) + (a)-GLUE landed sorry-free; `segBall_vol_le`
  NOT discharged; both SegmentPolar `sorry`s UNTOUCHED; endpoint `volInput_of_bg`
  STILL 0%.**  Failure-first: the decisive blocker is step (c)'s **sharp `N=1`
  transverse bound**, a genuine MISSING-API frontier (independently confirmed).

  *Landed (SegmentGauss.lean, all sorry-free, targeted build 3814 jobs, clean):*
  - `radialJac_eq_vel` (step (i)): `intrinsicJacobi x u u 1 = curveVelocity
    (intrinsicGeodesic x u) 1`.  Route as planned (reparametrize `u+r•u=(1+r)•u`,
    spray homogeneity `intrinsicGeodesic_smul`, `HasMFDerivAt.comp` with the unit
    shift's `id` differential); the `mfderiv (1+·) 0 1` fiddle dissolved (the
    `.comp` carries `id`; final CLM step closes by `rfl`, not `simp`).
  - `curveGram_recomb` / `curveDensity_recomb` (step (a) glue): change-of-basis
    congruence `curveGram V' t = Cᵀ · curveGram V t · C`, `curveDensity V' t =
    |det C| · curveDensity V t` for `V' i t = ∑ k C k i • V k t`.
  - `curveDensity_reindex`: `curveDensity (V∘e) t = curveDensity V t`, `e : ι≃κ`.

  *THE BLOCKER (step (c), sharp `N=1`) — missing API, confirmed 2026-07-26.*  The
  transverse bound `curveDensity(gₓ-ON transverse)(1) ≤ hypSn(qℓ,1)^{n-1}` needs
  the pole ratio `→ 1`.  The only in-tree pole cap, `intrPoleCap`
  (IntrinsicRatio.lean:205, private), is **NON-sharp**: it yields
  `N = (normalChartDensity(0)+1)/c` with `c = ℓ/|det(B→model)|`, and its OWN
  docstring flags the sharp `N=1` as "not yet available".  `segBall_vol_le` is an
  EQUALITY on flat ℝ² (the σ constant is exact), so any `N>1` breaks it — a lossy
  bound cannot discharge it.  The sharp pole normalization (`normalChartDensity(0)
  ·|det(B→model)|/ℓ = 1`, i.e. `mfderiv exp_x at 0 = id` pushed through the density
  defs) is a genuine ~200-line sub-project that does not exist in-tree.  Also:
  `exists_intrFrame` (IntrRadialFrame.lean:57) gives a FULL `n`-frame (parallel,
  g-ON at every point), NOT the transverse `(n-1)` frame; the transverse perp
  frame comes from `exists_perp_pos`.

  *Also missing (assembly, tractable, blocked behind (c)):* step (a) full
  assembly (launch-basis `|det C_b| = ℓ/√det gₓ` + `Fin n ≃ Option (Fin (n-1))`
  reindex to `velJacFrame`); step (b)+(d) (`gₓ^{1/2}` CoV via
  `addHaar_image_linearMap`, truncated E-polar from `lintegral_polar` +
  `toSphere_apply_univ` + `volumeIoiPow`).  L7 (`segBall_vol_rel`) NOT started.

  Obstruction class = **missing reusable API** (sharp Bishop pole normalization).
  Statements correct + anisotropy-robust; do NOT weaken.  See SegmentGauss.md
  "What is NOT here" for the ordered remaining sub-lemmas.

- **2026-07-26 (B5d) — step (a) CORE landed; full L6 route DERIVED with exact
  constants (de-risked); both SegmentPolar `sorry`s UNTOUCHED; endpoint 0%.**

  Failure-first: `segBall_vol_le` / `segBall_vol_rel` are NOT discharged.  L6 is a
  genuine multi-session from-scratch Bishop–Gromov absolute bound (four
  interlocking substantial sub-lemmas); one session lands a fraction.

  *Landed (new file `SegmentGauss.lean`, sorry-free, axiom-clean, targeted build
  3814 jobs):* `velJac_gram_split` / `velJac_density_split` — the **global** Gauss
  block-determinant / density factorization at the geodesic endpoint (step (a)
  core), `det[{γ̇(1)}∪{Jᵢ(1)}] = g_x(u,u)·det[transverse]`, from the PUBLIC
  `intrinsicJacobi_perp` + `intrinsicGeodesic_speedSq_eq`.  See `SegmentGauss.md`.

  *THE COMPLETE ROUTE (verified on flat ℝ² AND diag(4,1) — constants telescope):*
  With `K = SegDom ∩ closedGBall R`, `riemVol_exp_image_le` (DONE) gives
  `V(x,R) ≤ ∫⁻_K ofReal(expJacDensity v) ∂modelHaar`, where
  `expJacDensity v = curveDensity(chartModelBasis Jacobi frame)(1)`.  Then:
  1. **step (a)** — change `chartModelBasis` (E-ON) to the gₓ-ON adapted basis
     `{v/ℓ, ê₁,…,ê_{n-1}}` (ℓ = |v|_{g_x}); `velJac_gram_split` (radial slot is
     `γ̇(1) = radial Jacobi via `radialJac_eq_vel`) block-splits the Gram.  The
     E-ON↔gₓ-ON change-of-basis determinant is **|det C| = √det(g_x,x)** (constant
     in v).  Net: `expJacDensity v = √det(g_x,x) · curveDensity(transverse gₓ-ON
     frame adapted to v)(1)`.
  2. **step (c) — SHARP `N=1`** — `curveDensity(transverse gₓ-ON)(1) ≤
     hypSn(q·ℓ, 1)^{n-1}` (`= hypDensity(q·ℓ)(n-1)(1)`).  From
     `exists_intrRatio` (ratio AntitoneOn `Ioo 0 b`) fed a gₓ-ON perp frame, whose
     pole limit is `√det Gram(vᵢ) = 1` (ON); antitone ⟹ ratio ≤ 1 at t=1.  KEY
     normalization fact (why the constant is exactly 1): `hypSn(q·ℓ, t) =
     sinh(qℓt)/(qℓ) ~ t` as t→0 (the ℓ cancels inside), so `hypDensity(q·ℓ)(n-1)(t)
     ~ t^{n-1}` and `curveDensity(transverse ON)(t) ~ t^{n-1}·1`.
  3. **step (b) — √det g_x cancels** — pointwise `expJacDensity v ≤ √det(g_x,x)·
     hypSn(q·|v|_{g_x},1)^{n-1}` (measurable RHS!).  Change variables `w = g_x^{1/2}v`
     (E-linear, |det g_x^{-1/2}| = 1/√det g_x): `|v|_{g_x}=|w|_E`,
     `closedGBall R ↦ E-ball R`, `d modelHaar(v) = (1/√det g_x) d modelHaar(w)`.
     `√det g_x · (1/√det g_x) = 1` — the √det cancels.
  4. **step (d) — E-polar** — `∫_{|w|_E≤R} hypSn(q|w|,1)^{n-1} dHaar` via
     `lintegral_polar` / `integral_fun_norm_addHaar` = `σ·∫₀^R r^{n-1}·
     hypSn(qr,1)^{n-1} dr`, and the polar `r^{n-1}` combines with
     `hypSn(qr,1)^{n-1} = sinh(qr)^{n-1}/(qr)^{n-1}` to give exactly
     `hypSn(q,r)^{n-1}`, so `= σ·∫₀^R hypSn(q,r)^{n-1} dr = σ·hypRadVol q (n-1) R`.
     `σ = (modelHaar E).toSphere univ = n·vol(unit ball)` (`toSphere_apply_univ`).

  *Remaining sub-lemmas (each substantial; the ORDER for next sessions):*
  - `radialJac_eq_vel` (SegmentGauss.lean — attempted, blocked only on an
    `mfderiv (1+·) 0 1 = 1` notation fiddle; route recorded in-file).
  - step (a) change-of-basis: `curveDensity(chartModelBasis)(1) = |det C|·
    curveDensity(adapted)(1)` (curveGram is `CᵀGC`; det = (det C)²·…) + `|det C| =
    √det g_x` for a gₓ-ON vs E-ON basis (linear algebra; likely near
    `RadialGram.gram_det_change`, but do it globally / for the intrinsic frame).
  - step (c) sharp: an `exists_intrRatio`-analogue taking a gₓ-ON perp frame as
    INPUT (the in-tree one CHOOSES the frame via `exists_perp_pos`), plus the
    pole-limit lemma `curveDensity(V)(t)/hypDensity(q·ℓ)(n-1)(t) → √det Gram(∇Jᵢ(0))`
    (reuse `intrPoleCap`/`densUB_of_pole` machinery, but SHARP not `N=M₀/c`).
  - step (b)+(d): the `g_x^{1/2}` change-of-variables (Mathlib
    `MeasurePreserving`/`addHaar` linear-map pushforward, |det| = 1/√det g_x) and
    the E-polar assembly (`lintegral_polar`, `radial_lintegral_eq`,
    `toSphere_apply_univ`).

  Obstruction class: **missing reusable API** (from-scratch Bishop–Gromov absolute
  bound), NOT a local proof-search gap or wrong statement.  The statements are
  correct (anisotropy-robust; the telescope above is the proof of that).  Do NOT
  weaken them.

- **2026-07-25 (B5c) — frontier MOVED; L5 landed, L6/L7 remain.**  The B2-era
  "missing bridge" (the manifold non-injective area inequality) is now
  **in-tree and sorry-free**: `riemVol_exp_image_le` in `SegmentArea.lean`
  (`riemannianVolumeMeasure g (exp x '' K) ≤ ∫⁻ v in K, ofReal(curveDensity …)`
  for compact `K`, axioms `[propext, Classical.choice, Quot.sound]` only).  The
  fictional `expMap_contMDiffAt_of_ne_zero` citation is removed — off-zero
  velocity regularity is `intrinsicFiber_smooth`/`expChart_contDiffAt` (global
  `C^∞`).  Both `segBall_vol_le`/`segBall_vol_rel` remain `sorry` (statements
  UNCHANGED); the file's "frontier"/"Smallest unblocking lemma" sections below
  are SUPERSEDED by the header's updated route.  **Remaining frontier (L6):** the
  absolute Bishop bound `∫⁻ v in SegDom ∩ closedGBall R, ofReal(curveDensity v)
  ∂modelHaar ≤ σ·hypRadVol` — NOT assembly (no absolute `V ≤ σ·hypRadVol`
  template exists in ANY regime; the diffeo regime is polar-EQUALITY +
  RELATIVE-ratio only).  Needs: (a) GLOBAL Gauss block-det split
  (full n-frame → radial × transverse; `intrinsic_gauss` gives the global
  orthogonality, but `endpoint_det_split`/`density_det_eq` are chart-scale +
  `private` in `RadialGram.lean` → redo past the cut locus); (b) the `√det(gₓ)`
  E-vs-`gₓ`-Haar constant reconciling `modelHaar.toSphere` (E-sphere) with the
  `gₓ`-arclength model; (c) a **SHARP `N=1`** transverse bound (in-tree
  `intrDens_le_hyp` is non-sharp `N=M₀/c`; sharp needs `exists_intrFrame`'s
  `gₓ`-orthonormal parallel frame with pole ratio → 1); (d) `lintegral_polar`
  integration to `σ·hypRadVol`.  **L7** (`segBall_vol_rel`) further needs the
  truncated polar (`τ(θ)`) + `lintegral_cross_le` (B4) + injectivity of
  `expMapIntrinsic` on the open minimizing interior.  Blocker class = missing
  reusable API (from-scratch Bishop–Gromov absolute/relative bound), not a local
  proof-search gap.  compact-`K` helper attempted but hit the TangentSpace-vs-E
  norm trap (see `SegmentArea.md`); do it with the g-norm (`hEnorm` gives
  `‖v‖ = √(g.inner x v v)`, so `closedGBall = closedBall`) under the
  `attribute [-instance]` header, NOT E-norm coercivity.

- 2026-07-25 (post-review): file compiles GREEN.  `segBall_vol_le` (corrected
  with `σ`) + `segBall_vol_rel` are the two `sorry` frontiers; `segBall_vol_fin`
  is PROVED (corollary, transitively sorry-dependent on `segBall_vol_le`).
  Targeted build passed.
- 2026-07-25 (initial): file compiles GREEN with the two intended `sorry`s (frontier).
  Statements typecheck against the sorry-free `SegmentDomain.lean` and the
  Bishop model-volume API.  Instance setup mirrors `SegmentDomain.lean`
  (file-level base + `I.Boundaryless` + `T2Space M` + `T2Space (TangentBundle I M)`
  + `SigmaCompactSpace M` + `RiemannianBundle`; per-theorem emetric quartet +
  `ConnectedSpace`; per-theorem `attribute [-instance] Tensor0SBundle.tangentSpace_*`
  — WITHOUT the attribute the fibre `InnerProductSpace` family fails to synth).
