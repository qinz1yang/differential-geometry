# IntrinsicRatio.lean — B3 (§5 (β) ratio monotonicity) notes

Brick B3 of `C4/A0PRIME_VOLUME_PLAN.md` §5: thin consumer-facing adapters on
the intrinsic Bishop ratio layer.  New reusable producer lives in
`BishopIntrinsic.lean` (needs its `private` setup helpers); consumer deliverables
in this file (`IntrinsicRatio.lean`).

## Parametrization / convention (recorded per brick instruction)

- `γ = intrinsicGeodesic g hEnorm p u` runs unit-interval-style; its constant
  speed-square is `g.inner p u u`, so length `ℓ = √(g.inner p u u)`
  (`intrinsicGeodesic_speedSq_eq`).
- The model comparison is scaled by the speed: the ratio and mean-curvature
  bounds use `hypDensity (q * ℓ) d` and `hypMeanCurv (q * ℓ) d`, NOT `hypDensity q d`.
  This is the TRUE form (`curveMean_le_hyp` concludes `≤ hypMeanCurv (q*a) d` with
  `a = ℓ`); no `q` vs `q·ℓ` fudge.  `d = finrank ℝ E - 1` = transverse dimension.
- Ricci hypothesis: `RicciBoundedBelow g (-((finrank-1) * q^2))` (the `-(n-1)q²`
  form), consumed verbatim by `curveMean_le_hyp`.

## Deliverables

1. `intrDens_le_hyp` (PRIORITY; B2 imports): pointwise upper density
   `curveDensity g γ V t ≤ N · hypDensity (q·ℓ) d t` on `Ioo 0 b`, positive `N`.
   STATUS: **UNCONDITIONAL, sorry-free.**  `densUB_of_pole` (antitone→pointwise,
   the ratio sup is at the pole — fully proved) ∘ `intrPoleCap` (near-pole cap,
   DISCHARGED via the chart bridge — see "Pole frontier: CLOSED" below).
2. `intrCross_anti` (B4/B5-facing): cross-multiplicative / division-free antitone
   `curveDensity b' · hypDensity a' ≤ curveDensity a' · hypDensity b'` for
   `0 < a' ≤ b'` in the window.  FULLY PROVED from `exists_intrRatio` + hypDensity
   positivity.  No pole input.
3. `intrNoConj_min` (glue): `∀ t ∈ Ioo 0 b, ¬ IsConjVec …` from `tail_no_conj`
   (`Ioc 0 1 ⊇ Ioo 0 1`).  Independent of B2's SegDom names.

## Producer

`exists_intrRatio` (added to BishopIntrinsic.lean, END): companion to
`exists_intrMean`.  Same transverse-Jacobi setup (reuses the file's `private`
`intr*` helpers + `radialRatio_auto` + `intrJacobi_raw`), but concludes the
antitone density ratio via `curveRatio_anti ∘ curveMean_le_hyp` instead of the
`t = 1` mean value.  Requires `hd : 0 < finrank-1` (drops `exists_intrMean`'s
`d=0` branch — dimension ≥ 2 in every BG use) and only `hb : 0 < b` (not `1 < b`;
`exists_intrMean` needed `1<b` solely to place `t=1`).  Window `Ioo 0 b`,
nonconjugacy `hno` on the same window, exactly like `exists_intrMean`.

## Pole frontier: CLOSED

The antitone ratio `R t = curveDensity/hypDensity` has sup = its `t→0⁺` limit,
so a uniform `curveDensity ≤ N·hypDensity` on `Ioo 0 b` needs an UPPER bound of
`R` near the pole.  The tree has ONLY the lower/monotone apparatus as a
STANDALONE lemma (`radialRatio_auto` = `C ≤ R`); no light near-pole upper cap
exists.  BUT the discharge assembles cleanly from PUBLIC pieces (`intrPoleCap`,
sorry-free):

1. `exists_perp_basis` (private, added here): `u` + orthogonal `LinearIndependent`
   family `v` ⟹ `Option`-basis `B` of `E`, `B none = u`, `B (some i) = v i`, via
   `LinearIndependent.option` (the `u ∉ span v` proof uses `g.inner p u ·`
   vanishing on `span v` but `> 0` at `u`) + `basisOfLinearIndependentOfCardEqFinrank`.
   Built over `TangentSpace I p`, concluded over `E` by defeq — compiles.
2. `normalDensity_curve` (PUBLIC) on a small window `Ioo 0 b₀` (`b₀ =
   expMapC2Radius / ‖ue‖`) gives `t^d · normalChartDensity(t•u) = c · curveDensity_radial`.
3. `normalChartDensity` `ContinuousAt 0` re-derived from PUBLIC `paramDensity_contOn`
   (`ContinuousOn` on the whole source, no chart hypothesis) ⟹ `∀ᶠ w, ncd w < ncd 0 + 1`.
4. `hypDens_ge_pow` (`hypSn q t ≥ t` via `Real.self_le_sinh`) ⟹ `hypDensity ≥ t^d`.
5. `intrJacobi_raw` transfers curve/Jacobi equality intrinsic↔radial near 0.
   Assembles to `R t ≤ (ncd 0 + 1)/c =: N` eventually; then `densUB_of_pole`.

KEY LESSON (type-synonym norm trap): `‖r • (u : E)‖` with `u : TangentSpace I p`
picks the **Riemannian-metric** norm instance, NOT `E`'s Euclidean norm the chart
lemmas need (`instNormedAddCommGroupOfRiemannianBundle…` vs `E`'s). Passing
`(u : E)` INTO a function whose parameter is `E` forces `E`'s instances (works);
computing the norm YOURSELF does not.  Fix: bind a genuine `let ue : E := (u : E)`
and use `ue`.  Do NOT `set ue := (u : E)` — `(u:E)` reduces to `u`, so `set`
folds every `u` (corrupts `g.inner p u u`).

## Verification status

**Targeted `lake build` PASSED, sorry-free** (2026-07-25) for both edited modules.
Only pre-existing `HopfRinow.lean` sorrys remain in the dependency graph (B0-known,
not ours).  All of `exists_intrRatio` (BishopIntrinsic.lean) and
`exists_perp_basis` / `hypSn_ge_id` / `hypDens_ge_pow` / `intrPoleCap` /
`densUB_of_pole` / `intrDens_le_hyp` / `intrCross_anti` / `intrNoConj_min`
(IntrinsicRatio.lean) verify. No new axioms.

Lemma-name / elaboration notes (this Mathlib): cross-multiplication is
`div_le_div_iff₀` (NOT `div_le_div_iff`, removed); `lt_div_iff₀`, `div_le_iff₀`,
`Ioo_mem_nhdsGT`, `Set.Ioo_subset_Ioc_self`, `norm_pos_iff`,
`Module.finrank_pos_iff`, `basisOfLinearIndependentOfCardEqFinrank` /
`coe_basisOfLinearIndependentOfCardEqFinrank`, `LinearIndependent.option`,
`Option.casesOn'` all resolve.  `AntitoneOn`-applied results come out as
beta-redexes `(fun t => …) t` — ascribe the reduced type before `rw`.  `open
DifferentialGeometry.Geometry.Riemannian.NormalCoordinates` +
`DifferentialGeometry.Integral.Measure` needed for `expMapDiffeo` / `paramDensity_*`.
`ContinuousAt` used directly as `Tendsto` (`hcontAt (Iio_mem_nhds …)`) to dodge
higher-order `apply` unification.
