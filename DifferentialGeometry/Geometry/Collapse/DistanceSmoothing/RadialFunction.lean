import DifferentialGeometry.Geometry.Collapse.DistanceSmoothing.LocalizedDistanceSmoothing
import DifferentialGeometry.Geometry.Collapse.RadialFunctionBand
import DifferentialGeometry.Geometry.Collapse.RadialAnnularCutoff

/-!
# LC30, LC67 (existence) and LC31 (at a supplied cone scale) from LC28

Compositions of lane W3-F4's accepted tiers with LC28 (`exists_localized_point_distance_smoothing`,
`θ = ε / 4`); no new hypotheses beyond the rows' own.

* `exists_radialFunction_of_kleinerLottApprox` — **LC30** (A:21214–21268) with the explicit cone
  error `δ₀ = radialSmoothingConeError (ε / 4)`: W3-F4's tier 1
  (`minimizingDirectionsTo_pairwise_lt_of_kleinerLottApprox`) verifies LC28's hypothesis on
  `U = {1/20 < d_p < 20}`, LC28 produces `η`, and W3-F4's tier 2 (`radialFunction_of_smoothing`)
  gives the LC30 conclusions.
* `exists_coneError_radialFunction` — LC30 in the row's `∀ ε ∃ δ₀` form.
* `exists_buffered_radialFunction_of_kleinerLottApprox` — the existence half of **LC67**
  (A:23899–23945): the same `η`, smooth near the buffered shell `C⁺ = {3/40 ≤ d_p ≤ 11}`.
* `exists_annularCutoff_of_kleinerLottApprox` — **LC31 at a supplied cone scale**: the LC30 `η`
  together with `ζ = Φ ∘ η` (W3-F4's `annularCutoff cutoffProfile`), globally smooth, compactly
  supported, `[0,1]`-valued, one on `η⁻¹[3/10, 4/5]`, topologically supported in
  `{1/5 - e < d_p < 9/10 + e}`, with `‖∇ζ‖ ≤ L_Φ (1 + ε)`, `L_Φ = sup |Φ'|`. The eventual choice of
  the scale (LC24: `r_p^0 ∈ [Tρ, Vρ]` for all `α > α₀`) is not included: LC24 is blocked on the
  Tits-cone producer (sheet-W3-F4 Addendum 3).
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Real
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Topology
open DifferentialGeometry.Analysis.Calculus
open GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] [ChartedSpace H M]
  [IsManifold I ∞ M] in
theorem isOpen_radialShell (p : M) (a b : ℝ) : IsOpen {x : M | a < dist x p ∧ dist x p < b} :=
  (isOpen_lt continuous_const (continuous_id.dist continuous_const)).inter
    (isOpen_lt (continuous_id.dist continuous_const) continuous_const)

/-- **LC30**: a radial function and its noncritical level band, with the explicit cone error
`radialSmoothingConeError (ε / 4)`. -/
theorem exists_radialFunction_of_kleinerLottApprox (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm g) {p : M} {C : Type*} [MetricSpace C] {o : C} {δ ε e : ℝ}
    (φ : KleinerLottApprox p o δ) (H : RadialConeData o)
    (hsec : ∀ y ∈ Metric.ball p 400, SectionalBoundedBelowAt g y (-(1 / 60) ^ 2))
    (hε : 0 < ε) (hε1 : ε < 1) (hδ : δ < radialSmoothingConeError (ε / 4)) (he : 0 < e)
    (he1 : e < 1 / 40) :
    ∃ F : M → ℝ, LipschitzWith (Real.toNNReal (1 + ε)) F ∧
      (∃ O : Set M, IsOpen O ∧ {x : M | 1 / 10 ≤ dist x p ∧ dist x p ≤ 10} ⊆ O ∧
        ContMDiffOn I 𝓘(ℝ, ℝ) ∞ F O) ∧
      (∀ x, |F x - Metric.infDist x {p}| < e) ∧
      (∀ x, x ∉ {x : M | 1 / 20 < dist x p ∧ dist x p < 20} → F x = Metric.infDist x {p}) ∧
      (∀ x y, |(F x - Metric.infDist x {p}) - (F y - Metric.infDist y {p})| ≤ ε * dist x y) ∧
      (∀ x, 0 ≤ F x) ∧ F p = 0 ∧
      (∀ q ∈ {x : M | 1 / 10 ≤ dist x p ∧ dist x p ≤ 10},
        1 - ε ≤ Real.sqrt (g.inner q (gradFun g F q) (gradFun g F q)) ∧
          Real.sqrt (g.inner q (gradFun g F q) (gradFun g F q)) ≤ 1 + ε) ∧
      (∀ x, F x ∈ Icc (1 / 5 : ℝ) 2 → 1 / 5 - e < dist x p ∧ dist x p < 2 + e) ∧
      F ⁻¹' Icc (1 / 5 : ℝ) 2 ⊆ {x : M | 1 / 10 ≤ dist x p ∧ dist x p ≤ 10} ∧
      ∃ O' : Set M, IsOpen O' ∧ F ⁻¹' Icc (1 / 5 : ℝ) 2 ⊆ O' ∧
        ContMDiffOn I 𝓘(ℝ, ℝ) ∞ F O' ∧ ∀ q ∈ O', gradFun g F q ≠ 0 := by
  have hpU : p ∉ {x : M | 1 / 20 < dist x p ∧ dist x p < 20} := by
    intro h
    have := h.1
    rw [dist_self] at this
    norm_num at this
  have hCc : IsCompact {x : M | 1 / 10 ≤ dist x p ∧ dist x p ≤ 10} :=
    (soul_isCompact_closedBall (I := I) g hEnorm p 10).of_isClosed_subset
      ((isClosed_le continuous_const (continuous_id.dist continuous_const)).inter
        (isClosed_le (continuous_id.dist continuous_const) continuous_const))
      (fun x hx => Metric.mem_closedBall.mpr hx.2)
  have hCU : {x : M | 1 / 10 ≤ dist x p ∧ dist x p ≤ 10} ⊆
      {x : M | 1 / 20 < dist x p ∧ dist x p < 20} := fun x hx =>
    ⟨by linarith [hx.1], by linarith [hx.2]⟩
  obtain ⟨F, O, hO, hCO, hFO, hclose, hout, hlip, hLip⟩ :=
    exists_localized_point_distance_smoothing g hEnorm hε (isOpen_radialShell p _ _) hpU
      (minimizingDirectionsTo_pairwise_lt_of_kleinerLottApprox g hEnorm φ H hsec
        (by positivity) hδ) hCc hCU he
  exact ⟨F, hLip, ⟨O, hO, hCO, hFO⟩, hclose, hout, hlip,
    radialFunction_of_smoothing g hEnorm p hε.le hε1 he1 hO hCO hFO hclose hout hlip⟩

/-- **LC30** in the row's form: for every `0 < ε < 1/4` there is `δ₀ > 0` (namely
`radialSmoothingConeError (ε / 4)`, independent of the manifold) such that every pointed
Kleiner–Lott `δ`-map, `δ < δ₀`, to an AC82 cone under `sec ≥ -(1/60)²` on `B(p, 400)` yields, for
every `0 < e < 1/40`, an LC30 radial function. -/
theorem exists_coneError_radialFunction (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    {ε : ℝ} (hε : 0 < ε) (hε4 : ε < 1 / 4) :
    ∃ δ₀ > 0, δ₀ = radialSmoothingConeError (ε / 4) ∧
      ∀ (p : M) (C : Type*) [MetricSpace C] (o : C) (δ : ℝ), KleinerLottApprox p o δ →
        RadialConeData o →
        (∀ y ∈ Metric.ball p 400, SectionalBoundedBelowAt g y (-(1 / 60) ^ 2)) → δ < δ₀ →
        ∀ e, 0 < e → e < 1 / 40 → ∃ F : M → ℝ, LipschitzWith (Real.toNNReal (1 + ε)) F ∧
          (∃ O : Set M, IsOpen O ∧ {x : M | 1 / 10 ≤ dist x p ∧ dist x p ≤ 10} ⊆ O ∧
            ContMDiffOn I 𝓘(ℝ, ℝ) ∞ F O) ∧
          (∀ x, |F x - Metric.infDist x {p}| < e) ∧
          (∀ x, x ∉ {x : M | 1 / 20 < dist x p ∧ dist x p < 20} →
            F x = Metric.infDist x {p}) ∧
          (∀ x y, |(F x - Metric.infDist x {p}) - (F y - Metric.infDist y {p})| ≤
            ε * dist x y) ∧
          (∀ x, 0 ≤ F x) ∧ F p = 0 ∧
          (∀ q ∈ {x : M | 1 / 10 ≤ dist x p ∧ dist x p ≤ 10},
            1 - ε ≤ Real.sqrt (g.inner q (gradFun g F q) (gradFun g F q)) ∧
              Real.sqrt (g.inner q (gradFun g F q) (gradFun g F q)) ≤ 1 + ε) ∧
          F ⁻¹' Icc (1 / 5 : ℝ) 2 ⊆ {x : M | 1 / 10 ≤ dist x p ∧ dist x p ≤ 10} ∧
          ∃ O' : Set M, IsOpen O' ∧ F ⁻¹' Icc (1 / 5 : ℝ) 2 ⊆ O' ∧
            ContMDiffOn I 𝓘(ℝ, ℝ) ∞ F O' ∧ ∀ q ∈ O', gradFun g F q ≠ 0 := by
  refine ⟨radialSmoothingConeError (ε / 4), radialSmoothingConeError_pos (by positivity), rfl,
    fun p C _ o δ φ H hsec hδ e he he1 => ?_⟩
  obtain ⟨F, h1, h2, h3, h4, h5, h6, h7, h8, -, h10, h11⟩ :=
    exists_radialFunction_of_kleinerLottApprox g hEnorm φ H hsec hε (by linarith) hδ he he1
  exact ⟨F, h1, h2, h3, h4, h5, h6, h7, h8, h10, h11⟩

/-- The existence half of **LC67**: the LC30 radial function can be chosen smooth near the
buffered shell `C⁺ = {3/40 ≤ d_p ≤ 11}`, with all LC30 conclusions. -/
theorem exists_buffered_radialFunction_of_kleinerLottApprox (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm g) {p : M} {C : Type*} [MetricSpace C] {o : C} {δ ε e : ℝ}
    (φ : KleinerLottApprox p o δ) (H : RadialConeData o)
    (hsec : ∀ y ∈ Metric.ball p 400, SectionalBoundedBelowAt g y (-(1 / 60) ^ 2))
    (hε : 0 < ε) (hε1 : ε < 1) (hδ : δ < radialSmoothingConeError (ε / 4)) (he : 0 < e)
    (he1 : e < 1 / 40) :
    ∃ F : M → ℝ, LipschitzWith (Real.toNNReal (1 + ε)) F ∧
      (∃ O : Set M, IsOpen O ∧ {x : M | 3 / 40 ≤ dist x p ∧ dist x p ≤ 11} ⊆ O ∧
        ContMDiffOn I 𝓘(ℝ, ℝ) ∞ F O) ∧
      (∀ x, |F x - Metric.infDist x {p}| < e) ∧
      (∀ x, x ∉ {x : M | 1 / 20 < dist x p ∧ dist x p < 20} → F x = Metric.infDist x {p}) ∧
      (∀ x y, |(F x - Metric.infDist x {p}) - (F y - Metric.infDist y {p})| ≤ ε * dist x y) ∧
      (∀ x, 0 ≤ F x) ∧ F p = 0 ∧
      (∀ q ∈ {x : M | 1 / 10 ≤ dist x p ∧ dist x p ≤ 10},
        1 - ε ≤ Real.sqrt (g.inner q (gradFun g F q) (gradFun g F q)) ∧
          Real.sqrt (g.inner q (gradFun g F q) (gradFun g F q)) ≤ 1 + ε) ∧
      (∀ x, F x ∈ Icc (1 / 5 : ℝ) 2 → 1 / 5 - e < dist x p ∧ dist x p < 2 + e) ∧
      F ⁻¹' Icc (1 / 5 : ℝ) 2 ⊆ {x : M | 1 / 10 ≤ dist x p ∧ dist x p ≤ 10} ∧
      ∃ O' : Set M, IsOpen O' ∧ F ⁻¹' Icc (1 / 5 : ℝ) 2 ⊆ O' ∧
        ContMDiffOn I 𝓘(ℝ, ℝ) ∞ F O' ∧ ∀ q ∈ O', gradFun g F q ≠ 0 := by
  have hpU : p ∉ {x : M | 1 / 20 < dist x p ∧ dist x p < 20} := by
    intro h
    have := h.1
    rw [dist_self] at this
    norm_num at this
  have hCc : IsCompact {x : M | 3 / 40 ≤ dist x p ∧ dist x p ≤ 11} :=
    (soul_isCompact_closedBall (I := I) g hEnorm p 11).of_isClosed_subset
      ((isClosed_le continuous_const (continuous_id.dist continuous_const)).inter
        (isClosed_le (continuous_id.dist continuous_const) continuous_const))
      (fun x hx => Metric.mem_closedBall.mpr hx.2)
  have hCU : {x : M | 3 / 40 ≤ dist x p ∧ dist x p ≤ 11} ⊆
      {x : M | 1 / 20 < dist x p ∧ dist x p < 20} := fun x hx =>
    ⟨by linarith [hx.1], by linarith [hx.2]⟩
  obtain ⟨F, O, hO, hCO, hFO, hclose, hout, hlip, hLip⟩ :=
    exists_localized_point_distance_smoothing g hEnorm hε (isOpen_radialShell p _ _) hpU
      (minimizingDirectionsTo_pairwise_lt_of_kleinerLottApprox g hEnorm φ H hsec
        (by positivity) hδ) hCc hCU he
  have hCO' : {x : M | 1 / 10 ≤ dist x p ∧ dist x p ≤ 10} ⊆ O := fun x hx =>
    hCO ⟨by linarith [hx.1], by linarith [hx.2]⟩
  exact ⟨F, hLip, ⟨O, hO, hCO, hFO⟩, hclose, hout, hlip,
    radialFunction_of_smoothing g hEnorm p hε.le hε1 he1 hO hCO' hFO hclose hout hlip⟩

/-- **LC31 at a supplied cone scale**: the LC30 radial function `η` and the cutoff
`ζ = Φ ∘ η` (`Φ = annularCutoff cutoffProfile`): `ζ` is globally smooth and compactly supported,
`0 ≤ ζ ≤ 1`, `ζ = 1` where `3/10 ≤ η ≤ 4/5`, `tsupport ζ ⊆ {1/5 - e < d_p < 9/10 + e}`, and
`‖∇ζ‖ ≤ L_Φ (1 + ε)` with `L_Φ = sup_t |Φ'(t)|`. -/
theorem exists_annularCutoff_of_kleinerLottApprox (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm g) {p : M} {C : Type*} [MetricSpace C] {o : C} {δ ε e : ℝ}
    (φ : KleinerLottApprox p o δ) (H : RadialConeData o)
    (hsec : ∀ y ∈ Metric.ball p 400, SectionalBoundedBelowAt g y (-(1 / 60) ^ 2))
    (hε : 0 < ε) (hε1 : ε < 1) (hδ : δ < radialSmoothingConeError (ε / 4)) (he : 0 < e)
    (he1 : e < 1 / 40) :
    ∃ F : M → ℝ, LipschitzWith (Real.toNNReal (1 + ε)) F ∧
      (∃ O : Set M, IsOpen O ∧ {x : M | 1 / 10 ≤ dist x p ∧ dist x p ≤ 10} ⊆ O ∧
        ContMDiffOn I 𝓘(ℝ, ℝ) ∞ F O) ∧
      (∀ x, |F x - Metric.infDist x {p}| < e) ∧
      (∀ x, x ∉ {x : M | 1 / 20 < dist x p ∧ dist x p < 20} → F x = Metric.infDist x {p}) ∧
      (∀ x y, |(F x - Metric.infDist x {p}) - (F y - Metric.infDist y {p})| ≤ ε * dist x y) ∧
      (∀ x, 0 ≤ F x) ∧ F p = 0 ∧
      (∀ q ∈ {x : M | 1 / 10 ≤ dist x p ∧ dist x p ≤ 10},
        1 - ε ≤ Real.sqrt (g.inner q (gradFun g F q) (gradFun g F q)) ∧
          Real.sqrt (g.inner q (gradFun g F q) (gradFun g F q)) ≤ 1 + ε) ∧
      F ⁻¹' Icc (1 / 5 : ℝ) 2 ⊆ {x : M | 1 / 10 ≤ dist x p ∧ dist x p ≤ 10} ∧
      ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x => annularCutoff cutoffProfile (F x)) ∧
      HasCompactSupport (fun x => annularCutoff cutoffProfile (F x)) ∧
      (∀ x, annularCutoff cutoffProfile (F x) ∈ Icc (0 : ℝ) 1) ∧
      (∀ x, F x ∈ Icc (3 / 10 : ℝ) (4 / 5) → annularCutoff cutoffProfile (F x) = 1) ∧
      tsupport (fun x => annularCutoff cutoffProfile (F x)) ⊆
        {x : M | 1 / 5 - e < dist x p ∧ dist x p < 9 / 10 + e} ∧
      ∀ q, Real.sqrt (g.inner q (gradFun g (fun x => annularCutoff cutoffProfile (F x)) q)
        (gradFun g (fun x => annularCutoff cutoffProfile (F x)) q)) ≤
          (⨆ t, |deriv (annularCutoff cutoffProfile) t|) * (1 + ε) := by
  have : ProperSpace M := ⟨soul_isCompact_closedBall (I := I) g hEnorm⟩
  obtain ⟨F, hLip, ⟨O, hO, hCO, hFO⟩, hclose, hout, hlip, hnn, hp0, hgrad, -, hsub, -⟩ :=
    exists_radialFunction_of_kleinerLottApprox g hEnorm φ H hsec hε hε1 hδ he he1
  obtain ⟨L, -, hL⟩ := exists_abs_deriv_annularCutoff_le cutoffProfile_contDiff
    fun _ ht => cutoffProfile_eq_zero ht
  have hbdd : BddAbove (range fun t => |deriv (annularCutoff cutoffProfile) t|) :=
    ⟨L, by rintro _ ⟨t, rfl⟩; exact hL t⟩
  have hLΦ : ∀ t, |deriv (annularCutoff cutoffProfile) t| ≤
      ⨆ t, |deriv (annularCutoff cutoffProfile) t| := fun t => le_ciSup hbdd t
  have hclose' : ∀ x, |F x - dist x p| < e := by
    intro x
    have := hclose x
    rwa [Metric.infDist_singleton] at this
  have hband : F ⁻¹' Icc (1 / 5 : ℝ) (9 / 10) ⊆ F ⁻¹' Icc (1 / 5 : ℝ) 2 :=
    fun x hx => ⟨hx.1, hx.2.trans (by norm_num)⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := annularCutoff_comp_radial cutoffProfile_contDiff
    cutoffProfile_mem_Icc (fun _ ht => cutoffProfile_eq_one ht)
    (fun _ ht => cutoffProfile_eq_zero ht) g p hε.le hLip.continuous hO hFO
    (fun x hx => hCO (hsub (hband hx))) hclose' (fun q hq => (hgrad q (hsub (hband hq))).2) hLΦ
  exact ⟨F, hLip, ⟨O, hO, hCO, hFO⟩, hclose, hout, hlip, hnn, hp0, hgrad, hsub, h1,
    hasCompactSupport_annularCutoff_comp_radial (fun _ ht => cutoffProfile_eq_zero ht) p hclose',
    h2, h3, h4, h5⟩

end DifferentialGeometry.Geometry.Collapse
