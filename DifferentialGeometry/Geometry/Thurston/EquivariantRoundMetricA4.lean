import DifferentialGeometry.Geometry.Thurston.EquivariantRoundMetricA3
import DifferentialGeometry.Geometry.Thurston.EquivariantRoundMetricA4Packing

/-!
# Diameter and lower scalar curvature bound for a positively curved surface flow

Chapter 7, packet P8, surface lemma U1, route (a), lane a4 (review 17 §4.5). For a Ricci flow on
`[0, T)` on a compact connected surface with positive initial scalar curvature, with
`C₀ = ∫ R dμ`, `A₀ = Area` at time `0` and `T* = A₀ / C₀`; no maximality is assumed.

* `surfaceFlow_scalar_ge_of_initial`: a lower bound of `R(0, ·)` persists, by the ODE comparison
  for the heat-potential supersolution `R` (`∂ₜ R = Δ R + R²`) with a constant barrier.
* `surfaceFlow_normalized_diam_le`: for `T* / 2 ≤ t`, `d_{g(t)} ≤ D √(T* - t)`. With
  `r² = ε (T* - t)`, the upper bound `R ≤ C / (2 (T* - t))` of
  `surfaceFlow_normalized_scalar_upper` on the backward window `[t - r², t]` gives
  `r⁴ |Rm|² ≤ 1`, so non-collapsing bounds the area of `r`-balls below by `κ r²`, while
  `Area (g t) = C₀ (T* - t)`; `riemannianEDistOf_toReal_lt_of_ball_volume` concludes.
* `surfaceFlow_normalized_scalar_lower`: `R(t, x) · 2 (T* - t) ≥ c > 0`. For `t ≥ 3 T* / 4` put
  `t₁ = 2 t - T*`; at a maximum point `x₁` of `R(t₁, ·)` the mean value gives
  `R(t₁, x₁) · 2 (T* - t₁) ≥ 2`, and Harnack from `(t₁, x₁)` with origin `t₁ / 2` and the diameter
  bound at `t₁` reach every `(t, y)`. Earlier times use `R ≥ min R(0, ·)` and `T* - t ≥ T* / 4`.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Tensor0SBundle
open MeasureTheory Filter Topology Set
open scoped Manifold ContDiff ENNReal

namespace GC.Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [CompactSpace M] [ConnectedSpace M]
  {T : ℝ} {hT : 0 < T}

private local instance a4Measurable : MeasurableSpace M := borel M
private local instance a4Borel : BorelSpace M := ⟨rfl⟩

omit [CompactSpace M] [ConnectedSpace M] in
theorem surfaceFlow_scalar_heatSupersolution (hdim : Module.finrank ℝ E = 2)
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S) :
    IsHeatPotSupersolutionOn D (flowG S) (fun s x => S.scalar s x) (fun s x => S.scalar s x) where
  jointSmooth := scalar_joint S hS
  jointCont := hS.scalarCont
  sliceSmooth := fun t _ => scalarSmoothOfSolution S t
  timeDiff := fun t ht x => (surfaceScalar_hasDerivAt S hS hdim ht x).differentiableAt
  equation_ge := by
    intro t ht x
    rw [(surfaceScalar_hasDerivAt S hS hdim ht x).deriv]
    have hlap : laplacianAt (flowG S) t (S.scalar t) x =
        ΔG (S.family.metric t) ⟨S.scalar t, scalarSmoothOfSolution S t⟩ x :=
      laplacian_levi_eq (S.family.metric t) (scalarSmoothOfSolution S t) x
    rw [hlap]
    nlinarith

omit [ConnectedSpace M] in
theorem surfaceFlow_scalar_ge_of_initial (hdim : Module.finrank ℝ E = 2)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT)) (hS : IsSolutionOn S)
    {m : ℝ} (hm : ∀ x, m ≤ S.scalar 0 x) {t : ℝ} (ht : t ∈ Ico 0 T) (x : M) :
    m ≤ S.scalar t x := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  rcases ht.1.eq_or_lt with h0 | _
  · rw [← h0]
    exact hm x
  let U := S.timeRestrict (RealTimeInterval.closed 0 t ht.1)
  have hU : IsSolutionOn U := isSolutionOn_timeRestrict hS
    (fun s hs => (⟨hs.1, lt_of_le_of_lt hs.2 ht.2⟩ : s ∈ Ico 0 T))
    (fun s hs => (⟨hs.1, hs.2.trans ht.2⟩ : s ∈ Ioo 0 T))
  have hcmp := scalar_weak_maximum_principle_ode_compare_supersolution_autonomous_of_heat_pot
    (flowG U) t ht.1 (fun s y => U.scalar s y) (fun _ => m) (fun _ => 0) 0 _
    (surfaceFlow_scalar_heatSupersolution hdim U hU) continuousOn_const
    (fun _ _ _ => differentiableWithinAt_const _)
    (fun _ _ y => mul_self_nonneg _)
    (fun _ _ _ => by simp)
    (fun y => hm y)
    (fun _ _ => (LipschitzWith.const 0).lipschitzOnWith)
  exact hcmp t ⟨ht.1, le_rfl⟩ x

omit [I.Boundaryless] [ConnectedSpace M] in
theorem exists_totalScalarCurvature_le_scalar_mul_area (g : SmoothRiemannianMetric I M)
    [Nonempty M] : ∃ x, totalScalarCurvature g ≤ metricScalarAt g x * surfaceArea g := by
  obtain ⟨x, -, hx⟩ := isCompact_univ.exists_isMaxOn (Set.univ_nonempty (α := M))
    (metricScalar_smooth g).continuous.continuousOn
  refine ⟨x, ?_⟩
  let μ := riemannianVolumeMeasure I M g
  let _ : IsFiniteMeasure μ :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  have hint : Integrable (metricScalarAt g) μ :=
    (metricScalar_smooth g).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  calc totalScalarCurvature g = ∫ y, metricScalarAt g y ∂μ := rfl
    _ ≤ ∫ _y, metricScalarAt g x ∂μ :=
        integral_mono hint (integrable_const _) fun y => hx (Set.mem_univ y)
    _ = metricScalarAt g x * surfaceArea g := by
        rw [integral_const, smul_eq_mul, mul_comm]
        rfl

theorem surfaceFlow_normalized_diam_le (hdim : Module.finrank ℝ E = 2)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT)) (hS : IsSolutionOn S)
    (hscal : ∀ x, 0 < S.scalar 0 x) :
    ∃ D : ℝ, 0 < D ∧ ∀ t ∈ Ico 0 T,
      surfaceArea (S.family.metric 0) / totalScalarCurvature (S.family.metric 0) / 2 ≤ t →
      ∀ x y : M, riemannianEDistOf (S.family.metric t) x y ≤
        ENNReal.ofReal (D * Real.sqrt (surfaceArea (S.family.metric 0) /
          totalScalarCurvature (S.family.metric 0) - t)) := by
  obtain ⟨C, hC⟩ := surfaceFlow_normalized_scalar_upper hdim S hS hscal
  obtain ⟨κ, hκ, hvol⟩ := surfaceFlow_exists_ball_volume_lower hdim S hS one_pos
  set C₀ := totalScalarCurvature (S.family.metric 0)
  set A₀ := surfaceArea (S.family.metric 0)
  have hC₀ : 0 < C₀ := totalScalarCurvature_pos _ hscal
  set Tst := A₀ / C₀ with hTst
  have hTT : T ≤ Tst := surfaceFlow_le_extinctionTime hT S hS hdim hscal
  have hTstpos : 0 < Tst := hT.trans_le hTT
  set C' := max C 1
  have hC' : 0 < C' := lt_of_lt_of_le one_pos (le_max_right _ _)
  set ε := 1 / (1 + Tst + C') with hεdef
  have hε : 0 < ε := by positivity
  have hεT : ε * Tst ≤ 1 := by
    rw [hεdef, div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
    linarith
  have hεC : ε * C' ≤ 1 := by
    rw [hεdef, div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
    linarith
  have hε1 : ε ≤ 1 := by
    rw [hεdef, div_le_one (by positivity)]
    linarith
  refine ⟨2 * C₀ / (κ * Real.sqrt ε), by positivity, fun t ht htlow x y => ?_⟩
  set s := Tst - t with hsdef
  have hs : 0 < s := by linarith [ht.2]
  have htpos : 0 < t := lt_of_lt_of_le (by positivity) htlow
  set r := Real.sqrt (ε * s) with hrdef
  have hr : 0 < r := Real.sqrt_pos.mpr (by positivity)
  have hr2 : r ^ 2 = ε * s := Real.sq_sqrt (by positivity)
  have hr1 : r ≤ 1 := by
    rw [hrdef, Real.sqrt_le_one]
    calc ε * s ≤ ε * Tst := mul_le_mul_of_nonneg_left (by linarith [ht.1]) hε.le
      _ ≤ 1 := hεT
  have hrt : r ^ 2 ≤ t := by
    rw [hr2]
    calc ε * s ≤ 1 * s := mul_le_mul_of_nonneg_right hε1 hs.le
      _ ≤ t := by rw [hsdef]; linarith
  have hcurv : ∀ u ∈ Icc (t - r ^ 2) t, ∀ z,
      r ^ 4 * normSq0S (S.family.metric u) z 4 (metricRm04At (S.family.metric u) z) ≤ 1 := by
    intro u hu z
    rw [normSq0S_metricRm04At_eq_sq_of_finrank_two hdim]
    have hu0 : u ∈ Ico 0 T := ⟨by linarith [hu.1], lt_of_le_of_lt hu.2 ht.2⟩
    have hRpos : 0 < S.scalar u z := surfaceFlow_scalar_pos S hS hscal hu0 z
    have hRu := (hC u hu0 z).trans (le_max_left C 1)
    have hgap : s ≤ Tst - u := by rw [hsdef]; linarith [hu.2]
    have hRs : S.scalar u z * (2 * s) ≤ C' :=
      (mul_le_mul_of_nonneg_left (by linarith) hRpos.le).trans hRu
    have hrR : r ^ 2 * S.scalar u z ≤ 1 / 2 := by
      rw [hr2]
      have : ε * s * S.scalar u z = ε * (S.scalar u z * (2 * s)) / 2 := by ring
      rw [this, div_le_div_iff_of_pos_right (by norm_num)]
      calc ε * (S.scalar u z * (2 * s)) ≤ ε * C' := mul_le_mul_of_nonneg_left hRs hε.le
        _ ≤ 1 := hεC
    have hnn : 0 ≤ r ^ 2 * S.scalar u z := by positivity
    have : r ^ 4 * metricScalarAt (S.family.metric u) z ^ 2 = (r ^ 2 * S.scalar u z) ^ 2 := by
      change r ^ 4 * S.scalar u z ^ 2 = _
      ring
    rw [this]
    nlinarith
  have hball : ∀ z, ENNReal.ofReal (κ * r ^ 2) ≤
      riemannianVolumeMeasure I M (S.family.metric t)
        {w | riemannianEDistOf (S.family.metric t) z w < ENNReal.ofReal r} := by
    intro z
    rw [ENNReal.ofReal_mul hκ.le, ENNReal.ofReal_pow hr.le]
    exact hvol t ⟨htpos, ht.2⟩ z r hr hr1 hrt hcurv
  have hpack := riemannianEDistOf_toReal_lt_of_ball_volume (S.family.metric t) hr
    (by positivity) hball x y
  have hA : surfaceArea (S.family.metric t) = C₀ * s := by
    rw [surfaceFlow_area_eq_initial_sub hT S hS hdim ht, hsdef, hTst]
    field_simp
    ring
  rw [hA] at hpack
  have hsq : Real.sqrt (ε * s) = Real.sqrt ε * Real.sqrt s := Real.sqrt_mul hε.le s
  have hss : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs.le
  have hsqε : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  have hsqs : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have heq : 2 * r * (C₀ * s / (κ * r ^ 2)) = 2 * C₀ / (κ * Real.sqrt ε) * Real.sqrt s := by
    rw [hrdef, hsq]
    field_simp
    rw [hss]
  rw [heq] at hpack
  rw [← ENNReal.ofReal_toReal (riemannianEDistOf_ne_top (S.family.metric t) x y)]
  exact ENNReal.ofReal_le_ofReal hpack.le

theorem surfaceFlow_normalized_scalar_lower (hdim : Module.finrank ℝ E = 2)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT)) (hS : IsSolutionOn S)
    (hscal : ∀ x, 0 < S.scalar 0 x) :
    ∃ c : ℝ, 0 < c ∧ ∀ t ∈ Ico 0 T, ∀ x, c ≤ S.scalar t x *
      (2 * (surfaceArea (S.family.metric 0) / totalScalarCurvature (S.family.metric 0) - t)) := by
  obtain ⟨D, hD, hdiam⟩ := surfaceFlow_normalized_diam_le hdim S hS hscal
  set C₀ := totalScalarCurvature (S.family.metric 0)
  set A₀ := surfaceArea (S.family.metric 0)
  have hC₀ : 0 < C₀ := totalScalarCurvature_pos _ hscal
  set Tst := A₀ / C₀ with hTst
  have hTT : T ≤ Tst := surfaceFlow_le_extinctionTime hT S hS hdim hscal
  have hTstpos : 0 < Tst := hT.trans_le hTT
  obtain ⟨x₀, -, hx₀⟩ := isCompact_univ.exists_isMinOn (Set.univ_nonempty (α := M))
    (scalarSmoothOfSolution S 0).continuous.continuousOn
  set m₀ := S.scalar 0 x₀
  have hm₀ : 0 < m₀ := hscal x₀
  have hge : ∀ t ∈ Ico 0 T, ∀ x, m₀ ≤ S.scalar t x := fun t ht x =>
    surfaceFlow_scalar_ge_of_initial hdim S hS (fun y => hx₀ (Set.mem_univ y)) ht x
  refine ⟨min (Real.exp (-(D ^ 2 / 2)) / 3) (m₀ * Tst / 2), by positivity, fun t ht x => ?_⟩
  have hgap : 0 < Tst - t := by linarith [ht.2]
  by_cases hlate : 3 * Tst / 4 ≤ t
  swap
  · push Not at hlate
    refine (min_le_right _ _).trans ?_
    have h1 : Tst / 2 ≤ 2 * (Tst - t) := by linarith
    calc m₀ * Tst / 2 = m₀ * (Tst / 2) := by ring
      _ ≤ S.scalar t x * (2 * (Tst - t)) :=
        mul_le_mul (hge t ht x) h1 (by positivity) (hm₀.le.trans (hge t ht x))
  refine (min_le_left _ _).trans ?_
  set t₁ := 2 * t - Tst with ht₁def
  have ht₁low : Tst / 2 ≤ t₁ := by rw [ht₁def]; linarith
  have ht₁pos : 0 < t₁ := lt_of_lt_of_le (by positivity) ht₁low
  have ht₁t : t₁ < t := by rw [ht₁def]; linarith [ht.2]
  have ht₁ : t₁ ∈ Ico 0 T := ⟨ht₁pos.le, ht₁t.trans ht.2⟩
  have hgap₁ : Tst - t₁ = 2 * (Tst - t) := by rw [ht₁def]; ring
  have hdt : t - t₁ = Tst - t := by rw [ht₁def]; ring
  obtain ⟨x₁, hx₁⟩ := exists_totalScalarCurvature_le_scalar_mul_area (S.family.metric t₁)
  rw [surfaceFlow_totalScalarCurvature_eq_initial hT S hS hdim ht₁,
    surfaceFlow_area_eq_initial_sub hT S hS hdim ht₁] at hx₁
  have hA₁ : A₀ - C₀ * t₁ = C₀ * (Tst - t₁) := by
    rw [hTst]
    field_simp
  change C₀ ≤ S.scalar t₁ x₁ * (A₀ - C₀ * t₁) at hx₁
  rw [hA₁] at hx₁
  have hR₁ : 1 ≤ S.scalar t₁ x₁ * (2 * (Tst - t)) := by
    rw [← hgap₁]
    have : C₀ * 1 ≤ C₀ * (S.scalar t₁ x₁ * (Tst - t₁)) := by linarith
    exact le_of_mul_le_mul_left this hC₀
  set o := t₁ / 2 with hodef
  have ho : 0 < o := by positivity
  have ho₁ : o < t₁ := by rw [hodef]; linarith
  have hh := surfaceFlow_harnack hdim S hS hscal ho ho₁ ht₁t ht.2 x₁ x
  set d := (riemannianEDistOf (S.family.metric t₁) x₁ x).toReal with hddef
  have hd0 : 0 ≤ d := ENNReal.toReal_nonneg
  have hdD : d ≤ D * Real.sqrt (Tst - t₁) := by
    have hle := hdiam t₁ ht₁ ht₁low x₁ x
    have hDnn : 0 ≤ D * Real.sqrt (Tst - t₁) := mul_nonneg hD.le (Real.sqrt_nonneg _)
    exact ENNReal.toReal_le_of_le_ofReal hDnn hle
  have hd2 : d ^ 2 ≤ D ^ 2 * (2 * (Tst - t)) := by
    have h := pow_le_pow_left₀ hd0 hdD 2
    rw [mul_pow, Real.sq_sqrt (by linarith), hgap₁] at h
    exact h
  have harg : -(D ^ 2 / 2) ≤ -(d ^ 2 / (4 * (t - t₁))) := by
    rw [neg_le_neg_iff, hdt, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hE := Real.exp_le_exp.mpr harg
  have hcoef : 1 / 3 ≤ (t₁ - o) / (t - o) := by
    rw [le_div_iff₀ (by rw [hodef]; linarith), hodef]
    linarith
  have hR₁pos : 0 < S.scalar t₁ x₁ := surfaceFlow_scalar_pos S hS hscal ht₁ x₁
  have hmain : 1 / 3 * Real.exp (-(D ^ 2 / 2)) * S.scalar t₁ x₁ ≤ S.scalar t x :=
    le_trans (mul_le_mul_of_nonneg_right
      (mul_le_mul hcoef hE (Real.exp_pos _).le (by linarith)) hR₁pos.le) hh
  have h2 : 0 ≤ 2 * (Tst - t) := by positivity
  calc Real.exp (-(D ^ 2 / 2)) / 3 ≤
        1 / 3 * Real.exp (-(D ^ 2 / 2)) * (S.scalar t₁ x₁ * (2 * (Tst - t))) := by
        have hEpos := Real.exp_pos (-(D ^ 2 / 2))
        nlinarith
    _ = 1 / 3 * Real.exp (-(D ^ 2 / 2)) * S.scalar t₁ x₁ * (2 * (Tst - t)) := by ring
    _ ≤ S.scalar t x * (2 * (Tst - t)) := mul_le_mul_of_nonneg_right hmain h2

end GC.Geometry
