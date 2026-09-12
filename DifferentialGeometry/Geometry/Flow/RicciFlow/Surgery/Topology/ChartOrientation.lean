import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.Homology
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.LinearOrientation
import DifferentialGeometry.Bundle.TangentSpace
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
import Mathlib.Analysis.Normed.Module.Convex



noncomputable section
open Set Filter Asymptotics
open scoped Topology
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_relative_derivative_bound {f : E → F}
    (L : E ≃L[ℝ] F) (hf : HasFDerivAt f L.toContinuousLinearMap 0)
    (hzero : f 0 = 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ Metric.ball (0 : E) ε,
      ‖f x - L x‖ ≤ (1 / 2 : ℝ) * ‖L x‖ := by
  have herr : (fun x : E => f x - L x) =o[𝓝 (0 : E)] (fun x : E => x) := by
    convert hf.isLittleO using 1
    · rfl
    · rfl
    · simp only [hzero, sub_zero]
      rfl
    · simp only [sub_zero]
  have hbig : (fun x : E => x) =O[𝓝 (0 : E)] (fun x : E => L x) := by
    apply Asymptotics.isBigO_iff.mpr
    refine ⟨‖L.symm.toContinuousLinearMap‖, Filter.Eventually.of_forall ?_⟩
    intro x
    have h := L.symm.toContinuousLinearMap.le_opNorm (L x)
    simpa only [ContinuousLinearEquiv.coe_coe, L.symm_apply_apply] using h
  exact Metric.eventually_nhds_iff_ball.mp
    ((herr.trans_isBigO hbig).bound (by norm_num : (0 : ℝ) < 1 / 2))

theorem derivative_blend_ne_zero {f : E → F}
    (L : E ≃L[ℝ] F) (t : unitInterval) {x : E} (hx : x ≠ 0)
    (hbound : ‖f x - L x‖ ≤ (1 / 2 : ℝ) * ‖L x‖) :
    L x + (t : ℝ) • (f x - L x) ≠ 0 := by
  have hL : L x ≠ 0 := fun h => hx (L.injective (h.trans (map_zero L).symm))
  have hsmall : ‖(t : ℝ) • (f x - L x)‖ < ‖L x‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg t.property.1]
    calc
      (t : ℝ) * ‖f x - L x‖ ≤ ‖f x - L x‖ :=
        mul_le_of_le_one_left (norm_nonneg _) t.property.2
      _ ≤ (1 / 2 : ℝ) * ‖L x‖ := hbound
      _ < ‖L x‖ := by nlinarith [norm_pos_iff.mpr hL]
  intro h
  have heq : (t : ℝ) • (f x - L x) = -L x := by
    rw [add_comm] at h
    exact add_eq_zero_iff_eq_neg.mp h
  rw [heq, norm_neg] at hsmall
  exact (lt_irrefl _ hsmall)

theorem exists_punctured_derivative_deformation {f : E → F}
    (L : E ≃L[ℝ] F) (hf : HasFDerivAt f L.toContinuousLinearMap 0)
    (hzero : f 0 = 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : unitInterval, ∀ x ∈ Metric.ball (0 : E) ε,
      x ≠ 0 → L x + (t : ℝ) • (f x - L x) ≠ 0 := by
  obtain ⟨ε, hε, hb⟩ := exists_relative_derivative_bound L hf hzero
  exact ⟨ε, hε, fun t x hx hne => derivative_blend_ne_zero L t hne (hb x hx)⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology


noncomputable section
open Set Metric
open scoped Topology
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

theorem compact_family_small_scaling
    {P E : Type*} [TopologicalSpace P] [CompactSpace P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : C(P, E))
    {U : Set E} (hU : IsOpen U) {a : E} (ha : a ∈ U) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ r ∈ Icc (0 : ℝ) ε, ∀ p : P, a + r • f p ∈ U := by
  obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds ha)
  obtain ⟨C, hC⟩ := (isCompact_range f.continuous.norm).bddAbove
  let B : ℝ := max C 0 + 1
  have hB : 0 < B := by dsimp [B]; positivity
  have hb (p : P) : ‖f p‖ ≤ B :=
    (hC (mem_range_self p)).trans ((le_max_left C 0).trans (by dsimp [B]; linarith))
  let ε : ℝ := (δ / 2) / B
  have hε : 0 < ε := div_pos (half_pos hδ) hB
  refine ⟨ε, hε, ?_⟩
  intro r hr p
  apply hδU
  rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg hr.1]
  calc
    r * ‖f p‖ ≤ r * B := mul_le_mul_of_nonneg_left (hb p) hr.1
    _ ≤ ε * B := mul_le_mul_of_nonneg_right hr.2 hB.le
    _ = δ / 2 := div_mul_cancel₀ _ (ne_of_gt hB)
    _ < δ := half_lt_self hδ

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology


noncomputable section
open Bundle Manifold Set
open scoped Manifold ContDiff
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] {o : TangentOrientationSection M} {x : M}

private def simplexDerivativeEquiv (S : OrientedChartSimplex o x) :
    TangentSpace ThreeModel x ≃L[ℝ] ThreeSpace := by
  letI : T2Space (TangentSpace ThreeModel x) := inferInstanceAs (T2Space ThreeSpace)
  letI : T2Space (TangentSpace ThreeModel (S.chart x)) :=
    inferInstanceAs (T2Space ThreeSpace)
  letI : FiniteDimensional ℝ (TangentSpace ThreeModel x) :=
    inferInstanceAs (FiniteDimensional ℝ ThreeSpace)
  exact (LinearEquiv.ofBijective (mfderiv ThreeModel ThreeModel S.chart x).toLinearMap
    S.derivative_bijective).toContinuousLinearEquiv |>.trans
      (tangentSpaceModelContinuousLinearEquiv (I := ThreeModel) (S.chart x))

private def simplexDerivativeTransition (S T : OrientedChartSimplex o x) :
    ThreeSpace ≃L[ℝ] ThreeSpace :=
  (simplexDerivativeEquiv S).symm.trans (simplexDerivativeEquiv T)

private theorem chart_transition_orientation_map_comp
    {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module ℝ A] [Module ℝ B] [Module ℝ C]
    (a : A ≃ₗ[ℝ] B) (b : B ≃ₗ[ℝ] C) (oA : Orientation ℝ A (Fin 3)) :
    Orientation.map (Fin 3) b (Orientation.map (Fin 3) a oA) =
      Orientation.map (Fin 3) (a.trans b) oA := by
  induction oA using Quotient.inductionOn with
  | h oA => rfl

theorem simplexDerivativeTransition_det_pos (S T : OrientedChartSimplex o x) :
    0 < LinearMap.det (simplexDerivativeTransition S T).toLinearMap := by
  have hcard : Fintype.card (Fin 3) = Module.finrank ℝ ThreeSpace := by simp
  have hS : Orientation.map (Fin 3) (simplexDerivativeEquiv S).toLinearEquiv
      (o.orientation x) = standardThreeOrientation := by
    have h : (simplexDerivativeEquiv S).toLinearEquiv =
        LinearEquiv.ofBijective (mfderiv ThreeModel ThreeModel S.chart x).toLinearMap
          S.derivative_bijective := rfl
    rw [h]
    exact S.positive
  have hT : Orientation.map (Fin 3) (simplexDerivativeEquiv T).toLinearEquiv
      (o.orientation x) = standardThreeOrientation := by
    have h : (simplexDerivativeEquiv T).toLinearEquiv =
        LinearEquiv.ofBijective (mfderiv ThreeModel ThreeModel T.chart x).toLinearMap
          T.derivative_bijective := rfl
    rw [h]
    exact T.positive
  have hmap : Orientation.map (Fin 3) (simplexDerivativeTransition S T).toLinearEquiv
      standardThreeOrientation = standardThreeOrientation := by
    have htrans : (simplexDerivativeTransition S T).toLinearEquiv =
        (simplexDerivativeEquiv S).toLinearEquiv.symm.trans
          (simplexDerivativeEquiv T).toLinearEquiv := rfl
    rw [htrans, ← chart_transition_orientation_map_comp]
    conv_lhs => rw [← hS]
    conv_rhs => rw [← hT]
    congr 1
    exact (Orientation.map (Fin 3) (simplexDerivativeEquiv S).toLinearEquiv).symm_apply_apply
      (o.orientation x)
  exact (Orientation.map_eq_iff_det_pos standardThreeOrientation
    (simplexDerivativeTransition S T).toLinearEquiv hcard).mp hmap

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

noncomputable section
open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] {o : TangentOrientationSection M} {x : M}


set_option backward.isDefEq.respectTransparency false in
private theorem chartSimplex_hasFDerivAt_native (S : OrientedChartSimplex o x) :
    HasFDerivAt (S.chart ∘ (chartAt ThreeSpace x).symm)
      (simplexDerivativeEquiv S).toContinuousLinearMap (chartAt ThreeSpace x x) := by
  have hmd : MDifferentiableAt ThreeModel ThreeModel (⇑S.chart : M → ThreeSpace) x :=
    S.differentiableAt
  have hβ := hmd.hasMFDerivAt.2
  rw [ModelWithCorners.range_eq_univ ThreeModel, hasFDerivWithinAt_univ] at hβ
  have hfun : writtenInExtChartAt ThreeModel ThreeModel x (⇑S.chart) =
      (S.chart ∘ (chartAt ThreeSpace x).symm) := by
    funext y
    simp only [writtenInExtChartAt, Function.comp_apply]
    rw [extChartAt_model_space_eq_id, PartialEquiv.refl_coe]
    rw [extChartAt_coe_symm]
    rfl
  have hpt : extChartAt ThreeModel x x = chartAt ThreeSpace x x := by
    rw [extChartAt_coe]
    rfl
  have hderiv : (simplexDerivativeEquiv S).toContinuousLinearMap =
      mfderiv ThreeModel ThreeModel (⇑S.chart) x := by
    ext v
    simp only [simplexDerivativeEquiv]
    rfl
  rw [hfun, hpt] at hβ
  exact hβ.congr_fderiv hderiv.symm

theorem chartSimplex_hasFDerivAt_transition (S T : OrientedChartSimplex o x) :
    HasFDerivAt (T.chart ∘ S.chart.symm)
      (simplexDerivativeTransition S T).toContinuousLinearMap (S.chart x) := by
  let c := chartAt ThreeSpace x
  let e := c.symm.trans S.chart
  have hx : x ∈ c.source := mem_chart_source ThreeSpace x
  have he : S.chart x ∈ e.target := by
    change S.chart x ∈ S.chart.target ∩ S.chart.symm ⁻¹' c.source
    exact ⟨S.chart.map_source S.center_mem,
      by simpa only [mem_preimage, S.chart.left_inv S.center_mem] using hx⟩
  have he0 : e.symm (S.chart x) = c x := by
    change c (S.chart.symm (S.chart x)) = c x
    rw [S.chart.left_inv S.center_mem]
  have hd : HasFDerivAt e (simplexDerivativeEquiv S).toContinuousLinearMap
      (e.symm (S.chart x)) := by
    rw [he0]
    exact chartSimplex_hasFDerivAt_native S
  have hinv := e.hasFDerivAt_symm he hd
  have hT := chartSimplex_hasFDerivAt_native T
  rw [← he0] at hT
  have hcomp := hT.comp (S.chart x) hinv
  have hnear : ∀ᶠ y in 𝓝 (S.chart x), S.chart.symm y ∈ c.source :=
    (S.chart.continuousAt_symm (S.chart.map_source S.center_mem)).preimage_mem_nhds
      (by simpa only [S.chart.left_inv S.center_mem] using c.open_source.mem_nhds hx)
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [hnear] with y hy
  change T.chart (S.chart.symm y) = T.chart (c.symm (c (S.chart.symm y)))
  rw [c.left_inv hy]


def chartSimplex_centeredTransition (S T : OrientedChartSimplex o x) (v : ThreeSpace) :
    ThreeSpace := T.chart (S.chart.symm (S.chart x + v)) - T.chart x

@[simp] theorem chartSimplex_centeredTransition_zero (S T : OrientedChartSimplex o x) :
    chartSimplex_centeredTransition S T 0 = 0 := by
  simp [chartSimplex_centeredTransition, S.chart.left_inv S.center_mem]

theorem chartSimplex_hasFDerivAt_centeredTransition (S T : OrientedChartSimplex o x) :
    HasFDerivAt (chartSimplex_centeredTransition S T)
      (simplexDerivativeTransition S T).toContinuousLinearMap 0 := by
  have h : HasFDerivAt (T.chart ∘ S.chart.symm)
      (simplexDerivativeTransition S T).toContinuousLinearMap (S.chart x + 0) := by
    simpa only [add_zero] using chartSimplex_hasFDerivAt_transition S T
  have hshift := (hasFDerivAt_id (𝕜 := ℝ) (0 : ThreeSpace)).const_add (S.chart x)
  have hcomp := h.comp 0 hshift
  convert! hcomp.sub_const (T.chart x) using 1


def chartSimplex_transitionDomain (S T : OrientedChartSimplex o x) : Set ThreeSpace :=
  (fun v => S.chart x + v) ⁻¹' (S.chart.symm.trans T.chart).source

theorem chartSimplex_transitionDomain_open (S T : OrientedChartSimplex o x) :
    IsOpen (chartSimplex_transitionDomain S T) :=
  (S.chart.symm.trans T.chart).open_source.preimage (continuous_const.add continuous_id)

theorem chartSimplex_zero_mem_transitionDomain (S T : OrientedChartSimplex o x) :
    0 ∈ chartSimplex_transitionDomain S T := by
  change S.chart x + 0 ∈ S.chart.target ∩ S.chart.symm ⁻¹' T.chart.source
  simpa only [add_zero, mem_inter_iff, mem_preimage, S.chart.left_inv S.center_mem] using
    And.intro (S.chart.map_source S.center_mem) T.center_mem

theorem chartSimplex_centeredTransition_continuousOn (S T : OrientedChartSimplex o x) :
    ContinuousOn (chartSimplex_centeredTransition S T) (chartSimplex_transitionDomain S T) := by
  exact ((S.chart.symm.trans T.chart).continuousOn.comp
    (continuous_const.add continuous_id).continuousOn (fun _ h => h)).sub continuousOn_const

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
noncomputable section
open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] {o : TangentOrientationSection M} {x : M}

theorem chartSimplex_exists_blend_radius (S T : OrientedChartSimplex o x) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ v ∈ Metric.ball (0 : ThreeSpace) ε,
      v ∈ chartSimplex_transitionDomain S T ∧
      ∀ t : unitInterval,
        T.chart x + (simplexDerivativeTransition S T v +
          (t : ℝ) • (chartSimplex_centeredTransition S T v -
            simplexDerivativeTransition S T v)) ∈ T.chart.target ∧
        (v ≠ 0 → simplexDerivativeTransition S T v +
          (t : ℝ) • (chartSimplex_centeredTransition S T v -
            simplexDerivativeTransition S T v) ≠ 0) := by
  let D := simplexDerivativeTransition S T
  let f := chartSimplex_centeredTransition S T
  have hf := chartSimplex_hasFDerivAt_centeredTransition S T
  have hf0 : f 0 = 0 := chartSimplex_centeredTransition_zero S T
  obtain ⟨δ, hδ, hδin⟩ := Metric.mem_nhds_iff.mp
    (T.chart.open_target.mem_nhds (T.chart.map_source T.center_mem))
  obtain ⟨η, hη, hbound⟩ := exists_relative_derivative_bound D hf hf0
  have hU : ∀ᶠ v in 𝓝 (0 : ThreeSpace), v ∈ chartSimplex_transitionDomain S T :=
    (chartSimplex_transitionDomain_open S T).mem_nhds
      (chartSimplex_zero_mem_transitionDomain S T)
  have hF : ∀ᶠ v in 𝓝 (0 : ThreeSpace), f v ∈ Metric.ball 0 δ :=
    hf.continuousAt.preimage_mem_nhds
      (by rw [chartSimplex_centeredTransition_zero]; exact Metric.ball_mem_nhds _ hδ)
  have hD : ∀ᶠ v in 𝓝 (0 : ThreeSpace), D v ∈ Metric.ball 0 δ :=
    D.continuous.continuousAt.preimage_mem_nhds
      (by rw [map_zero]; exact Metric.ball_mem_nhds _ hδ)
  have hηnear : ∀ᶠ v in 𝓝 (0 : ThreeSpace), v ∈ Metric.ball 0 η :=
    Metric.ball_mem_nhds _ hη
  obtain ⟨ε, hε, hall⟩ := Metric.eventually_nhds_iff_ball.mp
    (hU.and (hF.and (hD.and hηnear)))
  refine ⟨ε, hε, fun v hv => ⟨(hall v hv).1, fun t => ⟨?_, ?_⟩⟩⟩
  · apply hδin
    have hb := (convex_ball (0 : ThreeSpace) δ).add_smul_sub_mem
      (hall v hv).2.2.1 (hall v hv).2.1 t.property
    simpa only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero] using hb
  · intro hne
    exact derivative_blend_ne_zero D t hne (hbound v (hall v hv).2.2.2)


private theorem chartSimplex_lift_ne_center (T : OrientedChartSimplex o x)
    {v : ThreeSpace} (hv : T.chart x + v ∈ T.chart.target) (hne : v ≠ 0) :
    T.chart.symm (T.chart x + v) ≠ x := by
  intro h
  have he := congrArg T.chart h
  rw [T.chart.right_inv hv] at he
  exact hne (add_left_cancel (he.trans (add_zero (T.chart x)).symm))

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
noncomputable section
open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] {o : TangentOrientationSection M} {x : M}

theorem OrientedChartSimplex.localClass_eq_of_positive_charts
    (S T : OrientedChartSimplex o x) : S.localClass = T.localClass := by
  sorry


theorem exists_unique_localOrientationClass_from_chart_comparison
    (o : TangentOrientationSection M) (x : M) :
    ∃! xi : LocalIntegralHomology M x 3, ∀ S : OrientedChartSimplex o x, S.localClass = xi := by
  obtain ⟨S⟩ := exists_orientedChartSimplex o x
  exact ⟨S.localClass, fun T => T.localClass_eq_of_positive_charts S,
    fun xi hxi => (hxi S).symm⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
