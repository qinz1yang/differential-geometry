import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.Background
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.LinearOrientation
import DifferentialGeometry.Bundle.TangentSpace
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv


noncomputable section
open Bundle Manifold Set
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M]

def standardThreeOrientation : Orientation ℝ ThreeSpace (Fin 3) :=
  (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation

def positiveTetrahedronVertex : Fin 4 → ThreeSpace :=
  ![WithLp.toLp 2 ![-1, -1, -1], WithLp.toLp 2 ![1, 0, 0],
    WithLp.toLp 2 ![0, 1, 0], WithLp.toLp 2 ![0, 0, 1]]


def positiveTetrahedron : C(stdSimplex ℝ (Fin 4), ThreeSpace) where
  toFun q := ∑ i : Fin 4, q.val i • positiveTetrahedronVertex i
  continuous_toFun := continuous_finsetSum _ fun i _ =>
    ((continuous_apply i).comp continuous_subtype_val).smul continuous_const


theorem positiveTetrahedron_det :
    Matrix.det (fun i j : Fin 3 =>
      (positiveTetrahedronVertex j.succ - positiveTetrahedronVertex 0) i) = 4 := by
  convert Matrix.det_fin_three (fun i j : Fin 3 =>
    (positiveTetrahedronVertex j.succ - positiveTetrahedronVertex 0) i) using 1
  norm_num [positiveTetrahedronVertex, Matrix.cons_val_two, Matrix.cons_val_three]


theorem positiveTetrahedron_coordinate (q : stdSimplex ℝ (Fin 4)) (i : Fin 3) :
    positiveTetrahedron q i = q.val i.succ - q.val 0 := by
  fin_cases i <;>
    simp [positiveTetrahedron, positiveTetrahedronVertex, Fin.sum_univ_succ] <;> ring


theorem positiveTetrahedron_zero_iff (q : stdSimplex ℝ (Fin 4)) :
    positiveTetrahedron q = 0 ↔ ∀ i : Fin 4, q.val i = (1 / 4 : ℝ) := by
  constructor
  · intro h
    have hc : ∀ i : Fin 3, q.val i.succ - q.val 0 = 0 := by
      intro i
      rw [← positiveTetrahedron_coordinate, h]
      rfl
    have hc0 := hc 0
    have hc1 := hc 1
    have hc2 := hc 2
    change q.val 1 - q.val 0 = 0 at hc0
    change q.val 2 - q.val 0 = 0 at hc1
    change q.val 3 - q.val 0 = 0 at hc2
    have hsum := q.property.2
    simp [Fin.sum_univ_succ] at hsum
    have hzero : q.val 0 = (1 / 4 : ℝ) := by linarith
    exact Fin.cases hzero (fun j => by have hj := hc j; linarith)
  · intro h
    ext i
    rw [positiveTetrahedron_coordinate, h, h]
    simp


theorem positiveTetrahedron_face_ne_zero (q : stdSimplex ℝ (Fin 4))
    (i : Fin 4) (hi : q.val i = 0) : positiveTetrahedron q ≠ 0 := by
  intro h
  have hquarter := (positiveTetrahedron_zero_iff q).mp h i
  linarith

structure OrientedChartSimplex (o : TangentOrientationSection M) (x : M) where
  chart : OpenPartialHomeomorph M ThreeSpace
  center_mem : x ∈ chart.source
  differentiableAt : MDifferentiableAt ThreeModel ThreeModel chart x
  derivative_bijective : Function.Bijective (mfderiv ThreeModel ThreeModel chart x)
  positive : Orientation.map (Fin 3)
    (LinearEquiv.ofBijective (mfderiv ThreeModel ThreeModel chart x).toLinearMap
      derivative_bijective) (o.orientation x) = standardThreeOrientation
  radius : ℝ
  radius_pos : 0 < radius
  simplex_inside : ∀ q : stdSimplex ℝ (Fin 4),
    chart x + radius • positiveTetrahedron q ∈ chart.target


def OrientedChartSimplex.simplex {o : TangentOrientationSection M} {x : M}
    (S : OrientedChartSimplex o x) : C(stdSimplex ℝ (Fin 4), M) where
  toFun q := S.chart.symm (S.chart x + S.radius • positiveTetrahedron q)
  continuous_toFun := S.chart.continuousOn_symm.comp_continuous
    (by fun_prop) S.simplex_inside

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

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

private def simplexContraction (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (q : stdSimplex ℝ (Fin 4)) : stdSimplex ℝ (Fin 4) :=
  ⟨fun j => a * q.val j + (1 - a) / 4, by
    constructor
    · intro j
      exact add_nonneg (mul_nonneg ha.1 (q.property.1 j))
        (div_nonneg (sub_nonneg.mpr ha.2) (by norm_num))
    · simp only [Finset.sum_add_distrib, ← Finset.mul_sum, q.property.2,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring⟩

private theorem positiveTetrahedron_simplexContraction (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (q : stdSimplex ℝ (Fin 4)) :
    positiveTetrahedron (simplexContraction a ha q) = a • positiveTetrahedron q := by
  ext i
  rw [positiveTetrahedron_coordinate]
  change (a * q.val i.succ + (1 - a) / 4) - (a * q.val 0 + (1 - a) / 4) =
    a * positiveTetrahedron q i
  rw [positiveTetrahedron_coordinate]
  ring

private theorem chartSimplex_mem_of_ratio (S : OrientedChartSimplex o x) {r : ℝ}
    (h0 : 0 ≤ r) (hr : r ≤ S.radius) (q : stdSimplex ℝ (Fin 4)) :
    S.chart x + r • positiveTetrahedron q ∈ S.chart.target := by
  have ha : r / S.radius ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg h0 S.radius_pos.le, (div_le_one S.radius_pos).mpr hr⟩
  have hp := S.simplex_inside (simplexContraction (r / S.radius) ha q)
  rw [positiveTetrahedron_simplexContraction (r / S.radius) ha q, smul_smul,
    mul_div_cancel₀ r (ne_of_gt S.radius_pos)] at hp
  exact hp

private theorem chartSimplex_ratio_mem (S : OrientedChartSimplex o x) {b : ℝ}
    (hb : b ∈ Icc (0 : ℝ) 1) (q : stdSimplex ℝ (Fin 4)) :
    S.chart x + S.radius • (b • positiveTetrahedron q) ∈ S.chart.target := by
  have hp := S.simplex_inside (simplexContraction b hb q)
  rwa [positiveTetrahedron_simplexContraction b hb q] at hp

private theorem chartSimplex_blendRatio_mem (S : OrientedChartSimplex o x) {r : ℝ}
    (h0 : 0 ≤ r) (hr : r ≤ S.radius) (t : unitInterval) (q : stdSimplex ℝ (Fin 4)) :
    S.chart x + S.radius • (((1 - (t : ℝ)) + (t : ℝ) * (r / S.radius)) •
      positiveTetrahedron q) ∈ S.chart.target := by
  apply chartSimplex_ratio_mem S _ q
  exact ⟨by
      have h1 : 0 ≤ r / S.radius := div_nonneg h0 S.radius_pos.le
      nlinarith [t.2.1, t.2.2, h1], by
      have h1 : r / S.radius ≤ 1 := (div_le_one S.radius_pos).mpr hr
      nlinarith [t.2.1, t.2.2, h1]⟩

private theorem chartSimplex_blendRatio_pos (S : OrientedChartSimplex o x) {r : ℝ}
    (h0 : 0 < r) (t : unitInterval) :
    0 < (1 - (t : ℝ)) + (t : ℝ) * (r / S.radius) := by
  have h1 : 0 ≤ r / S.radius := div_nonneg h0.le S.radius_pos.le
  by_cases ht : (t : ℝ) = 1
  · have he : (1 - (t : ℝ)) + (t : ℝ) * (r / S.radius) = r / S.radius := by
      rw [ht]; ring
    rw [he]
    exact div_pos h0 S.radius_pos
  · have hlt : (t : ℝ) < 1 := lt_of_le_of_ne t.2.2 ht
    have hpos : 0 < 1 - (t : ℝ) := sub_pos.mpr hlt
    have h2 : 0 ≤ (t : ℝ) * (r / S.radius) := mul_nonneg t.2.1 h1
    linarith

private theorem chartSimplex_ratio_smul_ne_zero (S : OrientedChartSimplex o x)
    {b : ℝ} (hb : b ≠ 0) {q : stdSimplex ℝ (Fin 4)} (hq : positiveTetrahedron q ≠ 0) :
    S.radius • (b • positiveTetrahedron q) ≠ 0 := by
  intro h
  rcases smul_eq_zero.mp h with h1 | h1
  · exact (ne_of_gt S.radius_pos) h1
  · rcases smul_eq_zero.mp h1 with h2 | h2
    · exact hb h2
    · exact hq h2

private theorem positiveTetrahedron_ne_zero_of_boundary (q : stdSimplex ℝ (Fin 4))
    (hq : ∃ i : Fin 4, q.val i = 0) : positiveTetrahedron q ≠ 0 := by
  obtain ⟨i, hi⟩ := hq
  exact positiveTetrahedron_face_ne_zero q i hi

private noncomputable def chartSimplexRadius (S : OrientedChartSimplex o x) (r : ℝ)
    (h0 : 0 ≤ r) (hr : r ≤ S.radius) : C(stdSimplex ℝ (Fin 4), M) where
  toFun q := S.chart.symm (S.chart x + r • positiveTetrahedron q)
  continuous_toFun := S.chart.continuousOn_symm.comp_continuous (by fun_prop)
    (fun q => chartSimplex_mem_of_ratio S h0 hr q)

@[simp] private theorem chartSimplexRadius_apply (S : OrientedChartSimplex o x) (r : ℝ)
    (h0 : 0 ≤ r) (hr : r ≤ S.radius) (q : stdSimplex ℝ (Fin 4)) :
    chartSimplexRadius S r h0 hr q = S.chart.symm (S.chart x + r • positiveTetrahedron q) :=
  rfl

private noncomputable def chartSimplexRadiusHomotopy (S : OrientedChartSimplex o x) (r : ℝ)
    (h0 : 0 < r) (hr : r ≤ S.radius) :
    S.simplex.Homotopy (chartSimplexRadius S r h0.le hr) where
  toFun p := S.chart.symm (S.chart x + S.radius •
    (((1 - (p.1 : ℝ)) + (p.1 : ℝ) * (r / S.radius)) • positiveTetrahedron p.2))
  continuous_toFun := S.chart.continuousOn_symm.comp_continuous (by fun_prop)
    (fun p => chartSimplex_blendRatio_mem S h0.le hr p.1 p.2)
  map_zero_left q := by
    apply congrArg S.chart.symm
    have h0' : ((0 : unitInterval) : ℝ) = 0 := rfl
    rw [h0']
    norm_num
  map_one_left q := by
    apply congrArg S.chart.symm
    have h1' : ((1 : unitInterval) : ℝ) = 1 := rfl
    rw [h1']
    norm_num
    rw [smul_smul, mul_div_cancel₀ r (ne_of_gt S.radius_pos)]

private noncomputable def chartSimplexLinear (T : OrientedChartSimplex o x)
    (D : ThreeSpace →L[ℝ] ThreeSpace) (r : ℝ)
    (hmem : ∀ q, T.chart x + D (r • positiveTetrahedron q) ∈ T.chart.target) :
    C(stdSimplex ℝ (Fin 4), M) where
  toFun q := T.chart.symm (T.chart x + D (r • positiveTetrahedron q))
  continuous_toFun := T.chart.continuousOn_symm.comp_continuous (by fun_prop) hmem

@[simp] private theorem chartSimplexLinear_apply (T : OrientedChartSimplex o x)
    (D : ThreeSpace →L[ℝ] ThreeSpace) (r : ℝ)
    (hmem : ∀ q, T.chart x + D (r • positiveTetrahedron q) ∈ T.chart.target)
    (q : stdSimplex ℝ (Fin 4)) :
    chartSimplexLinear T D r hmem q = T.chart.symm (T.chart x + D (r • positiveTetrahedron q)) :=
  rfl

private noncomputable def chartSimplexBlendHomotopy (S T : OrientedChartSimplex o x)
    {ε : ℝ} (D : ThreeSpace →L[ℝ] ThreeSpace) (r : ℝ) (h0 : 0 ≤ r) (hrS : r ≤ S.radius)
    (hblend : ∀ v ∈ Metric.ball (0 : ThreeSpace) ε,
      v ∈ chartSimplex_transitionDomain S T ∧
      ∀ t : unitInterval,
        T.chart x + (D v + (t : ℝ) • (chartSimplex_centeredTransition S T v - D v)) ∈
          T.chart.target ∧
        (v ≠ 0 → D v + (t : ℝ) • (chartSimplex_centeredTransition S T v - D v) ≠ 0))
    (hε : ∀ q, r • positiveTetrahedron q ∈ Metric.ball (0 : ThreeSpace) ε)
    (hmem : ∀ q, T.chart x + D (r • positiveTetrahedron q) ∈ T.chart.target) :
    (chartSimplexLinear T D r hmem).Homotopy (chartSimplexRadius S r h0 hrS) where
  toFun p := T.chart.symm (T.chart x + (D (r • positiveTetrahedron p.2) +
    (p.1 : ℝ) • (chartSimplex_centeredTransition S T (r • positiveTetrahedron p.2) -
      D (r • positiveTetrahedron p.2))))
  continuous_toFun := by
    have hv : Continuous fun p : unitInterval × stdSimplex ℝ (Fin 4) =>
        r • positiveTetrahedron p.2 := by fun_prop
    have hmem1 : ∀ p : unitInterval × stdSimplex ℝ (Fin 4),
        S.chart x + r • positiveTetrahedron p.2 ∈ S.chart.target := by
      intro p
      have h := (hblend _ (hε p.2)).1
      rw [chartSimplex_transitionDomain, OpenPartialHomeomorph.trans_source,
        OpenPartialHomeomorph.symm_source, Set.mem_preimage, Set.mem_inter_iff] at h
      exact h.1
    have hmem2 : ∀ p : unitInterval × stdSimplex ℝ (Fin 4),
        S.chart.symm (S.chart x + r • positiveTetrahedron p.2) ∈ T.chart.source := by
      intro p
      have h := (hblend _ (hε p.2)).1
      rw [chartSimplex_transitionDomain, OpenPartialHomeomorph.trans_source,
        OpenPartialHomeomorph.symm_source, Set.mem_preimage, Set.mem_inter_iff] at h
      exact h.2
    have hsymm : Continuous fun p : unitInterval × stdSimplex ℝ (Fin 4) =>
        S.chart.symm (S.chart x + r • positiveTetrahedron p.2) :=
      S.chart.continuousOn_symm.comp_continuous (continuous_const.add hv) hmem1
    have hchart : Continuous fun p : unitInterval × stdSimplex ℝ (Fin 4) =>
        T.chart (S.chart.symm (S.chart x + r • positiveTetrahedron p.2)) :=
      T.chart.continuousOn.comp_continuous hsymm hmem2
    have hcent : Continuous fun p : unitInterval × stdSimplex ℝ (Fin 4) =>
        chartSimplex_centeredTransition S T (r • positiveTetrahedron p.2) :=
      hchart.sub continuous_const
    have hDv : Continuous fun p : unitInterval × stdSimplex ℝ (Fin 4) =>
        D (r • positiveTetrahedron p.2) := D.continuous.comp hv
    have ht : Continuous fun p : unitInterval × stdSimplex ℝ (Fin 4) => (p.1 : ℝ) :=
      continuous_subtype_val.comp continuous_fst
    have hcomb : Continuous fun p : unitInterval × stdSimplex ℝ (Fin 4) =>
        T.chart x + (D (r • positiveTetrahedron p.2) + (p.1 : ℝ) •
          (chartSimplex_centeredTransition S T (r • positiveTetrahedron p.2) -
            D (r • positiveTetrahedron p.2))) :=
      continuous_const.add (hDv.add (ht.smul (hcent.sub hDv)))
    exact T.chart.continuousOn_symm.comp_continuous hcomb
      (fun p => (hblend _ (hε p.2)).2 p.1 |>.1)
  map_zero_left q := by
    simp only [chartSimplexLinear_apply]
    apply congrArg T.chart.symm
    have h0' : ((0 : unitInterval) : ℝ) = 0 := rfl
    rw [h0']
    simp
  map_one_left q := by
    simp only [chartSimplexRadius_apply]
    have h1' : ((1 : unitInterval) : ℝ) = 1 := rfl
    rw [h1', one_smul, chartSimplex_centeredTransition]
    have hw : S.chart.symm (S.chart x + r • positiveTetrahedron q) ∈ T.chart.source := by
      have h := (hblend _ (hε q)).1
      rw [chartSimplex_transitionDomain, OpenPartialHomeomorph.trans_source,
        OpenPartialHomeomorph.symm_source, Set.mem_preimage, Set.mem_inter_iff] at h
      exact h.2
    have harg : T.chart x + (D (r • positiveTetrahedron q) +
        (T.chart (S.chart.symm (S.chart x + r • positiveTetrahedron q)) - T.chart x -
          D (r • positiveTetrahedron q))) =
        T.chart (S.chart.symm (S.chart x + r • positiveTetrahedron q)) := by abel
    rw [harg, T.chart.left_inv hw]

private noncomputable def chartSimplexLinearHomotopy (T : OrientedChartSimplex o x)
    (D : ThreeSpace →L[ℝ] ThreeSpace) (r : ℝ) (h0 : 0 ≤ r) (hrT : r ≤ T.radius)
    (H : (⟨D, D.continuous⟩ : C(ThreeSpace, ThreeSpace)).Homotopy (ContinuousMap.id ThreeSpace))
    (hmemH : ∀ (t : unitInterval) (q : stdSimplex ℝ (Fin 4)),
      T.chart x + H (t, r • positiveTetrahedron q) ∈ T.chart.target)
    (hmemD : ∀ q, T.chart x + D (r • positiveTetrahedron q) ∈ T.chart.target) :
    (chartSimplexLinear T D r hmemD).Homotopy (chartSimplexRadius T r h0 hrT) where
  toFun p := T.chart.symm (T.chart x + H (p.1, r • positiveTetrahedron p.2))
  continuous_toFun := T.chart.continuousOn_symm.comp_continuous
    (by
      have hv : Continuous fun p : unitInterval × stdSimplex ℝ (Fin 4) =>
          r • positiveTetrahedron p.2 := by fun_prop
      exact continuous_const.add (H.continuous.comp (Continuous.prodMk continuous_fst hv)))
    (fun p => hmemH p.1 p.2)
  map_zero_left q := by
    simp only [chartSimplexLinear_apply]
    apply congrArg T.chart.symm
    have h : H (0, r • positiveTetrahedron q) = D (r • positiveTetrahedron q) :=
      H.map_zero_left _
    rw [h]
  map_one_left q := by
    simp only [chartSimplexRadius_apply]
    apply congrArg T.chart.symm
    have h : H (1, r • positiveTetrahedron q) = r • positiveTetrahedron q :=
      H.map_one_left _
    rw [h]

theorem OrientedChartSimplex.exists_positiveCharts_simplexFamily
    (S T : OrientedChartSimplex o x) :
    ∃ H : S.simplex.Homotopy T.simplex, ∀ (t : unitInterval) (q : stdSimplex ℝ (Fin 4)),
      (∃ i : Fin 4, q.val i = 0) → H (t, q) ≠ x := by
  classical
  obtain ⟨ε, hε, hblend⟩ := chartSimplex_exists_blend_radius S T
  obtain ⟨H, hHne, C, hC⟩ := positive_linear_homotopy (EuclideanSpace.basisFun (Fin 3) ℝ)
    (simplexDerivativeTransition S T) (simplexDerivativeTransition_det_pos S T)
  obtain ⟨R, hRpos, hR⟩ :=
    (isCompact_range positiveTetrahedron.continuous).isBounded.exists_pos_norm_le
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp
    (T.chart.open_target.mem_nhds (T.chart.map_source T.center_mem))
  have hR1 : 0 < R + 1 := by linarith
  have hC0 : 0 < max C 0 + 1 := by
    have := le_max_right C 0
    linarith
  set r : ℝ := min (min S.radius T.radius)
    (min (ε / (2 * (R + 1))) (δ / (2 * (R + 1) * (max C 0 + 1)))) with hrdef
  have hr0 : 0 < r := by
    rw [hrdef]
    exact lt_min (lt_min S.radius_pos T.radius_pos)
      (lt_min (div_pos hε (by positivity)) (div_pos hδ (by positivity)))
  have hrS : r ≤ S.radius := (min_le_left _ _).trans (min_le_left _ _)
  have hrT : r ≤ T.radius := (min_le_left _ _).trans (min_le_right _ _)
  have hrε : r * R < ε := by
    have h1 : r ≤ ε / (2 * (R + 1)) := (min_le_right _ _).trans (min_le_left _ _)
    have h2 : r * R ≤ (ε / (2 * (R + 1))) * R :=
      mul_le_mul_of_nonneg_right h1 hRpos.le
    have h3 : (ε / (2 * (R + 1))) * R < ε := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      simpa only [mul_comm] using mul_lt_mul_of_pos_left (by linarith : R < 2 * (R + 1)) hε
    linarith
  have hrδ : r * R * (max C 0 + 1) < δ := by
    have h1 : r ≤ δ / (2 * (R + 1) * (max C 0 + 1)) :=
      (min_le_right _ _).trans (min_le_right _ _)
    have h2 : r * (R * (max C 0 + 1)) ≤
        (δ / (2 * (R + 1) * (max C 0 + 1))) * (R * (max C 0 + 1)) :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    have h3 : (δ / (2 * (R + 1) * (max C 0 + 1))) * (R * (max C 0 + 1)) < δ := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      exact mul_lt_mul_of_pos_left (by nlinarith [hRpos, hC0] :
        R * (max C 0 + 1) < 2 * (R + 1) * (max C 0 + 1)) hδ
    nlinarith [h2, h3]
  have hεball : ∀ q : stdSimplex ℝ (Fin 4),
      r • positiveTetrahedron q ∈ Metric.ball (0 : ThreeSpace) ε := by
    intro q
    rw [Metric.mem_ball, dist_eq_norm, sub_zero, norm_smul, Real.norm_eq_abs, abs_of_pos hr0]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (hR _ ⟨q, rfl⟩) hr0.le) hrε
  have hmemD : ∀ q : stdSimplex ℝ (Fin 4),
      T.chart x + simplexDerivativeTransition S T (r • positiveTetrahedron q) ∈
        T.chart.target := by
    intro q
    have h := (hblend _ (hεball q)).2 0 |>.1
    have h0' : ((0 : unitInterval) : ℝ) = 0 := rfl
    rw [h0', zero_smul, add_zero] at h
    exact h
  have hmemH : ∀ (t : unitInterval) (q : stdSimplex ℝ (Fin 4)),
      T.chart x + H (t, r • positiveTetrahedron q) ∈ T.chart.target := by
    intro t q
    apply hδsub
    rw [Metric.mem_ball, dist_eq_norm']
    have hd : T.chart x - (T.chart x + H (t, r • positiveTetrahedron q)) =
        -(H (t, r • positiveTetrahedron q)) := by abel
    rw [hd, norm_neg]
    have h2 : ‖r • positiveTetrahedron q‖ ≤ r * R := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr0]
      exact mul_le_mul_of_nonneg_left (hR _ ⟨q, rfl⟩) hr0.le
    have h3 : ‖H (t, r • positiveTetrahedron q)‖ ≤ max C 0 * (r * R) :=
      calc
        ‖H (t, r • positiveTetrahedron q)‖ ≤ C * ‖r • positiveTetrahedron q‖ := hC t _
        _ ≤ max C 0 * (r * R) :=
          mul_le_mul (le_max_left C 0) h2 (norm_nonneg _) (le_max_right C 0)
    have h4 : max C 0 * (r * R) ≤ r * R * (max C 0 + 1) := by
      have h5 : 0 ≤ r * R := mul_nonneg hr0.le hRpos.le
      nlinarith [le_max_left C 0, h5]
    linarith
  refine ⟨(chartSimplexRadiusHomotopy S r hr0 hrS).trans
      (((chartSimplexBlendHomotopy S T (simplexDerivativeTransition S T) r hr0.le hrS
          hblend hεball hmemD).symm).trans
        ((chartSimplexLinearHomotopy T (simplexDerivativeTransition S T) r hr0.le hrT
            H hmemH hmemD).trans
          ((chartSimplexRadiusHomotopy T r hr0 hrT).symm))), ?_⟩
  have hpq : ∀ q : stdSimplex ℝ (Fin 4), (∃ i : Fin 4, q.val i = 0) →
      positiveTetrahedron q ≠ 0 :=
    fun q hq => positiveTetrahedron_ne_zero_of_boundary q hq
  have hrv : ∀ q : stdSimplex ℝ (Fin 4), (∃ i : Fin 4, q.val i = 0) →
      r • positiveTetrahedron q ≠ 0 := by
    intro q hq h
    exact hpq q hq (smul_eq_zero.mp h |>.resolve_left (ne_of_gt hr0))
  have hne1 : ∀ (t : unitInterval) (q : stdSimplex ℝ (Fin 4)),
      (∃ i : Fin 4, q.val i = 0) →
        chartSimplexRadiusHomotopy S r hr0 hrS (t, q) ≠ x := by
    intro t q hq
    change S.chart.symm (S.chart x + S.radius •
      (((1 - (t : ℝ)) + (t : ℝ) * (r / S.radius)) • positiveTetrahedron q)) ≠ x
    exact chartSimplex_lift_ne_center S (chartSimplex_blendRatio_mem S hr0.le hrS t q)
      (chartSimplex_ratio_smul_ne_zero S
        (ne_of_gt (chartSimplex_blendRatio_pos S hr0 t)) (hpq q hq))
  have hne2 : ∀ (t : unitInterval) (q : stdSimplex ℝ (Fin 4)),
      (∃ i : Fin 4, q.val i = 0) →
        (chartSimplexBlendHomotopy S T (simplexDerivativeTransition S T) r hr0.le hrS
          hblend hεball hmemD).symm (t, q) ≠ x := by
    intro t q hq
    rw [ContinuousMap.Homotopy.symm_apply]
    change T.chart.symm (T.chart x + (simplexDerivativeTransition S T
        (r • positiveTetrahedron q) +
      ((unitInterval.symm t : unitInterval) : ℝ) •
        (chartSimplex_centeredTransition S T (r • positiveTetrahedron q) -
          simplexDerivativeTransition S T (r • positiveTetrahedron q)))) ≠ x
    exact chartSimplex_lift_ne_center T ((hblend _ (hεball q)).2 (unitInterval.symm t) |>.1)
      ((hblend _ (hεball q)).2 (unitInterval.symm t) |>.2 (hrv q hq))
  have hne3 : ∀ (t : unitInterval) (q : stdSimplex ℝ (Fin 4)),
      (∃ i : Fin 4, q.val i = 0) →
        chartSimplexLinearHomotopy T (simplexDerivativeTransition S T) r hr0.le hrT
          H hmemH hmemD (t, q) ≠ x := by
    intro t q hq
    change T.chart.symm (T.chart x + H (t, r • positiveTetrahedron q)) ≠ x
    exact chartSimplex_lift_ne_center T (hmemH t q) (hHne t _ (hrv q hq))
  have hne4 : ∀ (t : unitInterval) (q : stdSimplex ℝ (Fin 4)),
      (∃ i : Fin 4, q.val i = 0) →
        (chartSimplexRadiusHomotopy T r hr0 hrT).symm (t, q) ≠ x := by
    intro t q hq
    rw [ContinuousMap.Homotopy.symm_apply]
    change T.chart.symm (T.chart x + T.radius •
      (((1 - ((unitInterval.symm t : unitInterval) : ℝ)) +
        ((unitInterval.symm t : unitInterval) : ℝ) * (r / T.radius)) •
          positiveTetrahedron q)) ≠ x
    exact chartSimplex_lift_ne_center T
      (chartSimplex_blendRatio_mem T hr0.le hrT (unitInterval.symm t) q)
      (chartSimplex_ratio_smul_ne_zero T
        (ne_of_gt (chartSimplex_blendRatio_pos T hr0 (unitInterval.symm t))) (hpq q hq))
  intro t q hq
  rw [ContinuousMap.Homotopy.trans_apply]
  split_ifs with ht1
  · exact hne1 _ _ hq
  · rw [ContinuousMap.Homotopy.trans_apply]
    split_ifs with ht2
    · exact hne2 _ _ hq
    · rw [ContinuousMap.Homotopy.trans_apply]
      split_ifs with ht3
      · exact hne3 _ _ hq
      · exact hne4 _ _ hq

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
