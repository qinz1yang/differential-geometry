import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.FillingDisc
import DifferentialGeometry.Topology.Manifold.SmoothBoundaryAtlas.Interior
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Chart
import Mathlib.LinearAlgebra.Complex.Determinant
import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# Chapter-14 assembly, relative COMPARE G2: a conjugation-symmetric Euclidean box in the solid torus

Lane ASM-L2e, group G2 (first part). The placement of a ball chart into a fibre tube compares two
balls inside ONE Euclidean chart of the solid torus `solidSet` in which the conjugation
`(w, θ) ↦ (w̄, θ)` is a linear reflection; the orientation choice is then a determinant sign.

* `planeCircleConj`, `solidConj ε`: the conjugation of `PlaneLift × Circle` and of `solidSet`
  (`ε = false`: the identity).
* `solidInteriorPD`: the inclusion of the interior of `solidSet`, a partial diffeomorphism.
* `planeCircleBox`: a Euclidean chart `E³ ⊇ V → PlaneLift × Circle` (`V` open and convex), with
  `planeCircleBox_conj`: `conj (box x) = box (R x)` for a linear `R` with `det R = -1`
  (`boxReflection_det`), `R V = V`; its image has plane radius `< 1/4`.
* `solidBox`: the same chart into `solidSet`, and `tubeBox φ`: the chart pushed into a manifold
  through a tube chart `φ` scaled by `1/3`, with `solidTubeFill φ (solidBox x) = tubeBox φ x`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold Metric
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E1" => EuclideanSpace ℝ (Fin 1)

/-! ### Conjugation -/

theorem contMDiff_planeCircleConj :
    ContMDiff (𝓘(ℝ, ℂ).prod (𝓡 1)) (𝓘(ℝ, ℂ).prod (𝓡 1)) ∞
      (fun p : PlaneLift.{u} × Circle => (ULift.up (Complex.conjCLE p.1.down), p.2)) :=
  (contMDiff_planeLift_up.comp (Complex.conjCLE.contDiff.contMDiff.comp
    (contMDiff_planeLift_down.comp contMDiff_fst))).prodMk contMDiff_snd

/-- Complex conjugation on the plane factor of `PlaneLift × Circle`. -/
def planeCircleConj : (PlaneLift.{u} × Circle) ≃ₘ⟮𝓘(ℝ, ℂ).prod (𝓡 1), 𝓘(ℝ, ℂ).prod (𝓡 1)⟯
    (PlaneLift.{u} × Circle) where
  toFun p := (ULift.up (Complex.conjCLE p.1.down), p.2)
  invFun p := (ULift.up (Complex.conjCLE p.1.down), p.2)
  left_inv p := by
    apply Prod.ext
    · apply ULift.ext
      simp
    · rfl
  right_inv p := by
    apply Prod.ext
    · apply ULift.ext
      simp
    · rfl
  contMDiff_toFun := contMDiff_planeCircleConj
  contMDiff_invFun := contMDiff_planeCircleConj

theorem planeCircleConj_apply (p : PlaneLift.{u} × Circle) :
    planeCircleConj p = (ULift.up ((starRingEnd ℂ) p.1.down), p.2) := rfl

theorem planeCircleConj_norm (p : PlaneLift.{u} × Circle) :
    ‖(planeCircleConj p).1.down‖ = ‖p.1.down‖ := by
  change ‖(starRingEnd ℂ) p.1.down‖ = _
  exact Complex.norm_conj _

/-- The conjugation of the solid torus (`ε = true`) or the identity (`ε = false`). -/
def solidConj : Bool → (solidSet.{u} ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ solidSet.{u})
  | true => solidAtlas.diffeomorphOfAmbient solidAtlas planeCircleConj (fun x => by
      rw [mem_solidSet_iff, mem_solidSet_iff, planeCircleConj_norm])
  | false => Diffeomorph.refl (𝓡∂ 3) solidSet.{u} ∞

theorem solidConj_val (ε : Bool) (x : solidSet.{u}) :
    (solidConj ε x).val = if ε then (ULift.up ((starRingEnd ℂ) x.val.1.down), x.val.2)
      else x.val := by
  cases ε
  · rfl
  · rfl

theorem solidConj_norm (ε : Bool) (x : solidSet.{u}) :
    ‖(solidConj ε x).val.1.down‖ = ‖x.val.1.down‖ := by
  rw [solidConj_val]
  cases ε
  · rfl
  · exact Complex.norm_conj _

/-! ### The interior of the solid torus -/

theorem mem_interior_solidSet {p : PlaneLift.{u} × Circle} (hp : ‖p.1.down‖ < 3) :
    p ∈ interior solidSet.{u} := by
  have hopen : IsOpen {q : PlaneLift.{u} × Circle | ‖q.1.down‖ < 3} :=
    isOpen_lt (continuous_norm.comp (continuous_uliftDown.comp continuous_fst)) continuous_const
  exact interior_maximal (fun q hq => (mem_solidSet_iff q).mpr (le_of_lt hq)) hopen hp

/-- The inclusion of the interior of the solid torus. -/
def solidInteriorPD : PartialDiffeomorph (𝓡∂ 3) (𝓘(ℝ, ℂ).prod (𝓡 1)) solidSet.{u}
    (PlaneLift.{u} × Circle) ∞ :=
  solidAtlas.interiorPartialDiffeomorph (Classical.arbitrary solidSet.{u})

theorem solidInteriorPD_apply (x : solidSet.{u}) : solidInteriorPD x = x.val := rfl

theorem solidInteriorPD_target : (solidInteriorPD.{u}).target = interior solidSet.{u} := rfl

theorem solidInteriorPD_symm_val {p : PlaneLift.{u} × Circle} (hp : p ∈ interior solidSet.{u}) :
    (solidInteriorPD.symm p).val = p :=
  solidInteriorPD.right_inv hp

/-! ### The Euclidean box -/

/-- A linear identification of `E³` with `ℂ × E¹`. -/
def boxLinear : E3 ≃L[ℝ] ℂ × E1 :=
  ContinuousLinearEquiv.ofFinrankEq (by
    rw [finrank_euclideanSpace_fin, Module.finrank_prod, Complex.finrank_real_complex,
      finrank_euclideanSpace_fin])

/-- The chart of the circle at `1`. -/
def circleChart : PartialDiffeomorph (𝓡 1) 𝓘(ℝ, E1) Circle E1 ∞ :=
  DifferentialGeometry.PartialDiffeomorph.extChartAt (𝓡 1) ∞ (1 : Circle)

theorem circleChart_one_mem : (1 : Circle) ∈ circleChart.source :=
  mem_extChartAt_source (I := 𝓡 1) (1 : Circle)

theorem exists_circleBox : ∃ ρ > (0 : ℝ), ball (circleChart (1 : Circle)) ρ ⊆ circleChart.target :=
  Metric.isOpen_iff.mp circleChart.open_target _ (circleChart.map_source circleChart_one_mem)

/-- The radius of the circle factor of the box. -/
def circleBoxRadius : ℝ := exists_circleBox.choose

theorem circleBoxRadius_pos : 0 < circleBoxRadius := exists_circleBox.choose_spec.1

theorem circleBox_subset : ball (circleChart (1 : Circle)) circleBoxRadius ⊆ circleChart.target :=
  exists_circleBox.choose_spec.2

/-- The box in `ℂ × E¹`. -/
def boxCoord : Set (ℂ × E1) := ball (0 : ℂ) (1 / 4) ×ˢ ball (circleChart (1 : Circle)) circleBoxRadius

/-- The box in `E³`. -/
def boxSet : Set E3 := boxLinear ⁻¹' boxCoord

theorem isOpen_boxCoord : IsOpen boxCoord := isOpen_ball.prod isOpen_ball

theorem isOpen_boxSet : IsOpen boxSet := isOpen_boxCoord.preimage boxLinear.continuous

theorem convex_boxSet : Convex ℝ boxSet :=
  ((convex_ball _ _).prod (convex_ball _ _)).linear_preimage boxLinear.toLinearMap

theorem boxSet_nonempty : boxSet.Nonempty :=
  ⟨boxLinear.symm (0, circleChart (1 : Circle)), by
    change boxLinear (boxLinear.symm _) ∈ boxCoord
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact ⟨mem_ball_self (by norm_num), mem_ball_self circleBoxRadius_pos⟩⟩

/-- The box chart of `PlaneLift × Circle`. -/
def planeCircleBox : PartialDiffeomorph 𝓘(ℝ, E3) (𝓘(ℝ, ℂ).prod (𝓡 1)) E3
    (PlaneLift.{u} × Circle) ∞ where
  toFun x := (ULift.up (boxLinear x).1, circleChart.symm (boxLinear x).2)
  invFun p := boxLinear.symm (p.1.down, circleChart p.2)
  source := boxSet
  target := {p | p.2 ∈ circleChart.source ∧ (p.1.down, circleChart p.2) ∈ boxCoord}
  map_source' x hx := by
    have h2 : (boxLinear x).2 ∈ circleChart.target := circleBox_subset hx.2
    refine ⟨circleChart.map_target h2, ?_⟩
    change ((boxLinear x).1, circleChart (circleChart.symm (boxLinear x).2)) ∈ boxCoord
    erw [circleChart.right_inv h2]
    exact hx
  map_target' p hp := by
    change boxLinear (boxLinear.symm _) ∈ boxCoord
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact hp.2
  left_inv' x hx := by
    have h2 : (boxLinear x).2 ∈ circleChart.target := circleBox_subset hx.2
    change boxLinear.symm ((boxLinear x).1, circleChart (circleChart.symm (boxLinear x).2)) = x
    erw [circleChart.right_inv h2]
    exact boxLinear.symm_apply_apply x
  right_inv' p hp := by
    change (ULift.up (boxLinear (boxLinear.symm _)).1,
      circleChart.symm (boxLinear (boxLinear.symm (p.1.down, circleChart p.2))).2) = p
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact Prod.ext rfl (circleChart.left_inv hp.1)
  open_source := isOpen_boxSet
  open_target := by
    have hc : ContinuousOn (fun p : PlaneLift.{u} × Circle => (p.1.down, circleChart p.2))
        {p | p.2 ∈ circleChart.source} :=
      (continuous_uliftDown.comp continuous_fst).continuousOn.prodMk
        (circleChart.contMDiffOn_toFun.continuousOn.comp continuous_snd.continuousOn fun p hp => hp)
    exact hc.isOpen_inter_preimage (circleChart.open_source.preimage continuous_snd)
      isOpen_boxCoord
  contMDiffOn_toFun := by
    have h1 : ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, ℂ) ∞ (fun x : E3 => (boxLinear x).1) :=
      (contDiff_fst.comp boxLinear.contDiff).contMDiff
    have h2 : ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, E1) ∞ (fun x : E3 => (boxLinear x).2) :=
      (contDiff_snd.comp boxLinear.contDiff).contMDiff
    exact (contMDiff_planeLift_up.comp h1).contMDiffOn.prodMk
      (circleChart.contMDiffOn_invFun.comp h2.contMDiffOn fun x hx => circleBox_subset hx.2)
  contMDiffOn_invFun := by
    have hg : ContMDiffOn (𝓘(ℝ, ℂ).prod (𝓡 1)) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, E1)) ∞
        (fun p : PlaneLift.{u} × Circle => (p.1.down, circleChart p.2))
        {p | p.2 ∈ circleChart.source ∧ (p.1.down, circleChart p.2) ∈ boxCoord} :=
      (contMDiff_planeLift_down.comp contMDiff_fst).contMDiffOn.prodMk
        (circleChart.contMDiffOn_toFun.comp contMDiff_snd.contMDiffOn fun p hp => hp.1)
    have hL : ContMDiff (𝓘(ℝ, ℂ).prod 𝓘(ℝ, E1)) 𝓘(ℝ, E3) ∞ (boxLinear.symm : ℂ × E1 → E3) := by
      rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
      exact boxLinear.symm.contDiff.contMDiff
    exact hL.comp_contMDiffOn hg

theorem planeCircleBox_apply (x : E3) :
    planeCircleBox.{u} x = (ULift.up (boxLinear x).1, circleChart.symm (boxLinear x).2) := rfl

theorem planeCircleBox_source : (planeCircleBox.{u}).source = boxSet := rfl

theorem planeCircleBox_norm {x : E3} (hx : x ∈ boxSet) : ‖(planeCircleBox.{u} x).1.down‖ < 1 / 4 :=
  mem_ball_zero_iff.mp hx.1

/-- The linear reflection of the box induced by the conjugation. -/
def boxReflection : E3 ≃L[ℝ] E3 :=
  boxLinear.trans ((Complex.conjCLE.prodCongr (ContinuousLinearEquiv.refl ℝ E1)).trans
    boxLinear.symm)

theorem boxLinear_boxReflection (x : E3) :
    boxLinear (boxReflection x) = (Complex.conjCLE (boxLinear x).1, (boxLinear x).2) := by
  change boxLinear (boxLinear.symm _) = _
  rw [ContinuousLinearEquiv.apply_symm_apply]
  rfl

theorem boxReflection_mem {x : E3} (hx : x ∈ boxSet) : boxReflection x ∈ boxSet := by
  change boxLinear (boxReflection x) ∈ boxCoord
  rw [boxLinear_boxReflection]
  refine ⟨?_, hx.2⟩
  have h1 := hx.1
  rw [mem_ball_zero_iff] at h1 ⊢
  change ‖(starRingEnd ℂ) (boxLinear x).1‖ < 1 / 4
  rwa [Complex.norm_conj]

/-- **Equivariance.** The conjugation acts on the box chart through the linear reflection. -/
theorem planeCircleBox_conj (x : E3) :
    planeCircleConj (planeCircleBox.{u} x) = planeCircleBox.{u} (boxReflection x) := by
  rw [planeCircleBox_apply, planeCircleBox_apply, boxLinear_boxReflection]
  rfl

theorem boxReflection_det : LinearMap.det (boxReflection : E3 →ₗ[ℝ] E3) = -1 := by
  let K : ℂ × E1 →ₗ[ℝ] ℂ × E1 :=
    ((Complex.conjCLE.prodCongr (ContinuousLinearEquiv.refl ℝ E1) : ℂ × E1 →L[ℝ] ℂ × E1) :
      ℂ × E1 →ₗ[ℝ] ℂ × E1)
  have hK : LinearMap.det K = -1 := by
    have h : K = (Complex.conjAe.toLinearEquiv.toLinearMap).prodMap LinearMap.id :=
      LinearMap.ext fun p => rfl
    rw [h, LinearMap.det_prodMap, Complex.det_conjAe, LinearMap.det_id, mul_one]
  have h : (boxReflection : E3 →ₗ[ℝ] E3) =
      (boxLinear.symm.toLinearEquiv : ℂ × E1 →ₗ[ℝ] E3) ∘ₗ K ∘ₗ
        (boxLinear.symm.toLinearEquiv.symm : E3 →ₗ[ℝ] ℂ × E1) :=
    LinearMap.ext fun x => rfl
  rw [h, LinearMap.det_conj, hK]

/-! ### The box in the solid torus and in a tube -/

/-- The box chart of the solid torus. -/
def solidBox : PartialDiffeomorph 𝓘(ℝ, E3) (𝓡∂ 3) E3 solidSet.{u} ∞ :=
  planeCircleBox.trans solidInteriorPD.symm

theorem planeCircleBox_mem_interior {x : E3} (hx : x ∈ boxSet) :
    planeCircleBox.{u} x ∈ interior solidSet.{u} :=
  mem_interior_solidSet ((planeCircleBox_norm.{u} hx).trans (by norm_num))

theorem solidBox_source : (solidBox.{u}).source = boxSet := by
  ext x
  constructor
  · exact fun hx => hx.1
  · exact fun hx => ⟨hx, planeCircleBox_mem_interior hx⟩

theorem solidBox_val {x : E3} (hx : x ∈ boxSet) : (solidBox.{u} x).val = planeCircleBox.{u} x :=
  solidInteriorPD_symm_val (planeCircleBox_mem_interior hx)

theorem solidBox_norm {x : E3} (hx : x ∈ boxSet) : ‖(solidBox.{u} x).val.1.down‖ < 1 / 4 := by
  rw [solidBox_val hx]
  exact planeCircleBox_norm hx

theorem solidBox_target_interior : (solidBox.{u}).target ⊆ (𝓡∂ 3).interior solidSet.{u} := by
  intro y hy
  have hs : solidBox.symm y ∈ boxSet := by
    rw [← solidBox_source]
    exact solidBox.map_target hy
  have he : solidBox (solidBox.symm y) = y := solidBox.right_inv hy
  change (𝓡∂ 3).IsInteriorPoint y
  rw [solidSet_isInteriorPoint_iff, ← he]
  exact (solidBox_norm hs).trans (by norm_num)

theorem solidBox_target_norm {y : solidSet.{u}} (hy : y ∈ (solidBox.{u}).target) :
    ‖y.val.1.down‖ < 1 / 4 := by
  have hs : solidBox.symm y ∈ boxSet := by
    rw [← solidBox_source]
    exact solidBox.map_target hy
  have he : solidBox (solidBox.symm y) = y := solidBox.right_inv hy
  rw [← he]
  exact solidBox_norm hs

/-- **Equivariance in the solid torus.** -/
theorem solidConj_solidBox (ε : Bool) {x : E3} (hx : x ∈ boxSet) :
    solidConj ε (solidBox.{u} x) = solidBox.{u} (if ε then boxReflection x else x) := by
  cases ε
  · rfl
  · apply Subtype.ext
    simp only [solidConj_val, ↓reduceIte]
    rw [solidBox_val hx, solidBox_val (boxReflection_mem hx), ← planeCircleBox_conj]
    rfl

theorem contMDiff_planeCircleScale (a : ℝ) :
    ContMDiff (𝓘(ℝ, ℂ).prod (𝓡 1)) (𝓘(ℝ, ℂ).prod (𝓡 1)) ∞
      (fun p : PlaneLift.{u} × Circle => (ULift.up (a • p.1.down), p.2)) :=
  (contMDiff_planeLift_up.comp
    (((a • (ContinuousLinearMap.id ℝ ℂ)).contDiff.contMDiff).comp
      (contMDiff_planeLift_down.comp contMDiff_fst))).prodMk contMDiff_snd

/-- The scaling `w ↦ w / 3` of the plane factor. -/
def planeCircleThird : (PlaneLift.{u} × Circle) ≃ₘ⟮𝓘(ℝ, ℂ).prod (𝓡 1), 𝓘(ℝ, ℂ).prod (𝓡 1)⟯
    (PlaneLift.{u} × Circle) where
  toFun p := (ULift.up ((1 / 3 : ℝ) • p.1.down), p.2)
  invFun p := (ULift.up ((3 : ℝ) • p.1.down), p.2)
  left_inv p := by
    apply Prod.ext
    · apply ULift.ext
      simp
    · rfl
  right_inv p := by
    apply Prod.ext
    · apply ULift.ext
      simp
    · rfl
  contMDiff_toFun := contMDiff_planeCircleScale (1 / 3)
  contMDiff_invFun := contMDiff_planeCircleScale 3

/-- The radius-three solid torus filled into the unit tube of a tube chart. -/
def solidTubeFill {H M : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E3 H}
    [TopologicalSpace M] [ChartedSpace H M]
    (φ : PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) I (PlaneLift.{u} × Circle) M ∞)
    (x : solidSet.{u}) : M :=
  φ (ULift.up (x.val.1.down / 3), x.val.2)

section Tube

variable {H M : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E3 H}
  [TopologicalSpace M] [ChartedSpace H M]
  (φ : PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) I (PlaneLift.{u} × Circle) M ∞)

/-- The box chart pushed into a manifold through a tube chart. -/
def tubeBox : PartialDiffeomorph 𝓘(ℝ, E3) I E3 M ∞ :=
  (planeCircleBox.trans planeCircleThird.toPartialDiffeomorph).trans φ

theorem tubeBox_apply (x : E3) :
    tubeBox φ x = φ (ULift.up ((1 / 3 : ℝ) • (planeCircleBox.{u} x).1.down),
      (planeCircleBox.{u} x).2) := rfl

theorem tubeBox_source (h3 : {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 3} ⊆ φ.source) :
    (tubeBox φ).source = boxSet := by
  ext x
  constructor
  · exact fun hx => hx.1.1
  · intro hx
    refine ⟨⟨hx, mem_univ _⟩, h3 ?_⟩
    change ‖(1 / 3 : ℝ) • (planeCircleBox.{u} x).1.down‖ ≤ 3
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 3)]
    have := planeCircleBox_norm.{u} hx
    nlinarith [norm_nonneg (planeCircleBox.{u} x).1.down]

theorem tubeBox_target_subset : (tubeBox φ).target ⊆ φ.target := fun _ hy => hy.1

/-- The fill of the solid box is the tube box. -/
theorem solidTubeFill_solidBox {x : E3} (hx : x ∈ boxSet) :
    solidTubeFill φ (solidBox.{u} x) = tubeBox φ x := by
  rw [solidTubeFill, solidBox_val hx, tubeBox_apply]
  congr 3
  rw [div_eq_inv_mul, Complex.real_smul]
  push_cast
  ring

end Tube

end GC.GraphManifold.Assembly
