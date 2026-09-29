import DifferentialGeometry.Topology.ThreeManifold.CutCap
import DifferentialGeometry.Topology.Manifold.HalfCollarExtension
import Mathlib.Geometry.Manifold.Instances.Icc

set_option autoImplicit false
noncomputable section

open Set Manifold Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology

universe u
local notation "E1" => EuclideanSpace ℝ (Fin 1)
local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Sphere" => Metric.sphere (0 : E3) 1
local notation "Half" => Ico (0 : ℝ) (1 / 2)
local notation "Interval" => Icc (-2 : ℝ) 2
local notation "CI" => ModelWithCorners.prod (𝓡 2) (𝓡∂ 1)

private local instance tubeBounds : Fact ((-2 : ℝ) < 2) := ⟨by norm_num⟩
private local instance halfCharts : ChartedSpace (EuclideanHalfSpace 1) Half :=
  Manifold.halfClosedIntervalChartedSpace (by norm_num : (0 : ℝ) < 1 / 2)
private local instance halfSmooth : IsManifold (𝓡∂ 1) ∞ Half :=
  Manifold.halfClosedInterval_isManifold (by norm_num : (0 : ℝ) < 1 / 2)

private def retainedTimeAffine (side : Bool) : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞ where
  toFun t := if side then 1 + t else -1 - t
  invFun t := if side then t - 1 else -1 - t
  left_inv t := by cases side <;> simp
  right_inv t := by cases side <;> simp
  contMDiff_toFun := by
    change ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun t : ℝ => if side then 1 + t else -1 - t)
    cases side <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;>
      apply ContDiff.contMDiff <;> fun_prop
  contMDiff_invFun := by
    change ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun t : ℝ => if side then t - 1 else -1 - t)
    cases side <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;>
      apply ContDiff.contMDiff <;> fun_prop

namespace SphericalTubeSystem

def coreCollarParameter (side : Bool) (t : Half) : Interval :=
  ⟨if side then 1 + t.val else -1 - t.val, by
    cases side <;> change -2 ≤ _ ∧ _ ≤ 2 <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;>
      constructor <;> linarith [t.property.1, t.property.2]⟩

theorem coreCollarParameter_val (side : Bool) (t : Half) :
    (coreCollarParameter side t).val =
      (boundaryLevel side).val + (if side then t.val else -t.val) := by
  cases side <;> simp [coreCollarParameter, boundaryLevel]
  ring

@[simp] theorem coreCollarParameter_zero (side : Bool) :
    coreCollarParameter side (⟨0, by constructor <;> norm_num⟩ : Half) = boundaryLevel side := by
  apply Subtype.ext
  cases side <;> simp [coreCollarParameter, boundaryLevel]

private theorem coreCollarParameter_contMDiff (side : Bool) :
    ContMDiff (𝓡∂ 1) (𝓡∂ 1) ∞ (coreCollarParameter side) := by
  have hi := (Manifold.isSmoothEmbedding_halfClosedInterval_inclusion
    (by norm_num : (0 : ℝ) < 1 / 2)).contMDiff
  have h : ContMDiff (𝓡∂ 1) 𝓘(ℝ, ℝ) ∞
      (fun t : Half => retainedTimeAffine side t.val) :=
    (retainedTimeAffine side).contMDiff.comp hi
  exact (contMDiff_iff_comp_subtypeVal_Icc (n := ∞)).mpr ⟨h.continuous.subtype_mk _, h⟩

private theorem coreCollarParameter_injective_mfderiv (side : Bool) (t : Half) :
    Injective (mfderiv (𝓡∂ 1) (𝓡∂ 1) (coreCollarParameter side) t) := by
  have hi : IsSmoothEmbedding (𝓡∂ 1) 𝓘(ℝ, ℝ) ∞ (Subtype.val : Half → ℝ) :=
    Manifold.isSmoothEmbedding_halfClosedInterval_inclusion (by norm_num : (0 : ℝ) < 1 / 2)
  have hchain := mfderiv_comp t
    ((retainedTimeAffine side).contMDiff.mdifferentiableAt (by simp))
    (hi.contMDiff.mdifferentiableAt (by simp))
  have hj : Injective (mfderiv (𝓡∂ 1) 𝓘(ℝ, ℝ)
      ((Subtype.val : Interval → ℝ) ∘ coreCollarParameter side) t) := by
    rw [show (Subtype.val : Interval → ℝ) ∘ coreCollarParameter side =
      retainedTimeAffine side ∘ (Subtype.val : Half → ℝ) from rfl, hchain]
    exact ((retainedTimeAffine side).mfderivToContinuousLinearEquiv (by simp) t.val).injective.comp
      ((hi.isImmersion.isImmersionAt t).mfderiv_injective (by simp))
  rw [mfderiv_comp t
    ((contMDiff_subtypeVal_Icc (x := (-2 : ℝ)) (y := 2) (n := ∞)).mdifferentiableAt (by simp))
    ((coreCollarParameter_contMDiff side).mdifferentiableAt (by simp))] at hj
  change Injective ((mfderiv (𝓡∂ 1) 𝓘(ℝ, ℝ) (Subtype.val : Interval → ℝ)
    (coreCollarParameter side t)) ∘ mfderiv (𝓡∂ 1) (𝓡∂ 1) (coreCollarParameter side) t) at hj
  exact hj.of_comp

variable {M : ClosedOrientedManifold.{u} 3} (T : SphericalTubeSystem M)

theorem tube_coreCollarParameter_mem_core (b : T.Boundary) (z : Sphere) (t : Half) :
    T.tube b.1 (z, coreCollarParameter b.2 t) ∈ T.core := by
  intro h
  obtain ⟨a, y, hy, heq⟩ := by
    simpa only [core, mem_compl_iff, mem_iUnion, removedBand, mem_image] using h
  have ha : a = b.1 := by
    by_contra hne
    exact Set.disjoint_left.mp (T.disjoint hne) (Set.mem_range_self y)
      ⟨(z, coreCollarParameter b.2 t), heq.symm⟩
  subst a
  have htime := congrArg (fun q : Sphere × Interval => q.2.val)
    ((T.smooth b.1).isEmbedding.injective heq)
  rcases b with ⟨a, side⟩
  cases side <;> dsimp [coreCollarParameter, retainedTimeAffine] at htime <;>
    rcases hy with ⟨hlo, hhi⟩ <;> linarith [t.property.1]

end SphericalTubeSystem

namespace SphericalCapping

variable {M N : ClosedOrientedManifold.{u} 3} {T : SphericalTubeSystem M}
  (C : SphericalCapping M N T)

private local instance cellCharts : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  Handle.closedCellChartedSpaceSucc 2
private local instance cellSmooth : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) := Handle.closedCellIsManifold 2

def coreBoundaryHalfCollar (b : T.Boundary) (p : Sphere × Half) : T.core :=
  ⟨T.tube b.1 (C.attaching b p.1, SphericalTubeSystem.coreCollarParameter b.2 p.2),
    T.tube_coreCollarParameter_mem_core b (C.attaching b p.1) p.2⟩

theorem coreBoundaryHalfCollar_val (b : T.Boundary) (p : Sphere × Half) :
    (C.coreBoundaryHalfCollar b p).val =
      T.tube b.1 (C.attaching b p.1, SphericalTubeSystem.coreCollarParameter b.2 p.2) := rfl

@[simp] theorem coreBoundaryHalfCollar_zero (b : T.Boundary) (z : Sphere) :
    C.coreBoundaryHalfCollar b (z, ⟨0, by constructor <;> norm_num⟩) =
      T.coreBoundarySphere b (C.attaching b z) := by
  apply Subtype.ext
  change T.tube b.1 (C.attaching b z, SphericalTubeSystem.coreCollarParameter b.2 _) = _
  rw [SphericalTubeSystem.coreCollarParameter_zero]
  rfl

theorem coreBoundaryHalfCollar_contMDiff (b : T.Boundary) :
    let _ := C.coreCharts
    ContMDiff CI (𝓡∂ 3) ∞ (C.coreBoundaryHalfCollar b) := by
  let _ := C.coreCharts
  let _ := C.coreSmooth
  have h : ContMDiff CI (𝓡 3) ∞
      (fun p : Sphere × Half => T.tube b.1
        (C.attaching b p.1, SphericalTubeSystem.coreCollarParameter b.2 p.2)) :=
    (T.smooth b.1).contMDiff.comp
      ((C.attaching b).contMDiff.prodMap (SphericalTubeSystem.coreCollarParameter_contMDiff b.2))
  exact (ContMDiff.iff_comp_isImmersion C.core_induced.isImmersion).mpr
    ⟨h.continuous.subtype_mk _, h⟩

theorem coreBoundaryHalfCollar_mfderiv_bijective (b : T.Boundary) (p : Sphere × Half) :
    let _ := C.coreCharts
    Function.Bijective (mfderiv CI (𝓡∂ 3) (C.coreBoundaryHalfCollar b) p) := by
  let _ := C.coreCharts
  let _ := C.coreSmooth
  let k : Sphere × Half → Sphere × Interval :=
    Prod.map (C.attaching b) (SphericalTubeSystem.coreCollarParameter b.2)
  have hk : ContMDiff CI CI ∞ k := (C.attaching b).contMDiff.prodMap
    (SphericalTubeSystem.coreCollarParameter_contMDiff b.2)
  have hDk : Injective (mfderiv CI CI k p) := by
    rw [mfderiv_prodMap ((C.attaching b).contMDiff.mdifferentiableAt (by simp))
      ((SphericalTubeSystem.coreCollarParameter_contMDiff b.2).mdifferentiableAt (by simp))]
    exact ((C.attaching b).mfderivToContinuousLinearEquiv (by simp) p.1).injective.prodMap
      (SphericalTubeSystem.coreCollarParameter_injective_mfderiv b.2 p.2)
  have hD : Injective (mfderiv CI (𝓡 3)
      ((Subtype.val : T.core → M.Carrier) ∘ C.coreBoundaryHalfCollar b) p) := by
    change Injective (mfderiv CI (𝓡 3) ((T.tube b.1) ∘ k) p)
    rw [mfderiv_comp p ((T.smooth b.1).contMDiff.mdifferentiableAt (by simp))
      (hk.mdifferentiableAt (by simp))]
    exact ((T.smooth b.1).isImmersion.isImmersionAt _ |>.mfderiv_injective (by simp)).comp hDk
  rw [mfderiv_comp p (C.core_induced.contMDiff.mdifferentiableAt (by simp))
    ((C.coreBoundaryHalfCollar_contMDiff b).mdifferentiableAt (by simp))] at hD
  change Injective ((mfderiv (𝓡∂ 3) (𝓡 3) (Subtype.val : T.core → M.Carrier)
    (C.coreBoundaryHalfCollar b p)) ∘ mfderiv CI (𝓡∂ 3) (C.coreBoundaryHalfCollar b) p) at hD
  let L : (E2 × E1) →L[ℝ] E3 := mfderiv CI (𝓡∂ 3) (C.coreBoundaryHalfCollar b) p
  have hL : Injective L := hD.of_comp
  exact (L.toLinearMap.linearEquivOfInjective hL (by simp)).bijective

def coreInclusionHalfCollar (b : T.Boundary) : Sphere × Half → N.Carrier :=
  C.coreInclusion ∘ C.coreBoundaryHalfCollar b

@[simp] theorem coreInclusionHalfCollar_zero (b : T.Boundary) (z : Sphere) :
    C.coreInclusionHalfCollar b (z, ⟨0, by constructor <;> norm_num⟩) =
      C.cap b (sphereToClosedCell z) := by
  change C.coreInclusion (C.coreBoundaryHalfCollar b _) = _
  rw [C.coreBoundaryHalfCollar_zero, C.boundary_eq]

theorem coreInclusionHalfCollar_contMDiff (b : T.Boundary) :
    ContMDiff CI (𝓡 3) ∞ (C.coreInclusionHalfCollar b) :=
  by
    let _ := C.coreCharts
    let _ := C.coreSmooth
    exact C.core_embedding.contMDiff.comp (C.coreBoundaryHalfCollar_contMDiff b)

theorem coreInclusionHalfCollar_mfderiv_bijective (b : T.Boundary) (p : Sphere × Half) :
    Function.Bijective (mfderiv CI (𝓡 3) (C.coreInclusionHalfCollar b) p) := by
  let _ := C.coreCharts
  let _ := C.coreSmooth
  rw [coreInclusionHalfCollar, mfderiv_comp p
    (C.core_embedding.contMDiff.mdifferentiableAt (by simp))
    ((C.coreBoundaryHalfCollar_contMDiff b).mdifferentiableAt (by simp))]
  exact (Manifold.bijective_mfderiv_of_isImmersionAt (𝓡∂ 3) (𝓡 3) C.coreInclusion _
    (C.core_embedding.isImmersion.isImmersionAt _) rfl).comp
    (C.coreBoundaryHalfCollar_mfderiv_bijective b p)

theorem exists_coreBoundaryCollar (b : T.Boundary) :
    ∃ d : SmoothTwoSidedCollar (𝓡 2) (𝓡 3) (C.cap b ∘ sphereToClosedCell),
      ∃ hwidth : d.radius ≤ 1 / 2,
      ∀ (p : Sphere × symmetricOpenInterval d.radius) (hp : 0 ≤ p.2.val),
        d.toFun p = C.coreInclusionHalfCollar b
          (p.1, ⟨p.2.val, hp, p.2.property.2.trans_le hwidth⟩) := by
  have hinj : Function.Injective (fun z : Sphere =>
      C.coreInclusionHalfCollar b (z, (⟨0, by constructor <;> norm_num⟩ : Half))) := by
    intro z w h
    simp only [C.coreInclusionHalfCollar_zero] at h
    exact Subtype.ext (congrArg (fun x : ClosedCell 3 => x.val) ((C.cap_embedding b).isEmbedding.injective h))
  obtain ⟨d, hwidth, hd⟩ := exists_smoothTwoSidedCollar_of_halfClosedInterval
    (J := 𝓡 2) (I := 𝓡 3) (by norm_num : (0 : ℝ) < 1 / 2)
    (C.coreInclusionHalfCollar b) (C.coreInclusionHalfCollar_contMDiff b) hinj
    (fun z => C.coreInclusionHalfCollar_mfderiv_bijective b (z, _))
  let d' : SmoothTwoSidedCollar (𝓡 2) (𝓡 3) (C.cap b ∘ sphereToClosedCell) :=
    { radius := d.radius
      radius_pos := d.radius_pos
      neighborhood := d.neighborhood
      toDiffeomorph := d.toDiffeomorph
      zero_eq := fun z => (d.zero_eq z).trans (C.coreInclusionHalfCollar_zero b z) }
  exact ⟨d', hwidth, hd⟩

end SphericalCapping
end DifferentialGeometry.Topology
