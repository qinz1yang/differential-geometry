import DifferentialGeometry.Topology.LoopSpace.Basic
import Mathlib.Topology.Path
import Mathlib.Topology.Maps.Proper.Basic








noncomputable section

open Set Function ContinuousMap
open scoped Topology

namespace DifferentialGeometry.Topology


abbrev basedCircleLoop {Q : Type*} [TopologicalSpace Q] (q : Q) :=
  {γ : freeLoop Q // γ 0 = q}


theorem unitInterval_to_loopCircle_surjective :
    Surjective (fun t : unitInterval => (t.val : loopCircle)) := by
  intro θ
  have hmem : θ ∈ (fun t : ℝ => (t : loopCircle)) '' Icc 0 1 := by
    have h : (fun t : ℝ => (t : loopCircle)) '' Icc 0 1 = univ := by
      simpa only [zero_add] using AddCircle.coe_image_Icc_eq (1 : ℝ) 0
    rw [h]
    exact mem_univ θ
  obtain ⟨t, ht, hθ⟩ := hmem
  exact ⟨⟨t, ht⟩, hθ⟩



theorem unitInterval_to_loopCircle_prod_quotient (K : Type*) [TopologicalSpace K] :
    _root_.Topology.IsQuotientMap
      (Prod.map (id : K → K) (fun t : unitInterval => (t.val : loopCircle))) := by
  have hc : Continuous (fun t : unitInterval => (t.val : loopCircle)) :=
    (AddCircle.continuous_mk' (1 : ℝ)).comp continuous_subtype_val
  have hp : IsProperMap (Prod.map (id : K → K)
      (fun t : unitInterval => (t.val : loopCircle))) := isProperMap_id.prodMap hc.isProperMap
  exact hp.isClosedMap.isQuotientMap hp.continuous
    ((surjective_id : Surjective (id : K → K)).prodMap unitInterval_to_loopCircle_surjective)

variable {Q : Type*} [TopologicalSpace Q] {q : Q}


def pathToCircle (p : Path q q) : freeLoop Q :=
  ⟨AddCircle.liftIco 1 0 p.extend,
    AddCircle.liftIco_zero_continuous (by rw [p.extend_zero, p.extend_one]) p.continuous_extend.continuousOn⟩

theorem pathToCircle_zero (p : Path q q) : pathToCircle p 0 = q := by
  change AddCircle.liftIco 1 0 p.extend ((0 : ℝ) : loopCircle) = q
  rw [AddCircle.liftIco_zero_coe_apply (by norm_num : (0 : ℝ) ∈ Ico 0 1), p.extend_zero]



theorem pathToCircle_coe (p : Path q q) (t : unitInterval) :
    pathToCircle p (t.val : loopCircle) = p t := by
  by_cases ht : (t : ℝ) < 1
  · change AddCircle.liftIco 1 0 p.extend (t.val : loopCircle) = p t
    rw [AddCircle.liftIco_zero_coe_apply ⟨t.property.1, ht⟩]
    exact p.extend_extends' t
  · have ht1 : t = 1 := Subtype.ext (le_antisymm t.property.2 (le_of_not_gt ht))
    subst t
    change pathToCircle p ((1 : ℝ) : loopCircle) = p 1
    rw [AddCircle.coe_period, Path.target]
    exact pathToCircle_zero p


theorem continuous_pathToCircle : Continuous (pathToCircle (q := q)) := by
  apply continuous_of_continuous_uncurry
  apply (unitInterval_to_loopCircle_prod_quotient (Path q q)).continuous_iff.mpr
  have hc : Continuous (fun p : Path q q × unitInterval => p.1 p.2) :=
    Path.continuous_uncurry_iff.mpr continuous_id
  apply hc.congr
  intro p
  exact (pathToCircle_coe p.1 p.2).symm


def circleToPath (γ : basedCircleLoop q) : Path q q where
  toFun t := γ.val (t.val : loopCircle)
  continuous_toFun := γ.val.continuous.comp
    ((AddCircle.continuous_mk' (1 : ℝ)).comp continuous_subtype_val)
  source' := γ.property
  target' := by
    change γ.val ((1 : ℝ) : loopCircle) = q
    simpa only [AddCircle.coe_period] using γ.property


theorem continuous_circleToPath : Continuous (circleToPath (q := q)) := by
  apply Path.continuous_uncurry_iff.mp
  exact (continuous_eval.comp ((continuous_subtype_val.comp continuous_fst).prodMk
    ((AddCircle.continuous_mk' (1 : ℝ)).comp (continuous_subtype_val.comp continuous_snd))))



def basedPathCircleHomeomorph (q : Q) : Path q q ≃ₜ basedCircleLoop q where
  toFun p := ⟨pathToCircle p, pathToCircle_zero p⟩
  invFun := circleToPath
  left_inv p := by ext t; exact pathToCircle_coe p t
  right_inv γ := by
    apply Subtype.ext
    ext θ
    obtain ⟨t, rfl⟩ := unitInterval_to_loopCircle_surjective θ
    exact pathToCircle_coe (circleToPath γ) t
  continuous_toFun := continuous_pathToCircle.subtype_mk _
  continuous_invFun := continuous_circleToPath

end DifferentialGeometry.Topology
