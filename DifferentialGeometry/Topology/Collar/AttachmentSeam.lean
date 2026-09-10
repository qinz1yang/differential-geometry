import DifferentialGeometry.Topology.Attachment.MappingCylinder
import DifferentialGeometry.Topology.Collar.Rescaling
import Mathlib.Topology.Piecewise
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Set Function Topology
set_option autoImplicit false
noncomputable section
namespace DifferentialGeometry.Topology.Collar

variable {B X : Type*} [TopologicalSpace B] [TopologicalSpace X] {ε : ℝ}

def attachmentSeam (f : C(B, X)) (c : C(B × Icc (0 : ℝ) ε, X))
    (a : Icc (0 : ℝ) ε)
    (hzero : ∀ p, c (p, ⟨0, ⟨le_rfl, a.property.1.trans a.property.2⟩⟩) = f p) :
    C(B × Icc (-1 : ℝ) 1, MappingCylinder f) := by
  classical
  let P : C(B × Icc (-1 : ℝ) 1, MappingCylinder f) :=
    (mappingCylinderProduct f).comp
      ⟨fun q => (q.1, ⟨max q.2.val 0, le_max_right _ _, max_le q.2.property.2 (by norm_num)⟩),
        by fun_prop⟩
  let N : C(B × Icc (-1 : ℝ) 1, MappingCylinder f) :=
    (mappingCylinderOriginal f).comp (c.comp
      ⟨fun q => (q.1, ⟨max (-a.val * q.2.val) 0, le_max_right _ _, by
        apply max_le
        · nlinarith [q.2.property.1, a.property.1, a.property.2]
        · exact a.property.1.trans a.property.2⟩), by fun_prop⟩)
  refine ⟨fun q => if 0 ≤ q.2.val then P q else N q, ?_⟩
  apply Continuous.if ?_ P.continuous N.continuous
  intro q hq
  have hh := (continuous_subtype_val.comp continuous_snd).frontier_preimage_subset (Ici (0 : ℝ)) hq
  have ht : q.2.val = 0 := by simpa only [mem_preimage, frontier_Ici, mem_singleton_iff, Function.comp_apply] using hh
  have hp : P q = mappingCylinderProduct f (q.1, 0) := by
    dsimp [P]
    congr 2
    apply Subtype.ext
    simp [ht]
  have hn : N q = mappingCylinderOriginal f (c (q.1, ⟨0, ⟨le_rfl, a.property.1.trans a.property.2⟩⟩)) := by
    dsimp [N]
    congr 3
    apply Subtype.ext
    simp [ht]
  rw [hp, hn, hzero]
  exact mappingCylinder_seam f q.1


theorem attachmentSeam_nonneg (f : C(B, X)) (c : C(B × Icc (0 : ℝ) ε, X))
    (a : Icc (0 : ℝ) ε)
    (hzero : ∀ p, c (p, ⟨0, ⟨le_rfl, a.property.1.trans a.property.2⟩⟩) = f p)
    (q : B × Icc (-1 : ℝ) 1) (hq : 0 ≤ q.2.val) :
    attachmentSeam f c a hzero q = mappingCylinderProduct f (q.1, ⟨q.2.val, hq, q.2.property.2⟩) := by
  simp [attachmentSeam, hq]

theorem attachmentSeam_nonpos (f : C(B, X)) (c : C(B × Icc (0 : ℝ) ε, X))
    (a : Icc (0 : ℝ) ε)
    (hzero : ∀ p, c (p, ⟨0, ⟨le_rfl, a.property.1.trans a.property.2⟩⟩) = f p)
    (q : B × Icc (-1 : ℝ) 1) (hq : q.2.val ≤ 0) :
    attachmentSeam f c a hzero q = mappingCylinderOriginal f
      (c (q.1, ⟨-a.val * q.2.val, mul_nonneg_of_nonpos_of_nonpos
        (neg_nonpos.mpr a.property.1) hq, by
          nlinarith [q.2.property.1, a.property.1, a.property.2]⟩)) := by
  by_cases ht : 0 ≤ q.2.val
  · have hq0 : q.2.val = 0 := le_antisymm hq ht
    rw [attachmentSeam_nonneg f c a hzero q ht]
    convert mappingCylinder_seam f q.1 using 1
    · congr 1
      apply Prod.ext
      · rfl
      · exact Subtype.ext hq0
    · rw [← hzero]
      congr 2
      apply Prod.ext
      · rfl
      · apply Subtype.ext
        simp [hq0]
  · have hm : 0 ≤ -a.val * q.2.val :=
      mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr a.property.1) hq
    dsimp only [attachmentSeam, ContinuousMap.coe_mk]
    rw [if_neg ht]
    simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk]
    congr 2
    apply Prod.ext
    · rfl
    · exact Subtype.ext (max_eq_left hm)

theorem attachmentSeam_realization (f : C(B, X)) (c : C(B × Icc (0 : ℝ) ε, X))
    (a : Icc (0 : ℝ) ε)
    (hzero : ∀ p, c (p, ⟨0, ⟨le_rfl, a.property.1.trans a.property.2⟩⟩) = f p)
    (hc : IsEmbedding c) (h2a : 2 * a.val ≤ ε)
    (σ : C(Icc (0 : ℝ) ε, Icc (0 : ℝ) ε))
    (hσnear : ∀ t : Icc (0 : ℝ) ε, t.val ≤ a.val → (σ t).val = t.val + a.val)
    (h : MappingCylinder f ≃ₜ X)
    (hO : ∀ x, h (mappingCylinderOriginal f x) = rescale c hc σ x)
    (hP : ∀ q : B × Icc (0 : ℝ) 1, h (mappingCylinderProduct f q) =
      c (q.1, ⟨a.val * (1 - q.2.val),
        ⟨mul_nonneg a.property.1 (sub_nonneg.mpr q.2.property.2), by
          nlinarith [q.2.property.1, a.property.1, a.property.2]⟩⟩))
    (q : B × Icc (-1 : ℝ) 1) :
    h (attachmentSeam f c a hzero q) =
      c (q.1, ⟨a.val * (1 - q.2.val),
        ⟨mul_nonneg a.property.1 (sub_nonneg.mpr q.2.property.2), by
          nlinarith [q.2.property.1, a.property.1]⟩⟩) := by
  by_cases ht : 0 ≤ q.2.val
  · rw [attachmentSeam_nonneg f c a hzero q ht, hP]
  · rw [attachmentSeam_nonpos f c a hzero q (le_of_lt (lt_of_not_ge ht)), hO, rescale_apply]
    congr 1
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      rw [hσnear _ (by dsimp; nlinarith [q.2.property.1, a.property.1])]
      ring

end DifferentialGeometry.Topology.Collar
