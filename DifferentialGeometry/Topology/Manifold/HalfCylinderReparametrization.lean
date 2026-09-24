import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Topology.Order.Compact

set_option autoImplicit false
noncomputable section

open Set Function TopologicalSpace Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.Manifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H}

private abbrev positiveProduct : Opens (M × ℝ) := ⟨univ ×ˢ Ioi (0 : ℝ),isOpen_univ.prod isOpen_Ioi⟩

variable (F : (M × ℝ) ≃ₘ⟮I.prod 𝓘(ℝ), I.prod 𝓘(ℝ)⟯ (M × ℝ))
  (hfix : ∀ p : (M × ℝ), p.2 ≤ 0 → F p = p)

include hfix in
theorem halfCylinder_image_nonneg_iff (p : (M × ℝ)) : 0 ≤ (F p).2 ↔ 0 ≤ p.2 := by
  constructor
  · intro hp
    by_contra hn
    have hneg : p.2 < 0 := lt_of_not_ge hn
    rw [hfix p hneg.le] at hp
    exact (not_le_of_gt hneg) hp
  · intro hp
    by_contra hn
    have hneg : (F p).2 < 0 := lt_of_not_ge hn
    have heq : F p = p := F.injective (hfix (F p) hneg.le)
    rw [heq] at hneg
    exact (not_lt_of_ge hp) hneg

include hfix in
theorem halfCylinder_image_pos_iff (p : (M × ℝ)) : 0 < (F p).2 ↔ 0 < p.2 := by
  have hiff : (F p).2 ≤ 0 ↔ p.2 ≤ 0 := by
    constructor
    · intro hp
      have heq : F p = p := F.injective (hfix (F p) hp)
      exact heq ▸ hp
    · intro hp
      rw [hfix p hp]
      exact hp
  exact not_le.symm.trans (hiff.not.trans not_le)

def halfCylinderHomeomorph : {p : M × ℝ // 0 ≤ p.2} ≃ₜ {p : M × ℝ // 0 ≤ p.2} :=
  F.toHomeomorph.subtype (fun p => (halfCylinder_image_nonneg_iff F hfix p).symm)

def positiveCylinderDiffeomorph : (positiveProduct (M := M)) ≃ₘ⟮I.prod 𝓘(ℝ), I.prod 𝓘(ℝ)⟯ (positiveProduct (M := M)) where
  toEquiv := (F.toHomeomorph.subtype (fun p => by
    change (True ∧ 0 < p.2) ↔ (True ∧ 0 < (F p).2)
    exact and_congr_right fun _ => (halfCylinder_image_pos_iff F hfix p).symm)).toEquiv
  contMDiff_toFun := by
    apply (ContMDiff.subtypeVal_comp_iff (positiveProduct (M := M)) _).mp
    exact F.contMDiff.comp contMDiff_subtype_val
  contMDiff_invFun := by
    apply (ContMDiff.subtypeVal_comp_iff (positiveProduct (M := M)) _).mp
    exact F.symm.contMDiff.comp contMDiff_subtype_val

theorem range_comp_halfCylinder
    {X : Type*} (f : {p : M × ℝ // 0 ≤ p.2} → X) :
    range (f ∘ halfCylinderHomeomorph F hfix) = range f :=
  (halfCylinderHomeomorph F hfix).surjective.range_comp f


theorem exists_axial_bound_of_compact_support
    (K : Set (M × ℝ)) (hK : IsCompact K) (hF : EqOn F id Kᶜ) :
    ∃ b : ℝ, ∀ q : (M × ℝ), b ≤ q.2 → F q = q := by
  obtain ⟨B, hB⟩ := hK.bddAbove_image continuous_snd.continuousOn
  refine ⟨B + 1, ?_⟩
  intro q hq
  apply hF
  intro hqK
  have hle := hB (mem_image_of_mem Prod.snd hqK)
  linarith

end DifferentialGeometry.Topology.Manifold
