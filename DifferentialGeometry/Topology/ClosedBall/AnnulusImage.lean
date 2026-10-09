/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.ClosedBall.AnnulusHomeomorph
import DifferentialGeometry.Topology.OpenEmbeddingFrontier
import Mathlib.Topology.UnitInterval

open Set Metric

namespace DifferentialGeometry.Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem interior_range_sphere_prod_unitInterval
    (g : sphere (0 : E) 1 × unitInterval → E)
    (hg : Continuous g) (hinj : Function.Injective g) :
    interior (range g) = g '' {p | (p.2 : ℝ) ∈ Ioo (0 : ℝ) 1} := by
  let e : (sphere (0 : E) 1 × unitInterval) ≃ₜ {x : E | ‖x‖ ∈ Icc (1 : ℝ) 2} :=
    ((Homeomorph.refl _).prodCongr (iccHomeoI (1 : ℝ) 2 (by norm_num)).symm).trans
      (sphereProdIccHomeomorphAnnulus 1 2 (by norm_num))
  have hnorm (p : sphere (0 : E) 1 × unitInterval) : ‖(e p : E)‖ = (p.2 : ℝ) + 1 := by
    change ‖(((iccHomeoI (1 : ℝ) 2 (by norm_num)).symm p.2 : ℝ)) • (p.1 : E)‖ = _
    rw [iccHomeoI_symm_apply_coe]
    have hpos : 0 < (p.2 : ℝ) + 1 := by linarith [p.2.property.1]
    simp only [one_mul, norm_smul, Real.norm_eq_abs,
      show (2 : ℝ) - 1 = 1 from by norm_num,
      abs_of_pos hpos, mem_sphere_zero_iff_norm.mp p.1.property, mul_one]
  have hrange : range (g ∘ e.symm) = range g := by
    rw [range_comp, e.symm.surjective.range_eq, image_univ]
  have h := interior_range_eq_image_preimage_interior (isCompact_norm_band (E := E) 1 2)
    (g ∘ e.symm) (hg.comp e.symm.continuous) (hinj.comp e.symm.injective)
  rw [hrange, interior_norm_band (by norm_num) (by norm_num)] at h
  rw [h]
  apply Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    refine ⟨e.symm x, ?_, rfl⟩
    have heq := hnorm (e.symm x)
    rw [e.apply_symm_apply] at heq
    change (1 : ℝ) < ‖(x : E)‖ ∧ ‖(x : E)‖ < 2 at hx
    change 0 < ((e.symm x).2 : ℝ) ∧ ((e.symm x).2 : ℝ) < 1
    constructor <;> linarith [hx.1, hx.2]
  · rintro y ⟨p, hp, rfl⟩
    refine ⟨e p, ?_, by simp⟩
    change (1 : ℝ) < ‖(e p : E)‖ ∧ ‖(e p : E)‖ < 2
    rw [hnorm]
    constructor <;> linarith [hp.1, hp.2]

theorem frontier_range_sphere_prod_unitInterval
    (g : sphere (0 : E) 1 × unitInterval → E)
    (hg : Continuous g) (hinj : Function.Injective g) :
    frontier (range g) =
      g '' {p | (p.2 : ℝ) = 0} ∪ g '' {p | (p.2 : ℝ) = 1} := by
  have heq : (univ : Set (sphere (0 : E) 1 × unitInterval)) \
      {p | (p.2 : ℝ) ∈ Ioo (0 : ℝ) 1} =
      {p | (p.2 : ℝ) = 0} ∪ {p | (p.2 : ℝ) = 1} := by
    ext p
    simp only [mem_sdiff, mem_univ, true_and, mem_ofPred_eq, mem_Ioo, mem_union]
    constructor
    · intro h
      rcases le_or_gt (p.2 : ℝ) 0 with h₀ | h₀
      · exact Or.inl (le_antisymm h₀ p.2.property.1)
      · exact Or.inr (le_antisymm p.2.property.2 (not_lt.mp (fun h₁ => h ⟨h₀, h₁⟩)))
    · rintro (h | h) <;> simp [h]
  rw [(isCompact_range hg).isClosed.frontier_eq,
    interior_range_sphere_prod_unitInterval g hg hinj,
    ← image_univ, ← image_sdiff hinj, heq, image_union]

noncomputable def sphereProdIooHomeomorphInteriorRange
    (g : sphere (0 : E) 1 × unitInterval → E)
    (hg : Continuous g) (hinj : Function.Injective g) :
    (sphere (0 : E) 1 × Ioo (0 : ℝ) 1) ≃ₜ interior (range g) := by
  let j : (sphere (0 : E) 1 × Ioo (0 : ℝ) 1) → sphere (0 : E) 1 × unitInterval :=
    Prod.map id (Set.inclusion Ioo_subset_Icc_self)
  have hj : _root_.Topology.IsEmbedding j :=
    _root_.Topology.IsEmbedding.id.prodMap (_root_.Topology.IsEmbedding.inclusion _)
  have hemb : _root_.Topology.IsEmbedding g := (hg.isClosedEmbedding hinj).isEmbedding
  have hrange : range (g ∘ j) = interior (range g) := by
    rw [interior_range_sphere_prod_unitInterval g hg hinj]
    ext y
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨j p, p.2.property, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨(p.1, ⟨(p.2 : ℝ), hp⟩), rfl⟩
  exact (hemb.comp hj).toHomeomorph.trans (Homeomorph.setCongr hrange)

@[simp]
theorem sphereProdIooHomeomorphInteriorRange_apply_coe
    (g : sphere (0 : E) 1 × unitInterval → E)
    (hg : Continuous g) (hinj : Function.Injective g)
    (p : sphere (0 : E) 1 × Ioo (0 : ℝ) 1) :
    (sphereProdIooHomeomorphInteriorRange g hg hinj p : E) =
      g (p.1, ⟨(p.2 : ℝ), Ioo_subset_Icc_self p.2.property⟩) := rfl

end DifferentialGeometry.Topology
