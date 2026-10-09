/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.MoiseChain
import DifferentialGeometry.Topology.PiecewiseLinear.AnnulusBoundary

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem IsPLAnnulusWithEnds.of_isPLHomeomorphOn {X Y J₀ J₁ : Set E3} {f : E3 → E3}
    (h : IsPLAnnulusWithEnds X J₀ J₁) (hf : IsPLHomeomorphOn f X Y) :
    IsPLAnnulusWithEnds Y (f '' J₀) (f '' J₁) := by
  obtain ⟨J, ρ, hJ, hρ, h₀, h₁⟩ := h
  exact ⟨J, f ∘ ρ, hJ, hρ.trans hf, by rw [image_comp, h₀], by rw [image_comp, h₁]⟩

theorem IsPLAnnulusWithEnds.of_isPLHomeomorphOn_eqOn {X Y J₀ J₁ : Set E3} {f : E3 → E3}
    (h : IsPLAnnulusWithEnds X J₀ J₁) (hf : IsPLHomeomorphOn f X Y)
    (hfix : EqOn f id (J₀ ∪ J₁)) : IsPLAnnulusWithEnds Y J₀ J₁ := by
  have h₀ : f '' J₀ = J₀ := by
    simpa only [image_id] using (hfix.mono subset_union_left).image_eq
  have h₁ : f '' J₁ = J₁ := by
    simpa only [image_id] using (hfix.mono subset_union_right).image_eq
  simpa only [h₀, h₁] using h.of_isPLHomeomorphOn hf

theorem IsPLAnnulusWithEnds.exists_complex [d : DecidableEq E3] {X J₀ J₁ : Set E3}
    (h : IsPLAnnulusWithEnds X J₀ J₁) :
    ∃ K : Geometry.SimplicialComplex ℝ E3, K.faces.Finite ∧
      IsCombinatorialManifoldWithBoundary 2 K ∧ IsConnected K.space ∧ K.space = X ∧
      (boundaryComplex 2 K).space = J₀ ∪ J₁ := by
  have hd : d = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  subst d
  let _ : DecidableEq E3 := fun a b => Classical.propDecidable (a = b)
  obtain ⟨J, ρ, hJ, hρ, h₀, h₁⟩ := h
  obtain ⟨K, hKfin, hK, hconn, hspace, hboundary⟩ := hρ.exists_annulus_complex hJ zero_lt_one
  have hpair : J ×ˢ ({0, 1} : Set ℝ) = (J ×ˢ {0}) ∪ (J ×ˢ {1}) := by
    ext p
    simp only [mem_prod, mem_insert_iff, mem_singleton_iff, mem_union]
    tauto
  refine ⟨K, hKfin, hK, hconn, hspace, ?_⟩
  rw [hboundary, hpair, image_union, ← h₀, ← h₁]

end DifferentialGeometry.Topology.PiecewiseLinear
