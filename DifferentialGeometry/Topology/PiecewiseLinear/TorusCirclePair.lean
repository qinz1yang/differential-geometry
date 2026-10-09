/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.EssentialPolygonProductCoordinates
import DifferentialGeometry.Topology.PiecewiseLinear.CircleArcs
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalTowerSeams
import DifferentialGeometry.Topology.PiecewiseLinear.PLAnnulusEnds

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem IsCombinatorialSolidTorus.exists_annulus_pair_of_essential_circles
    {S J₀ J₁ : Set E3} (hS : IsCombinatorialSolidTorus S)
    (h₀ : IsPLSphere 1 J₀) (h₁ : IsPLSphere 1 J₁)
    (h₀S : J₀ ⊆ frontier S) (h₁S : J₁ ⊆ frontier S) (hdis : Disjoint J₀ J₁)
    (hess₀ : ¬ boundsDiskIn J₀ (frontier S)) (hess₁ : ¬ boundsDiskIn J₁ (frontier S)) :
    ∃ A B : Set E3, IsPLAnnulusWithEnds A J₀ J₁ ∧ IsPLAnnulusWithEnds B J₀ J₁ ∧
      A ∪ B = frontier S ∧ A ∩ B = J₀ ∪ J₁ := by
  let G : Fin 2 → Set E3 := ![J₀, J₁]
  have hG : ∀ i, IsPLSphere 1 (G i) := by
    intro i
    fin_cases i
    · exact h₀
    · exact h₁
  have hGS : ∀ i, G i ⊆ frontier S := by
    intro i
    fin_cases i
    · exact h₀S
    · exact h₁S
  have hGdis : Pairwise fun i j => Disjoint (G i) (G j) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact hdis
    · exact hdis.symm
    · exact (hij rfl).elim
  have hGess : ∀ i, ¬ boundsDiskIn (G i) (frontier S) := by
    intro i
    fin_cases i
    · exact hess₀
    · exact hess₁
  obtain ⟨J, Q, f, q, hJ, hQ, hf, hq, hqinj, hlabel⟩ :=
    exists_product_coordinates_for_disjoint_essential_polygons hS G (by norm_num)
      hG hGS hGdis hGess
  have hlabel₀ : J₀ = f '' (J ×ˢ {q 0}) := hlabel 0
  have hlabel₁ : J₁ = f '' (J ×ˢ {q 1}) := hlabel 1
  obtain ⟨A, B, γ, δ, hγ, hδ, hγ₀, hγ₁, hδ₀, hδ₁, hcover, hmeet⟩ :=
    exists_arc_decomposition_of_isPLSphere_one hQ (hq 0) (hq 1)
      (fun heq => (by decide : (0 : Fin 2) ≠ 1) (hqinj heq))
  have hAQ : A ⊆ Q := subset_union_left.trans hcover.subset
  have hBQ : B ⊆ Q := subset_union_right.trans hcover.subset
  have hann (A : Set E3) (γ : ℝ → E3) (hγ : IsPLHomeomorphOn γ (Icc 0 1) A)
      (hγ₀ : γ 0 = q 0) (hγ₁ : γ 1 = q 1) (hAQ : A ⊆ Q) :
      IsPLAnnulusWithEnds (f '' (J ×ˢ A)) J₀ J₁ := by
    have hApoly : IsPolyhedron A :=
      ((isPLBall_Icc (by norm_num : (0 : ℝ) < 1)).of_isPLHomeomorphOn hγ).isPolyhedron
    have hρ : IsPLHomeomorphOn (f ∘ Prod.map id γ) (J ×ˢ Icc 0 1) (f '' (J ×ˢ A)) :=
      (hJ.isPolyhedron.isPLHomeomorphOn_id.prodMap hγ).trans
        (hf.restrict (hJ.isPolyhedron.prod hApoly) (prod_mono Subset.rfl hAQ))
    refine ⟨J, f ∘ Prod.map id γ, hJ, hρ, ?_, ?_⟩
    · rw [image_comp, prodMap_image_prod, image_id, image_singleton, hγ₀, hlabel₀]
    · rw [image_comp, prodMap_image_prod, image_id, image_singleton, hγ₁, hlabel₁]
  refine ⟨f '' (J ×ˢ A), f '' (J ×ˢ B), hann A γ hγ hγ₀ hγ₁ hAQ,
    hann B δ hδ hδ₀ hδ₁ hBQ, ?_, ?_⟩
  · rw [← image_union, ← prod_union, hcover, hf.image_eq]
  · have himage : f '' (J ×ˢ A) ∩ f '' (J ×ˢ B) = f '' (J ×ˢ (A ∩ B)) := by
      ext x
      constructor
      · rintro ⟨⟨p, hp, hpx⟩, ⟨q, hqB, hqx⟩⟩
        have hpq := hf.bijOn.injOn ⟨hp.1, hAQ hp.2⟩ ⟨hqB.1, hBQ hqB.2⟩
          (hpx.trans hqx.symm)
        exact ⟨p, ⟨hp.1, hp.2, hpq ▸ hqB.2⟩, hpx⟩
      · rintro ⟨p, hp, rfl⟩
        exact ⟨⟨p, ⟨hp.1, hp.2.1⟩, rfl⟩, ⟨p, ⟨hp.1, hp.2.2⟩, rfl⟩⟩
    rw [himage, hmeet, ← singleton_union, prod_union, image_union, ← hlabel₀, ← hlabel₁]

end DifferentialGeometry.Topology.PiecewiseLinear
