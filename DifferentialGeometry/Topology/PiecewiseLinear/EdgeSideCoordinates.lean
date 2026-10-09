/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.GluedEdgeSides

open Set Topology Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]

theorem exists_eq_add_smul_of_mem_openSimplex_pair {a b x : E} (hab : a ≠ b)
    (hx : x ∈ openSimplex ({a, b} : Finset E)) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ x = a + θ • (b - a) := by
  obtain ⟨w, hw₀, hw₁, hwx⟩ := hx
  rw [Finset.sum_pair hab] at hw₁ hwx
  have ha := hw₀ a (Finset.mem_insert_self a {b})
  have hb := hw₀ b (Finset.mem_insert_of_mem (Finset.mem_singleton_self b))
  refine ⟨w b, hb, by linarith, ?_⟩
  rw [← hwx, show w a = 1 - w b by linarith]
  module

theorem pair_independent_of_affineIndependent_insert {a b c x : E}
    (hind : AffineIndependent ℝ ((↑) : ↥(insert c ({a, b} : Finset E)) → E)) (hab : a ≠ b)
    (hc : c ∉ ({a, b} : Finset E)) {θ : ℝ} (hx : x = a + θ • (b - a)) :
    ∀ α β : ℝ, α • (b - a) + β • (c - x) = 0 → α = 0 ∧ β = 0 := by
  intro α β h
  have hca : c ≠ a := fun hh => hc (by rw [hh]; exact Finset.mem_insert_self a {b})
  have hcb : c ≠ b := fun hh => hc (by
    rw [hh]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self b))
  have hba : b ≠ a := hab.symm
  let w : E → ℝ := fun u => if u = a then 1 else 0
  let w' : E → ℝ := fun u => if u = a then 1 - (α - β * θ) - β else if u = b then α - β * θ
    else β
  have wc : w c = 0 := ite_eq_right hca
  have wa : w a = 1 := ite_eq_left rfl
  have wb : w b = 0 := ite_eq_right hba
  have w'c : w' c = β := by
    change (if c = a then 1 - (α - β * θ) - β else if c = b then α - β * θ else β) = β
    rw [ite_eq_right hca, ite_eq_right hcb]
  have w'a : w' a = 1 - (α - β * θ) - β := ite_eq_left rfl
  have w'b : w' b = α - β * θ := by
    change (if b = a then 1 - (α - β * θ) - β else if b = b then α - β * θ else β) = α - β * θ
    rw [ite_eq_right hba, ite_eq_left rfl]
  have hw : ∑ u ∈ insert c ({a, b} : Finset E), w u = 1 := by
    rw [Finset.sum_insert hc, Finset.sum_pair hab, wc, wa, wb]
    ring
  have hw' : ∑ u ∈ insert c ({a, b} : Finset E), w' u = 1 := by
    rw [Finset.sum_insert hc, Finset.sum_pair hab, w'c, w'a, w'b]
    ring
  have hcomb : ∑ u ∈ insert c ({a, b} : Finset E), w u • u =
      ∑ u ∈ insert c ({a, b} : Finset E), w' u • u := by
    rw [Finset.sum_insert hc, Finset.sum_pair hab, Finset.sum_insert hc, Finset.sum_pair hab,
      wc, wa, wb, w'c, w'a, w'b]
    have key : β • c + ((1 - (α - β * θ) - β) • a + (α - β * θ) • b) =
        a + (α • (b - a) + β • (c - x)) := by
      rw [hx]
      module
    rw [key, h]
    module
  have hww := eq_on_of_sum_smul_eq hind hw hw' hcomb
  have hc' := hww c (Finset.mem_insert_self c _)
  have hb' := hww b (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
    (Finset.mem_singleton_self b)))
  rw [wc, w'c] at hc'
  rw [wb, w'b, ← hc'] at hb'
  refine ⟨?_, hc'.symm⟩
  linarith

end General

section Plane

theorem exists_eq_insert_of_ssubset_of_card_eq_two
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    {σ u : Finset (EuclideanSpace ℝ (Fin 2))} (hσ2 : σ.card = 2) (hu : u ∈ K.faces)
    (hσu : σ ⊆ u) (hne : u ≠ σ) : ∃ c, c ∉ σ ∧ u = insert c σ := by
  have h3 : u.card ≤ 3 := by
    have h := (K.indep hu).card_le_finrank_succ
    have h2' := Submodule.finrank_le
      (vectorSpan ℝ (Set.range ((↑) : u → EuclideanSpace ℝ (Fin 2))))
    rw [Fintype.card_coe] at h
    rw [finrank_euclideanSpace_fin] at h2'
    omega
  have hlt : σ.card < u.card :=
    Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hσu, fun h => hne h.symm⟩)
  obtain ⟨c, hc, hins⟩ := Finset.exists_eq_insert_iff.mpr ⟨hσu, by omega⟩
  exact ⟨c, hc, hins.symm⟩

theorem exists_edgeSideCoordinates (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    {a b c x : EuclideanSpace ℝ (Fin 2)} (hab : a ≠ b)
    (hx : x ∈ openSimplex ({a, b} : Finset (EuclideanSpace ℝ (Fin 2))))
    (hc : c ∉ ({a, b} : Finset (EuclideanSpace ℝ (Fin 2))))
    (hτ : insert c ({a, b} : Finset (EuclideanSpace ℝ (Fin 2))) ∈ K.faces) :
    ∃ (G : EuclideanSpace ℝ (Fin 2) ≃ₗ[ℝ] ℝ × ℝ) (θ : ℝ), 0 < θ ∧ θ < 1 ∧
      x = a + θ • (b - a) ∧ (∀ α β : ℝ, G (α • (b - a) + β • (c - x)) = (α, β)) ∧
      (∀ ζ, ζ = (G ζ).1 • (b - a) + (G ζ).2 • (c - x)) ∧
      (∀ ζ, (G ζ).2 = 0 → ζ ∈ vectorSpan ℝ
        ((({a, b} : Finset (EuclideanSpace ℝ (Fin 2))) : Set (EuclideanSpace ℝ (Fin 2))))) ∧
      (G (a - x)).2 = 0 ∧ (G (b - x)).2 = 0 ∧ (G (c - x)).2 = 1 := by
  obtain ⟨θ, hθ0, hθ1, hxθ⟩ := exists_eq_add_smul_of_mem_openSimplex_pair hab hx
  have hen := pair_independent_of_affineIndependent_insert (K.indep hτ) hab hc hxθ
  obtain ⟨G, hG⟩ := exists_linearEquiv_prod_of_independent_pair finrank_euclideanSpace_fin hen
  have hdec : ∀ ζ, ζ = (G ζ).1 • (b - a) + (G ζ).2 • (c - x) := by
    intro ζ
    apply G.injective
    rw [hG]
  refine ⟨G, θ, hθ0, hθ1, hxθ, hG, hdec, ?_, ?_, ?_, ?_⟩
  · intro ζ hζ
    rw [hdec ζ, hζ, zero_smul, add_zero, Finset.coe_pair, vectorSpan_pair]
    refine Submodule.smul_mem _ _ ?_
    have hmem : (a -ᵥ b) ∈ Submodule.span ℝ {a -ᵥ b} := Submodule.mem_span_singleton_self _
    have hneg := Submodule.neg_mem _ hmem
    rwa [vsub_eq_sub, neg_sub] at hneg
  · have h : a - x = (-θ) • (b - a) + (0 : ℝ) • (c - x) := by
      rw [hxθ]
      module
    rw [h, hG]
  · have h : b - x = (1 - θ) • (b - a) + (0 : ℝ) • (c - x) := by
      rw [hxθ]
      module
    rw [h, hG]
  · have h : c - x = (0 : ℝ) • (b - a) + (1 : ℝ) • (c - x) := by module
    rw [h, hG]

end Plane

end DifferentialGeometry.Topology.PiecewiseLinear
