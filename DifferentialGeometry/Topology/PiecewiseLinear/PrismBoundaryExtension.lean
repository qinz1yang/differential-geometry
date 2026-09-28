/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryExtension
import DifferentialGeometry.Topology.PiecewiseLinear.CylinderEndMap
import DifferentialGeometry.Topology.PiecewiseLinear.PrismBoundary

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_isPLHomeomorphOn_prism_eqOn_top_and_side {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {P : Set E} {q : (Fin 3 → ℝ) → E}
    (hq : IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) P)
    {u : E → E} (hu : IsPLHomeomorphOn u P P)
    (hfix : EqOn u id (q '' stdSimplexBoundary 2)) :
    ∃ Φ : E × ℝ → E × ℝ,
      IsPLHomeomorphOn Φ (P ×ˢ Icc (0 : ℝ) 1) (P ×ˢ Icc (0 : ℝ) 1) ∧
      (∀ x ∈ P, Φ (x, 0) = (u x, 0)) ∧
      EqOn Φ id (P ×ˢ ({1} : Set ℝ) ∪ (q '' stdSimplexBoundary 2) ×ˢ Icc (0 : ℝ) 1) := by
  classical
  have hP : IsPLBall 2 P := ⟨q, hq⟩
  obtain ⟨K, hKfin, hKP⟩ := hP.isPolyhedron.exists_simplicialComplex
  let _ : Finite K.faces := hKfin.to_subtype
  let _ : Finite (boundaryComplex 2 K).faces := (boundaryComplex_faces_finite 2 K).to_subtype
  have hK : IsPLBall 2 K.space := hKP.symm ▸ hP
  have hbdK : (boundaryComplex 2 K).space = q '' stdSimplexBoundary 2 := by
    have h := boundaryComplex_space_of_isPLHomeomorphOn_stdSimplex K (hKP.symm ▸ hq)
    rwa [simplexBoundary_stdVertices_space] at h
  have hQ : IsPLBall 3 (P ×ˢ Icc (0 : ℝ) 1) :=
    isPLBall_three_prod hP (isPLBall_Icc zero_lt_one)
  obtain ⟨A, hAfin, hAQ⟩ := hQ.isPolyhedron.exists_simplicialComplex
  let _ : Finite A.faces := hAfin.to_subtype
  have hA : IsPLBall 3 A.space := hAQ.symm ▸ hQ
  have hbdA : (boundaryComplex 3 A).space = P ×ˢ ({0} : Set ℝ) ∪
      (P ×ˢ ({1} : Set ℝ) ∪ (q '' stdSimplexBoundary 2) ×ˢ Icc (0 : ℝ) 1) := by
    rw [boundaryComplex_space_prism K hK zero_lt_one A (hKP.symm ▸ hAQ), hKP, hbdK]
    ext z
    simp only [mem_union, mem_prod, mem_insert_iff, mem_singleton_iff]
    tauto
  let θ : E × ℝ → E × ℝ := fun z => if z.2 = 0 then (u z.1, z.2) else z
  have hbottom : IsPolyhedron (P ×ˢ ({0} : Set ℝ)) := isPolyhedron_prod_singleton
    hP.isPolyhedron 0
  have hrest : IsPolyhedron
      (P ×ˢ ({1} : Set ℝ) ∪ (q '' stdSimplexBoundary 2) ×ˢ Icc (0 : ℝ) 1) :=
    (isPolyhedron_prod_singleton hP.isPolyhedron 1).union
      ((hbdK ▸ isPolyhedron_space (boundaryComplex 2 K)).prod isHPolytope_Icc.isPolyhedron)
  have hθ0 : IsPLHomeomorphOn θ (P ×ˢ ({0} : Set ℝ)) (P ×ˢ ({0} : Set ℝ)) := by
    have hs : IsPolyhedron ({0} : Set ℝ) := by
      rw [← Icc_self (0 : ℝ)]
      exact isHPolytope_Icc.isPolyhedron
    refine (hu.prodMap hs.isPLHomeomorphOn_id).congr ?_
    rintro z ⟨_, hz⟩
    simp only [θ, ite_eq_left (show z.2 = 0 from hz)]
    rfl
  have hθfix : EqOn θ id
      (P ×ˢ ({1} : Set ℝ) ∪ (q '' stdSimplexBoundary 2) ×ˢ Icc (0 : ℝ) 1) := by
    rintro z (hz | hz)
    · have hz1 : z.2 = 1 := hz.2
      simp only [θ, hz1, one_ne_zero, ↓reduceIte, id_eq]
    · by_cases hz0 : z.2 = 0
      · simp only [θ, ite_eq_left hz0, hfix hz.1, id_eq]
      · exact ite_eq_right hz0
  have hθrest := hrest.isPLHomeomorphOn_id.congr hθfix
  have hmeet : θ '' ((P ×ˢ ({0} : Set ℝ)) ∩
      (P ×ˢ ({1} : Set ℝ) ∪ (q '' stdSimplexBoundary 2) ×ˢ Icc (0 : ℝ) 1)) =
      (P ×ˢ ({0} : Set ℝ)) ∩
        (P ×ˢ ({1} : Set ℝ) ∪ (q '' stdSimplexBoundary 2) ×ˢ Icc (0 : ℝ) 1) :=
    (hθfix.mono inter_subset_right).image_eq.trans (image_id _)
  have hθ := hθ0.union hθrest hbottom hrest hmeet
  rw [← hbdA] at hθ
  obtain ⟨Φ, hΦ, hΦθ⟩ := exists_isPLHomeomorphOn_of_boundaryComplex A A hA hA hθ
  refine ⟨Φ, hAQ ▸ hΦ, ?_, ?_⟩
  · intro x hx
    have hm : (x, (0 : ℝ)) ∈ (boundaryComplex 3 A).space := by
      rw [hbdA]
      exact Or.inl ⟨hx, rfl⟩
    rw [hΦθ hm]
    exact ite_eq_left rfl
  · intro z hz
    exact (hΦθ (hbdA.symm ▸ Or.inr hz)).trans (hθfix hz)

end DifferentialGeometry.Topology.PiecewiseLinear
