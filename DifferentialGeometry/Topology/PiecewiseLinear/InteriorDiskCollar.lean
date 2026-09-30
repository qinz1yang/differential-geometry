/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SpanningDiskPrism
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.DiskPushOff

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsPLHomeomorphOn.exists_collar_of_centered_prism {D N : Set E}
    {r : (Fin 3 → ℝ) → E} {f : (Fin 3 → ℝ) × ℝ → E}
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D)
    (hf : IsPLHomeomorphOn f (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1) N)
    (hzero : ∀ x ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3), f (x, 0) = r x) :
    ∃ (C : Set E) (ρ : E × ℝ → E),
      IsPLHomeomorphOn ρ (D ×ˢ Icc (0 : ℝ) 1) C ∧ C ⊆ N ∧ D ⊆ C ∧
        (∀ x ∈ D, ρ (x, 0) = x) ∧ MapsTo ρ (D ×ˢ Ioc (0 : ℝ) 1) (C \ D) := by
  have hsub : Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1 ⊆
      Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1 :=
    prod_mono Subset.rfl (Icc_subset_Icc (by norm_num) le_rfl)
  have hpoly : IsPolyhedron (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1) :=
    (isPLBall_stdSimplex 2).isPolyhedron.prod
      (isHPolytope_Icc (a := (0 : ℝ)) (b := 1)).isPolyhedron
  have hfC : IsPLHomeomorphOn f (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1)
      (f '' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1)) := hf.restrict hpoly hsub
  have hρ : IsPLHomeomorphOn
      (f ∘ Prod.map (Function.invFunOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3))) (id : ℝ → ℝ))
      (D ×ˢ Icc (0 : ℝ) 1) (f '' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1)) :=
    (hr.symm.prodMap
      (isHPolytope_Icc (a := (0 : ℝ)) (b := 1)).isPolyhedron.isPLHomeomorphOn_id).trans hfC
  have hbase : ∀ x ∈ D,
      (f ∘ Prod.map (Function.invFunOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3))) (id : ℝ → ℝ)) (x, 0) = x := by
    intro x hx
    change f (Function.invFunOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) x, (0 : ℝ)) = x
    rw [hzero _ (hr.symm.bijOn.mapsTo hx)]
    exact hr.bijOn.invOn_invFunOn.2 hx
  have hDC : D ⊆ f '' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1) := by
    intro x hx
    rw [← hbase x hx]
    exact hρ.bijOn.mapsTo ⟨hx, le_rfl, zero_le_one⟩
  refine ⟨_, _, hρ, (image_mono hsub).trans hf.image_eq.subset, hDC, hbase, ?_⟩
  rintro z ⟨hzD, hzpos, hzle⟩
  have hzdom : z ∈ D ×ˢ Icc (0 : ℝ) 1 := ⟨hzD, hzpos.le, hzle⟩
  refine ⟨hρ.bijOn.mapsTo hzdom, ?_⟩
  intro hmem
  have heq := hρ.bijOn.injOn hzdom ⟨hmem, le_rfl, zero_le_one⟩ (hbase _ hmem).symm
  exact (ne_of_gt hzpos) (congrArg Prod.snd heq)

theorem IsPLHomeomorphOn.centered_prism_neg {N : Set E} {r : (Fin 3 → ℝ) → E}
    {f : (Fin 3 → ℝ) × ℝ → E}
    (hf : IsPLHomeomorphOn f (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1) N)
    (hzero : ∀ x ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3), f (x, 0) = r x) :
    IsPLHomeomorphOn (f ∘ Prod.map (id : (Fin 3 → ℝ) → (Fin 3 → ℝ)) (fun t : ℝ => -t))
        (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1) N ∧
      ∀ x ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3),
        (f ∘ Prod.map (id : (Fin 3 → ℝ) → (Fin 3 → ℝ)) (fun t : ℝ => -t)) (x, 0) = r x := by
  refine ⟨?_, ?_⟩
  · have hreflect : IsPLHomeomorphOn (fun t : ℝ => -t) (Icc (-1 : ℝ) 1) (Icc (-1 : ℝ) 1) := by
      apply isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn isHPolytope_Icc.isPolyhedron
        (isPiecewiseAffineOn_of_affine_of_isHPolytope
          (-LinearMap.id : ℝ →ₗ[ℝ] ℝ).toAffineMap isHPolytope_Icc)
      refine ⟨?_, fun _ _ _ _ h => neg_injective h, ?_⟩
      · intro t ht
        change -1 ≤ -t ∧ -t ≤ 1
        exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
      · intro t ht
        exact ⟨-t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, neg_neg t⟩
    exact ((isPLBall_stdSimplex 2).isPolyhedron.isPLHomeomorphOn_id.prodMap hreflect).trans hf
  · intro x hx
    change f (x, -(0 : ℝ)) = r x
    rw [neg_zero]
    exact hzero x hx

theorem IsPLBall.exists_collar_of_properly_embedded_disk
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsPLBall 3 K.space)
    (hdim : Module.finrank ℝ E = 3) {D : Set E} {r : (Fin 3 → ℝ) → E}
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D) (hDK : D ⊆ K.space)
    (hproper : D ∩ frontier K.space = r '' stdSimplexBoundary 2) :
    ∃ (C : Set E) (ρ : E × ℝ → E),
      IsPLHomeomorphOn ρ (D ×ˢ Icc (0 : ℝ) 1) C ∧ C ⊆ K.space ∧ D ⊆ C ∧
        (∀ x ∈ D, ρ (x, 0) = x) ∧ MapsTo ρ (D ×ˢ Ioc (0 : ℝ) 1) (C \ D) := by
  obtain ⟨N, f, hf, hNK, hzero, -, -⟩ :=
    hK.exists_centered_prism_subset_of_boundary_neighborhood K hdim hr hDK hproper
      (S := frontier K.space) inter_subset_left
      (mem_nhdsSetWithin.mpr ⟨univ, isOpen_univ, subset_univ _, inter_subset_right⟩)
  obtain ⟨C, ρ, hρ, hCN, hDC, hbase, hmaps⟩ := hr.exists_collar_of_centered_prism hf hzero
  exact ⟨C, ρ, hρ, hCN.trans hNK, hDC, hbase, hmaps⟩

theorem IsPLBall.exists_pushOff_of_properly_embedded_disk
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsPLBall 3 K.space)
    (hdim : Module.finrank ℝ E = 3) {D : Set E} {r : (Fin 3 → ℝ) → E}
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D) (hDK : D ⊆ K.space)
    (hproper : D ∩ frontier K.space = r '' stdSimplexBoundary 2) :
    ∃ (D' : Set E) (q : (Fin 3 → ℝ) → E),
      IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D' ∧ D' ⊆ K.space ∧
        q '' stdSimplexBoundary 2 = r '' stdSimplexBoundary 2 ∧
          D' ∩ D = r '' stdSimplexBoundary 2 := by
  obtain ⟨C, ρ, hρ, hCK, -, hbase, -⟩ :=
    hK.exists_collar_of_properly_embedded_disk K hdim hr hDK hproper
  obtain ⟨D', q, hq, hD'C, hqb, hmeet⟩ :=
    hr.exists_isPLHomeomorphOn_pushOff_of_collar (by norm_num : (0 : ℝ) < 1) hρ hbase
  exact ⟨D', q, hq, hD'C.trans hCK, hqb, hmeet⟩

theorem IsCombinatorialManifold.exists_collar_of_spanning_disk
    (S : Geometry.SimplicialComplex ℝ E) [Finite S.faces]
    (hS : IsCombinatorialManifold 2 S) (hSc : IsConnected S.space)
    (hdim : Module.finrank ℝ E = 3) {D U : Set E} {r : (Fin 3 → ℝ) → E}
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D)
    (hmeet : D ∩ S.space = r '' stdSimplexBoundary 2) (hU : IsOpen U) (hDU : D ⊆ U) :
    ∃ (C : Set E) (ρ : E × ℝ → E),
      IsPLHomeomorphOn ρ (D ×ˢ Icc (0 : ℝ) 1) C ∧ C ⊆ U ∧ D ⊆ C ∧
        (∀ x ∈ D, ρ (x, 0) = x) ∧ MapsTo ρ (D ×ˢ Ioc (0 : ℝ) 1) (C \ D) := by
  obtain ⟨N, f, hf, hNU, hzero, -, -⟩ :=
    hS.exists_centered_prism_neighborhood_of_spanning_disk S hSc hdim hr hmeet hU hDU
  obtain ⟨C, ρ, hρ, hCN, hDC, hbase, hmaps⟩ := hr.exists_collar_of_centered_prism hf hzero
  exact ⟨C, ρ, hρ, hCN.trans hNU, hDC, hbase, hmaps⟩

theorem IsCombinatorialManifold.exists_pushOff_of_spanning_disk
    (S : Geometry.SimplicialComplex ℝ E) [Finite S.faces]
    (hS : IsCombinatorialManifold 2 S) (hSc : IsConnected S.space)
    (hdim : Module.finrank ℝ E = 3) {D U : Set E} {r : (Fin 3 → ℝ) → E}
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D)
    (hmeet : D ∩ S.space = r '' stdSimplexBoundary 2) (hU : IsOpen U) (hDU : D ⊆ U) :
    ∃ (D' : Set E) (q : (Fin 3 → ℝ) → E),
      IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D' ∧ D' ⊆ U ∧
        q '' stdSimplexBoundary 2 = r '' stdSimplexBoundary 2 ∧
          D' ∩ D = r '' stdSimplexBoundary 2 := by
  obtain ⟨C, ρ, hρ, hCU, -, hbase, -⟩ :=
    hS.exists_collar_of_spanning_disk S hSc hdim hr hmeet hU hDU
  obtain ⟨D', q, hq, hD'C, hqb, hmeetD⟩ :=
    hr.exists_isPLHomeomorphOn_pushOff_of_collar (by norm_num : (0 : ℝ) < 1) hρ hbase
  exact ⟨D', q, hq, hD'C.trans hCU, hqb, hmeetD⟩

end DifferentialGeometry.Topology.PiecewiseLinear
