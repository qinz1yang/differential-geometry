/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryExtension
import DifferentialGeometry.Topology.PiecewiseLinear.CircleFourPoints
import DifferentialGeometry.Topology.PiecewiseLinear.FourSpokeAbstract

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_planar_coordinates_of_isPLBall_two {D : Set E} (hD : IsPLBall 2 D) :
    ∃ (J : Set (EuclideanSpace ℝ (Fin 2))) (σ : E → EuclideanSpace ℝ (Fin 2)),
      IsPLSphere 1 J ∧ IsPLHomeomorphOn σ D (closure (Schoenflies.inside J)) := by
  obtain ⟨T, hT, hcard, -, -, -⟩ := exists_affineIndependent_openSimplex_subset
    (by simp : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 1 + 1)
    (0 : EuclideanSpace ℝ (Fin 2)) (Filter.univ_mem : univ ∈ 𝓝 (0 : EuclideanSpace ℝ (Fin 2)))
  have hC := (isPLBall_convexHull_of_affineIndependent T hT hcard).isPLSphere_frontier
  obtain ⟨u, hu⟩ := hD
  obtain ⟨v, hv⟩ := isPLBall_closure_inside_of_isPLSphere_one hC
  exact ⟨_, _, hC, hu.symm.trans hv⟩

theorem exists_isPLHomeomorphOn_fourSpokeSphere {Λ : Set E} {Λ' : Set F} {t : E → ℝ}
    {t' : F → ℝ} {ℓ : E → ℝ} (hℓ : Continuous ℓ) {uP uN : (Fin 3 → ℝ) → E}
    {u'P u'N : (Fin 3 → ℝ) → F}
    (huP : IsPLHomeomorphOn uP (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (Λ ∩ {x | 0 ≤ t x}))
    (huN : IsPLHomeomorphOn uN (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (Λ ∩ {x | t x ≤ 0}))
    (hbP : uP '' stdSimplexBoundary 2 = Λ ∩ {x | t x = 0})
    (hbN : uN '' stdSimplexBoundary 2 = Λ ∩ {x | t x = 0})
    (hu'P : IsPLHomeomorphOn u'P (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (Λ' ∩ {x | 0 ≤ t' x}))
    (hu'N : IsPLHomeomorphOn u'N (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (Λ' ∩ {x | t' x ≤ 0}))
    (hb'P : u'P '' stdSimplexBoundary 2 = Λ' ∩ {x | t' x = 0})
    (hb'N : u'N '' stdSimplexBoundary 2 = Λ' ∩ {x | t' x = 0})
    {m : Fin 4 → Set E} {β : Fin 4 → ℝ → E} {c : E}
    (hβ : ∀ i, IsPLHomeomorphOn (β i) (Icc 0 1) (m i)) (hβc : ∀ i, β i 0 = c)
    (hm : ∀ i, m i ⊆ Λ ∩ {x | 0 ≤ t x}) (hmC : ∀ i, m i ∩ {x | t x = 0} = {β i 1})
    (hmm : ∀ i j, i ≠ j → m i ∩ m j = {c})
    (hsep : Λ ∩ {x | t x = 0} ∩ {x | ℓ x = 0} = {β 0 1, β 2 1})
    (hpos : 0 < ℓ (β 1 1)) (hneg : ℓ (β 3 1) < 0)
    {m' : Fin 4 → Set F} {β' : Fin 4 → ℝ → F} {c' : F}
    (hβ' : ∀ i, IsPLHomeomorphOn (β' i) (Icc 0 1) (m' i)) (hβ'c : ∀ i, β' i 0 = c')
    (hm' : ∀ i, m' i ⊆ Λ' ∩ {x | 0 ≤ t' x}) (hm'C : ∀ i, m' i ∩ {x | t' x = 0} = {β' i 1})
    (hm'm : ∀ i j, i ≠ j → m' i ∩ m' j = {c'}) :
    ∃ φ : E → F, IsPLHomeomorphOn φ Λ Λ' ∧
      φ '' (Λ ∩ {x | 0 ≤ t x}) = Λ' ∩ {x | 0 ≤ t' x} ∧
      φ '' (Λ ∩ {x | t x = 0}) = Λ' ∩ {x | t' x = 0} ∧
      φ '' (⋃ i, m i) = ⋃ i, m' i ∧ φ c = c' := by
  classical
  have hI : IsPLBall 1 (Icc (0 : ℝ) 1) := isPLBall_Icc zero_lt_one
  have hC : IsPLSphere 1 (Λ ∩ {x | t x = 0}) := hbP ▸ huP.isPLSphere_image_stdSimplexBoundary
  have hC' : IsPLSphere 1 (Λ' ∩ {x | t' x = 0}) :=
    hb'P ▸ hu'P.isPLSphere_image_stdSimplexBoundary
  have hCsub : Λ ∩ {x | t x = 0} ⊆ Λ ∩ {x | 0 ≤ t x} := fun x hx => ⟨hx.1, hx.2.symm.le⟩
  have hC'sub : Λ' ∩ {x | t' x = 0} ⊆ Λ' ∩ {x | 0 ≤ t' x} := fun x hx => ⟨hx.1, hx.2.symm.le⟩
  have hvm : ∀ i, β i 1 ∈ m i ∩ {x | t x = 0} := fun i => (hmC i).symm ▸ mem_singleton _
  have hwm : ∀ i, β' i 1 ∈ m' i ∩ {x | t' x = 0} := fun i => (hm'C i).symm ▸ mem_singleton _
  have hvC : ∀ i, β i 1 ∈ Λ ∩ {x | t x = 0} := fun i => ⟨(hm i (hvm i).1).1, (hvm i).2⟩
  have hwC : ∀ i, β' i 1 ∈ Λ' ∩ {x | t' x = 0} := fun i => ⟨(hm' i (hwm i).1).1, (hwm i).2⟩
  have hcm : ∀ i, c ∈ m i := fun i => hβc i ▸ (hβ i).bijOn.mapsTo ⟨le_rfl, zero_le_one⟩
  have hc'm : ∀ i, c' ∈ m' i := fun i => hβ'c i ▸ (hβ' i).bijOn.mapsTo ⟨le_rfl, zero_le_one⟩
  have hcC : c ∉ Λ ∩ {x | t x = 0} := by
    intro hc
    have h : c ∈ m 0 ∩ {x | t x = 0} := ⟨hcm 0, hc.2⟩
    rw [hmC 0] at h
    exact zero_ne_one ((hβ 0).bijOn.injOn ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩
      ((hβc 0).trans h))
  have hc'C : c' ∉ Λ' ∩ {x | t' x = 0} := by
    intro hc
    have h : c' ∈ m' 0 ∩ {x | t' x = 0} := ⟨hc'm 0, hc.2⟩
    rw [hm'C 0] at h
    exact zero_ne_one ((hβ' 0).bijOn.injOn ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩
      ((hβ'c 0).trans h))
  have hvinj : Function.Injective fun i => β i 1 := by
    intro i j hij
    by_contra hne
    have h : β i 1 ∈ m i ∩ m j := ⟨(hvm i).1, (show β i 1 = β j 1 from hij) ▸ (hvm j).1⟩
    rw [hmm i j hne] at h
    exact hcC ((mem_singleton_iff.mp h) ▸ hvC i)
  have hwinj : Function.Injective fun i => β' i 1 := by
    intro i j hij
    by_contra hne
    have h : β' i 1 ∈ m' i ∩ m' j := ⟨(hwm i).1, (show β' i 1 = β' j 1 from hij) ▸ (hwm j).1⟩
    rw [hm'm i j hne] at h
    exact hc'C ((mem_singleton_iff.mp h) ▸ hwC i)
  obtain ⟨α, δ, hα, hδ, hα0, hα1, hδ0, hδ1⟩ := exists_isPLHomeomorphOn_Icc_inter_of_fiber_pair
    hC hℓ.continuousOn (r := 0) hsep (hvinj.ne (by decide)) ⟨β 1 1, hvC 1, hpos⟩
    ⟨β 3 1, hvC 3, hneg⟩
  have hAB : (Λ ∩ {x | t x = 0} ∩ {x | 0 ≤ ℓ x}) ∩ (Λ ∩ {x | t x = 0} ∩ {x | ℓ x ≤ 0}) =
      {α 0, α 1} := by
    rw [hα0, hα1, ← hsep]
    ext x
    exact ⟨fun h => ⟨h.1.1, le_antisymm h.2.2 h.1.2⟩, fun h => ⟨⟨h.1, h.2.ge⟩, h.1, h.2.le⟩⟩
  have hABu : (Λ ∩ {x | t x = 0} ∩ {x | 0 ≤ ℓ x}) ∪ (Λ ∩ {x | t x = 0} ∩ {x | ℓ x ≤ 0}) =
      Λ ∩ {x | t x = 0} := by
    ext x
    exact ⟨fun h => h.elim (·.1) (·.1), fun h => (le_total 0 (ℓ x)).elim
      (fun h' => Or.inl ⟨h, h'⟩) (fun h' => Or.inr ⟨h, h'⟩)⟩
  have hv1 : β 1 1 ∈ (Λ ∩ {x | t x = 0} ∩ {x | 0 ≤ ℓ x}) \ {α 0, α 1} := by
    refine ⟨⟨hvC 1, hpos.le⟩, ?_⟩
    rw [hα0, hα1]
    rintro (h | h)
    · exact absurd (hvinj h) (by decide)
    · exact absurd (hvinj h) (by decide)
  have hv3 : β 3 1 ∈ (Λ ∩ {x | t x = 0} ∩ {x | ℓ x ≤ 0}) \ {δ 0, δ 1} := by
    refine ⟨⟨hvC 3, hneg.le⟩, ?_⟩
    rw [hδ0, hδ1]
    rintro (h | h)
    · exact absurd (hvinj h) (by decide)
    · exact absurd (hvinj h) (by decide)
  rw [← hα.image_Ioo_eq_sdiff_endpoints zero_lt_one] at hv1
  rw [← hδ.image_Ioo_eq_sdiff_endpoints zero_lt_one] at hv3
  obtain ⟨s, hs, hαs⟩ := hv1
  obtain ⟨r, hr, hδr⟩ := hv3
  obtain ⟨π, γ, hγ, hγ0, hγ1, hγ2, hγ3⟩ := exists_isPLHomeomorphOn_circle_four_points hα hδ
    (hδ0.trans hα0.symm) (hδ1.trans hα1.symm) hAB hs hr hC' (w := fun i => β' i 1) hwC hwinj
  rw [hABu] at hγ
  have hγv : ∀ i, γ (β i 1) = β' (π i) 1 := by
    intro i
    rcases (by decide : ∀ j : Fin 4, j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) i with
      rfl | rfl | rfl | rfl
    · rw [← hα0]
      exact hγ0
    · rw [← hαs]
      exact hγ1
    · rw [← hα1]
      exact hγ2
    · rw [← hδr]
      exact hγ3
  have hDP : IsPLBall 2 (Λ ∩ {x | 0 ≤ t x}) := ⟨uP, huP⟩
  have hDN : IsPLBall 2 (Λ ∩ {x | t x ≤ 0}) := ⟨uN, huN⟩
  have hD'P : IsPLBall 2 (Λ' ∩ {x | 0 ≤ t' x}) := ⟨u'P, hu'P⟩
  obtain ⟨J, σ, hJ, hσ⟩ := exists_planar_coordinates_of_isPLBall_two hDP
  obtain ⟨J', σ', hJ', hσ'⟩ := exists_planar_coordinates_of_isPLBall_two hD'P
  have hσC : σ '' (Λ ∩ {x | t x = 0}) = J := by
    have h := (huP.trans hσ).image_stdSimplexBoundary
    rwa [frontier_closure_inside_of_isPLSphere_one hJ, image_comp, hbP] at h
  have hσ'C : σ' '' (Λ' ∩ {x | t' x = 0}) = J' := by
    have h := (hu'P.trans hσ').image_stdSimplexBoundary
    rwa [frontier_closure_inside_of_isPLSphere_one hJ', image_comp, hb'P] at h
  have huσ : ∀ x ∈ Λ ∩ {x | 0 ≤ t x}, Function.invFunOn σ (Λ ∩ {x | 0 ≤ t x}) (σ x) = x :=
    fun x hx => hσ.bijOn.invOn_invFunOn.1 hx
  have hu'σ' : ∀ x ∈ Λ' ∩ {x | 0 ≤ t' x},
      Function.invFunOn σ' (Λ' ∩ {x | 0 ≤ t' x}) (σ' x) = x :=
    fun x hx => hσ'.bijOn.invOn_invFunOn.1 hx
  have huimg : ∀ S ⊆ Λ ∩ {x | 0 ≤ t x},
      Function.invFunOn σ (Λ ∩ {x | 0 ≤ t x}) '' (σ '' S) = S := by
    intro S hS
    rw [image_image]
    exact (show EqOn (fun x => Function.invFunOn σ (Λ ∩ {x | 0 ≤ t x}) (σ x)) id S from
      fun x hx => huσ x (hS hx)).image_eq.trans (image_id S)
  have hu'img : ∀ S ⊆ Λ' ∩ {x | 0 ≤ t' x},
      Function.invFunOn σ' (Λ' ∩ {x | 0 ≤ t' x}) '' (σ' '' S) = S := by
    intro S hS
    rw [image_image]
    exact (show EqOn (fun x => Function.invFunOn σ' (Λ' ∩ {x | 0 ≤ t' x}) (σ' x)) id S from
      fun x hx => hu'σ' x (hS hx)).image_eq.trans (image_id S)
  have hfr := frontier_closure_inside_of_isPLSphere_one hJ
  have hfr' := frontier_closure_inside_of_isPLSphere_one hJ'
  have hmpoly : ∀ i, IsPolyhedron (m i) := fun i => (hI.of_isPLHomeomorphOn (hβ i)).isPolyhedron
  have hm'poly : ∀ i, IsPolyhedron (m' i) :=
    fun i => (hI.of_isPLHomeomorphOn (hβ' i)).isPolyhedron
  have hσβ : ∀ i, IsPLHomeomorphOn (σ ∘ β i) (Icc 0 1) (σ '' m i) :=
    fun i => (hβ i).trans (hσ.restrict (hmpoly i) (hm i))
  have hσ'β' : ∀ i, IsPLHomeomorphOn (σ' ∘ β' i) (Icc 0 1) (σ' '' m' i) :=
    fun i => (hβ' i).trans (hσ'.restrict (hm'poly i) (hm' i))
  have hmCeq : ∀ i, m i ∩ (Λ ∩ {x | t x = 0}) = {β i 1} := by
    intro i
    rw [← hmC i]
    ext x
    exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, (hm i h.1).1, h.2⟩⟩
  have hm'Ceq : ∀ i, m' i ∩ (Λ' ∩ {x | t' x = 0}) = {β' i 1} := by
    intro i
    rw [← hm'C i]
    ext x
    exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, (hm' i h.1).1, h.2⟩⟩
  have hApoly : IsPolyhedron (Λ ∩ {x | t x = 0} ∩ {x | 0 ≤ ℓ x}) :=
    (hI.of_isPLHomeomorphOn hα).isPolyhedron
  have hBpoly : IsPolyhedron (Λ ∩ {x | t x = 0} ∩ {x | ℓ x ≤ 0}) :=
    (hI.of_isPLHomeomorphOn hδ).isPolyhedron
  have hσα := hα.trans (hσ.restrict hApoly (fun x hx => hCsub hx.1))
  have hσδ := hδ.trans (hσ.restrict hBpoly (fun x hx => hCsub hx.1))
  have hcut : Schoenflies.IsCutPair (frontier (closure (Schoenflies.inside J))) (σ (β 0 1))
      (σ (β 2 1)) (σ '' (Λ ∩ {x | t x = 0} ∩ {x | 0 ≤ ℓ x}))
      (σ '' (Λ ∩ {x | t x = 0} ∩ {x | ℓ x ≤ 0})) := by
    refine ⟨⟨σ ∘ α, hσα.isPiecewiseAffineOn.continuousOn, hσα.bijOn.injOn, hσα.image_eq, ?_, ?_⟩,
      ⟨σ ∘ δ, hσδ.isPiecewiseAffineOn.continuousOn, hσδ.bijOn.injOn, hσδ.image_eq, ?_, ?_⟩, ?_,
      ?_⟩
    · simp only [Function.comp_apply, hα0]
    · simp only [Function.comp_apply, hα1]
    · simp only [Function.comp_apply, hδ0]
    · simp only [Function.comp_apply, hδ1]
    · rw [← image_union, hABu, hσC, hfr]
    · rw [← hσ.bijOn.injOn.image_inter (fun x hx => hCsub hx.1) (fun x hx => hCsub hx.1), hAB,
        image_pair, hα0, hα1]
  obtain ⟨ΦP, hΦP, hΦPγ, hΦPQ, hΦPm⟩ := exists_isPLHomeomorphOn_of_fourSpokeChart
    (T₀ := fun i => σ '' m i) (T₀' := fun i => σ' '' m' i) (v₀ := fun i => σ (β i 1))
    (v₀' := fun i => σ' (β' i 1)) (c₀ := σ c) (c₀' := σ' c')
    (isPLBall_closure_inside_of_isPLSphere_one hJ) (isPLBall_closure_inside_of_isPLSphere_one hJ')
    (fun i => hI.of_isPLHomeomorphOn (hσβ i)) (fun i => hI.of_isPLHomeomorphOn (hσ'β' i))
    (fun i => ⟨σ ∘ β i, (hσβ i).isPiecewiseAffineOn.continuousOn, (hσβ i).bijOn.injOn,
      (hσβ i).image_eq, by simp only [Function.comp_apply, hβc], rfl⟩)
    (fun i => ⟨σ' ∘ β' i, (hσ'β' i).isPiecewiseAffineOn.continuousOn, (hσ'β' i).bijOn.injOn,
      (hσ'β' i).image_eq, by simp only [Function.comp_apply, hβ'c], rfl⟩)
    (fun i => (image_mono (hm i)).trans hσ.image_eq.subset)
    (fun i => (image_mono (hm' i)).trans hσ'.image_eq.subset)
    (fun i => by
      change σ '' m i ∩ _ = {σ (β i 1)}
      rw [hfr, ← hσC, ← hσ.bijOn.injOn.image_inter (hm i) hCsub, hmCeq i, image_singleton])
    (fun i => by
      change σ' '' m' i ∩ _ = {σ' (β' i 1)}
      rw [hfr', ← hσ'C, ← hσ'.bijOn.injOn.image_inter (hm' i) hC'sub, hm'Ceq i,
        image_singleton])
    (fun i j hij => by
      change σ '' m i ∩ σ '' m j = {σ c}
      rw [← hσ.bijOn.injOn.image_inter (hm i) (hm j), hmm i j hij, image_singleton])
    (fun i j hij => by
      change σ' '' m' i ∩ σ' '' m' j = {σ' c'}
      rw [← hσ'.bijOn.injOn.image_inter (hm' i) (hm' j), hm'm i j hij, image_singleton])
    hcut ⟨β 1 1, ⟨hvC 1, hpos.le⟩, rfl⟩ ⟨β 3 1, ⟨hvC 3, hneg.le⟩, rfl⟩ hσ.symm hσ'.symm
    (π := π) (γ := γ)
    (by rw [hfr, hfr', ← hσC, ← hσ'C, huimg _ hCsub, hu'img _ hC'sub]; exact hγ)
    (fun i => by
      rw [huσ _ (hCsub (hvC i)), hu'σ' _ (hC'sub (hwC (π i)))]
      exact hγv i)
    (Q := fun i => β' (π i) ∘ Function.invFunOn (β i) (Icc 0 1))
    (fun i => by
      change IsPLHomeomorphOn _ (Function.invFunOn σ _ '' (σ '' m i))
        (Function.invFunOn σ' _ '' (σ' '' m' (π i)))
      rw [huimg _ (hm i), hu'img _ (hm' (π i))]
      exact (hβ i).symm.trans (hβ' (π i)))
    (fun i => by
      change β' (π i) (Function.invFunOn (β i) (Icc 0 1) (Function.invFunOn σ _ (σ c))) =
        Function.invFunOn σ' _ (σ' c')
      rw [huσ _ (hm 0 (hcm 0)), hu'σ' _ (hm' 0 (hc'm 0)), ← hβc i,
        (hβ i).bijOn.invOn_invFunOn.1 ⟨le_rfl, zero_le_one⟩, hβ'c])
    (fun i => by
      change β' (π i) (Function.invFunOn (β i) (Icc 0 1)
          (Function.invFunOn σ _ (σ (β i 1)))) = γ (Function.invFunOn σ _ (σ (β i 1)))
      rw [huσ _ (hCsub (hvC i)), (hβ i).bijOn.invOn_invFunOn.1 ⟨zero_le_one, le_rfl⟩, hγv i])
  rw [hfr, ← hσC, huimg _ hCsub] at hΦPγ
  have hΦPm' : ∀ i, ΦP '' m i = m' (π i) := by
    intro i
    have h := hΦPm i
    rwa [huimg _ (hm i), hu'img _ (hm' (π i))] at h
  have hΦPc : ΦP c = c' := by
    have h := hΦPQ 0 (show c ∈ Function.invFunOn σ _ '' (σ '' m 0) by
      rw [huimg _ (hm 0)]
      exact hcm 0)
    rw [h]
    change β' (π 0) (Function.invFunOn (β 0) (Icc 0 1) c) = c'
    rw [← hβc 0, (hβ 0).bijOn.invOn_invFunOn.1 ⟨le_rfl, zero_le_one⟩, hβ'c]
  obtain ⟨ΦN, hΦN, hΦNγ⟩ := exists_isPLHomeomorphOn_of_stdSimplexBoundary (n := 1) huN hu'N
    (g := γ) (by rw [hbN, hb'N]; exact hγ)
  rw [hbN] at hΦNγ
  have hinter : (Λ ∩ {x | 0 ≤ t x}) ∩ (Λ ∩ {x | t x ≤ 0}) = Λ ∩ {x | t x = 0} := by
    ext x
    exact ⟨fun h => ⟨h.1.1, le_antisymm h.2.2 h.1.2⟩, fun h => ⟨⟨h.1, h.2.ge⟩, h.1, h.2.le⟩⟩
  have hinter' : (Λ' ∩ {x | 0 ≤ t' x}) ∩ (Λ' ∩ {x | t' x ≤ 0}) = Λ' ∩ {x | t' x = 0} := by
    ext x
    exact ⟨fun h => ⟨h.1.1, le_antisymm h.2.2 h.1.2⟩, fun h => ⟨⟨h.1, h.2.ge⟩, h.1, h.2.le⟩⟩
  have hunion : (Λ ∩ {x | 0 ≤ t x}) ∪ (Λ ∩ {x | t x ≤ 0}) = Λ := by
    ext x
    exact ⟨fun h => h.elim (·.1) (·.1), fun h => (le_total 0 (t x)).elim
      (fun h' => Or.inl ⟨h, h'⟩) (fun h' => Or.inr ⟨h, h'⟩)⟩
  have hunion' : (Λ' ∩ {x | 0 ≤ t' x}) ∪ (Λ' ∩ {x | t' x ≤ 0}) = Λ' := by
    ext x
    exact ⟨fun h => h.elim (·.1) (·.1), fun h => (le_total 0 (t' x)).elim
      (fun h' => Or.inl ⟨h, h'⟩) (fun h' => Or.inr ⟨h, h'⟩)⟩
  obtain ⟨φ, hφ, hφP, hφN⟩ := exists_isPLHomeomorphOn_union hDP.isPolyhedron hDN.isPolyhedron
    hΦP hΦN (by
      rw [hinter]
      exact hΦPγ.trans hΦNγ.symm)
    (by
      rw [hinter, hinter']
      intro y hy
      obtain ⟨x, hx, rfl⟩ := hγ.bijOn.surjOn hy
      exact ⟨x, hx, hΦPγ hx⟩)
  rw [hunion, hunion'] at hφ
  refine ⟨φ, hφ, hφP.image_eq.trans hΦP.image_eq, ?_, ?_, ?_⟩
  · rw [(hφP.mono hCsub).image_eq, hΦPγ.image_eq, hγ.image_eq]
  · rw [image_iUnion]
    calc ⋃ i, φ '' m i = ⋃ i, m' (π i) :=
          iUnion_congr fun i => ((hφP.mono (hm i)).image_eq).trans (hΦPm' i)
      _ = ⋃ i, m' i := Equiv.iSup_comp π
  · rw [hφP (hm 0 (hcm 0)), hΦPc]

end DifferentialGeometry.Topology.PiecewiseLinear
