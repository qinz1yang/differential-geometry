import DifferentialGeometry.Topology.SphereSeparation.Defs
import DifferentialGeometry.Topology.SphereSeparation.SourceTheorems
import DifferentialGeometry.Topology.Embedding.Sphere

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.SphereSeparation

structure TwoSidedSeparation {X : Type*} [TopologicalSpace X] (S : Set X) where
  positiveSide : Set X
  negativeSide : Set X
  isOpen_positiveSide : IsOpen positiveSide
  isOpen_negativeSide : IsOpen negativeSide
  nonempty_positiveSide : positiveSide.Nonempty
  nonempty_negativeSide : negativeSide.Nonempty
  disjoint : Disjoint positiveSide negativeSide
  union_eq_compl : positiveSide ∪ negativeSide = Sᶜ
  frontier_positiveSide : frontier positiveSide = S
  frontier_negativeSide : frontier negativeSide = S

namespace TwoSidedSeparation

def ofClosedCover {X : Type*} [TopologicalSpace X] {S A B : Set X}
    (hA : closure (interior A) = A) (hB : closure (interior B) = B)
    (hAne : A.Nonempty) (hBne : B.Nonempty)
    (hcover : A ∪ B = univ) (hinter : A ∩ B = S)
    (hfrontA : frontier A = S) (hfrontB : frontier B = S) : TwoSidedSeparation S := by
  have hAc : IsClosed A := hA ▸ isClosed_closure
  have hBc : IsClosed B := hB ▸ isClosed_closure
  have hAS : interior A ⊆ Sᶜ := by
    rw [← hfrontA]
    exact disjoint_left.mp disjoint_interior_frontier
  have hBS : interior B ⊆ Sᶜ := by
    rw [← hfrontB]
    exact disjoint_left.mp disjoint_interior_frontier
  refine ⟨interior A, interior B, isOpen_interior, isOpen_interior, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · by_contra hn
    have he : interior A = ∅ := not_nonempty_iff_eq_empty.mp hn
    rw [he, closure_empty] at hA
    exact hAne.ne_empty hA.symm
  · by_contra hn
    have he : interior B = ∅ := not_nonempty_iff_eq_empty.mp hn
    rw [he, closure_empty] at hB
    exact hBne.ne_empty hB.symm
  · rw [disjoint_left]
    intro x hxA hxB
    exact hAS hxA (hinter.subset ⟨interior_subset hxA, interior_subset hxB⟩)
  · ext x
    constructor
    · rintro (h | h)
      · exact hAS h
      · exact hBS h
    · intro hx
      have hmem : x ∈ A ∪ B := hcover.symm.subset (mem_univ x)
      rcases hmem with h | h
      · left
        rw [← self_sdiff_frontier A, hfrontA]
        exact ⟨h, hx⟩
      · right
        rw [← self_sdiff_frontier B, hfrontB]
        exact ⟨h, hx⟩
  · rw [frontier, hA, interior_interior, ← hfrontA, frontier]
    rw [hAc.closure_eq]
  · rw [frontier, hB, interior_interior, ← hfrontB, frontier]
    rw [hBc.closure_eq]

variable {X : Type*} [TopologicalSpace X] {S C U V O : Set X}

theorem positiveSide_subset_compl (d : TwoSidedSeparation S) : d.positiveSide ⊆ Sᶜ := by
  rw [← d.union_eq_compl]
  exact subset_union_left

theorem negativeSide_subset_compl (d : TwoSidedSeparation S) : d.negativeSide ⊆ Sᶜ := by
  rw [← d.union_eq_compl]
  exact subset_union_right

theorem positiveSide_disjoint_sphere (d : TwoSidedSeparation S) :
    Disjoint d.positiveSide S := by
  rw [Set.disjoint_left]
  intro x hxB hxS
  exact d.positiveSide_subset_compl hxB hxS

theorem negativeSide_disjoint_sphere (d : TwoSidedSeparation S) :
    Disjoint d.negativeSide S := by
  rw [Set.disjoint_left]
  intro x hxE hxS
  exact d.negativeSide_subset_compl hxE hxS

theorem subset_positiveSide_or_subset_negativeSide (d : TwoSidedSeparation S)
    (hC : IsPreconnected C) (hCS : C ⊆ Sᶜ) :
    C ⊆ d.positiveSide ∨ C ⊆ d.negativeSide := by
  apply hC.subset_or_subset d.isOpen_positiveSide d.isOpen_negativeSide d.disjoint
  simpa only [d.union_eq_compl] using hCS

theorem not_isPreconnected_compl (d : TwoSidedSeparation S) : ¬ IsPreconnected Sᶜ := by
  intro hpre
  rcases d.subset_positiveSide_or_subset_negativeSide hpre subset_rfl with h | h
  · have hsub : d.negativeSide ⊆ ∅ := fun x hx =>
      Set.disjoint_left.mp d.disjoint (h (d.negativeSide_subset_compl hx)) hx
    obtain ⟨x, hx⟩ := d.nonempty_negativeSide
    rw [Set.subset_empty_iff.mp hsub] at hx
    exact hx
  · have hsub : d.positiveSide ⊆ ∅ := fun x hx =>
      Set.disjoint_left.mp d.disjoint hx (h (d.positiveSide_subset_compl hx))
    obtain ⟨x, hx⟩ := d.nonempty_positiveSide
    rw [Set.subset_empty_iff.mp hsub] at hx
    exact hx

theorem not_mem_connectedComponentIn_of_mem_other_side (d : TwoSidedSeparation S)
    {p z : X} (hp : p ∈ d.negativeSide) (hz : z ∈ d.positiveSide) :
    z ∉ connectedComponentIn Sᶜ p := by
  intro hzcomp
  have hpcompl : p ∈ Sᶜ := d.negativeSide_subset_compl hp
  have hsub : connectedComponentIn Sᶜ p ⊆ Sᶜ := connectedComponentIn_subset Sᶜ p
  rcases d.subset_positiveSide_or_subset_negativeSide isPreconnected_connectedComponentIn hsub with
    h | h
  · exact Set.disjoint_left.mp d.disjoint (h (mem_connectedComponentIn hpcompl)) hp
  · exact Set.disjoint_left.mp d.disjoint hz (h hzcomp)

theorem not_mem_connectedComponentIn_of_mem_other_side_symm (d : TwoSidedSeparation S)
    {p z : X} (hp : p ∈ d.positiveSide) (hz : z ∈ d.negativeSide) :
    z ∉ connectedComponentIn Sᶜ p := by
  intro hzcomp
  have hpcompl : p ∈ Sᶜ := d.positiveSide_subset_compl hp
  have hsub : connectedComponentIn Sᶜ p ⊆ Sᶜ := connectedComponentIn_subset Sᶜ p
  rcases d.subset_positiveSide_or_subset_negativeSide isPreconnected_connectedComponentIn hsub with
    h | h
  · exact Set.disjoint_left.mp d.disjoint (h hzcomp) hz
  · exact Set.disjoint_left.mp d.disjoint hp (h (mem_connectedComponentIn hpcompl))

theorem neighborhood_halves_opposite_of_inter_nonempty (d : TwoSidedSeparation S)
    (hU : IsConnected U) (hV : IsConnected V)
    (hUS : U ⊆ Sᶜ) (hVS : V ⊆ Sᶜ)
    (hOopen : IsOpen O) (hSO : (S ∩ O).Nonempty) (hO : O ⊆ (U ∪ S) ∪ V) :
    Xor (U ⊆ d.positiveSide ∧ V ⊆ d.negativeSide)
      (U ⊆ d.negativeSide ∧ V ⊆ d.positiveSide) := by
  have not_both_positive : ¬ (U ⊆ d.positiveSide ∧ V ⊆ d.positiveSide) := by
    rintro ⟨hUB, hVB⟩
    obtain ⟨s, hsS, hsO⟩ := hSO
    have hsClosure : s ∈ closure d.negativeSide := by
      apply frontier_subset_closure
      simpa only [d.frontier_negativeSide] using hsS
    obtain ⟨x, hxO, hxE⟩ := mem_closure_iff.1 hsClosure O hOopen hsO
    rcases hO hxO with (hxU | hxS) | hxV
    · exact Set.disjoint_left.1 d.disjoint (hUB hxU) hxE
    · exact Set.disjoint_left.1 d.negativeSide_disjoint_sphere hxE hxS
    · exact Set.disjoint_left.1 d.disjoint (hVB hxV) hxE
  have not_both_negative : ¬ (U ⊆ d.negativeSide ∧ V ⊆ d.negativeSide) := by
    rintro ⟨hUE, hVE⟩
    obtain ⟨s, hsS, hsO⟩ := hSO
    have hsClosure : s ∈ closure d.positiveSide := by
      apply frontier_subset_closure
      simpa only [d.frontier_positiveSide] using hsS
    obtain ⟨x, hxO, hxB⟩ := mem_closure_iff.1 hsClosure O hOopen hsO
    rcases hO hxO with (hxU | hxS) | hxV
    · exact Set.disjoint_left.1 d.disjoint hxB (hUE hxU)
    · exact Set.disjoint_left.1 d.positiveSide_disjoint_sphere hxB hxS
    · exact Set.disjoint_left.1 d.disjoint hxB (hVE hxV)
  rcases d.subset_positiveSide_or_subset_negativeSide hU.isPreconnected hUS with hUB | hUE
  · rcases d.subset_positiveSide_or_subset_negativeSide hV.isPreconnected hVS with hVB | hVE
    · exact False.elim (not_both_positive ⟨hUB, hVB⟩)
    · refine Or.inl ⟨⟨hUB, hVE⟩, ?_⟩
      rintro ⟨hUE', _⟩
      obtain ⟨x, hxU⟩ := hU.nonempty
      exact Set.disjoint_left.1 d.disjoint (hUB hxU) (hUE' hxU)
  · rcases d.subset_positiveSide_or_subset_negativeSide hV.isPreconnected hVS with hVB | hVE
    · refine Or.inr ⟨⟨hUE, hVB⟩, ?_⟩
      rintro ⟨hUB', _⟩
      obtain ⟨x, hxU⟩ := hU.nonempty
      exact Set.disjoint_left.1 d.disjoint (hUB' hxU) (hUE hxU)
    · exact False.elim (not_both_negative ⟨hUE, hVE⟩)

theorem neighborhood_halves_opposite (d : TwoSidedSeparation S)
    (hS : S.Nonempty) (hU : IsConnected U) (hV : IsConnected V)
    (hUS : U ⊆ Sᶜ) (hVS : V ⊆ Sᶜ)
    (hOopen : IsOpen O) (hSO : S ⊆ O) (hO : O ⊆ (U ∪ S) ∪ V) :
    Xor (U ⊆ d.positiveSide ∧ V ⊆ d.negativeSide)
      (U ⊆ d.negativeSide ∧ V ⊆ d.positiveSide) := by
  exact d.neighborhood_halves_opposite_of_inter_nonempty hU hV hUS hVS hOopen
    (hS.mono (fun _ hx => ⟨hx, hSO hx⟩)) hO

theorem positiveSide_eq_connectedComponentIn (d : TwoSidedSeparation S)
    {x : X} (hU : U ⊆ Sᶜ) (hp : IsPreconnected d.positiveSide)
    (hsub : d.positiveSide ⊆ U) (hx : x ∈ d.positiveSide) :
    d.positiveSide = connectedComponentIn U x := by
  apply Subset.antisymm (hp.subset_connectedComponentIn hx hsub)
  rcases d.subset_positiveSide_or_subset_negativeSide isPreconnected_connectedComponentIn
    ((connectedComponentIn_subset U x).trans hU) with h | h
  · exact h
  · exact False.elim (disjoint_left.mp d.disjoint hx (h (mem_connectedComponentIn (hsub hx))))

theorem negativeSide_eq_connectedComponentIn (d : TwoSidedSeparation S)
    {x : X} (hU : U ⊆ Sᶜ) (hp : IsPreconnected d.negativeSide)
    (hsub : d.negativeSide ⊆ U) (hx : x ∈ d.negativeSide) :
    d.negativeSide = connectedComponentIn U x := by
  apply Subset.antisymm (hp.subset_connectedComponentIn hx hsub)
  rcases d.subset_positiveSide_or_subset_negativeSide isPreconnected_connectedComponentIn
    ((connectedComponentIn_subset U x).trans hU) with h | h
  · exact False.elim (disjoint_left.mp d.disjoint (h (mem_connectedComponentIn (hsub hx))) hx)
  · exact h

end TwoSidedSeparation

namespace SphereSides

variable {X : Type*} [TopologicalSpace X] {S : Set X}

def toTwoSidedSeparation (d : SphereSides S) : TwoSidedSeparation S where
  positiveSide := d.compactSide
  negativeSide := d.endSide
  isOpen_positiveSide := d.isOpen_compactSide
  isOpen_negativeSide := d.isOpen_endSide
  nonempty_positiveSide := d.compactSide_nonempty
  nonempty_negativeSide := d.endSide_nonempty
  disjoint := d.disjoint
  union_eq_compl := d.union_eq_compl
  frontier_positiveSide := d.frontier_compactSide
  frontier_negativeSide := d.frontier_endSide

end SphereSides

private theorem frontier_prod_Ioi (a : ℝ) :
    frontier (Set.univ ×ˢ Set.Ioi a : Set (SphereTwo × ℝ)) = Set.univ ×ˢ {a} := by
  rw [frontier_eq_closure_inter_closure, closure_prod_eq, closure_Ioi, closure_univ]
  have hc : (Set.univ ×ˢ Set.Ioi a : Set (SphereTwo × ℝ))ᶜ = Set.univ ×ˢ Set.Iic a := by
    ext p
    simp only [Set.mem_compl_iff, Set.mem_prod, Set.mem_univ, true_and, Set.mem_Ioi,
      Set.mem_Iic, not_lt]
  rw [hc, closure_prod_eq, closure_Iic, closure_univ, Set.prod_inter_prod, Set.univ_inter]
  congr 1
  ext x
  exact ⟨fun h => (le_antisymm h.1 h.2).symm, fun h => ⟨h.ge, h.le⟩⟩

private theorem frontier_prod_Iio (a : ℝ) :
    frontier (Set.univ ×ˢ Set.Iio a : Set (SphereTwo × ℝ)) = Set.univ ×ˢ {a} := by
  rw [frontier_eq_closure_inter_closure, closure_prod_eq, closure_Iio, closure_univ]
  have hc : (Set.univ ×ˢ Set.Iio a : Set (SphereTwo × ℝ))ᶜ = Set.univ ×ˢ Set.Ici a := by
    ext p
    simp only [Set.mem_compl_iff, Set.mem_prod, Set.mem_univ, true_and, Set.mem_Iio,
      Set.mem_Ici, not_lt]
  rw [hc, closure_prod_eq, closure_Ici, closure_univ, Set.prod_inter_prod, Set.univ_inter]
  congr 1
  ext x
  exact ⟨fun h => (le_antisymm h.2 h.1).symm, fun h => ⟨h.le, h.ge⟩⟩

private theorem range_prod_zero :
    Set.range (fun x : SphereTwo => (x, (0 : ℝ))) =
      (Set.univ ×ˢ ({0} : Set ℝ) : Set (SphereTwo × ℝ)) := by
  ext p
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨trivial, rfl⟩
  · rintro ⟨-, h⟩
    exact ⟨p.1, Prod.ext rfl (by simpa using h.symm)⟩

theorem nonempty_twoSidedSeparation_sphereTwoProdReal :
    Nonempty (TwoSidedSeparation (Set.range (fun x : SphereTwo => (x, (0 : ℝ))))) := by
  let p₀ : SphereTwo :=
    ⟨sphereTwoNorthVector, by
      rw [Metric.mem_sphere, dist_eq_norm, sub_zero, norm_sphereTwoNorthVector]⟩
  have hpos : ({p : SphereTwo × ℝ | 0 < p.2} : Set (SphereTwo × ℝ)) =
      Set.univ ×ˢ Set.Ioi 0 := by
    ext p
    simp
  have hneg : ({p : SphereTwo × ℝ | p.2 < 0} : Set (SphereTwo × ℝ)) =
      Set.univ ×ˢ Set.Iio 0 := by
    ext p
    simp
  refine ⟨{p : SphereTwo × ℝ | 0 < p.2}, {p : SphereTwo × ℝ | p.2 < 0},
    isOpen_lt continuous_const continuous_snd, isOpen_lt continuous_snd continuous_const,
    ⟨(p₀, 1), by simp⟩, ⟨(p₀, -1), by simp⟩, ?_, ?_, ?_, ?_⟩
  · rw [Set.disjoint_left]
    intro p ha hb
    have ha' : 0 < p.2 := ha
    have hb' : p.2 < 0 := hb
    linarith
  · rw [range_prod_zero]
    ext p
    constructor
    · rintro (h | h) hpz
      · have hpz' : p.2 = 0 := by simpa using hpz
        have h' : 0 < p.2 := h
        linarith
      · have hpz' : p.2 = 0 := by simpa using hpz
        have h' : p.2 < 0 := h
        linarith
    · intro hpz
      have hpz' : p.2 ≠ 0 := by simpa using hpz
      rcases lt_or_gt_of_ne hpz' with h | h
      · exact Or.inr h
      · exact Or.inl h
  · rw [hpos, range_prod_zero]
    exact frontier_prod_Ioi 0
  · rw [hneg, range_prod_zero]
    exact frontier_prod_Iio 0

theorem nonempty_twoSidedSeparation_range_coe_sphere :
    Nonempty (TwoSidedSeparation (Set.range (fun x : SphereTwo => (x : EuclideanThree)))) :=
by
  have he := @isSmoothEmbedding_coe_sphere EuclideanThree inferInstance inferInstance 2
    (⟨by simp⟩ : Fact (Module.finrank ℝ EuclideanThree = 2 + 1))
  have d : SphereSides (Set.range (fun x : SphereTwo => (x : EuclideanThree))) :=
    ((jordanBrouwer_openThreeSpace (fun x : SphereTwo => (x : EuclideanThree)) he
      (Diffeomorph.refl (modelWithCornersSelf ℝ EuclideanThree)
        EuclideanThree ∞)).toSphereSides)
  exact ⟨d.toTwoSidedSeparation⟩

end DifferentialGeometry.Topology.SphereSeparation
