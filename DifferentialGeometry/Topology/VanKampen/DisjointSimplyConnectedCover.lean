import DifferentialGeometry.Topology.VanKampen.TorsionFreeCover
import DifferentialGeometry.Topology.VanKampen.SimplyConnectedUnion
import DifferentialGeometry.Topology.Algebra.Group.FiniteTorsionFree

noncomputable section

open Set

namespace Poincare.Topology.VanKampen

private theorem path_range_subset_cover_member
    {X ι : Type*} [TopologicalSpace X] (U : ι → Set X)
    (hU : ∀ i, IsOpen (U i)) (hd : Pairwise fun i j ↦ Disjoint (U i) (U j))
    {x y : X} (p : Path x y) (hp : range p ⊆ ⋃ i, U i)
    (i : ι) (hx : x ∈ U i) : range p ⊆ U i := by
  classical
  let V := ⋃ j, ⋃ (_ : j ≠ i), U j
  have hV : IsOpen V := isOpen_iUnion fun j ↦ isOpen_iUnion fun _ ↦ hU j
  have hdV : Disjoint (U i) V := by
    simp only [V, disjoint_iUnion_right]
    intro j hji
    exact hd hji.symm
  have hc : range p ⊆ U i ∪ V := by
    intro z hz
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hp hz)
    by_cases hji : j = i
    · exact Or.inl (hji ▸ hj)
    · exact Or.inr (mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨hji, hj⟩⟩)
  exact (isPreconnected_range p.continuous).subset_left_of_subset_union
    (hU i) hV hdV hc ⟨x, ⟨0, p.source⟩, hx⟩

theorem subsingleton_pathHomotopicQuotient_iUnion_of_pairwise_disjoint
    {X ι : Type*} [TopologicalSpace X] (U : ι → Set X)
    (hU : ∀ i, IsOpen (U i)) (hd : Pairwise fun i j ↦ Disjoint (U i) (U j))
    (hsc : ∀ i, SimplyConnectedSpace (U i)) (x y : ↑(⋃ i, U i)) :
    Subsingleton (Path.Homotopic.Quotient x y) := by
  classical
  constructor
  intro p q
  induction p using Path.Homotopic.Quotient.ind with
  | mk p =>
    induction q using Path.Homotopic.Quotient.ind with
    | mk q =>
      obtain ⟨i, hxi⟩ := mem_iUnion.mp x.property
      let p' : Path x.val y.val := p.map continuous_subtype_val
      let q' : Path x.val y.val := q.map continuous_subtype_val
      have hp : range p' ⊆ U i := path_range_subset_cover_member U hU hd p'
        (by rintro z ⟨t, rfl⟩; exact (p t).property) i hxi
      have hq : range q' ⊆ U i := path_range_subset_cover_member U hU hd q'
        (by rintro z ⟨t, rfl⟩; exact (q t).property) i hxi
      let _ : SimplyConnectedSpace (U i) := hsc i
      let j : C(U i, ↑(⋃ i, U i)) :=
        ⟨fun z ↦ ⟨z.val, mem_iUnion.mpr ⟨i, z.property⟩⟩,
          continuous_subtype_val.subtype_mk _⟩
      have hh := (SimplyConnectedSpace.paths_homotopic
        (pathIn (U i) p' hp) (pathIn (U i) q' hq)).map j
      have he₁ : (pathIn (U i) p' hp).map j.continuous = p := by ext t; rfl
      have he₂ : (pathIn (U i) q' hq).map j.continuous = q := by ext t; rfl
      rw [he₁, he₂] at hh
      exact Path.Homotopic.Quotient.eq.mpr hh

theorem isMulTorsionFree_fundamentalGroup_of_two_disjoint_families
    {X ι κ : Type*} [TopologicalSpace X] [PathConnectedSpace X]
    (U : ι → Set X) (V : κ → Set X)
    (hU : ∀ i, IsOpen (U i)) (hV : ∀ j, IsOpen (V j))
    (hdU : Pairwise fun i j ↦ Disjoint (U i) (U j))
    (hdV : Pairwise fun i j ↦ Disjoint (V i) (V j))
    (hscU : ∀ i, SimplyConnectedSpace (U i)) (hscV : ∀ j, SimplyConnectedSpace (V j))
    (hcover : (⋃ i, U i) ∪ (⋃ j, V j) = univ) (x₀ : X) :
    IsMulTorsionFree (FundamentalGroup X x₀) :=
  isMulTorsionFree_fundamentalGroup_of_open_cover
    (⋃ i, U i) (⋃ j, V j) (isOpen_iUnion hU) (isOpen_iUnion hV) hcover
    (subsingleton_pathHomotopicQuotient_iUnion_of_pairwise_disjoint U hU hdU hscU)
    (subsingleton_pathHomotopicQuotient_iUnion_of_pairwise_disjoint V hV hdV hscV) x₀

theorem isMulTorsionFree_fundamentalGroup_of_open_chain
    {X : Type*} [TopologicalSpace X] [PathConnectedSpace X] {n : ℕ}
    (U : Fin n → Set X) (hU : ∀ i, IsOpen (U i))
    (hsc : ∀ i, SimplyConnectedSpace (U i))
    (hd : ∀ i j, i.val + 1 < j.val → Disjoint (U i) (U j))
    (hcover : ⋃ i, U i = univ) (x₀ : X) :
    IsMulTorsionFree (FundamentalGroup X x₀) := by
  classical
  let A := {i : Fin n // i.val % 2 = 0}
  let B := {i : Fin n // i.val % 2 ≠ 0}
  have hdisj {i j : Fin n} (hne : i ≠ j) (hpar : i.val % 2 = j.val % 2) :
      Disjoint (U i) (U j) := by
    have hv : i.val ≠ j.val := fun h ↦ hne (Fin.ext h)
    rcases lt_or_gt_of_ne hv with hij | hji
    · exact hd i j (by omega)
    · exact (hd j i (by omega)).symm
  apply isMulTorsionFree_fundamentalGroup_of_two_disjoint_families
    (fun i : A ↦ U i.val) (fun j : B ↦ U j.val)
    (fun i ↦ hU i.val) (fun j ↦ hU j.val)
    (fun i j hij ↦ hdisj (fun h ↦ hij (Subtype.ext h))
      (i.property.trans j.property.symm))
    (fun i j hij ↦ hdisj (fun h ↦ hij (Subtype.ext h)) (by
      have hi := i.property
      have hj := j.property
      omega))
    (fun i ↦ hsc i.val) (fun j ↦ hsc j.val) ?_ x₀
  apply eq_univ_of_forall
  intro x
  have hx : x ∈ ⋃ i, U i := by rw [hcover]; trivial
  obtain ⟨i, hi⟩ := mem_iUnion.mp hx
  by_cases hp : i.val % 2 = 0
  · exact Or.inl (mem_iUnion.mpr ⟨⟨i, hp⟩, hi⟩)
  · exact Or.inr (mem_iUnion.mpr ⟨⟨i, hp⟩, hi⟩)

theorem isMulTorsionFree_fundamentalGroup_iUnion_of_open_chain
    {X : Type*} [TopologicalSpace X] {n : ℕ}
    (U : Fin n → Set X) (hU : ∀ i, IsOpen (U i))
    (hsc : ∀ i, SimplyConnectedSpace (U i))
    (hd : ∀ i j, i.val + 1 < j.val → Disjoint (U i) (U j))
    [PathConnectedSpace (↑(⋃ i, U i))] (x₀ : ↑(⋃ i, U i)) :
    IsMulTorsionFree (FundamentalGroup (↑(⋃ i, U i)) x₀) := by
  let V (i : Fin n) : Set (↑(⋃ i, U i)) := Subtype.val ⁻¹' U i
  have hVsc (i : Fin n) : SimplyConnectedSpace (V i) := by
    let _ : SimplyConnectedSpace (U i) := hsc i
    let e : V i ≃ₜ U i := _root_.Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange
      (by intro x hx; exact ⟨⟨x, mem_iUnion.mpr ⟨i, hx⟩⟩, rfl⟩)
    exact e.toHomotopyEquiv.simplyConnectedSpace
  apply isMulTorsionFree_fundamentalGroup_of_open_chain V
    (fun i ↦ (hU i).preimage continuous_subtype_val) hVsc
    (fun i j hij ↦ (hd i j hij).preimage Subtype.val) ?_ x₀
  apply eq_univ_of_forall
  intro x
  obtain ⟨i, hi⟩ := mem_iUnion.mp x.property
  exact mem_iUnion.mpr ⟨i, hi⟩

theorem simplyConnectedSpace_of_injective_comp_through_torsion_free
    {W N M : Type*} [TopologicalSpace W] [TopologicalSpace N] [TopologicalSpace M]
    [PathConnectedSpace W] (f : C(W, N)) (g : C(N, M)) (w₀ : W)
    [Finite (FundamentalGroup M (g (f w₀)))]
    [IsMulTorsionFree (FundamentalGroup N (f w₀))]
    (hinj : Function.Injective
      ((FundamentalGroup.map g (f w₀)).comp (FundamentalGroup.map f w₀))) :
    SimplyConnectedSpace W := by
  apply (simplyConnectedSpace_iff_fundamentalGroup_subsingleton W w₀).2
  exact Poincare.Algebra.Group.subsingleton_of_injective_comp_through_torsion_free
    (FundamentalGroup.map f w₀) (FundamentalGroup.map g (f w₀)) hinj

end Poincare.Topology.VanKampen
