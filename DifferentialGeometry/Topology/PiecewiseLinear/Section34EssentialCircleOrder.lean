import DifferentialGeometry.Topology.PiecewiseLinear.Section34EssentialCircleAdjacency
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingGenerators
import Mathlib.Data.Finset.Sort

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLSphere.exists_ordered_disk_caps_of_essential_family
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {S A A₀ A₁ : Set E} (hS : IsPLSphere 2 S) (hA : IsAnnulusOn A A₀ A₁)
    (hAS : A ⊆ S) (C : Set (Set E)) (hC : C.Finite)
    (hCsph : ∀ J ∈ C, IsPLSphere 1 J) (hCA : ∀ J ∈ C, J ⊆ A)
    (hCend : ∀ J ∈ C, Disjoint J (A₀ ∪ A₁)) (hCdisj : C.PairwiseDisjoint id)
    (hCess : ∀ J ∈ C, ¬ ∃ (D : Set E) (r : (Fin 3 → ℝ) → E),
      IsPLHomeomorphOn r (stdSimplex ℝ (Fin 3)) D ∧ D ⊆ A ∧
        r '' stdSimplexBoundary 2 = J) :
    ∃ (e : Fin C.ncard ≃ C) (D₀ D₁ : Fin C.ncard → Set E)
      (r₀ r₁ : Fin C.ncard → (Fin 3 → ℝ) → E),
      (∀ i, IsPLHomeomorphOn (r₀ i) (stdSimplex ℝ (Fin 3)) (D₀ i) ∧
        IsPLHomeomorphOn (r₁ i) (stdSimplex ℝ (Fin 3)) (D₁ i) ∧
        r₀ i '' stdSimplexBoundary 2 = (e i).val ∧
        r₁ i '' stdSimplexBoundary 2 = (e i).val ∧
        D₀ i ∪ D₁ i = S ∧ D₀ i ∩ D₁ i = (e i).val ∧
        A₀ ⊆ D₀ i ∧ A₁ ⊆ D₁ i) ∧
      StrictMono D₀ ∧ StrictAnti D₁ ∧
      (∀ i j, i < j → Disjoint (D₀ i) (D₁ j)) ∧
      (∀ i j, (e i).val ⊆ D₀ j ↔ i ≤ j) ∧
      (∀ i j, (e i).val ⊆ D₁ j ↔ j ≤ i) := by
  classical
  let _ : Fintype C := hC.fintype
  choose D₀ D₁ r₀ r₁ hDU hDI hr₀ hr₁ hb₀ hb₁ hA₀D hA₁D using
    fun i : C => (hS.exists_disk_in_annulus_or_separating_ends hA hAS
      (hCsph i.val i.property) (hCA i.val i.property)
      (hCend i.val i.property)).resolve_left (hCess i.val i.property)
  have horder : ∀ i j : C, i ≠ j →
      (j.val ⊆ D₀ i ∧ D₀ j ⊂ D₀ i ∧ Disjoint (D₁ i) (D₀ j)) ∨
        (j.val ⊆ D₁ i ∧ D₀ i ⊂ D₀ j ∧ Disjoint (D₀ i) (D₁ j)) := by
    intro i j hij
    apply disk_caps_strictly_ordered_of_disjoint_boundaries
      (hDU i) (hDI i) (hDU j) (hDI j)
      (IsPLBall.isConnected ⟨r₀ i, hr₀ i⟩).isPreconnected
      (IsPLBall.isConnected ⟨r₁ i, hr₁ i⟩).isPreconnected
      (IsPLBall.isPolyhedron ⟨r₀ i, hr₀ i⟩).isClosed
      (IsPLBall.isPolyhedron ⟨r₁ i, hr₁ i⟩).isClosed
      (IsPLBall.isPolyhedron ⟨r₀ j, hr₀ j⟩).isClosed
      (IsPLBall.isPolyhedron ⟨r₁ j, hr₁ j⟩).isClosed
      (hCsph i.val i.property).nonempty (hCsph j.val j.property).isConnected
      (hCdisj i.property j.property (fun h => hij (Subtype.ext h)))
    · obtain ⟨x, hx⟩ := hA.ends_nonempty.1
      exact ⟨x, ⟨hA₀D i hx, hA₀D j hx⟩,
        fun hxJ => disjoint_left.mp (hCend j.val j.property) hxJ (Or.inl hx)⟩
    · obtain ⟨x, hx⟩ := hA.ends_nonempty.2
      exact ⟨x, ⟨hA₁D i hx, hA₁D j hx⟩,
        fun hxJ => disjoint_left.mp (hCend j.val j.property) hxJ (Or.inr hx)⟩
  have hinj : Function.Injective D₀ := by
    intro i j heq
    by_contra hij
    rcases horder i j hij with h | h
    · exact h.2.1.ne heq.symm
    · exact h.2.1.ne heq
  let ord : PartialOrder C := PartialOrder.lift D₀ hinj
  let _ : LinearOrder C :=
    { ord with
      le_total := by
        intro i j
        by_cases hij : i = j
        · exact Or.inl (hij ▸ Subset.rfl)
        rcases horder i j hij with h | h
        · exact Or.inr h.2.1.1
        · exact Or.inl h.2.1.1
      toDecidableLE := fun i j => Classical.propDecidable (D₀ i ⊆ D₀ j) }
  let _ : LE C := ord.toLE
  let e := Fintype.orderIsoFinOfCardEq C (k := C.ncard)
    (by rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq])
  have hmono : StrictMono (D₀ ∘ e) := by
    intro i j hij
    refine ⟨e.le_iff_le.mpr hij.le, ?_⟩
    intro hji
    exact hij.not_ge (e.le_iff_le.mp hji)
  have hdis (i j : Fin C.ncard) (hij : i < j) : Disjoint (D₀ (e i)) (D₁ (e j)) := by
    rcases horder (e i) (e j) (e.injective.ne hij.ne) with h | h
    · exact (h.2.1.2 (hmono hij).1).elim
    · exact h.2.2
  have hanti : StrictAnti (D₁ ∘ e) := by
    intro i j hij
    refine ⟨?_, ?_⟩
    · intro x hx
      have hxS : x ∈ S := hDU (e j) ▸ Or.inr hx
      exact ((hDU (e i)).symm ▸ hxS).resolve_left
        (fun hy => disjoint_left.mp (hdis i j hij) hy hx)
    · intro hsub
      obtain ⟨x, hx⟩ := (hCsph (e i).val (e i).property).nonempty
      have hxD := (hDI (e i)).symm ▸ hx
      exact disjoint_left.mp (hdis i j hij) hxD.1 (hsub hxD.2)
  refine ⟨e.toEquiv, D₀ ∘ e, D₁ ∘ e, r₀ ∘ e, r₁ ∘ e, ?_, hmono, hanti, hdis, ?_, ?_⟩
  · intro i
    exact ⟨hr₀ (e i), hr₁ (e i), hb₀ (e i), hb₁ (e i), hDU (e i), hDI (e i),
      hA₀D (e i), hA₁D (e i)⟩
  · intro i j
    constructor
    · intro hsub
      by_contra hij
      have hji := lt_of_not_ge hij
      obtain ⟨x, hx⟩ := (hCsph (e i).val (e i).property).nonempty
      exact disjoint_left.mp (hdis j i hji) (hsub hx) ((hDI (e i)).superset hx).2
    · intro hij x hx
      exact hmono.monotone hij ((hDI (e i)).superset hx).1
  · intro i j
    constructor
    · intro hsub
      by_contra hji
      have hij := lt_of_not_ge hji
      obtain ⟨x, hx⟩ := (hCsph (e i).val (e i).property).nonempty
      exact disjoint_left.mp (hdis i j hij) ((hDI (e i)).superset hx).1 (hsub hx)
    · intro hji x hx
      exact hanti.antitone hji ((hDI (e i)).superset hx).2

end DifferentialGeometry.Topology.PiecewiseLinear
