import DifferentialGeometry.Topology.PiecewiseLinear.CompactEmbeddingApproximation
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellOnPolyhedralBall
import DifferentialGeometry.Topology.PiecewiseLinear.LocallyFiniteLocalModel

open Set Function Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem mapsTo_of_equiv_eqOn_compl {X : Type*} (f : X ≃ X)
    {S : Set X} (hfix : EqOn f id Sᶜ) : MapsTo f S S := by
  intro x hx
  by_contra hnot
  have heq : f x = x := f.injective (hfix hnot)
  exact hnot (heq.symm ▸ hx)

private theorem image_eq_of_equiv_eqOn_compl {X : Type*} (f : X ≃ X)
    {S : Set X} (hfix : EqOn f id Sᶜ) : f '' S = S := by
  refine Subset.antisymm (mapsTo_of_equiv_eqOn_compl f hfix).image_subset ?_
  intro y hy
  obtain ⟨x, rfl⟩ := f.surjective y
  refine ⟨x, ?_, rfl⟩
  by_contra hx
  exact hx (by simpa only [hfix hx, id_eq] using hy)

private theorem exists_equiv_of_finite_disjoint_support {ι X : Type*}
    (s : Finset ι) (Ω : ι → Set X) (φ : ι → X ≃ X) (hdis : Pairwise (Disjoint on Ω))
    (hfix : ∀ i ∈ s, EqOn (φ i) id (Ω i)ᶜ) :
    ∃ Φ : X ≃ X, (∀ i ∈ s, EqOn Φ (φ i) (Ω i)) ∧ EqOn Φ id (⋃ i ∈ s, Ω i)ᶜ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨Equiv.refl X, ?_, fun _ _ => rfl⟩
    simp
  | @insert i s hi ih =>
    obtain ⟨Φ, hΦeq, hΦfix⟩ := ih (fun j hj => hfix j (Finset.mem_insert_of_mem hj))
    refine ⟨Φ.trans (φ i), ?_, ?_⟩
    · intro j hj x hx
      rcases Finset.mem_insert.mp hj with hji | hj
      · subst j
        have hxout : x ∉ ⋃ j ∈ s, Ω j := by
          intro hxU
          obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hxU
          exact Set.disjoint_left.mp (hdis (show i ≠ j from fun heq => hi (heq.symm ▸ hj))) hx hxj
        change φ i (Φ x) = φ i x
        rw [hΦfix hxout, id_eq]
      · have hji : j ≠ i := fun heq => hi (heq ▸ hj)
        have hy : φ j x ∈ Ω j := mapsTo_of_equiv_eqOn_compl (φ j)
          (hfix j (Finset.mem_insert_of_mem hj)) hx
        change φ i (Φ x) = φ j x
        rw [hΦeq j hj hx]
        exact hfix i (Finset.mem_insert_self _ _) (Set.disjoint_left.mp (hdis hji) hy)
    · intro x hx
      have hxi : x ∉ Ω i := fun hxi => hx (mem_iUnion₂.mpr
        ⟨i, Finset.mem_insert_self _ _, hxi⟩)
      have hxs : x ∉ ⋃ j ∈ s, Ω j := by
        intro hxU
        obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hxU
        exact hx (mem_iUnion₂.mpr ⟨j, Finset.mem_insert_of_mem hj, hxj⟩)
      change φ i (Φ x) = x
      rw [hΦfix hxs, id_eq, hfix i (Finset.mem_insert_self _ _) hxi, id_eq]

theorem exists_isPL_embedding_of_finite_disjoint_support {ι M : Type*}
    [TopologicalSpace M] [T2Space M] {n : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [HasGroupoid M (plGroupoid n)]
    {C : Set M} (hC : IsCompact C) (hid : IsPLOn n n (id : M → M) C)
    (s : Finset ι) (Ω K : ι → Set M) (φ : ι → M ≃ M)
    (hΩ : ∀ i ∈ s, IsOpen (Ω i)) (hK : ∀ i ∈ s, IsClosed (K i))
    (hKΩ : ∀ i ∈ s, K i ⊆ Ω i) (hdis : Pairwise (Disjoint on Ω))
    (hPL : ∀ i ∈ s, IsPLOn n n (φ i) C) (hfix : ∀ i ∈ s, EqOn (φ i) id (K i)ᶜ) :
    ∃ Φ : M ≃ M, IsPLHomeomorphInto n Φ C ∧
      (∀ i ∈ s, EqOn Φ (φ i) (Ω i)) ∧
      (∀ i ∈ s, Φ '' C ∩ Ω i = φ i '' C ∩ Ω i) ∧ EqOn Φ id (⋃ i ∈ s, K i)ᶜ := by
  obtain ⟨Φ, hΦeq, hΦfix⟩ := exists_equiv_of_finite_disjoint_support s Ω φ hdis
    (fun i hi x hx => hfix i hi fun hxK => hx (hKΩ i hi hxK))
  have hΦK : EqOn Φ id (⋃ i ∈ s, K i)ᶜ := by
    intro x hx
    by_cases hxΩ : x ∈ ⋃ i ∈ s, Ω i
    · obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hxΩ
      exact (hΦeq i hi hxi).trans (hfix i hi fun hxK => hx (mem_iUnion₂.mpr ⟨i, hi, hxK⟩))
    · exact hΦfix hxΩ
  have hPLΦ : IsPLOn n n Φ C := by
    intro x hx
    by_cases hxΩ : x ∈ ⋃ i ∈ s, Ω i
    · obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hxΩ
      apply piecewiseAffineProperty_localInvariantProp.liftPropWithinAt_congr_of_eventuallyEq_of_mem
        (hPL i hi x hx) _ hx
      filter_upwards [mem_nhdsWithin_of_mem_nhds ((hΩ i hi).mem_nhds hxi)] with y hy
      exact hΦeq i hi hy
    · have hxK : x ∉ ⋃ i ∈ s, K i := by
        intro hxK
        obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hxK
        exact hxΩ (mem_iUnion₂.mpr ⟨i, hi, hKΩ i hi hxi⟩)
      have hclosed : IsClosed (⋃ i ∈ s, K i) := isClosed_biUnion_finset hK
      apply piecewiseAffineProperty_localInvariantProp.liftPropWithinAt_congr_of_eventuallyEq_of_mem
        (hid x hx) _ hx
      filter_upwards [mem_nhdsWithin_of_mem_nhds (hclosed.isOpen_compl.mem_nhds hxK)] with y hy
      exact hΦK hy
  refine ⟨Φ, hPLΦ.isPLHomeomorphInto hC Φ.injective.injOn, hΦeq, ?_, hΦK⟩
  intro i hi
  have hφΩ : φ i '' Ω i = Ω i := image_eq_of_equiv_eqOn_compl (φ i)
    (fun x hx => hfix i hi fun hxK => hx (hKΩ i hi hxK))
  have hΦΩ : Φ '' Ω i = Ω i := (image_congr (hΦeq i hi)).trans hφΩ
  calc
    Φ '' C ∩ Ω i = Φ '' (C ∩ Ω i) := by rw [image_inter Φ.injective, hΦΩ]
    _ = φ i '' (C ∩ Ω i) := image_congr ((hΦeq i hi).mono inter_subset_right)
    _ = φ i '' C ∩ Ω i := by rw [image_inter (φ i).injective, hφΩ]

theorem IsPLCellOn.exists_image_of_finite_disjoint_support {ι M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [HasGroupoid M (plGroupoid 3)] {d : ℕ} {C B : Set M} (hC : IsPLCellOn d C B)
    (s : Finset ι) (Ω K : ι → Set M) (φ : ι → M ≃ M)
    (hΩ : ∀ i ∈ s, IsOpen (Ω i)) (hK : ∀ i ∈ s, IsClosed (K i))
    (hKΩ : ∀ i ∈ s, K i ⊆ Ω i) (hdis : Pairwise (Disjoint on Ω))
    (hPL : ∀ i ∈ s, IsPLOn 3 3 (φ i) C) (hfix : ∀ i ∈ s, EqOn (φ i) id (K i)ᶜ) :
    ∃ Φ : M ≃ M, IsPLCellOn d (Φ '' C) (Φ '' B) ∧
      (∀ i ∈ s, EqOn Φ (φ i) (Ω i)) ∧
      (∀ i ∈ s, Φ '' C ∩ Ω i = φ i '' C ∩ Ω i) ∧
      EqOn Φ id (⋃ i ∈ s, K i)ᶜ ∧ Φ '' C \ (⋃ i ∈ s, K i) = C \ (⋃ i ∈ s, K i) := by
  obtain ⟨T, -⟩ := hC.isPolyhedralBall
  obtain ⟨Φ, hΦ, heq, himage, hΦfix⟩ := exists_isPL_embedding_of_finite_disjoint_support
    hC.isCompact T.isPLOn_id
    s Ω K φ hΩ hK hKΩ hdis hPL hfix
  refine ⟨Φ, hC.image hΦ, heq, himage, hΦfix, ?_⟩
  apply Subset.antisymm
  · rintro y ⟨⟨x, hx, hxy⟩, hy⟩
    have he : x = y := Φ.injective (hxy.trans (hΦfix hy).symm)
    exact ⟨he ▸ hx, hy⟩
  · rintro x ⟨hx, hn⟩
    exact ⟨⟨x, hx, hΦfix hn⟩, hn⟩

end DifferentialGeometry.Topology.PiecewiseLinear
