import DifferentialGeometry.Topology.VanKampen.SimplyConnectedStarCover
import Mathlib.Data.Fintype.Pi

set_option autoImplicit false

noncomputable section

open Set

universe u v

namespace DifferentialGeometry.Topology.VanKampen

private noncomputable def subtypePreimageHomeomorph {X : Type u} [TopologicalSpace X]
    {A B : Set X} (hAB : A ⊆ B) : {x : ↥B // x.1 ∈ A} ≃ₜ ↥A where
  toFun x := ⟨x.1.1, x.2⟩
  invFun a := ⟨⟨a.1, hAB a.2⟩, a.2⟩
  left_inv _ := Subtype.ext (Subtype.ext rfl)
  right_inv _ := Subtype.ext rfl
  continuous_toFun := Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _
  continuous_invFun := Continuous.subtype_mk (Continuous.subtype_mk continuous_subtype_val _) _

private theorem simplyConnectedSpace_subtype_preimage_iff {X : Type u} [TopologicalSpace X]
    {A B : Set X} (hAB : A ⊆ B) :
    SimplyConnectedSpace {x : ↥B // x.1 ∈ A} ↔ SimplyConnectedSpace ↥A :=
  (subtypePreimageHomeomorph hAB).toHomotopyEquiv.simplyConnectedSpace_iff

private theorem pathConnectedSpace_of_homeomorph {A B : Type u} [TopologicalSpace A]
    [TopologicalSpace B] (e : A ≃ₜ B) : PathConnectedSpace A ↔ PathConnectedSpace B := by
  constructor
  · intro h
    have h3 := (pathConnectedSpace_iff_univ.mp h).image e.continuous
    rw [Set.image_univ, e.surjective.range_eq] at h3
    exact pathConnectedSpace_iff_univ.mpr h3
  · intro h
    have h3 := (pathConnectedSpace_iff_univ.mp h).image e.symm.continuous
    rw [Set.image_univ, e.symm.surjective.range_eq] at h3
    exact pathConnectedSpace_iff_univ.mpr h3

private theorem pathConnectedSpace_subtype_preimage_iff {X : Type u} [TopologicalSpace X]
    {A B : Set X} (hAB : A ⊆ B) :
    PathConnectedSpace {x : ↥B // x.1 ∈ A} ↔ PathConnectedSpace ↥A :=
  pathConnectedSpace_of_homeomorph (subtypePreimageHomeomorph hAB)

private theorem isPathConnected_union_iUnion_fin {X : Type u} [TopologicalSpace X] :
    ∀ {n : ℕ} (U : Set X) (V : Fin n → Set X), IsPathConnected U →
      (∀ i, IsPathConnected (V i)) → (∀ i, (U ∩ V i).Nonempty) →
      IsPathConnected (U ∪ ⋃ i, V i) := by
  intro n
  induction n with
  | zero =>
      intro U V hU _ _
      simpa using hU
  | succ n ih =>
      intro U V hU hV hne
      have hres := ih U (fun i : Fin n => V i.castSucc) hU (fun i => hV i.castSucc)
        (fun i => hne i.castSucc)
      have hneY : ((U ∪ ⋃ i : Fin n, V i.castSucc) ∩ V (Fin.last n)).Nonempty := by
        obtain ⟨x, hx⟩ := hne (Fin.last n)
        exact ⟨x, Or.inl hx.1, hx.2⟩
      have h2 := hres.union (hV (Fin.last n)) hneY
      have htarget : U ∪ ⋃ i : Fin (n + 1), V i =
          (U ∪ ⋃ i : Fin n, V i.castSucc) ∪ V (Fin.last n) := by
        rw [Set.iUnion_fin_add_one_eq_iUnion_castSucc V, Set.union_assoc]
        rfl
      rw [htarget]
      exact h2

private theorem simplyConnectedSpace_coverMembers_fin :
    ∀ (n : ℕ) (X : Type u) [TopologicalSpace X] (U : Set X) (V : Fin n → Set X),
      IsOpen U → (∀ i, IsOpen (V i)) → U ∪ ⋃ i, V i = univ →
      Pairwise (fun i j => Disjoint (V i) (V j)) →
      PathConnectedSpace ↥U → (∀ i, PathConnectedSpace ↥(V i)) →
      SimplyConnectedSpace X → (∀ i, SimplyConnectedSpace ↥(U ∩ V i)) →
      SimplyConnectedSpace ↥U ∧ ∀ i, SimplyConnectedSpace ↥(V i) := by
  intro n
  induction n with
  | zero =>
      intro X _ U V hU hV hcover hdisj hpcU hpcV hscX hscI
      have hUuniv : U = univ := by
        have h : U ∪ ⋃ i : Fin 0, V i = U := by simp
        rw [h] at hcover
        exact hcover
      constructor
      · rw [hUuniv]
        exact (Homeomorph.Set.univ X).toHomotopyEquiv.simplyConnectedSpace_iff.mpr hscX
      · intro i
        exact i.elim0
  | succ n ih =>
      intro X _ U V hU hV hcover hdisj hpcU hpcV hscX hscI
      let A : Set X := U ∪ ⋃ i : Fin n, V i.castSucc
      have hAopen : IsOpen A := hU.union (isOpen_iUnion fun i => hV i.castSucc)
      have hYopen : IsOpen (V (Fin.last n)) := hV _
      have hAY : A ∩ V (Fin.last n) = U ∩ V (Fin.last n) := by
        ext x
        constructor
        · rintro ⟨hx, hxY⟩
          rcases hx with hx | hx
          · exact ⟨hx, hxY⟩
          · obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
            exact (Set.disjoint_left.mp (hdisj (Fin.castSucc_ne_last i)) hxi hxY).elim
        · rintro ⟨hx, hxY⟩
          exact ⟨Or.inl hx, hxY⟩
      have hAunion : A ∪ V (Fin.last n) = univ := by
        have h : A ∪ V (Fin.last n) = U ∪ ⋃ i : Fin (n + 1), V i := by
          change (U ∪ ⋃ i : Fin n, V i.castSucc) ∪ V (Fin.last n) =
            U ∪ ⋃ i : Fin (n + 1), V i
          rw [Set.iUnion_fin_add_one_eq_iUnion_castSucc V, Set.union_assoc]
          rfl
        rw [h]
        exact hcover
      have hpcA : PathConnectedSpace ↥A := by
        refine isPathConnected_iff_pathConnectedSpace.mp ?_
        exact isPathConnected_union_iUnion_fin U (fun i : Fin n => V i.castSucc)
          (isPathConnected_iff_pathConnectedSpace.mpr hpcU)
          (fun i => isPathConnected_iff_pathConnectedSpace.mpr (hpcV i.castSucc))
          (fun i => by
            obtain ⟨w⟩ := (simply_connected_iff_unique_homotopic
              ↥(U ∩ V i.castSucc)).mp (hscI i.castSucc) |>.1
            exact ⟨w.1, w.2⟩)
      have hneLast : (U ∩ V (Fin.last n)).Nonempty := by
        obtain ⟨w⟩ := (simply_connected_iff_unique_homotopic
          ↥(U ∩ V (Fin.last n))).mp (hscI (Fin.last n)) |>.1
        exact ⟨w.1, w.2⟩
      obtain ⟨z, hz⟩ := hneLast
      obtain ⟨hzU, hzY⟩ := hz
      have hscAY : SimplyConnectedSpace ↥(A ∩ V (Fin.last n)) := by
        rw [hAY]
        exact hscI (Fin.last n)
      obtain ⟨hAsc, hYsc⟩ :=
        @simplyConnected_coverMembers_of_union X _ A (V (Fin.last n)) hAopen hYopen
          hAunion z ⟨Or.inl hzU, hzY⟩ hpcA (hpcV (Fin.last n)) hscX hscAY
      have hUA : U ⊆ A := fun _ hx => Or.inl hx
      have hVA : ∀ i : Fin n, V i.castSucc ⊆ A :=
        fun i _ hx => Or.inr (Set.mem_iUnion.mpr ⟨i, hx⟩)
      have hpcU' : PathConnectedSpace ↥(Subtype.val ⁻¹' U : Set ↥A) :=
        (pathConnectedSpace_subtype_preimage_iff hUA).mpr hpcU
      have hpcV' : ∀ i : Fin n,
          PathConnectedSpace ↥(Subtype.val ⁻¹' (V i.castSucc) : Set ↥A) :=
        fun i => (pathConnectedSpace_subtype_preimage_iff (hVA i)).mpr (hpcV i.castSucc)
      have hscI' : ∀ i : Fin n, SimplyConnectedSpace
          ↥((Subtype.val ⁻¹' U : Set ↥A) ∩ (Subtype.val ⁻¹' (V i.castSucc) : Set ↥A)) :=
        fun i => (simplyConnectedSpace_subtype_preimage_iff (A := U ∩ V i.castSucc)
          (fun _ hx => Or.inl hx.1)).mpr (hscI i.castSucc)
      have hcover' : (Subtype.val ⁻¹' U : Set ↥A) ∪
          ⋃ i : Fin n, (Subtype.val ⁻¹' (V i.castSucc) : Set ↥A) = univ := by
        rw [← Set.preimage_iUnion, ← Set.preimage_union]
        exact Set.eq_univ_of_forall fun x => x.2
      have hdisj' : Pairwise fun i j : Fin n =>
          Disjoint (Subtype.val ⁻¹' (V i.castSucc) : Set ↥A)
            (Subtype.val ⁻¹' (V j.castSucc) : Set ↥A) :=
        fun i j hij => Disjoint.preimage _ (hdisj fun h => hij (Fin.castSucc_inj.mp h))
      have hrec := ih ↥A (Subtype.val ⁻¹' U)
        (fun i : Fin n => Subtype.val ⁻¹' (V i.castSucc))
        (hU.preimage continuous_subtype_val)
        (fun i => (hV i.castSucc).preimage continuous_subtype_val)
        hcover' hdisj' hpcU' hpcV' hAsc hscI'
      have hUsc : SimplyConnectedSpace ↥U :=
        (simplyConnectedSpace_subtype_preimage_iff hUA).mp hrec.1
      have hVsc : ∀ i : Fin n, SimplyConnectedSpace ↥(V i.castSucc) :=
        fun i => (simplyConnectedSpace_subtype_preimage_iff (hVA i)).mp (hrec.2 i)
      refine ⟨hUsc, ?_⟩
      intro j
      exact Fin.lastCases hYsc hVsc j

theorem simplyConnectedSpace_coverMembers_of_pairwiseDisjoint_open_cover
    {X : Type u} [TopologicalSpace X] {ι : Type v} [Finite ι]
    (U : Set X) (V : ι → Set X) (hU : IsOpen U) (hV : ∀ i, IsOpen (V i))
    (hcover : U ∪ ⋃ i, V i = univ)
    (hdisj : Pairwise fun i j => Disjoint (V i) (V j))
    [PathConnectedSpace ↥U] [∀ i, PathConnectedSpace ↥(V i)]
    [SimplyConnectedSpace X] [∀ i, SimplyConnectedSpace ↥(U ∩ V i)] :
    SimplyConnectedSpace ↥U ∧ ∀ i, SimplyConnectedSpace ↥(V i) := by
  classical
  have hFintype : Fintype ι := Fintype.ofFinite ι
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let V' : Fin (Fintype.card ι) → Set X := fun i => V (e.symm i)
  have hunion : (⋃ i : Fin (Fintype.card ι), V' i) = ⋃ i : ι, V i := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_iUnion.mpr ⟨e.symm i, hxi⟩
    · intro hx
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_iUnion.mpr ⟨e i, by simpa [V'] using hxi⟩
  have hdisj' : Pairwise fun i j : Fin (Fintype.card ι) => Disjoint (V' i) (V' j) :=
    fun i j hij => hdisj fun h => hij (e.symm.injective h)
  have hpc' : ∀ i : Fin (Fintype.card ι), PathConnectedSpace ↥(V' i) :=
    fun i => inferInstanceAs (PathConnectedSpace ↥(V (e.symm i)))
  have hscI' : ∀ i : Fin (Fintype.card ι), SimplyConnectedSpace ↥(U ∩ V' i) :=
    fun i => inferInstanceAs (SimplyConnectedSpace ↥(U ∩ V (e.symm i)))
  have hres := simplyConnectedSpace_coverMembers_fin (Fintype.card ι) X U V' hU
    (fun i => hV _) (by rw [hunion]; exact hcover) hdisj' inferInstance hpc'
    inferInstance hscI'
  refine ⟨hres.1, fun i => ?_⟩
  have h := hres.2 (e i)
  rwa [show V' (e i) = V i from by simp [V', e]] at h

theorem simplyConnectedSpace_coverMembers_of_two_disjoint_open
    {X : Type u} [TopologicalSpace X] (U V₀ V₁ : Set X)
    (hU : IsOpen U) (hV₀ : IsOpen V₀) (hV₁ : IsOpen V₁)
    (hcover : U ∪ (V₀ ∪ V₁) = univ) (hdisj : Disjoint V₀ V₁)
    [PathConnectedSpace ↥U] [PathConnectedSpace ↥V₀] [PathConnectedSpace ↥V₁]
    [SimplyConnectedSpace X] [SimplyConnectedSpace ↥(U ∩ V₀)] [SimplyConnectedSpace ↥(U ∩ V₁)] :
    SimplyConnectedSpace ↥U ∧ SimplyConnectedSpace ↥V₀ ∧ SimplyConnectedSpace ↥V₁ := by
  let W : Bool → Set X := fun i => bif i then V₁ else V₀
  have hWopen : ∀ i, IsOpen (W i) := by
    intro i
    cases i
    · simpa [W] using hV₀
    · simpa [W] using hV₁
  have hW : (⋃ i : Bool, W i) = V₀ ∪ V₁ := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      cases i
      · exact Or.inl (by simpa [W] using hi)
      · exact Or.inr (by simpa [W] using hi)
    · intro hx
      rcases hx with h | h
      · exact Set.mem_iUnion.mpr ⟨false, by simpa [W] using h⟩
      · exact Set.mem_iUnion.mpr ⟨true, by simpa [W] using h⟩
  have hcoverW : U ∪ ⋃ i : Bool, W i = univ := by
    rw [hW]
    exact hcover
  have hdisjW : Pairwise fun i j : Bool => Disjoint (W i) (W j) := by
    intro i j hij
    cases i <;> cases j
    · exact absurd rfl hij
    · simpa [W] using hdisj
    · simpa [W] using hdisj.symm
    · exact absurd rfl hij
  have hpcW : ∀ i : Bool, PathConnectedSpace ↥(W i) := by
    intro i
    cases i
    · simpa [W] using inferInstanceAs (PathConnectedSpace ↥V₀)
    · simpa [W] using inferInstanceAs (PathConnectedSpace ↥V₁)
  have hscIW : ∀ i : Bool, SimplyConnectedSpace ↥(U ∩ W i) := by
    intro i
    cases i
    · simpa [W] using inferInstanceAs (SimplyConnectedSpace ↥(U ∩ V₀))
    · simpa [W] using inferInstanceAs (SimplyConnectedSpace ↥(U ∩ V₁))
  obtain ⟨h1, h2⟩ := @simplyConnectedSpace_coverMembers_of_pairwiseDisjoint_open_cover
    X _ Bool _ U W hU hWopen hcoverW hdisjW inferInstance hpcW inferInstance hscIW
  exact ⟨h1, h2 false, h2 true⟩

end DifferentialGeometry.Topology.VanKampen
