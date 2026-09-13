import DifferentialGeometry.Topology.VanKampen.SimplyConnectedUnion

set_option autoImplicit false

noncomputable section

open Set

universe u v

namespace DifferentialGeometry.Topology.VanKampen

private noncomputable def subtypePreimageHomeomorph {X : Type u} [TopologicalSpace X]
    {A B : Set X} (hAB : A ⊆ B) : {x : ↥B // x.1 ∈ A} ≃ₜ ↥A where
  toFun x := ⟨x.1.1, x.2⟩
  invFun a := ⟨⟨a.1, hAB a.2⟩, a.2⟩
  left_inv := fun _ => Subtype.ext (Subtype.ext rfl)
  right_inv := fun _ => Subtype.ext rfl
  continuous_toFun :=
    Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _
  continuous_invFun :=
    Continuous.subtype_mk (Continuous.subtype_mk continuous_subtype_val _) _

private theorem simplyConnectedSpace_of_homeomorph {A B : Type u} [TopologicalSpace A]
    [TopologicalSpace B] (e : A ≃ₜ B) (hA : SimplyConnectedSpace A) :
    SimplyConnectedSpace B :=
  (e.toHomotopyEquiv.simplyConnectedSpace_iff).mp hA

private theorem pathConnectedSpace_of_homeomorph {A B : Type u} [TopologicalSpace A]
    [TopologicalSpace B] (e : A ≃ₜ B) (hA : PathConnectedSpace A) : PathConnectedSpace B := by
  have h : IsPathConnected (Set.univ : Set A) := pathConnectedSpace_iff_univ.mp hA
  have h2 : IsPathConnected (Set.univ : Set B) := by
    have h3 := h.image e.continuous
    rwa [Set.image_univ, e.surjective.range_eq] at h3
  exact pathConnectedSpace_iff_univ.mpr h2

private theorem simplyConnectedSpace_of_subtype_preimage {X : Type u} [TopologicalSpace X]
    {A B : Set X} (hAB : A ⊆ B) (hA : SimplyConnectedSpace ↥A) :
    SimplyConnectedSpace {x : ↥B // x.1 ∈ A} :=
  simplyConnectedSpace_of_homeomorph (subtypePreimageHomeomorph hAB).symm hA

private theorem pathConnectedSpace_of_subtype_preimage {X : Type u} [TopologicalSpace X]
    {A B : Set X} (hAB : A ⊆ B) (hA : PathConnectedSpace ↥A) :
    PathConnectedSpace {x : ↥B // x.1 ∈ A} :=
  pathConnectedSpace_of_homeomorph (subtypePreimageHomeomorph hAB).symm hA

private theorem fin_castSucc_ne_last {n : ℕ} (i : Fin n) : i.castSucc ≠ Fin.last n := by
  intro h
  have hval := congrArg Fin.val h
  simp at hval
  omega

private theorem iUnion_fin_succ_eq {X : Type u} {n : ℕ} (V : Fin (n + 1) → Set X) :
    (⋃ i : Fin (n + 1), V i) =
      (⋃ i : Fin n, V i.castSucc) ∪ V (Fin.last n) :=
  Set.iUnion_fin_add_one_eq_iUnion_castSucc V

theorem simplyConnectedSpace_of_injective_fundamentalGroup {K : Type u} {X : Type u}
    [TopologicalSpace K] [TopologicalSpace X] [PathConnectedSpace K] (f : C(K, X)) (x₀ : K)
    [SimplyConnectedSpace X] (hf : Function.Injective (FundamentalGroup.map f x₀)) :
    SimplyConnectedSpace K :=
  (simplyConnectedSpace_iff_fundamentalGroup_subsingleton K x₀).2
    ⟨fun _ _ => hf (Subsingleton.elim _ _)⟩

theorem simplyConnectedSpace_of_open_cover_of_pairwise_disjoint
    {X : Type u} [TopologicalSpace X] {n : ℕ}
    (U : Set X) (V : Fin n → Set X) (hU : IsOpen U) (hV : ∀ i, IsOpen (V i))
    (hcover : U ∪ ⋃ i, V i = univ)
    (hdisj : Pairwise fun i j => Disjoint (V i) (V j))
    [SimplyConnectedSpace ↥U] [∀ i, SimplyConnectedSpace ↥(V i)]
    [∀ i, SimplyConnectedSpace ↥(U ∩ V i)] :
    SimplyConnectedSpace X := by
  classical
  have key : ∀ (n : ℕ) (U : Set X) (V : Fin n → Set X),
      IsOpen U → (∀ i, IsOpen (V i)) → Pairwise (fun i j => Disjoint (V i) (V j)) →
      SimplyConnectedSpace ↥U → (∀ i, SimplyConnectedSpace ↥(V i)) →
      (∀ i, SimplyConnectedSpace ↥(U ∩ V i)) →
      SimplyConnectedSpace ↥(U ∪ ⋃ i, V i) := by
    intro n
    induction n with
    | zero =>
      intro U V _ _ _ hUsc _ _
      have h : (U ∪ ⋃ i : Fin 0, V i) = U := by simp
      rw [h]
      exact hUsc
    | succ n ih =>
      intro U V hU hV hdisj hUsc hVsc hUscI
      let W : Fin n → Set X := fun i => V i.castSucc
      let Y : Set X := V (Fin.last n)
      have hWopen : ∀ i, IsOpen (W i) := fun i => hV i.castSucc
      have hWsc : ∀ i, SimplyConnectedSpace ↥(W i) := fun i => hVsc i.castSucc
      have hWdisj : Pairwise fun i j => Disjoint (W i) (W j) :=
        fun i j hij => hdisj fun h => hij (Fin.castSucc_inj.mp h)
      have hWscI : ∀ i, SimplyConnectedSpace ↥(U ∩ W i) := fun i => hUscI i.castSucc
      have hscUY : SimplyConnectedSpace ↥(U ∩ Y) := hUscI (Fin.last n)
      have ihapp : SimplyConnectedSpace ↥(U ∪ ⋃ i : Fin n, W i) :=
        ih U W hU hWopen hWdisj hUsc hWsc hWscI
      have hdisjY : ∀ i : Fin n, Disjoint (W i) Y := fun i =>
        hdisj (fin_castSucc_ne_last i)
      rw [iUnion_fin_succ_eq V, ← Set.union_assoc]
      have hUo : IsOpen (U ∪ ⋃ i : Fin n, W i) :=
        hU.union (isOpen_iUnion fun i => hWopen i)
      have hYo : IsOpen Y := hV (Fin.last n)
      have hinter : (U ∪ ⋃ i : Fin n, W i) ∩ Y = U ∩ Y := by
        ext x
        constructor
        · rintro ⟨hx, hxY⟩
          rcases hx with hx | hx
          · exact ⟨hx, hxY⟩
          · obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
            have hne : (W i ∩ Y) = ∅ := Set.disjoint_iff_inter_eq_empty.mp (hdisjY i)
            exact absurd (show x ∈ W i ∩ Y from ⟨hxi, hxY⟩) (by rw [hne]; exact not_false)
        · rintro ⟨hx, hxY⟩
          exact ⟨Or.inl hx, hxY⟩
      obtain ⟨z⟩ := (inferInstance : Nonempty ↥(U ∩ Y))
      let x₀ : ↥((U ∪ ⋃ i : Fin n, W i) ∪ Y) := ⟨z.1, Or.inl (Or.inl z.2.1)⟩
      have hx₀ : x₀ ∈ (Subtype.val ⁻¹' (U ∪ ⋃ i : Fin n, W i) :
            Set ↥((U ∪ ⋃ i : Fin n, W i) ∪ Y)) ∩
          (Subtype.val ⁻¹' Y : Set ↥((U ∪ ⋃ i : Fin n, W i) ∪ Y)) :=
        ⟨Or.inl z.2.1, z.2.2⟩
      have hscA : SimplyConnectedSpace
          ↥(Subtype.val ⁻¹' (U ∪ ⋃ i : Fin n, W i) :
            Set ↥((U ∪ ⋃ i : Fin n, W i) ∪ Y)) :=
        simplyConnectedSpace_of_subtype_preimage Set.subset_union_left ihapp
      have hscY : SimplyConnectedSpace
          ↥(Subtype.val ⁻¹' Y : Set ↥((U ∪ ⋃ i : Fin n, W i) ∪ Y)) :=
        simplyConnectedSpace_of_subtype_preimage Set.subset_union_right (hVsc (Fin.last n))
      have hpc : PathConnectedSpace
          ↥((Subtype.val ⁻¹' (U ∪ ⋃ i : Fin n, W i) :
              Set ↥((U ∪ ⋃ i : Fin n, W i) ∪ Y)) ∩
            (Subtype.val ⁻¹' Y : Set ↥((U ∪ ⋃ i : Fin n, W i) ∪ Y))) := by
        have hset : ((Subtype.val ⁻¹' (U ∪ ⋃ i : Fin n, W i) :
              Set ↥((U ∪ ⋃ i : Fin n, W i) ∪ Y)) ∩
            (Subtype.val ⁻¹' Y : Set ↥((U ∪ ⋃ i : Fin n, W i) ∪ Y))) =
            (Subtype.val ⁻¹' (U ∩ Y) : Set ↥((U ∪ ⋃ i : Fin n, W i) ∪ Y)) := by
          rw [← Set.preimage_inter, hinter]
        rw [hset]
        exact pathConnectedSpace_of_subtype_preimage
          (A := U ∩ Y) (B := (U ∪ ⋃ i : Fin n, W i) ∪ Y)
          (Set.inter_subset_right.trans Set.subset_union_right) inferInstance
      exact simplyConnectedSpace_of_open_cover
        (Subtype.val ⁻¹' (U ∪ ⋃ i : Fin n, W i) :
          Set ↥((U ∪ ⋃ i : Fin n, W i) ∪ Y))
        (Subtype.val ⁻¹' Y : Set ↥((U ∪ ⋃ i : Fin n, W i) ∪ Y))
        (hUo.preimage continuous_subtype_val) (hYo.preimage continuous_subtype_val)
        (by
          rw [← Set.preimage_union]
          exact Set.eq_univ_of_forall fun x => x.2)
        x₀ hx₀
  have hfin := key n U V hU hV hdisj inferInstance inferInstance inferInstance
  rw [hcover] at hfin
  exact (Homeomorph.Set.univ X).toHomotopyEquiv.simplyConnectedSpace_iff.mp hfin

theorem simplyConnectedSpace_of_open_cover_of_pairwise_disjoint_of_fintype
    {X : Type u} [TopologicalSpace X] {ι : Type v} [Finite ι]
    (U : Set X) (V : ι → Set X) (hU : IsOpen U) (hV : ∀ i, IsOpen (V i))
    (hcover : U ∪ ⋃ i, V i = univ)
    (hdisj : Pairwise fun i j => Disjoint (V i) (V j))
    [SimplyConnectedSpace ↥U] [∀ i, SimplyConnectedSpace ↥(V i)]
    [∀ i, SimplyConnectedSpace ↥(U ∩ V i)] :
    SimplyConnectedSpace X := by
  classical
  have hFintype : Fintype ι := Fintype.ofFinite ι
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let V' : Fin (Fintype.card ι) → Set X := fun i => V (e.symm i)
  have hV' : ∀ i, IsOpen (V' i) := fun i => hV _
  have hdisj' : Pairwise fun i j => Disjoint (V' i) (V' j) :=
    fun i j hij => hdisj fun h => hij (e.symm.injective h)
  have hVsc : ∀ i : Fin (Fintype.card ι), SimplyConnectedSpace ↥(V' i) :=
    fun i => inferInstanceAs (SimplyConnectedSpace ↥(V (e.symm i)))
  have hUsc : ∀ i : Fin (Fintype.card ι), SimplyConnectedSpace ↥(U ∩ V' i) :=
    fun i => inferInstanceAs (SimplyConnectedSpace ↥(U ∩ V (e.symm i)))
  have hunion : (⋃ i : Fin (Fintype.card ι), V' i) = ⋃ i : ι, V i := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_iUnion.mpr ⟨e.symm i, hxi⟩
    · intro hx
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_iUnion.mpr ⟨e i, by simpa [V'] using hxi⟩
  exact simplyConnectedSpace_of_open_cover_of_pairwise_disjoint (X := X) U V' hU hV'
    (by rw [hunion]; exact hcover) hdisj'

end DifferentialGeometry.Topology.VanKampen
