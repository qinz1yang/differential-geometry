import DifferentialGeometry.Topology.VanKampen.FundamentalGroupUnion
import DifferentialGeometry.Topology.VanKampen.SimplyConnectedStarCover
import DifferentialGeometry.Topology.FundamentalGroup.HomotopyEquiv
set_option autoImplicit false
noncomputable section
open Set DifferentialGeometry.Topology
open DifferentialGeometry.Topology.VanKampen
universe u v
namespace GC.Topology

open private subtypePreimageHomeomorph pathConnectedSpace_of_subtype_preimage
  simplyConnectedSpace_of_subtype_preimage
  from DifferentialGeometry.Topology.VanKampen.SimplyConnectedStarCover

theorem pathConnectedSpace_union {X : Type u} [TopologicalSpace X]
    (U V : Set X) [PathConnectedSpace U] [PathConnectedSpace V]
    (h : (U ∩ V).Nonempty) : PathConnectedSpace ↥(U ∪ V) :=
  isPathConnected_iff_pathConnectedSpace.mp
    ((isPathConnected_iff_pathConnectedSpace.mpr inferInstance).union
      (isPathConnected_iff_pathConnectedSpace.mpr inferInstance) h)

theorem union_fundamentalGroup_equiv {X : Type u} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    [PathConnectedSpace U] [SimplyConnectedSpace V] [SimplyConnectedSpace ↥(U ∩ V)]
    (x : U) (y : ↥(U ∪ V)) :
    Nonempty (FundamentalGroup ↥(U ∪ V) y ≃* FundamentalGroup U x) := by
  let z : ↥(U ∩ V) := Classical.choice inferInstance
  let := pathConnectedSpace_union U V ⟨z.val, z.property⟩
  let A : Set ↥(U ∪ V) := Subtype.val ⁻¹' U
  let B : Set ↥(U ∪ V) := Subtype.val ⁻¹' V
  let : PathConnectedSpace A := pathConnectedSpace_of_subtype_preimage
    (show U ⊆ U ∪ V from subset_union_left) inferInstance
  let : SimplyConnectedSpace B := simplyConnectedSpace_of_subtype_preimage
    (show V ⊆ U ∪ V from subset_union_right) inferInstance
  let : SimplyConnectedSpace ↥(A ∩ B) := by
    change SimplyConnectedSpace (Subtype.val ⁻¹' U ∩ Subtype.val ⁻¹' V : Set ↥(U ∪ V))
    rw [← preimage_inter]
    exact simplyConnectedSpace_of_subtype_preimage
      (show U ∩ V ⊆ U ∪ V from inter_subset_left.trans subset_union_left)
      (inferInstance : SimplyConnectedSpace ↥(U ∩ V))
  let z₀ : ↥(U ∪ V) := ⟨z.val, Or.inl z.property.1⟩
  have hz₀ : z₀ ∈ A ∩ B := z.property
  let e := fundamentalGroupEquivOfOpenCover A B
    (hU.preimage continuous_subtype_val) (hV.preimage continuous_subtype_val)
    (by ext a; exact ⟨fun _ => trivial, fun _ => a.property⟩) z₀ hz₀
  let f := subtypePreimageHomeomorph (show U ⊆ U ∪ V from subset_union_left)
  let a := fundamentalGroupMulEquivOfHomotopyEquiv f.toHomotopyEquiv
    (leftBasepoint A z₀ hz₀.1) (f (leftBasepoint A z₀ hz₀.1)) rfl
  exact ⟨(FundamentalGroup.fundamentalGroupMulEquivOfPathConnected y z₀).trans
    (e.trans (a.trans (FundamentalGroup.fundamentalGroupMulEquivOfPathConnected _ x)))⟩

theorem star_union_fundamentalGroup_equiv {X : Type u} [TopologicalSpace X] :
    ∀ (n : ℕ) (U : Set X) (V : Fin n → Set X),
      IsOpen U → (∀ i, IsOpen (V i)) →
      Pairwise (fun i j => Disjoint (V i) (V j)) →
      PathConnectedSpace U → (∀ i, SimplyConnectedSpace (V i)) →
      (∀ i, SimplyConnectedSpace ↥(U ∩ V i)) →
      PathConnectedSpace ↥(U ∪ ⋃ i, V i) ∧
        ∀ (x : U) (y : ↥(U ∪ ⋃ i, V i)),
          Nonempty (FundamentalGroup ↥(U ∪ ⋃ i, V i) y ≃* FundamentalGroup U x) := by
  intro n
  induction n with
  | zero =>
      intro U V _ _ _ hUconn _ _
      let := hUconn
      have heq : (U ∪ ⋃ i : Fin 0, V i) = U := by simp
      rw [heq]
      exact ⟨hUconn, fun x y => ⟨FundamentalGroup.fundamentalGroupMulEquivOfPathConnected y x⟩⟩
  | succ n ih =>
      intro U V hU hV hdisj hUconn hVsc hInt
      let W : Fin n → Set X := fun i => V i.castSucc
      let A := U ∪ ⋃ i : Fin n, W i
      let Y := V (Fin.last n)
      obtain ⟨hAconn, hAgroup⟩ := ih U W hU (fun i => hV i.castSucc)
        (fun i j hij => hdisj fun h => hij (Fin.castSucc_inj.mp h)) hUconn
        (fun i => hVsc i.castSucc) (fun i => hInt i.castSucc)
      let := hAconn
      let : SimplyConnectedSpace Y := hVsc (Fin.last n)
      have hinter : A ∩ Y = U ∩ Y := by
        ext x
        constructor
        · rintro ⟨hx, hxY⟩
          rcases hx with hx | hx
          · exact ⟨hx, hxY⟩
          · obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
            have hne : i.castSucc ≠ Fin.last n := by
              intro heq
              have hh := congrArg Fin.val heq
              simp only [Fin.val_castSucc, Fin.val_last] at hh
              omega
            exact (disjoint_left.mp (hdisj hne) hxi hxY).elim
        · rintro ⟨hx, hxY⟩
          exact ⟨Or.inl hx, hxY⟩
      let : SimplyConnectedSpace ↥(A ∩ Y) := by
        rw [hinter]
        exact hInt (Fin.last n)
      have hAo : IsOpen A := hU.union (isOpen_iUnion fun i => hV i.castSucc)
      let z : ↥(A ∩ Y) := Classical.choice inferInstance
      have hAYconn := pathConnectedSpace_union A Y ⟨z.val, z.property⟩
      rw [iUnion_fin_add_one_eq_iUnion_castSucc V, ← union_assoc]
      refine ⟨hAYconn, ?_⟩
      intro x y
      let a : A := ⟨x.val, Or.inl x.property⟩
      obtain ⟨e⟩ := union_fundamentalGroup_equiv A Y hAo (hV (Fin.last n)) a y
      obtain ⟨f⟩ := hAgroup x a
      exact ⟨e.trans f⟩

theorem star_cover_fundamentalGroup_equiv {X : Type u} [TopologicalSpace X]
    {ι : Type v} [Finite ι] (U : Set X) (V : ι → Set X)
    (hU : IsOpen U) (hV : ∀ i, IsOpen (V i)) (hcover : U ∪ ⋃ i, V i = univ)
    (hdisj : Pairwise fun i j => Disjoint (V i) (V j))
    [PathConnectedSpace U] [∀ i, SimplyConnectedSpace (V i)]
    [∀ i, SimplyConnectedSpace ↥(U ∩ V i)] (x : U) (y : X) :
    Nonempty (FundamentalGroup X y ≃* FundamentalGroup U x) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let e := Fintype.equivFin ι
  let V' := fun i => V (e.symm i)
  have hunion : (⋃ i, V' i) = ⋃ i, V i := by
    ext z
    simp only [mem_iUnion]
    exact ⟨fun ⟨i, hi⟩ => ⟨e.symm i, hi⟩,
      fun ⟨i, hi⟩ => ⟨e i, by simpa [V'] using hi⟩⟩
  have hc : U ∪ ⋃ i, V' i = univ := by rw [hunion]; exact hcover
  obtain ⟨_, hg⟩ := star_union_fundamentalGroup_equiv (Fintype.card ι) U V' hU
    (fun i => hV _) (fun i j hij => hdisj fun h => hij (e.symm.injective h))
    inferInstance (fun i => inferInstanceAs (SimplyConnectedSpace (V (e.symm i))))
    (fun i => inferInstanceAs (SimplyConnectedSpace ↥(U ∩ V (e.symm i))))
  let D : ↥(U ∪ ⋃ i, V' i) ≃ₜ X := (Homeomorph.setCongr hc).trans (Homeomorph.Set.univ X)
  obtain ⟨g⟩ := hg x (D.symm y)
  exact ⟨(fundamentalGroupMulEquivOfHomotopyEquiv D.symm.toHomotopyEquiv y (D.symm y) rfl).trans g⟩

end GC.Topology
