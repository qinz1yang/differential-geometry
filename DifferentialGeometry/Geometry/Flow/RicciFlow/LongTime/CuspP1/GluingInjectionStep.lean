import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.GluingInjectionCore

/-!
# CP1-C: general-loop amalgam / HNN steps for piece inclusions

Copies of `InjInto.union_of_amalgam` / `InjInto.union_of_hnn` (`MultiSeamInjective.lean`)
whose conclusion is `IncInj_CPC` (inclusion of a piece into the union is `π₁`-injective at every
basepoint) instead of injectivity of torus maps.
-/

set_option autoImplicit false

noncomputable section
open CategoryTheory DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open GC.GraphManifold DifferentialGeometry.Topology.VanKampen
open scoped Topology ContinuousMap

universe u

namespace GC.LongTime.CuspP1
open GC.Seifert

section Steps
variable {M : Type u} [TopologicalSpace M]

theorem incl_iff_CPC (X S : Set M) (h : S ⊆ X) (y : S) :
    Function.Injective (FundamentalGroup.map (inclusionMap h) y) ↔
      Function.Injective (FundamentalGroup.map
        (subsetToAmbient (Subtype.val ⁻¹' S : Set X)) ((preimageValHomeo X S h).symm y)) :=
  injective_iff_homeo2_CPC (preimageValHomeo X S h).symm (Homeomorph.refl _) (inclusionMap h)
    (subsetToAmbient (Subtype.val ⁻¹' S : Set X)) (fun _ => rfl) y

theorem IncInj.union_of_amalgam_CPC {A V : Set M} (hA : IsOpen A) (hV : IsOpen V)
    (hApc : IsPathConnected A) (hVpc : IsPathConnected V) (hAVpc : IsPathConnected (A ∩ V))
    (f : C(Torus, M)) (hf : ∀ t, f t ∈ A ∩ V) (t₀ : Torus)
    (hsurj : Function.Surjective (FundamentalGroup.map (toSubset f (A ∩ V) hf) t₀))
    (hfA : InjInto A f) (hfV : InjInto V f) :
    IncInj_CPC (Set.subset_union_left : A ⊆ A ∪ V) ∧
      IncInj_CPC (Set.subset_union_right : V ⊆ A ∪ V) := by
  have hAX : A ⊆ A ∪ V := Set.subset_union_left
  have hVX : V ⊆ A ∪ V := Set.subset_union_right
  have hIX : A ∩ V ⊆ A ∪ V := Set.inter_subset_left.trans hAX
  have hU'o : IsOpen (Subtype.val ⁻¹' A : Set (A ∪ V : Set M)) :=
    hA.preimage continuous_subtype_val
  have hV'o : IsOpen (Subtype.val ⁻¹' V : Set (A ∪ V : Set M)) :=
    hV.preimage continuous_subtype_val
  have hcov : (Subtype.val ⁻¹' A : Set (A ∪ V : Set M)) ∪ Subtype.val ⁻¹' V = Set.univ :=
    Set.eq_univ_of_forall fun y => y.2
  have := pathConnectedSpace_preimage hApc hAX
  have := pathConnectedSpace_preimage hVpc hVX
  have hI : PathConnectedSpace ↑((Subtype.val ⁻¹' A : Set (A ∪ V : Set M)) ∩
      Subtype.val ⁻¹' V) := pathConnectedSpace_preimage hAVpc hIX
  let F := liftTo (A ∪ V) (A ∩ V) hIX f hf
  have hFs : Function.Surjective (FundamentalGroup.map F t₀) :=
    surjective_liftTo (A ∪ V) (A ∩ V) hIX f hf t₀ hsurj
  have hFU : Function.Injective (FundamentalGroup.map ((interToLeft
      (Subtype.val ⁻¹' A : Set (A ∪ V : Set M)) (Subtype.val ⁻¹' V)).comp F) t₀) :=
    (injective_liftTo_iff (A ∪ V) A hAX f (fun t => (hf t).1) t₀).mpr (hfA.2 t₀)
  have hFV : Function.Injective (FundamentalGroup.map ((interToRight
      (Subtype.val ⁻¹' A : Set (A ∪ V : Set M)) (Subtype.val ⁻¹' V)).comp F) t₀) :=
    (injective_liftTo_iff (A ∪ V) V hVX f (fun t => (hf t).2) t₀).mpr (hfV.2 t₀)
  have hl := injective_fundamentalGroup_map_of_comp F _ t₀ hFs hFU
  have hr := injective_fundamentalGroup_map_of_comp F _ t₀ hFs hFV
  have hleft := injective_fundamentalGroup_map_left _ _ hU'o hV'o hcov (F t₀) hl hr
  have hright := injective_fundamentalGroup_map_right _ _ hU'o hV'o hcov (F t₀) hl hr
  constructor
  · intro y
    refine (incl_iff_CPC (A ∪ V) A hAX y).mpr ?_
    exact (GC.Topology.injective_fundamentalGroup_map_iff
      (subsetToAmbient (Subtype.val ⁻¹' A : Set (A ∪ V : Set M))) _ _).mp hleft
  · intro y
    refine (incl_iff_CPC (A ∪ V) V hVX y).mpr ?_
    exact (GC.Topology.injective_fundamentalGroup_map_iff
      (subsetToAmbient (Subtype.val ⁻¹' V : Set (A ∪ V : Set M))) _ _).mp hright

theorem IncInj.union_of_hnn_CPC {A V N₀ N₁ : Set M} (hA : IsOpen A) (hV : IsOpen V)
    (hApc : IsPathConnected A) (hVpc : IsPathConnected V) (hN : A ∩ V = N₀ ∪ N₁)
    (hN₀ : IsOpen N₀) (hN₁ : IsOpen N₁) (hdisj : Disjoint N₀ N₁)
    (hN₀pc : IsPathConnected N₀) (hN₁pc : IsPathConnected N₁) (f₀ f₁ : C(Torus, M))
    (hf₀ : ∀ t, f₀ t ∈ A ∩ V) (hf₁ : ∀ t, f₁ t ∈ A ∩ V) (t₀ : Torus) (hf₀N : f₀ t₀ ∈ N₀)
    (hf₁N : f₁ t₀ ∈ N₁)
    (hb₀ : Function.Bijective (FundamentalGroup.map (toSubset f₀ (A ∩ V) hf₀) t₀))
    (hb₀V : Function.Bijective (FundamentalGroup.map (toSubset f₀ V (fun t => (hf₀ t).2)) t₀))
    (hs₁ : Function.Surjective (FundamentalGroup.map (toSubset f₁ (A ∩ V) hf₁) t₀))
    (hi₁V : InjInto V f₁) (hi₀A : InjInto A f₀) (hi₁A : InjInto A f₁) :
    IncInj_CPC (Set.subset_union_left : A ⊆ A ∪ V) := by
  have hAX : A ⊆ A ∪ V := Set.subset_union_left
  have hVX : V ⊆ A ∪ V := Set.subset_union_right
  have hIX : A ∩ V ⊆ A ∪ V := Set.inter_subset_left.trans hAX
  let F₀ := liftTo (A ∪ V) (A ∩ V) hIX f₀ hf₀
  let F₁ := liftTo (A ∪ V) (A ∩ V) hIX f₁ hf₁
  have hF₀ := bijective_liftTo (A ∪ V) (A ∩ V) hIX f₀ hf₀ t₀ hb₀
  have hF₁ := surjective_liftTo (A ∪ V) (A ∩ V) hIX f₁ hf₁ t₀ hs₁
  have hsplit : ∀ y : M, y ∈ A ∩ V → (y ∈ N₀ ↔ y ∉ N₁) := fun y hy => by
    rw [hN] at hy
    rcases hy with h0 | h1
    · exact ⟨fun _ h1 => hdisj.le_bot ⟨h0, h1⟩, fun _ => h0⟩
    · exact ⟨fun h0 => (hdisj.le_bot ⟨h0, h1⟩).elim, fun h => (h h1).elim⟩
  let K : TwoComponentCover (Subtype.val ⁻¹' A : Set (A ∪ V : Set M)) (Subtype.val ⁻¹' V) :=
    { left_connected := pathConnectedSpace_preimage hApc hAX
      right_connected := pathConnectedSpace_preimage hVpc hVX
      isOpen_left := hA.preimage continuous_subtype_val
      isOpen_right := hV.preimage continuous_subtype_val
      cover := Set.eq_univ_of_forall fun y => y.2
      base := F₀ t₀
      far := F₁ t₀
      not_joined := not_joined_of_separated
        ⟨fun y : ↑((Subtype.val ⁻¹' A : Set (A ∪ V : Set M)) ∩ Subtype.val ⁻¹' V) => y.1.1,
          continuous_subtype_val.comp continuous_subtype_val⟩ hN₀ hN₁ hdisj
        (fun y => hN ▸ y.2) hf₀N hf₁N
      joined := fun a => by
        have ha : (a : M) ∈ A ∩ V := a.2
        have hsub : ∀ N : Set M, N ⊆ A ∩ V → (Subtype.val ⁻¹' N : Set (A ∪ V : Set M)) ⊆
            (Subtype.val ⁻¹' A : Set (A ∪ V : Set M)) ∩ Subtype.val ⁻¹' V :=
          fun N hNs y hy => hNs hy
        have hN₀s : N₀ ⊆ A ∩ V := hN ▸ Set.subset_union_left
        have hN₁s : N₁ ⊆ A ∩ V := hN ▸ Set.subset_union_right
        by_cases h0 : (a : M) ∈ N₀
        · exact Or.inl ((((hN₀pc.preimage_coe (hN₀s.trans hIX)).joinedIn _ hf₀N _ h0).mono
            (hsub N₀ hN₀s)).joined_subtype)
        · have h1 : (a : M) ∈ N₁ := by
            by_contra h1
            exact h0 ((hsplit _ ha).mpr h1)
          exact Or.inr ((((hN₁pc.preimage_coe (hN₁s.trans hIX)).joinedIn _ hf₁N _ h1).mono
            (hsub N₁ hN₁s)).joined_subtype)
      right_bijective := bijective_fundamentalGroup_map_of_comp F₀ _ t₀ hF₀
        (bijective_liftTo (A ∪ V) V hVX f₀ (fun t => (hf₀ t).2) t₀ hb₀V)
      left_injective := injective_fundamentalGroup_map_of_comp F₀ _ t₀ hF₀.2
        ((injective_liftTo_iff (A ∪ V) A hAX f₀ (fun t => (hf₀ t).1) t₀).mpr (hi₀A.2 t₀))
      left_injective_far := injective_fundamentalGroup_map_of_comp F₁ _ t₀ hF₁
        ((injective_liftTo_iff (A ∪ V) A hAX f₁ (fun t => (hf₁ t).1) t₀).mpr (hi₁A.2 t₀))
      right_injective_far := injective_fundamentalGroup_map_of_comp F₁ _ t₀ hF₁
        ((injective_liftTo_iff (A ∪ V) V hVX f₁ (fun t => (hf₁ t).2) t₀).mpr (hi₁V.2 t₀)) }
  have hleft := K.injective_fundamentalGroup_map_left
  have := K.left_connected
  intro y
  refine (incl_iff_CPC (A ∪ V) A hAX y).mpr ?_
  exact (GC.Topology.injective_fundamentalGroup_map_iff
    (subsetToAmbient (Subtype.val ⁻¹' A : Set (A ∪ V : Set M))) _ _).mp hleft

end Steps

end GC.LongTime.CuspP1
