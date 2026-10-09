import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MultiSeamInjective
import DifferentialGeometry.Topology.Algebra.Group.FreeProduct.GraphOfGroupsIndecomposable
import DifferentialGeometry.Topology.Algebra.Group.FreeProduct.Commutative

/-!
# Freely indecomposable regions glued along tori

Chapter 5 plan P4, tier T2 (gluing steps). `IndecomposableNoncyclic H` is "freely indecomposable
and not cyclic", the vertex condition of the graph-of-groups theorem of lane GG. A subset `S` of
a space is `RegionFI` when π₁ of `S` satisfies it at every point. The condition moves along
π₁-bijective maps, from a set to a relatively clopen subset and back
(`RegionFI.of_isClopen`, `regionFI_of_forall_isClopen`), and between the points of a
path-connected set.

The torus group `ℤ × ℤ` is commutative, nontrivial and not cyclic
(`indecomposableNoncyclic_torus`, `nontrivial_torus`). Gluing two `RegionFI` open sets along an
intersection carried by a torus that is π₁-injective on both sides gives a `RegionFI` union: by
van Kampen (`fundamentalGroupEquivAmalgamatedProduct`) π₁ of the union is the amalgam of the two
groups over the nontrivial intersection group, freely indecomposable by
`freelyIndecomposable_pushout` (`RegionFI.union_of_amalgam`). For an intersection with two
torus components the union is an HNN extension (`TwoComponentCover.equivExtension`, K09) and
`freelyIndecomposable_hnnExtension` applies (`RegionFI.union_of_hnn`). The hypotheses are those of
K09c's `InjInto.union_of_amalgam` and `InjInto.union_of_hnn`.
-/

set_option autoImplicit false

noncomputable section
open CategoryTheory DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open GC.GraphManifold DifferentialGeometry.Topology.VanKampen
open GC.Topology (torusFundamentalGroup)
open scoped Topology ContinuousMap

universe u

namespace GC.Seifert

section Groups

def IndecomposableNoncyclic (H : Type*) [Group H] : Prop :=
  GC.Group.FreelyIndecomposable H ∧ ¬ IsCyclic H

theorem IndecomposableNoncyclic.of_mulEquiv {G H : Type*} [Group G] [Group H]
    (h : IndecomposableNoncyclic G) (e : G ≃* H) : IndecomposableNoncyclic H :=
  ⟨h.1.of_mulEquiv e, fun hc => h.2 (e.isCyclic.mpr hc)⟩

theorem not_isCyclic_of_injective {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Injective f) (hG : ¬ IsCyclic G) : ¬ IsCyclic H :=
  fun _ => hG (isCyclic_of_injective f hf)

theorem not_isCyclic_multiplicative_int_prod :
    ¬ IsCyclic (Multiplicative ℤ × Multiplicative ℤ) := by
  intro hc
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Multiplicative ℤ × Multiplicative ℤ)
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hg (Multiplicative.ofAdd 1, 1))
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hg (1, Multiplicative.ofAdd 1))
  have h1 : (g.1 ^ m).toAdd = (1 : ℤ) := congrArg (fun p => Multiplicative.toAdd p.1) hm
  have h3 : (g.1 ^ n).toAdd = (0 : ℤ) := congrArg (fun p => Multiplicative.toAdd p.1) hn
  have h4 : (g.2 ^ n).toAdd = (1 : ℤ) := congrArg (fun p => Multiplicative.toAdd p.2) hn
  rw [toAdd_zpow, smul_eq_mul] at h1 h3 h4
  rcases mul_eq_zero.mp h3 with h | h
  · rw [h, zero_mul] at h4
    exact zero_ne_one h4
  · rw [h, mul_zero] at h1
    exact zero_ne_one h1

theorem commute_torus (t : Torus) (a b : FundamentalGroup Torus t) : a * b = b * a := by
  let e := (FundamentalGroup.fundamentalGroupMulEquivOfPathConnected t (1, 1)).trans
    torusFundamentalGroup
  apply e.injective
  rw [map_mul, map_mul, mul_comm]

theorem indecomposableNoncyclic_torus (t : Torus) :
    IndecomposableNoncyclic (FundamentalGroup Torus t) := by
  let e := (FundamentalGroup.fundamentalGroupMulEquivOfPathConnected t (1, 1)).trans
    torusFundamentalGroup
  exact ⟨GC.Group.commutative_freelyIndecomposable _ (commute_torus t),
    fun hc => not_isCyclic_multiplicative_int_prod (e.isCyclic.mp hc)⟩

theorem nontrivial_torus (t : Torus) : Nontrivial (FundamentalGroup Torus t) := by
  let e := (FundamentalGroup.fundamentalGroupMulEquivOfPathConnected t (1, 1)).trans
    torusFundamentalGroup
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  apply not_isCyclic_multiplicative_int_prod
  have : Subsingleton (Multiplicative ℤ × Multiplicative ℤ) := e.symm.toEquiv.subsingleton
  infer_instance

end Groups

section Maps
variable {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]

theorem indecomposableNoncyclic_iff_of_bijective (f : C(Y, Z)) (y : Y)
    (hb : Function.Bijective (FundamentalGroup.map f y)) :
    IndecomposableNoncyclic (FundamentalGroup Y y) ↔
      IndecomposableNoncyclic (FundamentalGroup Z (f y)) :=
  ⟨fun h => h.of_mulEquiv (MulEquiv.ofBijective _ hb),
    fun h => h.of_mulEquiv (MulEquiv.ofBijective _ hb).symm⟩

theorem bijective_map_homeomorph (e : Y ≃ₜ Z) (y : Y) :
    Function.Bijective (FundamentalGroup.map (e : C(Y, Z)) y) :=
  bijective_fundamentalGroup_map_of_homotopyEquiv_leftInverse e.symm.toHomotopyEquiv
    (e : C(Y, Z)) e.symm_apply_apply y

theorem nontrivial_of_injective_comp {T : Type*} [TopologicalSpace T] (f : C(T, Y)) (g : C(Y, Z))
    (t : T) [Nontrivial (FundamentalGroup T t)]
    (h : Function.Injective (FundamentalGroup.map (g.comp f) t)) :
    Nontrivial (FundamentalGroup Y (f t)) := by
  obtain ⟨a, ha⟩ := exists_ne (1 : FundamentalGroup T t)
  refine nontrivial_of_ne (FundamentalGroup.map f t a) 1 fun h1 => ha (h ?_)
  rw [GC.Topology.fundamentalGroup_map_comp, MonoidHom.comp_apply, h1, map_one, map_one]

end Maps

section Regions
variable {M : Type u} [TopologicalSpace M]

def RegionFI (S : Set M) : Prop :=
  ∀ x : S, IndecomposableNoncyclic (FundamentalGroup S x)

theorem bijective_inclusion_of_isClopen {S S' : Set M} (h : S ⊆ S')
    (hcl : IsClopen (Subtype.val ⁻¹' S : Set S')) (x : S) :
    Function.Bijective (FundamentalGroup.map (inclusionMap h) x) :=
  bijective_fundamentalGroup_map_of_clopen (inclusionMap h) (clopenRetraction S S' hcl x)
    (fun z => Subtype.ext (clopenRetraction_apply_of_mem S S' hcl x _ z.2)) _ hcl
    (fun y hy => Subtype.ext (clopenRetraction_apply_of_mem S S' hcl x y hy)) x x.2

theorem RegionFI.of_isClopen {S S' : Set M} (h : S ⊆ S')
    (hcl : IsClopen (Subtype.val ⁻¹' S : Set S')) (hS' : RegionFI S') : RegionFI S :=
  fun x => (indecomposableNoncyclic_iff_of_bijective _ x
    (bijective_inclusion_of_isClopen h hcl x)).mpr (hS' _)

theorem regionFI_of_forall_isClopen {S' : Set M}
    (h : ∀ x ∈ S', ∃ S ⊆ S', x ∈ S ∧ IsClopen (Subtype.val ⁻¹' S : Set S') ∧ RegionFI S) :
    RegionFI S' := by
  intro x
  obtain ⟨S, hS, hx, hcl, hfi⟩ := h x x.2
  exact (indecomposableNoncyclic_iff_of_bijective (inclusionMap hS) ⟨x, hx⟩
    (bijective_inclusion_of_isClopen hS hcl ⟨x, hx⟩)).mp (hfi ⟨x, hx⟩)

theorem regionFI_of_isPathConnected {S : Set M} (hS : IsPathConnected S) (x : S)
    (hx : IndecomposableNoncyclic (FundamentalGroup S x)) : RegionFI S := by
  have := isPathConnected_iff_pathConnectedSpace.mp hS
  exact fun y => hx.of_mulEquiv (FundamentalGroup.fundamentalGroupMulEquivOfPathConnected x y)

theorem RegionFI.preimage {X S : Set M} (h : S ⊆ X) (hS : RegionFI S)
    (x : (Subtype.val ⁻¹' S : Set X)) :
    IndecomposableNoncyclic (FundamentalGroup (Subtype.val ⁻¹' S : Set X) x) :=
  (indecomposableNoncyclic_iff_of_bijective _ x
    (bijective_map_homeomorph (preimageValHomeo X S h) x)).mpr (hS _)

theorem RegionFI.union_of_amalgam {U V : Set M} (hU : IsOpen U) (hV : IsOpen V)
    (hUpc : IsPathConnected U) (hVpc : IsPathConnected V) (hUVpc : IsPathConnected (U ∩ V))
    (f : C(Torus, M)) (hf : ∀ t, f t ∈ U ∩ V) (t₀ : Torus)
    (hsurj : Function.Surjective (FundamentalGroup.map (toSubset f (U ∩ V) hf) t₀))
    (hfU : InjInto U f) (hfV : InjInto V f) (hUfi : RegionFI U) (hVfi : RegionFI V) :
    RegionFI (U ∪ V) := by
  have hUX : U ⊆ U ∪ V := Set.subset_union_left
  have hVX : V ⊆ U ∪ V := Set.subset_union_right
  have hIX : U ∩ V ⊆ U ∪ V := Set.inter_subset_left.trans hUX
  have hU'o : IsOpen (Subtype.val ⁻¹' U : Set (U ∪ V : Set M)) :=
    hU.preimage continuous_subtype_val
  have hV'o : IsOpen (Subtype.val ⁻¹' V : Set (U ∪ V : Set M)) :=
    hV.preimage continuous_subtype_val
  have hcov : (Subtype.val ⁻¹' U : Set (U ∪ V : Set M)) ∪ Subtype.val ⁻¹' V = Set.univ :=
    Set.eq_univ_of_forall fun y => y.2
  have := pathConnectedSpace_preimage hUpc hUX
  have := pathConnectedSpace_preimage hVpc hVX
  have hI : PathConnectedSpace ↑((Subtype.val ⁻¹' U : Set (U ∪ V : Set M)) ∩
      Subtype.val ⁻¹' V) := pathConnectedSpace_preimage hUVpc hIX
  let F := liftTo (U ∪ V) (U ∩ V) hIX f hf
  have hFs : Function.Surjective (FundamentalGroup.map F t₀) :=
    surjective_liftTo (U ∪ V) (U ∩ V) hIX f hf t₀ hsurj
  have hFU : Function.Injective (FundamentalGroup.map ((interToLeft
      (Subtype.val ⁻¹' U : Set (U ∪ V : Set M)) (Subtype.val ⁻¹' V)).comp F) t₀) :=
    (injective_liftTo_iff (U ∪ V) U hUX f (fun t => (hf t).1) t₀).mpr (hfU.2 t₀)
  have hFV : Function.Injective (FundamentalGroup.map ((interToRight
      (Subtype.val ⁻¹' U : Set (U ∪ V : Set M)) (Subtype.val ⁻¹' V)).comp F) t₀) :=
    (injective_liftTo_iff (U ∪ V) V hVX f (fun t => (hf t).2) t₀).mpr (hfV.2 t₀)
  have hl := injective_fundamentalGroup_map_of_comp F _ t₀ hFs hFU
  have hr := injective_fundamentalGroup_map_of_comp F _ t₀ hFs hFV
  let x₀ : ↑((Subtype.val ⁻¹' U : Set (U ∪ V : Set M)) ∩ Subtype.val ⁻¹' V) := F t₀
  have hφ := fundamentalGroupAmalgamation_injective _ _ x₀ hl hr
  have := nontrivial_torus t₀
  have hC : Nontrivial (FundamentalGroup ↑((Subtype.val ⁻¹' U : Set (U ∪ V : Set M)) ∩
      Subtype.val ⁻¹' V) (overlapBasepoint _ _ x₀.1 x₀.2)) :=
    nontrivial_of_injective_comp F _ t₀ hFU
  have hG : ∀ i, IndecomposableNoncyclic (fundamentalGroupFactor
      (Subtype.val ⁻¹' U : Set (U ∪ V : Set M)) (Subtype.val ⁻¹' V) x₀.1 x₀.2 i) := by
    intro i
    cases i
    · exact hUfi.preimage hUX _
    · exact hVfi.preimage hVX _
  have hPI : GC.Group.FreelyIndecomposable (fundamentalGroupAmalgamatedProduct
      (Subtype.val ⁻¹' U : Set (U ∪ V : Set M)) (Subtype.val ⁻¹' V) x₀.1 x₀.2) :=
    GC.Group.freelyIndecomposable_pushout _ hφ (fun i => (hG i).1) (fun i => (hG i).2)
  let e := fundamentalGroupEquivAmalgamatedProduct _ _ hU'o hV'o hcov x₀.1 x₀.2
  have hX : IndecomposableNoncyclic (FundamentalGroup (U ∪ V : Set M) x₀.1) :=
    ⟨hPI.of_mulEquiv e, not_isCyclic_of_injective (e.toMonoidHom.comp
      (Monoid.PushoutI.of false)) (e.injective.comp (Monoid.PushoutI.of_injective hφ false))
      (hG false).2⟩
  exact regionFI_of_isPathConnected (hUpc.union hVpc ⟨f t₀, (hf t₀).1, (hf t₀).2⟩) _ hX

theorem RegionFI.union_of_hnn {A V N₀ N₁ : Set M} (hA : IsOpen A) (hV : IsOpen V)
    (hApc : IsPathConnected A) (hVpc : IsPathConnected V) (hN : A ∩ V = N₀ ∪ N₁)
    (hN₀ : IsOpen N₀) (hN₁ : IsOpen N₁) (hdisj : Disjoint N₀ N₁)
    (hN₀pc : IsPathConnected N₀) (hN₁pc : IsPathConnected N₁) (f₀ f₁ : C(Torus, M))
    (hf₀ : ∀ t, f₀ t ∈ A ∩ V) (hf₁ : ∀ t, f₁ t ∈ A ∩ V) (t₀ : Torus) (hf₀N : f₀ t₀ ∈ N₀)
    (hf₁N : f₁ t₀ ∈ N₁)
    (hb₀ : Function.Bijective (FundamentalGroup.map (toSubset f₀ (A ∩ V) hf₀) t₀))
    (hb₀V : Function.Bijective (FundamentalGroup.map (toSubset f₀ V (fun t => (hf₀ t).2)) t₀))
    (hs₁ : Function.Surjective (FundamentalGroup.map (toSubset f₁ (A ∩ V) hf₁) t₀))
    (hi₁V : InjInto V f₁) (hi₀A : InjInto A f₀) (hi₁A : InjInto A f₁) (hAfi : RegionFI A) :
    RegionFI (A ∪ V) := by
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
  have hfar : Function.Injective (FundamentalGroup.map ((interToRight
      (Subtype.val ⁻¹' A : Set (A ∪ V : Set M)) (Subtype.val ⁻¹' V)).comp F₁) t₀) :=
    (injective_liftTo_iff (A ∪ V) V hVX f₁ (fun t => (hf₁ t).2) t₀).mpr (hi₁V.2 t₀)
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
      right_injective_far := injective_fundamentalGroup_map_of_comp F₁ _ t₀ hF₁ hfar }
  have := nontrivial_torus t₀
  have hD : Nontrivial (FundamentalGroup ↑((Subtype.val ⁻¹' A : Set (A ∪ V : Set M)) ∩
      Subtype.val ⁻¹' V) K.far) := nontrivial_of_injective_comp F₁ _ t₀ hfar
  have hR : Nontrivial K.rightEdge.range :=
    (MonoidHom.ofInjective K.rightEdge_injective).symm.toEquiv.nontrivial
  have hG : IndecomposableNoncyclic (FundamentalGroup (Subtype.val ⁻¹' A : Set (A ∪ V : Set M))
      (interToLeft _ _ K.base)) := hAfi.preimage hAX _
  have hX : IndecomposableNoncyclic (FundamentalGroup (A ∪ V : Set M)
      ((subsetToAmbient _) (interToLeft _ _ K.base))) :=
    ⟨(GC.Group.freelyIndecomposable_hnnExtension K.edgePairing hG.1 hG.2).of_mulEquiv
      K.equivExtension.symm,
      not_isCyclic_of_injective _ K.injective_fundamentalGroup_map_left hG.2⟩
  have hpc : IsPathConnected (A ∪ V) :=
    hApc.union hVpc ⟨f₀ t₀, (hf₀ t₀).1, (hf₀ t₀).2⟩
  exact regionFI_of_isPathConnected hpc _ hX

end Regions

end GC.Seifert
