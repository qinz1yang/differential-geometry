import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.GluingHNN

/-!
# Seam tori are injective when the ports are

Chapter 6, K09c. For a torus presentation without external tori whose pieces have π₁-injective ports
(`pieceBoundaryTori … incompressible`, the shape of K10), every seam torus is π₁-injective into `W`
at every basepoint (`injective_seamTorus_of_ports`), and the K04 torus decomposition of a closed
presentation is incompressible (`incompressible_toTorusDecomposition_of_ports`). No separation
hypothesis and no restricted presentation is used.

The induction runs over finsets `K` of seams through the open sets `cutOpen K` (`W` with the seam
tori outside `K` removed). The invariant `SeamLevelsInj K` says that every seam torus pushed to the
collar levels `∓1/2` (`levelNeg`, `levelPos`) is π₁-injective into `cutOpen K`. For `K = ∅` this is
read off the ports through the inverse of the interior diffeomorphism (`cutOpenRetract`) and the
homotopy along the collar (`pieceLevelHomotopy`). Adding a seam `j` glues its collar to the path
components `A`, `B` of `cutOpen K` through the two collar halves: for `A = B` by the HNN step
(`InjInto.union_of_hnn`, from `TwoComponentCover`), otherwise by two amalgam steps
(`InjInto.union_of_amalgam`); the glued region and every untouched component are clopen in
`cutOpen (insert j K)` (`injInto_insert`).

`InjInto S f` is π₁-injectivity of a torus `f` into the subset `S`, at every basepoint. It is
transported along inclusions of clopen subsets by retractions (`InjInto.of_isClopen`) and along the
homeomorphisms between subsets of a subset and subsets of the space (`liftTo`).
-/

set_option autoImplicit false

noncomputable section
open CategoryTheory DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open GC.GraphManifold DifferentialGeometry.Topology.VanKampen
open scoped Topology ContinuousMap

universe u

namespace GC.Seifert

section Regions
variable {M : Type u} [TopologicalSpace M]

def toSubset (f : C(Torus, M)) (S : Set M) (hf : ∀ t, f t ∈ S) : C(Torus, S) :=
  ⟨fun t => ⟨f t, hf t⟩, f.continuous.subtype_mk _⟩

def InjInto (S : Set M) (f : C(Torus, M)) : Prop :=
  ∃ hf : ∀ t, f t ∈ S, ∀ t, Function.Injective (FundamentalGroup.map (toSubset f S hf) t)

def inclusionMap {S S' : Set M} (h : S ⊆ S') : C(S, S') :=
  ⟨Set.inclusion h, continuous_inclusion h⟩

theorem InjInto.mem {S : Set M} {f : C(Torus, M)} (h : InjInto S f) (t : Torus) : f t ∈ S :=
  h.1 t

theorem InjInto.of_subset {S S' : Set M} {f : C(Torus, M)} (h : S ⊆ S') (hf : ∀ t, f t ∈ S)
    (hS' : InjInto S' f) : InjInto S f := by
  obtain ⟨_, hinj⟩ := hS'
  exact ⟨hf, fun t => GC.Topology.injective_inner_of_composite (toSubset f S hf)
    (inclusionMap h) t (hinj t)⟩

theorem InjInto.mono {S S' : Set M} {f : C(Torus, M)} (h : S ⊆ S')
    (hinc : ∀ x : S, Function.Injective (FundamentalGroup.map (inclusionMap h) x))
    (hS : InjInto S f) : InjInto S' f := by
  obtain ⟨hf, hinj⟩ := hS
  refine ⟨fun t => h (hf t), fun t => ?_⟩
  have hc := (hinc (toSubset f S hf t)).comp (hinj t)
  rw [← MonoidHom.coe_comp, ← GC.Topology.fundamentalGroup_map_comp] at hc
  exact hc

def clopenRetraction (S S' : Set M) (hcl : IsClopen (Subtype.val ⁻¹' S : Set S')) (x : S) :
    C(S', S) := by
  classical
  refine ⟨fun y => ⟨if (y : M) ∈ S then (y : M) else (x : M), ?_⟩, ?_⟩
  · split_ifs with hy
    exacts [hy, x.2]
  · refine Continuous.subtype_mk (Continuous.if (fun a ha => ?_) continuous_subtype_val
      continuous_const) _
    rw [show {y : S' | (y : M) ∈ S} = Subtype.val ⁻¹' S from rfl, hcl.frontier_eq] at ha
    exact ha.elim

theorem clopenRetraction_apply_of_mem (S S' : Set M) (hcl : IsClopen (Subtype.val ⁻¹' S : Set S'))
    (x : S) (y : S') (hy : (y : M) ∈ S) : (clopenRetraction S S' hcl x y : M) = y := by
  simp [clopenRetraction, hy]

theorem injective_inclusion_of_isClopen {S S' : Set M} (h : S ⊆ S')
    (hcl : IsClopen (Subtype.val ⁻¹' S : Set S')) (x : S) :
    Function.Injective (FundamentalGroup.map (inclusionMap h) x) :=
  injective_fundamentalGroup_map_of_leftInverse (inclusionMap h)
    (clopenRetraction S S' hcl x) (fun z => Subtype.ext
      (clopenRetraction_apply_of_mem S S' hcl x _ z.2)) x

theorem InjInto.of_isClopen {S S' : Set M} {f : C(Torus, M)} (h : S ⊆ S')
    (hcl : IsClopen (Subtype.val ⁻¹' S : Set S')) (hS : InjInto S f) : InjInto S' f :=
  hS.mono h (injective_inclusion_of_isClopen h hcl)

theorem injective_map_iff_of_homeomorph {Y Y' : Type*} [TopologicalSpace Y]
    [TopologicalSpace Y'] (e : Y ≃ₜ Y') (g : C(Torus, Y)) (h : C(Torus, Y'))
    (hgh : ∀ t, e (g t) = h t) (t : Torus) :
    Function.Injective (FundamentalGroup.map g t) ↔
      Function.Injective (FundamentalGroup.map h t) := by
  have hh : h = (e : C(Y, Y')).comp g := ContinuousMap.ext fun s => (hgh s).symm
  subst hh
  rw [GC.Topology.fundamentalGroup_map_comp, MonoidHom.coe_comp]
  exact ⟨fun hg => (injective_fundamentalGroup_map_of_leftInverse (e : C(Y, Y'))
    (e.symm : C(Y', Y)) e.symm_apply_apply (g t)).comp hg, fun hc => hc.of_comp⟩

theorem surjective_map_of_homeomorph {Y Y' : Type*} [TopologicalSpace Y]
    [TopologicalSpace Y'] (e : Y ≃ₜ Y') (g : C(Torus, Y)) (h : C(Torus, Y'))
    (hgh : ∀ t, e (g t) = h t) (t : Torus)
    (hs : Function.Surjective (FundamentalGroup.map g t)) :
    Function.Surjective (FundamentalGroup.map h t) := by
  have hh : h = (e : C(Y, Y')).comp g := ContinuousMap.ext fun s => (hgh s).symm
  subst hh
  rw [GC.Topology.fundamentalGroup_map_comp, MonoidHom.coe_comp]
  exact (bijective_fundamentalGroup_map_of_homotopyEquiv_leftInverse e.symm.toHomotopyEquiv
    (e : C(Y, Y')) e.symm_apply_apply (g t)).2.comp hs

def preimageValHomeo (X S : Set M) (h : S ⊆ X) : (Subtype.val ⁻¹' S : Set X) ≃ₜ S where
  toFun x := ⟨x.1.1, x.2⟩
  invFun y := ⟨⟨y.1, h y.2⟩, y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

def liftTo (X S : Set M) (h : S ⊆ X) (f : C(Torus, M)) (hf : ∀ t, f t ∈ S) :
    C(Torus, (Subtype.val ⁻¹' S : Set X)) :=
  ⟨fun t => ⟨⟨f t, h (hf t)⟩, hf t⟩, (f.continuous.subtype_mk _).subtype_mk _⟩

theorem injective_liftTo_iff (X S : Set M) (h : S ⊆ X) (f : C(Torus, M)) (hf : ∀ t, f t ∈ S)
    (t : Torus) : Function.Injective (FundamentalGroup.map (liftTo X S h f hf) t) ↔
      Function.Injective (FundamentalGroup.map (toSubset f S hf) t) :=
  injective_map_iff_of_homeomorph (preimageValHomeo X S h) _ _ (fun _ => rfl) t

theorem surjective_liftTo (X S : Set M) (h : S ⊆ X) (f : C(Torus, M)) (hf : ∀ t, f t ∈ S)
    (t : Torus) (hs : Function.Surjective (FundamentalGroup.map (toSubset f S hf) t)) :
    Function.Surjective (FundamentalGroup.map (liftTo X S h f hf) t) :=
  surjective_map_of_homeomorph (preimageValHomeo X S h).symm _ _ (fun _ => rfl) t hs

theorem pathConnectedSpace_preimage {X S : Set M} (hS : IsPathConnected S) (h : S ⊆ X) :
    PathConnectedSpace (Subtype.val ⁻¹' S : Set X) :=
  isPathConnected_iff_pathConnectedSpace.mp (hS.preimage_coe h)

theorem InjInto.union_of_amalgam {A V : Set M} (hA : IsOpen A) (hV : IsOpen V)
    (hApc : IsPathConnected A) (hVpc : IsPathConnected V) (hAVpc : IsPathConnected (A ∩ V))
    (f : C(Torus, M)) (hf : ∀ t, f t ∈ A ∩ V) (t₀ : Torus)
    (hsurj : Function.Surjective (FundamentalGroup.map (toSubset f (A ∩ V) hf) t₀))
    (hfA : InjInto A f) (hfV : InjInto V f) :
    (∀ g, InjInto A g → InjInto (A ∪ V) g) ∧ (∀ g, InjInto V g → InjInto (A ∪ V) g) := by
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
  · rintro g ⟨hg, hginj⟩
    refine ⟨fun t => hAX (hg t), fun t => ?_⟩
    have h1 := (GC.Topology.injective_fundamentalGroup_map_iff
      (subsetToAmbient (Subtype.val ⁻¹' A : Set (A ∪ V : Set M))) _
      (liftTo (A ∪ V) A hAX g hg t)).mp hleft
    have h2 := (injective_liftTo_iff (A ∪ V) A hAX g hg t).mpr (hginj t)
    have hc := h1.comp h2
    rw [← MonoidHom.coe_comp, ← GC.Topology.fundamentalGroup_map_comp] at hc
    exact hc
  · rintro g ⟨hg, hginj⟩
    refine ⟨fun t => hVX (hg t), fun t => ?_⟩
    have h1 := (GC.Topology.injective_fundamentalGroup_map_iff
      (subsetToAmbient (Subtype.val ⁻¹' V : Set (A ∪ V : Set M))) _
      (liftTo (A ∪ V) V hVX g hg t)).mp hright
    have h2 := (injective_liftTo_iff (A ∪ V) V hVX g hg t).mpr (hginj t)
    have hc := h1.comp h2
    rw [← MonoidHom.coe_comp, ← GC.Topology.fundamentalGroup_map_comp] at hc
    exact hc

theorem bijective_liftTo (X S : Set M) (h : S ⊆ X) (f : C(Torus, M)) (hf : ∀ t, f t ∈ S)
    (t : Torus) (hb : Function.Bijective (FundamentalGroup.map (toSubset f S hf) t)) :
    Function.Bijective (FundamentalGroup.map (liftTo X S h f hf) t) :=
  ⟨(injective_liftTo_iff X S h f hf t).mpr hb.1, surjective_liftTo X S h f hf t hb.2⟩

theorem not_joined_of_separated {Y : Type*} [TopologicalSpace Y] (π : C(Y, M)) {N₀ N₁ : Set M}
    (hN₀ : IsOpen N₀) (hN₁ : IsOpen N₁) (hdisj : Disjoint N₀ N₁) (hcov : ∀ y, π y ∈ N₀ ∪ N₁)
    {y₀ y₁ : Y} (h₀ : π y₀ ∈ N₀) (h₁ : π y₁ ∈ N₁) : ¬ Joined y₀ y₁ := by
  rintro ⟨γ⟩
  have hp : Continuous (π ∘ γ) := π.continuous.comp γ.continuous
  have hcl : IsClopen ((π ∘ γ) ⁻¹' N₀) := by
    refine ⟨?_, hN₀.preimage hp⟩
    have he : (π ∘ γ) ⁻¹' N₀ = ((π ∘ γ) ⁻¹' N₁)ᶜ := by
      ext s
      rcases hcov (γ s) with h | h
      · exact ⟨fun _ h' => hdisj.le_bot ⟨h, h'⟩, fun _ => h⟩
      · exact ⟨fun h' => (hdisj.le_bot ⟨h', h⟩).elim, fun h' => (h' h).elim⟩
    rw [he]
    exact (hN₁.preimage hp).isClosed_compl
  have h0 : (0 : unitInterval) ∈ (π ∘ γ) ⁻¹' N₀ := by
    change π (γ 0) ∈ N₀
    rw [Path.source]
    exact h₀
  have huniv := hcl.eq_univ ⟨0, h0⟩
  have h1 : (1 : unitInterval) ∈ (π ∘ γ) ⁻¹' N₀ := huniv ▸ Set.mem_univ _
  have h1' : π (γ 1) ∈ N₁ := by
    rw [Path.target]
    exact h₁
  exact hdisj.le_bot ⟨h1, h1'⟩

theorem InjInto.union_of_hnn {A V N₀ N₁ : Set M} (hA : IsOpen A) (hV : IsOpen V)
    (hApc : IsPathConnected A) (hVpc : IsPathConnected V) (hN : A ∩ V = N₀ ∪ N₁)
    (hN₀ : IsOpen N₀) (hN₁ : IsOpen N₁) (hdisj : Disjoint N₀ N₁)
    (hN₀pc : IsPathConnected N₀) (hN₁pc : IsPathConnected N₁) (f₀ f₁ : C(Torus, M))
    (hf₀ : ∀ t, f₀ t ∈ A ∩ V) (hf₁ : ∀ t, f₁ t ∈ A ∩ V) (t₀ : Torus) (hf₀N : f₀ t₀ ∈ N₀)
    (hf₁N : f₁ t₀ ∈ N₁)
    (hb₀ : Function.Bijective (FundamentalGroup.map (toSubset f₀ (A ∩ V) hf₀) t₀))
    (hb₀V : Function.Bijective (FundamentalGroup.map (toSubset f₀ V (fun t => (hf₀ t).2)) t₀))
    (hs₁ : Function.Surjective (FundamentalGroup.map (toSubset f₁ (A ∩ V) hf₁) t₀))
    (hi₁V : InjInto V f₁) (hi₀A : InjInto A f₀) (hi₁A : InjInto A f₁) :
    ∀ g, InjInto A g → InjInto (A ∪ V) g := by
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
  rintro g ⟨hg, hginj⟩
  refine ⟨fun t => hAX (hg t), fun t => ?_⟩
  have h1 := (GC.Topology.injective_fundamentalGroup_map_iff
    (subsetToAmbient (Subtype.val ⁻¹' A : Set (A ∪ V : Set M))) _
    (liftTo (A ∪ V) A hAX g hg t)).mp hleft
  have h2 := (injective_liftTo_iff (A ∪ V) A hAX g hg t).mpr (hginj t)
  have hc := h1.comp h2
  rw [← MonoidHom.coe_comp, ← GC.Topology.fundamentalGroup_map_comp] at hc
  exact hc

theorem isClopen_preimage_of_cover {S X D : Set M} (hX : IsOpen X) (hD : IsOpen D)
    (hcov : S ⊆ X ∪ D) (hdisj : Disjoint X D) : IsClopen (Subtype.val ⁻¹' X : Set S) := by
  refine ⟨?_, hX.preimage continuous_subtype_val⟩
  have he : (Subtype.val ⁻¹' X : Set S) = (Subtype.val ⁻¹' D)ᶜ := by
    ext y
    constructor
    · intro hy hy'
      exact hdisj.le_bot ⟨hy, hy'⟩
    · intro hy
      rcases hcov y.2 with h | h
      · exact h
      · exact (hy h).elim
  rw [he]
  exact (hD.preimage continuous_subtype_val).isClosed_compl

theorem surjective_toSubset_of_isClopen {S S' : Set M} (h : S ⊆ S')
    (hcl : IsClopen (Subtype.val ⁻¹' S : Set S')) (f : C(Torus, M)) (hf : ∀ t, f t ∈ S)
    (t : Torus)
    (hs : Function.Surjective (FundamentalGroup.map (toSubset f S' fun t => h (hf t)) t)) :
    Function.Surjective (FundamentalGroup.map (toSubset f S hf) t) := by
  intro γ
  obtain ⟨a, ha⟩ := hs (FundamentalGroup.map (inclusionMap h) (toSubset f S hf t) γ)
  refine ⟨a, injective_inclusion_of_isClopen h hcl _ ?_⟩
  rw [← ha, ← MonoidHom.comp_apply, ← GC.Topology.fundamentalGroup_map_comp]
  rfl

theorem bijective_toSubset_congr {S S' : Set M} (h : S = S') (f : C(Torus, M))
    (hf : ∀ t, f t ∈ S) (hf' : ∀ t, f t ∈ S') (t : Torus)
    (hb : Function.Bijective (FundamentalGroup.map (toSubset f S hf) t)) :
    Function.Bijective (FundamentalGroup.map (toSubset f S' hf') t) := by
  subst h
  exact hb

theorem disjoint_pathComponentIn {O : Set M} {x y : M} (h : y ∉ pathComponentIn O x) :
    Disjoint (pathComponentIn O y) (pathComponentIn O x) := by
  rw [Set.disjoint_left]
  intro z hzy hzx
  have hy : y ∈ O := pathComponentIn_nonempty_iff.mp ⟨z, hzy⟩
  apply h
  rw [← pathComponentIn_congr hzx, pathComponentIn_congr hzy]
  exact mem_pathComponentIn_self hy

theorem isOpen_diff_pathComponentIn [LocallyPathConnectedSpace M] {O : Set M} (hO : IsOpen O)
    (x : M) : IsOpen (O \ pathComponentIn O x) := by
  refine isOpen_iff_forall_mem_open.mpr fun y hy => ?_
  refine ⟨pathComponentIn O y, fun z hz => ⟨pathComponentIn_subset hz, fun hzx => ?_⟩,
    hO.pathComponentIn y, mem_pathComponentIn_self hy.1⟩
  exact (disjoint_pathComponentIn hy.2).le_bot ⟨hz, hzx⟩

theorem InjInto.injective_of_eq_univ {S : Set M} {f : C(Torus, M)} (h : InjInto S f)
    (hS : S = Set.univ) (t : Torus) : Function.Injective (FundamentalGroup.map f t) := by
  subst hS
  obtain ⟨hf, hinj⟩ := h
  exact (injective_map_iff_of_homeomorph (Homeomorph.Set.univ M) (toSubset f Set.univ hf) f
    (fun _ => rfl) t).mp (hinj t)

theorem injective_fundamentalGroup_map_of_homotopy {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {F₀ F₁ : C(X, Y)} (H : F₀.Homotopy F₁) (x : X)
    (h : Function.Injective (FundamentalGroup.map F₁ x)) :
    Function.Injective (FundamentalGroup.map F₀ x) := by
  have key : ∀ a : FundamentalGroup X x,
      (FundamentalGroupoid.map F₀).map a ≫ Path.Homotopic.Quotient.mk (H.evalAt x) =
        Path.Homotopic.Quotient.mk (H.evalAt x) ≫ (FundamentalGroupoid.map F₁).map a := by
    intro a
    induction a using Path.Homotopic.Quotient.ind with
    | mk ℓ => exact Path.Homotopic.Quotient.eq.mpr (Path.Homotopic.map_trans_evalAt H ℓ)
  intro a b hab
  apply h
  change (FundamentalGroupoid.map F₀).map a = (FundamentalGroupoid.map F₀).map b at hab
  change (FundamentalGroupoid.map F₁).map a = (FundamentalGroupoid.map F₁).map b
  have ha := key a
  rw [hab, key b] at ha
  exact ((cancel_epi (show FundamentalGroupoid.mk (F₀ x) ⟶ FundamentalGroupoid.mk (F₁ x) from
    Path.Homotopic.Quotient.mk (H.evalAt x))).mp ha).symm

def clopenRetract (S : Set M) (hS : IsClopen S) (x : S) : C(M, S) := by
  classical
  refine ⟨fun y => ⟨if y ∈ S then y else (x : M), ?_⟩, ?_⟩
  · split_ifs with hy
    exacts [hy, x.2]
  · refine Continuous.subtype_mk (Continuous.if (fun a ha => ?_) continuous_id
      continuous_const) _
    rw [show {y : M | y ∈ S} = S from rfl, hS.frontier_eq] at ha
    exact ha.elim

theorem clopenRetract_apply_of_mem (S : Set M) (hS : IsClopen S) (x : S) (y : M) (hy : y ∈ S) :
    (clopenRetract S hS x y : M) = y := by
  simp [clopenRetract, hy]

theorem injective_subsetToAmbient_of_isClopen (S : Set M) (hS : IsClopen S) (x : S) :
    Function.Injective (FundamentalGroup.map (subsetToAmbient S) x) :=
  injective_fundamentalGroup_map_of_leftInverse (subsetToAmbient S) (clopenRetract S hS x)
    (fun z => Subtype.ext (clopenRetract_apply_of_mem S hS x _ z.2)) x

end Regions

namespace TorusPresentation
variable {W : CompactCarrier.{u}} (G : TorusPresentation W)

theorem locallyPathConnectedSpace_carrier : LocallyPathConnectedSpace W.Carrier :=
  Manifold.locallyPathConnectedSpace_of_modelWithCorners (M := W.Carrier) W.model

def cutOpen (K : Finset (Fin G.pairing.count)) : Set W.Carrier :=
  (⋃ k ∈ Finset.univ \ K, G.seamSurface k)ᶜ

theorem isOpen_cutOpen (K : Finset (Fin G.pairing.count)) : IsOpen (G.cutOpen K) :=
  (isClosed_biUnion_finset fun k _ => G.isClosed_seamSurface k).isOpen_compl

theorem mem_cutOpen {K : Finset (Fin G.pairing.count)} {y : W.Carrier} :
    y ∈ G.cutOpen K ↔ ∀ k, k ∉ K → y ∉ G.seamSurface k := by
  simp [cutOpen]

theorem cutOpen_univ : G.cutOpen Finset.univ = Set.univ :=
  Set.eq_univ_of_forall fun _ => G.mem_cutOpen.mpr fun k hk => (hk (Finset.mem_univ k)).elim

theorem seamSurface_disjoint_seamCollar {j k : Fin G.pairing.count} (h : k ≠ j) :
    Disjoint (G.seamSurface k) (G.seamCollar j) :=
  (G.seam_disjoint h).mono_left (G.seamSurface_subset_seamCollar k)

def levelMap (k : Fin G.pairing.count) (c : ℝ) (hc : -1 < c ∧ c < 1) : C(Torus, W.Carrier) :=
  ⟨fun t => G.seam k (t, c),
    (G.continuousOn_seam k).comp_continuous (by fun_prop) fun _ => G.mem_seam_source k hc⟩

theorem levelMap_mem_seamCollar (k : Fin G.pairing.count) (c : ℝ) (hc : -1 < c ∧ c < 1)
    (t : Torus) : G.levelMap k c hc t ∈ G.seamCollar k :=
  G.seam_mem_seamCollar k hc

theorem levelMap_mem_cutOpen (k : Fin G.pairing.count) (c : ℝ) (hc : -1 < c ∧ c < 1)
    (h0 : c ≠ 0) (K : Finset (Fin G.pairing.count)) (t : Torus) :
    G.levelMap k c hc t ∈ G.cutOpen K := by
  rw [mem_cutOpen]
  intro k' _ hs
  by_cases hk : k' = k
  · subst hk
    exact G.seam_not_mem_seamSurface k' hc h0 hs
  · exact (G.seamSurface_disjoint_seamCollar hk).le_bot ⟨hs, G.seam_mem_seamCollar k hc⟩

theorem cutOpen_subset_insert (j : Fin G.pairing.count) (K : Finset (Fin G.pairing.count)) :
    G.cutOpen K ⊆ G.cutOpen (insert j K) := fun _ hy =>
  G.mem_cutOpen.mpr fun k hk => G.mem_cutOpen.mp hy k fun h => hk (Finset.mem_insert_of_mem h)

theorem seamCollar_subset_cutOpen_insert (j : Fin G.pairing.count)
    (K : Finset (Fin G.pairing.count)) : G.seamCollar j ⊆ G.cutOpen (insert j K) := fun y hy =>
  G.mem_cutOpen.mpr fun k hk hs => (G.seamSurface_disjoint_seamCollar
    (fun h => hk (by rw [h]; exact Finset.mem_insert_self j K))).le_bot ⟨hs, hy⟩

theorem cutOpen_insert_subset (j : Fin G.pairing.count) (K : Finset (Fin G.pairing.count)) :
    G.cutOpen (insert j K) ⊆ G.cutOpen K ∪ G.seamCollar j := by
  intro y hy
  by_cases hs : y ∈ G.seamSurface j
  · exact Or.inr (G.seamSurface_subset_seamCollar j hs)
  · refine Or.inl (G.mem_cutOpen.mpr fun k hk => ?_)
    by_cases hkj : k = j
    · exact hkj ▸ hs
    · exact G.mem_cutOpen.mp hy k fun h => (Finset.mem_insert.mp h).elim hkj hk

theorem seamCollar_inter_cutOpen (j : Fin G.pairing.count) {K : Finset (Fin G.pairing.count)}
    (hj : j ∉ K) : G.seamCollar j ∩ G.cutOpen K = (G.seamSurface j)ᶜ ∩ G.seamCollar j := by
  ext y
  constructor
  · rintro ⟨hc, ho⟩
    exact ⟨G.mem_cutOpen.mp ho j hj, hc⟩
  · rintro ⟨hs, hc⟩
    refine ⟨hc, G.mem_cutOpen.mpr fun k _ hk => ?_⟩
    by_cases hkj : k = j
    · exact hs (hkj ▸ hk)
    · exact (G.seamSurface_disjoint_seamCollar hkj).le_bot ⟨hk, hc⟩

def negHalf (j : Fin G.pairing.count) : Set W.Carrier := G.seam j '' slab (-1) 0

def posHalf (j : Fin G.pairing.count) : Set W.Carrier := G.seam j '' slab 0 1

theorem isOpen_seam_slab (j : Fin G.pairing.count) {a b : ℝ} (ha : -1 ≤ a) (hb : b ≤ 1) :
    IsOpen (G.seam j '' slab a b) :=
  (G.seam j).toOpenPartialHomeomorph.isOpen_image_of_subset_source
    ((isOpen_lt continuous_const continuous_snd).inter (isOpen_lt continuous_snd continuous_const))
    fun _ hp => G.mem_seam_source j ⟨lt_of_le_of_lt ha hp.1, lt_of_lt_of_le hp.2 hb⟩

theorem isOpen_negHalf (j : Fin G.pairing.count) : IsOpen (G.negHalf j) :=
  G.isOpen_seam_slab j le_rfl (by norm_num)

theorem isOpen_posHalf (j : Fin G.pairing.count) : IsOpen (G.posHalf j) :=
  G.isOpen_seam_slab j (by norm_num) le_rfl

theorem isPathConnected_negHalf (j : Fin G.pairing.count) : IsPathConnected (G.negHalf j) :=
  G.isPathConnected_seam_slab j le_rfl (by norm_num) (by norm_num)

theorem isPathConnected_posHalf (j : Fin G.pairing.count) : IsPathConnected (G.posHalf j) :=
  G.isPathConnected_seam_slab j (by norm_num) (by norm_num) le_rfl

theorem disjoint_negHalf_posHalf (j : Fin G.pairing.count) :
    Disjoint (G.negHalf j) (G.posHalf j) := by
  rw [Set.disjoint_left]
  rintro _ ⟨p, hp, rfl⟩ ⟨q, hq, hpq⟩
  have h := (G.seam j).toPartialEquiv.injOn
    (G.mem_seam_source j ⟨hq.1.trans' (by norm_num), hq.2⟩)
    (G.mem_seam_source j ⟨hp.1, hp.2.trans (by norm_num)⟩) hpq
  have h2 := congrArg Prod.snd h
  have := hp.2
  have := hq.1
  linarith

theorem gap_eq (j : Fin G.pairing.count) :
    (G.seamSurface j)ᶜ ∩ G.seamCollar j = G.negHalf j ∪ G.posHalf j := by
  ext y
  constructor
  · rintro ⟨hs, hc⟩
    have hy : G.seam j ((G.seam j).toPartialEquiv.symm y) = y :=
      (G.seam j).toPartialEquiv.right_inv hc
    have hsrc := (G.seam j).toPartialEquiv.map_target hc
    rw [G.seam_source j] at hsrc
    have hne : ((G.seam j).toPartialEquiv.symm y).2 ≠ 0 := fun h0 => hs ⟨_, by
      rw [seamTorus_apply, ← h0]
      exact hy⟩
    rcases lt_or_gt_of_ne hne with h | h
    · exact Or.inl ⟨_, ⟨hsrc.1, h⟩, hy⟩
    · exact Or.inr ⟨_, ⟨h, hsrc.2⟩, hy⟩
  · rintro (h | h)
    · exact G.seam_slab_subset_gap j le_rfl (by norm_num) (by simp) h
    · exact G.seam_slab_subset_gap j (by norm_num) le_rfl (by simp) h

attribute [local instance] locallyPathConnectedSpace_carrier

def levelNeg (k : Fin G.pairing.count) : C(Torus, W.Carrier) :=
  G.levelMap k (-2⁻¹) ⟨by norm_num, by norm_num⟩

def levelPos (k : Fin G.pairing.count) : C(Torus, W.Carrier) :=
  G.levelMap k 2⁻¹ ⟨by norm_num, by norm_num⟩

theorem levelNeg_mem_negHalf (k : Fin G.pairing.count) (t : Torus) :
    G.levelNeg k t ∈ G.negHalf k :=
  ⟨(t, -2⁻¹), ⟨by norm_num, by norm_num⟩, rfl⟩

theorem levelPos_mem_posHalf (k : Fin G.pairing.count) (t : Torus) :
    G.levelPos k t ∈ G.posHalf k :=
  ⟨(t, 2⁻¹), ⟨by norm_num, by norm_num⟩, rfl⟩

theorem injInto_seamCollar_levelNeg (k : Fin G.pairing.count) :
    InjInto (G.seamCollar k) (G.levelNeg k) :=
  ⟨fun t => G.levelMap_mem_seamCollar k _ _ t, fun t =>
    (G.bijective_collar_gapLevel k (-2⁻¹) ⟨by norm_num, by norm_num⟩ (by norm_num) t).1⟩

theorem injInto_seamCollar_levelPos (k : Fin G.pairing.count) :
    InjInto (G.seamCollar k) (G.levelPos k) :=
  ⟨fun t => G.levelMap_mem_seamCollar k _ _ t, fun t =>
    (G.bijective_collar_gapLevel k 2⁻¹ ⟨by norm_num, by norm_num⟩ (by norm_num) t).1⟩

theorem negHalf_subset_gap (j : Fin G.pairing.count) :
    G.negHalf j ⊆ (G.seamSurface j)ᶜ ∩ G.seamCollar j := by
  rw [G.gap_eq j]
  exact Set.subset_union_left

theorem posHalf_subset_gap (j : Fin G.pairing.count) :
    G.posHalf j ⊆ (G.seamSurface j)ᶜ ∩ G.seamCollar j := by
  rw [G.gap_eq j]
  exact Set.subset_union_right

def SeamLevelsInj (K : Finset (Fin G.pairing.count)) : Prop :=
  ∀ k, InjInto (G.cutOpen K) (G.levelNeg k) ∧ InjInto (G.cutOpen K) (G.levelPos k)

section Step
variable {G} {j : Fin G.pairing.count} {K : Finset (Fin G.pairing.count)}

theorem injInto_insert (hj : j ∉ K) (hK : G.SeamLevelsInj K) (f : C(Torus, W.Carrier))
    (hf : InjInto (G.cutOpen K) f) : InjInto (G.cutOpen (insert j K)) f := by
  set O := G.cutOpen K with hOdef
  set O' := G.cutOpen (insert j K) with hO'def
  set C := G.seamCollar j with hCdef
  have hO : IsOpen O := G.isOpen_cutOpen K
  have hgap : C ∩ O = (G.seamSurface j)ᶜ ∩ C := G.seamCollar_inter_cutOpen j hj
  have hgap' : C ∩ O = G.negHalf j ∪ G.posHalf j := hgap.trans (G.gap_eq j)
  have hnegO : G.negHalf j ⊆ O := fun y hy =>
    (hgap' ▸ (Or.inl hy : y ∈ G.negHalf j ∪ G.posHalf j) : y ∈ C ∩ O).2
  have hposO : G.posHalf j ⊆ O := fun y hy =>
    (hgap' ▸ (Or.inr hy : y ∈ G.negHalf j ∪ G.posHalf j) : y ∈ C ∩ O).2
  have hnegC : G.negHalf j ⊆ C := fun y hy => (G.negHalf_subset_gap j hy).2
  have hposC : G.posHalf j ⊆ C := fun y hy => (G.posHalf_subset_gap j hy).2
  have hOO' : O ⊆ O' := G.cutOpen_subset_insert j K
  have hCO' : C ⊆ O' := G.seamCollar_subset_cutOpen_insert j K
  have hO'cov : O' ⊆ O ∪ C := G.cutOpen_insert_subset j K
  have hCo : IsOpen C := G.isOpen_seamCollar j
  set t₀ : Torus := (1, 1)
  set A := pathComponentIn O (G.levelNeg j t₀) with hAdef
  set B := pathComponentIn O (G.levelPos j t₀) with hBdef
  have hAo : IsOpen A := hO.pathComponentIn _
  have hBo : IsOpen B := hO.pathComponentIn _
  have hApc : IsPathConnected A :=
    isPathConnected_pathComponentIn (hnegO (G.levelNeg_mem_negHalf j t₀))
  have hBpc : IsPathConnected B :=
    isPathConnected_pathComponentIn (hposO (G.levelPos_mem_posHalf j t₀))
  have hnegA : G.negHalf j ⊆ A :=
    (G.isPathConnected_negHalf j).subset_pathComponentIn (G.levelNeg_mem_negHalf j t₀) hnegO
  have hposB : G.posHalf j ⊆ B :=
    (G.isPathConnected_posHalf j).subset_pathComponentIn (G.levelPos_mem_posHalf j t₀) hposO
  have hAO : A ⊆ O := pathComponentIn_subset
  have hBO : B ⊆ O := pathComponentIn_subset
  have hCOsub : ∀ y, y ∈ C → y ∈ O → y ∈ G.negHalf j ∪ G.posHalf j := fun y hc ho =>
    hgap' ▸ (⟨hc, ho⟩ : y ∈ C ∩ O)
  have hiNeg : InjInto A (G.levelNeg j) :=
    (hK j).1.of_subset hAO fun t => hnegA (G.levelNeg_mem_negHalf j t)
  have hiPos : InjInto B (G.levelPos j) :=
    (hK j).2.of_subset hBO fun t => hposB (G.levelPos_mem_posHalf j t)
  have hcolNeg := G.injInto_seamCollar_levelNeg j
  have hcolPos := G.injInto_seamCollar_levelPos j
  have hmerged : ∀ g, (InjInto A g → InjInto O' g) ∧ (InjInto B g → InjInto O' g) := by
    by_cases hAB : G.levelPos j t₀ ∈ A
    · have hBA : B = A := pathComponentIn_congr hAB
      have hposA : G.posHalf j ⊆ A := hBA ▸ hposB
      have hN : A ∩ C = G.negHalf j ∪ G.posHalf j := by
        ext y
        constructor
        · rintro ⟨ha, hc⟩
          exact hCOsub y hc (hAO ha)
        · rintro (h | h)
          · exact ⟨hnegA h, hnegC h⟩
          · exact ⟨hposA h, hposC h⟩
      have hAgap : (G.seamSurface j)ᶜ ∩ C = A ∩ C := (hN.trans (G.gap_eq j).symm).symm
      have hf₀ : ∀ t, G.levelNeg j t ∈ A ∩ C := fun t =>
        ⟨hnegA (G.levelNeg_mem_negHalf j t), hnegC (G.levelNeg_mem_negHalf j t)⟩
      have hf₁ : ∀ t, G.levelPos j t ∈ A ∩ C := fun t =>
        ⟨hposA (G.levelPos_mem_posHalf j t), hposC (G.levelPos_mem_posHalf j t)⟩
      have hX := InjInto.union_of_hnn hAo hCo hApc (G.isPathConnected_seamCollar j) hN
        (G.isOpen_negHalf j) (G.isOpen_posHalf j) (G.disjoint_negHalf_posHalf j)
        (G.isPathConnected_negHalf j) (G.isPathConnected_posHalf j) (G.levelNeg j)
        (G.levelPos j) hf₀ hf₁ t₀ (G.levelNeg_mem_negHalf j t₀) (G.levelPos_mem_posHalf j t₀)
        (bijective_toSubset_congr hAgap (G.levelNeg j) _ _ t₀ (G.bijective_gapLevel_neg j t₀))
        (G.bijective_collar_gapLevel j (-2⁻¹) ⟨by norm_num, by norm_num⟩ (by norm_num) t₀)
        (bijective_toSubset_congr hAgap (G.levelPos j) _ _ t₀
          (G.bijective_gapLevel_pos j t₀)).2
        hcolPos hiNeg (hBA ▸ hiPos)
      have hXO' : A ∪ C ⊆ O' := Set.union_subset (hAO.trans hOO') hCO'
      have hXcl : IsClopen (Subtype.val ⁻¹' (A ∪ C) : Set O') := by
        refine isClopen_preimage_of_cover (D := O \ A) (hAo.union hCo)
          (isOpen_diff_pathComponentIn hO _) (fun y hy => ?_) ?_
        · rcases hO'cov hy with h | h
          · by_cases ha : y ∈ A
            · exact Or.inl (Or.inl ha)
            · exact Or.inr ⟨h, ha⟩
          · exact Or.inl (Or.inr h)
        · rw [Set.disjoint_left]
          rintro y (ha | hc) ⟨ho, hna⟩
          · exact hna ha
          · rcases hCOsub y hc ho with h | h
            · exact hna (hnegA h)
            · exact hna (hposA h)
      intro g
      exact ⟨fun hg => (hX g hg).of_isClopen hXO' hXcl,
        fun hg => (hX g (hBA ▸ hg)).of_isClopen hXO' hXcl⟩
    · have hBA : Disjoint B A := disjoint_pathComponentIn hAB
      have hCB : C ∩ B = G.posHalf j := by
        ext y
        constructor
        · rintro ⟨hc, hb⟩
          rcases hCOsub y hc (hBO hb) with h | h
          · exact (hBA.le_bot ⟨hb, hnegA h⟩).elim
          · exact h
        · intro h
          exact ⟨hposC h, hposB h⟩
      have hAV : A ∩ (C ∪ B) = G.negHalf j := by
        ext y
        constructor
        · rintro ⟨ha, hc | hb⟩
          · rcases hCOsub y hc (hAO ha) with h | h
            · exact h
            · exact (hBA.le_bot ⟨hposB h, ha⟩).elim
          · exact (hBA.le_bot ⟨hb, ha⟩).elim
        · intro h
          exact ⟨hnegA h, Or.inl (hnegC h)⟩
      have hgapcov : ∀ y, y ∈ (G.seamSurface j)ᶜ ∩ C → y ∈ G.negHalf j ∪ G.posHalf j :=
        fun y hy => (G.gap_eq j) ▸ hy
      have hcl1 : IsClopen (Subtype.val ⁻¹' (C ∩ B) : Set ((G.seamSurface j)ᶜ ∩ C : Set _)) := by
        refine isClopen_preimage_of_cover (D := A) (hCo.inter hBo) hAo (fun y hy => ?_) ?_
        · rcases hgapcov y hy with h | h
          · exact Or.inr (hnegA h)
          · exact Or.inl ⟨hposC h, hposB h⟩
        · rw [Set.disjoint_left]
          rintro y ⟨_, hb⟩ ha
          exact hBA.le_bot ⟨hb, ha⟩
      have hsub1 : C ∩ B ⊆ (G.seamSurface j)ᶜ ∩ C := fun y hy =>
        G.posHalf_subset_gap j (hCB ▸ hy)
      have hf1 : ∀ t, G.levelPos j t ∈ C ∩ B := fun t =>
        ⟨hposC (G.levelPos_mem_posHalf j t), hposB (G.levelPos_mem_posHalf j t)⟩
      have h1 := InjInto.union_of_amalgam hCo hBo (G.isPathConnected_seamCollar j) hBpc
        (hCB ▸ G.isPathConnected_posHalf j) (G.levelPos j) hf1 t₀
        (surjective_toSubset_of_isClopen hsub1 hcl1 (G.levelPos j) hf1 t₀
          (G.bijective_gapLevel_pos j t₀).2) hcolPos hiPos
      have hCBpc : IsPathConnected (C ∪ B) := (G.isPathConnected_seamCollar j).union hBpc
        ⟨G.levelPos j t₀, hposC (G.levelPos_mem_posHalf j t₀),
          hposB (G.levelPos_mem_posHalf j t₀)⟩
      have hcl2 : IsClopen (Subtype.val ⁻¹' (A ∩ (C ∪ B)) :
          Set ((G.seamSurface j)ᶜ ∩ C : Set _)) := by
        refine isClopen_preimage_of_cover (D := B) (hAo.inter (hCo.union hBo)) hBo
          (fun y hy => ?_) ?_
        · rcases hgapcov y hy with h | h
          · exact Or.inl (hAV ▸ h)
          · exact Or.inr (hposB h)
        · rw [Set.disjoint_left]
          rintro y ⟨ha, _⟩ hb
          exact hBA.le_bot ⟨hb, ha⟩
      have hsub2 : A ∩ (C ∪ B) ⊆ (G.seamSurface j)ᶜ ∩ C := fun y hy =>
        G.negHalf_subset_gap j (hAV ▸ hy)
      have hf2 : ∀ t, G.levelNeg j t ∈ A ∩ (C ∪ B) := fun t =>
        ⟨hnegA (G.levelNeg_mem_negHalf j t), Or.inl (hnegC (G.levelNeg_mem_negHalf j t))⟩
      have h2 := InjInto.union_of_amalgam hAo (hCo.union hBo) hApc hCBpc
        (hAV ▸ G.isPathConnected_negHalf j) (G.levelNeg j) hf2 t₀
        (surjective_toSubset_of_isClopen hsub2 hcl2 (G.levelNeg j) hf2 t₀
          (G.bijective_gapLevel_neg j t₀).2) hiNeg (h1.1 _ hcolNeg)
      have hXO' : A ∪ (C ∪ B) ⊆ O' :=
        Set.union_subset (hAO.trans hOO') (Set.union_subset hCO' (hBO.trans hOO'))
      have hXcl : IsClopen (Subtype.val ⁻¹' (A ∪ (C ∪ B)) : Set O') := by
        refine isClopen_preimage_of_cover (D := (O \ A) ∩ (O \ B))
          (hAo.union (hCo.union hBo))
          ((isOpen_diff_pathComponentIn hO _).inter (isOpen_diff_pathComponentIn hO _))
          (fun y hy => ?_) ?_
        · rcases hO'cov hy with h | h
          · by_cases ha : y ∈ A
            · exact Or.inl (Or.inl ha)
            · by_cases hb : y ∈ B
              · exact Or.inl (Or.inr (Or.inr hb))
              · exact Or.inr ⟨⟨h, ha⟩, ⟨h, hb⟩⟩
          · exact Or.inl (Or.inr (Or.inl h))
        · rw [Set.disjoint_left]
          rintro y (ha | hc | hb) ⟨⟨ho, hna⟩, ⟨_, hnb⟩⟩
          · exact hna ha
          · rcases hCOsub y hc ho with h | h
            · exact hna (hnegA h)
            · exact hnb (hposB h)
          · exact hnb hb
      intro g
      exact ⟨fun hg => (h2.1 g hg).of_isClopen hXO' hXcl,
        fun hg => (h2.2 g (h1.2 g hg)).of_isClopen hXO' hXcl⟩
  have hother : ∀ D : Set W.Carrier, IsOpen D → D ⊆ O → IsOpen (O \ D) → Disjoint D A →
      Disjoint D B → ∀ g, InjInto D g → InjInto O' g := by
    intro D hDo hDO hDc hDA hDB g hg
    refine hg.of_isClopen (hDO.trans hOO')
      (isClopen_preimage_of_cover (D := (O \ D) ∪ C) hDo (hDc.union hCo) ?_ ?_)
    · intro y hy
      rcases hO'cov hy with h | h
      · by_cases hd : y ∈ D
        · exact Or.inl hd
        · exact Or.inr (Or.inl ⟨h, hd⟩)
      · exact Or.inr (Or.inr h)
    · rw [Set.disjoint_left]
      rintro y hyD (⟨_, h⟩ | hyC)
      · exact h hyD
      · rcases hCOsub y hyC (hDO hyD) with h | h
        · exact hDA.le_bot ⟨hyD, hnegA h⟩
        · exact hDB.le_bot ⟨hyD, hposB h⟩
  have hfO : ∀ t, f t ∈ O := hf.1
  set D := pathComponentIn O (f t₀) with hDdef
  have hfD : ∀ t, f t ∈ D := fun t => (isPathConnected_range f.continuous).subset_pathComponentIn
    (Set.mem_range_self t₀) (Set.range_subset_iff.mpr hfO) (Set.mem_range_self t)
  have hfD' : InjInto D f := hf.of_subset pathComponentIn_subset hfD
  by_cases hA' : f t₀ ∈ A
  · have hDA : D = A := pathComponentIn_congr hA'
    exact (hmerged f).1 (hDA ▸ hfD')
  by_cases hB' : f t₀ ∈ B
  · have hDB : D = B := pathComponentIn_congr hB'
    exact (hmerged f).2 (hDB ▸ hfD')
  exact hother D (hO.pathComponentIn _) pathComponentIn_subset
    (isOpen_diff_pathComponentIn hO _) (disjoint_pathComponentIn hA')
    (disjoint_pathComponentIn hB') f hfD'

end Step

section Base
variable {G}

theorem cutMap_surjective : Function.Surjective G.cutMap := by
  intro y
  obtain ⟨x, hx⟩ := Quotient.exists_rep (G.reconstruction.symm y)
  refine ⟨x, ?_⟩
  change G.reconstruction (Quotient.mk'' x) = y
  rw [show (Quotient.mk'' x : G.pairing.QuotientSpace) = G.reconstruction.symm y from hx,
    Homeomorph.apply_symm_apply]

theorem exists_seamSurface_of_boundary (hext : G.externalCount = 0) {x : G.cutCarrier.Carrier}
    (hx : x ∈ G.cutCarrier.model.boundary G.cutCarrier.Carrier) :
    ∃ k, G.cutMap x ∈ G.seamSurface k := by
  rw [G.cut_boundary_exhausted] at hx
  rcases hx with hx | hx
  · obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
    rcases hk with hl | hr
    · refine ⟨k, (G.pairing.leftParam k).symm ⟨x, hl⟩, ?_⟩
      rw [seamTorus_eq_cutMap, Homeomorph.apply_symm_apply]
    · refine ⟨k, (G.pairing.matching k).symm ((G.pairing.rightParam k).symm ⟨x, hr⟩), ?_⟩
      rw [seamTorus_eq_cutMap_right, Diffeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]
  · obtain ⟨i, _⟩ := Set.mem_iUnion.mp hx
    have hi : (i : ℕ) < 0 := hext ▸ i.isLt
    exact absurd hi (Nat.not_lt_zero _)

theorem isInteriorPoint_of_forall_not_mem (hext : G.externalCount = 0)
    {x : G.cutCarrier.Carrier} (hx : ∀ k, G.cutMap x ∉ G.seamSurface k) :
    G.cutCarrier.model.IsInteriorPoint x := by
  rcases G.cutCarrier.model.isInteriorPoint_or_isBoundaryPoint x with h | h
  · exact h
  · obtain ⟨k, hk⟩ := G.exists_seamSurface_of_boundary hext h
    exact (hx k hk).elim

theorem not_mem_seamSurface_of_mem_cutOpen_empty {y : W.Carrier} (hy : y ∈ G.cutOpen ∅)
    (k : Fin G.pairing.count) : y ∉ G.seamSurface k :=
  G.mem_cutOpen.mp hy k (Finset.notMem_empty k)

theorem mem_interiorImage (hext : G.externalCount = 0) {y : W.Carrier} (hy : y ∈ G.cutOpen ∅) :
    y ∈ G.interiorImage := by
  obtain ⟨x, rfl⟩ := G.cutMap_surjective y
  have hx := G.isInteriorPoint_of_forall_not_mem hext
    (G.not_mem_seamSurface_of_mem_cutOpen_empty hy)
  have h := (G.interiorDiffeomorph ⟨x, hx⟩).2
  rw [G.interior_map ⟨x, hx⟩] at h
  exact h

def cutOpenRetract (hext : G.externalCount = 0) : C(G.cutOpen ∅, G.cutCarrier.Carrier) :=
  ⟨fun y => (G.interiorDiffeomorph.symm ⟨y.1, G.mem_interiorImage hext y.2⟩ :
      G.cutCarrier.interior).1,
    continuous_subtype_val.comp (G.interiorDiffeomorph.symm.continuous.comp
      (continuous_subtype_val.subtype_mk _))⟩

theorem cutOpenRetract_cutMap (hext : G.externalCount = 0) {x : G.cutCarrier.Carrier}
    (hx : G.cutCarrier.model.IsInteriorPoint x) (hy : G.cutMap x ∈ G.cutOpen ∅) :
    G.cutOpenRetract hext ⟨G.cutMap x, hy⟩ = x := by
  have h : (⟨G.cutMap x, G.mem_interiorImage hext hy⟩ : G.interiorImage) =
      G.interiorDiffeomorph ⟨x, hx⟩ := Subtype.ext (G.interior_map ⟨x, hx⟩).symm
  change (G.interiorDiffeomorph.symm ⟨G.cutMap x, G.mem_interiorImage hext hy⟩ :
    G.cutCarrier.interior).1 = x
  rw [h, Diffeomorph.symm_apply_apply]

theorem halfPoint_mem_source (s : G.Side) (t : Torus) {c : ℝ} (hc : 0 ≤ c ∧ c < 1) :
    (t, halfPoint c hc.1) ∈ (G.sideCollar s).source := by
  rw [G.sideCollar_source]
  exact hc.2

def sideLevel (s : G.Side) (c : ℝ) (hc : 0 ≤ c ∧ c < 1) : C(Torus, G.cutCarrier.Carrier) :=
  ⟨fun t => G.sideCollar s (t, halfPoint c hc.1),
    (G.sideCollar s).contMDiffOn.continuousOn.comp_continuous (by fun_prop)
      fun t => G.halfPoint_mem_source s t hc⟩

def pieceLevel (s : G.Side) (c : ℝ) (hc : 0 ≤ c ∧ c < 1) :
    C(Torus, G.components.piece (G.sidePiece s)) :=
  ⟨fun t => ⟨G.sideLevel s c hc t, G.sideCollar_target_subset s
      ((G.sideCollar s).map_source' (G.halfPoint_mem_source s t hc))⟩,
    (G.sideLevel s c hc).continuous.subtype_mk _⟩

private theorem mul_mem_unit {c : ℝ} (hc : 0 ≤ c ∧ c < 1) (τ : unitInterval) :
    0 ≤ (1 - (τ : ℝ)) * c ∧ (1 - (τ : ℝ)) * c < 1 := by
  have h0 := τ.2.1
  have h1 := τ.2.2
  constructor <;> nlinarith [hc.1, hc.2]

def pieceLevelHomotopy (s : G.Side) (c : ℝ) (hc : 0 ≤ c ∧ c < 1) :
    (G.pieceLevel s c hc).Homotopy (G.pieceLevel s 0 ⟨le_rfl, one_pos⟩) where
  toFun z := ⟨G.sideCollar s (z.2, halfPoint ((1 - (z.1 : ℝ)) * c) (mul_mem_unit hc z.1).1),
    G.sideCollar_target_subset s ((G.sideCollar s).map_source'
      (G.halfPoint_mem_source s z.2 (mul_mem_unit hc z.1)))⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ((G.sideCollar s).contMDiffOn.continuousOn.comp_continuous
      (continuous_snd.prodMk (Continuous.subtype_mk (by fun_prop) _))
      fun z => G.halfPoint_mem_source s z.2 (mul_mem_unit hc z.1)) _
  map_zero_left t := by
    apply Subtype.ext
    change G.sideCollar s (t, halfPoint ((1 - 0) * c) _) = G.sideCollar s (t, halfPoint c _)
    congr 2
    exact Subtype.ext (by simp [halfPoint])
  map_one_left t := by
    apply Subtype.ext
    change G.sideCollar s (t, halfPoint ((1 - 1) * c) _) = G.sideCollar s (t, halfPoint 0 _)
    congr 2
    exact Subtype.ext (by simp [halfPoint])

theorem injective_pieceLevel_zero (s : G.Side)
    (hports : (G.pieceBoundaryTori (G.sidePiece s)).incompressible) (t : Torus) :
    Function.Injective (FundamentalGroup.map (G.pieceLevel s 0 ⟨le_rfl, one_pos⟩) t) := by
  have h := hports (Fintype.equivFin _ ⟨s, rfl⟩) t
  have he : (G.pieceBoundaryTori (G.sidePiece s)).boundaryMap (Fintype.equivFin _ ⟨s, rfl⟩) =
      G.pieceLevel s 0 ⟨le_rfl, one_pos⟩ := by
    refine ContinuousMap.ext fun t' => Subtype.ext ?_
    refine (G.pieceBoundaryTori_torusMap _ _ t').trans ?_
    rw [Equiv.symm_apply_apply]
    rfl
  rwa [he] at h

theorem injective_sideLevel (s : G.Side)
    (hports : (G.pieceBoundaryTori (G.sidePiece s)).incompressible) (c : ℝ)
    (hc : 0 ≤ c ∧ c < 1) (t : Torus) :
    Function.Injective (FundamentalGroup.map (G.sideLevel s c hc) t) := by
  have h1 := injective_fundamentalGroup_map_of_homotopy (G.pieceLevelHomotopy s c hc) t
    (G.injective_pieceLevel_zero s hports t)
  have h2 := injective_subsetToAmbient_of_isClopen
    ((G.components.piece (G.sidePiece s) : Set G.cutCarrier.Carrier))
    ⟨G.components.closed _, (G.components.piece _).isOpen⟩ (G.pieceLevel s c hc t)
  have hc' := h2.comp h1
  rw [← MonoidHom.coe_comp, ← GC.Topology.fundamentalGroup_map_comp] at hc'
  exact hc'

theorem injInto_cutOpen_empty_levelNeg (hext : G.externalCount = 0)
    (hports : ∀ i, (G.pieceBoundaryTori i).incompressible) (k : Fin G.pairing.count) :
    InjInto (G.cutOpen ∅) (G.levelNeg k) := by
  have hmem := fun t => G.levelMap_mem_cutOpen k (-2⁻¹) ⟨by norm_num, by norm_num⟩
    (by norm_num) ∅ t
  refine ⟨hmem, fun t => ?_⟩
  apply GC.Topology.injective_inner_of_composite _ (G.cutOpenRetract hext) t
  have he : (G.cutOpenRetract hext).comp (toSubset (G.levelNeg k) (G.cutOpen ∅) hmem) =
      G.sideLevel (.inl k) 2⁻¹ ⟨by norm_num, by norm_num⟩ := by
    refine ContinuousMap.ext fun t' => ?_
    have hp : (t', halfPoint 2⁻¹ (by norm_num)) ∈ halfCollarSource := by
      change (2⁻¹ : ℝ) < 1
      norm_num
    have hc : G.levelNeg k t' =
        G.cutMap (G.pairing.leftCollar k (t', halfPoint 2⁻¹ (by norm_num))) :=
      (G.cutMap_leftCollar k hp).symm
    have hx := G.isInteriorPoint_of_forall_not_mem hext (x := G.pairing.leftCollar k
      (t', halfPoint 2⁻¹ (by norm_num))) fun k' => by
        rw [← hc]
        exact G.not_mem_seamSurface_of_mem_cutOpen_empty (hmem t') k'
    have hm : G.cutMap (G.pairing.leftCollar k (t', halfPoint 2⁻¹ (by norm_num))) ∈
        G.cutOpen ∅ := hc ▸ hmem t'
    change G.cutOpenRetract hext ⟨G.levelNeg k t', hmem t'⟩ = _
    rw [show (⟨G.levelNeg k t', hmem t'⟩ : G.cutOpen ∅) = ⟨_, hm⟩ from Subtype.ext hc,
      G.cutOpenRetract_cutMap hext hx hm]
    rfl
  rw [he]
  exact G.injective_sideLevel (.inl k) (hports _) _ _ t

theorem injInto_cutOpen_empty_levelPos (hext : G.externalCount = 0)
    (hports : ∀ i, (G.pieceBoundaryTori i).incompressible) (k : Fin G.pairing.count) :
    InjInto (G.cutOpen ∅) (G.levelPos k) := by
  have hmem := fun t => G.levelMap_mem_cutOpen k 2⁻¹ ⟨by norm_num, by norm_num⟩
    (by norm_num) ∅ t
  refine ⟨hmem, fun t => ?_⟩
  apply GC.Topology.injective_inner_of_composite _ (G.cutOpenRetract hext) t
  have he : (G.cutOpenRetract hext).comp (toSubset (G.levelPos k) (G.cutOpen ∅) hmem) =
      (G.sideLevel (.inr (.inl k)) 2⁻¹ ⟨by norm_num, by norm_num⟩).comp
        ((G.pairing.matching k).toHomeomorph : C(Torus, Torus)) := by
    refine ContinuousMap.ext fun t' => ?_
    have hc : G.levelPos k t' = G.cutMap (G.pairing.rightCollar k
        (G.pairing.matching k t', halfPoint 2⁻¹ (by norm_num))) :=
      G.seam_positive k t' 2⁻¹ (by norm_num) (by norm_num)
    have hx := G.isInteriorPoint_of_forall_not_mem hext (x := G.pairing.rightCollar k
      (G.pairing.matching k t', halfPoint 2⁻¹ (by norm_num))) fun k' => by
        rw [← hc]
        exact G.not_mem_seamSurface_of_mem_cutOpen_empty (hmem t') k'
    have hm : G.cutMap (G.pairing.rightCollar k
        (G.pairing.matching k t', halfPoint 2⁻¹ (by norm_num))) ∈ G.cutOpen ∅ := hc ▸ hmem t'
    change G.cutOpenRetract hext ⟨G.levelPos k t', hmem t'⟩ = _
    rw [show (⟨G.levelPos k t', hmem t'⟩ : G.cutOpen ∅) = ⟨_, hm⟩ from Subtype.ext hc,
      G.cutOpenRetract_cutMap hext hx hm]
    rfl
  rw [he, GC.Topology.fundamentalGroup_map_comp, MonoidHom.coe_comp]
  exact (G.injective_sideLevel (.inr (.inl k)) (hports _) _ _ _).comp
    (injective_fundamentalGroup_map_of_leftInverse
      (((G.pairing.matching k).toHomeomorph : Torus ≃ₜ Torus) : C(Torus, Torus))
      (((G.pairing.matching k).toHomeomorph.symm : Torus ≃ₜ Torus) : C(Torus, Torus))
      (G.pairing.matching k).toHomeomorph.symm_apply_apply t)

theorem seamLevelsInj_empty (hext : G.externalCount = 0)
    (hports : ∀ i, (G.pieceBoundaryTori i).incompressible) : G.SeamLevelsInj ∅ :=
  fun k => ⟨G.injInto_cutOpen_empty_levelNeg hext hports k,
    G.injInto_cutOpen_empty_levelPos hext hports k⟩

end Base

theorem seamLevelsInj_univ (h0 : G.SeamLevelsInj ∅) : G.SeamLevelsInj Finset.univ := by
  have key : ∀ K : Finset (Fin G.pairing.count), G.SeamLevelsInj K := by
    intro K
    induction K using Finset.induction_on with
    | empty => exact h0
    | insert j K hj ih =>
      exact fun k => ⟨injInto_insert hj ih _ (ih k).1, injInto_insert hj ih _ (ih k).2⟩
  exact key _

theorem injective_levelNeg_of_univ (h : G.SeamLevelsInj Finset.univ) (k : Fin G.pairing.count)
    (t : Torus) : Function.Injective (FundamentalGroup.map (G.levelNeg k) t) := by
  exact (h k).1.injective_of_eq_univ G.cutOpen_univ t

theorem injective_seamTorus_of_levelNeg (k : Fin G.pairing.count)
    (h : ∀ t, Function.Injective (FundamentalGroup.map (G.levelNeg k) t)) (t : Torus) :
    Function.Injective (FundamentalGroup.map (G.seamTorus k) t) := by
  have hV : PathConnectedSpace ↑(G.seamCollar k) :=
    isPathConnected_iff_pathConnectedSpace.mp (G.isPathConnected_seamCollar k)
  have hmem := fun t => G.levelMap_mem_seamCollar k (-2⁻¹) ⟨by norm_num, by norm_num⟩ t
  have h1 : Function.Injective (FundamentalGroup.map ((subsetToAmbient (G.seamCollar k)).comp
      (toSubset (G.levelNeg k) (G.seamCollar k) hmem)) (1, 1)) := h (1, 1)
  have h3 := injective_fundamentalGroup_map_of_comp _ _ (1, 1)
    (G.bijective_collar_gapLevel k (-2⁻¹) ⟨by norm_num, by norm_num⟩ (by norm_num) (1, 1)).2 h1
  have h4 := (GC.Topology.injective_fundamentalGroup_map_iff (subsetToAmbient (G.seamCollar k)) _
    (G.seamTorusIn k (G.seamCollar k) le_rfl (1, 1))).mp h3
  have h5 : Function.Injective (FundamentalGroup.map ((subsetToAmbient (G.seamCollar k)).comp
      (G.seamTorusIn k (G.seamCollar k) le_rfl)) (1, 1)) := by
    rw [GC.Topology.fundamentalGroup_map_comp, MonoidHom.coe_comp]
    exact h4.comp (G.bijective_seamTorusIn k (G.seamCollar k) rfl (1, 1)).1
  rw [GC.Topology.injective_fundamentalGroup_map_iff (G.seamTorus k) t (1, 1)]
  exact h5

theorem injective_seamTorus_of_ports (hext : G.externalCount = 0)
    (hports : ∀ i, (G.pieceBoundaryTori i).incompressible) (k : Fin G.pairing.count)
    (t : Torus) : Function.Injective (FundamentalGroup.map (G.seamTorus k) t) :=
  G.injective_seamTorus_of_levelNeg k
    (G.injective_levelNeg_of_univ (G.seamLevelsInj_univ (G.seamLevelsInj_empty hext hports)) k)
    t

section Closed
variable {P : ConnectedClosedOrientedManifold.{u} 3} (T : TorusPresentation (NoCuts.carrier P))

theorem incompressible_toTorusDecomposition_of_ports
    (hports : ∀ i, (T.pieceBoundaryTori i).incompressible) :
    T.toTorusDecomposition.reconstructionAtlas.Incompressible
      T.toTorusDecomposition.reconstruction := by
  intro i x
  rw [T.toTorusDecomposition_torusInPrime_eq i]
  exact T.injective_seamTorus_of_ports T.externalCount_eq_zero hports i x

end Closed

end TorusPresentation

end GC.Seifert
