/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Covering.FundamentalGroup.CoveringSquareInjective
import DifferentialGeometry.Topology.FundamentalGroup.MarkedFundamentalGroup

set_option autoImplicit false

namespace DifferentialGeometry.Topology

theorem injective_fundamentalGroup_map_of_eq {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f g : C(X, Y)} (hfg : f = g) (x : X)
    (hf : Function.Injective (FundamentalGroup.map f x)) :
    Function.Injective (FundamentalGroup.map g x) := by
  subst hfg
  exact hf

theorem injective_fundamentalGroup_map_of_comp_eq {T K H : Type*} [TopologicalSpace T]
    [TopologicalSpace K] [TopologicalSpace H] (k : C(T, K)) (i : C(K, H)) (slice : C(T, H))
    (hslice : ∀ x, i (k x) = slice x) (x₀ : T)
    (h : Function.Injective (FundamentalGroup.map slice x₀)) :
    Function.Injective (FundamentalGroup.map k x₀) := by
  have hEq : i.comp k = slice := ContinuousMap.ext hslice
  exact GC.Topology.injective_inner_of_composite k i x₀
    (injective_fundamentalGroup_map_of_eq hEq.symm x₀ h)

theorem injective_fundamentalGroup_map_of_conj {X Y X' Y' : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y']
    (f : C(X, Y)) (f' : C(X', Y')) (u : C(X', X)) (u' : C(X, X')) (v : C(Y, Y'))
    (v' : C(Y', Y)) (hu : Function.LeftInverse u' u) (hv : Function.LeftInverse v' v)
    (hconj : ∀ x, f' x = v (f (u x))) (x₀ : X')
    (hf : Function.Injective (FundamentalGroup.map f (u x₀))) :
    Function.Injective (FundamentalGroup.map f' x₀) := by
  have hEq : (v.comp f).comp u = f' := ContinuousMap.ext fun x => (hconj x).symm
  refine injective_fundamentalGroup_map_of_eq hEq x₀ ?_
  rw [GC.Topology.fundamentalGroup_map_comp, GC.Topology.fundamentalGroup_map_comp]
  exact ((injective_fundamentalGroup_map_of_leftInverse v v' hv (f (u x₀))).comp hf).comp
    (injective_fundamentalGroup_map_of_leftInverse u u' hu x₀)

theorem injective_fundamentalGroup_map_of_homeomorph_conj {X Y X' Y' : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y']
    (f : C(X, Y)) (f' : C(X', Y')) (eX : X ≃ₜ X') (eY : Y ≃ₜ Y')
    (hconj : ∀ x, f' (eX x) = eY (f x)) (x₀ : X) (x₀' : X') (hx : eX x₀ = x₀')
    (hf : Function.Injective (FundamentalGroup.map f x₀)) :
    Function.Injective (FundamentalGroup.map f' x₀') := by
  have hx' : eX.symm x₀' = x₀ :=
    (DFunLike.congr_arg eX.symm hx).symm.trans (eX.symm_apply_apply x₀)
  subst hx'
  exact injective_fundamentalGroup_map_of_conj f f' (eX.symm : C(X', X)) (eX : C(X, X'))
    (eY : C(Y, Y')) (eY.symm : C(Y', Y)) eX.apply_symm_apply eY.symm_apply_apply
    (fun x => (DFunLike.congr_arg f' (eX.apply_symm_apply x)).symm.trans
      (hconj (eX.symm x)))
    x₀' hf

theorem simplyConnectedSpace_connectedComponent_of_simplyConnectedSpace {L : Type*}
    [TopologicalSpace L] [SimplyConnectedSpace L] (s : L) :
    SimplyConnectedSpace (connectedComponent s) :=
  ((Homeomorph.setCongr (PreconnectedSpace.connectedComponent_eq_univ s)).trans
    (Homeomorph.Set.univ L)).toHomotopyEquiv.simplyConnectedSpace

theorem fundamentalGroup_map_injective_of_covering_square_of_surjective
    {L T E H : Type*} [TopologicalSpace L] [TopologicalSpace T]
    [TopologicalSpace E] [TopologicalSpace H]
    (q : C(L, T)) (p : C(E, H)) (i : C(T, H)) (j : C(L, E))
    (hq : IsCoveringMap q) (hp : IsCoveringMap p)
    (comm : ∀ z, p (j z) = i (q z)) (hj : Function.Injective j)
    [SimplyConnectedSpace L] (hqs : Function.Surjective q) (t : T) :
    Function.Injective (FundamentalGroup.map i t) := by
  obtain ⟨s, rfl⟩ := hqs t
  exact @fundamentalGroup_map_injective_of_covering_square L T E H _ _ _ _
    q p i j hq hp comm hj s (simplyConnectedSpace_connectedComponent_of_simplyConnectedSpace s)

theorem fundamentalGroup_subtype_map_injective_of_covering_preimage_of_lift
    {E H : Type*} [TopologicalSpace E] [TopologicalSpace H]
    (p : C(E, H)) (hp : IsCoveringMap p) (T : Set H)
    (hlift : ∀ t : T, ∃ s : p ⁻¹' T, p s = t ∧ SimplyConnectedSpace (connectedComponent s))
    (t : T) :
    Function.Injective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(T, H)) t) := by
  obtain ⟨s, hst, hsc⟩ := hlift t
  have ht : (⟨p s, s.property⟩ : T) = t := Subtype.ext hst
  subst ht
  exact @fundamentalGroup_subtype_map_injective_of_covering_preimage E H _ _ p hp T s hsc

theorem fundamentalGroup_subtype_map_injective_of_covering_image
    {E H : Type*} [TopologicalSpace E] [TopologicalSpace H]
    (p : C(E, H)) (hp : IsCoveringMap p) (S : Set E) (T : Set H) (hT : p '' S = T)
    (hS : ∀ x : p ⁻¹' T, (x : E) ∈ S → SimplyConnectedSpace (connectedComponent x))
    (t : T) :
    Function.Injective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(T, H)) t) := by
  refine fundamentalGroup_subtype_map_injective_of_covering_preimage_of_lift p hp T ?_ t
  intro t'
  have ht' : (t' : H) ∈ p '' S := by
    rw [hT]
    exact t'.property
  obtain ⟨s, hs, hst⟩ := ht'
  have hsT : s ∈ p ⁻¹' T := by
    rw [Set.mem_preimage, hst]
    exact t'.property
  exact ⟨⟨s, hsT⟩, hst, hS ⟨s, hsT⟩ hs⟩

theorem injective_fundamentalGroup_map_of_isEmbedding {X H : Type*} [TopologicalSpace X]
    [TopologicalSpace H] (σ : C(X, H)) (hσ : _root_.Topology.IsEmbedding σ) (x : X)
    (h : Function.Injective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(Set.range σ, H)) (hσ.toHomeomorph x))) :
    Function.Injective (FundamentalGroup.map σ x) := by
  have hEq : (⟨Subtype.val, continuous_subtype_val⟩ : C(Set.range σ, H)).comp
      (hσ.toHomeomorph : C(X, Set.range σ)) = σ :=
    ContinuousMap.ext fun _ => rfl
  refine injective_fundamentalGroup_map_of_eq hEq x ?_
  rw [GC.Topology.fundamentalGroup_map_comp]
  exact h.comp (injective_fundamentalGroup_map_of_leftInverse
    (hσ.toHomeomorph : C(X, Set.range σ)) (hσ.toHomeomorph.symm : C(Set.range σ, X))
    hσ.toHomeomorph.symm_apply_apply x)

theorem injective_fundamentalGroup_map_of_isEmbedding_of_eq_range {X H : Type*}
    [TopologicalSpace X] [TopologicalSpace H] (σ : C(X, H))
    (hσ : _root_.Topology.IsEmbedding σ) (A : Set H) (hA : A = Set.range σ) (x : X) (y : A)
    (hy : (y : H) = σ x)
    (h : Function.Injective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(A, H)) y)) :
    Function.Injective (FundamentalGroup.map σ x) := by
  subst hA
  have hyx : hσ.toHomeomorph x = y := Subtype.ext hy.symm
  subst hyx
  exact injective_fundamentalGroup_map_of_isEmbedding σ hσ x h

theorem injective_fundamentalGroup_map_of_covering_image_eq_range {E H X : Type*}
    [TopologicalSpace E] [TopologicalSpace H] [TopologicalSpace X]
    (p : C(E, H)) (hp : IsCoveringMap p) (S : Set E) (σ : C(X, H))
    (hσ : _root_.Topology.IsEmbedding σ) (hT : p '' S = Set.range σ)
    (hS : ∀ y : p ⁻¹' Set.range σ, (y : E) ∈ S →
      SimplyConnectedSpace (connectedComponent y))
    (x : X) :
    Function.Injective (FundamentalGroup.map σ x) :=
  injective_fundamentalGroup_map_of_isEmbedding σ hσ x
    (fundamentalGroup_subtype_map_injective_of_covering_image p hp S (Set.range σ) hT hS
      (hσ.toHomeomorph x))

end DifferentialGeometry.Topology
