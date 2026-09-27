/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.VanKampen.AmalgamatedProduct

open Set

namespace DifferentialGeometry.Topology

open VanKampen

theorem injective_fundamentalGroup_map_inter_of_open_cover
    {X : Type*} [TopologicalSpace X] (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    [PathConnectedSpace U] [PathConnectedSpace V] [PathConnectedSpace (↑(U ∩ V))]
    (x : X) (hx : x ∈ U ∩ V)
    (hleft : Function.Injective (fundamentalGroupInterToLeft U V x hx).hom)
    (hright : Function.Injective (fundamentalGroupInterToRight U V x hx).hom) :
    Function.Injective ((fundamentalGroupLeftToAmbient U x hx.1).hom.comp
      (fundamentalGroupInterToLeft U V x hx).hom) := by
  let φ := fundamentalGroupAmalgamation U V x hx
  have hφ : ∀ i, Function.Injective (φ i) := by
    intro i
    cases i with
    | false => exact hleft
    | true => exact hright
  let e := fundamentalGroupEquivAmalgamatedProduct U V hU hV hcover x hx
  have hvalue (q : FundamentalGroup (↑(U ∩ V)) (overlapBasepoint U V x hx)) :
      e (Monoid.PushoutI.base φ q) = (fundamentalGroupLeftToAmbient U x hx.1).hom
        ((fundamentalGroupInterToLeft U V x hx).hom q) := by
    calc
      e (Monoid.PushoutI.base φ q) = e
          ((fundamentalGroupAmalgamatedProductLeft U V x hx).hom
            ((fundamentalGroupInterToLeft U V x hx).hom q)) :=
        congrArg e (Monoid.PushoutI.of_apply_eq_base φ false q).symm
      _ = (fundamentalGroupLeftToAmbient U x hx.1).hom
          ((fundamentalGroupInterToLeft U V x hx).hom q) :=
        DFunLike.congr_fun
          (fundamentalGroupEquivAmalgamatedProduct_comp_left U V hU hV hcover x hx) _
  intro a b hab
  apply Monoid.PushoutI.base_injective hφ
  apply e.injective
  rwa [hvalue, hvalue]

theorem exists_nontrivial_fundamentalGroup_kernel_of_open_cover
    {X : Type*} [TopologicalSpace X] (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    [PathConnectedSpace U] [PathConnectedSpace V] [PathConnectedSpace (↑(U ∩ V))]
    (x : X) (hx : x ∈ U ∩ V)
    (g : FundamentalGroup (↑(U ∩ V)) (overlapBasepoint U V x hx)) (hg : g ≠ 1)
    (hnull : (fundamentalGroupLeftToAmbient U x hx.1).hom
      ((fundamentalGroupInterToLeft U V x hx).hom g) = 1) :
    (∃ a : FundamentalGroup (↑(U ∩ V)) (overlapBasepoint U V x hx),
      a ≠ 1 ∧ (fundamentalGroupInterToLeft U V x hx).hom a = 1) ∨
    (∃ a : FundamentalGroup (↑(U ∩ V)) (overlapBasepoint U V x hx),
      a ≠ 1 ∧ (fundamentalGroupInterToRight U V x hx).hom a = 1) := by
  by_contra h
  have hleft : Function.Injective (fundamentalGroupInterToLeft U V x hx).hom := by
    apply (injective_iff_map_eq_one _).mpr
    intro a ha
    by_contra hne
    exact h (Or.inl ⟨a, hne, ha⟩)
  have hright : Function.Injective (fundamentalGroupInterToRight U V x hx).hom := by
    apply (injective_iff_map_eq_one _).mpr
    intro a ha
    by_contra hne
    exact h (Or.inr ⟨a, hne, ha⟩)
  have hi := injective_fundamentalGroup_map_inter_of_open_cover U V hU hV hcover x hx hleft hright
  exact hg (hi (hnull.trans (map_one _).symm))

end DifferentialGeometry.Topology
