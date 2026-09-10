/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.CategoryTheory.SingleObj
import DifferentialGeometry.Topology.VanKampen.FullGroupoid

set_option autoImplicit false

open CategoryTheory Set

universe u v

namespace Poincare.Topology.VanKampen

noncomputable def coverCycleLocalFunctorData
    {X : Type u} [TopologicalSpace X] (U V : Set X)
    {G : Type v} [Group G] (label : V → G)
    (hlabel : ∀ (x y : ↑(U ∩ V)) (_ : Path x y),
      label ⟨x.1, x.2.2⟩ = label ⟨y.1, y.2.2⟩) :
    LocalFunctorData U V (SingleObj G) where
  left := SingleObj.differenceFunctor (fun _ : FundamentalGroupoid U => 1)
  right := SingleObj.differenceFunctor (fun x : FundamentalGroupoid V => label x.as)
  compatibility := by
    apply Functor.hext
    · intro z
      exact Subsingleton.elim _ _
    · intro x y f
      rcases Path.Homotopic.Quotient.mk_surjective f with ⟨p, rfl⟩
      apply heq_of_eq
      have hxy := hlabel x.as y.as p
      change (1 : G) * 1⁻¹ =
        label ⟨y.as.1, y.as.2.2⟩ * (label ⟨x.as.1, x.as.2.2⟩)⁻¹
      rw [hxy]
      simp

theorem not_simplyConnectedSpace_of_cover_cycle
    {X : Type u} [TopologicalSpace X] (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    (x₀ x₁ : X) (hx₀U : x₀ ∈ U) (hx₁U : x₁ ∈ U)
    (hx₀V : x₀ ∈ V) (hx₁V : x₁ ∈ V)
    (pU : Path (⟨x₀, hx₀U⟩ : U) ⟨x₁, hx₁U⟩)
    (pV : Path (⟨x₀, hx₀V⟩ : V) ⟨x₁, hx₁V⟩)
    {G : Type v} [Group G] (label : V → G)
    (hlabel : ∀ (x y : ↑(U ∩ V)) (_ : Path x y),
      label ⟨x.1, x.2.2⟩ = label ⟨y.1, y.2.2⟩)
    (hne : label ⟨x₁, hx₁V⟩ * (label ⟨x₀, hx₀V⟩)⁻¹ ≠ 1) :
    ¬ SimplyConnectedSpace X := by
  intro hsc
  let _ : SimplyConnectedSpace X := hsc
  let F := coverCycleLocalFunctorData U V label hlabel
  let E := F.extension hU hV hcover
  let pUA : Path x₀ x₁ := pU.map continuous_subtype_val
  let pVA : Path x₀ x₁ := pV.map continuous_subtype_val
  have hpq : Path.Homotopic.Quotient.mk pUA = Path.Homotopic.Quotient.mk pVA :=
    Subsingleton.elim _ _
  have heq : E.map (Path.Homotopic.Quotient.mk pUA) =
      E.map (Path.Homotopic.Quotient.mk pVA) :=
    Functor.congr_map E hpq
  have hfunU := F.extension_comp_left hU hV hcover
  have hmapU := congrArg
    (fun H : CategoryTheory.Functor (FundamentalGroupoid U) (SingleObj G) =>
      H.map (Path.Homotopic.Quotient.mk pU)) hfunU
  have hfunV := F.extension_comp_right hU hV hcover
  have hmapV := congrArg
    (fun H : CategoryTheory.Functor (FundamentalGroupoid V) (SingleObj G) =>
      H.map (Path.Homotopic.Quotient.mk pV)) hfunV
  dsimp only [Functor.comp_map] at hmapU hmapV
  rw [FundamentalGroupoid.map_map, ← Path.Homotopic.Quotient.mk_map] at hmapU hmapV
  dsimp only [F, coverCycleLocalFunctorData] at hmapU hmapV
  simp only [SingleObj.differenceFunctor_map, inv_one, mul_one] at hmapU hmapV
  change E.map (Path.Homotopic.Quotient.mk
      (pU.map continuous_subtype_val)) = (1 : G) at hmapU
  change E.map (Path.Homotopic.Quotient.mk
      (pV.map continuous_subtype_val)) =
    label ⟨x₁, hx₁V⟩ * (label ⟨x₀, hx₀V⟩)⁻¹ at hmapV
  change E.map (Path.Homotopic.Quotient.mk pUA) = (1 : G) at hmapU
  change E.map (Path.Homotopic.Quotient.mk pVA) =
    label ⟨x₁, hx₁V⟩ * (label ⟨x₀, hx₀V⟩)⁻¹ at hmapV
  apply hne
  rw [← hmapV, ← heq, hmapU]

end Poincare.Topology.VanKampen
