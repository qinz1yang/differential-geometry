/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.MoiseChain
import DifferentialGeometry.Topology.Homotopy.ConvexProduct
import Mathlib.Topology.Piecewise

open Set
open scoped ContinuousMap

namespace DifferentialGeometry.Topology.PiecewiseLinear

private abbrev ShellCircle := Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1
private abbrev ShellModel := (ShellCircle × ShellCircle) × Set.Icc (0 : ℝ) 1

private theorem frontier_eq_inter_closure_diff
    {S₁ S₂ : Set (EuclideanSpace ℝ (Fin 3))}
    (hS₁ : IsClosed S₁) (hsub : S₁ ⊆ interior S₂) :
    frontier S₁ = S₁ ∩ closure (S₂ \ S₁) := by
  apply Set.Subset.antisymm
  · intro x hx
    rw [frontier_eq_closure_inter_closure] at hx
    have hxS₁ : x ∈ S₁ := hS₁.closure_eq ▸ hx.1
    refine ⟨hxS₁, ?_⟩
    rw [mem_closure_iff]
    intro U hU hxU
    have hxint : x ∈ interior S₂ := hsub hxS₁
    have hU' : IsOpen (U ∩ interior S₂) := hU.inter isOpen_interior
    have hxU' : x ∈ U ∩ interior S₂ := ⟨hxU, hxint⟩
    obtain ⟨y, hyU, hyc⟩ := mem_closure_iff.mp hx.2 (U ∩ interior S₂) hU' hxU'
    exact ⟨y, hyU.1, ⟨interior_subset hyU.2, hyc⟩⟩
  · intro x hx
    have hxS₁ : x ∈ S₁ := hx.1
    have hxX : x ∈ closure (S₂ \ S₁) := hx.2
    rw [frontier_eq_closure_inter_closure]
    refine ⟨subset_closure hxS₁, ?_⟩
    exact closure_mono (by
      intro y hy
      exact hy.2) hxX

private theorem solidTorus_union_shell
    {S₁ S₂ : Set (EuclideanSpace ℝ (Fin 3))}
    (hS₂ : IsClosed S₂) (hsub : S₁ ⊆ interior S₂) :
    S₂ = S₁ ∪ closure (S₂ \ S₁) := by
  apply Set.Subset.antisymm
  · intro x hx
    by_cases h₁ : x ∈ S₁
    · exact Or.inl h₁
    · exact Or.inr (subset_closure ⟨hx, h₁⟩)
  · intro x hx
    obtain hx | hx := hx
    · exact interior_subset (hsub hx)
    · exact closure_minimal (fun y hy => hy.1) hS₂ hx

open Classical in
private theorem shell_projection_eq_self_on_frontier
    {S₁ S₂ : Set (EuclideanSpace ℝ (Fin 3))}
    (hfrontier : frontier S₁ = S₁ ∩ closure (S₂ \ S₁))
    (φ : ShellModel ≃ₜ closure (S₂ \ S₁))
    (h0 : frontier S₁ = Subtype.val '' (φ '' {p | (p.2 : ℝ) = 0}))
    (z : Set.Icc (0 : ℝ) 1) (hz : (z : ℝ) = 0) :
    ∀ (x : EuclideanSpace ℝ (Fin 3)) (hx : x ∈ frontier S₁),
      (φ ((φ.symm (⟨x, hfrontier ▸ hx |>.2⟩ : closure (S₂ \ S₁))).1, z) :
        EuclideanSpace ℝ (Fin 3)) = x := by
  intro x hx
  have hxX : x ∈ closure (S₂ \ S₁) := (hfrontier ▸ hx).2
  obtain ⟨y, ⟨q, hq, hqφ⟩, hxy⟩ := h0 ▸ hx
  have hy : y = (⟨x, hxX⟩ : closure (S₂ \ S₁)) := by
    apply Subtype.ext
    exact hxy
  have hqeq : q = φ.symm (⟨x, hxX⟩ : closure (S₂ \ S₁)) := by
    apply φ.injective
    rw [φ.apply_symm_apply]
    exact hqφ.trans hy
  have hqzero : (q.2 : ℝ) = 0 := hq
  have hqz : q.2 = z := Subtype.ext (hqzero.trans hz.symm)
  have harg : ((φ.symm (⟨x, hxX⟩ : closure (S₂ \ S₁))).1, z) = q := by
    apply Prod.ext
    · exact (congrArg Prod.fst hqeq).symm
    · exact hqz.symm
  change (φ ((φ.symm (⟨x, hxX⟩ : closure (S₂ \ S₁))).1, z) :
    EuclideanSpace ℝ (Fin 3)) = x
  rw [harg]
  exact (congrArg Subtype.val hqφ).trans hxy

open Classical in
private theorem shell_coordinate_zero_on_frontier
    {S₁ S₂ : Set (EuclideanSpace ℝ (Fin 3))}
    (hfrontier : frontier S₁ = S₁ ∩ closure (S₂ \ S₁))
    (φ : ShellModel ≃ₜ closure (S₂ \ S₁))
    (h0 : frontier S₁ = Subtype.val '' (φ '' {p | (p.2 : ℝ) = 0}))
    (z : Set.Icc (0 : ℝ) 1) (hz : (z : ℝ) = 0)
    (x : EuclideanSpace ℝ (Fin 3)) (hx : x ∈ frontier S₁) :
    (φ.symm (⟨x, hfrontier ▸ hx |>.2⟩ : closure (S₂ \ S₁))).2 = z := by
  have hxX : x ∈ closure (S₂ \ S₁) := (hfrontier ▸ hx).2
  obtain ⟨y, ⟨q, hq, hqφ⟩, hxy⟩ := h0 ▸ hx
  have hy : y = (⟨x, hxX⟩ : closure (S₂ \ S₁)) := by
    apply Subtype.ext
    exact hxy
  have hqeq : q = φ.symm (⟨x, hxX⟩ : closure (S₂ \ S₁)) := by
    apply φ.injective
    rw [φ.apply_symm_apply]
    exact hqφ.trans hy
  apply Subtype.ext
  have hqzero : (q.2 : ℝ) = 0 := hq
  have hzero : ((φ.symm (⟨x, hxX⟩ : closure (S₂ \ S₁))).2 : ℝ) = 0 := by
    rw [← congrArg Prod.snd hqeq]
    exact hqzero
  exact hzero.trans hz.symm

open Classical in
theorem homotopyEquiv_inclusion_of_isToroidalShell
    {S₁ S₂ : Set (EuclideanSpace ℝ (Fin 3))}
    (hS₁ : IsClosed S₁) (hS₂ : IsClosed S₂)
    (hsub : S₁ ⊆ interior S₂)
    (hshell : IsToroidalShell (closure (S₂ \ S₁)) (frontier S₁) (frontier S₂)) :
    ∃ (e : S₂ ≃ₕ S₁), Function.LeftInverse e
      (⟨Set.inclusion (show S₁ ⊆ S₂ from fun _x hx => interior_subset (hsub hx)),
        continuous_inclusion (show S₁ ⊆ S₂ from fun _x hx => interior_subset (hsub hx))⟩ :
        C(S₁, S₂)) := by
  obtain ⟨φ, h0, -⟩ := hshell
  let X : Set (EuclideanSpace ℝ (Fin 3)) := closure (S₂ \ S₁)
  let U : Set (EuclideanSpace ℝ (Fin 3)) := S₁ ∪ X
  let hfrontier : frontier S₁ = S₁ ∩ X := by
    exact frontier_eq_inter_closure_diff hS₁ hsub
  let hunion : S₂ = U := by
    exact solidTorus_union_shell hS₂ hsub
  let z : Set.Icc (0 : ℝ) 1 := ⟨0, by constructor <;> norm_num⟩
  let g₀ : C(X, EuclideanSpace ℝ (Fin 3)) :=
    { toFun := fun x => (φ ((φ.symm x).1, z) : EuclideanSpace ℝ (Fin 3))
      continuous_toFun := by fun_prop }
  have hg₀ : ∀ x, g₀ x ∈ frontier S₁ := by
    intro x
    rw [h0]
    exact ⟨φ ((φ.symm x).1, z), ⟨((φ.symm x).1, z), rfl, rfl⟩, rfl⟩
  let f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) := fun x =>
    if hx : x ∈ X then g₀ ⟨x, hx⟩ else x
  have hfX : ContinuousOn f X := by
    rw [continuousOn_iff_continuous_domRestrict]
    have heq : X.domRestrict f = g₀ := by
      apply funext
      intro x
      change f (x : EuclideanSpace ℝ (Fin 3)) = g₀ x
      simp [f]
    rw [heq]
    exact g₀.continuous
  let F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) :=
    Set.piecewise S₁ id f
  have hFcontU : ContinuousOn F U := by
    apply ContinuousOn.piecewise (s := U) (t := S₁)
    · intro x hx
      have hxfront : x ∈ frontier S₁ := hx.2
      have hxX : x ∈ X := (hfrontier ▸ hxfront).2
      have hfx : f x = g₀ ⟨x, hxX⟩ := by simp [f, hxX]
      rw [hfx]
      exact (shell_projection_eq_self_on_frontier hfrontier φ h0 z rfl x hxfront).symm
    · exact continuous_id.continuousOn
    · have hUX : U ∩ closure S₁ᶜ ⊆ X := by
        intro x hx
        obtain hxS₁ | hxX := hx.1
        · have hxfront : x ∈ frontier S₁ := by
            rw [frontier_eq_closure_inter_closure]
            exact ⟨subset_closure hxS₁, hx.2⟩
          exact (hfrontier ▸ hxfront).2
        · exact hxX
      exact hfX.mono hUX
  have hFmap : ∀ x ∈ U, F x ∈ S₁ := by
    intro x hx
    by_cases hxS₁ : x ∈ S₁
    · simp [F, hxS₁]
    · obtain hxX | hxX := hx
      · exact False.elim (hxS₁ hxX)
      · have hfx : f x = g₀ ⟨x, hxX⟩ := by simp [f, hxX]
        rw [show F x = f x by simp [F, hxS₁], hfx]
        exact frontier_subset_iff_isClosed.mpr hS₁ (hg₀ _)
  have hFcontS₂ : ContinuousOn F S₂ := by
    rw [hunion]
    exact hFcontU
  let hS₁S₂ : S₁ ⊆ S₂ := fun x hx => interior_subset (hsub hx)
  let i : C(S₁, S₂) :=
    ⟨Set.inclusion hS₁S₂, continuous_inclusion hS₁S₂⟩
  let r : C(S₂, S₁) :=
    { toFun := fun x => ⟨F x, hFmap x.1 (hunion ▸ x.property)⟩
      continuous_toFun := (continuousOn_iff_continuous_domRestrict.mp hFcontS₂).subtype_mk _ }
  have hri : Function.LeftInverse r i := by
    intro x
    apply Subtype.ext
    change F (x : EuclideanSpace ℝ (Fin 3)) = x
    simp [F]
  let lerp : Set.Icc (0 : ℝ) 1 → Set.Icc (0 : ℝ) 1 →
      Set.Icc (0 : ℝ) 1 → Set.Icc (0 : ℝ) 1 := fun a b t =>
    ⟨AffineMap.lineMap (a : ℝ) (b : ℝ) (t : ℝ),
      (convex_Icc (0 : ℝ) 1).lineMap_mem a.property b.property t.property⟩
  let H : C(Set.Icc (0 : ℝ) 1 × X, EuclideanSpace ℝ (Fin 3)) :=
    { toFun := fun p =>
        (φ ((φ.symm p.2).1, lerp z (φ.symm p.2).2 p.1) :
          EuclideanSpace ℝ (Fin 3))
      continuous_toFun := by fun_prop }
  let eProd : (Set.Icc (0 : ℝ) 1 × X) ≃ₜ
      ((Set.univ : Set (Set.Icc (0 : ℝ) 1)) ×ˢ X) :=
    { toFun := fun p =>
        ⟨(p.1, (p.2 : EuclideanSpace ℝ (Fin 3))),
          ⟨Set.mem_univ _, p.2.property⟩⟩
      invFun := fun p =>
        (p.1.1, ⟨p.1.2, p.property.2⟩)
      left_inv := by intro p; rfl
      right_inv := by intro p; apply Subtype.ext; rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  let Hf : Set.Icc (0 : ℝ) 1 × EuclideanSpace ℝ (Fin 3) →
      EuclideanSpace ℝ (Fin 3) := fun p =>
    if hx : p.2 ∈ X then H ⟨p.1, ⟨p.2, hx⟩⟩ else p.2
  have hHf : ContinuousOn Hf ((Set.univ : Set (Set.Icc (0 : ℝ) 1)) ×ˢ X) := by
    rw [continuousOn_iff_continuous_domRestrict]
    let eProdInv : C(((Set.univ : Set (Set.Icc (0 : ℝ) 1)) ×ˢ X),
        Set.Icc (0 : ℝ) 1 × X) :=
      ⟨eProd.symm, eProd.symm.continuous⟩
    let Hsub : C(((Set.univ : Set (Set.Icc (0 : ℝ) 1)) ×ˢ X),
        EuclideanSpace ℝ (Fin 3)) := H.comp eProdInv
    have heq : ((Set.univ : Set (Set.Icc (0 : ℝ) 1)) ×ˢ X).domRestrict Hf = Hsub := by
      apply funext
      intro p
      change Hf (p : Set.Icc (0 : ℝ) 1 × EuclideanSpace ℝ (Fin 3)) = Hsub p
      have hpX : ((p : ((Set.univ : Set (Set.Icc (0 : ℝ) 1)) ×ˢ X)) :
          Set.Icc (0 : ℝ) 1 × EuclideanSpace ℝ (Fin 3)).2 ∈ X := p.property.2
      dsimp [Hsub, eProdInv]
      change Hf (p : Set.Icc (0 : ℝ) 1 × EuclideanSpace ℝ (Fin 3)) = H (eProd.symm p)
      rw [show Hf (p : Set.Icc (0 : ℝ) 1 × EuclideanSpace ℝ (Fin 3)) =
          H ((p : Set.Icc (0 : ℝ) 1 × EuclideanSpace ℝ (Fin 3)).1,
            ⟨(p : Set.Icc (0 : ℝ) 1 × EuclideanSpace ℝ (Fin 3)).2, hpX⟩) by
        simp [Hf, hpX]]
      congr 1
    rw [heq]
    exact Hsub.continuous
  have hXsub : X ⊆ S₂ := by
    exact closure_minimal (fun y hy => hy.1) hS₂
  let A : Set (Set.Icc (0 : ℝ) 1 × EuclideanSpace ℝ (Fin 3)) :=
    (Set.univ : Set (Set.Icc (0 : ℝ) 1)) ×ˢ S₁
  let W : Set (Set.Icc (0 : ℝ) 1 × EuclideanSpace ℝ (Fin 3)) :=
    (Set.univ : Set (Set.Icc (0 : ℝ) 1)) ×ˢ U
  have hWA : W = A ∪ ((Set.univ : Set (Set.Icc (0 : ℝ) 1)) ×ˢ X) := by
    ext p
    simp only [W, A, mem_prod, mem_univ, true_and, mem_union]
    constructor
    · intro hp
      exact hp.elim Or.inl Or.inr
    · intro hp
      exact hp
  let K : Set.Icc (0 : ℝ) 1 × EuclideanSpace ℝ (Fin 3) →
      EuclideanSpace ℝ (Fin 3) := Set.piecewise A (fun p => p.2) Hf
  have hKcontW : ContinuousOn K W := by
    apply ContinuousOn.piecewise (s := W) (t := A)
    · intro p hp
      have hpfront : p ∈ frontier A := hp.2
      rw [frontier_prod_eq] at hpfront
      have hp2 : p.2 ∈ frontier S₁ := by
        simpa [A] using hpfront
      have hpX : p.2 ∈ X := (hfrontier ▸ hp2).2
      have hzero : lerp z z p.1 = z := by
        apply Subtype.ext
        simp [lerp]
      have hH : H ⟨p.1, ⟨p.2, hpX⟩⟩ = p.2 := by
        change (φ ((φ.symm (⟨p.2, hpX⟩ : X)).1,
          lerp z (φ.symm (⟨p.2, hpX⟩ : X)).2 p.1) :
            EuclideanSpace ℝ (Fin 3)) = p.2
        rw [shell_coordinate_zero_on_frontier hfrontier φ h0 z rfl p.2 hp2]
        have hzero : lerp z z p.1 = z := by
          apply Subtype.ext
          simp [lerp]
        rw [hzero]
        exact shell_projection_eq_self_on_frontier hfrontier φ h0 z rfl p.2 hp2
      change p.2 = Hf p
      rw [show Hf p = H ⟨p.1, ⟨p.2, hpX⟩⟩ by simp [Hf, hpX], hH]
    · exact continuous_snd.continuousOn
    · have hWAcomp : W ∩ closure Aᶜ ⊆
          (Set.univ : Set (Set.Icc (0 : ℝ) 1)) ×ˢ X := by
        intro p hp
        have hAc : Aᶜ = (Set.univ : Set (Set.Icc (0 : ℝ) 1)) ×ˢ S₁ᶜ := by
          ext q
          simp [A]
        rw [hAc, closure_prod_eq] at hp
        obtain hpS₁ | hpX := hp.1.2
        · have hpfront : p.2 ∈ frontier S₁ := by
            rw [frontier_eq_closure_inter_closure]
            exact ⟨subset_closure hpS₁, hp.2.2⟩
          exact ⟨Set.mem_univ _, (hfrontier ▸ hpfront).2⟩
        · exact ⟨Set.mem_univ _, hpX⟩
      exact hHf.mono hWAcomp
  have hKmap : ∀ p ∈ W, K p ∈ S₂ := by
    intro p hp
    by_cases hpS₁ : p.2 ∈ S₁
    · rw [show K p = p.2 by simp [K, A, hpS₁]]
      exact hS₁S₂ hpS₁
    · have hpX : p.2 ∈ X := by
        obtain hpU := hp.2
        exact hpU.resolve_left hpS₁
      have hHX : H ⟨p.1, ⟨p.2, hpX⟩⟩ ∈ X := by
        change (φ ((φ.symm (⟨p.2, hpX⟩ : X)).1,
          lerp z (φ.symm (⟨p.2, hpX⟩ : X)).2 p.1) :
            EuclideanSpace ℝ (Fin 3)) ∈ X
        exact (φ _).property
      rw [show K p = Hf p by simp [K, A, hpS₁]]
      rw [show Hf p = H ⟨p.1, ⟨p.2, hpX⟩⟩ by simp [Hf, hpX]]
      exact hXsub hHX
  let P₂ : Set (Set.Icc (0 : ℝ) 1 × EuclideanSpace ℝ (Fin 3)) :=
    (Set.univ : Set (Set.Icc (0 : ℝ) 1)) ×ˢ S₂
  have hP₂W : P₂ ⊆ W := by
    intro p hp
    exact ⟨Set.mem_univ _, hunion ▸ hp.2⟩
  have hKcontP₂ : ContinuousOn K P₂ := hKcontW.mono hP₂W
  let eP₂ : (Set.Icc (0 : ℝ) 1 × S₂) ≃ₜ P₂ :=
    { toFun := fun p =>
        ⟨(p.1, (p.2 : EuclideanSpace ℝ (Fin 3))),
          ⟨Set.mem_univ _, p.2.property⟩⟩
      invFun := fun p =>
        (p.1.1, ⟨p.1.2, p.property.2⟩)
      left_inv := by intro p; rfl
      right_inv := by intro p; apply Subtype.ext; rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  let eP₂CM : C(Set.Icc (0 : ℝ) 1 × S₂, P₂) :=
    ⟨eP₂, eP₂.continuous⟩
  let KP₂ : C(P₂, EuclideanSpace ℝ (Fin 3)) :=
    ⟨P₂.domRestrict K, hKcontP₂.domRestrict⟩
  let K₂E : C(Set.Icc (0 : ℝ) 1 × S₂, EuclideanSpace ℝ (Fin 3)) :=
    KP₂.comp eP₂CM
  let K₂ : C(Set.Icc (0 : ℝ) 1 × S₂, S₂) :=
    { toFun := fun p =>
        ⟨K₂E p, hKmap (eP₂ p) (hP₂W (eP₂ p).property)⟩
      continuous_toFun := K₂E.continuous.subtype_mk _ }
  let t₀ : Set.Icc (0 : ℝ) 1 := ⟨0, by constructor <;> norm_num⟩
  let t₁ : Set.Icc (0 : ℝ) 1 := ⟨1, by constructor <;> norm_num⟩
  have hKzero : ∀ x : S₂, K (t₀, (x : EuclideanSpace ℝ (Fin 3))) = F x := by
    intro x
    by_cases hxS₁ : (x : EuclideanSpace ℝ (Fin 3)) ∈ S₁
    · simp [K, F, A, t₀, hxS₁]
    · have hxX : (x : EuclideanSpace ℝ (Fin 3)) ∈ X := by
        have hxU : (x : EuclideanSpace ℝ (Fin 3)) ∈ U := by
          rw [← hunion]
          exact x.property
        exact hxU.resolve_left hxS₁
      have hlerp : lerp z (φ.symm (⟨(x : EuclideanSpace ℝ (Fin 3)), hxX⟩ : X)).2 t₀ = z := by
        apply Subtype.ext
        simp [lerp, t₀]
      have hHzero : H ⟨t₀, ⟨(x : EuclideanSpace ℝ (Fin 3)), hxX⟩⟩ =
          g₀ ⟨(x : EuclideanSpace ℝ (Fin 3)), hxX⟩ := by
        change (φ ((φ.symm (⟨(x : EuclideanSpace ℝ (Fin 3)), hxX⟩ : X)).1,
          lerp z (φ.symm (⟨(x : EuclideanSpace ℝ (Fin 3)), hxX⟩ : X)).2 t₀) :
            EuclideanSpace ℝ (Fin 3)) = g₀ ⟨(x : EuclideanSpace ℝ (Fin 3)), hxX⟩
        rw [hlerp]
        rfl
      change K (t₀, (x : EuclideanSpace ℝ (Fin 3))) = F x
      rw [show K (t₀, (x : EuclideanSpace ℝ (Fin 3))) =
          Hf (t₀, (x : EuclideanSpace ℝ (Fin 3))) by simp [K, A, hxS₁]]
      rw [show Hf (t₀, (x : EuclideanSpace ℝ (Fin 3))) =
          H ⟨t₀, ⟨(x : EuclideanSpace ℝ (Fin 3)), hxX⟩⟩ by simp [Hf, hxX], hHzero]
      simp [F, f, hxS₁, hxX]
  have hKone : ∀ x : S₂, K (t₁, (x : EuclideanSpace ℝ (Fin 3))) = x := by
    intro x
    by_cases hxS₁ : (x : EuclideanSpace ℝ (Fin 3)) ∈ S₁
    · simp [K, t₁, A, hxS₁]
    · have hxX : (x : EuclideanSpace ℝ (Fin 3)) ∈ X := by
        have hxU : (x : EuclideanSpace ℝ (Fin 3)) ∈ U := by
          rw [← hunion]
          exact x.property
        exact hxU.resolve_left hxS₁
      have hlerp : lerp z (φ.symm (⟨(x : EuclideanSpace ℝ (Fin 3)), hxX⟩ : X)).2 t₁ =
          (φ.symm (⟨(x : EuclideanSpace ℝ (Fin 3)), hxX⟩ : X)).2 := by
        apply Subtype.ext
        simp [lerp, t₁]
      have hHone : H ⟨t₁, ⟨(x : EuclideanSpace ℝ (Fin 3)), hxX⟩⟩ = x := by
        change (φ ((φ.symm (⟨(x : EuclideanSpace ℝ (Fin 3)), hxX⟩ : X)).1,
          lerp z (φ.symm (⟨(x : EuclideanSpace ℝ (Fin 3)), hxX⟩ : X)).2 t₁) :
            EuclideanSpace ℝ (Fin 3)) = x
        rw [hlerp]
        exact congrArg Subtype.val (φ.apply_symm_apply
          (⟨(x : EuclideanSpace ℝ (Fin 3)), hxX⟩ : X))
      change K (t₁, (x : EuclideanSpace ℝ (Fin 3))) = x
      rw [show K (t₁, (x : EuclideanSpace ℝ (Fin 3))) =
          Hf (t₁, (x : EuclideanSpace ℝ (Fin 3))) by simp [K, A, hxS₁]]
      rw [show Hf (t₁, (x : EuclideanSpace ℝ (Fin 3))) =
          H ⟨t₁, ⟨(x : EuclideanSpace ℝ (Fin 3)), hxX⟩⟩ by simp [Hf, hxX], hHone]
  have hleft : (r.comp i).Homotopic (ContinuousMap.id S₁) := by
    have heq : r.comp i = ContinuousMap.id S₁ := by
      apply ContinuousMap.ext
      intro x
      exact hri x
    rw [heq]
  have hright : (i.comp r).Homotopic (ContinuousMap.id S₂) := by
    refine ⟨{
      toFun := fun p => K₂ p
      continuous_toFun := K₂.continuous_toFun
      map_zero_left := by
        intro x
        apply Subtype.ext
        change K (t₀, (x : EuclideanSpace ℝ (Fin 3))) =
          (i (r x) : EuclideanSpace ℝ (Fin 3))
        rw [hKzero]
        rfl
      map_one_left := by
        intro x
        apply Subtype.ext
        change K (t₁, (x : EuclideanSpace ℝ (Fin 3))) =
          (ContinuousMap.id S₂ x : EuclideanSpace ℝ (Fin 3))
        rw [hKone]
        rfl }⟩
  let e : S₂ ≃ₕ S₁ :=
    { toFun := r
      invFun := i
      left_inv := hright
      right_inv := hleft }
  refine ⟨e, ?_⟩
  simpa [e, i, hS₁S₂] using hri

end DifferentialGeometry.Topology.PiecewiseLinear
