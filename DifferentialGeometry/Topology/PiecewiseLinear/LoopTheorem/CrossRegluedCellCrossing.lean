/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossRegluedCellFields
import DifferentialGeometry.Topology.PiecewiseLinear.SingularCrossingLocality
import DifferentialGeometry.Topology.PiecewiseLinear.SingularCrossingPrecomp

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

section CrossRegluedCrossing

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D H G : SingularTwoCell M} {BdM B : Set M}
  {A C U₁ U₂ U₃ P Q P' Q' A' : Set (EuclideanSpace ℝ (Fin 2))}
  {g f₁ f₂ h f₃ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}

theorem bijOn_crossRegluedPullback_inter_of_isOpen
    (hdomains : U₁ ∪ U₂ ∪ U₃ = D.domain) (hinter₁₂ : U₁ ∩ U₂ = A)
    (hinter₂₃ : U₂ ∩ U₃ = C) (hdisjoint₁₃ : Disjoint U₁ U₃)
    (hHdomain : H.domain = P ∪ Q) (hf₁ : IsPLHomeomorphOn f₁ P U₁)
    (hf₂ : IsPLHomeomorphOn f₂ Q U₂) (hf₂seam : f₂ '' (P ∩ Q) = C)
    (hGdomain : G.domain = P' ∪ Q') (hh : IsPLHomeomorphOn h P' H.domain)
    (hf₃ : IsPLHomeomorphOn f₃ Q' U₃) (hf₃seam : f₃ '' (P' ∩ Q') = C)
    {Ω Ω' : Set (EuclideanSpace ℝ (Fin 2))}
    (hmem : ∀ x ∈ G.domain, (crossRegluedPullback P' P h f₁ f₂ f₃ x ∈ Ω ↔ x ∈ Ω'))
    (hnotA : ∀ u ∈ D.domain ∩ Ω, u ∉ A) (hnotC : ∀ u ∈ D.domain ∩ Ω, u ∉ C) :
    BijOn (crossRegluedPullback P' P h f₁ f₂ f₃) (G.domain ∩ Ω') (D.domain ∩ Ω) := by
  have hmaps := mapsTo_crossRegluedPullback hdomains hHdomain hf₁ hf₂ hGdomain hh hf₃
  have htarget : ∀ x ∈ G.domain ∩ Ω',
      crossRegluedPullback P' P h f₁ f₂ f₃ x ∈ D.domain ∩ Ω :=
    fun x hx => ⟨hmaps hx.1, (hmem x hx.1).mpr hx.2⟩
  refine ⟨htarget, ?_, ?_⟩
  · intro x hx x' hx' hk
    exact eq_of_crossRegluedPullback_eq_of_notMem hinter₁₂ hinter₂₃ hdisjoint₁₃ hHdomain
      hf₁ hf₂ hf₂seam hGdomain hh hf₃ hx.1 hx'.1 hk (hnotA _ (htarget x hx))
  · intro u hu
    obtain ⟨x, hxG, hxu⟩ := exists_mem_crossRegluedPullback_eq hdomains hHdomain hf₁ hf₂
      hf₂seam hGdomain hh hf₃ hf₃seam hu.1 (hnotC u hu)
    exact ⟨x, ⟨hxG, (hmem x hxG).mp (by rw [hxu]; exact hu.2)⟩, hxu⟩

theorem isPiecewiseAffineOn_crossRegluedPullback_inter_of_isOpen
    (hinter₁₂ : U₁ ∩ U₂ = A) (hP : IsPLBall 2 P) (hQ : IsPLBall 2 Q)
    (hHdomain : H.domain = P ∪ Q) (hf₁ : IsPLHomeomorphOn f₁ P U₁)
    (hf₂ : IsPLHomeomorphOn f₂ Q U₂) (hf₁seam : f₁ '' (P ∩ Q) = A)
    (hA'def : A' = Function.invFunOn f₂ Q '' A) (hP' : IsPLBall 2 P')
    (hQ' : IsPLBall 2 Q') (hGdomain : G.domain = P' ∪ Q')
    (hh : IsPLHomeomorphOn h P' H.domain) (hf₃ : IsPLHomeomorphOn f₃ Q' U₃)
    (hhseam : h '' (P' ∩ Q') = A') {Ω : Set (EuclideanSpace ℝ (Fin 2))} (hΩ : IsOpen Ω)
    (hnotA : ∀ x ∈ G.domain ∩ Ω, crossRegluedPullback P' P h f₁ f₂ f₃ x ∉ A) :
    IsPiecewiseAffineOn (crossRegluedPullback P' P h f₁ f₂ f₃) (G.domain ∩ Ω) := by
  have hAU₂ : A ⊆ U₂ := fun w hw => (hinter₁₂.symm.subset hw).2
  have hA'Q : A' ⊆ Q := by
    rw [hA'def]
    rintro _ ⟨v, hv, rfl⟩
    exact hf₂.bijOn.surjOn.mapsTo_invFunOn (hAU₂ hv)
  have hf₂A' : f₂ '' A' = A := by
    rw [hA'def, ← image_comp]
    calc (f₂ ∘ Function.invFunOn f₂ Q) '' A = id '' A :=
          Set.image_congr fun v hv => hf₂.bijOn.invOn_invFunOn.2 (hAU₂ hv)
      _ = A := image_id A
  have hAiff : ∀ {w : EuclideanSpace ℝ (Fin 2)}, w ∈ P → (f₁ w ∈ A ↔ w ∈ P ∩ Q) := by
    intro w hw
    rw [← hf₁seam]
    exact hf₁.bijOn.injOn.mem_image_iff inter_subset_left hw
  have hA'iff : ∀ {w : EuclideanSpace ℝ (Fin 2)}, w ∈ Q → (f₂ w ∈ A ↔ w ∈ A') := by
    intro w hw
    rw [← hf₂A']
    exact hf₂.bijOn.injOn.mem_image_iff hA'Q hw
  have hhiff : ∀ {w : EuclideanSpace ℝ (Fin 2)}, w ∈ P' → (h w ∈ A' ↔ w ∈ P' ∩ Q') := by
    intro w hw
    rw [← hhseam]
    exact hh.bijOn.injOn.mem_image_iff inter_subset_left hw
  have hsheet : ∀ {w : EuclideanSpace ℝ (Fin 2)}, w ∈ P' → h w ∈ P ∪ Q := by
    intro w hw
    rw [← hHdomain]
    exact hh.bijOn.mapsTo hw
  have hPopen : IsOpen (Pᶜ : Set (EuclideanSpace ℝ (Fin 2))) :=
    hP.isPolyhedron.isClosed.isOpen_compl
  have hQopen : IsOpen (Qᶜ : Set (EuclideanSpace ℝ (Fin 2))) :=
    hQ.isPolyhedron.isClosed.isOpen_compl
  have hP'open : IsOpen (P'ᶜ : Set (EuclideanSpace ℝ (Fin 2))) :=
    hP'.isPolyhedron.isClosed.isOpen_compl
  have hQ'open : IsOpen (Q'ᶜ : Set (EuclideanSpace ℝ (Fin 2))) :=
    hQ'.isPolyhedron.isClosed.isOpen_compl
  have hconth : ContinuousOn h P' := hh.isPiecewiseAffineOn.continuousOn
  refine isPiecewiseAffineOn_of_locally ?_
  intro x hx
  by_cases hxP' : x ∈ P'
  · by_cases hhxP : h x ∈ P
    · have hhxQ : h x ∉ Q := by
        intro hcon
        have hkx := hnotA x hx
        rw [crossRegluedPullback_eq_left hxP' hhxP] at hkx
        exact hkx ((hAiff hhxP).mpr ⟨hhxP, hcon⟩)
      have hxQ' : x ∉ Q' := fun hcon => hhxQ (hA'Q ((hhiff hxP').mpr ⟨hxP', hcon⟩))
      obtain ⟨W, hWopen, hWeq⟩ := continuousOn_iff'.mp hconth Qᶜ hQopen
      have hOopen : IsOpen (Ω ∩ Q'ᶜ ∩ W) := (hΩ.inter hQ'open).inter hWopen
      refine ⟨Ω ∩ Q'ᶜ ∩ W, hOopen, ⟨⟨hx.2, hxQ'⟩, (hWeq.subset ⟨hhxQ, hxP'⟩).1⟩, ?_⟩
      have hset : G.domain ∩ Ω ∩ (Ω ∩ Q'ᶜ ∩ W) = P' ∩ h ⁻¹' P ∩ (Ω ∩ Q'ᶜ ∩ W) := by
        ext z
        constructor
        · rintro ⟨⟨hzG, -⟩, hzO⟩
          have hzP' : z ∈ P' := (hGdomain.subset hzG).resolve_right hzO.1.2
          exact ⟨⟨hzP', (hsheet hzP').resolve_right (hWeq.superset ⟨hzO.2, hzP'⟩).1⟩, hzO⟩
        · rintro ⟨⟨hzP', -⟩, hzO⟩
          exact ⟨⟨hGdomain.symm.subset (Or.inl hzP'), hzO.1.1⟩, hzO⟩
      rw [hset]
      refine ((hf₁.isPiecewiseAffineOn.comp hh.isPiecewiseAffineOn).inter_of_isOpen
        hOopen).congr ?_
      rintro z ⟨⟨hzP', hzP⟩, -⟩
      exact crossRegluedPullback_eq_left hzP' hzP
    · have hhxQ : h x ∈ Q := (hsheet hxP').resolve_left hhxP
      have hhxA' : h x ∉ A' := by
        intro hcon
        have hkx := hnotA x hx
        rw [crossRegluedPullback_eq_middle hxP' hhxP] at hkx
        exact hkx ((hA'iff hhxQ).mpr hcon)
      have hxQ' : x ∉ Q' := fun hcon => hhxA' ((hhiff hxP').mpr ⟨hxP', hcon⟩)
      obtain ⟨W, hWopen, hWeq⟩ := continuousOn_iff'.mp hconth Pᶜ hPopen
      have hOopen : IsOpen (Ω ∩ Q'ᶜ ∩ W) := (hΩ.inter hQ'open).inter hWopen
      refine ⟨Ω ∩ Q'ᶜ ∩ W, hOopen, ⟨⟨hx.2, hxQ'⟩, (hWeq.subset ⟨hhxP, hxP'⟩).1⟩, ?_⟩
      have hset : G.domain ∩ Ω ∩ (Ω ∩ Q'ᶜ ∩ W) = P' ∩ h ⁻¹' Q ∩ (Ω ∩ Q'ᶜ ∩ W) := by
        ext z
        constructor
        · rintro ⟨⟨hzG, -⟩, hzO⟩
          have hzP' : z ∈ P' := (hGdomain.subset hzG).resolve_right hzO.1.2
          exact ⟨⟨hzP', (hsheet hzP').resolve_left (hWeq.superset ⟨hzO.2, hzP'⟩).1⟩, hzO⟩
        · rintro ⟨⟨hzP', -⟩, hzO⟩
          exact ⟨⟨hGdomain.symm.subset (Or.inl hzP'), hzO.1.1⟩, hzO⟩
      rw [hset]
      refine ((hf₂.isPiecewiseAffineOn.comp hh.isPiecewiseAffineOn).inter_of_isOpen
        hOopen).congr ?_
      rintro z ⟨⟨hzP', -⟩, hzO⟩
      exact crossRegluedPullback_eq_middle hzP' (hWeq.superset ⟨hzO.2, hzP'⟩).1
  · refine ⟨Ω ∩ P'ᶜ, hΩ.inter hP'open, ⟨hx.2, hxP'⟩, ?_⟩
    have hset : G.domain ∩ Ω ∩ (Ω ∩ P'ᶜ) = Q' ∩ (Ω ∩ P'ᶜ) := by
      ext z
      constructor
      · rintro ⟨⟨hzG, -⟩, hzO⟩
        exact ⟨(hGdomain.subset hzG).resolve_left hzO.2, hzO⟩
      · rintro ⟨hzQ', hzO⟩
        exact ⟨⟨hGdomain.symm.subset (Or.inr hzQ'), hzO.1⟩, hzO⟩
    rw [hset]
    refine (hf₃.isPiecewiseAffineOn.inter_of_isOpen (hΩ.inter hP'open)).congr ?_
    rintro z ⟨-, hzO⟩
    exact crossRegluedPullback_eq_right hzO.2

theorem isPiecewiseAffineOn_invFunOn_crossRegluedPullback_inter_of_isOpen
    (hdomains : U₁ ∪ U₂ ∪ U₃ = D.domain) (hinter₁₂ : U₁ ∩ U₂ = A)
    (hinter₂₃ : U₂ ∩ U₃ = C) (hdisjoint₁₃ : Disjoint U₁ U₃)
    (hP : IsPLBall 2 P) (hQ : IsPLBall 2 Q) (hHdomain : H.domain = P ∪ Q)
    (hf₁ : IsPLHomeomorphOn f₁ P U₁) (hf₂ : IsPLHomeomorphOn f₂ Q U₂)
    (hf₂seam : f₂ '' (P ∩ Q) = C) (hGdomain : G.domain = P' ∪ Q')
    (hh : IsPLHomeomorphOn h P' H.domain) (hQ' : IsPLBall 2 Q')
    (hf₃ : IsPLHomeomorphOn f₃ Q' U₃) (hf₃seam : f₃ '' (P' ∩ Q') = C)
    {S Ω : Set (EuclideanSpace ℝ (Fin 2))} (hΩ : IsOpen Ω)
    (hbij : BijOn (crossRegluedPullback P' P h f₁ f₂ f₃) S (D.domain ∩ Ω))
    (hS : S ⊆ G.domain) (hnotA : ∀ u ∈ D.domain ∩ Ω, u ∉ A)
    (hnotC : ∀ u ∈ D.domain ∩ Ω, u ∉ C) :
    IsPiecewiseAffineOn (Function.invFunOn (crossRegluedPullback P' P h f₁ f₂ f₃) S)
      (D.domain ∩ Ω) := by
  have hU₁closed : IsClosed U₁ := by
    rw [← hf₁.bijOn.image_eq]
    exact (hP.isPolyhedron.isCompact.image_of_continuousOn
      hf₁.isPiecewiseAffineOn.continuousOn).isClosed
  have hU₂closed : IsClosed U₂ := by
    rw [← hf₂.bijOn.image_eq]
    exact (hQ.isPolyhedron.isCompact.image_of_continuousOn
      hf₂.isPiecewiseAffineOn.continuousOn).isClosed
  have hU₃closed : IsClosed U₃ := by
    rw [← hf₃.bijOn.image_eq]
    exact (hQ'.isPolyhedron.isCompact.image_of_continuousOn
      hf₃.isPiecewiseAffineOn.continuousOn).isClosed
  have hPH : P ⊆ H.domain := fun w hw => hHdomain.symm.subset (Or.inl hw)
  have hQH : Q ⊆ H.domain := fun w hw => hHdomain.symm.subset (Or.inr hw)
  have hinv : ∀ u ∈ D.domain ∩ Ω, ∀ x ∈ G.domain,
      crossRegluedPullback P' P h f₁ f₂ f₃ x = u →
      Function.invFunOn (crossRegluedPullback P' P h f₁ f₂ f₃) S u = x := by
    intro u hu x hx hxu
    refine eq_of_crossRegluedPullback_eq_of_notMem hinter₁₂ hinter₂₃ hdisjoint₁₃ hHdomain
      hf₁ hf₂ hf₂seam hGdomain hh hf₃ (hS (hbij.surjOn.mapsTo_invFunOn hu)) hx ?_ ?_
    · rw [hbij.invOn_invFunOn.2 hu, hxu]
    · rw [hbij.invOn_invFunOn.2 hu]
      exact hnotA u hu
  refine isPiecewiseAffineOn_of_locally ?_
  intro u hu
  by_cases hu₁ : u ∈ U₁
  · have hu₂ : u ∉ U₂ := fun hcon => hnotA u hu (hinter₁₂.subset ⟨hu₁, hcon⟩)
    have hu₃ : u ∉ U₃ := Set.disjoint_left.mp hdisjoint₁₃ hu₁
    have hOopen : IsOpen (Ω ∩ (U₂ ∪ U₃)ᶜ) :=
      hΩ.inter (hU₂closed.union hU₃closed).isOpen_compl
    refine ⟨Ω ∩ (U₂ ∪ U₃)ᶜ, hOopen, ⟨hu.2, fun hcon => hcon.elim hu₂ hu₃⟩, ?_⟩
    have hset : D.domain ∩ Ω ∩ (Ω ∩ (U₂ ∪ U₃)ᶜ) = U₁ ∩ (Ω ∩ (U₂ ∪ U₃)ᶜ) := by
      ext z
      constructor
      · rintro ⟨⟨hzD, -⟩, hzO⟩
        rcases hdomains.symm.subset hzD with (hz | hz) | hz
        · exact ⟨hz, hzO⟩
        · exact absurd (Or.inl hz) hzO.2
        · exact absurd (Or.inr hz) hzO.2
      · rintro ⟨hz₁, hzO⟩
        exact ⟨⟨hdomains.subset (Or.inl (Or.inl hz₁)), hzO.1⟩, hzO⟩
    rw [hset]
    have hcomp : IsPiecewiseAffineOn
        (Function.invFunOn h P' ∘ Function.invFunOn f₁ P) U₁ := by
      have hc := hh.isPiecewiseAffineOn_invFunOn.comp hf₁.isPiecewiseAffineOn_invFunOn
      have hsub : U₁ ⊆ Function.invFunOn f₁ P ⁻¹' H.domain :=
        fun w hw => hPH (hf₁.bijOn.surjOn.mapsTo_invFunOn hw)
      rwa [inter_eq_left.mpr hsub] at hc
    refine (hcomp.inter_of_isOpen hOopen).congr ?_
    rintro z ⟨hz₁, hzO⟩
    have hzD : z ∈ D.domain ∩ Ω := ⟨hdomains.subset (Or.inl (Or.inl hz₁)), hzO.1⟩
    have hzP : Function.invFunOn f₁ P z ∈ P := hf₁.bijOn.surjOn.mapsTo_invFunOn hz₁
    have hzf : f₁ (Function.invFunOn f₁ P z) = z := hf₁.bijOn.invOn_invFunOn.2 hz₁
    have hzP' : Function.invFunOn h P' (Function.invFunOn f₁ P z) ∈ P' :=
      hh.bijOn.surjOn.mapsTo_invFunOn (hPH hzP)
    have hzh : h (Function.invFunOn h P' (Function.invFunOn f₁ P z))
        = Function.invFunOn f₁ P z := hh.bijOn.invOn_invFunOn.2 (hPH hzP)
    have hval : crossRegluedPullback P' P h f₁ f₂ f₃
        (Function.invFunOn h P' (Function.invFunOn f₁ P z)) = z := by
      rw [crossRegluedPullback_eq_left hzP' (by rw [hzh]; exact hzP), hzh, hzf]
    exact hinv z hzD (Function.invFunOn h P' (Function.invFunOn f₁ P z))
      (hGdomain.symm.subset (Or.inl hzP')) hval
  · by_cases hu₂ : u ∈ U₂
    · have hu₃ : u ∉ U₃ := fun hcon => hnotC u hu (hinter₂₃.subset ⟨hu₂, hcon⟩)
      have hOopen : IsOpen (Ω ∩ (U₁ ∪ U₃)ᶜ) :=
        hΩ.inter (hU₁closed.union hU₃closed).isOpen_compl
      refine ⟨Ω ∩ (U₁ ∪ U₃)ᶜ, hOopen, ⟨hu.2, fun hcon => hcon.elim hu₁ hu₃⟩, ?_⟩
      have hset : D.domain ∩ Ω ∩ (Ω ∩ (U₁ ∪ U₃)ᶜ) = U₂ ∩ (Ω ∩ (U₁ ∪ U₃)ᶜ) := by
        ext z
        constructor
        · rintro ⟨⟨hzD, -⟩, hzO⟩
          rcases hdomains.symm.subset hzD with (hz | hz) | hz
          · exact absurd (Or.inl hz) hzO.2
          · exact ⟨hz, hzO⟩
          · exact absurd (Or.inr hz) hzO.2
        · rintro ⟨hz₂, hzO⟩
          exact ⟨⟨hdomains.subset (Or.inl (Or.inr hz₂)), hzO.1⟩, hzO⟩
      rw [hset]
      have hcomp : IsPiecewiseAffineOn
          (Function.invFunOn h P' ∘ Function.invFunOn f₂ Q) U₂ := by
        have hc := hh.isPiecewiseAffineOn_invFunOn.comp hf₂.isPiecewiseAffineOn_invFunOn
        have hsub : U₂ ⊆ Function.invFunOn f₂ Q ⁻¹' H.domain :=
          fun w hw => hQH (hf₂.bijOn.surjOn.mapsTo_invFunOn hw)
        rwa [inter_eq_left.mpr hsub] at hc
      refine (hcomp.inter_of_isOpen hOopen).congr ?_
      rintro z ⟨hz₂, hzO⟩
      have hzD : z ∈ D.domain ∩ Ω := ⟨hdomains.subset (Or.inl (Or.inr hz₂)), hzO.1⟩
      have hzQ : Function.invFunOn f₂ Q z ∈ Q := hf₂.bijOn.surjOn.mapsTo_invFunOn hz₂
      have hzf : f₂ (Function.invFunOn f₂ Q z) = z := hf₂.bijOn.invOn_invFunOn.2 hz₂
      have hzPnot : Function.invFunOn f₂ Q z ∉ P := by
        intro hcon
        refine hnotC z hzD ?_
        rw [← hzf, ← hf₂seam]
        exact ⟨Function.invFunOn f₂ Q z, ⟨hcon, hzQ⟩, rfl⟩
      have hzP' : Function.invFunOn h P' (Function.invFunOn f₂ Q z) ∈ P' :=
        hh.bijOn.surjOn.mapsTo_invFunOn (hQH hzQ)
      have hzh : h (Function.invFunOn h P' (Function.invFunOn f₂ Q z))
          = Function.invFunOn f₂ Q z := hh.bijOn.invOn_invFunOn.2 (hQH hzQ)
      have hval : crossRegluedPullback P' P h f₁ f₂ f₃
          (Function.invFunOn h P' (Function.invFunOn f₂ Q z)) = z := by
        rw [crossRegluedPullback_eq_middle hzP' (by rw [hzh]; exact hzPnot), hzh, hzf]
      exact hinv z hzD (Function.invFunOn h P' (Function.invFunOn f₂ Q z))
        (hGdomain.symm.subset (Or.inl hzP')) hval
    · have hOopen : IsOpen (Ω ∩ (U₁ ∪ U₂)ᶜ) :=
        hΩ.inter (hU₁closed.union hU₂closed).isOpen_compl
      refine ⟨Ω ∩ (U₁ ∪ U₂)ᶜ, hOopen, ⟨hu.2, fun hcon => hcon.elim hu₁ hu₂⟩, ?_⟩
      have hset : D.domain ∩ Ω ∩ (Ω ∩ (U₁ ∪ U₂)ᶜ) = U₃ ∩ (Ω ∩ (U₁ ∪ U₂)ᶜ) := by
        ext z
        constructor
        · rintro ⟨⟨hzD, -⟩, hzO⟩
          rcases hdomains.symm.subset hzD with (hz | hz) | hz
          · exact absurd (Or.inl hz) hzO.2
          · exact absurd (Or.inr hz) hzO.2
          · exact ⟨hz, hzO⟩
        · rintro ⟨hz₃, hzO⟩
          exact ⟨⟨hdomains.subset (Or.inr hz₃), hzO.1⟩, hzO⟩
      rw [hset]
      refine (hf₃.isPiecewiseAffineOn_invFunOn.inter_of_isOpen hOopen).congr ?_
      rintro z ⟨hz₃, hzO⟩
      have hzD : z ∈ D.domain ∩ Ω := ⟨hdomains.subset (Or.inr hz₃), hzO.1⟩
      have hzQ' : Function.invFunOn f₃ Q' z ∈ Q' := hf₃.bijOn.surjOn.mapsTo_invFunOn hz₃
      have hzf : f₃ (Function.invFunOn f₃ Q' z) = z := hf₃.bijOn.invOn_invFunOn.2 hz₃
      have hzP'not : Function.invFunOn f₃ Q' z ∉ P' := by
        intro hcon
        refine hnotC z hzD ?_
        rw [← hzf, ← hf₃seam]
        exact ⟨Function.invFunOn f₃ Q' z, ⟨hcon, hzQ'⟩, rfl⟩
      have hval : crossRegluedPullback P' P h f₁ f₂ f₃ (Function.invFunOn f₃ Q' z) = z := by
        rw [crossRegluedPullback_eq_right hzP'not, hzf]
      exact hinv z hzD (Function.invFunOn f₃ Q' z)
        (hGdomain.symm.subset (Or.inr hzQ')) hval

theorem NormalSingularCellData.crossing_crossReglued_of_notMem_branchCarrier [T2Space M]
    (hD : NormalSingularCellData D BdM B) {c : hD.singularSet.Branch}
    (hAC : Disjoint A C) (hcover : hD.branchPreimage c = A ∪ C)
    (hg : IsPLHomeomorphOn g A C) (hcompat : EqOn D (D ∘ g) A)
    (hdomains : U₁ ∪ U₂ ∪ U₃ = D.domain) (hinter₁₂ : U₁ ∩ U₂ = A)
    (hinter₂₃ : U₂ ∩ U₃ = C) (hdisjoint₁₃ : Disjoint U₁ U₃)
    (hP : IsPLBall 2 P) (hQ : IsPLBall 2 Q) (hHdomain : H.domain = P ∪ Q)
    (hf₁ : IsPLHomeomorphOn f₁ P U₁) (hf₂ : IsPLHomeomorphOn f₂ Q U₂)
    (hf₁seam : f₁ '' (P ∩ Q) = A) (hf₂seam : f₂ '' (P ∩ Q) = C)
    (hH₁ : EqOn H (D ∘ f₁) P) (hH₂ : EqOn H (D ∘ f₂) Q)
    (hA'def : A' = Function.invFunOn f₂ Q '' A)
    (hP' : IsPLBall 2 P') (hQ' : IsPLBall 2 Q') (hGdomain : G.domain = P' ∪ Q')
    (hh : IsPLHomeomorphOn h P' H.domain) (hf₃ : IsPLHomeomorphOn f₃ Q' U₃)
    (hhseam : h '' (P' ∩ Q') = A') (hf₃seam : f₃ '' (P' ∩ Q') = C)
    (hGH : EqOn G (H ∘ h) P') (hG₃ : EqOn G (D ∘ f₃) Q')
    (hbranch : hD.singularSet.branchCarrier c ⊆ doublePointSet G G.domain) :
    ∀ y ∈ doublePointSet G G.domain, y ∉ hD.singularSet.branchCarrier c →
      ∃ e ∈ atlas (EuclideanSpace ℝ (Fin 3)) M, y ∈ e.source ∧
        HasPLNormalDoubleCrossingAt (⇑e ∘ ⇑G) (G.domain ∩ ⇑G ⁻¹' e.source)
          (⇑e '' (e.source ∩ BdM)) (e y) := by
  have hdouble := hD.doublePointSet_crossReglued_eq hAC hcover hg hcompat hdomains hinter₁₂
    hinter₂₃ hdisjoint₁₃ hHdomain hf₁ hf₂ hf₂seam hH₁ hH₂ hGdomain hh hf₃ hf₃seam hGH hG₃
    hbranch
  intro y hy hybranch
  obtain ⟨e, he, hye, hcross⟩ := hD.crossing y (hdouble.subset hy)
  refine ⟨e, he, hye, ?_⟩
  obtain ⟨N, hNopen, hyN, hNsub, hNbranch⟩ :
      ∃ N : Set M, IsOpen N ∧ y ∈ N ∧ N ⊆ e.source ∧
        Disjoint N (hD.singularSet.branchCarrier c) :=
    ⟨e.source \ hD.singularSet.branchCarrier c,
      e.open_source.sdiff (hD.singularSet.branchCarrier_isCompact c).isClosed,
      ⟨hye, hybranch⟩, Set.sdiff_subset, Set.disjoint_left.mpr fun z hz hz' => hz.2 hz'⟩
  have hV : IsOpen (⇑e '' N) := e.isOpen_image_of_subset_source hNopen hNsub
  have hyV : e y ∈ ⇑e '' N := mem_image_of_mem _ hyN
  have hshrink : D.domain ∩ ⇑D ⁻¹' e.source ∩ (⇑e ∘ ⇑D) ⁻¹' (⇑e '' N) =
      D.domain ∩ ⇑D ⁻¹' N := by
    ext w
    constructor
    · rintro ⟨⟨hwD, hwe⟩, hwV⟩
      obtain ⟨m, hm, hme⟩ := hwV
      have hmeq : m = ⇑D w := e.injOn (hNsub hm) hwe hme
      exact ⟨hwD, by rw [mem_preimage, ← hmeq]; exact hm⟩
    · rintro ⟨hwD, hwN⟩
      exact ⟨⟨hwD, hNsub hwN⟩, ⟨⇑D w, hwN, rfl⟩⟩
  have hcross₀ : HasPLNormalDoubleCrossingAt (⇑e ∘ ⇑D) (D.domain ∩ ⇑D ⁻¹' N)
      (⇑e '' (e.source ∩ BdM)) (e y) := by
    have hloc := hcross.inter_preimage_of_isOpen hV hyV
    rwa [hshrink] at hloc
  obtain ⟨Ω, hΩopen, hΩ⟩ := continuousOn_iff'.mp D.continuousOn N hNopen
  obtain ⟨Ω', hΩ'open, hΩ'⟩ := continuousOn_iff'.mp G.continuousOn N hNopen
  have hDΩ : D.domain ∩ Ω = D.domain ∩ ⇑D ⁻¹' N := by
    rw [inter_comm D.domain Ω, ← hΩ, inter_comm (⇑D ⁻¹' N) D.domain]
  have hGΩ : G.domain ∩ Ω' = G.domain ∩ ⇑G ⁻¹' N := by
    rw [inter_comm G.domain Ω', ← hΩ', inter_comm (⇑G ⁻¹' N) G.domain]
  have hmaps := mapsTo_crossRegluedPullback hdomains hHdomain hf₁ hf₂ hGdomain hh hf₃
  have hmapk := map_crossRegluedPullback hHdomain hH₁ hH₂ hGdomain hh hGH hG₃
  have hmem : ∀ x ∈ G.domain, (crossRegluedPullback P' P h f₁ f₂ f₃ x ∈ Ω ↔ x ∈ Ω') := by
    intro x hx
    constructor
    · intro hxΩ
      have hk : crossRegluedPullback P' P h f₁ f₂ f₃ x ∈ D.domain ∩ ⇑D ⁻¹' N := by
        rw [← hDΩ]
        exact ⟨hmaps hx, hxΩ⟩
      have hGx : x ∈ G.domain ∩ ⇑G ⁻¹' N := ⟨hx, by rw [mem_preimage, ← hmapk x hx]; exact hk.2⟩
      rw [← hGΩ] at hGx
      exact hGx.2
    · intro hxΩ'
      have hGx : x ∈ G.domain ∩ ⇑G ⁻¹' N := by
        rw [← hGΩ]
        exact ⟨hx, hxΩ'⟩
      have hk : crossRegluedPullback P' P h f₁ f₂ f₃ x ∈ D.domain ∩ ⇑D ⁻¹' N :=
        ⟨hmaps hx, by rw [mem_preimage, hmapk x hx]; exact hGx.2⟩
      rw [← hDΩ] at hk
      exact hk.2
  have hnotAC : ∀ u ∈ D.domain ∩ Ω, u ∉ A ∪ C := by
    intro u hu hmemAC
    rw [hDΩ] at hu
    have hpre : u ∈ hD.branchPreimage c := by
      rw [hcover]
      exact hmemAC
    exact Set.disjoint_left.mp hNbranch hu.2 hpre.2
  have hnotA : ∀ u ∈ D.domain ∩ Ω, u ∉ A := fun u hu hA => hnotAC u hu (Or.inl hA)
  have hnotC : ∀ u ∈ D.domain ∩ Ω, u ∉ C := fun u hu hC => hnotAC u hu (Or.inr hC)
  have hbij := bijOn_crossRegluedPullback_inter_of_isOpen hdomains hinter₁₂ hinter₂₃
    hdisjoint₁₃ hHdomain hf₁ hf₂ hf₂seam hGdomain hh hf₃ hf₃seam hmem hnotA hnotC
  have hPL : IsPLHomeomorphOn (crossRegluedPullback P' P h f₁ f₂ f₃) (G.domain ∩ Ω')
      (D.domain ∩ Ω) :=
    ⟨hbij, isPiecewiseAffineOn_crossRegluedPullback_inter_of_isOpen hinter₁₂ hP hQ hHdomain
      hf₁ hf₂ hf₁seam hA'def hP' hQ' hGdomain hh hf₃ hhseam hΩ'open
      (fun x hx => hnotA _ (hbij.mapsTo hx)),
      isPiecewiseAffineOn_invFunOn_crossRegluedPullback_inter_of_isOpen hdomains hinter₁₂
        hinter₂₃ hdisjoint₁₃ hP hQ hHdomain hf₁ hf₂ hf₂seam hGdomain hh hQ' hf₃ hf₃seam
        hΩopen hbij inter_subset_left hnotA hnotC⟩
  have hcross₁ : HasPLNormalDoubleCrossingAt
      ((⇑e ∘ ⇑D) ∘ crossRegluedPullback P' P h f₁ f₂ f₃) (G.domain ∩ Ω')
      (⇑e '' (e.source ∩ BdM)) (e y) := by
    rw [← hDΩ] at hcross₀
    exact hcross₀.precomp_isPLHomeomorphOn hPL
  have hcross₂ : HasPLNormalDoubleCrossingAt (⇑e ∘ ⇑G) (G.domain ∩ Ω')
      (⇑e '' (e.source ∩ BdM)) (e y) :=
    hcross₁.congr_source fun z hz => by
      simp only [Function.comp_apply]
      rw [hmapk z hz.1]
  have hsub : G.domain ∩ Ω' ⊆ G.domain ∩ ⇑G ⁻¹' e.source := by
    rw [hGΩ]
    exact fun z hz => ⟨hz.1, hNsub hz.2⟩
  have hstep : G.domain ∩ ⇑G ⁻¹' e.source ∩ (⇑e ∘ ⇑G) ⁻¹' (⇑e '' N) ⊆ G.domain ∩ Ω' := by
    rintro z ⟨⟨hzG, hze⟩, hzV⟩
    obtain ⟨m, hm, hme⟩ := hzV
    have hmeq : m = ⇑G z := e.injOn (hNsub hm) hze hme
    rw [hGΩ]
    exact ⟨hzG, by rw [mem_preimage, ← hmeq]; exact hm⟩
  have hfib := eventually_inter_preimage_singleton_subset (g := ⇑e ∘ ⇑G)
    (G.domain ∩ ⇑G ⁻¹' e.source) hV hyV
  refine hcross₂.mono_of_subset hsub Subset.rfl
    (fun a ha _ => ⟨Ω', hΩ'open.mem_nhds ha.2, fun z hz => ⟨hz.1.1, hz.2⟩⟩) ?_
  filter_upwards [hfib] with z hz
  exact fun w hw => hstep (hz hw)

end CrossRegluedCrossing

theorem NormalSingularCellData.exists_cross_reglued_cell_crossing_of_boundaryBranch
    {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [T2Space M]
    {D : SingularTwoCell M} {BdM B : Set M} (hD : NormalSingularCellData D BdM B)
    {c : hD.singularSet.Branch} (hc : hD.singularSet.IsBoundaryBranch c) :
    ∃ G : SingularTwoCell M,
      ⇑G '' G.domain ⊆ ⇑D '' D.domain ∧
      hD.singularSet.branchCarrier c ⊆ doublePointSet G G.domain ∧
      doublePointSet G G.domain = doublePointSet D D.domain ∧
      (∀ x ∈ G.domain, ∃ V ∈ 𝓝[G.domain] x, InjOn (⇑G) V) ∧
      (∀ y, (G.domain ∩ ⇑G ⁻¹' {y}).encard ≤ 2) ∧
      (∀ y ∈ doublePointSet G G.domain, y ∉ hD.singularSet.branchCarrier c →
        ∃ e ∈ atlas (EuclideanSpace ℝ (Fin 3)) M, y ∈ e.source ∧
          HasPLNormalDoubleCrossingAt (⇑e ∘ ⇑G) (G.domain ∩ ⇑G ⁻¹' e.source)
            (⇑e '' (e.source ∩ BdM)) (e y)) ∧
      ∃ (x y : M) (σ : Path x y) (ω : Path y x) (e : loopCircle ≃ₜ frontier G.domain),
        ∀ θ, ⇑G (e θ) = pathToCircle (σ.trans ω) θ := by
  obtain ⟨A, C, U₁, U₂, U₃, P, Q, P', Q', A', _, _, _, _, _, _, _, _, g, f₁, f₂, h, f₃, H, G,
    -, -, hAC, hcover, hg, hcompat, -, -, -, -, -, hdomains, hinter₁₂, hinter₂₃,
    hdisjoint₁₃, hP, hQ, hHdomain, hf₁, hf₂, hf₁seam, hf₂seam, hH₁, hH₂,
    hA'def, -, hA'seam, -, -, hP', hQ', hGdomain, hh, hf₃, hhseam, hf₃seam, hGH, hG₃,
    -, -, -, -, -, -, -, -, -,
    hGimage, hbranch, x, y, σ, ω, e, -, -, hboundaryParam, -⟩ :=
    hD.exists_cross_reglued_cell_of_boundaryBranch hc
  exact ⟨G, hGimage, hbranch,
    hD.doublePointSet_crossReglued_eq hAC hcover hg hcompat hdomains hinter₁₂ hinter₂₃
      hdisjoint₁₃ hHdomain hf₁ hf₂ hf₂seam hH₁ hH₂ hGdomain hh hf₃ hf₃seam hGH hG₃ hbranch,
    hD.locallyInjective_crossReglued hAC hcover hg hcompat hdomains hinter₁₂ hinter₂₃
      hdisjoint₁₃ hP hQ hHdomain hf₁ hf₂ hf₁seam hf₂seam hH₁ hH₂ hA'def hA'seam hP' hQ'
      hGdomain hh hf₃ hhseam hf₃seam hGH hG₃,
    hD.fiber_le_two_crossReglued hAC hg hcompat hdomains hinter₁₂ hinter₂₃ hdisjoint₁₃
      hHdomain hf₁ hf₂ hf₂seam hH₁ hH₂ hGdomain hh hf₃ hf₃seam hGH hG₃,
    hD.crossing_crossReglued_of_notMem_branchCarrier hAC hcover hg hcompat hdomains hinter₁₂
      hinter₂₃ hdisjoint₁₃ hP hQ hHdomain hf₁ hf₂ hf₁seam hf₂seam hH₁ hH₂ hA'def hP' hQ'
      hGdomain hh hf₃ hhseam hf₃seam hGH hG₃ hbranch,
    x, y, σ, ω, e, hboundaryParam⟩

theorem NormalSingularCellData.exists_cross_reglued_cell_crossing_outside_of_boundaryBranch
    {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [T2Space M]
    {D : SingularTwoCell M} {BdM B : Set M} (hD : NormalSingularCellData D BdM B)
    {c : hD.singularSet.Branch} (hc : hD.singularSet.IsBoundaryBranch c) {U : Set M}
    (hU : hD.singularSet.branchCarrier c ⊆ U) :
    ∃ G : SingularTwoCell M,
      ⇑G '' G.domain ⊆ ⇑D '' D.domain ∧
      hD.singularSet.branchCarrier c ⊆ doublePointSet G G.domain ∧
      doublePointSet G G.domain = doublePointSet D D.domain ∧
      (∀ x ∈ G.domain, ∃ V ∈ 𝓝[G.domain] x, InjOn (⇑G) V) ∧
      (∀ y, (G.domain ∩ ⇑G ⁻¹' {y}).encard ≤ 2) ∧
      (∀ y ∈ doublePointSet G G.domain, y ∉ U →
        ∃ e ∈ atlas (EuclideanSpace ℝ (Fin 3)) M, y ∈ e.source ∧
          HasPLNormalDoubleCrossingAt (⇑e ∘ ⇑G) (G.domain ∩ ⇑G ⁻¹' e.source)
            (⇑e '' (e.source ∩ BdM)) (e y)) ∧
      ∃ (x y : M) (σ : Path x y) (ω : Path y x) (e : loopCircle ≃ₜ frontier G.domain),
        ∀ θ, ⇑G (e θ) = pathToCircle (σ.trans ω) θ := by
  obtain ⟨G, hGimage, hbranch, hdouble, hinj, hfiber, hcross, hrest⟩ :=
    hD.exists_cross_reglued_cell_crossing_of_boundaryBranch hc
  exact ⟨G, hGimage, hbranch, hdouble, hinj, hfiber,
    fun y hy hyU => hcross y hy fun hmem => hyU (hU hmem), hrest⟩

end DifferentialGeometry.Topology.PiecewiseLinear
