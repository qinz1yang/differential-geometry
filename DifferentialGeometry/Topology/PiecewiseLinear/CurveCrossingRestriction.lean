/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BigonBoundaryCrossing
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem HasPLCurveCrossingOnAt.of_openPartialHomeomorph_of_finrank_eq
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F)
    {S A B : Set F} {S' A' B' : Set E} {x : F} (e : OpenPartialHomeomorph F E)
    (he : IsPiecewiseAffineOn e e.source) (hx : x ∈ e.source)
    (hcross : HasPLCurveCrossingOnAt S' A' B' (e x))
    (hS : ∀ᶠ y in 𝓝 x, y ∈ S ↔ e y ∈ S')
    (hA : ∀ᶠ y in 𝓝 x, y ∈ A ↔ e y ∈ A')
    (hB : ∀ᶠ y in 𝓝 x, y ∈ B ↔ e y ∈ B') : HasPLCurveCrossingOnAt S A B x := by
  obtain ⟨U, V, φ, T, P, Q, hU, hV, hxU, hφ, hφx, hT, hP, hQ, hPT, hQT, hPQ,
    hlocal⟩ := hcross
  let L : E ≃ₗ[ℝ] F := LinearEquiv.ofFinrankEq E F hdim
  let l := L.toContinuousLinearEquiv.toHomeomorph.toOpenPartialHomeomorph
  let k₀ := e.trans (hφ.toOpenPartialHomeomorph hU hV)
  let k := k₀.trans l
  have hLpa : IsPiecewiseAffineOn l l.source :=
    isPiecewiseAffineOn_of_affine L.toLinearMap.toAffineMap isOpen_univ
  have hkpa : IsPiecewiseAffineOn k k.source := hLpa.comp (hφ.isPiecewiseAffineOn.comp he)
  have hxk : x ∈ k.source := ⟨⟨hx, hxU⟩, mem_univ _⟩
  have hdimR : ∀ R : Submodule ℝ E,
      Module.finrank ℝ (R.map L.toLinearMap) = Module.finrank ℝ R :=
    fun R => (Submodule.equivMapOfInjective L.toLinearMap L.injective R).finrank_eq.symm
  have hmem : ∀ (R : Submodule ℝ E) (z : E), L z ∈ R.map L.toLinearMap ↔ z ∈ R := by
    intro R z
    exact ⟨fun ⟨y, hy, hyz⟩ => L.injective hyz ▸ hy, fun hz => ⟨z, hz, rfl⟩⟩
  have hinf : P.map L.toLinearMap ⊓ Q.map L.toLinearMap = ⊥ := by
    rw [← Submodule.map_inf L.toLinearMap L.injective, hPQ, Submodule.map_bot]
  refine ⟨k.source, k.target, k, T.map L.toLinearMap, P.map L.toLinearMap,
    Q.map L.toLinearMap, k.open_source, k.open_target, hxk,
    isPLHomeomorphOn_openPartialHomeomorph k hkpa, ?_, (hdimR T).trans hT,
    (hdimR P).trans hP, (hdimR Q).trans hQ, Submodule.map_mono hPT,
    Submodule.map_mono hQT, hinf, ?_⟩
  · change L (φ (e x)) = 0
    rw [hφx, map_zero]
  · filter_upwards [(e.continuousAt hx).tendsto.eventually hlocal, hS, hA, hB]
      with y hy hyS hyA hyB
    change (y ∈ S ↔ L (φ (e y)) ∈ T.map L.toLinearMap) ∧
      (y ∈ A ↔ L (φ (e y)) ∈ P.map L.toLinearMap) ∧
      (y ∈ B ↔ L (φ (e y)) ∈ Q.map L.toLinearMap)
    rw [hmem, hmem, hmem]
    exact ⟨hyS.trans hy.1, hyA.trans hy.2.1, hyB.trans hy.2.2⟩

theorem HasPLCurveCrossingOnAt.preimage_linearMap
    {S A B : Set E} {x : F} (ι : F →ₗ[ℝ] E) (hι : Function.Injective ι)
    (hF : Module.finrank ℝ F = 2) (hcross : HasPLCurveCrossingOnAt S A B (ι x))
    (hS : ∀ᶠ y in 𝓝 (ι x), y ∈ S ↔ y ∈ LinearMap.range ι) :
    HasPLCurveCrossingOnAt univ (ι ⁻¹' A) (ι ⁻¹' B) x := by
  classical
  obtain ⟨U, V, φ, T, P, Q, hU, hV, hxU, hφ, hφx, hT, hP, hQ, hPT, hQT, hPQ,
    hlocal⟩ := hcross
  obtain ⟨O, hOsub, hO, hxO⟩ := _root_.mem_nhds_iff.mp (hlocal.and hS)
  let e₀ := hφ.toOpenPartialHomeomorph hU hV
  let e := e₀.restrOpen O hO
  have hxe : ι x ∈ e.source := ⟨hxU, hxO⟩
  have he : IsPiecewiseAffineOn e e.source :=
    hφ.isPiecewiseAffineOn.mono e.open_source inter_subset_left
  have hei : IsPiecewiseAffineOn e.symm e.target :=
    hφ.isPiecewiseAffineOn_invFunOn.mono e.open_target inter_subset_left
  have hplane : ∀ y ∈ e.source, y ∈ LinearMap.range ι ↔ e y ∈ T := by
    intro y hy
    exact (hOsub hy.2).2.symm.trans (hOsub hy.2).1.1
  have hcurves : ∀ y ∈ e.source, (y ∈ A ↔ e y ∈ P) ∧ (y ∈ B ↔ e y ∈ Q) :=
    fun y hy => (hOsub hy.2).1.2
  obtain ⟨π, hπι⟩ := ι.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hι)
  have hπι' : ∀ y, π (ι y) = y := fun y => LinearMap.congr_fun hπι y
  have hιπ : ∀ y ∈ LinearMap.range ι, ι (π y) = y := by
    rintro _ ⟨y, rfl⟩
    rw [hπι']
  let L : T ≃ₗ[ℝ] F := LinearEquiv.ofFinrankEq _ _ (hT.trans hF.symm)
  obtain ⟨r, hr⟩ := T.subtype.exists_leftInverse_of_injective T.ker_subtype
  let j : F →ₗ[ℝ] E := T.subtype.comp L.symm.toLinearMap
  let ρ : E →ₗ[ℝ] F := L.toLinearMap.comp r
  have hρj : ∀ y, ρ (j y) = y := by
    intro y
    change L (r (T.subtype (L.symm y))) = y
    have hry : r (T.subtype (L.symm y)) = L.symm y := LinearMap.congr_fun hr (L.symm y)
    rw [hry, L.apply_symm_apply]
  have hjρ : ∀ y ∈ T, j (ρ y) = y := by
    intro y hy
    change (L.symm (L (r y)) : E) = y
    rw [L.symm_apply_apply]
    have hry : r y = ⟨y, hy⟩ := LinearMap.congr_fun hr ⟨y, hy⟩
    rw [hry]
  have hjT : ∀ y, j y ∈ T := fun y => (L.symm y).2
  have hji : Function.Injective j := Function.LeftInverse.injective hρj
  have hjrange : LinearMap.range j = T := by
    apply le_antisymm
    · rintro _ ⟨y, rfl⟩
      exact hjT y
    · exact fun y hy => ⟨ρ y, hjρ y hy⟩
  let U₂ : Set F := ι ⁻¹' e.source
  let V₂ : Set F := j ⁻¹' e.target
  let f : F → F := ρ ∘ e ∘ ι
  let g : F → F := π ∘ e.symm ∘ j
  have hU₂ : IsOpen U₂ := e.open_source.preimage ι.continuous_of_finiteDimensional
  have hV₂ : IsOpen V₂ := e.open_target.preimage j.continuous_of_finiteDimensional
  have hfplane : ∀ y ∈ U₂, e (ι y) ∈ T := fun y hy =>
    (hplane (ι y) hy).mp ⟨y, rfl⟩
  have hgplane : ∀ y ∈ V₂, e.symm (j y) ∈ LinearMap.range ι := by
    intro y hy
    apply (hplane _ (e.map_target hy)).mpr
    rw [e.right_inv hy]
    exact hjT y
  have hfm : MapsTo f U₂ V₂ := by
    intro y hy
    change j (ρ (e (ι y))) ∈ e.target
    rw [hjρ _ (hfplane y hy)]
    exact e.map_source hy
  have hgm : MapsTo g V₂ U₂ := by
    intro y hy
    change ι (π (e.symm (j y))) ∈ e.source
    rw [hιπ _ (hgplane y hy)]
    exact e.map_target hy
  have hgf : ∀ y ∈ U₂, g (f y) = y := by
    intro y hy
    change π (e.symm (j (ρ (e (ι y))))) = y
    rw [hjρ _ (hfplane y hy), e.left_inv hy, hπι']
  have hfg : ∀ y ∈ V₂, f (g y) = y := by
    intro y hy
    change ρ (e (ι (π (e.symm (j y))))) = y
    rw [hιπ _ (hgplane y hy), e.right_inv hy, hρj]
  have hfbij : BijOn f U₂ V₂ := by
    refine ⟨hfm, ?_, ?_⟩
    · intro y hy z hz hyz
      exact (hgf y hy).symm.trans ((congrArg g hyz).trans (hgf z hz))
    · exact fun y hy => ⟨g y, hgm hy, hfg y hy⟩
  have hpa : IsPiecewiseAffineOn f U₂ := by
    have hιpa := isPiecewiseAffineOn_of_affine ι.toAffineMap hU₂
    have hρpa := isPiecewiseAffineOn_of_affine ρ.toAffineMap isOpen_univ
    have h := hρpa.comp (he.comp hιpa)
    rw [preimage_univ, inter_univ] at h
    change IsPiecewiseAffineOn f (U₂ ∩ U₂) at h
    simpa only [inter_self] using h
  have hgpa : IsPiecewiseAffineOn g V₂ := by
    have hjpa := isPiecewiseAffineOn_of_affine j.toAffineMap hV₂
    have hπpa := isPiecewiseAffineOn_of_affine π.toAffineMap isOpen_univ
    have h := hπpa.comp (hei.comp hjpa)
    rw [preimage_univ, inter_univ] at h
    change IsPiecewiseAffineOn g (V₂ ∩ V₂) at h
    simpa only [inter_self] using h
  have hf : IsPLHomeomorphOn f U₂ V₂ := by
    refine ⟨hfbij, hpa, hgpa.congr ?_⟩
    intro y hy
    apply hfbij.injOn (hfbij.surjOn.mapsTo_invFunOn hy) (hgm hy)
    exact (hfbij.invOn_invFunOn.2 hy).trans (hfg y hy).symm
  have hdim : ∀ R : Submodule ℝ E, R ≤ T →
      Module.finrank ℝ (R.comap j) = Module.finrank ℝ R := by
    intro R hRT
    have hmap : (R.comap j).map j = R :=
      Submodule.map_comap_eq_of_le (by rw [hjrange]; exact hRT)
    have hd := (Submodule.equivMapOfInjective j hji (R.comap j)).finrank_eq
    rwa [hmap] at hd
  have hinf : P.comap j ⊓ Q.comap j = ⊥ := by
    rw [← Submodule.comap_inf, hPQ, Submodule.comap_bot, LinearMap.ker_eq_bot]
    exact hji
  refine ⟨U₂, V₂, f, ⊤, P.comap j, Q.comap j, hU₂, hV₂, hxe, hf, ?_,
    ?_, (hdim P hPT).trans hP, (hdim Q hQT).trans hQ, le_top, le_top, hinf, ?_⟩
  · change ρ (φ (ι x)) = 0
    rw [hφx, map_zero]
  · simpa only [finrank_top] using hF
  · filter_upwards [hU₂.mem_nhds hxe] with y hy
    have hjf : j (f y) = e (ι y) := hjρ _ (hfplane y hy)
    refine ⟨iff_of_true (mem_univ y) (Submodule.mem_top), ?_, ?_⟩
    · change ι y ∈ A ↔ j (f y) ∈ P
      rw [hjf]
      exact (hcurves (ι y) hy).1
    · change ι y ∈ B ↔ j (f y) ∈ Q
      rw [hjf]
      exact (hcurves (ι y) hy).2

end DifferentialGeometry.Topology.PiecewiseLinear
