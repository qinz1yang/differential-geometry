/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.HoledSphereExtension

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

theorem IsPLCirclePositive.conj_of_leftInvOn
    {S : Set E} {T : Set F} {u : E → E} {h : E → F} {i : F → E}
    (hu : IsPLCirclePositive S u) (hmu : MapsTo u S S)
    (hh : ContinuousOn h S) (hbij : BijOn h S T) (hi : LeftInvOn i h S) :
    IsPLCirclePositive T (h ∘ u ∘ i) := by
  have hpos := hu.conj hmu hh hbij
  apply hpos.of_eqOn
  intro y hy
  have hiy : i y = Function.invFunOn h S y := by
    calc
      i y = i (h (Function.invFunOn h S y)) := congrArg i (hbij.invOn_invFunOn.2 hy).symm
      _ = Function.invFunOn h S y := hi (hbij.surjOn.mapsTo_invFunOn hy)
  simp only [Function.comp_apply, hiy]

theorem isPLCirclePositive_conj_iff_of_leftInvOn
    {S : Set E} {T : Set F} {u : E → E} {h : E → F} {i : F → E}
    (hmu : MapsTo u S S) (hh : ContinuousOn h S) (hic : ContinuousOn i T)
    (hbij : BijOn h S T) (hi : LeftInvOn i h S) :
    IsPLCirclePositive T (h ∘ u ∘ i) ↔ IsPLCirclePositive S u := by
  have him : MapsTo i T S := by
    rintro y hy
    obtain ⟨x, hx, rfl⟩ := hbij.surjOn hy
    rwa [hi hx]
  have hri : LeftInvOn h i T := by
    rintro y hy
    obtain ⟨x, hx, rfl⟩ := hbij.surjOn hy
    rw [hi hx]
  have hbi : BijOn i T S := (show InvOn i h S T from ⟨hi, hri⟩).symm.bijOn him hbij.mapsTo
  have hcm : MapsTo (h ∘ u ∘ i) T T := fun _ hy => hbij.mapsTo (hmu (him hy))
  constructor
  · intro hpos
    have hp := hpos.conj_of_leftInvOn hcm hic hbi hri
    apply hp.of_eqOn
    intro x hx
    simp only [Function.comp_apply, hi hx, hi (hmu hx)]
  · exact fun hp => hp.conj_of_leftInvOn hmu hh hbij hi

variable [NormedSpace ℝ E] [NormedSpace ℝ F] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

theorem IsPLHomeomorphOn.isPLCirclePositive_conj_iff
    {C S : Set E} {D : Set F} {h : E → F} (hh : IsPLHomeomorphOn h C D)
    (hSC : S ⊆ C) {u : E → E} (hmu : MapsTo u S S) :
    IsPLCirclePositive (h '' S) (h ∘ u ∘ Function.invFunOn h C) ↔ IsPLCirclePositive S u := by
  have hTD : h '' S ⊆ D := image_subset_iff.mpr (hh.bijOn.mapsTo.mono_left hSC)
  exact isPLCirclePositive_conj_iff_of_leftInvOn hmu
    (hh.isPiecewiseAffineOn.continuousOn.mono hSC)
    (hh.symm.isPiecewiseAffineOn.continuousOn.mono hTD)
    (hh.bijOn.injOn.mono hSC).bijOn_image (hh.bijOn.invOn_invFunOn.1.mono hSC)

end DifferentialGeometry.Topology.PiecewiseLinear
