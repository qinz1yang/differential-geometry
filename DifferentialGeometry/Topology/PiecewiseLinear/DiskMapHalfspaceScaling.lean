/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DiskMapHalfspaceExtension
import DifferentialGeometry.Topology.PiecewiseLinear.DiskMapHalfspaceHomotopy
import DifferentialGeometry.Topology.PiecewiseLinear.StableCrossingDoubleCrossing

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

theorem exists_isPLHomeomorphOn_extension_halfspaces_thickness
    {P : Set Plane} (hP : IsPLBall 2 P) {u : Plane → Plane}
    (hu : IsPLHomeomorphOn u P P) (hfix : EqOn u id (frontier P))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ Φ : (Plane × ℝ) ≃ₜ (Plane × ℝ), IsPLHomeomorphOn Φ univ univ ∧
      (∀ x ∈ P, Φ (x, 0) = (u x, 0)) ∧ EqOn Φ id (P ×ˢ Icc (-δ) δ)ᶜ ∧
      (∀ z, 0 ≤ (Φ z).2 ↔ 0 ≤ z.2) ∧ (∀ z, (Φ z).2 = 0 ↔ z.2 = 0) ∧
      ∃ H : (Plane × ℝ) × unitInterval → Plane × ℝ, Continuous H ∧
        (∀ z, H (z, 0) = z) ∧ (∀ z, H (z, 1) = Φ z) ∧
        (∀ t, EqOn (fun z => H (z, t)) id (P ×ˢ Icc (-δ) δ)ᶜ) ∧
        (∀ t, MapsTo (fun z => H (z, t)) (P ×ˢ Icc (-δ) δ) (P ×ˢ Icc (-δ) δ)) ∧
        (∀ z t, 0 ≤ z.2 → 0 ≤ (H (z, t)).2) ∧
        (∀ z t, z.2 = 0 → (H (z, t)).2 = 0) := by
  obtain ⟨f, hf, hf0, hffix, hfside, hfplane⟩ :=
    exists_isPLHomeomorphOn_extension_halfspaces hP hu hfix
  have hfbox : MapsTo f (P ×ˢ Icc (-1 : ℝ) 1) (P ×ˢ Icc (-1 : ℝ) 1) := by
    intro z hz
    by_contra hn
    have heq : f z = z := f.injective (hffix hn)
    exact hn (heq.symm ▸ hz)
  obtain ⟨H, hH, hH0, hH1, hHfix, hHbox, hHside, hHplane⟩ :=
    exists_diskMap_halfspace_homotopy hP f.continuous hffix hfbox
      (fun z => (hfside z).mpr)
  have hHplane' : ∀ z t, z.2 = 0 → (H (z, t)).2 = 0 :=
    hHplane (fun z => (hfplane z).mpr)
  let A : (Plane × ℝ) ≃ₗ[ℝ] (Plane × ℝ) :=
    (LinearEquiv.refl ℝ Plane).prodCongr (LinearEquiv.smulOfNeZero ℝ ℝ δ hδ.ne')
  let R := A.toContinuousLinearEquiv.toHomeomorph
  have hRapp : ∀ z, R z = (z.1, δ * z.2) := fun _ => rfl
  have hR0 : ∀ x, R (x, 0) = (x, 0) := fun x => by rw [hRapp, mul_zero]
  have hRi0 : ∀ x, R.symm (x, 0) = (x, 0) := fun x => by
    apply R.injective
    rw [R.apply_symm_apply, hR0]
  have hRpl : IsPLHomeomorphOn R univ univ :=
    isPLHomeomorphOn_univ_of_affineEquiv A.toAffineEquiv
  have hRbox : ∀ z, R z ∈ P ×ˢ Icc (-δ) δ ↔ z ∈ P ×ˢ Icc (-1 : ℝ) 1 := by
    intro z
    change (z.1 ∈ P ∧ -δ ≤ δ * z.2 ∧ δ * z.2 ≤ δ) ↔
      z.1 ∈ P ∧ (-1 : ℝ) ≤ z.2 ∧ z.2 ≤ 1
    have hlo : -δ ≤ δ * z.2 ↔ (-1 : ℝ) ≤ z.2 := by
      simpa only [mul_neg_one] using (mul_le_mul_iff_right₀ hδ (b := -1) (c := z.2))
    have hhi : δ * z.2 ≤ δ ↔ z.2 ≤ 1 := by
      simpa only [mul_one] using (mul_le_mul_iff_right₀ hδ (b := z.2) (c := 1))
    rw [hlo, hhi]
  have hRibox : ∀ z, R.symm z ∈ P ×ˢ Icc (-1 : ℝ) 1 ↔ z ∈ P ×ˢ Icc (-δ) δ := by
    intro z
    rw [← hRbox, R.apply_symm_apply]
  have hRside : ∀ z, 0 ≤ (R z).2 ↔ 0 ≤ z.2 := fun z =>
    mul_nonneg_iff_of_pos_left hδ
  have hRiside : ∀ z, 0 ≤ (R.symm z).2 ↔ 0 ≤ z.2 := fun z => by
    rw [← hRside, R.apply_symm_apply]
  have hRplane : ∀ z, (R z).2 = 0 ↔ z.2 = 0 := fun z => by
    change δ * z.2 = 0 ↔ z.2 = 0
    exact mul_eq_zero_iff_left hδ.ne'
  have hRiplane : ∀ z, (R.symm z).2 = 0 ↔ z.2 = 0 := fun z => by
    rw [← hRplane, R.apply_symm_apply]
  let Φ := (R.symm.trans f).trans R
  let G : (Plane × ℝ) × unitInterval → Plane × ℝ := fun w => R (H (R.symm w.1, w.2))
  refine ⟨Φ, (hRpl.homeomorph_symm.trans hf).trans hRpl, ?_, ?_, ?_, ?_,
    G, R.continuous.comp (hH.comp ((R.symm.continuous.comp continuous_fst).prodMk
      continuous_snd)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    change R (f (R.symm (x, 0))) = (u x, 0)
    rw [hRi0, hf0 x hx, hR0]
  · intro z hz
    change R (f (R.symm z)) = z
    rw [hffix (mt (hRibox z).mp hz), id_eq, R.apply_symm_apply]
  · intro z
    exact (hRside _).trans ((hfside _).trans (hRiside z))
  · intro z
    exact (hRplane _).trans ((hfplane _).trans (hRiplane z))
  · intro z
    change R (H (R.symm z, 0)) = z
    rw [hH0, R.apply_symm_apply]
  · intro z
    change R (H (R.symm z, 1)) = R (f (R.symm z))
    rw [hH1]
  · intro t z hz
    change R (H (R.symm z, t)) = z
    have heq : H (R.symm z, t) = R.symm z := hHfix t (mt (hRibox z).mp hz)
    rw [heq, R.apply_symm_apply]
  · intro t z hz
    exact (hRbox _).mpr (hHbox t ((hRibox z).mpr hz))
  · intro z t hz
    exact (hRside _).mpr (hHside _ t ((hRiside z).mpr hz))
  · intro z t hz
    exact (hRplane _).mpr (hHplane' _ t ((hRiplane z).mpr hz))

end DifferentialGeometry.Topology.PiecewiseLinear
