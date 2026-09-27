/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Manifold.SphereDirection
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open Set Metric Manifold
open scoped ContDiff Manifold

namespace DifferentialGeometry.Topology.PiecewiseLinear

open DifferentialGeometry.Topology.Manifold

theorem exists_sphereProd_band_openPartialHomeomorph {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 3 / 2) :
    ∃ j : OpenPartialHomeomorph (sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 × ℝ)
      (EuclideanSpace ℝ (Fin 2)),
      j.source = univ ∧ j.target = {w | |‖w‖ - 3 / 2| < ε} ∧
      ContMDiffOn ((𝓡 1).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞ j univ ∧
      ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ((𝓡 1).prod 𝓘(ℝ, ℝ)) ∞ j.symm j.target ∧
      ∃ κ : ℝ, 0 < κ ∧ κ < 1 ∧
        j '' (univ ×ˢ Icc (0 : ℝ) 1) = {w | 3 / 2 ≤ ‖w‖ ∧ ‖w‖ ≤ 3 / 2 + ε * κ} := by
  classical
  let τ : ℝ → ℝ := fun s => (Real.exp s - 1) / (Real.exp s + 1)
  let τi : ℝ → ℝ := fun u => Real.log ((1 + u) / (1 - u))
  have hτ' : ∀ s, τ s = 1 - 2 / (Real.exp s + 1) := by
    intro s
    have : Real.exp s + 1 ≠ 0 := by positivity
    change (Real.exp s - 1) / (Real.exp s + 1) = _
    field_simp
    ring
  have hτb : ∀ s, -1 < τ s ∧ τ s < 1 := by
    intro s
    have he := Real.exp_pos s
    have h2 : 0 < 2 / (Real.exp s + 1) := by positivity
    have h3 : 2 / (Real.exp s + 1) < 2 := by
      rw [div_lt_iff₀ (by positivity)]
      linarith
    rw [hτ']
    constructor <;> linarith
  have hτmono : StrictMono τ := by
    intro s t hst
    rw [hτ', hτ']
    have h1 := Real.exp_lt_exp.mpr hst
    have : 2 / (Real.exp t + 1) < 2 / (Real.exp s + 1) :=
      div_lt_div_of_pos_left two_pos (by positivity) (by linarith)
    linarith
  have hττi : ∀ u, -1 < u → u < 1 → τ (τi u) = u := by
    intro u h1 h2
    have hpos : 0 < (1 + u) / (1 - u) := div_pos (by linarith) (by linarith)
    change (Real.exp (Real.log ((1 + u) / (1 - u))) - 1) /
      (Real.exp (Real.log ((1 + u) / (1 - u))) + 1) = u
    rw [Real.exp_log hpos]
    have h3 : (1 : ℝ) - u ≠ 0 := by linarith
    field_simp
    ring
  have hτiτ : ∀ s, τi (τ s) = s := by
    intro s
    have he := Real.exp_pos s
    have h1 : (1 + τ s) / (1 - τ s) = Real.exp s := by
      change (1 + (Real.exp s - 1) / (Real.exp s + 1)) /
        (1 - (Real.exp s - 1) / (Real.exp s + 1)) = Real.exp s
      have h2 : Real.exp s + 1 ≠ 0 := by positivity
      field_simp
      ring
    change Real.log ((1 + τ s) / (1 - τ s)) = s
    rw [h1, Real.log_exp]
  have hτc : ContDiff ℝ ∞ τ := by
    have h1 : ContDiff ℝ ∞ Real.exp := Real.contDiff_exp
    exact (h1.sub contDiff_const).div (h1.add contDiff_const) fun s => by positivity
  let v₀ : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 :=
    ⟨EuclideanSpace.single 0 1, by simp⟩
  let T : Set (EuclideanSpace ℝ (Fin 2)) := {w | |‖w‖ - 3 / 2| < ε}
  have hTpos : ∀ w ∈ T, 0 < ‖w‖ := by
    intro w hw
    have : |‖w‖ - 3 / 2| < ε := hw
    rw [abs_lt] at this
    linarith
  have hTu : ∀ w ∈ T, -1 < (‖w‖ - 3 / 2) / ε ∧ (‖w‖ - 3 / 2) / ε < 1 := by
    intro w hw
    have : |‖w‖ - 3 / 2| < ε := hw
    rw [abs_lt] at this
    constructor
    · rw [lt_div_iff₀ hε]
      linarith
    · rw [div_lt_iff₀ hε]
      linarith
  have hrpos : ∀ s, 0 < 3 / 2 + ε * τ s := by
    intro s
    have := hτb s
    nlinarith
  have hnorm : ∀ q : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 × ℝ,
      ‖(3 / 2 + ε * τ q.2) • (q.1 : EuclideanSpace ℝ (Fin 2))‖ = 3 / 2 + ε * τ q.2 := by
    intro q
    rw [norm_smul, norm_eq_of_mem_sphere q.1, mul_one, Real.norm_of_nonneg (hrpos _).le]
  let _ : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 1 + 1) := ⟨by simp⟩
  have hscal : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, ℝ) ∞
      (fun w : EuclideanSpace ℝ (Fin 2) => τi ((‖w‖ - 3 / 2) / ε)) T := by
    refine contMDiffOn_iff_contDiffOn.mpr fun w hw => ?_
    have hw0 : w ≠ 0 := norm_pos_iff.mp (hTpos w hw)
    obtain ⟨hu1, hu2⟩ := hTu w hw
    have hn : ContDiffAt ℝ ∞ (fun w : EuclideanSpace ℝ (Fin 2) => (‖w‖ - 3 / 2) / ε) w :=
      ((contDiffAt_norm ℝ hw0).sub contDiffAt_const).div_const ε
    have hq : ContDiffAt ℝ ∞ (fun u : ℝ => (1 + u) / (1 - u)) ((‖w‖ - 3 / 2) / ε) :=
      (contDiffAt_const.add contDiffAt_id).div (contDiffAt_const.sub contDiffAt_id)
        (by change (1 : ℝ) - (‖w‖ - 3 / 2) / ε ≠ 0; linarith)
    have hl : ContDiffAt ℝ ∞ Real.log ((1 + (‖w‖ - 3 / 2) / ε) / (1 - (‖w‖ - 3 / 2) / ε)) :=
      Real.contDiffAt_log.mpr (div_pos (by linarith) (by linarith)).ne'
    exact (hl.comp w (hq.comp w hn)).contDiffWithinAt
  have hinvs : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ((𝓡 1).prod 𝓘(ℝ, ℝ)) ∞
      (fun w : EuclideanSpace ℝ (Fin 2) => (sphereDirection v₀ w, τi ((‖w‖ - 3 / 2) / ε))) T :=
    ContMDiffOn.prodMk ((contMDiffOn_sphereDirection v₀).mono fun w hw =>
      norm_pos_iff.mp (hTpos w hw)) hscal
  have hfs : ContMDiff ((𝓡 1).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞
      (fun q : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 × ℝ =>
        (3 / 2 + ε * τ q.2) • (q.1 : EuclideanSpace ℝ (Fin 2))) := by
    have hr : ContMDiff ((𝓡 1).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
        (fun q : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 × ℝ => 3 / 2 + ε * τ q.2) :=
      (contDiff_const.add (contDiff_const.mul hτc)).contMDiff.comp contMDiff_snd
    have hz : ContMDiff ((𝓡 1).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞
        (fun q : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 × ℝ =>
          (q.1 : EuclideanSpace ℝ (Fin 2))) :=
      contMDiff_coe_sphere.comp contMDiff_fst
    exact hr.smul hz
  let j : OpenPartialHomeomorph (sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 × ℝ)
      (EuclideanSpace ℝ (Fin 2)) :=
    { toFun := fun q => (3 / 2 + ε * τ q.2) • (q.1 : EuclideanSpace ℝ (Fin 2))
      invFun := fun w => (sphereDirection v₀ w, τi ((‖w‖ - 3 / 2) / ε))
      source := univ
      target := T
      map_source' := fun q _ => by
        change |‖(3 / 2 + ε * τ q.2) • (q.1 : EuclideanSpace ℝ (Fin 2))‖ - 3 / 2| < ε
        rw [hnorm, add_sub_cancel_left, abs_mul, abs_of_pos hε]
        have h1 : |τ q.2| < 1 := abs_lt.mpr (hτb q.2)
        nlinarith [abs_nonneg (τ q.2)]
      map_target' := fun _ _ => mem_univ _
      left_inv' := fun q _ => by
        apply Prod.ext
        · exact sphereDirection_pos_smul v₀ q.1 (hrpos q.2)
        · change τi ((‖(3 / 2 + ε * τ q.2) • (q.1 : EuclideanSpace ℝ (Fin 2))‖ - 3 / 2) / ε) =
            q.2
          rw [hnorm, add_sub_cancel_left, mul_div_cancel_left₀ _ hε.ne', hτiτ]
      right_inv' := fun w hw => by
        change (3 / 2 + ε * τ (τi ((‖w‖ - 3 / 2) / ε))) •
          (sphereDirection v₀ w : EuclideanSpace ℝ (Fin 2)) = w
        rw [hττi _ (hTu w hw).1 (hTu w hw).2, mul_div_cancel₀ _ hε.ne', add_sub_cancel]
        exact norm_smul_sphereDirection v₀ (norm_pos_iff.mp (hTpos w hw))
      open_source := isOpen_univ
      open_target := isOpen_lt (continuous_abs.comp (continuous_norm.sub continuous_const))
        continuous_const
      continuousOn_toFun := hfs.continuous.continuousOn
      continuousOn_invFun := hinvs.continuousOn }
  have hτ0 : τ 0 = 0 := by
    change (Real.exp 0 - 1) / (Real.exp 0 + 1) = 0
    simp
  have hτ1 : 0 < τ 1 := by
    change 0 < (Real.exp 1 - 1) / (Real.exp 1 + 1)
    have := Real.one_lt_exp_iff.mpr one_pos
    exact div_pos (by linarith) (by positivity)
  refine ⟨j, rfl, rfl, hfs.contMDiffOn, hinvs, τ 1, hτ1, (hτb 1).2, ?_⟩
  ext w
  constructor
  · rintro ⟨q, ⟨-, hq⟩, rfl⟩
    change 3 / 2 ≤ ‖(3 / 2 + ε * τ q.2) • (q.1 : EuclideanSpace ℝ (Fin 2))‖ ∧
      ‖(3 / 2 + ε * τ q.2) • (q.1 : EuclideanSpace ℝ (Fin 2))‖ ≤ 3 / 2 + ε * τ 1
    rw [hnorm]
    have h0 : τ 0 ≤ τ q.2 := hτmono.monotone hq.1
    have h1 : τ q.2 ≤ τ 1 := hτmono.monotone hq.2
    rw [hτ0] at h0
    constructor <;> nlinarith
  · rintro ⟨hw1, hw2⟩
    have hwT : w ∈ T := by
      change |‖w‖ - 3 / 2| < ε
      rw [abs_lt]
      have := (hτb 1).2
      constructor <;> nlinarith
    refine ⟨j.symm w, ⟨mem_univ _, ?_⟩, j.right_inv hwT⟩
    set u := (‖w‖ - 3 / 2) / ε with hudef
    have hu0 : 0 ≤ u := div_nonneg (by linarith) hε.le
    have hu1 : u ≤ τ 1 := by
      rw [hudef, div_le_iff₀ hε]
      linarith
    have hτs : τ (τi u) = u := hττi u (by linarith) (by linarith [(hτb 1).2])
    change 0 ≤ τi u ∧ τi u ≤ 1
    constructor
    · by_contra hn
      have := hτmono (not_le.mp hn)
      rw [hτs, hτ0] at this
      linarith
    · by_contra hn
      have := hτmono (not_le.mp hn)
      rw [hτs] at this
      linarith

end DifferentialGeometry.Topology.PiecewiseLinear
