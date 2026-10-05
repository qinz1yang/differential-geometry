import DifferentialGeometry.Geometry.Metric.ActualCloudCutoffAssembly
import DifferentialGeometry.Analysis.Calculus.Cutoff.UniformAxisCutoffApplications
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Consumers of CFS31.
* `smoothTransition_exists_deriv_bound`: Mathlib's `Real.smoothTransition` has a bounded derivative, so it is an
  admissible CFS22/CFS23/CFS31 profile with some `P ≥ 1`.
* `markerLocalitySourceCutoff_consumer`: an explicit two-point instance in `ℝ²` (one two-stratum block, full marker
  at both points): the source cutoff is one at the core point (`|η| = 0`), its derivative there obeys `80 N P²/ρ`,
  and it VANISHES at the point with `|η| = 8 > 13/2` — the strict stage-one localization.
* `actualCloud_first_stage_identity_off_core`: off the stage-one core the first stage does not move the original
  map (`ψ₁(F p) = 0`, so the FC32 adjustment is the identity there).
* `actualCloud_marker_budget_consumer`: explicit (MB) constants for `N = 1`, `P = 1`. -/

set_option autoImplicit false
noncomputable section
open Set Metric Filter Topology DifferentialGeometry.Analysis
open scoped ContDiff BigOperators

namespace GC.MetricGeometry

/-- `Real.smoothTransition` has a bounded derivative. -/
theorem smoothTransition_exists_deriv_bound :
    ∃ P : ℝ, 1 ≤ P ∧ ∀ t, |deriv Real.smoothTransition t| ≤ P := by
  have hcd : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hcd.continuousOn (s := Icc (0 : ℝ) 1))
  refine ⟨max C 1, le_max_right _ _, fun t => ?_⟩
  by_cases h0 : t < 0
  · have hev : Real.smoothTransition =ᶠ[𝓝 t] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds h0] with s hs
      exact Real.smoothTransition.zero_of_nonpos (le_of_lt hs)
    rw [hev.deriv_eq, deriv_const, abs_zero]
    exact le_trans zero_le_one (le_max_right _ _)
  by_cases h1 : 1 < t
  · have hev : Real.smoothTransition =ᶠ[𝓝 t] fun _ => 1 := by
      filter_upwards [Ioi_mem_nhds h1] with s hs
      exact Real.smoothTransition.one_of_one_le (le_of_lt hs)
    rw [hev.deriv_eq, deriv_const, abs_zero]
    exact le_trans zero_le_one (le_max_right _ _)
  have ht : t ∈ Icc (0 : ℝ) 1 := ⟨le_of_not_gt h0, le_of_not_gt h1⟩
  have := hC t ht
  rw [Real.norm_eq_abs] at this
  exact this.trans (le_max_left _ _)

/-- Off the stage-one core the source cutoff vanishes at the original image, so the first stage is the identity
there. -/
theorem actualCloud_first_stage_identity_off_core {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {I : Type*} [Fintype I] {E : I → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)] {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hχ0 : ∀ t ≤ 0, χ t = 0) (hχ1 : ∀ t, 1 ≤ t → χ t = 1)
    (hχI : ∀ t, χ t ∈ Icc (0 : ℝ) 1) {P : ℝ} (hP1 : 1 ≤ P) (hP : ∀ t, |deriv χ t| ≤ P) (N : ℕ)
    (u : ∀ i, H →L[ℝ] E i) (v : I → H →L[ℝ] ℝ) (hu : ∀ i, ‖u i‖ ≤ 1) (hv : ∀ i, ‖v i‖ ≤ 1)
    {X : Type*} (R : I → ℝ) (hR : ∀ i, 0 < R i) (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p)
    (U : I → Set X) (η : ∀ i, X → E i) (ζ : I → X → ℝ) (F : X → H)
    (hζU : ∀ i p, p ∉ U i → ζ i p = 0)
    (hblock : ∀ i p, u i (F p) = (R i * ζ i p) • η i p ∧ v i (F p) = R i * ζ i p)
    (hcount : ∀ p, (Finset.univ.filter fun i => 0 < ζ i p).card ≤ N)
    (hcomp : ∀ i p, 0 < ζ i p → 3 / 4 * R i ≤ ρ p ∧ ρ p ≤ 5 / 4 * R i)
    (hplateau : ∀ i p, p ∈ U i → ‖η i p‖ < 6 → ζ i p = 1)
    (Q : Submodule ℝ H) [Q.HasOrthogonalProjection] (Pst : H → H) (p : X)
    (hp : ∀ i, p ∈ U i → 13 / 2 < ‖η i p‖) :
    markerLocalitySourceCutoff χ R u v (F p) = 0 ∧
      adjustmentMap Q Pst (markerLocalitySourceCutoff χ R u v) (F p) = F p := by
  have hzero : markerLocalitySourceCutoff χ R u v (F p) = 0 := by
    by_contra hne
    obtain ⟨i, hiU, hη⟩ := (markerLocalitySourceCutoff_row hχ hχ0 hχ1 hχI hP1 hP N u v hu hv R
      hR ρ hρ U η ζ F hζU hblock hcount hcomp hplateau).2.2.2.1 p (subset_tsupport _ hne)
    exact absurd (hp i hiU) (not_lt.mpr hη)
  refine ⟨hzero, ?_⟩
  rw [adjustmentMap_apply, hzero, zero_smul, add_zero]

/-- An explicit instance of the source first cutoff in `ℝ²`. -/
theorem markerLocalitySourceCutoff_consumer :
    ∃ P : ℝ, 1 ≤ P ∧
      let e : Fin 2 → EuclideanSpace ℝ (Fin 2) := fun j => EuclideanSpace.single j 1
      let u : ∀ _ : Unit, EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ := fun _ => innerSL ℝ (e 0)
      let v : Unit → EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ := fun _ => innerSL ℝ (e 1)
      markerLocalitySourceCutoff Real.smoothTransition (fun _ => 1) u v (e 1) = 1 ∧
        ‖fderiv ℝ (markerLocalitySourceCutoff Real.smoothTransition (fun _ => 1) u v) (e 1)‖ ≤
          80 * 1 * P ^ 2 / 1 ∧
        markerLocalitySourceCutoff Real.smoothTransition (fun _ => 1) u v ((8 : ℝ) • e 0 + e 1) = 0 := by
  obtain ⟨P, hP1, hP⟩ := smoothTransition_exists_deriv_bound
  refine ⟨P, hP1, ?_⟩
  intro e u v
  have hcoord : ∀ j (z : EuclideanSpace ℝ (Fin 2)), innerSL ℝ (e j) z = z j := by
    intro j z
    simp only [e, innerSL_apply_apply, EuclideanSpace.inner_single_left, map_one, one_mul]
  have hnorm : ∀ j, ‖innerSL ℝ (e j)‖ ≤ 1 := by
    intro j
    rw [innerSL_apply_norm]
    simp [e]
  let F : Bool → EuclideanSpace ℝ (Fin 2) := fun b => if b then e 1 else (8 : ℝ) • e 0 + e 1
  let η : ∀ _ : Unit, Bool → ℝ := fun _ b => if b then 0 else 8
  have hF0 : ∀ b, F b 0 = η () b := by
    intro b
    cases b <;> simp [F, η, e]
  have hF1 : ∀ b, F b 1 = 1 := by
    intro b
    cases b <;> simp [F, e]
  have hprof := smoothTransition_cfs_profile
  have hrow := markerLocalitySourceCutoff_row hprof.1 hprof.2.1 hprof.2.2.1 hprof.2.2.2 hP1 hP 1
    u v (fun _ => hnorm 0) (fun _ => hnorm 1) (X := Bool) (fun _ => 1) (fun _ => one_pos)
    (fun _ => 1) (fun _ => one_pos) (fun _ => univ) η (fun _ _ => 1) F
    (fun _ p hp => absurd (mem_univ p) hp)
    (fun _ p => ⟨by simp [u, hcoord, hF0, η], by simp only [v, hcoord, hF1, mul_one]⟩)
    (fun _ => by simp)
    (fun _ _ _ => by norm_num) (fun _ _ _ _ => rfl)
  refine ⟨?_, ?_, ?_⟩
  · exact hrow.2.2.1 true ⟨(), mem_univ _, by simp [η]⟩
  · have h := hrow.2.2.2.2.1 true
    have hFt : F true = e 1 := rfl
    rw [hFt] at h
    simpa using h
  · by_contra hne
    obtain ⟨i, -, hη⟩ := hrow.2.2.2.1 false (subset_tsupport _ hne)
    simp [η] at hη
    norm_num at hη

/-- Explicit (MB) constants for `N = 1`, `P = 1`: `κ = 1/2000`, `c₁ = c₂ = t₂ = t₃ = 1/2500`, `c₃ = 1/512`. -/
theorem actualCloud_marker_budget_consumer :
    80 * (1 : ℝ) * 1 ^ 2 ≤ 10000 * (1 + 1) ^ 2 * 1 ^ 4 ∧ (1 / 2500 : ℝ) ≤ 1 / 512 ∧
      (1 / 2500 : ℝ) ≤ 4 * (1 / (1000 * (1 + 1) * 1 ^ 2)) / 5 := by
  have h := actualCloud_marker_budget (N := 1) (P := 1) (by norm_num) le_rfl
    (c₁ := 1 / 2500) (c₂ := 1 / 2500) (c₃ := 1 / 512) (t₂ := 1 / 2500) (t₃ := 1 / 2500)
    le_rfl (by norm_num) (by norm_num)
  exact ⟨h.1, h.2.2.2.1, h.2.2.2.2.2.2.1⟩

end GC.MetricGeometry
