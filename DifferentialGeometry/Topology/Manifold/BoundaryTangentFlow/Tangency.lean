import DifferentialGeometry.Topology.Manifold.BoundaryCollar.Conormal
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Geometry.Manifold.Instances.Icc

/-!
# Tangency to the boundary: curve form and coordinate form

For a manifold `M` modelled on the half-space `𝓡∂ (n + 1)` and a boundary point `y`, a tangent vector
`v ∈ T_y M` is tangent to `∂M` in the *curve form* (as in the chapter-14 assembly statements) if
some smooth curve `γ : ℝ → M` with `γ 0 = y`, staying in `∂M`, has velocity `v` at `0`; it is tangent
in the *coordinate form* if its normal coordinate (in the preferred chart at `y`) vanishes. The two
forms agree (`proj_zero_mfderiv_eq_zero_of_boundary_curve`, `exists_boundary_curve_of_proj_zero`), and
the coordinate form does not depend on the chart (`proj_zero_mfderiv_extChartAt_eq_zero_iff`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Manifold.BoundaryTangentFlow

open DifferentialGeometry.Manifold.BoundaryCollar

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [IsManifold (𝓡∂ (n + 1)) ∞ M]

/-- The normal coordinate of a tangent vector at a boundary point vanishes in one chart iff it
vanishes in the preferred chart at that point. -/
theorem proj_zero_mfderiv_extChartAt_eq_zero_iff (p : M) {y : M}
    (hy : y ∈ (chartAt (EuclideanHalfSpace (n + 1)) p).source)
    (hb : (𝓡∂ (n + 1)).IsBoundaryPoint y) {v : TangentSpace (𝓡∂ (n + 1)) y} :
    EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (n + 1))
        (mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
          (extChartAt (𝓡∂ (n + 1)) p) y v) = 0 ↔
      EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (n + 1)) v = 0 := by
  obtain ⟨c, hc, he⟩ := mfderiv_chartHeight_eq_pos_smul_proj (n := n + 1) p hy hb
  rw [mfderiv_chartHeight (n := n + 1) p hy] at he
  have h := congrArg (fun L : TangentSpace (𝓡∂ (n + 1)) y →L[ℝ] ℝ => L v) he
  change EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (n + 1))
      (mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
        (extChartAt (𝓡∂ (n + 1)) p) y v) =
      c * EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (n + 1)) v at h
  rw [h]
  exact mul_eq_zero.trans (or_iff_right hc.ne')

/-- The derivative of the height function of the preferred chart at its center. -/
theorem mfderiv_chartHeight_self (y : M) :
    mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) (chartHeight (n := n + 1) y) y =
      EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (n + 1)) := by
  rw [mfderiv_chartHeight (n := n + 1) y (mem_chart_source _ y), mfderiv_extChartAt_self]
  exact ContinuousLinearMap.comp_id _

/-- **Curve form ⇒ coordinate form.** The velocity at `0` of a smooth curve staying in the boundary
has vanishing normal coordinate. -/
theorem proj_zero_mfderiv_eq_zero_of_boundary_curve {γ : ℝ → M}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) (𝓡∂ (n + 1)) ∞ γ)
    (hγb : ∀ t, (𝓡∂ (n + 1)).IsBoundaryPoint (γ t)) :
    EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (n + 1))
      (mfderiv 𝓘(ℝ, ℝ) (𝓡∂ (n + 1)) γ 0 1) = 0 := by
  let y := γ 0
  have hsrc : ∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ (chartAt (EuclideanHalfSpace (n + 1)) y).source :=
    hγ.continuous.continuousAt.preimage_mem_nhds
      ((chartAt (EuclideanHalfSpace (n + 1)) y).open_source.mem_nhds (mem_chart_source _ y))
  have heq : (chartHeight (n := n + 1) y) ∘ γ =ᶠ[𝓝 (0 : ℝ)] (fun _ => (0 : ℝ)) := by
    filter_upwards [hsrc] with t ht
    exact (chartHeight_eq_zero_iff (n := n + 1) y ht).mpr (hγb t)
  have hh := mfderiv_comp (0 : ℝ)
    (((contMDiffOn_chartHeight (n := n + 1) (k := ∞) y).contMDiffAt
      ((chartAt (EuclideanHalfSpace (n + 1)) y).open_source.mem_nhds
        (mem_chart_source _ y))).mdifferentiableAt (by simp))
    ((hγ 0).mdifferentiableAt (by simp))
  erw [heq.mfderiv_eq, mfderiv_const, mfderiv_chartHeight_self] at hh
  have h1 := congrArg (fun L : ℝ →L[ℝ] ℝ => L 1) hh
  exact h1.symm

/-- **Coordinate form ⇒ curve form.** A tangent vector at a boundary point with vanishing normal
coordinate is the velocity of a smooth curve `ℝ → M` staying in the boundary. -/
theorem exists_boundary_curve_of_proj_zero {y : M} (hb : (𝓡∂ (n + 1)).IsBoundaryPoint y)
    (v : TangentSpace (𝓡∂ (n + 1)) y)
    (hv : EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (n + 1)) v = 0) :
    ∃ γ : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) (𝓡∂ (n + 1)) ∞ γ ∧ γ 0 = y ∧
      (∀ t, (𝓡∂ (n + 1)).IsBoundaryPoint (γ t)) ∧
        mfderiv 𝓘(ℝ, ℝ) (𝓡∂ (n + 1)) γ 0 1 = v := by
  let I := 𝓡∂ (n + 1)
  let E := EuclideanSpace ℝ (Fin (n + 1))
  let e := extChartAt I y
  let z₀ : E := e y
  let w : E := v
  have hz₀ : z₀ 0 = 0 := (chartHeight_eq_zero_iff (n := n + 1) y (mem_chart_source _ y)).mpr hb
  have hw : w 0 = 0 := hv
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhdsWithin_iff.mp (extChartAt_target_mem_nhdsWithin (I := I) y)
  set c : ℝ := r / (‖w‖ + 1) with hcdef
  have hc : 0 < c := div_pos hr (by positivity)
  have hcw : c * ‖w‖ < r := by
    rw [hcdef, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [norm_nonneg w]
  let ℓ : ℝ → E := fun t => z₀ + (c * Real.sin (t / c)) • w
  have hcoef : ContDiff ℝ ∞ (fun t : ℝ => c * Real.sin (t / c)) :=
    contDiff_const.mul (Real.contDiff_sin.comp (contDiff_id.div_const c))
  have hℓ : ContDiff ℝ ∞ ℓ := contDiff_const.add (hcoef.smul contDiff_const)
  have hℓ0 : ℓ 0 = z₀ := by simp [ℓ]
  have hℓz (t : ℝ) : ℓ t 0 = 0 := by
    change z₀ 0 + (c * Real.sin (t / c)) * w 0 = 0
    rw [hz₀, hw, mul_zero, add_zero]
  have hℓt (t : ℝ) : ℓ t ∈ e.target := by
    apply hball
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_ball, dist_eq_norm]
      change ‖z₀ + (c * Real.sin (t / c)) • w - z₀‖ < r
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_mul, abs_of_pos hc]
      calc c * |Real.sin (t / c)| * ‖w‖ ≤ c * 1 * ‖w‖ := by
            gcongr
            exact Real.abs_sin_le_one _
        _ = c * ‖w‖ := by ring
        _ < r := hcw
    · rw [range_modelWithCornersEuclideanHalfSpace]
      change 0 ≤ ℓ t 0
      rw [hℓz t]
  let γ : ℝ → M := e.symm ∘ ℓ
  have hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ :=
    (contMDiffOn_extChartAt_symm (I := I) (n := ∞) y).comp_contMDiff hℓ.contMDiff hℓt
  have hγsrc (t : ℝ) : γ t ∈ (chartAt (EuclideanHalfSpace (n + 1)) y).source := by
    have h := e.map_target (hℓt t)
    rw [extChartAt_source] at h
    exact h
  refine ⟨γ, hγ, ?_, ?_, ?_⟩
  · change e.symm (ℓ 0) = y
    rw [hℓ0]
    exact extChartAt_to_inv (I := I) y
  · intro t
    apply (chartHeight_eq_zero_iff (n := n + 1) y (hγsrc t)).mp
    change e (e.symm (ℓ t)) 0 = 0
    rw [e.right_inv (hℓt t)]
    exact hℓz t
  · have hd : HasDerivAt ℓ w 0 := by
      have hs : HasDerivAt (fun t : ℝ => c * Real.sin (t / c)) 1 0 := by
        have h1 := ((Real.hasDerivAt_sin (0 / c)).comp (0 : ℝ)
          ((hasDerivAt_id (0 : ℝ)).div_const c)).const_mul c
        convert h1 using 1
        · funext t
          rfl
        · rw [zero_div, Real.cos_zero, one_mul]
          field_simp
      have h2 := (hs.smul_const w).const_add z₀
      simpa only [one_smul] using h2
    have hcurve : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ℓ 0
        ((1 : ℝ →L[ℝ] ℝ).smulRight w) := hd.hasFDerivAt.hasMFDerivAt
    have hinv := (mdifferentiableWithinAt_extChartAt_symm (I := I) (hℓt 0)).hasMFDerivWithinAt
    have hcomp := hinv.comp (0 : ℝ) (hcurve.hasMFDerivWithinAt (s := univ))
      (fun t _ => extChartAt_target_subset_range (I := I) y (hℓt t))
    have hγd : HasMFDerivAt 𝓘(ℝ, ℝ) I γ 0
        ((mfderivWithin 𝓘(ℝ, E) I e.symm (range I) (ℓ 0)).comp
          ((1 : ℝ →L[ℝ] ℝ).smulRight w)) :=
      hasMFDerivWithinAt_univ.mp hcomp
    rw [hγd.mfderiv]
    change (mfderivWithin 𝓘(ℝ, E) I e.symm (range I) (ℓ 0)) (((1 : ℝ →L[ℝ] ℝ).smulRight w) 1) = v
    rw [ContinuousLinearMap.smulRight_apply, one_apply_eq_self, one_smul]
    have hid : mfderivWithin 𝓘(ℝ, E) I e.symm (range I) (ℓ 0) =
        ContinuousLinearMap.id ℝ E := by
      rw [hℓ0]
      exact mfderivWithin_range_extChartAt_symm (I := I) (x := y)
    rw [hid]
    rfl

end DifferentialGeometry.Manifold.BoundaryTangentFlow
