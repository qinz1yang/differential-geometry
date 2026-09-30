import DifferentialGeometry.Analysis.Calculus.Cutoff.EdgeNetworkProfiles
import DifferentialGeometry.Analysis.Calculus.JointCutoffNetwork

set_option autoImplicit false
open Set
open scoped ContDiff

namespace DifferentialGeometry.Analysis

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]

noncomputable def fixedJointCutoffNetwork (Δ : ℝ) (s : ι → ℝ)
    (u : ι → E →L[ℝ] ℝ) (v : E →L[ℝ] ℝ) :
    E → PiLp 2 (fun _ : Option ι => WithLp 2 (ℝ × ℝ)) :=
  jointCutoffNetwork Δ s edgeCoordinateProfile edgeHeightProfile jointHeightProfile edgeSumProfile u v

theorem contDiff_fixedJointCutoffNetwork (Δ : ℝ) (s : ι → ℝ)
    (u : ι → E →L[ℝ] ℝ) (v : E →L[ℝ] ℝ) : ContDiff ℝ ∞ (fixedJointCutoffNetwork Δ s u v) :=
  contDiff_jointCutoffNetwork edgeProfiles_contDiff.1 edgeProfiles_contDiff.2.1
    edgeProfiles_contDiff.2.2.1 edgeProfiles_contDiff.2.2.2 Δ s u v

theorem fixedJointCutoffNetwork_bounds {Δ : ℝ} (hΔ : 1 ≤ Δ)
    (s : ι → ℝ) (hs : ∀ i, s i ∈ Icc (1 / 2) 2)
    (u : ι → E →L[ℝ] ℝ) (v : E →L[ℝ] ℝ)
    (hu : ∀ i, ‖u i‖ ≤ 1) (hv : ‖v‖ ≤ 1) (x : E) :
    let N : ℝ := (Fintype.card ι : ℝ) + 1
    let K := 10 * N ^ 2 * edgeProfileDerivativeBound ^ 3
    ‖fixedJointCutoffNetwork Δ s u v x‖ ≤ 20 * Real.sqrt N * Δ ∧
      ‖fderiv ℝ (fixedJointCutoffNetwork Δ s u v) x‖ ≤ Real.sqrt N * (2 + 20 * K) ∧
      ‖fderiv ℝ (fderiv ℝ (fixedJointCutoffNetwork Δ s u v)) x‖ ≤ 24 * Real.sqrt N * K / Δ := by
  have hf := edgeProfiles_derivative_le (f := edgeCoordinateProfile) (by simp)
  have hg := edgeProfiles_derivative_le (f := edgeHeightProfile) (by simp)
  have hh := edgeProfiles_derivative_le (f := jointHeightProfile) (by simp)
  have hc := edgeProfiles_derivative_le (f := edgeSumProfile) (by simp)
  exact jointCutoffNetwork_bounds (edgeProfiles_contDiff.1.of_le (by simp))
    (edgeProfiles_contDiff.2.1.of_le (by simp)) (edgeProfiles_contDiff.2.2.1.of_le (by simp))
    (edgeProfiles_contDiff.2.2.2.of_le (by simp)) hΔ edgeProfileDerivativeBound_ge_one
    (fun y => (edgeProfiles_mem_Icc y).1) (fun y => (edgeProfiles_mem_Icc y).2.1)
    (fun y => (edgeProfiles_mem_Icc y).2.2.1) (fun y => (edgeProfiles_mem_Icc y).2.2.2)
    hf.1 hg.1 hh.1 hc.1 hf.2 hg.2 hh.2 hc.2
    edgeProfiles_support.1 edgeProfiles_support.2 s hs u v hu hv x

theorem fixedJointCutoffNetwork_c1_comp_sub_le {Δ : ℝ} (hΔ : 1 ≤ Δ)
    (s : ι → ℝ) (hs : ∀ i, s i ∈ Icc (1 / 2) 2)
    (u : ι → E →L[ℝ] ℝ) (v : E →L[ℝ] ℝ)
    (hu : ∀ i, ‖u i‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {U V : X → E} {x : X}
    (hU : DifferentiableAt ℝ U x) (hV : DifferentiableAt ℝ V x)
    {ε L₀ : ℝ} (hε : 0 ≤ ε) (hL₀ : 0 ≤ L₀)
    (hclose : ‖U x - V x‖ ≤ ε) (hDclose : ‖fderiv ℝ U x - fderiv ℝ V x‖ ≤ ε)
    (hDV : ‖fderiv ℝ V x‖ ≤ L₀) :
    let N : ℝ := (Fintype.card ι : ℝ) + 1
    let K := 10 * N ^ 2 * edgeProfileDerivativeBound ^ 3
    let W := fixedJointCutoffNetwork Δ s u v
    max ‖W (U x) - W (V x)‖ ‖fderiv ℝ (W ∘ U) x - fderiv ℝ (W ∘ V) x‖ ≤
      (Real.sqrt N * (2 + 20 * K) + (24 * Real.sqrt N * K / Δ) * L₀) * ε := by
  have hP0 : 0 ≤ edgeProfileDerivativeBound := le_trans (by norm_num) edgeProfileDerivativeBound_ge_one
  have hΔ0 : 0 ≤ Δ := le_trans (by norm_num) hΔ
  have hW : ContDiff ℝ 2 (fixedJointCutoffNetwork Δ s u v) :=
    (contDiff_fixedJointCutoffNetwork Δ s u v).of_le (by simp)
  have hDW : Differentiable ℝ (fderiv ℝ (fixedJointCutoffNetwork Δ s u v)) :=
    (hW.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiable (by norm_num)
  have hb (y : E) := fixedJointCutoffNetwork_bounds hΔ s hs u v hu hv y
  exact c1_comp_sub_le_of_derivative_bounds (hW.differentiable (by norm_num)) hDW hU hV
    (by positivity) (by positivity) hL₀ hε (fun y => (hb y).2.1) (fun y => (hb y).2.2)
    hclose hDclose hDV

theorem fixedJointCutoffNetwork_low_height {Δ : ℝ} (hΔ : 0 < Δ)
    (s : ι → ℝ) (u : ι → E →L[ℝ] ℝ) (v : E →L[ℝ] ℝ) {x : E}
    (hx : v x < 3 * Δ / 20) :
    fixedJointCutoffNetwork Δ s u v x none = 0 ∧
      ∀ i, fixedJointCutoffNetwork Δ s u v x (some i) =
        WithLp.toLp 2 (s i * (u i x * edgeCoordinateProfile (Δ⁻¹ * u i x)),
          s i * edgeCoordinateProfile (Δ⁻¹ * u i x)) := by
  have harg : Δ⁻¹ * v x < 3 / 20 := by
    rw [mul_comm, ← div_eq_mul_inv]
    exact (div_lt_iff₀ hΔ).mpr (by linarith)
  have hb := edgeProfiles_low_height harg
  constructor
  · rw [fixedJointCutoffNetwork, jointCutoffNetwork_none]
    simp only [jointEdgeCutoff, hb.2, zero_mul, mul_zero]
    rfl
  · intro i
    rw [fixedJointCutoffNetwork, jointCutoffNetwork_some]
    simp only [edgeCutoff, hb.1, mul_one]

end DifferentialGeometry.Analysis
