import DifferentialGeometry.Analysis.Sobolev.Tools.Mollification.Holder
import DifferentialGeometry.Analysis.Sobolev.Tools.Mollification.WeakDerivative
import DifferentialGeometry.Analysis.Sobolev.Euclidean.LocallyLipschitz.ChainRule
import Mathlib.MeasureTheory.Integral.DominatedConvergence


noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace DifferentialGeometry.Analysis.Sobolev

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

theorem lipschitzWith_mollifyEps {ε : ℝ} (hε : 0 < ε)
    {u : E → ℝ} {C : ℝ≥0} (hu : LipschitzWith C u) :
    LipschitzWith C (mollifyEps hε u) :=
  holderWith_one.mp (holderWith_mollifyEps hε zero_lt_one hu.holderWith)

theorem ae_tendsto_partial_mollifyEps_of_lipschitzWith
    {ι : Type*} {l : Filter ι} {ε : ι → ℝ}
    (hε : ∀ n, 0 < ε n) (hεlim : Tendsto ε l (𝓝 0))
    {u : E → ℝ} {C : ℝ≥0} (hu : LipschitzWith C u) (i : Fin d) :
    ∀ᵐ x ∂volume, Tendsto
      (fun n => fderiv ℝ (mollifyEps (hε n) u) x (EuclideanSpace.single i 1))
      l (𝓝 (fderiv ℝ u x (EuclideanSpace.single i 1))) := by
  let g : E → ℝ := fun x => fderiv ℝ u x (EuclideanSpace.single i 1)
  have hg : LocallyIntegrable g volume := by
    apply (memLp_top_of_bound
      (measurable_fderiv_apply_const ℝ u (EuclideanSpace.single i 1)).aestronglyMeasurable
      ((C : ℝ) * ‖EuclideanSpace.single i (1 : ℝ)‖) ?_).locallyIntegrable le_top
    filter_upwards with x
    exact ((fderiv ℝ u x).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hu) (norm_nonneg _))
  have hweak := Euclidean.hasWeakPartialDeriv_fderiv_of_lipschitzOnWith
    isOpen_univ hu.lipschitzOnWith i
  filter_upwards [ae_tendsto_mollifyEps_of_locallyIntegrable hε hεlim hg] with x hx
  simpa only [mollifyEps_partial_eq_mollifyEps_weakPartial
    _ hu.continuous.locallyIntegrable hweak, g] using hx

theorem tendsto_integral_norm_mollifyEps_sub_of_lipschitzWith
    {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n) (hεlim : Tendsto ε atTop (𝓝 0))
    {u : E → ℝ} {C : ℝ≥0} (hu : LipschitzWith C u)
    {s : Set E} [IsFiniteMeasure (volume.restrict s)] :
    Tendsto (fun n => ∫ x in s, ‖mollifyEps (hε n) u x - u x‖)
      atTop (𝓝 0) := by
  have hlim : ∀ x, Tendsto (fun n => mollifyEps (hε n) u x - u x) atTop (𝓝 0) := by
    intro x
    simpa only [sub_self] using
      (tendsto_mollifyEps_of_continuous hε hεlim hu.continuous x).sub
        (tendsto_const_nhds (x := u x))
  have hsmall : ∀ᶠ n in atTop, ε n ≤ 1 :=
    (hεlim.eventually (gt_mem_nhds zero_lt_one)).mono fun _ hn => hn.le
  have hbound : ∀ᶠ n in atTop, ∀ᵐ x ∂volume.restrict s,
      ‖‖mollifyEps (hε n) u x - u x‖‖ ≤ (C : ℝ) := by
    filter_upwards [hsmall] with n hn
    filter_upwards with x
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    have hb := norm_mollifyEps_sub_le_of_holderWith (hε n) zero_lt_one hu.holderWith x
    simp only [NNReal.coe_one, Real.rpow_one] at hb
    exact hb.trans (by simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hn C.coe_nonneg)
  have hnormlim : ∀ᵐ x ∂volume.restrict s,
      Tendsto (fun n => ‖mollifyEps (hε n) u x - u x‖) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards with x
    simpa only [norm_zero] using (hlim x).norm
  simpa only [integral_zero] using tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict s) (fun _ : E => (C : ℝ))
    (F := fun n x => ‖mollifyEps (hε n) u x - u x‖) (f := fun _ => (0 : ℝ))
    (Eventually.of_forall fun n =>
      ((mollifyEps_continuous (hε n) hu.continuous.locallyIntegrable).sub
        hu.continuous).norm.aestronglyMeasurable) hbound (integrable_const _) hnormlim

theorem ae_tendsto_fderiv_mollifyEps_of_lipschitzWith
    {ι : Type*} {l : Filter ι} {ε : ι → ℝ}
    (hε : ∀ n, 0 < ε n) (hεlim : Tendsto ε l (𝓝 0))
    {u : E → ℝ} {C : ℝ≥0} (hu : LipschitzWith C u) :
    ∀ᵐ x ∂volume, Tendsto (fun n => fderiv ℝ (mollifyEps (hε n) u) x)
      l (𝓝 (fderiv ℝ u x)) := by
  let e₁ : E ≃L[ℝ] Fin d → ℝ := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)
  let e : (E →L[ℝ] ℝ) ≃L[ℝ] (Fin d → ℝ) :=
    (e₁.arrowCongr (1 : ℝ ≃L[ℝ] ℝ)).trans (ContinuousLinearEquiv.piRing (Fin d))
  filter_upwards [ae_all_iff.mpr
    (fun i => ae_tendsto_partial_mollifyEps_of_lipschitzWith hε hεlim hu i)] with x hx
  have he : Tendsto (fun n => e (fderiv ℝ (mollifyEps (hε n) u) x))
      l (𝓝 (e (fderiv ℝ u x))) := by
    apply tendsto_pi_nhds.mpr
    intro i
    exact hx i
  simpa only [Function.comp_def, ContinuousLinearEquiv.symm_apply_apply] using
    (e.symm.continuous.tendsto (e (fderiv ℝ u x))).comp he

theorem tendsto_integral_norm_fderiv_mollifyEps_sub_of_lipschitzWith
    {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n) (hεlim : Tendsto ε atTop (𝓝 0))
    {u : E → ℝ} {C : ℝ≥0} (hu : LipschitzWith C u)
    {s : Set E} [IsFiniteMeasure (volume.restrict s)] :
    Tendsto (fun n => ∫ x in s, ‖fderiv ℝ (mollifyEps (hε n) u) x - fderiv ℝ u x‖)
      atTop (𝓝 0) := by
  have hmeas (n : ℕ) : AEStronglyMeasurable
      (fun x => ‖fderiv ℝ (mollifyEps (hε n) u) x - fderiv ℝ u x‖)
      (volume.restrict s) :=
    ((measurable_fderiv ℝ _).sub (measurable_fderiv ℝ _)).norm.aestronglyMeasurable
  have hbound (n : ℕ) : ∀ᵐ x ∂volume.restrict s,
      ‖‖fderiv ℝ (mollifyEps (hε n) u) x - fderiv ℝ u x‖‖ ≤ 2 * (C : ℝ) := by
    filter_upwards with x
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact (norm_sub_le _ _).trans (by
      have h₁ := norm_fderiv_le_of_lipschitz ℝ (lipschitzWith_mollifyEps (hε n) hu)
        (x₀ := x)
      have h₂ := norm_fderiv_le_of_lipschitz ℝ hu (x₀ := x)
      linarith only [h₁, h₂])
  have hlim : ∀ᵐ x ∂volume.restrict s, Tendsto
      (fun n => ‖fderiv ℝ (mollifyEps (hε n) u) x - fderiv ℝ u x‖) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [ae_mono Measure.restrict_le_self
      (ae_tendsto_fderiv_mollifyEps_of_lipschitzWith hε hεlim hu)] with x hx
    simpa only [sub_self, norm_zero] using (hx.sub (tendsto_const_nhds (x := fderiv ℝ u x))).norm
  simpa only [integral_zero] using tendsto_integral_of_dominated_convergence
    (μ := volume.restrict s) (fun _ : E => 2 * (C : ℝ))
    hmeas (integrable_const _) hbound hlim

end DifferentialGeometry.Analysis.Sobolev
