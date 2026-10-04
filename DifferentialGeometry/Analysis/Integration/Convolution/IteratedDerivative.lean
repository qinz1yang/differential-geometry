import DifferentialGeometry.Analysis.Integration.Convolution.Approximation
import Mathlib.Topology.UniformSpace.HeineCantor

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter ContinuousLinearMap
open scoped ContDiff Convolution Topology

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
  {μ : Measure E}

namespace MeasureTheory

omit [NormedSpace ℝ E] [BorelSpace E] in
private theorem linearIsometryEquiv_convolution
    (L : F ≃ₗᵢ[ℝ] G) (κ : E → ℝ) (f : E → F) (x : E) :
    L ((κ ⋆[lsmul ℝ ℝ, μ] f) x) =
      (κ ⋆[lsmul ℝ ℝ, μ] (fun y => L (f y))) x := by
  simp only [convolution_def, lsmul_apply]
  change L.toLinearIsometry (∫ t, κ t • f (x - t) ∂μ) = _
  rw [← L.toLinearIsometry.integral_comp_comm]
  simp only [map_smul]
  rfl

section

variable [SFinite μ] [μ.IsAddLeftInvariant]

omit [CompleteSpace F] in
private theorem fderiv_smul_convolution
    {κ : E → ℝ} {f : E → F} (hκ : LocallyIntegrable κ μ)
    (hc : HasCompactSupport f) (hf : ContDiff ℝ 1 f) (x : E) :
    fderiv ℝ (κ ⋆[lsmul ℝ ℝ, μ] f) x =
      (κ ⋆[lsmul ℝ ℝ, μ] fderiv ℝ f) x := by
  rw [(hc.hasFDerivAt_convolution_right (lsmul ℝ ℝ) hκ hf x).fderiv]
  congr 1

theorem iteratedFDeriv_smul_convolution
    {κ : E → ℝ} {f : E → F} (hκ : LocallyIntegrable κ μ)
    (hc : HasCompactSupport f) (k : ℕ) (hf : ContDiff ℝ (k : ℕ∞ω) f) (x : E) :
    iteratedFDeriv ℝ k (κ ⋆[lsmul ℝ ℝ, μ] f) x =
      (κ ⋆[lsmul ℝ ℝ, μ] iteratedFDeriv ℝ k f) x := by
  induction k generalizing x with
  | zero =>
    simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_def] using
      linearIsometryEquiv_convolution (μ := μ)
        (continuousMultilinearCurryFin0 ℝ E F).symm κ f x
  | succ k ih =>
    have hlow : ContDiff ℝ (k : ℕ∞ω) f := hf.of_le (by exact_mod_cast Nat.le_succ k)
    have heq : iteratedFDeriv ℝ k (κ ⋆[lsmul ℝ ℝ, μ] f) =
        κ ⋆[lsmul ℝ ℝ, μ] iteratedFDeriv ℝ k f := funext (fun y => ih hlow y)
    have hjet : ContDiff ℝ 1 (iteratedFDeriv ℝ k f) :=
      hf.iteratedFDeriv_right (by exact_mod_cast (show 1 + k ≤ k + 1 by omega))
    simp only [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply]
    rw [heq, fderiv_smul_convolution hκ (hc.iteratedFDeriv k) hjet]
    exact linearIsometryEquiv_convolution
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => E) F).symm
      κ (fderiv ℝ (iteratedFDeriv ℝ k f)) x

end

end MeasureTheory

namespace ContDiffBump

variable [FiniteDimensional ℝ E] [μ.IsAddHaarMeasure]

theorem tendstoUniformly_iteratedFDeriv_normed_convolution
    {ι : Type*} {l : Filter ι} {φ : ι → ContDiffBump (0 : E)}
    (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0))
    {f : E → F} (hc : HasCompactSupport f) (k : ℕ)
    (hf : ContDiff ℝ (k : ℕ∞ω) f) :
    ∀ j, j ≤ k → TendstoUniformly
      (fun i => iteratedFDeriv ℝ j ((φ i).normed μ ⋆[lsmul ℝ ℝ, μ] f))
      (iteratedFDeriv ℝ j f) l := by
  intro j hj
  have hjf : ContDiff ℝ (j : ℕ∞ω) f := hf.of_le (by exact_mod_cast hj)
  have hcont : Continuous (iteratedFDeriv ℝ j f) := hjf.continuous_iteratedFDeriv'
  have huc := (hc.iteratedFDeriv j).uniformContinuous_of_continuous hcont
  have h := _root_.ContDiffBump.tendstoUniformly_normed_convolution (μ := μ) hφ huc
  have heq : (fun i => iteratedFDeriv ℝ j ((φ i).normed μ ⋆[lsmul ℝ ℝ, μ] f)) =
      (fun i => (φ i).normed μ ⋆[lsmul ℝ ℝ, μ] iteratedFDeriv ℝ j f) := by
    funext i x
    exact iteratedFDeriv_smul_convolution (φ i).integrable_normed.locallyIntegrable hc j hjf x
  rw [heq]
  exact h

end ContDiffBump
