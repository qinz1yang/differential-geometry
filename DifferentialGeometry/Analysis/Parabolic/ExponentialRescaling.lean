import DifferentialGeometry.Analysis.Parabolic.Energy.Caccioppoli
import DifferentialGeometry.Geometry.Operator.LaplacianBridge

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Analysis.Parabolic

open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Parabolic.Energy
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [I.Boundaryless] [T2Space M]

def exponentialTimeRescale (rate center : ℝ) (u : ℝ → M → ℝ) : ℝ → M → ℝ :=
  fun t x => Real.exp (rate * t - center) * u t x

omit [Module.Finite ℝ E] [IsManifold I ∞ M] [I.Boundaryless] [T2Space M] in
theorem contMDiff_exponentialTimeRescale
    (rate center : ℝ) (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2)) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => exponentialTimeRescale rate center u p.1 p.2) := by
  exact (Real.contDiff_exp.contMDiff.comp
    ((contMDiff_const.mul contMDiff_fst).sub contMDiff_const)).mul hu

omit [Module.Finite ℝ E] [TopologicalSpace M] [IsManifold I ∞ M]
    [I.Boundaryless] [T2Space M] in
theorem exponentialTimeRescale_pos
    (rate center : ℝ) (u : ℝ → M → ℝ)
    (hpos : ∀ t x, 0 < u t x) (t : ℝ) (x : M) :
    0 < exponentialTimeRescale rate center u t x := by
  exact mul_pos (Real.exp_pos _) (hpos t x)

omit [Module.Finite ℝ E] [IsManifold I ∞ M] [I.Boundaryless] [T2Space M] in
theorem deriv_exponentialTimeRescale
    (rate center : ℝ) (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2)) (t : ℝ) (x : M) :
    deriv (fun s => exponentialTimeRescale rate center u s x) t =
      Real.exp (rate * t - center) *
        (deriv (fun s => u s x) t + rate * u t x) := by
  have htime : ContDiff ℝ ∞ (fun s => u s x) :=
    contMDiff_iff_contDiff.mp (hu.comp (contMDiff_id.prodMk contMDiff_const))
  have hscale : HasDerivAt (fun s : ℝ => Real.exp (rate * s - center))
      (rate * Real.exp (rate * t - center)) t := by
    simpa only [id_eq, mul_one, mul_comm] using
      (((hasDerivAt_id t).const_mul rate).sub_const center).exp
  have hproduct := hscale.mul
    ((htime.differentiable (by norm_num) t).hasDerivAt)
  simpa only [exponentialTimeRescale] using hproduct.deriv.trans (by ring)

theorem laplacian_exponentialTimeRescale
    (g : SmoothRiemannianMetric I M)
    (rate center : ℝ) (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2)) (t : ℝ) (x : M) :
    Δ_g (I := I) g
        (smoothScalarSlice (I := I) g (exponentialTimeRescale rate center u)
          (contMDiff_exponentialTimeRescale rate center u hu) t).toContMDiffMap x =
      Real.exp (rate * t - center) *
        Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).toContMDiffMap x := by
  let ut := smoothScalarSlice (I := I) g u hu t
  let vt := smoothScalarSlice (I := I) g (exponentialTimeRescale rate center u)
    (contMDiff_exponentialTimeRescale rate center u hu) t
  unfold SmoothScalar.toContMDiffMap
  rw [← laplacian_levi_eq (I := I) g vt.smooth x,
    ← laplacian_levi_eq (I := I) g ut.smooth x]
  simpa only [vt, ut, smoothScalarSlice_toFun, exponentialTimeRescale,
    Pi.smul_apply, smul_eq_mul] using
    laplacian_const_smul (I := I) (LeviCivita (I := I) g) g
      (Real.exp (rate * t - center))
      (fun y => ut.smooth.mdifferentiable (by simp) y)
      ((grad_g (I := I) g ut.toContMDiffMap).mdifferentiable x)

theorem exponential_time_rescale_supersolution
    (g : SmoothRiemannianMetric I M)
    (rate center : ℝ) (hrate : 0 ≤ rate)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    {t : ℝ} {x : M}
    (hpde :
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).toContMDiffMap x ≤
        deriv (fun s => u s x) t) :
    Δ_g (I := I) g
        (smoothScalarSlice (I := I) g (exponentialTimeRescale rate center u)
          (contMDiff_exponentialTimeRescale rate center u hu) t).toContMDiffMap x ≤
      deriv (fun s => exponentialTimeRescale rate center u s x) t := by
  rw [laplacian_exponentialTimeRescale (I := I) (M := M) g rate center u hu t x,
    deriv_exponentialTimeRescale (I := I) (M := M) rate center u hu t x]
  have hscale : 0 ≤ Real.exp (rate * t - center) := (Real.exp_pos _).le
  have hreaction : 0 ≤ rate * u t x := mul_nonneg hrate (hpos t x).le
  exact mul_le_mul_of_nonneg_left (hpde.trans (le_add_of_nonneg_right hreaction)) hscale

end DifferentialGeometry.Analysis.Parabolic

end
