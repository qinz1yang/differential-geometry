import DifferentialGeometry.Analysis.Calculus.IteratedDerivative.Families
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add



noncomputable section

open Function
open scoped ContDiff

namespace DifferentialGeometry.Analysis

variable {T K F : Type*} [TopologicalSpace T] [TopologicalSpace K]
  [NormedAddCommGroup F] [NormedSpace ℝ F]



theorem deriv_affine_curve {f g : ℝ → F} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (a t : ℝ) :
    deriv (fun x => f x + a • (g x - f x)) t =
      deriv f t + a • (deriv g t - deriv f t) := by
  exact ((hf t).hasDerivAt.add (((hg t).hasDerivAt.sub (hf t).hasDerivAt).const_smul a)).deriv



theorem continuous_deriv_affine_family {f g : K × ℝ → F} {a : T → ℝ}
    (hf : ∀ k, Differentiable ℝ (fun t => f (k, t)))
    (hg : ∀ k, Differentiable ℝ (fun t => g (k, t))) (ha : Continuous a)
    (hdf : Continuous (fun p : K × ℝ => deriv (fun t => f (p.1, t)) p.2))
    (hdg : Continuous (fun p : K × ℝ => deriv (fun t => g (p.1, t)) p.2)) :
    Continuous (fun p : (T × K) × ℝ =>
      deriv (fun t => f (p.1.2, t) + a p.1.1 • (g (p.1.2, t) - f (p.1.2, t))) p.2) := by
  simp_rw [deriv_affine_curve (hf _) (hg _)]
  have hproj : Continuous (fun p : (T × K) × ℝ => (p.1.2, p.2)) :=
    (continuous_snd.comp continuous_fst).prodMk continuous_snd
  exact (hdf.comp hproj).add ((ha.comp (continuous_fst.comp continuous_fst)).smul
    ((hdg.comp hproj).sub (hdf.comp hproj)))

end DifferentialGeometry.Analysis
