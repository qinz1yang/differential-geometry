import DifferentialGeometry.Analysis.ODE.Flow.Planar.CompactFlowGerm
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Log

noncomputable section
open Set Metric Filter Topology
open scoped ContDiff Manifold

namespace Poincare.Analysis

theorem exists_compact_isotopy_realizing_complex_mul
    (a : ℂ) (ha : a ≠ 0) (r : ℝ) (hr : 0 < r) :
    ∃ D : ℝ → Diffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ ∞,
      ContDiff ℝ ∞ (fun q : ℝ × ℂ ↦ D q.1 q.2) ∧
      ContDiff ℝ ∞ (fun q : ℝ × ℂ ↦ (D q.1).symm q.2) ∧
      D 0 = Diffeomorph.refl 𝓘(ℝ, ℂ) ℂ ∞ ∧
      (D 1 : ℂ → ℂ) =ᶠ[𝓝 0] (fun z ↦ a * z) ∧
      ∀ p z, z ∉ closedBall 0 (2 * r) → D p z = z ∧ (D p).symm z = z := by
  let v : ℂ → ℂ := fun z ↦ Complex.log a * z
  let Γ : ℂ × ℝ → ℂ := fun q ↦ Complex.exp ((q.2 : ℂ) * Complex.log a) * q.1
  have hv : ContDiff ℝ ∞ v := contDiff_const.mul contDiff_id
  have hΓ : Continuous Γ := by fun_prop
  have hzero (z : ℂ) : Γ (z, 0) = z := by simp [Γ]
  have hfixed (t : ℝ) (_ : t ∈ Icc (0 : ℝ) 1) : Γ (0, t) = 0 := by simp [Γ]
  have hderiv (z : ℂ) (t : ℝ) (_ : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun s ↦ Γ (z, s)) (v (Γ (z, t))) t := by
    have hd := ((((hasDerivAt_id (t : ℂ)).mul_const (Complex.log a)).cexp).mul_const z).comp_ofReal
    convert hd using 1 <;> first | rfl | dsimp [Γ, v]; ring
  obtain ⟨D, hD, hDi, hD0, hgerm, hfix⟩ :=
    exists_compact_isotopy_realizing_flow_germ hv Γ hΓ hzero hfixed hderiv r hr
  refine ⟨D, hD, hDi, hD0, ?_, hfix⟩
  simpa only [Γ, Complex.ofReal_one, one_mul, Complex.exp_log ha] using hgerm

end Poincare.Analysis
