import DifferentialGeometry.Analysis.ODE.Flow.Planar.CompactFlowGerm
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

noncomputable section
open Set Metric Filter Topology
open scoped ContDiff Manifold

namespace Poincare.Analysis

theorem exists_compact_isotopy_realizing_shear
    (s r : ℝ) (hr : 0 < r) :
    ∃ D : ℝ → Diffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ ∞,
      ContDiff ℝ ∞ (fun q : ℝ × ℂ ↦ D q.1 q.2) ∧
      ContDiff ℝ ∞ (fun q : ℝ × ℂ ↦ (D q.1).symm q.2) ∧
      D 0 = Diffeomorph.refl 𝓘(ℝ, ℂ) ℂ ∞ ∧
      (D 1 : ℂ → ℂ) =ᶠ[𝓝 0] (fun z ↦ z + (s * z.im : ℝ)) ∧
      ∀ p z, z ∉ closedBall 0 (2 * r) → D p z = z ∧ (D p).symm z = z := by
  let v : ℂ → ℂ := fun z ↦ (s * z.im : ℝ)
  let Γ : ℂ × ℝ → ℂ := fun q ↦ q.1 + ((q.2 * s) * q.1.im : ℝ)
  have hv : ContDiff ℝ ∞ v :=
    Complex.ofRealCLM.contDiff.comp (contDiff_const.mul Complex.imCLM.contDiff)
  have hΓ : Continuous Γ := by fun_prop
  have hzero (z : ℂ) : Γ (z, 0) = z := by simp [Γ]
  have hfixed (t : ℝ) (_ : t ∈ Icc (0 : ℝ) 1) : Γ (0, t) = 0 := by simp [Γ]
  have hderiv (z : ℂ) (t : ℝ) (_ : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun u ↦ Γ (z, u)) (v (Γ (z, t))) t := by
    have hd := ((((hasDerivAt_id t).mul_const s).mul_const z.im).ofReal_comp).const_add z
    convert hd using 1 <;> first | rfl | simp [v, Γ]
  obtain ⟨D, hD, hDi, hD0, hgerm, hfix⟩ :=
    exists_compact_isotopy_realizing_flow_germ hv Γ hΓ hzero hfixed hderiv r hr
  refine ⟨D, hD, hDi, hD0, ?_, hfix⟩
  simpa only [Γ, one_mul] using hgerm

theorem exists_compact_isotopy_realizing_vertical_scale
    (b : ℝ) (hb : 0 < b) (r : ℝ) (hr : 0 < r) :
    ∃ D : ℝ → Diffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ ∞,
      ContDiff ℝ ∞ (fun q : ℝ × ℂ ↦ D q.1 q.2) ∧
      ContDiff ℝ ∞ (fun q : ℝ × ℂ ↦ (D q.1).symm q.2) ∧
      D 0 = Diffeomorph.refl 𝓘(ℝ, ℂ) ℂ ∞ ∧
      (D 1 : ℂ → ℂ) =ᶠ[𝓝 0] (fun z ↦ (z.re : ℂ) + (b * z.im) • Complex.I) ∧
      ∀ p z, z ∉ closedBall 0 (2 * r) → D p z = z ∧ (D p).symm z = z := by
  let v : ℂ → ℂ := fun z ↦ (Real.log b * z.im) • Complex.I
  let Γ : ℂ × ℝ → ℂ := fun q ↦ (q.1.re : ℂ) +
    (Real.exp (q.2 * Real.log b) * q.1.im) • Complex.I
  have hv : ContDiff ℝ ∞ v :=
    (contDiff_const.mul Complex.imCLM.contDiff).smul contDiff_const
  have hΓ : Continuous Γ := by fun_prop
  have hzero (z : ℂ) : Γ (z, 0) = z := by
    apply Complex.ext <;> simp [Γ]
  have hfixed (t : ℝ) (_ : t ∈ Icc (0 : ℝ) 1) : Γ (0, t) = 0 := by simp [Γ]
  have hderiv (z : ℂ) (t : ℝ) (_ : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun u ↦ Γ (z, u)) (v (Γ (z, t))) t := by
    have hd := (((((hasDerivAt_id t).mul_const (Real.log b)).exp).mul_const z.im).smul_const
      Complex.I).const_add (z.re : ℂ)
    convert hd using 1 <;> first | rfl | simp only [v, Γ, Complex.add_im, Complex.ofReal_im,
      Complex.smul_im, Complex.I_im, smul_eq_mul, mul_one, zero_add, id_eq]; congr 1; ring
  obtain ⟨D, hD, hDi, hD0, hgerm, hfix⟩ :=
    exists_compact_isotopy_realizing_flow_germ hv Γ hΓ hzero hfixed hderiv r hr
  refine ⟨D, hD, hDi, hD0, ?_, hfix⟩
  simpa only [Γ, one_mul, Real.exp_log hb] using hgerm

end Poincare.Analysis
