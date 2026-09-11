import DifferentialGeometry.Analysis.Parabolic.Energy.ParabolicLocalAlgebra
import Mathlib.Geometry.Manifold.Algebra.LieGroup

set_option autoImplicit false
noncomputable section

open Set Filter Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis.Parabolic
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Analysis

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem parabolic_div_at_zero_unit_denominator
    (G : MetricConnectionFamily (I := I) (M := M) ℝ)
    (T t : ℝ) (b d : ℝ → M → ℝ) (x : M)
    (hbtime :
      DifferentiableWithinAt ℝ (fun s => b s x) (Icc 0 T) t)
    (hdtime :
      DifferentiableWithinAt ℝ (fun s => d s x) (Icc 0 T) t)
    (hbspace : ContMDiff I 𝓘(ℝ, ℝ) ∞ (b t))
    (hdspace : ContMDiff I 𝓘(ℝ, ℝ) ∞ (d t))
    (hbzero : b t x = 0)
    (hdone : d t x = 1)
    (hdgrad :
      gradientFun (I := I) (G.metric t) (d t) x = 0) :
    parabolicOperatorWithDrift G T (fun _ _ => 0)
        (fun s y => b s y / d s y) t x =
      parabolicOperatorWithDrift G T (fun _ _ => 0) b t x := by
  have hdne : d t x ≠ 0 := by
    rw [hdone]
    norm_num
  have hnear : ∀ᶠ y in 𝓝 x, d t y ≠ 0 :=
    hdspace.continuous.continuousAt.eventually_ne hdne
  have hbin :
      ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (b t) y :=
    Eventually.of_forall fun y => hbspace.mdifferentiableAt (by simp)
  have hdin :
      ∀ᶠ y in 𝓝 x,
        MDifferentiableAt I 𝓘(ℝ, ℝ) (fun z => (d t z)⁻¹) y :=
    hnear.mono fun y hy =>
      (hdspace.mdifferentiableAt (by simp)).inv hy
  have hditime :
      DifferentiableWithinAt ℝ (fun s => (d s x)⁻¹) (Icc 0 T) t :=
    hdtime.inv hdne
  have hdiAt :
      ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun y => (d t y)⁻¹) x :=
    hdspace.contMDiffAt.inv₀ hdne
  have hdigradReg :
      MDifferentiableAt I (I.prod 𝓘(ℝ, E))
        (T% fun y =>
          gradientFun (I := I) (G.metric t)
            (fun z => (d t z)⁻¹) y) x :=
    (gradientFun_contMDiffAt (G.metric t) hdiAt).mdifferentiableAt
      (by simp)
  have hdigrad :
      gradientFun (I := I) (G.metric t)
        (fun y => (d t y)⁻¹) x = 0 := by
    have h :=
      gradientFun_comp (I := I) (G.metric t)
        (φ := fun r : ℝ => r⁻¹) (f := d t)
        (hasDerivAt_inv hdne).differentiableAt
        (hdspace.mdifferentiableAt (by simp))
    simpa only [hdgrad, smul_zero] using h
  have hm :=
    parabolic_mul_local G T (fun _ _ => 0)
      b (fun s y => (d s y)⁻¹) t x
      hbtime hditime hbin hdin
      (gradientFun_mdiffAt (G.metric t) hbspace x)
      hdigradReg
  simpa only [div_eq_mul_inv, hbzero, hdone, inv_one,
    zero_mul, one_mul, gradientAt, hdigrad, map_zero,
    mul_zero, sub_zero, zero_add] using hm

end DifferentialGeometry.Analysis
