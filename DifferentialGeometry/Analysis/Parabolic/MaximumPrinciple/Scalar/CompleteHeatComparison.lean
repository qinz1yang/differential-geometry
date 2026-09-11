import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.Scalar.CompleteScalarComparison

set_option autoImplicit false
noncomputable section

open Set Filter Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.PDE.RicciFlow
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Analysis

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless]

theorem nonpositive_of_heat_subsolution_and_cutoffs
    (G : MetricConnectionFamily (I := I) (M := M) ℝ)
    (T : ℝ) (hT : 0 < T)
    (q : ℝ → M → ℝ) (C : ℝ)
    (hcont : ContinuousOn (fun p : ℝ × M => q p.1 p.2)
      (Icc 0 T ×ˢ univ))
    (htime : ∀ t ∈ Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt ℝ (fun s => q s x) (Icc 0 T) t)
    (hspace : ∀ t ∈ Icc 0 T, 0 < t →
      ContMDiff I 𝓘(ℝ, ℝ) ∞ (q t))
    (hinit : ∀ x : M, q 0 x ≤ 0)
    (hbound : ∀ t ∈ Icc 0 T, ∀ x : M, q t x ≤ C)
    (hheat : ∀ t ∈ Icc 0 T, 0 < t → ∀ x : M,
      parabolicOperatorWithDrift G T (fun _ _ => 0) q t x ≤ 0)
    (hcut : ∀ O : M, Nonempty (ShiBarrierCutoffData G T O)) :
    ∀ t ∈ Icc 0 T, ∀ x : M, q t x ≤ 0 := by
  let φ : ℝ → ℝ := fun r => Real.exp r - 1
  let u : ℝ → M → ℝ := fun t x => φ (q t x)
  let N : ℝ → M → ℝ := fun t x =>
    (G.metric t).inner x
      (gradientFun (I := I) (G.metric t) (q t) x)
      (gradientFun (I := I) (G.metric t) (q t) x)
  let w : ℝ → M → ℝ := fun t x => Real.exp (q t x) / 2 * N t x
  let B : ℝ := Real.exp C
  have hB : 0 ≤ B := (Real.exp_pos C).le
  have hN : ∀ t x, 0 ≤ N t x := by
    intro t x
    exact metric_inner_self_nonneg (G.metric t) x _
  have hφdiff : Differentiable ℝ φ := by
    simpa only [φ] using Real.differentiable_exp.sub_const 1
  have hφderiv : deriv φ = Real.exp := by
    funext r
    exact ((Real.hasDerivAt_exp r).sub_const 1).deriv
  have hucont :
      ContinuousOn (fun p : ℝ × M => u p.1 p.2)
        (Icc 0 T ×ˢ univ) := by
    have hh := (Real.continuous_exp.comp_continuousOn hcont).sub (continuousOn_const (c := (1 : ℝ)))
    convert hh using 1
    rfl
  have hutime : ∀ t ∈ Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt ℝ (fun s => u s x) (Icc 0 T) t := by
    intro t ht hp x
    simpa only [u, φ] using (htime t ht hp x).exp.sub_const 1
  have huspace : ∀ t ∈ Icc 0 T, 0 < t →
      ContMDiff I 𝓘(ℝ, ℝ) ∞ (u t) := by
    intro t ht hp
    have hh := (Real.contDiff_exp.contMDiff.comp (hspace t ht hp)).sub (contMDiff_const (c := (1 : ℝ)))
    convert hh using 1 <;> rfl
  have huinit : ∀ x : M, u 0 x ≤ 0 := by
    intro x
    change Real.exp (q 0 x) - 1 ≤ 0
    exact sub_nonpos.mpr (Real.exp_le_one_iff.mpr (hinit x))
  have hubound : ∀ t ∈ Icc 0 T, ∀ x : M, u t x ≤ B := by
    intro t ht x
    have he := Real.exp_le_exp.mpr (hbound t ht x)
    change Real.exp (q t x) - 1 ≤ Real.exp C
    linarith only [he]
  have hw : ∀ t ∈ Icc 0 T, ∀ x : M, 0 ≤ w t x := by
    intro t _ x
    exact mul_nonneg
      (div_nonneg (Real.exp_pos (q t x)).le (by norm_num)) (hN t x)
  have hugrad : ∀ t ∈ Icc 0 T, 0 < t → ∀ x : M, 0 < u t x →
      (G.metric t).inner x
        (gradientFun (I := I) (G.metric t) (u t) x)
        (gradientFun (I := I) (G.metric t) (u t) x) ≤
          4 * B * w t x := by
    intro t ht hp x _
    have hg :
        gradientFun (I := I) (G.metric t) (u t) x =
          Real.exp (q t x) •
            gradientFun (I := I) (G.metric t) (q t) x := by
      simpa only [u, hφderiv] using
        (gradientFun_comp (I := I) (G.metric t)
          (φ := φ) (f := q t)
          (hφdiff (q t x))
          ((hspace t ht hp).mdifferentiableAt (by simp)))
    have he : Real.exp (q t x) ≤ B :=
      Real.exp_le_exp.mpr (hbound t ht x)
    have heN : 0 ≤ Real.exp (q t x) * N t x :=
      mul_nonneg (Real.exp_pos (q t x)).le (hN t x)
    calc
      (G.metric t).inner x
          (gradientFun (I := I) (G.metric t) (u t) x)
          (gradientFun (I := I) (G.metric t) (u t) x) =
          Real.exp (q t x) * (Real.exp (q t x) * N t x) := by
        rw [hg]
        simp only [map_smul, smul_apply, smul_eq_mul]
        rfl
      _ ≤ B * (Real.exp (q t x) * N t x) :=
        mul_le_mul_of_nonneg_right he heN
      _ = 2 * B * w t x := by
        dsimp only [w]
        ring
      _ ≤ 4 * B * w t x := by
        nlinarith only [mul_nonneg hB (hw t ht x)]
  have huheat : ∀ t ∈ Icc 0 T, 0 < t → ∀ x : M, 0 < u t x →
      parabolicOperatorWithDrift G T (fun _ _ => 0) u t x ≤
        -2 * w t x + 0 * u t x := by
    intro t ht hp x _
    have hφ' : DifferentiableAt ℝ (deriv φ) (q t x) := by
      rw [hφderiv]
      exact Real.differentiable_exp _
    have hc :
        parabolicOperatorWithDrift G T (fun _ _ => 0) u t x =
          Real.exp (q t x) *
            parabolicOperatorWithDrift G T (fun _ _ => 0) q t x -
              Real.exp (q t x) * N t x := by
      simpa only [u, hφderiv, Real.deriv_exp, gradientAt, N] using
        (parabolic_comp (I := I) G T (fun _ _ => 0)
          (φ := φ) q t x hφdiff hφ'
          (htime t ht hp x)
          (fun y => (hspace t ht hp).mdifferentiableAt (by simp))
          (gradientFun_mdiffAt (G.metric t) (hspace t ht hp) x))
    have hpq :
        Real.exp (q t x) *
          parabolicOperatorWithDrift G T (fun _ _ => 0) q t x ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos
        (Real.exp_pos (q t x)).le (hheat t ht hp x)
    rw [hc]
    simp only [zero_mul, add_zero]
    dsimp only [w]
    nlinarith only [hpq]
  have hu :=
    nonpositive_of_dissipation_and_cutoffs G T hT u w 0 B
      (by norm_num) hB hucont hutime huspace huinit hubound hw
      hugrad huheat hcut
  intro t ht x
  have h := hu t ht x
  change Real.exp (q t x) - 1 ≤ 0 at h
  exact Real.exp_le_one_iff.mp (by linarith only [h])

end DifferentialGeometry.Analysis
