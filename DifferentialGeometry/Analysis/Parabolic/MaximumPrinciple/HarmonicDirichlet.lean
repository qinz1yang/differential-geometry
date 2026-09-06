import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.InitialData

set_option autoImplicit false

namespace DifferentialGeometry.Analysis.Parabolic

noncomputable section

open Bundle Set
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

theorem exists_local_scalar_dirichlet_solution_of_harmonic_data
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T s t c : Real}
    (X : Real → (x : M) → TangentSpace I x)
    (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ T)
    (Kset : Set M) (f₀ : M → Real)
    (hf₀ : ContMDiff I 𝓘(Real, Real) ∞ f₀)
    (hf₀_boundary : ∀ z ∈ frontier Kset, f₀ z = 0)
    (hf₀_pos : ∀ z ∈ interior Kset, 0 < f₀ z)
    (hf₀_harmonic : ∀ q ∈ Set.Ioc s t, ∀ z ∈ interior Kset,
      heatOperatorWithDrift (I := I) G q (X q) f₀ z = 0) :
    ∃ f : Real → M → Real,
      IsLocalScalarDirichletSolution (I := I) G T X s t c Kset f₀ f := by
  have hTpos : 0 < T := by
    linarith
  let v : Real → M → Real := fun _ z => Real.exp (c * s) * f₀ z
  let f : Real → M → Real := fun q z => Real.exp (-c * q) * v q z
  have hv_space : ∀ q : Real, ∀ z : M,
      MDifferentiableAt I 𝓘(Real, Real) (v q) z := by
    intro q z
    exact (contMDiff_const.mul hf₀).mdifferentiable (by simp) z
  have hv_grad : ∀ q : Real, ∀ z : M,
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric q) (v q) y) z := by
    intro q z
    exact gradientFun_mdiffAt (I := I) (G.metric q)
      (contMDiff_const.mul hf₀) z
  have hf_cont : ContinuousOn (fun p : Real × M => f p.1 p.2)
      (Set.Icc s t ×ˢ Kset) := by
    have hexp : Continuous (fun p : Real × M => Real.exp (-c * p.1)) := by
      fun_prop
    have hconst : Continuous (fun _ : Real × M => Real.exp (c * s)) :=
      continuous_const
    have hf₀' : Continuous (fun p : Real × M => f₀ p.2) :=
      hf₀.continuous.comp continuous_snd
    change ContinuousOn
      ((fun p : Real × M => Real.exp (-c * p.1)) *
        (fun p : Real × M => Real.exp (c * s) * f₀ p.2))
      (Set.Icc s t ×ˢ Kset)
    exact (hexp.mul (hconst.mul hf₀')).continuousOn
  have hf_initial : ∀ z ∈ Kset, f s z = f₀ z := by
    intro z hz
    dsimp [f, v]
    calc
      Real.exp (-c * s) * (Real.exp (c * s) * f₀ z) =
          (Real.exp (-c * s) * Real.exp (c * s)) * f₀ z := by ring
      _ = f₀ z := by
        rw [← Real.exp_add]
        ring_nf
        simp
  have hf_boundary : ∀ q ∈ Set.Icc s t, ∀ z ∈ frontier Kset, f q z = 0 := by
    intro q hq z hz
    simp [f, v, hf₀_boundary z hz]
  have hf_pos : ∀ q ∈ Set.Ioc s t, ∀ z ∈ interior Kset, 0 < f q z := by
    intro q hq z hz
    exact mul_pos (Real.exp_pos _) (mul_pos (Real.exp_pos _) (hf₀_pos z hz))
  have hf_time : ∀ q ∈ Set.Ioc s t, ∀ z ∈ interior Kset,
      DifferentiableAt Real (fun r => f r z) q := by
    intro q hq z hz
    dsimp [f, v]
    fun_prop
  have hf_space : ∀ q ∈ Set.Ioc s t, ∀ z ∈ interior Kset,
      MDifferentiableAt I 𝓘(Real, Real) (f q) z := by
    intro q hq z hz
    exact (contMDiff_const.mul (contMDiff_const.mul hf₀)).mdifferentiable
      (by simp) z
  have hf_grad : ∀ q ∈ Set.Ioc s t, ∀ z ∈ interior Kset,
      MDiffAt (T% fun w : M =>
        gradientFun (I := I) (G.metric q) (f q) w) z := by
    intro q hq z hz
    exact gradientFun_mdiffAt (I := I) (G.metric q)
      (contMDiff_const.mul (contMDiff_const.mul hf₀)) z
  have hf_equation : ∀ q ∈ Set.Ioc s t, ∀ z ∈ interior Kset,
      parabolicOperatorWithDrift (I := I) G T X f q z = -c * f q z := by
    intro q hq z hz
    have hqmem : q ∈ Set.Icc (0 : Real) T := by
      exact ⟨hs.trans (le_of_lt hq.1), hq.2.trans ht⟩
    have huniq : UniqueDiffWithinAt Real (Set.Icc 0 T) q :=
      (uniqueDiffOn_Icc hTpos).uniqueDiffWithinAt hqmem
    have hv_time : DifferentiableWithinAt Real
        (fun r : Real => v r z) (Set.Icc 0 T) q :=
      differentiableWithinAt_const _
    have hscale : DifferentiableWithinAt Real
        (fun r : Real => Real.exp (-c * r)) (Set.Icc 0 T) q := by
      fun_prop
    have hres := parabolic_exp_rescale_identity (I := I) G T c X v q
      huniq (hv_space q) z (hv_grad q z) (hv_time) hscale
    have hscale_op := heatOperatorWithDrift_const_smul (I := I) G q (X q)
      (Real.exp (c * s)) (f := f₀)
      (fun y => hf₀.mdifferentiable (by simp) y)
      (gradientFun_mdiffAt (I := I) (G.metric q) hf₀ z)
    have hv_op : parabolicOperatorWithDrift (I := I) G T X v q z = 0 := by
      unfold parabolicOperatorWithDrift
      rw [show derivWithin (fun _r : Real => v _r z) (Set.Icc 0 T) q = 0 by
        exact (hasDerivWithinAt_const (x := q) (s := Set.Icc 0 T)
          (c := v q z)).derivWithin huniq]
      simp only [zero_sub]
      rw [show heatOperatorWithDrift (I := I) G q (X q) (v q) z =
          Real.exp (c * s) * heatOperatorWithDrift (I := I) G q (X q) f₀ z by
        rw [show v q = Real.exp (c * s) • f₀ by
          funext y
          simp [v, smul_eq_mul]]
        exact hscale_op]
      rw [hf₀_harmonic q hq z hz]
      simp
    rw [hres, hv_op]
    dsimp [f, v]
    ring
  refine ⟨f, ?_⟩
  exact ⟨hf_cont, hf_initial, hf_boundary, hf_pos, hf_time, hf_space,
    hf_grad, hf_equation⟩

end

end DifferentialGeometry.Analysis.Parabolic
