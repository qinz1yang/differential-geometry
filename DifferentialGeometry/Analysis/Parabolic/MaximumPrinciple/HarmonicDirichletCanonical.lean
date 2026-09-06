import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.HarmonicDirichlet

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

noncomputable def harmonicDirichletSolution
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
    Real → M → Real :=
  Classical.choose (exists_local_scalar_dirichlet_solution_of_harmonic_data
    (I := I) (c := c) G X hs hst ht Kset f₀ hf₀ hf₀_boundary hf₀_pos
      hf₀_harmonic)

theorem harmonic_dirichlet_solution_spec
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
    IsLocalScalarDirichletSolution (I := I) G T X s t c Kset f₀
      (harmonicDirichletSolution (c := c) G X hs hst ht Kset f₀ hf₀
        hf₀_boundary hf₀_pos hf₀_harmonic) := by
  exact Classical.choose_spec (exists_local_scalar_dirichlet_solution_of_harmonic_data
    (I := I) (c := c) G X hs hst ht Kset f₀ hf₀ hf₀_boundary hf₀_pos
      hf₀_harmonic)

theorem exists_local_scalar_dirichlet_solution_of_eigenfunction_data
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T s t c lambda : Real}
    (X : Real → (x : M) → TangentSpace I x)
    (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ T)
    (Kset : Set M) (f₀ : M → Real)
    (hf₀ : ContMDiff I 𝓘(Real, Real) ∞ f₀)
    (hf₀_boundary : ∀ z ∈ frontier Kset, f₀ z = 0)
    (hf₀_pos : ∀ z ∈ interior Kset, 0 < f₀ z)
    (hf₀_eigen : ∀ q ∈ Set.Ioc s t, ∀ z ∈ interior Kset,
      heatOperatorWithDrift (I := I) G q (X q) f₀ z = lambda * f₀ z) :
    ∃ f : Real → M → Real,
      IsLocalScalarDirichletSolution (I := I) G T X s t c Kset f₀ f := by
  have hTpos : 0 < T := by linarith
  let L : Real := c - lambda
  let v : Real → M → Real := fun _ z => Real.exp (L * s) * f₀ z
  let f : Real → M → Real := fun q z => Real.exp (-L * q) * v q z
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
    have hexp : Continuous (fun p : Real × M => Real.exp (-L * p.1)) := by
      fun_prop
    have hconst : Continuous (fun _ : Real × M => Real.exp (L * s)) :=
      continuous_const
    have hf₀' : Continuous (fun p : Real × M => f₀ p.2) :=
      hf₀.continuous.comp continuous_snd
    change ContinuousOn
      ((fun p : Real × M => Real.exp (-L * p.1)) *
        (fun p : Real × M => Real.exp (L * s) * f₀ p.2))
      (Set.Icc s t ×ˢ Kset)
    exact (hexp.mul (hconst.mul hf₀')).continuousOn
  have hf_initial : ∀ z ∈ Kset, f s z = f₀ z := by
    intro z hz
    dsimp [f, v, L]
    have he : Real.exp (-(c - lambda) * s) *
        Real.exp ((c - lambda) * s) = 1 := by
      rw [← Real.exp_add]
      rw [show -(c - lambda) * s + (c - lambda) * s = 0 by ring,
        Real.exp_zero]
    rw [← mul_assoc, he, one_mul]
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
        (fun r : Real => Real.exp (-L * r)) (Set.Icc 0 T) q := by
      fun_prop
    have hres := parabolic_exp_rescale_identity (I := I) G T L X v q
      huniq (hv_space q) z (hv_grad q z) hv_time hscale
    have hv_op : parabolicOperatorWithDrift (I := I) G T X v q z =
        -lambda * v q z := by
      unfold parabolicOperatorWithDrift
      rw [show derivWithin (fun _r : Real => v _r z) (Set.Icc 0 T) q = 0 by
        exact (hasDerivWithinAt_const (x := q) (s := Set.Icc 0 T)
          (c := v q z)).derivWithin huniq]
      simp only [zero_sub]
      have hheat := heatOperatorWithDrift_const_smul (I := I) G q (X q)
        (Real.exp (L * s)) (f := f₀)
        (fun y => hf₀.mdifferentiable (by simp) y)
        (gradientFun_mdiffAt (I := I) (G.metric q) hf₀ z)
      rw [show v q = Real.exp (L * s) • f₀ by
        funext y
        simp [v, smul_eq_mul], hheat,
        hf₀_eigen q hq z hz]
      dsimp [v]
      ring
    rw [hres, hv_op]
    dsimp [f, v, L]
    ring
  refine ⟨f, ?_⟩
  exact ⟨hf_cont, hf_initial, hf_boundary, hf_pos, hf_time, hf_space,
    hf_grad, hf_equation⟩

theorem eigenfunction_dirichlet_solution_spec
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T s t c lambda : Real}
    (X : Real → (x : M) → TangentSpace I x)
    (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ T)
    (Kset : Set M) (f₀ : M → Real)
    (hf₀ : ContMDiff I 𝓘(Real, Real) ∞ f₀)
    (hf₀_boundary : ∀ z ∈ frontier Kset, f₀ z = 0)
    (hf₀_pos : ∀ z ∈ interior Kset, 0 < f₀ z)
    (hf₀_eigen : ∀ q ∈ Set.Ioc s t, ∀ z ∈ interior Kset,
      heatOperatorWithDrift (I := I) G q (X q) f₀ z = lambda * f₀ z) :
    IsLocalScalarDirichletSolution (I := I) G T X s t c Kset f₀
      (Classical.choose (exists_local_scalar_dirichlet_solution_of_eigenfunction_data
        (I := I) (c := c) G X hs hst ht Kset f₀ hf₀ hf₀_boundary hf₀_pos
          hf₀_eigen)) := by
  exact Classical.choose_spec (exists_local_scalar_dirichlet_solution_of_eigenfunction_data
    (I := I) (c := c) G X hs hst ht Kset f₀ hf₀ hf₀_boundary hf₀_pos
      hf₀_eigen)

theorem exists_local_scalar_dirichlet_solution_of_constant_data
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T s t : Real}
    (X : Real → (x : M) → TangentSpace I x)
    (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ T) :
    ∃ f : Real → M → Real,
      IsLocalScalarDirichletSolution (I := I) G T X s t 0 Set.univ
        (fun _ : M => (1 : Real)) f := by
  have hharmonic : ∀ q ∈ Set.Ioc s t, ∀ z ∈ interior (Set.univ : Set M),
      heatOperatorWithDrift (I := I) G q (X q) (fun _ : M => (1 : Real)) z = 0 := by
    intro q hq z hz
    unfold heatOperatorWithDrift laplacianAt driftTerm gradientAt
    rw [laplacian_const, gradientFun_const]
    simp
  apply exists_local_scalar_dirichlet_solution_of_harmonic_data
    (I := I) (c := 0) G X hs hst ht Set.univ (fun _ : M => (1 : Real))
      contMDiff_const
  · intro z hz
    simp at hz
  · intro z hz
    simp
  · exact hharmonic

theorem exists_local_scalar_dirichlet_solution_of_constant_data_value
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T s t c r : Real}
    (X : Real → (x : M) → TangentSpace I x)
    (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ T) (hr : 0 < r) :
    ∃ f : Real → M → Real,
      IsLocalScalarDirichletSolution (I := I) G T X s t c Set.univ
        (fun _ : M => r) f := by
  have hharmonic : ∀ q ∈ Set.Ioc s t, ∀ z ∈ interior (Set.univ : Set M),
      heatOperatorWithDrift (I := I) G q (X q) (fun _ : M => r) z = 0 := by
    intro q hq z hz
    unfold heatOperatorWithDrift laplacianAt driftTerm gradientAt
    rw [laplacian_const, gradientFun_const]
    simp
  apply exists_local_scalar_dirichlet_solution_of_harmonic_data
    (I := I) (c := c) G X hs hst ht Set.univ (fun _ : M => r)
      contMDiff_const
  · intro z hz
    have hz' : z ∈ (∅ : Set M) := by
      simpa only [frontier_univ] using hz
    exact hz'.elim
  · intro z hz
    exact hr
  · exact hharmonic

end

end DifferentialGeometry.Analysis.Parabolic
