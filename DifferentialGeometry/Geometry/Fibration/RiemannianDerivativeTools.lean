import DifferentialGeometry.Geometry.Fibration.ManifoldBlockDerivativeApplications

/-!
# Riemannian derivative bounds from local Lipschitz bounds (tools for CGP02's block budgets)

In T0's convention (a smooth metric `g` whose Riemannian distance is the distance of `M`, no bundle
instances), with `ν = √(g_x(v, v))`:

* `abs_mvfderiv_le_of_lipschitzOn_riem`: a real function `L`-Lipschitz on an open set `U ∋ x` and
  differentiable at `x` has `|df(v)| ≤ L ν` (the tree's unit-vector version
  `abs_mvfderiv_le_of_lipschitzOn` plus the scaling `abs_mvfderiv_le_mul_sqrt_of_unit`);
* `norm_mvfderiv_le_of_lipschitzOn_riem`: the same for maps to an inner product space
  (`‖df(v)‖ ≤ L ν`, testing against the unit vector `df(v)/‖df(v)‖`);
* `mvfderiv_comp_hasDerivAt`, `mvfderiv_comp_hasFDerivAt`, `mvfderiv_clm_comp`: the chain rule for
  a real profile, a vector profile and a continuous linear map after a manifold map.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function Bundle
open scoped Topology Manifold ContDiff
open DifferentialGeometry.Geometry.Riemannian

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

section Chain

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Chain rule: a vector profile `φ` with derivative `φ'` at `f(x)` after a manifold map `f`. -/
theorem mvfderiv_comp_hasFDerivAt {f : M → F} {x : M} (hf : MDifferentiableAt I 𝓘(ℝ, F) f x)
    {φ : F → G} {φ' : F →L[ℝ] G} (hφ : HasFDerivAt φ φ' (f x)) (v : TangentSpace I x) :
    mvfderiv I (fun y => φ (f y)) x v = φ' (mvfderiv I f x v) := by
  have h := hφ.hasMFDerivAt.comp x hf.hasMFDerivAt
  rw [mvfderiv_apply_LC, mvfderiv_apply_LC]
  change mfderiv I 𝓘(ℝ, G) (φ ∘ f) x v = _
  rw [h.mfderiv]
  rfl

/-- Chain rule: a continuous linear map after a manifold map. -/
theorem mvfderiv_clm_comp {f : M → F} {x : M} (hf : MDifferentiableAt I 𝓘(ℝ, F) f x)
    (A : F →L[ℝ] G) (v : TangentSpace I x) :
    mvfderiv I (fun y => A (f y)) x v = A (mvfderiv I f x v) :=
  mvfderiv_comp_hasFDerivAt hf A.hasFDerivAt v

/-- Chain rule: a real profile `φ` with derivative `φ'` at `f(x)` after a real function `f`. -/
theorem mvfderiv_comp_hasDerivAt {f : M → ℝ} {x : M} (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x)
    {φ : ℝ → ℝ} {φ' : ℝ} (hφ : HasDerivAt φ φ' (f x)) (v : TangentSpace I x) :
    mvfderiv I (fun y => φ (f y)) x v = φ' * mvfderiv I f x v := by
  rw [mvfderiv_comp_hasFDerivAt hf hφ.hasFDerivAt v]
  simp [mul_comm]

end Chain

section Lipschitz

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [CompleteSpace M]
  [SigmaCompactSpace M]

/-- **Local Lipschitz ⇒ Riemannian derivative bound** (real functions, T0 convention). -/
theorem abs_mvfderiv_le_of_lipschitzOn_riem (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ a b : M, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)) {f : M → ℝ}
    {U : Set M} (hU : IsOpen U) {x : M} (hx : x ∈ U) (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x)
    {L : ℝ} (hlip : ∀ y ∈ U, ∀ z ∈ U, |f y - f z| ≤ L * dist y z) (v : TangentSpace I x) :
    |mvfderiv I f x v| ≤ L * Real.sqrt (g.inner x v v) := by
  let hRB : RiemannianBundle (fun y : M => TangentSpace I y) := ⟨g.toRiemannianMetric⟩
  have hRM : IsRiemannianManifold I M := ⟨fun a b => by
    change edist a b = riemannianEDistOf g a b
    rw [edist_dist, hmetric]⟩
  have hcont : IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  have hEnorm : IsMetricNorm (I := I) g := isMetricNorm_of_riemannianBundle g
  have hunit : ∀ w : TangentSpace I x, g.inner x w w = 1 → |mvfderiv (I := I) f x w| ≤ L :=
    fun w hw => DifferentialGeometry.Geometry.Comparison.abs_mvfderiv_le_of_lipschitzOn g hEnorm
      hU hx hf hlip w hw
  exact abs_mvfderiv_le_mul_sqrt_of_unit g hEnorm hunit v

/-- **Local Lipschitz ⇒ Riemannian derivative bound** for maps to an inner product space. -/
theorem norm_mvfderiv_le_of_lipschitzOn_riem {W : Type*} [NormedAddCommGroup W]
    [InnerProductSpace ℝ W] (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ a b : M, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)) {f : M → W}
    {U : Set M} (hU : IsOpen U) {x : M} (hx : x ∈ U) (hf : MDifferentiableAt I 𝓘(ℝ, W) f x)
    {L : ℝ} (hL : 0 ≤ L) (hlip : ∀ y ∈ U, ∀ z ∈ U, ‖f y - f z‖ ≤ L * dist y z)
    (v : TangentSpace I x) :
    ‖mvfderiv I f x v‖ ≤ L * Real.sqrt (g.inner x v v) := by
  set w : W := mvfderiv I f x v with hw
  rcases eq_or_ne w 0 with h0 | h0
  · rw [h0, norm_zero]
    positivity
  set u : W := ‖w‖⁻¹ • w with hu
  have hnu : ‖u‖ = 1 := by
    rw [hu, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr h0)]
  let A : W →L[ℝ] ℝ := innerSL ℝ u
  have hA : mvfderiv I (fun y => A (f y)) x v = A w := mvfderiv_clm_comp hf A v
  have hAw : A w = ‖w‖ := by
    change inner ℝ u w = ‖w‖
    rw [hu, inner_smul_left, real_inner_self_eq_norm_sq]
    simp only [conj_trivial]
    field_simp [norm_ne_zero_iff.mpr h0]
  have hlipA : ∀ y ∈ U, ∀ z ∈ U, |A (f y) - A (f z)| ≤ L * dist y z := by
    intro y hy z hz
    rw [← map_sub]
    calc |A (f y - f z)| = |inner ℝ u (f y - f z)| := rfl
      _ ≤ ‖u‖ * ‖f y - f z‖ := abs_real_inner_le_norm _ _
      _ = ‖f y - f z‖ := by rw [hnu, one_mul]
      _ ≤ L * dist y z := hlip y hy z hz
  have hfA : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => A (f y)) x :=
    A.hasFDerivAt.differentiableAt.comp_mdifferentiableAt hf
  have h := abs_mvfderiv_le_of_lipschitzOn_riem g hmetric hU hx hfA hlipA v
  rw [hA, hAw, abs_norm] at h
  exact h

end Lipschitz

end DifferentialGeometry.Geometry.Collapse
