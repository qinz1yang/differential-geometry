import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.Scalar.Weak

set_option autoImplicit false
noncomputable section
open Set Filter Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis.Parabolic
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Analysis
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable (G : MetricConnectionFamily (I := I) (M := M) ℝ) (T : ℝ)
  (X : ℝ → (x : M) → TangentSpace I x) (u v : ℝ → M → ℝ) (t : ℝ) (x : M)
  (hu_time : DifferentiableWithinAt ℝ (fun s => u s x) (Icc 0 T) t)
  (hv_time : DifferentiableWithinAt ℝ (fun s => v s x) (Icc 0 T) t)
  (hu_space : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (u t) y)
  (hv_space : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (v t) y)
  (hu_grad : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
    (T% fun y => gradientFun (I := I) (G.metric t) (u t) y) x)
  (hv_grad : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
    (T% fun y => gradientFun (I := I) (G.metric t) (v t) y) x)

include hu_time hv_time hu_space hv_space hu_grad hv_grad in
theorem parabolic_mul_local :
    parabolicOperatorWithDrift G T X (fun s y => u s y * v s y) t x =
      u t x * parabolicOperatorWithDrift G T X v t x +
        v t x * parabolicOperatorWithDrift G T X u t x -
          2 * (G.metric t).inner x (gradientAt G t (u t) x) (gradientAt G t (v t) x) := by
  let U := gradientFun (I := I) (G.metric t) (u t)
  let V := gradientFun (I := I) (G.metric t) (v t)
  have he : gradientFun (I := I) (G.metric t) (fun y => u t y * v t y) =ᶠ[𝓝 x]
      u t • V + v t • U := by
    filter_upwards [hu_space, hv_space] with y huy hvy
    exact gradientFun_mul (G.metric t) huy hvy
  have hfirst := hu_space.self_of_nhds.smul_section hv_grad
  have hsecond := hv_space.self_of_nhds.smul_section hu_grad
  have hr := mdifferentiableAt_add_section hfirst hsecond
  have hl : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (T% fun y => gradientFun (I := I) (G.metric t) (fun z => u t z * v t z) y) x := by
    apply hr.congr_of_eventuallyEq
    filter_upwards [he] with y hy
    exact congrArg (fun w => (⟨y, w⟩ : TotalSpace E (TangentSpace I))) hy
  have hcov := (G.connection t).isCovariantDerivativeOnUniv.congr_of_eventuallyEq
    hl hr univ_mem he
  have hlap : laplacianAt G t (fun y => u t y * v t y) x =
      u t x * laplacianAt G t (v t) x + v t x * laplacianAt G t (u t) x +
        2 * (G.metric t).inner x (U x) (V x) := by
    calc
      _ = divergence (I := I) (G.connection t) (u t • V + v t • U) x := by
        unfold laplacianAt laplacian divergence
        rw [hcov]
      _ = _ := by
        rw [divergence_add (G.connection t) inferInstance hfirst hsecond,
          divergence_smul (G.connection t) inferInstance hu_space.self_of_nhds hv_grad,
          divergence_smul (G.connection t) inferInstance hv_space.self_of_nhds hu_grad]
        have hu : mvfderiv (I := I) (u t) x (V x) = (G.metric t).inner x (U x) (V x) := by
          simpa only [mvfderiv, U] using (inner_gradientFun (G.metric t) (u t) x (V x)).symm
        have hv : mvfderiv (I := I) (v t) x (U x) = (G.metric t).inner x (V x) (U x) := by
          simpa only [mvfderiv, V] using (inner_gradientFun (G.metric t) (v t) x (U x)).symm
        rw [hu, hv, (G.metric t).symm x (V x) (U x)]
        change u t x * laplacianAt G t (v t) x + (G.metric t).inner x (U x) (V x) +
          (v t x * laplacianAt G t (u t) x + (G.metric t).inner x (U x) (V x)) = _
        ring
  unfold parabolicOperatorWithDrift heatOperatorWithDrift
  rw [derivWithin_fun_mul hu_time hv_time, hlap,
    driftTerm_mul G t (X t) hu_space.self_of_nhds hv_space.self_of_nhds]
  change _ = _ - 2 * (G.metric t).inner x (U x) (V x)
  ring

include hu_time hv_time hu_space hv_space hu_grad hv_grad in
theorem parabolic_add_local :
    parabolicOperatorWithDrift G T X (fun s y => u s y + v s y) t x =
      parabolicOperatorWithDrift G T X u t x + parabolicOperatorWithDrift G T X v t x := by
  have he : gradientFun (I := I) (G.metric t) (fun y => u t y + v t y) =ᶠ[𝓝 x]
      gradientFun (I := I) (G.metric t) (u t) + gradientFun (I := I) (G.metric t) (v t) := by
    filter_upwards [hu_space, hv_space] with y huy hvy
    exact gradientFun_add (G.metric t) huy hvy
  have hr := mdifferentiableAt_add_section hu_grad hv_grad
  have hl : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (T% fun y => gradientFun (I := I) (G.metric t) (fun z => u t z + v t z) y) x := by
    apply hr.congr_of_eventuallyEq
    filter_upwards [he] with y hy
    exact congrArg (fun w => (⟨y, w⟩ : TotalSpace E (TangentSpace I))) hy
  have hcov := (G.connection t).isCovariantDerivativeOnUniv.congr_of_eventuallyEq
    hl hr univ_mem he
  have hlap : laplacianAt G t (fun y => u t y + v t y) x =
      laplacianAt G t (u t) x + laplacianAt G t (v t) x := by
    calc
      _ = divergence (I := I) (G.connection t)
          (gradientFun (I := I) (G.metric t) (u t) + gradientFun (I := I) (G.metric t) (v t)) x := by
        unfold laplacianAt laplacian divergence
        rw [hcov]
      _ = _ := divergence_add (G.connection t) inferInstance hu_grad hv_grad
  unfold parabolicOperatorWithDrift heatOperatorWithDrift
  rw [derivWithin_fun_add hu_time hv_time, hlap,
    driftTerm_add G t (X t) hu_space.self_of_nhds hv_space.self_of_nhds]
  ring
include hu_time hu_space hu_grad in
theorem parabolic_time_mul_local (a : ℝ → ℝ) (a' : ℝ)
    (ha : HasDerivWithinAt a a' (Icc 0 T) t)
    (huniq : UniqueDiffWithinAt ℝ (Icc 0 T) t) :
    parabolicOperatorWithDrift G T X (fun s y => a s * u s y) t x =
      a t * parabolicOperatorWithDrift G T X u t x + a' * u t x := by
  have has : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (fun _ : M => a t) y :=
    Eventually.of_forall fun _ => mdifferentiableAt_const
  have hag : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (T% fun y => gradientFun (I := I) (G.metric t) (fun _ : M => a t) y) x := by
    simp only [gradientFun_const]
    exact mdifferentiableAt_zeroSection (𝕜 := ℝ) (F := E) (E := TangentSpace I)
  have hh := parabolic_mul_local G T X (fun s _ => a s) u t x
    ha.differentiableWithinAt hu_time has hu_space hag hu_grad
  have hp : parabolicOperatorWithDrift G T X (fun s _ => a s) t x = a' := by
    unfold parabolicOperatorWithDrift heatOperatorWithDrift laplacianAt
    rw [ha.derivWithin huniq, laplacian_const]
    simp only [driftTerm, gradientAt, gradientFun_const, map_zero, zero_add, sub_zero]
  rw [hp] at hh
  simpa only [gradientAt, gradientFun_const, map_zero, zero_apply, mul_zero, sub_zero, mul_comm a' (u t x)] using hh

include hu_time hu_space hu_grad in
theorem parabolic_exp_rescale_local (b : ℝ)
    (huniq : UniqueDiffWithinAt ℝ (Icc 0 T) t) :
    parabolicOperatorWithDrift G T X (fun s y => Real.exp (-b * s) * u s y) t x =
      Real.exp (-b * t) * (parabolicOperatorWithDrift G T X u t x - b * u t x) := by
  have hd : HasDerivWithinAt (fun s : ℝ => Real.exp (-b * s))
      (Real.exp (-b * t) * (-b)) (Icc 0 T) t := by
    have hh := (((hasDerivAt_id t).const_mul (-b)).exp).hasDerivWithinAt (s := Icc 0 T)
    simp only [mul_one, id_eq] at hh
    exact hh
  rw [parabolic_time_mul_local G T X u t x hu_time hu_space hu_grad _ _ hd huniq]
  ring
end DifferentialGeometry.Analysis
