import DifferentialGeometry.Analysis.Parabolic.Operator
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Analysis.Parabolic

open Bundle Filter Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem parabolic_comp_of_eventually_differentiable
    (G : MetricConnectionFamily (I := I) (M := M) ℝ)
    (T : ℝ) (X : ℝ → (x : M) → TangentSpace I x)
    {φ : ℝ → ℝ} (u : ℝ → M → ℝ) (t : ℝ) (x : M)
    (hφ : ∀ᶠ z in 𝓝 (u t x), DifferentiableAt ℝ φ z)
    (hφ' : DifferentiableAt ℝ (deriv φ) (u t x))
    (hu_time : DifferentiableWithinAt ℝ (fun s => u s x) (Icc 0 T) t)
    (hu_space : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (u t) y)
    (hu_grad : MDiffAt (T% fun y : M => gradientFun (I := I) (G.metric t) (u t) y) x) :
    parabolicOperatorWithDrift (I := I) G T X (fun s y => φ (u s y)) t x =
      deriv φ (u t x) * parabolicOperatorWithDrift (I := I) G T X u t x -
        deriv (deriv φ) (u t x) * (G.metric t).inner x
          (gradientAt (I := I) G t (u t) x) (gradientAt (I := I) G t (u t) x) := by
  have htime : derivWithin (fun s => φ (u s x)) (Icc 0 T) t =
      deriv φ (u t x) * derivWithin (fun s => u s x) (Icc 0 T) t := by
    have hcomp := derivWithin_comp (x := t)
      (h := fun s => u s x) (h₂ := φ) (s := Icc 0 T) (s' := Set.univ)
      hφ.self_of_nhds.differentiableWithinAt hu_time (Set.mapsTo_univ _ _)
    rw [derivWithin_univ] at hcomp
    exact hcomp
  have hlap := laplacian_comp_of_eventually_differentiable (I := I)
    (G.connection t) (G.metric t) hφ hφ' hu_space hu_grad
  have hgrad := gradientFun_comp (I := I) (G.metric t) hφ.self_of_nhds
    hu_space.self_of_nhds
  unfold parabolicOperatorWithDrift heatOperatorWithDrift laplacianAt driftTerm gradientAt
  rw [htime, hlap, hgrad]
  simp only [map_smul, smul_eq_mul]
  ring

theorem parabolic_log_at
    (G : MetricConnectionFamily (I := I) (M := M) ℝ)
    (T : ℝ) (X : ℝ → (x : M) → TangentSpace I x)
    (u : ℝ → M → ℝ) (t : ℝ) (x : M) (hu : u t x ≠ 0)
    (hu_time : DifferentiableWithinAt ℝ (fun s => u s x) (Icc 0 T) t)
    (hu_space : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (u t) y)
    (hu_grad : MDiffAt (T% fun y : M => gradientFun (I := I) (G.metric t) (u t) y) x) :
    parabolicOperatorWithDrift (I := I) G T X (fun s y => Real.log (u s y)) t x =
      (u t x)⁻¹ * parabolicOperatorWithDrift (I := I) G T X u t x +
        (u t x ^ 2)⁻¹ * (G.metric t).inner x
          (gradientAt (I := I) G t (u t) x) (gradientAt (I := I) G t (u t) x) := by
  have hlog : ∀ᶠ z in 𝓝 (u t x), DifferentiableAt ℝ Real.log z := by
    filter_upwards [eventually_ne_nhds hu] with z hz
    exact Real.differentiableAt_log hz
  have hlog' : DifferentiableAt ℝ (deriv Real.log) (u t x) := by
    simpa only [Real.deriv_log'] using (differentiableAt_inv (𝕜 := ℝ) hu)
  rw [parabolic_comp_of_eventually_differentiable (I := I) G T X u t x hlog hlog'
    hu_time hu_space hu_grad]
  rw [Real.deriv_log', deriv_inv]
  simp only [sub_eq_add_neg, neg_mul, neg_neg]

theorem parabolic_mul_log_at
    (G : MetricConnectionFamily (I := I) (M := M) ℝ)
    (T : ℝ) (X : ℝ → (x : M) → TangentSpace I x)
    (u : ℝ → M → ℝ) (t : ℝ) (x : M) (hu : u t x ≠ 0)
    (hu_time : DifferentiableWithinAt ℝ (fun s => u s x) (Icc 0 T) t)
    (hu_space : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (u t) y)
    (hu_grad : MDiffAt (T% fun y : M => gradientFun (I := I) (G.metric t) (u t) y) x) :
    parabolicOperatorWithDrift (I := I) G T X (fun s y => u s y * Real.log (u s y)) t x =
      (Real.log (u t x) + 1) * parabolicOperatorWithDrift (I := I) G T X u t x -
        (u t x)⁻¹ * (G.metric t).inner x
          (gradientAt (I := I) G t (u t) x) (gradientAt (I := I) G t (u t) x) := by
  have hφ : ∀ᶠ z in 𝓝 (u t x), DifferentiableAt ℝ (fun z => z * Real.log z) z := by
    filter_upwards [eventually_ne_nhds hu] with z hz
    exact (Real.hasDerivAt_mul_log hz).differentiableAt
  have heq : deriv (fun z => z * Real.log z) =ᶠ[𝓝 (u t x)] (fun z => Real.log z + 1) := by
    filter_upwards [eventually_ne_nhds hu] with z hz
    exact Real.deriv_mul_log hz
  have hφ' : DifferentiableAt ℝ (deriv (fun z => z * Real.log z)) (u t x) :=
    ((Real.differentiableAt_log hu).add_const 1).congr_of_eventuallyEq heq
  rw [parabolic_comp_of_eventually_differentiable G T X u t x hφ hφ'
    hu_time hu_space hu_grad, Real.deriv_mul_log hu]
  rw [show deriv (deriv (fun z => z * Real.log z)) (u t x) = (u t x)⁻¹ from
    Real.deriv2_mul_log (u t x)]

theorem parabolic_sub_mul_log_at
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) ℝ)
    (T : ℝ) (X : ℝ → (x : M) → TangentSpace I x)
    (u v : ℝ → M → ℝ) (t : ℝ) (x : M) (hv : v t x ≠ 0)
    (hu_time : DifferentiableWithinAt ℝ (fun s => u s x) (Icc 0 T) t)
    (hv_time : DifferentiableWithinAt ℝ (fun s => v s x) (Icc 0 T) t)
    (hu_space : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (u t) y)
    (hv_space : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (v t) y)
    (hu_grad : MDiffAt (T% fun y : M => gradientFun (I := I) (G.metric t) (u t) y) x)
    (hv_grad : MDiffAt (T% fun y : M => gradientFun (I := I) (G.metric t) (v t) y) x) :
    parabolicOperatorWithDrift (I := I) G T X
        (fun s y => u s y - v s y * Real.log (v s y)) t x =
      parabolicOperatorWithDrift (I := I) G T X u t x -
        (Real.log (v t x) + 1) * parabolicOperatorWithDrift (I := I) G T X v t x +
          (v t x)⁻¹ * (G.metric t).inner x
            (gradientAt (I := I) G t (v t) x) (gradientAt (I := I) G t (v t) x) := by
  have hnear : ∀ᶠ y in 𝓝 x, v t y ≠ 0 :=
    hv_space.self_of_nhds.continuousAt.eventually_ne hv
  have hlogspace : ∀ᶠ y in 𝓝 x,
      MDifferentiableAt I 𝓘(ℝ, ℝ) (fun z => v t z * Real.log (v t z)) y := by
    filter_upwards [hv_space, hnear] with y hy hne
    exact (Real.hasDerivAt_mul_log hne).differentiableAt.mdifferentiableAt.comp y hy
  have hloggrad : MDiffAt (T% fun y : M =>
      gradientFun (I := I) (G.metric t) (fun z => v t z * Real.log (v t z)) y) x := by
    have hc : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => Real.log (v t y) + 1) x :=
      ((Real.differentiableAt_log hv).mdifferentiableAt.comp x
        hv_space.self_of_nhds).add mdifferentiableAt_const
    refine (hc.smul_section hv_grad).congr_of_eventuallyEq ?_
    filter_upwards [hv_space, hnear] with y hy hne
    apply congrArg (fun w => (⟨y, w⟩ : TotalSpace E (TangentSpace I : M → Type _)))
    rw [gradientFun_comp (I := I) (G.metric t)
      (Real.hasDerivAt_mul_log hne).differentiableAt hy, Real.deriv_mul_log hne]
    rfl
  have hlogtime : DifferentiableWithinAt ℝ
      (fun s => v s x * Real.log (v s x)) (Icc 0 T) t :=
    hv_time.mul (hv_time.log hv)
  rw [parabolic_sub_nhds (G := G) T X u (fun s y => v s y * Real.log (v s y)) t x
    hu_time hlogtime
    hu_space hlogspace hu_grad hloggrad,
    parabolic_mul_log_at G T X v t x hv hv_time hv_space hv_grad]
  ring

theorem parabolic_mul_log_add_time_at
    (G : MetricConnectionFamily (I := I) (M := M) ℝ)
    (T : ℝ) (X : ℝ → (x : M) → TangentSpace I x)
    (u : ℝ → M → ℝ) (c : ℝ → ℝ) (t : ℝ) (x : M) (hu : u t x ≠ 0)
    (hu_time : DifferentiableWithinAt ℝ (fun s => u s x) (Icc 0 T) t)
    (hc_time : DifferentiableWithinAt ℝ c (Icc 0 T) t)
    (hu_space : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (u t) y)
    (hu_grad : MDiffAt (T% fun y : M => gradientFun (I := I) (G.metric t) (u t) y) x) :
    parabolicOperatorWithDrift (I := I) G T X
        (fun s y => u s y * (Real.log (u s y) + c s)) t x =
      (Real.log (u t x) + c t + 1) * parabolicOperatorWithDrift (I := I) G T X u t x +
        derivWithin c (Icc 0 T) t * u t x -
          (u t x)⁻¹ * (G.metric t).inner x
            (gradientAt (I := I) G t (u t) x) (gradientAt (I := I) G t (u t) x) := by
  let φ : ℝ → ℝ := fun z => z * (Real.log z + c t)
  have hderiv (z : ℝ) (hz : z ≠ 0) :
      HasDerivAt φ (Real.log z + c t + 1) z := by
    have h := (hasDerivAt_id z).mul ((Real.hasDerivAt_log hz).add_const (c t))
    simpa only [φ, id_eq, one_mul, mul_inv_cancel₀ hz] using! h
  have hφ : ∀ᶠ z in 𝓝 (u t x), DifferentiableAt ℝ φ z := by
    filter_upwards [eventually_ne_nhds hu] with z hz
    exact (hderiv z hz).differentiableAt
  have heq : deriv φ =ᶠ[𝓝 (u t x)] (fun z => Real.log z + c t + 1) := by
    filter_upwards [eventually_ne_nhds hu] with z hz
    exact (hderiv z hz).deriv
  have hφ' : DifferentiableAt ℝ (deriv φ) (u t x) :=
    (((Real.differentiableAt_log hu).add_const (c t)).add_const 1).congr_of_eventuallyEq heq
  have hsecond : deriv (deriv φ) (u t x) = (u t x)⁻¹ := by
    rw [heq.deriv_eq]
    exact (((Real.hasDerivAt_log hu).add_const (c t)).add_const 1).deriv
  have hstatic := parabolic_comp_of_eventually_differentiable G T X u t x hφ hφ'
    hu_time hu_space hu_grad
  rw [(hderiv _ hu).deriv, hsecond] at hstatic
  have hlogtime := hu_time.log hu
  have hdynt : DifferentiableWithinAt ℝ (fun s => Real.log (u s x) + c s) (Icc 0 T) t :=
    hlogtime.add hc_time
  have hfixt : DifferentiableWithinAt ℝ (fun s => Real.log (u s x) + c t) (Icc 0 T) t :=
    hlogtime.add_const (c t)
  have htime :
      derivWithin (fun s => u s x * (Real.log (u s x) + c s)) (Icc 0 T) t =
        derivWithin (fun s => φ (u s x)) (Icc 0 T) t +
          derivWithin c (Icc 0 T) t * u t x := by
    dsimp only [φ]
    rw [derivWithin_fun_mul hu_time hdynt,
      derivWithin_fun_mul hu_time hfixt,
      derivWithin_fun_add hlogtime hc_time,
      derivWithin_add_const (c t)]
    ring
  unfold parabolicOperatorWithDrift at hstatic ⊢
  rw [htime]
  dsimp only [φ] at hstatic
  linarith

theorem parabolic_sub_mul_log_add_time_at
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) ℝ)
    (T : ℝ) (X : ℝ → (x : M) → TangentSpace I x)
    (u v : ℝ → M → ℝ) (c : ℝ → ℝ) (t : ℝ) (x : M) (hv : v t x ≠ 0)
    (hu_time : DifferentiableWithinAt ℝ (fun s => u s x) (Icc 0 T) t)
    (hv_time : DifferentiableWithinAt ℝ (fun s => v s x) (Icc 0 T) t)
    (hc_time : DifferentiableWithinAt ℝ c (Icc 0 T) t)
    (hu_space : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (u t) y)
    (hv_space : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (v t) y)
    (hu_grad : MDiffAt (T% fun y : M => gradientFun (I := I) (G.metric t) (u t) y) x)
    (hv_grad : MDiffAt (T% fun y : M => gradientFun (I := I) (G.metric t) (v t) y) x) :
    parabolicOperatorWithDrift (I := I) G T X
        (fun s y => u s y - v s y * (Real.log (v s y) + c s)) t x =
      parabolicOperatorWithDrift (I := I) G T X u t x -
        (Real.log (v t x) + c t + 1) * parabolicOperatorWithDrift (I := I) G T X v t x - derivWithin c (Icc 0 T) t * v t x +
          (v t x)⁻¹ * (G.metric t).inner x
            (gradientAt (I := I) G t (v t) x) (gradientAt (I := I) G t (v t) x) := by
  have hnear : ∀ᶠ y in 𝓝 x, v t y ≠ 0 :=
    hv_space.self_of_nhds.continuousAt.eventually_ne hv
  have hlogspace : ∀ᶠ y in 𝓝 x,
      MDifferentiableAt I 𝓘(ℝ, ℝ) (fun z => v t z * (Real.log (v t z) + c t)) y := by
    filter_upwards [hv_space, hnear] with y hy hne
    exact hy.mul (((Real.differentiableAt_log hne).mdifferentiableAt.comp y hy).add
      mdifferentiableAt_const)
  have hloggrad : MDiffAt (T% fun y : M =>
      gradientFun (I := I) (G.metric t) (fun z => v t z * (Real.log (v t z) + c t)) y) x := by
    have hc : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => Real.log (v t y) + c t + 1) x :=
      ((Real.differentiableAt_log hv).mdifferentiableAt.comp x
        hv_space.self_of_nhds).add mdifferentiableAt_const |>.add mdifferentiableAt_const
    refine (hc.smul_section hv_grad).congr_of_eventuallyEq ?_
    filter_upwards [hv_space, hnear] with y hy hne
    apply congrArg (fun w => (⟨y, w⟩ : TotalSpace E (TangentSpace I : M → Type _)))
    have hd : HasDerivAt (fun z : ℝ => z * (Real.log z + c t))
        (Real.log (v t y) + c t + 1) (v t y) := by
      simpa only [id_eq, one_mul, mul_inv_cancel₀ hne] using!
        (hasDerivAt_id (v t y)).mul ((Real.hasDerivAt_log hne).add_const (c t))
    rw [gradientFun_comp (I := I) (G.metric t) hd.differentiableAt hy, hd.deriv]
    rfl
  have hlogtime : DifferentiableWithinAt ℝ
      (fun s => v s x * (Real.log (v s x) + c s)) (Icc 0 T) t :=
    hv_time.mul ((hv_time.log hv).add hc_time)
  rw [parabolic_sub_nhds (G := G) T X u (fun s y => v s y * (Real.log (v s y) + c s)) t x
    hu_time hlogtime
    hu_space hlogspace hu_grad hloggrad,
    parabolic_mul_log_add_time_at G T X v c t x hv hv_time hc_time hv_space hv_grad]
  ring

end DifferentialGeometry.Analysis.Parabolic
