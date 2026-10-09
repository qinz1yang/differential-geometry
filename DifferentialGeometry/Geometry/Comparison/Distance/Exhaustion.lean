import DifferentialGeometry.Geometry.Connection.LeviCivita.Defs
import DifferentialGeometry.Geometry.Comparison.Distance.Hessian
import DifferentialGeometry.Geometry.Comparison.HopfRinow.Proper
import DifferentialGeometry.Geometry.Connection.ChartBridge.Scalar.Laplacian
import DifferentialGeometry.Geometry.Operator.Gradient.Regularity
import DifferentialGeometry.Geometry.Operator.Scalar.Calculus
import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas

open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set Topology
open scoped ContDiff ENNReal Manifold

namespace DifferentialGeometry

private def distanceExhaustionProfile (s : Real) : Real :=
  s * Real.smoothTransition (s - 1)

private theorem distanceExhaustionProfile_contDiff :
    ContDiff Real ∞ distanceExhaustionProfile := by
  exact contDiff_id.mul
    (Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const))

private theorem distanceExhaustionProfile_eq_zero {s : Real} (hs : s ≤ 1) :
    distanceExhaustionProfile s = 0 := by
  rw [distanceExhaustionProfile,
    Real.smoothTransition.zero_of_nonpos (sub_nonpos.mpr hs), mul_zero]

private theorem distanceExhaustionProfile_eq_self {s : Real} (hs : 2 ≤ s) :
    distanceExhaustionProfile s = s := by
  rw [distanceExhaustionProfile,
    Real.smoothTransition.one_of_one_le (by linarith), mul_one]

private theorem distanceExhaustionProfile_nonneg {s : Real} (hs : 0 ≤ s) :
    0 ≤ distanceExhaustionProfile s :=
  mul_nonneg hs (Real.smoothTransition.nonneg _)

private theorem distanceExhaustionProfile_monotone :
    Monotone distanceExhaustionProfile := by
  intro a b hab
  by_cases hb : b ≤ 1
  · rw [distanceExhaustionProfile_eq_zero hb,
      distanceExhaustionProfile_eq_zero (hab.trans hb)]
  · by_cases ha : a ≤ 1
    · rw [distanceExhaustionProfile_eq_zero ha]
      exact distanceExhaustionProfile_nonneg (le_trans (by norm_num) (lt_of_not_ge hb).le)
    · unfold distanceExhaustionProfile
      calc
        a * Real.smoothTransition (a - 1) ≤
            b * Real.smoothTransition (a - 1) :=
          mul_le_mul_of_nonneg_right hab (Real.smoothTransition.nonneg _)
        _ ≤ b * Real.smoothTransition (b - 1) :=
          mul_le_mul_of_nonneg_left
            (Real.smoothTransition.monotone (sub_le_sub_right hab 1))
            (le_trans (by norm_num) (lt_of_not_ge hb).le)

private theorem distanceExhaustionProfile_deriv_eq_zero {s : Real} (hs : s < 1) :
    deriv distanceExhaustionProfile s = 0 := by
  have hloc : distanceExhaustionProfile =ᶠ[nhds s] fun _ => (0 : Real) := by
    filter_upwards [Iio_mem_nhds hs] with y hy
    exact distanceExhaustionProfile_eq_zero hy.le
  rw [hloc.deriv_eq, deriv_const]

private theorem distanceExhaustionProfile_deriv_eq_one {s : Real} (hs : 2 < s) :
    deriv distanceExhaustionProfile s = 1 := by
  have hloc : distanceExhaustionProfile =ᶠ[nhds s] id := by
    filter_upwards [Ioi_mem_nhds hs] with y hy
    exact distanceExhaustionProfile_eq_self hy.le
  rw [hloc.deriv_eq, deriv_id]

private theorem distanceExhaustionProfile_second_deriv_eq_zero_of_lt_one
    {s : Real} (hs : s < 1) :
    deriv (deriv distanceExhaustionProfile) s = 0 := by
  have hloc : deriv distanceExhaustionProfile =ᶠ[nhds s] fun _ => (0 : Real) := by
    filter_upwards [Iio_mem_nhds hs] with y hy
    exact distanceExhaustionProfile_deriv_eq_zero hy
  rw [hloc.deriv_eq, deriv_const]

private theorem distanceExhaustionProfile_second_deriv_eq_zero_of_two_lt
    {s : Real} (hs : 2 < s) :
    deriv (deriv distanceExhaustionProfile) s = 0 := by
  have hloc : deriv distanceExhaustionProfile =ᶠ[nhds s] fun _ => (1 : Real) := by
    filter_upwards [Ioi_mem_nhds hs] with y hy
    exact distanceExhaustionProfile_deriv_eq_one hy
  rw [hloc.deriv_eq, deriv_const]

private theorem exists_distanceExhaustionProfile_deriv_bounds :
    ∃ C : Real, 1 ≤ C ∧
      (∀ s : Real, |deriv distanceExhaustionProfile s| ≤ C) ∧
      (∀ s : Real, |deriv (deriv distanceExhaustionProfile) s| ≤ C) := by
  have hderivSmooth : ContDiff Real ∞ (deriv distanceExhaustionProfile) :=
    (contDiff_infty_iff_deriv.mp distanceExhaustionProfile_contDiff).2
  have hderivCont : Continuous (deriv distanceExhaustionProfile) :=
    hderivSmooth.continuous
  have hsecondCont : Continuous (deriv (deriv distanceExhaustionProfile)) :=
    ((contDiff_infty_iff_deriv.mp hderivSmooth).2).continuous
  obtain ⟨s₁, -, hs₁⟩ :=
    (isCompact_Icc (a := (1 : Real)) (b := 2)).exists_isMaxOn
      (Set.nonempty_Icc.2 (by norm_num)) hderivCont.norm.continuousOn
  obtain ⟨s₂, -, hs₂⟩ :=
    (isCompact_Icc (a := (1 : Real)) (b := 2)).exists_isMaxOn
      (Set.nonempty_Icc.2 (by norm_num)) hsecondCont.norm.continuousOn
  let C := max 1 (max |deriv distanceExhaustionProfile s₁|
    |deriv (deriv distanceExhaustionProfile) s₂|)
  refine ⟨C, le_max_left _ _, ?_, ?_⟩
  · intro s
    by_cases hslo : s < 1
    · rw [distanceExhaustionProfile_deriv_eq_zero hslo, abs_zero]
      exact le_trans (by norm_num) (le_max_left _ _)
    · by_cases hshi : 2 < s
      · rw [distanceExhaustionProfile_deriv_eq_one hshi, abs_one]
        exact le_max_left _ _
      · push Not at hslo hshi
        have hmax := Filter.eventually_principal.mp hs₁ s (Set.mem_Icc.2 ⟨hslo, hshi⟩)
        exact hmax.trans (le_trans (le_max_left _ _) (le_max_right _ _))
  · intro s
    by_cases hslo : s < 1
    · rw [distanceExhaustionProfile_second_deriv_eq_zero_of_lt_one hslo, abs_zero]
      exact le_trans (by norm_num) (le_max_left _ _)
    · by_cases hshi : 2 < s
      · rw [distanceExhaustionProfile_second_deriv_eq_zero_of_two_lt hshi, abs_zero]
        exact le_trans (by norm_num) (le_max_left _ _)
      · push Not at hslo hshi
        have hmax := Filter.eventually_principal.mp hs₂ s (Set.mem_Icc.2 ⟨hslo, hshi⟩)
        exact hmax.trans (le_trans (le_max_right _ _) (le_max_right _ _))

private theorem laplacian_comp_of_eventually_mdiff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [FiniteDimensional Real E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners Real E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (g : SmoothRiemannianMetric I M)
    {φ : Real → Real} {f : M → Real} {x : M}
    (hφ : Differentiable Real φ)
    (hφ' : DifferentiableAt Real (deriv φ) (f x))
    (hf : ∀ᶠ y in nhds x,
      MDifferentiableAt I (modelWithCornersSelf Real Real) f y)
    (hgrad : MDiffAt
      (T% fun y : M => gradientFun (I := I) g f y) x) :
    laplacian (I := I) cov g (fun y : M => φ (f y)) x =
      deriv φ (f x) * laplacian (I := I) cov g f x +
        deriv (deriv φ) (f x) *
          g.inner x (gradientFun (I := I) g f x)
            (gradientFun (I := I) g f x) := by
  let coeffFun : M → Real := fun y => deriv φ (f y)
  have hcoeff : MDifferentiableAt I (modelWithCornersSelf Real Real) coeffFun x :=
    hφ'.mdifferentiableAt.comp x hf.self_of_nhds
  have hcompGrad : MDiffAt
      (T% fun y : M => gradientFun (I := I) g (fun z => φ (f z)) y) x :=
    grad_comp_mdiffAt (I := I) g hφ hφ' hf hgrad
  have hproductGrad : MDiffAt
      (T% fun y : M => coeffFun y • gradientFun (I := I) g f y) x :=
    hcoeff.smul_section hgrad
  have hgradEq :
      (fun y : M => gradientFun (I := I) g (fun z => φ (f z)) y) =ᶠ[nhds x]
        fun y : M => coeffFun y • gradientFun (I := I) g f y := by
    filter_upwards [hf] with y hy
    exact gradientFun_comp (I := I) g (hφ (f y)) hy
  have hcovEq :
      cov (fun y : M => gradientFun (I := I) g (fun z => φ (f z)) y) x =
        cov (fun y : M => coeffFun y • gradientFun (I := I) g f y) x :=
    cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      hcompGrad hproductGrad Filter.univ_mem hgradEq
  calc
    laplacian (I := I) cov g (fun y : M => φ (f y)) x =
        divergence (I := I) cov
          (fun y : M => coeffFun y • gradientFun (I := I) g f y) x := by
      unfold laplacian divergence
      rw [hcovEq]
    _ = coeffFun x * laplacian (I := I) cov g f x +
          g.inner x (gradientFun (I := I) g coeffFun x)
            (gradientFun (I := I) g f x) :=
      divergence_smul_gradientFun_pair (I := I) cov g hcoeff hgrad
    _ = deriv φ (f x) * laplacian (I := I) cov g f x +
          deriv (deriv φ) (f x) *
            g.inner x (gradientFun (I := I) g f x)
              (gradientFun (I := I) g f x) := by
      rw [gradientFun_comp (I := I) g hφ' hf.self_of_nhds]
      simp [coeffFun]

private theorem hessFun_comp_of_contDiff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [FiniteDimensional Real E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners Real E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [T2Space M]
    (g : SmoothRiemannianMetric I M)
    {phi : Real → Real} {f : M → Real}
    (hphi : ContDiff Real ∞ phi)
    (hf : ContMDiff I (modelWithCornersSelf Real Real) ∞ f)
    (x : M) (v w : TangentSpace I x) :
    hessFun (I := I) g (fun y ↦ phi (f y)) x v w =
      deriv phi (f x) * hessFun (I := I) g f x v w +
        deriv (deriv phi) (f x) *
          g.inner x (gradientFun (I := I) g f x) v *
          g.inner x (gradientFun (I := I) g f x) w := by
  let coeffFun : M → Real := fun y ↦ deriv phi (f y)
  have hphiDiff : Differentiable Real phi := hphi.differentiable (by simp)
  have hphiDeriv : ContDiff Real ∞ (deriv phi) :=
    (contDiff_infty_iff_deriv.mp hphi).2
  have hcoeff : ContMDiff I (modelWithCornersSelf Real Real) ∞ coeffFun :=
    hphiDeriv.contMDiff.comp hf
  have hgradf : ContMDiff I (I.prod (modelWithCornersSelf Real E)) ∞
      (T% fun y : M ↦ gradFun (I := I) g f y) :=
    gradFun_contMDiff_total_section (I := I) g hf
  have hgradEq :
      (fun y : M ↦ gradFun (I := I) g (phi ∘ f) y) =
        coeffFun • fun y : M ↦ gradFun (I := I) g f y := by
    funext y
    change gradientFun (I := I) g (fun z ↦ phi (f z)) y =
      deriv phi (f y) • gradientFun (I := I) g f y
    exact gradientFun_comp (I := I) g (hphiDiff (f y))
      ((hf y).mdifferentiableAt (by simp))
  have hcoeffDeriv :
      mvfderiv (I := I) coeffFun x v =
        deriv (deriv phi) (f x) * mvfderiv (I := I) f x v := by
    have hchain := mvfderiv_comp_apply
      (I := modelWithCornersSelf Real Real) (I' := I)
      (f := f) (g := deriv phi) x
      (hphiDeriv.differentiable (by simp) (f x)).mdifferentiableAt
      ((hf x).mdifferentiableAt (by simp)) v
    rw [mvfderiv_real_model_eq_fderiv,
      (hphiDeriv.differentiable (by simp) (f x)).hasDerivAt.hasFDerivAt.fderiv]
      at hchain
    rw [← mvfderiv_real_eq_mfderiv I f x v] at hchain
    simpa [coeffFun, Function.comp_def,
      ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, mul_comm] using hchain
  change hessFun (I := I) g (phi ∘ f) x v w = _
  rw [hessFun_eq_cov_grad (I := I) g
    (hphi.contMDiff.comp hf) x v w, hgradEq]
  rw [(LeviCivita (I := I) g).isCovariantDerivativeOnUniv.leibniz
    ((hgradf x).mdifferentiableAt (by simp))
    ((hcoeff x).mdifferentiableAt (by simp))]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    map_add, map_smul, smul_eq_mul]
  rw [hessFun_eq_cov_grad (I := I) g hf x v w, hcoeffDeriv,
    inner_gradientFun]
  simp only [coeffFun, gradient_eq_gradFun]

private theorem hessFun_comp_of_contMDiffOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [FiniteDimensional Real E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners Real E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [T2Space M]
    (g : SmoothRiemannianMetric I M)
    {phi : Real → Real} {f : M → Real} {U : Set M}
    (hphi : ContDiff Real ∞ phi)
    (hU : IsOpen U)
    (hf : ContMDiffOn I (modelWithCornersSelf Real Real) ∞ f U)
    {x : M} (hx : x ∈ U) (v w : TangentSpace I x) :
    hessFun (I := I) g (fun y ↦ phi (f y)) x v w =
      deriv phi (f x) * hessFun (I := I) g f x v w +
        deriv (deriv phi) (f x) *
          g.inner x (gradientFun (I := I) g f x) v *
          g.inner x (gradientFun (I := I) g f x) w := by
  obtain ⟨F, hF, hFf⟩ :=
    DifferentialGeometry.exists_smooth_germ (I := I) hU hx hf
  have hcomp : (fun y ↦ phi (F y)) =ᶠ[nhds x] fun y ↦ phi (f y) :=
    hFf.fun_comp phi
  have hvalue : F x = f x := hFf.eq_of_nhds
  have hgrad :
      gradientFun (I := I) g F x = gradientFun (I := I) g f x := by
    unfold gradientFun
    congr 1
    unfold mvfderiv
    rw [hFf.mfderiv_eq, hvalue]
    ext u
    rfl
  calc
    hessFun (I := I) g (fun y ↦ phi (f y)) x v w =
        hessFun (I := I) g (fun y ↦ phi (F y)) x v w := by
      exact congrArg (fun B ↦ B v w)
        (hessFun_congr (I := I) g hcomp.symm)
    _ = deriv phi (F x) * hessFun (I := I) g F x v w +
          deriv (deriv phi) (F x) *
            g.inner x (gradientFun (I := I) g F x) v *
            g.inner x (gradientFun (I := I) g F x) w :=
      hessFun_comp_of_contDiff (I := I) g hphi hF x v w
    _ = _ := by
      rw [hvalue, hgrad,
        congrArg (fun B ↦ B v w) (hessFun_congr (I := I) g hFf)]

private theorem hessFun_const
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [FiniteDimensional Real E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners Real E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [T2Space M]
    (g : SmoothRiemannianMetric I M) (c : Real) (x : M) :
    hessFun (I := I) g (fun _ : M ↦ c) x = 0 := by
  have hzero : hessFun (I := I) g (fun _ : M ↦ (0 : Real)) x = 0 := by
    have hsmul := congrFun
      (hessFun_smul (I := I) g 0 (fun _ : M ↦ (1 : Real))) x
    change hessFun (I := I) g (0 : M → Real) x = 0
    simpa using hsmul
  have hadd := hessFun_add_const (I := I) g c
    (U := Set.univ) (f := fun _ : M ↦ (0 : Real)) isOpen_univ
    contMDiffOn_const (Set.mem_univ x)
  simpa [hzero] using hadd

private theorem gInner_sq_le_mul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [FiniteDimensional Real E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners Real E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M]
    (g : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    (g.inner x v w) ^ 2 ≤ g.inner x v v * g.inner x w w := by
  let D := (Tensor0SBundle.tangentMetricData (I := I) g x).metric
  let : PreInnerProductSpace.Core Real (TangentSpace I x) := D.toCore.toCore
  let : Inner Real (TangentSpace I x) := D.toCore.toCore.toInner
  have hcs := InnerProductSpace.Core.inner_mul_inner_self_le
    (𝕜 := Real) (F := TangentSpace I x) v w
  have hvw : Inner.inner Real v w = g.inner x v w := by
    exact Tensor0SBundle.TangentMetricData.inner_eq
      (Tensor0SBundle.tangentMetricData (I := I) g x) v w
  have hwv : Inner.inner Real w v = g.inner x v w := by
    calc
      Inner.inner Real w v = g.inner x w v :=
        Tensor0SBundle.TangentMetricData.inner_eq
          (Tensor0SBundle.tangentMetricData (I := I) g x) w v
      _ = g.inner x v w := g.symm x w v
  have hvv : Inner.inner Real v v = g.inner x v v := by
    exact Tensor0SBundle.TangentMetricData.inner_eq
      (Tensor0SBundle.tangentMetricData (I := I) g x) v v
  have hww : Inner.inner Real w w = g.inner x w w := by
    exact Tensor0SBundle.TangentMetricData.inner_eq
      (Tensor0SBundle.tangentMetricData (I := I) g x) w w
  rw [hvw, hwv, hvv, hww] at hcs
  simpa [Real.norm_eq_abs, pow_two] using hcs

private theorem isProperMap_one_add_distanceExhaustionProfile
    {M : Type*} [MetricSpace M] [ProperSpace M] (O : M) :
    IsProperMap
      (fun x : M => 1 + distanceExhaustionProfile (dist O x)) := by
  rw [isProperMap_iff_isCompact_preimage]
  refine ⟨continuous_const.add
    (distanceExhaustionProfile_contDiff.continuous.comp
      (continuous_const.dist continuous_id)), ?_⟩
  intro K hK
  obtain ⟨B, hB⟩ := hK.bddAbove
  have hcont : Continuous
      (fun x : M => 1 + distanceExhaustionProfile (dist O x)) :=
    continuous_const.add
      (distanceExhaustionProfile_contDiff.continuous.comp
        (continuous_const.dist continuous_id))
  refine (isCompact_closedBall O (max 2 (B - 1))).of_isClosed_subset
    (hK.isClosed.preimage hcont) ?_
  intro x hx
  rw [Metric.mem_closedBall]
  have hvalue : 1 + distanceExhaustionProfile (dist O x) ≤ B :=
    hB hx
  by_cases hdist : 2 ≤ dist O x
  · rw [distanceExhaustionProfile_eq_self hdist] at hvalue
    rw [dist_comm]
    exact (by linarith : dist O x ≤ B - 1).trans (le_max_right _ _)
  · rw [dist_comm]
    exact (lt_of_not_ge hdist).le.trans (le_max_left _ _)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_proper_distance_exhaustion
    [NeZero (Module.finrank Real E)] [T2Space (TangentBundle I M)]
    [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M)
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (q : Real) (hq : 0 ≤ q)
    (hRic : Geometry.Riemannian.BonnetMyers.RicciBoundedBelow (I := I) g
      (-(((Module.finrank Real E - 1 : Nat) : Real) * q ^ 2)))
    (O : M) :
    ∃ h : M → Real, Continuous h ∧ IsProperMap h ∧
      (∀ x, 1 ≤ h x) ∧
      ∃ C : Real, 1 ≤ C ∧ ∀ x : M, ∃ hbar : M → Real,
        ContMDiffAt I 𝓘(Real, Real) ∞ hbar x ∧
        hbar x = h x ∧
        (∀ᶠ y in nhds x, h y ≤ hbar y) ∧
        g.inner x
            (gradientFun (I := I) g hbar x)
            (gradientFun (I := I) g hbar x) ≤ C ∧
        laplacian (I := I) (LeviCivita (I := I) g) g hbar x ≤ C := by
  let _ : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := (∞ : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  let _ : TopologicalSpace.MetrizableSpace M :=
    Manifold.metrizableSpace I M
  let _ : T3Space M := inferInstance
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let _ : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let _ : PseudoEMetricSpace M := inferInstance
  let _ : CompleteSpace M := hcomplete.complete
  let _ : MetricSpace M :=
    Geometry.Riemannian.HopfRinow.riemMetricSpace (I := I) (M := M)
  let _ : ProperSpace M :=
    Geometry.Riemannian.HopfRinow.properSpace_riemMetric
        (I := I) (M := M) hcomplete.complete g
        (fun x v ↦ Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
          (I := I) g x v)
  obtain ⟨D, hD, hDfirst, hDsecond⟩ :=
    exists_distanceExhaustionProfile_deriv_bounds
  let n : Real := ((Module.finrank Real E - 1 : Nat) : Real)
  let C : Real := max 1 (max (D ^ 2) (D * (2 * n + n * q) + D))
  let h : M → Real := fun x ↦ 1 + distanceExhaustionProfile (dist O x)
  have hcont : Continuous h :=
    continuous_const.add
      (distanceExhaustionProfile_contDiff.continuous.comp
        (continuous_const.dist continuous_id))
  refine ⟨h, hcont, isProperMap_one_add_distanceExhaustionProfile O, ?_, C,
    le_max_left _ _, ?_⟩
  · intro x
    exact le_add_of_nonneg_right
      (distanceExhaustionProfile_nonneg dist_nonneg)
  · intro x
    by_cases hx : x = O
    · subst x
      refine ⟨fun _ ↦ 1, contMDiffAt_const, ?_, ?_, ?_, ?_⟩
      · simp [h, distanceExhaustionProfile_eq_zero]
      · filter_upwards [Metric.ball_mem_nhds O (by norm_num : (0 : Real) < 1)] with y hy
        have hdist : dist O y ≤ 1 := by
          rw [dist_comm]
          exact (Metric.mem_ball.mp hy).le
        simp [h, distanceExhaustionProfile_eq_zero hdist]
      · rw [gradientFun_const]
        simp only [map_zero]
        exact le_trans (by norm_num) (le_max_left _ _)
      · rw [laplacian_const]
        exact le_trans (by norm_num) (le_max_left _ _)
    · have hfin :
          riemannianEDistOf (I := I) g O x ≠ (⊤ : ENNReal) := by
        simpa [riemannianEDistOf] using
          (Geometry.Riemannian.Exponential.riemannianEDist_ne_top
            (I := I) O x)
      obtain ⟨tail, hrhoSmooth, hrhoValue, hrhoUpper, hrhoDiff,
          hrhoGrad, hrhoNorm, hrhoLap⟩ :=
        exists_calabiData_of_complete_metric (I := I) (M := M)
          g hcomplete q hq hRic (Ne.symm hx) hfin
      let rho : M → Real := fun y ↦
        tail.initialLength + Geometry.Riemannian.Exponential.branchRadius
          (I := I) g tail.branch y
      let hbar : M → Real := fun y ↦
        1 + distanceExhaustionProfile (rho y)
      have hprofileDiff : Differentiable Real distanceExhaustionProfile :=
        distanceExhaustionProfile_contDiff.differentiable (by simp)
      have hprofileDerivDiff :
          Differentiable Real (deriv distanceExhaustionProfile) :=
        ((contDiff_infty_iff_deriv.mp
          distanceExhaustionProfile_contDiff).2).differentiable (by simp)
      have hrhoValue' : rho x = dist O x := by
        rw [Geometry.Riemannian.HopfRinow.riemMetric_dist_eq
          (I := I) (M := M)]
        exact hrhoValue
      have hbarSmooth : ContMDiffAt I 𝓘(Real, Real) ∞ hbar x := by
        exact contMDiffAt_const.add
          (distanceExhaustionProfile_contDiff.contMDiff.contMDiffAt.comp
            x hrhoSmooth)
      have hbarUpper : ∀ᶠ y in nhds x, h y ≤ hbar y := by
        filter_upwards [hrhoUpper] with y hy
        change 1 + distanceExhaustionProfile (dist O y) ≤
          1 + distanceExhaustionProfile (rho y)
        have hprofile : distanceExhaustionProfile (dist O y) ≤
            distanceExhaustionProfile (rho y) := by
          apply distanceExhaustionProfile_monotone
          rw [Geometry.Riemannian.HopfRinow.riemMetric_dist_eq
            (I := I) (M := M)]
          exact hy
        linarith
      have hgradEq :
          gradientFun (I := I) g hbar x =
            deriv distanceExhaustionProfile (rho x) •
              gradientFun (I := I) g rho x := by
        have hcomp :
            gradientFun (I := I) g
                (fun y ↦ distanceExhaustionProfile (rho y)) x =
              deriv distanceExhaustionProfile (rho x) •
                gradientFun (I := I) g rho x :=
          gradientFun_comp (I := I) g
            (hprofileDiff (rho x)) hrhoDiff.self_of_nhds
        have hadd :
            gradientFun (I := I) g hbar x =
              gradientFun (I := I) g (fun _ : M ↦ (1 : Real)) x +
                gradientFun (I := I) g
                  (fun y ↦ distanceExhaustionProfile (rho y)) x := by
          apply gradientFun_add (I := I) g
          · exact mdifferentiableAt_const
          · exact (hprofileDiff (rho x)).mdifferentiableAt.comp x
              hrhoDiff.self_of_nhds
        rw [hadd, gradientFun_const, zero_add, hcomp]
      have hgradBound :
          g.inner x
              (gradientFun (I := I) g hbar x)
              (gradientFun (I := I) g hbar x) ≤ C := by
        rw [hgradEq, Geometry.Riemannian.Exponential.gInner_smul_self
          (I := I) g x, hrhoNorm]
        simp only [mul_one]
        have habs := hDfirst (rho x)
        have hsq : deriv distanceExhaustionProfile (rho x) ^ 2 ≤ D ^ 2 := by
          apply sq_le_sq.mpr
          simpa [abs_of_nonneg (le_trans (by norm_num) hD)] using habs
        exact hsq.trans (le_trans (le_max_left _ _) (le_max_right _ _))
      have hlapEq := laplacian_comp_of_eventually_mdiff
        (I := I) (LeviCivita (I := I) g) g hprofileDiff
          (hprofileDerivDiff (rho x)) hrhoDiff hrhoGrad
      have hlapBound :
          laplacian (I := I) (LeviCivita (I := I) g) g hbar x ≤ C := by
        have hcompGrad := grad_comp_mdiffAt (I := I) g hprofileDiff
          (hprofileDerivDiff (rho x)) hrhoDiff hrhoGrad
        have haddLap :
            laplacian (I := I) (LeviCivita (I := I) g) g hbar x =
              laplacian (I := I) (LeviCivita (I := I) g) g
                (fun y ↦ distanceExhaustionProfile (rho y)) x := by
          apply laplacian_add_const (I := I)
          · exact Filter.Eventually.mono hrhoDiff fun y hy ↦
              (hprofileDiff (rho y)).mdifferentiableAt.comp y hy
          · exact hcompGrad
        rw [haddLap, hlapEq, hrhoNorm]
        simp only [mul_one]
        by_cases hr : dist O x < 1
        · rw [hrhoValue', distanceExhaustionProfile_deriv_eq_zero hr]
          simp only [zero_mul, zero_add]
          have hDC : D ≤ C := by
            have hDD : D ≤ D ^ 2 := by nlinarith
            exact hDD.trans
              ((le_max_left _ _).trans (le_max_right _ _))
          exact (le_abs_self _).trans
            ((hDsecond (dist O x)).trans hDC)
        · have hrone : 1 ≤ dist O x := le_of_not_gt hr
          have hrpos : 0 < dist O x := lt_of_lt_of_le (by norm_num) hrone
          have hn : 0 ≤ n := Nat.cast_nonneg _
          have hderivNonneg :
              0 ≤ deriv distanceExhaustionProfile (rho x) :=
            distanceExhaustionProfile_monotone.deriv_nonneg
          have hderivLe : deriv distanceExhaustionProfile (rho x) ≤ D :=
            (le_abs_self _).trans (hDfirst (rho x))
          have hsecondLe :
              deriv (deriv distanceExhaustionProfile) (rho x) ≤ D :=
            (le_abs_self _).trans (hDsecond (rho x))
          have hrhoLap' :
              laplacian (I := I) (LeviCivita (I := I) g) g rho x ≤
                2 * n + n * q := by
            have hfrac : 2 * n / dist O x ≤ 2 * n := by
              rw [div_le_iff₀ hrpos]
              nlinarith
            have hdistEq : (riemannianEDist I O x).toReal = dist O x :=
              hrhoValue.symm.trans hrhoValue'
            change laplacian (I := I) (LeviCivita (I := I) g) g rho x ≤
              2 * n / (riemannianEDist I O x).toReal + n * q at hrhoLap
            rw [hdistEq] at hrhoLap
            exact hrhoLap.trans (add_le_add hfrac le_rfl)
          have htarget :
              deriv distanceExhaustionProfile (rho x) *
                    laplacian (I := I) (LeviCivita (I := I) g) g rho x +
                  deriv (deriv distanceExhaustionProfile) (rho x) ≤
                D * (2 * n + n * q) + D := by
            have hbase : 0 ≤ 2 * n + n * q := by positivity
            exact add_le_add
              ((mul_le_mul_of_nonneg_left hrhoLap' hderivNonneg).trans
                (mul_le_mul_of_nonneg_right hderivLe hbase))
              hsecondLe
          exact htarget.trans
            (le_trans (le_max_right _ _) (le_max_right _ _))
      refine ⟨hbar, hbarSmooth, ?_, hbarUpper, hgradBound, hlapBound⟩
      simp only [hbar, h, hrhoValue']

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_proper_distance_exhaustion_with_hessian_bound
    [NeZero (Module.finrank Real E)] [T2Space (TangentBundle I M)]
    [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M)
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsec : ∀ y : M, metricRm04At (I := I) g y ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    (O : M) :
    ∃ h : M → Real, Continuous h ∧ IsProperMap h ∧
      (∀ x, 1 ≤ h x) ∧
      ∃ C : Real, 1 ≤ C ∧ ∀ x : M, ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
        ∃ hbar : M → Real, ContMDiffOn I 𝓘(Real, Real) ∞ hbar U ∧
        hbar x = h x ∧
        (∀ᶠ y in nhds x, h y ≤ hbar y) ∧
        g.inner x
            (gradientFun (I := I) g hbar x)
            (gradientFun (I := I) g hbar x) ≤ C ∧
        ∀ v : TangentSpace I x,
          hessFun (I := I) g hbar x v v ≤ C * g.inner x v v := by
  let _ : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := (∞ : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  let _ : TopologicalSpace.MetrizableSpace M :=
    Manifold.metrizableSpace I M
  let _ : T3Space M := inferInstance
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let _ : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let _ : PseudoEMetricSpace M := inferInstance
  let _ : CompleteSpace M := hcomplete.complete
  let _ : MetricSpace M :=
    Geometry.Riemannian.HopfRinow.riemMetricSpace (I := I) (M := M)
  let _ : ProperSpace M :=
    Geometry.Riemannian.HopfRinow.properSpace_riemMetric
        (I := I) (M := M) hcomplete.complete g
        (fun x v ↦ Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
          (I := I) g x v)
  obtain ⟨D, hD, hDfirst, hDsecond⟩ :=
    exists_distanceExhaustionProfile_deriv_bounds
  let C : Real := max 1 (max (D ^ 2) (3 * D))
  let h : M → Real := fun x ↦ 1 + distanceExhaustionProfile (dist O x)
  have hcont : Continuous h :=
    continuous_const.add
      (distanceExhaustionProfile_contDiff.continuous.comp
        (continuous_const.dist continuous_id))
  refine ⟨h, hcont, isProperMap_one_add_distanceExhaustionProfile O, ?_, C,
    le_max_left _ _, ?_⟩
  · intro x
    exact le_add_of_nonneg_right
      (distanceExhaustionProfile_nonneg dist_nonneg)
  · intro x
    by_cases hx : x = O
    · subst x
      refine ⟨Set.univ, isOpen_univ, Set.mem_univ O, fun _ ↦ 1,
        contMDiffOn_const, ?_, ?_, ?_, ?_⟩
      · simp [h, distanceExhaustionProfile_eq_zero]
      · filter_upwards [Metric.ball_mem_nhds O (by norm_num : (0 : Real) < 1)] with y hy
        have hdist : dist O y ≤ 1 := by
          rw [dist_comm]
          exact (Metric.mem_ball.mp hy).le
        simp [h, distanceExhaustionProfile_eq_zero hdist]
      · rw [gradientFun_const]
        simp only [map_zero]
        exact le_trans (by norm_num) (le_max_left _ _)
      · intro v
        rw [hessFun_const]
        exact mul_nonneg (le_trans (by norm_num) (le_max_left _ _))
          (Geometry.Riemannian.Exponential.gInner_self_nonneg (I := I) g O v)
    · have hfin :
          riemannianEDistOf (I := I) g O x ≠ (⊤ : ENNReal) := by
        simpa [riemannianEDistOf] using
          (Geometry.Riemannian.Exponential.riemannianEDist_ne_top
            (I := I) O x)
      have hEnorm : Geometry.Riemannian.IsMetricNorm (I := I) (M := M) g := by
        intro y v
        exact Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
          (I := I) g y v
      have hfin' : riemannianEDist I O x ≠ (⊤ : ENNReal) := by
        simpa [riemannianEDistOf] using hfin
      obtain ⟨rho, U, hU, hxU, hrhoSmooth, hrhoValue, hrhoUpper,
          hrhoNorm, hrhoHess⟩ :=
        calabiDist_hess_support_on (I := I) (M := M)
          g hEnorm hsec (Ne.symm hx) hfin'
      let hbar : M → Real := fun y ↦
        1 + distanceExhaustionProfile (rho y)
      have hrhoAt : ContMDiffAt I 𝓘(Real, Real) ∞ rho x :=
        hrhoSmooth.contMDiffAt (hU.mem_nhds hxU)
      have hprofileDiff : Differentiable Real distanceExhaustionProfile :=
        distanceExhaustionProfile_contDiff.differentiable (by simp)
      have hrhoValue' : rho x = dist O x := by
        rw [Geometry.Riemannian.HopfRinow.riemMetric_dist_eq
          (I := I) (M := M)]
        exact hrhoValue
      have hprofileOn : ContMDiffOn I 𝓘(Real, Real) ∞
          (fun y ↦ distanceExhaustionProfile (rho y)) U :=
        distanceExhaustionProfile_contDiff.contMDiff.contMDiffOn.comp
          (t := Set.univ) hrhoSmooth (fun _ _ ↦ Set.mem_univ _)
      have hbarSmooth : ContMDiffOn I 𝓘(Real, Real) ∞ hbar U :=
        contMDiffOn_const.add hprofileOn
      have hbarUpper : ∀ᶠ y in nhds x, h y ≤ hbar y := by
        filter_upwards [hrhoUpper] with y hy
        change 1 + distanceExhaustionProfile (dist O y) ≤
          1 + distanceExhaustionProfile (rho y)
        have hprofile : distanceExhaustionProfile (dist O y) ≤
            distanceExhaustionProfile (rho y) := by
          apply distanceExhaustionProfile_monotone
          rw [Geometry.Riemannian.HopfRinow.riemMetric_dist_eq
            (I := I) (M := M)]
          exact hy
        linarith
      have hgradEq :
          gradientFun (I := I) g hbar x =
            deriv distanceExhaustionProfile (rho x) •
              gradientFun (I := I) g rho x := by
        have hcomp :
          gradientFun (I := I) g
                (fun y ↦ distanceExhaustionProfile (rho y)) x =
              deriv distanceExhaustionProfile (rho x) •
                gradientFun (I := I) g rho x :=
          gradientFun_comp (I := I) g
            (hprofileDiff (rho x)) (hrhoAt.mdifferentiableAt (by simp))
        have hadd :
            gradientFun (I := I) g hbar x =
              gradientFun (I := I) g (fun _ : M ↦ (1 : Real)) x +
                gradientFun (I := I) g
                  (fun y ↦ distanceExhaustionProfile (rho y)) x := by
          apply gradientFun_add (I := I) g
          · exact mdifferentiableAt_const
          · exact (hprofileDiff (rho x)).mdifferentiableAt.comp x
              (hrhoAt.mdifferentiableAt (by simp))
        rw [hadd, gradientFun_const, zero_add, hcomp]
      have hgradBound :
          g.inner x
              (gradientFun (I := I) g hbar x)
              (gradientFun (I := I) g hbar x) ≤ C := by
        rw [hgradEq, Geometry.Riemannian.Exponential.gInner_smul_self
          (I := I) g x, hrhoNorm]
        simp only [mul_one]
        have habs := hDfirst (rho x)
        have hsq : deriv distanceExhaustionProfile (rho x) ^ 2 ≤ D ^ 2 := by
          apply sq_le_sq.mpr
          simpa [abs_of_nonneg (le_trans (by norm_num) hD)] using habs
        exact hsq.trans (le_trans (le_max_left _ _) (le_max_right _ _))
      refine ⟨U, hU, hxU, hbar, hbarSmooth, ?_, hbarUpper, hgradBound, ?_⟩
      · simp only [hbar, h, hrhoValue']
      · intro v
        have hcomp := hessFun_comp_of_contMDiffOn (I := I) g
          distanceExhaustionProfile_contDiff hU hrhoSmooth hxU v v
        have hadd := hessFun_add_const (I := I) g 1 hU hprofileOn hxU
        change hessFun (I := I) g hbar x v v ≤ C * g.inner x v v
        rw [show hessFun (I := I) g hbar x =
          hessFun (I := I) g
            (fun y ↦ distanceExhaustionProfile (rho y)) x from hadd]
        rw [hcomp]
        by_cases hr : dist O x < 1
        · rw [hrhoValue', distanceExhaustionProfile_deriv_eq_zero hr,
            distanceExhaustionProfile_second_deriv_eq_zero_of_lt_one hr]
          simp only [zero_mul, zero_add]
          exact mul_nonneg (le_trans (by norm_num) (le_max_left _ _))
            (Geometry.Riemannian.Exponential.gInner_self_nonneg (I := I) g x v)
        · have hrone : 1 ≤ dist O x := le_of_not_gt hr
          have hrpos : 0 < dist O x := lt_of_lt_of_le (by norm_num) hrone
          have hDnonneg : 0 ≤ D := le_trans (by norm_num) hD
          have hderivNonneg :
              0 ≤ deriv distanceExhaustionProfile (rho x) :=
            distanceExhaustionProfile_monotone.deriv_nonneg
          have hderivLe : deriv distanceExhaustionProfile (rho x) ≤ D :=
            (le_abs_self _).trans (hDfirst (rho x))
          have hsecondLe :
              deriv (deriv distanceExhaustionProfile) (rho x) ≤ D :=
            (le_abs_self _).trans (hDsecond (rho x))
          have hqnonneg : 0 ≤ g.inner x v v :=
            Geometry.Riemannian.Exponential.gInner_self_nonneg (I := I) g x v
          have hfrac : 2 * g.inner x v v / dist O x ≤
              2 * g.inner x v v := by
            rw [div_le_iff₀ hrpos]
            nlinarith
          have hdistEq : (riemannianEDist I O x).toReal = dist O x :=
            hrhoValue.symm.trans hrhoValue'
          have hhess : hessFun (I := I) g rho x v v ≤
              2 * g.inner x v v := by
            have hraw := hrhoHess v
            rw [hdistEq] at hraw
            exact hraw.trans hfrac
          have hinnerSq :
              (g.inner x (gradientFun (I := I) g rho x) v) ^ 2 ≤
                g.inner x v v := by
            have hcs := gInner_sq_le_mul (I := I) g x
              (gradientFun (I := I) g rho x) v
            rw [hrhoNorm, one_mul] at hcs
            exact hcs
          have hfirstTerm :
              deriv distanceExhaustionProfile (rho x) *
                  hessFun (I := I) g rho x v v ≤
                D * (2 * g.inner x v v) := by
            calc
              _ ≤ deriv distanceExhaustionProfile (rho x) *
                    (2 * g.inner x v v) :=
                mul_le_mul_of_nonneg_left hhess hderivNonneg
              _ ≤ D * (2 * g.inner x v v) :=
                mul_le_mul_of_nonneg_right hderivLe (by positivity)
          have hsecondTerm :
              deriv (deriv distanceExhaustionProfile) (rho x) *
                  (g.inner x (gradientFun (I := I) g rho x) v) ^ 2 ≤
                D * g.inner x v v := by
            calc
              _ ≤ D *
                    (g.inner x (gradientFun (I := I) g rho x) v) ^ 2 :=
                mul_le_mul_of_nonneg_right hsecondLe (sq_nonneg _)
              _ ≤ D * g.inner x v v :=
                mul_le_mul_of_nonneg_left hinnerSq hDnonneg
          have hsum :
              deriv distanceExhaustionProfile (rho x) *
                    hessFun (I := I) g rho x v v +
                  deriv (deriv distanceExhaustionProfile) (rho x) *
                    g.inner x (gradientFun (I := I) g rho x) v *
                    g.inner x (gradientFun (I := I) g rho x) v ≤
                3 * D * g.inner x v v := by
            nlinarith
          exact hsum.trans
            (mul_le_mul_of_nonneg_right
              (le_trans (le_max_right _ _) (le_max_right _ _)) hqnonneg)

end DifferentialGeometry

end

noncomputable section

namespace DifferentialGeometry

open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [T2Space M]


omit [I.Boundaryless] [T2Space M] in
theorem exists_constant_proper_exhaustion_with_gradient_laplacian_bound
    [CompactSpace M]
    (G : ℝ → SmoothRiemannianMetric I M) :
    ∃ h : M → ℝ, h = (fun _ => 1) ∧ Continuous h ∧ IsProperMap h ∧
      (∀ x, 1 ≤ h x) ∧
      ∀ t : ℝ, ∀ x : M,
        ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ ∃ hbar : M → ℝ,
          ContMDiffOn I 𝓘(ℝ, ℝ) ∞ hbar U ∧
          hbar x = h x ∧
          (∀ᶠ y in nhds x, h y ≤ hbar y) ∧
          Real.sqrt ((G t).inner x
            (gradientFun (I := I) (G t) hbar x)
            (gradientFun (I := I) (G t) hbar x)) ≤ 1 * h x ∧
          laplacian (I := I) (LeviCivita (I := I) (G t)) (G t) hbar x ≤ 1 * h x := by
  refine ⟨fun _ => 1, rfl, continuous_const, isProperMap_const 1,
    fun _ => le_rfl, ?_⟩
  intro t x
  refine ⟨Set.univ, isOpen_univ, Set.mem_univ x, fun _ => 1,
    contMDiffOn_const, rfl, Filter.Eventually.of_forall (fun _ => le_rfl), ?_, ?_⟩
  · rw [gradientFun_const]
    simp
  · rw [laplacian_const]
    norm_num

end DifferentialGeometry

end
