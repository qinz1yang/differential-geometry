import DifferentialGeometry.Geometry.Metric.Conformal.ConnectionOfContDiff
import DifferentialGeometry.Geometry.Operator.HessianComposition
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option autoImplicit false
noncomputable section

open Bundle Manifold Set Filter MeasureTheory
open DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Metric.BarrierProfile

/-- The cutoff is one on a neighborhood of the closed interior region and
has a flat zero at the outer edge. -/
def cutoff (a r : ℝ) : ℝ := 1 - Real.smoothTransition (2 * r / a - 1)

def logWeight (a r : ℝ) : ℝ := -Real.log (cutoff a r)

def barrier (a r : ℝ) : ℝ := ∫ s in (0 : ℝ)..r, (cutoff a s)⁻¹ ^ 2

theorem cutoff_smooth (a : ℝ) : ContDiff ℝ ∞ (cutoff a) := by
  unfold cutoff
  fun_prop

theorem cutoff_eq_one {a : ℝ} (ha : 0 < a) {r : ℝ} (hr : r ≤ a / 2) :
    cutoff a r = 1 := by
  unfold cutoff
  rw [Real.smoothTransition.zero_of_nonpos]
  · ring
  · have hh : 2 * r / a ≤ 1 := (div_le_iff₀ ha).2 (by linarith)
    linarith

theorem cutoff_pos_iff {a : ℝ} (ha : 0 < a) (r : ℝ) :
    0 < cutoff a r ↔ r < a := by
  constructor
  · intro h
    by_contra hn
    have hh : 1 ≤ 2 * r / a - 1 := by
      have hh : 2 ≤ 2 * r / a := (le_div_iff₀ ha).2 (by linarith)
      linarith
    simp only [cutoff, Real.smoothTransition.one_of_one_le hh, sub_self] at h
    exact lt_irrefl _ h
  · intro hr
    have hh : 2 * r / a - 1 < 1 := by
      have hh : 2 * r / a < 2 := (div_lt_iff₀ ha).2 (by linarith)
      linarith
    exact sub_pos.mpr (Real.smoothTransition.lt_one_of_lt_one hh)

theorem cutoff_antitone {a : ℝ} (ha : 0 < a) : Antitone (cutoff a) := by
  intro r s hrs
  have hh : 2 * r / a - 1 ≤ 2 * s / a - 1 := by
    gcongr
  exact sub_le_sub_left (Real.smoothTransition.monotone hh) 1

theorem logWeight_smoothOn {a : ℝ} (ha : 0 < a) :
    ContDiffOn ℝ ∞ (logWeight a) (Iio a) :=
  ((cutoff_smooth a).contDiffOn.log (fun r hr => ((cutoff_pos_iff ha r).2 hr).ne')).neg

private theorem inverse_square_smoothOn {a : ℝ} (ha : 0 < a) :
    ContDiffOn ℝ ∞ (fun r => (cutoff a r)⁻¹ ^ 2) (Iio a) :=
  ((cutoff_smooth a).contDiffOn.inv (fun r hr => ((cutoff_pos_iff ha r).2 hr).ne')).pow 2

private theorem interval_subset {a r : ℝ} (ha : 0 < a) (hr : r < a) :
    uIcc (0 : ℝ) r ⊆ Iio a := by
  intro s hs
  rcases mem_uIcc.mp hs with hs | hs
  · exact hs.2.trans_lt hr
  · exact hs.2.trans_lt ha

theorem barrier_hasDerivAt {a : ℝ} (ha : 0 < a) {r : ℝ} (hr : r < a) :
    HasDerivAt (barrier a) ((cutoff a r)⁻¹ ^ 2) r := by
  have hc := (inverse_square_smoothOn ha).continuousOn
  exact intervalIntegral.integral_hasDerivAt_right
    (hc.mono (interval_subset ha hr)).intervalIntegrable
    (hc.stronglyMeasurableAtFilter isOpen_Iio r hr)
    ((hc r hr).continuousAt (isOpen_Iio.mem_nhds hr))

theorem deriv_barrier {a : ℝ} (ha : 0 < a) {r : ℝ} (hr : r < a) :
    deriv (barrier a) r = (cutoff a r)⁻¹ ^ 2 :=
  (barrier_hasDerivAt ha hr).deriv

theorem barrier_smoothOn {a : ℝ} (ha : 0 < a) :
    ContDiffOn ℝ ∞ (barrier a) (Iio a) := by
  rw [contDiffOn_infty_iff_deriv_of_isOpen isOpen_Iio]
  refine ⟨fun r hr => (barrier_hasDerivAt ha hr).differentiableAt.differentiableWithinAt, ?_⟩
  exact (inverse_square_smoothOn ha).congr (fun r hr => deriv_barrier ha hr)

theorem deriv_barrier_pos {a : ℝ} (ha : 0 < a) {r : ℝ} (hr : r < a) :
    0 < deriv (barrier a) r := by
  rw [deriv_barrier ha hr]
  exact sq_pos_of_pos (inv_pos.mpr ((cutoff_pos_iff ha r).2 hr))

private theorem logWeight_hasDerivAt {a : ℝ} (ha : 0 < a) {r : ℝ} (hr : r < a) :
    HasDerivAt (logWeight a) (-deriv (cutoff a) r / cutoff a r) r := by
  have hh := (((cutoff_smooth a).differentiable (by simp) r).hasDerivAt.log
    ((cutoff_pos_iff ha r).2 hr).ne').neg
  exact hh.congr_deriv (neg_div (cutoff a r) (deriv (cutoff a) r)).symm

theorem deriv_logWeight_nonneg {a : ℝ} (ha : 0 < a) {r : ℝ} (hr : r < a) :
    0 ≤ deriv (logWeight a) r := by
  rw [(logWeight_hasDerivAt ha hr).deriv]
  exact div_nonneg (neg_nonneg.mpr (cutoff_antitone ha).deriv_nonpos)
    ((cutoff_pos_iff ha r).2 hr).le

theorem second_deriv_barrier {a : ℝ} (ha : 0 < a) {r : ℝ} (hr : r < a) :
    deriv (deriv (barrier a)) r =
      2 * deriv (logWeight a) r * deriv (barrier a) r := by
  have heq : deriv (barrier a) =ᶠ[𝓝 r] (fun s => (cutoff a s)⁻¹ ^ 2) := by
    filter_upwards [isOpen_Iio.mem_nhds hr] with s hs
    exact deriv_barrier ha hs
  have hn : cutoff a r ≠ 0 := ((cutoff_pos_iff ha r).2 hr).ne'
  have hd := ((((cutoff_smooth a).differentiable (by simp) r).hasDerivAt.inv hn).pow 2).deriv
  change deriv (fun s : ℝ => (cutoff a s)⁻¹ ^ 2) r =
    (2 : ℝ) * (cutoff a r)⁻¹ ^ (2 - 1) *
      (-deriv (cutoff a) r / cutoff a r ^ 2) at hd
  rw [heq.deriv_eq, hd, (logWeight_hasDerivAt ha hr).deriv, deriv_barrier ha hr]
  simp only [Nat.reduceSub, pow_one, div_eq_mul_inv, inv_pow]
  ring

theorem barrier_eq_self {a : ℝ} (ha : 0 < a) {r : ℝ} (hr : r ≤ a / 2) :
    barrier a r = r := by
  unfold barrier
  calc
    (∫ s in (0 : ℝ)..r, (cutoff a s)⁻¹ ^ 2) = ∫ _s in (0 : ℝ)..r, (1 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro s hs
      have hs' : s ≤ a / 2 := by
        rcases mem_uIcc.mp hs with hs | hs
        · exact hs.2.trans hr
        · exact hs.2.trans (by positivity)
      change (cutoff a s)⁻¹ ^ 2 = 1
      rw [cutoff_eq_one ha hs', inv_one, one_pow]
    _ = r := by simp

theorem barrier_strictMonoOn {a : ℝ} (ha : 0 < a) :
    StrictMonoOn (barrier a) (Iio a) :=
  strictMonoOn_of_deriv_pos (convex_Iio a) (barrier_smoothOn ha).continuousOn
    (fun _r hr => deriv_barrier_pos ha (interior_subset (s := Iio a) hr))

theorem barrier_le_zero_iff {a : ℝ} (ha : 0 < a) {r : ℝ} (hr : r < a) :
    barrier a r ≤ 0 ↔ r ≤ 0 := by
  have hz : barrier a 0 = 0 := barrier_eq_self ha (by positivity)
  simpa only [hz] using (barrier_strictMonoOn ha).le_iff_le hr ha

section Geometry
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

/-- Local scalar smoothness on an actual open domain suffices for the
canonical Hessian chain rule. -/
theorem hessFun_comp_of_contDiffOn
    (g : SmoothRiemannianMetric I M) {f : ℝ → ℝ} {s : Set ℝ}
    (hs : IsOpen s) (hf : ContDiffOn ℝ ∞ f s)
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ) ∞ u)
    (x : M) (hx : u x ∈ s) (v w : TangentSpace I x) :
    hessFun g (fun y => f (u y)) x v w =
      deriv (deriv f) (u x) * mvfderiv I u x v * mvfderiv I u x w +
        deriv f (u x) * hessFun g u x v w := by
  obtain ⟨F, hF, heq⟩ := DifferentialGeometry.exists_smooth_germ (I := 𝓘(ℝ))
    hs hx (contMDiffOn_iff_contDiffOn.mpr hf)
  have hF' : ContDiff ℝ ∞ F := contMDiff_iff_contDiff.mp hF
  have hc := heq.comp_tendsto (show Tendsto u (𝓝 x) (𝓝 (u x)) from hu.continuous.continuousAt.tendsto)
  change (fun y => F (u y)) =ᶠ[𝓝 x] (fun y => f (u y)) at hc
  rw [← hessFun_congr g hc, hessFun_comp g hF' hu,
    heq.deriv_eq, heq.deriv.deriv_eq]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] in
private theorem contMDiff_comp_of_contDiffOn
    {f : ℝ → ℝ} {s : Set ℝ} (hs : IsOpen s) (hf : ContDiffOn ℝ ∞ f s)
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ) ∞ u) (hmem : ∀ x, u x ∈ s) :
    ContMDiff I 𝓘(ℝ) ∞ (fun x => f (u x)) := by
  intro x
  exact ((hf (u x) (hmem x)).contDiffAt (hs.mem_nhds (hmem x))).comp_contMDiffAt
    hu.contMDiffAt

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] in
private theorem differential_scalar_comp {f : ℝ → ℝ} {u : M → ℝ}
    (x : M) (hf : DifferentiableAt ℝ f (u x))
    (hu : MDifferentiableAt I 𝓘(ℝ) u x) (v : TangentSpace I x) :
    mvfderiv I (fun y => f (u y)) x v = deriv f (u x) * mvfderiv I u x v := by
  have hh := mvfderiv_comp_apply (I := 𝓘(ℝ)) (I' := I)
    (f := u) (g := f) x hf.mdifferentiableAt hu v
  rw [mvfderiv_real_model_eq_fderiv, hf.hasDerivAt.hasFDerivAt.fderiv,
    ← mvfderiv_real_eq_mfderiv I u x v] at hh
  simpa only [Function.comp_def, ContinuousLinearMap.toSpanSingleton_apply,
    smul_eq_mul, mul_comm] using hh

private theorem conformal_hessian_diagonal
    (g : SmoothRiemannianMetric I M) {F f : M → ℝ}
    (hF : ContMDiff I 𝓘(ℝ) ∞ F) (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (x : M) (v : TangentSpace I x) :
    hessFun (conformalMetricOfContDiff g F hF) f x v v =
      hessFun g f x v v - 2 * mvfderiv I F x v * mvfderiv I f x v +
        g.inner x v v * mvfderiv I f x (gradFun g F x) := by
  have hh := hessFun_sub_eq_neg_mvfderiv_connectionDifference
    (conformalMetricOfContDiff g F hF) g isOpen_univ hf.contMDiffOn
    (mem_univ x) v v
  change hessFun (conformalMetricOfContDiff g F hF) f x v v -
      hessFun g f x v v =
    -mvfderiv I f x
      (PDE.DeTurck.connectionDifference (conformalMetricOfContDiff g F hF) g x v v) at hh
  rw [connectionDifference_conformalMetricOfContDiff] at hh
  simp only [map_sub, map_add, map_smul, smul_eq_mul] at hh
  linarith


/-- The conformal metric of the actual profile, defined on a carrier whose
original defining function takes values below the outer edge. -/
def profileMetric (g : SmoothRiemannianMetric I M) (a : ℝ) (ha : 0 < a)
    (ρ : M → ℝ) (hρ : ContMDiff I 𝓘(ℝ) ∞ ρ) (hρa : ∀ x, ρ x < a) :
    SmoothRiemannianMetric I M :=
  conformalMetricOfContDiff g (fun x => logWeight a (ρ x))
    (contMDiff_comp_of_contDiffOn isOpen_Iio (logWeight_smoothOn ha) hρ hρa)

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] in
theorem profileMetric_inner
    (g : SmoothRiemannianMetric I M) (a : ℝ) (ha : 0 < a)
    (ρ : M → ℝ) (hρ : ContMDiff I 𝓘(ℝ) ∞ ρ) (hρa : ∀ x, ρ x < a)
    (x : M) (v w : TangentSpace I x) :
    (profileMetric g a ha ρ hρ hρa).inner x v w =
      (cutoff a (ρ x))⁻¹ ^ 2 * g.inner x v w := by
  change Real.exp (2 * -Real.log (cutoff a (ρ x))) * g.inner x v w = _
  simp only [two_mul, Real.exp_add, Real.exp_neg,
    Real.exp_log ((cutoff_pos_iff ha (ρ x)).2 (hρa x)), pow_two]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] in
theorem barrier_comp_smooth
    (a : ℝ) (ha : 0 < a) (ρ : M → ℝ)
    (hρ : ContMDiff I 𝓘(ℝ) ∞ ρ) (hρa : ∀ x, ρ x < a) :
    ContMDiff I 𝓘(ℝ) ∞ (fun x => barrier a (ρ x)) :=
  contMDiff_comp_of_contDiffOn isOpen_Iio (barrier_smoothOn ha) hρ hρa

/-- The actual profile cancels the radial Hessian error of the conformal
change. No Hessian identity or inequality is assumed. -/
theorem hess_profileMetric_barrier
    (g : SmoothRiemannianMetric I M) (a : ℝ) (ha : 0 < a)
    (ρ : M → ℝ) (hρ : ContMDiff I 𝓘(ℝ) ∞ ρ) (hρa : ∀ x, ρ x < a)
    (x : M) (v : TangentSpace I x) :
    hessFun (profileMetric g a ha ρ hρ hρa) (fun y => barrier a (ρ y)) x v v =
      (cutoff a (ρ x))⁻¹ ^ 2 *
        (hessFun g ρ x v v + deriv (logWeight a) (ρ x) *
          g.inner x (gradFun g ρ x) (gradFun g ρ x) * g.inner x v v) := by
  have hF : ContMDiff I 𝓘(ℝ) ∞ (fun y => logWeight a (ρ y)) :=
    contMDiff_comp_of_contDiffOn isOpen_Iio (logWeight_smoothOn ha) hρ hρa
  have hb := barrier_comp_smooth a ha ρ hρ hρa
  have hFd : DifferentiableAt ℝ (logWeight a) (ρ x) :=
    (logWeight_hasDerivAt ha (hρa x)).differentiableAt
  have hbd : DifferentiableAt ℝ (barrier a) (ρ x) :=
    (barrier_hasDerivAt ha (hρa x)).differentiableAt
  have hρd := hρ.mdifferentiable (by simp) x
  change hessFun (conformalMetricOfContDiff g (fun y => logWeight a (ρ y)) hF)
    (fun y => barrier a (ρ y)) x v v = _
  rw [conformal_hessian_diagonal g hF hb,
    hessFun_comp_of_contDiffOn g isOpen_Iio (barrier_smoothOn ha) hρ x (hρa x),
    differential_scalar_comp x hFd hρd, differential_scalar_comp x hbd hρd]
  have hgrad : gradFun g (fun y => logWeight a (ρ y)) x =
      deriv (logWeight a) (ρ x) • gradFun g ρ x :=
    gradientFun_comp g hFd hρd
  rw [hgrad, map_smul, smul_eq_mul, differential_scalar_comp x hbd hρd]
  have hnorm : mvfderiv I ρ x (gradFun g ρ x) =
      g.inner x (gradFun g ρ x) (gradFun g ρ x) := (inner_gradFun g ρ x _).symm
  rw [hnorm, second_deriv_barrier ha (hρa x), deriv_barrier ha (hρa x)]
  ring

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] in
/-- Both the original metric and the original defining function are preserved
as germs on the actual open region below the start of the transition. -/
theorem profile_preserved_germs
    (g : SmoothRiemannianMetric I M) (a : ℝ) (ha : 0 < a)
    (ρ : M → ℝ) (hρ : ContMDiff I 𝓘(ℝ) ∞ ρ) (hρa : ∀ x, ρ x < a)
    (x : M) (hx : ρ x < a / 2) :
    ∀ᶠ y in 𝓝 x,
      (profileMetric g a ha ρ hρ hρa).inner y = g.inner y ∧
        barrier a (ρ y) = ρ y := by
  filter_upwards [(isOpen_lt hρ.continuous continuous_const).mem_nhds hx] with y hy
  refine ⟨?_, barrier_eq_self ha hy.le⟩
  ext v w
  rw [profileMetric_inner, cutoff_eq_one ha hy.le, inv_one, one_pow, one_mul]

end Geometry
end DifferentialGeometry.Geometry.Metric.BarrierProfile
