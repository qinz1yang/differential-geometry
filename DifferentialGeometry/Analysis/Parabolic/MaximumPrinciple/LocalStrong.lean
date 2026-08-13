import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.Weak
import DifferentialGeometry.Geometry.Curvature.Riemann.Basic.Field
import DifferentialGeometry.Geometry.Operator.LaplacianBridge
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Geometry.Manifold.BumpFunction

set_option autoImplicit false

namespace DifferentialGeometry.Analysis.Parabolic

noncomputable section

open Bundle Filter Set
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private abbrev EuclN := EuclideanSpace Real (Fin (Module.finrank Real E))

private def coordRadiusSq (c x : M) : Real :=
  ‖(toEuclidean (E := E)) (extChartAt I c x - extChartAt I c c)‖ ^ 2

private theorem coordRadiusSq_contMDiffOn (c : M) :
    ContMDiffOn I 𝓘(Real, Real) ∞ (coordRadiusSq (I := I) c)
      (chartAt H c).source := by
  unfold coordRadiusSq
  intro x hx
  have hq : ContDiff Real ∞
      (fun z : E => ‖(toEuclidean (E := E)) (z - extChartAt I c c)‖ ^ 2) := by
    exact ((toEuclidean (E := E)).contDiff.comp
      (contDiff_id.sub contDiff_const)).norm_sq Real
  simpa only [Function.comp_apply] using
    (hq.contMDiff.contMDiffAt.comp x
      (((contMDiffOn_extChartAt (I := I) (x := c)) x hx).contMDiffAt
        ((chartAt H c).open_source.mem_nhds hx))).contMDiffWithinAt

private def compactCoordRadiusSq [T2Space M]
    {c : M} (b : SmoothBumpFunction I c) (x : M) : Real :=
  b x * coordRadiusSq (I := I) c x

private theorem compactCoordRadiusSq_contMDiff [T2Space M]
    {c : M} (b : SmoothBumpFunction I c) :
    ContMDiff I 𝓘(Real, Real) ∞ (compactCoordRadiusSq (I := I) b) := by
  unfold compactCoordRadiusSq
  simpa only [smul_eq_mul] using
    b.contMDiff_smul (coordRadiusSq_contMDiffOn (I := I) c)

omit [IsManifold I ∞ M] in
private theorem compactCoordRadiusSq_eventuallyEq [T2Space M]
    {c x : M} (b : SmoothBumpFunction I c)
    (hx : x ∈ (chartAt H c).source)
    (hd : dist (extChartAt I c x) (extChartAt I c c) < b.rIn) :
    EventuallyEq (nhds x) (compactCoordRadiusSq (I := I) b)
      (coordRadiusSq (I := I) c) := by
  filter_upwards [b.eventuallyEq_one_of_dist_lt hx hd] with y hy
  simp [compactCoordRadiusSq, hy]

private theorem fderiv_coordNormSq_apply_self (z z0 : E) :
    fderiv Real
        (fun w : E => ‖(toEuclidean (E := E)) (w - z0)‖ ^ 2) z (z - z0) =
      2 * ‖(toEuclidean (E := E)) (z - z0)‖ ^ 2 := by
  have h := (((toEuclidean (E := E)).hasFDerivAt.comp z
    ((hasFDerivAt_id z).sub_const z0))).norm_sq
  change fderiv Real
      (fun x => ‖((toEuclidean (E := E) : E → EuclN) ∘
        fun y => id y - z0) x‖ ^ 2) z (z - z0) = _
  rw [h.fderiv]
  simp only [id_eq, Function.comp_apply, map_sub, ContinuousLinearMap.comp_id,
    ContinuousLinearMap.sub_comp, ContinuousLinearMap.coe_smul',
    ContinuousLinearMap.coe_sub', ContinuousLinearMap.coe_comp', coe_innerSL_apply,
    ContinuousLinearEquiv.coe_coe, Pi.smul_apply, Pi.sub_apply, nsmul_eq_mul,
    Nat.cast_ofNat]
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
    real_inner_comm ((toEuclidean (E := E)) z0) ((toEuclidean (E := E)) z)]
  rw [norm_sub_sq_real]
  ring_nf
  rw [real_inner_comm]
  ring

private theorem coordRadiusSq_mfderiv_ne_zero
    {c x : M} (hx : x ∈ (chartAt H c).source) (hxc : x ≠ c) :
    mfderiv I 𝓘(Real, Real) (coordRadiusSq (I := I) c) x ≠ 0 := by
  let z : E := extChartAt I c x
  let z0 : E := extChartAt I c c
  let q : E → Real := fun w => ‖(toEuclidean (E := E)) (w - z0)‖ ^ 2
  have hcomp :
      mfderiv I 𝓘(Real, Real) (coordRadiusSq (I := I) c) x =
        (fderiv Real q z).comp (mfderiv I 𝓘(Real, E) (extChartAt I c) x) := by
    have hq : MDifferentiableAt 𝓘(Real, E) 𝓘(Real, Real) q z := by
      have hqcd : ContMDiff 𝓘(Real, E) 𝓘(Real, Real) ∞ q :=
        (((toEuclidean (E := E)).contDiff.comp
          (contDiff_id.sub contDiff_const)).norm_sq Real).contMDiff
      exact hqcd.mdifferentiable (by simp) z
    have hchart : MDifferentiableAt I 𝓘(Real, E) (extChartAt I c) x :=
      mdifferentiableAt_extChartAt (I := I) hx
    simpa only [coordRadiusSq, q, z, mfderiv_eq_fderiv, Function.comp_apply] using
      mfderiv_comp x hq hchart
  intro hzero
  have hqzero : fderiv Real q z = 0 := by
    have hinv := isInvertible_mfderiv_extChartAt (I := I)
      (show x ∈ (extChartAt I c).source by simpa [extChartAt_source] using hx)
    apply ContinuousLinearMap.ext
    intro v
    obtain ⟨w, hw⟩ := hinv.surjective v
    have happ := congrArg (fun L : TangentSpace I x →L[Real] Real => L w) hzero
    rw [hcomp] at happ
    simp only [ContinuousLinearMap.comp_apply] at happ
    calc
      fderiv Real q z v = fderiv Real q z
          ((mfderiv I 𝓘(Real, E) (extChartAt I c) x) w) := by rw [hw]
      _ = 0 := by simpa using happ
  have hz_ne : z ≠ z0 := by
    intro hz
    apply hxc
    have hs := congrArg (extChartAt I c).symm hz
    rw [(extChartAt I c).left_inv
      (show x ∈ (extChartAt I c).source by simpa [extChartAt_source] using hx),
      (extChartAt I c).left_inv (mem_extChartAt_source c)] at hs
    exact hs
  have hL_ne : (toEuclidean (E := E)) (z - z0) ≠ 0 := by
    intro hL
    have hsub := (toEuclidean (E := E)).injective
      (show (toEuclidean (E := E)) (z - z0) =
        (toEuclidean (E := E)) 0 by simpa using hL)
    exact (sub_ne_zero.mpr hz_ne) hsub
  have happ := fderiv_coordNormSq_apply_self (E := E) z z0
  rw [hqzero] at happ
  simp only [ContinuousLinearMap.zero_apply] at happ
  have hpos : 0 < 2 * ‖(toEuclidean (E := E)) (z - z0)‖ ^ 2 := by
    positivity
  linarith

private theorem compactCoordRadiusSq_gradient_ne_zero [T2Space M]
    (g : SmoothRiemannianMetric I M) {c x : M}
    (b : SmoothBumpFunction I c)
    (hx : x ∈ (chartAt H c).source)
    (hd : dist (extChartAt I c x) (extChartAt I c c) < b.rIn)
    (hxc : x ≠ c) :
    gradientFun (I := I) g (compactCoordRadiusSq (I := I) b) x ≠ 0 := by
  have hev := compactCoordRadiusSq_eventuallyEq (I := I) b hx hd
  have hcompact :
      mfderiv I 𝓘(Real, Real) (compactCoordRadiusSq (I := I) b) x ≠ 0 := by
    rw [hev.mfderiv_eq]
    exact coordRadiusSq_mfderiv_ne_zero (I := I) hx hxc
  intro hgrad
  apply hcompact
  apply ContinuousLinearMap.ext
  intro v
  have hinner := inner_gradientFun (I := I) g
    (compactCoordRadiusSq (I := I) b) x v
  rw [hgrad] at hinner
  simpa using hinner.symm

private theorem gradientNormSq_continuous [T2Space M]
    (g : SmoothRiemannianMetric I M) {f : M → Real}
    (hf : ContMDiff I 𝓘(Real, Real) ∞ f) :
    Continuous (fun x => g.inner x
      (gradientFun (I := I) g f x) (gradientFun (I := I) g f x)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  have hgrad : ContMDiffAt I (I.prod 𝓘(Real, E)) ∞
      (T% fun y : M => gradientFun (I := I) g f y) x :=
    (gradientFun_smooth (I := I) g hf).contMDiffAt
  exact (CovariantDerivative.metric_inner_contMDiffAt
    (I := I) g hgrad hgrad le_rfl).continuousAt

private def chartClosedAnnulus (c : M) (r R : Real) : Set M :=
  (extChartAt I c).symm ''
    ((Metric.closedBall (extChartAt I c c) R \
      Metric.ball (extChartAt I c c) r) ∩ Set.range I)

omit [IsManifold I ∞ M] in
private theorem chartClosedAnnulus_isCompact [T2Space M]
    {c : M} (b : SmoothBumpFunction I c) {r R : Real}
    (hR : R ≤ b.rOut) :
    IsCompact (chartClosedAnnulus (I := I) c r R) := by
  have hbase : IsCompact
      ((Metric.closedBall (extChartAt I c c) R \
        Metric.ball (extChartAt I c c) r) ∩ Set.range I) := by
    exact ((isCompact_closedBall _ _).diff Metric.isOpen_ball).inter_right I.isClosed_range
  apply hbase.image_of_continuousOn
  apply (continuousOn_extChartAt_symm (I := I) c).mono
  intro y hy
  apply b.closedBall_subset
  exact ⟨Metric.closedBall_subset_closedBall hR hy.1.1, hy.2⟩

omit [FiniteDimensional Real E] [IsManifold I ∞ M] in
private theorem mem_chartClosedAnnulus_data
    {c x : M} (b : SmoothBumpFunction I c) {r R : Real}
    (hR : R ≤ b.rOut)
    (hx : x ∈ chartClosedAnnulus (I := I) c r R) :
    x ∈ (chartAt H c).source ∧
      r ≤ dist (extChartAt I c x) (extChartAt I c c) ∧
      dist (extChartAt I c x) (extChartAt I c c) ≤ R := by
  rcases hx with ⟨y, ⟨⟨hyR, hyr⟩, hyI⟩, rfl⟩
  have hytarget : y ∈ (extChartAt I c).target := by
    apply b.closedBall_subset
    exact ⟨Metric.closedBall_subset_closedBall hR hyR, hyI⟩
  have hsource : (extChartAt I c).symm y ∈ (extChartAt I c).source :=
    (extChartAt I c).map_target hytarget
  have hright : extChartAt I c ((extChartAt I c).symm y) = y :=
    (extChartAt I c).right_inv hytarget
  constructor
  · simpa [extChartAt_source] using hsource
  constructor
  · rw [hright]
    exact le_of_not_gt hyr
  · rw [hright]
    exact hyR

omit [FiniteDimensional Real E] [IsManifold I ∞ M] in
private theorem mem_chartClosedAnnulus_of_data
    {c x : M} {r R : Real}
    (hx : x ∈ (chartAt H c).source)
    (hr : r ≤ dist (extChartAt I c x) (extChartAt I c c))
    (hR : dist (extChartAt I c x) (extChartAt I c c) ≤ R) :
    x ∈ chartClosedAnnulus (I := I) c r R := by
  refine ⟨extChartAt I c x, ?_, ?_⟩
  · refine ⟨⟨hR, not_lt_of_ge hr⟩, ?_⟩
    simp [extChartAt]
  · exact (extChartAt I c).left_inv
      (show x ∈ (extChartAt I c).source by simpa [extChartAt_source] using hx)

private theorem exists_pos_le_gradientNormSq_on_chartClosedAnnulus
    [T2Space M]
    (g : SmoothRiemannianMetric I M) {c : M}
    (b : SmoothBumpFunction I c) {r R : Real}
    (hr : 0 < r) (hR : R < b.rIn)
    (hne : (chartClosedAnnulus (I := I) c r R).Nonempty) :
    ∃ m : Real, 0 < m ∧ ∀ x ∈ chartClosedAnnulus (I := I) c r R,
      m ≤ g.inner x
        (gradientFun (I := I) g (compactCoordRadiusSq (I := I) b) x)
        (gradientFun (I := I) g (compactCoordRadiusSq (I := I) b) x) := by
  let q : M → Real := fun x => g.inner x
    (gradientFun (I := I) g (compactCoordRadiusSq (I := I) b) x)
    (gradientFun (I := I) g (compactCoordRadiusSq (I := I) b) x)
  have hK := chartClosedAnnulus_isCompact (I := I) b (r := r) (R := R)
    (hR.le.trans b.rIn_lt_rOut.le)
  have hqcont : Continuous q := by
    exact gradientNormSq_continuous (I := I) g
      (compactCoordRadiusSq_contMDiff (I := I) b)
  obtain ⟨x0, hx0, hx0min⟩ := hK.exists_isMinOn hne hqcont.continuousOn
  have hxdata := mem_chartClosedAnnulus_data (I := I) b
    (hR.le.trans b.rIn_lt_rOut.le) hx0
  have hxc : x0 ≠ c := by
    intro hxc
    subst x0
    have hdist : dist (extChartAt I c c) (extChartAt I c c) = 0 := dist_self _
    linarith [hxdata.2.1]
  have hgrad :
      gradientFun (I := I) g (compactCoordRadiusSq (I := I) b) x0 ≠ 0 :=
    compactCoordRadiusSq_gradient_ne_zero (I := I) g b hxdata.1
      (hxdata.2.2.trans_lt hR) hxc
  refine ⟨q x0, ?_, ?_⟩
  · exact g.pos x0 _ hgrad
  · intro x hx
    exact hx0min hx

private def fixedMetricFamily
    (g : SmoothRiemannianMetric I M) :
    MetricConnectionFamily (I := I) (M := M) Real where
  metric := fun _ => g
  connection := fun _ => LeviCivita (I := I) g
  metricCompatible := by
    intro t
    simpa using
      (leviCivitaConnectionOfMetric_isMetricCompatible (I := I) g)

@[simp] private theorem fixedMetricFamily_metric
    (g : SmoothRiemannianMetric I M) (t : Real) :
    (fixedMetricFamily (I := I) g).metric t = g := by
  rfl

@[simp] private theorem fixedMetricFamily_connection
    (g : SmoothRiemannianMetric I M) (t : Real) :
    (fixedMetricFamily (I := I) g).connection t = LeviCivita (I := I) g := by
  rfl

private theorem exists_abs_laplacian_le_on_chartClosedAnnulus
    [I.Boundaryless] [T2Space M]
    (g : SmoothRiemannianMetric I M) {c : M}
    (b : SmoothBumpFunction I c) {r R : Real}
    (hR : R < b.rIn)
    (hne : (chartClosedAnnulus (I := I) c r R).Nonempty) :
    ∃ B : Real, 0 ≤ B ∧ ∀ x ∈ chartClosedAnnulus (I := I) c r R,
      |Δ_g (I := I) g
        ⟨_, compactCoordRadiusSq_contMDiff (I := I) b⟩ x| ≤ B := by
  let f : M → Real := compactCoordRadiusSq (I := I) b
  let q : M → Real := fun x => |Δ_g (I := I) g
    ⟨_, compactCoordRadiusSq_contMDiff (I := I) b⟩ x|
  have hK := chartClosedAnnulus_isCompact (I := I) b (r := r) (R := R)
    (hR.le.trans b.rIn_lt_rOut.le)
  have hqcont : Continuous q := by
    exact (continuous_abs.comp
      (Δ_g_contMDiff (I := I) g
        ⟨_, compactCoordRadiusSq_contMDiff (I := I) b⟩).continuous)
  obtain ⟨x0, hx0, hx0max⟩ := hK.exists_isMaxOn hne hqcont.continuousOn
  refine ⟨q x0, abs_nonneg _, ?_⟩
  intro x hx
  exact hx0max hx

omit [FiniteDimensional Real E] [IsManifold I ∞ M] in
private theorem exp_neg_mul_contMDiff
    {f : M → Real} (hf : ContMDiff I 𝓘(Real, Real) ∞ f)
    (alpha : Real) :
    ContMDiff I 𝓘(Real, Real) ∞
      (fun x => Real.exp (-alpha * f x)) := by
  have hc : ContMDiff I 𝓘(Real, Real) ∞ (fun _ : M => -alpha) :=
    contMDiff_const
  exact Real.contDiff_exp.contMDiff.comp (hc.mul hf)

private theorem delta_exp_neg_mul
    [I.Boundaryless] [T2Space M]
    (g : SmoothRiemannianMetric I M) {f : M → Real}
    (hf : ContMDiff I 𝓘(Real, Real) ∞ f)
    (alpha : Real) (x : M) :
    Δ_g (I := I) g ⟨_, exp_neg_mul_contMDiff (I := I) hf alpha⟩ x =
      Real.exp (-alpha * f x) *
        (-alpha * Δ_g (I := I) g ⟨f, hf⟩ x + alpha ^ 2 *
          g.inner x (gradientFun (I := I) g f x)
            (gradientFun (I := I) g f x)) := by
  let G := fixedMetricFamily (I := I) g
  let phi : Real → Real := Real.exp ∘ ((-alpha) * ·)
  have hphiDeriv (s : Real) :
      HasDerivAt phi (-alpha * Real.exp (-alpha * s)) s := by
    have hraw := (Real.hasDerivAt_exp (-alpha * s)).comp s
      ((hasDerivAt_id s).const_mul (-alpha))
    have hev : phi =ᶠ[nhds s] Real.exp ∘ HMul.hMul (-alpha) :=
      Filter.Eventually.of_forall fun y => by simp [phi]
    have h := hraw.congr_of_eventuallyEq hev
    convert h using 1
    ring
  have hphi : Differentiable Real phi := by
    intro s
    exact (hphiDeriv s).differentiableAt
  have hphi' : DifferentiableAt Real (deriv phi) (f x) := by
    have hderiv : deriv phi = fun s => -alpha * Real.exp (-alpha * s) := by
      funext s
      exact (hphiDeriv s).deriv
    rw [hderiv]
    fun_prop
  have hchain := heatDrift_comp (I := I) G (0 : Real)
    (fun _ => 0) hphi hphi'
    (fun y => hf.mdifferentiable (by simp) y)
    (gradientFun_mdiffAt (I := I) g hf x)
  have hfLap : laplacianAt (I := I) G 0 f x = Δ_g (I := I) g ⟨f, hf⟩ x := by
    exact laplacianAt_eq_delta (I := I) G 0 hf rfl x
  have hcompSmooth : ContMDiff I 𝓘(Real, Real) ∞
      (fun y => phi (f y)) :=
    exp_neg_mul_contMDiff (I := I) hf alpha
  have hcompLap :
      laplacianAt (I := I) G 0 (fun y => phi (f y)) x =
        Δ_g (I := I) g ⟨_, hcompSmooth⟩ x := by
    exact laplacianAt_eq_delta (I := I) G 0 hcompSmooth rfl x
  unfold heatOperatorWithDrift driftTerm at hchain
  rw [hcompLap, hfLap] at hchain
  have hchain' :
      Δ_g (I := I) g ⟨_, hcompSmooth⟩ x =
        deriv phi (f x) * Δ_g (I := I) g ⟨f, hf⟩ x +
          deriv (deriv phi) (f x) *
            g.inner x (gradientFun (I := I) g f x)
              (gradientFun (I := I) g f x) := by
    simpa [G] using hchain
  have hderiv1 : deriv phi (f x) = -alpha * Real.exp (-alpha * f x) := by
    exact (hphiDeriv (f x)).deriv
  have hderiv2 : deriv (deriv phi) (f x) =
      alpha ^ 2 * Real.exp (-alpha * f x) := by
    have hderiv : deriv phi = fun s => -alpha * Real.exp (-alpha * s) := by
      funext s
      exact (hphiDeriv s).deriv
    have harg := (hasDerivAt_id (f x)).const_mul (-alpha)
    have hexp := (Real.hasDerivAt_exp (-alpha * f x)).comp (f x) harg
    have hs := hexp.const_mul (-alpha)
    rw [hderiv]
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hs.deriv
  change Δ_g (I := I) g ⟨_, hcompSmooth⟩ x = _
  rw [hchain', hderiv1, hderiv2]
  ring

private def barrierRadius [T2Space M]
    {c : M} (b : SmoothBumpFunction I c) (R : Real) (x : M) : Real :=
  compactCoordRadiusSq (I := I) b x + R * (1 - b x)

private theorem barrierRadius_contMDiff [T2Space M]
    {c : M} (b : SmoothBumpFunction I c) (R : Real) :
    ContMDiff I 𝓘(Real, Real) ∞ (barrierRadius (I := I) b R) := by
  exact (compactCoordRadiusSq_contMDiff (I := I) b).add
    (contMDiff_const.mul (contMDiff_const.sub b.contMDiff))

omit [IsManifold I ∞ M] in
private theorem barrierRadius_nonneg [T2Space M]
    {c : M} (b : SmoothBumpFunction I c) {R : Real} (hR : 0 ≤ R) (x : M) :
    0 ≤ barrierRadius (I := I) b R x := by
  have hb0 := b.nonneg (x := x)
  have hb1 := b.le_one (x := x)
  have hrho : 0 ≤ coordRadiusSq (I := I) c x := sq_nonneg _
  unfold barrierRadius compactCoordRadiusSq
  exact add_nonneg (mul_nonneg hb0 hrho)
    (mul_nonneg hR (sub_nonneg.mpr hb1))

omit [IsManifold I ∞ M] in
private theorem barrierRadius_lt_imp [T2Space M]
    {c x : M} (b : SmoothBumpFunction I c) {R : Real}
    (h : barrierRadius (I := I) b R x < R) :
    0 < b x ∧ coordRadiusSq (I := I) c x < R := by
  have hb0 := b.nonneg (x := x)
  unfold barrierRadius compactCoordRadiusSq at h
  have hfactor : b x * (coordRadiusSq (I := I) c x - R) < 0 := by
    nlinarith
  have hbne : b x ≠ 0 := by
    intro hb
    rw [hb, zero_mul] at hfactor
    exact (lt_irrefl 0) hfactor
  have hbpos : 0 < b x := lt_of_le_of_ne hb0 (Ne.symm hbne)
  rcases (mul_neg_iff.mp hfactor) with hcase | hcase
  · exact ⟨hbpos, by linarith [hcase.2]⟩
  · exact (not_lt_of_ge hb0 hcase.1).elim

omit [IsManifold I ∞ M] in
private theorem barrierRadius_eventuallyEq_coordRadiusSq [T2Space M]
    {c x : M} (b : SmoothBumpFunction I c)
    (hx : x ∈ (chartAt H c).source)
    (hd : dist (extChartAt I c x) (extChartAt I c c) < b.rIn)
    (R : Real) :
    EventuallyEq (nhds x) (barrierRadius (I := I) b R)
      (coordRadiusSq (I := I) c) := by
  filter_upwards [b.eventuallyEq_one_of_dist_lt hx hd] with y hy
  simp [barrierRadius, compactCoordRadiusSq, hy]

omit [IsManifold I ∞ M] in
private theorem barrierRadius_eventuallyEq_compactCoordRadiusSq [T2Space M]
    {c x : M} (b : SmoothBumpFunction I c)
    (hx : x ∈ (chartAt H c).source)
    (hd : dist (extChartAt I c x) (extChartAt I c c) < b.rIn)
    (R : Real) :
    EventuallyEq (nhds x) (barrierRadius (I := I) b R)
      (compactCoordRadiusSq (I := I) b) :=
  (barrierRadius_eventuallyEq_coordRadiusSq (I := I) b hx hd R).trans
    (compactCoordRadiusSq_eventuallyEq (I := I) b hx hd).symm

private theorem delta_barrierRadius_eq_compactCoordRadiusSq
    [I.Boundaryless] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (g : SmoothRiemannianMetric I M) {c x : M}
    (b : SmoothBumpFunction I c)
    (hx : x ∈ (chartAt H c).source)
    (hd : dist (extChartAt I c x) (extChartAt I c c) < b.rIn)
    (R : Real) :
    Δ_g (I := I) g ⟨_, barrierRadius_contMDiff (I := I) b R⟩ x =
      Δ_g (I := I) g ⟨_, compactCoordRadiusSq_contMDiff (I := I) b⟩ x :=
  Δ_g_congr_of_eventuallyEq (I := I) g
    (barrierRadius_contMDiff (I := I) b R)
    (compactCoordRadiusSq_contMDiff (I := I) b)
    (barrierRadius_eventuallyEq_compactCoordRadiusSq (I := I) b hx hd R)

private def chartParabolicBarrier [T2Space M]
    {c : M} (b : SmoothBumpFunction I c)
    (epsilon alpha R kappa tau : Real) (t : Real) (x : M) : Real :=
  epsilon * (Real.exp (-alpha *
    (barrierRadius (I := I) b R x + kappa * (t - tau) ^ 2)) -
      Real.exp (-alpha * R))

private theorem chartParabolicBarrier_slice_contMDiff [T2Space M]
    {c : M} (b : SmoothBumpFunction I c)
    (epsilon alpha R kappa tau t : Real) :
    ContMDiff I 𝓘(Real, Real) ∞
      (chartParabolicBarrier (I := I) b epsilon alpha R kappa tau t) := by
  have harg : ContMDiff I 𝓘(Real, Real) ∞
      (fun x => -alpha *
        (barrierRadius (I := I) b R x + kappa * (t - tau) ^ 2)) :=
    contMDiff_const.mul ((barrierRadius_contMDiff (I := I) b R).add contMDiff_const)
  exact contMDiff_const.mul
    ((Real.contDiff_exp.contMDiff.comp harg).sub contMDiff_const)

private theorem chartParabolicBarrier_joint_continuous [T2Space M]
    {c : M} (b : SmoothBumpFunction I c)
    (epsilon alpha R kappa tau : Real) :
    Continuous (fun p : Real × M =>
      chartParabolicBarrier (I := I) b epsilon alpha R kappa tau p.1 p.2) := by
  have hF : Continuous (barrierRadius (I := I) b R) :=
    (barrierRadius_contMDiff (I := I) b R).continuous
  unfold chartParabolicBarrier
  fun_prop

omit [IsManifold I ∞ M] in
private theorem chartParabolicBarrier_time_differentiable [T2Space M]
    {c : M} (b : SmoothBumpFunction I c)
    (epsilon alpha R kappa tau : Real) (x : M) :
    Differentiable Real
      (fun t => chartParabolicBarrier (I := I)
        b epsilon alpha R kappa tau t x) := by
  unfold chartParabolicBarrier
  fun_prop

private def barrierPhase [T2Space M]
    {c : M} (b : SmoothBumpFunction I c)
    (R kappa tau : Real) (t : Real) (x : M) : Real :=
  barrierRadius (I := I) b R x + kappa * (t - tau) ^ 2

private theorem gradient_barrierPhase_eq_compactCoordRadiusSq
    [T2Space M]
    (g : SmoothRiemannianMetric I M) {c x : M}
    (b : SmoothBumpFunction I c)
    (hx : x ∈ (chartAt H c).source)
    (hd : dist (extChartAt I c x) (extChartAt I c c) < b.rIn)
    (R kappa tau t : Real) :
    gradientFun (I := I) g (barrierPhase (I := I) b R kappa tau t) x =
      gradientFun (I := I) g (compactCoordRadiusSq (I := I) b) x := by
  have hbr : gradientFun (I := I) g (barrierRadius (I := I) b R) x =
      gradientFun (I := I) g (compactCoordRadiusSq (I := I) b) x := by
    unfold gradientFun metricSharp
    rw [(barrierRadius_eventuallyEq_compactCoordRadiusSq
      (I := I) b hx hd R).mfderiv_eq]
  rw [show barrierPhase (I := I) b R kappa tau t =
      fun y => barrierRadius (I := I) b R y + kappa * (t - tau) ^ 2 from rfl]
  rw [gradientFun_add (I := I) g
    ((barrierRadius_contMDiff (I := I) b R).mdifferentiable (by simp) x)
    mdifferentiableAt_const]
  rw [gradientFun_const, add_zero, hbr]

omit [IsManifold I ∞ M] in
private theorem barrierPhase_time_derivWithin [T2Space M]
    {c : M} (b : SmoothBumpFunction I c)
    {T R kappa tau t : Real} (hT : 0 < T) (ht : t ∈ Set.Icc 0 T)
    (x : M) :
    derivWithin (fun s => barrierPhase (I := I) b R kappa tau s x)
        (Set.Icc 0 T) t = 2 * kappa * (t - tau) := by
  have hderiv : HasDerivAt
      (fun s => barrierPhase (I := I) b R kappa tau s x)
      (2 * kappa * (t - tau)) t := by
    unfold barrierPhase
    convert (hasDerivAt_const t (barrierRadius (I := I) b R x)).add
      (((hasDerivAt_id t).sub_const tau).pow 2 |>.const_mul kappa) using 1
    simp only [id_eq]
    ring
  exact hderiv.hasDerivWithinAt.derivWithin
    ((uniqueDiffOn_Icc hT).uniqueDiffWithinAt ht)

private theorem barrierPhase_parabolicOperator
    [I.Boundaryless] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (g : SmoothRiemannianMetric I M) {c : M}
    (b : SmoothBumpFunction I c)
    {T R kappa tau t : Real} (hT : 0 < T) (ht : t ∈ Set.Icc 0 T)
    (x : M) :
    parabolicOperatorWithDrift (I := I) (fixedMetricFamily (I := I) g) T
        (fun _ _ => 0) (barrierPhase (I := I) b R kappa tau) t x =
      2 * kappa * (t - tau) -
        Δ_g (I := I) g ⟨_, barrierRadius_contMDiff (I := I) b R⟩ x := by
  unfold parabolicOperatorWithDrift heatOperatorWithDrift driftTerm
  rw [barrierPhase_time_derivWithin (I := I) b hT ht x]
  have hslice : ContMDiff I 𝓘(Real, Real) ∞
      (barrierPhase (I := I) b R kappa tau t) :=
    (barrierRadius_contMDiff (I := I) b R).add contMDiff_const
  have hlap : laplacianAt (I := I) (fixedMetricFamily (I := I) g) t
      (barrierPhase (I := I) b R kappa tau t) x =
      Δ_g (I := I) g ⟨_, hslice⟩ x :=
    laplacianAt_eq_delta (I := I) (fixedMetricFamily (I := I) g) t hslice rfl x
  rw [hlap]
  have hadd := Δ_g_add (I := I) g
    ⟨_, barrierRadius_contMDiff (I := I) b R⟩
    ⟨_, (contMDiff_const : ContMDiff I 𝓘(Real, Real) ∞
      (fun _ : M => kappa * (t - tau) ^ 2))⟩ x
  have hconst := Δ_g_const (I := I) g (kappa * (t - tau) ^ 2) x
  have hadd' : Δ_g (I := I) g ⟨_, hslice⟩ x =
      Δ_g (I := I) g ⟨_, barrierRadius_contMDiff (I := I) b R⟩ x := by
    calc
      Δ_g (I := I) g ⟨_, hslice⟩ x =
          Δ_g (I := I) g ⟨_, barrierRadius_contMDiff (I := I) b R⟩ x +
            Δ_g (I := I) g
              ⟨_, (contMDiff_const : ContMDiff I 𝓘(Real, Real) ∞
                (fun _ : M => kappa * (t - tau) ^ 2))⟩ x := by
                  simpa using hadd
      _ = Δ_g (I := I) g ⟨_, barrierRadius_contMDiff (I := I) b R⟩ x := by
            rw [hconst, add_zero]
  rw [hadd']
  simp

private def expNegMul (alpha : Real) : Real → Real :=
  Real.exp ∘ ((-alpha) * ·)

private theorem expNegMul_hasDerivAt (alpha s : Real) :
    HasDerivAt (expNegMul alpha)
      (-alpha * Real.exp (-alpha * s)) s := by
  have hraw := (Real.hasDerivAt_exp (-alpha * s)).comp s
    ((hasDerivAt_id s).const_mul (-alpha))
  have hev : expNegMul alpha =ᶠ[nhds s] Real.exp ∘ HMul.hMul (-alpha) :=
    Filter.Eventually.of_forall fun y => by simp [expNegMul]
  have h := hraw.congr_of_eventuallyEq hev
  convert h using 1
  ring

private theorem expNegMul_deriv (alpha s : Real) :
    deriv (expNegMul alpha) s = -alpha * Real.exp (-alpha * s) :=
  (expNegMul_hasDerivAt alpha s).deriv

private theorem expNegMul_secondDeriv (alpha s : Real) :
    deriv (deriv (expNegMul alpha)) s = alpha ^ 2 * Real.exp (-alpha * s) := by
  have hderiv : deriv (expNegMul alpha) =
      fun z => -alpha * Real.exp (-alpha * z) := by
    funext z
    exact expNegMul_deriv alpha z
  have harg := (hasDerivAt_id s).const_mul (-alpha)
  have hexp := (Real.hasDerivAt_exp (-alpha * s)).comp s harg
  have hs := hexp.const_mul (-alpha)
  rw [hderiv]
  simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hs.deriv

private theorem exp_barrierPhase_parabolicOperator
    [I.Boundaryless] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (g : SmoothRiemannianMetric I M) {c : M}
    (b : SmoothBumpFunction I c) (alpha : Real)
    {T R kappa tau t : Real} (hT : 0 < T) (ht : t ∈ Set.Icc 0 T)
    (x : M) :
    parabolicOperatorWithDrift (I := I) (fixedMetricFamily (I := I) g) T
        (fun _ _ => 0)
        (fun s y => Real.exp (-alpha * barrierPhase (I := I) b R kappa tau s y)) t x =
      Real.exp (-alpha * barrierPhase (I := I) b R kappa tau t x) *
        (-alpha * (2 * kappa * (t - tau) -
          Δ_g (I := I) g ⟨_, barrierRadius_contMDiff (I := I) b R⟩ x) -
          alpha ^ 2 * g.inner x
            (gradientFun (I := I) g
              (barrierPhase (I := I) b R kappa tau t) x)
            (gradientFun (I := I) g
              (barrierPhase (I := I) b R kappa tau t) x)) := by
  let phi := expNegMul alpha
  have hphi : Differentiable Real phi := by
    intro s
    exact (expNegMul_hasDerivAt alpha s).differentiableAt
  have hphi' : DifferentiableAt Real (deriv phi)
      (barrierPhase (I := I) b R kappa tau t x) := by
    have hd : deriv phi = fun s => -alpha * Real.exp (-alpha * s) := by
      funext s
      exact expNegMul_deriv alpha s
    rw [hd]
    fun_prop
  have htime : DifferentiableWithinAt Real
      (fun s => barrierPhase (I := I) b R kappa tau s x)
      (Set.Icc 0 T) t := by
    unfold barrierPhase
    fun_prop
  have hslice : ContMDiff I 𝓘(Real, Real) ∞
      (barrierPhase (I := I) b R kappa tau t) :=
    (barrierRadius_contMDiff (I := I) b R).add contMDiff_const
  have hchain := parabolic_comp (I := I)
    (fixedMetricFamily (I := I) g) T (fun _ _ => 0)
    (barrierPhase (I := I) b R kappa tau) t x hphi hphi' htime
    (fun y => hslice.mdifferentiable (by simp) y)
    (gradientFun_mdiffAt (I := I) g hslice x)
  rw [barrierPhase_parabolicOperator (I := I) g b hT ht x] at hchain
  rw [expNegMul_deriv, expNegMul_secondDeriv] at hchain
  have hchain' :
      parabolicOperatorWithDrift (I := I) (fixedMetricFamily (I := I) g) T
          (fun _ _ => 0)
          (fun s y => Real.exp
            (-alpha * barrierPhase (I := I) b R kappa tau s y)) t x =
        -alpha * Real.exp
            (-alpha * barrierPhase (I := I) b R kappa tau t x) *
            (2 * kappa * (t - tau) -
              Δ_g (I := I) g ⟨_, barrierRadius_contMDiff (I := I) b R⟩ x) -
          alpha ^ 2 * Real.exp
            (-alpha * barrierPhase (I := I) b R kappa tau t x) *
            g.inner x
              (gradientFun (I := I) g
                (barrierPhase (I := I) b R kappa tau t) x)
              (gradientFun (I := I) g
                (barrierPhase (I := I) b R kappa tau t) x) := by
    simpa [phi, expNegMul, gradientAt_eq] using hchain
  rw [hchain']
  ring

private theorem chartParabolicBarrier_parabolicOperator
    [I.Boundaryless] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (g : SmoothRiemannianMetric I M) {c : M}
    (b : SmoothBumpFunction I c) (epsilon alpha : Real)
    {T R kappa tau t : Real} (hT : 0 < T) (ht : t ∈ Set.Icc 0 T)
    (x : M) :
    parabolicOperatorWithDrift (I := I) (fixedMetricFamily (I := I) g) T
        (fun _ _ => 0)
        (chartParabolicBarrier (I := I) b epsilon alpha R kappa tau) t x =
      epsilon * Real.exp
          (-alpha * barrierPhase (I := I) b R kappa tau t x) *
        (-alpha * (2 * kappa * (t - tau) -
          Δ_g (I := I) g ⟨_, barrierRadius_contMDiff (I := I) b R⟩ x) -
          alpha ^ 2 * g.inner x
            (gradientFun (I := I) g
              (barrierPhase (I := I) b R kappa tau t) x)
            (gradientFun (I := I) g
              (barrierPhase (I := I) b R kappa tau t) x)) := by
  let e : Real → M → Real := fun s y => Real.exp
    (-alpha * barrierPhase (I := I) b R kappa tau s y)
  let q : Real → M → Real := fun s y => e s y - Real.exp (-alpha * R)
  have he_space : ∀ y : M,
      MDifferentiableAt I 𝓘(Real, Real) (e t) y := by
    intro y
    exact (exp_neg_mul_contMDiff (I := I)
      ((barrierRadius_contMDiff (I := I) b R).add contMDiff_const) alpha
      |>.mdifferentiable (by simp) y)
  have he_time : DifferentiableWithinAt Real (fun s => e s x)
      (Set.Icc 0 T) t := by
    dsimp [e, barrierPhase]
    fun_prop
  have hc_time : DifferentiableWithinAt Real
      (fun _ : Real => Real.exp (-alpha * R)) (Set.Icc 0 T) t :=
    differentiableWithinAt_const _
  have hsub := parabolic_sub_time_curve_identity (I := I)
    (fixedMetricFamily (I := I) g) T (fun _ _ => 0) e
    (fun _ => Real.exp (-alpha * R)) t he_space x he_time hc_time
  have huniq : UniqueDiffWithinAt Real (Set.Icc 0 T) t :=
    (uniqueDiffOn_Icc hT).uniqueDiffWithinAt ht
  have hc_deriv : derivWithin (fun _ : Real => Real.exp (-alpha * R))
      (Set.Icc 0 T) t = 0 :=
    (hasDerivWithinAt_const (x := t) (s := Set.Icc 0 T)
      (c := Real.exp (-alpha * R))).derivWithin huniq
  rw [hc_deriv, sub_zero] at hsub
  have hq_time : DifferentiableWithinAt Real (fun s => q s x)
      (Set.Icc 0 T) t := he_time.sub hc_time
  have hq_space : ∀ y : M,
      MDifferentiableAt I 𝓘(Real, Real) (q t) y := by
    intro y
    exact (he_space y).sub mdifferentiableAt_const
  have hq_grad : MDiffAt (T% fun y : M =>
      gradientFun (I := I) g (q t) y) x := by
    have hq_smooth : ContMDiff I 𝓘(Real, Real) ∞ (q t) :=
      (exp_neg_mul_contMDiff (I := I)
        ((barrierRadius_contMDiff (I := I) b R).add contMDiff_const) alpha).sub
          contMDiff_const
    exact gradientFun_mdiffAt (I := I) g hq_smooth x
  have hscale := parabolic_smul (I := I)
    (fixedMetricFamily (I := I) g) T (fun _ _ => 0) epsilon q t x
    hq_time hq_space hq_grad
  have hexp := exp_barrierPhase_parabolicOperator (I := I)
    g b alpha (R := R) (kappa := kappa) (tau := tau) hT ht x
  change parabolicOperatorWithDrift (I := I)
      (fixedMetricFamily (I := I) g) T (fun _ _ => 0) q t x =
    parabolicOperatorWithDrift (I := I)
      (fixedMetricFamily (I := I) g) T (fun _ _ => 0) e t x at hsub
  change parabolicOperatorWithDrift (I := I)
      (fixedMetricFamily (I := I) g) T (fun _ _ => 0)
        (chartParabolicBarrier (I := I) b epsilon alpha R kappa tau) t x =
    epsilon * parabolicOperatorWithDrift (I := I)
      (fixedMetricFamily (I := I) g) T (fun _ _ => 0) q t x at hscale
  rw [hsub, hexp] at hscale
  calc
    parabolicOperatorWithDrift (I := I) (fixedMetricFamily (I := I) g) T
        (fun _ _ => 0)
        (chartParabolicBarrier (I := I) b epsilon alpha R kappa tau) t x =
      epsilon * (Real.exp
          (-alpha * barrierPhase (I := I) b R kappa tau t x) *
        (-alpha * (2 * kappa * (t - tau) -
          Δ_g (I := I) g ⟨_, barrierRadius_contMDiff (I := I) b R⟩ x) -
          alpha ^ 2 * g.inner x
            (gradientFun (I := I) g
              (barrierPhase (I := I) b R kappa tau t) x)
            (gradientFun (I := I) g
              (barrierPhase (I := I) b R kappa tau t) x))) := hscale
    _ = _ := by ring

private theorem fixed_metric_local_positivity
    [I.Boundaryless]
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (g : SmoothRiemannianMetric I M) {T : Real} (hT : 0 < T)
    (u : Real → M → Real)
    (hu_cont : ContinuousOn (fun p : Real × M => u p.1 p.2)
      (spacetimeSlab (M := M) T))
    (hu_nonneg : ∀ t ∈ Set.Icc 0 T, ∀ x : M, 0 ≤ u t x)
    (hu_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s => u s x) (Set.Icc 0 T) t)
    (hu_mdiff : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDifferentiableAt I 𝓘(Real, Real) (u t) x)
    (hu_grad : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDiffAt (T% fun y : M => gradientFun (I := I) g (u t) y) x)
    (hu_super : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      0 ≤ parabolicOperatorWithDrift (I := I)
        (fixedMetricFamily (I := I) g) T (fun _ _ => 0) u t x)
    {c : M} (b : SmoothBumpFunction I c)
    {r Rdist R delta eta m B kappa alpha : Real}
    (hRdist : Rdist < b.rIn)
    (hR : 0 < R)
    (hsublevel : ∀ x : M, coordRadiusSq (I := I) c x < R →
      dist (extChartAt I c x) (extChartAt I c c) < Rdist)
    (hdelta : 0 < delta) (heta : 0 < eta)
    (hlocal : ∀ t ∈ Set.Icc 0 T, T - delta < t → ∀ x : M,
      dist (extChartAt I c x) (extChartAt I c c) < r → eta ≤ u t x)
    (hgrad_lower : ∀ x ∈ chartClosedAnnulus (I := I) c r Rdist,
      m ≤ g.inner x
        (gradientFun (I := I) g (compactCoordRadiusSq (I := I) b) x)
        (gradientFun (I := I) g (compactCoordRadiusSq (I := I) b) x))
    (hlap_bound : ∀ x ∈ chartClosedAnnulus (I := I) c r Rdist,
      |Δ_g (I := I) g ⟨_, compactCoordRadiusSq_contMDiff (I := I) b⟩ x| ≤ B)
    (hkappa : 0 < kappa) (hinit : R ≤ kappa * T ^ 2)
    (htime : R ≤ kappa * delta ^ 2)
    (halpha : 0 < alpha) (hdom : 2 * kappa * T + B ≤ alpha * m)
    {y : M} (hy_source : y ∈ (chartAt H c).source)
    (hy : coordRadiusSq (I := I) c y < R) :
    0 < u T y := by
  let epsilon : Real := eta / 2
  let v : Real → M → Real :=
    chartParabolicBarrier (I := I) b epsilon alpha R kappa T
  let w : Real → M → Real := fun t x => u t x - v t x
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon]
    linarith
  have hkappa_nonneg : 0 ≤ kappa := hkappa.le
  have hR_nonneg : 0 ≤ R := hR.le
  have hphase_nonneg : ∀ t ∈ Set.Icc 0 T, ∀ x : M,
      0 ≤ barrierPhase (I := I) b R kappa T t x := by
    intro t ht x
    exact add_nonneg (barrierRadius_nonneg (I := I) b hR_nonneg x)
      (mul_nonneg hkappa_nonneg (sq_nonneg _))
  have hv_lt_epsilon : ∀ t ∈ Set.Icc 0 T, ∀ x : M,
      v t x < epsilon := by
    intro t ht x
    have hexp_le : Real.exp
        (-alpha * barrierPhase (I := I) b R kappa T t x) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr halpha.le)
        (hphase_nonneg t ht x)
    have hexpR : 0 < Real.exp (-alpha * R) := Real.exp_pos _
    have hdiff : Real.exp
        (-alpha * barrierPhase (I := I) b R kappa T t x) -
        Real.exp (-alpha * R) < 1 := by
      linarith
    change epsilon * (Real.exp
        (-alpha * barrierPhase (I := I) b R kappa T t x) -
          Real.exp (-alpha * R)) < epsilon
    simpa only [mul_comm] using (mul_lt_iff_lt_one_left hepsilon).mpr hdiff
  have hv_pos_imp_phase_lt : ∀ t x, 0 < v t x →
      barrierPhase (I := I) b R kappa T t x < R := by
    intro t x hv
    have hexp_lt : Real.exp (-alpha * R) <
        Real.exp (-alpha * barrierPhase (I := I) b R kappa T t x) := by
      have hmul : 0 < epsilon *
          (Real.exp (-alpha * barrierPhase (I := I) b R kappa T t x) -
            Real.exp (-alpha * R)) := by
        exact hv
      have hdiff : 0 <
          Real.exp (-alpha * barrierPhase (I := I) b R kappa T t x) -
            Real.exp (-alpha * R) := ((mul_pos_iff.mp hmul).resolve_right
        (fun h => (not_lt_of_ge hepsilon.le h.1).elim)).2
      linarith
    have harg := Real.exp_lt_exp.mp hexp_lt
    nlinarith
  have hv_cont : ContinuousOn (fun p : Real × M => v p.1 p.2)
      (spacetimeSlab (M := M) T) :=
    (chartParabolicBarrier_joint_continuous (I := I)
      b epsilon alpha R kappa T).continuousOn
  have hw_cont : ContinuousOn (fun p : Real × M => w p.1 p.2)
      (spacetimeSlab (M := M) T) := by
    exact hu_cont.sub hv_cont
  have hw0 : ∀ x : M, 0 ≤ w 0 x := by
    intro x
    have hphase0 : R ≤ barrierPhase (I := I) b R kappa T 0 x := by
      have hbr := barrierRadius_nonneg (I := I) b hR_nonneg x
      unfold barrierPhase
      nlinarith
    have hexp_le : Real.exp
        (-alpha * barrierPhase (I := I) b R kappa T 0 x) ≤
        Real.exp (-alpha * R) := by
      exact Real.exp_le_exp.mpr (by nlinarith)
    have hv0 : v 0 x ≤ 0 := by
      dsimp [v, chartParabolicBarrier]
      exact mul_nonpos_of_nonneg_of_nonpos hepsilon.le (sub_nonpos.mpr hexp_le)
    dsimp [w]
    linarith [hu_nonneg 0 ⟨le_rfl, hT.le⟩ x]
  have hv_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s => v s x) (Set.Icc 0 T) t := by
    intro t ht htpos x
    exact (chartParabolicBarrier_time_differentiable (I := I)
      b epsilon alpha R kappa T x t).differentiableWithinAt
  have hv_mdiff : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDifferentiableAt I 𝓘(Real, Real) (v t) x := by
    intro t ht htpos x
    exact (chartParabolicBarrier_slice_contMDiff (I := I)
      b epsilon alpha R kappa T t).mdifferentiable (by simp) x
  have hv_grad : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDiffAt (T% fun y : M => gradientFun (I := I) g (v t) y) x := by
    intro t ht htpos x
    exact gradientFun_mdiffAt (I := I) g
      (chartParabolicBarrier_slice_contMDiff (I := I)
        b epsilon alpha R kappa T t) x
  have hw_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s => w s x) (Set.Icc 0 T) t := by
    intro t ht htpos x
    exact (hu_time t ht htpos x).sub (hv_time t ht htpos x)
  have hw_mdiff : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDifferentiableAt I 𝓘(Real, Real) (w t) x := by
    intro t ht htpos x
    exact (hu_mdiff t ht htpos x).sub (hv_mdiff t ht htpos x)
  have hw_grad : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDiffAt (T% fun y : M => gradientFun (I := I) g (w t) y) x := by
    intro t ht htpos x
    have heq :
        (T% fun y : M => gradientFun (I := I) g (w t) y) =
          (T% fun y : M => gradientFun (I := I) g (u t) y -
            gradientFun (I := I) g (v t) y) := by
      funext z
      apply congrArg (fun q =>
        (⟨z, q⟩ : TotalSpace E (TangentSpace I : M → Type _)))
      exact gradientFun_sub (I := I) g
        (hu_mdiff t ht htpos z) (hv_mdiff t ht htpos z)
    rw [heq]
    exact mdifferentiableAt_sub_section
      (hu_grad t ht htpos x) (hv_grad t ht htpos x)
  have hnegative : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      w t x < 0 → 0 ≤ parabolicOperatorWithDrift (I := I)
        (fixedMetricFamily (I := I) g) T (fun _ _ => 0) w t x := by
    intro t ht htpos x hwneg
    have hvpos : 0 < v t x := by
      dsimp [w] at hwneg
      linarith [hu_nonneg t ht x]
    have hphase_lt := hv_pos_imp_phase_lt t x hvpos
    have hbr_lt : barrierRadius (I := I) b R x < R := by
      have htime_nonneg : 0 ≤ kappa * (t - T) ^ 2 :=
        mul_nonneg hkappa_nonneg (sq_nonneg _)
      unfold barrierPhase at hphase_lt
      linarith
    obtain ⟨hbpos, hcoord⟩ := barrierRadius_lt_imp (I := I) b hbr_lt
    have hx_support : x ∈ Function.support b := hbpos.ne'
    have hx_source : x ∈ (chartAt H c).source :=
      b.support_subset_source hx_support
    have hdist_upper :
        dist (extChartAt I c x) (extChartAt I c c) < Rdist :=
      hsublevel x hcoord
    have htime_sq : kappa * (t - T) ^ 2 < R := by
      have hbr_nonneg := barrierRadius_nonneg (I := I) b hR_nonneg x
      unfold barrierPhase at hphase_lt
      linarith
    have htime_close : T - delta < t := by
      have hsq : (t - T) ^ 2 < delta ^ 2 := by
        nlinarith
      have ht_le : t ≤ T := ht.2
      nlinarith [sq_nonneg (t - T + delta)]
    have hdist_lower : r ≤
        dist (extChartAt I c x) (extChartAt I c c) := by
      by_contra hnot
      have hdist_small :
          dist (extChartAt I c x) (extChartAt I c c) < r := lt_of_not_ge hnot
      have hu_eta := hlocal t ht htime_close x hdist_small
      have hv_eps := hv_lt_epsilon t ht x
      dsimp [w] at hwneg
      dsimp [epsilon] at hv_eps
      linarith
    have hxK : x ∈ chartClosedAnnulus (I := I) c r Rdist :=
      mem_chartClosedAnnulus_of_data (I := I) hx_source hdist_lower
        hdist_upper.le
    have hdist_core :
        dist (extChartAt I c x) (extChartAt I c c) < b.rIn :=
      hdist_upper.trans hRdist
    have hdelta_eq := delta_barrierRadius_eq_compactCoordRadiusSq
      (I := I) g b hx_source hdist_core R
    have hgrad_eq := gradient_barrierPhase_eq_compactCoordRadiusSq
      (I := I) g b hx_source hdist_core R kappa T t
    have hlap := hlap_bound x hxK
    have hgradq := hgrad_lower x hxK
    have hPv := chartParabolicBarrier_parabolicOperator (I := I)
      g b epsilon alpha (R := R) (kappa := kappa) (tau := T) hT ht x
    rw [hdelta_eq, hgrad_eq] at hPv
    have hdelta_upper :
        Δ_g (I := I) g ⟨_, compactCoordRadiusSq_contMDiff (I := I) b⟩ x ≤ B :=
      le_trans (le_abs_self _) hlap
    have hbracket :
        -alpha * (2 * kappa * (t - T) -
          Δ_g (I := I) g ⟨_, compactCoordRadiusSq_contMDiff (I := I) b⟩ x) -
          alpha ^ 2 * g.inner x
            (gradientFun (I := I) g (compactCoordRadiusSq (I := I) b) x)
            (gradientFun (I := I) g (compactCoordRadiusSq (I := I) b) x) ≤ 0 := by
      have hkt : 0 ≤ kappa * t := mul_nonneg hkappa_nonneg ht.1
      have hlin :
          -(2 * kappa * (t - T) -
            Δ_g (I := I) g
              ⟨_, compactCoordRadiusSq_contMDiff (I := I) b⟩ x) ≤
            2 * kappa * T + B := by
        nlinarith
      have hqmul : alpha * m ≤ alpha * g.inner x
          (gradientFun (I := I) g (compactCoordRadiusSq (I := I) b) x)
          (gradientFun (I := I) g (compactCoordRadiusSq (I := I) b) x) :=
        mul_le_mul_of_nonneg_left hgradq halpha.le
      have hlinq :
          -(2 * kappa * (t - T) -
            Δ_g (I := I) g
              ⟨_, compactCoordRadiusSq_contMDiff (I := I) b⟩ x) ≤
            alpha * g.inner x
              (gradientFun (I := I) g
                (compactCoordRadiusSq (I := I) b) x)
              (gradientFun (I := I) g
                (compactCoordRadiusSq (I := I) b) x) :=
        hlin.trans (hdom.trans hqmul)
      have hmul := mul_le_mul_of_nonneg_left hlinq halpha.le
      calc
        -alpha * (2 * kappa * (t - T) -
            Δ_g (I := I) g
              ⟨_, compactCoordRadiusSq_contMDiff (I := I) b⟩ x) -
            alpha ^ 2 * g.inner x
              (gradientFun (I := I) g
                (compactCoordRadiusSq (I := I) b) x)
              (gradientFun (I := I) g
                (compactCoordRadiusSq (I := I) b) x) =
          alpha * (-(2 * kappa * (t - T) -
            Δ_g (I := I) g
              ⟨_, compactCoordRadiusSq_contMDiff (I := I) b⟩ x)) -
            alpha * (alpha * g.inner x
              (gradientFun (I := I) g
                (compactCoordRadiusSq (I := I) b) x)
              (gradientFun (I := I) g
                (compactCoordRadiusSq (I := I) b) x)) := by ring
        _ ≤ 0 := sub_nonpos.mpr hmul
    have hPv_nonpos : parabolicOperatorWithDrift (I := I)
        (fixedMetricFamily (I := I) g) T (fun _ _ => 0) v t x ≤ 0 := by
      change parabolicOperatorWithDrift (I := I)
        (fixedMetricFamily (I := I) g) T (fun _ _ => 0)
        (chartParabolicBarrier (I := I) b epsilon alpha R kappa T) t x ≤ 0
      rw [hPv]
      exact mul_nonpos_of_nonneg_of_nonpos
        (mul_nonneg hepsilon.le (Real.exp_pos _).le) hbracket
    have hsub := parabolic_sub (I := I)
      (fixedMetricFamily (I := I) g) T (fun _ _ => 0) u v t x
      (hu_time t ht htpos x) (hv_time t ht htpos x)
      (hu_mdiff t ht htpos) (hv_mdiff t ht htpos)
      (hu_grad t ht htpos x) (hv_grad t ht htpos x)
    change parabolicOperatorWithDrift (I := I)
        (fixedMetricFamily (I := I) g) T (fun _ _ => 0) w t x = _ at hsub
    rw [hsub]
    linarith [hu_super t ht htpos x]
  have hw_nonneg := strict_barrier_positive_region (I := I)
    (fixedMetricFamily (I := I) g) T (fun _ _ => 0) w
    hw_cont hw0 hw_time hw_mdiff
    (by simpa using hw_grad) hnegative T ⟨hT.le, le_rfl⟩ y
  have hy_dist : dist (extChartAt I c y) (extChartAt I c c) < Rdist :=
    hsublevel y hy
  have hy_core : dist (extChartAt I c y) (extChartAt I c c) < b.rIn :=
    hy_dist.trans hRdist
  have hy_radius : barrierRadius (I := I) b R y =
      coordRadiusSq (I := I) c y :=
    (barrierRadius_eventuallyEq_coordRadiusSq (I := I)
      b hy_source hy_core R).eq_of_nhds
  have hvT_pos : 0 < v T y := by
    have hexp_lt : Real.exp (-alpha * R) <
        Real.exp (-alpha * coordRadiusSq (I := I) c y) := by
      exact Real.exp_lt_exp.mpr (by nlinarith)
    have hphaseT : barrierPhase (I := I) b R kappa T T y =
        coordRadiusSq (I := I) c y := by
      simp [barrierPhase, hy_radius]
    change 0 < epsilon *
      (Real.exp (-alpha * barrierPhase (I := I) b R kappa T T y) -
        Real.exp (-alpha * R))
    rw [hphaseT]
    exact mul_pos hepsilon (sub_pos.mpr hexp_lt)
  dsimp [w] at hw_nonneg
  linarith

end

end DifferentialGeometry.Analysis.Parabolic
