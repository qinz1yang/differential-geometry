import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornGeometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WitnessTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WitnessClosedBallJets


set_option autoImplicit false
noncomputable section
open Bundle Manifold Set
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Analysis.Laplacian

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

universe u

variable {M N : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace ThreeSpace N] [IsManifold I3 ∞ N]
  [T2Space N] [SigmaCompactSpace N] [T2Space (TangentBundle I3 N)]

private local instance transportSourceC1 : IsManifold I3 1 M :=
  IsManifold.of_le (n := ∞) (by decide)
private local instance transportModelC1 : IsManifold I3 1 N :=
  IsManifold.of_le (n := ∞) (by decide)
private local instance transportDimension : NeZero (Module.finrank ℝ ThreeSpace) :=
  ⟨by simp [ThreeSpace]⟩

variable {h : ℝ → SmoothRiemannianMetric I3 N}
  {g : ℝ → SmoothRiemannianMetric I3 M}
  {F : PartialDiffeomorph I3 I3 N M ∞} {K : Set N} {J : Set ℝ}
  {order : ℕ} {eps : ℝ}

omit [T2Space M] [T2Space (TangentBundle I3 N)] in
theorem MetricComparisonOn.jet_zero_eq
    (C : MetricComparisonOn h g F K J order eps) (s : ℝ) :
    C.jet 0 s = C.pullback s - metricTensorField (h s) := by
  refine DFunLike.ext _ _ (fun y => ?_)
  have hy : (C.pullback s - metricTensorField (h s)) y =
      C.pullback s y - metricTensorField (h s) y := by
    simp only [ContMDiffSection.coe_sub, Pi.sub_apply]
  rw [hy]
  exact tensor0SSpace_ext 2 y (fun v => by
    rw [C.jet_zero, Tensor0SSpace.sub_apply, metricTensorField_apply])

omit [T2Space (TangentBundle I3 N)] in
theorem MetricComparisonOn.metricUniformEquivalentOn
    (C : MetricComparisonOn h g F K J order eps)
    (heps : 0 ≤ eps) (heps1 : eps < 1) {s : ℝ} (hs : s ∈ J) :
    MetricUniformEquivalentOn (Subtype.val ⁻¹' K : Set (sourceOpen F))
      (witnessModelMetric F h s) (witnessPullbackMetric F g s) (witnessLambda eps) := by
  refine ⟨one_le_witnessLambda heps heps1, ?_⟩
  intro y hy v
  obtain ⟨hlow, hhigh⟩ := C.equivalence s hs (y : N) hy v
  have hpb : (witnessPullbackMetric F g s).inner y v v =
      C.pullback s (y : N) (fun _ => v) := by
    rw [witnessPullbackMetric, openPullbackMetric_inner]
    exact (C.pullback_eq s (y : N) hy (fun _ => v)).symm
  have href : (witnessModelMetric F h s).inner y v v = (h s).inner (y : N) v v := rfl
  constructor
  · simpa only [hpb, href, witnessLambda, inv_inv] using hlow
  · rw [hpb, href]
    exact hhigh.trans (mul_le_mul_of_nonneg_right (one_add_le_witnessLambda heps heps1)
      (inner_self_nonneg (h s) (y : N) v))


theorem MetricComparisonOn.metricCovDerivOrderBoundOn
    (g₀ : SmoothRiemannianMetric I3 N) (hg₀ : RiemannianMetricComplete g₀)
    (p : N) {R : ℝ} (hR : 0 < R)
    (C : MetricComparisonOn h g F (riemannianClosedBallOf g₀ p R) J order eps)
    {s : ℝ} (hs : s ∈ J) {a : ℕ} (ha1 : 1 ≤ a) (ha : a ≤ order) :
    MetricCovDerivOrderBoundOn
      (Subtype.val ⁻¹' riemannianClosedBallOf g₀ p R : Set (sourceOpen F)) a
      (witnessPullbackMetric F g s) (witnessModelMetric F h s) eps := by
  let V := sourceOpen F
  let A := metricTensorField (witnessPullbackMetric F g s)
  let B := restrictOpen0S (I := I3) 2 (V := V) (C.pullback s)
  let O : Set V := Subtype.val ⁻¹' riemannianBallOf g₀ p R
  have hO : IsOpen O :=
    (isOpen_lt (continuous_riemannianEDist g₀ p) continuous_const).preimage continuous_subtype_val
  have hclosure : closure O = (Subtype.val ⁻¹' riemannianClosedBallOf g₀ p R : Set V) := by
    calc
      closure O = (Subtype.val : V → N) ⁻¹' closure (riemannianBallOf g₀ p R) := by
        exact (IsOpenMap.preimage_closure_eq_closure_preimage (f := (Subtype.val : V → N))
          V.isOpen.isOpenEmbedding_subtypeVal.isOpenMap continuous_subtype_val _).symm
      _ = _ := congrArg (fun A : Set N => (Subtype.val : V → N) ⁻¹' A)
        (closure_riemannianBallOf g₀ hg₀ p hR)
  have hAB : ∀ y ∈ O, A y = B y := by
    intro y hy
    have hyK : (y : N) ∈ riemannianClosedBallOf g₀ p R := by
      change riemannianEDistOf g₀ p (y : N) ≤ ENNReal.ofReal R
      exact hy.le
    apply tensor0SSpace_ext 2 y
    intro v
    change metricTensorField (witnessPullbackMetric F g s) y v = C.pullback s (y : N) v
    rw [metricTensorField_apply, witnessPullbackMetric, openPullbackMetric_inner]
    exact (C.pullback_eq s (y : N) hyK v).symm
  intro y hy
  have hyclosure : y ∈ closure O := by rw [hclosure]; exact hy
  have hnorm := tensor02CovDerivNormWith_eq_on_closure
    (witnessModelMetric F h s) (witnessModelMetric F h s) A B hO hAB a hyclosure
  have hactual : metricCovDerivNorm a (witnessPullbackMetric F g s) (witnessModelMetric F h s) y =
      tensor02CovDerivNormWith a A (witnessModelMetric F h s) (witnessModelMetric F h s) y := by
    simp only [metricCovDerivNorm, tensor02CovDerivNormWith, A,
      metricCovDeriv_eq_covDerivOfField, tensor02_cov_deriv_eq_cov_deriv_of_field]
  have hrestrict : tensor02CovDerivNormWith a B (witnessModelMetric F h s)
      (witnessModelMetric F h s) y =
      tensor02CovDerivNormWith a (C.pullback s) (h s) (h s) (y : N) :=
    tensor02CovDerivNormWith_restrictOpen0S V (h s) (h s) (C.pullback s) a y
  have hfield : tensor02CovDeriv (C.pullback s) (h s) a = tensor02CovDeriv (C.jet 0 s) (h s) a := by
    obtain ⟨b, rfl⟩ : ∃ b : ℕ, a = b + 1 := ⟨a - 1, by omega⟩
    rw [C.jet_zero_eq, tensor02CovDeriv_sub_metricTensorField]
  have hjetnorm : tensor02CovDerivNormWith a (C.pullback s) (h s) (h s) (y : N) =
      tensor02CovDerivNormWith a (C.jet 0 s) (h s) (h s) (y : N) := by
    unfold tensor02CovDerivNormWith
    rw [hfield]
  rw [hactual, hnorm, hrestrict, hjetnorm]
  exact C.close a 0 (by simpa only [mul_zero, add_zero] using ha) s hs (y : N) hy

private theorem sqrt_le_of_squared_bound {A B a b c : ℝ} (hB : 0 ≤ B)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hA : A ≤ B ^ 2 * a * b * c) :
    Real.sqrt A ≤ B * Real.sqrt a * Real.sqrt b * Real.sqrt c := by
  have hprod : B ^ 2 * a * b * c = (B * Real.sqrt a * Real.sqrt b * Real.sqrt c) ^ 2 := by
    rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt ha, Real.sq_sqrt hb, Real.sq_sqrt hc]
  rw [hprod] at hA
  exact (Real.sqrt_le_sqrt hA).trans_eq (Real.sqrt_sq (by positivity))


theorem MetricComparisonOn.riemannOp_sub_norm_le
    (g₀ : SmoothRiemannianMetric I3 N) (hg₀ : RiemannianMetricComplete g₀)
    (p : N) {R : ℝ} (hR : 0 < R)
    (C : MetricComparisonOn h g F (riemannianClosedBallOf g₀ p R) J order eps)
    (heps : 0 ≤ eps) (heps1 : eps < 1) (horder : 2 ≤ order)
    {s : ℝ} (hs : s ∈ J) {y : sourceOpen F}
    (hy : (y : N) ∈ riemannianClosedBallOf g₀ p R) (v w u : TangentSpace I3 y) :
    Real.sqrt ((witnessModelMetric F h s).inner y
      (riemannOp (cov := LeviCivita (witnessPullbackMetric F g s)) y v w u -
        riemannOp (cov := LeviCivita (witnessModelMetric F h s)) y v w u)
      (riemannOp (cov := LeviCivita (witnessPullbackMetric F g s)) y v w u -
        riemannOp (cov := LeviCivita (witnessModelMetric F h s)) y v w u)) ≤
      witnessRiemannC eps * Real.sqrt ((witnessModelMetric F h s).inner y v v) *
        Real.sqrt ((witnessModelMetric F h s).inner y w w) *
        Real.sqrt ((witnessModelMetric F h s).inner y u u) := by
  have hEq := C.metricUniformEquivalentOn heps heps1 hs
  have hJet1 := C.metricCovDerivOrderBoundOn g₀ hg₀ p hR hs (a := 1) le_rfl (by omega)
  have hJet2 := C.metricCovDerivOrderBoundOn g₀ hg₀ p hR hs (a := 2) (by omega) horder
  have hh := riemannDiff_gJet_le (witnessModelMetric F h s) (witnessPullbackMetric F g s)
    hEq hJet1 hJet2 hy v w u
  exact sqrt_le_of_squared_bound (witnessRiemannC_nonneg heps heps1)
    (inner_self_nonneg _ _ _) (inner_self_nonneg _ _ _) (inner_self_nonneg _ _ _) hh


theorem MetricComparisonOn.riemannOp_norm_le
    (g₀ : SmoothRiemannianMetric I3 N) (hg₀ : RiemannianMetricComplete g₀)
    (p : N) {R : ℝ} (hR : 0 < R)
    (C : MetricComparisonOn h g F (riemannianClosedBallOf g₀ p R) J order eps)
    (heps : 0 ≤ eps) (heps1 : eps < 1) (horder : 2 ≤ order)
    {s : ℝ} (hs : s ∈ J) {y : sourceOpen F}
    (hy : (y : N) ∈ riemannianClosedBallOf g₀ p R)
    {Kb : ℝ} (hKb0 : 0 ≤ Kb)
    (hKb : ∀ a b c : TangentSpace I3 y,
      (witnessModelMetric F h s).inner y
        (riemannOp (cov := LeviCivita (witnessModelMetric F h s)) y a b c)
        (riemannOp (cov := LeviCivita (witnessModelMetric F h s)) y a b c) ≤
        Kb * (witnessModelMetric F h s).inner y a a *
          (witnessModelMetric F h s).inner y b b * (witnessModelMetric F h s).inner y c c)
    (v w u : TangentSpace I3 y) :
    Real.sqrt ((witnessPullbackMetric F g s).inner y
      (riemannOp (cov := LeviCivita (witnessPullbackMetric F g s)) y v w u)
      (riemannOp (cov := LeviCivita (witnessPullbackMetric F g s)) y v w u)) ≤
      witnessLambda eps ^ 2 * (witnessRiemannC eps + Real.sqrt Kb) *
        Real.sqrt ((witnessPullbackMetric F g s).inner y v v) *
        Real.sqrt ((witnessPullbackMetric F g s).inner y w w) *
        Real.sqrt ((witnessPullbackMetric F g s).inner y u u) := by
  let href := witnessModelMetric F h s
  let pb := witnessPullbackMetric F g s
  let L := witnessLambda eps
  have hEq := C.metricUniformEquivalentOn heps heps1 hs
  have hL1 : 1 ≤ L := hEq.1
  have hLpos : 0 < L := zero_lt_one.trans_le hL1
  have hL0 : 0 ≤ L := hLpos.le
  have hA (v : TangentSpace I3 y) :
      Real.sqrt (pb.inner y v v) ≤ Real.sqrt L * Real.sqrt (href.inner y v v) := by
    calc Real.sqrt (pb.inner y v v) ≤ Real.sqrt (L * href.inner y v v) :=
        Real.sqrt_le_sqrt (hEq.2 y hy v).2
      _ = _ := Real.sqrt_mul hL0 _
  have hB (v : TangentSpace I3 y) :
      Real.sqrt (href.inner y v v) ≤ Real.sqrt L * Real.sqrt (pb.inner y v v) := by
    have hlow := (hEq.2 y hy v).1
    have hup : href.inner y v v ≤ L * pb.inner y v v := by
      have hmul := mul_le_mul_of_nonneg_left hlow hL0
      rw [← mul_assoc, mul_inv_cancel₀ hLpos.ne', one_mul] at hmul
      exact hmul
    exact (Real.sqrt_le_sqrt hup).trans_eq (Real.sqrt_mul hL0 _)
  let Rv := riemannOp (cov := LeviCivita pb) y v w u
  let Rh := riemannOp (cov := LeviCivita href) y v w u
  have htri : Real.sqrt (href.inner y Rv Rv) ≤
      Real.sqrt (href.inner y (Rv - Rh) (Rv - Rh)) + Real.sqrt (href.inner y Rh Rh) := by
    have hh := sqrt_inner_add_le href y (Rv - Rh) Rh
    rwa [sub_add_cancel] at hh
  have hDb := C.riemannOp_sub_norm_le g₀ hg₀ p hR heps heps1 horder hs hy v w u
  have hRhb : Real.sqrt (href.inner y Rh Rh) ≤
      Real.sqrt Kb * Real.sqrt (href.inner y v v) * Real.sqrt (href.inner y w w) *
        Real.sqrt (href.inner y u u) := by
    apply sqrt_le_of_squared_bound (Real.sqrt_nonneg Kb)
      (inner_self_nonneg _ _ _) (inner_self_nonneg _ _ _) (inner_self_nonneg _ _ _)
    rw [Real.sq_sqrt hKb0]
    exact hKb v w u
  have hsum : Real.sqrt (href.inner y Rv Rv) ≤
      (witnessRiemannC eps + Real.sqrt Kb) *
        (Real.sqrt (href.inner y v v) * Real.sqrt (href.inner y w w) *
          Real.sqrt (href.inner y u u)) := by
    calc Real.sqrt (href.inner y Rv Rv) ≤
        Real.sqrt (href.inner y (Rv - Rh) (Rv - Rh)) + Real.sqrt (href.inner y Rh Rh) := htri
      _ ≤ witnessRiemannC eps * Real.sqrt (href.inner y v v) * Real.sqrt (href.inner y w w) *
          Real.sqrt (href.inner y u u) +
          Real.sqrt Kb * Real.sqrt (href.inner y v v) * Real.sqrt (href.inner y w w) *
          Real.sqrt (href.inner y u u) := add_le_add hDb hRhb
      _ = _ := by ring
  have hC0 : 0 ≤ witnessRiemannC eps + Real.sqrt Kb :=
    add_nonneg (witnessRiemannC_nonneg heps heps1) (Real.sqrt_nonneg Kb)
  have hr4 : Real.sqrt L ^ 4 = L ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt hL0]
  calc Real.sqrt (pb.inner y Rv Rv) ≤ Real.sqrt L * Real.sqrt (href.inner y Rv Rv) := hA Rv
    _ ≤ Real.sqrt L * ((witnessRiemannC eps + Real.sqrt Kb) *
        (Real.sqrt (href.inner y v v) * Real.sqrt (href.inner y w w) *
          Real.sqrt (href.inner y u u))) := mul_le_mul_of_nonneg_left hsum (Real.sqrt_nonneg L)
    _ ≤ Real.sqrt L * ((witnessRiemannC eps + Real.sqrt Kb) *
        ((Real.sqrt L * Real.sqrt (pb.inner y v v)) *
          (Real.sqrt L * Real.sqrt (pb.inner y w w)) *
          (Real.sqrt L * Real.sqrt (pb.inner y u u)))) := by
      apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg L)
      apply mul_le_mul_of_nonneg_left _ hC0
      exact mul_le_mul
        (mul_le_mul (hB v) (hB w) (Real.sqrt_nonneg _) (by positivity)) (hB u)
        (Real.sqrt_nonneg _) (by positivity)
    _ = _ := by rw [← hr4]; ring

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
