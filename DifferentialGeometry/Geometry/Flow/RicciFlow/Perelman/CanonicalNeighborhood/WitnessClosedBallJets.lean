import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WitnessSpatialBuffer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.OpenTensorJets
import DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetricContinuity


set_option autoImplicit false
noncomputable section
open Set Filter Bundle Manifold
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

private local instance closedBallJetsC1 : IsManifold I 1 M :=
  IsManifold.of_le (n := ∞) (by decide)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [CompleteSpace E] in
theorem closure_riemannianBallOf [I.Boundaryless] [NeZero (Module.finrank ℝ E)]
    [T2Space (TangentBundle I M)]
    (g : SmoothRiemannianMetric I M) (hg : RiemannianMetricComplete g)
    (p : M) {R : ℝ} (hR : 0 < R) :
    closure (riemannianBallOf g p R) = riemannianClosedBallOf g p R := by
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let : T3Space M := inferInstance
  let : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let : CompleteSpace M := hg.complete
  have hEnorm : IsMetricNorm (I := I) (M := M) g :=
    fun x v => tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) g x v
  have hnorm (v : TangentSpace I p) : ‖v‖ = Real.sqrt (g.inner p v v) := by
    have hv := hEnorm p v
    rw [← ofReal_norm] at hv
    exact (ENNReal.ofReal_eq_ofReal_iff (norm_nonneg v) (Real.sqrt_nonneg _)).mp hv
  have himage : (expMapIntrinsic (I := I) g hEnorm p) ''
      Metric.ball (0 : TangentSpace I p) R ⊆ riemannianBallOf g p R := by
    rintro _ ⟨v, hv, rfl⟩
    have hvR : Real.sqrt (g.inner p v v) < R := by
      simpa only [Metric.mem_ball, dist_zero_right, hnorm] using hv
    have hd := intrinsicGeodesic_riemannianEDist_le (I := I) g hEnorm p v
      (show (0 : ℝ) ≤ 1 by norm_num)
    rw [intrinsicGeodesic_zero, ← expMapIntrinsic_def, sub_zero, mul_one] at hd
    exact hd.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hR).mpr hvR)
  apply Subset.antisymm
  · have hsub : riemannianBallOf g p R ⊆ riemannianClosedBallOf g p R := by
      intro x hx
      change riemannianEDistOf (I := I) g p x < ENNReal.ofReal R at hx
      change riemannianEDistOf (I := I) g p x ≤ ENNReal.ofReal R
      exact hx.le
    exact closure_minimal hsub
      (isClosed_le (continuous_riemannianEDist g p) continuous_const)
  · intro x hx
    have hfinite : riemannianEDist I p x ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top hx
    obtain ⟨v, hv, hlen⟩ :=
      hopf_rinow_expMapIntrinsic_surjective_minimizing_of_ne_top g hEnorm p x hfinite
    have hvclosed : v ∈ Metric.closedBall (0 : TangentSpace I p) R := by
      rw [Metric.mem_closedBall, dist_zero_right, hnorm, hlen]
      exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hx).trans_eq
        (ENNReal.toReal_ofReal hR.le)
    have hvclosure : v ∈ closure (Metric.ball (0 : TangentSpace I p) R) := by
      rwa [closure_ball _ hR.ne']
    have hexp := image_closure_subset_closure_image
      (expMapIntrinsic_continuous (I := I) g hEnorm p) ⟨v, hvclosure, hv⟩
    exact closure_mono himage hexp

omit [SigmaCompactSpace M] in
theorem tensor02CovDerivNormWith_eq_on_closure
    (gcov gnorm : SmoothRiemannianMetric I M)
    (A B : Tensor0SField (I := I) (M := M) (n := ∞) 2)
    {U : Set M} (hU : IsOpen U) (hAB : ∀ x ∈ U, A x = B x) (a : ℕ) :
    EqOn (tensor02CovDerivNormWith a A gcov gnorm)
      (tensor02CovDerivNormWith a B gcov gnorm) (closure U) := by
  let V : TopologicalSpace.Opens M := ⟨U, hU⟩
  have hrestrict : restrictOpen0S (I := I) 2 (V := V) A =
      restrictOpen0S (I := I) 2 (V := V) B := by
    ext x v
    change A (x : M) v = B (x : M) v
    exact congrArg (fun T => T v) (hAB x x.property)
  have heq : EqOn (tensor02CovDerivNormWith a A gcov gnorm)
      (tensor02CovDerivNormWith a B gcov gnorm) U := by
    intro x hx
    calc
      _ = tensor02CovDerivNormWith a (restrictOpen0S (I := I) 2 (V := V) A)
          (gcov.restrictOpen V) (gnorm.restrictOpen V) (⟨x, hx⟩ : V) :=
        (tensor02CovDerivNormWith_restrictOpen0S V gcov gnorm A a ⟨x, hx⟩).symm
      _ = tensor02CovDerivNormWith a (restrictOpen0S (I := I) 2 (V := V) B)
          (gcov.restrictOpen V) (gnorm.restrictOpen V) (⟨x, hx⟩ : V) := by rw [hrestrict]
      _ = _ := tensor02CovDerivNormWith_restrictOpen0S V gcov gnorm B a ⟨x, hx⟩
  exact heq.closure
    (Real.continuous_sqrt.comp (normSq0S_cont gnorm (tensor02CovDeriv A gcov a)))
    (Real.continuous_sqrt.comp (normSq0S_cont gnorm (tensor02CovDeriv B gcov a)))


theorem tensor02CovDerivNormWith_eq_on_riemannianClosedBall
    [I.Boundaryless] [NeZero (Module.finrank ℝ E)] [T2Space (TangentBundle I M)]
    (g : SmoothRiemannianMetric I M) (hg : RiemannianMetricComplete g)
    (p : M) {R : ℝ} (hR : 0 < R)
    (gcov gnorm : SmoothRiemannianMetric I M)
    (A B : Tensor0SField (I := I) (M := M) (n := ∞) 2)
    (hAB : ∀ x ∈ riemannianClosedBallOf g p R, A x = B x) (a : ℕ) :
    EqOn (tensor02CovDerivNormWith a A gcov gnorm)
      (tensor02CovDerivNormWith a B gcov gnorm) (riemannianClosedBallOf g p R) := by
  rw [← closure_riemannianBallOf g hg p hR]
  exact tensor02CovDerivNormWith_eq_on_closure gcov gnorm A B
    (isOpen_lt (continuous_riemannianEDist g p) continuous_const)
    (fun x hx => hAB x (by
      change riemannianEDistOf (I := I) g p x ≤ ENNReal.ofReal R
      exact hx.le)) a

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
