import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.RoundCanonicalWitness
import DifferentialGeometry.Geometry.Metric.TensorInner.Fiber.MetricData
import DifferentialGeometry.Geometry.Metric.Sphere.Quotient.Descent
import DifferentialGeometry.Geometry.Metric.Sphere.Quotient.SpaceForm
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.RoundModelClassification

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff ENNReal Topology
open scoped Bundle

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open Bundle _root_.MeasureTheory
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Tensor0SBundle

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]

omit [T2Space M] [SigmaCompactSpace M] in
theorem metric_inner_sq_le (g : SmoothRiemannianMetric I3 M) (x : M)
    (v w : TangentSpace I3 x) :
    (g.inner x v w) ^ 2 ≤ g.inner x v v * g.inner x w w := by
  let D := (tangentMetricData (I := I3) g x).metric
  let : PreInnerProductSpace.Core ℝ (TangentSpace I3 x) := D.toCore.toCore
  let : Inner ℝ (TangentSpace I3 x) := D.toCore.toCore.toInner
  have hcs := InnerProductSpace.Core.inner_mul_inner_self_le (𝕜 := ℝ)
    (F := TangentSpace I3 x) v w
  have hAB : Inner.inner ℝ v w = g.inner x v w :=
    (MetricFiberData.toCore_inner D v w).trans (TangentMetricData.inner_eq _ v w)
  have hBA : Inner.inner ℝ w v = g.inner x v w :=
    (MetricFiberData.toCore_inner D w v).trans
      ((MetricFiberData.symm D w v).trans (TangentMetricData.inner_eq _ v w))
  have hAA : Inner.inner ℝ v v = g.inner x v v :=
    (MetricFiberData.toCore_inner D v v).trans (TangentMetricData.inner_eq _ v v)
  have hBB : Inner.inner ℝ w w = g.inner x w w :=
    (MetricFiberData.toCore_inner D w w).trans (TangentMetricData.inner_eq _ w w)
  rw [hAB, hBA, hAA, hBB] at hcs
  simpa [Real.norm_eq_abs, pow_two, sq_abs] using hcs

omit [T2Space M] [SigmaCompactSpace M] in
theorem secLower_zero_of_constantCurvature (g : SmoothRiemannianMetric I3 M)
    (hcurv : ∀ (z : M) (v w : TangentSpace I3 z),
      metricRm04At g z (vec4 v w w v) =
        (1 / 6 : ℝ) * (g.inner z v v * g.inner z w w - (g.inner z v w) ^ 2)) :
    SecLower g 0 (Set.univ : Set M) := by
  intro y _ v w
  have hvec : (fun i : Fin 4 => ![v, w, w, v] i) = vec4 v w w v := by
    funext i
    fin_cases i <;> simp [vec4]
  rw [zero_mul, hvec, hcurv y v w]
  have hcs := metric_inner_sq_le g y v w
  nlinarith [hcs]

omit [SigmaCompactSpace M] in
theorem curvatureOperatorLowerBoundAt_of_constantCurvature
    (g : SmoothRiemannianMetric I3 M)
    (hcurv : ∀ (z : M) (v w : TangentSpace I3 z),
      metricRm04At g z (vec4 v w w v) =
        (1 / 6 : ℝ) * (g.inner z v v * g.inner z w w - (g.inner z v w) ^ 2))
    (y : M) :
    curvatureOperatorLowerBoundAt (I := I3) g y
      (metricAlgebraicCurvatureTensorAt (I := I3) (M := M) g y) 0 := by
  have h := (secLower_iff_curvatureOperatorLowerBoundAt (M := M) g
    (by simp [ThreeSpace]) 0 Set.univ).mp
      (secLower_zero_of_constantCurvature g hcurv)
  simpa using h y trivial

omit [SigmaCompactSpace M] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_ball_eq_univ_of_compact (g : SmoothRiemannianMetric I3 M)
    [CompactSpace M] [PreconnectedSpace M] (x : M) :
    ∃ R : ℝ, 0 < R ∧ (Set.univ : Set M) ⊆ riemannianBallOf g x R := by
  have : Nonempty M := ⟨x⟩
  let : RiemannianBundle (fun y : M => TangentSpace I3 y) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle ThreeSpace
      (fun y : M => TangentSpace I3 y) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  have hfin : ∀ y : M, Manifold.riemannianEDist I3 x y ≠ ⊤ := by
    intro y
    change riemannianEDistOf (I := I3) g x y ≠ ⊤
    exact riemannianEDistOf_ne_top (I := I3) g x y
  have hcontOn := continuousOn_riemannianEDist_toReal_on_finite
    (I := I3) g x
  have hfinite_set : {q : M |
      Manifold.riemannianEDist I3 x q ≠ (⊤ : ℝ≥0∞)} = Set.univ := by
    ext q
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact hfin q
  have hcont : Continuous (fun y : M =>
      (Manifold.riemannianEDist I3 x y).toReal) :=
    continuousOn_univ.mp (by simpa only [hfinite_set] using hcontOn)
  obtain ⟨y₀, _, hmax⟩ :=
    isCompact_univ.exists_isMaxOn (Set.univ_nonempty) hcont.continuousOn
  refine ⟨max ((Manifold.riemannianEDist I3 x y₀).toReal) 1 + 1,
    by positivity, fun y hy => ?_⟩
  change Manifold.riemannianEDist I3 x y <
    ENNReal.ofReal (max ((Manifold.riemannianEDist I3 x y₀).toReal) 1 + 1)
  apply (ENNReal.lt_ofReal_iff_toReal_lt (hfin y)).mpr
  have hle : (Manifold.riemannianEDist I3 x y).toReal ≤
      max ((Manifold.riemannianEDist I3 x y₀).toReal) 1 :=
    (hmax trivial).trans (le_max_left _ _)
  exact hle.trans_lt (lt_add_one _)

theorem roundComponent_of_constantCurvature (g : SmoothRiemannianMetric I3 M)
    [CompactSpace M] [ConnectedSpace M]
    (hcurv : ∀ (z : M) (v w : TangentSpace I3 z),
      metricRm04At g z (vec4 v w w v) =
        (1 / 6 : ℝ) * (g.inner z v v * g.inner z w w - (g.inner z v w) ^ 2))
    (hscalar : ∀ z : M, metricScalarAt g z = 1)
    {eps : ℝ} (heps : 0 < eps) (x : M) :
    Nonempty (RoundComponent (SolutionOn.const g (RealTimeInterval.univ 0))
      eps x 0 Set.univ) := by
  have hsx : (SolutionOn.const g (RealTimeInterval.univ 0)).scalar 0 x = 1 := by
    change metricScalarAt g x = 1
    exact hscalar x
  have hQ : 0 < (SolutionOn.const g (RealTimeInterval.univ 0)).scalar 0 x := by
    rw [hsx]
    norm_num
  refine ⟨{
    Z := M
    topology := inferInstance
    charted := inferInstance
    smooth := inferInstance
    t2 := inferInstance
    compact := inferInstance
    connected := inferInstance
    metric := g
    p := x
    scalar_one := hscalar
    constant_curvature := ?_
    map := PartialDiffeomorph.refl (I := I3) M
    source_eq := rfl
    target_eq := rfl
    center_eq := rfl
    Q_pos := hQ
    comparison := ?_
    metric_bounds := ?_ }⟩
  · intro z v w
    have hvec : (fun i : Fin 4 => ![v, w, w, v] i) = vec4 v w w v := by
      funext i
      fin_cases i <;> simp [vec4]
    rw [hvec]
    exact hcurv z v w
  · convert metricComparisonOnRefl (M := M) (g := fun _ => g) Set.univ
      ({0} : Set ℝ) (⌈eps⁻¹⌉₊) heps using 1
    funext s
    apply SmoothRiemannianMetric.ext_inner
    intro y v w
    change (SolutionOn.const g (RealTimeInterval.univ 0)).scalar 0 x *
        g.inner y v w = g.inner y v w
    rw [hsx, one_mul]
  · intro z v
    have hmap : ((↑(PartialDiffeomorph.refl (I := I3) M).toPartialEquiv) :
        M → M) = id := by
      funext y
      rfl
    rw [hmap]
    simp only [SolutionOn.const_metric, mfderiv_id, ContinuousLinearMap.id_apply, id_eq]
    rw [hsx, one_mul]
    have hnn : 0 ≤ g.inner z v v := metric_inner_self_nonneg g z v
    constructor <;> linarith

private theorem one_le_sqrt_three : (1 : ℝ) ≤ Real.sqrt 3 := by
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg 3]

theorem exists_canonicalWitness_of_constantCurvature
    (g : SmoothRiemannianMetric I3 M)
    [CompactSpace M] [ConnectedSpace M]
    (hcurv : ∀ (z : M) (v w : TangentSpace I3 z),
      metricRm04At g z (vec4 v w w v) =
        (1 / 6 : ℝ) * (g.inner z v v * g.inner z w w - (g.inner z v w) ^ 2))
    (hscalar : ∀ z : M, metricScalarAt g z = 1)
    (x : M) {eps : ℝ} (heps : 0 < eps) (heps_one : eps < 1) :
    ∃ C1 C2 : ℝ, 1 ≤ C1 ∧ 1 ≤ C2 ∧
      Nonempty (CanonicalWitness (SolutionOn.const g (RealTimeInterval.univ 0))
        eps C1 C2 x 0) := by
  obtain ⟨R, hRpos, hRball⟩ := exists_ball_eq_univ_of_compact g x
  obtain ⟨RC⟩ := roundComponent_of_constantCurvature g hcurv hscalar heps x
  have hsx : (SolutionOn.const g (RealTimeInterval.univ 0)).scalar 0 x = 1 := by
    change metricScalarAt g x = 1
    exact hscalar x
  have hQ : 0 < (SolutionOn.const g (RealTimeInterval.univ 0)).scalar 0 x := by
    rw [hsx]
    norm_num
  have hsall : ∀ y : M, (SolutionOn.const g (RealTimeInterval.univ 0)).scalar 0 y = 1 := by
    intro y
    change metricScalarAt g y = 1
    exact hscalar y
  have hRnonneg : 0 ≤ R := hRpos.le
  refine ⟨max R 1, Real.sqrt 3, le_max_right _ _, one_le_sqrt_three, ?_⟩
  refine ⟨{
    Q_pos := hQ
    time_mem := Set.mem_univ 0
    eps_pos := heps
    eps_lt_one := heps_one
    domain := {
      carrier := Set.univ
      compact := isCompact_univ
      connected := isConnected_univ
      regular_closed := by simp
      boundary_chart := by
        intro y hy
        simp at hy }
    center_inside := by
      change x ∈ interior (Set.univ : Set M)
      simp
    radius := max R 1
    radius_lower := ?_
    radius_upper := ?_
    ball_inside := ?_
    inside_ball := ?_
    scalar_bounds := ?_
    rm_bound := ?_
    alternative := CanonicalAlternative.round
      (PreconnectedSpace.connectedComponent_eq_univ x).symm RC
    volume := by
      intro hv
      cases hv
    gradient := ?_
    time_derivative := ?_ }⟩
  · rw [hsx]
    simp
  · rw [hsx]
    simp
  · intro y hy
    exact Set.mem_univ y
  · intro y hy
    exact riemannianBallOf_mono (I := I3) g x
      (by
        have h1 : 0 ≤ max R 1 := le_trans zero_le_one (le_max_right _ _)
        have h2 : max R 1 ≤ 2 * max R 1 := by linarith
        exact (le_max_left R 1).trans h2)
      (hRball hy)
  · intro y hy
    rw [hsx, hsall y]
    constructor
    · simpa using inv_le_one_of_one_le₀ one_le_sqrt_three
    · nlinarith [one_le_sqrt_three]
  · intro y hy
    have hnn : curvatureOperatorLowerBoundAt (I := I3)
        ((SolutionOn.const g (RealTimeInterval.univ 0)).base.metric 0) y
        (metricAlgebraicCurvatureTensorAt (I := I3) (M := M)
          ((SolutionOn.const g (RealTimeInterval.univ 0)).base.metric 0) y) 0 := by
      change curvatureOperatorLowerBoundAt (I := I3) g y
        (metricAlgebraicCurvatureTensorAt (I := I3) (M := M) g y) 0
      exact curvatureOperatorLowerBoundAt_of_constantCurvature g hcurv y
    have hbound := sqrt_rmNormSq_le_sqrt_three_mul_scalar_of_curvatureOperatorNonneg
      (S := SolutionOn.const g (RealTimeInterval.univ 0)) (by simp [ThreeSpace]) 0 y hnn
    simpa only [hsall x, hsall y, one_mul] using hbound
  · intro v
    have h0 : scalarDifferential (I := I3)
        (SolutionOn.const g (RealTimeInterval.univ 0)) 0 x v = 0 := by
      simp only [scalarDifferential]
      have h : (fun y : M =>
          (SolutionOn.const g (RealTimeInterval.univ 0)).scalar 0 y) = fun _ => 1 := by
        funext y
        change metricScalarAt g y = 1
        exact hscalar y
      rw [h, mfderiv_const]
      rfl
    rw [h0]
    simp only [abs_zero]
    rw [hsall x]
    positivity
  · rw [hsall x]
    have h : (fun s : ℝ =>
        (SolutionOn.const g (RealTimeInterval.univ 0)).scalar s x) = fun _ => 1 := by
      funext s
      exact hsall x
    rw [h]
    simp

theorem exists_canonicalWitness_roundSphereThree_via_constantCurvature
    (x : RoundSphereThree) {eps : ℝ} (heps : 0 < eps) (heps_one : eps < 1) :
    ∃ C1 C2 : ℝ, 1 ≤ C1 ∧ 1 ≤ C2 ∧
      Nonempty (CanonicalWitness (roundSphereThreeSolution (RealTimeInterval.univ 0))
        eps C1 C2 x 0) := by
  let : ConnectedSpace RoundSphereThree := by
    refine isConnected_iff_connectedSpace.mp ?_
    refine isConnected_sphere (E := EuclideanSpace ℝ (Fin 4)) ?_ 0 (r := 1) (by norm_num)
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
    norm_num
  have hcurv : ∀ (z : RoundSphereThree) (v w : TangentSpace I3 z),
      metricRm04At roundSphereThreeMetric z (vec4 v w w v) =
        (1 / 6 : ℝ) * (roundSphereThreeMetric.inner z v v *
          roundSphereThreeMetric.inner z w w -
          (roundSphereThreeMetric.inner z v w) ^ 2) := by
    intro z v w
    have hvec : (fun i : Fin 4 => ![v, w, w, v] i) = vec4 v w w v := by
      funext i
      fin_cases i <;> simp [vec4]
    rw [← hvec]
    exact roundSphereThree_constant_curvature z v w
  exact exists_canonicalWitness_of_constantCurvature roundSphereThreeMetric hcurv
    roundSphereThree_scalar_one x heps heps_one

noncomputable def roundSphereQuotientUnitMetric
    (Dq : RoundSphereQuotient.{0, u} (EuclideanSpace ℝ (Fin 4)) 3) :
    SmoothRiemannianMetric (𝓡 3) Dq.Q :=
  scaleMetric (I := 𝓡 3) (6 * Classical.choose Dq.gQuot_constPosSec)
    (by
      have h := (Classical.choose_spec Dq.gQuot_constPosSec).1
      positivity) Dq.gQuot

theorem exists_canonicalWitness_roundSphereQuotient
    (Dq : RoundSphereQuotient.{0, u} (EuclideanSpace ℝ (Fin 4)) 3)
    (x : Dq.Q) {eps : ℝ} (heps : 0 < eps) (heps_one : eps < 1) :
    ∃ C1 C2 : ℝ, 1 ≤ C1 ∧ 1 ≤ C2 ∧
      Nonempty (CanonicalWitness
        (SolutionOn.const (roundSphereQuotientUnitMetric Dq) (RealTimeInterval.univ 0))
        eps C1 C2 x 0) := by
  have hsurj : Function.Surjective Dq.proj := fun y =>
    ⟨_, (Dq.sectionAt y).proj_localSection ⟨y, (Dq.sectionAt y).mem_baseNeighborhood⟩⟩
  let : CompactSpace Dq.Q := hsurj.compactSpace Dq.proj_smooth.continuous
  let : ConnectedSpace Dq.Q := hsurj.connectedSpace Dq.proj_smooth.continuous
  have hcspec := Classical.choose_spec Dq.gQuot_constPosSec
  have hscalar : ∀ z : Dq.Q, metricScalarAt (roundSphereQuotientUnitMetric Dq) z = 1 := by
    intro z
    rw [roundSphereQuotientUnitMetric, metricScalarAt_scaleMetric,
      DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.gQuot_metricScalarAt_eq_six_mul
        Dq hcspec.2 z]
    have hne : (6 * Classical.choose Dq.gQuot_constPosSec) ≠ 0 := by
      have h := hcspec.1
      positivity
    rw [inv_mul_cancel₀ hne]
  have hcurv : ∀ (z : Dq.Q) (v w : TangentSpace I3 z),
      metricRm04At (roundSphereQuotientUnitMetric Dq) z (vec4 v w w v) =
        (1 / 6 : ℝ) * ((roundSphereQuotientUnitMetric Dq).inner z v v *
          (roundSphereQuotientUnitMetric Dq).inner z w w -
          ((roundSphereQuotientUnitMetric Dq).inner z v w) ^ 2) := by
    intro z v w
    rw [← metricRm04StandardAt_apply, roundSphereQuotientUnitMetric,
      metricRmStandard_scale, hcspec.2 z v w]
    simp only [scaleMetric_inner]
    ring
  exact exists_canonicalWitness_of_constantCurvature (roundSphereQuotientUnitMetric Dq)
    hcurv hscalar x heps heps_one

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
