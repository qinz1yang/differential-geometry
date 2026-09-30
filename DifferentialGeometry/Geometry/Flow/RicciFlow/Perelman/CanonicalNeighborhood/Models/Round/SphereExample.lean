import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornGeometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Stationary
import DifferentialGeometry.Geometry.Curvature.Sphere.ConstCurvature
import DifferentialGeometry.Geometry.Curvature.ScalarSectional
import DifferentialGeometry.Geometry.Curvature.Metric.Scaling
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.RmNormFromEigenvalues
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ComparisonReflexive
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.PositiveSectionalLowerBound

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff ENNReal Topology
open scoped Bundle

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open Bundle
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Tensor0SBundle

abbrev RoundSphereThree := Sphere 3

private instance roundSphereThreeFact :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) :=
  ⟨by norm_num [finrank_euclideanSpace_fin]⟩

def roundSphereThreeMetric : SmoothRiemannianMetric I3 RoundSphereThree :=
  scaleMetric (I := I3) 6 (by norm_num)
    (roundMetric (E := EuclideanSpace ℝ (Fin 4)) (n := 3))

theorem roundSphereThree_constant_curvature :
    ∀ z (v w : TangentSpace I3 z),
      metricRm04At roundSphereThreeMetric z (fun i : Fin 4 => ![v, w, w, v] i) =
        (1 / 6 : ℝ) * (roundSphereThreeMetric.inner z v v *
          roundSphereThreeMetric.inner z w w -
          (roundSphereThreeMetric.inner z v w) ^ 2) := by
  intro z v w
  have hvec : (fun i : Fin 4 => ![v, w, w, v] i) = vec4 v w w v := by
    funext i
    fin_cases i <;> simp [vec4]
  rw [hvec, ← metricRm04StandardAt_apply]
  simp only [roundSphereThreeMetric]
  rw [metricRmStandard_scale (I := I3) 6 (by norm_num)
      (roundMetric (E := EuclideanSpace ℝ (Fin 4)) (n := 3)) z v w w v,
    roundMetric_sec_value (E := EuclideanSpace ℝ (Fin 4)) (n := 3) z v w]
  simp only [scaleMetric_inner]
  ring

theorem roundSphereThree_scalar_one (z : RoundSphereThree) :
    metricScalarAt roundSphereThreeMetric z = 1 := by
  rw [metricScalarAt_of_constant_sectional roundSphereThreeMetric z (1 / 6)
    (fun u v => by
      have hfun : (fun i : Fin 4 => ![u, v, v, u] i) = vec4 u v v u := by
        funext i
        fin_cases i <;> simp [vec4]
      simpa only [metricRm04StandardAt_apply, hfun] using
        roundSphereThree_constant_curvature z u v)]
  norm_num

private instance roundSphereThreeConnected : ConnectedSpace RoundSphereThree := by
  refine isConnected_iff_connectedSpace.mp ?_
  refine isConnected_sphere (E := EuclideanSpace ℝ (Fin 4)) ?_ 0 (r := 1) (by norm_num)
  rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
  norm_num

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_roundSphereThree_ball_eq_univ (x : RoundSphereThree) :
    ∃ R : ℝ, 0 < R ∧
      (Set.univ : Set RoundSphereThree) ⊆ riemannianBallOf roundSphereThreeMetric x R := by
  let : RiemannianBundle (fun y : RoundSphereThree => TangentSpace I3 y) :=
    ⟨roundSphereThreeMetric.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle ThreeSpace
      (fun y : RoundSphereThree => TangentSpace I3 y) :=
    ⟨roundSphereThreeMetric.inner, roundSphereThreeMetric.contMDiff.continuous,
      fun _ _ _ => rfl⟩
  have hfin : ∀ y : RoundSphereThree,
      Manifold.riemannianEDist I3 x y ≠ ⊤ := by
    intro y
    change riemannianEDistOf (I := I3) roundSphereThreeMetric x y ≠ ⊤
    exact riemannianEDistOf_ne_top (I := I3) roundSphereThreeMetric x y
  have hcontOn := continuousOn_riemannianEDist_toReal_on_finite
    (I := I3) roundSphereThreeMetric x
  have hfinite_set : {q : RoundSphereThree |
      Manifold.riemannianEDist I3 x q ≠ (⊤ : ℝ≥0∞)} = Set.univ := by
    ext q
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact hfin q
  have hcont : Continuous (fun y : RoundSphereThree =>
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

def roundSphereThreeSolution (D : RealTimeInterval) :
    SolutionOn (I := I3) (M := RoundSphereThree) D :=
  SolutionOn.const roundSphereThreeMetric D

theorem roundSphereThree_solution_scalar (D : RealTimeInterval) (t : ℝ)
    (x : RoundSphereThree) :
    (roundSphereThreeSolution D).scalar t x = 1 := by
  change metricScalarAt (I := I3) roundSphereThreeMetric x = 1
  exact roundSphereThree_scalar_one x

def roundSphereThreeCompactDomain : CompactDomain RoundSphereThree where
  carrier := Set.univ
  compact := isCompact_univ
  connected := isConnected_univ
  regular_closed := by simp
  boundary_chart := by
    intro x hx
    simp at hx

theorem roundSphereThree_secLower_zero :
    SecLower roundSphereThreeMetric 0 (Set.univ : Set RoundSphereThree) := by
  intro y hy v w
  rw [zero_mul, roundSphereThree_constant_curvature]
  have hcs := real_inner_mul_inner_self_le
    (dIncl (n := 3) y v) (dIncl (n := 3) y w)
  simp only [roundSphereThreeMetric, scaleMetric_inner, roundMetric_inner] at hcs ⊢
  nlinarith [hcs]

theorem roundSphereThree_curvatureOperatorLowerBoundAt (y : RoundSphereThree) :
    curvatureOperatorLowerBoundAt (I := I3) roundSphereThreeMetric y
      (metricAlgebraicCurvatureTensorAt (I := I3) (M := RoundSphereThree)
        roundSphereThreeMetric y) 0 := by
  simpa using (secLower_iff_curvatureOperatorLowerBoundAt (M := RoundSphereThree)
    roundSphereThreeMetric (by simp [ThreeSpace]) 0 Set.univ).mp
      roundSphereThree_secLower_zero y trivial

private theorem one_le_sqrt_three : (1 : ℝ) ≤ Real.sqrt 3 := by
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg 3]

theorem roundSphereThree_scalarDifferential_zero (x : RoundSphereThree)
    (v : TangentSpace I3 x) :
    scalarDifferential (I := I3)
      (roundSphereThreeSolution (RealTimeInterval.univ 0)) 0 x v = 0 := by
  simp only [scalarDifferential]
  have h : (fun y : RoundSphereThree =>
      (roundSphereThreeSolution (RealTimeInterval.univ 0)).scalar 0 y) = fun _ => 1 := by
    funext y
    exact roundSphereThree_solution_scalar _ _ y
  rw [h, mfderiv_const]
  rfl

theorem roundSphereThree_time_derivative_zero (x : RoundSphereThree) :
    derivWithin (fun s : ℝ =>
      (roundSphereThreeSolution (RealTimeInterval.univ 0)).scalar s x) (Set.Iic 0) 0 = 0 := by
  have h : (fun s : ℝ =>
      (roundSphereThreeSolution (RealTimeInterval.univ 0)).scalar s x) = fun _ => 1 := by
    funext s
    exact roundSphereThree_solution_scalar _ _ x
  rw [h]
  simp

theorem nonempty_roundComponent_roundSphereThree {eps : ℝ} (heps : 0 < eps)
    (x : RoundSphereThree) :
    Nonempty (RoundComponent (roundSphereThreeSolution (RealTimeInterval.univ 0))
      eps x 0 Set.univ) := by
  have hQ : 0 < (roundSphereThreeSolution (RealTimeInterval.univ 0)).scalar 0 x := by
    rw [roundSphereThree_solution_scalar]
    norm_num
  refine ⟨{
    Z := RoundSphereThree
    topology := inferInstance
    charted := inferInstance
    smooth := inferInstance
    t2 := inferInstance
    compact := inferInstance
    connected := inferInstance
    metric := roundSphereThreeMetric
    p := x
    scalar_one := roundSphereThree_scalar_one
    constant_curvature := roundSphereThree_constant_curvature
    map := PartialDiffeomorph.refl (I := I3) RoundSphereThree
    source_eq := rfl
    target_eq := rfl
    center_eq := rfl
    Q_pos := hQ
    comparison := ?_
    metric_bounds := ?_ }⟩
  · convert metricComparisonOnRefl (M := RoundSphereThree)
      (g := fun _ => roundSphereThreeMetric)
      Set.univ ({0} : Set ℝ) (⌈eps⁻¹⌉₊) heps using 1
    funext s
    apply SmoothRiemannianMetric.ext_inner
    intro y v w
    have hs : (roundSphereThreeSolution (RealTimeInterval.univ 0)).scalar 0 x = 1 :=
      roundSphereThree_solution_scalar _ _ x
    change (roundSphereThreeSolution (RealTimeInterval.univ 0)).scalar 0 x *
        roundSphereThreeMetric.inner y v w = roundSphereThreeMetric.inner y v w
    rw [hs, one_mul]
  · intro z v
    have hmap : ((↑(PartialDiffeomorph.refl (I := I3) RoundSphereThree).toPartialEquiv) :
        RoundSphereThree → RoundSphereThree) = id := by
      funext y
      rfl
    rw [hmap]
    simp only [mfderiv_id, ContinuousLinearMap.id_apply, id_eq]
    rw [roundSphereThree_solution_scalar]
    simp only [roundSphereThreeSolution, SolutionOn.const]
    simp only [one_mul]
    have hnn : 0 ≤ roundSphereThreeMetric.inner z v v :=
      metric_inner_self_nonneg roundSphereThreeMetric z v
    constructor <;> linarith

theorem exists_canonicalWitness_roundSphereThree (x : RoundSphereThree)
    {eps : ℝ} (heps : 0 < eps) (heps_one : eps < 1) :
    ∃ C1 C2 : ℝ, 1 ≤ C1 ∧ 1 ≤ C2 ∧
      Nonempty (CanonicalWitness (roundSphereThreeSolution (RealTimeInterval.univ 0))
        eps C1 C2 x 0) := by
  obtain ⟨R, hRpos, hRball⟩ := exists_roundSphereThree_ball_eq_univ x
  obtain ⟨RC⟩ := nonempty_roundComponent_roundSphereThree heps x
  have hQ : 0 < (roundSphereThreeSolution (RealTimeInterval.univ 0)).scalar 0 x := by
    rw [roundSphereThree_solution_scalar]
    norm_num
  have hRnonneg : 0 ≤ R := hRpos.le
  refine ⟨max R 1, Real.sqrt 3, le_max_right _ _, one_le_sqrt_three, ?_⟩
  refine ⟨{
    Q_pos := hQ
    time_mem := Set.mem_univ 0
    eps_pos := heps
    eps_lt_one := heps_one
    domain := roundSphereThreeCompactDomain
    center_inside := by
      change x ∈ interior (Set.univ : Set RoundSphereThree)
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
  · rw [roundSphereThree_solution_scalar]
    simp
  · rw [roundSphereThree_solution_scalar]
    simp
  · intro y hy
    exact Set.mem_univ y
  · intro y hy
    exact riemannianBallOf_mono (I := I3) roundSphereThreeMetric x
      (by
        have h1 : 0 ≤ max R 1 := le_trans zero_le_one (le_max_right _ _)
        have h2 : max R 1 ≤ 2 * max R 1 := by linarith
        exact (le_max_left R 1).trans h2)
      (hRball hy)
  · intro y hy
    rw [roundSphereThree_solution_scalar, roundSphereThree_solution_scalar]
    constructor
    · simpa using inv_le_one_of_one_le₀ one_le_sqrt_three
    · nlinarith [one_le_sqrt_three]
  · intro y hy
    rw [roundSphereThree_solution_scalar]
    have hnn : curvatureOperatorLowerBoundAt (I := I3)
        ((roundSphereThreeSolution (RealTimeInterval.univ 0)).base.metric 0) y
        (metricAlgebraicCurvatureTensorAt (I := I3) (M := RoundSphereThree)
          ((roundSphereThreeSolution (RealTimeInterval.univ 0)).base.metric 0) y) 0 := by
      change curvatureOperatorLowerBoundAt (I := I3) roundSphereThreeMetric y
        (metricAlgebraicCurvatureTensorAt (I := I3) (M := RoundSphereThree)
          roundSphereThreeMetric y) 0
      exact roundSphereThree_curvatureOperatorLowerBoundAt y
    have hbound := sqrt_rmNormSq_le_sqrt_three_mul_scalar_of_curvatureOperatorNonneg
      (S := roundSphereThreeSolution (RealTimeInterval.univ 0)) (by simp [ThreeSpace])
      0 y hnn
    simpa only [roundSphereThree_solution_scalar, one_mul] using hbound
  · intro v
    rw [roundSphereThree_scalarDifferential_zero]
    simp only [abs_zero]
    positivity
  · change |derivWithin
        (fun s => (roundSphereThreeSolution (RealTimeInterval.univ 0)).scalar s x)
        (Set.Iic 0) 0| ≤ Real.sqrt 3 *
      ((roundSphereThreeSolution (RealTimeInterval.univ 0)).scalar 0 x) ^ 2
    rw [roundSphereThree_time_derivative_zero]
    simp only [abs_zero]
    positivity

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
