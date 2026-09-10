import DifferentialGeometry.Geometry.Comparison.HopfRinow.Proper
import DifferentialGeometry.Geometry.Curvature.Metric.Defs
import DifferentialGeometry.Geometry.Metric.Completeness
import DifferentialGeometry.Bundle.FiberBundleHausdorff
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Filter Set
open scoped Topology

section ProperMetric

variable {X : Type*} [MetricSpace X] [ProperSpace X]

theorem exists_controlled_ball_of_pos
    {f : X → ℝ} (hf : Continuous f) (hnonneg : ∀ z, 0 ≤ f z)
    (y : X) (hy : 0 < f y) :
    ∃ (x : X) (r : ℝ), 0 < r ∧ r ≤ 1 / 2 ∧ 0 < f x ∧
      f y / 4 ≤ f x * r ^ 2 ∧
      ∀ z : X, dist z x < r → f z ≤ 4 * f x := by
  let F : X → ℝ := fun z => f z * (1 - dist y z) ^ 2
  have hF : Continuous F :=
    hf.mul ((continuous_const.sub (continuous_const.dist continuous_id)).pow 2)
  obtain ⟨x, hx, hmax⟩ := (isCompact_closedBall y 1).exists_isMaxOn
    ⟨y, by simp⟩ hF.continuousOn
  let sigma : ℝ := 1 - dist y x
  have hxle : dist y x ≤ 1 := by
    simpa only [Metric.mem_closedBall, dist_comm] using hx
  have hsigma : 0 ≤ sigma := sub_nonneg.mpr hxle
  have hsigma_le : sigma ≤ 1 := by
    dsimp only [sigma]
    linarith [dist_nonneg (x := y) (y := x)]
  have hweight : f y ≤ f x * sigma ^ 2 := by
    have hmaxy : F y ≤ F x := hmax (by simp : y ∈ Metric.closedBall y 1)
    simpa only [F, sigma, dist_self, sub_zero, one_pow, mul_one] using
      hmaxy
  have hsigma_pos : 0 < sigma := by
    by_contra hn
    have hz : sigma = 0 := le_antisymm (le_of_not_gt hn) hsigma
    rw [hz, zero_pow (by decide), mul_zero] at hweight
    exact (not_le_of_gt hy) hweight
  have hfx : 0 < f x :=
    (mul_pos_iff_of_pos_right (sq_pos_of_pos hsigma_pos)).mp (hy.trans_le hweight)
  refine ⟨x, sigma / 2, by positivity, by linarith, hfx, ?_, ?_⟩
  · nlinarith [hweight]
  · intro z hz
    have hz' : dist x z < sigma / 2 := by simpa only [dist_comm] using hz
    have htri := dist_triangle y x z
    have hzball : z ∈ Metric.closedBall y 1 := by
      rw [Metric.mem_closedBall, dist_comm]
      dsimp only [sigma] at hz'
      linarith
    have hslack : sigma / 2 ≤ 1 - dist y z := by
      dsimp only [sigma] at hz' ⊢
      linarith
    have hsquare : sigma ^ 2 / 4 ≤ (1 - dist y z) ^ 2 := by
      have h := mul_self_le_mul_self (by positivity : 0 ≤ sigma / 2) hslack
      nlinarith
    have hmaxz : f z * (1 - dist y z) ^ 2 ≤ f x * sigma ^ 2 := hmax hzball
    have hprod := mul_le_mul_of_nonneg_left hsquare (hnonneg z)
    apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hsigma_pos)).mp
    nlinarith [hmaxz, hprod]

theorem tendsto_dist_atTop_of_continuous_values_atTop
    {iota : Type*} {l : Filter iota} {f : X → ℝ} (hf : Continuous f)
    {x : iota → X} (hfx : Tendsto (fun i => f (x i)) l atTop) (p : X) :
    Tendsto (fun i => dist p (x i)) l atTop := by
  refine tendsto_atTop.2 fun B => ?_
  obtain ⟨C, hC⟩ := (isCompact_closedBall p (max B 0)).bddAbove_image hf.continuousOn
  filter_upwards [hfx.eventually_gt_atTop C] with i hi
  by_contra hd
  have hball : x i ∈ Metric.closedBall p (max B 0) := by
    rw [Metric.mem_closedBall, dist_comm]
    exact (le_of_lt (lt_of_not_ge hd)).trans (le_max_left B 0)
  exact (not_le_of_gt hi) (hC ⟨x i, hball, rfl⟩)

theorem exists_spatialPointSelection
    {f : X → ℝ} (hf : Continuous f) (hnonneg : ∀ z, 0 ≤ f z)
    (hunbounded : ¬ BddAbove (Set.range f)) (p : X) :
    ∃ (x : ℕ → X) (r : ℕ → ℝ),
      (∀ i, 0 < r i ∧ r i ≤ 1 / 2 ∧ 0 < f (x i)) ∧
      Tendsto (fun i => f (x i)) atTop atTop ∧
      Tendsto (fun i => f (x i) * r i ^ 2) atTop atTop ∧
      Tendsto (fun i => dist p (x i)) atTop atTop ∧
      Tendsto (fun i => dist p (x i) / r i) atTop atTop ∧
      ∀ i z, dist z (x i) < r i → f z ≤ 4 * f (x i) := by
  classical
  have hlarge (i : ℕ) : ∃ y : X, 4 * ((i : ℝ) + 1) < f y := by
    obtain ⟨b, ⟨y, rfl⟩, hb⟩ := not_bddAbove_iff.mp hunbounded (4 * ((i : ℝ) + 1))
    exact ⟨y, hb⟩
  choose y hy using hlarge
  have hypos (i : ℕ) : 0 < f (y i) := by
    linarith [hy i, Nat.cast_nonneg (α := ℝ) i]
  choose x r hrpos hrle hfx hweight hcontrol using
    fun i => exists_controlled_ball_of_pos hf hnonneg (y i) (hypos i)
  have hprod : Tendsto (fun i => f (x i) * r i ^ 2) atTop atTop := by
    apply tendsto_atTop_mono (fun i => ?_) (tendsto_natCast_atTop_atTop (R := ℝ))
    linarith [hy i, hweight i]
  have hvalue : Tendsto (fun i => f (x i)) atTop atTop := by
    apply tendsto_atTop_mono (fun i => ?_) hprod
    apply mul_le_of_le_one_right (hfx i).le
    nlinarith [hrpos i, hrle i]
  have hdist : Tendsto (fun i => dist p (x i)) atTop atTop :=
    tendsto_dist_atTop_of_continuous_values_atTop hf hvalue p
  have hratio : Tendsto (fun i => dist p (x i) / r i) atTop atTop := by
    apply tendsto_atTop_mono (fun i => ?_) hdist
    apply (le_div_iff₀ (hrpos i)).2
    exact mul_le_of_le_one_right dist_nonneg (by linarith [hrle i])
  exact ⟨x, r, fun i => ⟨hrpos i, hrle i, hfx i⟩,
    hvalue, hprod, hdist, hratio, hcontrol⟩

end ProperMetric

open Bundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.HopfRinow
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

omit [CompleteSpace E] in
theorem exists_spatialPointSelection_riemannian
    (g : SmoothRiemannianMetric I M) (hcomplete : RiemannianMetricComplete (I := I) g)
    {f : M → ℝ} (hf : Continuous f) (hnonneg : ∀ z, 0 ≤ f z)
    (hunbounded : ¬ BddAbove (Set.range f)) (p : M) :
    let d := fun x y : M => (riemannianEDistOf (I := I) g x y).toReal
    ∃ (x : ℕ → M) (r : ℕ → ℝ),
      (∀ i, 0 < r i ∧ r i ≤ 1 / 2 ∧ 0 < f (x i)) ∧
      Tendsto (fun i => f (x i)) atTop atTop ∧
      Tendsto (fun i => f (x i) * r i ^ 2) atTop atTop ∧
      Tendsto (fun i => d p (x i)) atTop atTop ∧
      Tendsto (fun i => d p (x i) / r i) atTop atTop ∧
      ∀ i z, d z (x i) < r i → f z ≤ 4 * f (x i) := by
  classical
  by_cases hz : Module.finrank ℝ E = 0
  · let : Subsingleton E := Module.finrank_zero_iff.mp hz
    let : Subsingleton H := I.injective.subsingleton
    let : DiscreteTopology H := inferInstance
    let : DiscreteTopology M := ChartedSpace.discreteTopology H M
    let : Subsingleton M := subsingleton_of_preconnected_totallyDisconnected
    apply (hunbounded ?_).elim
    refine ⟨f p, ?_⟩
    rintro b ⟨x, rfl⟩
    exact le_of_eq (congrArg f (Subsingleton.elim x p))
  · let : NeZero (Module.finrank ℝ E) := ⟨hz⟩
    let : IsManifold I 1 M := IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)
    let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
    let : T3Space M := inferInstance
    let : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
    let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
    let : CompleteSpace M := hcomplete.complete
    have hEnorm : IsMetricNorm (I := I) (M := M) g := fun x v =>
      tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) g x v
    let : MetricSpace M := riemMetricSpace (I := I) (M := M)
    let : ProperSpace M := properSpace_riemMetric (I := I) hcomplete.complete g hEnorm
    have hd (a b : M) : dist a b = (riemannianEDistOf (I := I) g a b).toReal := by
      rw [riemMetric_dist_eq (I := I),
        ← riemannianEDistOf_eq_riemannianEDist (I := I) g hEnorm]
    simpa only [hd] using exists_spatialPointSelection hf hnonneg hunbounded p

theorem exists_scalarSpatialPointSelection
    (g : SmoothRiemannianMetric I M) (hcomplete : RiemannianMetricComplete (I := I) g)
    (hnonneg : ∀ z, 0 ≤ metricScalarAt (I := I) g z)
    (hunbounded : ¬ BddAbove (Set.range (metricScalarAt (I := I) g))) (p : M) :
    let d := fun x y : M => (riemannianEDistOf (I := I) g x y).toReal
    ∃ (x : ℕ → M) (r : ℕ → ℝ),
      (∀ i, 0 < r i ∧ r i ≤ 1 / 2 ∧ 0 < metricScalarAt (I := I) g (x i)) ∧
      Tendsto (fun i => metricScalarAt (I := I) g (x i)) atTop atTop ∧
      Tendsto (fun i => metricScalarAt (I := I) g (x i) * r i ^ 2) atTop atTop ∧
      Tendsto (fun i => d p (x i)) atTop atTop ∧
      Tendsto (fun i => d p (x i) / r i) atTop atTop ∧
      ∀ i z, d z (x i) < r i → metricScalarAt (I := I) g z ≤
        4 * metricScalarAt (I := I) g (x i) := by
  exact exists_spatialPointSelection_riemannian g hcomplete
    (metricScalar_smooth (I := I) g).continuous hnonneg hunbounded p

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
