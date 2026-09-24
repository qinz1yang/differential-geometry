import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Distance.TerminalScalar
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CompactScalarMinimum
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperator.Nonnegative
import DifferentialGeometry.Geometry.Metric.Distance.Finiteness

set_option autoImplicit false
noncomputable section
open Set
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem BackwardExtension.metricDistance_sub_terminal_le_of_left_endpoint_ge
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    {X : NormalizedSequence.{u} eps kappa sigma Phi} {L : TerminalLimit X}
    {T a : ℝ} (ha : a < 0) (hTa : T ≤ a)
    (B : BackwardExtension L (RealTimeInterval.closed a 0 ha.le))
    {Q : ℝ} (hQ : 0 ≤ Q) (hterminal : ∀ x : L.space.M, metricScalarAt L.space.metric x ≤ Q)
    {t : ℝ} (ht : t ∈ Icc a 0) (x y : L.space.M) :
    0 ≤ metricDistance (B.solution.base.metric t) x y - metricDistance L.space.metric x y ∧
      metricDistance (B.solution.base.metric t) x y - metricDistance L.space.metric x y ≤
        (20 / 3 : ℝ) * Real.sqrt (2 * (-T) * Q) * Real.sqrt (-T) := by
  have hoperator : ∀ r ∈ Icc a 0, ∀ z : L.space.M,
      metricAlgebraicCurvatureTensorAt (B.solution.base.metric r) z ∈
        algebraicCurvatureOperatorNonnegativeCone := by
    intro r hr z
    apply (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff_sectional
      (B.solution.base.metric r) z (by simp [ThreeSpace])).mpr
    intro v w
    have hvec : (fun i => ![v, w, w, v] i) = vec4 (I := I3) v w w v := by
      funext i
      fin_cases i <;> simp [vec4]
    simpa only [zero_mul, metricRm04StandardAt_apply, hvec] using
      B.nonnegative r hr z (mem_univ z) v w
  obtain ⟨C, hC⟩ := B.compact_time_bound a 0 ha.le Subset.rfl
  have h := ricciFlow_additive_distance_bound_of_terminal_scalar B.solution B.isSolution
    (by simp [ThreeSpace]) L.connected ha Subset.rfl Subset.rfl
    (fun r hr => ⟨(B.complete r hr).complete⟩) ⟨C, hC⟩ hoperator hQ
    (fun z => by
      change metricScalarAt (B.solution.base.metric 0) z ≤ Q
      rw [B.terminal]
      exact hterminal z) ht x y
  rw [B.terminal] at h
  have h' : 0 ≤ metricDistance (B.solution.base.metric t) x y - metricDistance L.space.metric x y ∧
      metricDistance (B.solution.base.metric t) x y - metricDistance L.space.metric x y ≤
        (20 / 3 : ℝ) * Real.sqrt (2 * (-a) * Q) *
          (Real.sqrt (-a) - Real.sqrt (t - a)) := by
    simpa only [ThreeSpace, finrank_euclideanSpace, Fintype.card_fin, Nat.cast_ofNat,
      show (3 : ℝ) - 1 = 2 by norm_num, zero_sub, metricDistance] using h
  refine ⟨h'.1, h'.2.trans ?_⟩
  have hcoeff : (20 / 3 : ℝ) * Real.sqrt (2 * (-a) * Q) ≤
      (20 / 3 : ℝ) * Real.sqrt (2 * (-T) * Q) :=
    mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by nlinarith)) (by norm_num)
  have hroot : Real.sqrt (-a) ≤ Real.sqrt (-T) := Real.sqrt_le_sqrt (by linarith)
  calc
    (20 / 3 : ℝ) * Real.sqrt (2 * (-a) * Q) *
        (Real.sqrt (-a) - Real.sqrt (t - a)) ≤
      (20 / 3 : ℝ) * Real.sqrt (2 * (-a) * Q) * Real.sqrt (-a) :=
      mul_le_mul_of_nonneg_left (sub_le_self _ (Real.sqrt_nonneg _)) (by positivity)
    _ ≤ (20 / 3 : ℝ) * Real.sqrt (2 * (-T) * Q) * Real.sqrt (-T) :=
      mul_le_mul hcoeff hroot (Real.sqrt_nonneg _) (by positivity)

theorem exists_uniform_scalar_bounded_point_and_diameter_of_compact
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    {X : NormalizedSequence.{u} eps kappa sigma Phi} (L : TerminalLimit X)
    [CompactSpace L.space.M] (T : ℝ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (a : ℝ) (ha : a < 0), T ≤ a →
      ∀ B : BackwardExtension L (RealTimeInterval.closed a 0 ha.le),
        ∀ t ∈ Icc a 0, (∃ z : L.space.M, B.solution.scalar t z ≤ 1) ∧
          ∀ x y : L.space.M, metricDistance (B.solution.base.metric t) x y ≤ D := by
  let _ : ConnectedSpace L.space.M := L.connected
  let _ : EMetricSpace L.space.M := L.space.emetricSpace
  have hfinite (x y : L.space.M) : edist x y ≠ ⊤ :=
    riemannianEDistOf_ne_top L.space.metric x y
  let _ : MetricSpace L.space.M := EMetricSpace.toMetricSpace hfinite
  have hdist (x y : L.space.M) : dist x y = metricDistance L.space.metric x y := rfl
  obtain ⟨R, hR, hball⟩ :=
    (isCompact_univ : IsCompact (univ : Set L.space.M)).isBounded.subset_closedBall_lt
      0 L.space.basepoint
  have hdiam (x y : L.space.M) : metricDistance L.space.metric x y ≤ 2 * R := by
    have hx := hball (mem_univ x)
    have hy := hball (mem_univ y)
    rw [Metric.mem_closedBall] at hx hy
    have htri := dist_triangle x L.space.basepoint y
    rw [dist_comm L.space.basepoint y] at htri
    rw [← hdist]
    linarith
  obtain ⟨Q₀, hQ₀⟩ := L.scalar_bound
  let Q := max Q₀ 0
  have hQ : 0 ≤ Q := le_max_right _ _
  have hterminal : ∀ x : L.space.M, metricScalarAt L.space.metric x ≤ Q :=
    fun x => (hQ₀ x).trans (le_max_left _ _)
  let D := 2 * R + (20 / 3 : ℝ) * Real.sqrt (2 * (-T) * Q) * Real.sqrt (-T)
  refine ⟨D, by dsimp [D]; positivity, ?_⟩
  intro a ha hTa B t ht
  refine ⟨B.exists_scalar_le_one_of_compact ht, ?_⟩
  intro x y
  have hd := (B.metricDistance_sub_terminal_le_of_left_endpoint_ge ha hTa hQ hterminal ht x y).2
  have hxy := hdiam x y
  dsimp [D]
  linarith

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
