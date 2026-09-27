import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardParabolicSequence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardTerminalGeometry
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Scaling

noncomputable section

open Set Filter Manifold
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

@[simp] theorem standardParabolicSequence_atTime_zero
    (B : ℝ) (hB : 0 < B) (S : ℕ → PartialStandardSolution)
    (time : ℕ → ℝ) (point : ℕ → E3)
    (htime : ∀ i, time i ∈ (S i).domain ∧ 3 / 4 ≤ time i ∧ time i < 1) :
    (standardParabolicSequence B hB S time point htime).atTime 0 =
      (⟨fun i => ((S i).pointedFlow.atTime (time i)).repoint (point i)⟩ :
        PointedRiemannianSeq (𝓡 3)).scaleMetric B hB := by
  unfold FlowSequence.atTime PointedRiemannianSeq.scaleMetric
  congr 1
  funext i
  unfold PointedFlowData.atTime PointedRiemannianManifold.repoint
    PointedRiemannianManifold.scaleMetric
  congr 1
  change scaleMetric B hB ((S i).metric (time i + 0 / B)) =
    scaleMetric B hB ((S i).metric (time i))
  rw [zero_div, add_zero]


theorem exists_standard_parabolic_pointed_convergence_within_radius
    (B : ℝ) (hB : 0 < B) (S : ℕ → PartialStandardSolution)
    (time : ℕ → ℝ) (point : ℕ → E3) {rho : ℝ} (hrho : 0 < rho)
    (htime : ∀ i, time i ∈ (S i).domain ∧ 3 / 4 ≤ time i ∧ time i < 1)
    (hscalar : ∀ r : ℝ, 0 < r → r < rho → ∃ A : ℝ, ∀ᶠ i in atTop,
      ∀ y ∈ riemannianClosedBallOf ((S i).metric (time i)) (point i) r,
        metricScalarAt ((S i).metric (time i)) y ≤ A) :
    let X := (standardParabolicSequence B hB S time point htime).atTime 0
    ∃ phi : ℕ → ℕ, StrictMono phi ∧ ∃ radius : ℕ → ℝ,
      (∀ k, 0 < radius k ∧ radius k < Real.sqrt B * rho) ∧
      Tendsto radius atTop (𝓝 (Real.sqrt B * rho)) ∧
      ∃ L : PointedRiemannianManifold (𝓡 3),
      ∃ maps : PointedRiemannianConvergenceMaps X L phi,
      ∃ C : PointedRiemannianConverges X L phi maps,
        (∀ k, C.metrics.domain k = CanonicalMetricCompactness.canonicalSourceData maps k) ∧
        (∀ k, maps.target k = riemannianBallOf (X.obj (phi k)).metric
          (X.obj (phi k)).basepoint (radius k)) ∧
        (∀ x : L.M, riemannianEDistOf L.metric L.basepoint x <
          ENNReal.ofReal (Real.sqrt B * rho)) ∧
        (∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
          ∀ x ∈ maps.source k, ∀ v : TangentSpace (𝓡 3) x,
            (1 - eps) * L.metric.inner x v v ≤
              (X.obj (phi k)).metric.inner (maps.partialDiffeomorph k x)
                (mfderiv (𝓡 3) (𝓡 3) (maps.partialDiffeomorph k) x v)
                (mfderiv (𝓡 3) (𝓡 3) (maps.partialDiffeomorph k) x v) ∧
              (X.obj (phi k)).metric.inner (maps.partialDiffeomorph k x)
                (mfderiv (𝓡 3) (𝓡 3) (maps.partialDiffeomorph k) x v)
                (mfderiv (𝓡 3) (𝓡 3) (maps.partialDiffeomorph k) x v) ≤
              (1 + eps) * L.metric.inner x v v) ∧
        ∀ r : ℝ, 0 ≤ r → r < Real.sqrt B * rho →
          IsCompact (riemannianClosedBallOf L.metric L.basepoint r) := by
  dsimp only
  rw [standardParabolicSequence_atTime_zero]
  obtain ⟨phi, hphi, radius, hrad, hradlim, L, maps, C,
    hcanonical, htargets, hradial, hmetrics, hcompact⟩ :=
    exists_standard_terminal_pointed_convergence_within_radius S time point
      (by norm_num : (0 : ℝ) < 3 / 4) hrho htime hscalar
  have hsqrt : 0 < Real.sqrt B := Real.sqrt_pos.mpr hB
  refine ⟨phi, hphi, fun k => Real.sqrt B * radius k,
    fun k => ⟨mul_pos hsqrt (hrad k).1, mul_lt_mul_of_pos_left (hrad k).2 hsqrt⟩,
    hradlim.const_mul (Real.sqrt B), L.scaleMetric B hB, maps.scaleMetric B hB,
    C.scaleMetric B hB, ?_, ?_, ?_, ?_, ?_⟩
  · exact C.metrics.scaleMetric_domain_eq_canonical hcanonical B hB
  · intro k
    change maps.target k = riemannianBallOf (scaleMetric B hB ((S (phi k)).metric (time (phi k))))
      (point (phi k)) (Real.sqrt B * radius k)
    rw [riemannianBallOf_scaleMetric]
    exact htargets k
  · intro x
    change x ∈ riemannianBallOf (scaleMetric B hB L.metric) L.basepoint (Real.sqrt B * rho)
    rw [riemannianBallOf_scaleMetric]
    exact hradial x
  · intro eps heps
    obtain ⟨N, hN⟩ := hmetrics eps heps
    refine ⟨N, fun k hk x hx v => ?_⟩
    obtain ⟨hlow, hupp⟩ := hN k hk x hx v
    change (1 - eps) * (B * L.metric.inner x v v) ≤
        B * ((S (phi k)).metric (time (phi k))).inner (maps.partialDiffeomorph k x)
          (mfderiv (𝓡 3) (𝓡 3) (maps.partialDiffeomorph k) x v)
          (mfderiv (𝓡 3) (𝓡 3) (maps.partialDiffeomorph k) x v) ∧
      B * ((S (phi k)).metric (time (phi k))).inner (maps.partialDiffeomorph k x)
          (mfderiv (𝓡 3) (𝓡 3) (maps.partialDiffeomorph k) x v)
          (mfderiv (𝓡 3) (𝓡 3) (maps.partialDiffeomorph k) x v) ≤
        (1 + eps) * (B * L.metric.inner x v v)
    constructor
    · simpa only [mul_left_comm B] using mul_le_mul_of_nonneg_left hlow hB.le
    · simpa only [mul_left_comm B] using mul_le_mul_of_nonneg_left hupp hB.le
  · intro r hr hrrho
    change IsCompact (riemannianClosedBallOf (scaleMetric B hB L.metric) L.basepoint r)
    have hcancel : Real.sqrt B * (r / Real.sqrt B) = r := mul_div_cancel₀ r hsqrt.ne'
    have hball := riemannianClosedBallOf_scaleMetric B hB L.metric L.basepoint (r / Real.sqrt B)
    rw [hcancel] at hball
    rw [hball]
    exact hcompact (r / Real.sqrt B) (div_nonneg hr hsqrt.le)
      ((div_lt_iff₀ hsqrt).mpr (by simpa only [mul_comm] using hrrho))

end DifferentialGeometry.PDE.RicciFlow
