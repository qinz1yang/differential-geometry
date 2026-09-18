import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.PullbackConnectionBounds
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Derivative.GeodesicAcceleration

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : PointedFlowSeq (I := I)} {P : PointedRiemannianManifold (I := I)}
  {subseq : ℕ → ℕ}

theorem FlowMetricConvergenceData.exists_eventually_reference_geodesic_acceleration_bound
    (Φ : PointedCGHMaps (I := I) X P subseq)
    (R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M)
    (bf : BumpFamily (I := I) Φ) (hsrc : SourceIsSigmaCompact Φ) (htgt : TargetIsSigmaCompact Φ)
    {a b : ℝ} (co : FlowMetricConvergenceData (I := I) Φ R bf hsrc htgt a b)
    (hG : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      MetricFamilySmoothOn X.D co.gInf)
    (hreg : Icc a b ⊆ X.D.regular)
    {K : Set P.M} (hK : letI : TopologicalSpace P.M := P.topology; IsCompact K) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ k ≥ N, ∀ t ∈ Icc a b,
      ∀ (beta : ℝ → P.M) (r : ℝ), beta r ∈ K → IsGeodesicAt R beta r →
        let G := gSeqExt Φ R bf hsrc htgt (co.φ k) t
        Real.sqrt (G.inner (beta r)
          (covDerivAlong G beta (fun s ↦ mfderiv 𝓘(ℝ, ℝ) I beta s (1 : ℝ)) r)
          (covDerivAlong G beta (fun s ↦ mfderiv 𝓘(ℝ, ℝ) I beta s (1 : ℝ)) r)) ≤
          C * R.inner (beta r)
            (mfderiv 𝓘(ℝ, ℝ) I beta r (1 : ℝ))
            (mfderiv 𝓘(ℝ, ℝ) I beta r (1 : ℝ)) := by
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : T2Space P.M := P.t2
  let : IsManifold I ∞ P.M := P.smooth
  let : SigmaCompactSpace P.M := P.sigmaCompact
  have hcarrier : Icc a b ⊆ X.D.carrier :=
    fun _ ht ↦ X.D.regular_subset (hreg ht)
  obtain ⟨L, hL, hlimit⟩ :=
    exists_metric_uniform_equivalent_on_compact_of_metricFamilySmoothOn
      co.gInf hG isCompact_Icc hcarrier hK R
  obtain ⟨J, hJ, N₁, hN₁⟩ :=
    FlowMetricConvergenceData.exists_eventually_metricCovDerivNorm_bound
      Φ R bf hsrc htgt co hG hreg hK 1
  obtain ⟨N₂, hN₂⟩ :=
    FlowMetricConvergenceData.exists_eventually_metricUniformEquivalentOn
      Φ R bf hsrc htgt co hK hL hlimit
  let A : ℝ := 3 / 2 * (2 * L) ^ 3 * J
  let C : ℝ := Real.sqrt (2 * L) * A
  have hLp : 0 < 2 * L := by linarith
  have hA : 0 < A := by dsimp [A]; positivity
  have hC : 0 < C := mul_pos (Real.sqrt_pos.mpr hLp) hA
  refine ⟨C, hC, max N₁ N₂, ?_⟩
  intro k hk t ht beta r hx hbeta
  let G := gSeqExt Φ R bf hsrc htgt (co.φ k) t
  have hk₁ : N₁ ≤ k := (le_max_left _ _).trans hk
  have hk₂ : N₂ ≤ k := (le_max_right _ _).trans hk
  have hEq : MetricUniformEquivalentOn K R G (2 * L) := hN₂ k hk₂ t ht
  have hJet : MetricCovDerivOrderBoundOn K 1 G R J :=
    fun x hx ↦ hN₁ k hk₁ t ht 1 le_rfl x hx
  have hconnection (u w : TangentSpace I (beta r)) :
      Real.sqrt (R.inner (beta r)
        (CovariantDerivative.difference (metricCov G) (metricCov R) (beta r) u w)
        (CovariantDerivative.difference (metricCov G) (metricCov R) (beta r) u w)) ≤
        A * Real.sqrt (R.inner (beta r) u u) * Real.sqrt (R.inner (beta r) w w) := by
    simpa only [A, metricCov, mul_assoc, mul_comm, mul_left_comm] using
      connectionDifference_gJet_le hEq hJet hx w u
  have hacc := covDerivAlong_velocity_norm_le_of_reference_geodesic
    R G beta r hbeta hLp.le hA.le
    (fun z ↦ (hEq.2 (beta r) hx z).2) hconnection le_rfl
  rw [Real.sq_sqrt (metric_inner_self_nonneg R (beta r)
    (mfderiv 𝓘(ℝ, ℝ) I beta r (1 : ℝ)))] at hacc
  simpa only [C, mul_assoc] using hacc

theorem
  FlowMetricConvergenceData.exists_eventually_reference_geodesic_acceleration_bound_of_speed_bound
    (Φ : PointedCGHMaps (I := I) X P subseq)
    (R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M)
    (bf : BumpFamily (I := I) Φ) (hsrc : SourceIsSigmaCompact Φ) (htgt : TargetIsSigmaCompact Φ)
    {a b : ℝ} (co : FlowMetricConvergenceData (I := I) Φ R bf hsrc htgt a b)
    (hG : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      MetricFamilySmoothOn X.D co.gInf)
    (hreg : Icc a b ⊆ X.D.regular)
    {K : Set P.M} (hK : letI : TopologicalSpace P.M := P.topology; IsCompact K) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ k ≥ N, ∀ t ∈ Icc a b,
      ∀ (beta : ℝ → P.M) (r : ℝ), beta r ∈ K → IsGeodesicAt R beta r →
      ∀ B : ℝ,
        Real.sqrt (R.inner (beta r)
          (mfderiv 𝓘(ℝ, ℝ) I beta r (1 : ℝ))
          (mfderiv 𝓘(ℝ, ℝ) I beta r (1 : ℝ))) ≤ B →
        let G := gSeqExt Φ R bf hsrc htgt (co.φ k) t
        Real.sqrt (G.inner (beta r)
          (covDerivAlong G beta (fun s ↦ mfderiv 𝓘(ℝ, ℝ) I beta s (1 : ℝ)) r)
          (covDerivAlong G beta (fun s ↦ mfderiv 𝓘(ℝ, ℝ) I beta s (1 : ℝ)) r)) ≤ C * B ^ 2 := by
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : T2Space P.M := P.t2
  let : IsManifold I ∞ P.M := P.smooth
  let : SigmaCompactSpace P.M := P.sigmaCompact
  obtain ⟨C, hC, N, hN⟩ :=
    FlowMetricConvergenceData.exists_eventually_reference_geodesic_acceleration_bound
      Φ R bf hsrc htgt co hG hreg hK
  refine ⟨C, hC, N, ?_⟩
  intro k hk t ht beta r hpoint hbeta B hspeed
  have hB : 0 ≤ B := (Real.sqrt_nonneg _).trans hspeed
  have hbase := hN k hk t ht beta r hpoint hbeta
  have hsq :
      (Real.sqrt (R.inner (beta r)
        (mfderiv 𝓘(ℝ, ℝ) I beta r (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) I beta r (1 : ℝ)))) ^ 2 ≤ B ^ 2 :=
    (sq_le_sq₀ (Real.sqrt_nonneg _) hB).mpr hspeed
  have hspeedSq :
      R.inner (beta r)
        (mfderiv 𝓘(ℝ, ℝ) I beta r (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) I beta r (1 : ℝ)) ≤ B ^ 2 := by
    simpa only [Real.sq_sqrt (metric_inner_self_nonneg R (beta r)
      (mfderiv 𝓘(ℝ, ℝ) I beta r (1 : ℝ)))] using hsq
  exact hbase.trans (mul_le_mul_of_nonneg_left hspeedSq (by positivity))

end DifferentialGeometry.CheegerGromovCompactness
