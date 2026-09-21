import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedScalarConvergence

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter Manifold Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Tensor0SBundle
open scoped _root_.Topology ContDiff Manifold

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

private local instance pointedCompactScalarManifoldOne {P : Type*} [TopologicalSpace P]
    [ChartedSpace H P] [IsManifold I ∞ P] : IsManifold I 1 P :=
  IsManifold.of_le (I := I) (M := P) (n := ∞) (by decide)

variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
  {L : PointedRiemannianManifold.{u, uE, uH} (I := I)} {subseq : ℕ → ℕ}
  (Phi : PointedRiemannianConvergenceMaps (I := I) X L subseq)

private local instance pointedCompactScalarLimitTopology : TopologicalSpace L.M := L.topology
private local instance pointedCompactScalarLimitCharted : ChartedSpace H L.M := L.charted
private local instance pointedCompactScalarLimitSmooth : IsManifold I ∞ L.M := L.smooth
private local instance pointedCompactScalarLimitT2 : T2Space L.M := L.t2
private local instance pointedCompactScalarLimitSigma : SigmaCompactSpace L.M := L.sigmaCompact

private local instance pointedCompactScalarApproxTopology (k : ℕ) :
    TopologicalSpace (X.obj k).M := (X.obj k).topology
private local instance pointedCompactScalarApproxCharted (k : ℕ) :
    ChartedSpace H (X.obj k).M := (X.obj k).charted
private local instance pointedCompactScalarApproxSmooth (k : ℕ) :
    IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
private local instance pointedCompactScalarApproxT2 (k : ℕ) : T2Space (X.obj k).M := (X.obj k).t2
private local instance pointedCompactScalarApproxSigma (k : ℕ) :
    SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact

variable {Phi}

theorem pointedScalar_uniform_on_compact_of_canonical_domains
    (C : MetricConvergenceData (I := I) Phi)
    (hcanonical : ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData Phi k)
    (K : Set L.M) (hK : IsCompact K) :
    ∀ epsilon : ℝ, 0 < epsilon → ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
      K ⊆ Phi.source k ∧ ∀ x ∈ K,
        |metricScalarAt (I := I) (X.obj (subseq k)).metric (Phi.map k x) -
          metricScalarAt (I := I) L.metric x| < epsilon := by
  have hconv := C.converges K hK 2
  have hdomain : C.domain = CanonicalMetricCompactness.canonicalSourceData Phi := funext hcanonical
  rw [hdomain] at hconv
  have hU := pointedScalar_tendstoUniformlyOn_of_canonical_metric_convergence hK hconv
  obtain ⟨N, hN⟩ := Phi.source_subset hK
  intro epsilon hepsilon
  apply eventually_atTop.mp
  filter_upwards [eventually_ge_atTop N,
    Metric.tendstoUniformlyOn_iff.mp hU epsilon hepsilon] with k hk herr
  refine ⟨hN k hk, fun x hx => ?_⟩
  have h := herr x hx
  rwa [dist_comm, Real.dist_eq] at h

theorem exists_pointed_scalar_bound_on_compact
    (C : MetricConvergenceData (I := I) Phi)
    (hcanonical : ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData Phi k)
    (K : Set L.M) (hK : IsCompact K) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ k in atTop, K ⊆ Phi.source k ∧
      ∀ x ∈ K, |metricScalarAt (I := I) (X.obj (subseq k)).metric (Phi.map k x)| ≤ B := by
  obtain ⟨R, hR⟩ := (hK.image (metricScalar_smooth (I := I) L.metric).continuous.abs).bddAbove
  obtain ⟨k0, hk0⟩ := pointedScalar_uniform_on_compact_of_canonical_domains
    C hcanonical K hK 1 zero_lt_one
  refine ⟨max R 0 + 1, by positivity, Filter.eventually_atTop.2 ⟨k0, fun k hk => ?_⟩⟩
  refine ⟨(hk0 k hk).1, fun x hx => ?_⟩
  have herr := (hk0 k hk).2 x hx
  have hlim : |metricScalarAt (I := I) L.metric x| ≤ max R 0 :=
    (hR ⟨x, hx, rfl⟩).trans (le_max_left _ _)
  calc
    |metricScalarAt (I := I) (X.obj (subseq k)).metric (Phi.map k x)| =
        |(metricScalarAt (I := I) (X.obj (subseq k)).metric (Phi.map k x) -
          metricScalarAt (I := I) L.metric x) + metricScalarAt (I := I) L.metric x| := by
      rw [sub_add_cancel]
    _ ≤ |metricScalarAt (I := I) (X.obj (subseq k)).metric (Phi.map k x) -
          metricScalarAt (I := I) L.metric x| + |metricScalarAt (I := I) L.metric x| :=
      abs_add_le _ _
    _ ≤ max R 0 + 1 := by linarith

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
