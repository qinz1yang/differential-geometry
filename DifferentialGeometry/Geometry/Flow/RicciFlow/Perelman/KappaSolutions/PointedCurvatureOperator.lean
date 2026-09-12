import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedSectionalCurvature
import DifferentialGeometry.Geometry.Curvature.Algebraic.CurvatureOperatorConeMetric

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Manifold Filter
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff _root_.Topology BigOperators

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
  {L : PointedRiemannianManifold.{u, uE, uH} (I := I)} {subseq : ℕ → ℕ}
  {Phi : PointedRiemannianConvergenceMaps (I := I) X L subseq}

local instance pointedOperatorLimitTopology : TopologicalSpace L.M := L.topology
local instance pointedOperatorLimitCharted : ChartedSpace H L.M := L.charted
local instance pointedOperatorLimitSmooth : IsManifold I ∞ L.M := L.smooth
local instance pointedOperatorLimitT2 : T2Space L.M := L.t2
local instance pointedOperatorLimitSigma : SigmaCompactSpace L.M := L.sigmaCompact

local instance pointedOperatorApproxTopology (k : ℕ) :
    TopologicalSpace (X.obj k).M := (X.obj k).topology
local instance pointedOperatorApproxCharted (k : ℕ) :
    ChartedSpace H (X.obj k).M := (X.obj k).charted
local instance pointedOperatorApproxSmooth (k : ℕ) :
    IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
local instance pointedOperatorApproxT2 (k : ℕ) : T2Space (X.obj k).M := (X.obj k).t2
local instance pointedOperatorApproxSigma (k : ℕ) :
    SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact

theorem pointedCurvatureOperatorQuadraticEval_tendsto_of_canonical_metric_convergence
    (hconv : ∀ K : Set L.M, IsCompact K →
      metricSourceConvergesOn (I := I) Phi
        (CanonicalMetricCompactness.canonicalSourceData Phi) K 2)
    (x : L.M) (n : ℕ) (c : Fin n → ℝ) (v w : Fin n → TangentSpace I x) :
    Tendsto (fun k => algebraicCurvatureOperatorQuadraticEval (I := I)
        (metricAlgebraicCurvatureTensorAt (I := I)
          (X.obj (subseq k)).metric (Phi.map k x)) c
        (fun i => mfderiv I I (Phi.map k) x (v i))
        (fun i => mfderiv I I (Phi.map k) x (w i))) atTop
      (𝓝 (algebraicCurvatureOperatorQuadraticEval (I := I)
        (metricAlgebraicCurvatureTensorAt (I := I) L.metric x) c v w)) := by
  change Tendsto (fun k => ∑ i : Fin n, ∑ j : Fin n, c i * c j *
      metricRm04StandardAt (I := I) (X.obj (subseq k)).metric (Phi.map k x)
        (mfderiv I I (Phi.map k) x (v i)) (mfderiv I I (Phi.map k) x (w i))
        (mfderiv I I (Phi.map k) x (w j)) (mfderiv I I (Phi.map k) x (v j))) atTop
    (𝓝 (∑ i : Fin n, ∑ j : Fin n, c i * c j *
      metricRm04StandardAt (I := I) L.metric x (v i) (w i) (w j) (v j)))
  refine tendsto_finsetSum _ fun i _ => ?_
  refine tendsto_finsetSum _ fun j _ => ?_
  exact (pointedRm04_tendsto_of_canonical_metric_convergence
    hconv x (v i) (w i) (w j) (v j)).const_mul (c i * c j)

theorem curvatureOperator_nonnegative_of_pointed_canonical_convergence
    (hconv : ∀ K : Set L.M, IsCompact K →
      metricSourceConvergesOn (I := I) Phi
        (CanonicalMetricCompactness.canonicalSourceData Phi) K 2)
    (hoperator : ∀ K : Set L.M, IsCompact K →
      ∀ᶠ k in atTop, ∀ y ∈ K, y ∈ Phi.source k →
        metricAlgebraicCurvatureTensorAt (I := I)
            (X.obj (subseq k)).metric (Phi.map k y) ∈
          algebraicCurvatureOperatorNonnegativeCone (I := I)) :
    ∀ x : L.M, metricAlgebraicCurvatureTensorAt (I := I) L.metric x ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I) := by
  intro x
  apply mem_algebraicCurvatureOperatorNonnegativeCone.mpr
  intro n c v w
  have hc := pointedCurvatureOperatorQuadraticEval_tendsto_of_canonical_metric_convergence
    hconv x n c v w
  obtain ⟨k0, hk0⟩ := Phi.source_subset (K := {x}) isCompact_singleton
  have hs : ∀ᶠ k in atTop, x ∈ Phi.source k := by
    filter_upwards [eventually_ge_atTop k0] with k hk
    exact hk0 k hk (Set.mem_singleton x)
  apply ge_of_tendsto hc
  filter_upwards [hoperator {x} isCompact_singleton, hs] with k hk hx
  exact (mem_algebraicCurvatureOperatorNonnegativeCone.mp
    (hk x (Set.mem_singleton x) hx)) n c
      (fun i => mfderiv I I (Phi.map k) x (v i))
      (fun i => mfderiv I I (Phi.map k) x (w i))

theorem curvatureOperator_nonnegative_of_canonical_metricCGConvergence
    (C : MetricConvergenceData (I := I) Phi)
    (hdomain : ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData Phi k)
    (hoperator : ∀ K : Set L.M, IsCompact K →
      ∀ᶠ k in atTop, ∀ y ∈ K, y ∈ Phi.source k →
        metricAlgebraicCurvatureTensorAt (I := I)
            (X.obj (subseq k)).metric (Phi.map k y) ∈
          algebraicCurvatureOperatorNonnegativeCone (I := I)) :
    ∀ x : L.M, metricAlgebraicCurvatureTensorAt (I := I) L.metric x ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I) := by
  have hD : C.domain = CanonicalMetricCompactness.canonicalSourceData Phi := funext hdomain
  have hc : ∀ K : Set L.M, IsCompact K →
      metricSourceConvergesOn (I := I) Phi
        (CanonicalMetricCompactness.canonicalSourceData Phi) K 2 := by
    intro K hK
    have ht := C.converges K hK 2
    rw [hD] at ht
    exact ht
  exact curvatureOperator_nonnegative_of_pointed_canonical_convergence hc hoperator

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
