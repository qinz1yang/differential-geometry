import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Compactness.Construction
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Metric.Proper

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open scoped Manifold ContDiff Topology

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

theorem exists_canonicalMetricCompactness_of_local_jets
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconnected : ∀ i : ℕ,
      letI : TopologicalSpace (X.obj i).M := (X.obj i).topology
      ConnectedSpace (X.obj i).M)
    (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (Ψ : letI : ∀ j, TopologicalSpace (X.obj (σ j)).M := fun j => (X.obj (σ j)).topology
         letI : ∀ j, ChartedSpace H (X.obj (σ j)).M := fun j => (X.obj (σ j)).charted
         letI : ∀ j, IsManifold I ∞ (X.obj (σ j)).M := fun j => (X.obj (σ j)).smooth
         ∀ j, PartialDiffeomorph I I ((X.obj (σ j)).M) ((X.obj (σ (j + 1))).M)
           (∞ : WithTop ℕ∞))
    (hbase : ∀ j, Ψ j (X.obj (σ j)).basepoint = (X.obj (σ (j + 1))).basepoint)
    (D : letI : ∀ j, TopologicalSpace (X.obj (σ j)).M := fun j => (X.obj (σ j)).topology
         letI : ∀ j, ChartedSpace H (X.obj (σ j)).M := fun j => (X.obj (σ j)).charted
         letI : ∀ j, IsManifold I ∞ (X.obj (σ j)).M := fun j => (X.obj (σ j)).smooth
         letI : ∀ j, SigmaCompactSpace (X.obj (σ j)).M := fun j => (X.obj (σ j)).sigmaCompact
         letI : ∀ j, T2Space (X.obj (σ j)).M := fun j => (X.obj (σ j)).t2
         letI : ∀ j, MetricSpace (X.obj (σ j)).M := fun j => ProperMetricOn.alignedMetricSpace
           (X.obj (σ j)) (properMetricOn (I := I) (X.obj (σ j))
             (hcomplete.complete (σ j)) (hconnected (σ j)))
         ConvergentMetricChain (I := I) (fun j => (X.obj (σ j)).basepoint) Ψ
           (fun j => (X.obj (σ j)).metric)) :
    Nonempty (CanonicalMetricCompactness (I := I) X) :=
  ⟨(connectedCanonicalMetricCompactnessOfConvergentChain (I := I)
      (fun k => properMetricOn (I := I) (X.obj k) (hcomplete.complete k) (hconnected k))
      σ hσ Ψ hbase D).canonical⟩

end CheegerGromovCompactness
end DifferentialGeometry
