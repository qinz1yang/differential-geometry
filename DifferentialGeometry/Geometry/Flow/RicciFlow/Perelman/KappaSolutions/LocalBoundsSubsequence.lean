import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Bounds.LocalJetSubsequence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.LocalInjectivityRadiusDecay

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open Bundle Set Manifold Metric Filter
open scoped Manifold ContDiff Topology ENNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Curvature

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]

theorem exists_subsequence_curvDerivNorm_bound_and_injectivityRadius_on_ball_of_local_jets
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k : ℕ,
      let _ : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (hinj : BaseInjBound (I := I) X)
    (hjets : ∀ A : ℝ, 0 < A → ∀ p : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ i in atTop,
        let _ : TopologicalSpace (X.obj i).M := (X.obj i).topology
        let _ : ChartedSpace H (X.obj i).M := (X.obj i).charted
        let _ : IsManifold I ∞ (X.obj i).M := (X.obj i).smooth
        let _ : T2Space (X.obj i).M := (X.obj i).t2
        let _ : SigmaCompactSpace (X.obj i).M := (X.obj i).sigmaCompact
        ∀ x : (X.obj i).M,
          riemannianEDistOf (I := I) (X.obj i).metric (X.obj i).basepoint x ≤
            ENNReal.ofReal A → curvDerivNorm (I := I) p (X.obj i).metric x ≤ C)
    (A : ℝ) (hA : 0 < A) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        (∀ j : ℕ,
          letI : TopologicalSpace (X.obj (φ j)).M := (X.obj (φ j)).topology
          letI : EMetricSpace (X.obj (φ j)).M := (X.obj (φ j)).emetricSpace (I := I)
          ∀ x : (X.obj (φ j)).M,
            edist (X.obj (φ j)).basepoint x ≤ ENNReal.ofReal A →
              HasInjRadiusAt (I := I) (X.obj (φ j)) x ρ) ∧
        ∃ C : ℕ → ℕ → ℝ, (∀ n p : ℕ, 0 ≤ C n p) ∧
          ∀ n p j : ℕ, n + p ≤ j →
            letI : TopologicalSpace (X.obj (φ j)).M := (X.obj (φ j)).topology
            letI : ChartedSpace H (X.obj (φ j)).M := (X.obj (φ j)).charted
            letI : IsManifold I ∞ (X.obj (φ j)).M := (X.obj (φ j)).smooth
            letI : T2Space (X.obj (φ j)).M := (X.obj (φ j)).t2
            letI : SigmaCompactSpace (X.obj (φ j)).M := (X.obj (φ j)).sigmaCompact
            ∀ x : (X.obj (φ j)).M,
              riemannianEDistOf (I := I) (X.obj (φ j)).metric (X.obj (φ j)).basepoint x ≤
                ENNReal.ofReal (n : ℝ) →
              curvDerivNorm (I := I) p (X.obj (φ j)).metric x ≤ C n p := by
  obtain ⟨ρ, hρ, hρev⟩ :=
    exists_uniform_injectivity_radius_on_ball_of_local_jets X hcomplete hconn hinj hjets A hA
  obtain ⟨φ, hφ, hφρ, C, hC0, hC⟩ :=
    exists_subsequence_curvDerivNorm_ball_le_of_local_jets_and_eventually X hjets
      (Q := fun j =>
        letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
        letI : EMetricSpace (X.obj j).M := (X.obj j).emetricSpace (I := I)
        ∀ x : (X.obj j).M,
          edist (X.obj j).basepoint x ≤ ENNReal.ofReal A →
            HasInjRadiusAt (I := I) (X.obj j) x ρ)
      hρev
  exact ⟨ρ, hρ, φ, hφ, hφρ, C, hC0, hC⟩

end CheegerGromovCompactness
end DifferentialGeometry
