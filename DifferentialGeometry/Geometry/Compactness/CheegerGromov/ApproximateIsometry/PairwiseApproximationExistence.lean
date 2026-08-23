import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.BoundedGeometryPairwiseApproximation




set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open scoped ContDiff Manifold

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

theorem MetricCompactBase.exists_partial_approximate_isometry_subsequence
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (b : MetricCompactBase (I := I) X)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M) :
    ∃ ψ : Nat → Nat, StrictMono ψ ∧
      let Xψ := X.subseq ψ
      let Pψ : ∀ k : Nat, ProperMetricOn (I := I) (Xψ.obj k) :=
        fun k => properMetricOn (I := I) (Xψ.obj k)
          (hcomplete.complete (ψ k)) (hconn (ψ k))
      ∀ (r : Real), 0 < r → ∀ (ε : Real), 0 < ε → ε < 1 → ∀ (p : Nat),
        ∃ k₀ : Nat, ∀ k ℓ : Nat, k₀ ≤ k → k₀ ≤ ℓ →
          letI : TopologicalSpace (Xψ.obj k).M := (Xψ.obj k).topology
          letI : ChartedSpace H (Xψ.obj k).M := (Xψ.obj k).charted
          letI : IsManifold I ∞ (Xψ.obj k).M := (Xψ.obj k).smooth
          letI : T2Space (Xψ.obj k).M := (Xψ.obj k).t2
          letI : SigmaCompactSpace (Xψ.obj k).M := (Xψ.obj k).sigmaCompact
          letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (Xψ.obj k).M :=
            (Xψ.obj k).smooth
          letI : TopologicalSpace (Xψ.obj ℓ).M := (Xψ.obj ℓ).topology
          letI : ChartedSpace H (Xψ.obj ℓ).M := (Xψ.obj ℓ).charted
          letI : IsManifold I ∞ (Xψ.obj ℓ).M := (Xψ.obj ℓ).smooth
          letI : T2Space (Xψ.obj ℓ).M := (Xψ.obj ℓ).t2
          letI : SigmaCompactSpace (Xψ.obj ℓ).M := (Xψ.obj ℓ).sigmaCompact
          letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (Xψ.obj ℓ).M :=
            (Xψ.obj ℓ).smooth
          letI : MetricSpace (Xψ.obj k).M := (Pψ k).ms
          letI : MetricSpace (Xψ.obj ℓ).M := (Pψ ℓ).ms
          ∃ Φ : PartialDiffeomorph I I (Xψ.obj k).M (Xψ.obj ℓ).M
              (∞ : WithTop ℕ∞),
            Metric.closedBall (Xψ.obj k).basepoint r ⊆ Φ.source ∧
            Φ (Xψ.obj k).basepoint = (Xψ.obj ℓ).basepoint ∧
            Nonempty (PartialDiffeomorphMetricApproximation (I := I)
              (Metric.closedBall (Xψ.obj k).basepoint r)
              ε p Φ (Xψ.obj k).metric (Xψ.obj ℓ).metric) := by
  obtain ⟨ψ, hψ, hraw⟩ := b.exists_pairwise_approximate_isometry_subsequence hcomplete hconn
  refine ⟨ψ, hψ, ?_⟩
  dsimp only
  intro r hr ε hε hε1 p
  exact PairwiseApproximateIsometryInput.exists_partial_approximate_isometry
    (X := X.subseq ψ)
    (fun k => properMetricOn (I := I) ((X.subseq ψ).obj k)
      (hcomplete.complete (ψ k)) (hconn (ψ k)))
    hraw r hr ε hε hε1 p

end HCGCompactness
end DifferentialGeometry
