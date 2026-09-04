import DifferentialGeometry.Analysis.Calculus.SecondDerivative.SectionComposition
import DifferentialGeometry.Geometry.Exponential.LocalAddition.VerticalInverse

noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Geometry.Riemannian.Exponential.LocalAddition

open DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [T2Space M]

noncomputable def secondDerivativeRemainder
    (g : SmoothRiemannianMetric I M) (p : M)
    (v : E → E) (z a b : E) : E :=
  fderiv ℝ (fderiv ℝ (targetCoordinates (I := I) g p)) (z, v z)
    (a, fderiv ℝ v z a) (b, fderiv ℝ v z b)

theorem secondDerivative_section_eq
    (g : SmoothRiemannianMetric I M) (p : M)
    (v : E → E) (z a b : E)
    (hF : ContDiffAt ℝ 2 (targetCoordinates (I := I) g p) (z, v z))
    (hv : ContDiffAt ℝ 2 v z) :
    fderiv ℝ
        (fderiv ℝ (fun x => targetCoordinates (I := I) g p (x, v x))) z a b =
      partialFDeriv₂ (targetCoordinates (I := I) g p) z (v z)
          (fderiv ℝ (fderiv ℝ v) z a b) +
        secondDerivativeRemainder (I := I) g p v z a b := by
  simpa only [secondDerivativeRemainder] using
    sectionCompD2 (targetCoordinates (I := I) g p) v z a b hF hv

theorem inverse_partialFDeriv₂_secondDerivative_sub_remainder
    (g : SmoothRiemannianMetric I M) (p : M)
    (v : E → E) (z a b : E)
    (hF : ContDiffAt ℝ 2 (targetCoordinates (I := I) g p) (z, v z))
    (hv : ContDiffAt ℝ 2 v z)
    (hJ : (partialFDeriv₂
      (targetCoordinates (I := I) g p) z (v z)).IsInvertible) :
    (partialFDeriv₂ (targetCoordinates (I := I) g p) z (v z)).inverse
        (fderiv ℝ
            (fderiv ℝ (fun x => targetCoordinates (I := I) g p (x, v x))) z a b -
          secondDerivativeRemainder (I := I) g p v z a b) =
      fderiv ℝ (fderiv ℝ v) z a b := by
  simpa only [secondDerivativeRemainder] using
    sectionD2_cancel (targetCoordinates (I := I) g p) v z a b hF hv hJ

theorem exists_secondDerivative_recovery_on_closedBall
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ r > 0,
      IsCompact (Metric.closedBall (zeroCoordinates (I := I) p) r) ∧
      ContinuousOn
        (fun w : E × E =>
          (partialFDeriv₂
            (targetCoordinates (I := I) g p) w.1 w.2).inverse)
        (Metric.closedBall (zeroCoordinates (I := I) p) r) ∧
      ∀ (v : E → E) (z a b : E),
        (z, v z) ∈ Metric.closedBall (zeroCoordinates (I := I) p) r →
        ContDiffAt ℝ 2 (targetCoordinates (I := I) g p) (z, v z) →
        ContDiffAt ℝ 2 v z →
        (partialFDeriv₂ (targetCoordinates (I := I) g p) z (v z)).inverse
            (fderiv ℝ
                (fderiv ℝ
                  (fun x => targetCoordinates (I := I) g p (x, v x))) z a b -
              secondDerivativeRemainder (I := I) g p v z a b) =
          fderiv ℝ (fderiv ℝ v) z a b := by
  obtain ⟨r, hr, hcompact, hinv, hcont⟩ :=
    exists_partialFDeriv₂_targetCoordinates_inverse_on_closedBall (I := I) g p
  refine ⟨r, hr, hcompact, hcont, ?_⟩
  intro v z a b hstate hF hv
  exact inverse_partialFDeriv₂_secondDerivative_sub_remainder (I := I) g p v z a b hF hv
    (hinv (z, v z) hstate)

end DifferentialGeometry.Geometry.Riemannian.Exponential.LocalAddition

end
