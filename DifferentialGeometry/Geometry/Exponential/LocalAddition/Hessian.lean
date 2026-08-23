import DifferentialGeometry.Analysis.Calculus.SectionCompD2
import DifferentialGeometry.Geometry.Exponential.LocalAddition.VerticalInverse

noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Pullback

open DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [T2Space M]

noncomputable def connAddD2Rem
    (g : SmoothRiemannianMetric I M) (p : M)
    (v : E → E) (z a b : E) : E :=
  fderiv ℝ (fderiv ℝ (localAddTarget (I := I) g p)) (z, v z)
    (a, fderiv ℝ v z a) (b, fderiv ℝ v z b)

theorem connAddD2_split
    (g : SmoothRiemannianMetric I M) (p : M)
    (v : E → E) (z a b : E)
    (hF : ContDiffAt ℝ 2 (localAddTarget (I := I) g p) (z, v z))
    (hv : ContDiffAt ℝ 2 v z) :
    fderiv ℝ
        (fderiv ℝ (fun x => localAddTarget (I := I) g p (x, v x))) z a b =
      partialFDeriv₂ (localAddTarget (I := I) g p) z (v z)
          (fderiv ℝ (fderiv ℝ v) z a b) +
        connAddD2Rem (I := I) g p v z a b := by
  simpa only [connAddD2Rem] using
    sectionCompD2 (localAddTarget (I := I) g p) v z a b hF hv

theorem connAddD2_cancel
    (g : SmoothRiemannianMetric I M) (p : M)
    (v : E → E) (z a b : E)
    (hF : ContDiffAt ℝ 2 (localAddTarget (I := I) g p) (z, v z))
    (hv : ContDiffAt ℝ 2 v z)
    (hJ : (partialFDeriv₂
      (localAddTarget (I := I) g p) z (v z)).IsInvertible) :
    (partialFDeriv₂ (localAddTarget (I := I) g p) z (v z)).inverse
        (fderiv ℝ
            (fderiv ℝ (fun x => localAddTarget (I := I) g p (x, v x))) z a b -
          connAddD2Rem (I := I) g p v z a b) =
      fderiv ℝ (fderiv ℝ v) z a b := by
  simpa only [connAddD2Rem] using
    sectionD2_cancel (localAddTarget (I := I) g p) v z a b hF hv hJ

theorem exists_connAddD2
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ r > 0,
      IsCompact (Metric.closedBall (localAddZeroCoord (I := I) p) r) ∧
      ContinuousOn
        (fun w : E × E =>
          (partialFDeriv₂
            (localAddTarget (I := I) g p) w.1 w.2).inverse)
        (Metric.closedBall (localAddZeroCoord (I := I) p) r) ∧
      ∀ (v : E → E) (z a b : E),
        (z, v z) ∈ Metric.closedBall (localAddZeroCoord (I := I) p) r →
        ContDiffAt ℝ 2 (localAddTarget (I := I) g p) (z, v z) →
        ContDiffAt ℝ 2 v z →
        (partialFDeriv₂ (localAddTarget (I := I) g p) z (v z)).inverse
            (fderiv ℝ
                (fderiv ℝ
                  (fun x => localAddTarget (I := I) g p (x, v x))) z a b -
              connAddD2Rem (I := I) g p v z a b) =
          fderiv ℝ (fderiv ℝ v) z a b := by
  obtain ⟨r, hr, hcompact, hinv, hcont⟩ :=
    exists_connAdd_tube (I := I) g p
  refine ⟨r, hr, hcompact, hcont, ?_⟩
  intro v z a b hstate hF hv
  exact connAddD2_cancel (I := I) g p v z a b hF hv
    (hinv (z, v z) hstate)

end DifferentialGeometry.PDE.RicciFlow.Pullback

end
