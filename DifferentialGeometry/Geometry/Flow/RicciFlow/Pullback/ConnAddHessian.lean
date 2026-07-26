import DifferentialGeometry.Analysis.Calculus.SectionCompD2
import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.ConnAddVertInv

/-!
# Full-state Hessian split for the local addition

This file specializes the Banach section-composition chain rule to the target
coordinate of the component-local exponential addition.  It records only a
fixed-chart calculus identity: the unique term containing `D²v` is multiplied
by the vertical derivative, and the inverse vertical derivative cancels that
factor exactly.
-/

noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Pullback

open DifferentialGeometry
open DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [T2Space M]

/-- The first-jet remainder in the Hessian of a local-addition section
composition.  Its dependence on `v` is only through `v z` and `Dv z`. -/
noncomputable def connAddD2Rem
    (g : SmoothRiemannianMetric I M) (p : M)
    (v : E → E) (z a b : E) : E :=
  fderiv ℝ (fderiv ℝ (localAddTarget (I := I) g p)) (z, v z)
    (a, fderiv ℝ v z a) (b, fderiv ℝ v z b)

/-- The exact full-state Hessian split for a fixed local-addition chart.  The
displayed vertical term is the only occurrence of the second derivative of
`v`; `connAddD2Rem` uses only its first jet. -/
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

/-- On the invertible vertical-derivative locus, subtracting the first-jet
remainder and applying the inverse recovers `D²v` exactly. -/
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

/-- A fixed chart admits one compact state tube on which the inverse vertical
derivative is continuous and the exact Hessian cancellation holds at every
`C²` section state in the tube. -/
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
