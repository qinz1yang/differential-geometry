import DifferentialGeometry.Geometry.Exponential.LocalAddition

/-!
# Target coordinate of the component-local addition

This file extracts the four target-coordinate facts needed by the harmonic-map
gauge from the much larger principal-operator module.  It depends only on the
component-local intrinsic addition and therefore gives the vertical-inverse and
Hessian layers a small, independently checkable geometric base.
-/

noncomputable section

open Bundle Manifold
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Pullback

open DifferentialGeometry
open DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [T2Space M]

/-- The tangent-bundle chart coordinate of the zero vector over `p` used by
the component-local addition. -/
noncomputable def localAddZeroCoord (p : M) : E × E :=
  extChartAt I.tangent
    (⟨connCompPt (I := I) p, (0 : E)⟩ :
      TangentBundle I (connCompOpen (I := I) p))
    (⟨connCompPt (I := I) p, (0 : E)⟩ :
      TangentBundle I (connCompOpen (I := I) p))

/-- The target-manifold coordinate of the component-local exponential
addition. -/
noncomputable def localAddTarget
    (g : SmoothRiemannianMetric I M) (p : M) : E × E → E :=
  fun z => (connAddChart (I := I) g p z).2

/-- At the zero section, the derivative of the target coordinate is
`(a,b) ↦ a+b`. -/
lemma localAddTarget_fd
    (g : SmoothRiemannianMetric I M) (p : M) (n : ℕ) (hn : 1 ≤ n) :
    HasFDerivAt (localAddTarget (I := I) g p)
      ((ContinuousLinearMap.snd ℝ E E).comp
        (unipotentCLE (E := E) : (E × E) →L[ℝ] (E × E)))
      (localAddZeroCoord (I := I) p) := by
  simpa only [localAddTarget, localAddZeroCoord] using
    (connAdd_fderiv (I := I) g p n hn).snd

/-- The target coordinate has identity derivative in a purely vertical
direction at the zero section. -/
lemma localAddTarget_vert
    (g : SmoothRiemannianMetric I M) (p : M) (n : ℕ) (hn : 1 ≤ n) (v : E) :
    fderiv ℝ (localAddTarget (I := I) g p)
        (localAddZeroCoord (I := I) p) (0, v) = v := by
  rw [(localAddTarget_fd (I := I) g p n hn).fderiv]
  simp [unipotentCLE, DifferentialGeometry.PhaseFlow.freeDiagCLE_apply]

end DifferentialGeometry.PDE.RicciFlow.Pullback

end
