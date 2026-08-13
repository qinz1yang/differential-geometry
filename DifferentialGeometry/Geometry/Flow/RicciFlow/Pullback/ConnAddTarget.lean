import DifferentialGeometry.Geometry.Exponential.LocalAddition

noncomputable section

open Bundle Manifold
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Pullback

open DifferentialGeometry
open DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [T2Space M]

noncomputable def localAddZeroCoord (p : M) : E × E :=
  extChartAt I.tangent
    (⟨connCompPt (I := I) p, (0 : E)⟩ :
      TangentBundle I (connCompOpen (I := I) p))
    (⟨connCompPt (I := I) p, (0 : E)⟩ :
      TangentBundle I (connCompOpen (I := I) p))

noncomputable def localAddTarget
    (g : SmoothRiemannianMetric I M) (p : M) : E × E → E :=
  fun z => (connAddChart (I := I) g p z).2

lemma localAddTarget_fd
    (g : SmoothRiemannianMetric I M) (p : M) (n : ℕ) (hn : 1 ≤ n) :
    HasFDerivAt (localAddTarget (I := I) g p)
      ((ContinuousLinearMap.snd ℝ E E).comp
        (unipotentCLE (E := E) : (E × E) →L[ℝ] (E × E)))
      (localAddZeroCoord (I := I) p) := by
  simpa only [localAddTarget, localAddZeroCoord] using
    (connAdd_fderiv (I := I) g p n hn).snd

lemma localAddTarget_vert
    (g : SmoothRiemannianMetric I M) (p : M) (n : ℕ) (hn : 1 ≤ n) (v : E) :
    fderiv ℝ (localAddTarget (I := I) g p)
        (localAddZeroCoord (I := I) p) (0, v) = v := by
  rw [(localAddTarget_fd (I := I) g p n hn).fderiv]
  simp [unipotentCLE, DifferentialGeometry.PhaseFlow.freeDiagCLE_apply]

end DifferentialGeometry.PDE.RicciFlow.Pullback

end
