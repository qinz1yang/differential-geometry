import DifferentialGeometry.Geometry.Exponential.LocalAddition.Basic

noncomputable section

open Bundle Manifold
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Geometry.Riemannian.Exponential.LocalAddition

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [T2Space M]

noncomputable def zeroCoordinates (p : M) : E × E :=
  extChartAt I.tangent
    (⟨connectedComponentPoint (I := I) p, (0 : E)⟩ :
      TangentBundle I (connectedComponentOpen (I := I) p))
    (⟨connectedComponentPoint (I := I) p, (0 : E)⟩ :
      TangentBundle I (connectedComponentOpen (I := I) p))

noncomputable def targetCoordinates
    (g : SmoothRiemannianMetric I M) (p : M) : E × E → E :=
  fun z => (localAdditionCoordinateMap (I := I) g p z).2

lemma targetCoordinates_hasFDerivAt
    (g : SmoothRiemannianMetric I M) (p : M) (n : ℕ) (hn : 1 ≤ n) :
    HasFDerivAt (targetCoordinates (I := I) g p)
      ((ContinuousLinearMap.snd ℝ E E).comp
        (DifferentialGeometry.PhaseFlow.freeDiagCLE (E := E) : (E × E) →L[ℝ] (E × E)))
      (zeroCoordinates (I := I) p) := by
  let : NormedAddCommGroup (E × E) := Prod.normedAddCommGroup
  let : NormedSpace ℝ (E × E) := Prod.normedSpace
  change HasFDerivAt (fun z : E × E => (localAdditionCoordinateMap (I := I) g p z).2)
    ((ContinuousLinearMap.snd ℝ E E).comp
      (DifferentialGeometry.PhaseFlow.freeDiagCLE (E := E) : (E × E) →L[ℝ] (E × E)))
    (extChartAt I.tangent
      (⟨connectedComponentPoint (I := I) p, (0 : E)⟩ :
        TangentBundle I (connectedComponentOpen (I := I) p))
      (⟨connectedComponentPoint (I := I) p, (0 : E)⟩ :
        TangentBundle I (connectedComponentOpen (I := I) p)))
  exact (localAdditionCoordinateMap_hasFDerivAt (I := I) g p n hn).snd

lemma targetCoordinates_fderiv_vertical
    (g : SmoothRiemannianMetric I M) (p : M) (n : ℕ) (hn : 1 ≤ n) (v : E) :
    fderiv ℝ (targetCoordinates (I := I) g p)
        (zeroCoordinates (I := I) p) (0, v) = v := by
  rw [(targetCoordinates_hasFDerivAt (I := I) g p n hn).fderiv]
  simp [DifferentialGeometry.PhaseFlow.freeDiagCLE]

end DifferentialGeometry.Geometry.Riemannian.Exponential.LocalAddition

end
