import DifferentialGeometry.Topology.Manifold.ClosedOriented
import DifferentialGeometry.Topology.Manifold.Homeomorph.Transport
import DifferentialGeometry.Topology.Manifold.DiffeomorphPullbackOrientation
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.SeamOrientationGlue

set_option autoImplicit false
noncomputable section
open Set Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

universe u v

namespace ConnectedClosedOrientedManifold

variable (N : ConnectedClosedOrientedManifold.{v} 3) {X : Type u} [TopologicalSpace X] (h : X ≃ₜ N.Carrier)

private def pullbackSmoothOrientation :
    let _ := DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace (H := E3) h
    Manifold.SmoothOrientation (𝓡 3) X := by
  let _ := DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace (H := E3) h
  let _ : IsManifold (𝓡 3) ∞ X :=
    DifferentialGeometry.Manifold.Homeomorph.instIsManifoldPullback (I := 𝓡 3) (n := ∞) h
  let F := DifferentialGeometry.Manifold.Homeomorph.pullbackDiffeomorph (I := 𝓡 3) (n := ∞) h
  let so := Manifold.smoothOrientationOfManifoldOrientation (𝓡 3)
    (OrientationAssembly.reindexManifoldOrientation (𝓡 3) (finCongr N.orientation.dimension_eq.symm) N.orientation)
  exact Manifold.pullbackSmoothOrientation (𝓡 3) (𝓡 3) F F.contMDiff
    (fun x => (F.mfderivToContinuousLinearEquiv (by simp) x).bijective) so

private def pullbackOrientation :
    let _ := DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace (H := E3) h
    ManifoldOrientation (𝓡 3) X 3 := by
  let _ := DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace (H := E3) h
  let _ : IsManifold (𝓡 3) ∞ X :=
    DifferentialGeometry.Manifold.Homeomorph.instIsManifoldPullback (I := 𝓡 3) (n := ∞) h
  let O := Classical.choose (Manifold.exists_manifoldOrientation_eq_of_smoothOrientation (𝓡 3)
    (pullbackSmoothOrientation N h))
  exact OrientationAssembly.reindexManifoldOrientation (𝓡 3) (finCongr (by simp : Module.finrank ℝ E3 = 3)) O

def pullback : ConnectedClosedOrientedManifold.{u} 3 where
  Carrier := X
  topology := inferInstance
  charts := DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace (H := E3) h
  smooth := DifferentialGeometry.Manifold.Homeomorph.instIsManifoldPullback (I := 𝓡 3) (n := ∞) h
  hausdorff := h.symm.t2Space
  compact := h.symm.compactSpace
  connected := h.connectedSpace_iff.mpr inferInstance
  orientation := pullbackOrientation N h

def pullbackOrientedDiffeomorph :
    ClosedOrientedManifold.OrientedDiffeomorph (pullback N h).toClosedOrientedManifold N.toClosedOrientedManifold := by
  let _ := DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace (H := E3) h
  let _ : IsManifold (𝓡 3) ∞ X :=
    DifferentialGeometry.Manifold.Homeomorph.instIsManifoldPullback (I := 𝓡 3) (n := ∞) h
  let F := DifferentialGeometry.Manifold.Homeomorph.pullbackDiffeomorph (I := 𝓡 3) (n := ∞) h
  refine ⟨F, ?_⟩
  let so := Manifold.smoothOrientationOfManifoldOrientation (𝓡 3)
    (OrientationAssembly.reindexManifoldOrientation (𝓡 3) (finCongr N.orientation.dimension_eq.symm) N.orientation)
  let hbij : ∀ x, Bijective (mfderiv (𝓡 3) (𝓡 3) F x) :=
    fun x => (F.mfderivToContinuousLinearEquiv (by simp) x).bijective
  apply Manifold.Diffeomorph.preservesOrientation_of_pullbackSmoothOrientation F F.contMDiff hbij so
    (pullbackOrientation N h) N.orientation
  · intro y
    rfl
  · intro x
    change Orientation.reindex ℝ E3 _
      ((Classical.choose (Manifold.exists_manifoldOrientation_eq_of_smoothOrientation (𝓡 3)
        (pullbackSmoothOrientation N h))).orientation x) = _
    rw [Classical.choose_spec (Manifold.exists_manifoldOrientation_eq_of_smoothOrientation (𝓡 3)
      (pullbackSmoothOrientation N h))]
    rfl

theorem pullbackOrientedDiffeomorph_apply (x : X) :
    (pullbackOrientedDiffeomorph N h).val x = h x := rfl

end ConnectedClosedOrientedManifold
end DifferentialGeometry.Topology
