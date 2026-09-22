import DifferentialGeometry.Topology.Manifold.SmoothOrientationComposition
import DifferentialGeometry.Topology.Manifold.SmoothOrientationComparison
import DifferentialGeometry.Topology.Manifold.SmoothOrientationCompatible

noncomputable section

open Manifold
open scoped Manifold ContDiff

namespace IsLocalDiffeomorph

variable {E H K X Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E K}
  [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
  [TopologicalSpace Y] [ChartedSpace K Y] [IsManifold J ∞ Y]
  {f : X → Y} {n : ℕ}

theorem orientation_agreement_isLocallyConstant
    (hf : IsLocalDiffeomorph I J ∞ f)
    (oX : DifferentialGeometry.ManifoldOrientation I X n)
    (oY : DifferentialGeometry.ManifoldOrientation J Y n) :
    IsLocallyConstant (fun x => Orientation.map (Fin n)
      ((hf x).mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv (oX.orientation x) =
        oY.orientation (f x)) := by
  have hd := oX.dimension_eq
  subst n
  let sX := DifferentialGeometry.Topology.Manifold.smoothOrientationOfManifoldOrientation I oX
  let sY := DifferentialGeometry.Topology.Manifold.smoothOrientationOfManifoldOrientation J oY
  let hb := fun x => ((hf x).mfderivToContinuousLinearEquiv (by simp)).bijective
  let sP := DifferentialGeometry.Topology.Manifold.pullbackSmoothOrientation I J f hf.contMDiff hb sY
  have hc := DifferentialGeometry.Topology.Manifold.smoothOrientation_agreement_locallyConstant I sP sX
  have heq : (fun x => sP.val x = sX.val x) =
      (fun x => Orientation.map (Fin (Module.finrank ℝ E))
        ((hf x).mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv (oX.orientation x) =
          oY.orientation (f x)) := by
    funext x
    apply propext
    have h := DifferentialGeometry.Topology.Manifold.pullbackSmoothOrientation_eq_iff
      I J f hf.contMDiff hb sY sX x
    rw [DifferentialGeometry.Topology.Manifold.tangentOrientationEquiv_self] at h
    have hlin : (DifferentialGeometry.Topology.Manifold.differentialEquivOfBijective I J f hb x).toLinearEquiv =
        ((hf x).mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv := by
      apply LinearEquiv.ext
      intro w
      rfl
    rw [hlin] at h
    exact h
  exact heq ▸ hc

end IsLocalDiffeomorph
