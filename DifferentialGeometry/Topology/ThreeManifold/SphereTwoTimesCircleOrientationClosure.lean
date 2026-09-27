import DifferentialGeometry.Topology.Manifold.ProductOrientationCongruence
import DifferentialGeometry.Topology.Manifold.StereographicAntipodal
import DifferentialGeometry.Topology.ThreeManifold.PoincareStandardFactorOrientation

set_option autoImplicit false
noncomputable section

open Manifold Metric
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

theorem sphereTwoTimesCircleOrientationClosure_holds : sphereTwoTimesCircleOrientationClosure := by
  let A := Manifold.sphereAntipodalDiffeomorph (E := EuclideanSpace ℝ (Fin 3)) (n := 2)
  let B := Diffeomorph.refl (𝓡 1) (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) ∞
  have hA : A.preservesOrientation (sphereOrientation 2 (by decide)).opposite
      (sphereOrientation 2 (by decide)) := by
    simpa only [ManifoldOrientation.opposite_opposite] using
      Diffeomorph.preservesOrientation_opposite
        sphereAntipodalDiffeomorph_preservesOrientation_opposite
  have hB : B.preservesOrientation (sphereOrientation 1 (by decide))
      (sphereOrientation 1 (by decide)) := Diffeomorph.preservesOrientation_refl _
  have hρ := Diffeomorph.prodCongr_preservesOrientation (I := 𝓡 2) (J := 𝓡 1)
    (I' := 𝓡 2) (J' := 𝓡 1) (m := 2) (n := 1)
    (oM := (sphereOrientation 2 (by decide)).opposite) (oN := sphereOrientation 1 (by decide))
    (oM' := sphereOrientation 2 (by decide)) (oN' := sphereOrientation 1 (by decide))
    (by decide) (by decide) A B hA hB
  rw [← productOrientation_opposite (I := 𝓡 2) (J := 𝓡 1) (by decide) (by decide)
    (sphereOrientation 2 (by decide)) (sphereOrientation 1 (by decide))] at hρ
  exact ⟨A.prodCongr B, hρ⟩

end DifferentialGeometry.Topology
