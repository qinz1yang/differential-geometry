import DifferentialGeometry.Geometry.Exponential.Flat.DeckTranslation
import DifferentialGeometry.Geometry.Exponential.Flat.IsometricDeckAction
import Mathlib.Analysis.Calculus.FDeriv.Affine
import Mathlib.Analysis.Calculus.AddTorsor.AffineMap

/-!
# Orientation of actual affine deck isometries

An affine isometry commuting with a local diffeomorphism into an oriented three-manifold
has positive linear determinant. The same statement applies to every member of the actual
isometric deck affine group, using its original deck-map square.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.FlatSurface

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {Y : Type*} [instY : TopologicalSpace Y] [instCharts : ChartedSpace E3 Y]
  [instManifold : IsManifold (𝓡 3) ∞ Y]

theorem affineDeck_det_pos (o : ManifoldOrientation (𝓡 3) Y 3)
    (p : E3 → Y) (hp : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ p)
    (a : E3 ≃ᵃⁱ[ℝ] E3) (hsquare : ∀ x, p (a x) = p x) :
    0 < LinearMap.det a.linearIsometryEquiv.toLinearEquiv.toLinearMap := by
  let A := a.toContinuousAffineEquiv.toContinuousAffineMap
  have ha : MDifferentiable (𝓡 3) (𝓡 3) (a : E3 → E3) :=
    (contMDiff_iff_contDiff.mpr (show ContDiff ℝ ∞ A from A.contDiff)).mdifferentiable
      (by simp)
  have hbij := fun x => ((hp x).mfderivToContinuousLinearEquiv (by simp)).bijective
  let so := smoothOrientationOfManifoldOrientation (𝓡 3) (by simpa using o)
  have hpos := det_mfderiv_pos_of_comp_eq hp.contMDiff hbij so ha hsquare 0
  change 0 < LinearMap.det ((fderiv ℝ A 0) : E3 →ₗ[ℝ] E3) at hpos
  rw [A.fderiv] at hpos
  exact hpos

theorem isometricDeckAffineGroup_det_pos (o : ManifoldOrientation (𝓡 3) Y 3)
    (p : E3 → Y) (hp : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ p)
    (hIso : ∀ γ : coveringDeckGroup p, Isometry (γ.1 : E3 → E3))
    (a : isometricDeckAffineGroup p hIso) :
    0 < LinearMap.det (a : E3 ≃ᵃⁱ[ℝ] E3).linearIsometryEquiv.toLinearEquiv.toLinearMap := by
  apply affineDeck_det_pos o p hp a.val
  intro x
  obtain ⟨γ, hγ⟩ := a.property
  rw [← hγ]
  exact coveringDeckGroup_map γ x

end DifferentialGeometry.Geometry.FlatSurface
