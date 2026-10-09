import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.DoubleBoundaryFoldGeometry
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.Defs
import DifferentialGeometry.Topology.Manifold.OpenSubtypeDifferential

/-!
The actual physical inclusion and positive whole fold determine the orientation of the factor
map at the same physical point. Its subtype derivative is compared through the true open inclusion.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold

variable (M Q : ConnectedClosedOrientedManifold.{u} 3)
  (c : OrientedBallChart M.toClosedOrientedManifold)
  (F : c.toBallChart.interior → Q.Carrier)
  (hsF : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ F)
  (K : CompactCarrier.{u}) (ι : K.Carrier → M.Carrier)
  (hsι : ContMDiff K.model (𝓡 3) ∞ ι)
  (hO : ∀ k, ∃ L : TangentSpace K.model k ≃L[ℝ] TangentSpace (𝓡 3) (ι k),
    L.toContinuousLinearMap = mfderiv K.model (𝓡 3) ι k ∧
    Orientation.map (Fin 3) L.toLinearEquiv (K.orientation.orientation k) =
      M.orientation.orientation (ι k))
  (hmem : ∀ k, ι k ∈ c.toBallChart.interior)
  (A : K.Carrier → Q.Carrier)
  (hA : IsOrientedFold (C := K) (W := NoCuts.carrier Q) A)
  (hsquare : ∀ k, F ⟨ι k, hmem k⟩ = A k)

include hsι hO hA hsquare in
theorem restoredFactorPointOrientation (k : K.Carrier) :
    Orientation.map (Fin 3)
      ((hsF ⟨ι k, hmem k⟩).mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv
      (M.orientation.orientation (ι k)) = Q.orientation.orientation (F ⟨ι k, hmem k⟩) := by
  let liftι : K.Carrier → c.toBallChart.interior := fun x => ⟨ι x, hmem x⟩
  have hslift : ContMDiff K.model (𝓡 3) ∞ liftι :=
    (ContMDiff.subtypeVal_comp_iff c.toBallChart.interior liftι).mp hsι
  have hderiv : mfderiv K.model (𝓡 3) liftι k = mfderiv K.model (𝓡 3) ι k :=
    (DifferentialGeometry.Topology.Manifold.mfderiv_comp_open_val
      K.model (𝓡 3) c.toBallChart.interior liftι hslift k).symm
  have hcomp : F ∘ liftι = A := funext hsquare
  obtain ⟨L, hL, hoL⟩ := hO k
  obtain ⟨R, hR, hoR⟩ := hA k
  let D := ((hsF (liftι k)).mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv
  have hlin : L.toLinearEquiv.trans D = R := by
    apply LinearEquiv.ext
    intro v
    change mfderiv (𝓡 3) (𝓡 3) F (liftι k) (L v) = R v
    erw [DFunLike.congr_fun hL v]
    rw [← hderiv]
    erw [← mfderiv_comp_apply k (hsF.mdifferentiable (by simp) (liftι k))
      (hslift.mdifferentiable (by simp) k), hcomp]
    exact (hR v).symm
  change Orientation.map (Fin 3) D (M.orientation.orientation (ι k)) = _
  erw [← hoL, ← orientation_map_trans_fin_three L.toLinearEquiv D, hlin]
  erw [hsquare k]
  exact hoR

end GC.GraphManifold
