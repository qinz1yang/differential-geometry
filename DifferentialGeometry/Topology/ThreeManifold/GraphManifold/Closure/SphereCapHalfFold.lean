import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.MixedBoundary
import DifferentialGeometry.Topology.Manifold.HalfLine

/-!
Smooth full-height spherical half-to-signed coordinates, with bijective actual differentials.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold

def sphereCapHalfSignedCoordinate (σ : ℝ)
    (p : ClosureSphere.{u} × EuclideanHalfSpace 1) : ClosureSphere.{u} × ℝ :=
  (p.1, σ * p.2.val 0)

theorem sphereCapHalfSignedCoordinate_contMDiff (σ : ℝ) :
    ContMDiff sphereHalfCollarModel sphereSignedCollarModel ∞
      (sphereCapHalfSignedCoordinate σ) :=
  contMDiff_fst.prodMk (contMDiff_const.mul
    (contMDiff_halfSpaceOneCoordinate.comp contMDiff_snd))

theorem sphereCapHalfSignedCoordinate_bijective {σ : ℝ} (hσ : σ ≠ 0)
    (p : ClosureSphere.{u} × EuclideanHalfSpace 1) :
    Bijective (mfderiv sphereHalfCollarModel sphereSignedCollarModel
      (sphereCapHalfSignedCoordinate σ) p) := by
  have hi := injective_mfderiv_scaledHalfSpaceOneProductCoordinate (𝓡 2) hσ p
  refine ⟨hi, ?_⟩
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (mfderiv sphereHalfCollarModel sphereSignedCollarModel
      (sphereCapHalfSignedCoordinate σ) p).toLinearMap) (by
        change Module.finrank ℝ
          (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 1)) =
            Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ)
        simp)).mp hi

theorem sphereCapHalfSignedCoordinate_mem {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    {p : ClosureSphere.{u} × EuclideanHalfSpace 1} (hp : p ∈ sphereHalfCollarSource) :
    sphereCapHalfSignedCoordinate σ p ∈ sphereSignedCollarSource := by
  have hs : 0 ≤ p.2.val 0 := p.2.property
  have ht : p.2.val 0 < 1 := hp
  rcases hσ with h | h <;> rw [h]
  · exact ⟨trivial, by change -1 < 1 * p.2.val 0; linarith,
      by change 1 * p.2.val 0 < 1; simpa using ht⟩
  · exact ⟨trivial, by change -1 < -1 * p.2.val 0; linarith,
      by change -1 * p.2.val 0 < 1; linarith⟩

end GC.GraphManifold
