import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.RelativeCaps
import DifferentialGeometry.Topology.Manifold.ClosedCellPunctured
import DifferentialGeometry.Topology.Manifold.OpenSubtypeDiffeomorph
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph

/-!
A genuine full normalized half collar of the real closed ball, with exact radial and zero maps.
-/

set_option autoImplicit false

noncomputable section

open Set Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold

local instance sphereCapBallCharts : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  Handle.closedCellChartedSpaceSucc 2

local instance sphereCapBallSmooth : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) :=
  Handle.closedCellIsManifold 2

private abbrev sphereCapPuncturedBall : TopologicalSpace.Opens (ClosedCell 3) :=
  ⟨{x | x.val ≠ 0}, isOpen_ne_fun continuous_subtype_val continuous_const⟩

private def sphereCapBallDiffeomorph :
    (ClosureSphere.{u} × EuclideanHalfSpace 1) ≃ₘ⟮sphereHalfCollarModel, 𝓡∂ 3⟯
      sphereCapPuncturedBall :=
  ((uliftDiffeomorph (𝓡 2) SphereTwo).symm.prodCongr
    (Diffeomorph.refl (𝓡∂ 1) (EuclideanHalfSpace 1) ∞)).trans
      (closedCellPuncturedDiffeomorph 2)

private theorem sphereCapPuncturedBall_nonempty : Nonempty sphereCapPuncturedBall := by
  let z : SphereTwo := Classical.choice inferInstance
  exact ⟨closedCellPuncturedDiffeomorph 2 (z, halfZero)⟩

def sphereCapBallCollar : PartialDiffeomorph sphereHalfCollarModel (𝓡∂ 3)
    (ClosureSphere.{u} × EuclideanHalfSpace 1) (ClosedCell 3) ∞ :=
  (sphereCapBallDiffeomorph.toPartialDiffeomorph.trans
    (DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph (𝓡∂ 3)
      sphereCapPuncturedBall sphereCapPuncturedBall_nonempty)).restrict sphereHalfCollarSource
        (isOpen_lt ((EuclideanSpace.proj 0).continuous.comp
          (continuous_subtype_val.comp continuous_snd)) continuous_const)

theorem sphereCapBallCollar_source :
    sphereCapBallCollar.source = sphereHalfCollarSource := by
  ext p
  change (p ∈ univ ∧ sphereCapBallDiffeomorph p ∈ univ) ∧ p ∈ sphereHalfCollarSource ↔ _
  simp

theorem sphereCapBallCollar_apply (p : ClosureSphere.{u} × EuclideanHalfSpace 1) :
    (sphereCapBallCollar p).val = (1 + p.2.val 0)⁻¹ • p.1.down.val := rfl

theorem sphereCapBallCollar_norm (p : ClosureSphere.{u} × EuclideanHalfSpace 1) :
    ‖(sphereCapBallCollar p).val‖ = (1 + p.2.val 0)⁻¹ :=
  closedCellPuncturedDiffeomorph_norm 2 (p.1.down, p.2)

theorem sphereCapBallCollar_zero (z : ClosureSphere.{u}) :
    sphereCapBallCollar (z, halfZero) = closureSphereToBall z := by
  apply Subtype.ext
  rw [sphereCapBallCollar_apply]
  change (1 + 0 : ℝ)⁻¹ • z.down.val = z.down.val
  simp

end GC.GraphManifold
