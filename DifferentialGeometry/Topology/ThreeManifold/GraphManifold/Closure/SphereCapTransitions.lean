import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SphereCapBallCollar
import DifferentialGeometry.Topology.Manifold.HalfSpaceInteriorChart

/-!
Genuine smooth positive and negative transition charts on full signed spherical collars.
-/

set_option autoImplicit false

noncomputable section

open Set Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold

local instance sphereCapTransitionBallCharts :
    ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) := Handle.closedCellChartedSpaceSucc 2

local instance sphereCapTransitionBallSmooth : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) :=
  Handle.closedCellIsManifold 2

private def sphereCapPositiveHeight :
    PartialDiffeomorph 𝓘(ℝ) (𝓡∂ 1) ℝ (EuclideanHalfSpace 1) ∞ where
  __ := halfSpaceInteriorChart 0
  contMDiffOn_toFun := halfSpaceInteriorChart_contMDiffOn 0
  contMDiffOn_invFun := (halfSpaceInteriorChart_symm_contMDiff 0).contMDiffOn

def sphereCapPositiveHalf : PartialDiffeomorph sphereSignedCollarModel sphereHalfCollarModel
    (ClosureSphere.{u} × ℝ) (ClosureSphere.{u} × EuclideanHalfSpace 1) ∞ :=
  DifferentialGeometry.Topology.PartialDiffeomorph.prod
    (Diffeomorph.refl (𝓡 2) ClosureSphere.{u} ∞).toPartialDiffeomorph sphereCapPositiveHeight

def sphereCapNegativeHalf : PartialDiffeomorph sphereSignedCollarModel sphereHalfCollarModel
    (ClosureSphere.{u} × ℝ) (ClosureSphere.{u} × EuclideanHalfSpace 1) ∞ :=
  ((Diffeomorph.refl (𝓡 2) ClosureSphere.{u} ∞).prodCongr
    (ContinuousLinearEquiv.neg ℝ).toDiffeomorph).toPartialDiffeomorph.trans sphereCapPositiveHalf

theorem sphereCapPositiveHalf_source :
    sphereCapPositiveHalf.source = {p : ClosureSphere.{u} × ℝ | 0 < p.2} := by
  ext p
  change (p.1 ∈ univ ∧ 0 < p.2) ↔ 0 < p.2
  simp

theorem sphereCapNegativeHalf_source :
    sphereCapNegativeHalf.source = {p : ClosureSphere.{u} × ℝ | p.2 < 0} := by
  ext p
  change (p ∈ univ ∧ (p.1, -p.2) ∈ sphereCapPositiveHalf.source) ↔ p.2 < 0
  rw [sphereCapPositiveHalf_source]
  simp

theorem sphereCapPositiveHalf_apply (z : ClosureSphere.{u}) (s : ℝ) (hs : 0 < s) :
    sphereCapPositiveHalf (z, s) = (z, halfPoint s hs.le) := by
  change (z, halfSpaceInteriorChart 0 s) = (z, halfPoint s hs.le)
  apply congrArg (fun y : EuclideanHalfSpace 1 => (z, y))
  apply Subtype.ext
  ext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  change max (s - 0) 0 = s
  rw [sub_zero, max_eq_left hs.le]

theorem sphereCapNegativeHalf_apply (z : ClosureSphere.{u}) (s : ℝ) (hs : s < 0) :
    sphereCapNegativeHalf (z, s) = (z, halfPoint (-s) (neg_nonneg.mpr hs.le)) :=
  sphereCapPositiveHalf_apply z (-s) (neg_pos.mpr hs)

namespace MixedBoundaryCertificate

variable {C : CompactCarrier.{u}} (B : MixedBoundaryCertificate C)

def sphereCapCoreTransition (i : Fin B.sphereCount) :
    PartialDiffeomorph sphereSignedCollarModel C.model
      (ClosureSphere.{u} × ℝ) C.Carrier ∞ := sphereCapPositiveHalf.trans (B.sphere i)

def sphereCapBallTransition : PartialDiffeomorph sphereSignedCollarModel (𝓡∂ 3)
    (ClosureSphere.{u} × ℝ) (ClosedCell 3) ∞ :=
  sphereCapNegativeHalf.trans sphereCapBallCollar

theorem sphereCapCoreTransition_source (i : Fin B.sphereCount) :
    (B.sphereCapCoreTransition i).source = univ ×ˢ Ioo (0 : ℝ) 1 := by
  ext p
  change (p ∈ sphereCapPositiveHalf.source ∧
    sphereCapPositiveHalf p ∈ (B.sphere i).source) ↔ _
  rw [sphereCapPositiveHalf_source, B.sphere_source]
  by_cases hp : 0 < p.2
  · rw [sphereCapPositiveHalf_apply p.1 p.2 hp]
    change (0 < p.2 ∧ p.2 < 1) ↔ (p.1 ∈ univ ∧ 0 < p.2 ∧ p.2 < 1)
    simp [hp]
  · simp [hp]

theorem sphereCapBallTransition_source :
    sphereCapBallTransition.source = univ ×ˢ Ioo (-1 : ℝ) 0 := by
  ext p
  change (p ∈ sphereCapNegativeHalf.source ∧
    sphereCapNegativeHalf p ∈ sphereCapBallCollar.source) ↔ _
  rw [sphereCapNegativeHalf_source, sphereCapBallCollar_source]
  by_cases hp : p.2 < 0
  · rw [sphereCapNegativeHalf_apply p.1 p.2 hp]
    change (p.2 < 0 ∧ -p.2 < 1) ↔ (p.1 ∈ univ ∧ -1 < p.2 ∧ p.2 < 0)
    simp only [mem_univ, true_and]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  · simp [hp]

end MixedBoundaryCertificate

end GC.GraphManifold
