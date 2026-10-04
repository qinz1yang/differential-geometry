import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SphereCapSmoothFold
import DifferentialGeometry.Topology.Manifold.ClosedCellInterior
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

/-!
The exact retained torus collars and intrinsic boundary of the actual spherical capping quotient.
-/

set_option autoImplicit false

noncomputable section

open Set Function Topology TopologicalSpace Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.MixedBoundaryCertificate

local instance sphereCapBoundaryBallCharts :
    ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) := Handle.closedCellChartedSpaceSucc 2

local instance sphereCapBoundaryLiftedBallCharts :
    ChartedSpace (EuclideanHalfSpace 3) (ULift.{u} sphereCapBallOpen) :=
  uliftChartedSpace (EuclideanHalfSpace 3) sphereCapBallOpen

variable {C : CompactCarrier.{u}} (B : MixedBoundaryCertificate C)
  [ChartedSpace (EuclideanHalfSpace 3) B.SphereCapQuotient]
  (hA : ∀ a : B.SphereCapPatchIndex,
    ContMDiffOn (B.sphereCapPatchModel a) (𝓡∂ 3) ∞
      (B.sphereCapPatch a) (B.sphereCapPatch a).source ∧
    ContMDiffOn (𝓡∂ 3) (B.sphereCapPatchModel a) ∞
      (B.sphereCapPatch a).symm (B.sphereCapPatch a).target)

include hA

def sphereCapCoreOpenDiffeomorph (x : B.sphereCapCoreOpen) :
    PartialDiffeomorph C.model (𝓡∂ 3) C.Carrier B.SphereCapQuotient ∞ :=
  (DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph C.model
    B.sphereCapCoreOpen ⟨x⟩).symm.trans (B.sphereCapPatchDiffeomorph hA (.inl x))

theorem sphereCapCoreOpenDiffeomorph_source (x : B.sphereCapCoreOpen) :
    (B.sphereCapCoreOpenDiffeomorph hA x).source = B.sphereCapCoreOpen := by
  change _ ∩ _ ⁻¹' univ = _
  rw [preimage_univ, inter_univ]
  change (DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph C.model
    B.sphereCapCoreOpen ⟨x⟩).target = _
  rw [DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_target]

theorem sphereCapCoreOpenDiffeomorph_apply (x : B.sphereCapCoreOpen)
    {y : C.Carrier} (hy : y ∈ B.sphereCapCoreOpen) :
    B.sphereCapCoreOpenDiffeomorph hA x y = B.sphereCapCore y := by
  let e := DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph C.model
    B.sphereCapCoreOpen ⟨x⟩
  have hyt : y ∈ e.target := by
    rwa [DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_target]
  change B.sphereCapCore (e.symm y).val = B.sphereCapCore y
  exact congrArg B.sphereCapCore (e.toOpenPartialHomeomorph.right_inv hyt)

theorem sphereCapCoreOpen_boundary_iff (x : B.sphereCapCoreOpen)
    {y : C.Carrier} (hy : y ∈ B.sphereCapCoreOpen) :
    (𝓡∂ 3).IsBoundaryPoint (B.sphereCapCore y) ↔ C.model.IsBoundaryPoint y := by
  let e := B.sphereCapCoreOpenDiffeomorph hA x
  have hys : y ∈ e.source := (B.sphereCapCoreOpenDiffeomorph_source hA x).symm ▸ hy
  rw [← B.sphereCapCoreOpenDiffeomorph_apply hA x hy]
  exact ((e.isLocalDiffeomorphAt C.model (𝓡∂ 3) ∞ hys).isBoundaryPoint_iff (by simp)).symm

def sphereCapRetainedPoint (i : Fin B.torusCount) : B.sphereCapCoreOpen :=
  ⟨B.tori.torusMap i (1, 1), B.torus_collar_mem_sphereCapCoreOpen i
    ((1, 1), halfZero) (zero_mem_halfCollarSource (1, 1))⟩

def sphereCapRetainedCollar (i : Fin B.torusCount) :
    PartialDiffeomorph halfCollarModel (𝓡∂ 3)
      (Torus × EuclideanHalfSpace 1) B.SphereCapQuotient ∞ :=
  (B.tori.collar i).trans (B.sphereCapCoreOpenDiffeomorph hA (B.sphereCapRetainedPoint i))

theorem sphereCapRetainedCollar_source (i : Fin B.torusCount) :
    (B.sphereCapRetainedCollar hA i).source = halfCollarSource := by
  ext p
  change p ∈ (B.tori.collar i).source ∧ B.tori.collar i p ∈
    (B.sphereCapCoreOpenDiffeomorph hA _).source ↔ p ∈ halfCollarSource
  rw [B.tori.source_eq, B.sphereCapCoreOpenDiffeomorph_source]
  exact ⟨And.left, fun hp => ⟨hp, B.torus_collar_mem_sphereCapCoreOpen i p hp⟩⟩

theorem sphereCapRetainedCollar_apply (i : Fin B.torusCount)
    {p : Torus × EuclideanHalfSpace 1} (hp : p ∈ halfCollarSource) :
    B.sphereCapRetainedCollar hA i p = B.sphereCapCore (B.tori.collar i p) := by
  change B.sphereCapCoreOpenDiffeomorph hA (B.sphereCapRetainedPoint i)
    (B.tori.collar i p) = _
  exact B.sphereCapCoreOpenDiffeomorph_apply hA (B.sphereCapRetainedPoint i)
    (B.torus_collar_mem_sphereCapCoreOpen i p hp)

theorem sphereCapRetainedCollar_target (i : Fin B.torusCount) :
    (B.sphereCapRetainedCollar hA i).target = B.sphereCapCore '' (B.tori.collar i).target := by
  ext q
  constructor
  · intro hq
    let p := (B.sphereCapRetainedCollar hA i).symm q
    have hp : p ∈ halfCollarSource := by
      have hh := (B.sphereCapRetainedCollar hA i).toOpenPartialHomeomorph.map_target hq
      change p ∈ (B.sphereCapRetainedCollar hA i).source at hh
      rwa [B.sphereCapRetainedCollar_source] at hh
    refine ⟨B.tori.collar i p, (B.tori.collar i).map_source' ?_, ?_⟩
    · rwa [B.tori.source_eq]
    · rw [← B.sphereCapRetainedCollar_apply hA i hp]
      exact (B.sphereCapRetainedCollar hA i).toOpenPartialHomeomorph.right_inv hq
  · rintro ⟨y, hy, rfl⟩
    let p := (B.tori.collar i).symm y
    have hp : p ∈ halfCollarSource := by
      have hh := (B.tori.collar i).toOpenPartialHomeomorph.map_target hy
      change p ∈ (B.tori.collar i).source at hh
      rwa [B.tori.source_eq] at hh
    have he : B.tori.collar i p = y := (B.tori.collar i).toOpenPartialHomeomorph.right_inv hy
    rw [← he, ← B.sphereCapRetainedCollar_apply hA i hp]
    exact (B.sphereCapRetainedCollar hA i).map_source'
      ((B.sphereCapRetainedCollar_source hA i).symm ▸ hp)

theorem sphereCapRetainedCollar_disjoint :
    Pairwise fun i j => Disjoint (B.sphereCapRetainedCollar hA i).target
      (B.sphereCapRetainedCollar hA j).target := by
  intro i j hij
  rw [B.sphereCapRetainedCollar_target, B.sphereCapRetainedCollar_target]
  apply Set.disjoint_left.mpr
  rintro q ⟨x, hx, hxq⟩ ⟨y, hy, hyq⟩
  have he : x = y := B.sphereCapCore_injective (hxq.trans hyq.symm)
  exact Set.disjoint_left.mp (B.tori.disjoint hij) hx (he.symm ▸ hy)

theorem sphereCapRetainedCollar_zero_boundary (i : Fin B.torusCount) (t : Torus) :
    (𝓡∂ 3).IsBoundaryPoint (B.sphereCapRetainedCollar hA i (t, halfZero)) := by
  have hp := zero_mem_halfCollarSource t
  rw [B.sphereCapRetainedCollar_apply hA i hp]
  exact (B.sphereCapCoreOpen_boundary_iff hA
    ⟨B.tori.torusMap i t, B.torus_collar_mem_sphereCapCoreOpen i (t, halfZero) hp⟩
      (B.torus_collar_mem_sphereCapCoreOpen i (t, halfZero) hp)).mpr
        (B.tori.boundary_zero i t)

theorem sphereCapSignedSeam_target_interior (i : Fin B.sphereCount) :
    (B.sphereCapSignedSeam i).target ⊆ (𝓡∂ 3).interior B.SphereCapQuotient := by
  intro q hq
  let e := B.sphereCapPatchDiffeomorph hA (.inr (.inr i))
  have hqs : q ∈ e.symm.source := hq
  have hl := e.symm.isLocalDiffeomorphAt (𝓡∂ 3) sphereSignedCollarModel ∞ hqs
  exact (hl.isInteriorPoint_iff (by simp)).mpr BoundarylessManifold.isInteriorPoint

theorem sphereCapBallPatch_target_interior (i : Fin B.sphereCount) :
    (B.sphereCapPatch (.inr (.inl i))).target ⊆ (𝓡∂ 3).interior B.SphereCapQuotient := by
  intro q hq
  let e := B.sphereCapPatchDiffeomorph hA (.inr (.inl i))
  let y : ULift.{u} sphereCapBallOpen := e.symm q
  have hyI : (𝓡∂ 3).IsInteriorPoint y.down.val := by
    change y.down.val ∈ (𝓡∂ 3).interior (ClosedCell 3)
    rw [closedCell_interior_eq_ball 2]
    exact y.down.property
  let d := DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph (𝓡∂ 3)
    sphereCapBallOpen ⟨y.down⟩
  have hyd : y.down ∈ d.source := by
    rw [DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_source]
    trivial
  have hyD : (𝓡∂ 3).IsInteriorPoint y.down :=
    ((d.isLocalDiffeomorphAt (𝓡∂ 3) (𝓡∂ 3) ∞ hyd).isInteriorPoint_iff (by simp)).mpr hyI
  have hl := (uliftDiffeomorph (𝓡∂ 3) sphereCapBallOpen).symm.isLocalDiffeomorph y
  have hyU : (𝓡∂ 3).IsInteriorPoint y := (hl.isInteriorPoint_iff (by simp)).mpr hyD
  have hqs : q ∈ e.symm.source := hq
  exact ((e.symm.isLocalDiffeomorphAt (𝓡∂ 3) (𝓡∂ 3) ∞ hqs).isInteriorPoint_iff (by simp)).mpr hyU

theorem sphereCapQuotient_boundary :
    (𝓡∂ 3).boundary B.SphereCapQuotient = B.sphereCapCore '' B.tori.image := by
  ext q
  constructor
  · intro hq
    obtain ⟨a, ha⟩ := B.sphereCapPatch_cover q
    cases a with
    | inl x =>
      rw [B.sphereCapPatch_core_target] at ha
      obtain ⟨y, rfl⟩ := ha
      have hy : C.model.IsBoundaryPoint y.val :=
        (B.sphereCapCoreOpen_boundary_iff hA x y.property).mp hq
      have hb : y.val ∈ B.tori.image ∪ B.sphereImage := B.exhausted ▸ hy
      rcases hb with ht | hs
      · exact ⟨y.val, ht, rfl⟩
      · exact False.elim (y.property hs)
    | inr a =>
      cases a with
      | inl i => exact False.elim ((𝓡∂ 3).disjoint_interior_boundary.le_bot
          ⟨B.sphereCapBallPatch_target_interior hA i ha, hq⟩)
      | inr i => exact False.elim ((𝓡∂ 3).disjoint_interior_boundary.le_bot
          ⟨B.sphereCapSignedSeam_target_interior hA i ha, hq⟩)
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨i, t, rfl⟩ := mem_iUnion.mp hx
    have hh := B.sphereCapRetainedCollar_zero_boundary hA i t
    rwa [B.sphereCapRetainedCollar_apply hA i (zero_mem_halfCollarSource t)] at hh

end GC.GraphManifold.MixedBoundaryCertificate
