import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SphereCapSeam

/-!
Actual core, ball-interior and signed-sphere quotient patches with a genuine covering ledger.
-/

set_option autoImplicit false

noncomputable section

open Set Function Topology TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.MixedBoundaryCertificate

local instance sphereCapPatchBallCharts : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  Handle.closedCellChartedSpaceSucc 2

variable {C : CompactCarrier.{u}} (B : MixedBoundaryCertificate C)

abbrev SphereCapPatchIndex := B.sphereCapCoreOpen ⊕ (Fin B.sphereCount ⊕ Fin B.sphereCount)

abbrev SphereCapPatchSpace : B.SphereCapPatchIndex → Type u
  | .inl _ => B.sphereCapCoreOpen
  | .inr (.inl _) => ULift.{u} sphereCapBallOpen
  | .inr (.inr _) => ClosureSphere.{u} × ℝ

abbrev SphereCapPatchVector : B.SphereCapPatchIndex → Type
  | .inl _ => EuclideanSpace ℝ (Fin 3)
  | .inr (.inl _) => EuclideanSpace ℝ (Fin 3)
  | .inr (.inr _) => EuclideanSpace ℝ (Fin 2) × ℝ

abbrev SphereCapPatchModelSpace : B.SphereCapPatchIndex → Type
  | .inl _ => C.kind.Space
  | .inr (.inl _) => EuclideanHalfSpace 3
  | .inr (.inr _) => ModelProd (EuclideanSpace ℝ (Fin 2)) ℝ

instance sphereCapPatchTopology (a : B.SphereCapPatchIndex) :
    TopologicalSpace (B.SphereCapPatchSpace a) := by
  cases a with
  | inl x => exact inferInstanceAs (TopologicalSpace B.sphereCapCoreOpen)
  | inr a =>
    cases a with
    | inl i => exact inferInstanceAs (TopologicalSpace (ULift.{u} sphereCapBallOpen))
    | inr i => exact inferInstanceAs (TopologicalSpace (ClosureSphere.{u} × ℝ))

instance sphereCapPatchModelTopology (a : B.SphereCapPatchIndex) :
    TopologicalSpace (B.SphereCapPatchModelSpace a) := by
  cases a with
  | inl x => exact inferInstanceAs (TopologicalSpace C.kind.Space)
  | inr a => cases a <;> exact inferInstance

instance sphereCapPatchNormedGroup (a : B.SphereCapPatchIndex) :
    NormedAddCommGroup (B.SphereCapPatchVector a) := by
  cases a with
  | inl x => exact inferInstanceAs (NormedAddCommGroup (EuclideanSpace ℝ (Fin 3)))
  | inr a => cases a <;> exact inferInstance

instance sphereCapPatchNormedSpace (a : B.SphereCapPatchIndex) :
    NormedSpace ℝ (B.SphereCapPatchVector a) := by
  cases a with
  | inl x => exact inferInstanceAs (NormedSpace ℝ (EuclideanSpace ℝ (Fin 3)))
  | inr a => cases a <;> exact inferInstance

instance sphereCapPatchCharts (a : B.SphereCapPatchIndex) :
    ChartedSpace (B.SphereCapPatchModelSpace a) (B.SphereCapPatchSpace a) := by
  cases a with
  | inl x => exact inferInstanceAs (ChartedSpace C.kind.Space B.sphereCapCoreOpen)
  | inr a =>
    cases a with
    | inl i => exact uliftChartedSpace (EuclideanHalfSpace 3) sphereCapBallOpen
    | inr i => exact inferInstanceAs
        (ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin 2)) ℝ) (ClosureSphere.{u} × ℝ))

def sphereCapPatchModel (a : B.SphereCapPatchIndex) :
    ModelWithCorners ℝ (B.SphereCapPatchVector a) (B.SphereCapPatchModelSpace a) := by
  cases a with
  | inl x => exact C.model
  | inr a =>
    cases a with
    | inl i => exact 𝓡∂ 3
    | inr i => exact sphereSignedCollarModel

private theorem sphereCapBallOpen_nonempty : Nonempty sphereCapBallOpen := by
  refine ⟨⟨⟨0, by simp⟩, ?_⟩⟩
  change ‖(0 : EuclideanSpace ℝ (Fin 3))‖ < 1
  simp

def sphereCapPatch (a : B.SphereCapPatchIndex) :
    OpenPartialHomeomorph (B.SphereCapPatchSpace a) B.SphereCapQuotient := by
  cases a with
  | inl x =>
    letI : Nonempty B.sphereCapCoreOpen := ⟨x⟩
    exact B.sphereCapCore_openEmbedding.toOpenPartialHomeomorph
      (fun y : B.sphereCapCoreOpen => B.sphereCapCore y.val)
  | inr a =>
    cases a with
    | inl i =>
      letI : Nonempty sphereCapBallOpen := sphereCapBallOpen_nonempty
      exact Homeomorph.ulift.toOpenPartialHomeomorph.trans
        ((B.sphereCapBall_openEmbedding i).toOpenPartialHomeomorph
          (fun y : sphereCapBallOpen => B.sphereCapBall i y.val))
    | inr i => exact B.sphereCapSignedSeam i

theorem sphereCapPatch_core_apply (x y : B.sphereCapCoreOpen) :
    B.sphereCapPatch (.inl x) y = B.sphereCapCore y.val := rfl

theorem sphereCapPatch_ball_apply (i : Fin B.sphereCount) (y : ULift.{u} sphereCapBallOpen) :
    B.sphereCapPatch (.inr (.inl i)) y = B.sphereCapBall i y.down.val := rfl

theorem sphereCapPatch_core_target (x : B.sphereCapCoreOpen) :
    (B.sphereCapPatch (.inl x)).target =
      range (fun y : B.sphereCapCoreOpen => B.sphereCapCore y.val) := by
  simp only [sphereCapPatch, IsOpenEmbedding.toOpenPartialHomeomorph_target]

theorem sphereCapPatch_ball_target (i : Fin B.sphereCount) :
    (B.sphereCapPatch (.inr (.inl i))).target =
      range (fun y : sphereCapBallOpen => B.sphereCapBall i y.val) := by
  simp only [sphereCapPatch, OpenPartialHomeomorph.trans_target,
    IsOpenEmbedding.toOpenPartialHomeomorph_target, Homeomorph.toOpenPartialHomeomorph_target,
    preimage_univ, inter_univ]

theorem sphereCapPatch_cover (q : B.SphereCapQuotient) :
    ∃ a : B.SphereCapPatchIndex, q ∈ (B.sphereCapPatch a).target := by
  obtain ⟨x, rfl⟩ := B.sphereCapQuotientMap_surjective q
  cases x with
  | inl x =>
    by_cases hx : x ∈ B.sphereCapCoreOpen
    · refine ⟨.inl ⟨x, hx⟩, ?_⟩
      rw [B.sphereCapPatch_core_target]
      exact ⟨⟨x, hx⟩, rfl⟩
    · have hxS : x ∈ B.sphereImage := by simpa [sphereCapCoreOpen] using hx
      obtain ⟨i, z, hz⟩ := mem_iUnion.mp hxS
      refine ⟨.inr (.inr i), ?_⟩
      have hs := (B.sphereCapSignedSeam i).map_source (by
        rw [B.sphereCapSignedSeam_source]
        exact ⟨trivial, by norm_num, by norm_num⟩ :
          (z, 0) ∈ (B.sphereCapSignedSeam i).source)
      rwa [B.sphereCapSignedSeam_zero i z, hz] at hs
  | inr x =>
    by_cases hx : ‖x.2.val‖ < 1
    · refine ⟨.inr (.inl x.1), ?_⟩
      rw [B.sphereCapPatch_ball_target]
      exact ⟨⟨x.2, hx⟩, rfl⟩
    · have hn : ‖x.2.val‖ = 1 := by
        have hb : ‖x.2.val‖ ≤ 1 := by
          simpa [Metric.mem_closedBall, dist_zero_right] using x.2.property
        exact le_antisymm hb (le_of_not_gt hx)
      let z : ClosureSphere.{u} := ULift.up ⟨x.2.val, by
        simpa [Metric.mem_sphere, dist_zero_right] using hn⟩
      have he : closureSphereToBall z = x.2 := rfl
      refine ⟨.inr (.inr x.1), ?_⟩
      have hs := (B.sphereCapSignedSeam x.1).map_source (by
        rw [B.sphereCapSignedSeam_source]
        exact ⟨trivial, by norm_num, by norm_num⟩ :
          (z, 0) ∈ (B.sphereCapSignedSeam x.1).source)
      rwa [B.sphereCapSignedSeam_zero x.1 z, B.sphereCap_attachment x.1 z, he] at hs

end GC.GraphManifold.MixedBoundaryCertificate
