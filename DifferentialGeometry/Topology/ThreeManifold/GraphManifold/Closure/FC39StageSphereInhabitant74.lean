import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageSlimOnly74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0SingletonRows

/-!
# Draft 74, A0 inhabitant: the stage geometry, cut choice and cut geometry of the S³ singleton

Lane S-JUNCTIONS (suffix `_JN74`). `A`, `D`, `H` of the X136 singleton: the actual closed zero
domain covering the round `S³` (`M₁ = ∅`), honest empty cusp, slim, edge and circle stages. A
regression of the contracts (D74-19), not the completion criterion.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0.X136

theorem sphereSlimReq74 : (SlimStage74.empty zeroW).slabImage ∪
    (SlimStage74.empty zeroW).facePoints ⊆ interior (∅ : Set (SlimStage74.empty zeroW).Base) := by
  change (∅ : Set PEmpty.{1}) ∪ ∅ ⊆ interior ∅
  simp

/-- The slim pieces of the S³ singleton: none (no slim component, `D₃ = ∅`). -/
def sphereSlimCut74 : SlimCutPieces74 (SmoothStageGeometry74.ofSlim74 zeroDomains zeroCusps
    (SlimStage74.empty zeroW))
    (StageCutChoice74.ofSlim74 zeroDomains zeroCusps (SlimStage74.empty zeroW) ∅ ∅
      isCompact_empty isCompact_empty (empty_inter _).symm sphereSlimReq74
      (by simp)) where
  pieces := zeroSlim
  componentEquiv :=
    { toFun := fun j => j.elim0
      invFun := fun K => False.elim (by
        obtain ⟨x, hx, -⟩ := K.2
        exact hx)
      left_inv := fun j => j.elim0
      right_inv := fun K => False.elim (by
        obtain ⟨x, hx, -⟩ := K.2
        exact hx) }
  piece_range := fun j => j.elim0
  shared_eq := fun e => e.1.1.elim0

/-- `A`: the actual stage geometry of the S³ singleton (whole zero domain, empty other stages). -/
def sphereStageGeometry74 : SmoothStageGeometry74 zeroW (BoundaryTori.empty zeroW) :=
  SmoothStageGeometry74.ofSlim74 zeroDomains zeroCusps (SlimStage74.empty zeroW)

/-- `D`: the empty cut choice of the S³ singleton. -/
def sphereCutChoice74 : StageCutChoice74 sphereStageGeometry74 :=
  StageCutChoice74.ofSlim74 zeroDomains zeroCusps (SlimStage74.empty zeroW) ∅ ∅ isCompact_empty
    isCompact_empty (empty_inter _).symm sphereSlimReq74 (by simp)

theorem sphereCutChoice74_M₂ : sphereCutChoice74.M₂ = ∅ := by
  change regionM1 zeroDomains zeroCusps \ _ = ∅
  rw [zeroRegionM1, empty_sdiff]

theorem sphereCutChoice74_slimSet : sphereCutChoice74.slimSet = ∅ :=
  eq_empty_of_forall_notMem fun _ ⟨_, hx⟩ => hx

/-- `H`: the empty cut geometry of the S³ singleton. -/
def sphereCutGeometry74 : StageCutGeometry74 sphereStageGeometry74 sphereCutChoice74 :=
  StageCutGeometry74.slimOnly74 zeroDomains zeroCusps (SlimStage74.empty zeroW) sphereCutChoice74
    sphereSlimCut74 sphereCutChoice74_M₂
    (eq_univ_of_univ_subset fun x _ =>
      Or.inl (Or.inl (Or.inl (mem_iUnion.2
        ⟨(0 : Fin 1), zeroClosedPiece_cover.symm ▸ mem_univ x⟩))))
    (fun x hx => (CircleRegion.false_of_bot zeroW ⟨x, hx.1⟩).elim)
    (fun _ b => b.elim0)
    (configurationResidualEmpty false) (configurationSharedEmpty false)

end GC.GraphManifold.Assembly.FC39P0.X136
