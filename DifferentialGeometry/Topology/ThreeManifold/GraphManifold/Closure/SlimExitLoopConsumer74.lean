import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SlimPiecesOfExits74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageLoopInhabitant74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageRows74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GFinalClosed

/-!
# Consumer of the slim adapter (loops): the closed slim loop `S² × S¹` as the exit of a sphere loop

Lane S-JUNCTIONS (suffix `_JN74`, group G4c). On the closed `S² × S¹` of the X136 inhabitant the
loop region is the whole carrier, the circle map is the second factor, and the standard sphere is
embedded onto the fibre over `1`. The slim piece built by the adapter (`sphereLoopPiece74`,
`sphereLoopModel74`, through the piece of a clopen connected region) replaces the hand-built one:
`slimLoopSlimCutOfExit74 : SlimCutPieces74 …` and the assembled rows of J1 on it.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open GC.GraphManifold.Assembly
open Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0.X136

/-- The total circle map of the loop: the second factor. -/
def slimLoopFn74 (x : slimWc.Carrier) : Circle :=
  slimProjection (slimBack74 x)

theorem slimLoopFn74_smooth : ContMDiff slimWc.model (𝓡 1) ∞ slimLoopFn74 :=
  slimProjection_smooth.comp slimBack74.contMDiff

theorem slimLoopFn74_submersion (x : slimWc.Carrier) :
    Surjective (mfderiv slimWc.model (𝓡 1) slimLoopFn74 x) := by
  have h := slimLoopProj74_submersion (⟨x, trivial⟩ : (⊤ : TopologicalSpace.Opens slimWc.Carrier))
  have h2 := DifferentialGeometry.mfderiv_restrict_open (I := slimWc.model) (J := 𝓡 1)
    slimLoopFn74 (⊤ : TopologicalSpace.Opens slimWc.Carrier) ⟨x, trivial⟩
  exact h2 ▸ h

/-- The standard sphere embedded onto the fibre over `1`, as a map into `W`. -/
def slimLoopFibre74 : ClosureSphere.{0} → slimWc.Carrier :=
  slimBack74.symm ∘ slimSphereMap

theorem slimLoopFibre74_embedding : IsSmoothEmbedding (𝓡 2) slimWc.model ∞ slimLoopFibre74 := by
  have hs : ContMDiff (𝓡 2) (𝓡 3) ∞ slimLoopFibre74 :=
    slimBack74.symm.contMDiff.comp slimSphereMap_smooth
  have hemb : Topology.IsEmbedding slimLoopFibre74 :=
    slimBack74.symm.toHomeomorph.isEmbedding.comp slimSphereMap_embedding.isEmbedding
  have hinj : ∀ z, Injective (mfderiv (𝓡 2) (𝓡 3) slimLoopFibre74 z) := by
    intro z
    have h1 := mfderiv_comp (I := 𝓡 2) (I' := 𝓡∂ 3) (I'' := 𝓡 3) z
      (g := slimBack74.symm) (f := slimSphereMap)
      (slimBack74.symm.contMDiff.mdifferentiableAt (by simp))
      (slimSphereMap_smooth.mdifferentiableAt (by simp))
    change Injective (mfderiv (𝓡 2) (𝓡 3) (slimBack74.symm ∘ slimSphereMap) z)
    rw [h1]
    exact (slimBack74.symm.mfderivToContinuousLinearEquiv (by simp) _).injective.comp
      (slimSphereMap_derivative z)
  exact isSmoothEmbedding_of_injective_mfderiv_of_interior_GSF (by simp) hs hemb hinj fun _ =>
    BoundarylessManifold.isInteriorPoint

theorem slimLoopFibre74_range :
    range slimLoopFibre74 = {x | x ∈ (univ : Set slimWc.Carrier) ∧ slimLoopFn74 x = 1} := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    have hz : slimSphereMap z ∈ range slimSphereMap := mem_range_self z
    rw [slimSphereMap_range] at hz
    refine ⟨mem_univ _, ?_⟩
    change slimProjection (slimBack74 (slimBack74.symm (slimSphereMap z))) = 1
    rw [slimBack74.apply_symm_apply]
    exact hz
  · rintro ⟨-, hx⟩
    have hy : slimBack74 x ∈ range slimSphereMap := by
      rw [slimSphereMap_range]
      exact hx
    obtain ⟨z, hz⟩ := hy
    exact ⟨z, by
      change slimBack74.symm (slimSphereMap z) = x
      rw [hz]
      exact slimBack74.symm_apply_apply x⟩

/-- **The exit of the sphere loop of `S² × S¹`.** -/
def slimLoopExit74 : SphereLoopExit74 slimWc where
  region :=
    { O := univ
      isClopen := isClopen_univ
      interior := fun x _ => ((NoCuts.interiorDiffeomorph sphereTwoTimesCircleLift).symm x).property
      connected := isPreconnected_univ }
  p := slimLoopFn74
  fibre := slimLoopFibre74
  p_smooth := slimLoopFn74_smooth.contMDiffOn
  p_sub := fun x _ => slimLoopFn74_submersion x
  fibre_embedding := slimLoopFibre74_embedding
  fibre_range := slimLoopFibre74_range

/-- **The slim exit of the `S² × S¹` cut choice**: one sphere loop over the single component. -/
def slimLoopSlimExit74 : SlimExit74 slimLoopStageGeometry74 slimLoopCutChoice74 where
  count := 1
  exit := fun _ => .sphereLoop slimLoopExit74
  componentEquiv := slimLoopSlimCut74.componentEquiv
  piece_range := fun j =>
    (range_sphereLoopPiece74 slimLoopExit74).trans
      ((slimLoopSlimCut74.piece_range j).symm.trans
        (wholePiece_range sphereTwoTimesCircleLift)).symm

/-- **`SlimCutPieces74` of the `S² × S¹` loop from the adapter** (instead of the hand-built
`slimLoopSlimCut74`). -/
def slimLoopSlimCutOfExit74 : SlimCutPieces74 slimLoopStageGeometry74 slimLoopCutChoice74 :=
  slimCutPieces_of_exit74 slimLoopSlimExit74

theorem slimLoopSlimCutOfExit74_union : slimLoopSlimCutOfExit74.pieces.union = univ :=
  slimLoopSlimCutOfExit74.union_eq.trans slimLoopCutChoice74_slimSet

instance slimLoopNeighbourFace_isEmpty : IsEmpty (NeighbourFace slimZero slimCusps) :=
  ⟨fun F => by
    rcases F with F | F
    · exact F.1.elim0
    · exact F.1.elim0⟩

instance slimLoopOfExit_end_isEmpty : IsEmpty slimLoopSlimCutOfExit74.pieces.End :=
  ⟨fun e => e.2.elim⟩

instance slimLoopOfExit_residual_isEmpty : IsEmpty slimLoopSlimCutOfExit74.pieces.ResidualFace :=
  ⟨fun F => by
    rcases F with F | e
    · exact (slimLoopNeighbourFace_isEmpty.false F.1)
    · exact (slimLoopOfExit_end_isEmpty.false e.1)⟩

instance slimLoopOfExit_shared_isEmpty :
    IsEmpty (ActualSharedFace slimLoopSlimCutOfExit74.pieces) :=
  ⟨fun e => slimLoopOfExit_end_isEmpty.false e.1⟩

/-- **The cut geometry of the `S² × S¹` loop with the adapter's slim piece.** -/
def slimLoopCutGeometryOfExit74 :
    StageCutGeometry74 slimLoopStageGeometry74 slimLoopCutChoice74 :=
  StageCutGeometry74.slimOnly74 slimZero slimCusps slimLoopStage74 slimLoopCutChoice74
    slimLoopSlimCutOfExit74 slimLoopCutChoice74_M₂
    (eq_univ_of_univ_subset fun x _ => Or.inl (Or.inr (slimLoopCutChoice74_slimSet ▸ mem_univ x)))
    (fun x _ => slimRegionM1_c ▸ mem_univ x)
    (fun i _ => i.elim0) slimLoopOfExit_residual_isEmpty slimLoopOfExit_shared_isEmpty

/-- **The rows of the `S² × S¹` loop with the adapter's slim piece.** -/
def slimLoopRowsOfExit74 : FC39RowsV2 slimWc (BoundaryTori.empty slimWc) :=
  rowsOfStageGeometry74 slimLoopStageGeometry74 slimLoopCutChoice74 slimLoopCutGeometryOfExit74

/-- The assembled rows have the slim piece of the adapter: one piece of image `univ`. -/
theorem slimLoopRowsOfExit74_slim :
    slimLoopRowsOfExit74.slim.count = 1 ∧ slimLoopRowsOfExit74.slim.union = univ :=
  ⟨rfl, slimLoopSlimCutOfExit74_union⟩

/-- **The end-to-end consumer**: the rows with the adapter's loop piece feed
`exists_strongCertificate_of_rows_GFIN`. -/
theorem slimLoopOfExit_strongCertificate_74 :
    Nonempty (StrongCertificate slimWc (BoundaryTori.empty slimWc)) :=
  exists_strongCertificate_of_rows_GFIN slimLoopRowsOfExit74

end GC.GraphManifold.Assembly.FC39P0.X136
