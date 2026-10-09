import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.ExitsKernelU74LND
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.RowsLinkOfStage74Applications
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.RowsLinkKernel74Applications
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageSphereInhabitant74

/-!
# Compiled inhabitants of the closed exits kernel (S³ singleton and S² × S¹ loop)

Lane S-LANDING (by S-LANDING2, suffix `_LND`), G4. `ExitsKernelU_LND` (the plain-data mirror of
`ClosedExitsOverU74`) is inhabited on the two non-empty fixtures of the abstract assembler (lane
S-JUNCTIONS `FC39StageSphereInhabitant74`, `FC39StageLoopInhabitant74`):

* **S³ singleton**: ONE zero domain (the whole sphere), empty slim / edge / circle stages over
  the empty base, every set of the data empty, `ψ = id`, block space `PUnit`;
* **S² × S¹ loop**: no zero domain, ONE slim stage over `S¹` (`K₃ = D₃ = C₃ = S¹`, whole
  `f₃`-preimage), empty edge / circle stages, `ψ = id`, `ι = id`, block space `S¹`.

Consumers: on each fixture the exits kernel feeds the bridges (`ExitsKernelU_LND.rows_tables`):
the zero, slim, edge (open ambient parent) and circle tables on the J1 rows (the loop's slim
table is non-empty, the sphere's zero table is non-empty).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0.X136

/-- The actual components of the empty set: none. -/
theorem isEmpty_actualComponent_empty_LND {Y : Type*} [TopologicalSpace Y] :
    IsEmpty (ActualComponent (∅ : Set Y)) :=
  ⟨fun K => by
    obtain ⟨x, hx, -⟩ := K.2
    exact hx⟩

/-! ## The S³ singleton -/

/-- The plain data of the S³ singleton: every set empty, block space `PUnit`. -/
def sphereExitsData_LND : StageIdentData_LND zeroW.Carrier PUnit.{1} where
  qs := fun _ => PUnit.unit
  q1 := fun _ => PUnit.unit
  q0 := fun _ => PUnit.unit
  U₂ := ∅
  hS := fun _ => 0
  lvl := 0
  slimC3 := ∅
  slab := ∅
  faces := ∅
  K₃ := ∅
  D₃ := ∅
  C₂ := ∅
  C₁ := ∅
  eO := ∅
  cO := ∅

local instance isEmpty_slimEmptyBase_LND :
    IsEmpty (SlimStage74.empty zeroW).toStageProj74.Base :=
  inferInstanceAs (IsEmpty PEmpty.{1})

local instance isEmpty_edgeEmptyBase_LND :
    IsEmpty (EdgeStage74.empty zeroW).toStageProj74.Base :=
  inferInstanceAs (IsEmpty PEmpty.{1})

local instance isEmpty_circleEmptyBase_LND : IsEmpty (StageProj74.empty zeroW 2).Base :=
  inferInstanceAs (IsEmpty PEmpty.{1})

/-- **The stage kernel of the S³ singleton**: the three stages are empty, the cut is the empty cut
choice of `sphereStageGeometry74`. -/
def sphereStageKernel_LND : StageGeometryKernelU_LND (Equiv.refl zeroW.Carrier) zeroDomains
    zeroCusps sphereExitsData_LND where
  slim := SlimStage74.empty zeroW
  edge := EdgeStage74.empty zeroW
  circle := StageProj74.empty zeroW 2
  ιslim := fun b => PEmpty.elim b
  ιedge := fun b => PEmpty.elim b
  ιcircle := fun b => PEmpty.elim b
  slim_ident := stageIdent_of_isEmpty_LND74 _ _ _ _
  edge_ident := ⟨Topology.IsEmbedding.of_subsingleton _,
    fun x => (CircleRegion.false_of_bot zeroW x).elim, by
      change ((⊥ : TopologicalSpace.Opens zeroW.Carrier) : Set zeroW.Carrier) = _
      simp [sphereExitsData_LND]⟩
  circle_ident := stageIdent_of_isEmpty_LND74 _ _ _ _
  slim_C₃ := image_empty _
  slim_slab := image_empty _
  slim_faces := image_empty _
  edge_height := fun x => (CircleRegion.false_of_bot zeroW x).elim
  edge_level := rfl
  cut := sphereCutChoice74
  cut_K₃ := image_empty _
  cut_D₃ := image_empty _
  cut_C₂ := image_empty _
  cut_C₁ := image_empty _
  cut_edgeOpen := image_empty _
  cut_circleOpen := image_empty _
  comp := @Equiv.equivOfIsEmpty _ _ isEmpty_actualComponent_empty_LND
    isEmpty_actualComponent_empty_LND
  comp_eq := fun c => (isEmpty_actualComponent_empty_LND.false c).elim

/-- **Inhabitant of the exits kernel on the S³ singleton**: ONE zero domain (the whole sphere),
empty stages, the A0 cut geometry `sphereCutGeometry74`, `M^edge = ∅`. -/
theorem sphere_exitsKernel_LND :
    ∃ (ι : Type) (dom inner outer : ι → Set zeroW.Carrier) (uv : ι → zeroW.Carrier → ℝ),
      Nonempty (ExitsKernelU_LND (Equiv.refl zeroW.Carrier) zeroDomains zeroCusps
        sphereExitsData_LND dom inner outer uv ∅) := by
  obtain ⟨ι, dom, inner, outer, uv, hz⟩ := zeroLink_configuration_LND74 false
  exact ⟨ι, dom, inner, outer, uv, ⟨{
    zero := hz
    stages := sphereStageKernel_LND
    geometry := sphereCutGeometry74
    edgeSet_eq := by simp [sphereExitsData_LND] }⟩⟩

/-- **Consumer on the S³ singleton**: the exits kernel feeds the four table bridges (the zero
table is non-empty: one zero domain). -/
theorem sphere_exitsKernel_tables_LND :
    ∃ (ι : Type) (dom inner outer : ι → Set zeroW.Carrier) (uv : ι → zeroW.Carrier → ℝ)
      (Rw : FC39RowsV2 zeroW (BoundaryTori.empty zeroW)),
      ZeroLink_LND74 (Equiv.refl zeroW.Carrier) Rw.zero dom inner outer uv ∧
      SlimLink_LND74 (Equiv.refl zeroW.Carrier) Rw.slim
        (fun c : ActualComponent sphereExitsData_LND.D₃ => sphereExitsData_LND.qs ⁻¹' c.1)
        (sphereExitsData_LND.qs ⁻¹' sphereExitsData_LND.D₃) ∧
      EdgeLinkU_LND74 (Equiv.refl zeroW.Carrier) Rw.edge sphereExitsData_LND.q1
        sphereExitsData_LND.hS sphereExitsData_LND.lvl sphereExitsData_LND.eO
        sphereExitsData_LND.C₂ sphereExitsData_LND.U₂ ∅ ∧
      CircleLink_LND74 (Equiv.refl zeroW.Carrier) Rw.circle sphereExitsData_LND.q0
        sphereExitsData_LND.cO sphereExitsData_LND.C₁
        (sphereExitsData_LND.q0 ⁻¹' sphereExitsData_LND.cO) ∅ := by
  obtain ⟨ι, dom, inner, outer, uv, ⟨E⟩⟩ := sphere_exitsKernel_LND
  obtain ⟨Rw, h⟩ := E.rows_tables (subset_refl _) (M₃ := ∅)
    (by simp [sphereExitsData_LND])
  exact ⟨ι, dom, inner, outer, uv, Rw, h⟩

/-! ## The S² × S¹ loop -/

/-- The plain data of the S² × S¹ loop: block space `S¹`, `f₃ = slimLoopQ`, `K₃ = D₃ = C₃ = S¹`,
every other set empty. -/
def slimLoopExitsData_LND : StageIdentData_LND slimWc.Carrier Circle where
  qs := slimLoopQ_LND74
  q1 := fun _ => 1
  q0 := fun _ => 1
  U₂ := ∅
  hS := fun _ => 0
  lvl := 0
  slimC3 := univ
  slab := ∅
  faces := ∅
  K₃ := univ
  D₃ := univ
  C₂ := ∅
  C₁ := ∅
  eO := ∅
  cO := ∅

local instance isEmpty_edgeEmptyBaseLoop_LND :
    IsEmpty (EdgeStage74.empty slimWc).toStageProj74.Base :=
  inferInstanceAs (IsEmpty PEmpty.{1})

local instance isEmpty_circleEmptyBaseLoop_LND : IsEmpty (StageProj74.empty slimWc 2).Base :=
  inferInstanceAs (IsEmpty PEmpty.{1})

/-- **The stage kernel of the S² × S¹ loop**: ONE slim stage over `S¹` identified with `f₃` by
`ι = id`, empty edge and circle stages, the cut choice `slimLoopCutChoice74` (`K₃ = D₃ = S¹`),
the components equivalence is the identity. -/
def slimLoopStageKernel_LND : StageGeometryKernelU_LND (Equiv.refl slimWc.Carrier) slimZero
    slimCusps slimLoopExitsData_LND where
  slim := slimLoopStage74
  edge := EdgeStage74.empty slimWc
  circle := StageProj74.empty slimWc 2
  ιslim := id
  ιedge := fun b => PEmpty.elim b
  ιcircle := fun b => PEmpty.elim b
  slim_ident := ⟨Topology.IsEmbedding.id, fun _ => rfl, fun _ _ => trivial⟩
  edge_ident := ⟨Topology.IsEmbedding.of_subsingleton _,
    fun x => (CircleRegion.false_of_bot slimWc x).elim,
    TopologicalSpace.Opens.coe_bot.trans (image_empty _).symm⟩
  circle_ident := stageIdent_of_isEmpty_LND74 _ _ _ _
  slim_C₃ := image_id _
  slim_slab := image_empty _
  slim_faces := image_empty _
  edge_height := fun x => (CircleRegion.false_of_bot slimWc x).elim
  edge_level := rfl
  cut := slimLoopCutChoice74
  cut_K₃ := image_id _
  cut_D₃ := image_id _
  cut_C₂ := image_empty _
  cut_C₁ := image_empty _
  cut_edgeOpen := image_empty _
  cut_circleOpen := image_empty _
  comp := Equiv.refl _
  comp_eq := fun _ => image_id _

/-- **Inhabitant of the exits kernel on the S² × S¹ loop**: no zero domain, ONE slim stage whose
whole `f₃`-preimage is the single slim piece, empty edge / circle stages, the A0 cut geometry
`slimLoopCutGeometry74`. -/
theorem slimLoop_exitsKernel_LND :
    ∃ (ι : Type) (dom inner outer : ι → Set slimWc.Carrier) (uv : ι → slimWc.Carrier → ℝ),
      Nonempty (ExitsKernelU_LND (Equiv.refl slimWc.Carrier) slimZero slimCusps
        slimLoopExitsData_LND dom inner outer uv ∅) := by
  obtain ⟨ι, dom, inner, outer, uv, hz⟩ := zeroLink_configuration_LND74 true
  exact ⟨ι, dom, inner, outer, uv, ⟨{
    zero := hz
    stages := slimLoopStageKernel_LND
    geometry := slimLoopCutGeometry74
    edgeSet_eq := (empty_inter _).symm }⟩⟩

/-- **Consumer on the S² × S¹ loop**: the exits kernel feeds the four table bridges; the slim
table is NON-empty (the whole `f₃`-preimage of the single component of `D₃ = S¹`). -/
theorem slimLoop_exitsKernel_tables_LND :
    ∃ (ι : Type) (dom inner outer : ι → Set slimWc.Carrier) (uv : ι → slimWc.Carrier → ℝ)
      (Rw : FC39RowsV2 slimWc (BoundaryTori.empty slimWc)),
      ZeroLink_LND74 (Equiv.refl slimWc.Carrier) Rw.zero dom inner outer uv ∧
      SlimLink_LND74 (Equiv.refl slimWc.Carrier) Rw.slim
        (fun c : ActualComponent slimLoopExitsData_LND.D₃ => slimLoopExitsData_LND.qs ⁻¹' c.1)
        (slimLoopExitsData_LND.qs ⁻¹' slimLoopExitsData_LND.D₃) ∧
      EdgeLinkU_LND74 (Equiv.refl slimWc.Carrier) Rw.edge slimLoopExitsData_LND.q1
        slimLoopExitsData_LND.hS slimLoopExitsData_LND.lvl slimLoopExitsData_LND.eO
        slimLoopExitsData_LND.C₂ slimLoopExitsData_LND.U₂ ∅ ∧
      CircleLink_LND74 (Equiv.refl slimWc.Carrier) Rw.circle slimLoopExitsData_LND.q0
        slimLoopExitsData_LND.cO slimLoopExitsData_LND.C₁
        (slimLoopExitsData_LND.q0 ⁻¹' slimLoopExitsData_LND.cO) ∅ := by
  obtain ⟨ι, dom, inner, outer, uv, ⟨E⟩⟩ := slimLoop_exitsKernel_LND
  obtain ⟨Rw, h⟩ := E.rows_tables (subset_refl _) (M₃ := ∅) preimage_empty.symm
  exact ⟨ι, dom, inner, outer, uv, Rw, h⟩

end GC.GraphManifold.Assembly.FC39P0.X136
