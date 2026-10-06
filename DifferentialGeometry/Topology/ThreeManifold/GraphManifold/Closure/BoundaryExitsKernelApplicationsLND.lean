import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.BoundaryExitsKernelLND
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.RowsLinkOfStage74Applications
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageSphereInhabitant74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.ExitsKernelU74ApplicationsLND

/-!
# Compiled inhabitants of the boundary exits kernel (S³ singleton and S² × S¹ loop, `n = 0`)

Lane S-LANDING (by S-LANDING2, suffix `_LND`), G6. `BoundaryExitsKernel_LND` (the plain-data mirror
of the boundary landing exits `BoundaryLandingExits74b`) is inhabited, with no cusp component
(`n = 0`, the degenerate boundary route of a closed member), on the two non-empty fixtures of the
abstract assembler (lane S-JUNCTIONS):

* **S³ singleton**: ONE zero domain (the whole sphere), empty slim / edge / circle stages, every
  piece empty, `M₁ = ∅`;
* **S² × S¹ loop**: no zero domain, ONE slim stage over `S¹` (parent `⊤`, source `X₂ = W`,
  `D₃ = S¹`, whole `f₃`-preimage), empty edge / circle stages, `M₁ = W`, `M₂ = ∅`.

Consumers: on each fixture the head `BoundaryExitsKernel_LND.rows_link` gives rows satisfying the
plain form of `BoundaryRowsLink`. The cusp rows (`n ≥ 1`) are not exercised: they need the solid
torus instance (lane S-SOLIDTORUS).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0.X136

/-- A stage whose parent is `⊥` and whose base is empty is identified with every map on the empty
source. -/
theorem stageIdentSrc_of_parent_bot_LND {k : ℕ} {W : CompactCarrier.{0}} {Bs : Type}
    [TopologicalSpace Bs] (Q : StageProj74 W k) [IsEmpty Q.Base] (hQ : Q.parent = ⊥)
    (q : W.Carrier → Bs) (ι : Q.Base → Bs) : StageIdentSrc_LND74 Q q ι ∅ :=
  ⟨Topology.IsEmbedding.of_subsingleton ι, fun x => isEmptyElim (Q.proj x), by
    rw [hQ]
    exact TopologicalSpace.Opens.coe_bot⟩

local instance isEmpty_slimEmptyBaseB_LND :
    IsEmpty (SlimStage74.empty zeroW).toStageProj74.Base :=
  inferInstanceAs (IsEmpty PEmpty.{1})

local instance isEmpty_edgeEmptyBaseB_LND :
    IsEmpty (EdgeStage74.empty zeroW).toStageProj74.Base :=
  inferInstanceAs (IsEmpty PEmpty.{1})

local instance isEmpty_circleEmptyBaseB_LND : IsEmpty (StageProj74.empty zeroW 2).Base :=
  inferInstanceAs (IsEmpty PEmpty.{1})

local instance isEmpty_edgeEmptyBaseBL_LND :
    IsEmpty (EdgeStage74.empty slimWc).toStageProj74.Base :=
  inferInstanceAs (IsEmpty PEmpty.{1})

local instance isEmpty_circleEmptyBaseBL_LND : IsEmpty (StageProj74.empty slimWc 2).Base :=
  inferInstanceAs (IsEmpty PEmpty.{1})

/-! ## The S³ singleton -/

/-- The plain data of the S³ singleton (`n = 0`): one zero domain `univ`, every piece empty. -/
def sphereBoundaryData_LND : BoundaryExitsData_LND zeroW PUnit.{1} 0 (Fin 1) where
  q0 := fun _ => PUnit.unit
  q1 := fun _ => PUnit.unit
  q2 := fun _ => PUnit.unit
  src0 := ∅
  src1 := ∅
  src2 := ∅
  eParent := ∅
  base0 := ∅
  base1 := ∅
  height := fun _ => 0
  lvl := 0
  Dset := ∅
  slimPiece := ∅
  edgePiece := ∅
  remainder := ∅
  M₁ := ∅
  M₂ := ∅
  zdom := fun _ => univ
  zdef := fun _ => wholeFunction standardThreeSphere
  cuspCore := fun i => i.elim0
  cuspFront := fun i => i.elim0
  cuspFn := fun i => i.elim0

/-- **The boundary exits kernel of the S³ singleton**. -/
def sphereBoundaryKernel_LND :
    BoundaryExitsKernel_LND sphereBoundaryData_LND (fun i => i.elim0) where
  Et := BoundaryTori.empty zeroW
  labels_eq := fun i => i.elim0
  zero := zeroDomains
  zero_link := ⟨finCongr rfl, fun _ => ⟨zeroClosedPiece_cover, rfl⟩⟩
  cusp := zeroCusps
  cusp_link := fun i => i.elim0
  slim := SlimStage74.empty zeroW
  edge := EdgeStage74.empty zeroW
  circle := StageProj74.empty zeroW 2
  ιslim := fun b => PEmpty.elim b
  ιedge := fun b => PEmpty.elim b
  ιcircle := fun b => PEmpty.elim b
  slim_ident := stageIdentSrc_of_parent_bot_LND _ rfl _ _
  edge_ident := stageIdentSrc_of_parent_bot_LND _ rfl _ _
  circle_ident := stageIdentSrc_of_parent_bot_LND _ rfl _ _
  edge_range := by
    rintro y ⟨b, -⟩
    exact isEmptyElim b
  circle_range := by
    rintro y ⟨b, -⟩
    exact isEmptyElim b
  edge_height := fun x => (CircleRegion.false_of_bot zeroW x).elim
  edge_level := rfl
  cut := sphereCutChoice74
  cut_D₃ := image_empty _
  cut_C₂ := (image_empty _).trans (image_empty _).symm
  cut_C₁ := (image_empty _).trans (image_empty _).symm
  comp := @Equiv.equivOfIsEmpty _ _ isEmpty_actualComponent_empty_LND
    isEmpty_actualComponent_empty_LND
  comp_eq := fun c => (isEmpty_actualComponent_empty_LND.false c).elim
  edgePiece_eq := by simp [sphereBoundaryData_LND]
  geometry := sphereCutGeometry74
  src1_eq := (empty_inter _).symm
  slimPiece_eq := (empty_inter _).symm
  M₁_eq := by simp [sphereBoundaryData_LND, iUnion_const]
  M₂_eq := (empty_sdiff _).symm
  remainder_eq := (empty_sdiff _).symm
  remainder_sat := (empty_inter _).symm

/-- **Consumer on the S³ singleton**: the head gives rows with ONE zero piece (the whole sphere),
`M₁ = ∅` and `M₃ = ∅`. -/
theorem sphere_boundaryKernel_rows_LND :
    ∃ Rw : FC39RowsV2 zeroW (BoundaryTori.empty zeroW),
      Rw.zero.count = 1 ∧ (∀ k, range (Rw.zero.piece k).map = univ) ∧
      regionM1 Rw.zero Rw.cusp = ∅ ∧ regionM3 Rw.slim Rw.edge = ∅ := by
  obtain ⟨Rw, ⟨σ, hσ⟩, -, -, -, -, h1, -, h3⟩ := sphereBoundaryKernel_LND.rows_link
  exact ⟨Rw, Fin.equiv_iff_eq.1 ⟨σ⟩, fun k => (hσ k).1, h1, h3⟩

/-! ## The S² × S¹ loop -/

theorem empty_inter_inter_LND {α : Type*} (s t : Set α) : (∅ : Set α) = ∅ ∩ s ∩ t := by simp

theorem univ_eq_inter_preimage_LND {α β : Type*} (f : α → β) :
    (univ : Set α) = univ ∩ f ⁻¹' univ := by simp

theorem univ_eq_compl_interior_fin0_LND {α : Type*} [TopologicalSpace α] (f g : Fin 0 → Set α) :
    (univ : Set α) = (interior ((⋃ k, f k) ∪ ⋃ i, g i))ᶜ := by simp

/-- The plain data of the S² × S¹ loop (`n = 0`): no zero domain, `X₂ = W`, `D₃ = S¹`, the slim
piece is `W`, every other piece empty. -/
def slimLoopBoundaryData_LND : BoundaryExitsData_LND slimWc Circle 0 (Fin 0) where
  q0 := fun _ => 1
  q1 := fun _ => 1
  q2 := slimLoopQ_LND74
  src0 := ∅
  src1 := ∅
  src2 := univ
  eParent := ∅
  base0 := ∅
  base1 := ∅
  height := fun _ => 0
  lvl := 0
  Dset := univ
  slimPiece := univ
  edgePiece := ∅
  remainder := ∅
  M₁ := univ
  M₂ := ∅
  zdom := fun i => i.elim0
  zdef := fun i => i.elim0
  cuspCore := fun i => i.elim0
  cuspFront := fun i => i.elim0
  cuspFn := fun i => i.elim0

/-- **The boundary exits kernel of the S² × S¹ loop**: ONE slim stage over `S¹` with source
`X₂ = W`, identified with `f₃` by `ι = id`; empty edge / circle stages. -/
def slimLoopBoundaryKernel_LND :
    BoundaryExitsKernel_LND slimLoopBoundaryData_LND (fun i => i.elim0) where
  Et := BoundaryTori.empty slimWc
  labels_eq := fun i => i.elim0
  zero := slimZero
  zero_link := ⟨finCongr rfl, fun i => i.elim0⟩
  cusp := slimCusps
  cusp_link := fun i => i.elim0
  slim := slimLoopStage74
  edge := EdgeStage74.empty slimWc
  circle := StageProj74.empty slimWc 2
  ιslim := id
  ιedge := fun b => PEmpty.elim b
  ιcircle := fun b => PEmpty.elim b
  slim_ident := ⟨Topology.IsEmbedding.id, fun _ => rfl, TopologicalSpace.Opens.coe_top⟩
  edge_ident := stageIdentSrc_of_parent_bot_LND _ rfl _ _
  circle_ident := stageIdentSrc_of_parent_bot_LND _ rfl _ _
  edge_range := by
    rintro y ⟨b, -⟩
    exact isEmptyElim b
  circle_range := by
    rintro y ⟨b, -⟩
    exact isEmptyElim b
  edge_height := fun x => (CircleRegion.false_of_bot slimWc x).elim
  edge_level := rfl
  cut := slimLoopCutChoice74
  cut_D₃ := image_id _
  cut_C₂ := (image_empty _).trans (image_empty _).symm
  cut_C₁ := (image_empty _).trans (image_empty _).symm
  comp := Equiv.refl _
  comp_eq := fun _ => image_id _
  edgePiece_eq := empty_inter_inter_LND _ _
  geometry := slimLoopCutGeometry74
  src1_eq := (empty_inter _).symm
  slimPiece_eq := univ_eq_inter_preimage_LND _
  M₁_eq := univ_eq_compl_interior_fin0_LND _ _
  M₂_eq := by
    change (∅ : Set slimWc.Carrier) = univ \ relInt univ univ
    rw [relativeInteriorUniv_c, Set.sdiff_self]
  remainder_eq := (empty_sdiff _).symm
  remainder_sat := (empty_inter _).symm

/-- **Consumer on the S² × S¹ loop**: the head gives rows whose slim union is `W`, with ONE slim
piece the whole `f₃`-preimage of the single component of `D₃ = S¹`, `M₁ = W`, `M₂ = ∅`. -/
theorem slimLoop_boundaryKernel_rows_LND :
    ∃ Rw : FC39RowsV2 slimWc (BoundaryTori.empty slimWc),
      Rw.slim.union = univ ∧
      (∃ σ : Fin Rw.slim.count ≃ ActualComponent (univ : Set Circle), ∀ j,
        range (Rw.slim.piece j).map = univ ∩ slimLoopQ_LND74 ⁻¹' (σ j).1) ∧
      regionM1 Rw.zero Rw.cusp = univ ∧ regionM2 Rw.slim = ∅ := by
  obtain ⟨Rw, -, -, hs, -, -, h1, h2, -⟩ := slimLoopBoundaryKernel_LND.rows_link
  exact ⟨Rw, hs.1, hs.2, h1, h2⟩

end GC.GraphManifold.Assembly.FC39P0.X136
