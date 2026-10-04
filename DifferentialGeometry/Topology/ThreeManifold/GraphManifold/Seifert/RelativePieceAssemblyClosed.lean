import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.RelativePieceAssembly
import DifferentialGeometry.Topology.Manifold.SmoothBoundaryAtlas.Tangent

/-!
# Relative piece assembly with closed pieces

Packet BA of the X38 survey, the general case of the frozen `exists_piecewisePresentation`
(review 20 §6.3: zero-port closed components must be handled, not assumed away).

If the cut carrier of `T` has kind `.withBoundary`, `exists_piecewisePresentation_of_withBoundary`
applies. Otherwise `T` has no seam and no external torus, its pieces are closed and own no side
(`isEmpty_ownedSide_of_kind_ne`), and the local presentations may have either kind. The common
kind is then `.withBoundary`: a local presentation of kind `.withBoundary` is used as it is, and a
local presentation of kind `.closed` has no seam, so its closed component is represented by itself
with a half-space atlas. That atlas (`univBoundaryAtlas`) is a `SmoothBoundaryAtlas` of `univ` in
a boundaryless manifold modelled on `ℝ³`: at `x` the extended chart, restricted to
`{v | v 0 > φ x 0 - 1}` and translated by `(φ x 0 - 1) e₀` (`shiftedChart`), takes values in
`{v | 0 < v 0}`, so every point is an interior point (`univBoundaryAtlas_isInteriorPoint`). With
it, `closedCutSystem` is the one-piece cut system of kind `.withBoundary` of a connected closed
carrier (no seams, no external tori; smooth inclusion with bijective differential by the atlas,
read through `recastCarrier`), and `LocalCutSystem.ofClosed` is its local system.
-/

set_option autoImplicit false

noncomputable section
open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert

section ShiftedAtlas

variable {X : Type*} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
  [IsManifold (𝓡 3) ∞ X]

private def shiftDiffeomorph (a : ℝ) :
    EuclideanSpace ℝ (Fin 3) ≃ₘ⟮𝓡 3, 𝓡 3⟯ EuclideanSpace ℝ (Fin 3) where
  toEquiv := Equiv.subRight (a • EuclideanSpace.single 0 1)
  contMDiff_toFun := (contDiff_id.sub contDiff_const).contMDiff
  contMDiff_invFun := (contDiff_id.add contDiff_const).contMDiff

private theorem shiftDiffeomorph_apply_zero (a : ℝ) (v : EuclideanSpace ℝ (Fin 3)) :
    shiftDiffeomorph a v 0 = v 0 - a := by
  change ((v - a • EuclideanSpace.single (0 : Fin 3) (1 : ℝ) : EuclideanSpace ℝ (Fin 3))) 0 =
    v 0 - a
  simp

omit [IsManifold (𝓡 3) ∞ X] in
private def shiftedSource (x : X) : Set X :=
  (extChartAt (𝓡 3) x).source ∩
    (extChartAt (𝓡 3) x) ⁻¹' {v | extChartAt (𝓡 3) x x 0 - 1 < v 0}

omit [IsManifold (𝓡 3) ∞ X] in
private theorem isOpen_shiftedSource (x : X) : IsOpen (shiftedSource x) :=
  (continuousOn_extChartAt x).isOpen_inter_preimage (isOpen_extChartAt_source x)
    (isOpen_lt continuous_const ((EuclideanSpace.proj (0 : Fin 3)).continuous))

private def shiftedChart (x : X) :
    _root_.PartialDiffeomorph (𝓡 3) (𝓡 3) X (EuclideanSpace ℝ (Fin 3)) ∞ :=
  (DifferentialGeometry.Topology.PartialDiffeomorph.restrict
    (DifferentialGeometry.Topology.PartialDiffeomorph.extendedChart x) (shiftedSource x)
      (isOpen_shiftedSource x)).trans
    (shiftDiffeomorph (extChartAt (𝓡 3) x x 0 - 1)).toPartialDiffeomorph

private theorem shiftedChart_source (x : X) : (shiftedChart x).source = shiftedSource x := by
  ext y
  change (y ∈ (extChartAt (𝓡 3) x).source ∧ y ∈ shiftedSource x) ∧ True ↔ _
  exact ⟨fun h => h.1.2, fun h => ⟨⟨h.1, h⟩, trivial⟩⟩

private theorem shiftedChart_apply_zero (x y : X) :
    shiftedChart x y 0 = extChartAt (𝓡 3) x y 0 - (extChartAt (𝓡 3) x x 0 - 1) :=
  shiftDiffeomorph_apply_zero _ _

private theorem shiftedChart_pos (x : X) {y : X} (hy : y ∈ (shiftedChart x).source) :
    0 < shiftedChart x y 0 := by
  rw [shiftedChart_source] at hy
  rw [shiftedChart_apply_zero]
  have := hy.2
  change extChartAt (𝓡 3) x x 0 - 1 < extChartAt (𝓡 3) x y 0 at this
  linarith

variable (X) in
def univBoundaryAtlas : SmoothBoundaryAtlas (𝓡 3) 3 (univ : Set X) where
  ambientChart x := shiftedChart x.val
  mem_source x := by
    rw [shiftedChart_source]
    refine ⟨mem_extChartAt_source x.val, ?_⟩
    change extChartAt (𝓡 3) x.val x.val 0 - 1 < extChartAt (𝓡 3) x.val x.val 0
    linarith
  mem_iff x y hy := ⟨fun _ => (shiftedChart_pos x.val hy).le, fun _ => trivial⟩

theorem univBoundaryAtlas_isInteriorPoint (x : (univ : Set X)) :
    letI := (univBoundaryAtlas X).toChartedSpace
    (𝓡∂ 3).IsInteriorPoint x := by
  let := (univBoundaryAtlas X).toChartedSpace
  refine ((𝓡∂ 3).isInteriorPoint_iff_not_isBoundaryPoint x).mpr fun h => ?_
  have h1 := ((univBoundaryAtlas X).isBoundaryPoint_iff x).mp h
  change shiftedChart x.val x.val 0 = 0 at h1
  rw [shiftedChart_apply_zero] at h1
  linarith

end ShiftedAtlas

section Closed

theorem recast_mfderiv_right (C : CompactCarrier.{u}) (k : CarrierModel) (h : C.kind = k)
    {F G Y : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace G]
    {J : ModelWithCorners ℝ F G} [TopologicalSpace Y] [ChartedSpace G Y]
    (f : Y → (recastCarrier C k h).Carrier) (y : Y) :
    @Eq (F →L[ℝ] EuclideanSpace ℝ (Fin 3)) (mfderiv J (recastCarrier C k h).model f y)
      (mfderiv J C.model (fun z => @id C.Carrier (f z)) y) := by
  subst h
  rfl

def closedCutSystem (C : CompactCarrier.{u}) (hC : C.kind = .closed) [ConnectedSpace C.Carrier] :
    EmbeddedCutSystem C .withBoundary := by
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) C.Carrier := (recastCarrier C .closed hC).charts
  letI : IsManifold (𝓡 3) ∞ C.Carrier := (recastCarrier C .closed hC).smooth
  letI : ChartedSpace CarrierModel.withBoundary.Space (univ : Set C.Carrier) :=
    (univBoundaryAtlas C.Carrier).toChartedSpace
  letI : IsManifold CarrierModel.withBoundary.model ∞ (univ : Set C.Carrier) :=
    (univBoundaryAtlas C.Carrier).isManifold
  exact {
    count := 1
    count_pos := Nat.one_pos
    Piece _ := (univ : Set C.Carrier)
    charts _ := inferInstance
    manifold _ := inferInstance
    compact _ := isCompact_iff_compactSpace.mp isCompact_univ
    connected _ := isConnected_iff_connectedSpace.mp isConnected_univ
    map _ := Subtype.val
    smooth _ := (recast_contMDiff_iff_right C .closed hC
      (Subtype.val : ↥(univ : Set C.Carrier) → C.Carrier)).mp
      (univBoundaryAtlas C.Carrier).contMDiff_subtype_val
    mfderiv_bijective _ q := (recast_mfderiv_right C .closed hC
      (J := CarrierModel.withBoundary.model)
      (Subtype.val : ↥(univ : Set C.Carrier) → C.Carrier) q) ▸
      (univBoundaryAtlas C.Carrier).mfderiv_subtypeVal_bijective q
    covers := Set.eq_univ_of_forall fun x => Set.mem_iUnion.mpr ⟨0, ⟨x, trivial⟩, rfl⟩
    torusCount _ := 0
    collar _ l := l.elim0
    collar_source _ l := l.elim0
    collar_disjoint _ l := l.elim0
    boundary_exhausted _ := by
      rw [Set.iUnion_of_empty]
      ext q
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hq
      exact ((𝓡∂ 3).isInteriorPoint_iff_not_isBoundaryPoint q).mp
        (univBoundaryAtlas_isInteriorPoint q) hq
    seamCount := 0
    side c := c.elim0
    externalCount := 0
    externalSide l := l.elim0
    sides_bijective := ⟨fun a => by
        rcases a with ⟨c, _⟩ | l <;> first | exact c.elim0 | exact l.elim0,
      fun b => b.2.elim0⟩
    matching c := c.elim0
    seam c := c.elim0
    seam_source c := c.elim0
    seam_neg c := c.elim0
    seam_pos c := c.elim0
    seam_interior c := c.elim0
    external_local l := l.elim0
    overlap j j' q q' h := by
      left
      obtain rfl : j = j' := Subsingleton.elim _ _
      rw [Subtype.ext h] }

end Closed

namespace TorusPresentation

variable {W : CompactCarrier.{u}} {T : TorusPresentation W}

theorem isEmpty_ownedSide_of_kind_ne (hT : T.cutCarrier.kind ≠ .withBoundary)
    (i : Fin T.components.count) : IsEmpty (T.OwnedSide i) := by
  refine ⟨fun s => ?_⟩
  rcases s with ⟨c | c | c, -⟩
  · exact (Fin.cast (T.pairing_count_eq_zero_of_kind_ne hT) c).elim0
  · exact (Fin.cast (T.pairing_count_eq_zero_of_kind_ne hT) c).elim0
  · exact (Fin.cast (T.externalCount_eq_zero_of_kind_ne hT) c).elim0

theorem component_kind_eq_closed (hT : T.cutCarrier.kind ≠ .withBoundary)
    (i : Fin T.components.count) : (T.Component i).kind = .closed := by
  change T.cutCarrier.kind = .closed
  cases h : T.cutCarrier.kind with
  | closed => rfl
  | withBoundary => exact absurd h hT

namespace LocalCutSystem

def ofClosed (hT : T.cutCarrier.kind ≠ .withBoundary) {i : Fin T.components.count}
    (R : TorusPresentation (T.Component i)) (hR : R.pairing.count = 0) :
    T.LocalCutSystem .withBoundary i R where
  system := @closedCutSystem (T.Component i) (component_kind_eq_closed hT i)
    (T.components.connected i)
  seamEquiv := finCongr hR.symm
  seam_eq c := c.elim0
  matching_eq c := c.elim0
  port :=
    { toFun := fun l => l.elim0
      invFun := fun s => (isEmpty_ownedSide_of_kind_ne hT i).elim s
      left_inv := fun l => l.elim0
      right_inv := fun s => (isEmpty_ownedSide_of_kind_ne hT i).elim s }
  port_collar l := l.elim0

end LocalCutSystem

end TorusPresentation

theorem exists_piecewisePresentation {W : CompactCarrier.{u}} (T : TorusPresentation W)
    (R : ∀ i, TorusPresentation (GC.Topology.componentCarrier T.cutCarrier T.components i))
    (port : ∀ i, Fin (R i).externalCount ≃ T.OwnedSide i)
    (hcollar : ∀ i j p, p ∈ halfCollarSource →
      ((R i).external.collar j p).val = T.pieceCollar i (port i j) p) :
    ∃ S : TorusPresentation W, ∃ hc : S.externalCount = T.externalCount,
      ∃ e : (Fin T.pairing.count ⊕ Σ i, Fin (R i).pairing.count) ≃ Fin S.pairing.count,
        (∀ j p, p ∈ halfCollarSource →
          S.external.collar (Fin.cast hc.symm j) p = T.external.collar j p) ∧
        (∀ j p, p ∈ signedCollarSource → S.seam (e (.inl j)) p = T.seam j p) ∧
        (∀ i j p, p ∈ signedCollarSource →
          S.seam (e (.inr ⟨i, j⟩)) p = T.pieceToCarrier i ((R i).seam j p)) ∧
        (∀ j, S.pairing.matching (e (.inl j)) = T.pairing.matching j) ∧
        (∀ i j, S.pairing.matching (e (.inr ⟨i, j⟩)) = (R i).pairing.matching j) := by
  by_cases hT : T.cutCarrier.kind = .withBoundary
  · exact T.exists_piecewisePresentation_of_withBoundary R port hcollar hT
  · refine TorusPresentation.LocalCutSystem.exists_piecewisePresentation
      (k := .withBoundary) fun i => ?_
    by_cases h : (R i).cutCarrier.kind = .withBoundary
    · exact TorusPresentation.LocalCutSystem.ofPresentation (R i) h (port i) (hcollar i)
    · exact TorusPresentation.LocalCutSystem.ofClosed hT (R i)
        ((R i).pairing_count_eq_zero_of_kind_ne h)

end GC.Seifert
