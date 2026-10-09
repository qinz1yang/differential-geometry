import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.ExtPortCuspsXPI
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0Edges

/-!
# FC39 external-port regression instance: zero domains, the slim piece, the empty edge bundle

On the carrier `T² × I` of `ExtPortCuspsXPI.lean`:

* `extportZeroDomains_XPI` — no zero domain;
* `extportSlim_XPI` — ONE slim piece, the torus interval `1 ≤ rad ≤ 3/2` (`slimRadii_XPI`):
  its end `false` (`rad = 1`) is SHARED with the internal model face of the inner cusp `1`, its end
  `true` (`rad = 3/2`) is NEW, with end function `rad² − 9/4` on `|rad − 3/2| < 1/4`;
* `extportEdgeBundle_XPI` — the empty edge bundle (empty base, empty source) and its component
  export `extportEdgeModels_XPI` (no interval, no circle component).
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0.ExtPortXPI

local instance carrierCharts_XPI'' :
    ChartedSpace (EuclideanHalfSpace 3) carrierW_XPI.Carrier := by
  change ChartedSpace (EuclideanHalfSpace 3) (productSet.{0} 2)
  exact inferInstance

/-! ## No zero domain -/

/-- **The zero domains of the external-port instance: none.** -/
def extportZeroDomains_XPI : ZeroDomains carrierW_XPI where
  count := 0
  piece i := i.elim0
  disjoint i := i.elim0
  ratio i := i.elim0
  near i := i.elim0
  near_interior i := i.elim0
  ratio_smooth i := i.elim0
  ratio_regular i := i.elim0
  zero_subset_near i := i.elim0
  boundary_eq i := i.elim0
  range_eq i := i.elim0
  model i := i.elim0

/-! ## The slim torus interval -/

/-- The slim band `1 ≤ rad ≤ 3/2` (end `false` at `rad = 1`, end `true` at `rad = 3/2`). -/
def slimRadii_XPI : BandRadii_XPI where
  r0 := 1
  r1 := 3 / 2
  twist := 0
  r0_ge := by norm_num
  r0_le := by norm_num
  r1_ge := by norm_num
  r1_le := by norm_num
  ne := by norm_num

/-- The slim piece. -/
def slimPiece_XPI : PieceEmbedding carrierW_XPI := bandPiece_XPI slimRadii_XPI

/-- The slim model: the torus interval of the band product. -/
def slimModel_XPI : SlimModel slimPiece_XPI := .torusInterval (bandProduct_XPI slimRadii_XPI)

theorem range_slimPiece_XPI :
    range slimPiece_XPI.map = {x | 1 ≤ rad_XPI x ∧ rad_XPI x ≤ 3 / 2} := by
  rw [slimPiece_XPI, range_bandPiece_XPI]
  ext x
  change (rad_XPI x - 1) * (rad_XPI x - 3 / 2) ≤ 0 ↔ _
  constructor
  · intro h
    constructor
    · by_contra hlt
      rw [not_le] at hlt
      have : 0 < (rad_XPI x - 1) * (rad_XPI x - 3 / 2) :=
        mul_pos_of_neg_of_neg (by linarith) (by linarith)
      linarith
    · by_contra hlt
      rw [not_le] at hlt
      have : 0 < (rad_XPI x - 1) * (rad_XPI x - 3 / 2) := mul_pos (by linarith) (by linarith)
      linarith
  · rintro ⟨h1, h2⟩
    exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)

/-- The ambient image of the slim end `b`: `rad = 1` (`false`) or `rad = 3/2` (`true`). -/
theorem slimEnd_image_XPI (b : Bool) :
    slimPiece_XPI.map '' slimModelEnd slimModel_XPI b =
      {x | rad_XPI x = bandEndRadius_XPI slimRadii_XPI b} := by
  refine ((range_comp _ _).symm).trans ?_
  exact range_bandEnd_map_XPI slimRadii_XPI b

/-- The shared neighbour face of the slim end `false`: the internal model face of the inner
cusp `1`. -/
def slimSharedFace_XPI : NeighbourFace extportZeroDomains_XPI extportCuspCores_XPI :=
  .inr ⟨1, ⟨extportCuspCores_XPI.internalModelFace 1, rfl⟩⟩

/-- The end kinds: `false` shared with the inner cusp, `true` new. -/
def slimEndKind_XPI (e : SlimEnd fun _ : Fin 1 => slimModel_XPI) :
    Option (NeighbourFace extportZeroDomains_XPI extportCuspCores_XPI) :=
  cond e.1.2 none (some slimSharedFace_XPI)

theorem slimEndKind_eq_none_iff_XPI {e : SlimEnd fun _ : Fin 1 => slimModel_XPI} :
    slimEndKind_XPI e = none ↔ e.1.2 = true := by
  unfold slimEndKind_XPI
  cases e.1.2 <;> simp

/-- The slim end function `rad² − 9/4`. -/
def slimEndFn_XPI : carrierW_XPI.Carrier → ℝ := carrierRadialFn_XPI (-(9 / 4)) 1

/-- The slim end neighbourhood `|rad − 3/2| < 1/4`. -/
def slimEndNear_XPI : TopologicalSpace.Opens carrierW_XPI.Carrier :=
  ⟨{x | |rad_XPI x - 3 / 2| < 1 / 4},
    isOpen_lt (continuous_abs.comp (continuous_rad_XPI.sub continuous_const)) continuous_const⟩

theorem slimEndNear_interior_XPI :
    (slimEndNear_XPI : Set carrierW_XPI.Carrier) ⊆ carrierW_XPI.interior := by
  intro x hx
  have hx' := abs_lt.mp (show |rad_XPI x - 3 / 2| < 1 / 4 from hx)
  exact mem_carrier_interior_XPI (by linarith [hx'.1]) (by linarith [hx'.2])

theorem slimEndFn_eq_XPI (x : carrierW_XPI.Carrier) :
    slimEndFn_XPI x = rad_XPI x ^ 2 - 9 / 4 := by
  rw [slimEndFn_XPI, carrierRadialFn_XPI]
  ring

theorem slimEnd_level_XPI :
    {x : carrierW_XPI.Carrier | rad_XPI x = 3 / 2} =
      {x | x ∈ slimEndNear_XPI ∧ slimEndFn_XPI x = 0} := by
  ext x
  have hx := rad_pos_XPI x
  constructor
  · intro h
    have h' : rad_XPI x = 3 / 2 := h
    refine ⟨?_, ?_⟩
    · change |rad_XPI x - 3 / 2| < 1 / 4
      rw [h', sub_self, abs_zero]
      norm_num
    · rw [slimEndFn_eq_XPI, h']
      norm_num
  · rintro ⟨-, h⟩
    rw [slimEndFn_eq_XPI] at h
    have h3 : (rad_XPI x - 3 / 2) * (rad_XPI x + 3 / 2) = 0 := by
      rw [← sub_eq_zero.mpr (show rad_XPI x ^ 2 = 9 / 4 by linarith)]
      ring
    exact sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_right (by linarith))

theorem slimEnd_sublevel_XPI :
    range slimPiece_XPI.map ∩ slimEndNear_XPI =
      {x | x ∈ slimEndNear_XPI ∧ slimEndFn_XPI x ≤ 0} := by
  rw [range_slimPiece_XPI]
  ext x
  have hx := rad_pos_XPI x
  constructor
  · rintro ⟨⟨-, h2⟩, h3⟩
    refine ⟨h3, ?_⟩
    rw [slimEndFn_eq_XPI]
    nlinarith
  · rintro ⟨h3, h4⟩
    have h3' := abs_lt.mp (show |rad_XPI x - 3 / 2| < 1 / 4 from h3)
    rw [slimEndFn_eq_XPI] at h4
    refine ⟨⟨by linarith [h3'.1], ?_⟩, h3⟩
    nlinarith

/-- **The slim piece of the external-port instance**: one torus interval, end `false` shared with
the inner cusp, end `true` new. -/
def extportSlim_XPI : SlimPiecesV2 carrierW_XPI extportZeroDomains_XPI extportCuspCores_XPI where
  count := 1
  piece _ := slimPiece_XPI
  model _ := slimModel_XPI
  disjoint j j' h := (h (Subsingleton.elim j j')).elim
  endFace e := bandModelFace_XPI slimRadii_XPI e.1.2
  endFace_eq _ := rfl
  endFace_exhausted j F := by
    rcases bandModelFace_cases_XPI slimRadii_XPI F with h | h
    · exact ⟨false, trivial, h.symm⟩
    · exact ⟨true, trivial, h.symm⟩
  endKind := slimEndKind_XPI
  endFn _ := slimEndFn_XPI
  endNear _ := slimEndNear_XPI
  endNear_interior _ := slimEndNear_interior_XPI
  endFn_smooth _ := (contMDiff_carrierRadialFn_XPI _ _).contMDiffOn
  endFn_regular _ x _ _ := carrierRadialFn_regular_XPI one_ne_zero x
  endFn_level e := by
    have he : e.1.1.2 = true := (slimEndKind_eq_none_iff_XPI (e := e.1)).mp e.2
    change slimPiece_XPI.map '' slimModelEnd slimModel_XPI e.1.1.2 = _
    rw [he, slimEnd_image_XPI]
    exact slimEnd_level_XPI
  endFn_eq _ := slimEnd_sublevel_XPI

theorem extportSlim_piece_XPI (j : Fin 1) : extportSlim_XPI.piece j = slimPiece_XPI :=
  rfl

/-! ## The empty edge bundle -/

theorem not_mem_bot_XPI {X : Type*} [TopologicalSpace X] (x : X) :
    x ∉ (⊥ : TopologicalSpace.Opens X) := by
  simp

instance isEmpty_bot_XPI {X : Type*} [TopologicalSpace X] :
    IsEmpty (⊥ : TopologicalSpace.Opens X) :=
  ⟨fun x => not_mem_bot_XPI x.1 x.2⟩

/-- The empty edge base. -/
abbrev emptyEdgeBase_XPI : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 1)) := ⊥

/-- **The empty edge bundle**: empty base, empty source, empty closed base. -/
def extportEdgeBundle_XPI : EdgeBundle carrierW_XPI where
  Base := emptyEdgeBase_XPI
  source := ⊥
  source_interior x hx := (not_mem_bot_XPI x hx).elim
  proj := ⟨isEmptyElim, continuous_of_discreteTopology⟩
  proj_smooth x := isEmptyElim x
  proj_submersion x := isEmptyElim x
  height := isEmptyElim
  height_smooth x := isEmptyElim x
  level := 0
  rank_two x := isEmptyElim x
  proper _ _ := by
    rw [Set.eq_empty_of_isEmpty {x : (⊥ : TopologicalSpace.Opens carrierW_XPI.Carrier) | _},
      image_empty]
    exact isCompact_empty
  fibre_disk c := isEmptyElim c
  cbase := ∅
  cbase_compact := isCompact_empty
  cbase_domain c hc := by
    rw [frontier_empty] at hc
    exact hc.elim

instance isEmpty_edgeBase_XPI : IsEmpty extportEdgeBundle_XPI.Base :=
  inferInstanceAs (IsEmpty emptyEdgeBase_XPI)

instance isEmpty_edgeEnd_XPI : IsEmpty extportEdgeBundle_XPI.EdgeEnd :=
  ⟨fun e => isEmptyElim e.1⟩

instance isEmpty_edgeBaseComponent_XPI : IsEmpty extportEdgeBundle_XPI.EdgeBaseComponent :=
  ⟨fun C => by
    obtain ⟨x, -, -⟩ := C.2
    exact isEmptyElim x⟩

theorem extportEdge_edgePiece_XPI : extportEdgeBundle_XPI.edgePiece = ∅ := by
  refine Set.eq_empty_of_forall_notMem ?_
  rintro x ⟨y, -, -⟩
  exact not_mem_bot_XPI _ y.2

/-- **The component export of the empty edge bundle**: no interval, no circle component. -/
def extportEdgeModels_XPI : EdgeComponentModels extportEdgeBundle_XPI where
  intervalCount := 0
  circleCount := 0
  componentEquiv := Equiv.equivOfIsEmpty _ _
  intervalBase i := i.elim0
  intervalBase_embedding i := i.elim0
  intervalBase_range i := i.elim0
  circleBase j := j.elim0
  circleBase_embedding j := j.elim0
  circleBase_range j := j.elim0
  endpointEquiv := Equiv.equivOfIsEmpty _ _
  endpointEquiv_apply i := i.elim0
  intervalTriv i := i.elim0
  intervalTriv_range i := i.elim0
  intervalTriv_proj i := i.elim0
  intervalTriv_disk i := i.elim0
  intervalTriv_rim i := i.elim0
  circleTriv j := j.elim0
  circleTriv_smooth j := j.elim0
  circleTriv_mfderiv j := j.elim0
  circleTriv_injective j := j.elim0
  circleTriv_range j := j.elim0
  circleTriv_proj j := j.elim0
  circleTriv_disk j := j.elim0
  circleTriv_rim j := j.elim0

end GC.GraphManifold.Assembly.FC39P0.ExtPortXPI
