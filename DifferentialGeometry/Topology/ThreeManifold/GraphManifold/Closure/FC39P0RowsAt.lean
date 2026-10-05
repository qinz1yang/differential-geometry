import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0Junctions
import DifferentialGeometry.Geometry.Collapse.StaticRegisterValidity
import DifferentialGeometry.Geometry.Fibration.ActualGlobalBlockMap

/-!
# The prepared rows WITH provenance at a closed register (lane FC39-VAL; review 49, B.1, B.7)

Design `build-logs/resume/design-FC39-VAL.md` §3. Replaces the `opaque` placeholder `ClosedRowsAt`
of the FC39-P0 targets (`evidence/fc39-p0/Targets.lean.txt:64–65`). Review item R-b: the record is
indexed by the member's METRIC `g` and the order `K` (the analytic chain lives on `(W, g)`; a metric
field would be arbitrary), so wrapper (1) passes `(g m)` and `K`.

`ClosedRowsAt K R W g E` carries, as DATA, the analytic chain's outputs on the member and the
identification of the rows with them (task-47 draft §4.3, review 49 Q2 "成立"):

* (P1) the analytic input: a normalized model of the member and ONE instance of the final family
  `LocalChartPacketsC14` at EXACTLY the register's parameters (`ClosedFamilyInstance`, with
  `V = R.split.V`, `T = R.split.T₀`), with its outputs `δ, εr < cap, Λz`, `20 Λz ≤ T₀`;
* (P2) the chain's map: CGP01's original block map `𝓔⁰ = F` of that instance
  (`ClosedFamilyInstance.originalMap`, `ActualGlobalBlockMap.lean:406`) and GAF02's adjusted map `E`
  on the member with (AE)'s value estimate `|E − F| < c₃ ρ` (B:5797–5808);
* (P3) the rows `FC39RowsV2 W E` and their provenance: every zero domain sits at an actual selected
  zero centre of the family (injectively) with ZSP02's inclusions (ZB) at its radius (B:6382–6384),
  and (B.7) on its boundary buffer the GLOBAL ratio is the RETAINED ratio `u_i(E)/v_i(E) − .4` of
  the adjusted zero block ((ZF)/(ZH), B:6388–6392, B:6458–6465); the edge bundle's level is `4Δ`
  (EDP04 (EV), FDC02).

Provenance items still waiting for their native Lean objects (design §4): the stage base maps
`f₁ = π₁E`, `f₂ = π₂E` and the final height `T` of EDP01 (GAF02's stage maps are not in Lean yet),
the retained whole circle fibres (GAF07), the derivative part of (AE), and the global form
`h₁ = ψ(η) + χ(η)(r − η)` of the zero ratio. They are added in later files, never as hypotheses.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open DifferentialGeometry.Geometry.Collapse
open scoped Manifold ContDiff Topology

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

namespace DifferentialGeometry.Geometry.Collapse.ClosedFamilyInstance

variable {K : ℕ} {D : ClosedEarlyData} {T : ClosedThresholds D} {R : ClosedRegister D T}
  {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g}
  {δ εr Λz : ℝ}

/-- The model metrics of the zero kind of the instance (keyed to `ClosedFamilyInstance`). -/
instance instMetricN_VAL (F : ClosedFamilyInstance K R M δ εr Λz) (b : M.X) :
    MetricSpace (F.family.N b) :=
  F.family.instMetricN b

/-- The model atlases of the zero kind of the instance (keyed to `ClosedFamilyInstance`). -/
instance instChartedN_VAL (F : ClosedFamilyInstance K R M δ εr Λz) (b : M.X) :
    ChartedSpace E3 (F.family.N b) :=
  F.family.instChartedN b

/-- The cone metrics of the zero kind of the instance (keyed to `ClosedFamilyInstance`). -/
instance instMetricC_VAL (F : ClosedFamilyInstance K R M δ εr Λz) (b : M.X) :
    MetricSpace (F.family.C b) :=
  F.family.instMetricC b

/-- The tags of CGP01's original block map of the instance (circle, slim, edge and zero centres,
`ρ`, `E'`). -/
abbrev Tag (F : ClosedFamilyInstance K R M δ εr Λz) : Type :=
  CGPTag F.family.toLocalChartFamily F.family.zero

/-- CGP01's original block map `𝓔⁰ = F` of the instance (defined ONCE in
`ActualGlobalBlockMap.lean:406`). -/
def originalMap (F : ClosedFamilyInstance K R M δ εr Λz) :
    M.X → BlockSpace (fun _ : F.Tag => ℝ²) :=
  cgpGlobalMap F.family.toLocalChartFamily F.family.zero

/-- The tag of a selected zero centre. -/
def zeroTag (F : ClosedFamilyInstance K R M δ εr Λz) (c : M.X) (hc : c ∈ F.family.zero.centres) :
    F.Tag :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨c, (Set.Finite.mem_toFinset _).mpr hc⟩)))

/-- The radius `R_i` of the selected zero ball at `c`. -/
def zeroRadius (F : ClosedFamilyInstance K R M δ εr Λz) (c : M.X)
    (hc : c ∈ F.family.zero.centres) : ℝ :=
  (F.family.zero.zero c hc).radius

/-- The axis coordinate `u` of a zero block (FC01: the block is `(R ζ η, R ζ)` with `η` on the axis
`planeAxis`). -/
def blockU (F : ClosedFamilyInstance K R M δ εr Λz) (y : BlockSpace (fun _ : F.Tag => ℝ²))
    (t : F.Tag) : ℝ :=
  @inner ℝ ℝ² _ (y t).fst (planeAxis 1)

/-- The marker `v` of a block. -/
def blockV (F : ClosedFamilyInstance K R M δ εr Λz) (y : BlockSpace (fun _ : F.Tag => ℝ²))
    (t : F.Tag) : ℝ :=
  (y t).snd

end DifferentialGeometry.Geometry.Collapse.ClosedFamilyInstance

namespace GC.GraphManifold.Assembly.FC39P0

/-- **The prepared rows with provenance at a closed register** (review 49, B.1 / B.7): the analytic
input on the member (P1), the chain's maps (P2), the rows and their identification (P3). -/
structure ClosedRowsAt (K : ℕ) {D : ClosedEarlyData} {T : ClosedThresholds D}
    (R : ClosedRegister D T) (W : CompactCarrier.{u})
    (g : SmoothRiemannianMetric W.model W.Carrier) (E : BoundaryTori W 0) : Type (u + 1) where
  /-- The member is closed. -/
  facts : ClosedMemberFacts W
  /-- (P1) the normalized model of the member. -/
  model : ClosedModel W g
  /-- (P1) the producer's analytic outputs. -/
  δ : ℝ
  εr : ℝ
  Λz : ℝ
  δ_pos : 0 < δ
  εr_pos : 0 < εr
  εr_lt : εr < R.famCap
  Λz_pos : 0 < Λz
  shell : 20 * Λz ≤ R.later.split.T₀
  /-- (P1) the final family at `R` on this member. -/
  inst : ClosedFamilyInstance K R model δ εr Λz
  /-- (P2) GAF02's adjusted map `E = Ψ₃Ψ₂Ψ₁F` (same block target as `F`). -/
  adjusted : W.Carrier → BlockSpace (fun _ : inst.Tag => ℝ²)
  /-- (P2) (AE), value part: `|E − F| < c₃ ρ`. -/
  adjusted_close : ∀ x : model.X,
    ‖adjusted (model.ψ x) - inst.originalMap x‖ < R.stage.c 2 * inst.ρ x
  /-- (P3) the revised rows. -/
  rows : FC39RowsV2 W E
  /-- (P3) the selected zero centre of each zero domain. -/
  zeroCentre : Fin rows.zero.count → model.X
  zeroCentre_mem : ∀ i, zeroCentre i ∈ inst.family.zero.centres
  zeroCentre_injective : Function.Injective zeroCentre
  /-- (P3) ZSP02 (ZB), inner inclusion: `B̄(p_i, .38 R_i) ⊆ int Z_i`. -/
  zero_inner : ∀ i, closedBall (zeroCentre i) (38 / 100 * inst.zeroRadius _ (zeroCentre_mem i)) ⊆
    model.ψ ⁻¹' interior (range (rows.zero.piece i).map)
  /-- (P3) ZSP02 (ZB), outer inclusion: `Z_i ⊆ B(p_i, .42 R_i)`. -/
  zero_outer : ∀ i, model.ψ ⁻¹' range (rows.zero.piece i).map ⊆
    ball (zeroCentre i) (42 / 100 * inst.zeroRadius _ (zeroCentre_mem i))
  /-- (P3) B.7: on the boundary buffer the GLOBAL ratio is the RETAINED ratio `u_i(E)/v_i(E) − .4`
  of the adjusted zero block. -/
  ratio_buffer : ∀ i, ∀ x ∈ rows.zero.near i,
    rows.zero.ratio i x =
      inst.blockU (adjusted x) (inst.zeroTag (zeroCentre i) (zeroCentre_mem i)) /
        inst.blockV (adjusted x) (inst.zeroTag (zeroCentre i) (zeroCentre_mem i)) - 2 / 5
  /-- (P3) EDP04 (EV) / FDC02: the edge disk bundle's level is `4Δ`. -/
  edge_level : rows.edge.level = 4 * R.later.excl.Δ

namespace ClosedRowsAt

variable {K : ℕ} {D : ClosedEarlyData} {T : ClosedThresholds D} {R : ClosedRegister D T}
  {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier} {E : BoundaryTori W 0}

/-- The rows forget their provenance. -/
def toRows (P : ClosedRowsAt K R W g E) : FC39RowsV2 W E :=
  P.rows

/-- **Consumer (B.7)**: on the boundary buffer of a zero domain, its boundary — the zero set of the
global ratio — is the level `u_i(E) = .4 v_i(E)` of the adjusted zero block (ZSP02 (ZF)), once the
marker is nonzero there. -/
theorem boundary_eq_retained_level_VAL {P : ClosedRowsAt K R W g E} {i : Fin P.rows.zero.count}
    {x : W.Carrier} (hx : x ∈ P.rows.zero.near i)
    (hv : P.inst.blockV (P.adjusted x) (P.inst.zeroTag (P.zeroCentre i) (P.zeroCentre_mem i)) ≠ 0) :
    x ∈ pieceBoundary (P.rows.zero.piece i) ↔
      P.inst.blockU (P.adjusted x) (P.inst.zeroTag (P.zeroCentre i) (P.zeroCentre_mem i)) =
        2 / 5 * P.inst.blockV (P.adjusted x)
          (P.inst.zeroTag (P.zeroCentre i) (P.zeroCentre_mem i)) := by
  rw [P.rows.zero.boundary_eq i, mem_ofPred_eq, P.ratio_buffer i x hx, sub_eq_zero,
    div_eq_iff hv]

/-- **Consumer**: the centre of a zero domain lies in its interior (ZB at radius `0`). -/
theorem centre_mem_interior_VAL (P : ClosedRowsAt K R W g E) (i : Fin P.rows.zero.count) :
    P.model.ψ (P.zeroCentre i) ∈ interior (range (P.rows.zero.piece i).map) := by
  have hR : 0 ≤ 38 / 100 * P.inst.zeroRadius _ (P.zeroCentre_mem i) := by
    have h := (P.inst.family.zero.radius_mem _ (P.zeroCentre_mem i)).1
    have hT : 0 < R.later.split.T₀ :=
      lt_of_lt_of_le (by have := R.later.hundred_lt_Δ; unfold closedLongLength; positivity)
        R.later.longLength_le_T₀
    have hρ := P.inst.ρ_pos (P.zeroCentre i)
    unfold ClosedFamilyInstance.zeroRadius
    nlinarith
  exact P.zero_inner i (mem_closedBall_self hR)

end ClosedRowsAt

end GC.GraphManifold.Assembly.FC39P0
