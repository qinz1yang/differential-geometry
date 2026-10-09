import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0Junctions
import DifferentialGeometry.Geometry.Collapse.BoundaryRegisterValidity

/-!
# The prepared rows WITH provenance at a boundary register (lane FC39-VAL; review 49, B.1)

Design `build-logs/resume/design-FC39-VAL.md` §3. Replaces the `opaque` placeholder `BoundaryRowsAt`
of the FC39-P0 targets (`evidence/fc39-p0/Targets.lean.txt:68–70`). Review item R-b: the record is
indexed by `K`, `A`, the index `m`, the member's metric `g` and its nearly cuspidal boundary `B`
(all in scope in wrapper (4), `Targets.lean.txt:146–154`).

`BoundaryRowsAt K A R m W g B E` carries, as DATA:

* (P1) a universe-`0` model of the member (`BoundaryModel`), LC88's export packet on it with
  `P.cusp = B₀` (the transported boundary), and the rest of T3's per-member conclusion for THIS
  packet at the register's interior values (`BoundaryPacketRest`, verbatim T3);
* (P3) the rows `FC39RowsV2 W E`, the ports (`range (E.torusMap i) = B.component i`) and the cusp
  provenance: every cusp core is the retained piece `{level_b ≤ 90}` of the packet's collar (the
  `level_sublevel_eq` / `retained` fields of `BoundaryCollarPacket`) and its defining function is
  `level_b − 90` on its neighbourhood.

Waiting (design §4): the zero / edge / circle provenance of the interior blocks (the interior family
`LocalPacketsOn` is an existential inside T3's conclusion; a data form of T3 is needed), the
boundary adjusted map of BCG04, and the universe-`0` boundary model itself.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open DifferentialGeometry.Geometry.Collapse
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

/-- **The prepared rows with provenance at a boundary register** (separated branch). -/
structure BoundaryRowsAt (K : ℕ) (A : ℝ → ℝ) {D : BoundaryEarlyData} {T : BoundaryThresholds D}
    (R : BoundaryRegister D T) (m : ℕ) (W : CompactCarrier.{u})
    (g : SmoothRiemannianMetric W.model W.Carrier)
    (B : NearlyCuspidalBoundary W g K (boundaryCounterexampleRatio D.δStar m))
    (E : BoundaryTori W B.count) : Type (u + 1) where
  /-- (P1) the universe-`0` model of the member. -/
  model : BoundaryModel W g B
  /-- (P1) the producer's analytic outputs. -/
  δ : ℝ
  εr : ℝ
  δ_pos : 0 < δ
  εr_pos : 0 < εr
  εr_lt : εr < 1 / 4
  /-- (P1) LC88's export packet on the model. -/
  packet : letI := model.connected₀
    BoundaryExportPacket model.W₀ model.g₀ K A (boundaryCounterexampleRatio D.δStar m) R.famεB
  packet_cusp : packet.cusp = model.B₀
  /-- (P1) the rest of T3's conclusion for THIS packet at the register's interior values. -/
  rest : letI := model.connected₀
    BoundaryPacketRest model.W₀ model.g₀ K A (boundaryCounterexampleRatio D.δStar m) R.famεB packet
      R.later.scale.Λ R.later.scale.w R.toClosedRegister.famβ R.later.excl.Δ
      R.toClosedRegister.famσs R.toClosedRegister.famσc R.later.err.μ R.later.split.b
      R.toClosedRegister.fams R.toClosedRegister.famb' R.toClosedRegister.fams'
      R.toClosedRegister.famε R.toClosedRegister.famγc R.toClosedRegister.famβc
      R.toClosedRegister.famLmax R.later.err.τ R.later.circle.γ δ εr R.later.err.e₀
      R.later.split.T₀ R.later.split.V
  /-- (P3) the revised rows. -/
  rows : FC39RowsV2 W E
  /-- (P3) the ports are the boundary components of `B`. -/
  ports : ∀ i, range (E.torusMap i) = B.component i
  /-- (P3) each cusp core is the retained piece `{level ≤ 90}` of the packet's collar. -/
  cusp_piece : ∀ b : Fin B.count, range (rows.cusp.piece b).map =
    model.ψ '' {y | packet.level (Fin.cast (by rw [packet_cusp]; exact model.count_eq.symm) b) y ≤
      90}
  /-- (P3) its defining function is `level − 90` on its neighbourhood. -/
  cusp_fn : ∀ b : Fin B.count, ∀ x ∈ rows.cusp.near b, rows.cusp.cuspFn b x =
    packet.level (Fin.cast (by rw [packet_cusp]; exact model.count_eq.symm) b) (model.ψ.symm x) -
      90

namespace BoundaryRowsAt

variable {K : ℕ} {A : ℝ → ℝ} {D : BoundaryEarlyData} {T : BoundaryThresholds D}
  {R : BoundaryRegister D T} {m : ℕ} {W : CompactCarrier.{u}}
  {g : SmoothRiemannianMetric W.model W.Carrier}
  {B : NearlyCuspidalBoundary W g K (boundaryCounterexampleRatio D.δStar m)}
  {E : BoundaryTori W B.count}

/-- The rows forget their provenance. -/
def toRows (P : BoundaryRowsAt K A R m W g B E) : FC39RowsV2 W E :=
  P.rows

/-- **Consumer**: the internal face of a cusp core is the level `90` of the packet (on its
neighbourhood). -/
theorem internal_eq_level_VAL (P : BoundaryRowsAt K A R m W g B E) (b : Fin B.count) :
    (range fun t => (P.rows.cusp.piece b).map (P.rows.cusp.product b (t, iccEnd true))) =
      {x | x ∈ P.rows.cusp.near b ∧
        P.packet.level (Fin.cast (by rw [P.packet_cusp]; exact P.model.count_eq.symm) b)
          (P.model.ψ.symm x) = 90} := by
  rw [P.rows.cusp.internal_eq b]
  ext x
  simp only [mem_ofPred_eq]
  constructor
  · rintro ⟨hx, h0⟩
    exact ⟨hx, by rw [P.cusp_fn b x hx] at h0; linarith⟩
  · rintro ⟨hx, h90⟩
    exact ⟨hx, by rw [P.cusp_fn b x hx]; linarith⟩

end BoundaryRowsAt

end GC.GraphManifold.Assembly.FC39P0
