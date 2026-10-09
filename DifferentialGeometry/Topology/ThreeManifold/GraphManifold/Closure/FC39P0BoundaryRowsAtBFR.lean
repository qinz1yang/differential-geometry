import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0BoundaryRowsAt
import DifferentialGeometry.Geometry.Collapse.BoundaryPacketRestBFR
import DifferentialGeometry.Geometry.Collapse.BoundarySequenceStageOrder

/-!
# The prepared rows with provenance on the FINAL boundary family (lane FC39-BQ2; review 54 §6.4)

External review 54, §6.4 (dispositions row 6): the per-sequence records keep T3's product-or-
separation alternative and the SAME-packet provenance: `packet_cusp`, the cusp piece is the
packet's `{level ≤ 90}`, the defining function is `level − 90`. FC39-VAL's `BoundaryRowsAt`
(`FC39P0BoundaryRowsAt.lean:41–77`) is the separated-branch record on the V1 register and T3's
`LocalPacketsOn`; checked against T3B-R / `lc88_boundary_packets_BFR_BCG5_IDX2`: the export packet
is now at the tolerance `cuspTolerance_BCUSP1 (β 1) βd εN` (cusp requests `βd = εN = R.cuspQuality`,
BR24), the rest is T3B-R's (`BoundaryPacketRestBFR_BQ2`: BCUSP-1 certificates, BCP04.a, ONE
`F : LocalPacketsOnBFR`, BZ-1, product OR separation), the register is the staged
`BoundaryRegisterV2`, and the member is member `n` of the boundary standing sequence at `D.δStar`
(ratio `δ_{n+1}`, BCP04.a index `n + 1`).

* `BoundaryRowsAtBFR_BQ2 K A R n W g B E εr Λz δ` — on a universe-`0` model of the member
  (`BoundaryModel`): THE export packet with `packet_cusp`, T3B-R's rest for THIS packet at the
  register's values and the witnesses `εr, Λz, δ` (those of the per-sequence family), the rows
  `FC39RowsV2 W E`, the ports, `cusp_piece` (`= ψ '' {level ≤ 90}` of the packet) and `cusp_fn`
  (`= level − 90`).
* Consumers: `toRows`, `internal_eq_level_BQ2` (the internal face of a cusp core is the packet's
  level `90`), `packet_alternative_BQ2` (T3's labelled whole-product branch or the separation, for
  THE packet on the model), `exists_packet_rest_of_out_BQ2` (T3B-R's per-member conclusion supplies
  exactly the packet fields of the record).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Hyperbolic
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

/-- **The prepared rows with same-packet provenance on the final boundary family** (separated
branch), at a staged boundary register, for member `n` of the boundary standing sequence. -/
structure BoundaryRowsAtBFR_BQ2 (K : ℕ) (A : ℝ → ℝ) {D : BoundaryEarlyData}
    {T : BoundaryThresholdsV2 D} (R : BoundaryRegisterV2 D T) (n : ℕ) (W : CompactCarrier.{u})
    (g : SmoothRiemannianMetric W.model W.Carrier)
    (B : NearlyCuspidalBoundary W g K (boundaryCounterexampleRatio D.δStar (n + 1)))
    (E : BoundaryTori W B.count) (εr Λz δ : ℝ) : Type (u + 1) where
  /-- The universe-`0` model of the member. -/
  model : BoundaryModel W g B
  /-- T3B-R's export packet on the model, at the register's cusp requests. -/
  packet : letI := model.connected₀
    BoundaryExportPacket model.W₀ model.g₀ K A (boundaryCounterexampleRatio D.δStar (n + 1))
      (cuspTolerance_BCUSP1 (closedβV3 R.later.split.β₁ R.later.excl 1) R.cuspQuality
        R.cuspQuality)
  packet_cusp : packet.cusp = model.B₀
  /-- T3B-R's rest for THIS packet at the register's values. -/
  rest : letI := model.connected₀
    BoundaryPacketRestBFR_BQ2 model.W₀ model.g₀ K A (boundaryCounterexampleRatio D.δStar (n + 1))
      ((n + 1 : ℕ) : ℝ) R.later.scale.Λ R.later.scale.w (closedβV3 R.later.split.β₁ R.later.excl)
      R.later.excl.Δ R.later.err.co.qs R.later.err.co.qe R.later.err.bd.μ R.later.split.b
      R.later.err.s R.later.err.wk.b' R.later.err.wk.s' R.later.err.co.ε R.later.circle.γc
      R.later.circle.βc R.later.Lmax R.later.err.bd.τ R.later.circle.γ δ εr R.later.err.co.e₀
      R.later.split.T₀ R.later.split.V R.later.err.co.ve R.later.err.co.ζ Λz R.cuspQuality
      R.cuspQuality packet
  /-- The revised rows. -/
  rows : FC39RowsV2 W E
  /-- The ports are the boundary components of `B`. -/
  ports : ∀ i, range (E.torusMap i) = B.component i
  /-- Each cusp core is the retained piece `{level ≤ 90}` of THE packet's collar. -/
  cusp_piece : ∀ b : Fin B.count, range (rows.cusp.piece b).map =
    model.ψ '' {y | packet.level (Fin.cast (by rw [packet_cusp]; exact model.count_eq.symm) b) y ≤
      90}
  /-- Its defining function is `level − 90` on its neighbourhood. -/
  cusp_fn : ∀ b : Fin B.count, ∀ x ∈ rows.cusp.near b, rows.cusp.cuspFn b x =
    packet.level (Fin.cast (by rw [packet_cusp]; exact model.count_eq.symm) b) (model.ψ.symm x) -
      90

namespace BoundaryRowsAtBFR_BQ2

variable {K : ℕ} {A : ℝ → ℝ} {D : BoundaryEarlyData} {T : BoundaryThresholdsV2 D}
  {R : BoundaryRegisterV2 D T} {n : ℕ} {W : CompactCarrier.{u}}
  {g : SmoothRiemannianMetric W.model W.Carrier}
  {B : NearlyCuspidalBoundary W g K (boundaryCounterexampleRatio D.δStar (n + 1))}
  {E : BoundaryTori W B.count} {εr Λz δ : ℝ}

/-- The rows forget their provenance. -/
def toRows (P : BoundaryRowsAtBFR_BQ2 K A R n W g B E εr Λz δ) : FC39RowsV2 W E :=
  P.rows

/-- **Consumer**: the internal face of a cusp core is the level `90` of THE packet (on its
neighbourhood). -/
theorem internal_eq_level_BQ2 (P : BoundaryRowsAtBFR_BQ2 K A R n W g B E εr Λz δ)
    (b : Fin B.count) :
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

/-- **Consumer (product-or-separation for THE packet)**: on the model, T3's labelled whole-product
branch for two distinct labels of the packet, or the separation of the enlarged collars and of the
level sets `{level ≤ 90}` at distance `≥ 1`. -/
theorem packet_alternative_BQ2 (P : BoundaryRowsAtBFR_BQ2 K A R n W g B E εr Λz δ) :
    letI := P.model.connected₀
    (∃ (i j : Fin P.packet.cusp.count), i ≠ j ∧
      ∃ Df : Diffeomorph (torusModel.prod (𝓡∂ 1)) P.model.W₀.model (Torus × Icc (0 : ℝ) 1)
          P.model.W₀.Carrier ∞,
        (∀ p, Df p ∈ P.packet.cusp.component i ↔ p.2.1 = 0) ∧
          ∀ p, Df p ∈ P.packet.cusp.component j ↔ p.2.1 = 1) ∨
    (∀ i j : Fin P.packet.cusp.count, i ≠ j →
      Disjoint ((P.packet.cusp.collar i).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92})
        ((P.packet.cusp.collar j).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92}) ∧
      Disjoint {x | P.packet.level i x ≤ 90} {y | P.packet.level j y ≤ 90} ∧
      ∀ x y, P.packet.level i x ≤ 90 → P.packet.level j y ≤ 90 →
        ENNReal.ofReal 1 ≤ riemannianEDistOf P.model.g₀ x y) :=
  letI := P.model.connected₀
  P.rest.alternative_BQ2

end BoundaryRowsAtBFR_BQ2

/-- **Consumer (the packet fields come from T3B-R)**: T3B-R's per-member conclusion on a member of
the model sequence supplies an export packet with `packet_cusp` and T3B-R's rest for THAT packet —
the four packet fields of `BoundaryRowsAtBFR_BQ2`. -/
theorem exists_packet_rest_of_out_BQ2 (K : ℕ) (A : ℝ → ℝ) {D : BoundaryEarlyData}
    {T : BoundaryThresholdsV2 D} (R : BoundaryRegisterV2 D T) (n : ℕ) (W₀ : CompactCarrier.{0})
    [ConnectedSpace W₀.Carrier] (g₀ : SmoothRiemannianMetric W₀.model W₀.Carrier)
    (B₀ : NearlyCuspidalBoundary W₀ g₀ K (boundaryCounterexampleRatio D.δStar (n + 1)))
    (εr Λz δ : ℝ)
    (h : BoundaryPacketsOutBFR_BQ W₀ g₀ K A (boundaryCounterexampleRatio D.δStar (n + 1)) B₀
      ((n + 1 : ℕ) : ℝ) R.later.scale.Λ R.later.scale.w (closedβV3 R.later.split.β₁ R.later.excl)
      R.later.excl.Δ R.later.err.co.qs R.later.err.co.qe R.later.err.bd.μ R.later.split.b
      R.later.err.s R.later.err.wk.b' R.later.err.wk.s' R.later.err.co.ε R.later.circle.γc
      R.later.circle.βc R.later.Lmax R.later.err.bd.τ R.later.circle.γ δ εr R.later.err.co.e₀
      R.later.split.T₀ R.later.split.V R.later.err.co.ve R.later.err.co.ζ Λz R.cuspQuality
      R.cuspQuality) :
    ∃ P : BoundaryExportPacket W₀ g₀ K A (boundaryCounterexampleRatio D.δStar (n + 1))
        (cuspTolerance_BCUSP1 (closedβV3 R.later.split.β₁ R.later.excl 1) R.cuspQuality
          R.cuspQuality),
      P.cusp = B₀ ∧
      BoundaryPacketRestBFR_BQ2 W₀ g₀ K A (boundaryCounterexampleRatio D.δStar (n + 1))
        ((n + 1 : ℕ) : ℝ) R.later.scale.Λ R.later.scale.w (closedβV3 R.later.split.β₁ R.later.excl)
        R.later.excl.Δ R.later.err.co.qs R.later.err.co.qe R.later.err.bd.μ R.later.split.b
        R.later.err.s R.later.err.wk.b' R.later.err.wk.s' R.later.err.co.ε R.later.circle.γc
        R.later.circle.βc R.later.Lmax R.later.err.bd.τ R.later.circle.γ δ εr R.later.err.co.e₀
        R.later.split.T₀ R.later.split.V R.later.err.co.ve R.later.err.co.ζ Λz R.cuspQuality
        R.cuspQuality P :=
  boundaryPacketsOutBFR_iff_rest_BQ2.mp h

end GC.GraphManifold.Assembly.FC39P0
