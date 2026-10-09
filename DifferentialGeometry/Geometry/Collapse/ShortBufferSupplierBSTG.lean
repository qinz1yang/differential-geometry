import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsC14StagedSTG
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4

/-!
# The Δ-stage short-buffer supplier (PR13; lane BSTG)

Blueprint 207B, PR13 (B:10129–10133): `Δ` is chosen "larger than `10⁶`, `100/β₂`, and all fixed
short-buffer lower bounds in TCP01–TCP04, FC22 and LFR35–LFR38. This is a finite lower-only
choice." Review 57 §3.4: the finite maximum of the rows' FIXED SHORT test windows, not a long-scale
radius. The accepted statements require:

* TCP01: `1 ≤ Δ` (`tcp01_row`, Fibration/ActualFirstComparisonList.lean);
* TCP02: `1 ≤ Δ` (`tcp02_row`: `∀ Δ, 1 ≤ Δ → ∃ η₁ …`, Fibration/ActualRawAlignment.lean);
* TCP03: `1 ≤ Δ` (circle, slim, zero rows) and `3 ≤ Δ` (edge row),
  Fibration/Actual*ConstantComparison.lean; the blueprint's `Δ ≥ 10⁶`, B:5415;
* TCP04: `1200 ≤ Δ` (`tcp04_row`, Fibration/ActualHeightComparison.lean; B:5464, and
  `9Δ + 20/.99 < 10Δ`, B:5472);
* FC22: none (the pointwise scalar step, Analysis/InnerProductSpace/AsymmetricTestSaturation.lean);
  the blueprint's `Δ > β₂⁻¹` (B:1502);
* LFR35–LFR38: `Δ₀(βc, γc) ≤ Δ`, the threshold of `exists_edge_full_collar_parameters` (LFR38,
  Collapse/EdgeFullCollar.lean:490, containing LFR35's / LFR36's), which IS the producer's output
  `Δ₀` (LE/EdgeChartsQF.lean:160);
* LFR37: none (fixed radii `100, 300`, A:28210).

So the finite maximum of the fixed short buffers is `1200`, and every staged prefix already exceeds
all of them: `C14PreScale.Δ_gt6` (`10⁶ < Δ`, also TCP03's blueprint bound), `Δ_gt` (`100/β₂ < Δ`,
FC22's `Δ > β₂⁻¹`) and `Δ₀_le` (LFR35–LFR38's threshold, the producer's own output). Every
register V4 does too (`ClosedLaterV4.Δ_gt`: `10⁶ < Δ`; the realization's `ΔLow` contains the
producer's Skolem `Δ₀`).

* `c14ShortBufferRq_BSTG`: the STG record whose `Δ` request is this maximum `1200`;
* `C14PreScale.short_buffers_BSTG`: every fixed short buffer of the list at every staged prefix;
  `C14PreScale.meets_shortBufferΔ_BSTG`;
* `ClosedLaterV4.short_buffers_BSTG`: the same at every register V4 (the slot `ΔLow` needs no
  supplier for these rows);
* consumer `C14PreFinal.tcp_row_numerics_BSTG`: the whole numeric hypothesis block of the accepted
  rows TCP01–TCP04 (`0 ≤ Λ`, `1200 ≤ Δ`, `μ, τ ≤ 1/100`, `10⁶ΔΛ < 10⁻⁵`,
  `4(10 + 2(2·10⁶Δ) + Δ/3) ≤ Lmax`, `e < 1/40`, `1600·10⁶Δ ≤ T`) at every staged prefix with
  `Lmax = c14Lmax` and `V ≥ T`.
-/

set_option autoImplicit false

noncomputable section

open Filter Set

namespace DifferentialGeometry.Geometry.Collapse

/-- **The Δ-stage short-buffer request** (PR13) as an STG record: the `Δ` request is the finite
maximum `1200` of the fixed short-buffer lower bounds of the accepted rows TCP01–TCP04
(`1, 1, 3, 1200`), FC22 (none) and LFR37 (none); LFR35–LFR38's threshold is the producer's output
`Δ₀`, already below `Δ` at every prefix. Every other request is trivial. -/
def c14ShortBufferRq_BSTG : C14StagedRequestsSTG :=
  { C14StagedRequestsSTG.trivial with Δ := fun _ => 1200 }

/-- **Every fixed short buffer at every staged prefix**: `1 ≤ Δ` (TCP01–TCP03), `1200 ≤ Δ`
(TCP04), `10⁶ ≤ Δ` (TCP03's blueprint bound), `β₂⁻¹ < Δ` (FC22) and `Δ₀ ≤ Δ` (LFR35–LFR38, the
producer's threshold). -/
theorem C14PreScale.short_buffers_BSTG (p : C14PreScale) :
    1 ≤ p.Δ ∧ 1200 ≤ p.Δ ∧ 1000000 ≤ p.Δ ∧ p.β₂⁻¹ < p.Δ ∧ p.Δ₀ ≤ p.Δ := by
  have h6 := p.Δ_gt6
  have hβ := p.β₂_pos
  have hinv : p.β₂⁻¹ ≤ 100 / p.β₂ := by
    rw [inv_eq_one_div]
    exact div_le_div_of_nonneg_right (by norm_num) hβ.le
  exact ⟨by linarith, by linarith, h6.le, hinv.trans_lt p.Δ_gt, p.Δ₀_le⟩

/-- Every staged prefix meets the short-buffer request. -/
theorem C14PreScale.meets_shortBufferΔ_BSTG (p : C14PreScale) :
    c14ShortBufferRq_BSTG.Δ p.toC14PreExcl ≤ p.Δ :=
  p.short_buffers_BSTG.2.1

/-- **Every fixed short buffer at every register V4**: `1 ≤ Δ`, `1200 ≤ Δ`, `10⁶ < Δ`,
`β₂⁻¹ < Δ` (PR13's built-in `max(10⁶, 100/β₂, ΔLow) < Δ`). -/
theorem ClosedLaterV4.short_buffers_BSTG {D : ClosedEarlyData} {T : ClosedThresholdsV4 D}
    {st : ClosedStage D} (la : ClosedLaterV4 D T st) :
    1 ≤ la.excl.Δ ∧ 1200 ≤ la.excl.Δ ∧ 1000000 < la.excl.Δ ∧ la.excl.β₂⁻¹ < la.excl.Δ := by
  have h := la.Δ_gt
  have h6 : (10 : ℝ) ^ 6 < la.excl.Δ := (le_max_left _ _).trans_lt h
  have h100 : 100 / la.excl.β₂ < la.excl.Δ :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans_lt h
  have hβ := la.β₂_pos
  have hinv : la.excl.β₂⁻¹ ≤ 100 / la.excl.β₂ := by
    rw [inv_eq_one_div]
    exact div_le_div_of_nonneg_right (by norm_num) hβ.le
  norm_num at h6
  exact ⟨by linarith, by linarith, h6, hinv.trans_lt h100⟩

/-- **Consumer: the numeric hypothesis block of the accepted rows TCP01–TCP04 at every staged
prefix** (`tcp01_row`, `tcp02_row`, `tcp03_*_row`, `tcp04_row`), with the short buffer
`1200 ≤ Δ`, for `Lmax = c14Lmax Rq P V` and any joint output `V ≥ T`. -/
theorem C14PreFinal.tcp_row_numerics_BSTG (P : C14PreFinal) (Rq : C14StagedRequests) {V : ℝ}
    (hV : P.T ≤ V) :
    0 ≤ P.Λ ∧ 1200 ≤ P.Δ ∧ P.μ ≤ 1 / 100 ∧ P.τ ≤ 1 / 100 ∧
      1000000 * P.Δ * P.Λ < 1 / 100000 ∧
      4 * (10 + 2 * (2000000 * P.Δ) + P.Δ / 3) ≤ c14Lmax Rq P V ∧ P.e < 1 / 40 ∧
      1600 * (1000000 * P.Δ) ≤ P.T := by
  have hb := P.short_buffers_BSTG
  have hL := c14Lmax_gt Rq P V
  have hT := P.T_Δ
  have hΔ := P.Δ_gt6
  refine ⟨P.Λ_pos.le, hb.2.1, P.μ_le.trans (by norm_num), P.τ_le30.trans (by norm_num), P.LΛ_lt,
    ?_, P.e_lt, hT⟩
  nlinarith

end DifferentialGeometry.Geometry.Collapse
