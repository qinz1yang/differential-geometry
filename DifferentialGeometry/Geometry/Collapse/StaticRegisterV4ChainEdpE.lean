import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainRowsE

/-!
# EDP-E's numeric hypotheses at the register (one lemma) and the rows' rim rank

Lane C14-REG-CHAIN, G7 part c (review 66 D66-8: the rows read EDP02–EDP06 on the chain's final map;
"闭链各行在 register 的 stage 数据上成立"). Lane C14-EDP-E's chain theorems
(`Gaf02Chain.edge_height_EH_EDPE`, `edge_homotopy_conorm_EDPE`, `edge_trace_EDPE`,
`edge_vertical_rank_EDPE`) carry the numeric hypotheses `0 ≤ c_w(1)`, `Σ₁ ≤ ε₁/10⁴`,
`c₃ < 10⁻⁵`, `C_ρ^chainΛΔ < 10⁻⁶`, `0 ≤ ε < 1`, `0 < γc ≤ 1/100`, `βc ≤ 10⁻⁵`. At every register of
a strategy below `closedStrategyCompleteV4C` (with PR10's binding) they are ALL consequences of the
register's own choices:

* `ClosedRegisterV4.collar_le_RGC`: `γc < 1/100` (TCP01's Gram cap in `circleUp`) and
  `βc < 10⁻⁵` (`3βc < β₂ < 10⁻⁶`);
* `ClosedRegisterV4.eps_lt_RGC`: `ε < γc/2000 < 1` (the scale budget);
* `ClosedRegisterV4.edpE_numerics_RGC`: the nine hypotheses at the chain parameters of the
  register (`c_w = stageCwAt_V4C R.stage`, `Σ = R.stage.Sig`, `Ξ_j = Ξ_j(Γ_j)`, `c = R.stage.c`);
* consumer `ClosedChainERowsSource_RGC.rim_rank_RGC`: EDP05's face rank for the rows' source at the
  register — at every rim point `T = 4Δ` of the edge buffer (`|g| < 4Δ`), the pair `(g, T)` of the
  rows' final edge coordinate and height is a submersion.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry GC.Endpoint GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

namespace ClosedRegisterV4

variable {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}

/-- The collar parameters at a register below the complete strategy: `0 < γc < 1/100` (TCP01's
Gram cap on `circleUp`) and `βc < 10⁻⁵` (`3βc < β₂ < 10⁻⁶`). -/
theorem collar_le_RGC
    (hT : ClosedStrategyBelowV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)))
    (R : ClosedRegisterV4 (earlyDataSharedV4 K) T) :
    0 < R.later.circle.γc ∧ R.later.circle.γc < 1 / 100 ∧ R.later.circle.βc < 1 / 100000 := by
  obtain ⟨-, -, hg, -⟩ := hT.complete_caps_V4C
  have hγc : R.later.circle.γc < 1 / 100 := by
    have h1 := R.later.γc_lt.trans_le (hg.circleUp_le _ _ _ _ _)
    exact h1.trans_le (min_le_right _ _)
  have h3 := R.later.three_mul_βc_lt_β₂_VAL6
  have h6 := R.later.β₂_lt_audit_VAL6
  refine ⟨R.later.γc_pos, hγc, ?_⟩
  norm_num at h6 ⊢
  linarith

/-- `ε < γc/2000 < 1` at a register below the complete strategy (the scale budget). -/
theorem eps_lt_RGC
    (hT : ClosedStrategyBelowV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)))
    (R : ClosedRegisterV4 (earlyDataSharedV4 K) T) :
    R.later.err.co.ε < R.later.circle.γc / 2000 ∧ R.later.err.co.ε < 1 := by
  obtain ⟨-, -, -, hrows⟩ := hT.complete_caps_V4C
  have hsc : ClosedStrategyBelowV4 T (scaleStrategyV4 (earlyDataSharedV4 K)) :=
    hrows.trans_VAL6 ((ClosedThresholdsV4.inf_below_left_VAL6 _ _).trans_VAL6
      (ClosedThresholdsV4.inf_below_left_VAL6 _ _))
  obtain ⟨-, -, -, hb, -, -⟩ := closedScaleBudgetV4_of_below_VAL6 hsc R
  have hΔΛ : 0 ≤ 300 * R.later.excl.Δ * R.later.scale.Λ := by
    have := R.later.Λ_pos
    have := R.later.Δ_pos_VAL6
    positivity
  have hsq := Real.sqrt_nonneg (504000 / R.later.excl.Δ + 3780 * R.later.err.bd.τ)
  have hε := R.later.ε_pos
  obtain ⟨-, hγc, -⟩ := R.collar_le_RGC hT
  constructor <;> linarith

/-- **EDP-E's nine numeric hypotheses at the register** (see the module header). -/
theorem edpE_numerics_RGC
    (hT : ClosedStrategyBelowV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)))
    (hNb : T.Nb = maxNb_V4C) (hcw : T.cw = maxCw_V4C)
    (R : ClosedRegisterV4 (earlyDataSharedV4 K) T) :
    0 ≤ stageCwAt_V4C R.stage 0 ∧
      R.stage.Sig 0 ≤ (earlyDataSharedV4 K).Ξ 0 (R.stage.Γ 0) / 10000 ∧
      R.stage.c 2 < 1 / 100000 ∧
      100 * (gafDerivativeBound + 1) *
          (1 + gafCutoffConstant + 1 * stageCwAt_V4C R.stage 0 / R.stage.Sig 0) *
          R.later.scale.Λ * R.later.excl.Δ < 1 / 1000000 ∧
      0 ≤ R.later.err.co.ε ∧ R.later.err.co.ε < 1 ∧ 0 < R.later.circle.γc ∧
      R.later.circle.γc ≤ 1 / 100 ∧ R.later.circle.βc ≤ 1 / 100000 := by
  obtain ⟨hγ0, hγ1, hβc⟩ := R.collar_le_RGC hT
  exact ⟨stageCwAt_nonneg_V4C R.stage 0, R.stage.sig_zero_le_RGC,
    R.stage.c_two_bounds_RGC.2.2.1, R.chain_scale_small_RGC hNb hcw, R.later.ε_pos.le,
    (R.eps_lt_RGC hT).2, hγ0, hγ1.le, hβc.le⟩

end ClosedRegisterV4

namespace ClosedChainERowsSource_RGC

variable {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
  {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{u}}
  {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}

/-- **EDP05's face rank for the rows' source at the register** (consumer): at every edge centre
`j` and every point `p` of the edge buffer with `|g_j(p)| < 4Δ` on the rim `T(p) = 4Δ` (`T` the
rows' height `A/s`, `g_j = u_j(E)/ρ_j` the final edge coordinate), the differential of `(g_j, T)`
is onto. -/
theorem rim_rank_RGC
    (hT : ClosedStrategyBelowV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)))
    (hNb : T.Nb = maxNb_V4C) (hcw : T.cw = maxCw_V4C)
    (S : ClosedChainERowsSource_RGC K R M δ εr Λz) {j : M.X}
    (hj : j ∈ S.F.family.edge.centres) (p : M.X)
    (hp : p ∈ ball j (100 * R.later.excl.Δ * S.F.ρ j))
    (hη : |S.F.family.edge.coord j p| < 5 * R.later.excl.Δ)
    (ht : S.F.family.edge.smoothing p / S.F.ρ p < 5 * R.later.excl.Δ)
    (hg : |EuclideanSpace.proj (0 : Fin 2) (gafEdgeVector S.F.family.toLocalChartFamily
      S.F.family.zero ⟨j, (Set.Finite.mem_toFinset _).mpr hj⟩ (S.chain.toChain.E p)) /
        S.F.ρ j| < 4 * R.later.excl.Δ)
    (hT4 : S.toRowsSource_RGC.height p = 4 * R.later.excl.Δ) :
    Function.Surjective (mvfderiv 𝓘(ℝ, E3) (edgeReferenceCoordinates
      ![fun z => EuclideanSpace.proj (0 : Fin 2) (gafEdgeVector S.F.family.toLocalChartFamily
          S.F.family.zero ⟨j, (Set.Finite.mem_toFinset _).mpr hj⟩ (S.chain.toChain.E z)) /
            S.F.ρ j, S.toRowsSource_RGC.height]) p) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := R.edpE_numerics_RGC hT hNb hcw
  have hrank := S.chain.toChain.edge_vertical_rank_EDPE (L := S.F.family.toLocalChartPacketsC14)
    h1 h2 h3 h4 h5 h6 h7 h8 h9 hj
  dsimp only at hrank
  rw [S.height_fun_RGC] at hT4 ⊢
  exact (hrank p hp hη ht hg hT4).2.2.2.1

end ClosedChainERowsSource_RGC

end DifferentialGeometry.Geometry.Collapse
