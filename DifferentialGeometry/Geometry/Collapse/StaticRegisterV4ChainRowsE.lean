import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainRows
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainEComplete
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEJAApplications
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEZeroBlock
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdpHeight

/-!
# The rows' source on the ENHANCED chain with (JA): one register choice, D66-2 provenance

Lane C14-REG-CHAIN, G7 part a (review 66 D66-8; D66-2). The closed prepared rows (`RowsAt` v2)
read ONE chain built on ONE register choice. G5's `ClosedChainRowsSource_RGC` fixed the
identification (`adj = C.E`, `s = C.scale`, `A = u_{E'}(C.E)`, `T = A/s`, `π_j ∘ C.E`) on a
`Gaf02Chain` with an arbitrary selection; here the source carries the chain of D66-2's
construction order, built on the register's stage data (`exists_chainEStrategy_RGC`):

* `ClosedChainERowsSource_RGC K R M δ ε_r Λ_z`: the instance `F` of the final family at `R`'s
  values and `Ĉ : Gaf02ChainEJA F.family.toLocalChartPacketsC14 K (Ξ_j(Γ_j)) Γ Σ e c
  (stageCwAt_V4C R.stage) (registerCadj_RGC K)` (enhanced planes, native outputs on the planes'
  slots and radii, rough data, (JA));
* `toRowsSource_RGC`: its G5 source (selection = the planes' radius selections, `rfl`), so every
  G5 accessor and fact applies; `adj_eq_RGC`, `scale_eq_RGC`, `sel_eq_RGC`, `plane_eq_RGC`;
* the chain rows at the register with their numeric hypotheses discharged from the register's own
  choices: `adj_close_RGC` (`‖E − 𝓔⁰‖ < c₃ρ`), `ClosedRegisterV4.chain_scale_small_RGC`
  (`C_ρ^chainΛΔ < 10⁻⁶`), `eps_lt_one_RGC`, `edge_height_RGC` (EDP-E's (EH) at every edge centre
  with tolerance `ClosedRegisterV4.heightTol_RGC`). Rows that are hypothesis-free on
  `Gaf02ChainEJA` are read on `S.chain` directly (GAF06 `gaf06_GAFC`, GAF07
    `gaf07_*_interface_GAFC`,
  ZSP01 `toGaf02ChainE.zsp01_ZE_GAF8`); the (JA) numerics are `R.stage.c_two_bounds_RGC`;
* inhabitant `exists_closedChainERowsSource_RGC`: at the strategy of
  `register_yields_chainEJA_RGC`, every register has on every member of its tail, for every base
  point, such a source.

The bases object (lane C14-BASES, `Gaf02Bases C R`) is added by a later extension (G7 part b).
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
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

/-- **The ONE source of the closed rows at a register, on the enhanced chain** (D66-2, D66-8): the
instance of the final family at the register's values and the chain on the enhanced planes with
(JA) on the register's own stage data. -/
structure ClosedChainERowsSource_RGC (K : ℕ) {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
    (R : ClosedRegisterV4 (earlyDataSharedV4 K) T) {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} (M : ClosedModel W g) (δ εr Λz : ℝ) where
  /-- The instance of the final family at `R`'s values. -/
  F : ClosedFamilyInstanceC14DV4 K R M δ εr Λz
  /-- The chain on the enhanced planes with (JA), on `R`'s own stage data. -/
  chain : Gaf02ChainEJA F.family.toLocalChartPacketsC14 K
    (fun j => (earlyDataSharedV4 K).Ξ j (R.stage.Γ j)) R.stage.Γ R.stage.Sig R.stage.e R.stage.c
    (stageCwAt_V4C R.stage) (registerCadj_RGC K)

/-- EDP01's chain constant times `ΛΔ` is below `10⁻⁶` (`C_ρ^chain ≤ C_ρ` and the register's
`C_ρΔΛ < 10⁻⁶`, PR10 binding). -/
theorem ClosedRegisterV4.chain_scale_small_RGC {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4
    K)}
    (hNb : T.Nb = maxNb_V4C) (hcw : T.cw = maxCw_V4C) (R : ClosedRegisterV4 (earlyDataSharedV4 K)
      T) :
    100 * (gafDerivativeBound + 1) *
        (1 + gafCutoffConstant + 1 * stageCwAt_V4C R.stage 0 / R.stage.Sig 0) *
        R.later.scale.Λ * R.later.excl.Δ < 1 / 1000000 := by
  have hdom := R.stage.chain_scaleConstant_le_RGC hNb hcw
  have hC := R.later.regScale_Cρ
  have hΛ := R.later.Λ_pos
  have hΔ := R.later.Δ_pos_VAL6
  have hΛΔ : 0 ≤ R.later.scale.Λ * R.later.excl.Δ := by positivity
  have h1 := mul_le_mul_of_nonneg_right hdom hΛΔ
  have h2 : closedScaleConstantV4 (earlyDataSharedV4 K) T R.stage *
      (R.later.scale.Λ * R.later.excl.Δ) < 1 / 1000000 := by
    have e : closedScaleConstantV4 (earlyDataSharedV4 K) T R.stage *
        (R.later.scale.Λ * R.later.excl.Δ) = closedScaleConstantV4 (earlyDataSharedV4 K) T R.stage *
          R.later.excl.Δ * R.later.scale.Λ := by ring
    rw [e]
    norm_num at hC ⊢
    exact hC
  have e2 : 100 * (gafDerivativeBound + 1) *
        (1 + gafCutoffConstant + 1 * stageCwAt_V4C R.stage 0 / R.stage.Sig 0) *
        R.later.scale.Λ * R.later.excl.Δ = 100 * (gafDerivativeBound + 1) *
        (1 + gafCutoffConstant + 1 * stageCwAt_V4C R.stage 0 / R.stage.Sig 0) *
        (R.later.scale.Λ * R.later.excl.Δ) := by ring
  rw [e2]
  exact h1.trans_lt h2

/-- The tolerance `h_* = 50(c₃ + κΔ)` of EDP-E's (EH) at the register (`κ = C_ρ^chainΛ`). -/
def ClosedRegisterV4.heightTol_RGC {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
    (R : ClosedRegisterV4 (earlyDataSharedV4 K) T) : ℝ :=
  50 * (R.stage.c 2 + 100 * (gafDerivativeBound + 1) *
    (1 + gafCutoffConstant + 1 * stageCwAt_V4C R.stage 0 / R.stage.Sig 0) * R.later.scale.Λ *
      R.later.excl.Δ)

/-- The tolerance, unfolded. -/
theorem ClosedRegisterV4.heightTol_eq_RGC {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
    (R : ClosedRegisterV4 (earlyDataSharedV4 K) T) :
    R.heightTol_RGC = 50 * (R.stage.c 2 + 100 * (gafDerivativeBound + 1) *
      (1 + gafCutoffConstant + 1 * stageCwAt_V4C R.stage 0 / R.stage.Sig 0) * R.later.scale.Λ *
        R.later.excl.Δ) :=
  rfl

namespace ClosedChainERowsSource_RGC

variable {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
  {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{u}}
  {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}

/-- The G5 source of the enhanced source: the same instance, the chain's own selection (the
planes' radius selections) and the forgetful chain. -/
def toRowsSource_RGC (S : ClosedChainERowsSource_RGC K R M δ εr Λz) :
    ClosedChainRowsSource_RGC K R M δ εr Λz where
  F := S.F
  sel := S.chain.toChain.sel
  hsel := S.chain.toChain.hsel
  chain := S.chain.toChain
  chain_sel := rfl

/-- `adj = Ĉ.E`. -/
theorem adj_eq_RGC (S : ClosedChainERowsSource_RGC K R M δ εr Λz) :
    S.toRowsSource_RGC.adj = S.chain.toChain.E :=
  rfl

/-- `s = Ĉ.scale`. -/
theorem scale_eq_RGC (S : ClosedChainERowsSource_RGC K R M δ εr Λz) :
    S.toRowsSource_RGC.scale = S.chain.toChain.scale :=
  rfl

/-- Provenance of the selection (D66-2): the rows' selections ARE the planes' radius
selections at the chain's base point. -/
theorem sel_eq_RGC (S : ClosedChainERowsSource_RGC K R M δ εr Λz) :
    S.toRowsSource_RGC.sel 0 = S.chain.planes₀.rsel S.chain.x₀ ∧
      S.toRowsSource_RGC.sel 1 = S.chain.planes₁.rsel S.chain.x₀ ∧
      S.toRowsSource_RGC.sel 2 = S.chain.planes₂.rsel S.chain.x₀ :=
  S.chain.sel_eq

/-- Provenance of the planes (D66-2): the chain's planes ARE the PDEF planes. -/
theorem plane_eq_RGC (S : ClosedChainERowsSource_RGC K R M δ εr Λz) :
    S.chain.toChain.plane 0 = S.chain.planes₀.plane ∧
      S.chain.toChain.plane 1 = S.chain.planes₁.plane ∧
      S.chain.toChain.plane 2 = S.chain.planes₂.plane :=
  S.chain.plane_eq

/-- `adj_close`: `‖E − 𝓔⁰‖ < c₃ρ` everywhere (GAF02's strict error at the register's `c₃`). -/
theorem adj_close_RGC (S : ClosedChainERowsSource_RGC K R M δ εr Λz) (p : M.X) :
    ‖S.chain.toChain.E p - cgpGlobalMap S.F.family.toLocalChartFamily S.F.family.zero p‖ <
      R.stage.c 2 * S.F.ρ p :=
  S.chain.toChain.stage_error_lt.2.2 p

/-- The register's `ε < 1` on a strategy below `closedStrategyCompleteV4C` (the scale budget:
`2ε < γc/1000`, and `γc ≤ 1` on the chain). -/
theorem eps_lt_one_RGC (hT : ClosedStrategyBelowV4 T (closedStrategyCompleteV4C (earlyDataSharedV4
    K)))
    (S : ClosedChainERowsSource_RGC K R M δ εr Λz) : R.later.err.co.ε < 1 := by
  obtain ⟨-, -, -, hrows⟩ := hT.complete_caps_V4C
  have hsc : ClosedStrategyBelowV4 T (scaleStrategyV4 (earlyDataSharedV4 K)) :=
    hrows.trans_VAL6 ((ClosedThresholdsV4.inf_below_left_VAL6 _ _).trans_VAL6
      (ClosedThresholdsV4.inf_below_left_VAL6 _ _))
  obtain ⟨-, -, -, hb, -, -⟩ := closedScaleBudgetV4_of_below_VAL6 hsc R
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hγc, -⟩ := S.chain.toChain.std
  have hΔΛ : 0 ≤ 300 * R.later.excl.Δ * R.later.scale.Λ := by
    have := R.later.Λ_pos
    have := R.later.Δ_pos_VAL6
    positivity
  have hsq := Real.sqrt_nonneg (504000 / R.later.excl.Δ + 3780 * R.later.err.bd.τ)
  have hε := R.later.ε_pos
  linarith [hγc.2]

/-- The rows' height as a function: `T = A/s` with `A = u_{E'}(Ĉ.E)`, `s = Ĉ.scale`. -/
theorem height_fun_RGC (S : ClosedChainERowsSource_RGC K R M δ εr Λz) :
    S.toRowsSource_RGC.height = fun z => EuclideanSpace.proj (0 : Fin 2)
      (gafHeightVector S.F.family.toLocalChartFamily S.F.family.zero (S.chain.toChain.E z)) /
        S.chain.toChain.scale z :=
  rfl

/-- **EDP-E's (EH) at every edge centre, at the register** (D66-8: the rows' height IS `T = A/s`):
`h_* < 1/1000`, `|T − t| < h_*` and `|dT(W) − dt(W)| < h_*` (for `R_j⁻²g`-unit `W`) on the edge
buffer `{p ∈ B(j, 100Δρ_j), |u_j| < 5Δ, .3Δ ≤ t < 5Δ}`, `t = F/ρ`, with every numeric hypothesis
of `Gaf02Chain.edge_height_EH_EDPE` discharged from the register (strategy below
`closedStrategyCompleteV4C`, PR10 binding). -/
theorem edge_height_RGC
    (hT : ClosedStrategyBelowV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)))
    (hNb : T.Nb = maxNb_V4C) (hcw : T.cw = maxCw_V4C)
    (S : ClosedChainERowsSource_RGC K R M δ εr Λz) {j : M.X} (hj : j ∈ S.F.family.edge.centres) :
    R.heightTol_RGC < 1 / 1000 ∧
    (∀ p ∈ ball j (100 * R.later.excl.Δ * S.F.ρ j), |S.F.family.edge.coord j p| <
        5 * R.later.excl.Δ → 3 / 10 * R.later.excl.Δ ≤ S.F.family.edge.smoothing p / S.F.ρ p →
      S.F.family.edge.smoothing p / S.F.ρ p < 5 * R.later.excl.Δ →
        |S.toRowsSource_RGC.height p - S.F.family.edge.smoothing p / S.F.ρ p| <
          R.heightTol_RGC) ∧
    ∀ p ∈ ball j (100 * R.later.excl.Δ * S.F.ρ j), |S.F.family.edge.coord j p| <
        5 * R.later.excl.Δ → 3 / 10 * R.later.excl.Δ < S.F.family.edge.smoothing p / S.F.ρ p →
      S.F.family.edge.smoothing p / S.F.ρ p < 5 * R.later.excl.Δ →
      ∀ W : TangentSpace 𝓘(ℝ, E3) p, (S.F.ρ j)⁻¹ ^ 2 * M.gX.inner p W W = 1 →
        |mvfderiv 𝓘(ℝ, E3) S.toRowsSource_RGC.height p W -
            mvfderiv 𝓘(ℝ, E3) (fun z => S.F.family.edge.smoothing z / S.F.ρ z) p W| <
          R.heightTol_RGC :=
by
  have hEH := S.chain.toChain.edge_height_EH_EDPE (L := S.F.family.toLocalChartPacketsC14)
    (stageCwAt_nonneg_V4C R.stage 0) R.stage.sig_zero_le_RGC R.stage.c_two_bounds_RGC.2.2.1
    (R.chain_scale_small_RGC hNb hcw) R.later.ε_pos.le (S.eps_lt_one_RGC hT) hj
  dsimp only at hEH
  obtain ⟨h1, h2, h3⟩ := hEH
  rw [R.heightTol_eq_RGC, S.height_fun_RGC]
  exact ⟨h1, h2, h3⟩

end ClosedChainERowsSource_RGC

/-- **Inhabitant of the enhanced rows' source** (consumer): on every closed standing sequence there
is a strategy refining `closedStrategyCompleteV4C`, with the validity record and PR10's binding, at
which every register has, on every member of its tail (a nonempty model), for every base point, a
source `ClosedChainERowsSource_RGC` whose chain has that base point. -/
theorem exists_closedChainERowsSource_RGC (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ x, 0 < x → 0 < A x) (Wseq : ℕ → CompactCarrier.{u})
    (gseq : ∀ m, SmoothRiemannianMetric (Wseq m).model (Wseq m).Carrier)
    (hf : ∀ m, ClosedMemberFacts (Wseq m))
    (hg : ∀ m, closedCollapseHypotheses (Wseq m) (gseq m) K A (closedCounterexampleRatio (m + 2))) :
    ∃ T : ClosedThresholdsV4 (earlyDataSharedV4 K),
      ClosedStrategyRefinesV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)) ∧
      PartialClosedThresholdValidityV4Rows K A Wseq gseq (earlyDataSharedV4 K) T ∧
      T.Nb = maxNb_V4C ∧ T.cw = maxCw_V4C ∧
      ∀ R : ClosedRegisterV4 (earlyDataSharedV4 K) T, ∃ εr δ Λz : ℝ, ∀ m, R.later.tail ≤ m →
        ∃ M : ClosedModel (Wseq m) (gseq m), Nonempty M.X ∧ ∀ x₀ : M.X,
          ∃ S : ClosedChainERowsSource_RGC K R M δ εr Λz, S.chain.x₀ = x₀ := by
  obtain ⟨T, hv, hTU, -, hNb, hcw, hR⟩ := register_yields_chainEJA_RGC K hK A hA Wseq gseq hf hg
  refine ⟨T, hTU, hv, hNb, hcw, fun R => ?_⟩
  obtain ⟨-, εr, -, Λz, δc, -, -, ht⟩ := hR R
  refine ⟨εr, δc, Λz, fun m hm => ?_⟩
  obtain ⟨M, F, -, -, -, -, -, -, hchain⟩ := ht m hm
  have : ConnectedSpace (Wseq m).Carrier := (hf m).connected
  refine ⟨M, ⟨M.ψ.symm (Classical.arbitrary (Wseq m).Carrier)⟩, fun x₀ => ?_⟩
  obtain ⟨C, hC, -⟩ := hchain x₀
  exact ⟨⟨F, C⟩, hC⟩

end DifferentialGeometry.Geometry.Collapse
