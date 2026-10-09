import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainPbr
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdpBlocks

/-!
# The identification interface of the closed `RowsAt` with the chain (review 66, D66-8)

Lane C14-REG-CHAIN, G5. D66-8 fixes NOW how the closed prepared rows (`RowsAt` v2, not yet in the
tree) read the GAF02 chain: `adj = C.E`, `s = C.scale`, `A = u_{E'}(C.E)`, `T = A/s`,
`RowsAt.edge.height = T` (never the original `cgpHeight`),
`ι_j ∘ f_j^{restricted} = (π_j C.E)|_{X_j}`,
and the certificates bind to ONE register choice and ONE bases object.

This file fixes the chain side of that interface:

* on every chain: `Gaf02Chain.rowsAxis_RGC` (`A = u_{E'}(E)`, FC01's axis coordinate of the `E'`
  block, the same expression as lane C14-EDP-E's EDP02/EDP03 statements),
  `Gaf02Chain.rowsHeight_RGC` (`T = A/s`), `Gaf02Chain.rowsStageMap_RGC` (`π_j ∘ E`,
  `π_j = (gafStageQ j).starProjection`, the projection of the chain's (ADJ));
* `ClosedChainRowsSource_RGC K R M δ ε_r Λ_z`: the ONE source a closed certificate reads at a
  register `R` of register V4 and a member model `M`: the instance `F` of the final family at `R`'s
  values, a selection, and the chain on `R`'s own stage data with that selection; its accessors
  `adj`, `scale`, `axis`, `height`, `stageMap` are DEFINED from the chain (so `height = axis/scale`
  holds by `rfl`, `height_eq_RGC`); the bases object (lane C14-BASES, `Gaf02Bases`, not yet in the
  tree) is to be added by a later extension of this record;
* `ClosedChainRowsSource_RGC.facts_RGC`: smoothness of `axis`, `scale`, `height`, `s > 0`, (AE)
  `|A − z₀P| < c₃ρ` (EDP-E), and EDP01's (SD) for `s` at the register's `C_ρ`;
* `exists_closedChainRowsSource_RGC` (inhabitant): on every closed standing sequence, at the
  strategy of `register_yields_chain_RGC`, every register has on every member of its tail such a
  source.
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

namespace Gaf02Chain

variable {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}
  {P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V}
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

/-- `A = u_{E'}(E)`: FC01's axis coordinate of the `E'` block of the chain's final map. -/
def rowsAxis_RGC (C : Gaf02Chain P Kj Ξ Γ S eg c cw) : X → ℝ :=
  fun p => EuclideanSpace.proj (0 : Fin 2) (gafHeightVector P.toLocalChartFamily P.zero (C.E p))

/-- The final edge height `T = A/s` (`s = C.scale = ℓ_ρ(E)`); never the original `cgpHeight`. -/
def rowsHeight_RGC (C : Gaf02Chain P Kj Ξ Γ S eg c cw) : X → ℝ :=
  fun p => C.rowsAxis_RGC p / C.scale p

/-- The stage-`j` coordinates of the final map, `π_j ∘ E` (`π_j = (gafStageQ j).starProjection`,
the projection of the chain's (ADJ)); `ι_j ∘ f_j^{restricted}` must equal it on `X_j`. -/
def rowsStageMap_RGC (C : Gaf02Chain P Kj Ξ Γ S eg c cw) (j : Fin 3) :
    X → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) :=
  fun p => (gafStageQ P.toLocalChartFamily P.zero j).starProjection (C.E p)

end Gaf02Chain

/-- **The ONE source of the closed rows at a register** (D66-8): the instance of the final family
at the register's values, a selection of original preimages, and the chain on the register's own
stage data with that selection. -/
structure ClosedChainRowsSource_RGC (K : ℕ) {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
    (R : ClosedRegisterV4 (earlyDataSharedV4 K) T) {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} (M : ClosedModel W g) (δ εr Λz : ℝ) where
  /-- The instance of the final family at `R`'s values. -/
  F : ClosedFamilyInstanceC14DV4 K R M δ εr Λz
  /-- The selection of original preimages over the enlarged stage clouds. -/
  sel : Fin 3 → BlockSpace (fun _ : CGPTag F.family.toLocalChartFamily F.family.zero => ℝ²) → M.X
  hsel : ∀ st, ∀ x ∈ gafCloudEnlarged F.family.toLocalChartFamily F.family.zero st,
    cgpProjMap F.family.toLocalChartFamily F.family.zero
      (gafStageTags F.family.toLocalChartFamily F.family.zero st) (sel st x) = x
  /-- The chain on `R`'s own stage data. -/
  chain : Gaf02Chain F.family.toLocalChartPackets K
    (fun j => (earlyDataSharedV4 K).Ξ j (R.stage.Γ j)) R.stage.Γ R.stage.Sig R.stage.e R.stage.c
    (stageCwAt_V4C R.stage)
  chain_sel : chain.sel = sel

namespace ClosedChainRowsSource_RGC

variable {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
  {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{u}}
  {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}

/-- `adj = C.E`. -/
def adj (S : ClosedChainRowsSource_RGC K R M δ εr Λz) :
    M.X → BlockSpace (fun _ : CGPTag S.F.family.toLocalChartFamily S.F.family.zero => ℝ²) :=
  S.chain.E

/-- `s = C.scale`. -/
def scale (S : ClosedChainRowsSource_RGC K R M δ εr Λz) : M.X → ℝ :=
  S.chain.scale

/-- `A = u_{E'}(C.E)`. -/
def axis (S : ClosedChainRowsSource_RGC K R M δ εr Λz) : M.X → ℝ :=
  S.chain.rowsAxis_RGC

/-- `RowsAt.edge.height = T = A/s`. -/
def height (S : ClosedChainRowsSource_RGC K R M δ εr Λz) : M.X → ℝ :=
  S.chain.rowsHeight_RGC

/-- `π_j ∘ C.E`. -/
def stageMap (S : ClosedChainRowsSource_RGC K R M δ εr Λz) (j : Fin 3) :
    M.X → BlockSpace (fun _ : CGPTag S.F.family.toLocalChartFamily S.F.family.zero => ℝ²) :=
  S.chain.rowsStageMap_RGC j

/-- The height of the rows is `A/s`, by definition. -/
theorem height_eq_RGC (S : ClosedChainRowsSource_RGC K R M δ εr Λz) :
    S.height = fun p => S.axis p / S.scale p :=
  rfl

/-- The stage maps of the rows are `π_j ∘ adj`, by definition. -/
theorem stageMap_eq_RGC (S : ClosedChainRowsSource_RGC K R M δ εr Λz) (j : Fin 3) :
    S.stageMap j = fun p =>
      (gafStageQ S.F.family.toLocalChartFamily S.F.family.zero j).starProjection (S.adj p) :=
  rfl

/-- Smoothness of the rows' chain quantities: `A`, `s`, `T = A/s` are smooth on the member. -/
theorem smooth_RGC (S : ClosedChainRowsSource_RGC K R M δ εr Λz) :
    ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ S.axis ∧ ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ S.scale ∧
      ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ S.height := by
  obtain ⟨hA, hs, -, hT, -⟩ := S.chain.final_smooth_EDPE
  exact ⟨hA, hs, hT⟩

/-- (AE) for the rows' axis: `|A − z₀P| < c₃ρ` with `c₃ = c_3` of the register's stage. -/
theorem axis_value_RGC (S : ClosedChainRowsSource_RGC K R M δ εr Λz) (p : M.X) :
    |S.axis p - cgpEdgeMarker S.F.family.toLocalChartFamily p * S.F.family.edge.smoothing p| <
      R.stage.c 2 * S.F.ρ p :=
  (S.chain.heightAxis_value_EDPE p).1

/-- EDP01's (SD) value bound for the rows' scale at the register's `C_ρ`. -/
theorem scale_value_RGC (hNb : T.Nb = maxNb_V4C) (hcw : T.cw = maxCw_V4C)
    (S : ClosedChainRowsSource_RGC K R M δ εr Λz) (p : M.X) :
    |S.scale p - S.F.ρ p| ≤
      closedScaleConstantV4 (earlyDataSharedV4 K) T R.stage * R.later.scale.Λ * S.F.ρ p := by
  obtain ⟨-, hed⟩ := S.chain.edp01_GAF8 (P := S.F.family.toLocalChartPacketsC14)
    (stageCwAt_nonneg_V4C R.stage 0) R.stage.sig_zero_le_RGC
  have hdom := R.stage.chain_scaleConstant_le_RGC hNb hcw
  have hΛ : 0 ≤ R.later.scale.Λ := R.later.Λ_pos.le
  exact (hed p).2.1.trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hdom hΛ) (S.F.ρ_pos p).le)

/-- EDP01's (SD) derivative bound for the rows' scale at the register's `C_ρ`. -/
theorem scale_deriv_RGC (hNb : T.Nb = maxNb_V4C) (hcw : T.cw = maxCw_V4C)
    (S : ClosedChainRowsSource_RGC K R M δ εr Λz) (p : M.X) (v : TangentSpace 𝓘(ℝ, E3) p) :
    |mvfderiv 𝓘(ℝ, E3) S.scale p v| ≤
      closedScaleConstantV4 (earlyDataSharedV4 K) T R.stage * R.later.scale.Λ *
        Real.sqrt (M.gX.inner p v v) := by
  obtain ⟨-, hed⟩ := S.chain.edp01_GAF8 (P := S.F.family.toLocalChartPacketsC14)
    (stageCwAt_nonneg_V4C R.stage 0) R.stage.sig_zero_le_RGC
  have hdom := R.stage.chain_scaleConstant_le_RGC hNb hcw
  have hΛ : 0 ≤ R.later.scale.Λ := R.later.Λ_pos.le
  exact ((hed p).2.2.1 v).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hdom hΛ) (Real.sqrt_nonneg _))

/-- **The analytic facts of the rows' chain quantities**: `A`, `s`, `T` smooth on the member,
`s > 0`, (AE) `|A − z₀P| < c₃ρ` with `c₃ = c_3` of the register's stage, and EDP01's (SD) for
`s` at the register's `C_ρ` (PR10 binding `T.Nb = maxNb_V4C`, `T.cw = maxCw_V4C`). -/
theorem facts_RGC (hNb : T.Nb = maxNb_V4C) (hcw : T.cw = maxCw_V4C)
    (S : ClosedChainRowsSource_RGC K R M δ εr Λz) :
    ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ S.axis ∧ ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ S.scale ∧
      ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ S.height ∧
      ∀ p : M.X, 0 < S.scale p ∧
        |S.axis p - cgpEdgeMarker S.F.family.toLocalChartFamily p *
            S.F.family.edge.smoothing p| < R.stage.c 2 * S.F.ρ p ∧
        |S.scale p - S.F.ρ p| ≤
          closedScaleConstantV4 (earlyDataSharedV4 K) T R.stage * R.later.scale.Λ * S.F.ρ p ∧
        ∀ v : TangentSpace 𝓘(ℝ, E3) p, |mvfderiv 𝓘(ℝ, E3) S.scale p v| ≤
          closedScaleConstantV4 (earlyDataSharedV4 K) T R.stage * R.later.scale.Λ *
            Real.sqrt (M.gX.inner p v v) := by
  obtain ⟨hA, hs, hT⟩ := S.smooth_RGC
  exact ⟨hA, hs, hT, fun p => ⟨(S.chain.scale_pos p).2, S.axis_value_RGC p,
    S.scale_value_RGC hNb hcw p, S.scale_deriv_RGC hNb hcw p⟩⟩

end ClosedChainRowsSource_RGC

/-- **Inhabitant of the rows' source** (consumer): on every closed standing sequence there is a
strategy refining `closedStrategyCompleteV4C`, with the validity record and PR10's binding, at which
every register has, on every member of its tail, a source `ClosedChainRowsSource_RGC` (final family,
selection, chain on the register's stage data). -/
theorem exists_closedChainRowsSource_RGC (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ x, 0 < x → 0 < A x) (Wseq : ℕ → CompactCarrier.{u})
    (gseq : ∀ m, SmoothRiemannianMetric (Wseq m).model (Wseq m).Carrier)
    (hf : ∀ m, ClosedMemberFacts (Wseq m))
    (hg : ∀ m, closedCollapseHypotheses (Wseq m) (gseq m) K A (closedCounterexampleRatio (m + 2))) :
    ∃ T : ClosedThresholdsV4 (earlyDataSharedV4 K),
      ClosedStrategyRefinesV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)) ∧
      PartialClosedThresholdValidityV4Rows K A Wseq gseq (earlyDataSharedV4 K) T ∧
      T.Nb = maxNb_V4C ∧ T.cw = maxCw_V4C ∧
      ∀ R : ClosedRegisterV4 (earlyDataSharedV4 K) T, ∃ εr δ Λz : ℝ, ∀ m, R.later.tail ≤ m →
        ∃ M : ClosedModel (Wseq m) (gseq m),
          Nonempty (ClosedChainRowsSource_RGC K R M δ εr Λz) := by
  obtain ⟨T, hv, hTU, -, hNb, hcw, hR⟩ := register_yields_chain_RGC K hK A hA Wseq gseq hf hg
  refine ⟨T, hTU, hv, hNb, hcw, fun R => ?_⟩
  obtain ⟨-, εr, -, Λz, δc, -, -, ht⟩ := hR R
  refine ⟨εr, δc, Λz, fun m hm => ?_⟩
  obtain ⟨M, F, -, -, -, -, -, -, hchain⟩ := ht m hm
  have : ConnectedSpace (Wseq m).Carrier := (hf m).connected
  have : Nonempty M.X := ⟨M.ψ.symm (Classical.arbitrary (Wseq m).Carrier)⟩
  obtain ⟨sel, hsel⟩ := exists_gafSelection_RGC F.family.toLocalChartPackets
  obtain ⟨C, hC, -⟩ := hchain sel hsel
  exact ⟨M, ⟨⟨F, sel, hsel, C, hC⟩⟩⟩

end DifferentialGeometry.Geometry.Collapse
