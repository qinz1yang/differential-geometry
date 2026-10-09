import DifferentialGeometry.Geometry.Fibration.ActualStageChainGoodCutOCL
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainCutChoiceRegister74
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainEdpE

/-!
# Draft 74 CL0, G1 (closed source): the produced cut choice `D_R` and its whole-fibre good bases

Lane O-CL0 (`_OCL`), G1. Named revision for the closed landing (lead, 2026-10-05): the exports are
produced at ONE explicit cut choice `D_R` of the closed source `S`. Here `D_R` is the closed-source
instance `S.goodCut_OCL B hT hεr : ClosedCutChoice74 S B` of the chain kernel `goodCutOn_OCL`
(ZSP04's actual `K₃, D₃`; `edgeBaseOpen = B₂` or `∅`; `circleBaseOpen = W₁ ∩ R₁`), and every
numeric premise of the rows it reads is discharged at the register from `hT` (the strategy lies
below `closedStrategyCompleteV4C`) and the strategy equalities `hNb`, `hcw` (the fields
`strategy_below`, `nb_eq`, `cw_eq` of `ClosedRowsNumericsAt74`), plus `ε_r < 1/2` (`eps_lt`):

* `ClosedRegisterV4.qe_le_thousandth_OCL` (`q_e < θ_e²/10⁸`), `b_mul_le_OCL` (`b < 10⁻⁵ b'`,
  `b' < 1/(10⁶Δ)`: LFR29's cap), `cut_numerics_OCL`, `gaf07_numerics_OCL` (TCP01's Gram request),
  `edp04_numerics_OCL` (EDP-E's nine with `μ, τ, σ_c, b`);
* `goodCut_facts_OCL`: `slimSet = M₁ ∩ f₃⁻¹(K₃)` compact, `M = Z ∪ slimSet ∪ M₂`, `M₃ ⊆ X₁`;
* **`goodCut_edge_disk_OCL`**: over EVERY point `w` of the edge base the whole fibre
  `{q₁ = w, H_S ≤ 4Δ}` (`H_S` the rows' height `A/s`, `4Δ = R.edgeLevel_R74`) is a smooth embedded
  disk whose boundary circle is the whole rim `{q₁ = w, H_S = 4Δ}`; `goodCut_edge_local_OCL`: the
  disks lie in FC33's open threshold-5 edge domain `U₂`;
* **`goodCut_circle_fibre_OCL`**: over EVERY point of the circle base the whole fibre `q₀⁻¹(w)` is a
  smooth embedded circle; `goodCut_circleSource_OCL`: the circle source is FDC03's circle-bundle
  domain `circleDomain_EFE` and lies in FC33's threshold-5 circle domain `U₀`;
* consumer `register_yields_goodCut_OCL`: at the strategy of `register_yields_chainEJAZ_RGC`, on
  every tail member and for every base point, the source `S` carries `D_R` on its own bases object
  with all of the above (no numeric premise left).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry GC.Endpoint GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Analysis
open DifferentialGeometry.Topology

namespace DifferentialGeometry.Geometry.Collapse

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

open DifferentialGeometry.Topology.Handle in
attribute [local instance] closedCellChartedSpaceSucc closedCellIsManifold

namespace ClosedRegisterV4

variable {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}

/-- `q_e ≤ 1/1000` at every register (`q_e < θ_e²/10⁸`, `θ_e < 1/100`). -/
theorem qe_le_thousandth_OCL (R : ClosedRegisterV4 (earlyDataSharedV4 K) T) :
    R.later.err.co.qe ≤ 1 / 1000 := by
  have h1 : R.later.err.co.qe < R.later.circle.θe ^ 2 / 10 ^ 8 :=
    R.later.qe_lt.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have h2 := R.later.θe_lt_hundredth_VAL6
  have h3 := R.later.θe_pos
  have h4 : R.later.circle.θe ^ 2 / 10 ^ 8 ≤ 1 / 1000 := by
    rw [div_le_iff₀ (by norm_num)]
    nlinarith
  linarith

/-- `b · (1000 Δ) ≤ 1` at every register below the complete strategy (LFR29's cap:
`b < 10⁻⁵ b'`, `b' < 1/(10⁶Δ)`). -/
theorem b_mul_le_OCL
    (hT : ClosedStrategyBelowV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)))
    (R : ClosedRegisterV4 (earlyDataSharedV4 K) T) :
    R.later.split.b * (1000 * R.later.excl.Δ) ≤ 1 := by
  obtain ⟨-, hl, -, -⟩ := hT.complete_caps_V4C
  obtain ⟨⟨hb'0, hb'W, -, -⟩, -, -, hb0, hbl⟩ := R.lfr29_numeric_of_below_V4C hl
  have hΔ := R.later.Δ_pos_VAL6
  have hW : lfr29WV4C R.later.excl.Δ R.later.err.bd.τ ≤ 1 / (10 ^ 6 * R.later.excl.Δ) :=
    (min_le_left _ _).trans (min_le_right _ _)
  have hb' : R.later.err.wk.b' * (10 ^ 6 * R.later.excl.Δ) ≤ 1 := by
    have := hb'W.le.trans hW
    rw [le_div_iff₀ (by positivity)] at this
    exact this
  have hbb : R.later.split.b ≤ 1 / 10 ^ 5 * R.later.err.wk.b' :=
    hbl.le.trans (mul_le_mul_of_nonneg_left ((min_le_right _ _).trans (min_le_left _ _))
      (by norm_num))
  nlinarith

/-- The cut's numeric premises at every register below the complete strategy:
`q_e ≤ 1/2`, `0 ≤ γ ≤ 3/4` (TCP01's Gram request `γ < 1/100`). -/
theorem cut_numerics_OCL
    (hT : ClosedStrategyBelowV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)))
    (R : ClosedRegisterV4 (earlyDataSharedV4 K) T) :
    R.later.err.co.qe ≤ 1 / 2 ∧ 0 ≤ R.later.circle.γ ∧ R.later.circle.γ ≤ 3 / 4 := by
  obtain ⟨-, -, hg, -⟩ := hT.complete_caps_V4C
  obtain ⟨hγ0, hγ1, -⟩ := R.gram_request_of_below_V4C hg
  exact ⟨R.later.qe_le_half_R74, hγ0.le, by linarith⟩

/-- GAF07's numeric premises at every register below the complete strategy:
`β₂ ≤ 10⁻⁷`, `γ + β₂ < 1/10`. -/
theorem gaf07_numerics_OCL
    (hT : ClosedStrategyBelowV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)))
    (R : ClosedRegisterV4 (earlyDataSharedV4 K) T) :
    R.β 2 ≤ 1 / 10000000 ∧ R.later.circle.γ + R.β 2 < 1 / 10 := by
  obtain ⟨-, -, hg, -⟩ := hT.complete_caps_V4C
  obtain ⟨-, hγ1, -, hβ⟩ := R.gram_request_of_below_V4C hg
  have h7 : (1 : ℝ) / 10 ^ 7 = 1 / 10000000 := by norm_num
  rw [h7] at hβ
  exact ⟨hβ, by linarith⟩

end ClosedRegisterV4

namespace ClosedChainEZRowsSource_RGC

variable {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
  {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{u}}
  {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}

/-- **The produced cut choice `D_R` of the closed source** (named revision for the closed landing):
the chain kernel `goodCutOn_OCL` on `S.chain` with the register's numerics. -/
def goodCut_OCL (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) (B : ClosedBases74 S)
    (hT : ClosedStrategyBelowV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)))
    (hεr : εr < 1 / 2) : ClosedCutChoice74 S B :=
  ⟨S.chain.goodCutOn_OCL hεr (R.cut_numerics_OCL hT).1 (R.cut_numerics_OCL hT).2.1
    (R.cut_numerics_OCL hT).2.2⟩

/-- **The facts of `D_R`**: `slimSet = M₁ ∩ f₃⁻¹(K₃)` compact, `M = Z ∪ slimSet ∪ M₂`, and
`M₃ ⊆ X₁ = q₀⁻¹(W₁ ∩ R₁)`. -/
theorem goodCut_facts_OCL (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) (B : ClosedBases74 S)
    (hT : ClosedStrategyBelowV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)))
    (hεr : εr < 1 / 2) :
    (S.goodCut_OCL B hT hεr).slimSet = (interior S.chain.zeroUnion_ZSP35)ᶜ ∩
        S.chain.slimMap_ZSP35 ⁻¹' (S.goodCut_OCL B hT hεr).K₃.carrier ∧
      IsCompact (S.goodCut_OCL B hT hεr).slimSet ∧
      S.chain.zeroUnion_ZSP35 ∪ (S.goodCut_OCL B hT hεr).slimSet ∪
        (S.goodCut_OCL B hT hεr).M₂ = univ ∧
      (S.goodCut_OCL B hT hεr).M₃ ⊆ {x | S.chain.toGaf02ChainE.cutQ_R74 0 x ∈
        S.chain.toChain.finalBase_BAS 0 ∩
          gaf07CircleRatio_G47 S.F.family.toLocalChartPacketsC14.toLocalChartPackets} :=
  S.chain.goodCutOn_facts_OCL hεr (R.cut_numerics_OCL hT).1 (R.cut_numerics_OCL hT).2.1
    (R.cut_numerics_OCL hT).2.2

/-- The edge base of `D_R` lies in EDP02's base `B₂`, and equals it when `C₂ ≠ ∅`; the circle base
of `D_R` is `R₁ ∩ W₁`. -/
theorem goodCut_bases_OCL (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) (B : ClosedBases74 S)
    (hT : ClosedStrategyBelowV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)))
    (hεr : εr < 1 / 2) :
    (S.goodCut_OCL B hT hεr).edgeBaseOpen ⊆ S.chain.toGaf02ChainE.edgeBase_EDP23 ∧
      ((S.goodCut_OCL B hT hεr).C₂ ≠ ∅ →
        (S.goodCut_OCL B hT hεr).edgeBaseOpen = S.chain.toGaf02ChainE.edgeBase_EDP23) ∧
      (S.goodCut_OCL B hT hεr).circleBaseOpen =
        gaf07CircleRatio_G47 S.F.family.toLocalChartPacketsC14.toLocalChartPackets ∩
          S.chain.toChain.finalBase_BAS 0 :=
  ⟨S.chain.goodCutOn_edgeBaseOpen_OCL hεr (R.cut_numerics_OCL hT).1 (R.cut_numerics_OCL hT).2.1
    (R.cut_numerics_OCL hT).2.2,
    S.chain.goodCutOn_edgeBaseOpen_eq_OCL hεr (R.cut_numerics_OCL hT).1 (R.cut_numerics_OCL hT).2.1
    (R.cut_numerics_OCL hT).2.2, rfl⟩

/-- The rows' height `H_S = A/s` of the closed source, written on the source's family and chain. -/
theorem height_eq_OCL (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) (x : M.X) :
    S.toE_RGC.toRowsSource_RGC.height x = EuclideanSpace.proj (0 : Fin 2)
      (gafHeightVector S.F.family.toLocalChartFamily S.F.family.zero (S.chain.toChain.E x)) /
        S.chain.toChain.scale x := by
  rw [S.toE_RGC.height_fun_RGC]
  rfl

/-- **EDP04 over EVERY point of the edge base of `D_R`**, in the rows' height `H_S = A/s` and the
rows' level `4Δ`: the whole fibre `{q₁ = w, H_S ≤ 4Δ}` is a smooth embedded disk whose boundary
circle is the whole rim `{q₁ = w, H_S = 4Δ}` (all numerics at the register). -/
theorem goodCut_edge_disk_OCL (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz)
    (B : ClosedBases74 S)
    (hT : ClosedStrategyBelowV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)))
    (hNb : T.Nb = maxNb_V4C) (hcw : T.cw = maxCw_V4C) (hεr : εr < 1 / 2)
    {w : BlockSpace (fun _ : CGPTag S.F.family.toLocalChartPacketsC14.toLocalChartFamily
      S.F.family.toLocalChartPacketsC14.zero => ℝ²)}
    (hw : w ∈ (S.goodCut_OCL B hT hεr).edgeBaseOpen) :
    ∃ φ : ClosedCell 2 → M.X, IsSmoothEmbedding (𝓡∂ 2) 𝓘(ℝ, E3) ∞ φ ∧
      range φ = {x | S.chain.toGaf02ChainE.cutQ_R74 1 x = w ∧
        S.toE_RGC.toRowsSource_RGC.height x ≤ R.edgeLevel_R74} ∧
      range (φ ∘ cellBoundaryInclusion 2) = {x | S.chain.toGaf02ChainE.cutQ_R74 1 x = w ∧
        S.toE_RGC.toRowsSource_RGC.height x = R.edgeLevel_R74} := by
  have hn := R.cut_numerics_OCL hT
  have hE := R.edpE_numerics_RGC hT hNb hcw
  have hw' : w ∈ (S.chain.goodCutOn_OCL hεr hn.1 hn.2.1 hn.2.2).edgeBaseOpen := hw
  have hk := S.chain.goodCutOn_edge_disk_OCL hεr hn.1 hn.2.1 hn.2.2 R.two_le_Δ_EDP23 hE.2.2.1
    hE.2.2.2.1 hE.2.2.2.2.1 hE.2.2.2.2.2.1 R.later.μ_lt_VAL6.le R.later.τ_lt_VAL6.le
    R.qe_le_thousandth_OCL (R.b_mul_le_OCL hT) hE.2.2.2.2.2.2.1 hE.2.2.2.2.2.2.2.1
    hE.2.2.2.2.2.2.2.2 hw'
  obtain ⟨φ, hφ, h1, h2⟩ := hk
  refine ⟨φ, hφ, h1.trans ?_, h2.trans ?_⟩ <;>
  · ext x
    rw [mem_ofPred_eq, mem_ofPred_eq, S.height_eq_OCL, ClosedRegisterV4.edgeLevel_R74]

/-- **ELoc for the edge base of `D_R`**: a point over the edge base with `H_S ≤ 4Δ` lies in
FC33's open threshold-5 edge domain `U₂`. -/
theorem goodCut_edge_local_OCL (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz)
    (B : ClosedBases74 S)
    (hT : ClosedStrategyBelowV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)))
    (hεr : εr < 1 / 2) {x : M.X}
    (hx : S.chain.toGaf02ChainE.cutQ_R74 1 x ∈ (S.goodCut_OCL B hT hεr).edgeBaseOpen)
    (hH : S.toE_RGC.toRowsSource_RGC.height x ≤ R.edgeLevel_R74) :
    x ∈ gafStageDomain5_BAS S.F.family.toLocalChartPacketsC14.toLocalChartPackets 1 :=
  S.chain.goodCutOn_edge_local_OCL hεr (R.cut_numerics_OCL hT).1 (R.cut_numerics_OCL hT).2.1
    (R.cut_numerics_OCL hT).2.2 R.two_le_Δ_EDP23 hx hH

/-- **The circle source of `D_R`** is FDC03's circle-bundle domain `circleDomain_EFE` (the whole
`q₀`-preimage of `W₁ ∩ R₁`) and lies in FC33's threshold-5 circle domain `U₀`. -/
theorem goodCut_circleSource_OCL (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz)
    (B : ClosedBases74 S)
    (hT : ClosedStrategyBelowV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)))
    (hεr : εr < 1 / 2) :
    (S.goodCut_OCL B hT hεr).circleSource = (S.chain.circleDomain_EFE : Set M.X) ∧
      (S.goodCut_OCL B hT hεr).circleSource ⊆
        gafStageDomain5_BAS S.F.family.toLocalChartPacketsC14.toLocalChartPackets 0 :=
  S.chain.goodCutOn_circleSource_OCL hεr (R.cut_numerics_OCL hT).1 (R.cut_numerics_OCL hT).2.1
    (R.cut_numerics_OCL hT).2.2 (R.gaf07_numerics_OCL hT).1
    (R.gaf07_numerics_OCL hT).2

/-- **GAF07 over EVERY point of the circle base of `D_R`**: the whole fibre `q₀⁻¹(w)` is a smooth
embedded circle. -/
theorem goodCut_circle_fibre_OCL (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz)
    (B : ClosedBases74 S)
    (hT : ClosedStrategyBelowV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)))
    (hεr : εr < 1 / 2)
    {w : BlockSpace (fun _ : CGPTag S.F.family.toLocalChartPacketsC14.toLocalChartFamily
      S.F.family.toLocalChartPacketsC14.zero => ℝ²)}
    (hw : w ∈ (S.goodCut_OCL B hT hεr).circleBaseOpen) :
    ∃ f : Circle → M.X, IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, E3) ∞ f ∧
      range f = S.chain.toGaf02ChainE.cutQ_R74 0 ⁻¹' {w} :=
  S.chain.goodCutOn_circle_fibre_OCL hεr (R.cut_numerics_OCL hT).1 (R.cut_numerics_OCL hT).2.1
    (R.cut_numerics_OCL hT).2.2 (R.gaf07_numerics_OCL hT).1
    (R.gaf07_numerics_OCL hT).2 hw

end ClosedChainEZRowsSource_RGC

/-- **Consumer: the register yields `D_R` with its good bases** (D74-18's order, no numeric premise
left): at the strategy of `register_yields_chainEJAZ_RGC`, every register has `0 < ε_r < 1/4` and,
on every tail member, for every base point, a C14Z source `S` with that base point whose produced
cut choice `D_R` (on `S.bases74`) has whole smooth disks over every point of its edge base and whole
smooth circles over every point of its circle base, with `M = Z ∪ slimSet ∪ M₂`. -/
theorem register_yields_goodCut_OCL (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ x, 0 < x → 0 < A x) (Wseq : ℕ → CompactCarrier.{u})
    (gseq : ∀ m, SmoothRiemannianMetric (Wseq m).model (Wseq m).Carrier)
    (hf : ∀ m, ClosedMemberFacts (Wseq m))
    (hg : ∀ m, closedCollapseHypotheses (Wseq m) (gseq m) K A (closedCounterexampleRatio (m + 2))) :
    ∃ T : ClosedThresholdsV4 (earlyDataSharedV4 K),
      ∃ hT : ClosedStrategyBelowV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)),
      T.Nb = maxNb_V4C ∧ T.cw = maxCw_V4C ∧
      ∀ R : ClosedRegisterV4 (earlyDataSharedV4 K) T, ∃ εr δ Λz : ℝ,
        ∃ hεr : εr < 1 / 2, ∀ m, R.later.tail ≤ m →
          ∃ M : ClosedModel (Wseq m) (gseq m), Nonempty M.X ∧
          ∀ x₀ : M.X, ∃ S : ClosedChainEZRowsSource_RGC K R M δ εr Λz, S.chain.x₀ = x₀ ∧
            S.chain.zeroUnion_ZSP35 ∪ (S.goodCut_OCL S.bases74 hT hεr).slimSet ∪
              (S.goodCut_OCL S.bases74 hT hεr).M₂ = univ ∧
            (∀ w ∈ (S.goodCut_OCL S.bases74 hT hεr).edgeBaseOpen,
              ∃ φ : ClosedCell 2 → M.X, IsSmoothEmbedding (𝓡∂ 2) 𝓘(ℝ, E3) ∞ φ ∧
                range φ = {x | S.chain.toGaf02ChainE.cutQ_R74 1 x = w ∧
                  S.toE_RGC.toRowsSource_RGC.height x ≤ R.edgeLevel_R74}) ∧
            (∀ w ∈ (S.goodCut_OCL S.bases74 hT hεr).circleBaseOpen,
              ∃ f : Circle → M.X, IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, E3) ∞ f ∧
                range f = S.chain.toGaf02ChainE.cutQ_R74 0 ⁻¹' {w}) := by
  obtain ⟨U', hU'U, hchain⟩ :=
    exists_chainEStrategy_RGC K (closedStrategyCompleteV4C (earlyDataSharedV4 K))
  obtain ⟨T, hTU', -, -, hfam⟩ :=
    exists_closed_realization_C14Z_RGC K hK A hA Wseq gseq hf hg U'
  have hTU := hTU'.trans_RGC hU'U
  have hbU' : ClosedStrategyBelowV4 T U' := hTU'.below_VAL6
  have hb : ClosedStrategyBelowV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)) :=
    hTU.below_VAL6
  refine ⟨T, hb, hTU.Nb_eq, hTU.cw_eq, fun R => ?_⟩
  obtain ⟨εrF, δ'F, ΛzF, hF⟩ := hfam
  obtain ⟨hεr0, hεr14, hεrε₀, -, -, hΛz, δc, -, -, ht⟩ := hF R
  have hεr : εrF R.stage R.later.circle R.later.excl R.later.err R.later.scale R.later.split.b
      R.later.split.β₁ < 1 / 2 := by linarith
  refine ⟨εrF R.stage R.later.circle R.later.excl R.later.err R.later.scale R.later.split.b
      R.later.split.β₁, δc, ΛzF R.stage R.later.circle R.later.excl R.later.err R.later.scale
      R.later.split.b R.later.split.β₁, hεr, fun m hm => ?_⟩
  obtain ⟨M, ⟨F⟩, -, -⟩ := ht m hm
  have : ConnectedSpace (Wseq m).Carrier := (hf m).connected
  refine ⟨M, ⟨M.ψ.symm (Classical.arbitrary (Wseq m).Carrier)⟩, fun x₀ => ?_⟩
  obtain ⟨C, hCx⟩ := hchain T hbU' R F.family.toLocalChartPacketsC14 hεr0.le hεrε₀ hΛz x₀
  let S : ClosedChainEZRowsSource_RGC K R M δc _ _ := ⟨F, C⟩
  refine ⟨S, hCx, (S.goodCut_facts_OCL S.bases74 hb hεr).2.2.1, fun w hw => ?_, fun w hw => ?_⟩
  · obtain ⟨φ, hφ, hr, -⟩ := S.goodCut_edge_disk_OCL S.bases74 hb hTU.Nb_eq hTU.cw_eq hεr hw
    exact ⟨φ, hφ, hr⟩
  · exact S.goodCut_circle_fibre_OCL S.bases74 hb hεr hw

end DifferentialGeometry.Geometry.Collapse
