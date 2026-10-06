import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainEdgeSetEqOCL

/-!
# Draft 74 CL0, G7a: FDC02's frontier data on the good edge base at `D_R` (clause (d))

Lane O-CL1 (`_OCL`), group G7a. The `cbase_domain` field of `EdgeCutFacts74 P.A P.cut` for the
produced stage geometry `P` at `D_R` (clause (d) of the gate-1A table), from lane S-EDP-FDC3's E1
head `edgeCompactDomain_EFE` on the actual chain with `D_R`'s `K₃, D₃`:

* `cbaseDomain_congr_OCL`: the frontier-data statement transported along an equality of open
  bases and a pointwise equality of the compact base sets (abstract);
* `goodCut_edgeSet_EFE_OCL`: `M₂ ∩ {x ∈ U₂ ∩ q₁⁻¹(ratio) | A/s ≤ 4Δ} = M^edge` at `D_R`, hence
  `goodCut_hcpt_OCL` (E1's compactness input = FDC04's `edge_compact`);
* **`edge_cbase_domain_at_OCL`**: the field itself (vacuous when `C₂ = ∅`; otherwise the good
  base of `D_R` IS `edgeBaseOpens_EFE` and the compact base `C₂` is E1's `π₂E(M₂ ∩ X₂)`), with
  the regularity inputs of G6a;
* **`edgeCutFactsAt2_OCL`**: `EdgeCutFacts74 P.A P.cut` from `rank_two` ALONE.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry GC.Endpoint GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Analysis
open GC.GraphManifold GC.GraphManifold.Assembly GC.GraphManifold.Assembly.FC39P0

namespace DifferentialGeometry.Geometry.Collapse

/-- **Transport of FDC02's frontier data** along an equality of open bases `V = V'` and a pointwise
equality of the compact base sets. -/
theorem cbaseDomain_congr_OCL {Y : Type*} [TopologicalSpace Y]
    [ChartedSpace (EuclideanSpace ℝ (Fin 1)) Y] {V V' : TopologicalSpace.Opens Y} (hV : V = V')
    {C : Set V} {C' : Set V'}
    (hC : ∀ y (hy : y ∈ V), (⟨y, hy⟩ : V) ∈ C ↔ (⟨y, hV ▸ hy⟩ : V') ∈ C')
    (H : ∀ c ∈ frontier C', ∃ U : TopologicalSpace.Opens V', c ∈ U ∧
      ∃ φ : V' → ℝ, ContMDiffOn (𝓡 1) 𝓘(ℝ, ℝ) ∞ φ U ∧ φ c = 0 ∧
        mfderiv (𝓡 1) 𝓘(ℝ, ℝ) φ c ≠ 0 ∧ C' ∩ U = {c' | c' ∈ U ∧ 0 ≤ φ c'}) :
    ∀ c ∈ frontier C, ∃ U : TopologicalSpace.Opens V, c ∈ U ∧
      ∃ φ : V → ℝ, ContMDiffOn (𝓡 1) 𝓘(ℝ, ℝ) ∞ φ U ∧ φ c = 0 ∧
        mfderiv (𝓡 1) 𝓘(ℝ, ℝ) φ c ≠ 0 ∧ C ∩ U = {c' | c' ∈ U ∧ 0 ≤ φ c'} := by
  subst hV
  have hCC : C = C' := by
    ext ⟨y, hy⟩
    exact hC y hy
  subst hCC
  exact H

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

namespace ClosedChainEZRowsSource_RGC

variable {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
  {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{0}}
  {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}

section At

variable (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) (B : ClosedBases74 S)
  (hT : ClosedStrategyBelowV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)))
  (hεr : εr < 1 / 2)

/-- E1's edge piece `M₂ ∩ {x ∈ U₂ ∩ q₁⁻¹(ratio) | A/s ≤ 4Δ}` is `M^edge` of `D_R`. -/
theorem goodCut_edgeSet_EFE_OCL :
    S.chain.toGaf02ChainE.cutM2_R74 (S.goodCut_OCL B hT hεr).K₃.carrier ∩
        Subtype.val '' {x : S.chain.toGaf02ChainE.edgeSource_EFE |
          S.chain.toGaf02ChainE.edgeHeight_EFE x ≤ 4 * R.later.excl.Δ} =
      (S.goodCut_OCL B hT hεr).edgeSet := by
  have hreg := S.chain.toGaf02ChainE.edgeRegion_eq_sublevel_R74
  ext x
  constructor
  · rintro ⟨hM, ⟨y, hy, rfl⟩⟩
    refine ⟨hM, ?_⟩
    rw [hreg]
    exact ⟨S.chain.toGaf02ChainE.edgeSource_mem_EFE y.2, hy⟩
  · intro hx
    have hx2 := hx.2
    rw [hreg] at hx2
    have hh : S.toE_RGC.toRowsSource_RGC.height x ≤ R.edgeLevel_R74 := by
      rw [S.height_eq_OCL]
      exact hx2.2
    have hU := S.goodCut_edge_local_OCL B hT hεr
      ((S.goodCut_OCL B hT hεr).edgeBaseOpen_sub ⟨x, hx, rfl⟩) hh
    exact ⟨hx.1, ⟨x, ⟨hU, hx2.1.2⟩⟩, hx2.2, rfl⟩

/-- E1's compactness input at `D_R` (FDC04's `edge_compact`). -/
theorem goodCut_hcpt_OCL (Htail : ClosedFdcFacts74 (S.goodCut_OCL B hT hεr)) :
    IsCompact (S.chain.toGaf02ChainE.cutM2_R74 (S.goodCut_OCL B hT hεr).K₃.carrier ∩
      Subtype.val '' {x : S.chain.toGaf02ChainE.edgeSource_EFE |
        S.chain.toGaf02ChainE.edgeHeight_EFE x ≤ 4 * R.later.excl.Δ}) := by
  rw [S.goodCut_edgeSet_EFE_OCL B hT hεr]
  exact Htail.edge_compact

variable (A : SmoothStageBases74 S) (zero : ZSP02SmoothExit74 S)

/-- The compact edge base of the carried cut, read on `edgeBaseOpens_EFE`, is E1's
`π₂E(M₂ ∩ X₂)`. -/
theorem cut_C₂_EFE_OCL {S : ClosedChainEZRowsSource_RGC K R M δ εr Λz} {B : ClosedBases74 S}
    {hT : ClosedStrategyBelowV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K))}
    {hεr : εr < 1 / 2} {y : ↥(S.chain.toChain.finalBase_BAS 1)}
    (hy : y ∈ S.chain.toGaf02ChainE.edgeBaseOpens_EFE) :
    (y : S.blockSpace_R74) ∈ (S.goodCut_OCL B hT hεr).C₂ ↔
      (⟨y, hy⟩ : S.chain.toGaf02ChainE.edgeBaseOpens_EFE) ∈ S.chain.toGaf02ChainE.edgeProj_EFE ''
        {x : S.chain.toGaf02ChainE.edgeSource_EFE |
          (x : M.X) ∈ S.chain.toGaf02ChainE.cutM2_R74 (S.goodCut_OCL B hT hεr).K₃.carrier ∧
            S.chain.toGaf02ChainE.edgeHeight_EFE x ≤ 4 * R.later.excl.Δ} := by
  constructor
  · rintro ⟨x', hx', hq⟩
    have hx'' : x' ∈ (S.goodCut_OCL B hT hεr).edgeSet := hx'
    rw [← S.goodCut_edgeSet_EFE_OCL B hT hεr] at hx''
    obtain ⟨hM, ⟨z, hz, rfl⟩⟩ := hx''
    exact ⟨z, ⟨hM, hz⟩, Subtype.ext (Subtype.ext hq)⟩
  · rintro ⟨z, ⟨hM, hz⟩, hzy⟩
    have hz' : (z : M.X) ∈ (S.goodCut_OCL B hT hεr).edgeSet := by
      rw [← S.goodCut_edgeSet_EFE_OCL B hT hεr]
      exact ⟨hM, ⟨z, hz, rfl⟩⟩
    refine ⟨z, hz', ?_⟩
    have h1 := congrArg (fun c : S.chain.toGaf02ChainE.edgeBaseOpens_EFE =>
      ((c : ↥(S.chain.toChain.finalBase_BAS 1)) : S.blockSpace_R74)) hzy
    exact h1

/-- **`cbase_domain`** of the edge facts at `D_R` (clause (d)). -/
theorem edge_cbase_domain_at_OCL (hNb : T.Nb = maxNb_V4C) (hcw : T.cw = maxCw_V4C)
    (Htail : ClosedFdcFacts74 (S.goodCut_OCL B hT hεr)) :
    ∀ c ∈ frontier (Subtype.val ⁻¹' (S.closedStagesAt_OCL B hT hεr A zero).cut.C₂ :
        Set (S.closedStagesAt_OCL B hT hεr A zero).cut.edgeBaseOpen),
      ∃ U : TopologicalSpace.Opens (S.closedStagesAt_OCL B hT hεr A zero).cut.edgeBaseOpen, c ∈ U ∧
        ∃ φ : (S.closedStagesAt_OCL B hT hεr A zero).cut.edgeBaseOpen → ℝ,
          ContMDiffOn (𝓡 1) 𝓘(ℝ, ℝ) ∞ φ U ∧ φ c = 0 ∧ mfderiv (𝓡 1) 𝓘(ℝ, ℝ) φ c ≠ 0 ∧
          (Subtype.val ⁻¹' (S.closedStagesAt_OCL B hT hεr A zero).cut.C₂ :
            Set (S.closedStagesAt_OCL B hT hεr A zero).cut.edgeBaseOpen) ∩ U =
            {c' | c' ∈ U ∧ 0 ≤ φ c'} := by
  by_cases hC2 : (S.goodCut_OCL B hT hεr).C₂ = ∅
  · intro c hc
    exfalso
    have hCb : (Subtype.val ⁻¹' (S.closedStagesAt_OCL B hT hεr A zero).cut.C₂ :
        Set (S.closedStagesAt_OCL B hT hεr A zero).cut.edgeBaseOpen) = ∅ := by
      refine eq_empty_iff_forall_notMem.mpr fun c' hc' => ?_
      let b : ↥(S.chain.toChain.finalBase_BAS 1) := c'.1
      have h1 : (b : S.blockSpace_R74) ∈ (S.goodCut_OCL B hT hεr).C₂ := hc'
      rw [hC2] at h1
      exact h1
    rw [hCb, frontier_empty] at hc
    exact hc
  · have hV : (S.closedStagesAt_OCL B hT hεr A zero).cut.edgeBaseOpen =
        S.chain.toGaf02ChainE.edgeBaseOpens_EFE := by
      apply TopologicalSpace.Opens.ext
      ext w
      let b : ↥(S.chain.toChain.finalBase_BAS 1) := w
      change (b : S.blockSpace_R74) ∈ (S.goodCut_OCL B hT hεr).edgeBaseOpen ↔
        (b : S.blockSpace_R74) ∈ edgeRatio_R74 S.F.family.toLocalChartPacketsC14
      rw [(S.goodCut_bases_OCL B hT hεr).2.1 hC2]
      exact ⟨fun h => h.2, fun h => ⟨b.2, h⟩⟩
    obtain ⟨hD, hKs, hKF, -⟩ := S.chain.slimDomains_spec_OCL hεr
    have hE := R.edpE_numerics_RGC hT hNb hcw
    have h := S.chain.edgeCompactDomain_EFE A hεr R.two_le_Δ_EDP23 hE.2.2.1 hE.2.2.2.1
      hE.2.2.2.2.1 hE.2.2.2.2.2.1 R.later.μ_lt_VAL6.le R.later.τ_lt_VAL6.le
      R.qe_le_thousandth_OCL (R.b_mul_le_OCL hT) hE.2.2.2.2.2.2.1 hE.2.2.2.2.2.2.2.1
      hE.2.2.2.2.2.2.2.2 (S.chain.slimK₃_OCL hεr) (S.chain.slimD₃_OCL hεr) hD hKs hKF
      (S.goodCut_D₃_reg_OCL B hT hεr) (S.goodCut_D₃_bdry_OCL B hT hεr)
      (S.goodCut_hcpt_OCL B hT hεr Htail)
    exact cbaseDomain_congr_OCL hV
      (fun y hy => cut_C₂_EFE_OCL (S := S) (B := B) (hT := hT) (hεr := hεr) (hV ▸ hy)) h.2.2

/-- **The edge facts at `D_R` from `rank_two` alone** (`cbase_domain`: clause (d) produced). -/
theorem edgeCutFactsAt2_OCL (hNb : T.Nb = maxNb_V4C) (hcw : T.cw = maxCw_V4C)
    (Htail : ClosedFdcFacts74 (S.goodCut_OCL B hT hεr))
    (rank_two : ∀ x : (S.closedStagesAt_OCL B hT hεr A zero).cut.edgeSource,
      (S.closedStagesAt_OCL B hT hεr A zero).cut.edgeHeight x =
        (S.closedStagesAt_OCL B hT hεr A zero).A.edge.level →
      Surjective fun v : TangentSpace W.model (x : W.Carrier) =>
        (mfderiv W.model (𝓡 1) ((S.closedStagesAt_OCL B hT hεr A zero).A.edge.restrictProj
            (S.closedStagesAt_OCL B hT hεr A zero).cut.edgeBaseOpen) x v,
          mfderiv W.model 𝓘(ℝ, ℝ) (S.closedStagesAt_OCL B hT hεr A zero).cut.edgeHeight x v)) :
    EdgeCutFacts74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut :=
  S.edgeCutFactsAt_OCL B hT hεr A zero hNb hcw Htail rank_two
    (S.edge_cbase_domain_at_OCL B hT hεr A zero hNb hcw Htail)

end At

end ClosedChainEZRowsSource_RGC

end DifferentialGeometry.Geometry.Collapse
