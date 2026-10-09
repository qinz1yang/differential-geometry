import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainGoodCutOCL
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainLinkValues74
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainTransport74
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainRowsOfExportsU74
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainFdcFacts74

/-!
# D74-4 heads at the explicit cut choice `D_R`: the form the closed row lane plugs into

Lane S-LANDING (by S-LANDING2, suffix `_LND`), G5. The heads of G2d
(`closed_rows_of_geometric_exports_atU74`, `closed_rows_of_rowsU74`) either return the link at
`G.choice` of an exports record or hide the choice behind `∃ D`. The closed rows lane (O-CL1)
produces ONE explicit choice `D_R = S.goodCut_OCL B hT hεr` and wants the link and the value rows
AT `D_R`. This file feeds the value rows of S-REG-CHAIN G14, the produced choice of O-CL0 and the
set identities of `transport_R74` into the heads:

* `closed_rows_at_of_exitsU74`: exits `O : ClosedExitsOverU74 D` ⟹
  `∃ Rw, ClosedRowsLinkAtU74 S B D Rw` (the link AT `D`, no `∃ D`);
* `closed_rows_at_of_rowsU74`: the same from the development-stage records `Htail` / `Hrows` at `D`;
* `closed_link_values_at_R74LND`: the value rows of `closed_link_values_R74` for ANY cut choice `D`
  with the two facts `M = Z ∪ slimSet ∪ M₂` and `M₃ ⊆ X₁` (not only for the `∃ D` of the
  register), and `closed_link_values_goodCut_R74LND` at `D_R` (facts of `goodCut_facts_OCL`);
* `closed_rows_values_atDR_U74`: at `D_R`, the link AND the value rows AND the transport
  identities of `transport_R74` in one statement (`Htail` at `D_R` and `Hrows` at `D_R`);
* `closed_rows_atDR_of_numerics_U74`: the same from the numerics record `N` and the member facts
  `Htail` (`hT := N.strategy_below`, `hεr := N.eps_lt`);
* consumer `register_yields_closed_rows_atDR_of_rows_U74`: on `register_yields_fdcFacts_RNUM`'s
  sources, `Hrows` at `D_R` gives the link at `D_R` with the value rows and the certificate.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry GC.Endpoint GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Analysis
open GC.GraphManifold GC.GraphManifold.Assembly GC.GraphManifold.Assembly.FC39P0

namespace DifferentialGeometry.Geometry.Collapse

universe u

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

/-- **The link AT the choice `D`** from the exits over `D` (the head of G2d, `choice = D` by
definition of `ClosedExitsOverU74.toExports`). -/
theorem closed_rows_at_of_exitsU74 {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
    {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}
    (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) (B : ClosedBases74 S)
    (D : ClosedCutChoice74 S B) (O : ClosedExitsOverU74 D) :
    ∃ Rw : FC39RowsV2 W (BoundaryTori.empty W), ClosedRowsLinkAtU74 S B D Rw :=
  closed_rows_of_geometric_exports_atU74 S B O.toExports

/-- **The link AT the choice `D`** from the development-stage records at `D`
(`closed_rows_of_rowsU74` keeps only `∃ D`). -/
theorem closed_rows_at_of_rowsU74 {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
    {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}
    (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) (B : ClosedBases74 S)
    (D : ClosedCutChoice74 S B) (Htail : ClosedFdcFacts74 D)
    (Hrows : RemainingActualRowExitsU74 S B D) :
    ∃ Rw : FC39RowsV2 W (BoundaryTori.empty W), ClosedRowsLinkAtU74 S B D Rw := by
  obtain ⟨O⟩ := Hrows.exits Htail
  exact closed_rows_at_of_exitsU74 S B D O

/-- **The value rows of D74-5 on `W` for ANY cut choice** `D` satisfying the two register facts
(`M = Z ∪ slimSet ∪ M₂`, `M₃ ⊆ X₁`): the edge row `ψ(M^edge) = ψ(M₂) ∩ (q₁∘ψ⁻¹)⁻¹(B₂) ∩
{H_W ≤ 4Δ}`, the circle region inside GAF07's `X₁`, the decomposition of `W`, and
`q_j ∘ ψ⁻¹ = Θ_j ∘ f_j ∘ ψ⁻¹`. -/
theorem closed_link_values_at_R74LND {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
    {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}
    (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) (B : ClosedBases74 S)
    (D : ClosedCutChoice74 S B)
    (hcov : S.chain.zeroUnion_ZSP35 ∪ D.slimSet ∪ D.M₂ = univ)
    (hM3 : D.M₃ ⊆ {x | S.chain.toGaf02ChainE.cutQ_R74 0 x ∈ S.chain.toChain.finalBase_BAS 0 ∩
      gaf07CircleRatio_G47 S.F.family.toLocalChartPacketsC14.toLocalChartPackets}) :
    M.ψ '' D.edgeSet = M.ψ '' D.M₂ ∩ (S.stageProjW_R74 1 ⁻¹'
        (S.chain.toChain.finalBase_BAS 1 ∩ edgeRatio_R74 S.F.family.toLocalChartPacketsC14) ∩
        {x | S.edgeHeightW_R74 x ≤ R.edgeLevel_R74}) ∧
      M.ψ '' D.M₃ ⊆ S.stageProjW_R74 0 ⁻¹' (S.chain.toChain.finalBase_BAS 0 ∩
        gaf07CircleRatio_G47 S.F.family.toLocalChartPacketsC14.toLocalChartPackets) ∧
      M.ψ '' S.chain.zeroUnion_ZSP35 ∪ M.ψ '' D.slimSet ∪ M.ψ '' D.M₂ = univ ∧
      ∀ j x, S.stageProjW_R74 j x =
        S.chain.toChain.Θ_BAS j (S.chain.toChain.stageMap_BAS j (M.ψ.symm x)) := by
  refine ⟨D.edgeSet_W_R74, ?_, ?_, S.stageProjW_ident_R74 B⟩
  · rintro _ ⟨x, hx, rfl⟩
    have h := hM3 hx
    rw [mem_preimage, ClosedChainEZRowsSource_RGC.stageProjW_R74, comp_apply,
      M.ψ.symm_apply_apply]
    exact h
  · rw [← image_union, ← image_union, hcov, image_univ]
    exact M.ψ.surjective.range_eq

/-- **The value rows of D74-5 at the produced choice `D_R`** (`goodCut_facts_OCL` discharges the two
register facts; the numerics are those of `hT`, `hεr`). -/
theorem closed_link_values_goodCut_R74LND {K : ℕ}
    {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
    {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}
    (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) (B : ClosedBases74 S)
    (hT : ClosedStrategyBelowV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)))
    (hεr : εr < 1 / 2) :
    M.ψ '' (S.goodCut_OCL B hT hεr).edgeSet = M.ψ '' (S.goodCut_OCL B hT hεr).M₂ ∩
        (S.stageProjW_R74 1 ⁻¹' (S.chain.toChain.finalBase_BAS 1 ∩
          edgeRatio_R74 S.F.family.toLocalChartPacketsC14) ∩
        {x | S.edgeHeightW_R74 x ≤ R.edgeLevel_R74}) ∧
      M.ψ '' (S.goodCut_OCL B hT hεr).M₃ ⊆ S.stageProjW_R74 0 ⁻¹'
        (S.chain.toChain.finalBase_BAS 0 ∩
          gaf07CircleRatio_G47 S.F.family.toLocalChartPacketsC14.toLocalChartPackets) ∧
      M.ψ '' S.chain.zeroUnion_ZSP35 ∪ M.ψ '' (S.goodCut_OCL B hT hεr).slimSet ∪
        M.ψ '' (S.goodCut_OCL B hT hεr).M₂ = univ ∧
      ∀ j x, S.stageProjW_R74 j x =
        S.chain.toChain.Θ_BAS j (S.chain.toChain.stageMap_BAS j (M.ψ.symm x)) := by
  obtain ⟨-, -, hcov, hM3⟩ := S.goodCut_facts_OCL B hT hεr
  exact closed_link_values_at_R74LND S B _ hcov hM3

/-- **CL1 at `D_R`, in one statement**: from `Htail` and `Hrows` at the produced choice, the
rows `Rw` linked to the chain AT `D_R` (revised link), the value rows of G14 at `D_R`, the
set identities of `transport_R74` at `D_R`, and the certificate of GROUP G. -/
theorem closed_rows_values_atDR_U74 {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
    {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}
    (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) (B : ClosedBases74 S)
    (hT : ClosedStrategyBelowV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)))
    (hεr : εr < 1 / 2) (Htail : ClosedFdcFacts74 (S.goodCut_OCL B hT hεr))
    (Hrows : RemainingActualRowExitsU74 S B (S.goodCut_OCL B hT hεr)) :
    ∃ Rw : FC39RowsV2 W (BoundaryTori.empty W),
      ClosedRowsLinkAtU74 S B (S.goodCut_OCL B hT hεr) Rw ∧
      (M.ψ '' (S.goodCut_OCL B hT hεr).edgeSet = M.ψ '' (S.goodCut_OCL B hT hεr).M₂ ∩
          (S.stageProjW_R74 1 ⁻¹' (S.chain.toChain.finalBase_BAS 1 ∩
            edgeRatio_R74 S.F.family.toLocalChartPacketsC14) ∩
          {x | S.edgeHeightW_R74 x ≤ R.edgeLevel_R74}) ∧
        M.ψ '' (S.goodCut_OCL B hT hεr).M₃ ⊆ S.stageProjW_R74 0 ⁻¹'
          (S.chain.toChain.finalBase_BAS 0 ∩
            gaf07CircleRatio_G47 S.F.family.toLocalChartPacketsC14.toLocalChartPackets) ∧
        M.ψ '' S.chain.zeroUnion_ZSP35 ∪ M.ψ '' (S.goodCut_OCL B hT hεr).slimSet ∪
          M.ψ '' (S.goodCut_OCL B hT hεr).M₂ = univ ∧
        ∀ j x, S.stageProjW_R74 j x =
          S.chain.toChain.Θ_BAS j (S.chain.toChain.stageMap_BAS j (M.ψ.symm x))) ∧
      (M.ψ '' (S.goodCut_OCL B hT hεr).M₃ = M.ψ '' (S.goodCut_OCL B hT hεr).M₂ \
          relInt (M.ψ '' (S.goodCut_OCL B hT hεr).M₂)
            (M.ψ '' (S.goodCut_OCL B hT hεr).edgeSet) ∧
        M.ψ '' frontier (S.goodCut_OCL B hT hεr).slimSet =
          frontier (M.ψ '' (S.goodCut_OCL B hT hεr).slimSet) ∧
        (∀ j (T' : Set (BlockSpace (fun _ : CGPTag
            S.F.family.toLocalChartPacketsC14.toLocalChartFamily
            S.F.family.toLocalChartPacketsC14.zero => EuclideanSpace ℝ (Fin 2)))),
          (S.chain.toGaf02ChainE.cutQ_R74 j ∘ M.ψ.symm) ⁻¹' T' =
            M.ψ '' (S.chain.toGaf02ChainE.cutQ_R74 j ⁻¹' T')) ∧
        M.ψ '' (S.goodCut_OCL B hT hεr).edgeSource =
          (S.chain.toGaf02ChainE.cutQ_R74 1 ∘ M.ψ.symm) ⁻¹'
            (S.goodCut_OCL B hT hεr).edgeBaseOpen ∧
        M.ψ '' (S.goodCut_OCL B hT hεr).circleSource =
          (S.chain.toGaf02ChainE.cutQ_R74 0 ∘ M.ψ.symm) ⁻¹'
            (S.goodCut_OCL B hT hεr).circleBaseOpen) ∧
      Nonempty (StrongCertificate W (BoundaryTori.empty W)) := by
  obtain ⟨Rw, L⟩ := closed_rows_at_of_rowsU74 S B _ Htail Hrows
  exact ⟨Rw, L, closed_link_values_goodCut_R74LND S B hT hεr,
    (S.goodCut_OCL B hT hεr).transport_R74, exists_strongCertificate_of_rows_GFIN Rw⟩

/-- **CL1 at `D_R` from the numerics record and the member facts**: `hT := N.strategy_below`,
`hεr := N.eps_lt`, `Htail := Htail.facts D_R`. -/
theorem closed_rows_atDR_of_numerics_U74 {K : ℕ}
    {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
    {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}
    (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) (B : ClosedBases74 S)
    (N : ClosedRowsNumericsAt74 S) (Htail : ClosedFdcMemberFacts74 S B)
    (Hrows : RemainingActualRowExitsU74 S B (S.goodCut_OCL B N.strategy_below N.eps_lt)) :
    ∃ Rw : FC39RowsV2 W (BoundaryTori.empty W),
      ClosedRowsLinkAtU74 S B (S.goodCut_OCL B N.strategy_below N.eps_lt) Rw ∧
      Nonempty (StrongCertificate W (BoundaryTori.empty W)) := by
  obtain ⟨Rw, L, -, -, hc⟩ := closed_rows_values_atDR_U74 S B N.strategy_below N.eps_lt
    (Htail.facts _) Hrows
  exact ⟨Rw, L, hc⟩

/-- **Consumer on the register**: on the sources of `register_yields_fdcFacts_RNUM` (numerics
record `N`, member facts `Htail` for every bases object), the development-stage record `Hrows` at
`D_R` gives the link at `D_R` and the certificate of GROUP G. -/
theorem register_yields_closed_rows_atDR_of_rows_U74 (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ x, 0 < x → 0 < A x) (Wseq : ℕ → CompactCarrier.{u})
    (gseq : ∀ m, SmoothRiemannianMetric (Wseq m).model (Wseq m).Carrier)
    (hf : ∀ m, ClosedMemberFacts (Wseq m))
    (hg : ∀ m, closedCollapseHypotheses (Wseq m) (gseq m) K A (closedCounterexampleRatio (m + 2))) :
    ∃ T : ClosedThresholdsV4 (earlyDataSharedV4 K),
      ∀ R : ClosedRegisterV4 (earlyDataSharedV4 K) T, ∃ εr δ Λz : ℝ, 0 < εr ∧ εr < 1 / 4 ∧
        ∃ n : ℕ, ∀ m, n ≤ m → ∃ M : ClosedModel (Wseq m) (gseq m), Nonempty M.X ∧
          ∀ x₀ : M.X, ∃ S : ClosedChainEZRowsSource_RGC K R M δ εr Λz, S.chain.x₀ = x₀ ∧
            ∃ N : ClosedRowsNumericsAt74 S, ∀ B : ClosedBases74 S,
              RemainingActualRowExitsU74 S B (S.goodCut_OCL B N.strategy_below N.eps_lt) →
                ∃ Rw : FC39RowsV2 (Wseq m) (BoundaryTori.empty (Wseq m)),
                  ClosedRowsLinkAtU74 S B (S.goodCut_OCL B N.strategy_below N.eps_lt) Rw ∧
                  Nonempty (StrongCertificate (Wseq m) (BoundaryTori.empty (Wseq m))) := by
  obtain ⟨T, -, -, -, hR⟩ := register_yields_fdcFacts_RNUM K hK A hA Wseq gseq hf hg
  refine ⟨T, fun R => ?_⟩
  obtain ⟨εr, δ, Λz, h0, h14, n, hn⟩ := hR R
  refine ⟨εr, δ, Λz, h0, h14, n, fun m hm => ?_⟩
  obtain ⟨M, hne, hS⟩ := hn m hm
  refine ⟨M, hne, fun x₀ => ?_⟩
  obtain ⟨S, hx, ⟨N⟩, hB⟩ := hS x₀
  exact ⟨S, hx, N, fun B Hrows => closed_rows_atDR_of_numerics_U74 S B N (hB B) Hrows⟩

end DifferentialGeometry.Geometry.Collapse
