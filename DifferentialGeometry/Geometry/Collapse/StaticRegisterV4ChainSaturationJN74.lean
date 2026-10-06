import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeRimRelIntJN74
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainCircleTrivAtOCL
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainCoverAtOCL
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainEdgeSetEqOCL

/-!
# Draft 74, FDC03's saturation `M₃ = q₀⁻¹(C₁)` at `D_R` (clause (f') of the circle facts)

Lane S-JUNCTIONS (by S-JUNCTIONS3), G8 (suffix `_JN74`). From the raw FDC03 / EDP06 set geometry
of the chain (no corner record, no `faces` / `cf` input):

* `goodCut_M₃_saturated_JN74`: `M₃(D_R) = q₀⁻¹(C₁(D_R))` on the actual chain
  (`cutM3_saturated_JN74`: EDP06's saturation of `M₂ ∩ X₁`, `E`-constancy of `T` and `q₁`,
  `int_{M₂} M^edge = M^edge ∩ {T < 4Δ}`);
* **`cut_M₃_eq_circleRegion_JN74`**: O-CL1's head `hsat`, `cut.M₃ = cut.circleRegion` for
  `cut = (S.closedStagesAt_OCL B hT hεr A zero).cut` (the carried `M₃` is `M.ψ(M₃)` by
  `M₂_at_OCL`, `edgeSet_at_OCL` and `relInt_image_R74`; the carried circle region is
  `M.ψ(q₀⁻¹(C₁))` by `stageSet_LND74`);
* `circleCutFactsAt2_JN74`: `circleCutFactsAt2_OCL` with `hsat` produced.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry GC.Endpoint GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Analysis
open DifferentialGeometry.Topology.Manifold
open GC.GraphManifold GC.GraphManifold.Assembly GC.GraphManifold.Assembly.FC39P0

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

namespace ClosedChainEZRowsSource_RGC

variable {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
  {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{0}}
  {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}

section At

variable (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) (B : ClosedBases74 S)
  (hT : ClosedStrategyBelowV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)))
  (hεr : εr < 1 / 2) (A : SmoothStageBases74 S) (zero : ZSP02SmoothExit74 S)

/-- **`M₃(D_R) = q₀⁻¹(C₁(D_R))` on the actual chain** (FDC03 / EDP06 saturation). -/
theorem goodCut_M₃_saturated_JN74 (A : SmoothStageBases74 S) (hNb : T.Nb = maxNb_V4C)
    (hcw : T.cw = maxCw_V4C) :
    (S.goodCut_OCL B hT hεr).M₃ =
      S.chain.toGaf02ChainE.cutQ_R74 0 ⁻¹' (S.goodCut_OCL B hT hεr).C₁ := by
  have hE := R.edpE_numerics_RGC hT hNb hcw
  have hg7 := R.gaf07_numerics_OCL hT
  have hfacts := (S.goodCut_facts_OCL B hT hεr).2.2.2
  ext x
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x', hx', hxx'⟩
    have hx'X : x' ∈ S.chain.circleDomain_EFE :=
      S.chain.mem_circleDomain_of_EFE (hfacts hx').1 (hfacts hx').2
    exact S.chain.cutM3_saturated_JN74 A hg7.1 hg7.2 hεr R.two_le_Δ_EDP23 hE.2.2.1 hE.2.2.2.1
      hE.2.2.2.2.1 hE.2.2.2.2.2.1 hE.2.2.2.2.2.2.1 hE.2.2.2.2.2.2.2.1 hE.2.2.2.2.2.2.2.2
      (S.goodCut_OCL B hT hεr).K₃ (S.goodCut_OCL B hT hεr).D₃
      (S.goodCut_OCL B hT hεr).D₃_eq (S.goodCut_OCL B hT hεr).K₃_req
      (S.goodCut_OCL B hT hεr).K₃_faces (S.goodCut_D₃_reg_OCL B hT hεr)
      (S.goodCut_D₃_bdry_OCL B hT hεr) hx' hx'X hxx'.symm

/-- **O-CL1's `hsat` at `D_R`, produced** (clause (f'), FDC03's saturation): the carried
`M₃ = M₂ ∖ int_{M₂} M^edge` equals the carried circle region `q₀⁻¹(C₁)`. -/
theorem cut_M₃_eq_circleRegion_JN74 (hNb : T.Nb = maxNb_V4C) (hcw : T.cw = maxCw_V4C) :
    (S.closedStagesAt_OCL B hT hεr A zero).cut.M₃ =
      (S.closedStagesAt_OCL B hT hεr A zero).cut.circleRegion := by
  have hE := S.goodCut_edgeSet_eq_OCL B hT hεr hNb hcw
  have hM3 : (S.closedStagesAt_OCL B hT hεr A zero).cut.M₃ =
      M.ψ '' (S.goodCut_OCL B hT hεr).M₃ := by
    change (S.closedStagesAt_OCL B hT hεr A zero).cut.M₂ \
      relInt (S.closedStagesAt_OCL B hT hεr A zero).cut.M₂
        (S.closedStagesAt_OCL B hT hεr A zero).cut.edgeSet = _
    rw [S.M₂_at_OCL B hT hεr A zero, S.edgeSet_at_OCL B hT hεr A zero hE,
      relInt_image_R74 M.ψ, ← image_sdiff (f := (M.ψ : M.X → W.Carrier)) M.ψ.injective]
    rfl
  have hR : (S.closedStagesAt_OCL B hT hεr A zero).cut.circleRegion =
      M.ψ '' (S.chain.toGaf02ChainE.cutQ_R74 0 ⁻¹' (S.goodCut_OCL B hT hεr).C₁) := by
    change {x | ∃ hx : x ∈ (S.closedStagesAt_OCL B hT hεr A zero).A.circle.parent,
      (S.closedStagesAt_OCL B hT hεr A zero).A.circle.proj ⟨x, hx⟩ ∈
        (S.closedStagesAt_OCL B hT hεr A zero).cut.C₁} = _
    rw [stageSet_LND74 (S.closedStagesAt_OCL B hT hεr A zero).circle_ident,
      (S.closedStagesAt_OCL B hT hεr A zero).cut_C₁]
    rfl
  rw [hM3, hR, S.goodCut_M₃_saturated_JN74 B hT hεr A hNb hcw]

/-- **The circle facts at `D_R` with the saturation PRODUCED** (`circleCutFactsAt2_OCL` with
`hsat := cut_M₃_eq_circleRegion_JN74`): only the trivialization inputs of the actual chain and the
FDC04 facts `Htail` remain. -/
def circleCutFactsAt2_JN74 (hNb : T.Nb = maxNb_V4C) (hcw : T.cw = maxCw_V4C)
    (Htail : ClosedFdcFacts74 (S.goodCut_OCL B hT hεr)) :
    CircleCutFacts74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut :=
  S.circleCutFactsAt2_OCL B hT hεr A zero Htail
    (S.cut_M₃_eq_circleRegion_JN74 B hT hεr A zero hNb hcw)

end At

end ClosedChainEZRowsSource_RGC

end DifferentialGeometry.Geometry.Collapse
