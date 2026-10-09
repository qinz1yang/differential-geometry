import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainHprimCoreJN74
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainSlimEndFreeOCL
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainFacesCoreJN74

/-!
# Draft 74, the endpoint primitives at `D_R`: the face equation of a new slim end

Lane S-JUNCTIONS (by S-JUNCTIONS5), G32 (suffix `_JN74`). For an endpoint `e` whose label is a NEW
slim end `en` of the exit `slimExitAt3_OCL`: the end function equals `b ∘ q₁` on the neighbourhood
of
the end, with `b = e_en ∘ Q₂ ∘ ι` (`e_en` the end coordinate of `slimEnd3_coord_OCL`, G4/G3 of
S-REG-CHAIN6; `f₃ = Q₂ ∘ π₂E`), smooth near `e`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry GC.Endpoint GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Analysis
open DifferentialGeometry.Topology
open GC.GraphManifold GC.GraphManifold.Assembly GC.GraphManifold.Assembly.FC39P0

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

open DifferentialGeometry.Topology.Handle in
attribute [local instance] closedCellChartedSpaceSucc closedCellIsManifold

namespace ClosedChainEZRowsSource_RGC

variable {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
  {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{0}}
  {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}

section At

variable (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz)

/-- The second stage projection `Q₂` of the source's packets, on the block space. -/
abbrev stageQ2_JN74 : S.blockSpace_R74 →L[ℝ] S.blockSpace_R74 :=
  (gafStageQ S.F.family.toLocalChartPacketsC14.toLocalChartFamily
    S.F.family.toLocalChartPacketsC14.zero 2).starProjection

/-- **`f₃ = Q₂ ∘ π₂E`**. -/
theorem slimMap_eq_JN74 (z : M.X) :
    S.chain.slimMap_ZSP35 z = S.stageQ2_JN74 (S.chain.toGaf02ChainE.edgeBlockProj_EFE z) :=
  (gafStageQ_two_starProjection_one_EFE S.F.family.toLocalChartPacketsC14.toLocalChartFamily
    S.F.family.toLocalChartPacketsC14.zero _).symm

variable (B : ClosedBases74 S)
  (hT : ClosedStrategyBelowV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)))
  (hεr : εr < 1 / 2) (A : SmoothStageBases74 S) (hK : 5 ≤ K)
  (edge : EDP04WholeDiskExitU74 (S.stagesAtZ_OCL B hT hεr A))
  (final : FDC03ActualRemainderU74 (S.stagesAtZ_OCL B hT hεr A))

/-- **The chain data of a new slim end label**: the end coordinate `e` (smooth on the open `Ne`,
equal to the end function on the neighbourhood of the end) and a point `z` of the edge source over
the endpoint inside the end set. -/
theorem slim_label_data_JN74
    (en : (S.slimPieces3_JN74 B hT hεr A hK).NewEnd)
    (e : (S.rows3_JN74 B hT hεr A hK edge final).edge.EdgeEnd)
    (hdisk : (S.rows3_JN74 B hT hεr A hK edge final).edge.disk e.1 ⊆
      (S.slimPieces3_JN74 B hT hεr A hK).endSet en.1) :
    ∃ (Ne : Set S.blockSpace_R74) (ee : S.blockSpace_R74 → ℝ)
      (z : (S.rows3_JN74 B hT hεr A hK edge final).edge.source),
      (S.rows3_JN74 B hT hεr A hK edge final).edge.proj z = e.1 ∧
      IsOpen Ne ∧ ContDiffOn ℝ ∞ ee Ne ∧
      S.chain.slimMap_ZSP35 (M.ψ.symm z.1) ∈ Ne ∧
      (∀ y ∈ ((S.slimPieces3_JN74 B hT hεr A hK).endNear en : Set W.Carrier),
        S.chain.slimMap_ZSP35 (M.ψ.symm y) ∈ Ne) ∧
      ∀ y ∈ ((S.slimPieces3_JN74 B hT hεr A hK).endNear en : Set W.Carrier),
        (S.slimPieces3_JN74 B hT hεr A hK).endFn en y =
          ee (S.chain.slimMap_ZSP35 (M.ψ.symm y)) := by
  obtain ⟨Ne, ee, hNo, hee, hmem, heq⟩ := S.slimEnd3_coord_OCL B hT hεr A hK en
  obtain ⟨x₀, hx₀⟩ := (S.rows3_JN74 B hT hεr A hK edge final).disk_nonempty_JN74 e.1
  have hn : x₀ ∈ ((S.slimPieces3_JN74 B hT hεr A hK).endNear en : Set W.Carrier) :=
    (S.slimPieces3_JN74 B hT hεr A hK).residualSet_subset_residualNear_JN74 (Sum.inr en)
      (hdisk hx₀)
  obtain ⟨z, ⟨hzc, -⟩, rfl⟩ := hx₀
  exact ⟨Ne, ee, z, hzc, hNo, hee, hmem _ hn, hmem, heq⟩

variable (zero : ZSP02SmoothExit74 S)

/-- **Smoothness of the slim end equation near the endpoint**. -/
theorem slim_smooth_JN74
    (F : EdgeCutFacts74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut)
    {Ne : Set S.blockSpace_R74} {ee : S.blockSpace_R74 → ℝ} (hNo : IsOpen Ne)
    (hee : ContDiffOn ℝ ∞ ee Ne)
    (c₀ : (edgeBundle74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut F).Base)
    (z : (edgeBundle74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut F).source)
    (hzc : (edgeBundle74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut F).proj z = c₀)
    (hz : S.chain.slimMap_ZSP35 (M.ψ.symm z.1) ∈ Ne) :
    let _ := A.edgeChartedSpace1
    ∃ U₀ : TopologicalSpace.Opens (edgeBundle74 (S.closedStagesAt_OCL B hT hεr A zero).A
        (S.closedStagesAt_OCL B hT hεr A zero).cut F).Base, c₀ ∈ U₀ ∧
      ContMDiffOn (𝓡 1) 𝓘(ℝ, ℝ) ∞
        (fun c => ee (S.stageQ2_JN74 (S.edgeVal_JN74 B hT hεr A zero F c))) U₀ := by
  intro _
  have hev := S.contMDiff_edgeVal_JN74 B hT hεr A zero F
  have hq : ContMDiff (𝓡 1) 𝓘(ℝ, S.blockSpace_R74) ∞
      fun c => S.stageQ2_JN74 (S.edgeVal_JN74 B hT hεr A zero F c) :=
    (S.stageQ2_JN74.contDiff.contMDiff).comp hev
  refine ⟨⟨{c | S.stageQ2_JN74 (S.edgeVal_JN74 B hT hεr A zero F c) ∈ Ne},
    hNo.preimage hq.continuous⟩, ?_, ?_⟩
  · change S.stageQ2_JN74 (S.edgeVal_JN74 B hT hεr A zero F c₀) ∈ Ne
    rw [← hzc, S.edgeVal_proj_JN74 B hT hεr A zero F z, ← S.slimMap_eq_JN74]
    exact hz
  · exact hee.contMDiffOn.comp hq.contMDiffOn (fun c hc => hc)

/-- **The slim end equation reads `e_en ∘ f₃ = (e_en ∘ Q₂ ∘ ι) ∘ q₁`** on the edge source. -/
theorem slim_eq_JN74
    (F : EdgeCutFacts74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut)
    (ee : S.blockSpace_R74 → ℝ) (x : W.Carrier) (hx : x ∈ (edgeBundle74
      (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut F).source) :
    ee (S.chain.slimMap_ZSP35 (M.ψ.symm x)) =
      ee (S.stageQ2_JN74 (S.edgeVal_JN74 B hT hεr A zero F
        ((edgeBundle74 (S.closedStagesAt_OCL B hT hεr A zero).A
          (S.closedStagesAt_OCL B hT hεr A zero).cut F).proj ⟨x, hx⟩))) := by
  rw [S.edgeVal_proj_JN74 B hT hεr A zero F ⟨x, hx⟩, S.slimMap_eq_JN74]

end At

end ClosedChainEZRowsSource_RGC

end DifferentialGeometry.Geometry.Collapse
