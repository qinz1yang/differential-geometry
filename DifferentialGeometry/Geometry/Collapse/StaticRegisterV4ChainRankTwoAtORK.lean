import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainRankTwoKernelsORK
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainCbaseDomainOCL

/-!
# Draft 74, FC39 gate 1A clause (c): `rank_two` of `EdgeCutFacts74` at `D_R`

Lane O-RANK2 (`_ORK`), group G2. The `rank_two` field of `EdgeCutFacts74 P.A P.cut` for the
produced stage geometry `P = S.closedStagesAt_OCL B hT hεr A zero` at the produced cut choice
`D_R = S.goodCut_OCL B hT hεr` (clause (c) of the gate-1A table), all numerics at the register:

* **`edgeCutFacts_rank_two_at_OCL_ORK`**: at every point `x` of the cut's edge source with
  `T x = 4Δ`, `(d(q₁ ∘ M.ψ⁻¹), dT) : T_x W → T V × ℝ` is onto. Proof: `M.ψ⁻¹ x` is a rim point of
  the chain's edge source (`rim_point_symm_ORK`); S-EDP-FDC4's `edge_coord_height_surj_EFE`
  gives an index `k` with `(d g_k, dT)` onto `ℝ²` there; the chain rule through `M.ψ`
  (`pair_realized_of_comp_ORK`) moves this to `(d(g_k ∘ M.ψ⁻¹), d(T ∘ M.ψ⁻¹))` at `x`; the
  descended functional `u` on the tangent line of `V` (`exists_descended_functional_W_ORK`) and
  the height identity (`edgeHeight_mfderiv_ORK`) finish with `surjective_pair_of_comp_EFE`;
* **`edgeCutFactsAt3_ORK`**: the complete `EdgeCutFacts74 P.A P.cut` from FDC04's member facts
  `Htail` alone (O-CL1's `edgeCutFactsAt2_OCL` with `rank_two` produced).

No numeric premise beyond those of `R.edpE_numerics_RGC` (`hNb`, `hcw`, `hT`) is needed.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry GC.Endpoint GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Analysis
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

/-- **`rank_two` of the edge facts at `D_R`** (clause (c)): at every point of the cut's edge
source on the rim `T = 4Δ`, the pair `(d(q₁ ∘ M.ψ⁻¹), dT)` is onto `T V × ℝ`. -/
theorem edgeCutFacts_rank_two_at_OCL_ORK (hNb : T.Nb = maxNb_V4C) (hcw : T.cw = maxCw_V4C) :
    ∀ x : (S.closedStagesAt_OCL B hT hεr A zero).cut.edgeSource,
      (S.closedStagesAt_OCL B hT hεr A zero).cut.edgeHeight x =
        (S.closedStagesAt_OCL B hT hεr A zero).A.edge.level →
      Surjective fun v : TangentSpace W.model (x : W.Carrier) =>
        (mfderiv W.model (𝓡 1) ((S.closedStagesAt_OCL B hT hεr A zero).A.edge.restrictProj
            (S.closedStagesAt_OCL B hT hεr A zero).cut.edgeBaseOpen) x v,
          mfderiv W.model 𝓘(ℝ, ℝ) (S.closedStagesAt_OCL B hT hεr A zero).cut.edgeHeight x v) := by
  intro x hx
  obtain ⟨hp, hx'⟩ := S.rim_point_symm_ORK B hT hεr A zero x hx
  obtain ⟨-, -, hc, hϑ, hε0, hε, hγc, hγc1, hβc1⟩ := R.edpE_numerics_RGC hT hNb hcw
  obtain ⟨k, hk⟩ := S.chain.toGaf02ChainE.edge_coord_height_surj_EFE R.two_le_Δ_EDP23 hc hϑ
    hε0 hε hγc hγc1 hβc1 ⟨_, hp⟩ hx'
  have hG₁ : ContMDiff W.model 𝓘(ℝ, ℝ) ∞
      (S.chain.toGaf02ChainE.edgeCoordG_EFE k ∘ M.ψ.symm) :=
    (S.chain.toGaf02ChainE.contMDiff_edgeCoordG_EFE k).comp M.ψ.symm.contMDiff
  have hG₂ : ContMDiff W.model 𝓘(ℝ, ℝ) ∞
      (S.chain.toGaf02ChainE.edgeHeightGlobal_EFE ∘ M.ψ.symm) :=
    S.chain.toGaf02ChainE.contMDiff_edgeHeightGlobal_EFE.comp M.ψ.symm.contMDiff
  have hW := pair_realized_of_comp_ORK (q := (x : W.Carrier)) (M.ψ.apply_symm_apply _)
    (M.ψ.mdifferentiable (by simp) (M.ψ.symm (x : W.Carrier)))
    (hG₁.contMDiffAt.mdifferentiableAt (by simp)) (hG₂.contMDiffAt.mdifferentiableAt (by simp))
    (funext fun q => congrArg (S.chain.toGaf02ChainE.edgeCoordG_EFE k) (M.ψ.symm_apply_apply q))
    (funext fun q => congrArg S.chain.toGaf02ChainE.edgeHeightGlobal_EFE
      (M.ψ.symm_apply_apply q)) hk
  obtain ⟨u, hu⟩ := S.exists_descended_functional_W_ORK A
    (S.closedStagesAt_OCL B hT hεr A zero).cut.edgeBaseOpen k x
  have hB : Module.finrank ℝ (TangentSpace (𝓡 1)
      ((S.closedStagesAt_OCL B hT hεr A zero).A.edge.restrictProj
        (S.closedStagesAt_OCL B hT hεr A zero).cut.edgeBaseOpen x)) = 1 := by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin 1)) = 1
    simp
  refine surjective_pair_of_comp_EFE hB
    (mfderiv W.model (𝓡 1) ((S.closedStagesAt_OCL B hT hεr A zero).A.edge.restrictProj
      (S.closedStagesAt_OCL B hT hεr A zero).cut.edgeBaseOpen) x).toLinearMap
    (mfderiv W.model 𝓘(ℝ, ℝ) (S.closedStagesAt_OCL B hT hεr A zero).cut.edgeHeight x).toLinearMap
    u ?_
  intro r s
  obtain ⟨w, hw1, hw2⟩ := hW r s
  exact ⟨w, (hu w).trans hw1, (S.edgeHeight_mfderiv_ORK B hT hεr A zero x w).trans hw2⟩

/-- **The complete edge facts at `D_R`** from FDC04's member facts alone: O-CL1's
`edgeCutFactsAt2_OCL` with `rank_two` produced (clauses (c), (d) of the gate-1A table). -/
theorem edgeCutFactsAt3_ORK (hNb : T.Nb = maxNb_V4C) (hcw : T.cw = maxCw_V4C)
    (Htail : ClosedFdcFacts74 (S.goodCut_OCL B hT hεr)) :
    EdgeCutFacts74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut :=
  S.edgeCutFactsAt2_OCL B hT hεr A zero hNb hcw Htail
    (S.edgeCutFacts_rank_two_at_OCL_ORK B hT hεr A zero hNb hcw)

end At

end ClosedChainEZRowsSource_RGC

end DifferentialGeometry.Geometry.Collapse
