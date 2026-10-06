import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainStagesCutOCL
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeRankTwoEFE

/-!
# Draft 74, FC39 gate 1A clause (c): three kernels for `rank_two` at `D_R`

Lane O-RANK2 (`_ORK`), group G1. The three pieces that bind S-EDP-FDC4's chain-level rank two
(`edge_coord_height_surj_EFE`: `(d g_k, dT)` onto `ℝ²` at a rim point of `edgeSource_EFE`) to the
`rank_two` field of `EdgeCutFacts74` on the closed route (edge stage `q₁ ∘ M.ψ⁻¹` on `W`):

* **`rim_point_symm_ORK`** (the rim points): a point `x` of the edge source of the cut at `D_R`
  with `T x = 4Δ` comes from a point `M.ψ⁻¹ x` of the chain's edge source `U₂ ∩ π₂E⁻¹(ratio)`
  (the open edge base of `D_R` lies in EDP02's `B₂ = W₂ ∩ ratio`) on the rim `A/s = 4Δ`;
* **`exists_descended_functional_W_ORK`** (the base derivative on `W`): over any open `V ⊆ W₂`, the
  differential of `q₁ ∘ M.ψ⁻¹ : q₁⁻¹(V) → V` (model `𝓡 1`) composed with the linear functional
  `u = ℓ_k ∘ dι` is the differential of `g_k ∘ M.ψ⁻¹` (`g_k = ℓ_k ∘ π₂E`, `ℓ_k` linear,
  `ι : W₂ → block space` smooth); with **`edgeHeight_mfderiv_ORK`** for the height;
* **`pair_realized_of_comp_ORK`** (the cross-model step through `ψ`): if `(d(G₁ ∘ φ), d(G₂ ∘ φ))`
  realizes every pair of reals at `p`, then `(dG₁, dG₂)` does at `φ p` (chain rule; no inverse of
  `dφ` is needed).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry GC.Endpoint GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Analysis
open GC.GraphManifold GC.GraphManifold.Assembly GC.GraphManifold.Assembly.FC39P0
open DifferentialGeometry.Topology.Manifold

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

/-- **Cross-model pair transfer** (chain rule): if the differentials of `f₁ = G₁ ∘ φ` and
`f₂ = G₂ ∘ φ` realize every pair of reals at `p`, then those of `G₁, G₂` do at `q = φ p`. -/
theorem pair_realized_of_comp_ORK {E₁ H₁ E₂ H₂ : Type*} [NormedAddCommGroup E₁]
    [NormedSpace ℝ E₁] [TopologicalSpace H₁] [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
    [TopologicalSpace H₂] {I₁ : ModelWithCorners ℝ E₁ H₁} {I₂ : ModelWithCorners ℝ E₂ H₂}
    {N₁ N₂ : Type*} [TopologicalSpace N₁] [ChartedSpace H₁ N₁] [TopologicalSpace N₂]
    [ChartedSpace H₂ N₂] {φ : N₁ → N₂} {p : N₁} {q : N₂} (hq : φ p = q)
    (hφ : MDifferentiableAt I₁ I₂ φ p) {G₁ G₂ : N₂ → ℝ} {f₁ f₂ : N₁ → ℝ}
    (hG₁ : MDifferentiableAt I₂ 𝓘(ℝ, ℝ) G₁ q) (hG₂ : MDifferentiableAt I₂ 𝓘(ℝ, ℝ) G₂ q)
    (hf₁ : G₁ ∘ φ = f₁) (hf₂ : G₂ ∘ φ = f₂)
    (h : ∀ r s : ℝ, ∃ v : TangentSpace I₁ p, mvfderiv I₁ f₁ p v = r ∧ mvfderiv I₁ f₂ p v = s) :
    ∀ r s : ℝ, ∃ w : TangentSpace I₂ q, mvfderiv I₂ G₁ q w = r ∧ mvfderiv I₂ G₂ q w = s := by
  subst hq hf₁ hf₂
  intro r s
  obtain ⟨v, h1, h2⟩ := h r s
  refine ⟨mfderiv I₁ I₂ φ p v, ?_, ?_⟩
  · rw [← hG₁.mvfderiv_comp_apply hφ]
    exact h1
  · rw [← hG₂.mvfderiv_comp_apply hφ]
    exact h2

namespace ClosedChainEZRowsSource_RGC

variable {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
  {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{0}}
  {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}

section Stage

variable (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) (A : SmoothStageBases74 S)

/-- **The base derivative on `W`** (descended functional): over an open `V ⊆ W₂`, the differential
of `g_k ∘ M.ψ⁻¹` at a point of `q₁⁻¹(V)` is `u ∘ d(q₁ ∘ M.ψ⁻¹)` for a linear functional `u` on
the tangent line of `V`. -/
theorem exists_descended_functional_W_ORK (V : TopologicalSpace.Opens (S.edgeStage74 A).Base)
    (k : S.F.family.toLocalChartPacketsC14.edge.finite_centres.toFinset)
    (x : (S.edgeStage74 A).restrictParent V) :
    ∃ u : TangentSpace (𝓡 1) ((S.edgeStage74 A).restrictProj V x) →ₗ[ℝ] ℝ,
      ∀ w : TangentSpace W.model (x : W.Carrier),
        u (mfderiv W.model (𝓡 1) ((S.edgeStage74 A).restrictProj V) x w) =
          mvfderiv W.model (S.chain.toGaf02ChainE.edgeCoordG_EFE k ∘ M.ψ.symm)
            (x : W.Carrier) w := by
  let valV : V → S.blockSpace_R74 := fun c =>
    ((show ↥(S.chain.toChain.finalBase_BAS 1) from (c : (S.edgeStage74 A).Base)) :
      S.blockSpace_R74)
  have hι : ContMDiff (𝓡 1) 𝓘(ℝ, S.blockSpace_R74) ∞ (fun c : (S.edgeStage74 A).Base =>
      ((show ↥(S.chain.toChain.finalBase_BAS 1) from c) : S.blockSpace_R74)) := by
    let _ := A.edgeChartedSpace1
    exact A.edge_isManifold1.2.1
  have hval : ContMDiff (𝓡 1) 𝓘(ℝ, S.blockSpace_R74) ∞ valV :=
    hι.comp (contMDiff_subtype_val (I := 𝓡 1) (U := V))
  let F := (S.edgeStage74 A).restrictProj V
  have hF : ContMDiff W.model (𝓡 1) ∞ F := (S.edgeStage74 A).restrictProj_smooth V
  let ℓ : S.blockSpace_R74 →L[ℝ] ℝ := (S.F.ρ k.1)⁻¹ • axisCoordCLM_BAS.comp
    (gafEdgeVector S.F.family.toLocalChartPacketsC14.toLocalChartFamily
      S.F.family.toLocalChartPacketsC14.zero k)
  have hℓ : ∀ z : (S.edgeStage74 A).restrictParent V,
      ℓ (valV (F z)) = (S.chain.toGaf02ChainE.edgeCoordG_EFE k ∘ M.ψ.symm) (z : W.Carrier) :=
    fun z => by
    change (S.F.ρ k.1)⁻¹ * EuclideanSpace.proj (0 : Fin 2) (blockVectorCLM (V := fun _ :
      CGPTag S.F.family.toLocalChartPacketsC14.toLocalChartFamily
        S.F.family.toLocalChartPacketsC14.zero => EuclideanSpace ℝ (Fin 2))
        (.inr (.inr (.inl k)))
        ((gafStageQ S.F.family.toLocalChartPacketsC14.toLocalChartFamily
          S.F.family.toLocalChartPacketsC14.zero 1).starProjection
          (S.chain.toChain.E (M.ψ.symm (z : W.Carrier))))) =
      EuclideanSpace.proj (0 : Fin 2) (gafEdgeVector
        S.F.family.toLocalChartPacketsC14.toLocalChartFamily
        S.F.family.toLocalChartPacketsC14.zero k
        (S.chain.toChain.E (M.ψ.symm (z : W.Carrier)))) / S.F.ρ k.1
    rw [gafStageQ_edgeVector_FDC S.F.family.toLocalChartPacketsC14.toLocalChartPackets k
      (S.chain.toChain.E (M.ψ.symm (z : W.Carrier))), div_eq_inv_mul]
    rfl
  have hmd : MDifferentiableAt (𝓡 1) 𝓘(ℝ, S.blockSpace_R74) valV (F x) :=
    (hval (F x)).mdifferentiableAt (by simp)
  have hpd : MDifferentiableAt W.model (𝓡 1) F x := (hF x).mdifferentiableAt (by simp)
  have hPv : MDifferentiableAt W.model 𝓘(ℝ, S.blockSpace_R74) (valV ∘ F) x := hmd.comp x hpd
  have hchain : mvfderiv W.model (valV ∘ F) x =
      (mvfderiv (𝓡 1) valV (F x)).comp (mfderiv W.model (𝓡 1) F x) := hmd.mvfderiv_comp hpd
  let u : TangentSpace (𝓡 1) (F x) →L[ℝ] ℝ := ℓ.comp (mvfderiv (𝓡 1) valV (F x))
  have hG : ContMDiff W.model 𝓘(ℝ, ℝ) ∞
      (S.chain.toGaf02ChainE.edgeCoordG_EFE k ∘ M.ψ.symm) :=
    (S.chain.toGaf02ChainE.contMDiff_edgeCoordG_EFE k).comp M.ψ.symm.contMDiff
  refine ⟨u.toLinearMap, fun w => ?_⟩
  have h1 : mvfderiv W.model (fun z : (S.edgeStage74 A).restrictParent V =>
      (S.chain.toGaf02ChainE.edgeCoordG_EFE k ∘ M.ψ.symm) (z : W.Carrier)) x =
      mvfderiv W.model (S.chain.toGaf02ChainE.edgeCoordG_EFE k ∘ M.ψ.symm) (x : W.Carrier) :=
    mvfderiv_comp_subtype_val_EFE ((S.edgeStage74 A).restrictParent V) (fun _ => rfl) x
      (hG.contMDiffAt.mdifferentiableAt (by simp))
  have h2 : (fun z : (S.edgeStage74 A).restrictParent V => ℓ ((valV ∘ F) z)) =
      fun z : (S.edgeStage74 A).restrictParent V =>
        (S.chain.toGaf02ChainE.edgeCoordG_EFE k ∘ M.ψ.symm) (z : W.Carrier) :=
    funext fun z => hℓ z
  have h3 := mvfderiv_clm_comp_apply_EDPE (I := W.model) ℓ hPv w
  calc u (mfderiv W.model (𝓡 1) F x w)
      = ℓ (mvfderiv W.model (valV ∘ F) x w) := by
        rw [hchain]
        rfl
    _ = mvfderiv W.model (fun z : (S.edgeStage74 A).restrictParent V => ℓ ((valV ∘ F) z)) x w :=
        h3.symm
    _ = mvfderiv W.model (fun z : (S.edgeStage74 A).restrictParent V =>
          (S.chain.toGaf02ChainE.edgeCoordG_EFE k ∘ M.ψ.symm) (z : W.Carrier)) x w := by
        rw [h2]
    _ = mvfderiv W.model (S.chain.toGaf02ChainE.edgeCoordG_EFE k ∘ M.ψ.symm)
          (x : W.Carrier) w :=
        congrArg (fun L => L w) h1

end Stage

section At

variable (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) (B : ClosedBases74 S)
  (hT : ClosedStrategyBelowV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)))
  (hεr : εr < 1 / 2) (A : SmoothStageBases74 S) (zero : ZSP02SmoothExit74 S)

/-- The edge height of the cut at `D_R` is the chain's global height `A/s` read through
`M.ψ⁻¹`. -/
theorem edgeHeight_at_ORK (x : (S.closedStagesAt_OCL B hT hεr A zero).cut.edgeSource) :
    (S.closedStagesAt_OCL B hT hεr A zero).cut.edgeHeight x =
      S.chain.toGaf02ChainE.edgeHeightGlobal_EFE (M.ψ.symm (x : W.Carrier)) := by
  change S.edgeHeightW_R74 (x : W.Carrier) = _
  rw [S.edgeHeightW_eq_R74]
  rfl

/-- **The height derivative at `D_R`**: the differential of the cut's edge height is that of the
chain's global height `A/s ∘ M.ψ⁻¹` on `W`. -/
theorem edgeHeight_mfderiv_ORK (x : (S.closedStagesAt_OCL B hT hεr A zero).cut.edgeSource)
    (w : TangentSpace W.model (x : W.Carrier)) :
    mfderiv W.model 𝓘(ℝ, ℝ) (S.closedStagesAt_OCL B hT hεr A zero).cut.edgeHeight x w =
      mvfderiv W.model (S.chain.toGaf02ChainE.edgeHeightGlobal_EFE ∘ M.ψ.symm)
        (x : W.Carrier) w := by
  have hG : ContMDiff W.model 𝓘(ℝ, ℝ) ∞
      (S.chain.toGaf02ChainE.edgeHeightGlobal_EFE ∘ M.ψ.symm) :=
    S.chain.toGaf02ChainE.contMDiff_edgeHeightGlobal_EFE.comp M.ψ.symm.contMDiff
  have h := mfderiv_comp_subtype_val_R74 (I := W.model)
    (S.closedStagesAt_OCL B hT hεr A zero).cut.edgeSource
    (f := S.chain.toGaf02ChainE.edgeHeightGlobal_EFE ∘ M.ψ.symm)
    (g := (S.closedStagesAt_OCL B hT hεr A zero).cut.edgeHeight)
    (fun z => S.edgeHeight_at_ORK B hT hεr A zero z) x
    (hG.contMDiffAt.mdifferentiableAt (by simp))
  rw [h]
  rfl

/-- **The rim points at `D_R`**: a point `x` of the cut's edge source with `T x = 4Δ` comes from
the point `M.ψ⁻¹ x` of the chain's edge source `U₂ ∩ π₂E⁻¹(ratio)`, on the rim `A/s = 4Δ`. -/
theorem rim_point_symm_ORK (x : (S.closedStagesAt_OCL B hT hεr A zero).cut.edgeSource)
    (hx : (S.closedStagesAt_OCL B hT hεr A zero).cut.edgeHeight x =
      (S.closedStagesAt_OCL B hT hεr A zero).A.edge.level) :
    ∃ hp : M.ψ.symm (x : W.Carrier) ∈ S.chain.toGaf02ChainE.edgeSource_EFE,
      S.chain.toGaf02ChainE.edgeHeight_EFE ⟨M.ψ.symm (x : W.Carrier), hp⟩ =
        4 * R.later.excl.Δ := by
  obtain ⟨h, hV⟩ := (S.edgeStage74 A).exists_of_mem_restrictParent x.2
  have h1 : M.ψ.symm (x : W.Carrier) ∈ S.edgeDomain_R74 := (mem_edgeParent_R74 (S := S)).1 h
  have hV' : S.stageProjW_R74 1 (x : W.Carrier) ∈ (S.goodCut_OCL B hT hεr).edgeBaseOpen := hV
  have h2 := ((S.goodCut_bases_OCL B hT hεr).1 hV').2
  refine ⟨⟨h1, h2⟩, ?_⟩
  have h3 := S.edgeHeight_at_ORK B hT hεr A zero x
  rw [hx] at h3
  exact h3.symm

end At

end ClosedChainEZRowsSource_RGC

end DifferentialGeometry.Geometry.Collapse
