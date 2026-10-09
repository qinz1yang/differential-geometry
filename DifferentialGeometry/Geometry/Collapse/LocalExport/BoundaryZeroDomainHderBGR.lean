import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryZeroDomainTransportBGR
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryChainEDerivative
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAffineHeightTransport
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCuspCoreChain
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryChainERowsBGR

/-!
# BCG07 F3: the derivative input of ZSP02 on the enhanced chain, and the `transport` field
(lane B-BCG-ROWS)

A3c (`BoundaryGaf02ChainE.stage_derivative_lt_BAUGD`, BAUG-D G9) is read through the inclusion
`val : W° → W` and the interior projection: for the kernel input `f = pr_int ∘ C.E ∘ val`
(`zeroBindMap_BGR`) and the ported CGP01 map `𝓔⁰ = cgpGlobalMap_BAUGP S.family …`
(`= pr_int ∘ F_∂ ∘ val`), `‖df − d𝓔⁰‖ ≤ H |·|_ĝ` with `0 ≤ H < c₂` (`‖pr_int‖ ≤ 1`, `g ≤ ĝ`
on `W°`).

* `mvfderiv_clm_comp_val_BGR` (chain rule through `val` and a continuous linear map);
* `BoundarySupply.cgpGlobalMap_eq_proj_original_BGR`, `BoundarySupply.mvfderiv_cgpGlobalMap_BGR`;
* `BoundaryGaf02ChainE.mdifferentiableAt_original_BGR`, `mdifferentiableAt_E_BGR`,
  **`zeroBind_hder_of_BGR`** (the `hder` input from any bound of `‖(DE − DF_∂)v‖`; A3c supplies
  one with `H < c₂`);
* **`BoundaryGaf02ChainE.zsp02_transport_BGR`**: BIFACEc's `transport` field of
  `BoundaryActualZeroDomains_BIFc` on the enhanced chain (premise `εr < 1/2` only, as frozen F3);
* consumer `zeroDomains_transport_placement_BGR` (transport ∧ the four placement fields of G14/G15).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}

omit [ConnectedSpace W.Carrier] in
/-- Chain rule through `val` followed by a continuous linear map. -/
theorem mvfderiv_clm_comp_val_BGR {F G : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (L : F →L[ℝ] G) (f : W.Carrier → F)
    (x : W.pieceInterior ⊤) (hf : MDifferentiableAt W.model 𝓘(ℝ, F) f x)
    (u : TangentSpace (𝓡 3) x) :
    mvfderiv (𝓡 3) (fun y : W.pieceInterior ⊤ => L (f y)) x u =
      L (mvfderiv W.model f x (mfderiv (𝓡 3) W.model Subtype.val x u)) := by
  rw [mvfderiv_comp_val_BCG7 W (fun y => L (f y)) x (L.differentiableAt.mdifferentiableAt.comp
    (x := (x : W.Carrier)) hf) u]
  have h := mvfderiv_comp_apply_of_differentiableAt_GAF3 (Ψ := L) hf L.differentiableAt
    (mfderiv (𝓡 3) W.model Subtype.val x u)
  rw [ContinuousLinearMap.fderiv] at h
  exact h

namespace BoundarySupply

variable (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM)

/-- The ported CGP01 global block map of the active family is `pr_int ∘ F_∂ ∘ val`. -/
theorem cgpGlobalMap_eq_proj_original_BGR :
    letI := inducedMetricSpace S.completion.metric
    letI := S.completion.complete
    letI := S.family.instMetricN
    letI := S.family.instChartedN
    letI := S.family.instMetricC
    cgpGlobalMap_BAUGP S.family.toLocalPacketsOnB S.family.zero =
      fun x : W.pieceInterior ⊤ => augIntProjCLM_BAUGC (ι := S.IntTag_BAUGA)
        (κ := Fin S.packet.cusp.count) (S.boundaryOriginalMap x.val) := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  let _ := S.family.instMetricN
  let _ := S.family.instChartedN
  let _ := S.family.instMetricC
  rw [← S.interiorMapOn_eq_cgpGlobalMap_BAUGP]
  funext x
  rw [← S.interiorMapW_val_BAUGA x]
  rfl

/-- The differential of the ported CGP01 global block map: `d𝓔⁰ = pr_int ∘ dF_∂ ∘ dval`. -/
theorem mvfderiv_cgpGlobalMap_BGR (p : W.pieceInterior ⊤) (v : TangentSpace (𝓡 3) p)
    (hFd : MDifferentiableAt W.model
      𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) S.boundaryOriginalMap
        p.val) :
    letI := inducedMetricSpace S.completion.metric
    letI := S.completion.complete
    letI := S.family.instMetricN
    letI := S.family.instChartedN
    letI := S.family.instMetricC
    mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap_BAUGP S.family.toLocalPacketsOnB S.family.zero) p v =
      augIntProjCLM_BAUGC (ι := S.IntTag_BAUGA) (κ := Fin S.packet.cusp.count)
        (mvfderiv W.model S.boundaryOriginalMap p.val (mfderiv (𝓡 3) W.model Subtype.val p v)) := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  let _ := S.family.instMetricN
  let _ := S.family.instChartedN
  let _ := S.family.instMetricC
  exact (congrArg (fun f => mvfderiv 𝓘(ℝ, E3) f p v) S.cgpGlobalMap_eq_proj_original_BGR).trans
    (mvfderiv_clm_comp_val_BGR _ _ p hFd v)

end BoundarySupply

namespace BoundaryGaf02ChainE

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}
  (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

include C in
/-- `F_∂` is differentiable at every point (register block `C.std`). -/
theorem mdifferentiableAt_original_BGR (p : W.Carrier) :
    MDifferentiableAt W.model 𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))
      S.boundaryOriginalMap p := by
  obtain ⟨hΛ, hΔ, hμ, hτ, hΔΛ, hV, hβ1, hb0, he, -⟩ := C.std
  exact (S.boundaryOriginalMap_smooth hΛ hΔ hμ hτ hΔΛ hV hβ1 hb0 he).mdifferentiableAt (by simp)

/-- `C.E` is differentiable at every point (A3a). -/
theorem mdifferentiableAt_E_BGR (p : W.Carrier) :
    MDifferentiableAt W.model 𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))
      C.toChain.E p :=
  (C.stage_smooth_BAUGD 3).mdifferentiableAt (by simp)

/-- The derivative input through `val`, for a given bound `Hd ≥ 0` of `‖(DE − DF_∂)v‖` on `W`. -/
theorem zeroBind_hder_of_BGR {Hd : ℝ} (hHd : 0 ≤ Hd)
    (hder : ∀ (p : W.Carrier) (v : TangentSpace W.model p),
      ‖mvfderiv W.model C.toChain.E p v - mvfderiv W.model S.boundaryOriginalMap p v‖ ≤
        Hd * Real.sqrt (g.inner p v v)) :
    letI := inducedMetricSpace S.completion.metric
    letI := S.completion.complete
    letI := S.family.instMetricN
    letI := S.family.instChartedN
    letI := S.family.instMetricC
    ∀ p (v : TangentSpace 𝓘(ℝ, E3) p),
    ‖mvfderiv 𝓘(ℝ, E3) C.toChain.zeroBindMap_BGR p v -
        mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap_BAUGP S.family.toLocalPacketsOnB S.family.zero) p v‖ ≤
      Hd * Real.sqrt (S.completion.metric.inner p v v) := by
  intro p v
  have hEd : MDifferentiableAt W.model
      𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) C.toChain.E p.val :=
    (C.stage_smooth_BAUGD 3).mdifferentiableAt (by simp)
  have hFd := C.mdifferentiableAt_original_BGR p.val
  have h1 := mvfderiv_clm_comp_val_BGR (augIntProjCLM_BAUGC (ι := S.IntTag_BAUGA)
    (κ := Fin S.packet.cusp.count)) C.toChain.E p hEd v
  have h2 := mvfderiv_clm_comp_val_BGR (augIntProjCLM_BAUGC (ι := S.IntTag_BAUGA)
    (κ := Fin S.packet.cusp.count)) S.boundaryOriginalMap p hFd v
  have e1 : mvfderiv 𝓘(ℝ, E3) C.toChain.zeroBindMap_BGR p v =
      augIntProjCLM_BAUGC (ι := S.IntTag_BAUGA) (κ := Fin S.packet.cusp.count)
        (mvfderiv W.model C.toChain.E p.val (mfderiv (𝓡 3) W.model Subtype.val p v)) := h1
  have e2 := S.mvfderiv_cgpGlobalMap_BGR p v hFd
  have hg : g.inner p.val (mfderiv (𝓡 3) W.model Subtype.val p v)
      (mfderiv (𝓡 3) W.model Subtype.val p v) ≤ S.completion.metric.inner p v v := by
    rw [← pieceInteriorMetric_inner W g ⊤ p v v]
    exact S.completion.inner_le p v
  have key : ‖augIntProjCLM_BAUGC (ι := S.IntTag_BAUGA) (κ := Fin S.packet.cusp.count)
        (mvfderiv W.model C.toChain.E p.val (mfderiv (𝓡 3) W.model Subtype.val p v)) -
      augIntProjCLM_BAUGC (ι := S.IntTag_BAUGA) (κ := Fin S.packet.cusp.count)
        (mvfderiv W.model S.boundaryOriginalMap p.val (mfderiv (𝓡 3) W.model Subtype.val p v))‖ ≤
      Hd * Real.sqrt (S.completion.metric.inner p v v) := by
    rw [← map_sub]
    calc _ ≤ ‖mvfderiv W.model C.toChain.E p.val (mfderiv (𝓡 3) W.model Subtype.val p v) -
          mvfderiv W.model S.boundaryOriginalMap p.val
            (mfderiv (𝓡 3) W.model Subtype.val p v)‖ := norm_augIntProj_le_BAUGC _
      _ ≤ Hd * Real.sqrt (g.inner p.val (mfderiv (𝓡 3) W.model Subtype.val p v)
            (mfderiv (𝓡 3) W.model Subtype.val p v)) := hder p.val _
      _ ≤ Hd * Real.sqrt (S.completion.metric.inner p v v) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hg) hHd
  exact (congrArg₂ (fun a b => ‖a - b‖) e1 e2).trans_le key

/-- **BIFACEc's `transport` field on the enhanced chain** (no derivative hypothesis: A3c): one
ambient diffeomorphism of `W` carries the original model sublevel / level `{radial_k ≤ / = 2/5}`
onto the actual zero domain / face of `C.E`. -/
theorem zsp02_transport_BGR (hεr : εr < 1 / 2) (k : S.ZeroIdx_BAUGC) :
    ∃ Ψ : W.Carrier ≃ₘ⟮W.model, W.model⟯ W.Carrier,
      Ψ '' (Subtype.val '' {q | S.zeroRadial_BIFc k q ≤ 2 / 5}) =
          C.toChain.actualZeroDomain_BIFc k ∧
        Ψ '' (Subtype.val '' {q | S.zeroRadial_BIFc k q = 2 / 5}) =
          C.toChain.actualZeroFace_BIFc k := by
  obtain ⟨hΛ, -, hμ, hτ, hΔΛ, hV, hβ1, hb, -, hΔ, -, -, he, hT, -⟩ := C.std
  obtain ⟨Hd, hHd, hder⟩ := C.stage_derivative_lt_BAUGD 2
  exact C.toChain.zsp02_transport_chain_BGR hΛ hΔ hμ hτ hΔΛ hV hβ1 hb he hT hεr k
    ((max_lt hHd C.toChain.c_two_pos_BCG6K).trans (C.validity.c_two_lt.trans (by norm_num)))
    (C.zeroBind_hder_of_BGR (le_max_right Hd 0) fun p v => (hder p v).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)))

/-- **Consumer**: on the enhanced chain, every actual zero domain of `C.E` is the transport of the
original model sublevel by an ambient diffeomorphism of `W`, lies in its original zero ball, covers
the `.38`-ball in its interior (`e ≤ 1/1000`, N76-6), is compact, and the domains are pairwise
disjoint. -/
theorem zeroDomains_transport_placement_BGR (hεr : εr < 1 / 2) (he : e ≤ 1 / 1000) :
    (∀ k : S.ZeroIdx_BAUGC, ∃ Ψ : W.Carrier ≃ₘ⟮W.model, W.model⟯ W.Carrier,
      Ψ '' (Subtype.val '' {q | S.zeroRadial_BIFc k q ≤ 2 / 5}) =
          C.toChain.actualZeroDomain_BIFc k ∧
        Ψ '' (Subtype.val '' {q | S.zeroRadial_BIFc k q = 2 / 5}) =
          C.toChain.actualZeroFace_BIFc k) ∧
    (∀ k : S.ZeroIdx_BAUGC, C.toChain.actualZeroDomain_BIFc k ⊆
      riemannianBallOf g k.1.val (S.zeroRadius_BAUGC k)) ∧
    (∀ (k : S.ZeroIdx_BAUGC) (q : W.pieceInterior ⊤),
      (letI := inducedMetricSpace S.completion.metric; dist q k.1) <
        38 / 100 * S.zeroRadius_BAUGC k →
      q.val ∈ interior (C.toChain.actualZeroDomain_BIFc k)) ∧
    (∀ k : S.ZeroIdx_BAUGC, IsCompact (C.toChain.actualZeroDomain_BIFc k)) ∧
    Pairwise (Disjoint on C.toChain.actualZeroDomain_BIFc) :=
  ⟨C.zsp02_transport_BGR hεr, C.actualZeroDomain_subset_ball_BGR,
    C.actualZeroDomain_cover_BGR he, C.isCompact_actualZeroDomain_BGR,
    C.actualZeroDomain_pairwise_disjoint_BGR⟩

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
