import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCircleLevelValues
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryChainEDerivative

/-!
# G17 circle level (b): the derivative clause `‖Dg_j − Dη_j‖ ≤ H ρ_j⁻¹ |u|` on the plateau
(S-BAUG-D2)

Closed twin `Gaf02Chain.gaf07_circle_derivative_GAFC`. On the circle chart `j`'s original
threshold-`6` plateau, with `g_j = κ_j ∘ f₀ ∘ val` (`f₀ = π₀ ∘ E = E`): for every tangent vector
`u` of `W°`, `‖Dg_j(u) − Dη_j(u)‖ ≤ H ρ_j⁻¹ |u|_ĝ` with ONE `H < c₂` (A3c
`stage_derivative_lt_BAUGD 2`): `Dη_j(u) = κ_j(DF_∂ (dι u))`
(`circleKappa_mvfderiv_eq_BBP`), `Dg_j(u) = κ_j(DE (dι u))`, `‖κ_j‖ ≤ ρ_j⁻¹`, and `g = ĝ` along
`dι` on `{D ≥ 4}` (`inner_mfderiv_val_BCG7`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open scoped ENNReal

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

namespace BoundaryGaf02ChainE

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}
  (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

include C in
/-- **GAF07's derivative clause on the boundary chain** (closed `gaf07_circle_derivative_GAFC`):
with `c₂ < 1/1000`, ONE `0 ≤ H < 1/1000` (`H = max Hd 0`, `Hd < c₂` from A3c) with
`‖Dg_j(u) − Dη_j(u)‖ ≤ H ρ_j⁻¹ |u|_ĝ` on every circle plateau. -/
theorem circle_final_deriv_close_BAUGD (hc : c 2 < 1 / 1000) :
    ∃ H : ℝ, 0 ≤ H ∧ H < 1 / 1000 ∧ ∀ (j : S.CircleIdx_BAUGD) {q : W.pieceInterior ⊤},
      (letI := inducedMetricSpace S.completion.metric; dist q j.1 < 200 * S.rho j.1) →
      ‖S.circleEta_BIF j.1 q‖ < 6 → ∀ u : TangentSpace (𝓡 3) q,
      ‖mvfderiv (𝓡 3) (fun x : W.pieceInterior ⊤ =>
          S.circleKappa_BBP j (C.toChain.stageMap 0 x.val)) q u -
        mvfderiv (𝓡 3) (S.circleEta_BIF j.1) q u‖ ≤
        H * ((S.rho j.1)⁻¹ * Real.sqrt (S.completion.metric.inner q u u)) := by
  obtain ⟨Hd, hHd, hder⟩ := C.stage_derivative_lt_BAUGD 2
  refine ⟨max Hd 0, le_max_right _ _, max_lt (hHd.trans hc) (by norm_num), ?_⟩
  intro j q hq hη u
  obtain ⟨hΛ, hΔ, hμ, hτ, hΔΛ, hV, hβ1, hb, he, -⟩ := C.std
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  have hr := S.rho_pos j.1
  have hD4 := S.four_le_distanceToBoundary_of_circle_plateau_BBP hΛ hΔ hμ hτ hΔΛ hV hβ1 hb he j
    hq hη
  have heq : ∀ y : W.pieceInterior ⊤, ENNReal.ofReal 4 ≤ distanceToBoundary W g y →
      S.completion.metric.inner y = (pieceInteriorMetric W g ⊤).inner y := fun y hy =>
    S.completion.inner_eq_on_agree y (S.completion.far_subset_agree hy)
  have hf : ∀ p, C.toChain.stageMap 0 p = C.toChain.stage (2 : Fin 3).succ p :=
    fun p => stageProj_zero_V2_BAUGD S _
  have hfun : (fun x : W.pieceInterior ⊤ => S.circleKappa_BBP j (C.toChain.stageMap 0 x.val)) =
      fun x : W.pieceInterior ⊤ => S.circleKappa_BBP j (C.toChain.stage (2 : Fin 3).succ x.val) :=
    funext fun x => by rw [hf]
  have hE : MDifferentiableAt W.model
      𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))
      (C.toChain.stage (2 : Fin 3).succ) q.val :=
    ((C.stage_smooth_BAUGD (2 : Fin 3).succ) q.val).mdifferentiableAt (by simp)
  have hκE : MDifferentiableAt W.model 𝓘(ℝ, ℝ²)
      (fun p => S.circleKappa_BBP j (C.toChain.stage (2 : Fin 3).succ p)) q.val :=
    (S.circleKappa_BBP j).differentiableAt.comp_mdifferentiableAt hE
  have e0 := congrArg (fun f => mvfderiv (𝓡 3) f q u) hfun
  have e1 := mvfderiv_comp_val_BCG7 W
    (fun p => S.circleKappa_BBP j (C.toChain.stage (2 : Fin 3).succ p)) q hκE u
  have e2 := mvfderiv_clm_comp_BDFB (S.circleKappa_BBP j) hE
    (mfderiv (𝓡 3) W.model Subtype.val q u)
  have e3 := C.circleKappa_mvfderiv_eq_BBP j hq hη u
  have e4 := congrArg (fun f => mvfderiv (𝓡 3) f q u) (S.circleEta_eq_cgpCircleCoord_BBP j)
  have hη' := e4.trans e3.symm
  have key := congrArg₂ (fun a b => a - b) (e0.trans (e1.trans e2)) hη'
  have hgv := inner_mfderiv_val_BCG7 W g S.completion.metric heq q hD4 u u
  have hn := hder q.val (mfderiv (𝓡 3) W.model Subtype.val q u)
  have hk := (S.circleKappa_BBP j).le_opNorm
    (mvfderiv W.model (C.toChain.stage (2 : Fin 3).succ) q.val
        (mfderiv (𝓡 3) W.model Subtype.val q u) -
      mvfderiv W.model S.boundaryOriginalMap q.val (mfderiv (𝓡 3) W.model Subtype.val q u))
  have hkn := S.norm_circleKappa_le_BBP j
  have hsq : Real.sqrt (g.inner q.val (mfderiv (𝓡 3) W.model Subtype.val q u)
      (mfderiv (𝓡 3) W.model Subtype.val q u)) =
      Real.sqrt (S.completion.metric.inner q u u) := congrArg Real.sqrt hgv
  have hmain : ‖S.circleKappa_BBP j
      (mvfderiv W.model (C.toChain.stage (2 : Fin 3).succ) q.val
        (mfderiv (𝓡 3) W.model Subtype.val q u) -
      mvfderiv W.model S.boundaryOriginalMap q.val (mfderiv (𝓡 3) W.model Subtype.val q u))‖ ≤
      max Hd 0 * ((S.rho j.1)⁻¹ * Real.sqrt (S.completion.metric.inner q u u)) := by
    calc _ ≤ ‖S.circleKappa_BBP j‖ * ‖mvfderiv W.model (C.toChain.stage (2 : Fin 3).succ) q.val
            (mfderiv (𝓡 3) W.model Subtype.val q u) -
          mvfderiv W.model S.boundaryOriginalMap q.val
            (mfderiv (𝓡 3) W.model Subtype.val q u)‖ := hk
      _ ≤ (S.rho j.1)⁻¹ * (Hd * Real.sqrt (g.inner q.val (mfderiv (𝓡 3) W.model Subtype.val q u)
            (mfderiv (𝓡 3) W.model Subtype.val q u))) :=
          mul_le_mul hkn hn (norm_nonneg _) (inv_pos.mpr hr).le
      _ ≤ (S.rho j.1)⁻¹ * (max Hd 0 * Real.sqrt (S.completion.metric.inner q u u)) := by
          rw [hsq]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_max_left _ _)
            (Real.sqrt_nonneg _)) (inv_pos.mpr hr).le
      _ = max Hd 0 * ((S.rho j.1)⁻¹ * Real.sqrt (S.completion.metric.inner q u u)) := by ring
  calc _ = ‖S.circleKappa_BBP j (mvfderiv W.model (C.toChain.stage (2 : Fin 3).succ) q.val
        (mfderiv (𝓡 3) W.model Subtype.val q u)) -
        S.circleKappa_BBP j (mvfderiv W.model S.boundaryOriginalMap q.val
          (mfderiv (𝓡 3) W.model Subtype.val q u))‖ := congrArg norm key
    _ = _ := congrArg norm (map_sub _ _ _).symm
    _ ≤ _ := hmain

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
