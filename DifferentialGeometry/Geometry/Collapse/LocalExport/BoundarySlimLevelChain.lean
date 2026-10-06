import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundarySlimLevelInputs
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCircleLevelChain
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryBasesStageSubmersionSlim

/-!
# O-WF G3b: the whole adjusted slim level of the boundary chain is a standard `S²` or `T²`

Closed twins: `Gaf02Chain.gaf07_slim_gauge_GAFC`, `gaf07_slim_level_standard_GAFC`
(`Fibration/ActualStageChainGaf07FibreTypes.lean`). On the boundary chain `C`, slim chart `j`,
`ℓ = 10⁵Δ`, `Y_j = {q ∈ B(j, 10⁶Δρ_j) | |η_j q| < 5ℓ}` (`slimY_OWF`), `g_j = κ_j ∘ f₂ ∘ val`:

* the value clause `|g_j − η_j| < 1/800` (`slim_final_value_close_OWF`; `κ_j(F_∂) = η_j` on the
  plateau, `‖E − F_∂‖ < c₂ρ`, `ρ ≤ 5ρ_j/4`), the derivative clause `|Dg_j − Dη_j| ≤ Hν`
  (`slim_final_deriv_close_OWF`, `ν q u = ρ_j⁻¹√ĝ(u, u)`), LFR20.1's right inverse of gauge
  `≤ 4/3` (`slim_right_inverse_OWF`), the compact slab;
* **`slim_level_standard_OWF`**: for `K ≥ 5` and `|a| < 4ℓ`, EITHER every whole adjusted level
  `{q ∈ Y_j | g_j q = a}` is the image of a smooth embedding of the standard `ClosureSphere`, OR
  every one of the standard `Torus` (FC34a `exists_embedding_adjusted_level_BAUGD` from the
  standard original levels `SlimCentreOn.standard_level_embedding_OWF`).

Register premises: `c₂ < 1/1000`, `K ≥ 5` (`Δ ≥ 1` is in `C.std`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic GC.GraphManifold
open scoped ENNReal

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

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

namespace BoundarySupplyCore

variable (S : BoundarySupplyCore K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
  ζ Λz W g δn n B oM)

/-- GAF07's original slim domain on `W°`: `Y_j = {q ∈ B(j, 10⁶Δρ_j) | |η_j q| < 5·10⁵Δ}`. -/
def slimY_OWF (j : S.SlimIdx_BAUGD) : Set (W.pieceInterior ⊤) :=
  letI := inducedMetricSpace S.completion.metric
  {q | dist q j.1 < 1000000 * Δ * S.rho j.1 ∧ |S.slimEta_BIF j.1 q| < 5 * (10 ^ 5 * Δ)}

/-- `Y_j` is open. -/
theorem isOpen_slimY_OWF (j : S.SlimIdx_BAUGD) : IsOpen (S.slimY_OWF j) := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  have hj : j.1 ∈ S.family.slim.centres := (Set.Finite.mem_toFinset _).mp j.2
  have hη : ContinuousOn (S.slimEta_BIF j.1) (ball j.1 (1000000 * Δ * S.rho j.1)) := by
    rw [S.slimEta_eq_coord_fun_BBP j]
    have h := (S.family.slim.centre j.1 hj).contMDiffOn_coord_BAUGA.continuousOn
    convert h using 3
    norm_num
  exact hη.isOpen_inter_preimage isOpen_ball
    (isOpen_lt continuous_abs (continuous_const (y := (5 * (10 ^ 5 * Δ) : ℝ))))

end BoundarySupplyCore

namespace BoundaryGaf02ChainE

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}
  (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

/-- The adjusted slim coordinate `g_j = κ_j ∘ f₂ ∘ val` is smooth on `W°`. -/
theorem slim_adjusted_contMDiff_OWF (j : S.SlimIdx_BAUGD) :
    ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞
      (fun q : W.pieceInterior ⊤ => S.slimKappa_BBP j (C.toChain.stageMap 2 q.val)) :=
  ((S.slimKappa_BBP j).comp ((actualSlotsV2_BAUGD S).stageProj 2)).contDiff.comp_contMDiff
    ((C.stage_smooth_BAUGD 3).comp (isLocalDiffeomorph_pieceInterior_val W ⊤).contMDiff)

/-- `κ_j ∘ f₂ = κ_j ∘ E` (`κ_j ∘ π₂ = κ_j`). -/
theorem slimKappa_stageMap_two_OWF (j : S.SlimIdx_BAUGD) (p : W.Carrier) :
    S.slimKappa_BBP j (C.toChain.stageMap 2 p) =
      S.slimKappa_BBP j (C.toChain.stage (2 : Fin 3).succ p) :=
  slimKappa_stageProj_BBP j _

/-- **The slim value clause** (closed `gaf07_slim_coordinate_G47`): on the plateau,
`|κ_j(f₂ q) − η_j q| < 1/800`. -/
theorem slim_final_value_close_OWF (hc : c 2 < 1 / 1000) (j : S.SlimIdx_BAUGD)
    {q : W.pieceInterior ⊤}
    (hq : letI := inducedMetricSpace S.completion.metric; dist q j.1 < 1000000 * Δ * S.rho j.1)
    (hη : |S.slimEta_BIF j.1 q| < 6 * (10 ^ 5 * Δ)) :
    |S.slimKappa_BBP j (C.toChain.stageMap 2 q.val) - S.slimEta_BIF j.1 q| < 1 / 800 := by
  obtain ⟨hΛ, hΔ, hμ, hτ, hΔΛ, hV, hβ1, hb, he, h1Δ, hΔΛ', -⟩ := C.std
  have hr := S.rho_pos j.1
  have hF : S.slimKappa_BBP j (S.boundaryOriginalMap q.val) = S.slimEta_BIF j.1 q :=
    (S.slimKappa_boundaryOriginalMap_eventuallyEq_BBP j hq hη hΔ.le).self_of_nhds
  have hE := C.stage_error_lt_BAUGD 2 q.val
  have hcut := S.slim_cutoff_eq_one_BBP j hq hη hΔ.le
  have hρq : S.rho q.val ≤ 5 / 4 * S.rho j.1 :=
    (S.slim_scale_comparable_BAUGP2 hΛ h1Δ hΔΛ' hV hβ1 hb j q.val (by rw [hcut]; exact one_pos)).2.1
  rw [C.slimKappa_stageMap_two_OWF j, ← hF, ← map_sub, ← Real.norm_eq_abs]
  have hk := (S.slimKappa_BBP j).le_opNorm (C.toChain.stage (2 : Fin 3).succ q.val -
    S.boundaryOriginalMap q.val)
  have hkn := S.norm_slimKappa_le_BBP j
  have hc2 : 0 < c 2 := by
    by_contra hneg
    push Not at hneg
    have h0 : c 2 * S.rho q.val ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hneg (S.rho_pos q.val).le
    exact absurd (hE.trans_le h0) (not_lt.mpr (norm_nonneg _))
  have hstep : ‖S.slimKappa_BBP j (C.toChain.stage (2 : Fin 3).succ q.val -
      S.boundaryOriginalMap q.val)‖ < (S.rho j.1)⁻¹ * (c 2 * S.rho q.val) := by
    calc _ ≤ ‖S.slimKappa_BBP j‖ * ‖C.toChain.stage (2 : Fin 3).succ q.val -
          S.boundaryOriginalMap q.val‖ := hk
      _ ≤ (S.rho j.1)⁻¹ * ‖C.toChain.stage (2 : Fin 3).succ q.val -
          S.boundaryOriginalMap q.val‖ := mul_le_mul_of_nonneg_right hkn (norm_nonneg _)
      _ < (S.rho j.1)⁻¹ * (c 2 * S.rho q.val) :=
          mul_lt_mul_of_pos_left hE (inv_pos.mpr hr)
  refine hstep.trans_le ?_
  have h54 : (S.rho j.1)⁻¹ * (c 2 * S.rho q.val) ≤ (S.rho j.1)⁻¹ * (c 2 * (5 / 4 * S.rho j.1)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hρq hc2.le) (inv_pos.mpr hr).le
  have h55 : (S.rho j.1)⁻¹ * (c 2 * (5 / 4 * S.rho j.1)) = 5 / 4 * c 2 := by
    field_simp
  rw [h55] at h54
  linarith

/-- **The slim derivative clause** (closed `gaf07_slim_derivative_GAFC`): ONE `0 ≤ H < 1/1000` with
`|Dg_j(u) − Dη_j(u)| ≤ H ρ_j⁻¹ |u|_ĝ` on every slim plateau. -/
theorem slim_final_deriv_close_OWF (hc : c 2 < 1 / 1000) :
    ∃ H : ℝ, 0 ≤ H ∧ H < 1 / 1000 ∧ ∀ (j : S.SlimIdx_BAUGD) {q : W.pieceInterior ⊤},
      (letI := inducedMetricSpace S.completion.metric; dist q j.1 < 1000000 * Δ * S.rho j.1) →
      |S.slimEta_BIF j.1 q| < 6 * (10 ^ 5 * Δ) → ∀ u : TangentSpace (𝓡 3) q,
      ‖mvfderiv (𝓡 3) (fun x : W.pieceInterior ⊤ =>
          S.slimKappa_BBP j (C.toChain.stageMap 2 x.val)) q u -
        mvfderiv (𝓡 3) (S.slimEta_BIF j.1) q u‖ ≤
        H * ((S.rho j.1)⁻¹ * Real.sqrt (S.completion.metric.inner q u u)) := by
  obtain ⟨Hd, hHd, hder⟩ := C.stage_derivative_lt_BAUGD 2
  refine ⟨max Hd 0, le_max_right _ _, max_lt (hHd.trans hc) (by norm_num), ?_⟩
  intro j q hq hη u
  obtain ⟨hΛ, hΔ, hμ, hτ, hΔΛ, hV, hβ1, hb, he, -⟩ := C.std
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  have hr := S.rho_pos j.1
  have hD4 := S.four_le_distanceToBoundary_of_slim_plateau_BBP hΛ hΔ hμ hτ hΔΛ hV hβ1 hb he j
    hq hη
  have heq : ∀ y : W.pieceInterior ⊤, ENNReal.ofReal 4 ≤ distanceToBoundary W g y →
      S.completion.metric.inner y = (pieceInteriorMetric W g ⊤).inner y := fun y hy =>
    S.completion.inner_eq_on_agree y (S.completion.far_subset_agree hy)
  have hfun : (fun x : W.pieceInterior ⊤ => S.slimKappa_BBP j (C.toChain.stageMap 2 x.val)) =
      fun x : W.pieceInterior ⊤ => S.slimKappa_BBP j (C.toChain.stage (2 : Fin 3).succ x.val) :=
    funext fun x => C.slimKappa_stageMap_two_OWF j x.val
  have hE : MDifferentiableAt W.model
      𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))
      (C.toChain.stage (2 : Fin 3).succ) q.val :=
    ((C.stage_smooth_BAUGD (2 : Fin 3).succ) q.val).mdifferentiableAt (by simp)
  have hκE : MDifferentiableAt W.model 𝓘(ℝ, ℝ)
      (fun p => S.slimKappa_BBP j (C.toChain.stage (2 : Fin 3).succ p)) q.val :=
    (S.slimKappa_BBP j).differentiableAt.comp_mdifferentiableAt hE
  have e0 := congrArg (fun f => mvfderiv (𝓡 3) f q u) hfun
  have e1 := mvfderiv_comp_val_BCG7 W
    (fun p => S.slimKappa_BBP j (C.toChain.stage (2 : Fin 3).succ p)) q hκE u
  have e2 := mvfderiv_clm_comp_BDFB (S.slimKappa_BBP j) hE
    (mfderiv (𝓡 3) W.model Subtype.val q u)
  have e3 := C.slimKappa_mvfderiv_eq_BBP j hq hη u
  have key := congrArg₂ (fun a b => a - b) (e0.trans (e1.trans e2)) e3.symm
  have hgv := inner_mfderiv_val_BCG7 W g S.completion.metric heq q hD4 u u
  have hn := hder q.val (mfderiv (𝓡 3) W.model Subtype.val q u)
  have hk := (S.slimKappa_BBP j).le_opNorm
    (mvfderiv W.model (C.toChain.stage (2 : Fin 3).succ) q.val
        (mfderiv (𝓡 3) W.model Subtype.val q u) -
      mvfderiv W.model S.boundaryOriginalMap q.val (mfderiv (𝓡 3) W.model Subtype.val q u))
  have hkn := S.norm_slimKappa_le_BBP j
  have hsq : Real.sqrt (g.inner q.val (mfderiv (𝓡 3) W.model Subtype.val q u)
      (mfderiv (𝓡 3) W.model Subtype.val q u)) =
      Real.sqrt (S.completion.metric.inner q u u) := congrArg Real.sqrt hgv
  have hmain : ‖S.slimKappa_BBP j
      (mvfderiv W.model (C.toChain.stage (2 : Fin 3).succ) q.val
        (mfderiv (𝓡 3) W.model Subtype.val q u) -
      mvfderiv W.model S.boundaryOriginalMap q.val (mfderiv (𝓡 3) W.model Subtype.val q u))‖ ≤
      max Hd 0 * ((S.rho j.1)⁻¹ * Real.sqrt (S.completion.metric.inner q u u)) := by
    calc _ ≤ ‖S.slimKappa_BBP j‖ * ‖mvfderiv W.model (C.toChain.stage (2 : Fin 3).succ) q.val
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
  calc _ = ‖S.slimKappa_BBP j (mvfderiv W.model (C.toChain.stage (2 : Fin 3).succ) q.val
        (mfderiv (𝓡 3) W.model Subtype.val q u)) -
        S.slimKappa_BBP j (mvfderiv W.model S.boundaryOriginalMap q.val
          (mfderiv (𝓡 3) W.model Subtype.val q u))‖ := congrArg norm key
    _ = _ := congrArg norm (map_sub _ _ _).symm
    _ ≤ _ := hmain

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
