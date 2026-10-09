import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortSlimClausesB
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortSlimGraphApprox
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortSlimRowsSupply

/-!
# SGP04 on a boundary supply in the interior tag space (lane B-PORT-SLIMb)

The ONE passage from the generic boundary family (`CGPTag_BAUGP S.family.toLocalPacketsOnB S.family.zero`,
`cgpProjMap_BPS … cgpQ3Tags_BPS`) to BAUG-A's interior tags `S.IntTag_BAUGA` and the stage projection
`blockRestrict (S.stageTagsV2_BAUGD 2) ∘ S.interiorMapOn_BAUGA` of the frozen port target (the two tag
types are definitionally equal, `intTag_eq_cgpTag_BAUGP`; the stage tags agree with `Q₃`):

* `blockRestrict_congr_BPS`, `stageTagsV2_two_eq_cgpQ3Tags_BPS`, **`cgpProjMap_Q3_eq_BPS`**
  (`π₃𝓔⁰ = π_{Q₃^∂} ∘ F_int` on `W°`);
* `slimModelOf_BPS S a sgn c zsgn zc : ℝ → H_int` (SGP04's full model `sgpFullGraph_BAUGP` of the slim
  reference `a`), its blocks (`slimModelOf_circle_BPS`, `…_edge_…`, `…_slim_…`, `…_zero_…`, `…_own_…`),
  `slimModelOf_blockRestrict_BPS` ((Q)), `contDiff_slimModelOf_BPS`, `slimModelOf_bounds_BPS` ((M));
* **`slim_row_supply_BPS`**: SGP04 (SG) on every boundary supply in the frozen form (thresholds `θ, Lc, η₀`
  first; value and derivative of `ρ(i)⁻¹π_{Q₃^∂}F_int` against `slimModelOf_BPS` on the threshold-`8` core).
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

/-- `π_s` does not depend on the decidable-equality instance, and only on the set `s`. -/
theorem blockRestrict_congr_BPS {κ : Type*} (i₁ i₂ : DecidableEq κ) {s₁ s₂ : Finset κ}
    (hs : s₁ = s₂) (x : BlockSpace (fun _ : κ => ℝ²)) :
    (letI := i₁; blockRestrict s₁ x) = (letI := i₂; blockRestrict s₂ x) := by
  subst hs
  rw [Subsingleton.elim i₁ i₂]

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}

namespace BoundarySupply

variable (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
  θ W g δn n B oM)

/-- The stage-`2` tags of the slot are the tags of `Q₃`. -/
theorem stageTagsV2_two_eq_cgpQ3Tags_BPS :
    letI := inducedMetricSpace S.completion.metric
    letI := S.completion.complete
    letI := S.family.instMetricN
    letI := S.family.instChartedN
    letI := S.family.instMetricC
    cgpQ3Tags_BPS S.family.toLocalPacketsOnB S.family.zero = S.stageTagsV2_BAUGD 2 := by
  ext t
  rw [BoundarySupplyCore.mem_stageTagsV2_two_BAUGD]
  simp only [cgpQ3Tags_BPS, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases t with j | j | j | k | bb <;> rfl

/-- **`π₃𝓔⁰ = π_{Q₃^∂} ∘ F_int` on `W°`** (the ported global map of the stored family is BAUG-A's
interior formula; the `Q₃` tags are the stage-`2` tags). -/
theorem cgpProjMap_Q3_eq_BPS (x : W.pieceInterior ⊤) :
    letI := inducedMetricSpace S.completion.metric
    letI := S.completion.complete
    letI := S.family.instMetricN
    letI := S.family.instChartedN
    letI := S.family.instMetricC
    cgpProjMap_BPS S.family.toLocalPacketsOnB S.family.zero
      (cgpQ3Tags_BPS S.family.toLocalPacketsOnB S.family.zero) x =
      (blockRestrict (S.stageTagsV2_BAUGD 2) (S.interiorMapOn_BAUGA x) :
        BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²)) := by
  unfold cgpProjMap_BPS
  rw [← S.interiorMapOn_eq_cgpGlobalMap_BAUGP]
  exact blockRestrict_congr_BPS _ _ (S.stageTagsV2_two_eq_cgpQ3Tags_BPS) _

/-- SGP04's full model of the slim reference `a`, as a map into the interior block space. -/
def slimModelOf_BPS (a : S.SlimIdx_BAUGD) (sgn c zsgn zc : W.pieceInterior ⊤ → ℝ) :
    ℝ → BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²) :=
  letI := inducedMetricSpace S.completion.metric
  letI := S.completion.complete
  letI := S.family.instMetricN
  letI := S.family.instChartedN
  letI := S.family.instMetricC
  sgpFullGraph_BAUGP S.family.toLocalPacketsOnB S.family.zero a sgn c zsgn zc

variable (a : S.SlimIdx_BAUGD) (sgn c zsgn zc : W.pieceInterior ⊤ → ℝ)

theorem slimModelOf_circle_BPS (j : S.CircleIdx_BAUGD) (u : ℝ) :
    S.slimModelOf_BPS a sgn c zsgn zc u (.inl j) = 0 :=
  rfl

theorem slimModelOf_edge_BPS (j : S.EdgeIdx_BAUGD) (u : ℝ) :
    S.slimModelOf_BPS a sgn c zsgn zc u (.inr (.inr (.inl j))) = 0 :=
  rfl

theorem slimModelOf_slim_BPS (j : S.SlimIdx_BAUGD) (u : ℝ) :
    S.slimModelOf_BPS a sgn c zsgn zc u (.inr (.inl j)) =
      (letI := inducedMetricSpace S.completion.metric
       letI := S.completion.complete
       sgpSlimModelBlock_BAUGP S.family.toLocalPacketsOnB a sgn c j u) :=
  rfl

theorem slimModelOf_zero_BPS (k : S.ZeroIdx_BAUGC) (u : ℝ) :
    S.slimModelOf_BPS a sgn c zsgn zc u (S.zeroTag_BAUGC k) =
      (letI := inducedMetricSpace S.completion.metric
       letI := S.completion.complete
       letI := S.family.instMetricN
       letI := S.family.instChartedN
       letI := S.family.instMetricC
       sgpZeroModelBlock_BAUGP S.family.toLocalPacketsOnB S.family.zero a zsgn zc k u) :=
  rfl

/-- The own block of the model is `(η, 1)`. -/
theorem slimModelOf_own_BPS (u : ℝ) :
    S.slimModelOf_BPS a sgn c zsgn zc u (.inr (.inl a)) = WithLp.toLp 2 (planeAxis u, 1) := by
  rw [slimModelOf_slim_BPS]
  simp [sgpSlimModelBlock_BAUGP]

/-- **(Q)** The model is `Q₃^∂`-valued. -/
theorem slimModelOf_blockRestrict_BPS (u : ℝ) :
    blockRestrict (S.stageTagsV2_BAUGD 2) (S.slimModelOf_BPS a sgn c zsgn zc u) =
      S.slimModelOf_BPS a sgn c zsgn zc u := by
  refine PiLp.ext fun t => ?_
  rw [blockRestrict_apply]
  split_ifs with ht
  · rfl
  · rcases t with j | j | j | k | bb
    · exact (S.slimModelOf_circle_BPS a sgn c zsgn zc j u).symm
    · exact (ht (S.slimTag_mem_stageTagsV2_BAUGD 2 j)).elim
    · exact (S.slimModelOf_edge_BPS a sgn c zsgn zc j u).symm
    · exact (ht (BoundarySupplyCore.mem_stageTagsV2_two_BAUGD.mpr rfl)).elim
    · rfl

/-- The model is smooth. -/
theorem contDiff_slimModelOf_BPS : ContDiff ℝ ∞ (S.slimModelOf_BPS a sgn c zsgn zc) :=
  letI := inducedMetricSpace S.completion.metric
  letI := S.completion.complete
  letI := S.family.instMetricN
  letI := S.family.instChartedN
  letI := S.family.instMetricC
  contDiff_sgpFullGraph_BAUGP S.family.toLocalPacketsOnB S.family.zero a sgn c zsgn zc

/-- **(M)** SGP04's global `C²` modulus for the model of a slim centre of a supply (signs of size at
most one; SGP01's zero clauses: at most one meeting zero support, zero scale ratio `≥ T/20 ≥ 1`). -/
theorem slimModelOf_bounds_BPS (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ) (hLΛ : 1000000 * Δ * Λ < 1 / 100000)
    (he : e < 1 / 40) (hT : 1600 * (1000000 * Δ) ≤ T) (hσs : 0 ≤ σs) (hσs1 : σs ≤ 1 / 100)
    (hsgn : ∀ j, |sgn j| ≤ 1) (hzsgn : ∀ k, |zsgn k| ≤ 1) (u : ℝ) :
    ‖fderiv ℝ (S.slimModelOf_BPS a sgn c zsgn zc) u‖ ≤ sgpGraphBound ∧
      ‖fderiv ℝ (fderiv ℝ (S.slimModelOf_BPS a sgn c zsgn zc)) u‖ ≤ sgpGraphBound :=
  letI := inducedMetricSpace S.completion.metric
  letI := S.completion.complete
  letI := S.family.instMetricN
  letI := S.family.instChartedN
  letI := S.family.instMetricC
  have hs01 := sgp01_row_BAUGP S.family.toLocalPacketsOnBFR.toLocalPacketsOnBF hΛ hΔ hLΛ he hT hσs
    hσs1 ((Set.Finite.mem_toFinset _).mp a.2)
  have h := sgp04_full_model_bounds_BAUGP S.family.toLocalPacketsOnB S.family.zero hΔ hΛ hLΛ a sgn
    c zsgn zc hsgn hzsgn
    (fun k hk hmt => (one_le_div_twenty_SGP4 hΔ hT).trans (hs01.2.2.2.2.1 k hk hmt).1)
    (fun k₁ hk₁ k₂ hk₂ h₁ h₂ => hs01.2.2.2.1 k₁ hk₁ k₂ hk₂ h₁ h₂) u
  ⟨h.1, h.2.1⟩

end BoundarySupply

/-- **SGP04 (SG) on every boundary supply, in the frozen form** (consumer of `sgp04_row_BAUGP`): for
`Δ ≥ 1`, `β₂ ∈ (0, 1)` and `0 < e < 1/100` there are `θ ∈ (0, 1)` and thresholds `Lc, η₀` such that on
every supply with SGP03's hypotheses at `θ` and every slim centre `i` there are signs and translations
with `|sgn|, |zsgn| ≤ 1` and the value / derivative comparison of `ρ(i)⁻¹π_{Q₃^∂}F_int` with
`slimModelOf_BPS` on the threshold-`8` core of `i`. -/
theorem slim_row_supply_BPS {Δ β₂ eg : ℝ} (hΔ : 1 ≤ Δ) (hβ₂ : 0 < β₂) (hβ₂1 : β₂ < 1)
    (heg : 0 < eg) (heg1 : eg < 1 / 100) :
    ∃ θs : ℝ, 0 < θs ∧ θs < 1 ∧ ∃ Lc η₀ : ℝ, 0 < Lc ∧ 0 < η₀ ∧
      ∀ {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
        {βd εN Λ w σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
        {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier]
        {g : SmoothRiemannianMetric W.model W.Carrier} {δn : ℝ} {n : ℕ}
        {B : NearlyCuspidalBoundary W g K δn}
        {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}
        (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
          θ W g δn n B oM),
        β 2 = β₂ → β 1 ≤ η₀ → Lc ≤ Lmax → 0 ≤ Λ → 1000000 * Δ * Λ < 1 / 100000 →
        e < 1 / 40 → 1600 * (1000000 * Δ) ≤ T → 20 * Λz ≤ T →
        0 < σs → σs < θs ^ 2 / 10 ^ 6 → vs < θs / 100 →
        0 < ζ → ζ < θs ^ 2 / 10 ^ 6 → ζ < 1 / (100 * (1000000 * Δ)) →
        εr < θs / (100 * (1000000 * Δ)) →
        ∀ i : S.SlimIdx_BAUGD, ∃ sgn c zsgn zc : W.pieceInterior ⊤ → ℝ,
          (∀ j, |sgn j| ≤ 1) ∧ (∀ k, |zsgn k| ≤ 1) ∧
          ∀ x : W.pieceInterior ⊤,
            (letI := inducedMetricSpace S.completion.metric
             dist x i.1 < 1000000 * Δ * S.rho i.1) →
            |S.slimEta_BIF i.1 x| ≤ 8 * (100000 * Δ) →
            ‖(S.rho i.1)⁻¹ • blockRestrict (S.stageTagsV2_BAUGD 2) (S.interiorMapOn_BAUGA x) -
              S.slimModelOf_BPS i sgn c zsgn zc (S.slimEta_BIF i.1 x)‖ < eg ∧
            ∀ w : TangentSpace 𝓘(ℝ, E3) x,
              ‖(S.rho i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3)
                  (fun y => blockRestrict (S.stageTagsV2_BAUGD 2) (S.interiorMapOn_BAUGA y)) x w -
                fderiv ℝ (S.slimModelOf_BPS i sgn c zsgn zc) (S.slimEta_BIF i.1 x)
                  (mvfderiv 𝓘(ℝ, E3) (S.slimEta_BIF i.1) x w)‖ ≤
                eg * Real.sqrt ((S.rho i.1)⁻¹ ^ 2 * S.completion.metric.inner x w w) := by
  obtain ⟨θs, hθ, hθ1, Lc, η₀, hLc, hη₀, hrow⟩ := sgp04_row_BAUGP hΔ hβ₂ hβ₂1 heg heg1
  refine ⟨θs, hθ, hθ1, Lc, η₀, hLc, hη₀, ?_⟩
  intro K A β βd εN Λ w σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ W _ g δn n B oM S
    hβ2 hβ1 hLmax hΛ hLΛ he hT hΛzT hσs hσθ hvθ hζ hζθ hζL hεr i
  have hi := (Set.Finite.mem_toFinset _).mp i.2
  have h := @hrow (W.pieceInterior ⊤) (inducedMetricSpace S.completion.metric) _ _
    S.completion.complete _ S.completion.metric (inducedMetricSpace_hmetric S.completion.metric)
      (fun x => S.rho x) (fun x => S.rho_pos x) Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
      vs ζ Λz _ _ _ _ (letI := inducedMetricSpace S.completion.metric
        letI := S.completion.complete
        S.family.toLocalPacketsOnBFR.toLocalPacketsOnBF) hβ2 hβ1 hLmax hΛ hLΛ he hT
      hΛzT hσs hσθ hvθ hζ hζθ hζL hεr i
  refine h.elim fun sgn h1 => h1.elim fun c h2 => h2.elim fun zsgn h3 => h3.elim fun zc h4 =>
    ⟨sgn, c, zsgn, zc, h4.1, h4.2.1, fun x hx hη => ?_⟩
  have hx' : x ∈ (letI := inducedMetricSpace S.completion.metric
      ball i.1 (10 ^ 6 * Δ * S.rho i.1)) := by
    have h10 : (10 : ℝ) ^ 6 * Δ * S.rho i.1 = 1000000 * Δ * S.rho i.1 := by norm_num
    refine (?_ : (letI := inducedMetricSpace S.completion.metric; dist x i.1) <
      10 ^ 6 * Δ * S.rho i.1)
    rw [h10]
    exact hx
  have hη' : |(letI := inducedMetricSpace S.completion.metric
      letI := S.completion.complete
      (S.family.slim.centre i.1 hi).coord_BCG2 x)| ≤ 8 * 10 ^ 5 * Δ := by
    rw [← S.slimEta_eq_coord_BAUGP2 i x]
    linarith only [hη]
  have h5 := h4.2.2 x hx' hη'
  have hfun := funext S.cgpProjMap_Q3_eq_BPS
  refine ⟨?_, fun w => ?_⟩
  · have hv := h5.1
    rw [S.cgpProjMap_Q3_eq_BPS x] at hv
    rw [S.slimEta_BIF_of_mem_BPS hi]
    exact hv
  · have hd := h5.2 w
    simp only [hfun, ← S.slimEta_BIF_of_mem_BPS hi] at hd
    exact hd

end DifferentialGeometry.Geometry.Collapse
