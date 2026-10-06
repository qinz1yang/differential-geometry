import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortEdgeClauses
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortEdgeGraphSupply

/-!
# EGP06 on a boundary supply in the interior tag space (lane S-PORT-EDGE)

The ONE passage from the generic boundary family (`CGPTag_BAUGP S.family.toLocalPacketsOnB
S.family.zero`, `cgpProjMap_BPS … cgpQ2Tags_BPE`) to BAUG-A's interior tags `S.IntTag_BAUGA` and the
stage projection `blockRestrict (S.stageTagsV2_BAUGD 1) ∘ S.interiorMapOn_BAUGA` of the frozen edge
port target (the two tag types are definitionally equal, `intTag_eq_cgpTag_BAUGP`; the stage-`1`
tags agree with `Q₂`). Twin of lane B-PORT-SLIMb's `BoundaryPortSlimTransport`:

* `blockRestrict_congr_BPE`, `stageTagsV2_one_eq_cgpQ2Tags_BPE`, **`cgpProjMap_Q2_eq_BPE`**
  (`π₂𝓔⁰ = π_{Q₂^∂} ∘ F_int` on `W°`);
* `edgeModelOf_BPE S a sgn c : ℝ → H_int` (EGP06's model `egpModelGraph_BAUGP` of the `edgeB`
  reference `a`), its blocks (`edgeModelOf_circle_BPE`, `…_own_BPE`),
  `edgeModelOf_blockRestrict_BPE` ((Q)), `contDiff_edgeModelOf_BPE`;
* `norm_le_mul_sqrt_of_unit_BPE` — unit-vector comparison bounds are homogeneous bounds;
* **`edge_row_supply_BPE`**: EGP06 on every boundary supply in the frozen form (thresholds `Lc, η₀`
  first; smooth model with `C²` bound `C†`, `Q₂`-valued, and the value / derivative comparison of
  `ρ(i)⁻¹π_{Q₂^∂}F_int` against `edgeModelOf_BPE` on the threshold-`8` core, the derivative bound in
  the homogeneous form `≤ eg·√(ρ(i)⁻²g(w, w))`).
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
theorem blockRestrict_congr_BPE {κ : Type*} (i₁ i₂ : DecidableEq κ) {s₁ s₂ : Finset κ}
    (hs : s₁ = s₂) (x : BlockSpace (fun _ : κ => ℝ²)) :
    (letI := i₁; blockRestrict s₁ x) = (letI := i₂; blockRestrict s₂ x) := by
  subst hs
  rw [Subsingleton.elim i₁ i₂]

/-- **Unit-vector bounds are homogeneous bounds**: if `D` is homogeneous (`D(c w) = c D(w)`),
`q` is a positive definite quadratic form (`q(c w) = c²q(w)`, `q ≥ 0`, `q = 0 ⟹ w = 0`) and
`‖D w‖ < e` whenever `q w = 1`, then `‖D w‖ ≤ e·√(q w)` for every `w`. -/
theorem norm_le_mul_sqrt_of_unit_BPE {V F : Type*} [AddCommGroup V] [Module ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (D : V → F) (q : V → ℝ)
    (hD : ∀ (c : ℝ) (w : V), D (c • w) = c • D w)
    (hq : ∀ (c : ℝ) (w : V), q (c • w) = c ^ 2 * q w) (hq0 : ∀ w, 0 ≤ q w)
    (hqz : ∀ w, q w = 0 → w = 0) {e : ℝ} (he : ∀ w, q w = 1 → ‖D w‖ < e) (w : V) :
    ‖D w‖ ≤ e * Real.sqrt (q w) := by
  by_cases hw : q w = 0
  · have hw0 := hqz w hw
    have h0 : D 0 = 0 := by
      have := hD 0 0
      rwa [zero_smul, zero_smul] at this
    have hq00 : q 0 = 0 := by simpa using hq 0 0
    rw [hw0, h0, norm_zero, hq00, Real.sqrt_zero, mul_zero]
  · have hpos : 0 < q w := lt_of_le_of_ne (hq0 w) (Ne.symm hw)
    have hr : 0 < Real.sqrt (q w) := Real.sqrt_pos.mpr hpos
    have hr2 : Real.sqrt (q w) ^ 2 = q w := Real.sq_sqrt hpos.le
    have hw1 : q ((Real.sqrt (q w))⁻¹ • w) = 1 := by
      rw [hq, inv_pow, hr2, inv_mul_cancel₀ hpos.ne']
    have h1 := he _ hw1
    have h2 : D w = Real.sqrt (q w) • D ((Real.sqrt (q w))⁻¹ • w) := by
      rw [← hD, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    rw [h2, norm_smul, Real.norm_eq_abs, abs_of_pos hr, mul_comm]
    exact mul_le_mul_of_nonneg_right h1.le hr.le

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}

namespace BoundarySupply

variable (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
  θ W g δn n B oM)

/-- The stage-`1` tags of the slot are the tags of `Q₂`. -/
theorem stageTagsV2_one_eq_cgpQ2Tags_BPE :
    letI := inducedMetricSpace S.completion.metric
    letI := S.completion.complete
    letI := S.family.instMetricN
    letI := S.family.instChartedN
    letI := S.family.instMetricC
    cgpQ2Tags_BPE S.family.toLocalPacketsOnB S.family.zero = S.stageTagsV2_BAUGD 1 := by
  ext t
  rw [BoundarySupplyCore.mem_stageTagsV2_one_BAUGD]
  simp only [cgpQ2Tags_BPE, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases t with j | j | j | k | bb <;> rfl

/-- **`π₂𝓔⁰ = π_{Q₂^∂} ∘ F_int` on `W°`** (the ported global map of the stored family is BAUG-A's
interior formula; the `Q₂` tags are the stage-`1` tags). -/
theorem cgpProjMap_Q2_eq_BPE (x : W.pieceInterior ⊤) :
    letI := inducedMetricSpace S.completion.metric
    letI := S.completion.complete
    letI := S.family.instMetricN
    letI := S.family.instChartedN
    letI := S.family.instMetricC
    cgpProjMap_BPS S.family.toLocalPacketsOnB S.family.zero
      (cgpQ2Tags_BPE S.family.toLocalPacketsOnB S.family.zero) x =
      (blockRestrict (S.stageTagsV2_BAUGD 1) (S.interiorMapOn_BAUGA x) :
        BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²)) := by
  unfold cgpProjMap_BPS
  rw [← S.interiorMapOn_eq_cgpGlobalMap_BAUGP]
  exact blockRestrict_congr_BPE _ _ (S.stageTagsV2_one_eq_cgpQ2Tags_BPE) _

/-- EGP06's model of the `edgeB` reference `a`, as a map into the interior block space. -/
def edgeModelOf_BPE (a : S.EdgeIdx_BAUGD) (sgn c : S.IntTag_BAUGA → ℝ) :
    ℝ → BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²) :=
  letI := inducedMetricSpace S.completion.metric
  letI := S.completion.complete
  letI := S.family.instMetricN
  letI := S.family.instChartedN
  letI := S.family.instMetricC
  egpModelGraph_BAUGP S.family.toLocalPacketsOnB S.family.zero a.1 sgn c

variable (a : S.EdgeIdx_BAUGD) (sgn c : S.IntTag_BAUGA → ℝ)

theorem edgeModelOf_circle_BPE (j : S.CircleIdx_BAUGD) (u : ℝ) :
    S.edgeModelOf_BPE a sgn c u (.inl j) = 0 :=
  rfl

/-- The own block of the model is `(η, 1)`. -/
theorem edgeModelOf_own_BPE (u : ℝ) :
    S.edgeModelOf_BPE a sgn c u (.inr (.inr (.inl a))) = WithLp.toLp 2 (planeAxis u, 1) :=
  letI := inducedMetricSpace S.completion.metric
  letI := S.completion.complete
  letI := S.family.instMetricN
  letI := S.family.instChartedN
  letI := S.family.instMetricC
  egpModelGraph_own_BAUGP S.family.toLocalPacketsOnB S.family.zero a.1 sgn c a rfl u

/-- **(Q)** The model is `Q₂^∂`-valued. -/
theorem edgeModelOf_blockRestrict_BPE (u : ℝ) :
    blockRestrict (S.stageTagsV2_BAUGD 1) (S.edgeModelOf_BPE a sgn c u) =
      S.edgeModelOf_BPE a sgn c u := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  let _ := S.family.instMetricN
  let _ := S.family.instChartedN
  let _ := S.family.instMetricC
  have h := blockRestrict_egpModelGraph_BAUGP S.family.toLocalPacketsOnB S.family.zero a.1 sgn c u
  rw [← S.stageTagsV2_one_eq_cgpQ2Tags_BPE]
  exact (blockRestrict_congr_BPE _ _ rfl _).trans h

/-- The model is smooth. -/
theorem contDiff_edgeModelOf_BPE : ContDiff ℝ ∞ (S.edgeModelOf_BPE a sgn c) :=
  letI := inducedMetricSpace S.completion.metric
  letI := S.completion.complete
  letI := S.family.instMetricN
  letI := S.family.instChartedN
  letI := S.family.instMetricC
  contDiff_egpModelGraph_BAUGP S.family.toLocalPacketsOnB S.family.zero a.1 sgn c

/-- Unfolding of `edgeModelOf_BPE`. -/
theorem edgeModelOf_eq_BPE (a : S.EdgeIdx_BAUGD) (sgn c : S.IntTag_BAUGA → ℝ) :
    S.edgeModelOf_BPE a sgn c =
      (letI := inducedMetricSpace S.completion.metric
       letI := S.completion.complete
       letI := S.family.instMetricN
       letI := S.family.instChartedN
       letI := S.family.instMetricC
       egpModelGraph_BAUGP S.family.toLocalPacketsOnB S.family.zero a.1 sgn c) :=
  rfl

/-- **The value comparison, transported** from the ported tags to the interior tags: the value bound
for `ρ(i)⁻¹π₂𝓔⁰` against EGP06's model is the value bound for `ρ(i)⁻¹π_{Q₂^∂}F_int` against
`edgeModelOf_BPE`. -/
theorem edgeValue_of_cgp_BPE (i : S.EdgeIdx_BAUGD) (sgn c : S.IntTag_BAUGA → ℝ)
    {x : W.pieceInterior ⊤} {eg : ℝ}
    (h : letI := inducedMetricSpace S.completion.metric
      letI := S.completion.complete
      letI := S.family.instMetricN
      letI := S.family.instChartedN
      letI := S.family.instMetricC
      ‖(S.rho i.1)⁻¹ • cgpProjMap_BPS S.family.toLocalPacketsOnB S.family.zero
          (cgpQ2Tags_BPE S.family.toLocalPacketsOnB S.family.zero) x -
        egpModelGraph_BAUGP S.family.toLocalPacketsOnB S.family.zero i.1 sgn c
          (S.family.edgeB.coord_BAUGA i.1 x)‖ < eg) :
    ‖(S.rho i.1)⁻¹ • blockRestrict (S.stageTagsV2_BAUGD 1) (S.interiorMapOn_BAUGA x) -
      S.edgeModelOf_BPE i sgn c (S.edgeEta_BIF i.1 x)‖ < eg := by
  have hi := (Set.Finite.mem_toFinset _).mp i.2
  rw [S.edgeEta_BIF_eq_coord_BPE hi, ← S.cgpProjMap_Q2_eq_BPE x, S.edgeModelOf_eq_BPE]
  exact h

/-- **The derivative comparison, transported** (unit vectors): as `edgeValue_of_cgp_BPE`. -/
theorem edgeDerivUnit_of_cgp_BPE (i : S.EdgeIdx_BAUGD) (sgn c : S.IntTag_BAUGA → ℝ)
    {x : W.pieceInterior ⊤} {eg : ℝ}
    (h : letI := inducedMetricSpace S.completion.metric
      letI := S.completion.complete
      letI := S.family.instMetricN
      letI := S.family.instChartedN
      letI := S.family.instMetricC
      ∀ w : TangentSpace 𝓘(ℝ, E3) x, (S.rho i.1)⁻¹ ^ 2 * S.completion.metric.inner x w w = 1 →
        ‖(S.rho i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap_BPS S.family.toLocalPacketsOnB
            S.family.zero (cgpQ2Tags_BPE S.family.toLocalPacketsOnB S.family.zero)) x w -
          fderiv ℝ (egpModelGraph_BAUGP S.family.toLocalPacketsOnB S.family.zero i.1 sgn c)
            (S.family.edgeB.coord_BAUGA i.1 x)
            (mvfderiv 𝓘(ℝ, E3) (S.family.edgeB.coord_BAUGA i.1) x w)‖ < eg) :
    ∀ w : TangentSpace 𝓘(ℝ, E3) x, (S.rho i.1)⁻¹ ^ 2 * S.completion.metric.inner x w w = 1 →
      ‖(S.rho i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3)
          (fun y => blockRestrict (S.stageTagsV2_BAUGD 1) (S.interiorMapOn_BAUGA y)) x w -
        fderiv ℝ (S.edgeModelOf_BPE i sgn c) (S.edgeEta_BIF i.1 x)
          (mvfderiv 𝓘(ℝ, E3) (S.edgeEta_BIF i.1) x w)‖ < eg := by
  have hi := (Set.Finite.mem_toFinset _).mp i.2
  have hfun := funext S.cgpProjMap_Q2_eq_BPE
  rw [S.edgeEta_BIF_eq_coord_BPE hi, ← hfun]
  exact h

/-- **Unit-vector derivative bounds are homogeneous**: the comparison of the derivatives on
`ρ(i)⁻²g`-unit vectors gives the bound `≤ eg·√(ρ(i)⁻²g(w, w))` for every tangent vector. -/
theorem edgeDeriv_homog_BPE (i : S.EdgeIdx_BAUGD) (sgn c : S.IntTag_BAUGA → ℝ)
    {x : W.pieceInterior ⊤} {eg : ℝ}
    (h : ∀ w : TangentSpace 𝓘(ℝ, E3) x, (S.rho i.1)⁻¹ ^ 2 * S.completion.metric.inner x w w = 1 →
      ‖(S.rho i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3)
          (fun y => blockRestrict (S.stageTagsV2_BAUGD 1) (S.interiorMapOn_BAUGA y)) x w -
        fderiv ℝ (S.edgeModelOf_BPE i sgn c) (S.edgeEta_BIF i.1 x)
          (mvfderiv 𝓘(ℝ, E3) (S.edgeEta_BIF i.1) x w)‖ < eg) :
    ∀ w : TangentSpace 𝓘(ℝ, E3) x,
      ‖(S.rho i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3)
          (fun y => blockRestrict (S.stageTagsV2_BAUGD 1) (S.interiorMapOn_BAUGA y)) x w -
        fderiv ℝ (S.edgeModelOf_BPE i sgn c) (S.edgeEta_BIF i.1 x)
          (mvfderiv 𝓘(ℝ, E3) (S.edgeEta_BIF i.1) x w)‖ ≤
        eg * Real.sqrt ((S.rho i.1)⁻¹ ^ 2 * S.completion.metric.inner x w w) := by
  have hri := S.rho_pos i.1
  have hr2 : (S.rho i.1)⁻¹ ^ 2 ≠ 0 := pow_ne_zero 2 (inv_ne_zero hri.ne')
  intro w
  refine norm_le_mul_sqrt_of_unit_BPE (fun w => (S.rho i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3)
      (fun y => blockRestrict (S.stageTagsV2_BAUGD 1) (S.interiorMapOn_BAUGA y)) x w -
        fderiv ℝ (S.edgeModelOf_BPE i sgn c) (S.edgeEta_BIF i.1 x)
          (mvfderiv 𝓘(ℝ, E3) (S.edgeEta_BIF i.1) x w))
    (fun w => (S.rho i.1)⁻¹ ^ 2 * S.completion.metric.inner x w w) ?_ ?_ ?_ ?_ h w
  · intro c' w'
    simp only [map_smul, smul_sub, smul_comm (S.rho i.1)⁻¹ c']
  · intro c' w'
    simp only [map_smul, smul_apply, smul_eq_mul]
    ring
  · intro w'
    exact mul_nonneg (pow_nonneg (inv_nonneg.mpr hri.le) 2)
      (metric_inner_self_nonneg S.completion.metric x w')
  · intro w' hw'
    by_contra hne
    have hpos := S.completion.metric.pos x w' hne
    have hz : S.completion.metric.inner x w' w' = 0 := by
      rcases mul_eq_zero.mp hw' with h0 | h0
      · exact absurd h0 hr2
      · exact h0
    exact absurd hz hpos.ne'

/-- **The model's smoothness and `C²` bounds, transported** from the ported tags. -/
theorem edgeModel_props_of_cgp_BPE (i : S.EdgeIdx_BAUGD) (sgn c : S.IntTag_BAUGA → ℝ)
    (h : letI := inducedMetricSpace S.completion.metric
      letI := S.completion.complete
      letI := S.family.instMetricN
      letI := S.family.instChartedN
      letI := S.family.instMetricC
      ContDiff ℝ ∞ (egpModelGraph_BAUGP S.family.toLocalPacketsOnB S.family.zero i.1 sgn c) ∧
        ∀ u, ‖fderiv ℝ (egpModelGraph_BAUGP S.family.toLocalPacketsOnB S.family.zero i.1 sgn c) u‖ ≤
            egpGraphConst ∧
          ‖fderiv ℝ (fderiv ℝ (egpModelGraph_BAUGP S.family.toLocalPacketsOnB S.family.zero i.1 sgn
            c)) u‖ ≤ egpGraphConst) :
    ContDiff ℝ ∞ (S.edgeModelOf_BPE i sgn c) ∧
      ∀ u, ‖fderiv ℝ (S.edgeModelOf_BPE i sgn c) u‖ ≤ egpGraphConst ∧
        ‖fderiv ℝ (fderiv ℝ (S.edgeModelOf_BPE i sgn c)) u‖ ≤ egpGraphConst := by
  rw [S.edgeModelOf_eq_BPE]
  exact h

end BoundarySupply

/-- **EGP06 on a boundary supply, in the ported tags** (consumer of `egp06_full_C14_BAUGP`): the
thresholds first, then for every `edgeB` centre `i` one choice of signs and translations with the
smooth model of `C²` bound `C†` and the value / unit-vector derivative comparison on the
threshold-`8` core `B(i, 100Δρ_i) ∩ {|η_i| ≤ 8Δ} ∩ {t ≤ 8Δ}`. -/
theorem egp06_full_supply_BPE {Δ β₂ eg : ℝ} (hΔ : 1 ≤ Δ) (hβ₂ : 0 < β₂) (hβ₂1 : β₂ < 1 / 1000000)
    (heg : 0 < eg) (heg1 : eg < 1 / 100) :
    ∃ Lc η₀ : ℝ, 0 < Lc ∧ 0 < η₀ ∧
      ∀ {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
        {βd εN Λ w σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
        {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier]
        {g : SmoothRiemannianMetric W.model W.Carrier} {δn : ℝ} {n : ℕ}
        {B : NearlyCuspidalBoundary W g K δn}
        {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}
        (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
          θ W g δn n B oM),
        b ≤ η₀ → s < 1 / 1000000 → β 1 ≤ η₀ → Lc ≤ Lmax → 0 ≤ Λ →
        1000000 * Δ * Λ < 1 / 100000 → μ ≤ 1 / 100 → τ ≤ 1 / 100 →
        σc ≤ (eg / (20 * egpGraphConst)) ^ 2 / 10 ^ 8 →
        μ * Δ < eg / (20 * egpGraphConst) / 100 → 0 < σs →
        σs ≤ (eg / (20 * egpGraphConst)) ^ 2 / 10 ^ 8 →
        vs < eg / (20 * egpGraphConst) / 100 → e < 1 / 40 →
        1600 * (1000000 * Δ) ≤ T → 20 * Λz ≤ T → 0 < ζ →
        ζ ≤ (eg / (20 * egpGraphConst)) ^ 2 / 10 ^ 8 → ζ ≤ 1 / (1000 * (1000000 * Δ)) →
        εr < eg / (20 * egpGraphConst) / (100 * (1000000 * Δ)) →
        letI := inducedMetricSpace S.completion.metric
        letI := S.completion.complete
        letI := S.family.instMetricN
        letI := S.family.instChartedN
        letI := S.family.instMetricC
        ∀ i ∈ S.family.edgeB.centres,
          ∃ sgn c : CGPTag_BAUGP S.family.toLocalPacketsOnB S.family.zero → ℝ,
            (∀ t, |sgn t| ≤ 1) ∧
            (ContDiff ℝ ∞ (egpModelGraph_BAUGP S.family.toLocalPacketsOnB S.family.zero i sgn c) ∧
              ∀ u, ‖fderiv ℝ (egpModelGraph_BAUGP S.family.toLocalPacketsOnB S.family.zero i sgn c)
                  u‖ ≤ egpGraphConst ∧
                ‖fderiv ℝ (fderiv ℝ (egpModelGraph_BAUGP S.family.toLocalPacketsOnB S.family.zero i
                  sgn c)) u‖ ≤ egpGraphConst) ∧
            ∀ x : W.pieceInterior ⊤, dist x i < 100 * Δ * S.rho i →
              |S.family.edgeB.coord_BAUGA i x| ≤ 8 * Δ → S.edgeHeightRaw x ≤ 8 * Δ →
              ‖(S.rho i)⁻¹ • cgpProjMap_BPS S.family.toLocalPacketsOnB S.family.zero
                  (cgpQ2Tags_BPE S.family.toLocalPacketsOnB S.family.zero) x -
                egpModelGraph_BAUGP S.family.toLocalPacketsOnB S.family.zero i sgn c
                  (S.family.edgeB.coord_BAUGA i x)‖ < eg ∧
              ∀ w : TangentSpace 𝓘(ℝ, E3) x, (S.rho i)⁻¹ ^ 2 * S.completion.metric.inner x w w = 1 →
                ‖(S.rho i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap_BPS S.family.toLocalPacketsOnB
                    S.family.zero (cgpQ2Tags_BPE S.family.toLocalPacketsOnB S.family.zero)) x w -
                  fderiv ℝ (egpModelGraph_BAUGP S.family.toLocalPacketsOnB S.family.zero i sgn c)
                    (S.family.edgeB.coord_BAUGA i x)
                    (mvfderiv 𝓘(ℝ, E3) (S.family.edgeB.coord_BAUGA i) x w)‖ < eg := by
  refine (egp06_full_C14_BAUGP hΔ hβ₂ hβ₂1 heg heg1).elim fun Lc h1 => h1.elim fun η₀ h2 =>
    ⟨Lc, η₀, h2.1, h2.2.1, ?_⟩
  have hrow := h2.2.2
  intro K A β βd εN Λ w σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ W _ g δn n B oM S
    hb hs hβ1 hLmax hΛ hLΛ hμ hτ hσc hμΔ hσs0 hσs hvs he hT hTz hζ0 hζθ hζL hεr i hi
  have h := @hrow (W.pieceInterior ⊤) (inducedMetricSpace S.completion.metric) _ _
    S.completion.complete _ S.completion.metric (inducedMetricSpace_hmetric S.completion.metric)
    (fun x => S.rho x) (fun x => S.rho_pos x) Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
    vs ζ Λz _ _ _ _ (letI := inducedMetricSpace S.completion.metric
      letI := S.completion.complete
      S.family.toLocalPacketsOnBFR.toLocalPacketsOnBF) hb hs hβ1 hLmax hΛ hLΛ hμ hτ hσc hμΔ hσs0
    hσs hvs he hT hTz hζ0 hζθ hζL hεr i hi
  refine h.elim fun sgn h1 => h1.elim fun c h2 => ⟨sgn, c, h2.1, ⟨h2.2.1, h2.2.2.1⟩,
    fun x hx hη ht => ?_⟩
  exact h2.2.2.2.2.2 x (show x ∈ (letI := inducedMetricSpace S.completion.metric
    ball i (100 * Δ * S.rho i)) from hx) hη ht

/-- **EGP06 on every boundary supply, in the frozen form**: thresholds `Lc, η₀` first; on every
supply satisfying the hypotheses of the row and at every `edgeB` centre `i` there are signs and
translations with `|sgn| ≤ 1` for which EGP06's model `edgeModelOf_BPE i sgn c` is smooth with
`‖DΦ‖, ‖D²Φ‖ ≤ C†` and the value / derivative comparison of `ρ(i)⁻¹π_{Q₂^∂}F_int` with the model
holds on the threshold-`8` core of `i` (the derivative bound in the homogeneous form). -/
theorem edge_row_supply_BPE {Δ β₂ eg : ℝ} (hΔ : 1 ≤ Δ) (hβ₂ : 0 < β₂) (hβ₂1 : β₂ < 1 / 1000000)
    (heg : 0 < eg) (heg1 : eg < 1 / 100) :
    ∃ Lc η₀ : ℝ, 0 < Lc ∧ 0 < η₀ ∧
      ∀ {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
        {βd εN Λ w σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
        {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier]
        {g : SmoothRiemannianMetric W.model W.Carrier} {δn : ℝ} {n : ℕ}
        {B : NearlyCuspidalBoundary W g K δn}
        {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}
        (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
          θ W g δn n B oM),
        b ≤ η₀ → s < 1 / 1000000 → β 1 ≤ η₀ → Lc ≤ Lmax → 0 ≤ Λ →
        1000000 * Δ * Λ < 1 / 100000 → μ ≤ 1 / 100 → τ ≤ 1 / 100 →
        σc ≤ (eg / (20 * egpGraphConst)) ^ 2 / 10 ^ 8 →
        μ * Δ < eg / (20 * egpGraphConst) / 100 → 0 < σs →
        σs ≤ (eg / (20 * egpGraphConst)) ^ 2 / 10 ^ 8 →
        vs < eg / (20 * egpGraphConst) / 100 → e < 1 / 40 →
        1600 * (1000000 * Δ) ≤ T → 20 * Λz ≤ T → 0 < ζ →
        ζ ≤ (eg / (20 * egpGraphConst)) ^ 2 / 10 ^ 8 → ζ ≤ 1 / (1000 * (1000000 * Δ)) →
        εr < eg / (20 * egpGraphConst) / (100 * (1000000 * Δ)) →
        ∀ i : S.EdgeIdx_BAUGD, ∃ sgn c : S.IntTag_BAUGA → ℝ, (∀ t, |sgn t| ≤ 1) ∧
          ContDiff ℝ ∞ (S.edgeModelOf_BPE i sgn c) ∧
          (∀ u, ‖fderiv ℝ (S.edgeModelOf_BPE i sgn c) u‖ ≤ egpGraphConst ∧
            ‖fderiv ℝ (fderiv ℝ (S.edgeModelOf_BPE i sgn c)) u‖ ≤ egpGraphConst) ∧
          ∀ x : W.pieceInterior ⊤,
            (letI := inducedMetricSpace S.completion.metric
             dist x i.1 < 100 * Δ * S.rho i.1) →
            |S.edgeEta_BIF i.1 x| ≤ 8 * Δ → S.edgeHeightRaw x ≤ 8 * Δ →
            ‖(S.rho i.1)⁻¹ • blockRestrict (S.stageTagsV2_BAUGD 1) (S.interiorMapOn_BAUGA x) -
              S.edgeModelOf_BPE i sgn c (S.edgeEta_BIF i.1 x)‖ < eg ∧
            ∀ w : TangentSpace 𝓘(ℝ, E3) x,
              ‖(S.rho i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3)
                  (fun y => blockRestrict (S.stageTagsV2_BAUGD 1) (S.interiorMapOn_BAUGA y)) x w -
                fderiv ℝ (S.edgeModelOf_BPE i sgn c) (S.edgeEta_BIF i.1 x)
                  (mvfderiv 𝓘(ℝ, E3) (S.edgeEta_BIF i.1) x w)‖ ≤
                eg * Real.sqrt ((S.rho i.1)⁻¹ ^ 2 * S.completion.metric.inner x w w) :=
  (egp06_full_supply_BPE hΔ hβ₂ hβ₂1 heg heg1).elim fun Lc h1 => h1.elim fun η₀ h2 =>
    ⟨Lc, η₀, h2.1, h2.2.1, fun {K A β βd εN Λ w σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
        Λz θ W} [_] {g δn n B oM} S hb hs hβ1 hLmax hΛ hLΛ hμ hτ hσc hμΔ hσs0 hσs hvs he hT hTz hζ0
        hζθ hζL hεr i =>
      (h2.2.2 S hb hs hβ1 hLmax hΛ hLΛ hμ hτ hσc hμΔ hσs0 hσs hvs he hT hTz hζ0 hζθ hζL hεr i.1
        ((Set.Finite.mem_toFinset _).mp i.2)).elim fun sgn h3 => h3.elim fun c h4 =>
        ⟨sgn, c, h4.1, (S.edgeModel_props_of_cgp_BPE i sgn c h4.2.1).1,
          (S.edgeModel_props_of_cgp_BPE i sgn c h4.2.1).2, fun x hx hη ht =>
          ⟨S.edgeValue_of_cgp_BPE i sgn c ((h4.2.2 x hx (by
            rwa [S.edgeEta_BIF_eq_coord_BPE ((Set.Finite.mem_toFinset _).mp i.2)] at hη) ht).1),
            S.edgeDeriv_homog_BPE i sgn c (S.edgeDerivUnit_of_cgp_BPE i sgn c
              ((h4.2.2 x hx (by
                rwa [S.edgeEta_BIF_eq_coord_BPE ((Set.Finite.mem_toFinset _).mp i.2)] at hη)
                ht).2))⟩⟩⟩

end DifferentialGeometry.Geometry.Collapse
