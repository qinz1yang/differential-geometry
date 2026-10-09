import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortCircleRow
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortCircleClauses

/-!
# TCP05 on a boundary supply in the interior tag space (lane O-PORT-A)

The ONE passage from the generic boundary family (`CGPTag_BAUGP S.family.toLocalPacketsOnB
S.family.zero`, `cgpGlobalMap_BAUGP`, `cgpCircleCoord_BAUGP`) to BAUG-A's interior tags
`S.IntTag_BAUGA`, the interior map `S.interiorMapOn_BAUGA` and BIFACE's circle coordinate
`S.circleEta_BIF` of the frozen circle port target (the two tag types are definitionally equal,
`intTag_eq_cgpTag_BAUGP`; `F_int = cgpGlobalMap_BAUGP`, `interiorMapOn_eq_cgpGlobalMap_BAUGP`;
`η = cgpCircleCoord_BAUGP`, `circleEta_eq_cgpCircleCoord_BBP`). Twin of the edge / slim lanes'
`BoundaryPortEdgeTransport` / `BoundaryPortSlimTransport`.

* `circleModelOf_BPC S a Ac cc A1 c1 Bτ cτ : ℝ² → H_int` (TCP05's model graph of the circle
  reference `a`, pruned by CFS27: `tcpPrunedModel_BPC`), `circleModelOf_eq_BPC`;
* `circleModelOf_marker_BPC` (deleted small markers: zero block);
* the transports `circleModel_props_of_cgp_BPC`, `circleTG_of_cgp_BPC`, `circleScale_of_cgp_BPC`;
* `circle_row_cgp_BPC` (TCP05's table at every circle centre of a boundary supply, pruned, in the
  ported tags) and **`circle_row_supply_BPC`** (the same in the frozen interior form).
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

namespace BoundarySupply

variable (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
  θ W g δn n B oM)

/-- **The stage-`0` model of the circle reference `a`**: TCP05's model graph with the actual lists
and the comparison data `A_c, c_c, A₁, c₁, B_τ, c_τ`, pruned by CFS27 at `ρ(a)`, as a map into the
interior block space. -/
def circleModelOf_BPC (a : S.CircleIdx_BAUGD) (Ac : S.IntTag_BAUGA → ℝ² →L[ℝ] ℝ²)
    (cc : S.IntTag_BAUGA → ℝ²) (A1 : S.IntTag_BAUGA → ℝ² →L[ℝ] ℝ) (c1 : S.IntTag_BAUGA → ℝ)
    (Bτ : ℝ² →L[ℝ] ℝ) (cτ : ℝ) : ℝ² → BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²) :=
  letI := inducedMetricSpace S.completion.metric
  letI := S.completion.complete
  letI := S.family.instMetricN
  letI := S.family.instChartedN
  letI := S.family.instMetricC
  tcpPrunedModel_BPC S.family.toLocalPacketsOnB S.family.zero a.1 Ac cc A1 c1 Bτ cτ

variable (a : S.CircleIdx_BAUGD) (Ac : S.IntTag_BAUGA → ℝ² →L[ℝ] ℝ²) (cc : S.IntTag_BAUGA → ℝ²)
  (A1 : S.IntTag_BAUGA → ℝ² →L[ℝ] ℝ) (c1 : S.IntTag_BAUGA → ℝ) (Bτ : ℝ² →L[ℝ] ℝ) (cτ : ℝ)

/-- Unfolding of `circleModelOf_BPC`. -/
theorem circleModelOf_eq_BPC :
    S.circleModelOf_BPC a Ac cc A1 c1 Bτ cτ =
      (letI := inducedMetricSpace S.completion.metric
       letI := S.completion.complete
       letI := S.family.instMetricN
       letI := S.family.instChartedN
       letI := S.family.instMetricC
       tcpPrunedModel_BPC S.family.toLocalPacketsOnB S.family.zero a.1 Ac cc A1 c1 Bτ cτ) :=
  rfl

/-- **(SB) CFS27's deleted blocks**: a marker chart with `ρ(c_m) ≤ ρ(a)/2` has a zero block in the
stage-`0` model of `a`. -/
theorem circleModelOf_marker_BPC (m : S.MarkerIdx_BAUGC)
    (hm : S.rho (S.markerCentre_BAUGC m) ≤ S.rho a.1 / 2) (u : ℝ²) :
    S.circleModelOf_BPC a Ac cc A1 c1 Bτ cτ u (S.markerTag_BAUGC m) = 0 := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  let _ := S.family.instMetricN
  let _ := S.family.instChartedN
  let _ := S.family.instMetricC
  have h := tcpPrunedModel_marker_BPC S.family.toLocalPacketsOnB S.family.zero a.1 Ac cc A1 c1 Bτ
    cτ m (by rcases m with j | j | j <;> exact hm) u
  rcases m with j | j | j <;> exact h

/-- **The model's smoothness, own block and `C²` bounds, transported** from the ported tags. -/
theorem circleModel_props_of_cgp_BPC
    (h : letI := inducedMetricSpace S.completion.metric
      letI := S.completion.complete
      letI := S.family.instMetricN
      letI := S.family.instChartedN
      letI := S.family.instMetricC
      ContDiff ℝ ∞ (tcpPrunedModel_BPC S.family.toLocalPacketsOnB S.family.zero a.1 Ac cc A1 c1 Bτ
          cτ) ∧
        (∀ u, tcpPrunedModel_BPC S.family.toLocalPacketsOnB S.family.zero a.1 Ac cc A1 c1 Bτ cτ u
          (.inl a) = WithLp.toLp 2 (u, 1)) ∧
        ∀ u, ‖fderiv ℝ (tcpPrunedModel_BPC S.family.toLocalPacketsOnB S.family.zero a.1 Ac cc A1 c1
            Bτ cτ) u‖ ≤ tcpGraphConst ∧
          ‖fderiv ℝ (fderiv ℝ (tcpPrunedModel_BPC S.family.toLocalPacketsOnB S.family.zero a.1 Ac
            cc A1 c1 Bτ cτ)) u‖ ≤ tcpGraphConst) :
    ContDiff ℝ ∞ (S.circleModelOf_BPC a Ac cc A1 c1 Bτ cτ) ∧
      (∀ u, S.circleModelOf_BPC a Ac cc A1 c1 Bτ cτ u (.inl a) = WithLp.toLp 2 (u, 1)) ∧
      ∀ u, ‖fderiv ℝ (S.circleModelOf_BPC a Ac cc A1 c1 Bτ cτ) u‖ ≤ tcpGraphConst ∧
        ‖fderiv ℝ (fderiv ℝ (S.circleModelOf_BPC a Ac cc A1 c1 Bτ cτ)) u‖ ≤ tcpGraphConst := by
  rw [S.circleModelOf_eq_BPC]
  exact h

/-- **The value comparison, transported** from the ported tags to the interior tags. -/
theorem circleValue_of_cgp_BPC {x : W.pieceInterior ⊤} {eg : ℝ}
    (h : letI := inducedMetricSpace S.completion.metric
      letI := S.completion.complete
      letI := S.family.instMetricN
      letI := S.family.instChartedN
      letI := S.family.instMetricC
      ‖(S.rho a.1)⁻¹ • cgpGlobalMap_BAUGP S.family.toLocalPacketsOnB S.family.zero x -
        tcpPrunedModel_BPC S.family.toLocalPacketsOnB S.family.zero a.1 Ac cc A1 c1 Bτ cτ
          (cgpCircleCoord_BAUGP S.family.toLocalPacketsOnB a.1 ((Set.Finite.mem_toFinset _).mp a.2)
            x)‖ < eg) :
    ‖(S.rho a.1)⁻¹ • S.interiorMapOn_BAUGA x -
      S.circleModelOf_BPC a Ac cc A1 c1 Bτ cτ (S.circleEta_BIF a.1 x)‖ < eg := by
  rw [S.circleEta_eq_cgpCircleCoord_BBP a, S.interiorMapOn_eq_cgpGlobalMap_BAUGP,
    S.circleModelOf_eq_BPC]
  exact h


/-- **The derivative comparison, transported** (homogeneous form). -/
theorem circleDeriv_of_cgp_BPC {x : W.pieceInterior ⊤} {eg : ℝ}
    (h : letI := inducedMetricSpace S.completion.metric
      letI := S.completion.complete
      letI := S.family.instMetricN
      letI := S.family.instChartedN
      letI := S.family.instMetricC
      ∀ w : TangentSpace 𝓘(ℝ, E3) x,
        ‖(S.rho a.1)⁻¹ • mvfderiv 𝓘(ℝ, E3)
            (cgpGlobalMap_BAUGP S.family.toLocalPacketsOnB S.family.zero) x w -
          fderiv ℝ (tcpPrunedModel_BPC S.family.toLocalPacketsOnB S.family.zero a.1 Ac cc A1 c1 Bτ
            cτ) (cgpCircleCoord_BAUGP S.family.toLocalPacketsOnB a.1
              ((Set.Finite.mem_toFinset _).mp a.2) x)
            (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord_BAUGP S.family.toLocalPacketsOnB a.1
              ((Set.Finite.mem_toFinset _).mp a.2)) x w)‖ ≤
          eg * Real.sqrt ((S.rho a.1)⁻¹ ^ 2 * S.completion.metric.inner x w w)) :
    ∀ w : TangentSpace 𝓘(ℝ, E3) x,
      ‖(S.rho a.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) S.interiorMapOn_BAUGA x w -
          fderiv ℝ (S.circleModelOf_BPC a Ac cc A1 c1 Bτ cτ) (S.circleEta_BIF a.1 x)
            (mvfderiv 𝓘(ℝ, E3) (S.circleEta_BIF a.1) x w)‖ ≤
        eg * Real.sqrt ((S.rho a.1)⁻¹ ^ 2 * S.completion.metric.inner x w w) := by
  rw [S.circleEta_eq_cgpCircleCoord_BBP a, S.interiorMapOn_eq_cgpGlobalMap_BAUGP,
    S.circleModelOf_eq_BPC]
  exact h


/-- **The value / derivative comparison, transported**: (TG) of the pruned model in the ported
tags is (TG) of `ρ(a)⁻¹F_int` against `circleModelOf_BPC` on the threshold-`8` core. -/
theorem circleTG_of_cgp_BPC {eg : ℝ}
    (h : letI := inducedMetricSpace S.completion.metric
      letI := S.completion.complete
      letI := S.family.instMetricN
      letI := S.family.instChartedN
      letI := S.family.instMetricC
      tcpTG_PLN_BAUGP S.family.toLocalPacketsOnBFR.toLocalPacketsOnBF eg
        (tcpPrunedModel_BPC S.family.toLocalPacketsOnB S.family.zero a.1 Ac cc A1 c1 Bτ cτ)
        (cgpCircleCoord_BAUGP S.family.toLocalPacketsOnB a.1 ((Set.Finite.mem_toFinset _).mp a.2))
        a.1) :
    ∀ x : W.pieceInterior ⊤, (letI := inducedMetricSpace S.completion.metric
        dist x a.1 < 200 * S.rho a.1) → ‖S.circleEta_BIF a.1 x‖ ≤ 8 →
      ‖(S.rho a.1)⁻¹ • S.interiorMapOn_BAUGA x -
          S.circleModelOf_BPC a Ac cc A1 c1 Bτ cτ (S.circleEta_BIF a.1 x)‖ < eg ∧
      ∀ w : TangentSpace 𝓘(ℝ, E3) x,
        ‖(S.rho a.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) S.interiorMapOn_BAUGA x w -
            fderiv ℝ (S.circleModelOf_BPC a Ac cc A1 c1 Bτ cτ) (S.circleEta_BIF a.1 x)
              (mvfderiv 𝓘(ℝ, E3) (S.circleEta_BIF a.1) x w)‖ ≤
          eg * Real.sqrt ((S.rho a.1)⁻¹ ^ 2 * S.completion.metric.inner x w w) := by
  intro x hx h8
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  let _ := S.family.instMetricN
  let _ := S.family.instChartedN
  let _ := S.family.instMetricC
  have h8' : ‖cgpCircleCoord_BAUGP S.family.toLocalPacketsOnB a.1
      ((Set.Finite.mem_toFinset _).mp a.2) x‖ ≤ 8 := by
    rw [← S.circleEta_eq_cgpCircleCoord_BBP a]
    exact h8
  have h' := h x hx h8'
  exact ⟨S.circleValue_of_cgp_BPC a Ac cc A1 c1 Bτ cτ h'.1,
    S.circleDeriv_of_cgp_BPC a Ac cc A1 c1 Bτ cτ h'.2⟩

/-- **The frozen scale, transported**: the scale block of the derivative of the model is zero. -/
theorem circleScale_of_cgp_BPC
    (h : letI := inducedMetricSpace S.completion.metric
      letI := S.completion.complete
      letI := S.family.instMetricN
      letI := S.family.instChartedN
      letI := S.family.instMetricC
      ∀ u v, blockMarkerCLM (cgpScaleTag_BAUGP S.family.toLocalPacketsOnB S.family.zero)
        (fderiv ℝ (tcpPrunedModel_BPC S.family.toLocalPacketsOnB S.family.zero a.1 Ac cc A1 c1 Bτ
          cτ) u v) = 0) :
    ∀ u v : ℝ², ((fderiv ℝ (S.circleModelOf_BPC a Ac cc A1 c1 Bτ cτ) u v) S.scaleTag_BAUGA).snd =
      0 := by
  intro u v
  rw [S.circleModelOf_eq_BPC]
  exact h u v

end BoundarySupply

/-- **TCP05 on a boundary supply, pruned, in the ported tags** (consumer of
`tcp05_row_table_PLN_BAUGP` and `tcp05_pruned_point_BPC`): the thresholds first, then at every
circle centre `a` of a supply satisfying the hypotheses of the row, TCP05's comparison data for
which the pruned model is smooth with own block `(u, 1)`, `C²` bound `C`, (TG) on the threshold-`8`
core, and zero scale derivative. -/
theorem circle_row_cgp_BPC {eg ν : ℝ} (heg : 0 < eg) (heg1 : eg < 1 / 100) (hν : 0 < ν)
    (hν1 : ν < 1) :
    ∃ σ : ℝ, 0 < σ ∧ σ ≤ 1 / 1000 ∧ ∃ η₂ γ₀ ηc θt : ℝ, 0 < η₂ ∧ 0 < γ₀ ∧ 0 < ηc ∧ 0 < θt ∧
    θt < 1 ∧ ∀ Δ : ℝ, 1200 ≤ Δ → ∃ η₁ : ℝ, 0 < η₁ ∧
    ∀ {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
      {βd εN Λ w σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
      {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier]
      {g : SmoothRiemannianMetric W.model W.Carrier} {δn : ℝ} {n : ℕ}
      {B : NearlyCuspidalBoundary W g K δn}
      {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}
      (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
        θ W g δn n B oM),
      0 ≤ Λ → μ ≤ 1 / 100 → τ ≤ 1 / 100 → 1000000 * Δ * Λ < 1 / 100000 →
      4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax → e < 1 / 40 → 1600 * (1000000 * Δ) ≤ T →
      0 ≤ ε → ε ≤ 1 → 0 ≤ σc → σc ≤ θt ^ 2 / 1000 → μ * Δ ≤ θt / 100 →
      3 * ν ≤ β 3 → β 3 < 1 → 3 * β 2 ≤ σ → β 2 ≤ η₂ → γ ≤ γ₀ → 0 < γc → γc ≤ γ₀ → βc ≤ ηc →
      b ≤ η₁ → β 1 ≤ η₁ → 0 < σs → σs ≤ θt ^ 2 / 1000 → vs ≤ θt / 100 → 0 < ζ →
      ζ ≤ θt ^ 2 / 1000 → εr ≤ θt / 100 → 20 * Λz ≤ T → σ⁻¹ ≤ Lmax →
      1000 * tcpGraphConst * Δ * Λ < eg →
      letI := inducedMetricSpace S.completion.metric
      letI := S.completion.complete
      letI := S.family.instMetricN
      letI := S.family.instChartedN
      letI := S.family.instMetricC
      ∀ a : S.CircleIdx_BAUGD,
        ∃ (Ac : CGPTag_BAUGP S.family.toLocalPacketsOnB S.family.zero → ℝ² →L[ℝ] ℝ²)
          (cc : CGPTag_BAUGP S.family.toLocalPacketsOnB S.family.zero → ℝ²)
          (A1 : CGPTag_BAUGP S.family.toLocalPacketsOnB S.family.zero → ℝ² →L[ℝ] ℝ)
          (c1 : CGPTag_BAUGP S.family.toLocalPacketsOnB S.family.zero → ℝ) (Bτ : ℝ² →L[ℝ] ℝ)
          (cτ : ℝ),
          (ContDiff ℝ ∞ (tcpPrunedModel_BPC S.family.toLocalPacketsOnB S.family.zero a.1 Ac cc A1 c1
              Bτ cτ) ∧
            (∀ u, tcpPrunedModel_BPC S.family.toLocalPacketsOnB S.family.zero a.1 Ac cc A1 c1 Bτ cτ
              u (.inl a) = WithLp.toLp 2 (u, 1)) ∧
            ∀ u, ‖fderiv ℝ (tcpPrunedModel_BPC S.family.toLocalPacketsOnB S.family.zero a.1 Ac cc
                A1 c1 Bτ cτ) u‖ ≤ tcpGraphConst ∧
              ‖fderiv ℝ (fderiv ℝ (tcpPrunedModel_BPC S.family.toLocalPacketsOnB S.family.zero a.1
                Ac cc A1 c1 Bτ cτ)) u‖ ≤ tcpGraphConst) ∧
          tcpTG_PLN_BAUGP S.family.toLocalPacketsOnBFR.toLocalPacketsOnBF eg
            (tcpPrunedModel_BPC S.family.toLocalPacketsOnB S.family.zero a.1 Ac cc A1 c1 Bτ cτ)
            (cgpCircleCoord_BAUGP S.family.toLocalPacketsOnB a.1
              ((Set.Finite.mem_toFinset _).mp a.2)) a.1 ∧
          ∀ u v, blockMarkerCLM (cgpScaleTag_BAUGP S.family.toLocalPacketsOnB S.family.zero)
            (fderiv ℝ (tcpPrunedModel_BPC S.family.toLocalPacketsOnB S.family.zero a.1 Ac cc A1 c1
              Bτ cτ) u v) = 0 := by
  have hrt := tcp05_row_table_PLN_BAUGP heg heg1 hν hν1
  obtain ⟨σ, hσ, hσ1, η₂, γ₀, ηc, θt, hη₂, hγ₀, hηc, hθt, hθt1, hrow⟩ := hrt
  refine ⟨σ, hσ, hσ1, η₂, γ₀, ηc, θt, hη₂, hγ₀, hηc, hθt, hθt1, fun Δ hΔ => ?_⟩
  have hrΔ := hrow Δ hΔ
  obtain ⟨η₁, hη₁, hrowΔ⟩ := hrΔ
  refine ⟨η₁, hη₁, ?_⟩
  intro K A β βd εN Λ w σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ W _ g δn n B oM S
    h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25
    h26 h27 h28 h29 h30 h31 a
  have hΔ1 : 1 ≤ Δ := by linarith only [hΔ]
  have h := @hrowΔ (W.pieceInterior ⊤) (inducedMetricSpace S.completion.metric) _ _
    S.completion.complete _ S.completion.metric (inducedMetricSpace_hmetric S.completion.metric)
    (fun x => S.rho x) (fun x => S.rho_pos x) Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
    vs ζ Λz _ _ _ _ (letI := inducedMetricSpace S.completion.metric
      letI := S.completion.complete
      S.family.toLocalPacketsOnBFR.toLocalPacketsOnBF) h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
    h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 a.1
    ((Set.Finite.mem_toFinset _).mp a.2)
  refine h.elim fun Ac h2' => h2'.elim fun cc h3' => h3'.elim fun A1 h4' => h4'.elim fun c1 h5' =>
    h5'.elim fun Bτ h6' => h6'.elim fun cτ h7' => ?_
  have hp := @tcp05_pruned_point_BPC (W.pieceInterior ⊤) (inducedMetricSpace S.completion.metric)
    _ _ S.completion.complete _ S.completion.metric (inducedMetricSpace_hmetric S.completion.metric)
    (fun x => S.rho x) (fun x => S.rho_pos x) Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
    vs ζ Λz _ _ _ _ (letI := inducedMetricSpace S.completion.metric
      letI := S.completion.complete
      S.family.toLocalPacketsOnBFR.toLocalPacketsOnBF) hΔ1 h1 h4 _ a Ac cc A1 c1 Bτ cτ h7'.1 h7'.2
  exact ⟨Ac, cc, A1, c1, Bτ, cτ, ⟨hp.1, hp.2.1, hp.2.2.1⟩, hp.2.2.2.1, hp.2.2.2.2.2⟩

/-- **TCP05 on every boundary supply, pruned, in the frozen interior form**: the thresholds first;
on every supply satisfying the hypotheses of the row and at every circle centre `a` there is
TCP05's comparison data for which the stage-`0` model `circleModelOf_BPC` is smooth with own block
`(u, 1)`, `‖DΦ‖, ‖D²Φ‖ ≤ C`, the value / derivative comparison of `ρ(a)⁻¹F_int` with the model on
the threshold-`8` core `B(a, 200ρ(a)) ∩ {‖η_a‖ ≤ 8}` and zero scale derivative. -/
theorem circle_row_supply_BPC {eg ν : ℝ} (heg : 0 < eg) (heg1 : eg < 1 / 100) (hν : 0 < ν)
    (hν1 : ν < 1) :
    ∃ σ : ℝ, 0 < σ ∧ σ ≤ 1 / 1000 ∧ ∃ η₂ γ₀ ηc θt : ℝ, 0 < η₂ ∧ 0 < γ₀ ∧ 0 < ηc ∧ 0 < θt ∧
    θt < 1 ∧ ∀ Δ : ℝ, 1200 ≤ Δ → ∃ η₁ : ℝ, 0 < η₁ ∧
    ∀ {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
      {βd εN Λ w σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
      {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier]
      {g : SmoothRiemannianMetric W.model W.Carrier} {δn : ℝ} {n : ℕ}
      {B : NearlyCuspidalBoundary W g K δn}
      {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}
      (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
        θ W g δn n B oM),
      0 ≤ Λ → μ ≤ 1 / 100 → τ ≤ 1 / 100 → 1000000 * Δ * Λ < 1 / 100000 →
      4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax → e < 1 / 40 → 1600 * (1000000 * Δ) ≤ T →
      0 ≤ ε → ε ≤ 1 → 0 ≤ σc → σc ≤ θt ^ 2 / 1000 → μ * Δ ≤ θt / 100 →
      3 * ν ≤ β 3 → β 3 < 1 → 3 * β 2 ≤ σ → β 2 ≤ η₂ → γ ≤ γ₀ → 0 < γc → γc ≤ γ₀ → βc ≤ ηc →
      b ≤ η₁ → β 1 ≤ η₁ → 0 < σs → σs ≤ θt ^ 2 / 1000 → vs ≤ θt / 100 → 0 < ζ →
      ζ ≤ θt ^ 2 / 1000 → εr ≤ θt / 100 → 20 * Λz ≤ T → σ⁻¹ ≤ Lmax →
      1000 * tcpGraphConst * Δ * Λ < eg →
      ∀ a : S.CircleIdx_BAUGD, ∃ (Ac : S.IntTag_BAUGA → ℝ² →L[ℝ] ℝ²) (cc : S.IntTag_BAUGA → ℝ²)
        (A1 : S.IntTag_BAUGA → ℝ² →L[ℝ] ℝ) (c1 : S.IntTag_BAUGA → ℝ) (Bτ : ℝ² →L[ℝ] ℝ) (cτ : ℝ),
        (ContDiff ℝ ∞ (S.circleModelOf_BPC a Ac cc A1 c1 Bτ cτ) ∧
          (∀ u, S.circleModelOf_BPC a Ac cc A1 c1 Bτ cτ u (.inl a) = WithLp.toLp 2 (u, 1)) ∧
          ∀ u, ‖fderiv ℝ (S.circleModelOf_BPC a Ac cc A1 c1 Bτ cτ) u‖ ≤ tcpGraphConst ∧
            ‖fderiv ℝ (fderiv ℝ (S.circleModelOf_BPC a Ac cc A1 c1 Bτ cτ)) u‖ ≤ tcpGraphConst) ∧
        (∀ x : W.pieceInterior ⊤, (letI := inducedMetricSpace S.completion.metric
            dist x a.1 < 200 * S.rho a.1) → ‖S.circleEta_BIF a.1 x‖ ≤ 8 →
          ‖(S.rho a.1)⁻¹ • S.interiorMapOn_BAUGA x -
              S.circleModelOf_BPC a Ac cc A1 c1 Bτ cτ (S.circleEta_BIF a.1 x)‖ < eg ∧
          ∀ w : TangentSpace 𝓘(ℝ, E3) x,
            ‖(S.rho a.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) S.interiorMapOn_BAUGA x w -
                fderiv ℝ (S.circleModelOf_BPC a Ac cc A1 c1 Bτ cτ) (S.circleEta_BIF a.1 x)
                  (mvfderiv 𝓘(ℝ, E3) (S.circleEta_BIF a.1) x w)‖ ≤
              eg * Real.sqrt ((S.rho a.1)⁻¹ ^ 2 * S.completion.metric.inner x w w)) ∧
        ∀ u v : ℝ², ((fderiv ℝ (S.circleModelOf_BPC a Ac cc A1 c1 Bτ cτ) u v)
          S.scaleTag_BAUGA).snd = 0 := by
  have hc := circle_row_cgp_BPC heg heg1 hν hν1
  obtain ⟨σ, hσ, hσ1, η₂, γ₀, ηc, θt, hη₂, hγ₀, hηc, hθt, hθt1, hrow⟩ := hc
  refine ⟨σ, hσ, hσ1, η₂, γ₀, ηc, θt, hη₂, hγ₀, hηc, hθt, hθt1, fun Δ hΔ => ?_⟩
  have hrΔ := hrow Δ hΔ
  obtain ⟨η₁, hη₁, hrowΔ⟩ := hrΔ
  refine ⟨η₁, hη₁, ?_⟩
  intro K A β βd εN Λ w σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ W _ g δn n B oM S
    h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25
    h26 h27 h28 h29 h30 h31 a
  have h := hrowΔ S h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21
    h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 a
  exact h.elim fun Ac h7' => h7'.elim fun cc h8' => h8'.elim fun A1 h9' => h9'.elim fun c1 h10' =>
    h10'.elim fun Bτ h11' => h11'.elim fun cτ h12' =>
      ⟨Ac, cc, A1, c1, Bτ, cτ, S.circleModel_props_of_cgp_BPC a Ac cc A1 c1 Bτ cτ h12'.1,
        S.circleTG_of_cgp_BPC a Ac cc A1 c1 Bτ cτ h12'.2.1,
        S.circleScale_of_cgp_BPC a Ac cc A1 c1 Bτ cτ h12'.2.2⟩

end DifferentialGeometry.Geometry.Collapse
