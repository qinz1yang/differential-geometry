import DifferentialGeometry.Geometry.Fibration.ActualStageChainBasesApplications
import DifferentialGeometry.Topology.Manifold.LinearChartSubmanifold

/-!
# Draft 74, D74-2: the smooth stage bases of a chain (the seven-row contract) and the adapter

Lane C14-REG-CHAIN (by C14-REG-CHAINc), G11. Draft 74 §1.2 asks for a DETERMINISTIC adapter
`Gaf02Bases.toSmoothStageBases74` from lane C14-BASES's bases object to the smooth stage bases
read by the rows assembler, with a seven-row field contract (stages `0, 1, 2` = circle, edge,
slim). The structure `SmoothStageBasesOn74 C` (on a chain `C`; the closed instance
`SmoothStageBases74 S` is `SmoothStageBasesOn74 S.chain.toChain`) records, row by row:

1. **bases of dimensions `2, 1, 1`**: chart data `circleChart / edgeChart / slimChart` (CGP07's
   chart inverses), each `Θ_st ∘ chart_j` smooth on its ball, onto the open piece
   `W_st ∩ {marked j}` with the LINEAR left inverse `κ_j`, the pieces covering `W_st`; the
   manifold structures are accessors (`circleChartedSpace`, …, `circle_isManifold`, … with model
   `ℝ²`, `ℝ`, `ℝ`; the inclusions into the block space are smooth immersions); Hausdorff and
   second countable as subspaces of the (finite-dimensional) block space;
2. **native / later / final**: `Θ_st` injective (no merging) and smooth on the WHOLE native
   marked base `V_st⁰`, `Θ₃ = id`, and every native patch is parametrized by the SAME chart
   (`chart_j (κ_j w) = w` on `V_j⁰`), so `Θ_st|V_j⁰ = (Θ_st ∘ chart_j) ∘ κ_j` is a smooth
   embedding onto `W_st ∩ {marked j}`;
3. **same-chain binding**: `π_st ∘ E = Θ_st ∘ f_st` at every point (`f_st = stageMap_BAS`);
4. **open parent domains**: FC33's exact threshold-5 domains `U_st` are OPEN in `X` (for the edge:
   the open ambient parent `{|η_j| < 5Δ, t < 5Δ}` on the chart ball, not a height-truncated disk
   space) — `isOpen_gafStageDomain5_R74`;
5. **projections**: `π_st ∘ E` smooth, `π_stE(U_st) ⊆ W_st`, the threshold-5 submersions in chart
   form;
6. **whole-fibre identification**: for `w₀ ∈ V_st⁰`, `{p | f_st p ∈ V_st⁰, π_stE p = Θ_st w₀} =
   f_st⁻¹(w₀)` (both inclusions; no merging), and (RF) on the carriers `D_st`;
7. **empty family**: an EMPTY actual centre set gives empty `W_st`, `V_st⁰` and `U_st`.

`Gaf02Bases.toSmoothStageBases74 B` fills every field from `B`'s fields (`B.circle.spec`, …,
`B.later`) and `isOpen_gafStageDomain5_R74`; it is a `def` (no existence statement).

GAPS (D74 "report, do not assume"; not fields): (a) the whole-fibre equality WITHOUT the
restriction `f_st p ∈ V_st⁰` (points whose native value leaves the marked base) needs either
`f_st(U_st) ⊆ V_st⁰` or injectivity of `Θ_st` beyond `V_st⁰` — neither is in `Gaf02Bases`;
(b) properness / exhaustion of `π_stE` on the parent domains in the abstract-manifold form
(the bases object only carries per-patch compact preimages of `κ_j`, `spec.proper`); (c) a
submersion statement into the abstract manifold `W_st` (here: chart form, `κ_j ∘ π_stE`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis DifferentialGeometry.Topology.Manifold

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}

/-- **D74-2 row 4: FC33's threshold-5 parent domains are open** (circle: chart ball and
`‖η_j‖ < 5`; edge: chart ball, `|η_j| < 5Δ`, `t < 5Δ` — the open AMBIENT parent; slim: chart
ball and `|η_j| < 5·10⁵Δ`). -/
theorem isOpen_gafStageDomain5_R74 (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b'
    s' ε γc βc Lmax τ γ δ εr e T V) (st : Fin 3) : IsOpen (gafStageDomain5_BAS P st) := by
  fin_cases st
  · change IsOpen {p | ∃ j : P.toLocalChartFamily.circle.finite_centres.toFinset,
        p ∈ ball j.1 (200 * ρ j.1) ∧ ‖cgpCoord P.toLocalChartFamily P.zero (.inl j) p‖ < 5}
    rw [ofPred_exists]
    refine isOpen_iUnion fun j => ?_
    have h := (cgpCircleCoord_contMDiffOn P.toLocalChartFamily
      ((Set.Finite.mem_toFinset _).mp j.2)).continuousOn.isOpen_inter_preimage isOpen_ball
      (isOpen_ball (x := (0 : ℝ²)) (ε := 5))
    convert h using 1
    ext p
    simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_ball_zero_iff]
    rfl
  · change IsOpen {p | ∃ j : P.edge.finite_centres.toFinset, p ∈ ball j.1 (100 * Δ * ρ j.1) ∧
        |P.edge.coord j.1 p| < 5 * Δ ∧ cgpHeight P.toLocalChartFamily p < 5 * Δ}
    rw [ofPred_exists]
    refine isOpen_iUnion fun j => ?_
    have h := ((P.edge.contMDiffOn_coord ((Set.Finite.mem_toFinset _).mp j.2)
      ).continuousOn.isOpen_inter_preimage isOpen_ball
      (isOpen_Ioo (a := -(5 * Δ)) (b := 5 * Δ))).inter
      ((isOpen_Iio (a := 5 * Δ)).preimage (continuous_cgpHeight P.toLocalChartFamily))
    convert h using 1
    ext p
    simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_Ioo, mem_Iio, abs_lt]
    tauto
  · change IsOpen {p | ∃ j : P.slim.finite_centres.toFinset, p ∈ ball j.1 (1000000 * Δ * ρ j.1) ∧
        |(P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord p| < 5 * (10 ^ 5 * Δ)}
    rw [ofPred_exists]
    refine isOpen_iUnion fun j => ?_
    have h := ((P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).contMDiffOn_coord
      ).continuousOn.isOpen_inter_preimage isOpen_ball
      (isOpen_Ioo (a := -(5 * (10 ^ 5 * Δ))) (b := 5 * (10 ^ 5 * Δ)))
    convert h using 1
    · ext p
      simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_Ioo, abs_lt]
      norm_num

/-- D74-2 rows 1–2 (charts): the bases of dimensions `2, 1, 1` in chart form for given chart
families, and the native patches parametrized by the same charts. -/
structure SmoothStageChartsSpec74
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc
      Lmax τ γ δ εr e T V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}
    (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (circleChart : P.toLocalChartFamily.circle.finite_centres.toFinset → ℝ² →
      BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    (edgeChart : P.edge.finite_centres.toFinset → ℝ →
      BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    (slimChart : P.slim.finite_centres.toFinset → ℝ →
      BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) : Prop where
  /-- Row 1, circle: `Θ₁ ∘ chart_j` is smooth on the ball. -/
  circle_smooth : ∀ j, ContDiffOn ℝ ∞ (C.Θ_BAS 0 ∘ circleChart j) (ball 0 (11 / 2 * 1))
  /-- Row 1, circle: `Θ₁ ∘ chart_j` lands in `W₁ ∩ {marked j}` with left inverse `κ_j`. -/
  circle_param : ∀ j, ∀ b ∈ ball (0 : ℝ²) (11 / 2 * 1),
    C.Θ_BAS 0 (circleChart j b) ∈ C.finalBase_BAS 0 ∩ markedCondition_BPRE
      (gafCircleVector P.toLocalChartPackets j) (gafCircleMarker P.toLocalChartPackets j)
      (ρ j.1) 1 ∧
    ((ρ j.1)⁻¹ • gafCircleVector P.toLocalChartPackets j) (C.Θ_BAS 0 (circleChart j b)) = b
  /-- Row 1, circle: `κ_j` maps `W₁ ∩ {marked j}` into the ball, inverse `Θ₁ ∘ chart_j`. -/
  circle_coord : ∀ j, ∀ y ∈ C.finalBase_BAS 0 ∩ markedCondition_BPRE
      (gafCircleVector P.toLocalChartPackets j) (gafCircleMarker P.toLocalChartPackets j)
      (ρ j.1) 1,
    ((ρ j.1)⁻¹ • gafCircleVector P.toLocalChartPackets j) y ∈ ball (0 : ℝ²) (11 / 2 * 1) ∧
      C.Θ_BAS 0 (circleChart j (((ρ j.1)⁻¹ • gafCircleVector P.toLocalChartPackets j) y)) = y
  /-- Row 1, circle: the marked pieces cover `W₁`. -/
  circle_cover : C.finalBase_BAS 0 ⊆ ⋃ j, markedCondition_BPRE
    (gafCircleVector P.toLocalChartPackets j) (gafCircleMarker P.toLocalChartPackets j) (ρ j.1) 1
  /-- Row 1, edge: `Θ₂ ∘ chart_j` is smooth on the interval. -/
  edge_smooth : ∀ j, ContDiffOn ℝ ∞ (C.Θ_BAS 1 ∘ edgeChart j) (ball 0 (11 / 2 * Δ))
  /-- Row 1, edge: `Θ₂ ∘ chart_j` lands in `W₂ ∩ {marked j}` with left inverse `κ_j`. -/
  edge_param : ∀ j, ∀ b ∈ ball (0 : ℝ) (11 / 2 * Δ),
    C.Θ_BAS 1 (edgeChart j b) ∈ C.finalBase_BAS 1 ∩ markedCondition_BPRE
      (axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j))
      (gafEdgeMarker P.toLocalChartFamily P.zero j) (ρ j.1) Δ ∧
    ((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j))
      (C.Θ_BAS 1 (edgeChart j b)) = b
  /-- Row 1, edge: `κ_j` maps `W₂ ∩ {marked j}` into the interval, inverse `Θ₂ ∘ chart_j`. -/
  edge_coord : ∀ j, ∀ y ∈ C.finalBase_BAS 1 ∩ markedCondition_BPRE
      (axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j))
      (gafEdgeMarker P.toLocalChartFamily P.zero j) (ρ j.1) Δ,
    ((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j)) y ∈
      ball (0 : ℝ) (11 / 2 * Δ) ∧
    C.Θ_BAS 1 (edgeChart j (((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp
      (gafEdgeVector P.toLocalChartFamily P.zero j)) y)) = y
  /-- Row 1, edge: the marked pieces cover `W₂`. -/
  edge_cover : C.finalBase_BAS 1 ⊆ ⋃ j, markedCondition_BPRE
    (axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j))
    (gafEdgeMarker P.toLocalChartFamily P.zero j) (ρ j.1) Δ
  /-- Row 1, slim: `Θ₃ ∘ chart_j` is smooth on the interval. -/
  slim_smooth : ∀ j, ContDiffOn ℝ ∞ (C.Θ_BAS 2 ∘ slimChart j) (ball 0 (11 / 2 * (10 ^ 5 * Δ)))
  /-- Row 1, slim: `Θ₃ ∘ chart_j` lands in `W₃ ∩ {marked j}` with left inverse `κ_j`. -/
  slim_param : ∀ j, ∀ b ∈ ball (0 : ℝ) (11 / 2 * (10 ^ 5 * Δ)),
    C.Θ_BAS 2 (slimChart j b) ∈ C.finalBase_BAS 2 ∩ markedCondition_BPRE
      (axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j))
      (gafSlimMarker P.toLocalChartFamily P.zero j) (ρ j.1) (10 ^ 5 * Δ) ∧
    ((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j))
      (C.Θ_BAS 2 (slimChart j b)) = b
  /-- Row 1, slim: `κ_j` maps `W₃ ∩ {marked j}` into the interval, inverse `Θ₃ ∘ chart_j`. -/
  slim_coord : ∀ j, ∀ y ∈ C.finalBase_BAS 2 ∩ markedCondition_BPRE
      (axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j))
      (gafSlimMarker P.toLocalChartFamily P.zero j) (ρ j.1) (10 ^ 5 * Δ),
    ((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j)) y ∈
      ball (0 : ℝ) (11 / 2 * (10 ^ 5 * Δ)) ∧
    C.Θ_BAS 2 (slimChart j (((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp
      (gafSlimVector P.toLocalChartFamily P.zero j)) y)) = y
  /-- Row 1, slim: the marked pieces cover `W₃`. -/
  slim_cover : C.finalBase_BAS 2 ⊆ ⋃ j, markedCondition_BPRE
    (axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j))
    (gafSlimMarker P.toLocalChartFamily P.zero j) (ρ j.1) (10 ^ 5 * Δ)
  /-- Row 2, circle: the native patch `V_j⁰` is parametrized by the SAME chart. -/
  circle_patch : ∀ j, ∀ w ∈ C.circlePatch_BAS j,
    ((ρ j.1)⁻¹ • gafCircleVector P.toLocalChartPackets j) w ∈ ball (0 : ℝ²) (11 / 2 * 1) ∧
      circleChart j (((ρ j.1)⁻¹ • gafCircleVector P.toLocalChartPackets j) w) = w
  /-- Row 2, edge: the native patch `V_j⁰` is parametrized by the SAME chart. -/
  edge_patch : ∀ j, ∀ w ∈ C.edgePatch_BAS j,
    ((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j)) w ∈
      ball (0 : ℝ) (11 / 2 * Δ) ∧
    edgeChart j (((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp
      (gafEdgeVector P.toLocalChartFamily P.zero j)) w) = w
  /-- Row 2, slim: the native patch `V_j⁰` is parametrized by the SAME chart. -/
  slim_patch : ∀ j, ∀ w ∈ C.slimPatch_BAS j,
    ((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j)) w ∈
      ball (0 : ℝ) (11 / 2 * (10 ^ 5 * Δ)) ∧
    slimChart j (((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp
      (gafSlimVector P.toLocalChartFamily P.zero j)) w) = w

/-- D74-2 rows 2–3 (later maps): no merging, smoothness on the whole native base, `Θ₃ = id`,
the same-chain factorization `π_st ∘ E = Θ_st ∘ f_st`. -/
structure SmoothStageLaterSpec74
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc
      Lmax τ γ δ εr e T V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}
    (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw) : Prop where
  /-- Row 2: no merging — `Θ_st` is injective on the whole native marked base `V_st⁰`. -/
  later_injOn : ∀ st, InjOn (C.Θ_BAS st) (C.markedBase_BAS st)
  /-- Row 2: `Θ_st` is smooth at every point of the whole native marked base. -/
  later_smooth : ∀ st, ∀ w ∈ C.markedBase_BAS st, ContDiffAt ℝ ∞ (C.Θ_BAS st) w
  /-- Row 2: the last later transport is the identity. -/
  later_last : C.Θ_BAS 2 = id
  /-- Row 3: same-chain binding `π_st ∘ E = Θ_st ∘ f_st` at every point. -/
  final_factor : ∀ st p, (gafStageQ P.toLocalChartFamily P.zero st).starProjection (C.E p) =
    C.Θ_BAS st (C.stageMap_BAS st p)

/-- D74-2 rows 4–5 (parent domains and projections): open threshold-5 domains, smooth final
projections into the final bases, threshold-5 submersions (chart form). -/
structure SmoothStageProjSpec74
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc
      Lmax τ γ δ εr e T V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}
    (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw) : Prop where
  /-- Row 4: the threshold-5 parent domains are open. -/
  domain_open : ∀ st, IsOpen (gafStageDomain5_BAS P.toLocalChartPackets st)
  /-- Row 5: `π_st ∘ E` is smooth. -/
  final_smooth : ∀ st, ContMDiff 𝓘(ℝ, E3)
    𝓘(ℝ, BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) ∞
    (fun p => (gafStageQ P.toLocalChartFamily P.zero st).starProjection (C.E p))
  /-- Row 5: `π_stE(U_st) ⊆ W_st`. -/
  mapsTo_final : ∀ st, MapsTo (fun p => (gafStageQ P.toLocalChartFamily P.zero st).starProjection
    (C.E p)) (gafStageDomain5_BAS P.toLocalChartPackets st) (C.finalBase_BAS st)
  /-- Row 5, circle: the threshold-5 submersion (chart form). -/
  circle_submersion : ∀ j {p : X}, p ∈ ball j.1 (200 * ρ j.1) →
    ‖cgpCoord P.toLocalChartFamily P.zero (.inl j) p‖ < 5 →
    (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.E p) ∈
        C.finalBase_BAS 0 ∩ markedCondition_BPRE (gafCircleVector P.toLocalChartPackets j)
          (gafCircleMarker P.toLocalChartPackets j) (ρ j.1) 1 ∧
      Surjective (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²) (fun q =>
        ((ρ j.1)⁻¹ • gafCircleVector P.toLocalChartPackets j)
          ((gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.E q))) p)
  /-- Row 5, edge: the threshold-5 submersion (chart form). -/
  edge_submersion : ∀ j {p : X}, p ∈ ball j.1 (100 * Δ * ρ j.1) →
    |P.edge.coord j.1 p| < 5 * Δ → cgpHeight P.toLocalChartFamily p < 5 * Δ →
    (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (C.E p) ∈
        C.finalBase_BAS 1 ∩ markedCondition_BPRE
          (axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j))
          (gafEdgeMarker P.toLocalChartFamily P.zero j) (ρ j.1) Δ ∧
      Surjective (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (fun q =>
        ((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j))
          ((gafStageQ P.toLocalChartFamily P.zero 1).starProjection (C.E q))) p)
  /-- Row 5, slim: the threshold-5 submersion (chart form). -/
  slim_submersion : ∀ j {p : X}, p ∈ ball j.1 (1000000 * Δ * ρ j.1) →
    |(P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord p| < 5 * (10 ^ 5 * Δ) →
    (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.E p) ∈
        C.finalBase_BAS 2 ∩ markedCondition_BPRE
          (axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j))
          (gafSlimMarker P.toLocalChartFamily P.zero j) (ρ j.1) (10 ^ 5 * Δ) ∧
      Surjective (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (fun q =>
        ((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j))
          ((gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.E q))) p)

/-- D74-2 rows 6–7 (fibres and empty family): whole-fibre identification over the native base,
(RF) on the carriers, empty stage by an empty actual centre set. -/
structure SmoothStageFibreSpec74
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc
      Lmax τ γ δ εr e T V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}
    (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw) : Prop where
  /-- Row 6: whole-fibre identification (both ways, no merging) over the native marked base. -/
  fibre_whole : ∀ st {w₀ : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)},
    w₀ ∈ C.markedBase_BAS st →
    {p | C.stageMap_BAS st p ∈ C.markedBase_BAS st ∧
        (gafStageQ P.toLocalChartFamily P.zero st).starProjection (C.E p) = C.Θ_BAS st w₀} =
      C.stageMap_BAS st ⁻¹' {w₀}
  /-- Row 6: (RF) on the carriers `D_st`. -/
  fibre_rf : ∀ st {w₀ : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)},
    w₀ ∈ C.markedBase_BAS st →
    {p | p ∈ C.carrier_BAS st ∧
        (gafStageQ P.toLocalChartFamily P.zero st).starProjection (C.E p) = C.Θ_BAS st w₀} =
      {p | p ∈ C.carrier_BAS st ∧ C.stageMap_BAS st p = w₀}
  /-- Row 7, circle: an empty actual circle centre set empties `W₁`, `V₁⁰`, `U₁`. -/
  circle_empty : P.toLocalChartFamily.circle.centres = ∅ →
    C.finalBase_BAS 0 = ∅ ∧ C.markedBase_BAS 0 = ∅ ∧
      gafStageDomain5_BAS P.toLocalChartPackets 0 = ∅
  /-- Row 7, edge: an empty actual edge centre set empties `W₂`, `V₂⁰`, `U₂`. -/
  edge_empty : P.edge.centres = ∅ →
    C.finalBase_BAS 1 = ∅ ∧ C.markedBase_BAS 1 = ∅ ∧
      gafStageDomain5_BAS P.toLocalChartPackets 1 = ∅
  /-- Row 7, slim: an empty actual slim centre set empties `W₃`, `V₃⁰`, `U₃`. -/
  slim_empty : P.slim.centres = ∅ →
    C.finalBase_BAS 2 = ∅ ∧ C.markedBase_BAS 2 = ∅ ∧
      gafStageDomain5_BAS P.toLocalChartPackets 2 = ∅


/-- **D74-2: the smooth stage bases of a chain** (seven-row contract; see the module doc): the
chart data and the four row groups. -/
structure SmoothStageBasesOn74
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc
      Lmax τ γ δ εr e T V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}
    (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw) : Type where
  /-- Row 1: CGP07's chart inverses of the circle patches (`W₁`, dimension 2). -/
  circleChart : P.toLocalChartFamily.circle.finite_centres.toFinset → ℝ² →
    BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
  /-- Row 1: CGP07's chart inverses of the edge patches (`W₂`, dimension 1). -/
  edgeChart : P.edge.finite_centres.toFinset → ℝ →
    BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
  /-- Row 1: CGP07's chart inverses of the slim patches (`W₃`, dimension 1). -/
  slimChart : P.slim.finite_centres.toFinset → ℝ →
    BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
  /-- Rows 1–2: the charts. -/
  charts : SmoothStageChartsSpec74 C circleChart edgeChart slimChart
  /-- Rows 2–3: the later maps. -/
  later : SmoothStageLaterSpec74 C
  /-- Rows 4–5: parent domains and projections. -/
  proj : SmoothStageProjSpec74 C
  /-- Rows 6–7: fibres and the empty family. -/
  fibres : SmoothStageFibreSpec74 C

namespace Gaf02Bases

variable {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}
  {C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw} {R : Gaf02RoughData C}

/-- Row 6 from the bases object: over the native marked base, the final fibre of `Θ_st w₀` is
the native fibre of `w₀` (no merging + the factorization at every point). -/
theorem fibre_whole_R74 (B : Gaf02Bases C R) (st : Fin 3)
    {w₀ : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)}
    (hw₀ : w₀ ∈ C.markedBase_BAS st) :
    {p | C.stageMap_BAS st p ∈ C.markedBase_BAS st ∧
        (gafStageQ P.toLocalChartFamily P.zero st).starProjection (C.E p) = C.Θ_BAS st w₀} =
      C.stageMap_BAS st ⁻¹' {w₀} := by
  ext p
  constructor
  · rintro ⟨hp, he⟩
    rw [B.later.final_factor st p] at he
    exact B.later.later_injOn st hp hw₀ he
  · intro h
    have h' : C.stageMap_BAS st p = w₀ := h
    refine ⟨h' ▸ hw₀, ?_⟩
    rw [B.later.final_factor st p, h']

end Gaf02Bases

namespace Gaf02Chain

variable {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

/-- Row 7, circle: an empty actual circle centre set empties `W₁`, `V₁⁰`, `U₁`. -/
theorem circle_empty_R74 (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (h : P.toLocalChartFamily.circle.centres = ∅) :
    C.finalBase_BAS 0 = ∅ ∧ C.markedBase_BAS 0 = ∅ ∧
      gafStageDomain5_BAS P.toLocalChartPackets 0 = ∅ := by
  have hno : ∀ j : P.toLocalChartFamily.circle.finite_centres.toFinset, False := fun j =>
    Set.eq_empty_iff_forall_notMem.mp h _ ((Set.Finite.mem_toFinset _).mp j.2)
  have hV : C.markedBase_BAS 0 = ∅ := iUnion_eq_empty.mpr fun j => (hno j).elim
  refine ⟨?_, hV, eq_empty_iff_forall_notMem.mpr fun p hp => ?_⟩
  · change C.Θ_BAS 0 '' C.markedBase_BAS 0 = ∅
    rw [hV, image_empty]
  · obtain ⟨j, -⟩ := hp
    exact hno j

/-- Row 7, edge: an empty actual edge centre set empties `W₂`, `V₂⁰`, `U₂`. -/
theorem edge_empty_R74 (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (h : P.edge.centres = ∅) :
    C.finalBase_BAS 1 = ∅ ∧ C.markedBase_BAS 1 = ∅ ∧
      gafStageDomain5_BAS P.toLocalChartPackets 1 = ∅ := by
  have hno : ∀ j : P.edge.finite_centres.toFinset, False := fun j =>
    Set.eq_empty_iff_forall_notMem.mp h _ ((Set.Finite.mem_toFinset _).mp j.2)
  have hV : C.markedBase_BAS 1 = ∅ := iUnion_eq_empty.mpr fun j => (hno j).elim
  refine ⟨?_, hV, eq_empty_iff_forall_notMem.mpr fun p hp => ?_⟩
  · change C.Θ_BAS 1 '' C.markedBase_BAS 1 = ∅
    rw [hV, image_empty]
  · obtain ⟨j, -⟩ := hp
    exact hno j

/-- Row 7, slim: an empty actual slim centre set empties `W₃`, `V₃⁰`, `U₃`. -/
theorem slim_empty_R74 (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (h : P.slim.centres = ∅) :
    C.finalBase_BAS 2 = ∅ ∧ C.markedBase_BAS 2 = ∅ ∧
      gafStageDomain5_BAS P.toLocalChartPackets 2 = ∅ := by
  have hno : ∀ j : P.slim.finite_centres.toFinset, False := fun j =>
    Set.eq_empty_iff_forall_notMem.mp h _ ((Set.Finite.mem_toFinset _).mp j.2)
  have hV : C.markedBase_BAS 2 = ∅ := iUnion_eq_empty.mpr fun j => (hno j).elim
  refine ⟨?_, hV, eq_empty_iff_forall_notMem.mpr fun p hp => ?_⟩
  · change C.Θ_BAS 2 '' C.markedBase_BAS 2 = ∅
    rw [hV, image_empty]
  · obtain ⟨j, -⟩ := hp
    exact hno j

end Gaf02Chain

namespace Gaf02Bases

variable {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}
  {C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw} {R : Gaf02RoughData C}

/-- **The D74-2 adapter** (deterministic): every field of the smooth stage bases read off the
bases object `B` (its stage packages and later package) and the openness of FC33's domains. -/
def toSmoothStageBases74 (B : Gaf02Bases C R) : SmoothStageBasesOn74 C where
  circleChart := B.circle.chart
  edgeChart := B.edge.chart
  slimChart := B.slim.chart
  charts :=
    { circle_smooth := fun j => (B.circle.spec.base_chart j).1
      circle_param := fun j => (B.circle.spec.base_chart j).2.1
      circle_coord := fun j => (B.circle.spec.base_chart j).2.2
      circle_cover := B.circle.spec.cover
      edge_smooth := fun j => (B.edge.spec.base_chart j).1
      edge_param := fun j => (B.edge.spec.base_chart j).2.1
      edge_coord := fun j => (B.edge.spec.base_chart j).2.2
      edge_cover := B.edge.spec.cover
      slim_smooth := fun j => (B.slim.spec.base_chart j).1
      slim_param := fun j => (B.slim.spec.base_chart j).2.1
      slim_coord := fun j => (B.slim.spec.base_chart j).2.2
      slim_cover := B.slim.spec.cover
      circle_patch := fun j _ hw =>
        ⟨(B.circle.spec.patch j).1.mapsTo hw, (B.circle.spec.patch j).2.2.1.1 hw⟩
      edge_patch := fun j _ hw =>
        ⟨(B.edge.spec.patch j).1.mapsTo hw, (B.edge.spec.patch j).2.2.1.1 hw⟩
      slim_patch := fun j _ hw =>
        ⟨(B.slim.spec.patch j).1.mapsTo hw, (B.slim.spec.patch j).2.2.1.1 hw⟩ }
  later :=
    { later_injOn := B.later.later_injOn
      later_smooth := B.later.later_contDiffAt
      later_last := B.later.later_last
      final_factor := B.later.final_factor }
  proj :=
    { domain_open := isOpen_gafStageDomain5_R74 P.toLocalChartPackets
      final_smooth := B.later.final_smooth
      mapsTo_final := B.later.mapsTo_final
      circle_submersion := fun j _ hp hη => B.circle.spec.submersion j hp hη
      edge_submersion := fun j _ hp hη ht => B.edge.spec.submersion j hp hη ht
      slim_submersion := fun j _ hp hη => B.slim.spec.submersion j hp hη }
  fibres :=
    { fibre_whole := fun st _ hw₀ => B.fibre_whole_R74 st hw₀
      fibre_rf := fun st _ hw₀ => B.later.rf st hw₀
      circle_empty := C.circle_empty_R74
      edge_empty := C.edge_empty_R74
      slim_empty := C.slim_empty_R74 }

end Gaf02Bases

namespace SmoothStageBasesOn74

variable {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}
  {C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw}

/-- **Row 1: `W₁` as a smooth surface** (model `ℝ²`): the linear charts `κ_j` of the marked
pieces, with inverses `Θ₁ ∘ chart_j`. -/
@[reducible]
def circleChartedSpace (A : SmoothStageBasesOn74 C) : ChartedSpace ℝ² (C.finalBase_BAS 0) :=
  linearChartedSpace_R74 (C.finalBase_BAS 0)
    (fun j => (ρ j.1)⁻¹ • gafCircleVector P.toLocalChartPackets j)
    (fun j => C.Θ_BAS 0 ∘ A.circleChart j)
    (fun j => markedCondition_BPRE (gafCircleVector P.toLocalChartPackets j)
      (gafCircleMarker P.toLocalChartPackets j) (ρ j.1) 1) (11 / 2 * 1)
    (fun _ => isOpen_markedCondition_BPRE _ _ _ _) A.charts.circle_smooth A.charts.circle_param
    A.charts.circle_coord A.charts.circle_cover

/-- **Row 1: `W₂` as a smooth curve** (model `ℝ`). -/
@[reducible]
def edgeChartedSpace (A : SmoothStageBasesOn74 C) : ChartedSpace ℝ (C.finalBase_BAS 1) :=
  linearChartedSpace_R74 (C.finalBase_BAS 1)
    (fun j => (ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j))
    (fun j => C.Θ_BAS 1 ∘ A.edgeChart j)
    (fun j => markedCondition_BPRE
      (axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j))
      (gafEdgeMarker P.toLocalChartFamily P.zero j) (ρ j.1) Δ) (11 / 2 * Δ)
    (fun _ => isOpen_markedCondition_BPRE _ _ _ _) A.charts.edge_smooth A.charts.edge_param
    A.charts.edge_coord A.charts.edge_cover

/-- **Row 1: `W₃` as a smooth curve** (model `ℝ`). -/
@[reducible]
def slimChartedSpace (A : SmoothStageBasesOn74 C) : ChartedSpace ℝ (C.finalBase_BAS 2) :=
  linearChartedSpace_R74 (C.finalBase_BAS 2)
    (fun j => (ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j))
    (fun j => C.Θ_BAS 2 ∘ A.slimChart j)
    (fun j => markedCondition_BPRE
      (axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j))
      (gafSlimMarker P.toLocalChartFamily P.zero j) (ρ j.1) (10 ^ 5 * Δ)) (11 / 2 * (10 ^ 5 * Δ))
    (fun _ => isOpen_markedCondition_BPRE _ _ _ _) A.charts.slim_smooth A.charts.slim_param
    A.charts.slim_coord A.charts.slim_cover

/-- `W₁` is a smooth manifold of dimension 2 and its inclusion is a smooth immersion. -/
theorem circle_isManifold (A : SmoothStageBasesOn74 C) :
    let _ := A.circleChartedSpace
    IsManifold 𝓘(ℝ, ℝ²) ∞ (C.finalBase_BAS 0) ∧
      ContMDiff 𝓘(ℝ, ℝ²) 𝓘(ℝ, BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) ∞
        (Subtype.val : C.finalBase_BAS 0 → _) ∧
      ∀ y, Injective (mfderiv 𝓘(ℝ, ℝ²)
        𝓘(ℝ, BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
        (Subtype.val : C.finalBase_BAS 0 → _) y) :=
  ⟨linearIsManifold_R74 _ _ _ _ _ _ _ _ _ _, contMDiff_linearInclusion_R74 _ _ _ _ _ _ _ _ _ _,
    mfderiv_linearInclusion_injective_R74 _ _ _ _ _ _ _ _ _ _⟩

/-- `W₂` is a smooth manifold of dimension 1 and its inclusion is a smooth immersion. -/
theorem edge_isManifold (A : SmoothStageBasesOn74 C) :
    let _ := A.edgeChartedSpace
    IsManifold 𝓘(ℝ, ℝ) ∞ (C.finalBase_BAS 1) ∧
      ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) ∞
        (Subtype.val : C.finalBase_BAS 1 → _) ∧
      ∀ y, Injective (mfderiv 𝓘(ℝ, ℝ)
        𝓘(ℝ, BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
        (Subtype.val : C.finalBase_BAS 1 → _) y) :=
  ⟨linearIsManifold_R74 _ _ _ _ _ _ _ _ _ _, contMDiff_linearInclusion_R74 _ _ _ _ _ _ _ _ _ _,
    mfderiv_linearInclusion_injective_R74 _ _ _ _ _ _ _ _ _ _⟩

/-- `W₃` is a smooth manifold of dimension 1 and its inclusion is a smooth immersion. -/
theorem slim_isManifold (A : SmoothStageBasesOn74 C) :
    let _ := A.slimChartedSpace
    IsManifold 𝓘(ℝ, ℝ) ∞ (C.finalBase_BAS 2) ∧
      ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) ∞
        (Subtype.val : C.finalBase_BAS 2 → _) ∧
      ∀ y, Injective (mfderiv 𝓘(ℝ, ℝ)
        𝓘(ℝ, BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
        (Subtype.val : C.finalBase_BAS 2 → _) y) :=
  ⟨linearIsManifold_R74 _ _ _ _ _ _ _ _ _ _, contMDiff_linearInclusion_R74 _ _ _ _ _ _ _ _ _ _,
    mfderiv_linearInclusion_injective_R74 _ _ _ _ _ _ _ _ _ _⟩

/-- Row 2: on a native patch, `Θ_st` is the smooth parametrization `Θ ∘ chart_j` after the linear
coordinate `κ_j`, with values in `W₁ ∩ {marked j}` — the later map is a smooth embedding of the
patch (inverse `chart_j ∘ κ_j`). -/
theorem circle_later_embedding (A : SmoothStageBasesOn74 C)
    (j : P.toLocalChartFamily.circle.finite_centres.toFinset) {w : BlockSpace
      (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)} (hw : w ∈ C.circlePatch_BAS j) :
    C.Θ_BAS 0 w = (C.Θ_BAS 0 ∘ A.circleChart j)
        (((ρ j.1)⁻¹ • gafCircleVector P.toLocalChartPackets j) w) ∧
      C.Θ_BAS 0 w ∈ C.finalBase_BAS 0 ∩ markedCondition_BPRE
        (gafCircleVector P.toLocalChartPackets j) (gafCircleMarker P.toLocalChartPackets j)
        (ρ j.1) 1 ∧
      A.circleChart j (((ρ j.1)⁻¹ • gafCircleVector P.toLocalChartPackets j)
        (C.Θ_BAS 0 w)) = w := by
  obtain ⟨hb, hcw⟩ := A.charts.circle_patch j w hw
  have hpar := A.charts.circle_param j _ hb
  rw [hcw] at hpar
  refine ⟨by rw [Function.comp_apply, hcw], hpar.1, ?_⟩
  rw [hpar.2, hcw]

end SmoothStageBasesOn74

attribute [local instance] dihedralTinyMetricSpace_CHI

/-- **Inhabitant on `RP³ # RP³`** (dihedral fixture of lane C14-CHAIN-INST, via
`gaf02Bases_dihedralTiny_BAS`): the enhanced chain of the fixture carries smooth stage bases on
its own chain (the adapter applied to its bases object). The fixture's stage families are empty
(joint satisfiability of every row group, including the empty-family row). -/
theorem smoothStageBases_dihedralTiny_R74 (Kj : ℕ) :
    ∃ (Ξ Γ S eg c cw : Fin 3 → ℝ) (β₂ γc Lmax σs ζ : ℝ) (h : β₂ ≤ 1 / 4)
      (C : Gaf02ChainE (dihedralTinyRowPackets_CHI β₂ γc Lmax σs ζ h) Kj Ξ Γ S eg c cw),
      Nonempty (SmoothStageBasesOn74 C.toChain) := by
  obtain ⟨Ξ, Γ, S, eg, c, cw, β₂, γc, Lmax, σs, ζ, h, C, ⟨B⟩, -⟩ := gaf02Bases_dihedralTiny_BAS Kj
  exact ⟨Ξ, Γ, S, eg, c, cw, β₂, γc, Lmax, σs, ζ, h, C, ⟨B.toSmoothStageBases74⟩⟩

end DifferentialGeometry.Geometry.Collapse
