import DifferentialGeometry.Geometry.Fibration.ActualCfs19RowCFSB

/-!
# CFS19 at the three actual cutoffs of the chain

Blueprint `master207B.tex`, CFS19 (B:3053–3115) and its application remarks (B:3088–3103): the
gates of the first (source), edge (CFS23) and slim (CFS22) formulas vanish outside the ORIGINAL open
threshold-`7` cores (the edge one in both `|η_i|` and `t = η_{E'}`, including the retained-marker
branch; on `{x_ρ > 0}`, which contains the original image). The open cores:

* `cfs19CircleCore_CFSB`: `{p | ∃ j, p ∈ B(c_j, 200ρ_j), ‖η_j(p)‖ < 7}`;
* `cfs19EdgeCore_CFSB`: `{p | ∃ j, p ∈ B(c_j, 100Δρ_j), |η_j(p)| < 7Δ, t(p) < 7Δ}`;
* `cfs19SlimCore_CFSB`: `{p | ∃ j, p ∈ B(c_j, 10⁶Δρ_j), |η_j(p)| < 7·10⁵Δ}`;

each is open, projects into the stage cloud, and contains every original point whose image lies in
the closed support of the stage cutoff. Instances `Gaf02Chain.cfs19_first_CFSB`,
`cfs19_edge_CFSB`, `cfs19_slim_CFSB`: the fixed-data tolerance `κ` (CFS19's first clause) with the
original-core localization and the CFS16 half-tube (second clause).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] LocalChartPackets.instMetricN LocalChartPackets.instChartedN
  LocalChartPackets.instMetricC

section Cores

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc : ℝ}
  {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
  [∀ a, MetricSpace (C a)] {o : ∀ a, C a} {δ εr e T V : ℝ}

variable (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
  (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V)

/-- The ORIGINAL open threshold-`7` circle core. -/
def cfs19CircleCore_CFSB : Set X :=
  {p | ∃ j : L.circle.finite_centres.toFinset, p ∈ ball j.1 (200 * ρ j.1) ∧
    ‖cgpCoord L Z (.inl j) p‖ < 7}

/-- The ORIGINAL open threshold-`7` edge core (both `|η_j|` and `t`). -/
def cfs19EdgeCore_CFSB : Set X :=
  {p | ∃ j : L.edge.finite_centres.toFinset, p ∈ ball j.1 (100 * Δ * ρ j.1) ∧
    |L.edge.coord j.1 p| < 7 * Δ ∧ cgpHeight L p < 7 * Δ}

/-- The ORIGINAL open threshold-`7·10⁵Δ` slim core. -/
def cfs19SlimCore_CFSB : Set X :=
  {p | ∃ j : L.slim.finite_centres.toFinset, p ∈ ball j.1 (10 ^ 6 * Δ * ρ j.1) ∧
    |(L.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord p| < 7 * (10 ^ 5 * Δ)}

theorem isOpen_cfs19CircleCore_CFSB : IsOpen (cfs19CircleCore_CFSB L Z) := by
  have h : cfs19CircleCore_CFSB L Z = ⋃ j : L.circle.finite_centres.toFinset,
      ball j.1 (200 * ρ j.1) ∩ (cgpCoord L Z (.inl j)) ⁻¹' {y | ‖y‖ < 7} := by
    ext p
    simp [cfs19CircleCore_CFSB, mem_iUnion]
  rw [h]
  refine isOpen_iUnion fun j => ?_
  have hj := (Set.Finite.mem_toFinset _).mp j.2
  have hc : ContinuousOn (cgpCoord L Z (.inl j)) (ball j.1 (200 * ρ j.1)) :=
    (cgpCircleCoord_contMDiffOn L hj).continuousOn
  exact hc.isOpen_inter_preimage isOpen_ball (isOpen_lt continuous_norm continuous_const)

theorem isOpen_cfs19EdgeCore_CFSB : IsOpen (cfs19EdgeCore_CFSB L) := by
  have h : cfs19EdgeCore_CFSB L = ⋃ j : L.edge.finite_centres.toFinset,
      (ball j.1 (100 * Δ * ρ j.1) ∩ (L.edge.coord j.1) ⁻¹' {y | |y| < 7 * Δ}) ∩
        (cgpHeight L) ⁻¹' {y | y < 7 * Δ} := by
    ext p
    simp [cfs19EdgeCore_CFSB, mem_iUnion, and_assoc]
  rw [h]
  refine isOpen_iUnion fun j => ?_
  have hj := (Set.Finite.mem_toFinset _).mp j.2
  have hc : ContinuousOn (L.edge.coord j.1) (ball j.1 (100 * Δ * ρ j.1)) :=
    (L.edge.contMDiffOn_coord hj).continuousOn
  exact (hc.isOpen_inter_preimage isOpen_ball (isOpen_lt continuous_abs continuous_const)).inter
    ((isOpen_lt continuous_id continuous_const).preimage (continuous_cgpHeight L))

theorem isOpen_cfs19SlimCore_CFSB : IsOpen (cfs19SlimCore_CFSB L) := by
  have h : cfs19SlimCore_CFSB L = ⋃ j : L.slim.finite_centres.toFinset,
      ball j.1 (10 ^ 6 * Δ * ρ j.1) ∩
        ((L.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord) ⁻¹'
          {y | |y| < 7 * (10 ^ 5 * Δ)} := by
    ext p
    simp [cfs19SlimCore_CFSB, mem_iUnion]
  rw [h]
  refine isOpen_iUnion fun j => ?_
  have hc := (L.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).contMDiffOn_coord.continuousOn
  exact hc.isOpen_inter_preimage isOpen_ball (isOpen_lt continuous_abs continuous_const)

end Cores

namespace Gaf02Chain

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}
  {P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V}
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

/-- **CFS19 at the first (source) cutoff** `ψ₁`: a fixed-data `κ ≤ 3Σ₁/10`; every `f` with
`|f − F| ≤ κρ` has its closed support of `ψ₁` only over the open circle core, with `f(p)` in the
CFS16 half-tube of the original centre. -/
theorem cfs19_first_CFSB (C : Gaf02Chain P Kj Ξ Γ S eg c cw) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 3 * S 0 / 10 ∧
      ∀ f : X → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²),
        (∀ p, ‖f p - cgpGlobalMap P.toLocalChartFamily P.zero p‖ ≤ κ * ρ p) →
      ∀ p, f p ∈ tsupport (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1)
          (gafCircleVector P) (gafCircleMarker P)) →
        p ∈ cfs19CircleCore_CFSB P.toLocalChartFamily P.zero ∧
        (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (f p) ∈
          ball ((gafStageQ P.toLocalChartFamily P.zero 0).starProjection
            (cgpGlobalMap P.toLocalChartFamily P.zero p)) (S 0 * ρ (C.cfs19Sel_CFSB 0 p)) := by
  have cb := C.cutoff_bindings.1
  obtain ⟨κ, hκ, hκS, hrow⟩ := C.cfs19_row_CFSB 0 _ isOpen_univ (fun _ => mem_univ _)
    cb.1.contDiffOn _ (isOpen_cfs19CircleCore_CFSB P.toLocalChartFamily P.zero)
    (fun p hp => gafStage_core_zero_GAF5 P.toLocalChartFamily P.zero p hp)
    (fun p hp => by
      obtain ⟨j, hj, hη⟩ := cb.2.2.2.1 p hp
      exact ⟨j, hj, by linarith⟩)
  refine ⟨κ, hκ, hκS, fun f hf p hp => ?_⟩
  obtain ⟨-, hloc, -, -⟩ := hrow f hf
  have hp' : f p ∈ closure (support (markerLocalitySourceCutoff lc87EdgeTransition
      (fun j => ρ j.1) (gafCircleVector P) (gafCircleMarker P)) ∩ univ) := by
    rw [inter_univ]
    exact hp
  obtain ⟨hA, hd, -⟩ := hloc p hp'
  have hr : 0 < S 0 * ρ (C.cfs19Sel_CFSB 0 p) := mul_pos (C.numbers.1 0).2.1 (hρ _)
  refine ⟨hA, ?_⟩
  rw [mem_ball, dist_eq_norm]
  linarith

/-- **CFS19 at the edge cutoff** `ψ₂` (CFS23, on `O = {x_ρ > 0}`): a fixed-data `κ ≤ 3Σ₂/10`; every
`f` with `|f − F| ≤ κρ` maps into `O`, and its relative closed support of `ψ₂` lies only over the
open edge core, with `f(p)` in the CFS16 half-tube of the original centre. -/
theorem cfs19_edge_CFSB (C : Gaf02Chain P Kj Ξ Γ S eg c cw) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 3 * S 1 / 10 ∧
      ∀ f : X → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²),
        (∀ p, ‖f p - cgpGlobalMap P.toLocalChartFamily P.zero p‖ ≤ κ * ρ p) →
      (∀ p, 0 < gafScaleMarker P.toLocalChartFamily P.zero (f p)) ∧
      ∀ p, f p ∈ closure (support (gafStageTwoCutoff P.toLocalChartFamily P.zero) ∩
          {z | 0 < gafScaleMarker P.toLocalChartFamily P.zero z}) →
        p ∈ cfs19EdgeCore_CFSB P.toLocalChartFamily ∧
        (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (f p) ∈
          ball ((gafStageQ P.toLocalChartFamily P.zero 1).starProjection
            (cgpGlobalMap P.toLocalChartFamily P.zero p)) (S 1 * ρ (C.cfs19Sel_CFSB 1 p)) := by
  obtain ⟨hΛ, hΔ, hμ, hτ, hLΛ, hLmax, he, hT, hσs, hσs1, -⟩ := C.std
  have hopen : IsOpen {z : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) |
      0 < gafScaleMarker P.toLocalChartFamily P.zero z} :=
    isOpen_lt continuous_const (gafScaleMarker P.toLocalChartFamily P.zero).continuous
  have hF0 := gaf02_stageTwo_cutoff P hΛ hΔ hμ hτ hLΛ hLmax he hT hσs hσs1
    (cgpGlobalMap P.toLocalChartFamily P.zero)
    (fun p => by
      rw [sub_self, norm_zero]
      exact mul_nonneg (by have := gafKappa_pos; positivity) (hρ p).le)
    (fun j p h0 => by
      rw [(gafEdge_block_GAF2 P.toLocalChartFamily P.zero j p).2, h0, mul_zero, abs_zero]
      exact div_nonneg (hρ _).le (by norm_num))
  obtain ⟨κ, hκ, hκS, hrow⟩ := C.cfs19_row_CFSB 1 _ hopen
    (fun p => by
      change 0 < gafScaleMarker P.toLocalChartFamily P.zero _
      rw [gafScaleMarker_globalMap_GAF2]
      exact hρ p)
    hF0.1 _ (isOpen_cfs19EdgeCore_CFSB P.toLocalChartFamily)
    (fun p hp => by
      obtain ⟨j, hj, hη, ht⟩ := hp
      exact gafStage_core_one_GAF5 P.toLocalChartFamily P.zero p
        ⟨j, hj, by rw [norm_planeAxis]; exact hη, ht⟩)
    (fun p hp => hF0.2.2.2.1 p hp)
  refine ⟨κ, hκ, hκS, fun f hf => ?_⟩
  obtain ⟨hfO, hloc, -, -⟩ := hrow f hf
  refine ⟨hfO, fun p hp => ?_⟩
  obtain ⟨hA, hd, -⟩ := hloc p hp
  have hr : 0 < S 1 * ρ (C.cfs19Sel_CFSB 1 p) := mul_pos (C.numbers.1 1).2.1 (hρ _)
  refine ⟨hA, ?_⟩
  rw [mem_ball, dist_eq_norm]
  linarith

/-- **CFS19 at the slim cutoff** `ψ₃` (CFS22): a fixed-data `κ ≤ 3Σ₃/10`; every `f` with
`|f − F| ≤ κρ` has its closed support of `ψ₃` only over the open slim core, with `f(p)` in the
CFS16 half-tube of the original centre. -/
theorem cfs19_slim_CFSB (C : Gaf02Chain P Kj Ξ Γ S eg c cw) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 3 * S 2 / 10 ∧
      ∀ f : X → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²),
        (∀ p, ‖f p - cgpGlobalMap P.toLocalChartFamily P.zero p‖ ≤ κ * ρ p) →
      ∀ p, f p ∈ tsupport (gafStageThreeCutoff P.toLocalChartFamily P.zero) →
        p ∈ cfs19SlimCore_CFSB P.toLocalChartFamily ∧
        (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (f p) ∈
          ball ((gafStageQ P.toLocalChartFamily P.zero 2).starProjection
            (cgpGlobalMap P.toLocalChartFamily P.zero p)) (S 2 * ρ (C.cfs19Sel_CFSB 2 p)) := by
  obtain ⟨hΛ, hΔ, hμ, hτ, hLΛ, hLmax, he, hT, hσs, hσs1, -⟩ := C.std
  have hF0 := gaf02_stageThree_cutoff P hΛ hΔ hμ hτ hLΛ hLmax he hT hσs hσs1
    (cgpGlobalMap P.toLocalChartFamily P.zero)
    (fun p => by
      rw [sub_self, norm_zero]
      exact mul_nonneg (by have := gafKappa_pos; positivity) (hρ p).le)
    (fun j p h0 => by
      rw [(gafSlim_block_GAF2 P.toLocalChartFamily P.zero j p).2, h0, mul_zero, abs_zero]
      exact div_nonneg (hρ _).le (by norm_num))
  have h6 : (10 : ℝ) ^ 6 = 1000000 := by norm_num
  obtain ⟨κ, hκ, hκS, hrow⟩ := C.cfs19_row_CFSB 2 _ isOpen_univ (fun _ => mem_univ _)
    hF0.1.contDiffOn _ (isOpen_cfs19SlimCore_CFSB P.toLocalChartFamily)
    (fun p hp => by
      obtain ⟨j, hj, hη⟩ := hp
      rw [h6] at hj
      exact gafStage_core_two_GAF5 P.toLocalChartFamily P.zero p
        ⟨j, hj, by rw [norm_planeAxis]; exact hη⟩)
    (fun p hp => by
      obtain ⟨j, hj, hη⟩ := hF0.2.2.2.1 p hp
      refine ⟨j, ?_, hη⟩
      rw [h6]
      exact hj)
  refine ⟨κ, hκ, hκS, fun f hf p hp => ?_⟩
  obtain ⟨-, hloc, -, -⟩ := hrow f hf
  have hp' : f p ∈ closure (support (gafStageThreeCutoff P.toLocalChartFamily P.zero) ∩ univ) := by
    rw [inter_univ]
    exact hp
  obtain ⟨hA, hd, -⟩ := hloc p hp'
  have hr : 0 < S 2 * ρ (C.cfs19Sel_CFSB 2 p) := mul_pos (C.numbers.1 2).2.1 (hρ _)
  refine ⟨hA, ?_⟩
  rw [mem_ball, dist_eq_norm]
  linarith

end Gaf02Chain

end DifferentialGeometry.Geometry.Collapse
