import DifferentialGeometry.Geometry.Fibration.ActualStageChain
import DifferentialGeometry.Geometry.Fibration.ActualFreezeScale

/-!
# EDP02–EDP03 on the chain object: the final edge quantities against the original ones

Lane C14-EDP-E. Blueprint `master207B.tex`, EDP02 (`lem:fibration-actual-edge-height-localization`,
B:6748–6835) and EDP03 (`lem:fibration-edge-original-buffer-and-height`, B:6837–6947), the clauses
that read the FINAL map `E` of GAF02 CORE. Everything is stated on ONE chain
`C : Gaf02Chain P Kj Ξ Γ S eg c cw` (lane C14-GAF8b; reusable through `Gaf02ChainE.toChain`), with
its own `E = C.E` and `s = C.scale`; no map is chosen again.

Conventions. `A = u_{E'}(E)` is the scalar coordinate of the `E'` block on FC01's axis,
`A p = proj₀ (gafHeightVector (E p))`; at `𝓔⁰` it is the original weak-edge vector
`A⁰ = ρ z₀ t = z₀ P` (`P = edge.smoothing`, `t = P/ρ`, `z₀ = cgpEdgeMarker`).
`u_j = proj₀ ∘ gafEdgeVector j`, `g_j = u_j(E)/R_j`, `R_j = ρ(j)`; at `𝓔⁰`, `u_j = R_j ζ_j η_j`.
`T = A/s`. Blueprint `c₃` is the chain's `c 2` (`‖E − 𝓔⁰‖ < c₃ρ`, derivative budget `H < c₃`).

* E-free block facts: `globalMap_heightAxis_EDPE` (`A⁰ = z₀P`), `globalMap_edgeAxis_EDPE`
  (`u_j(𝓔⁰) = R_jζ_jη_j`), `edge_cutoff_eq_one_EDPE` (`ζ_j = 1` on `{|η_j| < 8Δ, t ≤ 8Δ}` in the
  chart ball), `edgeMarker_eq_one_EDPE` (`z₀ = 1` there on `.3Δ ≤ t`), `isOpen_edgeBand_EDPE`,
  `scale_ratio_ball_EDPE` (`|ρ/R_j − 1| ≤ 100ΔΛ`).
* On the chain: `Gaf02Chain.accuracy_order_EDPE` (`0 < c₁ < c₂ < c₃`), `globalMap_smooth_EDPE`,
  `final_smooth_EDPE` (`A`, `s > 0`, `T`, every `g_j` smooth on `X`), `heightAxis_value_EDPE`
  ((AE) value: `|A − z₀P| < c₃ρ`, `A < P + c₃ρ`), `edgeAxis_value_EDPE` ((ETan) value:
  `|g_j − η_j| < c₃ρ/R_j ≤ 5c₃/4` on the threshold-8 part), `final_derivative_EDPE` ((AE) and
  (ETan) derivatives with ONE budget `H < c₃`; `dA⁰ = dP` on the OPEN band `.3Δ < t < 8Δ`),
  `low_branch_EDPE` (`t ≤ 3.5Δ ⇒ T < 4Δ`, `t < .3Δ ⇒ T < .31Δ`, and the vertical set of (ED)
  `{t ≤ .35Δ} ∪ {s > 0, T ≤ 4Δ} = {T ≤ 4Δ}` on all of `X`).

Deviation: the (AE) DERIVATIVE clause is stated on the open band `.3Δ < t` (where `z₀ ≡ 1` near the
point); at the single level `t = .3Δ` only the value clause is given. Not here (sheet
`state-C14-EDP-E.md`): GAF05's coordinate patch and exact marker, EDP02's (ELoc) and base
membership, CGP08's `Θ₂`.
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

attribute [local instance] nezero_finrank_euclideanThree_LC87

section Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem mvfderiv_clm_comp_apply_EDPE (ℓ : F →L[ℝ] G) {f : M → F} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, F) f x) (v : TangentSpace I x) :
    mvfderiv I (fun y => ℓ (f y)) x v = ℓ (mvfderiv I f x v) := by
  have hh := _root_.mvfderiv_comp_apply x ℓ.differentiableAt.mdifferentiableAt hf v
  rw [mvfderiv_eq_fderiv, ℓ.fderiv] at hh
  exact hh

theorem mvfderiv_congr_EDPE {f f' : M → F} {x : M} (h : f =ᶠ[𝓝 x] f') :
    mvfderiv I f x = mvfderiv I f' x := by
  unfold mvfderiv
  rw [h.mfderiv_eq, h.eq_of_nhds]
  rfl

end Calculus

theorem proj_planeAxis_EDPE (t : ℝ) : EuclideanSpace.proj (0 : Fin 2) (planeAxis t) = t := by
  simp [planeAxis_apply]

theorem norm_proj_blockVector_le_EDPE {κ : Type*} [Fintype κ] (t : κ)
    (y : BlockSpace (fun _ : κ => ℝ²)) :
    |EuclideanSpace.proj (0 : Fin 2) (blockVectorCLM (V := fun _ : κ => ℝ²) t y)| ≤ ‖y‖ := by
  have h1 : ‖EuclideanSpace.proj (0 : Fin 2) (blockVectorCLM (V := fun _ : κ => ℝ²) t y)‖ ≤
      ‖blockVectorCLM (V := fun _ : κ => ℝ²) t y‖ := by
    have := (EuclideanSpace.proj (0 : Fin 2) : ℝ² →L[ℝ] ℝ).le_opNorm
      (blockVectorCLM (V := fun _ : κ => ℝ²) t y)
    refine this.trans ?_
    have hn : ‖(EuclideanSpace.proj (0 : Fin 2) : ℝ² →L[ℝ] ℝ)‖ ≤ 1 := by
      refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
      rw [one_mul]
      simpa using PiLp.norm_apply_le v (0 : Fin 2)
    calc _ ≤ 1 * ‖blockVectorCLM (V := fun _ : κ => ℝ²) t y‖ :=
          mul_le_mul_of_nonneg_right hn (norm_nonneg _)
      _ = _ := one_mul _
  have h2 := (blockVectorCLM (V := fun _ : κ => ℝ²) t).le_opNorm y
  have h3 := norm_blockVectorCLM_le (V := fun _ : κ => ℝ²) t
  rw [Real.norm_eq_abs] at h1
  nlinarith [norm_nonneg y, norm_nonneg (blockVectorCLM (V := fun _ : κ => ℝ²) t)]


section Family

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}

/-- The model metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricN_EDPE
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPackets`, as a named local instance. -/
local instance instChartedN_EDPE
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricC_EDPE
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- The `E'` block of `𝓔⁰` on FC01's axis: `A⁰ = ρ z₀ t = z₀ P`. -/
theorem globalMap_heightAxis_EDPE
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (p : X) :
    EuclideanSpace.proj (0 : Fin 2) (gafHeightVector P.toLocalChartFamily P.zero
        (cgpGlobalMap P.toLocalChartFamily P.zero p)) =
      cgpEdgeMarker P.toLocalChartFamily p * P.edge.smoothing p := by
  change EuclideanSpace.proj (0 : Fin 2) ((ρ p * cgpEdgeMarker P.toLocalChartFamily p) •
    planeAxis (cgpHeight P.toLocalChartFamily p)) = _
  rw [map_smul, proj_planeAxis_EDPE, smul_eq_mul, cgpHeight]
  have := hρ p
  field_simp

/-- The edge block of `𝓔⁰` on FC01's axis: `u_j(𝓔⁰) = R_j ζ_j η_j`. -/
theorem globalMap_edgeAxis_EDPE
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (j : P.edge.finite_centres.toFinset) (p : X) :
    EuclideanSpace.proj (0 : Fin 2) (gafEdgeVector P.toLocalChartFamily P.zero j
        (cgpGlobalMap P.toLocalChartFamily P.zero p)) =
      ρ j.1 * P.edge.cutoff j.1 p * P.edge.coord j.1 p := by
  rw [(gafEdge_block_GAF2 P.toLocalChartFamily P.zero j p).1, map_smul, proj_planeAxis_EDPE,
    smul_eq_mul]

/-- On the threshold-8 part of the chart ball the actual edge cutoff is one. -/
theorem edge_cutoff_eq_one_EDPE
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΔ : 0 < Δ) {j : X} (hj : j ∈ P.edge.centres) {p : X} (hp : p ∈ ball j (100 * Δ * ρ j))
    (hη : |P.edge.coord j p| < 8 * Δ) (ht : P.edge.smoothing p / ρ p ≤ 8 * Δ) :
    P.edge.cutoff j p = 1 := by
  rw [cgp01_edge_identity P.toLocalChartFamily hj hp hη hΔ]
  have h0 : cfsRamp lc87EdgeTransition 8 9 (cgpHeight P.toLocalChartFamily p / Δ) = 0 := by
    refine cfsRamp_eq_zero (fun y hy => lc87EdgeTransition_eq_zero hy) (by norm_num) ?_
    rw [cgpHeight, div_le_iff₀ hΔ]
    linarith
  rw [h0, sub_zero]

/-- On the band `.3Δ ≤ t ≤ 8Δ` of the threshold-8 part of the chart ball the `E'` marker is one. -/
theorem edgeMarker_eq_one_EDPE
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΔ : 0 < Δ) {j : X} (hj : j ∈ P.edge.centres) {p : X} (hp : p ∈ ball j (100 * Δ * ρ j))
    (hη : |P.edge.coord j p| < 8 * Δ) (ht3 : 3 / 10 * Δ ≤ P.edge.smoothing p / ρ p)
    (ht : P.edge.smoothing p / ρ p ≤ 8 * Δ) :
    cgpEdgeMarker P.toLocalChartFamily p = 1 := by
  have hζ := edge_cutoff_eq_one_EDPE P hΔ hj hp hη ht
  have hsum : 1 ≤ cgpEdgeSum P.toLocalChartFamily p := by
    unfold cgpEdgeSum
    have hjF : j ∈ P.edge.finite_centres.toFinset := (Set.Finite.mem_toFinset _).mpr hj
    have h := Finset.single_le_sum (f := fun i : P.edge.finite_centres.toFinset =>
      P.edge.cutoff i.1 p) (fun i _ => (cgpEdgeCutoff_mem_Icc P.toLocalChartFamily hΔ i.1 p).1)
      (Finset.mem_univ ⟨j, hjF⟩)
    simp only at h
    rw [hζ] at h
    exact h
  have hH : cgpEdgeH (cgpHeight P.toLocalChartFamily p / Δ) = 1 := by
    have h3 : 3 / 10 ≤ cgpHeight P.toLocalChartFamily p / Δ := by
      rw [cgpHeight, le_div_iff₀ hΔ]
      linarith
    rw [cgpEdgeH_eq_of_le h3]
    have h0 : cfsRamp lc87EdgeTransition 8 9 (cgpHeight P.toLocalChartFamily p / Δ) = 0 := by
      refine cfsRamp_eq_zero (fun y hy => lc87EdgeTransition_eq_zero hy) (by norm_num) ?_
      rw [cgpHeight, div_le_iff₀ hΔ]
      linarith
    rw [h0, sub_zero]
  rw [cgpEdgeMarker, hH, one_mul]
  exact cfsRamp_eq_one (fun y hy => lc87EdgeTransition_eq_one hy) (by norm_num) hsum

/-- The open bands `{p ∈ B(j, 100Δρ(j)) : |η_j| < a, a' < t < c'}` of the chart ball. -/
theorem isOpen_edgeBand_EDPE
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    {j : X} (hj : j ∈ P.edge.centres) (a a' c' : ℝ) :
    IsOpen {p | p ∈ ball j (100 * Δ * ρ j) ∧ |P.edge.coord j p| < a ∧
      a' < P.edge.smoothing p / ρ p ∧ P.edge.smoothing p / ρ p < c'} := by
  have hη : IsOpen (ball j (100 * Δ * ρ j) ∩ P.edge.coord j ⁻¹' Ioo (-a) a) :=
    (P.edge.contMDiffOn_coord hj).continuousOn.isOpen_inter_preimage isOpen_ball isOpen_Ioo
  have ht : IsOpen ((fun p => P.edge.smoothing p / ρ p) ⁻¹' Ioo a' c') :=
    isOpen_Ioo.preimage (continuous_cgpHeight P.toLocalChartFamily)
  convert hη.inter ht using 1
  ext p
  simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_Ioo, abs_lt]
  tauto


/-- The scale ratio on the chart ball: `|ρ(p)/ρ(j) − 1| ≤ 100ΔΛ`. -/
theorem scale_ratio_ball_EDPE
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΛ : 0 ≤ Λ) {j p : X} (hp : p ∈ ball j (100 * Δ * ρ j)) :
    |ρ p / ρ j - 1| ≤ 100 * Δ * Λ := by
  have hrj := hρ j
  have hd : dist p j < 100 * Δ * ρ j := mem_ball.mp hp
  have hlip : |ρ p - ρ j| ≤ Λ * dist p j := by
    have h := P.lipschitz_scale.dist_le_mul p j
    rwa [Real.coe_toNNReal _ hΛ, Real.dist_eq] at h
  have hrw : ρ p / ρ j - 1 = (ρ p - ρ j) / ρ j := by field_simp
  rw [hrw, abs_div, abs_of_pos hrj, div_le_iff₀ hrj]
  nlinarith [dist_nonneg (x := p) (y := j)]

end Family

namespace Gaf02Chain

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}
  {P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V}
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

/-- The model metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricN_EDPE'
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPackets`, as a named local instance. -/
local instance instChartedN_EDPE'
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricC_EDPE'
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- The chain's cumulative accuracies are ordered and positive: `0 < c₁ < c₂ < c₃`. -/
theorem accuracy_order_EDPE (C : Gaf02Chain P Kj Ξ Γ S eg c cw) :
    0 < c 0 ∧ c 0 < c 1 ∧ c 1 < c 2 := by
  obtain ⟨hnum, hv₁, -, -, -, -, hv₂, -, -, -, -, hv₃, -, -⟩ := C.numbers
  obtain ⟨hΞ₀, hS₀, -, -⟩ := hnum 0
  obtain ⟨hΞ₁, hS₁, -, -⟩ := hnum 1
  obtain ⟨hΞ₂, hS₂, -, -⟩ := hnum 2
  have h0 : 0 < c 0 := by
    have : 0 < 5 / 3 * Ξ 0 * S 0 := by positivity
    linarith
  have h1 : c 0 < c 1 := by
    have : 0 < 5 / 3 * Ξ 1 * S 1 := by positivity
    have : 0 < (1 + Ξ 1) * c 0 := mul_pos (by linarith) h0
    linarith
  have h2 : c 1 < c 2 := by
    have : 0 < 5 / 3 * Ξ 2 * S 2 := by positivity
    have : 0 < (1 + Ξ 2) * c 1 := mul_pos (by linarith) (by linarith)
    linarith
  exact ⟨h0, h1, h2⟩

/-- **Smoothness of the final quantities** (EDP03: `g_i`, `T` smooth; EDP02: `s > 0`): the `E'`
axis coordinate `A = u_{E'}(E)`, the scale `s = ℓ_ρ(E)`, the height `T = A/s` and every edge
coordinate `g_j = u_j(E)/R_j` are smooth on all of `X`, and `s > 0`. -/
theorem final_smooth_EDPE (C : Gaf02Chain P Kj Ξ Γ S eg c cw) :
    ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (fun p => EuclideanSpace.proj (0 : Fin 2)
      (gafHeightVector P.toLocalChartFamily P.zero (C.E p))) ∧
    ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ C.scale ∧ (∀ p, 0 < C.scale p) ∧
    ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (fun p => EuclideanSpace.proj (0 : Fin 2)
      (gafHeightVector P.toLocalChartFamily P.zero (C.E p)) / C.scale p) ∧
    ∀ j : P.edge.finite_centres.toFinset, ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (fun p =>
      EuclideanSpace.proj (0 : Fin 2) (gafEdgeVector P.toLocalChartFamily P.zero j (C.E p)) /
        ρ j.1) := by
  have hE := C.stage_smooth.2.2
  have hA : ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (fun p => EuclideanSpace.proj (0 : Fin 2)
      (gafHeightVector P.toLocalChartFamily P.zero (C.E p))) :=
    ((EuclideanSpace.proj (0 : Fin 2)).comp
      (gafHeightVector P.toLocalChartFamily P.zero)).contDiff.contMDiff.comp hE
  have hs : ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ C.scale :=
    (gafScaleMarker P.toLocalChartFamily P.zero).contDiff.contMDiff.comp hE
  refine ⟨hA, hs, fun p => (C.scale_pos p).2, hA.div₀ hs fun p => (C.scale_pos p).2.ne',
    fun j => ?_⟩
  exact (((EuclideanSpace.proj (0 : Fin 2)).comp
    (gafEdgeVector P.toLocalChartFamily P.zero j)).contDiff.contMDiff.comp hE).div_const _


/-- **(AE), value, everywhere**: `|A − z₀ P| < c₃ρ` for `A = u_{E'}(E)` (`A⁰ = z₀ P` is the
original weak-edge vector), hence `A < P + c₃ρ`. -/
theorem heightAxis_value_EDPE (C : Gaf02Chain P Kj Ξ Γ S eg c cw) (p : X) :
    |EuclideanSpace.proj (0 : Fin 2) (gafHeightVector P.toLocalChartFamily P.zero (C.E p)) -
        cgpEdgeMarker P.toLocalChartFamily p * P.edge.smoothing p| < c 2 * ρ p ∧
      EuclideanSpace.proj (0 : Fin 2) (gafHeightVector P.toLocalChartFamily P.zero (C.E p)) <
        P.edge.smoothing p + c 2 * ρ p := by
  have hb := norm_proj_blockVector_le_EDPE (cgpEdgeTag P.toLocalChartFamily P.zero)
    (C.E p - cgpGlobalMap P.toLocalChartFamily P.zero p)
  have herr := C.stage_error_lt.2.2 p
  have h1 : |EuclideanSpace.proj (0 : Fin 2) (gafHeightVector P.toLocalChartFamily P.zero (C.E p)) -
      cgpEdgeMarker P.toLocalChartFamily p * P.edge.smoothing p| < c 2 * ρ p := by
    rw [← globalMap_heightAxis_EDPE P p, ← map_sub, ← map_sub]
    exact lt_of_le_of_lt hb herr
  refine ⟨h1, ?_⟩
  have hz := cgpEdgeMarker_mem_Icc P.toLocalChartFamily p
  have hF := P.edge.smoothing_nonneg p
  have hzF : cgpEdgeMarker P.toLocalChartFamily p * P.edge.smoothing p ≤ P.edge.smoothing p := by
    nlinarith [hz.2]
  have := (abs_lt.mp h1).2
  linarith

/-- **(ETan), value, everywhere**: `|u_j(E) − R_jζ_jη_j| < c₃ρ`; on the threshold-8 part of the
chart ball (`ζ_j = 1`), `|g_j − η_j| < c₃ρ/R_j ≤ 5c₃/4` for `g_j = u_j(E)/R_j`. -/
theorem edgeAxis_value_EDPE (C : Gaf02Chain P Kj Ξ Γ S eg c cw)
    (j : P.edge.finite_centres.toFinset) (p : X) :
    |EuclideanSpace.proj (0 : Fin 2) (gafEdgeVector P.toLocalChartFamily P.zero j (C.E p)) -
        ρ j.1 * P.edge.cutoff j.1 p * P.edge.coord j.1 p| < c 2 * ρ p ∧
      (p ∈ ball j.1 (100 * Δ * ρ j.1) → |P.edge.coord j.1 p| < 8 * Δ →
        P.edge.smoothing p / ρ p ≤ 8 * Δ →
        |EuclideanSpace.proj (0 : Fin 2) (gafEdgeVector P.toLocalChartFamily P.zero j (C.E p)) /
            ρ j.1 - P.edge.coord j.1 p| < c 2 * (ρ p / ρ j.1) ∧
        |EuclideanSpace.proj (0 : Fin 2) (gafEdgeVector P.toLocalChartFamily P.zero j (C.E p)) /
            ρ j.1 - P.edge.coord j.1 p| < 5 / 4 * c 2) := by
  obtain ⟨hΛ, hΔ, -, -, hLΛ, -⟩ := C.std
  have hΔ0 : 0 < Δ := by linarith
  have hb := norm_proj_blockVector_le_EDPE (cgpEdgeBlockTag P.toLocalChartFamily P.zero j)
    (C.E p - cgpGlobalMap P.toLocalChartFamily P.zero p)
  have herr := C.stage_error_lt.2.2 p
  have h1 : |EuclideanSpace.proj (0 : Fin 2) (gafEdgeVector P.toLocalChartFamily P.zero j (C.E p)) -
      ρ j.1 * P.edge.cutoff j.1 p * P.edge.coord j.1 p| < c 2 * ρ p := by
    rw [← globalMap_edgeAxis_EDPE P j p, ← map_sub, ← map_sub]
    exact lt_of_le_of_lt hb herr
  refine ⟨h1, fun hp hη ht => ?_⟩
  have hj := (Set.Finite.mem_toFinset _).mp j.2
  have hζ := edge_cutoff_eq_one_EDPE P hΔ0 hj hp hη ht
  rw [hζ, mul_one] at h1
  have hrj := hρ j.1
  have hrw : EuclideanSpace.proj (0 : Fin 2) (gafEdgeVector P.toLocalChartFamily P.zero j (C.E p)) /
      ρ j.1 - P.edge.coord j.1 p = (EuclideanSpace.proj (0 : Fin 2)
        (gafEdgeVector P.toLocalChartFamily P.zero j (C.E p)) - ρ j.1 * P.edge.coord j.1 p) /
          ρ j.1 := by
    field_simp
  have h2 : |EuclideanSpace.proj (0 : Fin 2) (gafEdgeVector P.toLocalChartFamily P.zero j (C.E p)) /
      ρ j.1 - P.edge.coord j.1 p| < c 2 * (ρ p / ρ j.1) := by
    rw [hrw, abs_div, abs_of_pos hrj, div_lt_iff₀ hrj]
    calc _ < c 2 * ρ p := h1
      _ = c 2 * (ρ p / ρ j.1) * ρ j.1 := by field_simp
  refine ⟨h2, lt_of_lt_of_le h2 ?_⟩
  have hq := scale_ratio_ball_EDPE P hΛ hp
  have hc := (C.accuracy_order_EDPE)
  have hq1 : ρ p / ρ j.1 ≤ 5 / 4 := by
    have := (abs_le.mp hq).2
    nlinarith
  have hc2 : 0 ≤ c 2 := by linarith [hc.1, hc.2.1, hc.2.2]
  have := mul_le_mul_of_nonneg_left hq1 hc2
  linarith


/-- `𝓔⁰` is smooth (CGP01 with the packet margin, from the chain's packet hypotheses). -/
theorem globalMap_smooth_EDPE (C : Gaf02Chain P Kj Ξ Γ S eg c cw) :
    ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) ∞
      (cgpGlobalMap P.toLocalChartFamily P.zero) := by
  obtain ⟨hΛ, hΔ, hμ, hτ, hLΛ, -, he, -⟩ := C.std
  have hΔΛ : 100 * Δ * Λ ≤ 1 / 100 := by nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ Δ) hΛ]
  exact cgp01_rowE P.toLocalChartFamilyE P.zero hΛ (by linarith) hμ hτ hΔΛ (by linarith)

/-- **(AE) and (ETan), derivatives** (EDP03, B:6857–6860 and the proof's normalized (AE)): ONE
budget `H < c₃` (GAF02 CORE's) with `|dA(W) − dA⁰(W)| ≤ H|W|_g` and
`|du_j(E)(W) − du_j(𝓔⁰)(W)| ≤ H|W|_g` everywhere (`A⁰ = z₀P`, `u_j(𝓔⁰) = R_jζ_jη_j`); on the open
band `{p ∈ B(j, 100Δρ(j)) : |η_j| < 8Δ, .3Δ < t < 8Δ}`, `|dA(W) − dP(W)| ≤ H|W|_g`; on the open
threshold-8 part `{|η_j| < 8Δ, t < 8Δ}` of the chart ball, `|dg_j(W) − dη_j(W)| ≤ H √(R_j⁻²g(W,W))`
for `g_j = u_j(E)/R_j`. -/
theorem final_derivative_EDPE (C : Gaf02Chain P Kj Ξ Γ S eg c cw) :
    ∃ Hd : ℝ, Hd < c 2 ∧
      (∀ p (W : TangentSpace 𝓘(ℝ, E3) p),
        |mvfderiv 𝓘(ℝ, E3) (fun y => EuclideanSpace.proj (0 : Fin 2)
            (gafHeightVector P.toLocalChartFamily P.zero (C.E y))) p W -
          mvfderiv 𝓘(ℝ, E3) (fun y => cgpEdgeMarker P.toLocalChartFamily y * P.edge.smoothing y)
            p W| ≤ Hd * Real.sqrt (g.inner p W W)) ∧
      (∀ (j : P.edge.finite_centres.toFinset) p (W : TangentSpace 𝓘(ℝ, E3) p),
        |mvfderiv 𝓘(ℝ, E3) (fun y => EuclideanSpace.proj (0 : Fin 2)
            (gafEdgeVector P.toLocalChartFamily P.zero j (C.E y))) p W -
          mvfderiv 𝓘(ℝ, E3) (fun y => ρ j.1 * P.edge.cutoff j.1 y * P.edge.coord j.1 y) p W| ≤
          Hd * Real.sqrt (g.inner p W W)) ∧
      (∀ (j : P.edge.finite_centres.toFinset) p, p ∈ ball j.1 (100 * Δ * ρ j.1) →
        |P.edge.coord j.1 p| < 8 * Δ → 3 / 10 * Δ < P.edge.smoothing p / ρ p →
        P.edge.smoothing p / ρ p < 8 * Δ → ∀ W : TangentSpace 𝓘(ℝ, E3) p,
        |mvfderiv 𝓘(ℝ, E3) (fun y => EuclideanSpace.proj (0 : Fin 2)
            (gafHeightVector P.toLocalChartFamily P.zero (C.E y))) p W -
          mvfderiv 𝓘(ℝ, E3) P.edge.smoothing p W| ≤ Hd * Real.sqrt (g.inner p W W)) ∧
      ∀ (j : P.edge.finite_centres.toFinset) p, p ∈ ball j.1 (100 * Δ * ρ j.1) →
        |P.edge.coord j.1 p| < 8 * Δ → P.edge.smoothing p / ρ p < 8 * Δ →
        ∀ W : TangentSpace 𝓘(ℝ, E3) p,
        |mvfderiv 𝓘(ℝ, E3) (fun y => EuclideanSpace.proj (0 : Fin 2)
            (gafEdgeVector P.toLocalChartFamily P.zero j (C.E y)) / ρ j.1) p W -
          mvfderiv 𝓘(ℝ, E3) (P.edge.coord j.1) p W| ≤
          Hd * Real.sqrt ((ρ j.1)⁻¹ ^ 2 * g.inner p W W) := by
  obtain ⟨hΛ, hΔ, -⟩ := C.std
  have hΔ0 : 0 < Δ := by linarith
  obtain ⟨Hd, hHd, hder⟩ := C.stage_derivative_lt.2.2
  have hE := C.stage_smooth.2.2
  have hF := C.globalMap_smooth_EDPE
  -- the two composite derivatives
  have hA : ∀ p (W : TangentSpace 𝓘(ℝ, E3) p),
      |mvfderiv 𝓘(ℝ, E3) (fun y => EuclideanSpace.proj (0 : Fin 2)
          (gafHeightVector P.toLocalChartFamily P.zero (C.E y))) p W -
        mvfderiv 𝓘(ℝ, E3) (fun y => EuclideanSpace.proj (0 : Fin 2)
          (gafHeightVector P.toLocalChartFamily P.zero
            (cgpGlobalMap P.toLocalChartFamily P.zero y))) p W| ≤
        Hd * Real.sqrt (g.inner p W W) := by
    intro p W
    have h1 := mvfderiv_clm_comp_apply_EDPE ((EuclideanSpace.proj (0 : Fin 2)).comp
      (gafHeightVector P.toLocalChartFamily P.zero)) ((hE p).mdifferentiableAt (by simp)) W
    have h2 := mvfderiv_clm_comp_apply_EDPE ((EuclideanSpace.proj (0 : Fin 2)).comp
      (gafHeightVector P.toLocalChartFamily P.zero)) ((hF p).mdifferentiableAt (by simp)) W
    simp only [ContinuousLinearMap.comp_apply] at h1 h2
    rw [h1, h2, ← map_sub, ← map_sub]
    exact (norm_proj_blockVector_le_EDPE (cgpEdgeTag P.toLocalChartFamily P.zero) _).trans
      (hder p W)
  have hU : ∀ (j : P.edge.finite_centres.toFinset) p (W : TangentSpace 𝓘(ℝ, E3) p),
      |mvfderiv 𝓘(ℝ, E3) (fun y => EuclideanSpace.proj (0 : Fin 2)
          (gafEdgeVector P.toLocalChartFamily P.zero j (C.E y))) p W -
        mvfderiv 𝓘(ℝ, E3) (fun y => EuclideanSpace.proj (0 : Fin 2)
          (gafEdgeVector P.toLocalChartFamily P.zero j
            (cgpGlobalMap P.toLocalChartFamily P.zero y))) p W| ≤
        Hd * Real.sqrt (g.inner p W W) := by
    intro j p W
    have h1 := mvfderiv_clm_comp_apply_EDPE ((EuclideanSpace.proj (0 : Fin 2)).comp
      (gafEdgeVector P.toLocalChartFamily P.zero j)) ((hE p).mdifferentiableAt (by simp)) W
    have h2 := mvfderiv_clm_comp_apply_EDPE ((EuclideanSpace.proj (0 : Fin 2)).comp
      (gafEdgeVector P.toLocalChartFamily P.zero j)) ((hF p).mdifferentiableAt (by simp)) W
    simp only [ContinuousLinearMap.comp_apply] at h1 h2
    rw [h1, h2, ← map_sub, ← map_sub]
    exact (norm_proj_blockVector_le_EDPE (cgpEdgeBlockTag P.toLocalChartFamily P.zero j) _).trans
      (hder p W)
  have hAfun : (fun y => EuclideanSpace.proj (0 : Fin 2)
      (gafHeightVector P.toLocalChartFamily P.zero (cgpGlobalMap P.toLocalChartFamily P.zero y))) =
      fun y => cgpEdgeMarker P.toLocalChartFamily y * P.edge.smoothing y :=
    funext fun y => globalMap_heightAxis_EDPE P y
  have hUfun : ∀ j : P.edge.finite_centres.toFinset, (fun y => EuclideanSpace.proj (0 : Fin 2)
      (gafEdgeVector P.toLocalChartFamily P.zero j (cgpGlobalMap P.toLocalChartFamily P.zero y))) =
      fun y => ρ j.1 * P.edge.cutoff j.1 y * P.edge.coord j.1 y :=
    fun j => funext fun y => globalMap_edgeAxis_EDPE P j y
  refine ⟨Hd, hHd, fun p W => ?_, fun j p W => ?_, fun j p hp hη ht3 ht8 W => ?_,
    fun j p hp hη ht8 W => ?_⟩
  · rw [← hAfun]
    exact hA p W
  · rw [← hUfun j]
    exact hU j p W
  · have hj := (Set.Finite.mem_toFinset _).mp j.2
    have hopen := isOpen_edgeBand_EDPE P hj (8 * Δ) (3 / 10 * Δ) (8 * Δ)
    have hev : (fun y => cgpEdgeMarker P.toLocalChartFamily y * P.edge.smoothing y) =ᶠ[𝓝 p]
        P.edge.smoothing := by
      filter_upwards [hopen.mem_nhds ⟨hp, hη, ht3, ht8⟩] with y hy
      rw [edgeMarker_eq_one_EDPE P hΔ0 hj hy.1 hy.2.1 hy.2.2.1.le hy.2.2.2.le, one_mul]
    rw [← mvfderiv_congr_EDPE hev, ← hAfun]
    exact hA p W
  · have hj := (Set.Finite.mem_toFinset _).mp j.2
    have hopen := isOpen_edgeBand_EDPE P hj (8 * Δ) (-1) (8 * Δ)
    have ht0 : (-1 : ℝ) < P.edge.smoothing p / ρ p := by
      have := div_nonneg (P.edge.smoothing_nonneg p) (hρ p).le
      linarith
    have hev : (fun y => ρ j.1 * P.edge.cutoff j.1 y * P.edge.coord j.1 y) =ᶠ[𝓝 p]
        fun y => ρ j.1 * P.edge.coord j.1 y := by
      filter_upwards [hopen.mem_nhds ⟨hp, hη, ht0, ht8⟩] with y hy
      rw [edge_cutoff_eq_one_EDPE P hΔ0 hj hy.1 hy.2.1 hy.2.2.2.le, mul_one]
    have hηd : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (P.edge.coord j.1) p :=
      ((P.edge.contMDiffOn_coord hj).contMDiffAt (isOpen_ball.mem_nhds hp)).mdifferentiableAt
        (by simp)
    have hud : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (fun y => EuclideanSpace.proj (0 : Fin 2)
        (gafEdgeVector P.toLocalChartFamily P.zero j (C.E y))) p :=
      ((((EuclideanSpace.proj (0 : Fin 2)).comp
        (gafEdgeVector P.toLocalChartFamily P.zero j)).contDiff.contMDiff.comp hE)
          p).mdifferentiableAt (by simp)
    have h1 := hU j p W
    rw [hUfun j, mvfderiv_congr_EDPE hev, mvfderiv_const_mul _ _ hηd] at h1
    rw [mvfderiv_div_const_FC19 hud, sqrt_inv_sq_mul_FC19 (hρ j.1)]
    have hrj := hρ j.1
    have hrw : (ρ j.1)⁻¹ * mvfderiv 𝓘(ℝ, E3) (fun y => EuclideanSpace.proj (0 : Fin 2)
        (gafEdgeVector P.toLocalChartFamily P.zero j (C.E y))) p W -
        mvfderiv 𝓘(ℝ, E3) (P.edge.coord j.1) p W = (ρ j.1)⁻¹ * (mvfderiv 𝓘(ℝ, E3)
          (fun y => EuclideanSpace.proj (0 : Fin 2)
            (gafEdgeVector P.toLocalChartFamily P.zero j (C.E y))) p W -
          (ρ j.1 • mvfderiv 𝓘(ℝ, E3) (P.edge.coord j.1) p) W) := by
      simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
      field_simp
    rw [hrw, abs_mul, abs_of_pos (inv_pos.mpr hrj)]
    calc (ρ j.1)⁻¹ * |_| ≤ (ρ j.1)⁻¹ * (Hd * Real.sqrt (g.inner p W W)) :=
          mul_le_mul_of_nonneg_left h1 (inv_pos.mpr hrj).le
      _ = Hd * ((ρ j.1)⁻¹ * Real.sqrt (g.inner p W W)) := by ring


/-- **(EZ)-free low branch** (EDP02, B:6781–6782 and B:6828–6834): `T < 4Δ` wherever
`t ≤ 3.5Δ` (in particular on the low branch `t ≤ .35Δ`), `T < .31Δ` wherever `t < .3Δ`, and the
vertical set of (ED) is `{t ≤ .35Δ} ∪ {s > 0, T ≤ 4Δ} = {T ≤ 4Δ}` on ALL of `X` (only `A < P + c₃ρ`,
`|s − ρ| < c₁ρ`, `c₁ < c₃ < 10⁻⁵` and `Δ ≥ 1` are used; no base membership). -/
theorem low_branch_EDPE (C : Gaf02Chain P Kj Ξ Γ S eg c cw) (hc : c 2 < 1 / 100000) :
    (∀ p, P.edge.smoothing p / ρ p ≤ 7 / 2 * Δ →
      EuclideanSpace.proj (0 : Fin 2) (gafHeightVector P.toLocalChartFamily P.zero (C.E p)) /
        C.scale p < 4 * Δ) ∧
    (∀ p, P.edge.smoothing p / ρ p < 3 / 10 * Δ →
      EuclideanSpace.proj (0 : Fin 2) (gafHeightVector P.toLocalChartFamily P.zero (C.E p)) /
        C.scale p < 31 / 100 * Δ) ∧
    {p | P.edge.smoothing p / ρ p ≤ 7 / 20 * Δ} ∪ {p | 0 < C.scale p ∧
      EuclideanSpace.proj (0 : Fin 2) (gafHeightVector P.toLocalChartFamily P.zero (C.E p)) /
        C.scale p ≤ 4 * Δ} =
      {p | EuclideanSpace.proj (0 : Fin 2) (gafHeightVector P.toLocalChartFamily P.zero (C.E p)) /
        C.scale p ≤ 4 * Δ} := by
  obtain ⟨-, hΔ, -⟩ := C.std
  obtain ⟨hc0, hc01, hc12⟩ := C.accuracy_order_EDPE
  have key : ∀ p (k k' : ℝ), P.edge.smoothing p / ρ p ≤ k * Δ →
      k * Δ + c 2 ≤ k' * Δ * (1 - c 2) → 0 ≤ k' * Δ →
      EuclideanSpace.proj (0 : Fin 2) (gafHeightVector P.toLocalChartFamily P.zero (C.E p)) /
        C.scale p < k' * Δ := by
    intro p k k' ht hk hk'
    have hrp := hρ p
    have hA := (C.heightAxis_value_EDPE p).2
    have hs := (C.scale_pos p).1
    have hs' : (1 - c 2) * ρ p < C.scale p := by
      have := (abs_lt.mp hs).1
      nlinarith
    have hpos : 0 < (1 - c 2) * ρ p := mul_pos (by linarith) hrp
    have hsp : 0 < C.scale p := lt_trans hpos hs'
    have hFt : P.edge.smoothing p = ρ p * (P.edge.smoothing p / ρ p) := by field_simp
    rw [div_lt_iff₀ hsp]
    have h1 : P.edge.smoothing p + c 2 * ρ p ≤ ρ p * (k * Δ + c 2) := by
      rw [hFt]
      nlinarith
    have h2 : ρ p * (k * Δ + c 2) ≤ k' * Δ * ((1 - c 2) * ρ p) := by nlinarith
    have h3 : k' * Δ * ((1 - c 2) * ρ p) ≤ k' * Δ * C.scale p :=
      mul_le_mul_of_nonneg_left hs'.le hk'
    linarith
  have h35 : ∀ p, P.edge.smoothing p / ρ p ≤ 7 / 2 * Δ →
      EuclideanSpace.proj (0 : Fin 2) (gafHeightVector P.toLocalChartFamily P.zero (C.E p)) /
        C.scale p < 4 * Δ :=
    fun p ht => key p (7 / 2) 4 ht (by nlinarith) (by linarith)
  refine ⟨h35, fun p ht => key p (3 / 10) (31 / 100) ht.le (by nlinarith) (by linarith), ?_⟩
  ext p
  simp only [mem_union, mem_ofPred_eq]
  constructor
  · rintro (h | h)
    · exact (h35 p (by linarith)).le
    · exact h.2
  · intro h
    exact Or.inr ⟨(C.scale_pos p).2, h⟩

end Gaf02Chain

end DifferentialGeometry.Geometry.Collapse
