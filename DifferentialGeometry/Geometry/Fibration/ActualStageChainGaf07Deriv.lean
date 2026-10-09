import DifferentialGeometry.Geometry.Fibration.ActualStageChainGaf07
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdpBlocks
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEJA

/-!
# GAF07 on the chain: the derivative comparison `‖Dg_i − Dη_i‖ < c₃` on `Y_i`

Blueprint `master207B.tex`, GAF07 (`thm:fibration-whole-closed-fiber-bundles`, B:6111–6125): on
the original open domain `Y_i = {|η_i| < 5ℓ_i}` put `g_i = u_i(π_jE)/R_i`. "Every point of `Y_i`
has full original marker, so (AE) gives, with source norm in `R_i⁻²g`, `|g_i − η_i| < 1/800`,
`‖Dg_i − Dη_i‖ < c₃`." The value clause is `Gaf02Chain.gaf07_circle_coordinate_G47` /
`gaf07_slim_coordinate_G47`; this module gives the DERIVATIVE clause, chain-only (GAF02 CORE's
derivative budget `C.stage_derivative_lt`, one `H < c₃` for all charts):

* `Gaf02Chain.gaf07_circle_derivative_GAFC` (`j = 1`, circle): on the open threshold-8 plateau
  `{p ∈ B(c_i, 200ρ(c_i)) : ‖η_i(p)‖ < 8}` (which contains `Y_i`),
  `‖Dg_i(W) − Dη_i(W)‖ ≤ H √(R_i⁻²g(W, W))` for the `ℝ²`-valued `g_i = R_i⁻¹u_i(π₁E)`.
* `Gaf02Chain.gaf07_slim_derivative_GAFC` (`j = 3`, slim): on `{p ∈ B(c_i, 10⁶Δρ(c_i)) :
  |η_i(p)| < 8·10⁵Δ}`, the same for the real AXIS coordinate `g_i = R_i⁻¹ proj₀ u_i(π₃E)` against
  the slim coordinate `η_i` (retained slim coordinates are one-dimensional, D66-7).
* `Gaf02Chain.gaf07_slim_axis_value_GAFC`: `|g_i − η_i| < 1/800` for the slim axis coordinate on
  `Y_i` (from the vector form of GAF47).
* `Gaf02Chain.gaf07_circle_smooth_GAFC`, `gaf07_slim_smooth_GAFC`: the adjusted coordinates are
  smooth on all of `X`.
* Consumer `Gaf02ChainEJA.gaf07_coordinates_GAFC`: on a chain with (JA), at every point of `Y_i`,
  the value and derivative clauses of GAF07 (circle and slim) with ONE `H < c₃ < 1/1000`.
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

/-- A `ρ⁻¹`-multiple of a block vector is `ρ⁻¹`-Lipschitz. -/
theorem norm_inv_smul_blockVector_le_GAFC {κ : Type*} [Fintype κ] (t : κ) {R : ℝ} (hR : 0 < R)
    (y : BlockSpace (fun _ : κ => ℝ²)) :
    ‖R⁻¹ • blockVectorCLM (V := fun _ : κ => ℝ²) t y‖ ≤ R⁻¹ * ‖y‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
  have h1 := (blockVectorCLM (V := fun _ : κ => ℝ²) t).le_opNorm y
  have h2 := norm_blockVectorCLM_le (V := fun _ : κ => ℝ²) t
  have h3 : ‖blockVectorCLM (V := fun _ : κ => ℝ²) t y‖ ≤ ‖y‖ := by
    nlinarith [norm_nonneg y, norm_nonneg (blockVectorCLM (V := fun _ : κ => ℝ²) t)]
  exact mul_le_mul_of_nonneg_left h3 (inv_pos.mpr hR).le

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}

namespace Gaf02Chain

variable {P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
    T V}
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

/-- The circle adjusted coordinate `g_i = R_i⁻¹u_i(π₁E)` is `R_i⁻¹u_i(E)` and is smooth. -/
theorem gaf07_circle_smooth_GAFC (C : Gaf02Chain P Kj Ξ Γ S eg c cw)
    (i : P.toLocalChartFamily.circle.finite_centres.toFinset) :
    (fun y => (ρ i.1)⁻¹ • blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (.inl i) ((gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.E y))) =
      (fun y => ((ρ i.1)⁻¹ • blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (.inl i)) (C.E y)) ∧
    ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²) ∞ (fun y => (ρ i.1)⁻¹ •
      blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inl i)
        ((gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.E y))) := by
  have hfun : (fun y => (ρ i.1)⁻¹ • blockVectorCLM
      (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inl i)
        ((gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.E y))) =
      (fun y => ((ρ i.1)⁻¹ • blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (.inl i)) (C.E y)) := by
    funext y
    rw [vector_stageQ_G47 P.toLocalChartFamily P.zero (st := 0) (t := .inl i)
      (Finset.mem_univ _) (C.E y), smul_apply]
  refine ⟨hfun, ?_⟩
  rw [hfun]
  exact ((ρ i.1)⁻¹ • blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
    (.inl i)).contDiff.contMDiff.comp C.stage_smooth.2.2

/-- The slim adjusted AXIS coordinate `g_i = R_i⁻¹ proj₀ u_i(π₃E)` is `R_i⁻¹ proj₀ u_i(E)` and is
smooth. -/
theorem gaf07_slim_smooth_GAFC (C : Gaf02Chain P Kj Ξ Γ S eg c cw)
    (i : P.toLocalChartFamily.slim.finite_centres.toFinset) :
    (fun y => EuclideanSpace.proj (0 : Fin 2) ((ρ i.1)⁻¹ •
        blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inr (.inl i))
          ((gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.E y)))) =
      (fun y => ((EuclideanSpace.proj (0 : Fin 2)).comp ((ρ i.1)⁻¹ •
        blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inr (.inl i))))
          (C.E y)) ∧
    ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (fun y => EuclideanSpace.proj (0 : Fin 2) ((ρ i.1)⁻¹ •
        blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inr (.inl i))
          ((gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.E y)))) := by
  have hfun : (fun y => EuclideanSpace.proj (0 : Fin 2) ((ρ i.1)⁻¹ •
        blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inr (.inl i))
          ((gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.E y)))) =
      (fun y => ((EuclideanSpace.proj (0 : Fin 2)).comp ((ρ i.1)⁻¹ •
        blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inr (.inl i))))
          (C.E y)) := by
    funext y
    rw [vector_stageQ_G47 P.toLocalChartFamily P.zero (st := 2) (t := .inr (.inl i))
      (slim_mem_cgpQ3Tags P.toLocalChartFamily P.zero i) (C.E y),
      ContinuousLinearMap.comp_apply, smul_apply]
  refine ⟨hfun, ?_⟩
  rw [hfun]
  exact ((EuclideanSpace.proj (0 : Fin 2)).comp ((ρ i.1)⁻¹ •
    blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (.inr (.inl i)))).contDiff.contMDiff.comp C.stage_smooth.2.2

/-- **GAF07's derivative comparison, circle stage** (B:6118–6121): ONE budget `H < c₃` such that
on the open threshold-8 plateau `{p ∈ B(c_i, 200ρ(c_i)) : ‖η_i(p)‖ < 8}` of every circle chart,
`‖Dg_i(W) − Dη_i(W)‖ ≤ H √(R_i⁻²g(W, W))` for `g_i = R_i⁻¹u_i(π₁E)`. -/
theorem gaf07_circle_derivative_GAFC (C : Gaf02Chain P Kj Ξ Γ S eg c cw) :
    ∃ H : ℝ, H < c 2 ∧ ∀ (i : P.toLocalChartFamily.circle.finite_centres.toFinset) (p : X),
      p ∈ ball i.1 (200 * ρ i.1) → ‖cgpCoord P.toLocalChartFamily P.zero (.inl i) p‖ < 8 →
      ∀ W : TangentSpace 𝓘(ℝ, E3) p,
        ‖mvfderiv 𝓘(ℝ, E3) (fun y => (ρ i.1)⁻¹ •
            blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inl i)
              ((gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.E y))) p W -
          mvfderiv 𝓘(ℝ, E3) (cgpCoord P.toLocalChartFamily P.zero (.inl i)) p W‖ ≤
          H * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner p W W) := by
  obtain ⟨H, hH, hder⟩ := C.stage_derivative_lt.2.2
  refine ⟨H, hH, fun i p hpi hη W => ?_⟩
  have hj := (Set.Finite.mem_toFinset _).mp i.2
  have hri := hρ i.1
  set ℓ : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ² :=
    (ρ i.1)⁻¹ • blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inl i)
    with hℓ
  have hE := C.stage_smooth.2.2
  have hF := C.globalMap_smooth_EDPE
  -- the open plateau and the original coordinate as `ℓ ∘ 𝓔⁰` there
  have hcont : ContinuousOn (cgpCoord P.toLocalChartFamily P.zero (.inl i))
      (ball i.1 (200 * ρ i.1)) :=
    (cgpCircleCoord_contMDiffOn P.toLocalChartFamily hj).continuousOn
  have hO : IsOpen (ball i.1 (200 * ρ i.1) ∩
      cgpCoord P.toLocalChartFamily P.zero (.inl i) ⁻¹' {v : ℝ² | ‖v‖ < 8}) :=
    hcont.isOpen_inter_preimage isOpen_ball (isOpen_lt continuous_norm continuous_const)
  have hev : (fun y => ℓ (cgpGlobalMap P.toLocalChartFamily P.zero y)) =ᶠ[𝓝 p]
      cgpCoord P.toLocalChartFamily P.zero (.inl i) := by
    filter_upwards [hO.mem_nhds ⟨hpi, hη⟩] with y hy
    obtain ⟨-, hu, -, -⟩ := C.circle_full_block_G47 i hy.1 (le_of_lt hy.2)
    rw [hℓ, smul_apply, hu, smul_smul, inv_mul_cancel₀ hri.ne', one_smul]
  have h1 := mvfderiv_clm_comp_apply_EDPE ℓ ((hE p).mdifferentiableAt (by simp)) W
  have h2 := mvfderiv_clm_comp_apply_EDPE ℓ ((hF p).mdifferentiableAt (by simp)) W
  rw [(C.gaf07_circle_smooth_GAFC i).1, h1, ← mvfderiv_congr_EDPE hev, h2, ← map_sub,
    sqrt_inv_sq_mul_FC19 hri]
  calc ‖ℓ (mvfderiv 𝓘(ℝ, E3) C.E p W -
        mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) p W)‖
      ≤ (ρ i.1)⁻¹ * ‖mvfderiv 𝓘(ℝ, E3) C.E p W -
        mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) p W‖ := by
        rw [hℓ, smul_apply]
        exact norm_inv_smul_blockVector_le_GAFC _ hri _
    _ ≤ (ρ i.1)⁻¹ * (H * Real.sqrt (g.inner p W W)) :=
        mul_le_mul_of_nonneg_left (hder p W) (inv_pos.mpr hri).le
    _ = H * ((ρ i.1)⁻¹ * Real.sqrt (g.inner p W W)) := by ring

/-- **GAF07's derivative comparison, slim stage** (B:6118–6121; retained slim coordinate on the
axis, D66-7): ONE budget `H < c₃` such that on `{p ∈ B(c_i, 10⁶Δρ(c_i)) : |η_i(p)| < 8·10⁵Δ}`,
`|Dg_i(W) − Dη_i(W)| ≤ H √(R_i⁻²g(W, W))` for `g_i = R_i⁻¹ proj₀ u_i(π₃E)`. -/
theorem gaf07_slim_derivative_GAFC (C : Gaf02Chain P Kj Ξ Γ S eg c cw) :
    ∃ H : ℝ, H < c 2 ∧ ∀ (i : P.toLocalChartFamily.slim.finite_centres.toFinset) (p : X),
      p ∈ ball i.1 (1000000 * Δ * ρ i.1) →
      |(P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord p| < 8 * (10 ^ 5 * Δ) →
      ∀ W : TangentSpace 𝓘(ℝ, E3) p,
        |mvfderiv 𝓘(ℝ, E3) (fun y => EuclideanSpace.proj (0 : Fin 2) ((ρ i.1)⁻¹ •
            blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inr (.inl i))
              ((gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.E y)))) p W -
          mvfderiv 𝓘(ℝ, E3) (P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord p W| ≤
          H * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner p W W) := by
  obtain ⟨H, hH, hder⟩ := C.stage_derivative_lt.2.2
  refine ⟨H, hH, fun i p hpi hη W => ?_⟩
  have hj := (Set.Finite.mem_toFinset _).mp i.2
  have hri := hρ i.1
  set ℓ : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ :=
    (EuclideanSpace.proj (0 : Fin 2)).comp ((ρ i.1)⁻¹ •
      blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inr (.inl i)))
    with hℓ
  have hE := C.stage_smooth.2.2
  have hF := C.globalMap_smooth_EDPE
  have hcont : ContinuousOn (P.slim.centre i.1 hj).coord (ball i.1 (10 ^ 6 * Δ * ρ i.1)) :=
    (P.slim.centre i.1 hj).contMDiffOn_coord.continuousOn
  have hball : ball i.1 (1000000 * Δ * ρ i.1) = ball i.1 (10 ^ 6 * Δ * ρ i.1) := by norm_num
  have hO : IsOpen (ball i.1 (10 ^ 6 * Δ * ρ i.1) ∩
      (P.slim.centre i.1 hj).coord ⁻¹' {t : ℝ | |t| < 8 * (10 ^ 5 * Δ)}) :=
    hcont.isOpen_inter_preimage isOpen_ball (isOpen_lt continuous_abs continuous_const)
  have hev : (fun y => ℓ (cgpGlobalMap P.toLocalChartFamily P.zero y)) =ᶠ[𝓝 p]
      (P.slim.centre i.1 hj).coord := by
    filter_upwards [hO.mem_nhds ⟨hball ▸ hpi, hη⟩] with y hy
    obtain ⟨-, hu, -, -⟩ := C.slim_full_block_G47 i (hball ▸ hy.1) (le_of_lt hy.2)
    rw [hℓ, ContinuousLinearMap.comp_apply, smul_apply, hu, smul_smul,
      inv_mul_cancel₀ hri.ne', one_smul, proj_planeAxis_EDPE]
  have h1 := mvfderiv_clm_comp_apply_EDPE ℓ ((hE p).mdifferentiableAt (by simp)) W
  have h2 := mvfderiv_clm_comp_apply_EDPE ℓ ((hF p).mdifferentiableAt (by simp)) W
  rw [(C.gaf07_slim_smooth_GAFC i).1, h1, ← mvfderiv_congr_EDPE hev, h2, ← map_sub,
    sqrt_inv_sq_mul_FC19 hri]
  have hpr : ∀ v : ℝ², |EuclideanSpace.proj (0 : Fin 2) v| ≤ ‖v‖ := fun v => by
    simpa using PiLp.norm_apply_le v (0 : Fin 2)
  calc |ℓ (mvfderiv 𝓘(ℝ, E3) C.E p W -
        mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) p W)|
      ≤ (ρ i.1)⁻¹ * ‖mvfderiv 𝓘(ℝ, E3) C.E p W -
        mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) p W‖ := by
        rw [hℓ, ContinuousLinearMap.comp_apply, smul_apply]
        exact (hpr _).trans (norm_inv_smul_blockVector_le_GAFC _ hri _)
    _ ≤ (ρ i.1)⁻¹ * (H * Real.sqrt (g.inner p W W)) :=
        mul_le_mul_of_nonneg_left (hder p W) (inv_pos.mpr hri).le
    _ = H * ((ρ i.1)⁻¹ * Real.sqrt (g.inner p W W)) := by ring

/-- **GAF07's value comparison, slim stage, on the AXIS** (B:6118): on
`Y_i = {|η_i| < 5·10⁵Δ} ∩ B(c_i, 10⁶Δρ(c_i))`, `|g_i − η_i| < 1/800` for the real axis coordinate
`g_i = R_i⁻¹ proj₀ u_i(π₃E)`. -/
theorem gaf07_slim_axis_value_GAFC (C : Gaf02Chain P Kj Ξ Γ S eg c cw) (hc : c 2 < 1 / 1000)
    (i : P.toLocalChartFamily.slim.finite_centres.toFinset) {p : X}
    (hpi : p ∈ ball i.1 (1000000 * Δ * ρ i.1))
    (hη : |(P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord p| < 5 * (10 ^ 5 * Δ)) :
    |EuclideanSpace.proj (0 : Fin 2) ((ρ i.1)⁻¹ •
        blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inr (.inl i))
          ((gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.E p))) -
      (P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord p| < 1 / 800 := by
  have k := (C.gaf07_slim_coordinate_G47 hc i hpi hη).1
  have hpr : ∀ v : ℝ², |EuclideanSpace.proj (0 : Fin 2) v| ≤ ‖v‖ := fun v => by
    simpa using PiLp.norm_apply_le v (0 : Fin 2)
  have h := hpr ((ρ i.1)⁻¹ • blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (.inr (.inl i)) ((gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.E p)) -
    planeAxis ((P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord p))
  rw [map_sub, proj_planeAxis_EDPE] at h
  exact h.trans_lt k

end Gaf02Chain

namespace Gaf02ChainEJA

variable {vs ζ Λz : ℝ}
  {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
    V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ} {cadj : ℝ}

/-- **Consumer: GAF07's coordinate comparisons on a chain with (JA)** (B:6111–6125): ONE budget
`H < c₃ < 1/1000` such that at every point of every circle domain `Y_i = {‖η_i‖ < 5}` and every slim
domain `Y_i = {|η_i| < 5·10⁵Δ}`, the adjusted coordinate is within `1/800` of `η_i` and its
derivative within `H` (source norm `R_i⁻²g`). -/
theorem gaf07_coordinates_GAFC (C : Gaf02ChainEJA P Kj Ξ Γ S eg c cw cadj) :
    ∃ H : ℝ, H < 1 / 1000 ∧
      (∀ (i : P.toLocalChartFamily.circle.finite_centres.toFinset) (p : X),
        p ∈ ball i.1 (200 * ρ i.1) → ‖cgpCoord P.toLocalChartFamily P.zero (.inl i) p‖ < 5 →
        ‖(ρ i.1)⁻¹ • blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
            (.inl i) ((gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E p)) -
          cgpCoord P.toLocalChartFamily P.zero (.inl i) p‖ < 1 / 800 ∧
        ∀ W : TangentSpace 𝓘(ℝ, E3) p,
          ‖mvfderiv 𝓘(ℝ, E3) (fun y => (ρ i.1)⁻¹ •
              blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inl i)
                ((gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E y))) p W -
            mvfderiv 𝓘(ℝ, E3) (cgpCoord P.toLocalChartFamily P.zero (.inl i)) p W‖ ≤
            H * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner p W W)) ∧
      ∀ (i : P.toLocalChartFamily.slim.finite_centres.toFinset) (p : X),
        p ∈ ball i.1 (1000000 * Δ * ρ i.1) →
        |(P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord p| < 5 * (10 ^ 5 * Δ) →
        |EuclideanSpace.proj (0 : Fin 2) ((ρ i.1)⁻¹ •
            blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inr (.inl i))
              ((gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.toChain.E p))) -
          (P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord p| < 1 / 800 ∧
        ∀ W : TangentSpace 𝓘(ℝ, E3) p,
          |mvfderiv 𝓘(ℝ, E3) (fun y => EuclideanSpace.proj (0 : Fin 2) ((ρ i.1)⁻¹ •
              blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
                (.inr (.inl i))
                ((gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.toChain.E y)))) p W -
            mvfderiv 𝓘(ℝ, E3) (P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord p W| ≤
            H * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner p W W) := by
  obtain ⟨H₁, hH₁, k₁⟩ := C.toChain.gaf07_circle_derivative_GAFC
  obtain ⟨H₂, hH₂, k₂⟩ := C.toChain.gaf07_slim_derivative_GAFC
  have hc := C.c_two_lt
  obtain ⟨-, hΔ, -⟩ := C.toChain.std
  refine ⟨max H₁ H₂, max_lt (hH₁.trans hc) (hH₂.trans hc), fun i p hpi hη => ⟨
    (C.toChain.gaf07_circle_coordinate_G47 hc i hpi hη).1, fun W => ?_⟩,
    fun i p hpi hη => ⟨C.toChain.gaf07_slim_axis_value_GAFC hc i hpi hη, fun W => ?_⟩⟩
  · refine (k₁ i p hpi (by linarith) W).trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)
  · refine (k₂ i p hpi (by linarith) W).trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.sqrt_nonneg _)

end Gaf02ChainEJA

end DifferentialGeometry.Geometry.Collapse
