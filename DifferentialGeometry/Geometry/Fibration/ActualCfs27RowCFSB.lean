import DifferentialGeometry.Geometry.Fibration.ActualCfs28RowCFSB
import DifferentialGeometry.Geometry.Fibration.ActualStageFirstPruning

/-!
# CFS27 on the actual data: pruning the small blocks before choosing the stage planes

Blueprint `master207B.tex`, CFS27 (`lem:fibration-pruned-model-planes`, B:3618–3684). For a
reference chart `a ∈ I₊` (any retained marker: circle, edge or slim centre, `R_a = ρ(c_a)`),
`K_a = π_{keep(R_a)}` is the orthogonal coordinate projection deleting every retained block `i` with
`R_i ≤ R_a/2` and keeping every other block — the reference block, the scale, `E'` and zero blocks
(`firstKeepTags_GAF5`). On the actual data (`F = 𝓔⁰`, `π_st = cgpProjMap (gafStageTags st)`):

* (PR) `K_a π_st F = π_st F` on the WHOLE domain `U_a = B(c_a, D_aR_a)`, with equality of
  derivatives there; every deleted block of `π_st F` vanishes on `U_a`;
* `K_a` keeps the reference block (the graph identity over the same reference coordinate) and has
  norm `≤ 1`, so value / `C¹` comparison errors and upper derivative bounds do not increase;
* (PP) on the enhanced chain (`Gaf02ChainE`): the plane at `x ∈ S_st` is
  `L_x = im D(K_{a(x)} ∘ Φ_{a(x)})(η_{a(x)}(q(x)))` with the LITERAL `K_{a(x)}` — stage `0` is
  pruned by it (TCP05's model), and at stages `1, 2` the EGP06 / SGP04 models already have zero
  small blocks, so `K_{a}Φ_a = Φ_a`; every deleted block is zero at `x` and on `L_x`.

Main theorem: `Gaf02ChainE.cfs27_row_CFSB`.
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

section Family

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc : ℝ}
  {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
  [∀ a, MetricSpace (C a)] {o : ∀ a, C a} {δ εr e T V : ℝ}

variable (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
  (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V)

open Classical in
/-- A tag outside the kept set at radius `r` is a retained marker with `ρ(c_i) ≤ r/2`. -/
theorem not_mem_keep_CFSB {r : ℝ} {t : CGPTag L Z} (ht : t ∉ firstKeepTags_GAF5 L Z r) :
    ∃ i : CGPMarkerIndex L, cgpMarkerTag L Z i = t ∧ ρ (cgpMarkerCentre L i) ≤ r / 2 := by
  rw [firstKeepTags_GAF5, Finset.mem_filter] at ht
  push Not at ht
  exact ht (Finset.mem_univ _)

open Classical in
/-- The reference block is kept: `tag a ∈ keep(R_a)`. -/
theorem keep_own_CFSB (a : CGPMarkerIndex L) :
    cgpMarkerTag L Z a ∈ firstKeepTags_GAF5 L Z (ρ (cgpMarkerCentre L a)) := by
  rw [firstKeepTags_GAF5, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, fun a' ha' => ?_⟩
  have hra := hρ (cgpMarkerCentre L a)
  have heq : a' = a := by
    rcases a with j | j | j <;> rcases a' with j' | j' | j' <;>
      simp_all [cgpMarkerTag]
  subst heq
  linarith

open Classical in
/-- `K_a` kills every deleted block. -/
theorem keep_deleted_CFSB {r : ℝ} (i : CGPMarkerIndex L) (hi : ρ (cgpMarkerCentre L i) ≤ r / 2)
    (y : BlockSpace (fun _ : CGPTag L Z => ℝ²)) :
    blockRestrict (firstKeepTags_GAF5 L Z r) y (cgpMarkerTag L Z i) = 0 := by
  rw [blockRestrict_apply, ite_eq_right (firstKeep_marker_GAF5 L Z i hi)]

open Classical in
/-- **(PR)** on the whole reference domain: `K_a π_st 𝓔⁰ = π_st 𝓔⁰` on `B(c_a, D_aR_a)`. -/
theorem keep_projMap_CFSB (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ) (hsmall : Λ * (1000000 * Δ) ≤ 1 / 4)
    (a : CGPMarkerIndex L) (st : Fin 3) {x : X}
    (hx : x ∈ ball (cgpMarkerCentre L a) (cgpMarkerDomain L a * ρ (cgpMarkerCentre L a))) :
    blockRestrict (firstKeepTags_GAF5 L Z (ρ (cgpMarkerCentre L a)))
        (cgpProjMap L Z (gafStageTags L Z st) x) = cgpProjMap L Z (gafStageTags L Z st) x := by
  refine PiLp.ext fun t => ?_
  rw [blockRestrict_apply]
  split_ifs with ht
  · rfl
  · obtain ⟨i, rfl, hi⟩ := not_mem_keep_CFSB L Z ht
    have hcut : cgpMarkerCutoff L i x = 0 := by
      by_contra hne
      have h1 := cgpMarkerCutoff_scale_lip_GAF4 L hΔ hΛ hsmall i x hne
      have h2 := cgpMarker_domain_scale_CFSB L hΔ hΛ hsmall a x (ball_subset_closedBall hx)
      have hra := hρ (cgpMarkerCentre L a)
      linarith [h1.2, h2.1]
    exact (projMap_block_eq_zero_CFSB L Z st i x hcut).symm

open Classical in
/-- **(PR) for the derivative** on the open reference domain. -/
theorem keep_projMap_mvfderiv_CFSB (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ)
    (hsmall : Λ * (1000000 * Δ) ≤ 1 / 4) (a : CGPMarkerIndex L) (st : Fin 3) {x : X}
    (hx : x ∈ ball (cgpMarkerCentre L a) (cgpMarkerDomain L a * ρ (cgpMarkerCentre L a)))
    (w : TangentSpace 𝓘(ℝ, E3) x) :
    blockRestrict (firstKeepTags_GAF5 L Z (ρ (cgpMarkerCentre L a)))
        (mvfderiv 𝓘(ℝ, E3) (cgpProjMap L Z (gafStageTags L Z st)) x w) =
      mvfderiv 𝓘(ℝ, E3) (cgpProjMap L Z (gafStageTags L Z st)) x w :=
  clm_mvfderiv_eq_of_eventuallyEq_GAF5 _
    (Filter.eventually_of_mem (isOpen_ball.mem_nhds hx) fun _ hy =>
      keep_projMap_CFSB L Z hΔ hΛ hsmall a st hy) w

open Classical in
/-- `K_a` does not move an EGP06 model of reference `a` (its small blocks are zero). -/
theorem keep_egpModel_CFSB (hΔ : 0 < Δ) (hΛ : 0 ≤ Λ) (hLΛ : 1000000 * Δ * Λ < 1 / 100000)
    (a : X) (sgn c : CGPTag L Z → ℝ) (u : ℝ) :
    blockRestrict (firstKeepTags_GAF5 L Z (ρ a)) (egpModelGraph L Z a sgn c u) =
      egpModelGraph L Z a sgn c u := by
  refine PiLp.ext fun t => ?_
  rw [blockRestrict_apply]
  split_ifs with ht
  · rfl
  · obtain ⟨i, rfl, hi⟩ := not_mem_keep_CFSB L Z ht
    have hra := hρ a
    exact (egpModel_smallBlock_CFSB L Z hΔ hΛ hLΛ a sgn c i (by linarith) u).symm

open Classical in
/-- `K_a` does not move an SGP04 full model of reference `a` (its small blocks are zero). -/
theorem keep_sgpFull_CFSB (hΔ : 0 < Δ) (hΛ : 0 ≤ Λ) (hLΛ : 1000000 * Δ * Λ < 1 / 100000)
    (a : L.slim.finite_centres.toFinset) (sgn c zsgn zc : X → ℝ) (u : ℝ) :
    blockRestrict (firstKeepTags_GAF5 L Z (ρ a.1)) (sgpFullGraph L Z a sgn c zsgn zc u) =
      sgpFullGraph L Z a sgn c zsgn zc u := by
  refine PiLp.ext fun t => ?_
  rw [blockRestrict_apply]
  split_ifs with ht
  · rfl
  · obtain ⟨i, rfl, hi⟩ := not_mem_keep_CFSB L Z ht
    have hra := hρ a.1
    exact (sgpFull_smallBlock_CFSB L Z hΔ hΛ hLΛ a sgn c zsgn zc i (by linarith) u).symm

open Classical in
/-- Pruning does not increase value errors at a point it fixes, nor `C¹` errors / upper bounds:
`‖y − K_a y'‖ ≤ ‖y − y'‖` if `K_a y = y`, and `‖K_a ∘ T‖ ≤ ‖T‖`. -/
theorem keep_contract_CFSB (r : ℝ) (y y' : BlockSpace (fun _ : CGPTag L Z => ℝ²))
    (hy : blockRestrict (firstKeepTags_GAF5 L Z r) y = y) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (Tl : E →L[ℝ] BlockSpace (fun _ : CGPTag L Z => ℝ²)) :
    ‖y - blockRestrict (firstKeepTags_GAF5 L Z r) y'‖ ≤ ‖y - y'‖ ∧
      ‖(blockRestrict (firstKeepTags_GAF5 L Z r)).comp Tl‖ ≤ ‖Tl‖ := by
  have hK := norm_blockRestrict_le (V := fun _ : CGPTag L Z => ℝ²) (firstKeepTags_GAF5 L Z r)
  constructor
  · calc ‖y - blockRestrict (firstKeepTags_GAF5 L Z r) y'‖
        = ‖blockRestrict (firstKeepTags_GAF5 L Z r) (y - y')‖ := by rw [map_sub, hy]
      _ ≤ ‖y - y'‖ := norm_blockRestrict_apply_le _ _
  · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul_of_nonneg_right hK (norm_nonneg _)).trans_eq (one_mul _))

end Family

namespace Gaf02ChainE

variable {X : Type} [MetricSpace X] [ChartedSpace E3 X]
  [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
    V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

open Classical in
/-- **(PP) at stage `0`**: `L_x = im D(K_a ∘ Φ_a)(η_a q(x))` with the literal `K_a`, `a = a(x)`;
every deleted block is zero at `x` and on `L_x`. -/
theorem cfs27_stage0_CFSB (C : Gaf02ChainE P Kj Ξ Γ S eg c cw)
    {x : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)}
    (hx : x ∈ gafCloud P.toLocalChartFamily P.zero 0) :
    C.toChain.plane 0 x = LinearMap.range (fderiv ℝ
      (blockRestrict (firstKeepTags_GAF5 P.toLocalChartFamily P.zero
          (ρ (C.planes₀.ref ⟨x, hx⟩).1)) ∘ C.planes₀.model (C.planes₀.ref ⟨x, hx⟩))
      (C.planes₀.coord (C.planes₀.ref ⟨x, hx⟩) (C.planes₀.pre ⟨x, hx⟩)) :
        ℝ² →ₗ[ℝ] BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) ∧
    ∀ i : CGPMarkerIndex P.toLocalChartFamily,
      ρ (cgpMarkerCentre P.toLocalChartFamily i) ≤ ρ (C.planes₀.ref ⟨x, hx⟩).1 / 2 →
      x (cgpMarkerTag P.toLocalChartFamily P.zero i) = 0 ∧
        ∀ w ∈ C.toChain.plane 0 x, w (cgpMarkerTag P.toLocalChartFamily P.zero i) = 0 := by
  obtain ⟨hΛ, hΔ, -, -, -, -, -, -, -, -, -⟩ := C.toChain.std
  have hsmall : Λ * (1000000 * Δ) ≤ 1 / 4 := C.toChain.small_BAS
  have hdef : C.toChain.plane 0 x = LinearMap.range (fderiv ℝ
      (blockRestrict (firstKeepTags_GAF5 P.toLocalChartFamily P.zero
          (ρ (C.planes₀.ref ⟨x, hx⟩).1)) ∘ C.planes₀.model (C.planes₀.ref ⟨x, hx⟩))
      (C.planes₀.coord (C.planes₀.ref ⟨x, hx⟩) (C.planes₀.pre ⟨x, hx⟩)) :
        ℝ² →ₗ[ℝ] BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) := by
    rw [C.plane_eq.1, ← C.planes₀.prune_eq]
    simp only [StagePlaneData_PLN.plane, hx, ↓reduceDIte]
    rfl
  refine ⟨hdef, fun i hi => ⟨?_, fun w hw => ?_⟩⟩
  · obtain ⟨hb, -, hpx⟩ := C.planes₀.pre_spec ⟨x, hx⟩
    have hPR := keep_projMap_CFSB P.toLocalChartFamily P.zero hΔ hΛ hsmall
      (.inl (C.planes₀.ref ⟨x, hx⟩)) 0 hb
    change cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 0)
      (C.planes₀.pre ⟨x, hx⟩) = x at hpx
    change blockRestrict (firstKeepTags_GAF5 P.toLocalChartFamily P.zero
      (ρ (C.planes₀.ref ⟨x, hx⟩).1)) _ = _ at hPR
    rw [← hpx, ← hPR]
    exact keep_deleted_CFSB P.toLocalChartFamily P.zero i hi _
  · rw [hdef] at hw
    obtain ⟨h, rfl⟩ := hw
    exact block_fderiv_eq_zero_of_zero_CFSB _ _
      (fun v => keep_deleted_CFSB P.toLocalChartFamily P.zero i hi _) _ h

open Classical in
/-- **(PP) at stage `1`**: `K_aΦ_a = Φ_a` for EGP06's model, so `L_x = im D(K_a ∘ Φ_a)(η_a q(x))`
with the literal `K_a`; every deleted block is zero at `x` and on `L_x`. -/
theorem cfs27_stage1_CFSB (C : Gaf02ChainE P Kj Ξ Γ S eg c cw)
    {x : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)}
    (hx : x ∈ gafCloud P.toLocalChartFamily P.zero 1) :
    C.toChain.plane 1 x = LinearMap.range (fderiv ℝ
      (blockRestrict (firstKeepTags_GAF5 P.toLocalChartFamily P.zero
          (ρ (C.planes₁.ref ⟨x, hx⟩).1)) ∘ C.planes₁.model (C.planes₁.ref ⟨x, hx⟩))
      (C.planes₁.coord (C.planes₁.ref ⟨x, hx⟩) (C.planes₁.pre ⟨x, hx⟩)) :
        ℝ →ₗ[ℝ] BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) ∧
    ∀ i : CGPMarkerIndex P.toLocalChartFamily,
      ρ (cgpMarkerCentre P.toLocalChartFamily i) ≤ ρ (C.planes₁.ref ⟨x, hx⟩).1 / 2 →
      x (cgpMarkerTag P.toLocalChartFamily P.zero i) = 0 ∧
        ∀ w ∈ C.toChain.plane 1 x, w (cgpMarkerTag P.toLocalChartFamily P.zero i) = 0 := by
  obtain ⟨hΛ, hΔ, -, -, hLΛ, -, -, -, -, -, -⟩ := C.toChain.std
  have hsmall : Λ * (1000000 * Δ) ≤ 1 / 4 := C.toChain.small_BAS
  have hΔ0 : 0 < Δ := by linarith
  set a := C.planes₁.ref ⟨x, hx⟩ with ha
  have hfun : blockRestrict (firstKeepTags_GAF5 P.toLocalChartFamily P.zero (ρ a.1)) ∘
      C.planes₁.model a = C.planes₁.prune a ∘ C.planes₁.model a := by
    funext u
    rw [Function.comp_apply, Function.comp_apply, C.planes₁.prune_eq, C.planes₁.model_eq,
      ContinuousLinearMap.id_apply]
    exact keep_egpModel_CFSB P.toLocalChartFamily P.zero hΔ0 hΛ hLΛ _ _ _ u
  have hdef : C.toChain.plane 1 x = LinearMap.range (fderiv ℝ
      (blockRestrict (firstKeepTags_GAF5 P.toLocalChartFamily P.zero (ρ a.1)) ∘
        C.planes₁.model a) (C.planes₁.coord a (C.planes₁.pre ⟨x, hx⟩)) :
        ℝ →ₗ[ℝ] BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) := by
    rw [hfun, C.plane_eq.2.1]
    simp only [StagePlaneData_PLN.plane, hx, ↓reduceDIte]
    rfl
  refine ⟨hdef, fun i hi => ⟨?_, fun w hw => ?_⟩⟩
  · obtain ⟨hb, -, -, hpx⟩ := C.planes₁.pre_spec ⟨x, hx⟩
    have hPR := keep_projMap_CFSB P.toLocalChartFamily P.zero hΔ hΛ hsmall (.inr (.inr a)) 1 hb
    change cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 1)
      (C.planes₁.pre ⟨x, hx⟩) = x at hpx
    change blockRestrict (firstKeepTags_GAF5 P.toLocalChartFamily P.zero (ρ a.1)) _ = _ at hPR
    rw [← hpx, ← hPR]
    exact keep_deleted_CFSB P.toLocalChartFamily P.zero i hi _
  · rw [hdef] at hw
    obtain ⟨h, rfl⟩ := hw
    exact block_fderiv_eq_zero_of_zero_CFSB _ _
      (fun v => keep_deleted_CFSB P.toLocalChartFamily P.zero i hi _) _ h

open Classical in
/-- **(PP) at stage `2`**: `K_aΦ_a = Φ_a` for SGP04's full model, so
`L_x = im D(K_a ∘ Φ_a)(η_a q(x))` with the literal `K_a`; every deleted block is zero at `x` and
on `L_x`. -/
theorem cfs27_stage2_CFSB (C : Gaf02ChainE P Kj Ξ Γ S eg c cw)
    {x : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)}
    (hx : x ∈ gafCloud P.toLocalChartFamily P.zero 2) :
    C.toChain.plane 2 x = LinearMap.range (fderiv ℝ
      (blockRestrict (firstKeepTags_GAF5 P.toLocalChartFamily P.zero
          (ρ (C.planes₂.ref ⟨x, hx⟩).1)) ∘ C.planes₂.model (C.planes₂.ref ⟨x, hx⟩))
      (C.planes₂.coord (C.planes₂.ref ⟨x, hx⟩) (C.planes₂.pre ⟨x, hx⟩)) :
        ℝ →ₗ[ℝ] BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) ∧
    ∀ i : CGPMarkerIndex P.toLocalChartFamily,
      ρ (cgpMarkerCentre P.toLocalChartFamily i) ≤ ρ (C.planes₂.ref ⟨x, hx⟩).1 / 2 →
      x (cgpMarkerTag P.toLocalChartFamily P.zero i) = 0 ∧
        ∀ w ∈ C.toChain.plane 2 x, w (cgpMarkerTag P.toLocalChartFamily P.zero i) = 0 := by
  obtain ⟨hΛ, hΔ, -, -, hLΛ, -, -, -, -, -, -⟩ := C.toChain.std
  have hsmall : Λ * (1000000 * Δ) ≤ 1 / 4 := C.toChain.small_BAS
  have hΔ0 : 0 < Δ := by linarith
  set a := C.planes₂.ref ⟨x, hx⟩ with ha
  have hfun : blockRestrict (firstKeepTags_GAF5 P.toLocalChartFamily P.zero (ρ a.1)) ∘
      C.planes₂.model a = C.planes₂.prune a ∘ C.planes₂.model a := by
    funext u
    rw [Function.comp_apply, Function.comp_apply, C.planes₂.prune_eq, C.planes₂.model_eq,
      ContinuousLinearMap.id_apply]
    exact keep_sgpFull_CFSB P.toLocalChartFamily P.zero hΔ0 hΛ hLΛ _ _ _ _ _ u
  have hdef : C.toChain.plane 2 x = LinearMap.range (fderiv ℝ
      (blockRestrict (firstKeepTags_GAF5 P.toLocalChartFamily P.zero (ρ a.1)) ∘
        C.planes₂.model a) (C.planes₂.coord a (C.planes₂.pre ⟨x, hx⟩)) :
        ℝ →ₗ[ℝ] BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) := by
    rw [hfun, C.plane_eq.2.2]
    simp only [StagePlaneData_PLN.plane, hx, ↓reduceDIte]
    rfl
  refine ⟨hdef, fun i hi => ⟨?_, fun w hw => ?_⟩⟩
  · obtain ⟨hb, -, hpx⟩ := C.planes₂.pre_spec ⟨x, hx⟩
    have hPR := keep_projMap_CFSB P.toLocalChartFamily P.zero hΔ hΛ hsmall (.inr (.inl a)) 2
      (by
        change _ ∈ ball a.1 (1000000 * Δ * ρ a.1)
        rw [ha]
        convert hb using 2
        norm_num)
    change cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 2)
      (C.planes₂.pre ⟨x, hx⟩) = x at hpx
    change blockRestrict (firstKeepTags_GAF5 P.toLocalChartFamily P.zero (ρ a.1)) _ = _ at hPR
    rw [← hpx, ← hPR]
    exact keep_deleted_CFSB P.toLocalChartFamily P.zero i hi _
  · rw [hdef] at hw
    obtain ⟨h, rfl⟩ := hw
    exact block_fderiv_eq_zero_of_zero_CFSB _ _
      (fun v => keep_deleted_CFSB P.toLocalChartFamily P.zero i hi _) _ h

open Classical in
/-- **CFS27** (`lem:fibration-pruned-model-planes`) on the enhanced chain. For every reference
`a ∈ I₊` and `K_a = π_{keep(R_a)}` (delete the retained blocks with `R_i ≤ R_a/2`): (PR)
`K_a π_st 𝓔⁰ = π_st 𝓔⁰` with equal derivatives on the whole domain `U_a = B(c_a, D_aR_a)`, every
stage; the reference block is kept (the graph identity over the same reference coordinate) and
`‖K_a‖ ≤ 1` (comparison errors and upper derivative bounds do not increase, `keep_contract_CFSB`);
(PP) at every stage: `L_x = im D(K_{a(x)} ∘ Φ_{a(x)})(η_{a(x)}(q(x)))` with the literal pruning,
and every deleted block is zero at `x` and on `L_x`. -/
theorem cfs27_row_CFSB (C : Gaf02ChainE P Kj Ξ Γ S eg c cw) :
    (∀ (a : CGPMarkerIndex P.toLocalChartFamily) (st : Fin 3) (x : X),
      x ∈ ball (cgpMarkerCentre P.toLocalChartFamily a)
        (cgpMarkerDomain P.toLocalChartFamily a * ρ (cgpMarkerCentre P.toLocalChartFamily a)) →
      blockRestrict (firstKeepTags_GAF5 P.toLocalChartFamily P.zero
          (ρ (cgpMarkerCentre P.toLocalChartFamily a)))
          (cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero st) x) =
        cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero st) x ∧
      ∀ w : TangentSpace 𝓘(ℝ, E3) x,
        blockRestrict (firstKeepTags_GAF5 P.toLocalChartFamily P.zero
            (ρ (cgpMarkerCentre P.toLocalChartFamily a)))
            (mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
              (gafStageTags P.toLocalChartFamily P.zero st)) x w) =
          mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
            (gafStageTags P.toLocalChartFamily P.zero st)) x w) ∧
    (∀ a : CGPMarkerIndex P.toLocalChartFamily, cgpMarkerTag P.toLocalChartFamily P.zero a ∈
      firstKeepTags_GAF5 P.toLocalChartFamily P.zero (ρ (cgpMarkerCentre P.toLocalChartFamily a))) ∧
    (∀ a : CGPMarkerIndex P.toLocalChartFamily,
      ‖(blockRestrict (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (firstKeepTags_GAF5 P.toLocalChartFamily P.zero
          (ρ (cgpMarkerCentre P.toLocalChartFamily a))))‖ ≤ 1) ∧
    (∀ (x : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
      (hx : x ∈ gafCloud P.toLocalChartFamily P.zero 0),
      C.toChain.plane 0 x = LinearMap.range (fderiv ℝ
        (blockRestrict (firstKeepTags_GAF5 P.toLocalChartFamily P.zero
            (ρ (C.planes₀.ref ⟨x, hx⟩).1)) ∘ C.planes₀.model (C.planes₀.ref ⟨x, hx⟩))
        (C.planes₀.coord (C.planes₀.ref ⟨x, hx⟩) (C.planes₀.pre ⟨x, hx⟩)) :
          ℝ² →ₗ[ℝ] BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) ∧
      ∀ i : CGPMarkerIndex P.toLocalChartFamily,
        ρ (cgpMarkerCentre P.toLocalChartFamily i) ≤ ρ (C.planes₀.ref ⟨x, hx⟩).1 / 2 →
        x (cgpMarkerTag P.toLocalChartFamily P.zero i) = 0 ∧
          ∀ w ∈ C.toChain.plane 0 x, w (cgpMarkerTag P.toLocalChartFamily P.zero i) = 0) ∧
    (∀ (x : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
      (hx : x ∈ gafCloud P.toLocalChartFamily P.zero 1),
      C.toChain.plane 1 x = LinearMap.range (fderiv ℝ
        (blockRestrict (firstKeepTags_GAF5 P.toLocalChartFamily P.zero
            (ρ (C.planes₁.ref ⟨x, hx⟩).1)) ∘ C.planes₁.model (C.planes₁.ref ⟨x, hx⟩))
        (C.planes₁.coord (C.planes₁.ref ⟨x, hx⟩) (C.planes₁.pre ⟨x, hx⟩)) :
          ℝ →ₗ[ℝ] BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) ∧
      ∀ i : CGPMarkerIndex P.toLocalChartFamily,
        ρ (cgpMarkerCentre P.toLocalChartFamily i) ≤ ρ (C.planes₁.ref ⟨x, hx⟩).1 / 2 →
        x (cgpMarkerTag P.toLocalChartFamily P.zero i) = 0 ∧
          ∀ w ∈ C.toChain.plane 1 x, w (cgpMarkerTag P.toLocalChartFamily P.zero i) = 0) ∧
    (∀ (x : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
      (hx : x ∈ gafCloud P.toLocalChartFamily P.zero 2),
      C.toChain.plane 2 x = LinearMap.range (fderiv ℝ
        (blockRestrict (firstKeepTags_GAF5 P.toLocalChartFamily P.zero
            (ρ (C.planes₂.ref ⟨x, hx⟩).1)) ∘ C.planes₂.model (C.planes₂.ref ⟨x, hx⟩))
        (C.planes₂.coord (C.planes₂.ref ⟨x, hx⟩) (C.planes₂.pre ⟨x, hx⟩)) :
          ℝ →ₗ[ℝ] BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) ∧
      ∀ i : CGPMarkerIndex P.toLocalChartFamily,
        ρ (cgpMarkerCentre P.toLocalChartFamily i) ≤ ρ (C.planes₂.ref ⟨x, hx⟩).1 / 2 →
        x (cgpMarkerTag P.toLocalChartFamily P.zero i) = 0 ∧
          ∀ w ∈ C.toChain.plane 2 x, w (cgpMarkerTag P.toLocalChartFamily P.zero i) = 0) := by
  obtain ⟨hΛ, hΔ, -, -, -, -, -, -, -, -, -⟩ := C.toChain.std
  have hsmall : Λ * (1000000 * Δ) ≤ 1 / 4 := C.toChain.small_BAS
  exact ⟨fun a st x hx => ⟨keep_projMap_CFSB P.toLocalChartFamily P.zero hΔ hΛ hsmall a st hx,
      fun w => keep_projMap_mvfderiv_CFSB P.toLocalChartFamily P.zero hΔ hΛ hsmall a st hx w⟩,
    fun a => keep_own_CFSB P.toLocalChartFamily P.zero a, fun _ => norm_blockRestrict_le _,
    fun _ hx => C.cfs27_stage0_CFSB hx, fun _ hx => C.cfs27_stage1_CFSB hx,
    fun _ hx => C.cfs27_stage2_CFSB hx⟩

end Gaf02ChainE

end DifferentialGeometry.Geometry.Collapse
