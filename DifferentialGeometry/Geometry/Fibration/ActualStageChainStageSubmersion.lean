import DifferentialGeometry.Geometry.Fibration.ActualStageChainFinalBases
import DifferentialGeometry.Analysis.InnerProductSpace.StageRankComparison
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdpBlocks
import DifferentialGeometry.Geometry.Fibration.ActualStageChainSubmersionInputs
import DifferentialGeometry.Geometry.Fibration.ActualStageChainReplacement


/-!
# GAF02 BASES, first step: the actual stage submersions (circle, edge)

Blueprint `master207B.tex`, CFS17–CFS20 and GAF02 (B:5797); external draft 59 §4 first step
("p_j a submersion does NOT make p_j ∘ π_jg_{j−1} one": a transverse rank estimate is needed);
review 66 D66-7 step 1 (original rank + same-plane normal error + Da_j + CHOICE margin); review 71
D71-13 (P3). Chart form (as `W_st` in `ActualStageChainFinalBases`): at every point `p` of the chart
`j`'s ORIGINAL threshold-6 plateau, `D(κ_j ∘ f_st)(p)` is onto, `κ_j = R_j⁻¹u_j`.

* Generic kernels: `surjective_of_pp_tangent_BAS` (rank from (PP) via `rank_ge_of_pp_comparison_BAS`
  of lane C14-BASES-P, then `surjective_of_rank_le_BAS`), `surjective_of_unit_pp_tangent_BAS`
  (edge unit-vector form), `coframe_smul_BAS`, numeric budgets `stage_rank_small_BAS`,
  `stage_rank_small_delta_BAS`.
* Circle: `Gaf02Chain.circle_stage_core_BAS`, **`Gaf02Chain.stage_submersion_circle_BAS`**.
* Edge: `Gaf02Chain.mvfderiv_projMap_two_BAS`, `edge_unit_derivative_error_BAS`,
  `edge_stage_finish_BAS`, `edge_stage_core_BAS`, `edgeAxis_starProjection_two_BAS`,
  `edge_stage_hasMFDerivAt_BAS`, **`Gaf02Chain.stage_submersion_edge_BAS`**.
(The slim stage: lane C14-BASES-P, `stage_submersion_slim_BAS`.)
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

/-- The `ContinuousSMul` instance of the block factors, named (protocol pitfall 2026-10-05). -/
local instance instContinuousSMulPlaneBlock_BAS :
    ContinuousSMul ℝ (WithLp 2 (EuclideanSpace ℝ (Fin 2) × ℝ)) :=
  IsBoundedSMul.continuousSMul

/-- **The stage-submersion kernel** (D66-7 step 1, generic): the plane's (PP) data for `D0`, the
stage-input derivative `B` `δ`-close to `D0`, the native map's derivative `Q` `Ξ`-close to `π_L`
with range in a subspace `Tm` of dimension `dim L = dim E`, and a coframe `m‖w‖ ≤ a‖κ w‖` on `Tm`
(`m > 0`) give: `κ ∘ Q ∘ B` is onto. -/
theorem surjective_of_pp_tangent_BAS {V H E : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℝ H) (Bf : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (N : V → ℝ) (hNpos : ∀ v, v ≠ 0 → 0 < N v)
    (D0 B : V →ₗ[ℝ] H) (Q : H →L[ℝ] H) {e δ Ξ Cu : ℝ}
    (hsurj : Surjective fun v => L.orthogonalProjectionOnto (D0 v))
    (hnormal : ∀ v, ‖D0 v - (L.orthogonalProjectionOnto (D0 v) : H)‖ ≤ e * N v)
    (hlow : ∀ v, (∀ k, L.orthogonalProjectionOnto (D0 k) = 0 → Bf v k = 0) →
      1 / 2 * N v ≤ ‖L.orthogonalProjectionOnto (D0 v)‖)
    (hup : ∀ v, ‖L.orthogonalProjectionOnto (D0 v)‖ ≤ Cu * N v)
    (hB : ∀ v, ‖B v - D0 v‖ ≤ δ * N v) (hQ : ‖Q - L.starProjection‖ ≤ Ξ)
    (hΞ : 0 ≤ Ξ) (hsmall : δ + Ξ * (Cu + e + δ) < 1 / 2)
    (Tm : Submodule ℝ H) (hQT : LinearMap.range (Q : H →ₗ[ℝ] H) ≤ Tm)
    (hTdim : Module.finrank ℝ Tm = Module.finrank ℝ L)
    (hLdim : Module.finrank ℝ L = Module.finrank ℝ E) (κ : H →L[ℝ] E) {m a : ℝ}
    (hcof : ∀ w ∈ Tm, m * ‖w‖ ≤ a * ‖κ w‖) (hm : 0 < m) :
    Surjective fun v => κ (Q (B v)) := by
  have hrank := rank_ge_of_pp_comparison_BAS L Bf N hNpos D0 B Q hsurj hnormal hlow hup hB hQ hΞ
    hsmall
  have hinj : Set.InjOn (κ : H →ₗ[ℝ] E) Tm := by
    intro w₁ h₁ w₂ h₂ h12
    have hw : w₁ - w₂ ∈ Tm := Tm.sub_mem h₁ h₂
    have h0 : κ (w₁ - w₂) = 0 := by
      rw [map_sub, sub_eq_zero]
      exact h12
    have h := hcof _ hw
    rw [h0, norm_zero, mul_zero] at h
    have hn : ‖w₁ - w₂‖ = 0 := le_antisymm (by nlinarith [norm_nonneg (w₁ - w₂)]) (norm_nonneg _)
    rw [norm_eq_zero, sub_eq_zero] at hn
    exact hn
  have hs := surjective_of_rank_le_BAS B (Q : H →ₗ[ℝ] H) Tm hQT (κ : H →ₗ[ℝ] E) hinj
    (hTdim.trans hLdim) (hLdim ▸ hrank)
  exact hs

/-- Numeric budget of the stage-submersion kernel: `δ = 0`, `Ξ < 1/(1000(Ω+1))`, `Cu ≤ 3Ω`,
`e ≤ 1`. -/
theorem stage_rank_small_BAS {Ξ Ω Cu e : ℝ} (hΩ : 1 ≤ Ω) (hΞ0 : 0 ≤ Ξ)
    (hΞ : Ξ < 1 / (1000 * (Ω + 1))) (hCu : Cu ≤ 3 * Ω) (he : e ≤ 1) :
    0 + Ξ * (Cu + e + 0) < 1 / 2 := by
  have hΩ1 : 0 < Ω + 1 := by linarith
  rw [lt_div_iff₀ (by positivity)] at hΞ
  have h1 : Ξ * (Cu + e + 0) ≤ Ξ * (3 * Ω + 1) := by
    apply mul_le_mul_of_nonneg_left _ hΞ0
    linarith
  nlinarith

/-- **The stage-submersion kernel, one-dimensional (edge) form**: the unit-vector (PP) at `w₀`,
`B` `δ`-close to `D0` at `w₀`, `Q` `Ξ`-close to `π_L` with range in a line `Tm`, `dim E = 1`, and a
coframe on `Tm` give: `κ ∘ Q ∘ B` is onto. -/
theorem surjective_of_unit_pp_tangent_BAS {V H E : Type*} [AddCommGroup V] [Module ℝ V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℝ H) (D0 B : V →ₗ[ℝ] H) (Q : H →L[ℝ] H) {e δ Ξ Cu : ℝ} (w₀ : V)
    (hw₀ : 1 / 2 ≤ ‖L.starProjection (D0 w₀)‖) (hnormal : ‖D0 w₀ - L.starProjection (D0 w₀)‖ < e)
    (hup : ‖L.starProjection (D0 w₀)‖ ≤ Cu) (hB : ‖B w₀ - D0 w₀‖ ≤ δ)
    (hQ : ‖Q - L.starProjection‖ ≤ Ξ) (hΞ : 0 ≤ Ξ) (hsmall : δ + Ξ * (Cu + e + δ) < 1 / 2)
    (Tm : Submodule ℝ H) (hQT : LinearMap.range (Q : H →ₗ[ℝ] H) ≤ Tm)
    (hTdim : Module.finrank ℝ Tm = Module.finrank ℝ E) (hE : Module.finrank ℝ E = 1)
    (κ : H →L[ℝ] E) {m a : ℝ} (hcof : ∀ w ∈ Tm, m * ‖w‖ ≤ a * ‖κ w‖) (hm : 0 < m) :
    Surjective fun v => κ (Q (B v)) := by
  have hne := ne_zero_of_unit_pp_comparison_BAS L D0 B Q w₀ hw₀ hnormal hup hB hQ hΞ hsmall
  have hrank : Module.finrank ℝ E ≤
      Module.finrank ℝ (LinearMap.range ((Q : H →ₗ[ℝ] H) ∘ₗ B)) := by
    rw [hE, Nat.one_le_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
    intro h0
    have hmem : (Q : H →ₗ[ℝ] H) (B w₀) ∈ LinearMap.range ((Q : H →ₗ[ℝ] H) ∘ₗ B) := ⟨w₀, rfl⟩
    rw [h0, Submodule.mem_bot] at hmem
    exact hne hmem
  have hinj : Set.InjOn (κ : H →ₗ[ℝ] E) Tm := by
    intro w₁ h₁ w₂ h₂ h12
    have hw : w₁ - w₂ ∈ Tm := Tm.sub_mem h₁ h₂
    have h0 : κ (w₁ - w₂) = 0 := by
      rw [map_sub, sub_eq_zero]
      exact h12
    have h := hcof _ hw
    rw [h0, norm_zero, mul_zero] at h
    have hn : ‖w₁ - w₂‖ = 0 := le_antisymm (by nlinarith [norm_nonneg (w₁ - w₂)]) (norm_nonneg _)
    rw [norm_eq_zero, sub_eq_zero] at hn
    exact hn
  exact surjective_of_rank_le_BAS B (Q : H →ₗ[ℝ] H) Tm hQT (κ : H →ₗ[ℝ] E) hinj hTdim hrank

/-- Numeric budget of the edge kernel: `δ ≤ 1/512`, `Ξ < 1/(1000(Ω+1))`, `Cu ≤ 3Ω`,
`e ≤ 1`. -/
theorem stage_rank_small_delta_BAS {Ξ Ω Cu e δ : ℝ} (hΩ : 1 ≤ Ω) (hΞ0 : 0 ≤ Ξ)
    (hΞ : Ξ < 1 / (1000 * (Ω + 1))) (hCu : Cu ≤ 3 * Ω) (he : e ≤ 1)
    (hδ : δ ≤ 1 / 512) : δ + Ξ * (Cu + e + δ) < 1 / 2 := by
  have hΩ1 : 0 < Ω + 1 := by linarith
  rw [lt_div_iff₀ (by positivity)] at hΞ
  have h1 : Ξ * (Cu + e + δ) ≤ Ξ * (3 * Ω + 2) := by
    apply mul_le_mul_of_nonneg_left _ hΞ0
    linarith
  nlinarith

/-- A coframe bound for `u` gives one for `R⁻¹ • u` (`R > 0`). -/
theorem coframe_smul_BAS {H E : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (u : H →L[ℝ] E) {R m a : ℝ} (hR : 0 < R)
    (Tm : Set H) (h : ∀ w ∈ Tm, m * ‖w‖ ≤ a * ‖u w‖) :
    ∀ w ∈ Tm, m * ‖w‖ ≤ (a * R) * ‖(R⁻¹ • u) w‖ := by
  intro w hw
  rw [clm_smul_apply_BPRE, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
  have hr : a * R * (R⁻¹ * ‖u w‖) = a * ‖u w‖ := by
    field_simp
  rw [hr]
  exact h w hw

variable {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}

namespace Gaf02Chain

variable {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

/-- **The circle stage-submersion core** (chain level, at `x = 𝓔⁰ p` with preimage `p` in the
chart `j`'s plateau): `κ_j ∘ Da(x) ∘ D𝓔⁰(p)` is onto `ℝ²`. -/
theorem circle_stage_core_BAS (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (R : Gaf02RoughData C) (j : P.toLocalChartFamily.circle.finite_centres.toFinset)
    (O : Cfs15StageOutput (gafStageDim 0) Kj (Ξ 0) (cw 0) (gafCloud P.toLocalChartFamily P.zero 0)
      (gafCloudEnlarged P.toLocalChartFamily P.zero 0) (fun x => S 0 * ρ (C.sel 0 x)) (C.plane 0))
    {p : X} (hp : p ∈ ball j.1 (200 * ρ j.1))
    (hη : ‖cgpCoord P.toLocalChartFamily P.zero (.inl j) p‖ < 6) :
    ∀ y : ℝ², ∃ w : TangentSpace 𝓘(ℝ, E3) p,
      ((ρ j.1)⁻¹ • gafCircleVector P.toLocalChartPackets j)
        (fderiv ℝ O.ambient (cgpGlobalMap P.toLocalChartFamily P.zero p)
          (mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) p w)) = y := by
  have hx : cgpGlobalMap P.toLocalChartFamily P.zero p ∈ gafCloud P.toLocalChartFamily P.zero 0 := by
    rw [gafCloud_zero_GAF4]
    exact ⟨p, ⟨j, hp, hη.le.trans (by norm_num)⟩, rfl⟩
  have : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ, E3) p) := inferInstanceAs (FiniteDimensional ℝ E3)
  obtain ⟨i, hPP⟩ := C.test0.2.2.1 _ hx
  have hPPp := hPP p rfl
  have hρi := hρ i.1
  have hρj := hρ j.1
  have hΩ := one_le_gafGraphOmega_BAS
  obtain ⟨hΞ0, -, -, he0⟩ := C.numbers.1 0
  obtain ⟨hεos, heos, he2⟩ := R.os 0
  have hrx := O.radius_pos _ hx
  have hQ := (O.ambient_value_deriv hx (mem_ball_self hrx)).2.2
  have h06 := C.cgp06_circle_BAS R j hx rfl hp (hη.le.trans (by norm_num))
  have hm : ∀ v ∈ C.plane 0 (cgpGlobalMap P.toLocalChartFamily P.zero p),
      1 / (2 * gafGraphOmega_BAS) * ‖v‖ ≤ ‖gafCircleVector P.toLocalChartPackets j v‖ := by
    intro v hv
    have h := h06 v hv
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
    linarith
  obtain ⟨Tm, hQT, hTdim, hcof⟩ := Cfs15StageOutput.ambient_tangent_coframe_BAS O ⟨_, hx⟩ (mem_ball_self hrx)
    (gafCircleVector P.toLocalChartPackets j) (norm_blockVectorCLM_le _) hm
    (R.eps_lt_margin_BAS 0).2
  have hm0 : 0 < 1 / (2 * gafGraphOmega_BAS) - Ξ 0 / 3 := by
    linarith [(R.eps_lt_margin_BAS 0).2]
  have hcof' : ∀ w ∈ Tm, (1 / (2 * gafGraphOmega_BAS) - Ξ 0 / 3) * ‖w‖ ≤
      ((1 + Ξ 0 / 3) * ρ j.1) * ‖((ρ j.1)⁻¹ • gafCircleVector P.toLocalChartPackets j) w‖ := by
    intro w hw
    have h := hcof w hw
    rw [clm_smul_apply_BPRE, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hρj)]
    have hr : ρ j.1 * ((ρ j.1)⁻¹ * ‖gafCircleVector P.toLocalChartPackets j w‖) =
        ‖gafCircleVector P.toLocalChartPackets j w‖ := by
      field_simp
    calc _ ≤ (1 + Ξ 0 / 3) * ‖gafCircleVector P.toLocalChartPackets j w‖ := h
      _ = _ := by rw [mul_assoc, hr]
  have hLdim : Module.finrank ℝ (C.plane 0 (cgpGlobalMap P.toLocalChartFamily P.zero p)) =
      Module.finrank ℝ ℝ² := by
    rw [(C.test0.1 _ hx).1, finrank_euclideanSpace_fin]
    rfl
  have hsurj := surjective_of_pp_tangent_BAS (V := TangentSpace 𝓘(ℝ, E3) p)
    (C.plane 0 (cgpGlobalMap P.toLocalChartFamily P.zero p))
    (ContinuousLinearMap.toLinearMap₁₂ (g.inner p))
    (fun w => Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner p w w))
    (fun w hw => Real.sqrt_pos.mpr (mul_pos (by positivity) (g.pos p w hw)))
    (((ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) p :
      TangentSpace 𝓘(ℝ, E3) p →L[ℝ] BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) :
        TangentSpace 𝓘(ℝ, E3) p →ₗ[ℝ] BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    (((ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) p :
      TangentSpace 𝓘(ℝ, E3) p →L[ℝ] BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) :
        TangentSpace 𝓘(ℝ, E3) p →ₗ[ℝ] BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    (fderiv ℝ O.ambient (cgpGlobalMap P.toLocalChartFamily P.zero p)) (δ := 0)
    hPPp.1 hPPp.2.1 (fun w hw => hPPp.2.2.1 w (fun k hk => by simpa using hw k hk)) hPPp.2.2.2
    (fun w => by simp) hQ hΞ0.le
    (stage_rank_small_BAS hΩ hΞ0.le hεos (by linarith [tcpGraphConst_le_gafGraphOmega_BAS])
      (by
        have h48 : 1 / (48 * gafGraphOmega_BAS) ≤ 1 / 48 :=
          one_div_le_one_div_of_le (by norm_num) (by linarith)
        linarith))
    Tm hQT hTdim hLdim ((ρ j.1)⁻¹ • gafCircleVector P.toLocalChartPackets j) hcof' hm0
  intro y
  obtain ⟨v, hv⟩ := hsurj y
  refine ⟨(ρ i.1)⁻¹ • v, ?_⟩
  rw [map_smul]
  exact hv

/-- **Stage submersion, circle stage** (draft 59 §4 step 1, D66-7; chart form): at every point
`p` of the circle chart `j`'s ORIGINAL threshold-6 plateau, `D(κ_j ∘ f₁)(p)` is onto `ℝ²`
(`κ_j = R_j⁻¹u_j`, the chart coordinate of `W₁` and of `V_j⁰`). Inputs: the plane's (PP) at
`x = 𝓔⁰ p` with preimage `p` (`C.test0`), the native map's derivative `Ξ₁`-close to `π_{L_x}`,
its range in the graph tangent with CGP06's coframe (`cgp06_circle_BAS`), `(OS)`. -/
theorem stage_submersion_circle_BAS (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (R : Gaf02RoughData C) (j : P.toLocalChartFamily.circle.finite_centres.toFinset) {p : X}
    (hp : p ∈ ball j.1 (200 * ρ j.1))
    (hη : ‖cgpCoord P.toLocalChartFamily P.zero (.inl j) p‖ < 6) :
    Surjective (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²) (fun q =>
      ((ρ j.1)⁻¹ • gafCircleVector P.toLocalChartPackets j) (C.stageMap_BAS 0 q)) p) := by
  have hj : j.1 ∈ P.circle.centres := (Set.Finite.mem_toFinset _).mp j.2
  cases hO : C.slot 0 with
  | inactive h =>
    exfalso
    have h' : P.circle.centres = ∅ := h
    exact Set.eq_empty_iff_forall_notMem.mp h' _ hj
  | active O =>
  have hx : cgpGlobalMap P.toLocalChartFamily P.zero p ∈ gafCloud P.toLocalChartFamily P.zero 0 := by
    rw [gafCloud_zero_GAF4]
    exact ⟨p, ⟨j, hp, hη.le.trans (by norm_num)⟩, rfl⟩
  have hrx := O.radius_pos _ hx
  have hloc := C.stageMap_eventuallyEq_BAS hO (p := p) ⟨j, hp, hη⟩
  have hfun : (fun q => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection
      (O.ambient ((gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.stageIn_BAS 0 q)))) =
      fun q => O.ambient (cgpGlobalMap P.toLocalChartFamily P.zero q) := by
    funext q
    rw [gafStageQ_zero_starProjection_BAS, gafStageQ_zero_starProjection_BAS]
    rfl
  rw [hfun] at hloc
  have hloc' : (fun q => ((ρ j.1)⁻¹ • gafCircleVector P.toLocalChartPackets j)
      (C.stageMap_BAS 0 q)) =ᶠ[𝓝 p] fun q => ((ρ j.1)⁻¹ • gafCircleVector P.toLocalChartPackets j)
        (O.ambient (cgpGlobalMap P.toLocalChartFamily P.zero q)) :=
    hloc.mono fun q hq => congrArg _ hq
  rw [hloc'.mfderiv_eq]
  have hxΩ := mem_cfs15Omega_of_mem_C15 (r := fun x => S 0 * ρ (C.sel 0 x)) hx (mem_ball_self hrx)
  have ha : DifferentiableAt ℝ O.ambient (cgpGlobalMap P.toLocalChartFamily P.zero p) :=
    (O.ambient_contDiffAt hxΩ).differentiableAt (by simp)
  have hF : MDifferentiableAt 𝓘(ℝ, E3)
      𝓘(ℝ, BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
      (cgpGlobalMap P.toLocalChartFamily P.zero) p :=
    (C.globalMap_smooth_EDPE p).mdifferentiableAt (by simp)
  have hg : HasFDerivAt (fun z => ((ρ j.1)⁻¹ • gafCircleVector P.toLocalChartPackets j)
      (O.ambient z)) (((ρ j.1)⁻¹ • gafCircleVector P.toLocalChartPackets j).comp
        (fderiv ℝ O.ambient (cgpGlobalMap P.toLocalChartFamily P.zero p)))
      (cgpGlobalMap P.toLocalChartFamily P.zero p) :=
    ((ρ j.1)⁻¹ • gafCircleVector P.toLocalChartPackets j).hasFDerivAt.comp _ ha.hasFDerivAt
  have hcomp := hg.hasMFDerivAt.comp p hF.hasMFDerivAt
  change Surjective (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²) ((fun z =>
    ((ρ j.1)⁻¹ • gafCircleVector P.toLocalChartPackets j) (O.ambient z)) ∘
      cgpGlobalMap P.toLocalChartFamily P.zero) p)
  rw [hcomp.mfderiv]
  intro y
  obtain ⟨w, hw⟩ := C.circle_stage_core_BAS R j O hp hη y
  exact ⟨w, hw⟩

/-- `π₂𝓔⁰`'s derivative is `π_{Q₂}` of `𝓔⁰`'s. -/
theorem mvfderiv_projMap_two_BAS (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw) (p : X)
    (w : TangentSpace 𝓘(ℝ, E3) p) :
    mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily
      P.zero)) p w = (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (mvfderiv 𝓘(ℝ, E3)
        (cgpGlobalMap P.toLocalChartFamily P.zero) p w) := by
  have hfun : cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero) =
      fun q => (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (cgpGlobalMap P.toLocalChartFamily P.zero q) :=
    funext fun q => (gafStageQ_one_globalMap_BAS q).symm
  have hF : MDifferentiableAt 𝓘(ℝ, E3)
      𝓘(ℝ, BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
      (cgpGlobalMap P.toLocalChartFamily P.zero) p :=
    (C.globalMap_smooth_EDPE p).mdifferentiableAt (by simp)
  have h := ((gafStageQ P.toLocalChartFamily P.zero 1).starProjection).hasFDerivAt.hasMFDerivAt.comp p hF.hasMFDerivAt
  rw [hfun]
  change (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    ((fun y => (gafStageQ P.toLocalChartFamily P.zero 1).starProjection y) ∘ cgpGlobalMap P.toLocalChartFamily P.zero) p) w = _
  rw [h.mfderiv]
  rfl

/-- The rescaled derivative error of `g₁` against `π₂𝓔⁰` at a unit vector (reference scale
`ρ_i`): `‖(ρ_i)⁻¹(π₂ Dg₁(p) w₀ − D(π₂𝓔⁰)(p) w₀)‖ ≤ H` when `‖Dg₁ − D𝓔⁰‖ ≤ H√g`. -/
theorem edge_unit_derivative_error_BAS (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (p : X) {i : X} (w₀ : TangentSpace 𝓘(ℝ, E3) p) (hw₀u : (ρ i)⁻¹ ^ 2 * g.inner p w₀ w₀ = 1)
    {Hd : ℝ} (hder : ‖mvfderiv 𝓘(ℝ, E3) C.g₁ p w₀ -
      mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) p w₀‖ ≤
        Hd * Real.sqrt (g.inner p w₀ w₀)) :
    ‖((ρ i)⁻¹ • ((gafStageQ P.toLocalChartFamily P.zero 1).starProjection).comp (mvfderiv 𝓘(ℝ, E3) C.g₁ p)) w₀ -
      ((ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
        (cgpQ2Tags P.toLocalChartFamily P.zero)) p) w₀‖ ≤ Hd := by
  have hρi := hρ i
  have h0 : ((ρ i)⁻¹ • ((gafStageQ P.toLocalChartFamily P.zero 1).starProjection).comp (mvfderiv 𝓘(ℝ, E3) C.g₁ p)) w₀ -
      ((ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
        (cgpQ2Tags P.toLocalChartFamily P.zero)) p) w₀ =
      (ρ i)⁻¹ • (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (mvfderiv 𝓘(ℝ, E3) C.g₁ p w₀ -
        mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) p w₀) := by
    change (ρ i)⁻¹ • (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (mvfderiv 𝓘(ℝ, E3) C.g₁ p w₀) -
      (ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
        (cgpQ2Tags P.toLocalChartFamily P.zero)) p w₀ = _
    rw [C.mvfderiv_projMap_two_BAS p, ← smul_sub, ← map_sub]
  rw [h0, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hρi)]
  have h1 := ((gafStageQ P.toLocalChartFamily P.zero 1).starProjection).le_opNorm (mvfderiv 𝓘(ℝ, E3) C.g₁ p w₀ -
    mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) p w₀)
  have h2 : ‖((gafStageQ P.toLocalChartFamily P.zero 1).starProjection : _ →L[ℝ] _)‖ ≤ 1 := Submodule.starProjection_norm_le _
  have hsq : Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner p w₀ w₀) =
      (ρ i)⁻¹ * Real.sqrt (g.inner p w₀ w₀) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  rw [hw₀u, Real.sqrt_one] at hsq
  have hn := norm_nonneg (mvfderiv 𝓘(ℝ, E3) C.g₁ p w₀ -
    mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) p w₀)
  have h3 : ‖(gafStageQ P.toLocalChartFamily P.zero 1).starProjection (mvfderiv 𝓘(ℝ, E3) C.g₁ p w₀ -
      mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) p w₀)‖ ≤
      Hd * Real.sqrt (g.inner p w₀ w₀) :=
    h1.trans ((mul_le_of_le_one_left hn h2).trans hder)
  have h4 := mul_le_mul_of_nonneg_left h3 (inv_nonneg.mpr hρi.le)
  calc _ ≤ (ρ i)⁻¹ * (Hd * Real.sqrt (g.inner p w₀ w₀)) := h4
    _ = Hd * ((ρ i)⁻¹ * Real.sqrt (g.inner p w₀ w₀)) := by ring
    _ = Hd := by rw [← hsq, mul_one]

/-- The edge stage-submersion core from its prepared data (reference `i`, unit vector `w₀` of the
plane's (PP) at `p`, derivative budget `Hd`, coframe lower bound on `L_x`). -/
theorem edge_stage_finish_BAS (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (R : Gaf02RoughData C) (j : P.edge.finite_centres.toFinset)
    (O : Cfs15StageOutput (gafStageDim 1) Kj (Ξ 1) (cw 1) (gafCloud P.toLocalChartFamily P.zero 1)
      (gafCloudEnlarged P.toLocalChartFamily P.zero 1) (fun x => S 1 * ρ (C.sel 1 x)) (C.plane 1))
    {p : X} (hx : (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (cgpGlobalMap P.toLocalChartFamily P.zero p) ∈ gafCloud P.toLocalChartFamily P.zero 1)
    (hz : (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (C.g₁ p) ∈ ball ((gafStageQ P.toLocalChartFamily P.zero 1).starProjection (cgpGlobalMap P.toLocalChartFamily P.zero p))
      (S 1 * ρ (C.sel 1 ((gafStageQ P.toLocalChartFamily P.zero 1).starProjection (cgpGlobalMap P.toLocalChartFamily P.zero p)))))
    {i : X} (w₀ : TangentSpace 𝓘(ℝ, E3) p) (hw₀u : (ρ i)⁻¹ ^ 2 * g.inner p w₀ w₀ = 1)
    (hw₀ : 1 / 2 ≤ ‖(C.plane 1 ((gafStageQ P.toLocalChartFamily P.zero 1).starProjection (cgpGlobalMap P.toLocalChartFamily P.zero p))).starProjection
      ((ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero)) p w₀)‖)
    (hnormal : ‖(ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero)) p w₀ - (C.plane 1 ((gafStageQ P.toLocalChartFamily P.zero 1).starProjection (cgpGlobalMap P.toLocalChartFamily P.zero p))).starProjection
      ((ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero)) p w₀)‖ < eg 1)
    (hup : ‖(C.plane 1 ((gafStageQ P.toLocalChartFamily P.zero 1).starProjection (cgpGlobalMap P.toLocalChartFamily P.zero p))).starProjection
      ((ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero)) p w₀)‖ ≤ 3 * egpGraphConst)
    {Hd : ℝ} (hHd : Hd < c 0) (hder : ‖mvfderiv 𝓘(ℝ, E3) C.g₁ p w₀ -
      mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) p w₀‖ ≤
        Hd * Real.sqrt (g.inner p w₀ w₀))
    (hm : ∀ v ∈ C.plane 1 ((gafStageQ P.toLocalChartFamily P.zero 1).starProjection (cgpGlobalMap P.toLocalChartFamily P.zero p)),
      1 / (2 * gafGraphOmega_BAS) * ‖v‖ ≤
        ‖(axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j)) v‖) :
    ∀ y : ℝ, ∃ w : TangentSpace 𝓘(ℝ, E3) p,
      ((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j))
        (fderiv ℝ O.ambient ((gafStageQ P.toLocalChartFamily P.zero 1).starProjection (C.g₁ p))
          ((gafStageQ P.toLocalChartFamily P.zero 1).starProjection (mvfderiv 𝓘(ℝ, E3) C.g₁ p w))) = y := by
  have hρj := hρ j.1
  have hΩ := one_le_gafGraphOmega_BAS
  have hΞ0 := (C.numbers.1 1).1
  have hεos := (R.os 1).1
  have he2 := (R.os 1).2.2
  have hQ := (O.ambient_value_deriv hx hz).2.2
  refine (Cfs15StageOutput.ambient_tangent_coframe_BAS O ⟨_, hx⟩ hz
    (axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j)) (norm_edgeAxis_le_BAS j) hm
    (R.eps_lt_margin_BAS 1).2).elim fun Tm hT => ?_
  have hm0 : 0 < 1 / (2 * gafGraphOmega_BAS) - Ξ 1 / 3 := by
    linarith [(R.eps_lt_margin_BAS 1).2]
  have hcof' := coframe_smul_BAS (axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j))
    hρj _ hT.2.2
  have hdim1 : Module.finrank ℝ (C.plane 1 ((gafStageQ P.toLocalChartFamily P.zero 1).starProjection (cgpGlobalMap P.toLocalChartFamily P.zero p))) = Module.finrank ℝ ℝ :=
    (C.test1.1 _ hx).1.trans (Module.finrank_self ℝ).symm
  have hTdim' : Module.finrank ℝ Tm = Module.finrank ℝ ℝ := hT.2.1.trans hdim1
  have hB := C.edge_unit_derivative_error_BAS p w₀ hw₀u hder
  have hsurj := surjective_of_unit_pp_tangent_BAS (V := TangentSpace 𝓘(ℝ, E3) p)
    (C.plane 1 ((gafStageQ P.toLocalChartFamily P.zero 1).starProjection (cgpGlobalMap P.toLocalChartFamily P.zero p)))
    (((ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero)) p :
      TangentSpace 𝓘(ℝ, E3) p →L[ℝ] BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) :
        TangentSpace 𝓘(ℝ, E3) p →ₗ[ℝ] BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    (((ρ i)⁻¹ • ((gafStageQ P.toLocalChartFamily P.zero 1).starProjection).comp (mvfderiv 𝓘(ℝ, E3) C.g₁ p) :
      TangentSpace 𝓘(ℝ, E3) p →L[ℝ] BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) :
        TangentSpace 𝓘(ℝ, E3) p →ₗ[ℝ] BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    (fderiv ℝ O.ambient ((gafStageQ P.toLocalChartFamily P.zero 1).starProjection (C.g₁ p))) w₀ hw₀ hnormal hup hB hQ hΞ0.le
    (stage_rank_small_delta_BAS hΩ hΞ0.le hεos (by linarith [egpGraphConst_le_gafGraphOmega_BAS])
      (by
        have h48 : 1 / (48 * gafGraphOmega_BAS) ≤ 1 / 48 :=
          one_div_le_one_div_of_le (by norm_num) (by linarith)
        linarith only [he2, h48])
      (by linarith only [hHd, C.c_le_BAS 0]))
    Tm hT.1 hTdim' (Module.finrank_self ℝ) ((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j)) hcof' hm0
  intro y
  obtain ⟨v, hv⟩ := hsurj y
  refine ⟨(ρ i)⁻¹ • v, ?_⟩
  rw [map_smul, map_smul]
  exact hv

/-- **The edge stage-submersion core** (at `x = π₂𝓔⁰ p`, preimage `p` in the edge chart `j`'s
plateau, `z = π₂ g₁ p`): `κ_j ∘ Da(z) ∘ π₂ ∘ Dg₁(p)` is onto `ℝ`. -/
theorem edge_stage_core_BAS (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (R : Gaf02RoughData C) (j : P.edge.finite_centres.toFinset)
    (O : Cfs15StageOutput (gafStageDim 1) Kj (Ξ 1) (cw 1) (gafCloud P.toLocalChartFamily P.zero 1)
      (gafCloudEnlarged P.toLocalChartFamily P.zero 1) (fun x => S 1 * ρ (C.sel 1 x)) (C.plane 1))
    {p : X} (hp : p ∈ ball j.1 (100 * Δ * ρ j.1)) (hη : |P.edge.coord j.1 p| < 6 * Δ)
    (ht : cgpHeight P.toLocalChartFamily p < 6 * Δ) :
    ∀ y : ℝ, ∃ w : TangentSpace 𝓘(ℝ, E3) p,
      ((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j))
        (fderiv ℝ O.ambient ((gafStageQ P.toLocalChartFamily P.zero 1).starProjection (C.g₁ p))
          ((gafStageQ P.toLocalChartFamily P.zero 1).starProjection (mvfderiv 𝓘(ℝ, E3) C.g₁ p w))) = y := by
  obtain ⟨-, hΔ, -⟩ := C.std
  have hcut := C.cutoff_eq_one_of_plateau_BAS (st := 1) (p := p) ⟨j, hp, hη, ht⟩
  have hin := C.stage_input_mem_omega_BAS (st := 1) (p := p) (by rw [hcut]; exact one_ne_zero)
  have hxp : cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero) p =
      (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (cgpGlobalMap P.toLocalChartFamily P.zero p) := (gafStageQ_one_globalMap_BAS p).symm
  have hΩ := one_le_gafGraphOmega_BAS
  have h06 := C.cgp06_edge_BAS R j hin.1 hxp hp (by linarith) (by linarith)
  have hm : ∀ v ∈ C.plane 1 ((gafStageQ P.toLocalChartFamily P.zero 1).starProjection (cgpGlobalMap P.toLocalChartFamily P.zero p)),
      1 / (2 * gafGraphOmega_BAS) * ‖v‖ ≤
        ‖(axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j)) v‖ := fun v hv =>
    inv_two_mul_le_of_le_BAS (by linarith only [hΩ]) (h06 v hv)
  exact (C.test1.2.2.1 _ hin.1).elim fun i hi => (C.stage_derivative_lt.1).elim fun Hd hHd =>
    (hi.2 p hxp).2.2.1.elim fun w₀ hw₀ => C.edge_stage_finish_BAS R j O hin.1 hin.2.1 w₀ hw₀.1 hw₀.2
      ((hi.2 p hxp).1 w₀ hw₀.1) ((hi.2 p hxp).2.1 w₀ hw₀.1) hHd.1 (hHd.2 p w₀) hm

/-- `κ_j` reads only the edge block, which `π_{Q₂}` keeps. -/
theorem edgeAxis_starProjection_two_BAS (j : P.edge.finite_centres.toFinset)
    (z : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) :
    ((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j)) ((gafStageQ P.toLocalChartFamily P.zero 1).starProjection z) = ((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j)) z := by
  rw [clm_smul_apply_BPRE, clm_smul_apply_BPRE, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, gafEdgeVector, gafStageQ_edgeVector_FDC]

/-- The derivative of `κ_j ∘ f₂` at a plateau point of the edge chart `j`:
`κ_j ∘ Da(z) ∘ π₂ ∘ Dg₁(p)` (`z = π₂ g₁ p`). -/
theorem edge_stage_hasMFDerivAt_BAS (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (j : P.edge.finite_centres.toFinset)
    {O : Cfs15StageOutput (gafStageDim 1) Kj (Ξ 1) (cw 1) (gafCloud P.toLocalChartFamily P.zero 1)
      (gafCloudEnlarged P.toLocalChartFamily P.zero 1) (fun x => S 1 * ρ (C.sel 1 x)) (C.plane 1)}
    (hO : C.slot 1 = .active O) {p : X} (hp : p ∈ ball j.1 (100 * Δ * ρ j.1))
    (hη : |P.edge.coord j.1 p| < 6 * Δ) (ht : cgpHeight P.toLocalChartFamily p < 6 * Δ) :
    HasMFDerivAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (fun q => ((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j)) (C.stageMap_BAS 1 q)) p
      (((((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j))).comp ((fderiv ℝ O.ambient ((gafStageQ P.toLocalChartFamily P.zero 1).starProjection (C.g₁ p))).comp
        (gafStageQ P.toLocalChartFamily P.zero 1).starProjection)).comp (mfderiv 𝓘(ℝ, E3)
          𝓘(ℝ, BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) C.g₁ p)) := by
  have hcut := C.cutoff_eq_one_of_plateau_BAS (st := 1) (p := p) ⟨j, hp, hη, ht⟩
  have hin := C.stage_input_mem_omega_BAS (st := 1) (p := p) (by rw [hcut]; exact one_ne_zero)
  have hloc := C.stageMap_eventuallyEq_BAS hO (p := p) ⟨j, hp, hη, ht⟩
  have hloc' : (fun q => ((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j)) (C.stageMap_BAS 1 q)) =ᶠ[𝓝 p]
      (fun y => ((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j)) (O.ambient ((gafStageQ P.toLocalChartFamily P.zero 1).starProjection y))) ∘ C.g₁ :=
    hloc.mono fun q hq => by
      beta_reduce at hq ⊢
      rw [hq]
      exact edgeAxis_starProjection_two_BAS j _
  have ha : DifferentiableAt ℝ O.ambient ((gafStageQ P.toLocalChartFamily P.zero 1).starProjection (C.g₁ p)) :=
    (O.ambient_contDiffAt hin.2.2).differentiableAt (by simp)
  have hg₁ : MDifferentiableAt 𝓘(ℝ, E3)
      𝓘(ℝ, BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) C.g₁ p :=
    (C.stage_smooth.1 p).mdifferentiableAt (by simp)
  have hg : HasFDerivAt (fun y => ((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j)) (O.ambient ((gafStageQ P.toLocalChartFamily P.zero 1).starProjection y)))
      ((((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j))).comp ((fderiv ℝ O.ambient ((gafStageQ P.toLocalChartFamily P.zero 1).starProjection (C.g₁ p))).comp
        (gafStageQ P.toLocalChartFamily P.zero 1).starProjection)) (C.g₁ p) :=
    (((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j))).hasFDerivAt.comp _ (ha.hasFDerivAt.comp _ ((gafStageQ P.toLocalChartFamily P.zero 1).starProjection).hasFDerivAt)
  exact (hg.hasMFDerivAt.comp p hg₁.hasMFDerivAt).congr_of_eventuallyEq hloc'

/-- **Stage submersion, edge stage** (draft 59 §4 step 1, D66-7; chart form): at every point `p`
of the edge chart `j`'s ORIGINAL threshold-6 plateau, `D(κ_j ∘ f₂)(p)` is onto `ℝ`
(`κ_j = R_j⁻¹u_j`, the ACTUAL one-dimensional axis coordinate). Inputs: the plane's unit-vector
(PP) at `x = π₂𝓔⁰ p` with preimage `p` (`C.test1`), `g₁`'s derivative error (`C.stage_derivative_lt`,
`H < c₁ ≤ 1/512`), the native map's derivative `Ξ₂`-close to `π_{L_x}` with range in the graph
tangent and CGP06's coframe (`cgp06_edge_BAS`), `(OS)`. -/
theorem stage_submersion_edge_BAS (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (R : Gaf02RoughData C) (j : P.edge.finite_centres.toFinset) {p : X}
    (hp : p ∈ ball j.1 (100 * Δ * ρ j.1)) (hη : |P.edge.coord j.1 p| < 6 * Δ)
    (ht : cgpHeight P.toLocalChartFamily p < 6 * Δ) :
    Surjective (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (fun q =>
      ((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j)) (C.stageMap_BAS 1 q)) p) := by
  have hj : j.1 ∈ P.edge.centres := (Set.Finite.mem_toFinset _).mp j.2
  cases hO : C.slot 1 with
  | inactive h =>
    exfalso
    have h' : P.edge.centres = ∅ := h
    exact Set.eq_empty_iff_forall_notMem.mp h' _ hj
  | active O =>
  rw [(C.edge_stage_hasMFDerivAt_BAS j hO hp hη ht).mfderiv]
  intro y
  obtain ⟨w, hw⟩ := C.edge_stage_core_BAS R j O hp hη ht y
  exact ⟨w, hw⟩

end Gaf02Chain

end DifferentialGeometry.Geometry.Collapse
