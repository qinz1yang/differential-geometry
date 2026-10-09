import DifferentialGeometry.Geometry.Fibration.ActualStageChainSubmersionInputsApplications
import DifferentialGeometry.Geometry.Fibration.ActualStageChainChartSlim
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdpBlocks
import DifferentialGeometry.Analysis.InnerProductSpace.StageRankComparison

/-!
# GAF02 BASES step 1, slim stage: the stage submersion (frozen batch 2, (d))

Blueprint `master207B.tex`, GAF02 (B:5797–5870); draft 59 §4 step 1; review 66 (D66-7: "original
rank + same-plane normal error + `Da_j` + CHOICE margin"). Frozen statement of lane C14-BASESb
(`ParallelTargets2.lean`): `Gaf02Chain.stage_submersion_slim_BAS`.

At `p` in the slim chart `j`'s original threshold-6 plateau, with `x = π₃𝓔⁰(p) ∈ S₃` and
`z = π₃g₂(p) ∈ B(x, r_x)`:

* near `p`, `κ_j ∘ f₃ = κ_j ∘ a ∘ π₃ ∘ g₂` (`stageMap_eventuallyEq_BAS` and the retention
  `κ_j ∘ π₃ = κ_j`), so `D(κ_j ∘ f₃)(p) = κ_j ∘ Da(z) ∘ π₃ ∘ Dg₂(p)`;
* rank: `rank_ge_of_pp_comparison_BAS` with `D0 = ρ_i⁻¹D(π₃𝓔⁰)(p)` (the plane's (PP) at `x`, preimage
  `p`, `C.test2`), `B = ρ_i⁻¹π₃Dg₂(p)` (`δ = H_d < c₂`, GAF02 CORE's derivative budget for `g₂`),
  `Q = Da(z)` (`‖Da(z) − π_{L_x}‖ ≤ Ξ₃`), `Cu = 3C_*`, `e = e₃`, margin from (OS);
* `range Da(z)` lies in the graph tangent `Tm` with `dim Tm = dim L_x = 1`, on which `u_j` is
  injective (`ambient_injOn_tangent_BASP` with CGP06's `m = 1/(2Ω)`, `cgp06_slim_BAS`);
* `surjective_of_rank_le_BAS`.
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
local instance instContinuousSMulPlaneBlock_BASP :
    ContinuousSMul ℝ (WithLp 2 (EuclideanSpace ℝ (Fin 2) × ℝ)) :=
  IsBoundedSMul.continuousSMul

/-- Numeric margin of the slim rank comparison: `δ ≤ 1/512`, `Ξ < 1/(1000(Ω+1))`, `Cu ≤ 3Ω`,
`e ≤ 1` give `δ + Ξ(Cu + e + δ) < 1/2`. -/
theorem slim_rank_small_BASP {δ Ξ Ω Cu e : ℝ} (hΩ : 1 ≤ Ω) (hΞ0 : 0 ≤ Ξ)
    (hΞ : Ξ < 1 / (1000 * (Ω + 1))) (hCu : Cu ≤ 3 * Ω) (he : e ≤ 1) (hδ : δ ≤ 1 / 512) :
    δ + Ξ * (Cu + e + δ) < 1 / 2 := by
  have hΩ1 : 0 < Ω + 1 := by linarith
  rw [lt_div_iff₀ (by positivity)] at hΞ
  have h1 : Ξ * (Cu + e + δ) ≤ Ξ * (3 * (Ω + 1)) := by
    apply mul_le_mul_of_nonneg_left _ hΞ0
    linarith
  have h2 : Ξ * (3 * (Ω + 1)) < 3 / 1000 := by nlinarith
  linarith

/-- The manifold derivative of a continuous linear map after a vector-valued map:
`D(A ∘ f)(x) v = A (Df(x) v)`. -/
theorem mvfderiv_clm_comp_apply_BASP {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [TopologicalSpace H'] {I : ModelWithCorners ℝ E' H'} {M : Type*} [TopologicalSpace M]
    [ChartedSpace H' M] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (A : F →L[ℝ] F)
    {f : M → F} {x : M} (hf : MDifferentiableAt I 𝓘(ℝ, F) f x) (v : TangentSpace I x) :
    mvfderiv I (A ∘ f) x v = A (mvfderiv I f x v) := by
  rw [mvfderiv_comp_apply x A.mdifferentiableAt hf, mvfderiv_eq_fderiv, ContinuousLinearMap.fderiv]
  rfl

/-- A map locally equal to one with a surjective derivative has a surjective derivative. -/
theorem surjective_mfderiv_of_eventuallyEq_BASP {E' H' : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [TopologicalSpace H'] {I : ModelWithCorners ℝ E' H'} {M : Type*}
    [TopologicalSpace M] [ChartedSpace H' M] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f f' : M → F} {x : M} {L : TangentSpace I x →L[ℝ] F} (hev : f =ᶠ[𝓝 x] f')
    (hL : HasMFDerivAt I 𝓘(ℝ, F) f' x L) (hs : Surjective L) :
    Surjective (mfderiv I 𝓘(ℝ, F) f x) := by
  rw [hev.mfderiv_eq, hL.mfderiv]
  exact hs

variable {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}

namespace Gaf02Chain

variable {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

/-- The derivative of `π₃𝓔⁰` is `π₃ ∘ D𝓔⁰`. -/
theorem mvfderiv_projMap_two_BASP (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw) (p : X)
    (w : TangentSpace 𝓘(ℝ, E3) p) :
    mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
      (cgpQ3Tags P.toLocalChartFamily P.zero)) p w =
      (gafStageQ P.toLocalChartFamily P.zero 2).starProjection
        (mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) p w) := by
  have hfun : cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero) =
      (gafStageQ P.toLocalChartFamily P.zero 2).starProjection ∘
        cgpGlobalMap P.toLocalChartFamily P.zero :=
    funext fun q => (gafStageQ_starProjection_globalMap P.toLocalChartFamily P.zero 2 q).symm
  rw [hfun]
  exact mvfderiv_clm_comp_apply_BASP _ ((C.globalMap_smooth_EDPE p).mdifferentiableAt (by simp)) w

/-- The stage-input derivative is close to the original one at the slim stage: with GAF02
CORE's budget `‖Dg₂ − D𝓔⁰‖ ≤ H_d|·|_g`, `‖r⁻¹π₃Dg₂(p)v − r⁻¹D(π₃𝓔⁰)(p)v‖ ≤ H_d√(r⁻²g(v,v))`. -/
theorem slim_stage_input_close_BASP (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (p : X) {Hd : ℝ} (hHdb : ∀ (q : X) (w : TangentSpace 𝓘(ℝ, E3) q),
      ‖mvfderiv 𝓘(ℝ, E3) C.g₂ q w - mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) q w‖ ≤
        Hd * Real.sqrt (g.inner q w w)) {r : ℝ} (hr : 0 < r) (v : TangentSpace 𝓘(ℝ, E3) p) :
    ‖(r⁻¹ • (gafStageQ P.toLocalChartFamily P.zero 2).starProjection
          (mvfderiv 𝓘(ℝ, E3) C.g₂ p v)) -
        r⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
          (cgpQ3Tags P.toLocalChartFamily P.zero)) p v‖ ≤
      Hd * Real.sqrt (r⁻¹ ^ 2 * g.inner p v v) := by
  rw [C.mvfderiv_projMap_two_BASP p v, ← smul_sub, ← map_sub, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hr)]
  have h1 := (Submodule.norm_starProjection_apply_le (gafStageQ P.toLocalChartFamily P.zero 2)
    (mvfderiv 𝓘(ℝ, E3) C.g₂ p v - mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero)
      p v)).trans (hHdb p v)
  have hsq : Real.sqrt (r⁻¹ ^ 2 * g.inner p v v) = r⁻¹ * Real.sqrt (g.inner p v v) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  rw [hsq]
  have h2 := mul_le_mul_of_nonneg_left h1 (inv_pos.mpr hr).le
  linarith

/-- The slim rank margin on the chain: for GAF02 CORE's budget `H_d < c₂`,
`H_d + Ξ₃(3C_* + e₃ + H_d) < 1/2` (CHOICE `c₂ ≤ 1/512`, (OS)). -/
theorem slim_rank_margin_BASP (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (R : Gaf02RoughData C) {Hd : ℝ} (hHd : Hd < c 1) :
    Hd + Ξ 2 * (3 * sgpGraphBound + eg 2 + Hd) < 1 / 2 := by
  have hΩ := one_le_gafGraphOmega_BAS
  have hΞ0 := (C.numbers.1 2).1
  have hos := R.os 2
  have hc1 := C.c_le_BAS 1
  have h48 : 1 / (48 * gafGraphOmega_BAS) ≤ 1 / 48 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  exact slim_rank_small_BASP hΩ hΞ0.le hos.1 (by linarith [sgpGraphBound_le_gafGraphOmega_BAS])
    (by linarith [hos.2.2, (C.numbers.1 2).2.2.2]) (by linarith)

/-- **The slim stage rank** (`rank_ge_of_pp_comparison_BAS` at `x = π₃𝓔⁰ p` with preimage `p`):
for some reference `i` of the plane's (PP), `rank(Da(z) ∘ ρ_i⁻¹π₃Dg₂(p)) ≥ dim L_x`. -/
theorem slim_stage_rank_BASP (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (R : Gaf02RoughData C)
    (O : Cfs15StageOutput (gafStageDim 2) Kj (Ξ 2) (cw 2) (gafCloud P.toLocalChartFamily P.zero 2)
      (gafCloudEnlarged P.toLocalChartFamily P.zero 2) (fun x => S 2 * ρ (C.sel 2 x)) (C.plane 2))
    {p : X} (hx : cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero) p ∈
      gafCloud P.toLocalChartFamily P.zero 2)
    {z : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)}
    (hz : z ∈ ball (cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero) p)
      (S 2 * ρ (C.sel 2 (cgpProjMap P.toLocalChartFamily P.zero
        (cgpQ3Tags P.toLocalChartFamily P.zero) p)))) :
    ∃ i : P.slim.finite_centres.toFinset,
      Module.finrank ℝ (C.plane 2 (cgpProjMap P.toLocalChartFamily P.zero
        (cgpQ3Tags P.toLocalChartFamily P.zero) p)) ≤
      Module.finrank ℝ (LinearMap.range ((fderiv ℝ O.ambient z : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) ∘ₗ
        (((ρ i.1)⁻¹ • ((gafStageQ P.toLocalChartFamily P.zero 2).starProjection.comp
          (mvfderiv 𝓘(ℝ, E3) C.g₂ p)) : TangentSpace 𝓘(ℝ, E3) p →L[ℝ] BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) :
            TangentSpace 𝓘(ℝ, E3) p →ₗ[ℝ] BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)))) := by
  have : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ, E3) p) := inferInstanceAs (FiniteDimensional ℝ E3)
  refine (C.test2.2.2.1 _ hx).elim fun i hPP => (C.stage_derivative_lt.2.1).elim fun Hd hH => ?_
  have hPPp := hPP p rfl
  have hρi := hρ i.1
  have hΞ0 := (C.numbers.1 2).1
  have hQ := (O.ambient_value_deriv hx hz).2.2
  refine ⟨i, rank_ge_of_pp_comparison_BAS (V := TangentSpace 𝓘(ℝ, E3) p)
    (C.plane 2 (cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero) p))
    (ContinuousLinearMap.toLinearMap₁₂ (g.inner p))
    (fun w => Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner p w w))
    (fun w hw => Real.sqrt_pos.mpr (mul_pos (by positivity) (g.pos p w hw)))
    (((ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
      (cgpQ3Tags P.toLocalChartFamily P.zero)) p : TangentSpace 𝓘(ℝ, E3) p →L[ℝ] BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) :
        TangentSpace 𝓘(ℝ, E3) p →ₗ[ℝ] BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    _ (fderiv ℝ O.ambient z) (δ := Hd)
    hPPp.1 hPPp.2.1 (fun w hw => hPPp.2.2.1 w (fun k hk => by simpa using hw k hk)) hPPp.2.2.2
    (C.slim_stage_input_close_BASP p hH.2 hρi) hQ hΞ0.le (C.slim_rank_margin_BASP R hH.1)⟩

/-- **The slim stage-submersion core** (at `x = π₃𝓔⁰ p`, `z = π₃g₂ p`):
`κ_j ∘ Da(z) ∘ π₃ ∘ Dg₂(p)` is onto `ℝ`. -/
theorem slim_stage_core_BASP (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (R : Gaf02RoughData C) (j : P.slim.finite_centres.toFinset)
    (O : Cfs15StageOutput (gafStageDim 2) Kj (Ξ 2) (cw 2) (gafCloud P.toLocalChartFamily P.zero 2)
      (gafCloudEnlarged P.toLocalChartFamily P.zero 2) (fun x => S 2 * ρ (C.sel 2 x)) (C.plane 2))
    {p : X} (hp : p ∈ ball j.1 (10 ^ 6 * Δ * ρ j.1))
    (hη : |(P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord p| ≤ 7 * 10 ^ 5 * Δ)
    {z : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)}
    (hz : z ∈ ball (cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero) p)
      (S 2 * ρ (C.sel 2 (cgpProjMap P.toLocalChartFamily P.zero
        (cgpQ3Tags P.toLocalChartFamily P.zero) p)))) :
    ∀ y : ℝ, ∃ w : TangentSpace 𝓘(ℝ, E3) p,
      ((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j))
        (fderiv ℝ O.ambient z ((gafStageQ P.toLocalChartFamily P.zero 2).starProjection
          (mvfderiv 𝓘(ℝ, E3) C.g₂ p w))) = y := by
  have hΔ : 1 ≤ Δ := C.std.2.1
  have hx := slimCloud_mem_BASP j hp hη
  have hρj := hρ j.1
  have hΩ := one_le_gafGraphOmega_BAS
  -- CGP06 at `x` with preimage `p`
  have hm : ∀ v ∈ C.plane 2 (cgpProjMap P.toLocalChartFamily P.zero
      (cgpQ3Tags P.toLocalChartFamily P.zero) p),
      1 / (2 * gafGraphOmega_BAS) * ‖v‖ ≤
        ‖axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j) v‖ := by
    intro v hv
    have h := C.cgp06_slim_BAS R j hx rfl hp (by linarith) v hv
    rw [ContinuousLinearMap.comp_apply, div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
    linarith
  refine (Cfs15StageOutput.ambient_injOn_tangent_BASP O ⟨_, hx⟩ hz
    (axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j))
    (norm_slimCoord_le_BASP j) hm (R.eps_lt_margin_BAS 2).2).elim fun Tm hT =>
      (C.slim_stage_rank_BASP R O hx hz).elim fun i hrank => ?_
  have hLdim : Module.finrank ℝ (C.plane 2 (cgpProjMap P.toLocalChartFamily P.zero
      (cgpQ3Tags P.toLocalChartFamily P.zero) p)) = Module.finrank ℝ ℝ := by
    rw [(C.test2.1 _ hx).1, Module.finrank_self]
    rfl
  have hρi := hρ i.1
  have hs := surjective_of_rank_le_BAS _ _ Tm hT.1
    (axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j) : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ) hT.2.2
    (hT.2.1.trans hLdim) (hLdim ▸ hrank)
  intro y
  refine (hs (ρ j.1 * y)).elim fun v hv => ⟨(ρ i.1)⁻¹ • v, ?_⟩
  have hv' : axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j)
      (fderiv ℝ O.ambient z ((gafStageQ P.toLocalChartFamily P.zero 2).starProjection
        (mvfderiv 𝓘(ℝ, E3) C.g₂ p ((ρ i.1)⁻¹ • v)))) = ρ j.1 * y := by
    rw [map_smul, map_smul]
    exact hv
  rw [clm_smul_apply_BPRE, hv', smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hρj.ne', one_mul]

/-- The slim chart coordinate reads a block retained by `π₃`: `κ_j ∘ π₃ = κ_j`. -/
theorem slimKappa_starProjection_BASP (j : P.slim.finite_centres.toFinset) (y : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) :
    ((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j))
        ((gafStageQ P.toLocalChartFamily P.zero 2).starProjection y) =
      ((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j)) y := by
  have ht : (.inr (.inl j) : CGPTag P.toLocalChartFamily P.zero) ∈
      gafStageTags P.toLocalChartFamily P.zero 2 := by
    change (.inr (.inl j) : CGPTag P.toLocalChartFamily P.zero) ∈
      cgpQ3Tags P.toLocalChartFamily P.zero
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  have hsv : gafSlimVector P.toLocalChartFamily P.zero j
      ((gafStageQ P.toLocalChartFamily P.zero 2).starProjection y) =
      gafSlimVector P.toLocalChartFamily P.zero j y := by
    rw [gafSlimVector, blockVectorCLM_apply, blockVectorCLM_apply,
      starProjection_apply_of_mem_tags_BAS P.toLocalChartPackets ht]
  rw [clm_smul_apply_BPRE, clm_smul_apply_BPRE, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, hsv]

/-- The derivative of `κ_j ∘ a ∘ π₃ ∘ g₂` at `p` (chain rule; `a` differentiable at `z = π₃g₂ p`). -/
theorem slim_stage_mfderiv_BASP (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (j : P.slim.finite_centres.toFinset)
    (O : Cfs15StageOutput (gafStageDim 2) Kj (Ξ 2) (cw 2) (gafCloud P.toLocalChartFamily P.zero 2)
      (gafCloudEnlarged P.toLocalChartFamily P.zero 2) (fun x => S 2 * ρ (C.sel 2 x)) (C.plane 2))
    (p : X) (ha : DifferentiableAt ℝ O.ambient
      ((gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.g₂ p))) :
    HasMFDerivAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (fun q =>
      ((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j))
        (O.ambient ((gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.g₂ q)))) p
      ((((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j)).comp
        ((fderiv ℝ O.ambient ((gafStageQ P.toLocalChartFamily P.zero 2).starProjection
          (C.g₂ p))).comp (gafStageQ P.toLocalChartFamily P.zero 2).starProjection)).comp
        (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) C.g₂ p)) := by
  have hg₂ : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) C.g₂ p :=
    (C.stage_smooth.2.1 p).mdifferentiableAt (by simp)
  have hF : HasFDerivAt (fun y : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) =>
      ((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j))
        (O.ambient ((gafStageQ P.toLocalChartFamily P.zero 2).starProjection y)))
      (((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j)).comp
        ((fderiv ℝ O.ambient ((gafStageQ P.toLocalChartFamily P.zero 2).starProjection
          (C.g₂ p))).comp (gafStageQ P.toLocalChartFamily P.zero 2).starProjection)) (C.g₂ p) :=
    ((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j)).hasFDerivAt.comp
      _ (ha.hasFDerivAt.comp _ (gafStageQ P.toLocalChartFamily P.zero 2).starProjection.hasFDerivAt)
  exact hF.hasMFDerivAt.comp p hg₂.hasMFDerivAt

/-- On the slim plateau the projected stage input lies in the CFS15 ball of the cloud point:
`π₃g₂(p) ∈ B(x, Σ₃ρ(sel₃ x))`, `x = π₃𝓔⁰(p)` (CFS16 at the plateau). -/
theorem slim_stage_input_mem_BASP (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    {p : X} (hpl : p ∈ gafStagePlateau_BAS P.toLocalChartPackets 2) :
    (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.g₂ p) ∈
      ball (cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero) p)
        (S 2 * ρ (C.sel 2 (cgpProjMap P.toLocalChartFamily P.zero
          (cgpQ3Tags P.toLocalChartFamily P.zero) p))) := by
  have hzt := (C.stage_input_mem_omega_BAS (st := 2) (p := p) (by
    rw [C.cutoff_eq_one_of_plateau_BAS hpl]
    exact one_ne_zero)).2.1
  rw [gafStageQ_starProjection_globalMap] at hzt
  exact hzt

/-- Near a slim plateau point (active slot `O`): `κ_j ∘ f₃ = κ_j ∘ a ∘ π₃ ∘ g₂`. -/
theorem slim_kappa_eventuallyEq_BASP (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (j : P.slim.finite_centres.toFinset)
    {O : Cfs15StageOutput (gafStageDim 2) Kj (Ξ 2) (cw 2) (gafCloud P.toLocalChartFamily P.zero 2)
      (gafCloudEnlarged P.toLocalChartFamily P.zero 2) (fun x => S 2 * ρ (C.sel 2 x)) (C.plane 2)}
    (hO : C.slot 2 = .active O) {p : X} (hpl : p ∈ gafStagePlateau_BAS P.toLocalChartPackets 2) :
    (fun q => ((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily
      P.zero j)) (C.stageMap_BAS 2 q)) =ᶠ[𝓝 p] fun q =>
      ((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j))
        (O.ambient ((gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.g₂ q))) :=
  (C.stageMap_eventuallyEq_BAS hO hpl).mono fun _ hq =>
    (congrArg _ hq).trans (slimKappa_starProjection_BASP j _)

/-- **Stage submersion, slim stage, for an active slot `O`** (the assembly). -/
theorem stage_submersion_slim_of_active_BASP (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (R : Gaf02RoughData C) (j : P.slim.finite_centres.toFinset)
    {O : Cfs15StageOutput (gafStageDim 2) Kj (Ξ 2) (cw 2) (gafCloud P.toLocalChartFamily P.zero 2)
      (gafCloudEnlarged P.toLocalChartFamily P.zero 2) (fun x => S 2 * ρ (C.sel 2 x)) (C.plane 2)}
    (hO : C.slot 2 = .active O) {p : X} (hp : p ∈ ball j.1 (1000000 * Δ * ρ j.1))
    (hη : |(P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord p| < 6 * (10 ^ 5 * Δ)) :
    Surjective (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (fun q =>
      ((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j))
        (C.stageMap_BAS 2 q)) p) := by
  have hΔ : 1 ≤ Δ := C.std.2.1
  have hpl : p ∈ gafStagePlateau_BAS P.toLocalChartPackets 2 := ⟨j, hp, hη⟩
  have hp6 : p ∈ ball j.1 (10 ^ 6 * Δ * ρ j.1) := by
    norm_num at hp ⊢
    exact hp
  have hη7 : |(P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord p| ≤
      7 * 10 ^ 5 * Δ := by linarith
  have hz := C.slim_stage_input_mem_BASP hpl
  exact surjective_mfderiv_of_eventuallyEq_BASP (C.slim_kappa_eventuallyEq_BASP j hO hpl)
    (C.slim_stage_mfderiv_BASP j O p
      (O.ambient_value_deriv (slimCloud_mem_BASP j hp6 hη7) hz).2.1)
    fun y => (C.slim_stage_core_BASP R j O hp6 hη7 hz y).elim fun w hw => ⟨w, hw⟩

/-- **(d) Stage submersion, slim stage** (draft 59 §4 step 1, D66-7; chart form, `W₃`'s chart
coordinate `κ_j = R_j⁻¹u_j`): at every point of the chart's original threshold-6 plateau,
`D(κ_j ∘ f₃)(p)` is onto `ℝ`. (C14-BASESb proves the circle and edge versions,
`stage_submersion_circle_BAS`, `stage_submersion_edge_BAS`, same shape.) -/
theorem stage_submersion_slim_BAS (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (R : Gaf02RoughData C) (j : P.slim.finite_centres.toFinset) {p : X}
    (hp : p ∈ ball j.1 (1000000 * Δ * ρ j.1))
    (hη : |(P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord p| < 6 * (10 ^ 5 * Δ)) :
    Surjective (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (fun q =>
      ((ρ j.1)⁻¹ • axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j))
        (C.stageMap_BAS 2 q)) p) :=
  (C.slot_two_active_BASP j).elim fun _ hO => C.stage_submersion_slim_of_active_BASP R j hO hp hη

end Gaf02Chain

end DifferentialGeometry.Geometry.Collapse
