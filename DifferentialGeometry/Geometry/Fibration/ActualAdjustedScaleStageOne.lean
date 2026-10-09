import DifferentialGeometry.Geometry.Fibration.ActualAdjustedScaleBlendApplications
import DifferentialGeometry.Geometry.Fibration.ActualStageFirstTest
import DifferentialGeometry.Geometry.Fibration.ActualStageMean

/-!
# EDP01, step: the stage-one scale `z_ρ = (P₁𝓔⁰)_ρ` from the stage nearest map with (SM)/(SW)

Blueprint `master207B.tex`, EDP01 (B:6684–6735): "With `z_ρ = (P₁F)_ρ`, `‖DF‖ ≤ L₀` and (SC)
therefore give `|z_ρ − ρ| ≤ 20ΛR_i ≤ (80/3)Λρ`, `‖Dz_ρ‖ ≤ 80N_b c_wL₀/(3Σ₁) Λ`", and the blend
`s = (1 − χ)ρ + χz_ρ`. This file is a STEP of the row, not the row: it takes as INPUTS the stage-one
nearest map `a` with the literal conclusions of `gaf01_row_nearest_mean_GAFS2` at stage `0`
(differentiability and (SMV) with CFS12's `c_w`) and the first-cloud planes with the SCALE clause
`plane x ≤ ker ℓ_s` (`ℓ_s = blockMarkerCLM cgpScaleTag`; "every first-cloud plane has zero scale
component", from TCP05's models — this clause is not yet a conclusion of the stage-0 test).

* `edp01_stage_one_zrho_step_GAFS2`: on `tsupport χ` (`χ = ψ₁ ∘ 𝓔⁰`), `z_ρ = ℓ_s ∘ a ∘ 𝓔⁰` is
  differentiable with `|z_ρ − ρ| ≤ (80/3)Λρ` and `|dz_ρ(v)| ≤ (80c_wL₀/(3Σ))Λ|v|_g` (CFS31's support
  index `i` with `|η_i| ≤ 13/2`, (SC) for every contributing centre via
  `edp01_contributor_scale_GAFS`, (SMV) with `R₀ = R_i`, `β = 10ΛR_i`, chain rule with
  `‖D𝓔⁰‖ ≤ L₀`). `N_b` is absorbed into `c_w` (the tree's CFS12 bound is for `Σ_y ‖Dw_y‖`).
* `edp01_value_arith_GAFS2`, `edp01_deriv_arith_GAFS2`: the real arithmetic of the two estimates.
The blend `s` and (SD): `edp01_stage_one_blend_step_GAFS2`
(`ActualAdjustedScaleStageOneApplications`).
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

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}

/-- The model metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricNC14SO_GAFS2
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsC14`, as a named local instance. -/
local instance instChartedNC14SO_GAFS2
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricCC14SO_GAFS2
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- EDP01's value arithmetic: `|z − R| ≤ 10ΛR` and `|ρ − R| ≤ 10ΛR` with `10Λ ≤ 1/4` give
`|z − ρ| ≤ (80/3)Λρ`. -/
theorem edp01_value_arith_GAFS2 {z ρp ρj Λ : ℝ} (hv : |z - ρj| ≤ 10 * Λ * ρj)
    (hp : |ρp - ρj| ≤ 10 * Λ * ρj) (hΛ : 0 ≤ Λ) (hΛ10 : 10 * Λ ≤ 1 / 4) (hρj : 0 < ρj) :
    |z - ρp| ≤ 80 / 3 * Λ * ρp := by
  have hlow : 3 / 4 * ρj ≤ ρp := by
    have := (abs_le.mp hp).1
    nlinarith
  calc |z - ρp| = |(z - ρj) - (ρp - ρj)| := by ring_nf
    _ ≤ |z - ρj| + |ρp - ρj| := abs_sub _ _
    _ ≤ 10 * Λ * ρj + 10 * Λ * ρj := add_le_add hv hp
    _ = 20 * Λ * ρj := by ring
    _ ≤ 20 * Λ * (4 / 3 * ρp) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith
    _ = 80 / 3 * Λ * ρp := by ring

/-- EDP01's derivative arithmetic: `A ≤ 2c_w(10ΛR)/(Σρ)`, `w ≤ L₀t`, `R ≤ (4/3)ρ` give
`A w ≤ (80c_wL₀/(3Σ))Λt`. -/
theorem edp01_deriv_arith_GAFS2 {A w cw Λ ρj ρp sg L t : ℝ}
    (hA : A ≤ 2 * cw * (10 * Λ * ρj) / (sg * ρp)) (hA0 : 0 ≤ A) (hw : w ≤ L * t) (hw0 : 0 ≤ w)
    (hcw : 0 ≤ cw) (hΛ : 0 ≤ Λ) (hsg : 0 < sg) (hρp : 0 < ρp) (hL : 0 ≤ L) (ht : 0 ≤ t)
    (hlow : 3 / 4 * ρj ≤ ρp) :
    A * w ≤ 80 * cw * L / (3 * sg) * Λ * t := by
  have h1 : A * w ≤ 2 * cw * (10 * Λ * ρj) / (sg * ρp) * (L * t) :=
    mul_le_mul hA hw hw0 (hA0.trans hA)
  have h2 : 2 * cw * (10 * Λ * ρj) ≤ 2 * cw * (10 * Λ * (4 / 3 * ρp)) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith
  have h3 : 2 * cw * (10 * Λ * ρj) / (sg * ρp) * (L * t) ≤
      2 * cw * (10 * Λ * (4 / 3 * ρp)) / (sg * ρp) * (L * t) :=
    mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right h2 (by positivity)) (by positivity)
  have h4 : 2 * cw * (10 * Λ * (4 / 3 * ρp)) / (sg * ρp) * (L * t) =
      80 * cw * L / (3 * sg) * Λ * t := by
    field_simp
    ring
  linarith

/-- **EDP01, step: the estimates for `z_ρ = (P₁𝓔⁰)_ρ`.** For the stage-one nearest map `a` with
(at stage `0`, selection `sel`, `r = Σρ ∘ sel`, accuracy `ε_c`, `Σ ≤ ε_c/10000`) differentiability
and (SMV) with `c_w ≥ 0` on every `B(x, r_x)`, and first-cloud planes with the scale clause: at
every point of `tsupport χ`, `z_ρ = ℓ_s ∘ a ∘ 𝓔⁰` is differentiable,
`|z_ρ − ρ| ≤ (80/3)Λρ` and `|dz_ρ(v)| ≤ (80c_wL₀/(3Σ))Λ|v|_g`. -/
theorem edp01_stage_one_zrho_step_GAFS2
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hLmax : 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax)
    (he : e < 1 / 40) (hT : 1600 * (1000000 * Δ) ≤ T) (hσs : 0 ≤ σs) (hσs1 : σs ≤ 1 / 100)
    (hσc : σc ∈ Icc (0 : ℝ) 1) (hγc : γc ∈ Icc (0 : ℝ) 1) (hεr : εr ∈ Icc (0 : ℝ) 1)
    {εc sg cw : ℝ} (hεc : 0 < εc) (hsg : 0 < sg) (hsgε : sg ≤ εc / 10000) (hcw : 0 ≤ cw)
    (sel : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X)
    (hsel : ∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero 0,
      cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 0)
        (sel x) = x)
    (plane : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
      Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)))
    (hscale : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 0,
      plane x ≤ LinearMap.ker ((blockMarkerCLM (cgpScaleTag P.toLocalChartFamily P.zero) :
        BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) :
          BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ))
    (a : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
      BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    (hda : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 0, ∀ z ∈ ball x (sg * ρ (sel x)),
      DifferentiableAt ℝ a z)
    (hmean : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 0, ∀ z ∈ ball x (sg * ρ (sel x)),
      ∀ ℓ : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ,
        (∀ i ∈ gafCloud P.toLocalChartFamily P.zero 0,
          (closedBall i (80 * εc⁻¹ * (sg * ρ (sel i))) ∩
            ball x (8 * εc⁻¹ * (sg * ρ (sel x)))).Nonempty →
          plane i ≤ LinearMap.ker
            (ℓ : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ)) →
        ∀ R₀ β : ℝ,
        (∀ i ∈ gafCloud P.toLocalChartFamily P.zero 0,
          (closedBall i (80 * εc⁻¹ * (sg * ρ (sel i))) ∩
            ball x (8 * εc⁻¹ * (sg * ρ (sel x)))).Nonempty → |ℓ i - R₀| ≤ β) →
        |ℓ (a z) - R₀| ≤ β ∧ ‖ℓ.comp (fderiv ℝ a z)‖ ≤ 2 * cw * β / (sg * ρ (sel x))) :
    let χ : X → ℝ := fun p => markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1)
      (gafCircleVector P.toLocalChartPackets) (gafCircleMarker P.toLocalChartPackets)
      (cgpGlobalMap P.toLocalChartFamily P.zero p)
    let zρ : X → ℝ := fun p =>
      blockMarkerCLM (cgpScaleTag P.toLocalChartFamily P.zero)
        (a (cgpGlobalMap P.toLocalChartFamily P.zero p))
    ∀ p ∈ tsupport χ, MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) zρ p ∧
      |zρ p - ρ p| ≤ 80 / 3 * Λ * ρ p ∧
      ∀ v : TangentSpace 𝓘(ℝ, E3) p, |mvfderiv 𝓘(ℝ, E3) zρ p v| ≤
        80 * cw * gafDerivativeBound / (3 * sg) * Λ * Real.sqrt (g.inner p v v) := by
  intro χ zρ p hp
  obtain ⟨-, -, -, hsupp, -⟩ := edp01_cutoff_GAFS P.toLocalChartPackets hΛ hΔ hμ hτ hLΛ hLmax he
    hT hσs hσs1 hσc hγc hεr
  obtain ⟨j, hpj, hηj⟩ := hsupp p hp
  have hFall := gaf01_derivative_bound P.toLocalChartPackets hΛ hΔ hμ hτ hLΛ hLmax he hT
    ⟨hσs, by linarith⟩ hσc hγc hεr
  have hℓF : ∀ q, blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (cgpScaleTag P.toLocalChartFamily P.zero)
      (cgpGlobalMap P.toLocalChartFamily P.zero q) = ρ q :=
    fun q => cgpGlobalMap_scale P.toLocalChartFamily P.zero q
  have hselF : ∀ y ∈ gafCloud P.toLocalChartFamily P.zero 0,
      cgpGlobalMap P.toLocalChartFamily P.zero (sel y) = y := by
    intro y hy
    have h := hsel y (gafCloud_subset_enlarged P.toLocalChartFamily P.zero (by linarith) 0 hy)
    rwa [show gafStageTags P.toLocalChartFamily P.zero 0 = Finset.univ from rfl,
      cgpProjMap_univ_GAF] at h
  have hρsel : ∀ q, cgpGlobalMap P.toLocalChartFamily P.zero q ∈
      gafCloud P.toLocalChartFamily P.zero 0 →
      ρ (sel (cgpGlobalMap P.toLocalChartFamily P.zero q)) = ρ q := by
    intro q hq
    rw [← hℓF (sel _), hselF _ hq, hℓF]
  have hp7 : p ∈ fc04Set P.toLocalChartFamily P.zero 7 := ⟨j, hpj, by linarith⟩
  have hx : cgpGlobalMap P.toLocalChartFamily P.zero p ∈
      gafCloud P.toLocalChartFamily P.zero 0 := by
    rw [gafCloud_zero_GAF4]
    exact ⟨p, hp7, rfl⟩
  have hρp := hρ p
  have hρj := hρ j.1
  have hrx : sg * ρ (sel (cgpGlobalMap P.toLocalChartFamily P.zero p)) = sg * ρ p := by
    rw [hρsel p hx]
  have hzball : cgpGlobalMap P.toLocalChartFamily P.zero p ∈
      ball (cgpGlobalMap P.toLocalChartFamily P.zero p)
        (sg * ρ (sel (cgpGlobalMap P.toLocalChartFamily P.zero p))) := by
    rw [hrx]
    exact mem_ball_self (mul_pos hsg hρp)
  have hsmall : Λ * (1000000 * Δ) ≤ 1 / 4 := by nlinarith
  have hβ : ∀ i ∈ gafCloud P.toLocalChartFamily P.zero 0,
      (closedBall i (80 * εc⁻¹ * (sg * ρ (sel i))) ∩
        ball (cgpGlobalMap P.toLocalChartFamily P.zero p)
          (8 * εc⁻¹ * (sg * ρ (sel (cgpGlobalMap P.toLocalChartFamily P.zero p))))).Nonempty →
      |blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (cgpScaleTag P.toLocalChartFamily P.zero) i - ρ j.1| ≤
        10 * Λ * ρ j.1 := by
    intro i hi hmeet
    have hi' := hi
    rw [gafCloud_zero_GAF4] at hi'
    obtain ⟨q, hq, rfl⟩ := hi'
    rw [hρsel q hi, hρsel p hx] at hmeet
    rw [hℓF q]
    exact (edp01_contributor_scale_GAFS P.toLocalChartPacketsR hΔ hΛ hsmall hεc hsg.le hsgε j hpj
      (by linarith) (fc04Set_mono _ _ (by norm_num) hq) hmeet).1
  have hmn := hmean _ hx _ hzball
    (blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (cgpScaleTag P.toLocalChartFamily P.zero))
    (fun i hi _ => hscale i hi) (ρ j.1) (10 * Λ * ρ j.1) hβ
  have hpR : |ρ p - ρ j.1| ≤ 10 * Λ * ρ j.1 :=
    abs_scale_sub_le_of_coord_GAFS P.toLocalChartPacketsR hΛ j hpj (by linarith)
  have hΛ10 : 10 * Λ ≤ 1 / 4 := by nlinarith
  have hlow : 3 / 4 * ρ j.1 ≤ ρ p := by
    have := (abs_le.mp hpR).1
    nlinarith
  have hFm : MDifferentiableAt 𝓘(ℝ, E3)
      𝓘(ℝ, BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
      (cgpGlobalMap P.toLocalChartFamily P.zero) p :=
    hFall.1.mdifferentiableAt (by simp)
  have hdap := hda _ hx _ hzball
  have hΨ : DifferentiableAt ℝ
      (fun y => blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (cgpScaleTag P.toLocalChartFamily P.zero) (a y))
      (cgpGlobalMap P.toLocalChartFamily P.zero p) :=
    (blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (cgpScaleTag P.toLocalChartFamily P.zero)).differentiableAt.comp _ hdap
  have hzeq : zρ = (fun y => blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (cgpScaleTag P.toLocalChartFamily P.zero) (a y)) ∘
      cgpGlobalMap P.toLocalChartFamily P.zero := rfl
  refine ⟨?_, edp01_value_arith_GAFS2 hmn.1 hpR hΛ hΛ10 hρj, fun v => ?_⟩
  · rw [hzeq]
    exact hΨ.comp_mdifferentiableAt hFm
  · have hchain : mvfderiv 𝓘(ℝ, E3) zρ p v =
        fderiv ℝ (fun y => blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (cgpScaleTag P.toLocalChartFamily P.zero) (a y))
          (cgpGlobalMap P.toLocalChartFamily P.zero p)
          (mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) p v) := by
      rw [hzeq]
      exact mvfderiv_comp_apply_of_differentiableAt_GAF3 hFm hΨ v
    have hcomp : fderiv ℝ
        (fun y => blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (cgpScaleTag P.toLocalChartFamily P.zero) (a y))
        (cgpGlobalMap P.toLocalChartFamily P.zero p) =
        (blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (cgpScaleTag P.toLocalChartFamily P.zero)).comp
          (fderiv ℝ a (cgpGlobalMap P.toLocalChartFamily P.zero p)) :=
      ((blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (cgpScaleTag P.toLocalChartFamily P.zero)).hasFDerivAt.comp _
        hdap.hasFDerivAt).fderiv
    rw [hchain, hcomp, ← Real.norm_eq_abs]
    have hd' := hmn.2
    rw [hrx] at hd'
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    exact edp01_deriv_arith_GAFS2 hd' (norm_nonneg _) (hFall.2 p v) (norm_nonneg _) hcw hΛ hsg hρp
      (le_trans zero_le_one one_le_gafDerivativeBound) (Real.sqrt_nonneg _) hlow

end DifferentialGeometry.Geometry.Collapse
