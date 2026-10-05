import DifferentialGeometry.Geometry.Fibration.ActualStageStepApplications
import DifferentialGeometry.Geometry.Fibration.ActualStageOneCutoff
import DifferentialGeometry.Geometry.Fibration.ActualAdjustmentChoiceApplications

/-!
# GAF02's first stage step on the actual `𝓔⁰`

Blueprint `master207B.tex`, GAF02 (B:5797) stage one: `Ψ₁ = adjustmentMap Q₁ P₁ ψ₁` after
`F = 𝓔⁰` (prior errors `0`), with CFS31's source cutoff `ψ₁` (`gaf02_stageOne_sourceCutoff`), a
stage projection `P₁` with CFS14 (3)'s bounds on the first cloud, and the first test's normal-error
rank clause (FC27 / TCP06):

* `normal_error_of_rank_GAF5`: the rank clause's normal error in units of a scale `c > 0`
  (`‖c·Dv − Π(c·Dv)‖ ≤ e√(c²n)`) gives `‖(I − Π)Dv‖ ≤ e√n`.
* `gafStageQ_zero_starProjection_GAF5`: `π_{Q₁} = id`.
* `gaf02_stageOne_step_GAF5`: for every `p`, `‖Ψ₁(F p) − F p‖ ≤ (5/3)ΞΣρ(p)`, `Ψ₁` is
  differentiable at `F p`, and `‖d(Ψ₁ ∘ F)_p w − dF_p w‖ ≤ ((5/3)ΞΣ b L + ΞL + e)√g(w, w)`
  (`b = gafCutoffConstant`, `L = gafDerivativeBound`): GAF01's stage-one budget with `E = H = 0`.
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

/-- The normal error of a rank clause in units of a scale `c > 0`: from
`‖c·Dv − Π_W(c·Dv)‖ ≤ e√(c²n)`, `‖(I − Π_W)Dv‖ ≤ e√n`. -/
theorem normal_error_of_rank_GAF5 {H T : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [AddCommGroup T] [Module ℝ T] [TopologicalSpace T] (W : Submodule ℝ H)
    [W.HasOrthogonalProjection] (D : T →L[ℝ] H) {c : ℝ} (hc : 0 < c) (v : T) {eg n : ℝ}
    (h : ‖c • D v - ((W.orthogonalProjectionOnto.comp (c • D)) v : H)‖ ≤
      eg * Real.sqrt (c ^ 2 * n)) :
    ‖(ContinuousLinearMap.id ℝ H - W.starProjection) (D v)‖ ≤ eg * Real.sqrt n := by
  have hs : Real.sqrt (c ^ 2 * n) = c * Real.sqrt n := by
    rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc.le]
  have heq : (ContinuousLinearMap.id ℝ H - W.starProjection) (D v) =
      c⁻¹ • (c • D v - ((W.orthogonalProjectionOnto.comp (c • D)) v : H)) := by
    simp only [sub_apply, ContinuousLinearMap.id_apply, smul_apply,
      ContinuousLinearMap.comp_apply, map_smul, Submodule.coe_smul]
    rw [smul_sub, smul_smul, smul_smul, inv_mul_cancel₀ hc.ne', one_smul, one_smul]
    rfl
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc)]
  calc c⁻¹ * ‖c • D v - ((W.orthogonalProjectionOnto.comp (c • D)) v : H)‖ ≤
      c⁻¹ * (eg * Real.sqrt (c ^ 2 * n)) := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hc.le)
    _ = eg * Real.sqrt n := by
      rw [hs]
      field_simp

section Model

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc : ℝ}
  {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
  [∀ a, MetricSpace (C a)] {o : ∀ a, C a} {δ εr e T V : ℝ}

variable (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
  (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V)

/-- The first stage target projection is the identity. -/
theorem gafStageQ_zero_starProjection_GAF5 :
    (gafStageQ L Z 0).starProjection = ContinuousLinearMap.id ℝ _ := by
  classical
  ext1 v
  rw [gafStageQ_starProjection]
  change blockRestrict Finset.univ v = v
  rw [blockRestrict_univ]
  rfl

end Model

section Packets

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}

/-- The model metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricN_GAF5s
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPackets`, as a named local instance. -/
local instance instChartedN_GAF5s
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricC_GAF5s
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- Stage one's localization: the closed support of the source cutoff at `𝓔⁰ p` puts
`π_{Q₁}𝓔⁰(p)` into the first cloud. -/
theorem gaf02_stageOne_loc_GAF5
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hLmax : 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax)
    (he : e < 1 / 40) (hT : 1600 * (1000000 * Δ) ≤ T) (hσs : 0 ≤ σs) (hσs1 : σs ≤ 1 / 100)
    (p : X) (hp : cgpGlobalMap P.toLocalChartFamily P.zero p ∈ tsupport
      (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
        (gafCircleMarker P))) :
    (gafStageQ P.toLocalChartFamily P.zero 0).starProjection
      (cgpGlobalMap P.toLocalChartFamily P.zero p) ∈ gafCloud P.toLocalChartFamily P.zero 0 := by
  have hcut := gaf02_stageOne_sourceCutoff P hΛ hΔ hμ hτ hLΛ hLmax he hT hσs hσs1
  obtain ⟨j, hj, hη⟩ := hcut.2.2.2.1 p hp
  exact gafStage_core_zero_GAF5 P.toLocalChartFamily P.zero p ⟨j, hj, by linarith⟩

/-- Stage one's normal error from the first test's rank clause (`π_{Q₁} = id`). -/
theorem gaf02_stageOne_normal_GAF5
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (plane : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
      Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) {eg : ℝ}
    (hrank : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 0,
      ∃ i : P.toLocalChartFamily.circle.finite_centres.toFinset,
      ∀ q, cgpGlobalMap P.toLocalChartFamily P.zero q = x → ∀ v,
        ‖(ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) q v -
            ((plane x).orthogonalProjectionOnto.comp ((ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3)
              (cgpGlobalMap P.toLocalChartFamily P.zero) q) v :
              BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))‖ ≤
          eg * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v)) (p : X) :
    (gafStageQ P.toLocalChartFamily P.zero 0).starProjection
      (cgpGlobalMap P.toLocalChartFamily P.zero p) ∈ gafCloud P.toLocalChartFamily P.zero 0 →
    ∀ w, ‖(ContinuousLinearMap.id ℝ
          (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) -
        (plane ((gafStageQ P.toLocalChartFamily P.zero 0).starProjection
          (cgpGlobalMap P.toLocalChartFamily P.zero p))).starProjection)
      ((gafStageQ P.toLocalChartFamily P.zero 0).starProjection
        (mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) p w))‖ ≤
      eg * Real.sqrt (g.inner p w w) := by
  have hQ := gafStageQ_zero_starProjection_GAF5 P.toLocalChartFamily P.zero
  intro hx w
  rw [hQ, ContinuousLinearMap.id_apply] at hx ⊢
  rw [ContinuousLinearMap.id_apply]
  refine Exists.elim (hrank _ hx) (fun i hi => ?_)
  exact normal_error_of_rank_GAF5 _ _ (inv_pos.mpr (hρ i.1)) w (hi p rfl w)

/-- **GAF02's first stage step on the actual `𝓔⁰`.** With CFS31's source cutoff `ψ₁`, a stage
projection `P₁` with CFS14 (3)'s value/derivative bounds `Ξ` on every `B(x, Σρ(sel x))`,
`x ∈ S₁`, and the first test's normal-error clause with error `e`: for every `p`,
`‖Ψ₁(𝓔⁰ p) − 𝓔⁰ p‖ ≤ (5/3)ΞΣρ(p)`, `Ψ₁` is differentiable at `𝓔⁰ p`, and
`‖d(Ψ₁ ∘ 𝓔⁰)_p w − d𝓔⁰_p w‖ ≤ ((5/3)ΞΣ·b·L + ΞL + e)√g(w, w)`. -/
theorem gaf02_stageOne_step_GAF5
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hLmax : 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax)
    (he : e < 1 / 40) (hT : 1600 * (1000000 * Δ) ≤ T) (hσs : 0 ≤ σs) (hσs1 : σs ≤ 1 / 100)
    (hσc : σc ∈ Icc (0 : ℝ) 1) (hγc : γc ∈ Icc (0 : ℝ) 1) (hεr : εr ∈ Icc (0 : ℝ) 1)
    (sel : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X)
    (hsel : ∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero 0,
      cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 0)
        (sel x) = x)
    (plane : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
      Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)))
    (Pst : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
      BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    {Ξ sg eg : ℝ} (hΞ : 0 ≤ Ξ) (hsg : 0 < sg) (heg : 0 ≤ eg)
    (hPst : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 0, ∀ z ∈ ball x (sg * ρ (sel x)),
      ‖Pst z - (x + (plane x).starProjection (z - x))‖ ≤ Ξ * (sg * ρ (sel x)))
    (hPd : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 0, ∀ z ∈ ball x (sg * ρ (sel x)),
      DifferentiableAt ℝ Pst z ∧ ‖fderiv ℝ Pst z - (plane x).starProjection‖ ≤ Ξ)
    (hrank : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 0,
      ∃ i : P.toLocalChartFamily.circle.finite_centres.toFinset,
      ∀ q, cgpGlobalMap P.toLocalChartFamily P.zero q = x → ∀ v,
        ‖(ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) q v -
            ((plane x).orthogonalProjectionOnto.comp ((ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3)
              (cgpGlobalMap P.toLocalChartFamily P.zero) q) v :
              BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))‖ ≤
          eg * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v)) :
    ∀ p,
      ‖adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 0) Pst
          (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
            (gafCircleMarker P)) (cgpGlobalMap P.toLocalChartFamily P.zero p) -
          cgpGlobalMap P.toLocalChartFamily P.zero p‖ ≤ 5 / 3 * Ξ * sg * ρ p ∧
      DifferentiableAt ℝ (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 0) Pst
          (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
            (gafCircleMarker P))) (cgpGlobalMap P.toLocalChartFamily P.zero p) ∧
      ∀ w, ‖mvfderiv 𝓘(ℝ, E3) (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 0) Pst
          (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
            (gafCircleMarker P)) ∘ cgpGlobalMap P.toLocalChartFamily P.zero) p w -
          mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) p w‖ ≤
        (5 / 3 * Ξ * sg * gafCutoffConstant * gafDerivativeBound + Ξ * gafDerivativeBound + eg) *
          Real.sqrt (g.inner p w w) := by
  intro p
  have hsmall : Λ * (1000000 * Δ) ≤ 1 / 4 := by
    have h' : Λ * (1000000 * Δ) = 1000000 * Δ * Λ := by ring
    linarith
  have hcut := gaf02_stageOne_sourceCutoff P hΛ hΔ hμ hτ hLΛ hLmax he hT hσs hσs1
  have hder := gaf01_derivative_bound P hΛ hΔ hμ hτ hLΛ hLmax he hT ⟨hσs, by linarith⟩ hσc hγc
    hεr
  have hloc := gaf02_stageOne_loc_GAF5 P hΛ hΔ hμ hτ hLΛ hLmax he hT hσs hσs1 p
  have hratio := gafCloud_preimage_ratio_two_GAF5 P.toLocalChartFamily P.zero hΔ hΛ hsmall 0 sel
    hsel
  have hprior : ‖cgpGlobalMap P.toLocalChartFamily P.zero p -
      cgpGlobalMap P.toLocalChartFamily P.zero p‖ ≤ 0 * ρ p := by simp
  have hE : (0 : ℝ) ≤ 3 * sg / 10 := by positivity
  have hval := stage_step_value_point_GAF5 (gafStageQ P.toLocalChartFamily P.zero 0)
    (gafCloud P.toLocalChartFamily P.zero 0) sel ρ plane Pst _ hcut.2.1 hΞ hsg le_rfl hE hPst
    (cgpGlobalMap P.toLocalChartFamily P.zero) (cgpGlobalMap P.toLocalChartFamily P.zero) (hρ p)
    hloc hratio hprior
  have hnormal := gaf02_stageOne_normal_GAF5 P plane hrank p
  have hdv := stage_step_deriv_point_GAF5 (I := 𝓘(ℝ, E3))
    (gafStageQ P.toLocalChartFamily P.zero 0) (gafCloud P.toLocalChartFamily P.zero 0) sel ρ
    plane Pst _ hcut.2.1 hΞ hsg le_rfl hE gafCutoffConstant_nonneg
    (zero_le_one.trans one_le_gafDerivativeBound) le_rfl heg hPst hPd
    (cgpGlobalMap P.toLocalChartFamily P.zero) (cgpGlobalMap P.toLocalChartFamily P.zero) (hρ p)
    hloc hratio hprior ((hder.1 p).mdifferentiableAt (by simp))
    (fun _ => ⟨hcut.1.differentiable (by simp) _, hcut.2.2.2.2 p⟩)
    (fun w => Real.sqrt (g.inner p w w)) (fun w => Real.sqrt_nonneg _) (fun w => hder.2 p w)
    hnormal (fun w => by simp)
  refine ⟨hval.trans_eq (by ring), hdv.1, fun w => (hdv.2 w).trans_eq (by ring)⟩

end Packets

end DifferentialGeometry.Geometry.Collapse
