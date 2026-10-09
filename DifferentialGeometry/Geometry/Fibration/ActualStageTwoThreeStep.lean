import DifferentialGeometry.Geometry.Fibration.ActualStageOneStep
import DifferentialGeometry.Geometry.Fibration.ActualStageCutoffs

/-!
# GAF02's second and third stage steps on the actual data

Blueprint `master207B.tex`, GAF02 (B:5797), stages two and three: `Ψ₂ = adjustmentMap Q₂ P₂ ψ₂`
after a map `f` (the stage-one output) with CFS23's edge cutoff `ψ₂ = gafStageTwoCutoff`, and
`Ψ₃ = adjustmentMap Q₃ P₃ ψ₃` with CFS22's slim cutoff `ψ₃ = gafStageThreeCutoff`. The preceding
map carries GAF01's prior errors (`‖f − 𝓔⁰‖ ≤ Eρ`, `‖df − d𝓔⁰‖ ≤ H₀√g`, `E ≤ 3Σ/10`,
`E ≤ 4κ/5`) and CFS31's zero-marker input (ZM) for the stage's family — exactly the inputs of
`gaf02_stageTwo_cutoff` / `gaf02_stageThree_cutoff`; the assembly proves (ZM) at the actual stage
outputs by CFS29/CFS30 (`actualCloud_stage_output_supplies_cutoff_contract`).

* `normal_error_of_unit_GAF6`: a normal-error clause on the unit sphere of a positive definite
  form in units of `c > 0` (the edge test's form, strict) gives `‖(I − Π)Dv‖ ≤ e√(B v v)`.
* `gafStage_projMap_mvfderiv_GAF6`: `d(π_{Q_st} 𝓔⁰) = π_{Q_st} d𝓔⁰`.
* `gaf02_stageTwo_step_GAF6`, `gaf02_stageThree_step_GAF6`: for every `p`,
  `‖Ψ(f p) − 𝓔⁰ p‖ ≤ (E + a)ρ(p)` with `a = (5/3)ΞΣ + (1 + Ξ)E`, `Ψ` is differentiable at `f p`,
  and `‖d(Ψ ∘ f)_p w − d𝓔⁰_p w‖ ≤ (a·b·(L + H₀) + Ξ(L + H₀) + e + 2H₀)√g(w, w)`
  (`b = gafCutoffConstant`, `L = gafDerivativeBound`): GAF01's stage budget.
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

/-- The normal error of a unit-sphere clause in units of a scale `c > 0`: if
`‖c·Dw − Π_W(c·Dw)‖ < e` for every `w` with `c²B(w, w) = 1` and `B` is positive definite, then
`‖(I − Π_W)Dv‖ ≤ e√(B(v, v))` for every `v`. -/
theorem normal_error_of_unit_GAF6 {H T : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [AddCommGroup T] [Module ℝ T] [TopologicalSpace T] (W : Submodule ℝ H)
    [W.HasOrthogonalProjection] (D : T →L[ℝ] H) (B : T →L[ℝ] T →L[ℝ] ℝ)
    (hB : ∀ v, v ≠ 0 → 0 < B v v) {c : ℝ} (hc : 0 < c) {eg : ℝ}
    (h : ∀ w, c ^ 2 * B w w = 1 → ‖c • D w - W.starProjection (c • D w)‖ < eg) (v : T) :
    ‖(ContinuousLinearMap.id ℝ H - W.starProjection) (D v)‖ ≤ eg * Real.sqrt (B v v) := by
  by_cases hv : v = 0
  · subst hv
    simp
  have hBv := hB v hv
  have hs : 0 < Real.sqrt (B v v) := Real.sqrt_pos.mpr hBv
  have hss : Real.sqrt (B v v) ^ 2 = B v v := Real.sq_sqrt hBv.le
  set s := Real.sqrt (B v v) with hsdef
  have hw : c ^ 2 * B ((c * s)⁻¹ • v) ((c * s)⁻¹ • v) = 1 := by
    simp only [map_smul, smul_apply, smul_eq_mul]
    rw [← hss]
    field_simp
  have hlt := h _ hw
  have heq : c • D ((c * s)⁻¹ • v) - W.starProjection (c • D ((c * s)⁻¹ • v)) =
      s⁻¹ • (ContinuousLinearMap.id ℝ H - W.starProjection) (D v) := by
    have hcs : c * (c * s)⁻¹ = s⁻¹ := by field_simp
    rw [map_smul, smul_smul, hcs, map_smul, sub_apply, ContinuousLinearMap.id_apply, smul_sub]
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs)] at hlt
  have h2 : ‖(ContinuousLinearMap.id ℝ H - W.starProjection) (D v)‖ < eg * s := by
    rw [inv_mul_lt_iff₀ hs] at hlt
    linarith
  exact h2.le

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

open Classical in
/-- `d(π_{Q_st} 𝓔⁰) = π_{Q_st} d𝓔⁰` where `𝓔⁰` is differentiable. -/
theorem gafStage_projMap_mvfderiv_GAF6 (st : Fin 3) {p : X}
    (hF : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace (fun _ : CGPTag L Z => ℝ²))
      (cgpGlobalMap L Z) p) (w : TangentSpace 𝓘(ℝ, E3) p) :
    mvfderiv 𝓘(ℝ, E3) (cgpProjMap L Z (gafStageTags L Z st)) p w =
      (gafStageQ L Z st).starProjection (mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap L Z) p w) := by
  have hfun : cgpProjMap L Z (gafStageTags L Z st) =
      fun y => (gafStageQ L Z st).starProjection (cgpGlobalMap L Z y) :=
    funext fun y => (gafStageQ_starProjection_globalMap L Z st y).symm
  rw [hfun]
  exact mvfderiv_clm_comp hF _ w

/-- Stage two's normal error from the edge test's unit-sphere clause. -/
theorem gafStage_two_normal_GAF6
    (hF : ∀ p, MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace (fun _ : CGPTag L Z => ℝ²))
      (cgpGlobalMap L Z) p)
    (plane : BlockSpace (fun _ : CGPTag L Z => ℝ²) →
      Submodule ℝ (BlockSpace (fun _ : CGPTag L Z => ℝ²))) (centres : Set X) {eg : ℝ}
    (hrank : ∀ x ∈ gafCloud L Z 1, ∃ i ∈ centres, ∀ q : X, cgpProjMap L Z (cgpQ2Tags L Z) q = x →
      ∀ w : TangentSpace 𝓘(ℝ, E3) q, (ρ i)⁻¹ ^ 2 * g.inner q w w = 1 →
        ‖(ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap L Z (cgpQ2Tags L Z)) q w -
          (plane x).starProjection
            ((ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap L Z (cgpQ2Tags L Z)) q w)‖ < eg) (p : X) :
    (gafStageQ L Z 1).starProjection (cgpGlobalMap L Z p) ∈ gafCloud L Z 1 →
    ∀ w, ‖(ContinuousLinearMap.id ℝ (BlockSpace (fun _ : CGPTag L Z => ℝ²)) -
        (plane ((gafStageQ L Z 1).starProjection (cgpGlobalMap L Z p))).starProjection)
      ((gafStageQ L Z 1).starProjection (mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap L Z) p w))‖ ≤
      eg * Real.sqrt (g.inner p w w) := by
  intro hx w
  obtain ⟨i, -, hi⟩ := hrank _ hx
  have hq : cgpProjMap L Z (cgpQ2Tags L Z) p =
      (gafStageQ L Z 1).starProjection (cgpGlobalMap L Z p) :=
    (gafStageQ_starProjection_globalMap L Z 1 p).symm
  have hn := normal_error_of_unit_GAF6 _ _ (g.inner p) (g.pos p) (inv_pos.mpr (hρ i)) (hi p hq) w
  rwa [show cgpQ2Tags L Z = gafStageTags L Z 1 from rfl,
    gafStage_projMap_mvfderiv_GAF6 L Z 1 (hF p)] at hn

/-- Stage three's normal error from the slim test's rank clause. -/
theorem gafStage_three_normal_GAF6
    (hF : ∀ p, MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace (fun _ : CGPTag L Z => ℝ²))
      (cgpGlobalMap L Z) p)
    (plane : BlockSpace (fun _ : CGPTag L Z => ℝ²) →
      Submodule ℝ (BlockSpace (fun _ : CGPTag L Z => ℝ²))) {eg : ℝ}
    (hrank : ∀ x ∈ gafCloud L Z 2, ∃ i : L.slim.finite_centres.toFinset,
      ∀ q, cgpProjMap L Z (cgpQ3Tags L Z) q = x → ∀ v,
        ‖(ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap L Z (cgpQ3Tags L Z)) q v -
            ((plane x).orthogonalProjectionOnto.comp ((ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3)
              (cgpProjMap L Z (cgpQ3Tags L Z)) q) v : BlockSpace (fun _ : CGPTag L Z => ℝ²))‖ ≤
          eg * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v)) (p : X) :
    (gafStageQ L Z 2).starProjection (cgpGlobalMap L Z p) ∈ gafCloud L Z 2 →
    ∀ w, ‖(ContinuousLinearMap.id ℝ (BlockSpace (fun _ : CGPTag L Z => ℝ²)) -
        (plane ((gafStageQ L Z 2).starProjection (cgpGlobalMap L Z p))).starProjection)
      ((gafStageQ L Z 2).starProjection (mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap L Z) p w))‖ ≤
      eg * Real.sqrt (g.inner p w w) := by
  intro hx w
  obtain ⟨i, hi⟩ := hrank _ hx
  have hq : cgpProjMap L Z (cgpQ3Tags L Z) p =
      (gafStageQ L Z 2).starProjection (cgpGlobalMap L Z p) :=
    (gafStageQ_starProjection_globalMap L Z 2 p).symm
  have hn := normal_error_of_rank_GAF5 _ _ (inv_pos.mpr (hρ i.1)) w (hi p hq w)
  rwa [show cgpQ3Tags L Z = gafStageTags L Z 2 from rfl,
    gafStage_projMap_mvfderiv_GAF6 L Z 2 (hF p)] at hn

end Model

section Packets

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}

/-- The model metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricN_GAF6s
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPackets`, as a named local instance. -/
local instance instChartedN_GAF6s
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricC_GAF6s
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- Stage two's cutoff at the preceding map: the closed support localizes `π_{Q₂}𝓔⁰(p)` into the
edge cloud, and on it `ψ₂` is differentiable at `f p` with `‖Dψ₂(f p)‖ ≤ b_cut/ρ(p)`. -/
theorem gaf02_stageTwo_cutoff_point_GAF6
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hLmax : 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax)
    (he : e < 1 / 40) (hT : 1600 * (1000000 * Δ) ≤ T) (hσs : 0 ≤ σs) (hσs1 : σs ≤ 1 / 100)
    (f : X → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    (hpert : ∀ p, ‖f p - cgpGlobalMap P.toLocalChartFamily P.zero p‖ ≤
      4 * gafKappa / 5 * ρ p)
    (hZM : ∀ (j : P.edge.finite_centres.toFinset) p, P.edge.cutoff j.1 p = 0 →
      |gafEdgeMarker P.toLocalChartFamily P.zero j (f p)| ≤ ρ j.1 / 32) (p : X) :
    (f p ∈ tsupport (gafStageTwoCutoff P.toLocalChartFamily P.zero) →
      (gafStageQ P.toLocalChartFamily P.zero 1).starProjection
        (cgpGlobalMap P.toLocalChartFamily P.zero p) ∈ gafCloud P.toLocalChartFamily P.zero 1) ∧
      DifferentiableAt ℝ (gafStageTwoCutoff P.toLocalChartFamily P.zero) (f p) ∧
      ‖fderiv ℝ (gafStageTwoCutoff P.toLocalChartFamily P.zero) (f p)‖ ≤
        gafCutoffConstant / ρ p := by
  have hcut := gaf02_stageTwo_cutoff P hΛ hΔ hμ hτ hLΛ hLmax he hT hσs hσs1 f hpert hZM
  have hseg := hcut.2.2.2.2 p 1 ⟨zero_le_one, le_rfl⟩
  have h1 : (1 - (1 : ℝ)) • cgpGlobalMap P.toLocalChartFamily P.zero p + (1 : ℝ) • f p = f p := by
    simp
  rw [h1] at hseg
  have hopen : IsOpen {z | 0 < gafScaleMarker P.toLocalChartFamily P.zero z} :=
    isOpen_lt continuous_const (gafScaleMarker P.toLocalChartFamily P.zero).continuous
  refine ⟨fun hp => ?_, ?_, hseg.2⟩
  · obtain ⟨j, hj, hη, ht⟩ := hcut.2.2.2.1 p hp
    exact gafStage_core_one_GAF5 P.toLocalChartFamily P.zero p
      ⟨j, hj, by rw [norm_planeAxis]; exact hη, ht⟩
  · exact (hcut.1.contDiffAt (hopen.mem_nhds hseg.1)).differentiableAt (by simp)

/-- Stage three's cutoff at the preceding map: the closed support localizes `π_{Q₃}𝓔⁰(p)` into
the slim cloud, `ψ₃` is differentiable, and `‖Dψ₃(f p)‖ ≤ b_cut/ρ(p)`. -/
theorem gaf02_stageThree_cutoff_point_GAF6
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hLmax : 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax)
    (he : e < 1 / 40) (hT : 1600 * (1000000 * Δ) ≤ T) (hσs : 0 ≤ σs) (hσs1 : σs ≤ 1 / 100)
    (f : X → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    (hpert : ∀ p, ‖f p - cgpGlobalMap P.toLocalChartFamily P.zero p‖ ≤
      4 * gafKappa / 5 * ρ p)
    (hZM : ∀ (j : P.slim.finite_centres.toFinset) p, P.slim.cutoff j.1 p = 0 →
      |gafSlimMarker P.toLocalChartFamily P.zero j (f p)| ≤ ρ j.1 / 32) (p : X) :
    (f p ∈ tsupport (gafStageThreeCutoff P.toLocalChartFamily P.zero) →
      (gafStageQ P.toLocalChartFamily P.zero 2).starProjection
        (cgpGlobalMap P.toLocalChartFamily P.zero p) ∈ gafCloud P.toLocalChartFamily P.zero 2) ∧
      DifferentiableAt ℝ (gafStageThreeCutoff P.toLocalChartFamily P.zero) (f p) ∧
      ‖fderiv ℝ (gafStageThreeCutoff P.toLocalChartFamily P.zero) (f p)‖ ≤
        gafCutoffConstant / ρ p := by
  have hcut := gaf02_stageThree_cutoff P hΛ hΔ hμ hτ hLΛ hLmax he hT hσs hσs1 f hpert hZM
  have hseg := hcut.2.2.2.2 p 1 ⟨zero_le_one, le_rfl⟩
  have h1 : (1 - (1 : ℝ)) • cgpGlobalMap P.toLocalChartFamily P.zero p + (1 : ℝ) • f p = f p := by
    simp
  rw [h1] at hseg
  refine ⟨fun hp => ?_, hcut.1.differentiable (by simp) _, hseg⟩
  obtain ⟨j, hj, hη⟩ := hcut.2.2.2.1 p hp
  exact gafStage_core_two_GAF5 P.toLocalChartFamily P.zero p
    ⟨j, hj, by rw [norm_planeAxis]; exact hη⟩

/-- **GAF02's second stage step on the actual data.** After a map `f` with GAF01's prior errors
(`E ≤ 3Σ/10`, `E ≤ 4κ/5`, `H₀`) and CFS31's (ZM) for the edge family, with CFS23's edge cutoff
`ψ₂`, a stage projection `P₂` with CFS14 (3)'s bounds `Ξ` on the edge cloud and the edge test's
normal-error clause: for every `p`, `‖Ψ₂(f p) − 𝓔⁰ p‖ ≤ (E + a)ρ(p)`, `Ψ₂` is differentiable at
`f p`, and `‖d(Ψ₂ ∘ f)_p w − d𝓔⁰_p w‖ ≤ (a·b·(L + H₀) + Ξ(L + H₀) + e + 2H₀)√g(w, w)`,
`a = (5/3)ΞΣ + (1 + Ξ)E`. -/
theorem gaf02_stageTwo_step_GAF6
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hLmax : 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax)
    (he : e < 1 / 40) (hT : 1600 * (1000000 * Δ) ≤ T) (hσs : 0 ≤ σs) (hσs1 : σs ≤ 1 / 100)
    (hσc : σc ∈ Icc (0 : ℝ) 1) (hγc : γc ∈ Icc (0 : ℝ) 1) (hεr : εr ∈ Icc (0 : ℝ) 1)
    (sel : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X)
    (hsel : ∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero 1,
      cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 1)
        (sel x) = x)
    (plane : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
      Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)))
    (Pst : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
      BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    {Ξ sg eg E H₀ : ℝ} (hΞ : 0 ≤ Ξ) (hsg : 0 < sg) (heg : 0 ≤ eg) (hE0 : 0 ≤ E)
    (hE : E ≤ 3 * sg / 10) (hEκ : E ≤ 4 * gafKappa / 5) (hH₀ : 0 ≤ H₀)
    (hPst : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 1, ∀ z ∈ ball x (sg * ρ (sel x)),
      ‖Pst z - (x + (plane x).starProjection (z - x))‖ ≤ Ξ * (sg * ρ (sel x)))
    (hPd : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 1, ∀ z ∈ ball x (sg * ρ (sel x)),
      DifferentiableAt ℝ Pst z ∧ ‖fderiv ℝ Pst z - (plane x).starProjection‖ ≤ Ξ)
    (hrank : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 1, ∃ i ∈ P.edge.centres,
      ∀ q : X,
      cgpProjMap P.toLocalChartFamily P.zero (cgpQ2Tags P.toLocalChartFamily P.zero) q = x →
        ∀ w : TangentSpace 𝓘(ℝ, E3) q, (ρ i)⁻¹ ^ 2 * g.inner q w w = 1 →
          ‖(ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
              (cgpQ2Tags P.toLocalChartFamily P.zero)) q w -
            (plane x).starProjection
              ((ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
                (cgpQ2Tags P.toLocalChartFamily P.zero)) q w)‖ < eg)
    (f : X → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    (hf : ∀ p, MDifferentiableAt 𝓘(ℝ, E3)
      𝓘(ℝ, BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) f p)
    (hprior : ∀ p, ‖f p - cgpGlobalMap P.toLocalChartFamily P.zero p‖ ≤ E * ρ p)
    (hpriorD : ∀ p w, ‖mvfderiv 𝓘(ℝ, E3) f p w -
      mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) p w‖ ≤
        H₀ * Real.sqrt (g.inner p w w))
    (hZM : ∀ (j : P.edge.finite_centres.toFinset) p, P.edge.cutoff j.1 p = 0 →
      |gafEdgeMarker P.toLocalChartFamily P.zero j (f p)| ≤ ρ j.1 / 32) :
    ∀ p,
      ‖adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 1) Pst
          (gafStageTwoCutoff P.toLocalChartFamily P.zero) (f p) -
          cgpGlobalMap P.toLocalChartFamily P.zero p‖ ≤
        (E + (5 / 3 * Ξ * sg + (1 + Ξ) * E)) * ρ p ∧
      DifferentiableAt ℝ (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 1) Pst
          (gafStageTwoCutoff P.toLocalChartFamily P.zero)) (f p) ∧
      ∀ w, ‖mvfderiv 𝓘(ℝ, E3) (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 1) Pst
          (gafStageTwoCutoff P.toLocalChartFamily P.zero) ∘ f) p w -
          mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) p w‖ ≤
        ((5 / 3 * Ξ * sg + (1 + Ξ) * E) * gafCutoffConstant * (gafDerivativeBound + H₀) +
          Ξ * (gafDerivativeBound + H₀) + eg + 2 * H₀) * Real.sqrt (g.inner p w w) := by
  intro p
  have hsmall : Λ * (1000000 * Δ) ≤ 1 / 4 := by
    have h' : Λ * (1000000 * Δ) = 1000000 * Δ * Λ := by ring
    linarith
  have hpert : ∀ q, ‖f q - cgpGlobalMap P.toLocalChartFamily P.zero q‖ ≤
      4 * gafKappa / 5 * ρ q := fun q =>
    (hprior q).trans (mul_le_mul_of_nonneg_right hEκ (hρ q).le)
  have hcut := gaf02_stageTwo_cutoff P hΛ hΔ hμ hτ hLΛ hLmax he hT hσs hσs1 f hpert hZM
  have hpt := gaf02_stageTwo_cutoff_point_GAF6 P hΛ hΔ hμ hτ hLΛ hLmax he hT hσs hσs1 f hpert
    hZM p
  have hder := gaf01_derivative_bound P hΛ hΔ hμ hτ hLΛ hLmax he hT ⟨hσs, by linarith⟩ hσc hγc
    hεr
  have hF : ∀ q, MDifferentiableAt 𝓘(ℝ, E3)
      𝓘(ℝ, BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
      (cgpGlobalMap P.toLocalChartFamily P.zero) q := fun q =>
    (hder.1 q).mdifferentiableAt (by simp)
  have hnormal := gafStage_two_normal_GAF6 P.toLocalChartFamily P.zero hF plane P.edge.centres
    hrank p
  have hval := gafStage_step_value_GAF5 P.toLocalChartFamily P.zero hΔ hΛ hsmall 1 sel hsel plane
    Pst _ hcut.2.1 hΞ hsg hE0 hE hPst f p hpt.1 (hprior p)
  have hdv := gafStage_step_deriv_GAF5 P.toLocalChartFamily P.zero hΔ hΛ hsmall 1 sel hsel plane
    Pst _ hcut.2.1 hΞ hsg hE0 hE gafCutoffConstant_nonneg
    (zero_le_one.trans one_le_gafDerivativeBound) hH₀ heg hPst hPd f p hpt.1 (hprior p) (hf p)
    (fun _ => hpt.2) (fun w => Real.sqrt (g.inner p w w)) (fun w => Real.sqrt_nonneg _)
    (fun w => hder.2 p w) hnormal (fun w => hpriorD p w)
  exact ⟨hval, hdv.1, hdv.2⟩

/-- **GAF02's third stage step on the actual data.** After a map `f` with GAF01's prior errors
and CFS31's (ZM) for the slim family, with CFS22's slim cutoff `ψ₃`, a stage projection `P₃` with
CFS14 (3)'s bounds `Ξ` on the slim cloud and the slim test's rank clause: the bounds of
`gaf02_stageTwo_step_GAF6` for `Ψ₃`. -/
theorem gaf02_stageThree_step_GAF6
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hLmax : 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax)
    (he : e < 1 / 40) (hT : 1600 * (1000000 * Δ) ≤ T) (hσs : 0 ≤ σs) (hσs1 : σs ≤ 1 / 100)
    (hσc : σc ∈ Icc (0 : ℝ) 1) (hγc : γc ∈ Icc (0 : ℝ) 1) (hεr : εr ∈ Icc (0 : ℝ) 1)
    (sel : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X)
    (hsel : ∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero 2,
      cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 2)
        (sel x) = x)
    (plane : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
      Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)))
    (Pst : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
      BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    {Ξ sg eg E H₀ : ℝ} (hΞ : 0 ≤ Ξ) (hsg : 0 < sg) (heg : 0 ≤ eg) (hE0 : 0 ≤ E)
    (hE : E ≤ 3 * sg / 10) (hEκ : E ≤ 4 * gafKappa / 5) (hH₀ : 0 ≤ H₀)
    (hPst : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 2, ∀ z ∈ ball x (sg * ρ (sel x)),
      ‖Pst z - (x + (plane x).starProjection (z - x))‖ ≤ Ξ * (sg * ρ (sel x)))
    (hPd : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 2, ∀ z ∈ ball x (sg * ρ (sel x)),
      DifferentiableAt ℝ Pst z ∧ ‖fderiv ℝ Pst z - (plane x).starProjection‖ ≤ Ξ)
    (hrank : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 2,
      ∃ i : P.toLocalChartFamily.slim.finite_centres.toFinset,
      ∀ q, cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero) q = x →
        ∀ v, ‖(ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
            (cgpQ3Tags P.toLocalChartFamily P.zero)) q v -
            ((plane x).orthogonalProjectionOnto.comp ((ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3)
              (cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero))
                q) v : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))‖ ≤
          eg * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v))
    (f : X → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    (hf : ∀ p, MDifferentiableAt 𝓘(ℝ, E3)
      𝓘(ℝ, BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) f p)
    (hprior : ∀ p, ‖f p - cgpGlobalMap P.toLocalChartFamily P.zero p‖ ≤ E * ρ p)
    (hpriorD : ∀ p w, ‖mvfderiv 𝓘(ℝ, E3) f p w -
      mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) p w‖ ≤
        H₀ * Real.sqrt (g.inner p w w))
    (hZM : ∀ (j : P.slim.finite_centres.toFinset) p, P.slim.cutoff j.1 p = 0 →
      |gafSlimMarker P.toLocalChartFamily P.zero j (f p)| ≤ ρ j.1 / 32) :
    ∀ p,
      ‖adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 2) Pst
          (gafStageThreeCutoff P.toLocalChartFamily P.zero) (f p) -
          cgpGlobalMap P.toLocalChartFamily P.zero p‖ ≤
        (E + (5 / 3 * Ξ * sg + (1 + Ξ) * E)) * ρ p ∧
      DifferentiableAt ℝ (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 2) Pst
          (gafStageThreeCutoff P.toLocalChartFamily P.zero)) (f p) ∧
      ∀ w, ‖mvfderiv 𝓘(ℝ, E3) (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 2) Pst
          (gafStageThreeCutoff P.toLocalChartFamily P.zero) ∘ f) p w -
          mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) p w‖ ≤
        ((5 / 3 * Ξ * sg + (1 + Ξ) * E) * gafCutoffConstant * (gafDerivativeBound + H₀) +
          Ξ * (gafDerivativeBound + H₀) + eg + 2 * H₀) * Real.sqrt (g.inner p w w) := by
  intro p
  have hsmall : Λ * (1000000 * Δ) ≤ 1 / 4 := by
    have h' : Λ * (1000000 * Δ) = 1000000 * Δ * Λ := by ring
    linarith
  have hpert : ∀ q, ‖f q - cgpGlobalMap P.toLocalChartFamily P.zero q‖ ≤
      4 * gafKappa / 5 * ρ q := fun q =>
    (hprior q).trans (mul_le_mul_of_nonneg_right hEκ (hρ q).le)
  have hcut := gaf02_stageThree_cutoff P hΛ hΔ hμ hτ hLΛ hLmax he hT hσs hσs1 f hpert hZM
  have hpt := gaf02_stageThree_cutoff_point_GAF6 P hΛ hΔ hμ hτ hLΛ hLmax he hT hσs hσs1 f hpert
    hZM p
  have hder := gaf01_derivative_bound P hΛ hΔ hμ hτ hLΛ hLmax he hT ⟨hσs, by linarith⟩ hσc hγc
    hεr
  have hF : ∀ q, MDifferentiableAt 𝓘(ℝ, E3)
      𝓘(ℝ, BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
      (cgpGlobalMap P.toLocalChartFamily P.zero) q := fun q =>
    (hder.1 q).mdifferentiableAt (by simp)
  have hnormal := gafStage_three_normal_GAF6 P.toLocalChartFamily P.zero hF plane hrank p
  have hval := gafStage_step_value_GAF5 P.toLocalChartFamily P.zero hΔ hΛ hsmall 2 sel hsel plane
    Pst _ hcut.2.1 hΞ hsg hE0 hE hPst f p hpt.1 (hprior p)
  have hdv := gafStage_step_deriv_GAF5 P.toLocalChartFamily P.zero hΔ hΛ hsmall 2 sel hsel plane
    Pst _ hcut.2.1 hΞ hsg hE0 hE gafCutoffConstant_nonneg
    (zero_le_one.trans one_le_gafDerivativeBound) hH₀ heg hPst hPd f p hpt.1 (hprior p) (hf p)
    (fun _ => hpt.2) (fun w => Real.sqrt (g.inner p w w)) (fun w => Real.sqrt_nonneg _)
    (fun w => hder.2 p w) hnormal (fun w => hpriorD p w)
  exact ⟨hval, hdv.1, hdv.2⟩

end Packets

end DifferentialGeometry.Geometry.Collapse
