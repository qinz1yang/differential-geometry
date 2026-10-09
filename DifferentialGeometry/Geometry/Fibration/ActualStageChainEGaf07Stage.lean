import DifferentialGeometry.Geometry.Fibration.ActualStageChainEGaf07Circle
import DifferentialGeometry.Geometry.Fibration.ActualStageChainGaf07LevelSlim

/-!
# GAF07: whole stage fibre = whole final fibre (circle), and the slim submersion

Blueprint `master207B.tex`, GAF07 (B:6150–6165): "let `f_j = π_j𝓔^j` and `Θ_j : V_j⁰ → W_j` be
CGP08's later diffeomorphism … `π_jE = Θ_j f_j` … GAF06 puts every such final preimage inside the
original threshold-5 chart, where CGP08 puts `f_j(p)` in `V_j⁰`. Injectivity of `Θ_j` then forces
`f_j(p) = Θ_j⁻¹(w)`. These two inclusions prove equality of the WHOLE stage and final fibres."

* `Gaf02ChainE.gaf07_circle_stage_fibre_GAFC` (circle, BASES' `Θ₁`, `V_i⁰`, `W₁`): for `w ∈ B₁`
  in the ratio piece of `i` there is `w₀ ∈ V_i⁰` with `Θ₁(w₀) = w`, and the WHOLE stage fibre
  `f₁⁻¹(w₀)` EQUALS the WHOLE final fibre `(π₁E)⁻¹(w)` (injectivity through the retained circle
  coordinate on `V_i⁰`, CGP07).
* `Gaf02Chain.gaf07_slim_submersion_GAFC` (slim, BASES-free): at every `p` whose final slim image
  `π₃E(p)` lies in the ratio piece of `i`, `p ∈ Y_i` and the adjusted axis coordinate
  `g_i = R_i⁻¹ proj₀ u_i(π₃E)` has surjective differential (LFR20.1 + `‖Dg_i − Dη_i‖ < c₃`).
* Consumer `Gaf02ChainEJA.gaf07_circle_stage_fibre_connected_GAFC`: on a chain with (JA) (TCP01
  range of the packet), every whole stage circle fibre over `B₁` is connected.
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

attribute [local instance] LocalChartPackets.instMetricN LocalChartPackets.instChartedN
  LocalChartPackets.instMetricC

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}

namespace Gaf02ChainE

variable {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

/-- **GAF07, whole stage fibre = whole final fibre, circle stage** (B:6150–6165): for `w ∈ W₁` in
the ratio piece of `i` there is `w₀ ∈ V_i⁰` with `Θ₁(w₀) = w`, and `f₁⁻¹(w₀) = (π₁E)⁻¹(w)` as WHOLE
subsets of `M`. -/
theorem gaf07_circle_stage_fibre_GAFC (C : Gaf02ChainE P Kj Ξ Γ S eg c cw) (hc : c 2 < 1 / 1000)
    (w : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    (hW : w ∈ C.toChain.finalBase_BAS 0)
    (i : P.toLocalChartFamily.circle.finite_centres.toFinset)
    (hm : 9 / 10 * ρ i.1 < blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (.inl i) w)
    (hr : ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inl i) w‖ <
      4 * blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inl i) w) :
    ∃ w₀ ∈ C.toChain.circlePatch_BAS i, C.toChain.Θ_BAS 0 w₀ = w ∧
      C.toChain.stageMap_BAS 0 ⁻¹' {w₀} =
        (fun p => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E p)) ⁻¹'
          {w} := by
  have hπ : ∀ y, (gafStageQ P.toLocalChartFamily P.zero 0).starProjection y = y :=
    gafStageQ_zero_starProjection_BAS P.toLocalChartPackets
  have hY : ∀ p, (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E p) = w →
      p ∈ gaf07CircleY_GAFC P.toLocalChartPackets i := by
    intro p hp
    rw [hπ] at hp
    have h1 : (1 - (1 : ℝ)) • cgpGlobalMap P.toLocalChartFamily P.zero p +
        (1 : ℝ) • C.toChain.E p = w := by
      rw [sub_self, zero_smul, zero_add, one_smul, hp]
    obtain ⟨hpi, hη, -⟩ := C.toChain.gaf06_circle_G47 hc i p 1 ⟨zero_le_one, le_rfl⟩
      (by rw [h1]; exact hm) (by rw [h1]; exact hr.le)
    exact ⟨hpi, by linarith⟩
  obtain ⟨p₀, hp₀⟩ := C.gaf07_circle_onto_GAFC w hW
  have hWm := C.final_mem_circleBase_GAFC i (hY p₀ hp₀)
  rw [hp₀, C.toChain.finalBase_inter_circle_BAS i] at hWm
  obtain ⟨w₀, hw₀, hΘ⟩ := hWm
  have hbij := (C.toChain.cgp07_circle_BAS C.rough i).1
  have hret : ∀ y, ((ρ i.1)⁻¹ • gafCircleVector P.toLocalChartPackets i) (C.toChain.Θ_BAS 0 y) =
      ((ρ i.1)⁻¹ • gafCircleVector P.toLocalChartPackets i) y := fun y => by
    simp only [FunLike.coe_smul, Pi.smul_apply, (C.toChain.theta_retains_circle_BAS i y).1]
  refine ⟨w₀, hw₀, hΘ, ?_⟩
  ext p
  constructor
  · intro hp
    have hp' : C.toChain.stageMap_BAS 0 p = w₀ := hp
    change (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E p) = w
    rw [C.toChain.final_factor_BAS 0 p, hp', hΘ]
  · intro hp
    have hp' : (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E p) = w := hp
    have hpY := hY p hp'
    have hpV := C.toChain.circle_mem_patch_of_domain5_BAS i hpY.1 hpY.2
    change C.toChain.stageMap_BAS 0 p = w₀
    refine hbij.injOn hpV hw₀ ?_
    rw [← hret (C.toChain.stageMap_BAS 0 p), ← C.toChain.final_factor_BAS 0 p, hp', ← hΘ, hret]

end Gaf02ChainE

namespace Gaf02Chain

variable {P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
    T V}
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

/-- **GAF07, submersion, slim stage** (B:6092–6093; BASES-free): at every `p` whose final slim
image `π₃E(p)` lies in the ratio piece of `i` (`v_i > .9R_i`, `‖u_i‖ < 4·10⁵Δ v_i`), `p ∈ Y_i` and
the adjusted axis coordinate `g_i` has surjective differential at `p`. -/
theorem gaf07_slim_submersion_GAFC (C : Gaf02Chain P Kj Ξ Γ S eg c cw) (hc : c 2 < 1 / 1000)
    (i : P.toLocalChartFamily.slim.finite_centres.toFinset) (p : X)
    (hm : 9 / 10 * ρ i.1 < blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (.inr (.inl i)) ((gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.E p)))
    (hr : ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inr (.inl i))
        ((gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.E p))‖ <
      4 * (10 ^ 5 * Δ) * blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (.inr (.inl i)) ((gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.E p))) :
    p ∈ gaf07SlimY_GAFC P i ∧
      Surjective (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (C.gaf07SlimCoord_GAFC i) p) := by
  have hj := (Set.Finite.mem_toFinset _).mp i.2
  set cc := P.slim.centre i.1 hj with hcc
  have hri := hρ i.1
  obtain ⟨-, hΔ1, -⟩ := C.std
  have hball : ball i.1 (1000000 * Δ * ρ i.1) = ball i.1 (10 ^ 6 * Δ * ρ i.1) := by norm_num
  have hmk := marker_stageQ_G47 P.toLocalChartFamily P.zero (st := 2) (t := .inr (.inl i))
    (slim_mem_cgpQ3Tags P.toLocalChartFamily P.zero i) (C.E p)
  have hvk := vector_stageQ_G47 P.toLocalChartFamily P.zero (st := 2) (t := .inr (.inl i))
    (slim_mem_cgpQ3Tags P.toLocalChartFamily P.zero i) (C.E p)
  rw [hmk] at hm
  rw [hmk, hvk] at hr
  have h1 : (1 - (1 : ℝ)) • cgpGlobalMap P.toLocalChartFamily P.zero p + (1 : ℝ) • C.E p =
      C.E p := by
    rw [sub_self, zero_smul, zero_add, one_smul]
  obtain ⟨hpi, hη, -⟩ := C.gaf06_slim_G47 hc i p 1 ⟨zero_le_one, le_rfl⟩
    (by rw [h1]; exact hm) (by rw [h1]; exact hr.le)
  refine ⟨⟨hpi, by nlinarith⟩, ?_⟩
  obtain ⟨H, hH, hder⟩ := C.gaf07_slim_derivative_GAFC
  have hyd : dist p i.1 < 91 / 100 * (10 ^ 6 * Δ) * ρ i.1 :=
    cc.dist_lt_of_abs_coord_le_ZERO (hball ▸ hpi) (by nlinarith [abs_nonneg (cc.coord p)])
  obtain ⟨w, hw1, hw⟩ := cc.derivative_GAFC hyd
  set d : ℝ := mvfderiv 𝓘(ℝ, E3) cc.coord p w with hd
  have hd0 : 0 < d := by linarith
  refine surjective_of_right_inverse_perturbation_nu_GAFC
    (show E3 →L[ℝ] ℝ from mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) cc.coord p)
    (show E3 →L[ℝ] ℝ from mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (C.gaf07SlimCoord_GAFC i) p)
    (ContinuousLinearMap.toSpanSingleton ℝ (d⁻¹ • w)) ?_
    (fun v => Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner p v v)) (c := max H 0) (K := 4 / 3)
    (fun t => ?_) (fun v => ?_) (le_max_right _ _) ?_
  · refine ContinuousLinearMap.ext fun t => ?_
    change (mvfderiv 𝓘(ℝ, E3) cc.coord p) (t • d⁻¹ • w) = t
    rw [map_smul, map_smul, ← hd, smul_eq_mul, smul_eq_mul, inv_mul_cancel₀ hd0.ne', mul_one]
  · change Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner p (t • d⁻¹ • w) (t • d⁻¹ • w)) ≤ 4 / 3 * ‖t‖
    have hsc : g.inner p (t • d⁻¹ • w) (t • d⁻¹ • w) = (t * d⁻¹) ^ 2 * g.inner p w w := by
      rw [smul_smul, map_smul, map_smul]
      simp only [smul_apply, smul_eq_mul]
      ring
    rw [hsc, show (ρ i.1)⁻¹ ^ 2 * ((t * d⁻¹) ^ 2 * g.inner p w w) =
      (t * d⁻¹) ^ 2 * ((ρ i.1)⁻¹ ^ 2 * g.inner p w w) by ring, hw1, mul_one,
      Real.sqrt_sq_eq_abs, abs_mul, abs_of_pos (inv_pos.mpr hd0), Real.norm_eq_abs]
    have h43 : d⁻¹ ≤ 4 / 3 := by
      rw [inv_le_comm₀ hd0 (by norm_num)]
      linarith
    calc |t| * d⁻¹ ≤ |t| * (4 / 3) := mul_le_mul_of_nonneg_left h43 (abs_nonneg t)
      _ = 4 / 3 * |t| := by ring
  · rw [Real.norm_eq_abs]
    refine (hder i p hpi (by nlinarith) v).trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)
  · have : max H 0 < 1 / 1000 := max_lt (hH.trans hc) (by norm_num)
    linarith

end Gaf02Chain

namespace Gaf02ChainEJA

variable {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ} {cadj : ℝ}

/-- **Consumer: whole stage circle fibres are connected** (chain with (JA), TCP01 range of the
packet): for `w ∈ W₁` in the ratio piece of `i`, the stage point `w₀ = Θ₁⁻¹(w) ∈ V_i⁰` has a
connected WHOLE stage fibre `f₁⁻¹(w₀)`, equal to the whole final fibre. -/
theorem gaf07_circle_stage_fibre_connected_GAFC (C : Gaf02ChainEJA P Kj Ξ Γ S eg c cw cadj)
    (hβ : β 2 ≤ 1 / 10000000) (hd : γ + β 2 < 1 / 10)
    (w : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    (hW : w ∈ C.toChain.finalBase_BAS 0)
    (i : P.toLocalChartFamily.circle.finite_centres.toFinset)
    (hm : 9 / 10 * ρ i.1 < blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (.inl i) w)
    (hr : ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inl i) w‖ <
      4 * blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inl i) w) :
    ∃ w₀ ∈ C.toChain.circlePatch_BAS i, C.toChain.Θ_BAS 0 w₀ = w ∧
      IsConnected (C.toChain.stageMap_BAS 0 ⁻¹' {w₀}) := by
  obtain ⟨w₀, hw₀, hΘ, heq⟩ := C.toGaf02ChainE.gaf07_circle_stage_fibre_GAFC C.c_two_lt w hW i hm hr
  refine ⟨w₀, hw₀, hΘ, ?_⟩
  rw [heq]
  exact (C.toGaf02ChainE.gaf07_circle_whole_fibre_GAFC C.c_two_lt hβ hd w hW i hm hr).2.2.2

end Gaf02ChainEJA

end DifferentialGeometry.Geometry.Collapse
