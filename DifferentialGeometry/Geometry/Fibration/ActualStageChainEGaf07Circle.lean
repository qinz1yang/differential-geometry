import DifferentialGeometry.Geometry.Fibration.ActualStageChainGaf07Level
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEGaf05Circle
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEJA

/-!
# GAF07, circle stage, on `Gaf02ChainE` with BASES' base `W₁`: onto, submersion, WHOLE fibres

Blueprint `master207B.tex`, GAF07 (`thm:fibration-whole-closed-fiber-bundles`, B:6049–6165),
`j = 1`: `B₁ = ⋃_i {w ∈ W₁ : v_i(w) > .9R_i, |u_i(w)|/v_i(w) < 4}`, `X₁ = (π₁E)⁻¹(B₁)`;
`π₁E : X₁ → B₁` is onto, a submersion, and its WHOLE fibres are connected, each equal to the whole
adjusted level `h_1⁻¹(a)` and homeomorphic (FC34: diffeomorphic) to the original fibre of `η_i`.
Here `W₁ = C.toChain.finalBase_BAS 0 = Θ₁(V₁⁰)` is lane C14-BASES' final base (CGP08), with the
CGP07 patches `V_i⁰` (`Gaf02Chain.cgp07_circle_BAS`) and GAF05's patch chart
(`Gaf02ChainE.gaf05_circleBase_chart_GAFC`); `B₁ = W₁ ∩ gaf07CircleRatio_G47` (GAF47's ratio set).

* `isOpen_gaf07CircleRatio_GAFC`: the ratio set is open, so `B₁` is relatively open in `W₁`
  (an open subset of the embedded base: a manifold once BASES gives `W₁`'s smooth structure).
* `Gaf02ChainE.gaf07_circle_onto_GAFC`: every `w ∈ B₁` is `π₁E(p)` (CGP07–08).
* `Gaf02ChainE.gaf07_circle_whole_fibre_GAFC`: for `w ∈ B₁` and an index `i` of its ratio piece,
  `a = R_i⁻¹u_i(w)` has `‖a‖ < 4`, the WHOLE fibre `(π₁E)⁻¹(w)` EQUALS the whole adjusted level
  `{p ∈ Y_i | g_i(p) = a}`, is homeomorphic to the original fibre `{p ∈ Y_i | η_i(p) = a}` and is
  connected (in particular nonempty).
* `Gaf02ChainE.gaf07_circle_submersion_GAFC`: at every `p ∈ X₁` and every ratio index `i` of
  `π₁E(p)`, the base chart `R_i⁻¹u_i` composed with `π₁E` (= `g_i`) has surjective differential.
* Consumer `Gaf02ChainEJA.gaf07_circle_bundle_GAFC`: the four clauses on a chain with (JA).

Numerical inputs: GAF01's `c₃ < 1/1000` and the packet's TCP01 range `β₂ ≤ 10⁻⁷`, `γ + β₂ < 1/10`
(the hypotheses of `tcp01_gram_right_inverse_FAM2`, TCP01's right inverse of `Dη_i`).
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

/-- GAF07's circle ratio set `⋃_i {v_i > .9R_i, ‖u_i‖ < 4v_i}` is open. -/
theorem isOpen_gaf07CircleRatio_GAFC (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s
    b' s' ε γc βc Lmax τ γ δ εr e T V) : IsOpen (gaf07CircleRatio_G47 P) := by
  refine isOpen_iUnion fun i => ?_
  exact (isOpen_lt continuous_const (blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily
      P.zero => ℝ²) (.inl i)).continuous).inter
    (isOpen_lt (blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (.inl i)).continuous.norm (continuous_const.mul (blockMarkerCLM
        (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inl i)).continuous))

namespace Gaf02ChainE

variable {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

/-- The final circle image `π₁E(p)` of a point of `Y_i` lies in the later patch
`V_i = W₁ ∩ {v_i > .9R_i, ‖u_i‖ < 5.5R_i} = Θ₁(V_i⁰)`. -/
theorem final_mem_circleBase_GAFC (C : Gaf02ChainE P Kj Ξ Γ S eg c cw)
    (i : P.toLocalChartFamily.circle.finite_centres.toFinset) {p : X}
    (hp : p ∈ gaf07CircleY_GAFC P.toLocalChartPackets i) :
    (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E p) ∈
      C.toChain.finalBase_BAS 0 ∩ markedCondition_BPRE (gafCircleVector P.toLocalChartPackets i)
        (gafCircleMarker P.toLocalChartPackets i) (ρ i.1) 1 := by
  rw [C.toChain.finalBase_inter_circle_BAS i, C.toChain.final_factor_BAS 0 p]
  exact ⟨_, C.toChain.circle_mem_patch_of_domain5_BAS i hp.1 hp.2, rfl⟩

/-- **GAF07, onto** (B:6094–6095, CGP07–CGP08): every point of `B₁ = W₁ ∩ R₁` (indeed of `W₁`) is
the final image `π₁E(p)` of an original threshold-6 plateau point. -/
theorem gaf07_circle_onto_GAFC (C : Gaf02ChainE P Kj Ξ Γ S eg c cw)
    (w : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    (hw : w ∈ C.toChain.finalBase_BAS 0) :
    ∃ p, (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E p) = w := by
  obtain ⟨w₀, hw₀, rfl⟩ := hw
  obtain ⟨_, ⟨j, rfl⟩, hj⟩ := hw₀
  obtain ⟨p, -, hp⟩ := (C.toChain.cgp07_circle_BAS C.rough j).2.1 w₀ hj
  exact ⟨p, by rw [C.toChain.final_factor_BAS 0 p, hp]⟩

/-- **GAF07, WHOLE circle fibres** (B:6104–6149): for `w ∈ B₁ = W₁ ∩ R₁` in the ratio piece of `i`,
`a = R_i⁻¹u_i(w)` has `‖a‖ < 4`; the WHOLE fibre `(π₁E)⁻¹(w)` equals the whole adjusted level
`{p ∈ Y_i | g_i(p) = a}`, is homeomorphic to the original fibre `{p ∈ Y_i | η_i(p) = a}`, and is
connected. -/
theorem gaf07_circle_whole_fibre_GAFC (C : Gaf02ChainE P Kj Ξ Γ S eg c cw) (hc : c 2 < 1 / 1000)
    (hβ : β 2 ≤ 1 / 10000000) (hd : γ + β 2 < 1 / 10)
    (w : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    (hW : w ∈ C.toChain.finalBase_BAS 0)
    (i : P.toLocalChartFamily.circle.finite_centres.toFinset)
    (hm : 9 / 10 * ρ i.1 < blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (.inl i) w)
    (hr : ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inl i) w‖ <
      4 * blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inl i) w) :
    ‖(ρ i.1)⁻¹ • blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inl i) w‖
        < 4 ∧
      (fun p => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E p)) ⁻¹' {w} =
        {p | p ∈ gaf07CircleY_GAFC P.toLocalChartPackets i ∧ C.toChain.gaf07CircleCoord_GAFC i p =
          (ρ i.1)⁻¹ • blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
            (.inl i) w} ∧
      Nonempty ((fun p => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection
          (C.toChain.E p)) ⁻¹' {w} ≃ₜ
        {p | p ∈ gaf07CircleY_GAFC P.toLocalChartPackets i ∧
          cgpCoord P.toLocalChartFamily P.zero (.inl i) p =
            (ρ i.1)⁻¹ • blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
              (.inl i) w}) ∧
      IsConnected ((fun p => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection
        (C.toChain.E p)) ⁻¹' {w}) := by
  have hri := hρ i.1
  have hπ : ∀ y, (gafStageQ P.toLocalChartFamily P.zero 0).starProjection y = y :=
    gafStageQ_zero_starProjection_BAS P.toLocalChartPackets
  -- GAF06 at a point of the fibre (τ = 1): the point lies in `Y_i`
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
  -- a preimage exists; its marker is exactly `R_i`, so `‖a‖ < 4`
  obtain ⟨p₀, hp₀⟩ := C.gaf07_circle_onto_GAFC w hW
  have hY₀ := hY p₀ hp₀
  have hv : blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inl i) w =
      ρ i.1 := by
    rw [← hp₀, hπ]
    exact C.gaf05_first_plateau_G47 i hY₀.1 (by linarith [hY₀.2])
  have ha : ‖(ρ i.1)⁻¹ • blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (.inl i) w‖ < 4 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hri)]
    rw [hv] at hr
    rw [inv_mul_lt_iff₀ hri]
    linarith
  -- the whole fibre is the whole adjusted level
  have hW₀ := C.final_mem_circleBase_GAFC i hY₀
  rw [hp₀] at hW₀
  have hinj := (C.gaf05_circleBase_chart_GAFC i).2.1.injOn
  have heq : (fun p => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection
      (C.toChain.E p)) ⁻¹' {w} =
      {p | p ∈ gaf07CircleY_GAFC P.toLocalChartPackets i ∧ C.toChain.gaf07CircleCoord_GAFC i p =
        (ρ i.1)⁻¹ • blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (.inl i) w} := by
    ext p
    constructor
    · intro hp
      have hp' : (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E p) = w := hp
      refine ⟨hY p hp', ?_⟩
      change (ρ i.1)⁻¹ • blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (.inl i) ((gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E p)) = _
      rw [hp']
    · rintro ⟨hpY, hpa⟩
      have hWp := C.final_mem_circleBase_GAFC i hpY
      change (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E p) = w
      refine hinj hWp hW₀ ?_
      change (ρ i.1)⁻¹ • blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (.inl i) ((gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E p)) =
        (ρ i.1)⁻¹ • blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (.inl i) w
      exact hpa
  obtain ⟨⟨φ⟩, hconn, -⟩ := C.toChain.gaf07_circle_level_GAFC hc hβ hd i ha
  refine ⟨ha, heq, ⟨(Homeomorph.setCongr heq).trans φ.symm⟩, ?_⟩
  rw [heq]
  exact hconn

/-- **GAF07, submersion** (B:6092–6093): at every point `p` of `X₁ = (π₁E)⁻¹(W₁ ∩ R₁)` and every
ratio index `i` of `π₁E(p)`, `p ∈ Y_i` and `g_i = R_i⁻¹u_i ∘ π₁E` (the base chart of GAF05 composed
with `π₁E`) has surjective differential at `p`. -/
theorem gaf07_circle_submersion_GAFC (C : Gaf02ChainE P Kj Ξ Γ S eg c cw) (hc : c 2 < 1 / 1000)
    (hβ : β 2 ≤ 1 / 10000000) (hd : γ + β 2 < 1 / 10)
    (i : P.toLocalChartFamily.circle.finite_centres.toFinset) (p : X)
    (hm : 9 / 10 * ρ i.1 < blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (.inl i) ((gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E p)))
    (hr : ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inl i)
        ((gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E p))‖ <
      4 * blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inl i)
        ((gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E p))) :
    p ∈ gaf07CircleY_GAFC P.toLocalChartPackets i ∧
      Surjective (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²) (C.toChain.gaf07CircleCoord_GAFC i) p) := by
  have hj := (Set.Finite.mem_toFinset _).mp i.2
  have hri := hρ i.1
  have hπ : ∀ y, (gafStageQ P.toLocalChartFamily P.zero 0).starProjection y = y :=
    gafStageQ_zero_starProjection_BAS P.toLocalChartPackets
  rw [hπ] at hm hr
  have h1 : (1 - (1 : ℝ)) • cgpGlobalMap P.toLocalChartFamily P.zero p +
      (1 : ℝ) • C.toChain.E p = C.toChain.E p := by
    rw [sub_self, zero_smul, zero_add, one_smul]
  obtain ⟨hpi, hη, -⟩ := C.toChain.gaf06_circle_G47 hc i p 1 ⟨zero_le_one, le_rfl⟩
    (by rw [h1]; exact hm) (by rw [h1]; exact hr.le)
  refine ⟨⟨hpi, by linarith⟩, ?_⟩
  obtain ⟨H, hH, hder⟩ := C.toChain.gaf07_circle_derivative_GAFC
  have key := tcp01_gram_right_inverse_FAM2 P.toLocalChartPackets hβ hd hj hpi
  let _ := radialScaledBundle g (ρ i.1)⁻¹ (inv_pos.mpr hri)
  obtain ⟨-, R, hR, -, hR2⟩ := key
  refine surjective_of_right_inverse_perturbation_nu_GAFC
    (show E3 →L[ℝ] ℝ² from mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²)
      (cgpCoord P.toLocalChartFamily P.zero (.inl i)) p)
    (show E3 →L[ℝ] ℝ² from mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²) (C.toChain.gaf07CircleCoord_GAFC i) p)
    R hR (fun v => Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner p v v)) (c := max H 0) (K := 2)
    (fun w => ?_) (fun v => ?_) (le_max_right _ _) ?_
  · have hn := norm_tangent_radialScaled_KA4 g hri p (R w)
    calc Real.sqrt _ = ‖R w‖ := hn.symm
      _ ≤ ‖R‖ * ‖w‖ := R.le_opNorm w
      _ ≤ 2 * ‖w‖ := mul_le_mul_of_nonneg_right hR2.le (norm_nonneg w)
  · refine (hder i p hpi (by linarith) v).trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)
  · have : max H 0 < 1 / 1000 := max_lt (hH.trans hc) (by norm_num)
    linarith

end Gaf02ChainE

namespace Gaf02ChainEJA

variable {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ} {cadj : ℝ}

/-- **Consumer: GAF07's circle bundle clauses on a chain with (JA)** (TCP01 range of the packet):
`B₁ = W₁ ∩ R₁` is relatively open in BASES' `W₁`; `π₁E` maps onto `W₁`; every WHOLE fibre over
`B₁` equals a whole adjusted level, is homeomorphic to an original circle fibre and is connected;
and `π₁E` is a submersion in the base charts at every point of `X₁`. -/
theorem gaf07_circle_bundle_GAFC (C : Gaf02ChainEJA P Kj Ξ Γ S eg c cw cadj)
    (hβ : β 2 ≤ 1 / 10000000) (hd : γ + β 2 < 1 / 10) :
    IsOpen (gaf07CircleRatio_G47 P.toLocalChartPackets) ∧
    (∀ w ∈ C.toChain.finalBase_BAS 0,
      ∃ p, (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E p) = w) ∧
    (∀ w ∈ C.toChain.finalBase_BAS 0 ∩ gaf07CircleRatio_G47 P.toLocalChartPackets,
      IsConnected ((fun p => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection
        (C.toChain.E p)) ⁻¹' {w})) ∧
    ∀ (i : P.toLocalChartFamily.circle.finite_centres.toFinset) (p : X),
      9 / 10 * ρ i.1 < blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (.inl i) ((gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E p)) →
      ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inl i)
          ((gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E p))‖ <
        4 * blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inl i)
          ((gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E p)) →
      Surjective (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²) (C.toChain.gaf07CircleCoord_GAFC i) p) := by
  refine ⟨isOpen_gaf07CircleRatio_GAFC _, fun w hw => C.toGaf02ChainE.gaf07_circle_onto_GAFC w hw,
    fun w hw => ?_, fun i p hm hr =>
      (C.toGaf02ChainE.gaf07_circle_submersion_GAFC C.c_two_lt hβ hd i p hm hr).2⟩
  obtain ⟨hW, hR⟩ := hw
  obtain ⟨_, ⟨i, rfl⟩, hi⟩ := hR
  exact (C.toGaf02ChainE.gaf07_circle_whole_fibre_GAFC C.c_two_lt hβ hd w hW i hi.1
    hi.2).2.2.2

end Gaf02ChainEJA

end DifferentialGeometry.Geometry.Collapse
