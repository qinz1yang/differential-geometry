import DifferentialGeometry.Geometry.Fibration.ActualStageChainWitness
import DifferentialGeometry.Geometry.Fibration.ActualStageCloudInputs

/-!
# CFS26 on the actual closed-carrier packets

Blueprint `master207B.tex`, CFS26 (`lem:fibration-actual-support-scale`, B:3582–3616). On the
actual packets `P : LocalChartPackets …` (an ancestor of the final family `LocalChartPacketsC14Z`),
with the retained markers `a ∈ I₊ = I₂ ∪ I_e ∪ I_s` of `𝓔⁰ = cgpGlobalMap` (centre `c_a`,
`R_a = ρ(c_a)`, actual smooth-domain radius `D_a ∈ {200, 100Δ, 10⁶Δ}`, actual cutoff
`cgpMarkerCutoff a`, whose zero extension off `U_a = B(c_a, D_aR_a)` it is), `D_* = 10⁶Δ`,
`Δ ≥ 1` and the row's choice `ΛD_* ≤ 1/4`:

* (AS) on the whole closed domain `B̄(c_a, D_aR_a) ⊇ U_a`, which contains the closed support of the
  cutoff; (AS) at every preimage of an image point with a positive marker;
* every point of an original core (the retained cloud) and of every enlarged stage cloud `S̃_st`
  has a retained FULL constant marker;
* ANY two preimages of a point of `S̃_st` have scale ratio in `[3/5, 5/3]`; FC26's radius control
  and CFS07's (MC) hold for every pair of cloud preimages and every selection of preimages;
* for `Q₁` the scale block gives the exact identity `|ρ p − ρ q| ≤ |𝓔⁰p − 𝓔⁰q|`.

Main theorem: `cfs26_row_CFSB`.
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

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}
  {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
  [∀ a, MetricSpace (C a)] {o : ∀ a, C a}

/-- The actual smooth-domain radii are at most `D_* = 10⁶Δ` (`Δ ≥ 1`). -/
theorem cgpMarkerDomain_le_CFSB
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc) (hΔ : 1 ≤ Δ)
    (a : CGPMarkerIndex L) : cgpMarkerDomain L a ≤ 1000000 * Δ := by
  rcases a with j | j | j
  · change (200 : ℝ) ≤ 1000000 * Δ
    linarith
  · exact le_rfl
  · change 100 * Δ ≤ 1000000 * Δ
    linarith

/-- (AS) on the whole closed domain `B̄(c_a, D_aR_a)` of a retained marker. -/
theorem cgpMarker_domain_scale_CFSB
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc) (hΔ : 1 ≤ Δ)
    (hΛ : 0 ≤ Λ) (hsmall : Λ * (1000000 * Δ) ≤ 1 / 4) (a : CGPMarkerIndex L) :
    ∀ q ∈ closedBall (cgpMarkerCentre L a) (cgpMarkerDomain L a * ρ (cgpMarkerCentre L a)),
      3 * ρ (cgpMarkerCentre L a) / 4 ≤ ρ q ∧ ρ q ≤ 5 * ρ (cgpMarkerCentre L a) / 4 := by
  intro q hq
  have hsmall' : ((Real.toNNReal Λ : NNReal) : ℝ) * cgpMarkerDomain L a ≤ 1 / 4 := by
    rw [Real.coe_toNNReal _ hΛ]
    exact (mul_le_mul_of_nonneg_left (cgpMarkerDomain_le_CFSB L hΔ a) hΛ).trans hsmall
  exact scale_bounds_on_closedBall L.lipschitz_scale (hρ _) hsmall' hq

/-- The closed support of an actual retained cutoff lies in its closed domain. -/
theorem tsupport_cgpMarkerCutoff_subset_CFSB
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc) (hΔ : 0 < Δ)
    (a : CGPMarkerIndex L) :
    tsupport (cgpMarkerCutoff L a) ⊆
      closedBall (cgpMarkerCentre L a) (cgpMarkerDomain L a * ρ (cgpMarkerCentre L a)) := by
  refine (closure_mono fun p hp => cgpMarkerCutoff_ne_zero L hΔ a p hp).trans ?_
  exact closure_ball_subset_closedBall

/-- Any two preimages of a point of an enlarged stage cloud have scale ratio in `[3/5, 5/3]`. -/
theorem gafCloudEnlarged_two_preimages_CFSB
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ)
    (hsmall : Λ * (1000000 * Δ) ≤ 1 / 4) (st : Fin 3) :
    ∀ x ∈ gafCloudEnlarged L Z st, ∀ q q' : X,
      cgpProjMap L Z (gafStageTags L Z st) q = x → cgpProjMap L Z (gafStageTags L Z st) q' = x →
      3 / 5 * ρ q ≤ ρ q' ∧ ρ q' ≤ 5 / 3 * ρ q := by
  classical
  intro x hx q q' hq hq'
  have : Nonempty X := ⟨q⟩
  let sel : BlockSpace (fun _ : CGPTag L Z => ℝ²) → X := fun y =>
    if y = x then q else Classical.epsilon (fun p => cgpProjMap L Z (gafStageTags L Z st) p = y)
  have hsel : ∀ y ∈ gafCloudEnlarged L Z st, cgpProjMap L Z (gafStageTags L Z st) (sel y) = y := by
    intro y hy
    by_cases hyx : y = x
    · simp only [sel, hyx, ↓reduceIte]
      exact hq
    · simp only [sel, hyx, ↓reduceIte]
      obtain ⟨p, -, hp⟩ := hy
      exact Classical.epsilon_spec (p := fun p => cgpProjMap L Z (gafStageTags L Z st) p = y)
        ⟨p, hp⟩
  have hselx : sel x = q := by simp only [sel, ↓reduceIte]
  have h := gafCloudEnlarged_preimage_ratio_BAS L Z hΔ hΛ hsmall st sel hsel x hx q'
    (by rw [gafStageQ_starProjection_globalMap]; exact hq')
  rw [hselx] at h
  have hq0 := hρ q
  have hq'0 := hρ q'
  constructor <;> nlinarith [h.1, h.2]

/-- **CFS26** (`lem:fibration-actual-support-scale`) on the actual packets. With `Δ ≥ 1`, `Λ ≥ 0`
and the row's choice `ΛD_* ≤ 1/4` (`D_* = 10⁶Δ`), for every retained marker `a` (`R_a = ρ(c_a)`):
(AS) on the whole closed domain `B̄(c_a, D_aR_a)`, which contains the closed support of the actual
cutoff; (AS) at every preimage with a positive marker of `𝓔⁰`; every original core point and every
point of every enlarged stage cloud carries a retained full constant marker; ANY two preimages of a
point of `S̃_st` have scale ratio in `[3/5, 5/3]`; FC26's radius control on the retained cloud for
every pair of preimages; CFS07's (MC) on every enlarged stage cloud for every selection of
preimages; and the exact first-stage identity `|ρ p − ρ q| ≤ |𝓔⁰p − 𝓔⁰q|`. -/
theorem cfs26_row_CFSB
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ) (hsmall : Λ * (1000000 * Δ) ≤ 1 / 4) (hσs : 0 ≤ σs)
    (hσs1 : σs ≤ 1 / 100) :
    (∀ a : CGPMarkerIndex P.toLocalChartFamily,
      ∀ q ∈ closedBall (cgpMarkerCentre P.toLocalChartFamily a)
        (cgpMarkerDomain P.toLocalChartFamily a * ρ (cgpMarkerCentre P.toLocalChartFamily a)),
      3 * ρ (cgpMarkerCentre P.toLocalChartFamily a) / 4 ≤ ρ q ∧
        ρ q ≤ 5 * ρ (cgpMarkerCentre P.toLocalChartFamily a) / 4) ∧
    (∀ a : CGPMarkerIndex P.toLocalChartFamily,
      tsupport (cgpMarkerCutoff P.toLocalChartFamily a) ⊆
        closedBall (cgpMarkerCentre P.toLocalChartFamily a)
          (cgpMarkerDomain P.toLocalChartFamily a * ρ (cgpMarkerCentre P.toLocalChartFamily a))) ∧
    (∀ a p, 0 < cgpMarker P.toLocalChartFamily P.zero a
        (cgpGlobalMap P.toLocalChartFamily P.zero p) →
      3 * ρ (cgpMarkerCentre P.toLocalChartFamily a) / 4 ≤ ρ p ∧
        ρ p ≤ 5 * ρ (cgpMarkerCentre P.toLocalChartFamily a) / 4) ∧
    (∀ p ∈ cgpRetainedCloud P.toLocalChartFamily, ∃ a,
      cgpMarker P.toLocalChartFamily P.zero a (cgpGlobalMap P.toLocalChartFamily P.zero p) =
        ρ (cgpMarkerCentre P.toLocalChartFamily a)) ∧
    (∀ st, ∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero st,
      ∃ a : CGPMarkerIndex P.toLocalChartFamily,
        blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero a) x =
          ρ (cgpMarkerCentre P.toLocalChartFamily a)) ∧
    (∀ st, ∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero st, ∀ q q' : X,
      cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero st) q = x →
      cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero st) q' =
        x →
      3 / 5 * ρ q ≤ ρ q' ∧ ρ q' ≤ 5 / 3 * ρ q) ∧
    (∀ sg : ℝ, 0 ≤ sg → sg ≤ 1 / 2 → ∀ p ∈ cgpRetainedCloud P.toLocalChartFamily,
      ∀ q ∈ cgpRetainedCloud P.toLocalChartFamily,
      |sg * ρ q - sg * ρ p| ≤ 2 * (dist (cgpGlobalMap P.toLocalChartFamily P.zero p)
        (cgpGlobalMap P.toLocalChartFamily P.zero q) + sg * ρ p)) ∧
    (∀ (st : Fin 3) (sel : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X),
      (∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero st,
        cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero st)
          (sel x) = x) →
      ∀ sg L' : ℝ, 0 ≤ sg → 0 ≤ L' → L' * sg ≤ 1 / 5 →
      ∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero st,
      ∀ y ∈ gafCloudEnlarged P.toLocalChartFamily P.zero st,
        dist y x ≤ L' * max (sg * ρ (sel y)) (sg * ρ (sel x)) →
        sg * ρ (sel x) / (5 / 3) ≤ sg * ρ (sel y) ∧ sg * ρ (sel y) ≤ (5 / 3) * (sg * ρ (sel x)))
      ∧
    ∀ p q : X, |ρ p - ρ q| ≤ dist (cgpGlobalMap P.toLocalChartFamily P.zero p)
      (cgpGlobalMap P.toLocalChartFamily P.zero q) := by
  have hΔ0 : 0 < Δ := by linarith
  obtain ⟨hAS, hfull, hrad⟩ := fc26_row P.toLocalChartFamily P.zero hΔ hσs hσs1 hΛ hsmall
  have h07 := cfs07_row P.toLocalChartFamily P.zero hΔ hσs hσs1 hΛ hsmall (L' := 0) (sg := 0)
    le_rfl le_rfl (by norm_num)
  refine ⟨fun a => cgpMarker_domain_scale_CFSB P.toLocalChartFamily hΔ hΛ hsmall a,
    fun a => tsupport_cgpMarkerCutoff_subset_CFSB P.toLocalChartFamily hΔ0 a, hAS, hfull,
    fun st => ?_, fun st => gafCloudEnlarged_two_preimages_CFSB P.toLocalChartFamily P.zero hΔ hΛ
      hsmall st, hrad,
    fun st sel hsel sg L' hsg hL' hLsg => gafCloud_mcb_GAF2 P.toLocalChartFamily P.zero hΔ hΛ hsmall
      st sel hsel hsg hL' hLsg, h07.2.2.1⟩
  fin_cases st
  · exact gafCloudEnlarged_fullMarker_zero_GAF5 P
  · exact gafCloudEnlarged_fullMarker_one_GAF5 P.toLocalChartFamily P.zero hΔ hΛ hsmall
  · exact gafCloudEnlarged_fullMarker_two_GAF5 P.toLocalChartFamily P.zero hΔ hΛ hsmall

end DifferentialGeometry.Geometry.Collapse
