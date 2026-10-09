import DifferentialGeometry.Geometry.Fibration.ActualStageCloudBudget
import DifferentialGeometry.Geometry.Fibration.ActualStageCloudTests

/-!
# `N_b` and `c_w` on the planes of FC27's accepted stage tests

Consumer of `nb_cw_stage_cloud_GAFS3` and `fc27_row_GAF2` (which assembles the accepted (CS) stage
tests `fc27_first_test_GAF4`, `fc27_edge_test_GAF3`, `fc27_slim_test_C14_GAF3`):

* `stage_buffer_radius_GAFS3`: (DS) `Γ ≤ d_b` and GAF01's range `Σ < Γ/200` give CFS15's (MO)
  `128bΣ ≤ 1/5`.
* `fc27_row_nb_cw_GAFS3`: FC27's frozen row with, for buffers `b_st ≥ 1` with `Γ_st ≤ d_{b_st}`,
  constants `c_w st ≥ 0` chosen before the thresholds, and on the planes FC27 produces, at every
  stage: the (CS) tests, CFS11's selection on `S_st`, `|J| ≤ N_b` and (LM) for every finite
  disjoint selection, and the weight derivative budget `Σ_i ‖Dw_i‖ ≤ c_w st / r_x`.
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

/-- (DS) `Γ ≤ d_b` and `Σ < Γ/200` give `128bΣ ≤ 1/5`. -/
theorem stage_buffer_radius_GAFS3 {bb Γ sg : ℝ} (hbb : 1 ≤ bb) (hΓ : 0 < Γ)
    (hsgΓ : sg < Γ / 200)
    (hds : Γ ≤ min (1 / (8 * (5 / 3)))
      (min (1 / (4 * (128 * bb * (5 / 3) + 3))) (1 / (8 * (5 / 3 + 1))))) :
    128 * bb * sg ≤ 1 / 5 := by
  have h0 : Γ ≤ 1 / (4 * (128 * bb * (5 / 3) + 3)) :=
    hds.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hpos : 0 < 4 * (128 * bb * (5 / 3) + 3) := by linarith
  have h1 : Γ * (4 * (128 * bb * (5 / 3) + 3)) ≤ 1 := (le_div_iff₀ hpos).mp h0
  have h2 : bb * sg ≤ bb * (Γ / 200) := mul_le_mul_of_nonneg_left hsgΓ.le (by linarith)
  nlinarith

/-- The model metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricNC14SBA_GAFS3 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsC14`, as a named local instance. -/
local instance instChartedNC14SBA_GAFS3 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricCC14SBA_GAFS3 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **FC27 on the actual clouds with `N_b` and `c_w`.** `fc27_row_GAF2`'s hypotheses, and buffers
`b_st ≥ 1` with (DS) `Γ_st ≤ d_{b_st}`: there are `c_w st ≥ 0` (before the thresholds) and FC27's
thresholds such that on every actual `LocalChartPacketsC14` with FC27's hypotheses and every
selection of preimages over the enlarged stage clouds there are planes with, at every stage: the
dimension, `plane ≤ Q_st` and the (CS) test (FC27), CFS11's selection on `S_st`, for every finite
disjoint selection `I ⊆ S_st` `|J| ≤ N_b = ⌈(1 + 2·(5/3)·165·b_st)^{k_st}⌉` and (LM), and under the
tube inclusion `Σ_i ‖Dw_i‖ ≤ c_w st / r_x` (`r = Σ_st ρ(sel st ·)`). -/
theorem fc27_row_nb_cw_GAFS3 {Δ β₂ ν : ℝ} (hΔ : 1200 ≤ Δ) (hβ₂ : 0 < β₂)
    (hβ₂1 : β₂ < 1 / 1000000) (hν : 0 < ν) (hν1 : ν < 1) (Γ sg eg : Fin 3 → ℝ)
    (hΓ : ∀ st, 0 < Γ st ∧ Γ st < 1)
    (hsg : ∀ st, 0 < sg st ∧ sg st < min (Γ st / 200) (Γ st ^ 3 / (100 * gafGraphConst st)))
    (heg : ∀ st, 0 < eg st ∧
      eg st < min (1 / 100) (min (Γ st * sg st / 100) (sg st / 1000)))
    (bb : Fin 3 → ℝ) (hbb : ∀ st, 1 ≤ bb st)
    (hΓb : ∀ st, Γ st ≤ min (1 / (8 * (5 / 3)))
      (min (1 / (4 * (128 * bb st * (5 / 3) + 3))) (1 / (8 * (5 / 3 + 1))))) :
    ∃ cw : Fin 3 → ℝ, (∀ st, 0 ≤ cw st) ∧
    ∃ σ η₂ γ₀ ηc θ η₁ θs Lc η₀ Lc' η₀' : ℝ,
      (0 < σ ∧ σ ≤ 1 / 1000 ∧ 0 < η₂ ∧ 0 < γ₀ ∧ 0 < ηc ∧ 0 < θ ∧ θ < 1 ∧ 0 < η₁ ∧
        0 < θs ∧ θs < 1 ∧ 0 < Lc ∧ 0 < η₀ ∧ 0 < Lc' ∧ 0 < η₀') ∧
      ∀ (X : Type) [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
        [CompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
        (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
        (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (σs : ℝ) (K : ℕ)
        (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ)
        (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
          εr e T V vs ζ Λz),
        -- TCP06
        0 ≤ Λ → μ ≤ 1 / 100 → τ ≤ 1 / 100 → 1000000 * Δ * Λ < 1 / 100000 →
        4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax → e < 1 / 40 → 1600 * (1000000 * Δ) ≤ T →
        0 ≤ ε → ε ≤ 1 → 0 ≤ σc → σc ≤ θ ^ 2 / 1000 → μ * Δ ≤ θ / 100 →
        3 * ν ≤ β 3 → β 3 < 1 → 3 * β 2 ≤ σ → β 2 ≤ η₂ → γ ≤ γ₀ → 0 < γc → γc ≤ γ₀ →
        βc ≤ ηc → b ≤ η₁ → β 1 ≤ η₁ → 0 < σs → σs ≤ θ ^ 2 / 1000 → vs ≤ θ / 100 → 0 < ζ →
        ζ ≤ θ ^ 2 / 1000 → εr ≤ θ / 100 → 20 * Λz ≤ T → σ⁻¹ ≤ Lmax →
        1000 * tcpGraphConst * Δ * Λ < eg 0 →
        -- SGP06
        β 2 = β₂ → β 1 ≤ η₀ → Lc ≤ Lmax → σs < θs ^ 2 / 10 ^ 6 → vs < θs / 100 →
        ζ < θs ^ 2 / 10 ^ 6 → ζ < 1 / (100 * (1000000 * Δ)) →
        εr < θs / (100 * (1000000 * Δ)) →
        -- EGP07
        b ≤ η₀' → s < 1 / 1000000 → β 1 ≤ η₀' → Lc' ≤ Lmax →
        σc ≤ (eg 1 / (20 * egpGraphConst)) ^ 2 / 10 ^ 8 →
        μ * Δ < eg 1 / (20 * egpGraphConst) / 100 →
        σs ≤ (eg 1 / (20 * egpGraphConst)) ^ 2 / 10 ^ 8 →
        vs < eg 1 / (20 * egpGraphConst) / 100 →
        ζ ≤ (eg 1 / (20 * egpGraphConst)) ^ 2 / 10 ^ 8 → ζ ≤ 1 / (1000 * (1000000 * Δ)) →
        εr < eg 1 / (20 * egpGraphConst) / (100 * (1000000 * Δ)) →
        ∀ sel : Fin 3 → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X,
        (∀ st, ∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero st,
          cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero st)
            (sel st x) = x) →
        ∃ plane : Fin 3 → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
            Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
          ∀ st,
          (∀ x ∈ gafCloud P.toLocalChartFamily P.zero st,
            Module.finrank ℝ (plane st x) = gafStageDim st ∧
            plane st x ≤ gafStageQ P.toLocalChartFamily P.zero st ∧
            hausdorffEDist (gafCloudEnlarged P.toLocalChartFamily P.zero st ∩
                ball x (sg st * ρ (sel st x) / Γ st))
              ((AffineSubspace.mk' x (plane st x) :
                  Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) ∩
                ball x (sg st * ρ (sel st x) / Γ st)) ≤
              ENNReal.ofReal (Γ st * (sg st * ρ (sel st x)))) ∧
          (∃ T' : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
            T' ⊆ gafCloud P.toLocalChartFamily P.zero st ∧ T'.Finite ∧
            T'.PairwiseDisjoint (fun i => ball i (sg st * ρ (sel st i))) ∧
            (∀ x ∈ gafCloud P.toLocalChartFamily P.zero st, ∃ i ∈ T',
              dist x i < 3 * (sg st * ρ (sel st i)) ∧
                sg st * ρ (sel st x) ≤ 2 * (sg st * ρ (sel st i))) ∧
            (⋃ x ∈ gafCloud P.toLocalChartFamily P.zero st,
                ball x (8 * bb st * (sg st * ρ (sel st x)))) ⊆
              ⋃ i ∈ T', ball i (20 * bb st * (sg st * ρ (sel st i))) ∧
            (⋃ i ∈ T', ball i (20 * bb st * (sg st * ρ (sel st i)))) ⊆
              ⋃ i ∈ T', ball i (30 * bb st * (sg st * ρ (sel st i)))) ∧
          ∀ (I : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)))
            (hI : I.Finite), I ⊆ gafCloud P.toLocalChartFamily P.zero st →
            I.PairwiseDisjoint (fun i => ball i (sg st * ρ (sel st i))) →
            (∀ x ∈ gafCloud P.toLocalChartFamily P.zero st,
              ((I ∩ {i | (closedBall i (80 * bb st * (sg st * ρ (sel st i))) ∩
                  ball x (30 * bb st * (sg st * ρ (sel st x)))).Nonempty}).ncard : ℝ) ≤
                (⌈(1 + 2 * (5 / 3) * 165 * bb st) ^ gafStageDim st⌉₊ : ℝ) ∧
              ∀ i ∈ I, (closedBall i (80 * bb st * (sg st * ρ (sel st i))) ∩
                  ball x (30 * bb st * (sg st * ρ (sel st x)))).Nonempty →
                sg st * ρ (sel st x) / (5 / 3) ≤ sg st * ρ (sel st i) ∧
                sg st * ρ (sel st i) ≤ (5 / 3) * (sg st * ρ (sel st x)) ∧
                dist i x < 165 * bb st * (sg st * ρ (sel st x))) ∧
            ((⋃ x ∈ gafCloud P.toLocalChartFamily P.zero st,
                ball x (8 * bb st * (sg st * ρ (sel st x)))) ⊆
              ⋃ i ∈ I, ball i (20 * bb st * (sg st * ρ (sel st i))) →
              ∀ x ∈ gafCloud P.toLocalChartFamily P.zero st,
              ∀ y ∈ ball x (8 * bb st * (sg st * ρ (sel st x))),
                (∑ i ∈ hI.toFinset, ‖fderiv ℝ (fun y' =>
                    ballCutoff i (40 * bb st * (sg st * ρ (sel st i)))
                      (2 * (40 * bb st * (sg st * ρ (sel st i)))) y' / (∑ a ∈ hI.toFinset,
                      ballCutoff a (40 * bb st * (sg st * ρ (sel st a)))
                        (2 * (40 * bb st * (sg st * ρ (sel st a)))) y')) y‖) ≤
                  cw st / (sg st * ρ (sel st x))) := by
  obtain ⟨cwf, hcwf⟩ := nb_cw_stage_cloud_GAFS3
  obtain ⟨σ, η₂, γ₀, ηc, θ, η₁, θs, Lc, η₀, Lc', η₀', hpos, hrow⟩ :=
    fc27_row_GAF2 hΔ hβ₂ hβ₂1 hν hν1 Γ sg eg hΓ hsg heg
  refine ⟨fun st => cwf st (bb st), fun st => (hcwf st (bb st) (hbb st)).1,
    σ, η₂, γ₀, ηc, θ, η₁, θs, Lc, η₀, Lc', η₀', hpos, ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz P
    t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25
    t26 t27 t28 t29 t30 t31 s1 s2 s3 s4 s5 s6 s7 s8 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 sel hsel
  obtain ⟨plane, hplane⟩ := hrow X g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
    T V vs ζ Λz P t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22
    t23 t24 t25 t26 t27 t28 t29 t30 t31 s1 s2 s3 s4 s5 s6 s7 s8 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11
    sel hsel
  refine ⟨plane, fun st => ⟨hplane st, ?_⟩⟩
  have hsgb : 128 * bb st * sg st ≤ 1 / 5 :=
    stage_buffer_radius_GAFS3 (hbb st) (hΓ st).1 (lt_of_lt_of_le (hsg st).2 (min_le_left _ _))
      (hΓb st)
  exact (hcwf st (bb st) (hbb st)).2 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ
    δ εr e T V vs ζ Λz P t1 (by linarith) t2 t3 (by linarith) t4 (sel st) (hsel st) (sg st)
    (hsg st).1 hsgb (Γ st) (hΓ st).1 (hΓb st) (plane st) (fun x hx => (hplane st x hx).1)
    (fun x hx => (hplane st x hx).2.2)

end DifferentialGeometry.Geometry.Collapse
