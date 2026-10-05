import DifferentialGeometry.Geometry.Collapse.BoundaryEarlyThresholdsBSTD1
import DifferentialGeometry.Geometry.Collapse.BoundaryStagedRequestsBSTG

/-!
# Staged inhabitants of the boundary early choices (lane BSTG-D1, D61-11 D1 consumer)

The early choices `BoundaryEarlyChoices_BSTD1 K hK A hA` over the exported boundary thresholds are
inhabited by the staged adapter of lane BSTG, now run on the EXPORTED threshold chain instead of an
existential producer: for every early tolerance record `t`, every early boundary layer
(`ϑ`, `c₃`, `P_*`, `N ≥ N_TCP + 1`, fixed first, so requests may read it) and every interior request
record `Rq` (each request read at its STG prefix; `β₂`'s before `βc`), ONE admissible staged prefix
`P` meets `Rq` with `3βc ≤ β 2`, and its producer outputs ARE the exported thresholds at its
parameters, so `P` is an early choice (`w < ω₃/4`, `vs < ϑ₃/4` from lane BSTG's caps).

* `BoundaryProducerThresholds_BSTD1.chain_BSTD1`: the exported thresholds as a producer chain in
  the shape of the STG stage lemmas, each output equal to its threshold function.
* `C14PreFinal.toBdryParams_BSTD1`: the parameters of a staged prefix.
* `exists_boundaryEarlyChoices_staged_BSTD1`: the staged inhabitant.
* consumer `exists_bdry_staged_early_continuation_BSTD1`: the staged boundary assignment through the
  export — the inhabitant AND, for every standing sequence with `δ₀ ≤ δStar`, the producer's
  continuation at exactly its parameters (lane BSTG G1's statement with `early` an input).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Analysis.Calculus
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Riemannian.Geodesic

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

/-- **The exported thresholds as a producer chain** in the binder shape of the boundary producer
(and of the STG stage lemmas): every output exists, has the producer's facts, and EQUALS the
exported threshold at the parameters before it. -/
theorem BoundaryProducerThresholds_BSTD1.chain_BSTD1 (Θ : BoundaryProducerThresholds_BSTD1) :
    ∀ γ : ℝ, 0 < γ → γ < 1 / 10 → ∃ β₀ : ℝ, 0 < β₀ ∧ β₀ ≤ Θ.a₂ ∧ (β₀ = Θ.B0 γ ∧
    ∀ βc γc : ℝ, 0 < βc → βc < γc / 1000 → 0 < γc → γc < 1 / 100 →
    ∃ σ₀ : ℝ, 0 < σ₀ ∧ ∃ Δ₀ : ℝ, 0 < Δ₀ ∧ (σ₀ = Θ.S0 ⟨γ, βc, γc⟩ ∧ Δ₀ = Θ.D0 ⟨γ, βc, γc⟩ ∧
    ∀ β₂ Δ : ℝ, 0 < β₂ → β₂ ≤ β₀ → β₂ < 1 / 100 → 100 / β₂ < Δ → Δ₀ ≤ Δ →
    ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∃ bc₀ : ℝ, 0 < bc₀ ∧ (τ₀ = Θ.T0 ⟨⟨γ, βc, γc⟩, β₂, Δ⟩ ∧
      bc₀ = Θ.BC ⟨⟨γ, βc, γc⟩, β₂, Δ⟩ ∧
    ∀ σc ε μ τ : ℝ, 0 < σc → σc ≤ σ₀ → σc < 1 → 0 < ε → ε < 1 / 100 → 0 < μ →
      μ ≤ 1 / 1000000 → 0 < τ → τ ≤ τ₀ → 140 * Real.sqrt τ < ε ^ 2 / 20 → ε ≤ 1 / 10 ^ 8 →
      μ ≤ 1 / 10 ^ 8 →
    ∀ s b' s' : ℝ, 0 < s → s < 1 / 100 → s < b' / 100000 → s < s' / 100000 →
      b' < 1 / (1000000 * Δ) → s' < 1 / (1000000 * Δ) →
      b' < τ * Δ / 1000000000 → s' < τ * Δ / 1000000000 → ∃ a₀ b₁ : ℝ, 0 < a₀ ∧ 0 < b₁ ∧
    ∀ σ : ℝ, 0 < σ → σ ≤ Θ.a₂ → σ ≤ threeSplittingExclusionThreshold.{0, 0} → σ ≤ a₀ →
      (a₀ = Θ.A0 ⟨⟨⟨γ, βc, γc⟩, β₂, Δ⟩, σc, ε, μ, τ, s, b', s'⟩ ∧
      b₁ = Θ.B1 ⟨⟨⟨γ, βc, γc⟩, β₂, Δ⟩, σc, ε, μ, τ, s, b', s'⟩ ∧
    ∀ Λ : ℝ, 0 < Λ → Δ * Λ * 2000000 ≤ 1 / 100 → Λ < 1 / (1000000 * Δ) →
      100 * Δ * Λ ≤ 1 / 1000000 →
      2 * ε + 300 * Δ * Λ + Real.sqrt (504000 / Δ + 3780 * τ) < γc / 1000 →
      Λ < s' / (100000000 * Δ ^ 2) → 100 * Δ * Λ ≤ 1 / 10 ^ 8 →
    ∃ w₀ : ℝ, 0 < w₀ ∧ (w₀ = Θ.W0 ⟨⟨⟨⟨γ, βc, γc⟩, β₂, Δ⟩, σc, ε, μ, τ, s, b', s'⟩, σ, Λ⟩ ∧
    ∀ w : ℝ, 0 < w → w < w₀ → w < 4 * Real.pi / 3 → ∃ bd₀ : ℝ, 0 < bd₀ ∧
      (bd₀ = Θ.BD ⟨⟨⟨⟨⟨γ, βc, γc⟩, β₂, Δ⟩, σc, ε, μ, τ, s, b', s'⟩, σ, Λ⟩, w⟩ ∧
    ∀ b : ℝ, 0 < b → b < s / 100000 → b < bc₀ → b < b₁ → 100 * Δ < b⁻¹ → b < bd₀ →
    ∀ σs vs : ℝ, 0 < σs → σs ≤ 1 / 100 → 0 < vs → ∃ b₀ : ℝ, 0 < b₀ ∧
      (b₀ = Θ.BZ ⟨⟨⟨⟨⟨⟨γ, βc, γc⟩, β₂, Δ⟩, σc, ε, μ, τ, s, b', s'⟩, σ, Λ⟩, w⟩, b, σs, vs⟩ ∧
    ∀ β : ℕ → ℝ, β 2 = β₂ → 0 < β 1 → β 1 < b₀ → β 1 < 1 →
      β 3 ≤ threeSplittingExclusionThreshold.{0, 0} →
    ∀ ζ cap : ℝ, β 1 < ζ → ζ < 1 → 0 < cap →
    ∃ εr δ' Λ' : ℝ, 0 < εr ∧ εr < 1 / 4 ∧ εr < cap ∧ 0 < δ' ∧ 0 < Λ' ∧
      (εr = Θ.ER ⟨⟨⟨⟨⟨⟨⟨γ, βc, γc⟩, β₂, Δ⟩, σc, ε, μ, τ, s, b', s'⟩, σ, Λ⟩, w⟩, b, σs, vs⟩, β, ζ,
        cap⟩ ∧
      δ' = Θ.DP ⟨⟨⟨⟨⟨⟨⟨γ, βc, γc⟩, β₂, Δ⟩, σc, ε, μ, τ, s, b', s'⟩, σ, Λ⟩, w⟩, b, σs, vs⟩, β, ζ,
        cap⟩ ∧
      Λ' = Θ.LZ ⟨⟨⟨⟨⟨⟨⟨γ, βc, γc⟩, β₂, Δ⟩, σc, ε, μ, τ, s, b', s'⟩, σ, Λ⟩, w⟩, b, σs, vs⟩, β, ζ,
        cap⟩)))))))) := by
  intro γ _ _
  refine ⟨Θ.B0 γ, Θ.B0_pos γ, Θ.B0_le γ, rfl, fun βc γc _ _ _ _ => ?_⟩
  refine ⟨Θ.S0 ⟨γ, βc, γc⟩, Θ.S0_pos _, Θ.D0 ⟨γ, βc, γc⟩, Θ.D0_pos _, rfl, rfl,
    fun β₂ Δ _ _ _ _ _ => ?_⟩
  refine ⟨Θ.T0 ⟨⟨γ, βc, γc⟩, β₂, Δ⟩, Θ.T0_pos _, Θ.BC ⟨⟨γ, βc, γc⟩, β₂, Δ⟩, Θ.BC_pos _, rfl, rfl,
    fun σc ε μ τ _ _ _ _ _ _ _ _ _ _ _ _ s b' s' _ _ _ _ _ _ _ _ => ?_⟩
  refine ⟨Θ.A0 ⟨⟨⟨γ, βc, γc⟩, β₂, Δ⟩, σc, ε, μ, τ, s, b', s'⟩,
    Θ.B1 ⟨⟨⟨γ, βc, γc⟩, β₂, Δ⟩, σc, ε, μ, τ, s, b', s'⟩, Θ.A0_pos _, Θ.B1_pos _,
    fun σ _ _ _ _ => ⟨rfl, rfl, fun Λ _ _ _ _ _ _ _ => ?_⟩⟩
  refine ⟨Θ.W0 ⟨⟨⟨⟨γ, βc, γc⟩, β₂, Δ⟩, σc, ε, μ, τ, s, b', s'⟩, σ, Λ⟩, Θ.W0_pos _, rfl,
    fun w _ _ _ => ?_⟩
  refine ⟨Θ.BD ⟨⟨⟨⟨⟨γ, βc, γc⟩, β₂, Δ⟩, σc, ε, μ, τ, s, b', s'⟩, σ, Λ⟩, w⟩, Θ.BD_pos _, rfl,
    fun b _ _ _ _ _ _ σs vs _ _ _ => ?_⟩
  refine ⟨Θ.BZ ⟨⟨⟨⟨⟨⟨γ, βc, γc⟩, β₂, Δ⟩, σc, ε, μ, τ, s, b', s'⟩, σ, Λ⟩, w⟩, b, σs, vs⟩,
    Θ.BZ_pos _, rfl, fun β _ _ _ _ _ ζ cap _ _ hcap => ?_⟩
  exact ⟨_, _, _, Θ.ER_pos _, Θ.ER_lt _, Θ.ER_lt_cap ⟨⟨⟨⟨⟨⟨⟨γ, βc, γc⟩, β₂, Δ⟩, σc, ε, μ, τ, s,
    b', s'⟩, σ, Λ⟩, w⟩, b, σs, vs⟩, β, ζ, cap⟩ hcap, Θ.DP_pos _, Θ.LZ_pos _, rfl, rfl, rfl⟩

/-- **Stage 11 with a `cap`-dependent continuation** (the STG zero stage `c14_stage_zero_FAM2b`,
whose continuation `Q` may also read `cap`). -/
theorem c14_stage_zero_dep_BSTD1 (p : C14PreBeta) {r : ℝ} (hr : 0 < r)
    {Q : ℝ → ℝ → ℝ → ℝ → Prop}
    (h : ∀ cap : ℝ, 0 < cap → ∃ εr δ' Λ' : ℝ, 0 < εr ∧ εr < 1 / 4 ∧ εr < cap ∧ 0 < δ' ∧
      0 < Λ' ∧ Q cap εr δ' Λ') :
    ∃ q : C14PreZero, q.toC14PreBeta = p ∧ q.cap ≤ r ∧ Q q.cap q.εr q.δ' q.Λz := by
  have hcap : 0 < min r (1 / 100) := by positivity
  obtain ⟨εr, δ', Λz, hεr, hεr4, hεrcap, hδ', hΛz, hQ⟩ := h _ hcap
  exact ⟨{
    toC14PreBeta := p
    cap := min r (1 / 100)
    εr := εr
    δ' := δ'
    Λz := Λz
    cap_pos := hcap
    cap_le := min_le_right _ _
    εr_pos := hεr
    εr_lt := hεr4
    εr_lt_cap := hεrcap
    δ'_pos := hδ'
    Λz_pos := hΛz }, rfl, min_le_left _ _, hQ⟩

/-- The producer parameters of a staged prefix. -/
def C14PreFinal.toBdryParams_BSTD1 (P : C14PreFinal) : BoundaryEarlyParams_BSTD1 :=
  ⟨⟨⟨⟨⟨⟨⟨⟨P.γ, P.βc, P.γc⟩, P.β₂, P.Δ⟩, P.σc, P.ε, P.μ, P.τ, P.s, P.b', P.s'⟩, P.σ, P.Λ⟩, P.w⟩,
    P.b, P.σs, P.vs⟩, P.β, P.ζ, P.cap⟩, P.T, P.e⟩

/-- **Staged inhabitants of the boundary early choices** (D61-11 D1): for every early tolerance
record `t`, every early boundary layer (`ϑ`, `c₃ ≥ 0`, `P_* ≥ 1`, `N ≥ N_TCP + 1`) and every
interior request record `Rq`, there is an early choice with exactly this layer whose parameters are
those of ONE admissible staged prefix `P` meeting `Rq` (each request at its STG prefix) with
`3βc ≤ β 2`. -/
theorem exists_boundaryEarlyChoices_staged_BSTD1 (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) (t : C14Tol)
    (ϑ : Fin 3 → ℝ) (hϑ : ∀ j, 0 < ϑ j) (c₃ : ℝ) (hc₃ : 0 ≤ c₃) (Pstar : ℝ) (hP : 1 ≤ Pstar)
    (N : ℕ) (hN : tcp01SupportBound + 1 ≤ N) (Rq : C14StagedRequestsSTG) :
    ∃ E : BoundaryEarlyChoices_BSTD1 K hK A hA, E.ϑ = ϑ ∧ E.c₃ = c₃ ∧ E.Pstar = Pstar ∧ E.N = N ∧
      ∃ P : C14PreFinal, P.toC14Tol = t ∧ Rq.toC14.Meets P ∧ 3 * P.βc ≤ P.β 2 ∧
        E.toBoundaryEarlyParams_BSTD1 = P.toBdryParams_BSTD1 := by
  obtain ⟨a₂, ha₂e⟩ : ∃ a₂ : ℝ, (bdryThresholds_BSTD1 K hK A hA).a₂ = a₂ := ⟨_, rfl⟩
  have ha₂ : 0 < a₂ := ha₂e ▸ (bdryThresholds_BSTD1 K hK A hA).a₂_pos
  have h0 := (bdryThresholds_BSTD1 K hK A hA).chain_BSTD1
  rw [ha₂e] at h0
  obtain ⟨p1, rfl, rfl, h1γ, e1, h⟩ :=
    c14_stage_circ_FAM2b t ha₂ ((Rq.withBdryCaps_BSTG (ϑ 2) (hϑ 2)).γ_pos t) h0
  obtain ⟨p2, rfl, h2βc, h2γc, e2σ, e2Δ, h⟩ := c14_stage_collar_STG p1
    (fun g => min ((Rq.withBdryCaps_BSTG (ϑ 2) (hϑ 2)).βc g.toC14PreCirc)
      (c14β₂Value_STG (Rq.withBdryCaps_BSTG (ϑ 2) (hϑ 2)) g / 3))
    (fun g => lt_min ((Rq.withBdryCaps_BSTG (ϑ 2) (hϑ 2)).βc_pos _)
      (div_pos (c14β₂Value_pos_STG _ g) zero_lt_three))
    ((Rq.withBdryCaps_BSTG (ϑ 2) (hϑ 2)).γc_pos p1) h
  have h2 : p2.βc ≤ min p2.β₀ (min ((Rq.withBdryCaps_BSTG (ϑ 2) (hϑ 2)).β₂ p2.toGc_STG)
      (min (1 / 10000000) (p2.γT / 20))) / 3 :=
    h2βc.trans (min_le_right _ _)
  obtain ⟨p3, rfl, h3β₂, h3v, h⟩ :=
    c14_stage_excl_STG p2 ((Rq.withBdryCaps_BSTG (ϑ 2) (hϑ 2)).β₂_pos p2.toGc_STG) h
  have h3βc : 3 * p3.βc ≤ p3.β₂ := by
    rw [h3v]
    linarith
  obtain ⟨p4, rfl, h4Δ, e4τ, e4bc, h⟩ :=
    c14_stage_scale_FAM2b p3 ((Rq.withBdryCaps_BSTG (ϑ 2) (hϑ 2)).Δ p3) h
  obtain ⟨p5, rfl, h5σc, h5ε, h5μ, h5τ, h5s, h5b', h5s', e5a, e5b, h⟩ := c14_stage_edge_FAM2b p4
    ((Rq.withBdryCaps_BSTG (ϑ 2) (hϑ 2)).σc_pos p4) ((Rq.withBdryCaps_BSTG (ϑ 2) (hϑ 2)).ε_pos p4)
    ((Rq.withBdryCaps_BSTG (ϑ 2) (hϑ 2)).μ_pos p4) ((Rq.withBdryCaps_BSTG (ϑ 2) (hϑ 2)).τ_pos p4)
    ((Rq.withBdryCaps_BSTG (ϑ 2) (hϑ 2)).s_pos p4) ((Rq.withBdryCaps_BSTG (ϑ 2) (hϑ 2)).b'_pos p4)
    ((Rq.withBdryCaps_BSTG (ϑ 2) (hϑ 2)).s'_pos p4) h
  obtain ⟨p6, rfl, h6Λ, e6w, h⟩ :=
    c14_stage_lip_FAM2b p5 ((Rq.withBdryCaps_BSTG (ϑ 2) (hϑ 2)).Λ_pos p5) h
  obtain ⟨p7, rfl, h7w, e7bd, h⟩ :=
    c14_stage_vol_FAM2b p6 ((Rq.withBdryCaps_BSTG (ϑ 2) (hϑ 2)).w_pos p6) h
  obtain ⟨p8, rfl, h8b, h⟩ :=
    c14_stage_split_FAM2b p7 ((Rq.withBdryCaps_BSTG (ϑ 2) (hϑ 2)).b_pos p7) h
  obtain ⟨p9, rfl, h9σs, h9vs, e9b, h⟩ := c14_stage_slim_FAM2b p8
    ((Rq.withBdryCaps_BSTG (ϑ 2) (hϑ 2)).σs_pos p8) ((Rq.withBdryCaps_BSTG (ϑ 2) (hϑ 2)).vs_pos p8)
    h
  obtain ⟨p10, rfl, h10ζ, h10β, h⟩ := c14_stage_beta_FAM2b p9
    ((Rq.withBdryCaps_BSTG (ϑ 2) (hϑ 2)).ζ_pos p9) ((Rq.withBdryCaps_BSTG (ϑ 2) (hϑ 2)).β₁_pos p9)
    h
  obtain ⟨p11, rfl, h11cap, e11r, e11d, e11z⟩ :=
    c14_stage_zero_dep_BSTD1 p10 ((Rq.withBdryCaps_BSTG (ϑ 2) (hϑ 2)).cap_pos p10) h
  obtain ⟨P, rfl, h12T, h12e, -⟩ := c14_stage_final_FAM2b p11
    ((Rq.withBdryCaps_BSTG (ϑ 2) (hϑ 2)).T p11) ((Rq.withBdryCaps_BSTG (ϑ 2) (hϑ 2)).e_pos p11)
    (Q := fun _ _ => True) (fun _ _ _ _ _ _ => trivial)
  have hM : (Rq.withBdryCaps_BSTG (ϑ 2) (hϑ 2)).toC14.Meets P :=
    ⟨h1γ, h2γc, h2βc.trans (min_le_left _ _), h3β₂, h4Δ, h5σc, h5ε, h5μ, h5τ, h5s, h5b', h5s',
      h6Λ, h7w, h8b, h9σs, h9vs, h10ζ, h10β, h11cap, h12T, h12e⟩
  obtain ⟨hMR, hw2, hvs8⟩ := C14StagedRequestsSTG.meets_of_withBdryCaps_BSTG hM
  have hcap := boundaryVolumeCap_pos
  have hϑ2 := hϑ 2
  refine ⟨{ toBoundaryEarlyParams_BSTD1 := P.toBdryParams_BSTD1
            γ_pos := P.γ_pos
            γ_lt := P.γ_lt
            βc_pos := P.βc_pos
            βc_lt := P.βc_lt
            γc_pos := P.γc_pos
            γc_lt := P.γc_lt
            β₂_pos := P.β₂_pos
            β₂_le := P.β₂_le.trans_eq e1
            β₂_lt := P.β₂_lt
            Δ_gt := P.Δ_gt
            Δ_ge := e2Δ.symm.trans_le P.Δ₀_le
            σc_pos := P.σc_pos
            σc_le := P.σc_le.trans_eq e2σ
            σc_lt := P.σc_lt
            ε_pos := P.ε_pos
            ε_lt := P.ε_lt
            μ_pos := P.μ_pos
            μ_le := P.μ_le
            τ_pos := P.τ_pos
            τ_le := P.τ_le.trans_eq e4τ
            τ_sqrt := P.τ_sqrt
            ε_le8 := P.ε_le8
            μ_le8 := P.μ_le8
            s_pos := P.s_pos
            s_lt := P.s_lt
            s_lt_b' := P.s_lt_b'
            s_lt_s' := P.s_lt_s'
            b'_lt := P.b'_lt
            s'_lt := P.s'_lt
            b'_lt_τ := P.b'_lt_τ
            s'_lt_τ := P.s'_lt_τ
            σ_pos := P.σ_pos
            σ_le_a₂ := P.σ_le_a₂.trans_eq ha₂e.symm
            σ_le_thr := P.σ_le_thr
            σ_le_a₀ := P.σ_le_a₀.trans_eq e5a
            Λ_pos := P.Λ_pos
            Λ_c1 := P.Λ_c1
            Λ_c2 := P.Λ_c2
            Λ_c3 := P.Λ_c3
            budget := P.budget
            Λ_c5 := P.Λ_c5
            Λ_c6 := P.Λ_c6
            w_pos := P.w_pos
            w_lt := P.w_lt.trans_eq e6w
            w_lt_pi := P.w_lt_pi
            b_pos := P.b_pos
            b_lt_s := P.b_lt_s
            b_lt_bc₀ := P.b_lt_bc₀.trans_eq e4bc
            b_lt_b₁ := P.b_lt_b₁.trans_eq e5b
            b_inv := P.b_inv
            b_lt_bd₀ := P.b_lt_bd₀.trans_eq e7bd
            σs_pos := P.σs_pos
            σs_le := P.σs_le
            vs_pos := P.vs_pos
            β_two := P.β_two
            β₁_pos := P.β₁_pos
            β₁_lt_b₀ := P.β₁_lt_b₀.trans_eq e9b
            β₁_lt := P.β₁_lt
            β_three := P.β_three.le
            β₁_lt_ζ := P.β₁_lt_ζ
            ζ_lt := P.ζ_lt
            cap_pos := P.cap_pos
            T_pos := P.T_pos
            T_ge := (mul_le_mul_of_nonneg_left e11z.symm.le (by norm_num)).trans P.T_Λz
            e_pos := P.e_pos
            e_lt := P.e_lt
            ϑ := ϑ
            ϑ_pos := hϑ
            c₃ := c₃
            c₃_nonneg := hc₃
            Pstar := Pstar
            one_le_Pstar := hP
            N := N
            N_ge := hN
            w_lt_cap := hw2.trans_lt (half_lt_self hcap)
            vs_lt_ϑ := hvs8.trans_lt (by linarith) }, rfl, rfl, rfl, rfl, P, rfl, hMR,
    by rw [P.β_two]; exact h3βc, rfl⟩

/-- **Consumer: the staged boundary assignment through the export** (lane BSTG G1's statement with
`early` an INPUT, on T3B-BFRZ): for every early tolerance record, early boundary layer and interior
request record there is an early choice, carried by ONE staged prefix meeting the requests, such
that every standing sequence with `δ₀ ≤ δStar` has the producer's continuation at exactly its
parameters (`V ≥ T`, `δ < δ'`, then T3B-BFRZ's per-member conclusion at `δ_{n+1}`, index
`n + 1`). -/
theorem exists_bdry_staged_early_continuation_BSTD1 (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) (t : C14Tol)
    (ϑ : Fin 3 → ℝ) (hϑ : ∀ j, 0 < ϑ j) (c₃ : ℝ) (hc₃ : 0 ≤ c₃) (Pstar : ℝ) (hP : 1 ≤ Pstar)
    (N : ℕ) (hN : tcp01SupportBound + 1 ≤ N) (Rq : C14StagedRequestsSTG) :
    ∃ E : BoundaryEarlyChoices_BSTD1 K hK A hA, E.ϑ = ϑ ∧
      (∃ P : C14PreFinal, P.toC14Tol = t ∧ Rq.toC14.Meets P ∧
        E.toBoundaryEarlyParams_BSTD1 = P.toBdryParams_BSTD1) ∧
      ∀ S : BoundaryStandingSequence_BSTD1 K A (bdryThresholds_BSTD1 K hK A hA).δStar,
      ∃ V : ℝ, E.T ≤ V ∧ ∃ δ : ℝ, 0 < δ ∧ δ < E.δ' ∧ ∀ Lmax : ℝ, 0 < Lmax →
      ∀ βd εN : ℝ, 0 < βd → 0 < εN → ∀ᶠ n in atTop,
        @BoundaryPacketsOutBFRZ_BSTD1 (S.W n) (S.conn n) (S.g n) K A
          (boundaryCounterexampleRatio S.δ₀ (n + 1)) (S.B n) ((n + 1 : ℕ) : ℝ) E.Λ E.w E.β E.Δ
          E.σs E.σc E.μ E.b E.s E.b' E.s' E.ε E.γc E.βc Lmax E.τ E.γ δ E.εr E.e E.T V E.vs E.ζ
          E.Λz βd εN := by
  obtain ⟨E, hϑE, -, -, -, P, hPt, hM, -, hEP⟩ :=
    exists_boundaryEarlyChoices_staged_BSTD1 K hK A hA t ϑ hϑ c₃ hc₃ Pstar hP N hN Rq
  exact ⟨E, hϑE, ⟨P, hPt, hM, hEP⟩, fun S => bdry_early_continuation_BSTD1 E S⟩

end DifferentialGeometry.Geometry.Collapse
