import DifferentialGeometry.Geometry.Collapse.FixtureC2.SphereLoopSgp5Rows
import DifferentialGeometry.Geometry.Collapse.FixtureC2.SphereLoopChainRows

/-!
# The counted slim rows incl. SGP05 on the production chain over the sphere loop packet
(S-FIXTURE-C2d, G8 file 2; acceptance configuration C-S of D75, slim stage)

`loopSlimRows5_FXC2` is `loopSlimRows_FXC2` (SphereLoopChainRows.lean) with the thresholds of
`loopSgp456_FXC2` (SGP04, SGP05, SGP06 on ONE triple) EXPOSED: the statement carries the triple
`(θ', L_c', η')` together with the generic rows (`hS`: for every closed chapter-14 family
`LocalChartPacketsC14` whose parameters satisfy the numeric hypotheses at `(θ', L_c', η')`, SGP04
(`Sgp04OutV2`), SGP06 (`Sgp06OutV2`) and the SGP05 conclusion, verbatim from `sgp05_row_C14`, hold)
and, for the closed family `loopPacketsC14Z_FXC2` of the C2 register (non-empty slim family, every
orientation parameter `oM`; `Δ = 1200`, `K = 5`, `εr = 0`, all other scalars `0`), the numeric
facts that make those hypotheses true, together with the chain row's conclusion (a chain
`Gaf02ChainEJA` at every base point with an ACTIVE stage-2 slot at a slim centre), the empty zero
family, and the register facts of GAF07's / ZSP02's strong rows (`loopChain_strongRows_FXC2`).
`loopSlimRows5_sgp_FXC2` (SphereLoopSgp5C2.lean) then states SGP04, SGP05 and SGP06 on
`C14of PZ` itself.

The SGP05 conclusion is NOT repeated for `C14of PZ` inside the existential statement: its
elaboration at the concrete C2 types alone costs about 80k heartbeats (generic form: 35k), which
together with the proof exceeds the 200k budget of one declaration.
-/

set_option autoImplicit false
noncomputable section
open Set Function Metric Bundle Manifold Filter GC.MetricGeometry
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace
attribute [local instance] sphereDimension cylinderDimension sphereCompact sphereConnected
  intrinsicMetric intrinsicUniform intrinsicEMetric intrinsicPseudoMetric intrinsicBundle
  cylinderRiemannian cylinderContinuous cylinderComplete
attribute [local instance] loopMS3_FXC2
attribute [local instance] nezero_finrank_euclideanThree_LC87
attribute [local instance] instMetricNC14_FXC2 instChartedNC14_FXC2 instMetricCC14_FXC2

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

local notation "C14of" PZ => LocalChartPacketsC14D.toLocalChartPacketsC14
  (LocalChartPacketsC14Z.toLocalChartPacketsC14D PZ)

/-- **The counted slim rows on the C2 chain, thresholds of SGP04 / SGP05 / SGP06 exposed.** See
the module docstring. -/
theorem loopSlimRows5_FXC2 :
    ∃ (β₂ θ' Lc' η' Γ₆ sg eg₆ : ℝ), 0 < θ' ∧ 0 < Lc' ∧ 0 < η' ∧
      (
      ∀ (X : Type) [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
        [CompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
        (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
        (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (σs : ℝ) (K : ℕ)
        (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ)
        (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β 1200 σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
          εr e T V vs ζ Λz),
        β 2 = β₂ → β 1 ≤ η' → Lc' ≤ Lmax → 0 ≤ Λ → 1000000 * 1200 * Λ < 1 / 100000 →
        e < 1 / 40 → 1600 * (1000000 * 1200) ≤ T → 20 * Λz ≤ T →
        0 < σs → σs < θ' ^ 2 / 10 ^ 6 → vs < θ' / 100 →
        0 < ζ → ζ < θ' ^ 2 / 10 ^ 6 → ζ < 1 / (100 * (1000000 * 1200)) →
        εr < θ' / (100 * (1000000 * 1200)) →
        Sgp04OutV2 P.toLocalChartPacketsRVZ (1 / 200 : ℝ) ∧ Sgp06OutV2 P Γ₆ sg eg₆ ∧
        ∀ i : P.toLocalChartFamily.slim.finite_centres.toFinset,
          ∃ sgn c zsgn zc : X → ℝ,
          (∀ j, |sgn j| ≤ 1) ∧ (∀ k, |zsgn k| ≤ 1) ∧
          (∀ x ∈ ball i.1 (10 ^ 6 * 1200 * ρ i.1),
            |(P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord x| ≤
              8 * 10 ^ 5 * 1200 →
            ‖(ρ i.1)⁻¹ • cgpProjMap P.toLocalChartFamily P.zero
                (cgpQ3Tags P.toLocalChartFamily P.zero) x -
              sgpFullGraph P.toLocalChartFamily P.zero i sgn c zsgn zc
                ((P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord x)‖ <
              (1 / 200 : ℝ) ∧
            ∀ w : TangentSpace 𝓘(ℝ, E3) x,
              ‖(ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
                  (cgpQ3Tags P.toLocalChartFamily P.zero)) x w -
                fderiv ℝ (sgpFullGraph P.toLocalChartFamily P.zero i sgn c zsgn zc)
                  ((P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord x)
                  (mvfderiv 𝓘(ℝ, E3) (P.slim.centre i.1
                    ((Set.Finite.mem_toFinset _).mp i.2)).coord x w)‖ ≤
                (1 / 200 : ℝ) * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner x w w)) ∧
          ∀ p ∈ ball i.1 (10 ^ 6 * 1200 * ρ i.1),
            |(P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord p| ≤
              7 * (10 ^ 5 * 1200) →
            ∀ q, cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero) q =
              cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero) p →
            let Tx := fderiv ℝ (sgpFullGraph P.toLocalChartFamily P.zero i sgn c zsgn zc)
              ((P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord p)
            let Pq := Tx.range.orthogonalProjectionOnto.comp ((ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3)
              (cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero)) q)
            Function.Surjective Pq ∧
            (∀ v, ‖(ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
                (cgpQ3Tags P.toLocalChartFamily P.zero)) q v - (Pq v : BlockSpace _)‖ ≤
              (1 / 200 : ℝ) * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v)) ∧
            (∀ v, (∀ k, Pq k = 0 → g.inner q v k = 0) →
              1 / 2 * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v) ≤ ‖Pq v‖) ∧
            ∀ v, ‖Pq v‖ ≤ 3 * sgpGraphBound * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v)) ∧
      ∃ (Ξ : Fin 3 → ℝ → ℝ) (Γ S eg c cw : Fin 3 → ℝ) (R : ℝ) (hR : 0 < R)
        (ℓ : LoopLen_FXC2) (β : ℕ → ℝ) (σs vs γc Lmax ζ : ℝ),
        (β 2 ≤ 1 / 10000000 ∧ (0 : ℝ) + β 2 < 1 / 10) ∧
        (β 2 = β₂ ∧ β 1 ≤ η' ∧ Lc' ≤ Lmax ∧ 0 < σs ∧ σs < θ' ^ 2 / 10 ^ 6 ∧ vs < θ' / 100 ∧
          0 < ζ ∧ ζ < θ' ^ 2 / 10 ^ 6 ∧ ζ < 1 / (100 * (1000000 * 1200))) ∧
        Nonempty (ManifoldOrientation 𝓘(ℝ, E3) (LoopC_FXC2 ℓ) 3) ∧
        ∀ oM : ManifoldOrientation 𝓘(ℝ, E3) (LoopC_FXC2 ℓ) 3,
          ∃ PZ : LocalChartPacketsC14Z (LoopC_FXC2 ℓ) (loopMetric3_FXC2 ℓ)
            (loopMS3_hmetric_FXC2 ℓ) (fun _ => R) (fun _ => hR) 0 β 1200 σs 5 0 0 0 0 0 0 0 γc 0
            Lmax 0 0 0 0 0 (1600 * (1000000 * 1200)) 0 vs ζ 0 oM,
          PZ.zero.centres = ∅ ∧
          (∃ j ∈ PZ.slim.centres, j ∈ gafStageCore PZ.toLocalChartFamily PZ.zero 2) ∧
          ∀ x₀ : LoopC_FXC2 ℓ,
            ∃ C : Gaf02ChainEJA (C14of PZ) 5 (fun j => Ξ j (Γ j)) Γ S eg c cw 1,
            C.x₀ = x₀ ∧ ∃ j ∈ PZ.slim.centres, ∃ O, C.toChain.slot 2 = Gaf02StageSlot.active O := by
  have h0 := gaf02_chainEJA_row_GAFC 5 (ν := 1 / 100) (cadj := 1) (by norm_num) (by norm_num)
    one_pos
  obtain ⟨θ, Ξ, c, Γ, S, eg, cw, hj, hc01, hc12, hc2, h1⟩ := h0
  obtain ⟨σ, η₂, γ₀, ηc, θt, hσ, hσ1, hη₂, hγ₀, hγ₀1, hηc, hθt, hθt1, hrow⟩ := h1
  have hbeta := loopBeta2s_FXC2 hσ hη₂
  obtain ⟨β₂, hβ₂pos, hβ₂7, hβ₂σ, hβ₂η⟩ := hbeta
  have hβ₂6 : β₂ < 1 / 1000000 := hβ₂7.trans_lt (by norm_num)
  have hr1 := hrow β₂ hβ₂pos hβ₂6 1200 (by norm_num)
  obtain ⟨η₁, Lc₁, η₀₁, θs, Lc₂, η₀₂, k1, k2, k3, k4, k5, k6, k7, hrow'⟩ := hr1
  have hpar := loopSgp06Params_FXC2
  obtain ⟨Γ₆, sg, eg₆, hΓ6, hΓ61, hsg, hsgΓ, hsgC, heg6, heg61, hegΓ⟩ := hpar
  have hsg46 := loopSgp456_FXC2 (Δ := 1200) (β₂ := β₂) (eg := 1 / 200) (by norm_num) hβ₂pos
    (hβ₂6.trans (by norm_num)) (by norm_num) (by norm_num) hΓ6 hΓ61 hsg hsgΓ hsgC heg6 heg61 hegΓ
  obtain ⟨θ', Lc', η', hθ', hLc', hη', hS⟩ := hsg46
  have heg1 : 0 < eg 1 := (hj 1).2.2.2.2.2.2.2.1
  have heg0 : 0 < eg 0 := (hj 0).2.2.2.2.2.2.2.1
  have hegp := egpGraphConst_pos_KC4
  have hθm : 0 < min θs θ' := lt_min k4 hθ'
  have hsm := loopSmall_FXC2 hθt hθm (by positivity : 0 < eg 1 / (20 * egpGraphConst))
    (by norm_num : (0 : ℝ) < 1200)
  obtain ⟨m, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9⟩ := hsm
  have hcs := loopCapMono_FXC2 (θ := θs) hθm (min_le_left _ _) hm4 hm7
  have hc' := loopCapMono_FXC2 (θ := θ') hθm (min_le_right _ _) hm4 hm7
  have hlm := loopLsum_FXC2 hσ k2 k6 hLc' hLc' hLc' (by norm_num : (0 : ℝ) < 1200)
  obtain ⟨L, hL1, hL2, hL3, hL4, hL5, hL6, hL7⟩ := hlm
  have hηm := loopEta6_FXC2 k1 k3 k7 hη' hη' hη'
  obtain ⟨η, hη, hηa, hηb, hηc', hηd, hηe, hηf⟩ := hηm
  have hpk := loopPacketZ_register_FXC2 (σs := m) (vs := m) hm0 hm1 hm0 (β₂ := β₂)
    (hβ₂7.trans_lt (by norm_num)) hη hη hη (Lam := 0) (σc := 0) (μ := 0) (b := 0) (s := 0)
    (b' := 0) (s' := 0) (ε := 0) (γc := γ₀) (βc := 0) (Lmax := L) (τ := 0) (γ := 0)
    (δ := 0) (εr := 0) (e := 0) (T := 1600 * (1000000 * 1200)) (V := 0) (ζ := m) (Λz := 0)
    (by norm_num)
  obtain ⟨R, hR, ℓ, β, ⟨hb1, hb2, hb3, hβ2e, hβ3e⟩, hZ⟩ := hpk
  have hβ7 : β 2 ≤ 1 / 10000000 := by rw [hβ2e]; exact hβ₂7
  have hd : (0 : ℝ) + β 2 < 1 / 10 := by rw [hβ2e]; exact loopGaf07Nums_FXC2 hβ₂7
  refine ⟨β₂, θ', Lc', η', Γ₆, sg, eg₆, hθ', hLc', hη', hS, Ξ, Γ, S, eg, c, cw, R, hR, ℓ, β, m, m,
    γ₀, L, m, ⟨hβ7, hd⟩, ⟨hβ2e, hb1.trans hηd, hL5, hm0, hc'.1, hc'.2, hm0, hc'.1, hm9⟩,
    loopOrientation_FXC2 ℓ, fun oM => ?_⟩
  have hz := hZ oM
  obtain ⟨PZ, hz0, j, hjc, hjcore⟩ := hz
  refine ⟨PZ, hz0, ⟨j, hjc, hjcore⟩, fun x₀ => ?_⟩
  have hC := hrow' (C14of PZ) le_rfl (by norm_num) (by norm_num) (by norm_num) hL1 (by norm_num)
    le_rfl le_rfl (by norm_num) le_rfl (by positivity) (by rw [zero_mul]; positivity)
    (by rw [hβ3e]; norm_num) (by rw [hβ3e]; norm_num) (by rw [hβ2e]; exact hβ₂σ)
    (by rw [hβ2e]; exact hβ₂η) hγ₀.le hγ₀ le_rfl hηc.le k1.le (hb1.trans hηa) hm0 hm2 hm5 hm0 hm2
    (by positivity) (by norm_num) hL2 (by rw [mul_zero]; exact heg0) k3.le (by norm_num)
    (hb1.trans hηb) hL3 (by positivity) (by rw [zero_mul]; positivity) hm3 hm6 hm3 hm8
    (by positivity) hβ2e (hb1.trans hηc') hL4 hcs.1 hcs.2 hcs.1 hm9 (by positivity) le_rfl x₀
  obtain ⟨C, hCx⟩ := hC
  exact ⟨C, hCx, j, hjc, slot_two_active_FXC2 C.toChain hjc⟩

end DifferentialGeometry.Geometry.Collapse
