import DifferentialGeometry.Geometry.Collapse.FixtureC2.SphereLoopSgpRows
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEJARow
import DifferentialGeometry.Geometry.Fibration.ActualStageChainGaf07RowStrong
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEZeroFacesStandard

/-!
# The counted slim rows run on the production chain over the sphere loop packet
(S-FIXTURE-C2c, R2, G6 file 3; acceptance configuration C-S of D75, slim stage)

`loopSlimRows_FXC2`: at one legal register (`Δ = 1200`, `K = 5`, `ν = 1/100`, `c_adj = 1`,
`β₂ ≤ 10⁻⁷`, `εr = 0`) of the production chain row `gaf02_chainEJA_row_GAFC` the closed family
`loopPacketsC14Z_FXC2` (non-empty slim family, for every orientation parameter `oM`) satisfies

* the conclusions of SGP04 (`Sgp04OutV2`) and SGP06 (`Sgp06OutV2`) on the packet (their thresholds
  are met by ONE triple: `loopSgp46_FXC2`);
* the hypotheses of the chain row, hence a chain `Ĉ : Gaf02ChainEJA` at every base point `x₀`, with
  an ACTIVE stage-2 slot at a slim centre of the slim stage core; the zero family is empty;
* the register facts `β 2 ≤ 10⁻⁷`, `γ + β 2 < 1/10`, `5 ≤ K`, `εr < 1/2`.

`loopChain_strongRows_FXC2`: these facts are exactly the hypotheses of GAF07's STRONG row
(`gaf07_row_strong_GAFD`; its slim part quantifies over the actual slim centres: D1 base piece,
chart map, local trivializations; D2 whole-fibre isotopy; for every orientation) and of ZSP02's
strong row (`zsp02_row_strong_ZSP35` on `PZ`), which therefore apply to every chain of
`loopSlimRows_FXC2`. (The two strong-row types are not repeated inside the existential statement:
their elaborated size alone exceeds the heartbeat budget of the register proof.)
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

/-- **GAF07's STRONG row and ZSP02's strong row on a chain over the closed C2 family.** The four
numeric hypotheses are exactly the register facts of `loopSlimRows_FXC2`
(`β 2 ≤ 10⁻⁷`, `γ + β 2 < 1/10`, `5 ≤ K`, `εr < 1/2`), so the rows apply to every chain it
produces. The slim part of the GAF07 row quantifies over the ACTUAL slim centres of `PZ`
(D1: base piece, chart map, local trivializations; D2: whole-fibre isotopy), the ZSP02 row over the
zero centres (an empty family on C2). -/
theorem loopChain_strongRows_FXC2 {ℓ : LoopLen_FXC2} {R : ℝ} {hR : 0 < R} {Lam : ℝ}
    {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ} {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    {oM : ManifoldOrientation 𝓘(ℝ, E3) (LoopC_FXC2 ℓ) 3}
    (PZ : LocalChartPacketsC14Z (LoopC_FXC2 ℓ) (loopMetric3_FXC2 ℓ) (loopMS3_hmetric_FXC2 ℓ)
      (fun _ => R) (fun _ => hR) Lam β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
      oM)
    {Kj : ℕ} {Ξ' Γ S eg c cw : Fin 3 → ℝ} {cadj : ℝ}
    (C : Gaf02ChainEJA (C14of PZ) Kj Ξ' Γ S eg c cw cadj) (hβ : β 2 ≤ 1 / 10000000)
    (hd : γ + β 2 < 1 / 10) (hK : 5 ≤ K) (hεr : εr < 1 / 2) :
    (∀ oM' : ManifoldOrientation 𝓘(ℝ, E3) (LoopC_FXC2 ℓ) 3,
      type_of% (C.gaf07_row_strong_GAFD hβ hd hK oM')) ∧
    type_of% (Gaf02ChainE.zsp02_row_strong_ZSP35 (P := PZ) C.toGaf02ChainE hεr) :=
  ⟨fun oM' => C.gaf07_row_strong_GAFD hβ hd hK oM',
    Gaf02ChainE.zsp02_row_strong_ZSP35 (P := PZ) C.toGaf02ChainE hεr⟩

/-- **The counted slim rows on the C2 chain.** See the module docstring. -/
theorem loopSlimRows_FXC2 :
    ∃ (Kj : ℕ) (Ξ : Fin 3 → ℝ → ℝ) (Γ S eg c cw : Fin 3 → ℝ) (cadj : ℝ) (R : ℝ) (hR : 0 < R)
      (ℓ : LoopLen_FXC2) (β : ℕ → ℝ) (Δ σs vs : ℝ) (K : ℕ)
      (Lam σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V ζ Λz : ℝ) (Γ₆ sg eg₄ eg₆ : ℝ),
      (β 2 ≤ 1 / 10000000 ∧ γ + β 2 < 1 / 10 ∧ 5 ≤ K ∧ εr < 1 / 2) ∧
      Nonempty (ManifoldOrientation 𝓘(ℝ, E3) (LoopC_FXC2 ℓ) 3) ∧
      ∀ oM : ManifoldOrientation 𝓘(ℝ, E3) (LoopC_FXC2 ℓ) 3,
        ∃ PZ : LocalChartPacketsC14Z (LoopC_FXC2 ℓ) (loopMetric3_FXC2 ℓ) (loopMS3_hmetric_FXC2 ℓ)
          (fun _ => R) (fun _ => hR) Lam β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
          Λz oM,
        Sgp04OutV2 (C14of PZ).toLocalChartPacketsRVZ eg₄ ∧ Sgp06OutV2 (C14of PZ) Γ₆ sg eg₆ ∧
        PZ.zero.centres = ∅ ∧
        (∃ j ∈ PZ.slim.centres, j ∈ gafStageCore PZ.toLocalChartFamily PZ.zero 2) ∧
        ∀ x₀ : LoopC_FXC2 ℓ,
          ∃ C : Gaf02ChainEJA (C14of PZ) Kj (fun j => Ξ j (Γ j)) Γ S eg c cw cadj,
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
  have hsg46 := loopSgp46_FXC2 (Δ := 1200) (β₂ := β₂) (eg := 1 / 200) (by norm_num) hβ₂pos
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
  refine ⟨5, Ξ, Γ, S, eg, c, cw, 1, R, hR, ℓ, β, 1200, m, m, 5, 0, 0, 0, 0, 0, 0, 0, 0, γ₀, 0, L,
    0, 0, 0, 0, 0, 1600 * (1000000 * 1200), 0, m, 0, Γ₆, sg, 1 / 200, eg₆,
    ⟨hβ7, hd, le_rfl, by norm_num⟩, loopOrientation_FXC2 ℓ, fun oM => ?_⟩
  have hz := hZ oM
  obtain ⟨PZ, hz0, j, hjc, hjcore⟩ := hz
  have hSS := hS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (C14of PZ) hβ2e
    (hb1.trans hηd) hL5 le_rfl (by norm_num) (by norm_num) le_rfl (by norm_num) hm0 hc'.1 hc'.2
    hm0 hc'.1 hm9 (by positivity)
  refine ⟨PZ, hSS.1, hSS.2, hz0, ⟨j, hjc, hjcore⟩, fun x₀ => ?_⟩
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
