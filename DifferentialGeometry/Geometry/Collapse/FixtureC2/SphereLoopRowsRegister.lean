import DifferentialGeometry.Geometry.Collapse.FixtureC2.SphereLoopChainRegister
import DifferentialGeometry.Geometry.Fibration.ActualStageChainRow

/-!
# The register of the counted slim rows on the sphere loop (S-FIXTURE-C2c, R2, G6 file 1)

Numbers and the closed packet for `SphereLoopChainRows.lean` (GAF07 strong row, ZSP02 strong row,
SGP04, SGP05, SGP06 on the production chain over the C2 packet), chosen in lemmas with clean
contexts:

* `loopBeta2s_FXC2`: GAF07's `β₂ ≤ 10⁻⁷` together with the chain row's `β₂ < 10⁻⁶`, `3β₂ ≤ σ`,
  `β₂ ≤ η₂`;
* `loopCapMono_FXC2`: the two SGP caps of a threshold `θ` from the same caps of a smaller `θ'`;
* `loopLsum_FXC2`: `L_max` above the lower bounds of the chain row and of the three SGP rows;
* `loopSgp06Params_FXC2`: `Γ, sg, eg` of SGP06;
* `loopPacketZ_register_FXC2`: for every orientation parameter, the closed family
  `loopPacketsC14Z_FXC2` of the register (as `loopPacket_register_FXC2`, with `PZ` in place of
  `P`; all packet parameters free).
-/

set_option autoImplicit false
noncomputable section
open Set Function Metric Bundle GC.MetricGeometry Filter
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Collapse
open scoped Manifold ContDiff Topology ENNReal

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace
attribute [local instance] sphereDimension cylinderDimension sphereCompact sphereConnected
  intrinsicMetric intrinsicUniform intrinsicEMetric intrinsicPseudoMetric intrinsicBundle
  cylinderRiemannian cylinderContinuous cylinderComplete
attribute [local instance] loopMS3_FXC2
attribute [local instance] nezero_finrank_euclideanThree_LC87
attribute [local instance] instMetricNC14_FXC2 instChartedNC14_FXC2 instMetricCC14_FXC2

namespace DifferentialGeometry.Geometry.Collapse

local notation "S2" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The row's `β₂` with GAF07's `β₂ ≤ 10⁻⁷`. -/
theorem loopBeta2s_FXC2 {σ η₂ : ℝ} (hσ : 0 < σ) (hη₂ : 0 < η₂) :
    ∃ β₂ : ℝ, 0 < β₂ ∧ β₂ ≤ 1 / 10000000 ∧ 3 * β₂ ≤ σ ∧ β₂ ≤ η₂ := by
  have h1 : (0 : ℝ) < σ / 3 := by positivity
  refine ⟨min (1 / 10000000) (min (σ / 3) η₂), lt_min (by norm_num) (lt_min h1 hη₂),
    min_le_left _ _, ?_, ?_⟩
  · have := (min_le_right (1 / 10000000 : ℝ) (min (σ / 3) η₂)).trans (min_le_left _ _)
    linarith
  · exact (min_le_right _ _).trans (min_le_right _ _)

/-- The two caps of an SGP threshold `θ` from the caps of a smaller `θ'`. -/
theorem loopCapMono_FXC2 {θ θ' m : ℝ} (hθ' : 0 < θ') (hle : θ' ≤ θ) (h1 : m < θ' ^ 2 / 10 ^ 6)
    (h2 : m < θ' / 100) : m < θ ^ 2 / 10 ^ 6 ∧ m < θ / 100 := by
  refine ⟨h1.trans_le ?_, h2.trans_le ?_⟩
  · gcongr
  · linarith

/-- A square cap transfers to a larger threshold. -/
theorem loopSqMono_FXC2 {x θ θ' : ℝ} (h0 : 0 < θ) (hle : θ ≤ θ') (h : x < θ ^ 2 / 10 ^ 6) :
    x < θ' ^ 2 / 10 ^ 6 :=
  h.trans_le (by gcongr)

/-- A linear cap transfers to a larger threshold. -/
theorem loopLinMono_FXC2 {x θ θ' : ℝ} (hle : θ ≤ θ') (h : x < θ / 100) : x < θ' / 100 :=
  h.trans_le (by linarith)

/-- `L_max` above the lower bounds of the chain row and of the three SGP rows. -/
theorem loopLsum_FXC2 {σ L₁ L₂ L₄ L₅ L₆ Δ : ℝ} (hσ : 0 < σ) (h₁ : 0 < L₁) (h₂ : 0 < L₂)
    (h₄ : 0 < L₄) (h₅ : 0 < L₅) (h₆ : 0 < L₆) (hΔ : 0 < Δ) :
    ∃ L : ℝ, 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ L ∧ σ⁻¹ ≤ L ∧ L₁ ≤ L ∧ L₂ ≤ L ∧ L₄ ≤ L ∧
      L₅ ≤ L ∧ L₆ ≤ L := by
  have hA : 0 < 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) := by positivity
  have hσ' : 0 < σ⁻¹ := inv_pos.mpr hσ
  refine ⟨4 * (10 + 2 * (2000000 * Δ) + Δ / 3) + σ⁻¹ + L₁ + L₂ + L₄ + L₅ + L₆, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩ <;> linarith

/-- One positive number below six positive thresholds. -/
theorem loopEta6_FXC2 {a b c d e f : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (he : 0 < e) (hf : 0 < f) :
    ∃ η : ℝ, 0 < η ∧ η ≤ a ∧ η ≤ b ∧ η ≤ c ∧ η ≤ d ∧ η ≤ e ∧ η ≤ f :=
  ⟨min a (min b (min c (min d (min e f)))),
    lt_min ha (lt_min hb (lt_min hc (lt_min hd (lt_min he hf)))), min_le_left _ _,
    (min_le_right _ _).trans (min_le_left _ _),
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)),
    (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))),
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))),
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _))))⟩

/-- GAF07's `γ + β₂ < 1/10` at `γ = 0`. -/
theorem loopGaf07Nums_FXC2 {β₂ : ℝ} (h : β₂ ≤ 1 / 10000000) : (0 : ℝ) + β₂ < 1 / 10 := by
  linarith

/-- The parameters of SGP06: `Γ = 1/2`, `sg`, `eg`. -/
theorem loopSgp06Params_FXC2 :
    ∃ Γ sg eg : ℝ, 0 < Γ ∧ Γ < 1 ∧ 0 < sg ∧ sg < Γ / 200 ∧
      sg < Γ ^ 3 / (100 * sgpGraphBound) ∧ 0 < eg ∧ eg < 1 / 100 ∧ eg < Γ * sg / 100 := by
  have hB : 0 < sgpGraphBound := sgpGraphBound_pos_GAF8
  have h1 : (0 : ℝ) < (1 / 2 : ℝ) / 400 := by norm_num
  have h2 : (0 : ℝ) < (1 / 2 : ℝ) ^ 3 / (200 * sgpGraphBound) := by positivity
  refine ⟨1 / 2, min ((1 / 2 : ℝ) / 400) ((1 / 2 : ℝ) ^ 3 / (200 * sgpGraphBound)),
    min (1 / 200) ((1 / 2 : ℝ) * min ((1 / 2 : ℝ) / 400)
      ((1 / 2 : ℝ) ^ 3 / (200 * sgpGraphBound)) / 200), by norm_num, by norm_num,
    lt_min h1 h2, ?_, ?_, ?_, ?_, ?_⟩
  · have := min_le_left ((1 / 2 : ℝ) / 400) ((1 / 2 : ℝ) ^ 3 / (200 * sgpGraphBound))
    linarith
  · have := min_le_right ((1 / 2 : ℝ) / 400) ((1 / 2 : ℝ) ^ 3 / (200 * sgpGraphBound))
    have h3 : (1 / 2 : ℝ) ^ 3 / (200 * sgpGraphBound) <
        (1 / 2 : ℝ) ^ 3 / (100 * sgpGraphBound) := by
      apply div_lt_div_of_pos_left (by norm_num) (by positivity) (by linarith)
    linarith
  · exact lt_min (by norm_num) (by have := lt_min h1 h2; positivity)
  · exact (min_le_left _ _).trans_lt (by norm_num)
  · have hs : 0 < min ((1 / 2 : ℝ) / 400) ((1 / 2 : ℝ) ^ 3 / (200 * sgpGraphBound)) := lt_min h1 h2
    have := min_le_right (1 / 200 : ℝ) ((1 / 2 : ℝ) * min ((1 / 2 : ℝ) / 400)
      ((1 / 2 : ℝ) ^ 3 / (200 * sgpGraphBound)) / 200)
    linarith

/-- **The closed family `loopPacketsC14Z_FXC2` at the register of the rows.** As
`loopPacket_register_FXC2`, with the closed family `PZ` (for every orientation parameter `oM`) in
place of `P`, and the zero family empty; the numbers `R, ℓ, β` do not depend on `oM`. -/
theorem loopPacketZ_register_FXC2 {σs vs : ℝ} (hσs : 0 < σs) (hσs1 : σs ≤ 1 / 100)
    (hvs : 0 < vs) {β₂ η₁ η₀₁ η₀₂ : ℝ} (hβ₂1 : β₂ < 1 / 10) (hη₁ : 0 < η₁)
    (hη₀₁ : 0 < η₀₁) (hη₀₂ : 0 < η₀₂)
    {Lam σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V ζ Λz : ℝ} (hbs : b + s ≤ 1 / 100) :
    ∃ (R : ℝ) (hR : 0 < R) (ℓ : LoopLen_FXC2) (β : ℕ → ℝ),
      (β 1 ≤ η₁ ∧ β 1 ≤ η₀₁ ∧ β 1 ≤ η₀₂ ∧ β 2 = β₂ ∧ β 3 = 3 / 100) ∧
      ∀ oM : ManifoldOrientation 𝓘(ℝ, E3) (LoopC_FXC2 ℓ) 3,
        ∃ PZ : LocalChartPacketsC14Z (LoopC_FXC2 ℓ) (loopMetric3_FXC2 ℓ) (loopMS3_hmetric_FXC2 ℓ)
          (fun _ => R) (fun _ => hR) Lam β 1200 σs 5 σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
          vs ζ Λz oM,
        PZ.zero.centres = ∅ ∧
          ∃ j ∈ PZ.slim.centres, j ∈ gafStageCore PZ.toLocalChartFamily PZ.zero 2 := by
  obtain ⟨D0, hD00, hD0⟩ := exists_sphereDiam_FXC2
  have hR : 0 < 200 * (D0 + 1) := by positivity
  have hR1 : 1 ≤ 200 * (D0 + 1) := by linarith
  let z₀ : S2 := slimSpherePole
  have hΔ : (1 : ℝ) ≤ 1200 := by norm_num
  have hK : 5 ≤ 5 := le_rfl
  let β0 := slimBeta0_FXC2 hR z₀ hΔ hσs hσs1 hvs hK
  have hβ0pos : 0 < β0 := slimBeta0_pos_FXC2 hR z₀ hΔ hσs hσs1 hvs hK
  let b1 : ℝ := min (min (β0 / 2) (1 / 200)) (min η₁ (min η₀₁ η₀₂))
  have hb1 : 0 < b1 :=
    lt_min (lt_min (half_pos hβ0pos) (by norm_num)) (lt_min hη₁ (lt_min hη₀₁ hη₀₂))
  let β : ℕ → ℝ := fun n => if n = 1 then b1 else if n = 2 then β₂ else 3 / 100
  have hβ1 : β 1 = b1 := by simp [β]
  have hβ2e : β 2 = β₂ := by simp [β]
  have hβ3e : β 3 = 3 / 100 := by simp [β]
  let N : ℕ := ⌈8 / b1⌉₊ + 1
  let ℓ : LoopLen_FXC2 := ⟨N * (1200 * (200 * (D0 + 1))), by positivity⟩
  have hN : ℓ.1 = N * (1200 * (200 * (D0 + 1))) := rfl
  have hb1' : b1 ≤ 1 / 200 := (min_le_left _ _).trans (min_le_right _ _)
  have hD0R : D0 / (200 * (D0 + 1)) ≤ 1 / 200 := by
    rw [div_le_div_iff₀ hR (by norm_num)]
    nlinarith
  have hβ1pos : 0 < β 1 := by rw [hβ1]; exact hb1
  have hβ1lt : β 1 < 1 := by rw [hβ1]; linarith
  have hβ2 : β 2 ≤ 3 / 20 := by rw [hβ2e]; linarith
  have hβ3 : β 3 ≤ 3 / 20 := by rw [hβ3e]; norm_num
  have hthin : β 1 / 2 + D0 / (200 * (D0 + 1)) ≤ 1 / 100 := by
    rw [hβ1]
    linarith
  have hℓ : 8 * (200 * (D0 + 1)) / β 1 ≤ ℓ.1 := by
    rw [hN, hβ1]
    have h1 : 8 / b1 ≤ (N : ℝ) := by
      have := Nat.le_ceil (8 / b1)
      have h2 : (⌈8 / b1⌉₊ : ℝ) ≤ N := by
        change (⌈8 / b1⌉₊ : ℝ) ≤ ((⌈8 / b1⌉₊ + 1 : ℕ) : ℝ)
        push_cast
        linarith
      linarith
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    calc 8 * (200 * (D0 + 1)) / b1 = (200 * (D0 + 1)) * (8 / b1) := by ring
      _ ≤ (200 * (D0 + 1)) * N := mul_le_mul_of_nonneg_left h1 hR.le
      _ ≤ N * (1200 * (200 * (D0 + 1))) := by nlinarith
  have hΔR : 2 * D0 ≤ 1200 * (200 * (D0 + 1)) := by nlinarith
  have hβ0lt : β 1 < β0 := by
    rw [hβ1]
    exact lt_of_le_of_lt ((min_le_left _ _).trans (min_le_left _ _)) (half_lt_self hβ0pos)
  have hN1 : 0 < N := Nat.succ_pos _
  refine ⟨200 * (D0 + 1), hR, ℓ, β, ⟨?_, ?_, ?_, hβ2e, hβ3e⟩, fun oM => ?_⟩
  · rw [hβ1]; exact (min_le_right _ _).trans (min_le_left _ _)
  · rw [hβ1]; exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  · rw [hβ1]; exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  · let PZ := loopPacketsC14Z_FXC2 (Lam := Lam) (σc := σc) (μ := μ) (b' := b') (s' := s')
      (ε := ε) (γc := γc) (βc := βc) (Lmax := Lmax) (τ := τ) (γ := γ) (δ := δ) (εr := εr)
      (e := e) (T := T) (V := V) (ζ := ζ) (Λz := Λz) ℓ hR hD0 hβ1pos hβ1lt hβ2 hβ3 hthin hℓ hΔ
      hσs hσs1 hvs hK hR1 hD00 z₀ hN hΔR hβ0lt hbs oM
    have hj : loopCentre_FXC2 ℓ z₀ (1200 * (200 * (D0 + 1))) (⟨0, hN1⟩ : Fin N) ∈
        PZ.slim.centres := ⟨⟨0, hN1⟩, rfl⟩
    exact ⟨PZ, rfl, _, hj, (gafCloud_two_nonempty_FXC2 _ _ hj (by norm_num)).1⟩

end DifferentialGeometry.Geometry.Collapse
