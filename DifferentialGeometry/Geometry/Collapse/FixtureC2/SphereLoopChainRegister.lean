import DifferentialGeometry.Geometry.Collapse.FixtureC2.SphereLoopStageSlim

/-!
# The numeric register and the packet of the chain row on the sphere loop
(S-FIXTURE-C2c, R2, G5 file 1)

The production row `gaf02_chainEJA_row_GAFC` is applied to the C2 packet in
`SphereLoopChainRow.lean`. Its big hypothesis context makes every arithmetic tactic slow, so all
numbers are chosen HERE, in lemmas with a clean context:

* `loopBeta2_FXC2`: the row's `β₂ < 10⁻⁶`, `3 β₂ ≤ σ`, `β₂ ≤ η₂`;
* `loopSmall_FXC2`: one small number `m > 0` below the nine caps of the row (`σs = vs = ζ = m`);
* `loopLmax_FXC2`: `L_max` above the four lower bounds of the row;
* `loopPacket_register_FXC2`: for ANY values of the free packet parameters with `b + s ≤ 1/100`
  and any positive `σs, vs, η₁, η₀₁, η₀₂` and `β₂ < 1/10`: the C2 packet `loopPacketsC14_FXC2` at
  `Δ = 1200`, `K = 5`, `R = 200 (D₀ + 1)` with `β 1 ≤ min(η₁, η₀₁, η₀₂, 1/200, β₀/2)`, `β 2 = β₂`,
  `β 3 = 3/100`, together with a slim centre in the slim stage core.
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

/-- The row's `β₂`: below `10⁻⁶`, `3 β₂ ≤ σ`, `β₂ ≤ η₂`. -/
theorem loopBeta2_FXC2 {σ η₂ : ℝ} (hσ : 0 < σ) (hη₂ : 0 < η₂) :
    ∃ β₂ : ℝ, 0 < β₂ ∧ β₂ < 1 / 1000000 ∧ 3 * β₂ ≤ σ ∧ β₂ ≤ η₂ := by
  have h1 : (0 : ℝ) < σ / 3 := by positivity
  refine ⟨min (1 / 2000000) (min (σ / 3) η₂), lt_min (by norm_num) (lt_min h1 hη₂), ?_, ?_, ?_⟩
  · exact (min_le_left _ _).trans_lt (by norm_num)
  · have := (min_le_right (1 / 2000000 : ℝ) (min (σ / 3) η₂)).trans (min_le_left _ _)
    linarith
  · exact (min_le_right _ _).trans (min_le_right _ _)

/-- One small number below the nine caps of the row (`c₁ = eg 1 / (20 C₁)`, `Δ > 0`). -/
theorem loopSmall_FXC2 {θt θs c₁ Δ : ℝ} (hθt : 0 < θt) (hθs : 0 < θs) (hc₁ : 0 < c₁)
    (hΔ : 0 < Δ) :
    ∃ m : ℝ, 0 < m ∧ m ≤ 1 / 100 ∧ m ≤ θt ^ 2 / 1000 ∧ m ≤ c₁ ^ 2 / 10 ^ 8 ∧
      m < θs ^ 2 / 10 ^ 6 ∧ m ≤ θt / 100 ∧ m < c₁ / 100 ∧ m < θs / 100 ∧
      m ≤ 1 / (1000 * (1000000 * Δ)) ∧ m < 1 / (100 * (1000000 * Δ)) := by
  have hev : ∀ᶠ x in 𝓝[>] (0 : ℝ), x < 1 / 100 ∧ x < θt ^ 2 / 1000 ∧ x < c₁ ^ 2 / 10 ^ 8 ∧
      x < θs ^ 2 / 10 ^ 6 ∧ x < θt / 100 ∧ x < c₁ / 100 ∧ x < θs / 100 ∧
      x < 1 / (1000 * (1000000 * Δ)) ∧ x < 1 / (100 * (1000000 * Δ)) := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 100 by norm_num),
      Ioo_mem_nhdsGT (show (0 : ℝ) < θt ^ 2 / 1000 by positivity),
      Ioo_mem_nhdsGT (show (0 : ℝ) < c₁ ^ 2 / 10 ^ 8 by positivity),
      Ioo_mem_nhdsGT (show (0 : ℝ) < θs ^ 2 / 10 ^ 6 by positivity),
      Ioo_mem_nhdsGT (show (0 : ℝ) < θt / 100 by positivity),
      Ioo_mem_nhdsGT (show (0 : ℝ) < c₁ / 100 by positivity),
      Ioo_mem_nhdsGT (show (0 : ℝ) < θs / 100 by positivity),
      Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / (1000 * (1000000 * Δ)) by positivity),
      Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / (100 * (1000000 * Δ)) by positivity)]
      with x h1 h2 h3 h4 h5 h6 h7 h8 h9
    exact ⟨h1.2, h2.2, h3.2, h4.2, h5.2, h6.2, h7.2, h8.2, h9.2⟩
  obtain ⟨x, ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩, h0⟩ := (hev.and self_mem_nhdsWithin).exists
  exact ⟨x, h0, h1.le, h2.le, h3.le, h4, h5.le, h6, h7, h8.le, h9⟩

/-- `L_max` above the four lower bounds of the row. -/
theorem loopLmax_FXC2 {σ L₁ L₂ Δ : ℝ} (hσ : 0 < σ) (h₁ : 0 < L₁) (h₂ : 0 < L₂) (hΔ : 0 < Δ) :
    ∃ L : ℝ, 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ L ∧ σ⁻¹ ≤ L ∧ L₁ ≤ L ∧ L₂ ≤ L := by
  have hA : 0 < 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) := by positivity
  have hσ' : 0 < σ⁻¹ := inv_pos.mpr hσ
  refine ⟨4 * (10 + 2 * (2000000 * Δ) + Δ / 3) + σ⁻¹ + L₁ + L₂, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- **The C2 packet at the register of the row.** For any values of the free packet parameters
with `b + s ≤ 1/100` and any positive `σs, vs, η₁, η₀₁, η₀₂` and `β₂ < 1/10`: at `Δ = 1200`,
`K = 5` and
`R = 200 (D₀ + 1)` there are `ℓ`, a scale function `β` with `β 1 ≤ η₁, η₀₁, η₀₂`, `β 2 = β₂`,
`β 3 = 3/100`, and the packet `loopPacketsC14_FXC2` (non-empty slim family) whose slim centre
`j` lies in the slim stage core. -/
theorem loopPacket_register_FXC2 {σs vs : ℝ} (hσs : 0 < σs) (hσs1 : σs ≤ 1 / 100)
    (hvs : 0 < vs) {β₂ η₁ η₀₁ η₀₂ : ℝ} (hβ₂1 : β₂ < 1 / 10) (hη₁ : 0 < η₁)
    (hη₀₁ : 0 < η₀₁) (hη₀₂ : 0 < η₀₂)
    {Lam σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V ζ Λz : ℝ} (hbs : b + s ≤ 1 / 100) :
    ∃ (R : ℝ) (hR : 0 < R) (ℓ : LoopLen_FXC2) (β : ℕ → ℝ)
      (P : LocalChartPacketsC14 (LoopC_FXC2 ℓ) (loopMetric3_FXC2 ℓ) (loopMS3_hmetric_FXC2 ℓ)
        (fun _ => R) (fun _ => hR) Lam β 1200 σs 5 σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        ζ Λz),
      β 1 ≤ η₁ ∧ β 1 ≤ η₀₁ ∧ β 1 ≤ η₀₂ ∧ β 2 = β₂ ∧ β 3 = 3 / 100 ∧
        ∃ j ∈ P.slim.centres, j ∈ gafStageCore P.toLocalChartFamily P.zero 2 := by
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
  let P := loopPacketsC14_FXC2 (Lam := Lam) (σc := σc) (μ := μ) (b' := b') (s' := s') (ε := ε)
    (γc := γc) (βc := βc) (Lmax := Lmax) (τ := τ) (γ := γ) (δ := δ) (εr := εr) (e := e)
    (T := T) (V := V) (ζ := ζ) (Λz := Λz) ℓ hR hD0 hβ1pos hβ1lt hβ2 hβ3 hthin hℓ hΔ hσs hσs1
    hvs hK hR1 hD00 z₀ hN hΔR hβ0lt hbs
  have hj : loopCentre_FXC2 ℓ z₀ (1200 * (200 * (D0 + 1))) (⟨0, hN1⟩ : Fin N) ∈ P.slim.centres :=
    ⟨⟨0, hN1⟩, rfl⟩
  refine ⟨200 * (D0 + 1), hR, ℓ, β, P, ?_, ?_, ?_, hβ2e, hβ3e,
    ⟨_, hj, (gafCloud_two_nonempty_FXC2 _ _ hj (by norm_num)).1⟩⟩
  · rw [hβ1]; exact (min_le_right _ _).trans (min_le_left _ _)
  · rw [hβ1]; exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  · rw [hβ1]; exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))

end DifferentialGeometry.Geometry.Collapse
