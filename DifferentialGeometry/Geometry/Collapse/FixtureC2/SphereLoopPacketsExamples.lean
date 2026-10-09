import DifferentialGeometry.Geometry.Collapse.FixtureC2.SphereLoopPackets

/-!
# Consumer of the sphere-loop packet (S-FIXTURE-C2b, F2, G3 file 5)

`loopPacketsC14Z_example_FXC2`: one explicit legal assignment (`R = 200 (D₀ + 1)`, `Δ = 1`,
`σs = 1/100`, `vs = 1`, `K = 5`, `β 1 = min (β₀/2, 1/200)`, `β 2 = β 3 = 1/20`, `b = s = 1/200`,
`ℓ = N R` with `N = ⌈8/β 1⌉ + 1`) at which `loopPacketsC14Z_FXC2` is a `LocalChartPacketsC14Z` on
the sphere loop (for every orientation parameter `oM`) with a NON-EMPTY, finite slim centre set,
for which every slim centre `j` carries its actual LC87 slim centre.
-/

set_option autoImplicit false
noncomputable section
open Set Function Metric Bundle GC.MetricGeometry
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

namespace DifferentialGeometry.Geometry.Collapse

local notation "S2" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem loopPacketsC14Z_example_FXC2 :
    ∃ (R : ℝ) (hR : 0 < R) (ℓ : LoopLen_FXC2) (β : ℕ → ℝ) (Δ σs vs : ℝ) (K : ℕ),
      ∀ oM : ManifoldOrientation 𝓘(ℝ, E3) (LoopC_FXC2 ℓ) 3,
        ∃ P : LocalChartPacketsC14Z (LoopC_FXC2 ℓ) (loopMetric3_FXC2 ℓ)
            (loopMS3_hmetric_FXC2 ℓ) (fun _ => R) (fun _ => hR) (Λ := 0) β Δ σs K (σc := 0)
            (μ := 0) (b := 1 / 200) (s := 1 / 200) (b' := 0) (s' := 0) (ε := 0) (γc := 0)
            (βc := 0) (Lmax := 0) (τ := 0) (γ := 0) (δ := 0) (εr := 0) (e := 0) (T := 0)
            (V := 0) (vs := vs) (ζ := 0) (Λz := 0) oM,
          P.slim.centres.Nonempty ∧ P.slim.centres.Finite ∧
            (∃ j ∈ P.slim.centres, ∃ j' ∈ P.slim.centres, j ≠ j') := by
  obtain ⟨D0, hD00, hD0⟩ := exists_sphereDiam_FXC2
  have hR : 0 < 200 * (D0 + 1) := by positivity
  have hR1 : 1 ≤ 200 * (D0 + 1) := by linarith
  let z₀ : S2 := slimSpherePole
  have hΔ : (1 : ℝ) ≤ 1 := le_rfl
  have hσs : (0 : ℝ) < 1 / 100 := by norm_num
  have hσs1 : (1 / 100 : ℝ) ≤ 1 / 100 := le_rfl
  have hvs : (0 : ℝ) < 1 := one_pos
  have hK : 5 ≤ 5 := le_rfl
  let β0 := slimBeta0_FXC2 hR z₀ hΔ hσs hσs1 hvs hK
  have hβ0pos : 0 < β0 := slimBeta0_pos_FXC2 hR z₀ hΔ hσs hσs1 hvs hK
  let b1 : ℝ := min (β0 / 2) (1 / 200)
  have hb1 : 0 < b1 := lt_min (half_pos hβ0pos) (by norm_num)
  let β : ℕ → ℝ := fun n => if n = 1 then b1 else 1 / 20
  have hβ1 : β 1 = b1 := by simp [β]
  let N : ℕ := ⌈8 / b1⌉₊ + 1
  let ℓ : LoopLen_FXC2 := ⟨N * (1 * (200 * (D0 + 1))), by positivity⟩
  have hN : ℓ.1 = N * (1 * (200 * (D0 + 1))) := rfl
  have hb1' : b1 ≤ 1 / 200 := min_le_right _ _
  have hD0R : D0 / (200 * (D0 + 1)) ≤ 1 / 200 := by
    rw [div_le_div_iff₀ hR (by norm_num)]
    nlinarith
  have hβ1pos : 0 < β 1 := by rw [hβ1]; exact hb1
  have hβ1lt : β 1 < 1 := by rw [hβ1]; linarith
  have hβ2 : β 2 ≤ 3 / 20 := by simp [β]; norm_num
  have hβ3 : β 3 ≤ 3 / 20 := by simp [β]; norm_num
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
    calc 8 * (200 * (D0 + 1)) / b1 = (200 * (D0 + 1)) * (8 / b1) := by ring
      _ ≤ (200 * (D0 + 1)) * N := mul_le_mul_of_nonneg_left h1 hR.le
      _ = N * (1 * (200 * (D0 + 1))) := by ring
  have hΔR : 2 * D0 ≤ 1 * (200 * (D0 + 1)) := by nlinarith
  have hβ0lt : β 1 < β0 := by rw [hβ1]; exact lt_of_le_of_lt (min_le_left _ _) (half_lt_self hβ0pos)
  have hbs : (1 / 200 : ℝ) + 1 / 200 ≤ 1 / 100 := by norm_num
  have hN1 : 0 < N := Nat.succ_pos _
  refine ⟨200 * (D0 + 1), hR, ℓ, β, 1, 1 / 100, 1, 5, fun oM => ?_⟩
  refine ⟨loopPacketsC14Z_FXC2 ℓ hR hD0 hβ1pos hβ1lt hβ2 hβ3 hthin hℓ hΔ hσs hσs1 hvs hK hR1
    hD00 z₀ hN hΔR hβ0lt hbs oM, ?_, ?_, ?_⟩
  · exact ⟨loopCentre_FXC2 ℓ z₀ (1 * (200 * (D0 + 1))) (⟨0, hN1⟩ : Fin N), ⟨⟨0, hN1⟩, rfl⟩⟩
  · exact loopCentres_finite_FXC2 ℓ z₀ (1 * (200 * (D0 + 1))) N
  · have hN2 : 1 < N := by
      have : 0 < 8 / b1 := by positivity
      have := Nat.ceil_pos.mpr this
      omega
    refine ⟨loopCentre_FXC2 ℓ z₀ (1 * (200 * (D0 + 1))) (⟨0, hN1⟩ : Fin N), ⟨⟨0, hN1⟩, rfl⟩,
      loopCentre_FXC2 ℓ z₀ (1 * (200 * (D0 + 1))) (⟨1, hN2⟩ : Fin N), ⟨⟨1, hN2⟩, rfl⟩, ?_⟩
    intro h
    have hfar := loopCentres_far_FXC2 ℓ z₀ (loop_sp_pos_FXC2 hR hΔ) hN
      (⟨0, hN1⟩ : Fin N) ⟨1, hN2⟩ (by simp)
    rw [h, dist_self] at hfar
    have := loop_sp_pos_FXC2 hR hΔ
    linarith

end DifferentialGeometry.Geometry.Collapse
