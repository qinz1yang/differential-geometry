import DifferentialGeometry.Geometry.MinimalSurface.Plateau.VaryingMetricCompactnessR7CRotation
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.VaryingMetricCompactnessR7CDecay
import DifferentialGeometry.Analysis.Complex.BoundaryLens.Rotation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# R7C L5（三）：边界一致 Morrey decay（无边界 energy concentration）

对 `(N, g)`（R7C 中取 completion buffer `(W, Ĝ)`）里 smooth embedded `γ`、对一切中心局部 `Λ`-quasi-minimal、
能量 `≤ E₀`、trace 由连续单调 lift `ψ` 给出且 lift 有一致增量模 `ψ b − ψ a ≤ 2/3`（`0 ≤ b − a ≤ η`）的
Lipschitz 盘 `u`：存在只依赖 `(g, γ, Λ, E₀, η)` 的 `N, θ < 1, ε₀, s₀`，使对每个边界点 `c` 与每个 `k`，
`E(u, B̄_{s₀/2^{N+k}}(c) ∩ D) ≤ θ^k ε₀`。证明：旋转到 `−1`（`rotated_local_quasi_min_R7C`），
lens hole-filling（`boundary_lens_hole_filling_qm_R7C`，lift 增量条件由增量模 + `1 − 2 arccos(ρ/2)/π ≤ ρ/2`
给出），再用二进 small-drop 迭代（`dyadic_decay_of_hole_filling_R7C`）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Metric Manifold
open DifferentialGeometry.Topology DifferentialGeometry.Analysis
open scoped Topology ContDiff Manifold ENNReal NNReal

namespace DifferentialGeometry.Geometry

/-- lens 参数弧长估计（R7C）：`1 − 2 arccos(ρ/2)/π ≤ ρ/2`（`0 ≤ ρ ≤ 2`，Jordan 不等式）。 -/
theorem one_sub_two_arccos_div_pi_le_R7C {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ2 : ρ ≤ 2) :
    1 - 2 * (Real.arccos (ρ / 2) / Real.pi) ≤ ρ / 2 := by
  have hx0 : 0 ≤ ρ / 2 := by positivity
  have hx1 : ρ / 2 ≤ 1 := by linarith
  set θ := Real.arcsin (ρ / 2) with hθ
  have hθ0 : 0 ≤ θ := Real.arcsin_nonneg.mpr hx0
  have hθ1 : θ ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two _
  have hsin : Real.sin θ = ρ / 2 := Real.sin_arcsin (by linarith) hx1
  have hJ := Real.mul_le_sin hθ0 hθ1
  rw [hsin] at hJ
  rw [Real.arccos_eq_pi_div_two_sub_arcsin, ← hθ]
  have hpi : 0 < Real.pi := Real.pi_pos
  have h1 : 1 - 2 * ((Real.pi / 2 - θ) / Real.pi) = 2 / Real.pi * θ := by
    field_simp
    ring
  rw [h1]
  linarith

variable {E N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace N] [ChartedSpace E N]
  [IsManifold 𝓘(ℝ, E) ∞ N] [T3Space N]

/-- **L5 边界一致 dyadic decay**（R7C）：见文件头。 -/
theorem boundary_dyadic_decay_R7C (g : SmoothRiemannianMetric 𝓘(ℝ, E) N) (γ : freeLoop N)
    (hγ : IsSmoothEmbeddedLoop (E := E) γ) {Λ E₀ η : ℝ} (hΛ : 0 ≤ Λ) (hE₀ : 0 ≤ E₀)
    (hη : 0 < η) :
    ∃ (K : ℕ) (θ ε₀ s₀ : ℝ), 0 ≤ θ ∧ θ < 1 ∧ 0 < ε₀ ∧ 0 < s₀ ∧ s₀ ≤ 1 / 8 ∧
      ∀ (u : C(closedDisk, N)) (L : ℝ≥0),
      (∀ z w : closedDisk, riemannianEDistOf g (u z) (u w) ≤ (L : ℝ≥0∞) * edist z w) →
      ∀ ψ : CircleDeg1Lift, Continuous ψ →
      (∀ t : ℝ, u (diskBoundary (t : loopCircle)) = γ ((ψ t : ℝ) : loopCircle)) →
      (∀ a b : ℝ, a ≤ b → b - a ≤ η → ψ b - ψ a ≤ 2 / 3) →
      (∫ z in closedBall (0 : ℂ) 1, diskMapEnergyDensity g (diskExtension u) z) ≤ E₀ →
      (∀ (c : ℂ) (s : ℝ) (w : C(closedDisk, N)) (Lw : ℝ≥0),
        (∀ z z', riemannianEDistOf g (w z) (w z') ≤ (Lw : ℝ≥0∞) * edist z z') →
        DiskWeakJordanTrace γ w → (∀ z : closedDisk, s ≤ dist (z : ℂ) c → w z = u z) →
        (∫ z in closedBall (0 : ℂ) 1 ∩ closedBall c s,
          diskMapEnergyDensity g (diskExtension u) z) ≤
          Λ * ∫ z in closedBall (0 : ℂ) 1 ∩ closedBall c s,
            diskMapEnergyDensity g (diskExtension w) z) →
      ∀ c ∈ sphere (0 : ℂ) 1, ∀ k : ℕ,
        (∫ z in closedBall c (s₀ / 2 ^ (K + k)) ∩ closedBall (0 : ℂ) 1,
          diskMapEnergyDensity g (diskExtension u) z) ≤ θ ^ k * ε₀ := by
  obtain ⟨ε₁, C, hε₁, hC, hhf⟩ := boundary_lens_hole_filling_qm_R7C g γ hγ
  set Kc : ℝ := Λ * C + 1 with hKc
  have hKc0 : 0 < Kc := by have := mul_nonneg hΛ hC; linarith
  obtain ⟨K, hK⟩ := dyadic_decay_of_hole_filling_R7C hε₁ hKc0 hE₀
  set s₀ : ℝ := min η (1 / 8) with hs₀
  have hs₀0 : 0 < s₀ := lt_min hη (by norm_num)
  have hs₀8 : s₀ ≤ 1 / 8 := min_le_right _ _
  have hs₀η : s₀ ≤ η := min_le_left _ _
  refine ⟨K, Kc / (1 + Kc), ε₁, s₀, by positivity, by rw [div_lt_one (by linarith)]; linarith,
    hε₁, hs₀0, hs₀8, ?_⟩
  intro u L hu ψ hψ htrace hmod hE hqm c hc k
  -- 旋转到 `−1`
  let ξ : Circle := ⟨-c, by
    apply mem_sphere_zero_iff_norm.mpr
    simpa only [mem_sphere, dist_zero_right, norm_neg] using hc⟩
  obtain ⟨α, hα⟩ := Circle.exp_surjective ξ
  set d := α / (2 * Real.pi) with hd
  have hζ : Circle.exp (2 * Real.pi * d) = ξ := by
    rw [hd, mul_div_cancel₀ _ (by positivity : 2 * Real.pi ≠ 0), hα]
  have hcenter : rotation (Circle.exp (2 * Real.pi * d)) (-1) = c := by
    rw [hζ, rotation_apply]
    change (-c) * (-1) = c
    ring
  set v := rotatedDiskMap u (Circle.exp (2 * Real.pi * d)) with hv
  set Ψ : CircleDeg1Lift := ψ * (CircleDeg1Lift.translate (Multiplicative.ofAdd d) : CircleDeg1Lift)
    with hΨ
  have hΨc : Continuous Ψ := ψ.continuous_mul_translate hψ d
  have hvL := riemannian_lipschitz_rotatedDiskMap g hu (Circle.exp (2 * Real.pi * d))
  have hvtr : ∀ t : ℝ, v (diskBoundary (t : loopCircle)) = γ ((Ψ t : ℝ) : loopCircle) :=
    rotatedDiskMap_trace_lift u γ ψ htrace d
  have hvqm := rotated_local_quasi_min_R7C g γ u hqm d
  have hlens : ∀ r : ℝ, (∫ z in boundaryLens r, diskMapEnergyDensity g (diskExtension v) z) =
      ∫ z in closedBall c r ∩ closedBall (0 : ℂ) 1, diskMapEnergyDensity g (diskExtension u) z := by
    intro r
    have h := integral_diskMapEnergyDensity_rotatedDiskMap_boundaryLens g u
      (Circle.exp (2 * Real.pi * d)) r
    rwa [hcenter] at h
  -- dyadic 序列
  set e : ℕ → ℝ := fun j =>
    ∫ z in boundaryLens (s₀ / 2 ^ j), diskMapEnergyDensity g (diskExtension v) z with hedef
  have hdi : IntegrableOn (diskMapEnergyDensity g (diskExtension v)) (closedBall (0 : ℂ) 1) :=
    integrable_diskMapEnergyDensity g hvL
  have hd0 : ∀ z, 0 ≤ diskMapEnergyDensity g (diskExtension v) z := fun z =>
    div_nonneg (add_nonneg (metric_inner_self_nonneg g _ _) (metric_inner_self_nonneg g _ _))
      (by norm_num)
  have hrad : ∀ j : ℕ, 0 < s₀ / 2 ^ j := fun j => by positivity
  have hradanti : Antitone fun j : ℕ => s₀ / 2 ^ j := fun i j hij =>
    div_le_div_of_nonneg_left hs₀0.le (by positivity) (pow_le_pow_right₀ (by norm_num) hij)
  have hradle : ∀ j : ℕ, s₀ / 2 ^ j ≤ s₀ := fun j => by
    simpa using hradanti (Nat.zero_le j)
  have he0 : ∀ j, 0 ≤ e j := fun j => integral_nonneg hd0
  have heanti : Antitone e := fun i j hij =>
    setIntegral_mono_set (hdi.mono_set inter_subset_right) (Eventually.of_forall hd0)
      (Eventually.of_forall fun z hz => ⟨closedBall_subset_closedBall (hradanti hij) hz.1, hz.2⟩)
  have heE : e 0 ≤ E₀ := by
    have hv0 : (∫ z in closedBall (0 : ℂ) 1, diskMapEnergyDensity g (diskExtension v) z) ≤ E₀ := by
      rw [hv, integral_diskMapEnergyDensity_rotatedDiskMap]
      exact hE
    exact (setIntegral_mono_set hdi (Eventually.of_forall hd0)
      (Eventually.of_forall inter_subset_right)).trans hv0
  have hdrop : ∀ j, e j - e (j + 1) < ε₁ → e (j + 1) ≤ Kc * (e j - e (j + 1)) := by
    intro j hj
    set s := s₀ / 2 ^ (j + 1) with hsdef
    have hstep : s₀ / 2 ^ j = 2 * s := by
      rw [hsdef, pow_succ]
      field_simp
    have hs : 0 < s := hrad (j + 1)
    have hs4 : s < 1 / 4 := by linarith [hradle (j + 1)]
    have hsub : boundaryLens s ⊆ boundaryLens (2 * s) := fun z hz =>
      ⟨closedBall_subset_closedBall (by linarith : s ≤ 2 * s) hz.1, hz.2⟩
    have hAnn : (∫ z in {z : ℂ | dist z (-1) ∈ Icc s (2 * s)} ∩ closedBall (0 : ℂ) 1,
        diskMapEnergyDensity g (diskExtension v) z) = e j - e (j + 1) := by
      have hm : MeasurableSet (boundaryLens s) :=
        (isClosed_closedBall.inter isClosed_closedBall).measurableSet
      have hsd := setIntegral_sdiff (μ := volume) (s := boundaryLens (2 * s)) (t := boundaryLens s)
        (f := diskMapEnergyDensity g (diskExtension v)) hm (hdi.mono_set inter_subset_right) hsub
      rw [integral_annulus_closedDisk_eq_boundaryLens_sdiff_R7C, hsd]
      simp only [hedef, hstep]
      rfl
    have hshort : ∀ ρ ∈ Ioo s (2 * s), Ψ (1 - Real.arccos (ρ / 2) / Real.pi) -
        Ψ (Real.arccos (ρ / 2) / Real.pi) ≤ 2 / 3 := by
      intro ρ hρ
      have hρ0 : 0 ≤ ρ := (hs.trans hρ.1).le
      have hρ2 : ρ ≤ 2 := by linarith [hρ.2]
      have hlen := one_sub_two_arccos_div_pi_le_R7C hρ0 hρ2
      have hapi : Real.arccos (ρ / 2) / Real.pi ≤ 1 / 2 := by
        rw [div_le_iff₀ Real.pi_pos]
        have := Real.arccos_le_pi_div_two.mpr (by positivity : 0 ≤ ρ / 2)
        linarith
      change ψ (d + (1 - Real.arccos (ρ / 2) / Real.pi)) -
        ψ (d + Real.arccos (ρ / 2) / Real.pi) ≤ 2 / 3
      apply hmod
      · linarith
      · have : ρ / 2 ≤ s₀ := by linarith [hρ.2, hradle (j + 1)]
        linarith
    have hqmρ : ∀ ρ ∈ Ioo s (2 * s), ∀ (w : C(closedDisk, N)) (Lw : ℝ≥0),
        (∀ z z', riemannianEDistOf g (w z) (w z') ≤ (Lw : ℝ≥0∞) * edist z z') →
        DiskWeakJordanTrace γ w → (∀ z : closedDisk, ρ ≤ dist (z : ℂ) (-1) → w z = v z) →
        (∫ z in closedBall (0 : ℂ) 1 ∩ closedBall (-1) ρ,
          diskMapEnergyDensity g (diskExtension v) z) ≤
          Λ * ∫ z in closedBall (0 : ℂ) 1 ∩ closedBall (-1) ρ,
            diskMapEnergyDensity g (diskExtension w) z :=
      fun ρ _ w Lw hwL hwΓ hwout => hvqm (-1) ρ w Lw hwL hwΓ hwout
    have h := hhf v L hvL Ψ hΨc hvtr s hs hs4 hshort (by rw [hAnn]; exact hj.le) Λ hΛ hqmρ
    rw [← hstep] at h
    change e (j + 1) ≤ Λ * C * (e j - e (j + 1)) at h
    have hdrop0 : 0 ≤ e j - e (j + 1) := sub_nonneg.mpr (heanti (Nat.le_succ j))
    nlinarith
  have hfinal := hK e heanti he0 heE hdrop k
  rw [hedef] at hfinal
  simp only at hfinal
  rwa [hlens] at hfinal

end DifferentialGeometry.Geometry
