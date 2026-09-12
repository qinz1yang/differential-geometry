import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornArmComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornEndAngle
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornRayApproximation

set_option autoImplicit false
noncomputable section
open Filter Manifold Set
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Toponogov

universe u

variable {W : Type u} [MetricSpace W] [ChartedSpace ThreeSpace W]
  [IsManifold I3 ∞ W] [SigmaCompactSpace W]

omit [ChartedSpace ThreeSpace W] [IsManifold I3 ∞ W] [SigmaCompactSpace W] in
theorem endComparisonAngle_eq_comparisonAngle {E : UniformSpace.Completion W} (a b : EndRay E)
    (s t : ℝ) :
    endComparisonAngle a b s t = comparisonAngle s t (dist (a.point s) (b.point t)) :=
  rfl

private theorem tendsto_comparisonAngle' {A : Type*} {l : Filter A} {a b c : A → ℝ}
    {a₀ b₀ c₀ : ℝ} (ha : Tendsto a l (𝓝 a₀)) (hb : Tendsto b l (𝓝 b₀))
    (hc : Tendsto c l (𝓝 c₀)) (ha₀ : 0 < a₀) (hb₀ : 0 < b₀) :
    Tendsto (fun i => comparisonAngle (a i) (b i) (c i)) l (𝓝 (comparisonAngle a₀ b₀ c₀)) := by
  simp only [comparisonAngle, comparisonCosine]
  exact Real.continuous_arccos.continuousAt.tendsto.comp
    (((ha.pow 2).add (hb.pow 2)).sub (hc.pow 2) |>.div
      ((tendsto_const_nhds.mul ha).mul hb) (by positivity))

omit [SigmaCompactSpace W] in
private theorem endComparisonAngle_mono_of_ray_approximation {g : SmoothRiemannianMetric I3 W}
    (H : FiniteHorn g) {inner : ℕ} {d : ℝ}
    (hcmp : ∀ (arm : Fin 2 → ℝ → W) (L : Fin 2 → ℝ), (∀ k, 0 < L k) →
      (∀ k, ContMDiffOn 𝓘(ℝ, ℝ) I3 ∞ (arm k) (Icc 0 (L k))) →
      (∀ k s, s ∈ Icc 0 (L k) → arm k s ∈ H.subend inner) →
      arm 0 0 = arm 1 0 →
      (∀ k s, s ∈ Icc 0 (L k) → ∀ t ∈ Icc 0 (L k), dist (arm k s) (arm k t) = |s - t|) →
      ∀ a1 a2 b1 b2 : ℝ, 0 < a1 → a1 ≤ a2 → a2 ≤ L 0 → 0 < b1 → b1 ≤ b2 → b2 ≤ L 1 →
        comparisonAngle a2 b2 (dist (arm 0 a2) (arm 1 b2)) ≤
          comparisonAngle a1 b1 (dist (arm 0 a1) (arm 1 b1)))
    (hrx : ∀ a b : EndRay H.endpoint, ∀ lo hi : Fin 2 → ℝ, (∀ k, 0 < lo k) →
      (∀ k, lo k ≤ hi k) → hi 0 ≤ a.length → hi 1 ≤ b.length → (∀ k, hi k ≤ d) →
      ∃ A : RayApproximation H a b lo hi, A.connector_index = inner)
    (a b : EndRay H.endpoint) {s₁ s₂ t₁ t₂ : ℝ}
    (hs₁ : 0 < s₁) (hs₁₂ : s₁ ≤ s₂) (hs₂ : s₂ ≤ min a.length d)
    (ht₁ : 0 < t₁) (ht₁₂ : t₁ ≤ t₂) (ht₂ : t₂ ≤ min b.length d) :
    endComparisonAngle a b s₂ t₂ ≤ endComparisonAngle a b s₁ t₁ := by
  let lo : Fin 2 → ℝ := ![s₁ / 2, t₁ / 2]
  let hi : Fin 2 → ℝ := ![min a.length d, min b.length d]
  have hlo : ∀ k, 0 < lo k := by
    intro k
    fin_cases k
    · show 0 < s₁ / 2
      linarith
    · show 0 < t₁ / 2
      linarith
  have hlohi : ∀ k, lo k ≤ hi k := by
    intro k
    fin_cases k
    · show s₁ / 2 ≤ min a.length d
      linarith
    · show t₁ / 2 ≤ min b.length d
      linarith
  have hia : hi 0 ≤ a.length := by
    show min a.length d ≤ a.length
    exact min_le_left _ _
  have hib : hi 1 ≤ b.length := by
    show min b.length d ≤ b.length
    exact min_le_left _ _
  have hid : ∀ k, hi k ≤ d := by
    intro k
    fin_cases k
    · show min a.length d ≤ d
      exact min_le_right _ _
    · show min b.length d ≤ d
      exact min_le_right _ _
  obtain ⟨A, hA⟩ := hrx a b lo hi hlo hlohi hia hib hid
  have hs₁I : s₁ ∈ Icc (lo 0) (hi 0) := by
    constructor
    · show s₁ / 2 ≤ s₁
      linarith
    · show s₁ ≤ min a.length d
      linarith
  have hs₂I : s₂ ∈ Icc (lo 0) (hi 0) := by
    constructor
    · show s₁ / 2 ≤ s₂
      linarith
    · show s₂ ≤ min a.length d
      linarith
  have ht₁I : t₁ ∈ Icc (lo 1) (hi 1) := by
    constructor
    · show t₁ / 2 ≤ t₁
      linarith
    · show t₁ ≤ min b.length d
      linarith
  have ht₂I : t₂ ∈ Icc (lo 1) (hi 1) := by
    constructor
    · show t₁ / 2 ≤ t₂
      linarith
    · show t₂ ≤ min b.length d
      linarith
  have heta_s : min s₁ t₁ / 4 ≤ s₁ / 2 := by linarith [min_le_left s₁ t₁, hs₁]
  have heta_t : min s₁ t₁ / 4 ≤ t₁ / 2 := by linarith [min_le_right s₁ t₁, ht₁]
  have hineq : ∀ᶠ i in atTop,
      comparisonAngle (A.parameter 0 i s₂) (A.parameter 1 i t₂)
          (dist (A.arm 0 i (A.parameter 0 i s₂)) (A.arm 1 i (A.parameter 1 i t₂))) ≤
        comparisonAngle (A.parameter 0 i s₁) (A.parameter 1 i t₁)
          (dist (A.arm 0 i (A.parameter 0 i s₁)) (A.arm 1 i (A.parameter 1 i t₁))) := by
    filter_upwards [A.uniform (min s₁ t₁ / 4) (by positivity)] with i hi
    have h₁ := hi.2 s₁ hs₁I t₁ ht₁I
    have h₂ := hi.2 s₂ hs₂I t₂ ht₂I
    have hsub : ∀ k s, s ∈ Icc 0 (A.length k i) → A.arm k i s ∈ H.subend inner := by
      intro k s hs
      have h := A.arm_buffer (subset_closure (A.arm_mem k i s hs))
      rwa [hA] at h
    have hσ₁ : 0 < A.parameter 0 i s₁ := by
      have h := (abs_lt.mp h₁.1).1
      linarith
    have hσ₁₂ : A.parameter 0 i s₁ ≤ A.parameter 0 i s₂ :=
      A.parameter_mono 0 i hs₁I hs₂I hs₁₂
    have hσ₂ : A.parameter 0 i s₂ ≤ A.length 0 i := (A.parameter_mem 0 i s₂ hs₂I).2
    have hτ₁ : 0 < A.parameter 1 i t₁ := by
      have h := (abs_lt.mp h₁.2.1).1
      linarith
    have hτ₁₂ : A.parameter 1 i t₁ ≤ A.parameter 1 i t₂ :=
      A.parameter_mono 1 i ht₁I ht₂I ht₁₂
    have hτ₂ : A.parameter 1 i t₂ ≤ A.length 1 i := (A.parameter_mem 1 i t₂ ht₂I).2
    exact hcmp (fun k => A.arm k i) (fun k => A.length k i) (fun k => A.length_pos k i)
      (fun k => A.arm_smooth k i) hsub
      (by rw [A.starts 0 i, A.starts 1 i])
      (fun k s hs t ht => A.minimizing k i s hs t ht)
      (A.parameter 0 i s₁) (A.parameter 0 i s₂) (A.parameter 1 i t₁) (A.parameter 1 i t₂)
      hσ₁ hσ₁₂ hσ₂ hτ₁ hτ₁₂ hτ₂
  have hlimσ : ∀ σ ∈ Icc (lo 0) (hi 0), Tendsto (fun i => A.parameter 0 i σ) atTop (𝓝 σ) := by
    intro σ hσ
    rw [Metric.tendsto_nhds]
    intro eta heta
    filter_upwards [A.uniform eta heta] with i hi
    simpa only [Real.dist_eq] using (hi.2 σ hσ t₁ ht₁I).1
  have hlimτ : ∀ σ ∈ Icc (lo 1) (hi 1), Tendsto (fun i => A.parameter 1 i σ) atTop (𝓝 σ) := by
    intro σ hσ
    rw [Metric.tendsto_nhds]
    intro eta heta
    filter_upwards [A.uniform eta heta] with i hi
    simpa only [Real.dist_eq] using (hi.2 s₁ hs₁I σ hσ).2.1
  have hlimΔ : Tendsto
      (fun i => dist (A.arm 0 i (A.parameter 0 i s₂)) (A.arm 1 i (A.parameter 1 i t₂)))
      atTop (𝓝 (dist (a.point s₂) (b.point t₂))) := by
    rw [Metric.tendsto_nhds]
    intro eta heta
    filter_upwards [A.uniform eta heta] with i hi
    simpa only [Real.dist_eq] using (hi.2 s₂ hs₂I t₂ ht₂I).2.2.2.2
  have hlim₂ := tendsto_comparisonAngle' (hlimσ s₂ hs₂I) (hlimτ t₂ ht₂I) hlimΔ
    (hs₁.trans_le hs₁₂) (ht₁.trans_le ht₁₂)
  have hlimΔ₁ : Tendsto
      (fun i => dist (A.arm 0 i (A.parameter 0 i s₁)) (A.arm 1 i (A.parameter 1 i t₁)))
      atTop (𝓝 (dist (a.point s₁) (b.point t₁))) := by
    rw [Metric.tendsto_nhds]
    intro eta heta
    filter_upwards [A.uniform eta heta] with i hi
    simpa only [Real.dist_eq] using (hi.2 s₁ hs₁I t₁ ht₁I).2.2.2.2
  have hlim₁ := tendsto_comparisonAngle' (hlimσ s₁ hs₁I) (hlimτ t₁ ht₁I) hlimΔ₁ hs₁ ht₁
  have hfinal : comparisonAngle s₂ t₂ (dist (a.point s₂) (b.point t₂)) ≤
      comparisonAngle s₁ t₁ (dist (a.point s₁) (b.point t₁)) :=
    le_of_tendsto_of_tendsto hlim₂ hlim₁ hineq
  rw [endComparisonAngle_eq_comparisonAngle a b s₂ t₂,
    endComparisonAngle_eq_comparisonAngle a b s₁ t₁]
  exact hfinal

theorem finite_horn_end_angle_monotone :
    ∃ H₀ : ℝ, 0 < H₀ ∧ ∀ (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g),
      H₀ ≤ H.collar_depth → ∃ d : ℝ, 0 < d ∧ ∀ a b : EndRay H.endpoint,
        CoordinatewiseNonincreasingOn (endRayLength H.endpoint d a) (endRayLength H.endpoint d b)
          (radialComparisonAngle (endRayFamily H.endpoint) a b) := by
  obtain ⟨H₁, hH₁, hcmp⟩ := exists_finiteHorn_arm_comparison_depth (W := W)
  obtain ⟨H₂, hH₂, happ⟩ := exists_finiteHorn_ray_approximation_in_subend_depth (W := W)
  refine ⟨max H₁ H₂, lt_max_of_lt_left hH₁, ?_⟩
  intro g H hdepth
  obtain ⟨inner, hinner⟩ := hcmp g H ((le_max_left H₁ H₂).trans hdepth)
  obtain ⟨d, hd, hlocal⟩ := happ g H ((le_max_right H₁ H₂).trans hdepth) inner
  have hfull : ∀ a b : EndRay H.endpoint,
      CoordinatewiseNonincreasingOn (min a.length d) (min b.length d) (endComparisonAngle a b) := by
    intro a b
    constructor
    · intro s₁ s₂ t hs₁ hs₂ ht hs₁₂
      exact endComparisonAngle_mono_of_ray_approximation H hinner hlocal a b
        hs₁.1 hs₁₂ hs₂.2 ht.1 le_rfl ht.2
    · intro s t₁ t₂ hs ht₁ ht₂ ht₁₂
      exact endComparisonAngle_mono_of_ray_approximation H hinner hlocal a b
        hs.1 le_rfl hs.2 ht₁.1 ht₁₂ ht₂.2
  refine ⟨d, hd, fun a b => ?_⟩
  have hfun : radialComparisonAngle (endRayFamily H.endpoint) a b = endComparisonAngle a b :=
    funext fun s => funext fun t => radialComparisonAngle_endRay a b s t
  rw [endRayLength, endRayLength, hfun]
  exact hfull a b

theorem finite_horn_end_angle_of_depth :
    ∃ H₀ : ℝ, 0 < H₀ ∧ ∀ (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g),
      H₀ ≤ H.collar_depth → Nonempty (EndAngles H) := by
  obtain ⟨H₀, hH₀, hmono⟩ := finite_horn_end_angle_monotone (W := W)
  refine ⟨H₀, hH₀, ?_⟩
  intro g H hdepth
  obtain ⟨d, hd, hmono'⟩ := hmono g H hdepth
  exact finite_horn_end_angle_of_monotone H d hd hmono'

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
