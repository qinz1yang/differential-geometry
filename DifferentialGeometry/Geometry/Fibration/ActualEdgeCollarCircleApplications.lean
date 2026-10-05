import DifferentialGeometry.Geometry.Fibration.ActualEdgeCollarCircle
import DifferentialGeometry.Geometry.Collapse.LocalExport.EdgeCollarConorm

/-!
# EDP06, E-free step on the final family, and its binding on LC20's tail

Lane C14-EDP6. Blueprint 207B, EDP06 (B:7103–7108).

* `edp06_collar_circle_C14` (kernel on `LocalChartPacketsC14`): a point of EDP06's band at an edge
  centre `j` (`d(x, j) < 100Δρ(j)`, `|η_j(x)| < 4.01Δ`, `|F(x)/ρ(x) − 4Δ| < h ≤ 1/1000`, `Δ ≥ 1`)
  with the row's no-three input is two-stratum and lies at distance `< 2ρ(a)` from a circle
  centre `a` with `‖η_a(x)‖ < 2(1 + γ)`, as soon as `3βc ≤ β 2 < 1`, `0 ≤ γ`.
* `eventually_edp06_collar_circle_EDP6` (binding): on LC20's eventual tail (the hypotheses of
  `eventually_mem_scaledSplittingStratum_two_of_plane_approx`), for every scale `ρ` in LC02's window
  (which the C14 producer outputs next to the family), every LC16 threshold with `β 3` below LC18's
  threshold and every family `LocalChartPacketsC14` on that scale, the same conclusion holds with no
  no-three hypothesis.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology NNReal
open DifferentialGeometry.Geometry.Riemannian
open GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

section Kernel

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {β : ℕ → ℝ} {Λ : ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}

/-- **EDP06's collar → circle chart step on the final family** (B:7103–7108, E-free): a point of
EDP06's band at an edge centre, with the row's no-three input, is two-stratum and lies in a circle
chart with `‖η_a(x)‖ < 2(1 + γ)`. -/
theorem edp06_collar_circle_C14
    (L : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz) (h3βc : 3 * βc ≤ β 2) (hβ2 : β 2 < 1) (hγ : 0 ≤ γ) (hΔ : 1 ≤ Δ) {h : ℝ}
    (hh : h ≤ 1 / 1000) {j : X} (hj : j ∈ L.edge.centres) {x : X}
    (hx : dist x j < 100 * Δ * ρ j)
    (hη : let c := L.edge.chart j hj
      let hMc : CompleteSpace X := complete_of_compact
      letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
      letI := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
      letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
        radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
      letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
        radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
      letI : CompleteSpace X :=
        (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
      |c.coord x| < 401 / 100 * Δ)
    (ht : |L.edge.smoothing x / ρ x - 4 * Δ| < h)
    (h3 : ¬ @HasEuclideanSplitting.{0, 0} X (mX.rescale (ρ x)⁻¹ (inv_pos.mpr (hρ x))) x 3 (β 3)) :
    x ∈ scaledSplittingStratum.{0, 0} ρ hρ β 2 ∧
      ∃ a, ∃ ha : a ∈ L.circle.centres, dist x a < 2 * ρ a ∧
        (let c := L.circle.chart a ha
         letI := mX.rescale (ρ a)⁻¹ (inv_pos.mpr (hρ a))
         ‖c.coord x‖ < 2 * (1 + γ)) := by
  obtain ⟨hη', hF1, hF2⟩ := edp06_band_mem_band_EDP6 hΔ hh hη ht
  have h2 := L.edge.collar_two_stratum_EDP6 h3βc hβ2 hj hx hη' hF1 hF2 h3
  exact ⟨h2, L.circle_chart_of_two_EDP6 hγ h2⟩

end Kernel

/-- **EDP06's collar → circle chart step on LC20's tail** (binding, no no-three hypothesis): for the
standing closed sequence, on one tail, every family `LocalChartPacketsC14` on a scale in LC02's
window (with `β 3` below LC18's threshold, `3βc ≤ β 2 < 1`, `0 ≤ γ`, `Δ ≥ 1`) has: every point of
EDP06's band at an edge centre is two-stratum and lies in a circle chart with
`‖η_a(x)‖ < 2(1 + γ)`. -/
theorem eventually_edp06_collar_circle_EDP6 {Λ₀ : ℝ} (hΛ₀ : 0 < Λ₀) :
    ∃ w₀ : ℝ, 0 < w₀ ∧ ∀ w : ℝ, 0 < w → w < w₀ → w < 4 * Real.pi / 3 →
      ∀ (Y : ℕ → Type) [mY : ∀ i, MetricSpace (Y i)] [∀ i, ChartedSpace E3 (Y i)]
        [∀ i, IsManifold 𝓘(ℝ, E3) ∞ (Y i)] [∀ i, CompactSpace (Y i)]
        (gY : ∀ i, SmoothRiemannianMetric 𝓘(ℝ, E3) (Y i))
        (hmY : ∀ i a b, riemannianEDistOf (gY i) a b = ENNReal.ofReal (dist a b)),
      ∀ α : ℕ → ℝ, Tendsto α atTop atTop →
      (∀ i (p : Y i), ENNReal.ofReal (α i * firstVolumeScale (gY i) p (α i)⁻¹) ≤
        curvatureRadius (gY i) p) →
      ∀ᶠ i in atTop, ∀ (ρY : Y i → ℝ) (hρY : ∀ y, 0 < ρY y),
        (∀ p, firstVolumeScale (gY i) p w / 2 ≤ ρY p ∧
          ρY p ≤ 2 * firstVolumeScale (gY i) p (w / (2 * (1 + 2 * Λ₀⁻¹) ^ 3))) →
        ∀ (Λ : ℝ) (βY : ℕ → ℝ) (Δ σs : ℝ) (K : ℕ)
          (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ),
        βY 3 ≤ threeSplittingExclusionThreshold.{0, 0} → 3 * βc ≤ βY 2 → βY 2 < 1 → 0 ≤ γ →
        1 ≤ Δ →
        ∀ L : LocalChartPacketsC14 (Y i) (gY i) (hmY i) ρY hρY Λ βY Δ σs K σc μ b s b' s' ε γc
          βc Lmax τ γ δ εr e T V vs ζ Λz,
        ∀ h : ℝ, h ≤ 1 / 1000 → ∀ j (hj : j ∈ L.edge.centres) (x : Y i),
        dist x j < 100 * Δ * ρY j →
        (let c := L.edge.chart j hj
         let hMc : CompleteSpace (Y i) := complete_of_compact
         letI := (mY i).rescale (ρY j)⁻¹ (inv_pos.mpr (hρY j))
         letI := radialScaledBundle (gY i) (ρY j)⁻¹ (inv_pos.mpr (hρY j))
         letI : IsContinuousRiemannianBundle E3 (fun x : Y i => TangentSpace 𝓘(ℝ, E3) x) :=
           radialScaledContinuous (gY i) (ρY j)⁻¹ (inv_pos.mpr (hρY j))
         letI : IsRiemannianManifold 𝓘(ℝ, E3) (Y i) :=
           radialScaledManifold (m := mY i) (gY i) (hmY i) (ρY j)⁻¹ (inv_pos.mpr (hρY j))
         letI : CompleteSpace (Y i) :=
           ((mY i).rescale_completeSpace_iff (ρY j)⁻¹ (inv_pos.mpr (hρY j))).mpr hMc
         |c.coord x| < 401 / 100 * Δ) →
        |L.edge.smoothing x / ρY x - 4 * Δ| < h →
        x ∈ scaledSplittingStratum.{0, 0} ρY hρY βY 2 ∧
          ∃ a, ∃ ha : a ∈ L.circle.centres, dist x a < 2 * ρY a ∧
            (let c := L.circle.chart a ha
             letI := (mY i).rescale (ρY a)⁻¹ (inv_pos.mpr (hρY a))
             ‖c.coord x‖ < 2 * (1 + γ)) := by
  obtain ⟨w₀, hw₀, htail⟩ :=
    eventually_mem_scaledSplittingStratum_two_of_plane_approx.{0, 0, 0, 0} (I := 𝓘(ℝ, E3))
      finrank_euclideanSpace_fin hΛ₀
  refine ⟨w₀, hw₀, ?_⟩
  intro w hw hww hwc Y mY _ _ _ gY hmY α hα hstand
  filter_upwards [htail w hw hww hwc Y gY hmY α hα hstand] with i hi
  intro ρY hρY hwin Λ βY Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz hβ3 h3βc
    hβ2 hγ hΔ L h hh j hj x hx hη ht
  obtain ⟨hη', hF1, hF2⟩ := edp06_band_mem_band_EDP6 hΔ hh hη ht
  have h2 : x ∈ scaledSplittingStratum.{0, 0} ρY hρY βY 2 :=
    hi ρY hρY βY hβ3 x (hwin x).1 (hwin x).2
      (L.edge.collar_plane_EDP6 h3βc hβ2 hj hx hη' hF1 hF2)
  exact ⟨h2, L.circle_chart_of_two_EDP6 hγ h2⟩

end DifferentialGeometry.Geometry.Collapse
