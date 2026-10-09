import DifferentialGeometry.Geometry.Collapse.LocalExport.EdgeCollarConorm
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsC14

/-!
# The collar co-norm on the edge charts of the final family (EDP03 / EDP04 / EDP06)

Lane C14-EDP6 (review 50 item B; blueprint 207B EDP03 B:6862–6865, B:6938–6946).

* `EdgeFamily.collar_conorm_EDP6`: for the edge chart at an edge centre `j` (the ANCHOR, normalized
  there: metric `ρ(j)⁻² g = R_j⁻² g`, scale `ρ/ρ(j)`, smoothing `F/ρ(j)`), on the chart's collar
  band (`x ∈ B(j, 100Δ)` normalized, `|η_j(x)| ≤ 10Δ`, `Δ/10 ≤ t(x) ≤ 10Δ`, `t = F/ρ`): the ratio
  `ρ(x)/ρ(j)` lies in `[99/100, 101/100]`, and at every `y ∈ B(x, 100ρ(x)/ρ(j))` every unit
  `ξ ∈ ℝ²` has an `R_j⁻² g`-unit `W` with
  `⟪DJ(y) W, ξ⟫ > (1 − (γc + βc))/(ρ(x)/ρ(j)) > 9/10`, `J = (η_j, F/ρ)` (the SAME pair).
* `edp03_collar_conorm_C14` (consumer, on `LocalChartPacketsC14`): EDP03's ".9" on its collar
  `|η_j| < 5Δ`, `3.9Δ < t < 4.1Δ`, at the point itself, and the surjectivity of `DJ(x)`.
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

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {β : ℕ → ℝ} {Δ σc μ b s b' s' ε γc βc : ℝ}

/-- **The collar co-norm of an LC87 edge chart at the anchor scale** (review 50 B1–B3): anchor `j`,
metric `ρ(j)⁻² g`, explicit ratio `ρ(x)/ρ(j) ∈ [99/100, 101/100]`, point set = the chart's collar
band; at every `y ∈ B(x, 100ρ(x)/ρ(j))` the surjective co-norm of `DJ(y)` exceeds
`(1 − (γc + βc))/(ρ(x)/ρ(j)) > 9/10`. -/
theorem EdgeFamily.collar_conorm_EDP6
    (Fe : EdgeFamily X g hmetric ρ hρ β Δ σc μ b s b' s' ε γc βc) (hγc : 0 < γc)
    (hγc1 : γc ≤ 1 / 100) (hβc1 : βc ≤ 1 / 100000) {j : X} (hj : j ∈ Fe.centres) :
    let c := Fe.chart j hj
    let Fs := Fe.smoothing
    let hMc : CompleteSpace X := complete_of_compact
    letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
      radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
      radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI : CompleteSpace X :=
      (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
    let gR : SmoothRiemannianMetric 𝓘(ℝ, E3) X :=
      scaleMetric ((ρ j)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hρ j)) 2) g
    ∀ x ∈ ball j (100 * Δ), |c.coord x| ≤ 10 * Δ →
      Δ / 10 ≤ Fs x / ρ j / (ρ x / ρ j) → Fs x / ρ j / (ρ x / ρ j) ≤ 10 * Δ →
      (99 / 100 ≤ ρ x / ρ j ∧ ρ x / ρ j ≤ 101 / 100) ∧
      ∀ y ∈ ball x (100 * (ρ x / ρ j)), ∀ ξ : EuclideanSpace ℝ (Fin 2), ‖ξ‖ = 1 →
        ∃ W : TangentSpace 𝓘(ℝ, E3) y, gR.inner y W W = 1 ∧
          (1 - (γc + βc)) / (ρ x / ρ j) < inner ℝ (mvfderiv (I := 𝓘(ℝ, E3))
            (edgeReferenceCoordinates ![c.coord, fun z => Fs z / ρ j / (ρ z / ρ j)]) y W) ξ ∧
          9 / 10 < inner ℝ (mvfderiv (I := 𝓘(ℝ, E3))
            (edgeReferenceCoordinates ![c.coord, fun z => Fs z / ρ j / (ρ z / ρ j)]) y W) ξ := by
  have hcc0 := Fe.chart_center j hj
  intro c Fs hMc gR x hx hη hF1 hF2
  let _ := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let _ := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let _ : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let _ : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let _ : CompleteSpace X := (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
  have hcc : c.center = j := hcc0
  have hx' : x ∈ ball c.center (100 * Δ) := by
    rw [hcc]
    exact hx
  refine ⟨c.collar_ratio_EDP6 hx' hη hF1 hF2, fun y hy ξ hξ => ?_⟩
  exact c.collar_conorm_anchor_EDP6 hγc hγc1 hβc1 hx' hη hF1 hF2 hy ξ hξ

variable {Λ : ℝ} {Δ σs : ℝ} {K : ℕ} {Lmax τ γ δ εr e T V vs ζ Λz : ℝ}

/-- **EDP03's collar co-norm on the final family** (consumer): at an edge centre `j` of
`LocalChartPacketsC14` and a point `x` of EDP03's collar (`x ∈ B(j, 100Δ)` normalized,
`|η_j(x)| < 5Δ`, `3.9Δ < t(x) < 4.1Δ`), `DJ(x)` is onto and every unit `ξ` has an `R_j⁻² g`-unit `W`
with `⟪DJ(x) W, ξ⟫ > 9/10` (blueprint B:6862–6865). -/
theorem edp03_collar_conorm_C14
    (L : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100) (hβc1 : βc ≤ 1 / 100000) (hΔ : 0 < Δ)
    {j : X} (hj : j ∈ L.edge.centres) :
    let c := L.edge.chart j hj
    let Fs := L.edge.smoothing
    let hMc : CompleteSpace X := complete_of_compact
    letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
      radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
      radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI : CompleteSpace X :=
      (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
    let gR : SmoothRiemannianMetric 𝓘(ℝ, E3) X :=
      scaleMetric ((ρ j)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hρ j)) 2) g
    ∀ x ∈ ball j (100 * Δ), |c.coord x| < 5 * Δ →
      39 / 10 * Δ < Fs x / ρ j / (ρ x / ρ j) → Fs x / ρ j / (ρ x / ρ j) < 41 / 10 * Δ →
      Function.Surjective (mvfderiv (I := 𝓘(ℝ, E3))
        (edgeReferenceCoordinates ![c.coord, fun z => Fs z / ρ j / (ρ z / ρ j)]) x) ∧
      ∀ ξ : EuclideanSpace ℝ (Fin 2), ‖ξ‖ = 1 →
        ∃ W : TangentSpace 𝓘(ℝ, E3) x, gR.inner x W W = 1 ∧
          9 / 10 < inner ℝ (mvfderiv (I := 𝓘(ℝ, E3))
            (edgeReferenceCoordinates ![c.coord, fun z => Fs z / ρ j / (ρ z / ρ j)]) x W) ξ := by
  intro c Fs hMc gR x hx hη ht1 ht2
  obtain ⟨hη', hF1, hF2⟩ := edp03_collar_mem_band_EDP6 hΔ hη ht1 ht2
  obtain ⟨-, h⟩ := L.edge.collar_conorm_EDP6 hγc hγc1 hβc1 hj x hx hη' hF1 hF2
  let _ := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let _ := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let _ : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let _ : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let _ : CompleteSpace X := (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
  have hxx : x ∈ ball x (100 * (ρ x / ρ j)) :=
    mem_ball_self (mul_pos (by norm_num) (div_pos (hρ x) (hρ j)))
  have hco : ∀ ξ : EuclideanSpace ℝ (Fin 2), ‖ξ‖ = 1 →
      ∃ W : TangentSpace 𝓘(ℝ, E3) x, gR.inner x W W = 1 ∧
        9 / 10 < inner ℝ (mvfderiv (I := 𝓘(ℝ, E3))
          (edgeReferenceCoordinates ![c.coord, fun z => Fs z / ρ j / (ρ z / ρ j)]) x W) ξ :=
    fun ξ hξ => by
      obtain ⟨W, hW, -, h9⟩ := h x hxx ξ hξ
      exact ⟨W, hW, h9⟩
  refine ⟨?_, hco⟩
  refine surjective_of_conorm_pos_EDP6 (mvfderiv (I := 𝓘(ℝ, E3))
    (edgeReferenceCoordinates ![c.coord, fun z => Fs z / ρ j / (ρ z / ρ j)]) x).toLinearMap
    (fun ξ hξ => ?_)
  obtain ⟨W, -, h9⟩ := hco ξ hξ
  exact ⟨W, by
    change 0 < inner ℝ (mvfderiv (I := 𝓘(ℝ, E3))
      (edgeReferenceCoordinates ![c.coord, fun z => Fs z / ρ j / (ρ z / ρ j)]) x W) ξ
    linarith⟩

end DifferentialGeometry.Geometry.Collapse
