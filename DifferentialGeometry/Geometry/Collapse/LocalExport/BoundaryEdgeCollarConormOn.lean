import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEdgeBCutoff
import DifferentialGeometry.Geometry.Collapse.LocalExport.EdgeCollarConormApplications

/-!
# EDP03's collar co-norm on a regional edge family (S-BAUG-D, G16 part b)

The regional version of `EdgeFamily.collar_conorm_phys_EDP3`
(`Fibration/ActualEdgeBufferCollar.lean`)
on an `EdgeFamilyOn` over a complete σ-compact carrier (the revised edge family `edgeB` of the
boundary supply lives on `W°`): the compactness of the carrier is replaced by its completeness (the
proof is the closed one, through `EdgeChart.collar_conorm_anchor_EDP6` of the chart at the centre).

* `EdgeFamilyOn.collar_conorm_BAUGD`: at a point `x` of the chart ball `B(j, 100Δρ(j))` with
  `|η_j(x)| ≤ 10Δ` and `Δ/10 ≤ t(x) ≤ 10Δ` (`t = F/ρ`): `ρ(x)/ρ(j) ∈ [99/100, 101/100]`, and every
  unit `ξ ∈ ℝ²` has a vector `W` with `g(W, W) = ρ(j)²` and `⟪D(η_j, t)(x) W, ξ⟫ > 9/10`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology NNReal
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {β : ℕ → ℝ} {Δ σc μ b s b' s' ε γc βc : ℝ}
  {U₁ U₂ : Set X}

/-- **The collar co-norm of a regional edge chart at the anchor scale** (regional
`EdgeFamily.collar_conorm_EDP6`, same proof): anchor `j`, metric `ρ(j)⁻² g`, ratio
`ρ(x)/ρ(j) ∈ [99/100, 101/100]`, and at every `y ∈ B(x, 100ρ(x)/ρ(j))` the co-norm of `DJ(y)`
exceeds `9/10`. -/
theorem EdgeFamilyOn.collar_conorm_anchor_BAUGD
    (Fe : EdgeFamilyOn X g hmetric ρ hρ β Δ σc μ b s b' s' ε γc βc U₁ U₂) (hγc : 0 < γc)
    (hγc1 : γc ≤ 1 / 100) (hβc1 : βc ≤ 1 / 100000) {j : X} (hj : j ∈ Fe.centres) :
    let c := Fe.chart j hj
    let Fs := Fe.smoothing
    let hMc : CompleteSpace X := ‹CompleteSpace X›
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
  obtain ⟨W, hW, -, h9⟩ := c.collar_conorm_anchor_EDP6 hγc hγc1 hβc1 hx' hη hF1 hF2 hy ξ hξ
  exact ⟨W, hW, h9⟩

/-- **EDP03's collar co-norm in physical units on a regional edge family**: at a point `x` of the
chart ball with `|η_j(x)| ≤ 10Δ` and `Δ/10 ≤ t(x) ≤ 10Δ`, `ρ(x)/ρ(j) ∈ [99/100, 101/100]` and every
unit `ξ ∈ ℝ²` has `W` with `g(W, W) = ρ(j)²` and `⟪D(η_j, F/ρ)(x) W, ξ⟫ > 9/10`. -/
theorem EdgeFamilyOn.collar_conorm_BAUGD
    (Fe : EdgeFamilyOn X g hmetric ρ hρ β Δ σc μ b s b' s' ε γc βc U₁ U₂) (hγc : 0 < γc)
    (hγc1 : γc ≤ 1 / 100) (hβc1 : βc ≤ 1 / 100000) {j : X} (hj : j ∈ Fe.centres)
    {x : X} (hx : x ∈ ball j (100 * Δ * ρ j)) (hη : |Fe.coord_BAUGA j x| ≤ 10 * Δ)
    (ht1 : Δ / 10 ≤ Fe.smoothing x / ρ x) (ht2 : Fe.smoothing x / ρ x ≤ 10 * Δ) :
    (99 / 100 ≤ ρ x / ρ j ∧ ρ x / ρ j ≤ 101 / 100) ∧
    ∀ ξ : EuclideanSpace ℝ (Fin 2), ‖ξ‖ = 1 → ∃ W : TangentSpace 𝓘(ℝ, E3) x,
      g.inner x W W = ρ j ^ 2 ∧
      9 / 10 < inner ℝ (mvfderiv 𝓘(ℝ, E3)
        (edgeReferenceCoordinates ![Fe.coord_BAUGA j, fun z => Fe.smoothing z / ρ z]) x W) ξ := by
  have hrj := hρ j
  have hd : (ρ j)⁻¹ * dist x j < 100 * Δ := inv_mul_dist_lt_of_mem_ball_LC87 hrj hx
  have hq : ∀ y, Fe.smoothing y / ρ j / (ρ y / ρ j) = Fe.smoothing y / ρ y := fun y => by
    have := hρ y
    field_simp
  have hF1 : Δ / 10 ≤ Fe.smoothing x / ρ j / (ρ x / ρ j) := by
    rw [hq]
    exact ht1
  have hF2 : Fe.smoothing x / ρ j / (ρ x / ρ j) ≤ 10 * Δ := by
    rw [hq]
    exact ht2
  have h := Fe.collar_conorm_anchor_BAUGD hγc hγc1 hβc1 hj
  have hcoordeq := Fe.coord_BAUGA_of_mem hj
  rw [hcoordeq] at hη ⊢
  unfold EdgeFamilyOn.coord_BCG1 at hη ⊢
  set Fs := Fe.smoothing with hFsdef
  let c := Fe.chart j hj
  let hMc : CompleteSpace X := ‹CompleteSpace X›
  let _ := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let _ := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let _ : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let _ : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let _ : CompleteSpace X := (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
  have hJ : edgeReferenceCoordinates ![c.coord, fun z => Fs z / ρ j / (ρ z / ρ j)] =
      edgeReferenceCoordinates ![c.coord, fun z => Fs z / ρ z] := by
    simp_rw [hq]
  have hη' : |c.coord x| ≤ 10 * Δ := hη
  have hxR : x ∈ ball j (100 * Δ) := hd
  obtain ⟨hratio, hco⟩ := h x hxR hη' hF1 hF2
  have hxx : x ∈ ball x (100 * (ρ x / ρ j)) :=
    mem_ball_self (mul_pos (by norm_num) (div_pos (hρ x) hrj))
  refine ⟨hratio, fun ξ hξ => ?_⟩
  obtain ⟨W, hW, h9⟩ := hco x hxx ξ hξ
  refine ⟨W, ?_, ?_⟩
  · have hw' : (ρ j)⁻¹ ^ 2 * g.inner x W W = 1 := hW
    have hr2 : 0 < ρ j ^ 2 := by positivity
    field_simp at hw'
    linarith
  · rw [← hJ]
    exact h9

end DifferentialGeometry.Geometry.Collapse
