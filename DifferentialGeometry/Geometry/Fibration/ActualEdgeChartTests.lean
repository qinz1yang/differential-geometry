import DifferentialGeometry.Geometry.Fibration.ActualEdgeRawAlignment
import DifferentialGeometry.Geometry.Fibration.ActualBlockBudgets
import DifferentialGeometry.Geometry.Collapse.SublevelCore.ScaledMinimizingDirections
import DifferentialGeometry.Geometry.Collapse.RiemannianOutwardPoint
import DifferentialGeometry.Analysis.InnerProductSpace.DirectionalSaturation
import DifferentialGeometry.Geometry.Metric.Approximation.EndpointProductLifts

/-!
# EGP04 tools: the original edge and slim tests at a common reference scale

Blueprint `master207B.tex`, EGP04 (`lem:fibration-edge-actual-comparison`, B:4943–5040). The
original derivative tests of an edge chart (LC84/LFR19, `EdgeChart.test`) and of a slim chart
(`SlimChart.test`) live in the chart's own normalized metric `ρ(j)⁻¹ d`, `ρ(j)⁻² g`. EGP04 runs
both tests of two charts along ONE minimizing direction of the reference metric `R⁻² g`.

* `intrinsicGeodesic_radialScaled_swap_KC2` (generic): the geodesic of `R₂⁻² g` with velocity
  `(R₂/R₁) v` at time `(R₁/R₂) t` is the geodesic of `R₁⁻² g` with velocity `v` at time `t`
  (both are the geodesic of `g`, `intrinsicGeodesic_radialScaled_eq`, reparametrized).
* `actual_geodesic_swap_KC2`: the same on a compact `X` with `riemannianEDistOf g = dist`, written
  with the chart blocks of the LC87 family.
* `EdgeFamily.value_KC2`, `EdgeFamily.test_at_scale_KC2`, `SlimCentre.test_at_scale_KC2`: LFR19's
  value error and the original tests in physical form, along a direction of the reference metric
  `R⁻² g` (`R` arbitrary, e.g. `R = ρ(i)`).
* `exists_minimizing_direction_KC2`: a unit minimizing direction of `R⁻² g` (Hopf–Rinow).
* `abs_sub_le_of_common_unit_KC2`: FC15's Riesz step for two covectors on `T_x X` with the norm of
  `c g`, stated without a norm instance.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology InnerProductSpace
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian.Exponential

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

section Swap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [m : MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [hM : CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

/-- **Change of reference scale for intrinsic geodesics.** -/
theorem intrinsicGeodesic_radialScaled_swap_KC2 (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) {R₁ R₂ : ℝ} (h₁ : 0 < R₁) (h₂ : 0 < R₂) (p : M)
    (v : TangentSpace I p) (t : ℝ) :
    (have hmetric := riemannianEDistOf_eq_ofReal_dist g hEnorm
    letI := m.rescale R₂⁻¹ (inv_pos.mpr h₂)
    letI := radialScaledBundle g R₂⁻¹ (inv_pos.mpr h₂)
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      radialScaledContinuous g R₂⁻¹ (inv_pos.mpr h₂)
    letI : IsRiemannianManifold I M := radialScaledManifold (m := m) g hmetric R₂⁻¹ (inv_pos.mpr h₂)
    letI : CompleteSpace M := (m.rescale_completeSpace_iff R₂⁻¹ (inv_pos.mpr h₂)).mpr hM
    let gR : SmoothRiemannianMetric I M := scaleMetric (R₂⁻¹ ^ 2) (pow_pos (inv_pos.mpr h₂) 2) g
    have hnR : IsMetricNorm (I := I) (M := M) gR := isMetricNorm_of_riemannianBundle gR
    intrinsicGeodesic (I := I) gR hnR p ((R₂ / R₁) • v) (R₁ / R₂ * t)) =
      (have hmetric := riemannianEDistOf_eq_ofReal_dist g hEnorm
      letI := m.rescale R₁⁻¹ (inv_pos.mpr h₁)
      letI := radialScaledBundle g R₁⁻¹ (inv_pos.mpr h₁)
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        radialScaledContinuous g R₁⁻¹ (inv_pos.mpr h₁)
      letI : IsRiemannianManifold I M :=
        radialScaledManifold (m := m) g hmetric R₁⁻¹ (inv_pos.mpr h₁)
      letI : CompleteSpace M := (m.rescale_completeSpace_iff R₁⁻¹ (inv_pos.mpr h₁)).mpr hM
      let gR : SmoothRiemannianMetric I M :=
        scaleMetric (R₁⁻¹ ^ 2) (pow_pos (inv_pos.mpr h₁) 2) g
      have hnR : IsMetricNorm (I := I) (M := M) gR := isMetricNorm_of_riemannianBundle gR
      intrinsicGeodesic (I := I) gR hnR p v t) := by
  have e₂ := congrFun (intrinsicGeodesic_radialScaled_eq g hEnorm h₂ p ((R₂ / R₁) • v))
    (R₁ / R₂ * t)
  have e₁ := congrFun (intrinsicGeodesic_radialScaled_eq g hEnorm h₁ p v) t
  have hs := intrinsicGeo_smul_apply (I := I) g hEnorm p v (R₂ / R₁) (R₁ / R₂ * t)
  have hc : R₂ / R₁ * (R₁ / R₂ * t) = t := by field_simp
  rw [hc] at hs
  exact e₂.trans (hs.trans e₁.symm)

end Swap

attribute [local instance] nezero_finrank_euclideanThree_LC87

section Actual

universe u

variable {X : Type u} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p}

/-- **Change of reference scale on an actual compact manifold** (the chart blocks of LC87). -/
theorem actual_geodesic_swap_KC2 (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
    (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)) {R₁ R₂ : ℝ}
    (h₁ : 0 < R₁) (h₂ : 0 < R₂) (p : X) (v : TangentSpace 𝓘(ℝ, E3) p) (t : ℝ) :
    (let hMc : CompleteSpace X := complete_of_compact
    letI := mX.rescale R₂⁻¹ (inv_pos.mpr h₂)
    letI := radialScaledBundle g R₂⁻¹ (inv_pos.mpr h₂)
    letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
      radialScaledContinuous g R₂⁻¹ (inv_pos.mpr h₂)
    letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
      radialScaledManifold (m := mX) g hmetric R₂⁻¹ (inv_pos.mpr h₂)
    letI : CompleteSpace X := (mX.rescale_completeSpace_iff R₂⁻¹ (inv_pos.mpr h₂)).mpr hMc
    let gR : SmoothRiemannianMetric 𝓘(ℝ, E3) X :=
      scaleMetric (R₂⁻¹ ^ 2) (pow_pos (inv_pos.mpr h₂) 2) g
    have hnR : IsMetricNorm (I := 𝓘(ℝ, E3)) (M := X) gR := isMetricNorm_of_riemannianBundle gR
    intrinsicGeodesic gR hnR p ((R₂ / R₁) • v) (R₁ / R₂ * t)) =
      (let hMc : CompleteSpace X := complete_of_compact
      letI := mX.rescale R₁⁻¹ (inv_pos.mpr h₁)
      letI := radialScaledBundle g R₁⁻¹ (inv_pos.mpr h₁)
      letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
        radialScaledContinuous g R₁⁻¹ (inv_pos.mpr h₁)
      letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
        radialScaledManifold (m := mX) g hmetric R₁⁻¹ (inv_pos.mpr h₁)
      letI : CompleteSpace X := (mX.rescale_completeSpace_iff R₁⁻¹ (inv_pos.mpr h₁)).mpr hMc
      let gR : SmoothRiemannianMetric 𝓘(ℝ, E3) X :=
        scaleMetric (R₁⁻¹ ^ 2) (pow_pos (inv_pos.mpr h₁) 2) g
      have hnR : IsMetricNorm (I := 𝓘(ℝ, E3)) (M := X) gR := isMetricNorm_of_riemannianBundle gR
      intrinsicGeodesic gR hnR p v t) := by
  let bP : RiemannianBundle (fun x : X => TangentSpace 𝓘(ℝ, E3) x) := ⟨g.toRiemannianMetric⟩
  have cP : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  have rP : IsRiemannianManifold 𝓘(ℝ, E3) X := ⟨fun a b => by
    change edist a b = riemannianEDistOf g a b
    rw [edist_dist, hmetric]⟩
  have kP : CompleteSpace X := complete_of_compact
  have hEn : IsMetricNorm (I := 𝓘(ℝ, E3)) g := isMetricNorm_of_riemannianBundle g
  exact intrinsicGeodesic_radialScaled_swap_KC2 g hEn h₁ h₂ p v t

variable {β : ℕ → ℝ} {Δ σc μ b s b' s' ε γc βc : ℝ}

/-- **LFR19's value error of the actual edge chart** (physical form): on `B(j, 100Δρ(j))`,
`|η_j − u_j| < μΔ`. -/
theorem EdgeFamily.value_KC2 (F : EdgeFamily X g hmetric ρ hρ β Δ σc μ b s b' s' ε γc βc)
    {j : X} (hj : j ∈ F.centres) {x : X} (hx : x ∈ ball j (100 * Δ * ρ j)) :
    |F.coord j x - egpRaw F j x| < μ * Δ := by
  have hc := F.chart_center j hj
  have hrj := hρ j
  have hd : (ρ j)⁻¹ * dist x j < 100 * Δ := inv_mul_dist_lt_of_mem_ball_LC87 hrj hx
  have hraw : egpRaw F j x = egpChartRaw F hj x := egpRaw_of_mem F hj x
  rw [hraw]
  unfold EdgeFamily.coord
  rw [dite_eq_left hj]
  let C := F.chart j hj
  let hMc : CompleteSpace X := complete_of_compact
  let mR : MetricSpace X := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let bR := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let cR : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let iR : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let kR : CompleteSpace X := (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
  have hc' : C.center = j := hc
  let _ := C.instY
  have hmem : x ∈ ball C.center (100 * Δ) := by
    rw [hc']
    exact hd
  exact C.value x hmem

/-- **The original edge test at a reference scale `R`.** For `x ∈ B(j, 100Δρ(j))`,
`y ∈ B(j, 1000Δρ(j))` with `d(x, y) > 100Δρ(j)`, and a unit vector `v` of `R⁻² g` whose geodesic
of `R⁻² g` reaches `y` at time `R⁻¹ d(x, y)`:
`|(ρ(j)/R) dη_j(v) − (ρ(j)/R)(u_j(y) − u_j(x))/(R⁻¹ d(x, y))| < σ`. -/
theorem EdgeFamily.test_at_scale_KC2 (F : EdgeFamily X g hmetric ρ hρ β Δ σc μ b s b' s' ε γc βc)
    {j : X} (hj : j ∈ F.centres) {R : ℝ} (hR : 0 < R) {x y : X}
    (hx : x ∈ ball j (100 * Δ * ρ j)) (hy : y ∈ ball j (1000 * Δ * ρ j))
    (hxy : 100 * Δ * ρ j < dist x y) (v : TangentSpace 𝓘(ℝ, E3) x)
    (hv : R⁻¹ ^ 2 * g.inner x v v = 1)
    (hgeo : let hMc : CompleteSpace X := complete_of_compact
      letI := mX.rescale R⁻¹ (inv_pos.mpr hR)
      letI := radialScaledBundle g R⁻¹ (inv_pos.mpr hR)
      letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
        radialScaledContinuous g R⁻¹ (inv_pos.mpr hR)
      letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
        radialScaledManifold (m := mX) g hmetric R⁻¹ (inv_pos.mpr hR)
      letI : CompleteSpace X := (mX.rescale_completeSpace_iff R⁻¹ (inv_pos.mpr hR)).mpr hMc
      let gR : SmoothRiemannianMetric 𝓘(ℝ, E3) X :=
        scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) g
      have hnR : IsMetricNorm (I := 𝓘(ℝ, E3)) (M := X) gR := isMetricNorm_of_riemannianBundle gR
      intrinsicGeodesic gR hnR x v (dist x y) = y) :
    |ρ j / R * mvfderiv 𝓘(ℝ, E3) (F.coord j) x v -
      ρ j / R * (egpRaw F j y - egpRaw F j x) / (R⁻¹ * dist x y)| < σc := by
  have hc := F.chart_center j hj
  have hrj := hρ j
  -- the geodesic of the chart metric
  have hswap := actual_geodesic_swap_KC2 g hmetric hR hrj x v (R⁻¹ * dist x y)
  have ht : R / ρ j * (R⁻¹ * dist x y) = (ρ j)⁻¹ * dist x y := by field_simp
  rw [ht] at hswap
  have hgeoj := hswap.trans hgeo
  have hxj : (ρ j)⁻¹ * dist x j < 100 * Δ := inv_mul_dist_lt_of_mem_ball_LC87 hrj hx
  have hyj : (ρ j)⁻¹ * dist y j < 1000 * Δ := inv_mul_dist_lt_of_mem_ball_LC87 hrj hy
  have hxyj : 100 * Δ < (ρ j)⁻¹ * dist x y := by
    rw [lt_inv_mul_iff₀ hrj]
    linarith
  have hwj : (scaleMetric ((ρ j)⁻¹ ^ 2) (pow_pos (inv_pos.mpr hrj) 2) g).inner x
      ((ρ j / R) • v) ((ρ j / R) • v) = 1 := by
    rw [scaleMetric_inner, map_smul, map_smul, smul_apply, smul_eq_mul, smul_eq_mul, ← hv]
    field_simp
  have hrawx : egpRaw F j x = egpChartRaw F hj x := egpRaw_of_mem F hj x
  have hrawy : egpRaw F j y = egpChartRaw F hj y := egpRaw_of_mem F hj y
  have hcoord : F.coord j = (let C := F.chart j hj
      let hMc : CompleteSpace X := complete_of_compact
      letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
      letI := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
      letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
        radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
      letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
        radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
      letI : CompleteSpace X :=
        (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
      C.coord) := by
    unfold EdgeFamily.coord
    rw [dite_eq_left hj]
  have hlin : mvfderiv 𝓘(ℝ, E3) (F.coord j) x ((ρ j / R) • v) =
      ρ j / R * mvfderiv 𝓘(ℝ, E3) (F.coord j) x v := by
    rw [map_smul, smul_eq_mul]
  have halg : ρ j / R * (egpRaw F j y - egpRaw F j x) / (R⁻¹ * dist x y) =
      (egpRaw F j y - egpRaw F j x) / ((ρ j)⁻¹ * dist x y) := by
    field_simp
  rw [← hlin, halg, hrawx, hrawy, hcoord]
  let C := F.chart j hj
  let hMc : CompleteSpace X := complete_of_compact
  let mR : MetricSpace X := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let bR := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let cR : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let iR : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let kR : CompleteSpace X := (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
  have hc' : C.center = j := hc
  let _ := C.instY
  have hxC : x ∈ ball C.center (100 * Δ) := by
    rw [hc']
    exact hxj
  have hyC : y ∈ ball C.center (1000 * Δ) := by
    rw [hc']
    exact hyj
  exact C.test x hxC y hyC hxyj ((ρ j / R) • v) hwj hgeoj

/-- **The original slim test at a reference scale `R`** (`SlimChart.test` of the packet at the
slim centre `j`, physical form): for `x ∈ B(j, Lρ(j))`, `y ∈ B(j, (L/σ)ρ(j))` with
`d(x, y) > Lρ(j)` (`L = 10⁶Δ`) and a unit vector `v` of `R⁻² g` whose geodesic of `R⁻² g` reaches
`y` at time `R⁻¹ d(x, y)`:
`|(ρ(j)/R) dη_j(v) − (ρ(j)/R)(u_j(y) − u_j(x))/(R⁻¹ d(x, y))| < σ`. -/
theorem SlimCentre.test_at_scale_KC2 {β₁ Δ σs : ℝ} {K : ℕ} {j : X}
    (c : SlimCentre X g hmetric ρ hρ β₁ Δ σs K j) {R : ℝ} (hR : 0 < R) {x y : X}
    (hx : x ∈ ball j (10 ^ 6 * Δ * ρ j)) (hy : y ∈ ball j (10 ^ 6 * Δ / σs * ρ j))
    (hxy : 10 ^ 6 * Δ * ρ j < dist x y) (v : TangentSpace 𝓘(ℝ, E3) x)
    (hv : R⁻¹ ^ 2 * g.inner x v v = 1)
    (hgeo : let hMc : CompleteSpace X := complete_of_compact
      letI := mX.rescale R⁻¹ (inv_pos.mpr hR)
      letI := radialScaledBundle g R⁻¹ (inv_pos.mpr hR)
      letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
        radialScaledContinuous g R⁻¹ (inv_pos.mpr hR)
      letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
        radialScaledManifold (m := mX) g hmetric R⁻¹ (inv_pos.mpr hR)
      letI : CompleteSpace X := (mX.rescale_completeSpace_iff R⁻¹ (inv_pos.mpr hR)).mpr hMc
      let gR : SmoothRiemannianMetric 𝓘(ℝ, E3) X :=
        scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) g
      have hnR : IsMetricNorm (I := 𝓘(ℝ, E3)) (M := X) gR := isMetricNorm_of_riemannianBundle gR
      intrinsicGeodesic gR hnR x v (dist x y) = y) :
    |ρ j / R * mvfderiv 𝓘(ℝ, E3) c.coord x v -
      ρ j / R * ((sgpSplitMap c y).fst - (sgpSplitMap c x).fst) / (R⁻¹ * dist x y)| < σs := by
  have hrj := hρ j
  have hswap := actual_geodesic_swap_KC2 g hmetric hR hrj x v (R⁻¹ * dist x y)
  have ht : R / ρ j * (R⁻¹ * dist x y) = (ρ j)⁻¹ * dist x y := by field_simp
  rw [ht] at hswap
  have hgeoj := hswap.trans hgeo
  have hxj : (ρ j)⁻¹ * dist x j < 10 ^ 6 * Δ := inv_mul_dist_lt_of_mem_ball_LC87 hrj hx
  have hyj : (ρ j)⁻¹ * dist y j < 10 ^ 6 * Δ / σs := inv_mul_dist_lt_of_mem_ball_LC87 hrj hy
  have hxyj : 10 ^ 6 * Δ < (ρ j)⁻¹ * dist x y := by
    rw [lt_inv_mul_iff₀ hrj]
    linarith
  have hwj : (scaleMetric ((ρ j)⁻¹ ^ 2) (pow_pos (inv_pos.mpr hrj) 2) g).inner x
      ((ρ j / R) • v) ((ρ j / R) • v) = 1 := by
    rw [scaleMetric_inner, map_smul, map_smul, smul_apply, smul_eq_mul, smul_eq_mul, ← hv]
    field_simp
  have hlin : mvfderiv 𝓘(ℝ, E3) c.coord x ((ρ j / R) • v) =
      ρ j / R * mvfderiv 𝓘(ℝ, E3) c.coord x v := by
    rw [map_smul, smul_eq_mul]
  have halg : ρ j / R * ((sgpSplitMap c y).fst - (sgpSplitMap c x).fst) / (R⁻¹ * dist x y) =
      ((sgpSplitMap c y).fst - (sgpSplitMap c x).fst) / ((ρ j)⁻¹ * dist x y) := by
    field_simp
  rw [← hlin, halg]
  unfold SlimCentre.coord
  let P := c.packet
  let iZ := c.instZ
  let hMc : CompleteSpace X := complete_of_compact
  let mR : MetricSpace X := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let bR := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let cR : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let iR : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let kR : CompleteSpace X := (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
  exact P.test x hxj y hyj hxyj ((ρ j / R) • v) hwj hgeoj

/-- **A unit minimizing direction of the reference metric `R⁻² g`** (Hopf–Rinow): for `x ≠ y`
there is `v` with `R⁻² g(v, v) = 1` whose geodesic of `R⁻² g` reaches `y` at time `R⁻¹ d(x, y)`. -/
theorem exists_minimizing_direction_KC2 (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
    (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)) {R : ℝ}
    (hR : 0 < R) {x y : X} (hxy : x ≠ y) :
    ∃ v : TangentSpace 𝓘(ℝ, E3) x, R⁻¹ ^ 2 * g.inner x v v = 1 ∧
      (let hMc : CompleteSpace X := complete_of_compact
      letI := mX.rescale R⁻¹ (inv_pos.mpr hR)
      letI := radialScaledBundle g R⁻¹ (inv_pos.mpr hR)
      letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
        radialScaledContinuous g R⁻¹ (inv_pos.mpr hR)
      letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
        radialScaledManifold (m := mX) g hmetric R⁻¹ (inv_pos.mpr hR)
      letI : CompleteSpace X := (mX.rescale_completeSpace_iff R⁻¹ (inv_pos.mpr hR)).mpr hMc
      let gR : SmoothRiemannianMetric 𝓘(ℝ, E3) X :=
        scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) g
      have hnR : IsMetricNorm (I := 𝓘(ℝ, E3)) (M := X) gR := isMetricNorm_of_riemannianBundle gR
      intrinsicGeodesic gR hnR x v (dist x y) = y) := by
  have hdpos0 : 0 < dist x y := dist_pos.mpr hxy
  let hMc : CompleteSpace X := complete_of_compact
  let mR : MetricSpace X := mX.rescale R⁻¹ (inv_pos.mpr hR)
  let bR := radialScaledBundle g R⁻¹ (inv_pos.mpr hR)
  let cR : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g R⁻¹ (inv_pos.mpr hR)
  let iR : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric R⁻¹ (inv_pos.mpr hR)
  let kR : CompleteSpace X := (mX.rescale_completeSpace_iff R⁻¹ (inv_pos.mpr hR)).mpr hMc
  let gR : SmoothRiemannianMetric 𝓘(ℝ, E3) X :=
    scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) g
  have hnR : IsMetricNorm (I := 𝓘(ℝ, E3)) (M := X) gR := isMetricNorm_of_riemannianBundle gR
  have hdpos : 0 < dist x y := by
    change 0 < R⁻¹ * @dist X mX.toDist x y
    positivity
  have hfin : riemannianEDist 𝓘(ℝ, E3) x y ≠ ⊤ := by
    rw [← IsRiemannianManifold.out (I := 𝓘(ℝ, E3)), edist_dist]
    exact ENNReal.ofReal_ne_top
  obtain ⟨u, hu, hlen⟩ := hopf_rinow_expMapIntrinsic_surjective_minimizing_of_ne_top gR hnR x y hfin
  have hdlen : (riemannianEDist 𝓘(ℝ, E3) x y).toReal = dist x y := by
    rw [← IsRiemannianManifold.out (I := 𝓘(ℝ, E3)), edist_dist, ENNReal.toReal_ofReal dist_nonneg]
  rw [hdlen] at hlen
  let w : TangentSpace 𝓘(ℝ, E3) x := (dist x y)⁻¹ • u
  have hupos : 0 < gR.inner x u u := Real.sqrt_pos.mp (hlen ▸ hdpos)
  have huu : gR.inner x u u = dist x y ^ 2 := by
    rw [← hlen, Real.sq_sqrt hupos.le]
  have hw : gR.inner x w w = 1 := by
    rw [gInner_smul_self, huu]
    field_simp
  refine ⟨w, ?_, ?_⟩
  · have h := hw
    rw [scaleMetric_inner] at h
    exact h
  · change intrinsicGeodesic gR hnR x w (dist x y) = y
    rw [← intrinsicGeodesic_smul gR hnR x w (dist x y)]
    have hdw : dist x y • w = u := by
      change dist x y • ((dist x y)⁻¹ • u) = u
      rw [smul_smul, mul_inv_cancel₀ hdpos.ne', one_smul]
    rw [hdw]
    exact hu

/-- **A point on a minimizing segment of the reference metric**: if a unit geodesic of `R⁻² g`
from `x` reaches `y` at time `R⁻¹ d(x, y)`, its point at time `t ∈ [0, R⁻¹ d(x, y)]` is at reference
distance `t` from `x` and `R⁻¹ d(x, y) − t` from `y`. -/
theorem geodesic_point_dist_KC2 (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
    (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)) {R : ℝ}
    (hR : 0 < R) {x y : X} (v : TangentSpace 𝓘(ℝ, E3) x) (hv : R⁻¹ ^ 2 * g.inner x v v = 1)
    (hgeo : let hMc : CompleteSpace X := complete_of_compact
      letI := mX.rescale R⁻¹ (inv_pos.mpr hR)
      letI := radialScaledBundle g R⁻¹ (inv_pos.mpr hR)
      letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
        radialScaledContinuous g R⁻¹ (inv_pos.mpr hR)
      letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
        radialScaledManifold (m := mX) g hmetric R⁻¹ (inv_pos.mpr hR)
      letI : CompleteSpace X := (mX.rescale_completeSpace_iff R⁻¹ (inv_pos.mpr hR)).mpr hMc
      let gR : SmoothRiemannianMetric 𝓘(ℝ, E3) X :=
        scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) g
      have hnR : IsMetricNorm (I := 𝓘(ℝ, E3)) (M := X) gR := isMetricNorm_of_riemannianBundle gR
      intrinsicGeodesic gR hnR x v (dist x y) = y) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ R⁻¹ * dist x y) :
    let z : X := (let hMc : CompleteSpace X := complete_of_compact
      letI := mX.rescale R⁻¹ (inv_pos.mpr hR)
      letI := radialScaledBundle g R⁻¹ (inv_pos.mpr hR)
      letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
        radialScaledContinuous g R⁻¹ (inv_pos.mpr hR)
      letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
        radialScaledManifold (m := mX) g hmetric R⁻¹ (inv_pos.mpr hR)
      letI : CompleteSpace X := (mX.rescale_completeSpace_iff R⁻¹ (inv_pos.mpr hR)).mpr hMc
      let gR : SmoothRiemannianMetric 𝓘(ℝ, E3) X :=
        scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) g
      have hnR : IsMetricNorm (I := 𝓘(ℝ, E3)) (M := X) gR := isMetricNorm_of_riemannianBundle gR
      intrinsicGeodesic gR hnR x v t)
    R⁻¹ * dist x z = t ∧ R⁻¹ * dist z y = R⁻¹ * dist x y - t := by
  intro z
  let hMc : CompleteSpace X := complete_of_compact
  let mR : MetricSpace X := mX.rescale R⁻¹ (inv_pos.mpr hR)
  let bR := radialScaledBundle g R⁻¹ (inv_pos.mpr hR)
  let cR : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g R⁻¹ (inv_pos.mpr hR)
  let iR : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric R⁻¹ (inv_pos.mpr hR)
  let kR : CompleteSpace X := (mX.rescale_completeSpace_iff R⁻¹ (inv_pos.mpr hR)).mpr hMc
  let gR : SmoothRiemannianMetric 𝓘(ℝ, E3) X :=
    scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) g
  have hnR : IsMetricNorm (I := 𝓘(ℝ, E3)) (M := X) gR := isMetricNorm_of_riemannianBundle gR
  have hsig : SigmaCompactSpace X := MetricSpace.rescale_compactSpace mX _ _ |>.sigmaCompact
  have hvR : gR.inner x v v = 1 := by
    rw [scaleMetric_inner]
    exact hv
  have hgeo' : intrinsicGeodesic gR hnR x v (dist x y) = y := hgeo
  have hzdef : z = intrinsicGeodesic gR hnR x v t := rfl
  have h1 := dist_intrinsicGeodesic_le_mul gR hnR x v ht0
  rw [intrinsicGeodesic_zero, hvR, Real.sqrt_one, one_mul, sub_zero, ← hzdef] at h1
  have ht1' : t ≤ dist x y := ht1
  have h2 := dist_intrinsicGeodesic_le_mul gR hnR x v ht1'
  rw [hgeo', hvR, Real.sqrt_one, one_mul, ← hzdef] at h2
  have h3 := dist_triangle x z y
  change dist x z ≤ t at h1
  change dist z y ≤ dist x y - t at h2
  change dist x y ≤ dist x z + dist z y at h3
  constructor
  · change dist x z = t
    linarith
  · change dist z y = dist x y - t
    linarith

end Actual

section Saturation

/-- **FC15's Riesz step without a norm instance**: two covectors on `T_x M` bounded by `1 + ε` for
the norm `√(c g)` that both exceed `1 − ε` on one `√(c g)`-unit vector differ by at most
`2√(4ε + ε²)` on every unit vector. -/
theorem abs_sub_le_of_common_unit_KC2 {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M]
    [IsManifold 𝓘(ℝ, E3) ∞ M] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) M) (x : M) {c : ℝ}
    (hc : 0 < c) (f₁ f₂ : TangentSpace 𝓘(ℝ, E3) x →L[ℝ] ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (h₁ : ∀ w, |f₁ w| ≤ (1 + ε) * Real.sqrt (c * g.inner x w w))
    (h₂ : ∀ w, |f₂ w| ≤ (1 + ε) * Real.sqrt (c * g.inner x w w))
    (v : TangentSpace 𝓘(ℝ, E3) x) (hv : c * g.inner x v v = 1) (hv₁ : 1 - ε ≤ f₁ v)
    (hv₂ : 1 - ε ≤ f₂ v) (w : TangentSpace 𝓘(ℝ, E3) x) (hw : c * g.inner x w w = 1) :
    |f₁ w - f₂ w| ≤ 2 * Real.sqrt (4 * ε + ε ^ 2) := by
  let bR : RiemannianBundle (fun y : M => TangentSpace 𝓘(ℝ, E3) y) :=
    ⟨(scaleMetric c hc g).toRiemannianMetric⟩
  have hnorm : ∀ u : TangentSpace 𝓘(ℝ, E3) x, ‖u‖ = Real.sqrt (c * g.inner x u u) := by
    intro u
    rw [← Real.sqrt_sq (norm_nonneg u), ← real_inner_self_eq_norm_sq]
    congr 1
  have hf₁ : ‖f₁‖ ≤ 1 + ε := ContinuousLinearMap.opNorm_le_bound _ (by linarith) fun u => by
    rw [Real.norm_eq_abs, hnorm]
    exact h₁ u
  have hf₂ : ‖f₂‖ ≤ 1 + ε := ContinuousLinearMap.opNorm_le_bound _ (by linarith) fun u => by
    rw [Real.norm_eq_abs, hnorm]
    exact h₂ u
  have hv1 : ‖v‖ = 1 := by rw [hnorm, hv, Real.sqrt_one]
  have hsat := ContinuousLinearMap.norm_sub_le_of_common_unit_saturation f₁ f₂ hε hf₁ hf₂ v hv1
    hv₁ hv₂
  have hle := (f₁ - f₂).le_opNorm w
  rw [hnorm w, hw, Real.sqrt_one, mul_one, Real.norm_eq_abs] at hle
  exact hle.trans hsat

end Saturation

section Lift

/-- **An offset lift through a real-factor splitting.** For a Kleiner–Lott `β`-map
`f = (u, v) : (X, p) → ℝ × Y` and a real offset `T`, there is `y` with
`|u(y) − u(x) − T| < 2β`, `|d(x, y) − |T|| < 3β` and `d(y, p) < |T| + 2d(x, p) + 5β`, provided this
radius stays below `β⁻¹` (the lift of `(u(x) + T, v(x))`). -/
theorem exists_raw_offset_lift_KC2 {X Y : Type*} [MetricSpace X] [MetricSpace Y] {p : X} {q : Y}
    {β : ℝ} (f : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), q)) β) (x : X) (T : ℝ)
    (hbuf : |T| + 2 * dist x p + 5 * β < β⁻¹) :
    ∃ y : X, dist y p < |T| + 2 * dist x p + 5 * β ∧
      |(f.toFun y).fst - (f.toFun x).fst - T| < 2 * β ∧ abs (dist x y - |T|) < 3 * β := by
  have hb := f.error_pos
  have hxp := dist_nonneg (x := x) (y := p)
  have hT := abs_nonneg T
  have hx : x ∈ ball p β⁻¹ := mem_ball.mpr (by linarith)
  have hrad := f.radial_error x hx
  have hfst := WithLp.dist_fst_le (f.toFun x) (WithLp.toLp 2 ((0 : ℝ), q))
  change dist (f.toFun x).fst 0 ≤ _ at hfst
  rw [Real.dist_eq, sub_zero] at hfst
  have hsnd := WithLp.dist_snd_le (f.toFun x) (WithLp.toLp 2 ((0 : ℝ), q))
  change dist (f.toFun x).snd q ≤ _ at hsnd
  have hfx : dist (f.toFun x) (WithLp.toLp 2 ((0 : ℝ), q)) ≤ dist x p + β := by
    linarith [(abs_le.mp hrad).2]
  have htabs : |(f.toFun x).fst + T| ≤ |(f.toFun x).fst| + |T| := abs_add_le _ _
  obtain ⟨y, hy1, hy2, -⟩ := f.exists_product_lift_radius ((f.toFun x).fst + T) (f.toFun x).snd
    (by linarith)
  have hyb : dist y p < |T| + 2 * dist x p + 5 * β := by linarith
  refine ⟨y, hyb, ?_, ?_⟩
  · have h := WithLp.dist_fst_le (f.toFun y) (WithLp.toLp 2 ((f.toFun x).fst + T, (f.toFun x).snd))
    change dist (f.toFun y).fst ((f.toFun x).fst + T) ≤ _ at h
    rw [Real.dist_eq] at h
    have he : (f.toFun y).fst - (f.toFun x).fst - T = (f.toFun y).fst - ((f.toFun x).fst + T) := by
      ring
    rw [he]
    linarith
  · have hy : y ∈ ball p β⁻¹ := mem_ball.mpr (by linarith)
    have hd := f.distortion y hy x hx
    have hxx : WithLp.toLp 2 ((f.toFun x).fst, (f.toFun x).snd) = f.toFun x := rfl
    have hT' : dist (WithLp.toLp 2 ((f.toFun x).fst + T, (f.toFun x).snd))
        (f.toFun x) = |T| := by
      have h := (WithLp.isometry_prodMk_right (E := ℝ) (f.toFun x).snd).dist_eq
        ((f.toFun x).fst + T) (f.toFun x).fst
      rw [hxx] at h
      rw [h, Real.dist_eq, add_sub_cancel_left]
    have t1 := dist_triangle (f.toFun y) (WithLp.toLp 2 ((f.toFun x).fst + T, (f.toFun x).snd))
      (f.toFun x)
    have t2 := dist_triangle (WithLp.toLp 2 ((f.toFun x).fst + T, (f.toFun x).snd)) (f.toFun y)
      (f.toFun x)
    rw [dist_comm (WithLp.toLp 2 ((f.toFun x).fst + T, (f.toFun x).snd)) (f.toFun y)] at t2
    rw [dist_comm x y]
    rw [abs_lt] at ⊢
    rw [abs_le] at hd
    constructor <;> linarith [hd.1, hd.2]

end Lift

/-- EGP04's Riesz budget: `ε < θ²/10⁶` gives `2√(4ε + ε²) < θ`. -/
theorem egp04_riesz_budget_KC2 {ε θ : ℝ} (hε : 0 ≤ ε) (hθ : 0 < θ) (hθ1 : θ < 1)
    (hεθ : ε < θ ^ 2 / 10 ^ 6) : 2 * Real.sqrt (4 * ε + ε ^ 2) < θ := by
  have hθ2 : θ ^ 2 < 1 := by nlinarith
  have hsq : 4 * ε + ε ^ 2 < (θ / 2) ^ 2 := by nlinarith
  have hroot : Real.sqrt (4 * ε + ε ^ 2) < θ / 2 := (Real.sqrt_lt' (by positivity)).mpr hsq
  linarith

end DifferentialGeometry.Geometry.Collapse
