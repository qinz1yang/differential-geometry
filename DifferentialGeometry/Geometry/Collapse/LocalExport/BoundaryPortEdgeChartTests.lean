import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortEdgeRawAlignment
import DifferentialGeometry.Geometry.Fibration.ActualEdgeChartTests

/-!
# EGP04's chart tests on the boundary family (lane B-PORT-EDGE, G1)

GENERATED from `Geometry/Fibration/ActualEdgeChartTests.lean` (section `Actual`) by
`build-logs/scratch/B-PORT-EDGE/gen_charttests.py` (tables of `portedge.py`); do not edit by hand,
re-run the script.

The physical forms of the edge charts' value and test clauses (LFR19 / LC84) on a regional edge
family `F : EdgeFamilyOn … U₁ U₂` over a complete σ-compact carrier (`EdgeFamilyOn.value_KC2_BAUGP`,
`EdgeFamilyOn.test_at_scale_KC2_BAUGP`), the slim centre's test at a reference scale
(`SlimCentreOn.test_at_scale_KC2_BAUGP`) and the Hopf–Rinow minimizing direction / segment point of
the reference metric (`exists_minimizing_direction_KC2_BAUGP`, `geodesic_point_dist_KC2_BAUGP`,
`actual_geodesic_swap_KC2_BAUGP`). Substitution table as in `BoundaryPortEdgeComparisonList.lean`;
the edge coordinate unfolds to BCG-1's `coord_BCG1` (the chart coordinate); the rescaled metric
has the carrier's topology, so σ-compactness is the carrier's. Reused unchanged (generic):
`intrinsicGeodesic_radialScaled_swap_KC2` and the sections `Saturation`, `Lift` of the closed file.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

open scoped InnerProductSpace
open DifferentialGeometry.Geometry.Riemannian.Exponential

section Actual

universe u

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p}

/-- **Change of reference scale on an actual compact manifold** (the chart blocks of LC87). -/
theorem actual_geodesic_swap_KC2_BAUGP (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
    (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)) {R₁ R₂ : ℝ}
    (h₁ : 0 < R₁) (h₂ : 0 < R₂) (p : X) (v : TangentSpace 𝓘(ℝ, E3) p) (t : ℝ) :
    (let hMc : CompleteSpace X := ‹CompleteSpace X›
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
      (let hMc : CompleteSpace X := ‹CompleteSpace X›
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
  have kP : CompleteSpace X := ‹CompleteSpace X›
  have hEn : IsMetricNorm (I := 𝓘(ℝ, E3)) g := isMetricNorm_of_riemannianBundle g
  exact intrinsicGeodesic_radialScaled_swap_KC2 g hEn h₁ h₂ p v t

variable {β : ℕ → ℝ} {Δ σc μ b s b' s' ε γc βc : ℝ} {U₁ U₂ : Set X}

/-- **LFR19's value error of the actual edge chart** (physical form): on `B(j, 100Δρ(j))`,
`|η_j − u_j| < μΔ`. -/
theorem EdgeFamilyOn.value_KC2_BAUGP (F : EdgeFamilyOn X g hmetric ρ hρ β Δ σc μ b s b' s' ε γc βc U₁ U₂)
    {j : X} (hj : j ∈ F.centres) {x : X} (hx : x ∈ ball j (100 * Δ * ρ j)) :
    |F.coord_BAUGA j x - egpRaw_BAUGP F j x| < μ * Δ := by
  have hc := F.chart_center j hj
  have hrj := hρ j
  have hd : (ρ j)⁻¹ * dist x j < 100 * Δ := inv_mul_dist_lt_of_mem_ball_LC87 hrj hx
  have hraw : egpRaw_BAUGP F j x = egpChartRaw_BAUGP F hj x := egpRaw_of_mem_BAUGP F hj x
  rw [hraw]
  unfold EdgeFamilyOn.coord_BAUGA EdgeFamilyOn.coord_BCG1
  rw [dite_eq_left hj]
  let C := F.chart j hj
  let hMc : CompleteSpace X := ‹CompleteSpace X›
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
theorem EdgeFamilyOn.test_at_scale_KC2_BAUGP (F : EdgeFamilyOn X g hmetric ρ hρ β Δ σc μ b s b' s' ε γc βc U₁ U₂)
    {j : X} (hj : j ∈ F.centres) {R : ℝ} (hR : 0 < R) {x y : X}
    (hx : x ∈ ball j (100 * Δ * ρ j)) (hy : y ∈ ball j (1000 * Δ * ρ j))
    (hxy : 100 * Δ * ρ j < dist x y) (v : TangentSpace 𝓘(ℝ, E3) x)
    (hv : R⁻¹ ^ 2 * g.inner x v v = 1)
    (hgeo : let hMc : CompleteSpace X := ‹CompleteSpace X›
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
    |ρ j / R * mvfderiv 𝓘(ℝ, E3) (F.coord_BAUGA j) x v -
      ρ j / R * (egpRaw_BAUGP F j y - egpRaw_BAUGP F j x) / (R⁻¹ * dist x y)| < σc := by
  have hc := F.chart_center j hj
  have hrj := hρ j
  -- the geodesic of the chart metric
  have hswap := actual_geodesic_swap_KC2_BAUGP g hmetric hR hrj x v (R⁻¹ * dist x y)
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
  have hrawx : egpRaw_BAUGP F j x = egpChartRaw_BAUGP F hj x := egpRaw_of_mem_BAUGP F hj x
  have hrawy : egpRaw_BAUGP F j y = egpChartRaw_BAUGP F hj y := egpRaw_of_mem_BAUGP F hj y
  have hcoord : F.coord_BAUGA j = (let C := F.chart j hj
      let hMc : CompleteSpace X := ‹CompleteSpace X›
      letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
      letI := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
      letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
        radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
      letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
        radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
      letI : CompleteSpace X :=
        (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
      C.coord) := by
    unfold EdgeFamilyOn.coord_BAUGA EdgeFamilyOn.coord_BCG1
    rw [dite_eq_left hj]
  have hlin : mvfderiv 𝓘(ℝ, E3) (F.coord_BAUGA j) x ((ρ j / R) • v) =
      ρ j / R * mvfderiv 𝓘(ℝ, E3) (F.coord_BAUGA j) x v := by
    rw [map_smul, smul_eq_mul]
  have halg : ρ j / R * (egpRaw_BAUGP F j y - egpRaw_BAUGP F j x) / (R⁻¹ * dist x y) =
      (egpRaw_BAUGP F j y - egpRaw_BAUGP F j x) / ((ρ j)⁻¹ * dist x y) := by
    field_simp
  rw [← hlin, halg, hrawx, hrawy, hcoord]
  let C := F.chart j hj
  let hMc : CompleteSpace X := ‹CompleteSpace X›
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
theorem SlimCentreOn.test_at_scale_KC2_BAUGP {β₁ Δ σs : ℝ} {K : ℕ} {j : X}
    (c : SlimCentreOn X g hmetric ρ hρ β₁ Δ σs K j) {R : ℝ} (hR : 0 < R) {x y : X}
    (hx : x ∈ ball j (10 ^ 6 * Δ * ρ j)) (hy : y ∈ ball j (10 ^ 6 * Δ / σs * ρ j))
    (hxy : 10 ^ 6 * Δ * ρ j < dist x y) (v : TangentSpace 𝓘(ℝ, E3) x)
    (hv : R⁻¹ ^ 2 * g.inner x v v = 1)
    (hgeo : let hMc : CompleteSpace X := ‹CompleteSpace X›
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
    |ρ j / R * mvfderiv 𝓘(ℝ, E3) c.coord_BCG2 x v -
      ρ j / R * ((sgpSplitMap_BAUGP c y).fst - (sgpSplitMap_BAUGP c x).fst) / (R⁻¹ * dist x y)| < σs := by
  have hrj := hρ j
  have hswap := actual_geodesic_swap_KC2_BAUGP g hmetric hR hrj x v (R⁻¹ * dist x y)
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
  have hlin : mvfderiv 𝓘(ℝ, E3) c.coord_BCG2 x ((ρ j / R) • v) =
      ρ j / R * mvfderiv 𝓘(ℝ, E3) c.coord_BCG2 x v := by
    rw [map_smul, smul_eq_mul]
  have halg : ρ j / R * ((sgpSplitMap_BAUGP c y).fst - (sgpSplitMap_BAUGP c x).fst) / (R⁻¹ * dist x y) =
      ((sgpSplitMap_BAUGP c y).fst - (sgpSplitMap_BAUGP c x).fst) / ((ρ j)⁻¹ * dist x y) := by
    field_simp
  rw [← hlin, halg]
  unfold SlimCentreOn.coord_BCG2
  let P := c.packet
  let iZ := c.instZ
  let hMc : CompleteSpace X := ‹CompleteSpace X›
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
theorem exists_minimizing_direction_KC2_BAUGP (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
    (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)) {R : ℝ}
    (hR : 0 < R) {x y : X} (hxy : x ≠ y) :
    ∃ v : TangentSpace 𝓘(ℝ, E3) x, R⁻¹ ^ 2 * g.inner x v v = 1 ∧
      (let hMc : CompleteSpace X := ‹CompleteSpace X›
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
  let hMc : CompleteSpace X := ‹CompleteSpace X›
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
theorem geodesic_point_dist_KC2_BAUGP (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
    (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)) {R : ℝ}
    (hR : 0 < R) {x y : X} (v : TangentSpace 𝓘(ℝ, E3) x) (hv : R⁻¹ ^ 2 * g.inner x v v = 1)
    (hgeo : let hMc : CompleteSpace X := ‹CompleteSpace X›
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
    let z : X := (let hMc : CompleteSpace X := ‹CompleteSpace X›
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
  let hMc : CompleteSpace X := ‹CompleteSpace X›
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
  have hsig : SigmaCompactSpace X := ‹SigmaCompactSpace X›
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

end DifferentialGeometry.Geometry.Collapse
