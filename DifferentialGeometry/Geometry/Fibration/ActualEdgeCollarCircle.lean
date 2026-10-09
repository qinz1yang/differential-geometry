import DifferentialGeometry.Geometry.Collapse.EdgeFullCollarTwoStratum
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsC14

/-!
# EDP06, E-free step: an edge collar point is two-stratum and lies in a circle chart

Lane C14-EDP6. Blueprint 207B, EDP06 (B:7103–7108): "At a point of (EV), (ELoc) and (EH) give
`|η_i| < 4.01Δ` and `|t − 4Δ| < h_*` for a witnessing edge index. LFR38 applies to the SAME original
pair on this full band and makes the point two-stratum, using the retained no-three result. LPA06's
original circle cover supplies a circle chart with `|η_a| < 2`." The (ELoc)/(EH) input and GAF07's
conclusion need the adjusted map `E`; this file proves the step between them on the family.

* `KleinerLottApprox.nonempty_of_le_EDP6`: a `δ`-Kleiner–Lott map is a `δ'`-map for `3δ ≤ δ' < 1`.
* `EdgeFamily.collar_plane_EDP6`: at a point of an edge chart's collar band (physical form:
  `d(x, j) < 100Δρ(j)`, `|η_j(x)| ≤ 10Δ`, `Δ/10 ≤ F(x)/ρ(x) ≤ 10Δ`) the chart's own LFR38 clause
  (`EdgeChart.collar`) gives a plane `(β 2)`-map at `x` in the point's own metric `ρ(x)⁻¹ d`, as
  soon as `3βc ≤ β 2 < 1` (the normalized pair `(ρ(j)⁻¹ d, ρ/ρ(j))` has own-scale metric
  `ρ(x)⁻¹ d`).
* `EdgeFamily.collar_two_stratum_EDP6`: with the row's no-three input at `x`, `x` is two-stratum.
* `LocalChartPackets.circle_chart_of_two_EDP6`: a two-stratum point lies, by the stored circle cover
  and the circle adapted packet, at distance `< 2ρ(a)` from a circle centre `a` with
  `‖η_a(x)‖ < 2(1 + γ)` (GAF07 needs `≤ 3.5`, B:6059).
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

/-- **Weakening a Kleiner–Lott map**: a `δ`-approximation is a `δ'`-approximation (same map) when
`3δ ≤ δ' < 1`. -/
theorem KleinerLottApprox.nonempty_of_le_EDP6 {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    {p : X} {q : Y} {δ δ' : ℝ} (f : KleinerLottApprox p q δ) (h3 : 3 * δ ≤ δ') (h1 : δ' < 1) :
    Nonempty (KleinerLottApprox p q δ') := by
  have hδ := f.error_pos
  have hinv : δ'⁻¹ ≤ δ⁻¹ := inv_anti₀ hδ (by linarith)
  have hball : ball p δ'⁻¹ ⊆ ball p δ⁻¹ := ball_subset_ball hinv
  refine Nonempty.intro
    { error_pos := by linarith
      error_lt_one := h1
      toFun := f.toFun
      basepoint := f.basepoint
      distortion := fun x hx x' hx' => ?_
      coverage := fun y hy => ?_ }
  · have h := f.distortion x (hball hx) x' (hball hx')
    linarith
  · have hy' : dist y q < δ⁻¹ - δ := by linarith
    obtain ⟨x, hx, hxy⟩ := f.coverage_witness y hy'
    have hrad := (abs_le.mp (f.radial_error x hx)).1
    have htri := dist_triangle (f.toFun x) y q
    rw [dist_comm (f.toFun x) y] at htri
    have hxp : x ∈ ball p δ'⁻¹ := by
      rw [mem_ball]
      linarith
    exact (infDist_le_dist_of_mem (Set.mem_image_of_mem f.toFun hxp)).trans (by linarith)

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {β : ℕ → ℝ} {Δ σc μ b s b' s' ε γc βc : ℝ}

/-- **The collar's plane map at the point's own scale** (LFR38 through `EdgeChart.collar`, physical
form): at an edge centre `j` and a point `x` with `d(x, j) < 100Δρ(j)`, `|η_j(x)| ≤ 10Δ` (`η_j` the
chart's coordinate) and `Δ/10 ≤ F(x)/ρ(x) ≤ 10Δ`, there is a plane Kleiner–Lott `(β 2)`-map at `x`
in the metric `ρ(x)⁻¹ d`, provided `3βc ≤ β 2 < 1`. -/
theorem EdgeFamily.collar_plane_EDP6
    (Fe : EdgeFamily X g hmetric ρ hρ β Δ σc μ b s b' s' ε γc βc) (h3βc : 3 * βc ≤ β 2)
    (hβ2 : β 2 < 1) {j : X} (hj : j ∈ Fe.centres) {x : X} (hx : dist x j < 100 * Δ * ρ j)
    (hη : let c := Fe.chart j hj
      let hMc : CompleteSpace X := complete_of_compact
      letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
      letI := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
      letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
        radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
      letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
        radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
      letI : CompleteSpace X :=
        (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
      |c.coord x| ≤ 10 * Δ)
    (hF1 : Δ / 10 ≤ Fe.smoothing x / ρ x) (hF2 : Fe.smoothing x / ρ x ≤ 10 * Δ) :
    Nonempty (@KleinerLottApprox X (WithLp 2 (ℝ × ℝ)) (mX.rescale (ρ x)⁻¹ (inv_pos.mpr (hρ x)))
      _ x (WithLp.toLp 2 ((0 : ℝ), (0 : ℝ))) (β 2)) := by
  have hcc0 := Fe.chart_center j hj
  have ht : Fe.smoothing x / ρ j / (ρ x / ρ j) = Fe.smoothing x / ρ x := by
    field_simp [(hρ j).ne', (hρ x).ne']
  have hF1' : Δ / 10 ≤ Fe.smoothing x / ρ j / (ρ x / ρ j) := by
    rw [ht]
    exact hF1
  have hF2' : Fe.smoothing x / ρ j / (ρ x / ρ j) ≤ 10 * Δ := by
    rw [ht]
    exact hF2
  have hxr : (ρ j)⁻¹ * dist x j < 100 * Δ := by
    rw [inv_mul_lt_iff₀ (hρ j)]
    linarith
  have hΦ : Nonempty (@KleinerLottApprox X (WithLp 2 (ℝ × ℝ))
      ((mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))).rescale (ρ x / ρ j)⁻¹
        (inv_pos.mpr (div_pos (hρ x) (hρ j)))) _ x (WithLp.toLp 2 ((0 : ℝ), (0 : ℝ))) βc) := by
    let c := Fe.chart j hj
    let hMc : CompleteSpace X := complete_of_compact
    let _ := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    let _ := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    let _ : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
      radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    let _ : IsRiemannianManifold 𝓘(ℝ, E3) X :=
      radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    let _ : CompleteSpace X :=
      (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
    have hcc : c.center = j := hcc0
    have hx' : x ∈ ball c.center (100 * Δ) := by
      rw [hcc, mem_ball]
      exact hxr
    obtain ⟨hq, ⟨Φ, -⟩, -⟩ := c.collar x hx' hη hF1' hF2'
    exact ⟨Φ⟩
  rw [MetricSpace.rescale_inv_ratio mX (hρ j) (hρ x)] at hΦ
  obtain ⟨Φ'⟩ := hΦ
  exact @KleinerLottApprox.nonempty_of_le_EDP6 X (WithLp 2 (ℝ × ℝ))
    (mX.rescale (ρ x)⁻¹ (inv_pos.mpr (hρ x))) _ x _ βc (β 2) Φ' h3βc hβ2

/-- **An edge collar point is two-stratum** (EDP06, B:7105–7106): at a point of an edge chart's
collar band (physical form), with the row's no-three input at `x` (scale `ρ(x)`, tolerance `β 3`)
and `3βc ≤ β 2 < 1`, `x` lies in the LC16 two-stratum. -/
theorem EdgeFamily.collar_two_stratum_EDP6
    (Fe : EdgeFamily X g hmetric ρ hρ β Δ σc μ b s b' s' ε γc βc) (h3βc : 3 * βc ≤ β 2)
    (hβ2 : β 2 < 1) {j : X} (hj : j ∈ Fe.centres) {x : X} (hx : dist x j < 100 * Δ * ρ j)
    (hη : let c := Fe.chart j hj
      let hMc : CompleteSpace X := complete_of_compact
      letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
      letI := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
      letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
        radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
      letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
        radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
      letI : CompleteSpace X :=
        (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
      |c.coord x| ≤ 10 * Δ)
    (hF1 : Δ / 10 ≤ Fe.smoothing x / ρ x) (hF2 : Fe.smoothing x / ρ x ≤ 10 * Δ)
    (h3 : ¬ @HasEuclideanSplitting.{0, 0} X (mX.rescale (ρ x)⁻¹ (inv_pos.mpr (hρ x))) x 3 (β 3)) :
    x ∈ scaledSplittingStratum.{0, 0} ρ hρ β 2 :=
  mem_scaledSplittingStratum_two_of_plane_approx hρ
    (Fe.collar_plane_EDP6 h3βc hβ2 hj hx hη hF1 hF2) h3

variable {Λ : ℝ} {Δ σs : ℝ} {K : ℕ} {Lmax τ γ δ εr e T V : ℝ}

/-- **A two-stratum point lies in a circle chart** (LPA06's circle cover, EDP06 B:7107 and FDC03
B:7334): some circle centre `a` has `d(x, a) < 2ρ(a)` and, normalized at `a`, `‖η_a(x)‖ < 2(1 + γ)`
(the circle adapted packet's `(1 + γ)`-Lipschitz bound on `B(a, 200)`). -/
theorem LocalChartPackets.circle_chart_of_two_EDP6
    (L : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hγ : 0 ≤ γ) {x : X} (hx : x ∈ scaledSplittingStratum.{0, 0} ρ hρ β 2) :
    ∃ a, ∃ ha : a ∈ L.circle.centres, dist x a < 2 * ρ a ∧
      (let c := L.circle.chart a ha
       letI := mX.rescale (ρ a)⁻¹ (inv_pos.mpr (hρ a))
       ‖c.coord x‖ < 2 * (1 + γ)) := by
  obtain ⟨a, ha, hsub⟩ := L.circle.covers x hx
  have hxa : dist x a < 2 * ρ a := mem_ball.mp (hsub (mem_ball_self (hρ x)))
  refine ⟨a, ha, hxa, ?_⟩
  have hxa' : (ρ a)⁻¹ * dist x a < 2 := by
    rw [inv_mul_lt_iff₀ (hρ a)]
    linarith
  have hcc0 := L.circle.chart_center a ha
  have hlip := (L.circleAdapted a ha).lipschitz
  let c := L.circle.chart a ha
  let _ := mX.rescale (ρ a)⁻¹ (inv_pos.mpr (hρ a))
  have hcc : c.center = a := hcc0
  have h0 : c.coord a = 0 := by
    have h := c.coord_center
    rwa [hcc] at h
  have hxa'' : dist x a < 2 := hxa'
  have hxB : x ∈ ball a 200 := by
    rw [mem_ball]
    linarith
  have haB : a ∈ ball a 200 := mem_ball_self (by norm_num)
  have hl : LipschitzOnWith (Real.toNNReal (1 + γ)) c.coord (ball a 200) := hlip
  have hd := hl.dist_le_mul x hxB a haB
  rw [h0, dist_zero_right, Real.coe_toNNReal _ (by linarith)] at hd
  have hpos : 0 < 1 + γ := by linarith
  change ‖c.coord x‖ < 2 * (1 + γ)
  calc ‖c.coord x‖ ≤ (1 + γ) * dist x a := hd
    _ < (1 + γ) * 2 := mul_lt_mul_of_pos_left hxa'' hpos
    _ = 2 * (1 + γ) := by ring

end DifferentialGeometry.Geometry.Collapse
