import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPacketsBFApplications
import DifferentialGeometry.Geometry.Fibration.ActualEdgeCollarCircle

/-!
# BCG01's edge-collar clause on the revised edge family `edgeB` (lane BCG-4)

Blueprint 207B, BCG01 (`B:8806–8814`): "for a selected edge center `d_a > 20`, require
`100ΔR_a < d_a/2`. Its WHOLE original edge domain then lies in `d > 10`. Every two-stratum point in
its LFR38 circle collar is an eligible circle-center candidate, so circle maximality covers it."
Review 51 (row 2, binding): `edgeB_domain` gives eligibility only; the collar cover claim also
needs the two-stratum fact and the same-chart collar certificate. Regional versions of lane
C14-EDP6's closed-route lemmas (`EdgeFamily.collar_plane_EDP6`,
`EdgeFamily.collar_two_stratum_EDP6`,
`LocalChartPackets.circle_chart_of_two_EDP6`; `[CompactSpace]` replaced by the carrier's
`CompleteSpace`, the circle cover restricted to `U₁`):

* `EdgeFamilyOn.collar_plane_BCG4`: the same-chart collar certificate — at a point of an edge
  chart's collar band (`d(x, j) < 100Δρ(j)`, `|η_j(x)| ≤ 10Δ`, `Δ/10 ≤ F(x)/ρ(x) ≤ 10Δ`) the chart's
  LFR38 clause gives a plane `(β 2)`-map at `x` in `ρ(x)⁻¹ d` (`3βc ≤ β 2 < 1`);
* `EdgeFamilyOn.collar_two_stratum_BCG4`: with the no-three input at `x`, `x` is two-stratum;
* `LocalPacketsOn.circle_chart_of_two_BCG4`: a two-stratum point of `U₁` lies in a circle chart
  (`d(x, a) < 2ρ(a)`, `B(x, ρ(x)) ⊆ B(a, 2ρ(a))`, `‖η_a(x)‖ < 2(1 + γ)`);
* `LocalPacketsOnBF.edgeB_collar_circle_cover_BCG4` (BCG01's clause): at every revised edge centre
  `j`, every two-stratum point of the packet domain `B(j, 1000Δρ(j)) ⊇ B(j, 100Δρ(j))` lies in
  `U₁` (`edgeB_domain`) and is covered by a circle chart;
* `LocalPacketsOnBF.edgeB_collar_circle_BCG4`: every point of the collar band of a revised edge
  chart, with the no-three input, is two-stratum and lies in a circle chart.

The no-three input at the collar points is NOT a clause of `LocalPacketsOnBF` or of T3B's tail
(the regional kernel proves rank `≤ 2` on `U₁` but does not export it): reported as a producer
gap; the sequence-level binding of the last statement waits for that field.
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

section Regional

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {β : ℕ → ℝ} {Δ σc μ b s b' s' ε γc βc : ℝ}
  {U₁ U₂ : Set X}

/-- **The same-chart collar certificate on a regional edge family** (LFR38 through
`EdgeChart.collar`, physical form): at an edge centre `j` and a point `x` with
`d(x, j) < 100Δρ(j)`, `|η_j(x)| ≤ 10Δ` and `Δ/10 ≤ F(x)/ρ(x) ≤ 10Δ`, there is a plane
Kleiner–Lott `(β 2)`-map at `x` in the metric `ρ(x)⁻¹ d`, provided `3βc ≤ β 2 < 1`. -/
theorem EdgeFamilyOn.collar_plane_BCG4
    (Fe : EdgeFamilyOn X g hmetric ρ hρ β Δ σc μ b s b' s' ε γc βc U₁ U₂) (h3βc : 3 * βc ≤ β 2)
    (hβ2 : β 2 < 1) {j : X} (hj : j ∈ Fe.centres) {x : X} (hx : dist x j < 100 * Δ * ρ j)
    (hη : let c := Fe.chart j hj
      let hMc : CompleteSpace X := ‹CompleteSpace X›
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
    let hMc : CompleteSpace X := ‹CompleteSpace X›
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

/-- **An edge collar point is two-stratum** (regional EDP06 step): at a point of a regional edge
chart's collar band (physical form), with the no-three input at `x` (scale `ρ(x)`, tolerance
`β 3`) and `3βc ≤ β 2 < 1`, `x` lies in the two-stratum. -/
theorem EdgeFamilyOn.collar_two_stratum_BCG4
    (Fe : EdgeFamilyOn X g hmetric ρ hρ β Δ σc μ b s b' s' ε γc βc U₁ U₂) (h3βc : 3 * βc ≤ β 2)
    (hβ2 : β 2 < 1) {j : X} (hj : j ∈ Fe.centres) {x : X} (hx : dist x j < 100 * Δ * ρ j)
    (hη : let c := Fe.chart j hj
      let hMc : CompleteSpace X := ‹CompleteSpace X›
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
    (Fe.collar_plane_BCG4 h3βc hβ2 hj hx hη hF1 hF2) h3

variable {Λ : ℝ} {σs : ℝ} {K : ℕ} {Lmax τ γ δ εr e T V : ℝ}

/-- **A two-stratum point of `U₁` lies in a circle chart** (regional LPA06 cover): some circle
centre `a` has `B(x, ρ(x)) ⊆ B(a, 2ρ(a))`, `d(x, a) < 2ρ(a)` and, normalized at `a`,
`‖η_a(x)‖ < 2(1 + γ)` (the circle adapted packet's `(1 + γ)`-Lipschitz bound on `B(a, 200)`). -/
theorem LocalPacketsOn.circle_chart_of_two_BCG4
    (L : LocalPacketsOn X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
      U₁ U₂)
    (hγ : 0 ≤ γ) {x : X} (hxU : x ∈ U₁) (hx : x ∈ scaledSplittingStratum.{0, 0} ρ hρ β 2) :
    ∃ a, ∃ ha : a ∈ L.circle.centres, ball x (ρ x) ⊆ ball a (2 * ρ a) ∧ dist x a < 2 * ρ a ∧
      (let c := L.circle.chart a ha
       letI := mX.rescale (ρ a)⁻¹ (inv_pos.mpr (hρ a))
       ‖c.coord x‖ < 2 * (1 + γ)) := by
  obtain ⟨a, ha, hsub⟩ := L.circle.covers x ⟨hxU, hx⟩
  have hxa : dist x a < 2 * ρ a := mem_ball.mp (hsub (mem_ball_self (hρ x)))
  refine ⟨a, ha, hsub, hxa, ?_⟩
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

end Regional

section Final

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}

/-- **BCG01's edge-collar clause on the revised edge family** (`B:8806–8814`): at every revised
edge centre `j` (eligible: `j ∈ Ue₁`, packet domain in `U₁`), every two-stratum point `x` of the
packet domain `B(j, 1000Δρ(j))` (which contains the LFR38 collar `B(j, 100Δρ(j))`) lies in `U₁`
and is covered by a circle chart: `B(x, ρ(x)) ⊆ B(a, 2ρ(a))`, `‖η_a(x)‖ < 2(1 + γ)`. -/
theorem LocalPacketsOnBF.edgeB_collar_circle_cover_BCG4
    (F : LocalPacketsOnBF X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
      vs ζ Λz U₁ U₂ Ue₁ Ue₂) (hγ : 0 ≤ γ) :
    ∀ j ∈ F.edgeB.centres, j ∈ Ue₁ ∧ ∀ x, dist x j < 1000 * Δ * ρ j →
      x ∈ scaledSplittingStratum.{0, 0} ρ hρ β 2 → x ∈ U₁ ∧
      ∃ a, ∃ ha : a ∈ F.circle.centres, ball x (ρ x) ⊆ ball a (2 * ρ a) ∧
        dist x a < 2 * ρ a ∧
        (let c := F.circle.chart a ha
         letI := mX.rescale (ρ a)⁻¹ (inv_pos.mpr (hρ a))
         ‖c.coord x‖ < 2 * (1 + γ)) := fun j hj =>
  ⟨F.edgeB.centres_subset hj, fun _ hx h2 =>
    ⟨F.edgeB_domain j hj (mem_ball.mpr hx),
      F.toLocalPacketsOn.circle_chart_of_two_BCG4 hγ (F.edgeB_domain j hj (mem_ball.mpr hx)) h2⟩⟩

/-- **The collar band of a revised edge chart is covered by circle charts** (BCG01 edge-collar
clause with the two-stratum fact; review 51 row 2): at a revised edge centre `j`, a point `x` of the
chart's collar band (`d(x, j) < 100Δρ(j)`, `|η_j(x)| ≤ 10Δ`, `Δ/10 ≤ F_s(x)/ρ(x) ≤ 10Δ`) with the
no-three input is two-stratum, lies in `U₁` and is covered by a circle chart (`3βc ≤ β 2 < 1`,
`0 ≤ γ`, `Δ ≥ 1`). -/
theorem LocalPacketsOnBF.edgeB_collar_circle_BCG4
    (F : LocalPacketsOnBF X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
      vs ζ Λz U₁ U₂ Ue₁ Ue₂) (h3βc : 3 * βc ≤ β 2) (hβ2 : β 2 < 1) (hγ : 0 ≤ γ) (hΔ : 1 ≤ Δ)
    {j : X} (hj : j ∈ F.edgeB.centres) {x : X} (hx : dist x j < 100 * Δ * ρ j)
    (hη : let c := F.edgeB.chart j hj
      let hMc : CompleteSpace X := ‹CompleteSpace X›
      letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
      letI := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
      letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
        radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
      letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
        radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
      letI : CompleteSpace X :=
        (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
      |c.coord x| ≤ 10 * Δ)
    (hF1 : Δ / 10 ≤ F.edgeB.smoothing x / ρ x) (hF2 : F.edgeB.smoothing x / ρ x ≤ 10 * Δ)
    (h3 : ¬ @HasEuclideanSplitting.{0, 0} X (mX.rescale (ρ x)⁻¹ (inv_pos.mpr (hρ x))) x 3 (β 3)) :
    x ∈ scaledSplittingStratum.{0, 0} ρ hρ β 2 ∧ x ∈ U₁ ∧
      ∃ a, ∃ ha : a ∈ F.circle.centres, ball x (ρ x) ⊆ ball a (2 * ρ a) ∧
        dist x a < 2 * ρ a ∧
        (let c := F.circle.chart a ha
         letI := mX.rescale (ρ a)⁻¹ (inv_pos.mpr (hρ a))
         ‖c.coord x‖ < 2 * (1 + γ)) := by
  have h2 := F.edgeB.collar_two_stratum_BCG4 h3βc hβ2 hj hx hη hF1 hF2 h3
  have hρj := hρ j
  have hx' : dist x j < 1000 * Δ * ρ j := by
    have : 0 < Δ * ρ j := mul_pos (by linarith) hρj
    nlinarith
  exact ⟨h2, (F.edgeB_collar_circle_cover_BCG4 hγ j hj).2 x hx' h2⟩

end Final

end DifferentialGeometry.Geometry.Collapse
