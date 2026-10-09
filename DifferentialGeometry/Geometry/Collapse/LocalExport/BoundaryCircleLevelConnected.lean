import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCircleLevelCoordinates
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryWholeFibreConnected
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortFirstComparisonList
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortConstantComparison
import DifferentialGeometry.Geometry.Collapse.LocalExport.OriginalSlabCompactness
import DifferentialGeometry.Geometry.Fibration.ActualCircleGramExternal
import DifferentialGeometry.Geometry.Fibration.ActualOriginalSlabs

/-!
# O-WF G2a: the whole adjusted circle level is connected (GAF07 Level on the boundary chain)

Closed twin `Gaf02Chain.gaf07_circle_level_GAFC` (`Fibration/ActualStageChainGaf07Level.lean`).
On the boundary chain `C`, for a circle chart `j` and `‖a‖ < 4`, the WHOLE adjusted level
`{q ∈ Y_j | κ_j(f₀ q) = a}` of `W°` is connected, `Y_j = {q ∈ B(j, 200ρ_j) | ‖η_j q‖ < 5}`
(`circleY_OWF`): FC34a (S-BAUG-D2's `connected_adjusted_level_of_isotopy_BAUGD`) with

* the value / derivative clauses `‖κ_j f₀ − η_j‖ < 1/800`, `‖D(κ_j f₀) − Dη_j‖ ≤ H ν`
  (S-BAUG-D2's `circle_final_coordinates_BAUGD`, gauge `ν q u = ρ_j⁻¹ √ĝ(u, u)`);
* TCP01's right inverse of `Dη_j` of gauge size `≤ 2` (`circle_gram_right_inverse_OWF`, from the
  boundary Gram bounds `circleAdapted_gram_lower_BBP` and the upper bound
  `circleAdapted_physical_KA2_BAUGP` through `gram_external_right_inverse_FAM2`);
* the compact slab and the connected original level of the family's circle chart
  (`isCompact_circleSlab_OWF`, `isConnected_circleLevel_OWF`; LFR07's chart, generic over any
  `LocalPacketsOnB`).

Register premises: `c₂ < 1/1000`, `β₂ ≤ 10⁻⁷`, `γ + β₂ < 1/10` (the closed GAF07's).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Analysis
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open scoped ENNReal

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

section Generic

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}
  {vs ζ Λz : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}

/-- **The whole closed circle slab** `{p ∈ B(j, 200ρ(j)) | ‖η_j p‖ ≤ a}` is compact (`a < 100`). -/
theorem isCompact_circleSlab_OWF
    (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
      U₁ U₂ Ue₁ Ue₂) {j : X} (hj : j ∈ L.circle.centres) {a : ℝ} (ha : a < 100) :
    IsCompact {p | p ∈ ball j (200 * ρ j) ∧ ‖cgpCircleCoord_BAUGP L j hj p‖ ≤ a} := by
  have hr := hρ j
  have hc0 := L.circle.chart_center j hj
  let c := L.circle.chart j hj
  let mR : MetricSpace X := mX.rescale (ρ j)⁻¹ (inv_pos.mpr hr)
  have hc : c.center = j := hc0
  have h1 := c.isCompact_closedSlab_FPRE ha
  rw [hc] at h1
  convert h1 using 1
  ext x
  exact and_congr_left' (mem_ball_rescale_iff_FPRE (m := mX) hr (k := 200)).symm

/-- **The original circle level is connected** (LFR07's fibres): for `‖a‖ < 100`,
`{p ∈ B(j, 200ρ(j)) | η_j p = a}` is connected. -/
theorem isConnected_circleLevel_OWF
    (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
      U₁ U₂ Ue₁ Ue₂) {j : X} (hj : j ∈ L.circle.centres) {a : ℝ²} (ha : ‖a‖ < 100) :
    IsConnected {p | p ∈ ball j (200 * ρ j) ∧ cgpCircleCoord_BAUGP L j hj p = a} := by
  have hr := hρ j
  have hc0 := L.circle.chart_center j hj
  let c := L.circle.chart j hj
  let mR : MetricSpace X := mX.rescale (ρ j)⁻¹ (inv_pos.mpr hr)
  have hc : c.center = j := hc0
  have hz : a ∈ planeBallOpens 100 := mem_planeBallOpens_iff.mpr ha
  have hf := (c.fibres ⟨a, hz⟩).2
  have him := hf.image Subtype.val continuous_subtype_val.continuousOn
  convert him using 1
  ext x
  constructor
  · rintro ⟨hx, hxa⟩
    have hxR : x ∈ @ball X mR.toPseudoMetricSpace c.center 200 := by
      rw [hc]
      exact (mem_ball_rescale_iff_FPRE (m := mX) hr (k := 200)).mpr hx
    have hxa' : c.coord x = a := hxa
    refine ⟨⟨x, hxR, ?_⟩, ?_, rfl⟩
    · change c.coord x ∈ ball (0 : ℝ²) 100
      rw [hxa', mem_ball_zero_iff]
      exact ha
    · exact Subtype.ext hxa'
  · intro hx
    obtain ⟨y, hy, hyx⟩ := hx
    have hy' : c.coord x = a := by
      rw [← hyx]
      exact congrArg Subtype.val hy
    have hxR' : x ∈ @ball X mR.toPseudoMetricSpace c.center 200 := hyx ▸ y.2.1
    rw [hc] at hxR'
    exact ⟨(mem_ball_rescale_iff_FPRE (m := mX) hr (k := 200)).mp hxR', hy'⟩

/-- **TCP01's right inverse of the circle differential** on the boundary family: for
`β₂ ≤ 10⁻⁷` and `γ + β₂ < 1/10`, at every `x ∈ B(j, 200ρ(j))` the differential `Dη_j(x)` has a
right inverse `R` with `ρ(j)⁻¹ √g(Rw, Rw) ≤ 2‖w‖`. -/
theorem circle_gram_right_inverse_OWF
    (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
      U₁ U₂ Ue₁ Ue₂) (hβ : β 2 ≤ 1 / 10000000) (hd : γ + β 2 < 1 / 10) {j : X}
    (hj : j ∈ L.circle.centres) {x : X} (hx : x ∈ ball j (200 * ρ j)) :
    ∃ R : ℝ² →L[ℝ] E3,
      (show E3 →L[ℝ] ℝ² from mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²) (cgpCircleCoord_BAUGP L j hj) x).comp R =
        ContinuousLinearMap.id ℝ ℝ² ∧
      ∀ w, (ρ j)⁻¹ * Real.sqrt (g.inner x (R w) (R w)) ≤ 2 * ‖w‖ := by
  have hrj := hρ j
  have hγ0 := circle_quality_nonneg_KA4_BAUGP L hj
  have hβ0 : 0 ≤ β 2 := by
    let Aj := L.circleAdapted j hj
    let _ := Aj.instY
    exact (@KleinerLottApprox.error_pos X _ (mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))) _ _ _ _
      Aj.split).le
  let _ := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr hrj)
  have hnorm : ∀ w : TangentSpace 𝓘(ℝ, E3) x, ‖w‖ = Real.sqrt ((ρ j)⁻¹ ^ 2 * g.inner x w w) :=
    fun w => norm_tangent_radialScaled_KA4 g hrj x w
  have hηd : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²) (cgpCircleCoord_BAUGP L j hj) x :=
    ((cgpCircleCoord_contMDiffOn_BAUGP L hj).contMDiffAt
      (isOpen_ball.mem_nhds hx)).mdifferentiableAt (by simp)
  have hphys := (circleAdapted_physical_KA2_BAUGP L hγ0 hj).2
  have hup : ∀ w : TangentSpace 𝓘(ℝ, E3) x, ‖w‖ = 1 →
      ‖mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord_BAUGP L j hj) x w‖ ≤ 1 + γ := by
    intro w hw
    have h := norm_mvfderiv_le_of_lipschitzOn_riem g hmetric isOpen_ball hx hηd
      (L := (1 + γ) / ρ j) (by positivity) hphys w
    have hs : Real.sqrt ((ρ j)⁻¹ ^ 2 * g.inner x w w) =
        (ρ j)⁻¹ * Real.sqrt (g.inner x w w) := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (inv_pos.mpr hrj).le]
    have h1 : (ρ j)⁻¹ * Real.sqrt (g.inner x w w) = 1 := by rw [← hs, ← hnorm, hw]
    calc ‖mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord_BAUGP L j hj) x w‖
        ≤ (1 + γ) / ρ j * Real.sqrt (g.inner x w w) := h
      _ = (1 + γ) * ((ρ j)⁻¹ * Real.sqrt (g.inner x w w)) := by ring
      _ = 1 + γ := by rw [h1, mul_one]
  have hlow : ∀ ξ : ℝ², ‖ξ‖ = 1 → ∃ w : TangentSpace 𝓘(ℝ, E3) x, ‖w‖ = 1 ∧
      1 - (γ + β 2) < inner ℝ (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord_BAUGP L j hj) x w) ξ := by
    intro ξ hξ
    obtain ⟨w, hw1, hw2⟩ := circleAdapted_gram_lower_BBP L hβ hj hx ξ hξ
    refine ⟨w, by rw [hnorm, hw1, Real.sqrt_one], ?_⟩
    have hcs : inner ℝ (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord_BAUGP L j hj) x w - ξ) ξ ≥
        -‖mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord_BAUGP L j hj) x w - ξ‖ := by
      have h := real_inner_le_norm (-(mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord_BAUGP L j hj) x w - ξ)) ξ
      rw [inner_neg_left, norm_neg, hξ, mul_one] at h
      linarith
    have hsplit : inner ℝ (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord_BAUGP L j hj) x w) ξ =
        inner ℝ (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord_BAUGP L j hj) x w - ξ) ξ +
          inner ℝ ξ ξ := by
      rw [inner_sub_left]
      ring
    have hξξ : inner ℝ ξ ξ = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, hξ]; norm_num
    linarith
  obtain ⟨-, R, hR, -, hR2⟩ := gram_external_right_inverse_FAM2
    (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord_BAUGP L j hj) x) hγ0 (by linarith) hd hup hlow
  refine ⟨R, hR, fun w => ?_⟩
  have hn := norm_tangent_radialScaled_KA4 g hrj x (R w)
  have hle : ‖R w‖ ≤ 2 * ‖w‖ :=
    (R.le_opNorm w).trans (mul_le_mul_of_nonneg_right hR2.le (norm_nonneg w))
  have hs : Real.sqrt ((ρ j)⁻¹ ^ 2 * g.inner x (R w) (R w)) =
      (ρ j)⁻¹ * Real.sqrt (g.inner x (R w) (R w)) := by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (inv_pos.mpr hrj).le]
  calc (ρ j)⁻¹ * Real.sqrt _ = Real.sqrt ((ρ j)⁻¹ ^ 2 * g.inner x (R w) (R w)) := hs.symm
    _ = ‖R w‖ := hn.symm
    _ ≤ 2 * ‖w‖ := hle

end Generic

end DifferentialGeometry.Geometry.Collapse
