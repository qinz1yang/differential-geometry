import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ChartJetsL1_O58
import DifferentialGeometry.Geometry.Metric.Distance.Topology
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# CH12-O58 G2: L1 R-B (`C⁰` chart ↔ `riemannianEDistOf`) + R-D (`ApproximatesLinearOn`, preimages)

`[FROZEN] CH12-O58 G2`.  R-B is uniform continuity of the chart and of its inverse on compact sets
for the pseudo-metric `H.metric.toPseudoMetricSpace` (same topology by `rfl`, `edist` =
`riemannianEDistOf` by `rfl`): no path-length argument is needed for L1, which only uses
`C⁰`-smallness in both directions.  R-D: `‖Du‖ ≤ 1/2` on a convex set makes `id + u`
`ApproximatesLinearOn id (1/2)`, and `‖u y₀‖ ≤ ε/2` gives a preimage of `y₀` in `closedBall y₀ ε`.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open Set Metric Filter
open scoped Manifold ContDiff Topology NNReal

namespace GC.LongTime.Ch12

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **R-B (1)**: Riemannian closeness to a compact subset of the chart source gives chart
membership and chart `C⁰`-closeness. -/
theorem chart_C0_of_dist_O58 (H : FiniteVolumeHyperbolicModel.{u}) (c : H.Carrier)
    {K : Set H.Carrier} (hK : IsCompact K) (hKs : K ⊆ (extChartAt (𝓡 3) c).source)
    {θ₀ : ℝ} (hθ₀ : 0 < θ₀) :
    ∃ θ : ℝ, 0 < θ ∧ ∀ p ∈ K, ∀ q : H.Carrier,
      riemannianEDistOf H.metric p q < ENNReal.ofReal θ →
      q ∈ (extChartAt (𝓡 3) c).source ∧
        ‖extChartAt (𝓡 3) c q - extChartAt (𝓡 3) c p‖ < θ₀ := by
  have : LocallyCompactSpace H.Carrier :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin 3)) H.Carrier
  have : RegularSpace H.Carrier := inferInstance
  let _ : PseudoMetricSpace H.Carrier := H.metric.toPseudoMetricSpace
  have hso : IsOpen (extChartAt (𝓡 3) c).source := by exact isOpen_extChartAt_source c
  have hK' : IsCompact K := by exact hK
  obtain ⟨δ₁, hδ₁, hδ₁s⟩ := hK'.exists_thickening_subset_open hso hKs
  have hU := hK'.uniformContinuousAt_of_continuousAt (extChartAt (𝓡 3) c)
    (fun a ha => by exact continuousAt_extChartAt' (hKs ha)) (Metric.dist_mem_uniformity hθ₀)
  obtain ⟨δ₂, hδ₂, hδ₂U⟩ := Metric.mem_uniformity_dist.1 hU
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun p hp q hpq => ?_⟩
  have hd : dist p q < min δ₁ δ₂ := edist_lt_ofReal.1 hpq
  refine ⟨hδ₁s (Metric.mem_thickening_iff.2 ⟨p, hp, ?_⟩), ?_⟩
  · rw [dist_comm]; exact hd.trans_le (min_le_left _ _)
  · have h := hδ₂U (a := p) (b := q) (hd.trans_le (min_le_right _ _)) hp
    rw [Set.mem_ofPred_eq, dist_comm, dist_eq_norm] at h
    exact h

/-- **R-B (2)**: chart closeness to a compact subset of the chart target gives target membership
and Riemannian closeness of the chart inverses. -/
theorem dist_of_chart_C0_O58 (H : FiniteVolumeHyperbolicModel.{u}) (c : H.Carrier)
    {Kc : Set E3} (hKc : IsCompact Kc) (hKct : Kc ⊆ (extChartAt (𝓡 3) c).target)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ y ∈ Kc, ∀ z : E3, ‖z - y‖ < τ →
      z ∈ (extChartAt (𝓡 3) c).target ∧
        riemannianEDistOf H.metric ((extChartAt (𝓡 3) c).symm y)
          ((extChartAt (𝓡 3) c).symm z) < ENNReal.ofReal ρ := by
  have : LocallyCompactSpace H.Carrier :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin 3)) H.Carrier
  have : RegularSpace H.Carrier := inferInstance
  let _ : PseudoMetricSpace H.Carrier := H.metric.toPseudoMetricSpace
  obtain ⟨δ₁, hδ₁, hδ₁s⟩ := hKc.exists_thickening_subset_open (isOpen_extChartAt_target c) hKct
  have hca : ∀ a ∈ Kc, ContinuousAt (extChartAt (𝓡 3) c).symm a := by
    intro a ha
    exact (continuousOn_extChartAt_symm c).continuousAt
      ((isOpen_extChartAt_target c).mem_nhds (hKct ha))
  have hU := hKc.uniformContinuousAt_of_continuousAt (extChartAt (𝓡 3) c).symm hca
    (Metric.dist_mem_uniformity hρ)
  obtain ⟨δ₂, hδ₂, hδ₂U⟩ := Metric.mem_uniformity_dist.1 hU
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun y hy z hz => ?_⟩
  have hd : dist y z < min δ₁ δ₂ := by rw [dist_comm, dist_eq_norm]; exact hz
  refine ⟨hδ₁s (Metric.mem_thickening_iff.2 ⟨y, hy, ?_⟩), ?_⟩
  · rw [dist_comm]; exact hd.trans_le (min_le_left _ _)
  · have h := hδ₂U (a := y) (b := z) (hd.trans_le (min_le_right _ _)) hy
    exact edist_lt_ofReal.2 h

/-- **R-D (1)**: `‖Du‖ ≤ 1/2` on a convex set makes `id + u` approximately the identity. -/
theorem approximatesLinearOn_of_fderiv_O58 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : E → E} {s : Set E} (hs : Convex ℝ s) (hd : ∀ y ∈ s, DifferentiableAt ℝ u y)
    (hD : ∀ y ∈ s, ‖fderiv ℝ u y‖ ≤ 1 / 2) :
    ApproximatesLinearOn (fun y => y + u y) ((ContinuousLinearEquiv.refl ℝ E : E ≃L[ℝ] E) :
      E →L[ℝ] E) s (1 / 2 : ℝ≥0) := by
  intro x hx y hy
  have h := hs.norm_image_sub_le_of_norm_fderiv_le hd hD hy hx
  have hcoe : ((1 / 2 : ℝ≥0) : ℝ) = 1 / 2 := by norm_num
  simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.refl_apply, hcoe]
  have : x + u x - (y + u y) - (x - y) = u x - u y := by abel
  rw [this]
  exact h

/-- **R-D (2)**: a preimage of `y₀` under `id + u` near `y₀`. -/
theorem exists_preimage_of_small_O58 {u : E3 → E3} {y₀ : E3} {ε : ℝ} (hε : 0 < ε)
    (hd : ∀ y ∈ closedBall y₀ ε, DifferentiableAt ℝ u y)
    (hD : ∀ y ∈ closedBall y₀ ε, ‖fderiv ℝ u y‖ ≤ 1 / 2) (h0 : ‖u y₀‖ ≤ ε / 2) :
    ∃ y ∈ closedBall y₀ ε, y + u y = y₀ := by
  have hf := approximatesLinearOn_of_fderiv_O58 (convex_closedBall y₀ ε) hd hD
  have hS := hf.surjOn_closedBall_of_nonlinearRightInverse
    (ContinuousLinearEquiv.refl ℝ E3).toNonlinearRightInverse hε.le subset_rfl
  have hN : (((ContinuousLinearEquiv.refl ℝ E3).toNonlinearRightInverse.nnnorm : ℝ≥0) : ℝ) = 1 := by
    simp [ContinuousLinearEquiv.toNonlinearRightInverse]
  rw [hN] at hS
  have hmem : y₀ ∈ closedBall (y₀ + u y₀) (((1 : ℝ)⁻¹ - ((1 / 2 : ℝ≥0) : ℝ)) * ε) := by
    rw [mem_closedBall, dist_eq_norm]
    have : y₀ - (y₀ + u y₀) = -u y₀ := by abel
    rw [this, norm_neg]
    norm_num
    linarith
  obtain ⟨y, hy, hyy⟩ := hS hmem
  exact ⟨y, hy, hyy⟩

end GC.LongTime.Ch12
