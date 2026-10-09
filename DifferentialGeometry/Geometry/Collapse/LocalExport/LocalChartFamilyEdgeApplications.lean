import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartFamilyEdgeProducer
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartFamilyBindings

/-!
# The edge link of the local chart family (packet (iv) consumers)

* `LocalChartFamilyE.edge_coord_sub_Qn_fst`: at normalized scale, the chart coordinate is within
  `μΔ ≤ Δ/100` of the first coordinate of the chart's recorded coarse-border composite `Q_j = Qn`
  on `B(j, 100Δ)` (`EdgeChart.value` and `EdgeChart.Qn_fst`).
* `LocalChartFamilyE.exists_edge_link`: the same link in the physical form of chapter 14's FC17/FC18
  rows (`ActualEdgeSupportRows.lean`): a plane map `Q` (the composite `Q_j` with its second coordinate
  truncated at `0`, equal to `Q_j` on `B(j, 200Δ)`) with `Q(j) = 0`, `Q₂ ≥ 0`, distortion `≤ τΔ`
  against `ρ(j)⁻¹ d` on `B(j, 200Δρ(j))`, the closed weak edge set at height `< Δ/10` on
  `B(j, 120Δρ(j))`, and `|η_j − Q₁| ≤ Δ/100` on `B(j, 100Δρ(j))` for `η_j = L.edge.coord j`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

universe u

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

namespace LocalChartFamilyE

variable {X : Type u} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ : ℝ}

/-- **The edge link at normalized scale.** -/
theorem edge_coord_sub_Qn_fst
    (L : LocalChartFamilyE X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ)
    (hΔ : 0 < Δ) (hμ : μ ≤ 1 / 100) {j : X} (hj : j ∈ L.edge.centres) :
    let c := L.edge.chart j hj
    let hMc : CompleteSpace X := complete_of_compact
    letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
      radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
      radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI : CompleteSpace X :=
      (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
    ∀ x ∈ ball j (100 * Δ), |c.coord x - (c.Qn x).fst| ≤ Δ / 100 := by
  have hcen := L.edge.chart_center j hj
  intro c hMc
  let mR : MetricSpace X := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let bR := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let cR : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let iR : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let kR : CompleteSpace X := (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
  have hcen' : c.center = j := hcen
  intro x hx
  have hx' : x ∈ ball c.center (100 * Δ) := by rw [hcen']; exact hx
  have hv := c.value x hx'
  rw [← c.Qn_fst x] at hv
  have hμΔ : μ * Δ ≤ Δ / 100 := by nlinarith
  linarith

/-- **The edge link in the physical form of FC17/FC18.** -/
theorem exists_edge_link
    (L : LocalChartFamilyE X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ)
    (hΔ : 0 < Δ) (hμ : μ ≤ 1 / 100) (hτ : τ < 1 / 10) {j : X} (hj : j ∈ L.edge.centres) :
    ∃ Q : X → WithLp 2 (ℝ × ℝ), Q j = 0 ∧ (∀ x, 0 ≤ (Q x).snd) ∧
      (∀ x y, (ρ j)⁻¹ * dist x j < 200 * Δ → (ρ j)⁻¹ * dist y j < 200 * Δ →
        |dist (Q x) (Q y) - (ρ j)⁻¹ * dist x y| ≤ τ * Δ) ∧
      (∀ z ∈ closure {y : X | @isEdgePoint.{u, 0} X (mX.rescale (ρ y)⁻¹ (inv_pos.mpr (hρ y)))
          y Δ b' s'}, (ρ j)⁻¹ * dist z j < 120 * Δ → (Q z).snd < Δ / 10) ∧
      (∀ x, (ρ j)⁻¹ * dist x j < 100 * Δ → |L.edge.coord j x - (Q x).fst| ≤ Δ / 100) := by
  have hco := L.edge_coarse j hj
  have hlink := L.edge_coord_sub_Qn_fst hΔ hμ hj
  let C := L.edge.chart j hj
  let hMc : CompleteSpace X := complete_of_compact
  let mR : MetricSpace X := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let bR := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let cR : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let iR : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let kR : CompleteSpace X := (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
  obtain ⟨h0, hdist, hnn, -, hlow, -⟩ := hco
  let Qn : X → WithLp 2 (ℝ × ℝ) := C.Qn
  let Q : X → WithLp 2 (ℝ × ℝ) := fun x => WithLp.toLp 2 ((Qn x).fst, max 0 (Qn x).snd)
  have hQ : ∀ x, (ρ j)⁻¹ * @dist X mX.toDist x j < 200 * Δ → Q x = Qn x := by
    intro x hx
    have h := hnn x hx
    change WithLp.toLp 2 ((Qn x).fst, max 0 (Qn x).snd) = Qn x
    rw [max_eq_right h]
    rfl
  have hτΔ : τ * Δ < Δ / 10 := by nlinarith
  refine ⟨Q, ?_, fun x => le_max_left _ _, ?_, ?_, ?_⟩
  · rw [hQ j (by rw [@dist_self X mX.toPseudoMetricSpace j, mul_zero]; positivity)]
    exact h0
  · intro x y hx hy
    rw [hQ x hx, hQ y hy]
    exact hdist x hx y hy
  · intro z hz hzj
    have hz' : (ρ j)⁻¹ * @dist X mX.toDist z j < 200 * Δ := by linarith
    rw [hQ z hz']
    exact (hlow z ⟨hz, show (ρ j)⁻¹ * @dist X mX.toDist z j < 190 * Δ by linarith⟩).trans_lt hτΔ
  · intro x hx
    have hx' : (ρ j)⁻¹ * @dist X mX.toDist x j < 200 * Δ := by linarith
    rw [hQ x hx']
    unfold EdgeFamily.coord
    simp only [hj, ↓reduceDIte]
    exact hlink x hx

end LocalChartFamilyE

end DifferentialGeometry.Geometry.Collapse
