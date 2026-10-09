import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsDisk
import DifferentialGeometry.Geometry.Collapse.LocalExport.EdgeDiskPacketApplications

/-!
# Consumers of the LC87 G10 family `LocalChartPacketsD`

* `EdgeDiskPacket.tsupport_cutoff_subset_ball_of_eq`, `EdgeDiskPacket.fibre_closedCell_of_eq`: the
  packet consumers of `EdgeDiskPacketApplications` stated for the edge chart `c` over which the
  packet sits (`P.toEdgeChart = c`).
* `LocalChartPacketsD.edge_tsupport_cutoff_subset_ball`: LC87's edge-domain margin on the final
  family — the family's edge cutoff at every edge centre `j` is supported in the physical ball
  `B(j, 13Δρ(j))` (the frozen G2 bound was `B̄(j, 100Δρ(j))`), well inside the chart domain.
* `LocalChartPacketsD.edge_zeroFibre_closedCell`: at every edge centre the entire zero fibre
  `{y ∈ B(j, 100Δ) : η_j y = 0, H y ≤ 4Δ}` of the family's own chart (normalized at `j`, the
  family's ONE smoothing) is homeomorphic to the closed disk, compact and connected (LFR33's
  proper `D²`-bundle fibre).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology NNReal
open DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.Riemannian
open GC.MetricGeometry
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

section Packet

variable {M : Type*} [mM : MetricSpace M] [ChartedSpace E3 M] [IsManifold 𝓘(ℝ, E3) ∞ M]
  [SigmaCompactSpace M] [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E3) x)]
  [IsRiemannianManifold 𝓘(ℝ, E3) M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E3 (fun x : M => TangentSpace 𝓘(ℝ, E3) x)]
  {g : SmoothRiemannianMetric 𝓘(ℝ, E3) M} {hEnorm : IsMetricNorm g}
  {Δ σ μ b γ β : ℝ} {A : Set M} {ρ F : M → ℝ}

/-- The packet margin for the chart under the packet: the edge cutoff of `c` is supported in
`B(c.center, 13Δ)`. -/
theorem EdgeDiskPacket.tsupport_cutoff_subset_ball_of_eq
    (P : EdgeDiskPacket g hEnorm Δ σ μ b γ β A ρ F) {c : EdgeChart g hEnorm Δ σ μ b γ β A ρ F}
    (hP : P.toEdgeChart = c) (hΔ : 0 < Δ) :
    tsupport ((Subtype.val : ball c.center (100 * Δ) → M).extend
      (fun x => edgeCoordinateProfile (c.coord x.val / Δ) *
        edgeHeightProfile (F x.val / (Δ * ρ x.val))) 0) ⊆ ball c.center (13 * Δ) := by
  subst hP
  exact P.tsupport_cutoff_subset_ball hΔ

/-- The disk fibre for the chart under the packet: the entire zero fibre of `c` is homeomorphic to
the closed disk, compact and connected. -/
theorem EdgeDiskPacket.fibre_closedCell_of_eq
    (P : EdgeDiskPacket g hEnorm Δ σ μ b γ β A ρ F) {c : EdgeChart g hEnorm Δ σ μ b γ β A ρ F}
    (hP : P.toEdgeChart = c) (hΔ : 0 < Δ) :
    Nonempty ({y : M // y ∈ ball c.center (100 * Δ) ∧ c.coord y = 0 ∧
        edgeRowHeight Δ F ρ y ≤ 4 * Δ} ≃ₜ ClosedCell 2) ∧
      CompactSpace {y : M // y ∈ ball c.center (100 * Δ) ∧ c.coord y = 0 ∧
        edgeRowHeight Δ F ρ y ≤ 4 * Δ} ∧
      ConnectedSpace {y : M // y ∈ ball c.center (100 * Δ) ∧ c.coord y = 0 ∧
        edgeRowHeight Δ F ρ y ≤ 4 * Δ} := by
  subst hP
  exact P.fibre_homeomorph_closedCell hΔ

end Packet

namespace LocalChartPacketsD

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}

/-- **LC87's edge-domain margin on the final family.** At every edge centre `j` the family's edge
cutoff is supported in the physical ball `B(j, 13Δρ(j))`. -/
theorem edge_tsupport_cutoff_subset_ball
    (L : LocalChartPacketsD X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΔ : 0 < Δ) {j : X} (hj : j ∈ L.edge.centres) :
    tsupport (L.edge.cutoff j) ⊆ ball j (13 * Δ * ρ j) := by
  have hc := L.edge.chart_center j hj
  have hD := L.edgeDisk j hj
  unfold EdgeFamily.cutoff
  rw [dite_eq_left hj]
  let C := L.edge.chart j hj
  have hsig : SigmaCompactSpace X := inferInstance
  let hMc : CompleteSpace X := complete_of_compact
  let mR : MetricSpace X := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let bR := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let cR : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let iR : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let kR : CompleteSpace X := (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
  have hc' : C.center = j := hc
  obtain ⟨P, hP⟩ := hD
  intro x hx
  have hx' : x ∈ ball C.center (13 * Δ) := P.tsupport_cutoff_subset_ball_of_eq hP hΔ hx
  rw [hc'] at hx'
  have hd : (ρ j)⁻¹ * @dist X mX.toDist x j < 13 * Δ := hx'
  have h := (inv_mul_lt_iff₀ (hρ j)).mp hd
  exact (show @dist X mX.toDist x j < 13 * Δ * ρ j by linarith)

/-- **LFR33's disk fibre on the final family.** At every edge centre `j` the entire zero fibre of
the family's own edge chart (normalized at `j`, the family's ONE smoothing) is homeomorphic to the
closed disk, compact and connected. -/
theorem edge_zeroFibre_closedCell
    (L : LocalChartPacketsD X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΔ : 0 < Δ) {j : X} (hj : j ∈ L.edge.centres) :
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
    Nonempty ({y : X // y ∈ ball j (100 * Δ) ∧ c.coord y = 0 ∧
        edgeRowHeight Δ (fun x => Fs x / ρ j) (fun x => ρ x / ρ j) y ≤ 4 * Δ} ≃ₜ ClosedCell 2) ∧
      CompactSpace {y : X // y ∈ ball j (100 * Δ) ∧ c.coord y = 0 ∧
        edgeRowHeight Δ (fun x => Fs x / ρ j) (fun x => ρ x / ρ j) y ≤ 4 * Δ} ∧
      ConnectedSpace {y : X // y ∈ ball j (100 * Δ) ∧ c.coord y = 0 ∧
        edgeRowHeight Δ (fun x => Fs x / ρ j) (fun x => ρ x / ρ j) y ≤ 4 * Δ} := by
  have hsig : SigmaCompactSpace X := inferInstance
  have hc := L.edge.chart_center j hj
  have hD := L.edgeDisk j hj
  intro c Fs hMc
  let mR : MetricSpace X := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let bR := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let cR : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let iR : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let kR : CompleteSpace X := (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
  have hc' : c.center = j := hc
  obtain ⟨P, hP⟩ := hD
  have h := P.fibre_closedCell_of_eq hP hΔ
  rw [hc'] at h
  exact h

end LocalChartPacketsD

end DifferentialGeometry.Geometry.Collapse
