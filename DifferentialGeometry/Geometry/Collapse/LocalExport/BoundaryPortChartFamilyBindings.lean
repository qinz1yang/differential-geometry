import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartFamilyBindings
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortChartFamilyApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortGlobalBlockMapBridge
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAffineHeight
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryWholeSupportCount
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryReplacementStrictBCF2K
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortQuantitativeApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortSupportRows
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortBlockBudgets
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortRawAlignment

/-!
# Boundary port (lane B-PORT-A): LocalChartFamilyBindings (circle-stage closure)

GENERATED from `DifferentialGeometry/Geometry/Collapse/LocalExport/LocalChartFamilyBindings.lean`
by `build-logs/scratch/B-PORT-A/gen_circle.py` (engine `portlib2.py`); do
not edit by hand, re-run the script. Closed family → boundary family (`LocalPacketsOnB` /
`LocalPacketsOnBF`, complete σ-compact carrier, regional `…On` families, ACTIVE edge `edgeB`); every
ported declaration `x` ↦ `x_BAUGP` (namespaced `T.m` ↦ `TOn.m_BAUGP`). Substitution table and
failure points: `build-logs/resume/state-B-PORT-A.md`.
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

universe u

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

section Circle

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : Type*} [mX : MetricSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {β : ℕ → ℝ} {U₁ U₂ : Set X}

/-- The closed support of a circle cutoff lies in `B̄(j, 102ρ(j))`. -/
theorem CircleFamilyOn.tsupport_cutoff_subset_closedBall_BAUGP (F : CircleFamilyOn I X ρ hρ β U₁
    U₂) {j : X}
    (hj : j ∈ F.centres) : tsupport (F.cutoff j) ⊆ closedBall j (102 * ρ j) := by
  refine (closure_mono ?_).trans closure_ball_subset_closedBall
  intro x hx
  have h1 := F.coord_lt_of_cutoff_ne_zero j hj x hx
  have hc := F.chart_center j hj
  let c := F.chart j hj
  let mR : MetricSpace X := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  have hc' : c.center = j := hc
  have h1' : x ∈ ball c.center 200 ∧ ‖c.coord x‖ < 9 := by
    rw [hc']
    exact h1
  have h2 : x ∈ ball c.center 102 := c.enclosure x h1'.1 (by linarith [h1'.2])
  rw [hc'] at h2
  have h3 : (ρ j)⁻¹ * @dist X mX.toDist x j < 102 := h2
  rw [inv_mul_lt_iff₀ (hρ j)] at h3
  change @dist X mX.toDist x j < 102 * ρ j
  linarith

end Circle

section Family

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p}
  {Lmax τ γ δ εr e T V vs ζ Λz : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}

namespace SlimCentreOn

variable {β₁ Δ σs : ℝ} {K : ℕ} {j : X}

/-- FC27 (slim): the slim cutoff is one where `|η_j| ≤ 8·10⁵Δ` in `B(j, 10⁶Δρ(j))`. -/
theorem cutoff_eq_one_of_abs_coord_le_BAUGP (c : SlimCentreOn X g hmetric ρ hρ β₁ Δ σs K j) {x : X}
    (hx : x ∈ ball j (10 ^ 6 * Δ * ρ j)) (hc : |c.coord_BCG2 x| ≤ 8 * 10 ^ 5 * Δ) : c.cutoff_BCNT
        x = 1 := by
  have hd : (ρ j)⁻¹ * dist x j < 10 ^ 6 * Δ := inv_mul_dist_lt_of_mem_ball_LC87 (hρ j) hx
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
  exact P.cutoff_eq_one x hd hc

end SlimCentreOn

namespace EdgeFamilyOn

variable {β : ℕ → ℝ} {Δ σc μ b s b' s' ε γc βc : ℝ}

end EdgeFamilyOn

namespace LocalPacketsOnB

variable {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ} {σc μ b s b' s' ε γc βc : ℝ}

/-- **FC12 on the actual circle supports.** For a circle centre `j` whose closed cutoff support
meets `B(p, Rρ(p))`: comparable scales, the test ball inside `B(j, (102 + 4R)ρ(j))`, which lies in
the
chart's smooth domain `B(j, 200ρ(j))`, with complement-distance margin `(98 - 4R)ρ(j)`. -/
theorem circle_support_scale_buffer_BAUGP
    (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂) (hΛ : 0 ≤ Λ)
    {j : X} (hj : j ∈ L.circle.centres) {p : X} {R : ℝ} (hR : 0 < R)
    (hbudget : Λ * max R 102 ≤ 1 / 4) (hgap : 4 * R < 98)
    (hmeet : (tsupport (L.circle.cutoff j) ∩ ball p (R * ρ p)).Nonempty) :
    ρ j / ρ p ∈ Icc (1 / 2) 2 ∧ dist j p ≤ (R + 2 * 102) * ρ p ∧
      ball p (R * ρ p) ⊆ ball j ((102 + 4 * R) * ρ j) ∧
      ball j ((102 + 4 * R) * ρ j) ⊆ ball j (200 * ρ j) ∧
      ∀ x ∈ ball p (R * ρ p), (ball j (200 * ρ j))ᶜ.Nonempty →
        (200 - 102 - 4 * R) * ρ j ≤ infDist x (ball j (200 * ρ j))ᶜ :=
  DifferentialGeometry.Geometry.Fibration.finite_packet_support_scale_buffer L.lipschitz_scale
    (hρ p) (hρ j) hR (by norm_num) (by rwa [Real.coe_toNNReal _ hΛ]) (by linarith)
    (L.circle.tsupport_cutoff_subset_closedBall_BAUGP hj) subset_rfl hmeet

/-- **FC12 on the actual slim supports.** For a slim centre `j` whose closed cutoff support meets
`B(p, Rρ(p))`: comparable scales, the test ball inside `B(j, (0.91·10⁶Δ + 4R)ρ(j))`, which lies in
`B(j, 10⁶Δρ(j))` where `η_j` is smooth, with complement-distance margin. -/
theorem slim_support_scale_buffer_BAUGP
    (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂) (hΛ : 0 ≤ Λ)
    (hΔ : 0 < Δ) {j : X} (hj : j ∈ L.slim.centres) {p : X} {R : ℝ} (hR : 0 < R)
    (hbudget : Λ * max R (91 / 100 * (10 ^ 6 * Δ)) ≤ 1 / 4)
    (hgap : 4 * R < 10 ^ 6 * Δ - 91 / 100 * (10 ^ 6 * Δ))
    (hmeet : (tsupport (L.slim.cutoff_BCNT j) ∩ ball p (R * ρ p)).Nonempty) :
    ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (L.slim.centre j hj).coord_BCG2 (ball j (10 ^ 6 * Δ * ρ j)) ∧
      ρ j / ρ p ∈ Icc (1 / 2) 2 ∧ dist j p ≤ (R + 2 * (91 / 100 * (10 ^ 6 * Δ))) * ρ p ∧
      ball p (R * ρ p) ⊆ ball j ((91 / 100 * (10 ^ 6 * Δ) + 4 * R) * ρ j) ∧
      ball j ((91 / 100 * (10 ^ 6 * Δ) + 4 * R) * ρ j) ⊆ ball j (10 ^ 6 * Δ * ρ j) ∧
      ∀ x ∈ ball p (R * ρ p), (ball j (10 ^ 6 * Δ * ρ j))ᶜ.Nonempty →
        (10 ^ 6 * Δ - 91 / 100 * (10 ^ 6 * Δ) - 4 * R) * ρ j ≤
          infDist x (ball j (10 ^ 6 * Δ * ρ j))ᶜ := by
  have hS : tsupport (L.slim.cutoff_BCNT j) ⊆ closedBall j (91 / 100 * (10 ^ 6 * Δ) * ρ j) := by
    unfold SlimFamilyOn.cutoff_BCNT
    rw [dite_eq_left hj]
    exact (L.slim.centre j hj).tsupport_cutoff_subset_BCNT
  exact ⟨(L.slim.centre j hj).contMDiffOn_coord_BAUGA,
    DifferentialGeometry.Geometry.Fibration.finite_packet_support_scale_buffer L.lipschitz_scale
      (hρ p) (hρ j) hR (by positivity) (by rwa [Real.coe_toNNReal _ hΛ]) hgap hS subset_rfl hmeet⟩

end LocalPacketsOnB

end Family


end DifferentialGeometry.Geometry.Collapse
