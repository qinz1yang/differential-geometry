import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartFamilyApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortGlobalBlockMapBridge
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAffineHeight
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryWholeSupportCount
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryReplacementStrictBCF2K
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortQuantitativeApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortSupportRows
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortBlockBudgets
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortRawAlignment

/-!
# Boundary port (lane B-PORT-A): LocalChartFamilyApplications (circle-stage closure)

GENERATED from
`DifferentialGeometry/Geometry/Collapse/LocalExport/LocalChartFamilyApplications.lean` by
`build-logs/scratch/B-PORT-A/gen_circle.py` (engine `portlib2.py`); do
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

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {Δ σ : ℝ}
  {Y : Type*} [MetricSpace Y] {p : M} {y₀ : Y} {β : ℝ}
  {α : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), y₀)) β}

end Abstract

section Family

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p}
  {Lmax τ γ δ εr e T V vs ζ Λz : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}

namespace SlimCentreOn

variable {β₁ Δ σs : ℝ} {K : ℕ} {j : X}

end SlimCentreOn

namespace EdgeFamilyOn

variable {β : ℕ → ℝ} {Δ σc μ b s b' s' ε γc βc : ℝ}

/-- The closed support of the edge cutoff lies in the physical ball `B̄(j, 100Δρ(j))`. -/
theorem tsupport_cutoff_subset_BAUGP (F : EdgeFamilyOn X g hmetric ρ hρ β Δ σc μ b s b' s' ε γc βc
    U₁ U₂)
    (j : X) : tsupport (F.cutoff_BAUGA j) ⊆ closedBall j (100 * Δ * ρ j) := by
  by_cases hj : j ∈ F.centres
  · refine (closure_mono ?_).trans closure_ball_subset_closedBall
    intro x hx
    by_contra hxb
    apply hx
    have hd : ¬ (ρ j)⁻¹ * dist x j < 100 * Δ := by
      intro h
      apply hxb
      have h' := (inv_mul_lt_iff₀ (hρ j)).mp h
      rw [mem_ball]
      linarith
    have hc := F.chart_center j hj
    unfold cutoff_BAUGA
    rw [dite_eq_left hj]
    let C := F.chart j hj
    let hMc : CompleteSpace X := ‹CompleteSpace X›
    let mR : MetricSpace X := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    let bR := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    let cR : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
      radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    let iR : IsRiemannianManifold 𝓘(ℝ, E3) X :=
      radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    let kR : CompleteSpace X :=
      (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
    have hc' : C.center = j := hc
    refine Function.extend_apply' _ _ _ ?_
    rintro ⟨a, ha⟩
    apply hd
    have hx' : x ∈ ball C.center (100 * Δ) := ha ▸ a.2
    rw [hc'] at hx'
    exact hx'
  · have h0 : F.cutoff_BAUGA j = 0 := by
      unfold cutoff_BAUGA
      rw [dite_eq_right hj]
    rw [h0, tsupport_zero]
    exact empty_subset _

end EdgeFamilyOn

namespace LocalPacketsOnB

variable {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ} {σc μ b s b' s' ε γc βc : ℝ}

end LocalPacketsOnB

end Family

section Tail

open DifferentialGeometry.Geometry.Comparison.Toponogov DifferentialGeometry.Geometry.Curvature

end Tail


end DifferentialGeometry.Geometry.Collapse
