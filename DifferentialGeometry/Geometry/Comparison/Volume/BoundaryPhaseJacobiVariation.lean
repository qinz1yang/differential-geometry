import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryOriginalPhaseSeed
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryFlowJacobiRegularity

/-!
Actual locally smooth phase seeds construct globally smooth angular seed variations.
Their native incomplete-flow variation fields are smooth Jacobi fields at all existing times.
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set TopologicalSpace
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Riemannian.Variation

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {E : Type*} [ambientNorm : NormedAddCommGroup E]
  [ambientSpace : NormedSpace ℝ E] [ambientFinite : FiniteDimensional ℝ E]
  {H : Type*} [modelTopology : TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [modelBoundaryless : I.Boundaryless]
  {N : Type*} [interiorTopology : TopologicalSpace N] [interiorCharts : ChartedSpace H N]
  [interiorSmooth : IsManifold I ∞ N] [interiorT2 : T2Space N]

theorem boundary_phase_local_variation_jacobi (g : SmoothRiemannianMetric I N)
    (W : Opens E) (σ : E → TangentBundle I N)
    (hσ : ContMDiffOn 𝓘(ℝ, E) I.tangent ∞ σ W) (v₀ w : E) (hv₀ : v₀ ∈ W) :
    ∃ ζ : ℝ → TangentBundle I N,
      ContMDiff 𝓘(ℝ) I.tangent ∞ ζ ∧ ζ 0 = σ v₀ ∧
      ζ =ᶠ[𝓝 (0 : ℝ)] (fun s : ℝ => σ (v₀ + s • w)) ∧
      ∀ t : ℝ, (ζ 0, t) ∈ g.geodesicFlowDomain →
        IsJacobiAt g (fun s => boundaryFlowVariation g ζ 0 s)
          (boundaryFlowJacobiField g ζ) t ∧
        ContMDiffAt 𝓘(ℝ) I.tangent ∞
          (fun s => (⟨boundaryFlowVariation g ζ 0 s,
            boundaryFlowJacobiField g ζ s⟩ : TangentBundle I N)) t := by
  let D : Set ℝ := {s | v₀ + s • w ∈ W}
  have hDopen : IsOpen D := W.isOpen.preimage
    (continuous_const.add (continuous_id.smul continuous_const))
  have hDzero : (0 : ℝ) ∈ D := by
    change v₀ + (0 : ℝ) • w ∈ W
    simpa only [zero_smul, add_zero] using hv₀
  obtain ⟨φ, hφ, hφid, hrange⟩ :=
    DifferentialGeometry.exists_contDiff_eventuallyEq_id_range_subset
      (hDopen.mem_nhds hDzero)
  let curve : ℝ → E := fun s => v₀ + φ s • w
  have hcurve : ContMDiff 𝓘(ℝ) 𝓘(ℝ, E) ∞ curve :=
    (contDiff_const.add (hφ.smul contDiff_const)).contMDiff
  have hcurveW (s : ℝ) : curve s ∈ W := hrange ⟨s, rfl⟩
  let ζ : ℝ → TangentBundle I N := fun s => σ (curve s)
  have hζ : ContMDiff 𝓘(ℝ) I.tangent ∞ ζ := by
    intro s
    exact (hσ.contMDiffAt (W.isOpen.mem_nhds (hcurveW s))).comp s hcurve.contMDiffAt
  have hzero : ζ 0 = σ v₀ := by
    simp only [ζ, curve, hφid.eq_of_nhds, id_eq, zero_smul, add_zero]
  have hev : ζ =ᶠ[𝓝 (0 : ℝ)] (fun s : ℝ => σ (v₀ + s • w)) := by
    filter_upwards [hφid] with s hs
    simp only [ζ, curve, hs, id_eq]
  refine ⟨ζ, hζ, hzero, hev, ?_⟩
  intro t ht
  exact ⟨boundaryFlowJacobiAt g ζ hζ t ht, boundaryFlowJacobi_smooth g ζ hζ t ht⟩

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
