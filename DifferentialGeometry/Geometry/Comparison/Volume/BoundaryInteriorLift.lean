import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryInteriorFlowMatching

/-!
Original smooth interior curves lift smoothly into the genuine boundaryless interior atlas.
An original smooth geodesic therefore seeds and matches the actual incomplete maximal flow.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff
open DifferentialGeometry.Geometry.Riemannian.Geodesic

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {E : Type*} [ambientNorm : NormedAddCommGroup E]
  [ambientSpace : NormedSpace ℝ E] [ambientFinite : FiniteDimensional ℝ E]
  {H : Type*} [modelTopology : TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [manifoldTopology : TopologicalSpace M] [manifoldCharts : ChartedSpace H M]
  [manifoldSmooth : IsManifold I ∞ M] [manifoldT2 : T2Space M]

private theorem interiorLift_infty_ne_zero : (∞ : WithTop ℕ∞) ≠ 0 := by simp

omit ambientFinite manifoldT2 in
theorem boundaryInteriorAtlas_smooth_iff :
    let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
      interiorLift_infty_ne_zero (M := M)
    let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
    let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
    ∀ (γ : ℝ → U) (t : ℝ),
      ContMDiffAt 𝓘(ℝ) 𝓘(ℝ, E) ∞ γ t ↔
        ContMDiffAt 𝓘(ℝ) I ∞ (fun s => (γ s : M)) t := by
  let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
    interiorLift_infty_ne_zero (M := M)
  let Φ := DifferentialGeometry.Manifold.interiorAtlasDiffeomorph I ∞ (M := U)
  let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
  let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
  dsimp only
  intro γ t
  constructor
  · intro hγ
    have hval := DifferentialGeometry.Manifold.contMDiff_intrinsicInterior_val
      I ∞ interiorLift_infty_ne_zero (M := M)
    exact hval.contMDiffAt.comp t hγ
  · intro hγ
    have hold : ContMDiffAt 𝓘(ℝ) I ∞ γ t :=
      (ContMDiffAt.subtypeVal_comp_iff U γ t).mp hγ
    have hnew := Φ.contMDiff.contMDiffAt.comp t hold
    exact hnew

theorem boundaryInteriorAtlas_original_flow_matches (g : SmoothRiemannianMetric I M) :
    let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
      interiorLift_infty_ne_zero (M := M)
    let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
    let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
    let k := boundaryInteriorAtlasMetric g
    ∀ (γ : ℝ → U) (r : ℝ), 0 < r →
      ContMDiffOn 𝓘(ℝ) I ∞ (fun t => (γ t : M)) (Metric.ball 0 r) →
      (∀ s ∈ Metric.ball 0 r, HasGeodesicEquationAt g (fun t => (γ t : M)) s) →
      ∃ ε : ℝ, 0 < ε ∧ ε ≤ r ∧
        ∀ s ∈ Metric.ball 0 ε,
          ((⟨γ 0, mfderiv 𝓘(ℝ) 𝓘(ℝ, E) γ 0 1⟩ : TangentBundle 𝓘(ℝ, E) U), s)
            ∈ k.geodesicFlowDomain ∧
          ((k.geodesicFlow
            (⟨γ 0, mfderiv 𝓘(ℝ) 𝓘(ℝ, E) γ 0 1⟩ : TangentBundle 𝓘(ℝ, E) U)
              s).proj : M) = (γ s : M) := by
  let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
    interiorLift_infty_ne_zero (M := M)
  let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
  let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
  dsimp only
  intro γ r hr hγ hgeo
  have hnew : ContMDiffOn 𝓘(ℝ) 𝓘(ℝ, E) ∞ γ (Metric.ball 0 r) := by
    intro s hs
    exact ((boundaryInteriorAtlas_smooth_iff γ s).mpr
      (hγ.contMDiffAt (Metric.isOpen_ball.mem_nhds hs))).contMDiffWithinAt
  exact boundaryInteriorAtlas_flow_matches g γ r hr hnew hgeo

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
