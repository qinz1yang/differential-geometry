import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryInteriorEquation
import DifferentialGeometry.Geometry.Exponential.Intrinsic.Geodesic.Basic

/-!
An actual original interior geodesic agrees locally with the native incomplete maximal flow.
The flow seed uses the curve's actual initial velocity and its existence time is derived.
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.Exponential

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {E : Type*} [ambientNorm : NormedAddCommGroup E]
  [ambientSpace : NormedSpace ℝ E] [ambientFinite : FiniteDimensional ℝ E]
  {H : Type*} [modelTopology : TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [manifoldTopology : TopologicalSpace M] [manifoldCharts : ChartedSpace H M]
  [manifoldSmooth : IsManifold I ∞ M] [manifoldT2 : T2Space M]

private theorem interiorMatching_infty_ne_zero : (∞ : WithTop ℕ∞) ≠ 0 := by simp

theorem boundaryInteriorAtlas_flow_matches (g : SmoothRiemannianMetric I M) :
    let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
      interiorMatching_infty_ne_zero (M := M)
    let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
    let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
    let k := boundaryInteriorAtlasMetric g
    ∀ (γ : ℝ → U) (r : ℝ), 0 < r →
      ContMDiffOn 𝓘(ℝ) 𝓘(ℝ, E) ∞ γ (Metric.ball 0 r) →
      (∀ s ∈ Metric.ball 0 r, HasGeodesicEquationAt g (fun t => (γ t : M)) s) →
      ∃ ε : ℝ, 0 < ε ∧ ε ≤ r ∧
        ∀ s ∈ Metric.ball 0 ε,
          ((⟨γ 0, mfderiv 𝓘(ℝ) 𝓘(ℝ, E) γ 0 1⟩ : TangentBundle 𝓘(ℝ, E) U), s)
            ∈ k.geodesicFlowDomain ∧
          ((k.geodesicFlow
            (⟨γ 0, mfderiv 𝓘(ℝ) 𝓘(ℝ, E) γ 0 1⟩ : TangentBundle 𝓘(ℝ, E) U)
              s).proj : M) = (γ s : M) := by
  let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
    interiorMatching_infty_ne_zero (M := M)
  let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
  let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
  let k := boundaryInteriorAtlasMetric g
  dsimp only
  intro γ r hr hγ hgeo
  let seed : TangentBundle 𝓘(ℝ, E) U := ⟨γ 0, mfderiv 𝓘(ℝ) 𝓘(ℝ, E) γ 0 1⟩
  let η : ℝ → U := fun s => (k.geodesicFlow seed s).proj
  have hzero := k.mem_geodesicFlowDomain_zero (r := ⊤) le_top seed
  have hopen := k.isOpen_geodesicFlowDomain (r := ⊤) le_top
  have hdomain : {s : ℝ | (seed, s) ∈ k.geodesicFlowDomain} ∈ 𝓝 0 :=
    (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds
      (hopen.mem_nhds hzero)
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hdomain
  let ε := min r δ
  have hε : 0 < ε := lt_min hr hδ
  have her : ε ≤ r := min_le_left r δ
  have heδ : ε ≤ δ := min_le_right r δ
  have hsub : Metric.ball (0 : ℝ) ε ⊆ Metric.ball 0 r := Metric.ball_subset_ball her
  have hflow (s : ℝ) (hs : s ∈ Metric.ball 0 ε) :
      (seed, s) ∈ k.geodesicFlowDomain := hδsub (Metric.ball_subset_ball heδ hs)
  have hηgeo : IsGeodesicOn k η (Metric.ball 0 ε) := by
    intro s hs
    have hi := Bundle.ContMDiffRiemannianMetric.isGeodesicOnWithInitial_geodesicFlow
      k (γ 0) (mfderiv 𝓘(ℝ) 𝓘(ℝ, E) γ 0 1)
    exact (hi.isGeodesicAt
      (isOpen_maximalIntegralCurveInterval.mem_nhds (hflow s hs))).hasGeodesicEquationAt
  have hγgeo : IsGeodesicOn k γ (Metric.ball 0 ε) := by
    intro s hs
    exact (boundaryInteriorAtlas_geodesicEquation_iff g γ s
      (hγ.contMDiffAt (Metric.isOpen_ball.mem_nhds (hsub hs)))).mpr (hgeo s (hsub hs))
  have hηcont : ContinuousOn η (Metric.ball 0 ε) := by
    intro s hs
    have hc := (k.hasMFDerivAt_geodesicFlow_proj (r := ⊤) le_top (hflow s hs)).continuousAt
    exact hc.continuousWithinAt
  have hγcont : ContinuousOn γ (Metric.ball 0 ε) := hγ.continuousOn.mono hsub
  have hinitial : η 0 = γ 0 := by
    change (k.geodesicFlow seed 0).proj = γ 0
    exact congrArg (fun q : TangentBundle 𝓘(ℝ, E) U => q.proj)
      (k.geodesicFlow_zero (r := ⊤) le_top seed)
  have hvelocity : (mfderiv 𝓘(ℝ) 𝓘(ℝ, E) η 0 1 : E) =
      mfderiv 𝓘(ℝ) 𝓘(ℝ, E) γ 0 1 := by
    have hder := (k.hasMFDerivAt_geodesicFlow_proj (r := ⊤) le_top hzero).mfderiv
    have happ := congrArg (fun A : ℝ →L[ℝ] E => A 1) hder
    have hv : (mfderiv 𝓘(ℝ) 𝓘(ℝ, E) η 0 1 : E) =
        (k.geodesicFlow seed 0).snd := by
      change (mfderiv 𝓘(ℝ) 𝓘(ℝ, E) η 0 1 : E) =
        (1 : ℝ) • (k.geodesicFlow seed 0).snd at happ
      simpa only [one_smul] using happ
    have hf := congrArg (fun q : TangentBundle 𝓘(ℝ, E) U => (q.snd : E))
      (k.geodesicFlow_zero (r := ⊤) le_top seed)
    exact hv.trans hf
  have heq := geo_eqOn_of_initial k Metric.isOpen_ball (convex_ball (0 : ℝ) ε).isPreconnected
    (Metric.mem_ball_self hε) hηgeo hγgeo hηcont hγcont hinitial hvelocity
  refine ⟨ε, hε, her, ?_⟩
  intro s hs
  exact ⟨hflow s hs, congrArg (fun x : U => (x : M)) (heq hs)⟩

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
