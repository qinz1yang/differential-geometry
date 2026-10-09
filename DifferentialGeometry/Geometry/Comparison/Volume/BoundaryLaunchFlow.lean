import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryInwardSmooth
import DifferentialGeometry.Geometry.Geodesic.Flow.CrossVectorFieldReduction

/-!
An actual positive-time original interior launch seeds the native incomplete maximal flow.
The seed, positive overlap and original equations at all existing flow times are constructed.
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Riemannian.Geodesic

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {E : Type*} [ambientNorm : NormedAddCommGroup E]
  [ambientSpace : NormedSpace ℝ E] [ambientFinite : FiniteDimensional ℝ E]
  {H : Type*} [modelTopology : TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [manifoldTopology : TopologicalSpace M] [manifoldCharts : ChartedSpace H M]
  [manifoldSmooth : IsManifold I ∞ M] [manifoldT2 : T2Space M]

private theorem launchFlow_infty_ne_zero : (∞ : WithTop ℕ∞) ≠ 0 := by simp

theorem boundary_original_launch_flow (g : SmoothRiemannianMetric I M) :
    let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
      launchFlow_infty_ne_zero (M := M)
    let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
    let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
    let k := boundaryInteriorAtlasMetric g
    ∀ (γ : ℝ → M) (T : ℝ), 0 < T → ContMDiffOn 𝓘(ℝ) I ∞ γ (Ioo 0 T) →
      (∀ t ∈ Ioo 0 T, HasGeodesicEquationAt g γ t) →
      (∀ t ∈ Ioo 0 T, I.IsInteriorPoint (γ t)) →
      ∃ seed : TangentBundle 𝓘(ℝ, E) U, ∃ ε : ℝ,
        0 < ε ∧ ε ≤ T / 4 ∧ (seed.proj : M) = γ (T / 2) ∧
        (∀ s ∈ Metric.ball 0 ε, (seed, s) ∈ k.geodesicFlowDomain ∧
          ((k.geodesicFlow seed s).proj : M) = γ (s + T / 2)) ∧
        ∀ s : ℝ, (seed, s) ∈ k.geodesicFlowDomain →
          ContMDiffAt 𝓘(ℝ) I ∞ (fun t => ((k.geodesicFlow seed t).proj : M)) s ∧
          HasGeodesicEquationAt g (fun t => ((k.geodesicFlow seed t).proj : M)) s ∧
          I.IsInteriorPoint ((k.geodesicFlow seed s).proj : M) := by
  classical
  let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
    launchFlow_infty_ne_zero (M := M)
  let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
  let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
  let k := boundaryInteriorAtlasMetric g
  dsimp only
  intro γ T hT hγ hgeo henter
  let a := T / 2
  let r := T / 4
  have hr : 0 < r := by dsimp only [r]; positivity
  have ha : a ∈ Ioo 0 T := by dsimp only [a]; constructor <;> linarith
  let p : U := ⟨γ a, henter a ha⟩
  let ρ : ℝ → U := fun s =>
    if hs : I.IsInteriorPoint (γ (s + a)) then ⟨γ (s + a), hs⟩ else p
  have htime (s : ℝ) (hs : s ∈ Metric.ball 0 r) : s + a ∈ Ioo 0 T := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt] at hs
    dsimp only [r] at hs
    dsimp only [a]
    constructor <;> linarith
  have hρ (s : ℝ) (hs : s ∈ Metric.ball 0 r) : (ρ s : M) = γ (s + a) := by
    dsimp only [ρ]
    rw [dite_eq_left (henter (s + a) (htime s hs))]
  have hev (s : ℝ) (hs : s ∈ Metric.ball 0 r) :
      (fun t => (ρ t : M)) =ᶠ[𝓝 s] (fun t => γ (t + a)) :=
    eventually_of_mem (Metric.isOpen_ball.mem_nhds hs) (fun t ht => hρ t ht)
  have hρsmooth : ContMDiffOn 𝓘(ℝ) I ∞ (fun t => (ρ t : M)) (Metric.ball 0 r) := by
    intro s hs
    have hshift : ContMDiffAt 𝓘(ℝ) I ∞ (fun t => γ (t + a)) s :=
      (hγ.contMDiffAt (isOpen_Ioo.mem_nhds (htime s hs))).comp s
        (contMDiffAt_id.add contMDiffAt_const)
    exact (hshift.congr_of_eventuallyEq (hev s hs)).contMDiffWithinAt
  have hρgeo (s : ℝ) (hs : s ∈ Metric.ball 0 r) :
      HasGeodesicEquationAt g (fun t => (ρ t : M)) s := by
    have hshift : HasGeodesicEquationAt g (fun t => γ (t + a)) s := by
      simpa only [one_mul] using hasGeodesicEquationAt_comp_affine
        (c := 1) (d := a) (t := s) (by simpa only [one_mul] using hgeo (s + a) (htime s hs))
    exact HasGeodesicEquationAt.congr_of_eventuallyEq_at (hρ s hs) (hev s hs) hshift
  obtain ⟨ε, hε, her, hmatch⟩ :=
    boundaryInteriorAtlas_original_flow_matches g ρ r hr hρsmooth hρgeo
  let seed : TangentBundle 𝓘(ℝ, E) U := ⟨ρ 0, mfderiv 𝓘(ℝ) 𝓘(ℝ, E) ρ 0 1⟩
  have hbase : (seed.proj : M) = γ a := by
    simpa only [seed, zero_add] using hρ 0 (Metric.mem_ball_self hr)
  obtain ⟨hdomain, hmap, hequation⟩ := boundaryInteriorAtlas_geodesicFlow g
  refine ⟨seed, ε, hε, her, hbase, ?_, ?_⟩
  · intro s hs
    have hsr : s ∈ Metric.ball 0 r := Metric.ball_subset_ball her hs
    exact ⟨(hmatch s hs).1, (hmatch s hs).2.trans (hρ s hsr)⟩
  · intro s hs
    have hsmooth : ContMDiffAt 𝓘(ℝ) I ∞
        (fun t => ((k.geodesicFlow seed t).proj : M)) s :=
      (hmap.contMDiffAt (hdomain.mem_nhds hs)).comp s
        (contMDiff_const.prodMk contMDiff_id).contMDiffAt
    exact ⟨hsmooth, hequation seed s hs, ((k.geodesicFlow seed s).proj).property⟩

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
