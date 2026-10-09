import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryInteriorAtlasMetric
import DifferentialGeometry.Geometry.Geodesic.FiniteMetric.Speed

/-!
Actual native interior-flow velocities map to the original metric by the genuine inclusion.
Original squared speed is conserved at every existing incomplete-flow time.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {E : Type*} [ambientNorm : NormedAddCommGroup E]
  [ambientSpace : NormedSpace ℝ E] [ambientFinite : FiniteDimensional ℝ E]
  {H : Type*} [modelTopology : TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [manifoldTopology : TopologicalSpace M] [manifoldCharts : ChartedSpace H M]
  [manifoldSmooth : IsManifold I ∞ M] [manifoldT2 : T2Space M]

private theorem flowSpeed_infty_ne_zero : (∞ : WithTop ℕ∞) ≠ 0 := by simp

theorem boundaryInteriorFlow_original_velocity (g : SmoothRiemannianMetric I M) :
    let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
      flowSpeed_infty_ne_zero (M := M)
    let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
    let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
    let k := boundaryInteriorAtlasMetric g
    ∀ (seed : TangentBundle 𝓘(ℝ, E) U) (t : ℝ), (seed, t) ∈ k.geodesicFlowDomain →
      (mfderiv 𝓘(ℝ) I (fun s => ((k.geodesicFlow seed s).proj : M)) t (1 : ℝ) : E) =
        mfderiv 𝓘(ℝ, E) I (Subtype.val : U → M) (k.geodesicFlow seed t).proj
          (k.geodesicFlow seed t).snd := by
  let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
    flowSpeed_infty_ne_zero (M := M)
  let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
  let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
  let k := boundaryInteriorAtlasMetric g
  dsimp only
  intro seed t ht
  have hval := DifferentialGeometry.Manifold.contMDiff_intrinsicInterior_val
    I ∞ (by simp) (M := M)
  have hnative := k.hasMFDerivAt_geodesicFlow_proj (r := ⊤) le_top ht
  have hcomp := mfderiv_comp t
    ((hval.contMDiffAt (x := (k.geodesicFlow seed t).proj)).mdifferentiableAt (by simp))
    hnative.mdifferentiableAt
  have hvelocity := congrArg (fun A : ℝ →L[ℝ] E => A (1 : ℝ)) hnative.mfderiv
  have hvelocityApplied :
      (mfderiv 𝓘(ℝ) 𝓘(ℝ, E) (fun s => (k.geodesicFlow seed s).proj) t (1 : ℝ) : E) =
        (k.geodesicFlow seed t).snd := by
    change (mfderiv 𝓘(ℝ) 𝓘(ℝ, E)
      (fun s => (k.geodesicFlow seed s).proj) t (1 : ℝ) : E) =
        (1 : ℝ) • (k.geodesicFlow seed t).snd at hvelocity
    simpa only [one_smul] using hvelocity
  have happ := congrArg (fun A : ℝ →L[ℝ] E => A (1 : ℝ)) hcomp
  change (mfderiv 𝓘(ℝ) I (fun s => ((k.geodesicFlow seed s).proj : M)) t (1 : ℝ) : E) =
    mfderiv 𝓘(ℝ, E) I (Subtype.val : U → M) (k.geodesicFlow seed t).proj
      (mfderiv 𝓘(ℝ) 𝓘(ℝ, E) (fun s => (k.geodesicFlow seed s).proj) t (1 : ℝ)) at happ
  exact happ.trans (congrArg
    (fun v : E => mfderiv 𝓘(ℝ, E) I (Subtype.val : U → M)
      (k.geodesicFlow seed t).proj v) hvelocityApplied)

theorem boundaryInteriorFlow_original_speed (g : SmoothRiemannianMetric I M) :
    let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
      flowSpeed_infty_ne_zero (M := M)
    let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
    let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
    let k := boundaryInteriorAtlasMetric g
    ∀ (seed : TangentBundle 𝓘(ℝ, E) U) (t : ℝ), (seed, t) ∈ k.geodesicFlowDomain →
      g.inner ((k.geodesicFlow seed t).proj : M)
        (mfderiv 𝓘(ℝ) I (fun s => ((k.geodesicFlow seed s).proj : M)) t (1 : ℝ))
        (mfderiv 𝓘(ℝ) I (fun s => ((k.geodesicFlow seed s).proj : M)) t (1 : ℝ)) =
      g.inner (seed.proj : M)
        (mfderiv 𝓘(ℝ, E) I (Subtype.val : U → M) seed.proj seed.snd)
        (mfderiv 𝓘(ℝ, E) I (Subtype.val : U → M) seed.proj seed.snd) := by
  let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
    flowSpeed_infty_ne_zero (M := M)
  let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
  let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
  let k := boundaryInteriorAtlasMetric g
  dsimp only
  intro seed t ht
  have hvel := boundaryInteriorFlow_original_velocity g seed t ht
  have htime := boundaryInteriorAtlasMetric_inner g (k.geodesicFlow seed t).proj
    (k.geodesicFlow seed t).snd (k.geodesicFlow seed t).snd
  have hinitial := boundaryInteriorAtlasMetric_inner g seed.proj seed.snd seed.snd
  have hconserve := k.inner_geodesicFlow_eq (r := ⊤) le_top seed t ht
  have hv : (mfderiv 𝓘(ℝ) I (fun s => ((k.geodesicFlow seed s).proj : M)) t (1 : ℝ)) =
      mfderiv 𝓘(ℝ, E) I (Subtype.val : U → M) (k.geodesicFlow seed t).proj
        (k.geodesicFlow seed t).snd := hvel
  rw [hv]
  exact htime.symm.trans (hconserve.trans hinitial)

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
