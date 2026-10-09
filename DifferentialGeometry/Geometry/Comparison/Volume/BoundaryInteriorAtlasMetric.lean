import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryOpenGeodesic
import DifferentialGeometry.Topology.Manifold.InteriorAtlas
import DifferentialGeometry.Geometry.Metric.Pullback.Cross
import DifferentialGeometry.Geometry.Geodesic.Naturality.PullbackCross
import DifferentialGeometry.Geometry.Geodesic.FiniteMetric.SmoothSpray

/-!
The genuine original interior has its actual pulled-back metric in a boundaryless atlas.
Its incomplete maximal geodesic flow maps to original-metric geodesics on every existing time.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Riemannian.Geodesic

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {E : Type*} [ambientNorm : NormedAddCommGroup E]
  [ambientSpace : NormedSpace ℝ E] [ambientFinite : FiniteDimensional ℝ E]
  {H : Type*} [modelTopology : TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [manifoldTopology : TopologicalSpace M] [manifoldCharts : ChartedSpace H M]
  [manifoldSmooth : IsManifold I ∞ M] [manifoldT2 : T2Space M]

private theorem boundaryInterior_infty_ne_zero : (∞ : WithTop ℕ∞) ≠ 0 := by simp

noncomputable def boundaryInteriorAtlasMetric (g : SmoothRiemannianMetric I M) :
    let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
      boundaryInterior_infty_ne_zero (M := M)
    let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
    let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
    SmoothRiemannianMetric 𝓘(ℝ, E) U :=
  let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
      boundaryInterior_infty_ne_zero (M := M)
  let Φ := DifferentialGeometry.Manifold.interiorAtlasDiffeomorph I ∞ (M := U)
  let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
  let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
  Diffeomorph.pullbackMetricCross (g.restrictOpen U) Φ.symm

theorem boundaryInteriorAtlasMetric_inner (g : SmoothRiemannianMetric I M) :
    let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
      boundaryInterior_infty_ne_zero (M := M)
    let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
    let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
    ∀ x : U, ∀ v w : TangentSpace 𝓘(ℝ, E) x,
      (boundaryInteriorAtlasMetric g).inner x v w = g.inner (x : M)
        (mfderiv 𝓘(ℝ, E) I (Subtype.val : U → M) x v)
        (mfderiv 𝓘(ℝ, E) I (Subtype.val : U → M) x w) := by
  let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
      boundaryInterior_infty_ne_zero (M := M)
  let Φ := DifferentialGeometry.Manifold.interiorAtlasDiffeomorph I ∞ (M := U)
  let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
  let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
  dsimp only
  intro x v w
  have hΦ := (Φ.symm.contMDiff.contMDiffAt (x := x)).mdifferentiableAt (by simp)
  have hval : MDifferentiableAt I I (Subtype.val : U → M) (Φ.symm x) :=
    (DifferentialGeometry.hasMFDerivAt_subtype_val (I := I) U (Φ.symm x)).mdifferentiableAt
  have hcomp := mfderiv_comp x hval hΦ
  have hfun : (Subtype.val : U → M) ∘ (Φ.symm : U → U) = Subtype.val := by
    funext z
    rfl
  rw [hfun] at hcomp
  rw [DifferentialGeometry.mfderiv_subtype_val (I := I) U (Φ.symm x)] at hcomp
  have hcompV := congrArg (fun B : TangentSpace 𝓘(ℝ, E) x →L[ℝ]
    TangentSpace I (x : M) => B v) hcomp
  have hcompW := congrArg (fun B : TangentSpace 𝓘(ℝ, E) x →L[ℝ]
    TangentSpace I (x : M) => B w) hcomp
  change mfderiv 𝓘(ℝ, E) I (Subtype.val : U → M) x v =
    mfderiv 𝓘(ℝ, E) I Φ.symm x v at hcompV
  change mfderiv 𝓘(ℝ, E) I (Subtype.val : U → M) x w =
    mfderiv 𝓘(ℝ, E) I Φ.symm x w at hcompW
  have hpull := Diffeomorph.pullbackMetricCross_inner (g.restrictOpen U) Φ.symm x v w
  rw [SmoothRiemannianMetric.restrictOpen_inner] at hpull
  change (boundaryInteriorAtlasMetric g).inner x v w = _ at hpull
  exact hpull.trans (by
    change g.inner (x : M) (mfderiv 𝓘(ℝ, E) I Φ.symm x v)
      (mfderiv 𝓘(ℝ, E) I Φ.symm x w) = _
    rw [← hcompV, ← hcompW])

theorem boundaryInteriorAtlas_geodesicEquation (g : SmoothRiemannianMetric I M) :
    let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
      boundaryInterior_infty_ne_zero (M := M)
    let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
    let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
    ∀ (γ : ℝ → U) (t : ℝ), ContMDiffAt 𝓘(ℝ) 𝓘(ℝ, E) ∞ γ t →
      HasGeodesicEquationAt (boundaryInteriorAtlasMetric g) γ t →
      HasGeodesicEquationAt g (fun s => (γ s : M)) t := by
  let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
      boundaryInterior_infty_ne_zero (M := M)
  let Φ := DifferentialGeometry.Manifold.interiorAtlasDiffeomorph I ∞ (M := U)
  let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
  let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
  dsimp only
  intro γ t hγ hgeo
  have hmapped := geoEq_mapCrossAt (g.restrictOpen U) Φ.symm γ t hγ hgeo
  change HasGeodesicEquationAt (g.restrictOpen U) γ t at hmapped
  exact (boundaryOpen_geodesicEquation_iff (g := g) (U := U)
    (γ := γ) (t := t) (γ t).property).mp hmapped

theorem boundaryInteriorAtlas_geodesicFlow (g : SmoothRiemannianMetric I M) :
    let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
      boundaryInterior_infty_ne_zero (M := M)
    let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
    let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
    let k := boundaryInteriorAtlasMetric g
    IsOpen k.geodesicFlowDomain ∧
      ContMDiffOn ((𝓘(ℝ, E)).tangent.prod 𝓘(ℝ)) I ∞
        (fun q => ((k.geodesicFlow q.1 q.2).proj : M)) k.geodesicFlowDomain ∧
      ∀ (seed : TangentBundle 𝓘(ℝ, E) U) (t : ℝ), (seed, t) ∈ k.geodesicFlowDomain →
        HasGeodesicEquationAt g (fun s => ((k.geodesicFlow seed s).proj : M)) t := by
  let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
      boundaryInterior_infty_ne_zero (M := M)
  let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
  let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
  let k := boundaryInteriorAtlasMetric g
  dsimp only
  have hdomain : IsOpen k.geodesicFlowDomain := k.isOpen_geodesicFlowDomain (r := ⊤) le_top
  have hflow := k.contMDiffOn_geodesicFlow (r := ⊤) le_top
  have hproj : ContMDiff (𝓘(ℝ, E)).tangent 𝓘(ℝ, E)
      ∞ (TotalSpace.proj : TangentBundle 𝓘(ℝ, E) U → U) :=
    contMDiff_proj (TangentSpace 𝓘(ℝ, E) : U → Type _)
  have hval := DifferentialGeometry.Manifold.contMDiff_intrinsicInterior_val
    I ∞ (by simp) (M := M)
  have hmap : ContMDiffOn ((𝓘(ℝ, E)).tangent.prod 𝓘(ℝ)) I ∞
      (fun q => ((k.geodesicFlow q.1 q.2).proj : M)) k.geodesicFlowDomain :=
    hval.comp_contMDiffOn (hproj.comp_contMDiffOn hflow)
  refine ⟨hdomain, hmap, ?_⟩
  intro seed t ht
  obtain ⟨p, v⟩ := seed
  have hnew : ContMDiffAt 𝓘(ℝ) 𝓘(ℝ, E) ∞
      (fun s => (k.geodesicFlow (⟨p, v⟩ : TangentBundle 𝓘(ℝ, E) U) s).proj) t := by
    have hphase := hflow.contMDiffAt (hdomain.mem_nhds ht)
    exact hproj.contMDiffAt.comp t
      (hphase.comp t (contMDiff_const.prodMk contMDiff_id).contMDiffAt)
  have hinitial := Bundle.ContMDiffRiemannianMetric.isGeodesicOnWithInitial_geodesicFlow k p v
  have hgeo := (hinitial.isGeodesicAt
    (isOpen_maximalIntegralCurveInterval.mem_nhds ht)).hasGeodesicEquationAt
  exact boundaryInteriorAtlas_geodesicEquation g _ t hnew hgeo

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
