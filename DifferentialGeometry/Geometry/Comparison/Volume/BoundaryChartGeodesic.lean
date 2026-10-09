import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryInteriorMetric
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryOpenGeodesic
import DifferentialGeometry.Geometry.Geodesic.Naturality.PullbackCross
import DifferentialGeometry.Geometry.Geodesic.Equation.FromIntegralCurve
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Opens

/-!
Ambient geodesic equations for the original chart tensor return to the same metric
through a diffeomorphism between genuine interior opens, including boundary models.
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set TopologicalSpace
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian.Geodesic

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {E : Type*} [ambientNorm : NormedAddCommGroup E]
  [ambientSpace : NormedSpace ℝ E] [ambientFinite : FiniteDimensional ℝ E]
  {H : Type*} [modelTopology : TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [manifoldTopology : TopologicalSpace M]
  [manifoldCharts : ChartedSpace H M] [manifoldSmooth : IsManifold I ∞ M]
  [manifoldSeparated : T2Space M]

theorem boundaryChart_geodesicEquation (g : SmoothRiemannianMetric I M) (p : M)
    (G : SmoothRiemannianMetric 𝓘(ℝ, E) E) (U : Opens E)
    (hG : ∀ y ∈ (U : Set E) ∩ range I, ∀ v w : E,
      G.inner y v w = metricFlatModelInChart g p y v w)
    (γ : ℝ → E) (t : ℝ)
    (ht : γ t ∈ (U : Set E) ∩ interior (extChartAt I p).target)
    (hγ : ContMDiffAt 𝓘(ℝ) 𝓘(ℝ, E) ∞ γ t)
    (hgeo : HasGeodesicEquationAt G γ t) :
    HasGeodesicEquationAt g (fun s => (extChartAt I p).symm (γ s)) t := by
  classical
  let Φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞ :=
    (DifferentialGeometry.Manifold.interiorChart I ∞ p).symm
  let V : Opens E := ⟨(U : Set E) ∩ Φ.source, U.isOpen.inter Φ.open_source⟩
  have hV : (V : Set E) ⊆ Φ.source := inter_subset_right
  let W : Opens M := ⟨Φ '' (V : Set E), image_opens_isOpen Φ hV⟩
  let Ψ : Diffeomorph 𝓘(ℝ, E) I V W ∞ := PartialDiffeomorph.toOpensDiffeo Φ hV
  let imageBoundaryless : BoundarylessManifold I W := Ψ.boundarylessManifold (by simp)
  let z : V := ⟨γ t, ht⟩
  let η : ℝ → V := fun s => if hs : γ s ∈ (V : Set E) then ⟨γ s, hs⟩ else z
  have hmem : ∀ᶠ s in 𝓝 t, γ s ∈ (V : Set E) :=
    hγ.continuousAt.preimage_mem_nhds (V.isOpen.mem_nhds z.property)
  have hη : (fun s => (η s : E)) =ᶠ[𝓝 t] γ := by
    filter_upwards [hmem] with s hs
    simp only [η, dite_eq_left hs]
  have hsmooth : ContMDiffAt 𝓘(ℝ) 𝓘(ℝ, E) ∞ η t := by
    have hb := hγ.congr_of_eventuallyEq hη
    simpa only [Subtype.coe_eta] using codRestr_contMDiffAt
      (fun s => (η s).property) hb
  have hmetric : G.restrictOpen V = Diffeomorph.pullbackMetricCross (g.restrictOpen W) Ψ := by
    apply SmoothRiemannianMetric.ext_inner
    intro y v w
    rw [SmoothRiemannianMetric.restrictOpen_inner, Diffeomorph.pullbackMetricCross_inner,
      SmoothRiemannianMetric.restrictOpen_inner, PartialDiffeomorph.mfderiv_toOpensDiffeo,
      PartialDiffeomorph.mfderiv_toOpensDiffeo]
    have hy : (y : E) ∈ interior (extChartAt I p).target := y.property.2
    change G.inner (y : E) (v : E) (w : E) =
      g.inner ((extChartAt I p).symm (y : E))
        (mfderiv 𝓘(ℝ, E) I (extChartAt I p).symm (y : E) (v : E))
        (mfderiv 𝓘(ℝ, E) I (extChartAt I p).symm (y : E) (w : E))
    rw [hG (y : E) ⟨y.property.1,
      extChartAt_target_subset_range p (interior_subset hy)⟩ (v : E) (w : E)]
    exact boundaryChart_metric_inner_of_interior g p hy v w
  have heq : HasGeodesicEquationAt (G.restrictOpen V) η t := by
    apply (boundaryOpen_geodesicEquation_iff
      (g := G) (U := V) (γ := η) (t := t) BoundarylessManifold.isInteriorPoint).mpr
    exact HasGeodesicEquationAt.congr_of_eventuallyEq_at hη.eq_of_nhds hη hgeo
  have hmap : HasGeodesicEquationAt (g.restrictOpen W) (fun s => Ψ (η s)) t := by
    rw [hmetric] at heq
    exact geoEq_mapCrossAt (g.restrictOpen W) Ψ η t hsmooth heq
  have horiginal : HasGeodesicEquationAt g (fun s => (Ψ (η s) : M)) t :=
    (boundaryOpen_geodesicEquation_iff (g := g) (U := W)
      (γ := fun s => Ψ (η s)) (t := t)
      (I.isInteriorPoint_iff_isInteriorPoint_val.mp
        (BoundarylessManifold.isInteriorPoint (I := I) (M := W)))).mp hmap
  have hreturn : (fun s => (extChartAt I p).symm (γ s)) =ᶠ[𝓝 t]
      (fun s => (Ψ (η s) : M)) := by
    filter_upwards [hη] with s hs
    change (extChartAt I p).symm (γ s) = (extChartAt I p).symm (η s : E)
    rw [hs]
  exact HasGeodesicEquationAt.congr_of_eventuallyEq_at hreturn.eq_of_nhds hreturn horiginal

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
