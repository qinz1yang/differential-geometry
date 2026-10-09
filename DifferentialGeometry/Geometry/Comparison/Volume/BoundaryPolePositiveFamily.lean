import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryPoleFlowFamily

/-!
One genuine open pole-family domain contains the entire positive original birth segment.
Every velocity-time point in that domain gives an original interior smooth geodesic.
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set TopologicalSpace
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Boundary
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {E : Type*} [ambientNorm : NormedAddCommGroup E]
  [ambientSpace : NormedSpace ℝ E] [ambientFinite : FiniteDimensional ℝ E]
  {H : Type*} [modelTopology : TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [modelBoundary : HasSmoothBoundary E H I]
  {M : Type*} [manifoldTopology : TopologicalSpace M] [manifoldCharts : ChartedSpace H M]
  [manifoldSmooth : IsManifold I ∞ M] [manifoldT2 : T2Space M]

theorem exists_boundary_pole_positive_family (g : SmoothRiemannianMetric I M) (p : M)
    (b : modelBoundary.boundaryE) (hb : extChartAt I p p = modelBoundaryParam I b) (v : E)
    (hin : ∃ w : modelBoundary.boundaryE, ∃ c : ℝ, 0 < c ∧
      v = fderiv ℝ (modelBoundaryParam I) b w + c • modelBoundary.inwardCoordE) :
    ∃ G : SmoothRiemannianMetric 𝓘(ℝ, E) E, RiemannianMetricComplete G ∧
      ∃ O : Opens E, extChartAt I p p ∈ O ∧
        (∀ y ∈ (O : Set E) ∩ range I, ∀ z w : E,
          G.inner y z w = DifferentialGeometry.Geometry.Connection.metricFlatModelInChart
            g p y z w) ∧
        ∃ ε : ℝ, 0 < ε ∧ ∃ V : Opens (E × ℝ),
          (∀ t ∈ Ioo 0 ε, (v, t) ∈ V) ∧
          (∀ q ∈ V,
            ((⟨extChartAt I p p, q.1⟩ : TangentBundle 𝓘(ℝ, E) E), q.2) ∈
              G.geodesicFlowDomain ∧
            boundaryPoleFlowFamily G (extChartAt I p p) q.1 q.2 ∈
              (O : Set E) ∩ interior (extChartAt I p).target ∧
            I.IsInteriorPoint ((extChartAt I p).symm
              (boundaryPoleFlowFamily G (extChartAt I p p) q.1 q.2)) ∧
            HasGeodesicEquationAt g
              (fun s => (extChartAt I p).symm
                (boundaryPoleFlowFamily G (extChartAt I p p) q.1 s)) q.2) ∧
          ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ)) I ∞
            (fun q : E × ℝ => (extChartAt I p).symm
              (boundaryPoleFlowFamily G (extChartAt I p p) q.1 q.2)) V := by
  obtain ⟨G, hcomplete, O, hpO, hG, ε, hε, hcenter, _V, _hV, _hall, _hsmooth⟩ :=
    exists_boundary_pole_original_family g p b hb v hin
  let y := extChartAt I p p
  let F : E × ℝ → E := fun q => boundaryPoleFlowFamily G y q.1 q.2
  let D : Set (E × ℝ) := {q | ((⟨y, q.1⟩ : TangentBundle 𝓘(ℝ, E) E), q.2) ∈
    G.geodesicFlowDomain}
  obtain ⟨hDopen, hF⟩ := boundaryPoleFlowFamily_smooth G y
  let S : Set E := (O : Set E) ∩ interior (extChartAt I p).target
  let V : Opens (E × ℝ) := ⟨D ∩ F ⁻¹' S,
    hF.continuousOn.isOpen_inter_preimage hDopen (O.isOpen.inter isOpen_interior)⟩
  refine ⟨G, hcomplete, O, hpO, hG, ε, hε, V, ?_, ?_, ?_⟩
  · intro t ht
    exact ⟨(hcenter t ht).1, (hcenter t ht).2.1⟩
  · intro q hq
    have hfq := hF.contMDiffAt (hDopen.mem_nhds hq.1)
    have hslice : ContMDiffAt 𝓘(ℝ) 𝓘(ℝ, E) ∞
        (boundaryPoleFlowFamily G y q.1) q.2 :=
      hfq.comp (f := fun t : ℝ => (q.1, t)) q.2
        (contMDiff_const.prodMk contMDiff_id).contMDiffAt
    have hi := Bundle.ContMDiffRiemannianMetric.isGeodesicOnWithInitial_geodesicFlow
      G y q.1
    have hgeo := (hi.isGeodesicAt
      (isOpen_maximalIntegralCurveInterval.mem_nhds hq.1)).hasGeodesicEquationAt
    have hinterior : I.IsInteriorPoint ((extChartAt I p).symm (F q)) :=
      DifferentialGeometry.Manifold.isInteriorPoint_of_mem_interiorChart_source I ∞
        (by simp) ((DifferentialGeometry.Manifold.interiorChart I ∞ p).map_target hq.2.2)
    exact ⟨hq.1, hq.2, hinterior, boundaryChart_geodesicEquation g p G O hG
      (boundaryPoleFlowFamily G y q.1) q.2 hq.2 hslice hgeo⟩
  · intro q hq
    have hfq := hF.contMDiffAt (hDopen.mem_nhds hq.1)
    have hcq : ContMDiffAt 𝓘(ℝ, E) I ∞ (extChartAt I p).symm (F q) :=
      (contMDiffOn_extChartAt_symm p).contMDiffAt
        (mem_interior_iff_mem_nhds.mp hq.2.2)
    exact (hcq.comp q hfq).contMDiffWithinAt

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
