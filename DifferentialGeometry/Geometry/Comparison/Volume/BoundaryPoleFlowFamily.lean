import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryCompleteChart
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryInwardSmooth
import DifferentialGeometry.Geometry.Geodesic.Flow.CrossVectorFieldReduction

/-!
A genuine boundary-chart metric produces an actual velocity-and-time geodesic family.
Its positive center ray and a jointly smooth neighborhood map into the original true interior.
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set TopologicalSpace
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Boundary
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {E : Type*} [ambientNorm : NormedAddCommGroup E]
  [ambientSpace : NormedSpace ℝ E] [ambientFinite : FiniteDimensional ℝ E]

noncomputable def boundaryPoleFlowFamily (G : SmoothRiemannianMetric 𝓘(ℝ, E) E)
    (y v : E) (t : ℝ) : E :=
  (G.geodesicFlow (⟨y, v⟩ : TangentBundle 𝓘(ℝ, E) E) t).proj

theorem boundaryPoleFlowFamily_smooth (G : SmoothRiemannianMetric 𝓘(ℝ, E) E) (y : E) :
    IsOpen {q : E × ℝ | ((⟨y, q.1⟩ : TangentBundle 𝓘(ℝ, E) E), q.2) ∈
      G.geodesicFlowDomain} ∧
    ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ)) 𝓘(ℝ, E) ∞
      (fun q : E × ℝ => boundaryPoleFlowFamily G y q.1 q.2)
      {q : E × ℝ | ((⟨y, q.1⟩ : TangentBundle 𝓘(ℝ, E) E), q.2) ∈
        G.geodesicFlowDomain} := by
  have hphase : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ))
      ((𝓘(ℝ, E)).tangent.prod 𝓘(ℝ)) ∞
      (fun q : E × ℝ => ((⟨y, q.1⟩ : TangentBundle 𝓘(ℝ, E) E), q.2)) :=
    ((DifferentialGeometry.contMDiff_tangentFiber (I := 𝓘(ℝ, E)) y).comp
      contMDiff_fst).prodMk contMDiff_snd
  have hproj : ContMDiff (𝓘(ℝ, E)).tangent 𝓘(ℝ, E) ∞
      (TotalSpace.proj : TangentBundle 𝓘(ℝ, E) E → E) :=
    contMDiff_proj (TangentSpace 𝓘(ℝ, E) : E → Type _)
  exact ⟨(G.isOpen_geodesicFlowDomain (r := ⊤) le_top).preimage hphase.continuous,
    (hproj.comp_contMDiffOn (G.contMDiffOn_geodesicFlow (r := ⊤) le_top)).comp
      hphase.contMDiffOn (fun q hq => hq)⟩

theorem boundaryPoleFlowFamily_initial (G : SmoothRiemannianMetric 𝓘(ℝ, E) E)
    (y v : E) : boundaryPoleFlowFamily G y v 0 = y ∧
      HasDerivAt (boundaryPoleFlowFamily G y v) v 0 := by
  have hz := G.geodesicFlow_zero (r := ⊤) le_top
    (⟨y, v⟩ : TangentBundle 𝓘(ℝ, E) E)
  have hzero : boundaryPoleFlowFamily G y v 0 = y :=
    congrArg (fun z : TangentBundle 𝓘(ℝ, E) E => z.proj) hz
  have hnative := G.hasMFDerivAt_geodesicFlow_proj (r := ⊤) le_top
    (G.mem_geodesicFlowDomain_zero (r := ⊤) le_top
      (⟨y, v⟩ : TangentBundle 𝓘(ℝ, E) E))
  have hv := congrArg (fun A : ℝ →L[ℝ] E => A (1 : ℝ)) hnative.mfderiv
  have hvApplied : (mfderiv 𝓘(ℝ) 𝓘(ℝ, E) (boundaryPoleFlowFamily G y v) 0 1 : E) =
      (G.geodesicFlow (⟨y, v⟩ : TangentBundle 𝓘(ℝ, E) E) 0).snd := by
    change (mfderiv 𝓘(ℝ) 𝓘(ℝ, E) (boundaryPoleFlowFamily G y v) 0 1 : E) =
      (1 : ℝ) • (G.geodesicFlow (⟨y, v⟩ : TangentBundle 𝓘(ℝ, E) E) 0).snd at hv
    simpa only [one_smul] using hv
  have hvelocity : (mfderiv 𝓘(ℝ) 𝓘(ℝ, E) (boundaryPoleFlowFamily G y v) 0 1 : E) = v :=
    hvApplied.trans (congrArg (fun z : TangentBundle 𝓘(ℝ, E) E => (z.snd : E)) hz)
  have hfd : HasFDerivAt (boundaryPoleFlowFamily G y v)
      (mfderiv 𝓘(ℝ) 𝓘(ℝ, E) (boundaryPoleFlowFamily G y v) 0) 0 :=
    hnative.mdifferentiableAt.hasMFDerivAt.hasFDerivAt
  let ambientAction : ContinuousSMul ℝ E := IsBoundedSMul.continuousSMul
  have hd := @HasFDerivAt.hasDerivAt ℝ inferInstance E ambientNorm.toAddCommGroup
    ambientSpace.toModule (inferInstanceAs (TopologicalSpace E))
    (boundaryPoleFlowFamily G y v) 0 ambientAction
    (mfderiv 𝓘(ℝ) 𝓘(ℝ, E) (boundaryPoleFlowFamily G y v) 0) hfd
  refine ⟨hzero, ?_⟩
  exact hd.congr_deriv hvelocity

variable {H : Type*} [modelTopology : TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [modelBoundary : HasSmoothBoundary E H I]
  {M : Type*} [manifoldTopology : TopologicalSpace M] [manifoldCharts : ChartedSpace H M]
  [manifoldSmooth : IsManifold I ∞ M] [manifoldT2 : T2Space M]

theorem exists_boundary_pole_original_family (g : SmoothRiemannianMetric I M) (p : M)
    (b : modelBoundary.boundaryE) (hb : extChartAt I p p = modelBoundaryParam I b) (v : E)
    (hin : ∃ w : modelBoundary.boundaryE, ∃ c : ℝ, 0 < c ∧
      v = fderiv ℝ (modelBoundaryParam I) b w + c • modelBoundary.inwardCoordE) :
    ∃ G : SmoothRiemannianMetric 𝓘(ℝ, E) E, RiemannianMetricComplete G ∧
      ∃ O : Opens E, extChartAt I p p ∈ O ∧
        (∀ y ∈ (O : Set E) ∩ range I, ∀ z w : E,
          G.inner y z w = DifferentialGeometry.Geometry.Connection.metricFlatModelInChart
            g p y z w) ∧
        ∃ ε : ℝ, 0 < ε ∧
          (∀ t ∈ Ioo 0 ε,
            ((⟨extChartAt I p p, v⟩ : TangentBundle 𝓘(ℝ, E) E), t) ∈ G.geodesicFlowDomain ∧
            boundaryPoleFlowFamily G (extChartAt I p p) v t ∈
              (O : Set E) ∩ interior (extChartAt I p).target ∧
            HasGeodesicEquationAt g
              (fun s => (extChartAt I p).symm
                (boundaryPoleFlowFamily G (extChartAt I p p) v s)) t) ∧
          ∃ V : Opens (E × ℝ), (v, ε / 2) ∈ V ∧
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
  have hp : I.IsBoundaryPoint p := by
    change extChartAt I p p ∈ frontier (range I)
    rw [hb, ← range_modelBoundaryParam I]
    exact mem_range_self b
  obtain ⟨G, hcomplete, O, hpO, hOtarget, hG⟩ := exists_boundary_complete_chart g p hp
  let y := extChartAt I p p
  let F : E × ℝ → E := fun q => boundaryPoleFlowFamily G y q.1 q.2
  let D : Set (E × ℝ) := {q | ((⟨y, q.1⟩ : TangentBundle 𝓘(ℝ, E) E), q.2) ∈
    G.geodesicFlowDomain}
  obtain ⟨hDopen, hF⟩ := boundaryPoleFlowFamily_smooth G y
  obtain ⟨hzero, hder⟩ := boundaryPoleFlowFamily_initial G y v
  obtain ⟨ε, hε, henter⟩ := eventually_model_interior_of_inward_derivative b v
    (boundaryPoleFlowFamily G y v) (hzero.trans hb) hder hin
  have htarget : ∀ᶠ t in 𝓝 (0 : ℝ),
      boundaryPoleFlowFamily G y v t ∈ (O : Set E) ∩ (I.symm ⁻¹' (chartAt H p).target) := by
    apply hder.continuousAt.preimage_mem_nhds
    rw [hzero]
    exact inter_mem (O.isOpen.mem_nhds hpO)
      (((chartAt H p).open_target.preimage I.continuous_symm).mem_nhds (hOtarget hpO))
  have hdomain : ∀ᶠ t in 𝓝 (0 : ℝ), (v, t) ∈ D :=
    (hDopen.preimage (continuous_const.prodMk continuous_id)).mem_nhds
      (G.mem_geodesicFlowDomain_zero (r := ⊤) le_top
        (⟨y, v⟩ : TangentBundle 𝓘(ℝ, E) E))
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (htarget.and hdomain)
  let τ := min ε r
  have hτ : 0 < τ := lt_min hε hr
  have hcenter (t : ℝ) (ht : t ∈ Ioo 0 τ) :
      (v, t) ∈ D ∧ F (v, t) ∈ (O : Set E) ∩ interior (extChartAt I p).target := by
    have htr : t ∈ Metric.ball (0 : ℝ) r := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht.1]
      exact ht.2.trans_le (min_le_right ε r)
    have hti : boundaryPoleFlowFamily G y v t ∈ interior (range I) :=
      henter t ⟨ht.1, ht.2.trans_le (min_le_left ε r)⟩
    refine ⟨(hball htr).2, (hball htr).1.1, ?_⟩
    rw [extChartAt_target, interior_inter,
      ((chartAt H p).open_target.preimage I.continuous_symm).interior_eq]
    exact ⟨(hball htr).1.2, hti⟩
  let S : Set E := (O : Set E) ∩ interior (extChartAt I p).target
  have hSopen : IsOpen S := O.isOpen.inter isOpen_interior
  let V : Opens (E × ℝ) := ⟨D ∩ F ⁻¹' S,
    hF.continuousOn.isOpen_inter_preimage hDopen hSopen⟩
  have ha : τ / 2 ∈ Ioo 0 τ := by constructor <;> linarith
  have hVcenter : (v, τ / 2) ∈ V := hcenter (τ / 2) ha
  have hVsmooth : ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ)) I ∞
      (fun q : E × ℝ => (extChartAt I p).symm (F q)) V := by
    intro q hq
    have hfq := hF.contMDiffAt (hDopen.mem_nhds hq.1)
    have hcq : ContMDiffAt 𝓘(ℝ, E) I ∞ (extChartAt I p).symm (F q) :=
      (contMDiffOn_extChartAt_symm p).contMDiffAt
      (mem_interior_iff_mem_nhds.mp hq.2.2)
    exact (hcq.comp q hfq).contMDiffWithinAt
  refine ⟨G, hcomplete, O, hpO, hG, τ, hτ, ?_, V, hVcenter, ?_, hVsmooth⟩
  · intro t ht
    obtain ⟨hdt, hft⟩ := hcenter t ht
    have hslice : ContMDiffAt 𝓘(ℝ) 𝓘(ℝ, E) ∞ (boundaryPoleFlowFamily G y v) t :=
      (hF.contMDiffAt (hDopen.mem_nhds hdt)).comp t
        (contMDiff_const.prodMk contMDiff_id).contMDiffAt
    have hi := Bundle.ContMDiffRiemannianMetric.isGeodesicOnWithInitial_geodesicFlow G y v
    have hgeo := (hi.isGeodesicAt
      (isOpen_maximalIntegralCurveInterval.mem_nhds hdt)).hasGeodesicEquationAt
    exact ⟨hdt, hft, boundaryChart_geodesicEquation g p G O hG
      (boundaryPoleFlowFamily G y v) t hft hslice hgeo⟩
  · intro q hq
    have hfq : ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ)) 𝓘(ℝ, E) ∞ F q :=
      hF.contMDiffAt (hDopen.mem_nhds hq.1)
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

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
