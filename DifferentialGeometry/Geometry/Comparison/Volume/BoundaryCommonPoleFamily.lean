import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryPoleFlowFamily
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryOriginalPhaseSeed
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryInteriorEquation

/-!
One original pole chooses a common auxiliary metric, open family domain, and interior lift.
Every strictly inward velocity enters that same family on its actual positive birth interval.
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

private theorem commonPole_infty_ne_zero : (∞ : WithTop ℕ∞) ≠ 0 := by simp

theorem exists_boundary_common_pole_family (g : SmoothRiemannianMetric I M) (p : M)
    (b : modelBoundary.boundaryE) (hb : extChartAt I p p = modelBoundaryParam I b) :
    let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
      commonPole_infty_ne_zero (M := M)
    let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
    let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
    let k := boundaryInteriorAtlasMetric g
    ∃ G : SmoothRiemannianMetric 𝓘(ℝ, E) E, RiemannianMetricComplete G ∧
      ∃ O : Opens E, extChartAt I p p ∈ O ∧
        (∀ y ∈ (O : Set E) ∩ range I, ∀ z w : E,
          G.inner y z w = DifferentialGeometry.Geometry.Connection.metricFlatModelInChart
            g p y z w) ∧
        ∃ V : Opens (E × ℝ), ∃ ρ : E × ℝ → U,
          ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ)) 𝓘(ℝ, E) ∞ ρ V ∧
          (∀ q ∈ V,
            ((⟨extChartAt I p p, q.1⟩ : TangentBundle 𝓘(ℝ, E) E), q.2) ∈
              G.geodesicFlowDomain ∧
            boundaryPoleFlowFamily G (extChartAt I p p) q.1 q.2 ∈
              (O : Set E) ∩ interior (extChartAt I p).target ∧
            (ρ q : M) = (extChartAt I p).symm
              (boundaryPoleFlowFamily G (extChartAt I p p) q.1 q.2) ∧
            HasGeodesicEquationAt k (fun t => ρ (q.1, t)) q.2) ∧
          ∀ v : E, (∃ w : modelBoundary.boundaryE, ∃ c : ℝ, 0 < c ∧
            v = fderiv ℝ (modelBoundaryParam I) b w + c • modelBoundary.inwardCoordE) →
            ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ Ioo 0 ε, (v, t) ∈ V := by
  let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
    commonPole_infty_ne_zero (M := M)
  let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
  let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
  let k := boundaryInteriorAtlasMetric g
  dsimp only
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
  let S : Set E := (O : Set E) ∩ interior (extChartAt I p).target
  let V : Opens (E × ℝ) := ⟨D ∩ F ⁻¹' S,
    hF.continuousOn.isOpen_inter_preimage hDopen (O.isOpen.inter isOpen_interior)⟩
  have hbirth (v : E)
      (hin : ∃ w : modelBoundary.boundaryE, ∃ c : ℝ, 0 < c ∧
        v = fderiv ℝ (modelBoundaryParam I) b w + c • modelBoundary.inwardCoordE) :
      ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ Ioo 0 ε, (v, t) ∈ V := by
    obtain ⟨hzero, hder⟩ := boundaryPoleFlowFamily_initial G y v
    obtain ⟨ε, hε, henter⟩ := eventually_model_interior_of_inward_derivative b v
      (boundaryPoleFlowFamily G y v) (hzero.trans hb) hder hin
    have htarget : ∀ᶠ t in 𝓝 (0 : ℝ),
        boundaryPoleFlowFamily G y v t ∈
          (O : Set E) ∩ (I.symm ⁻¹' (chartAt H p).target) := by
      apply hder.continuousAt.preimage_mem_nhds
      rw [hzero]
      exact inter_mem (O.isOpen.mem_nhds hpO)
        (((chartAt H p).open_target.preimage I.continuous_symm).mem_nhds (hOtarget hpO))
    have hdomain : ∀ᶠ t in 𝓝 (0 : ℝ), (v, t) ∈ D :=
      (hDopen.preimage (continuous_const.prodMk continuous_id)).mem_nhds
        (G.mem_geodesicFlowDomain_zero (r := ⊤) le_top
          (⟨y, v⟩ : TangentBundle 𝓘(ℝ, E) E))
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (htarget.and hdomain)
    refine ⟨min ε r, lt_min hε hr, ?_⟩
    intro t ht
    have htr : t ∈ Metric.ball (0 : ℝ) r := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht.1]
      exact ht.2.trans_le (min_le_right ε r)
    have hti : boundaryPoleFlowFamily G y v t ∈ interior (range I) :=
      henter t ⟨ht.1, ht.2.trans_le (min_le_left ε r)⟩
    refine ⟨(hball htr).2, (hball htr).1.1, ?_⟩
    rw [extChartAt_target, interior_inter,
      ((chartAt H p).open_target.preimage I.continuous_symm).interior_eq]
    exact ⟨(hball htr).1.2, hti⟩
  let R : E × ℝ → M := fun q => (extChartAt I p).symm (F q)
  have hR : ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ)) I ∞ R V := by
    intro q hq
    have hfq := hF.contMDiffAt (hDopen.mem_nhds hq.1)
    have hcq : ContMDiffAt 𝓘(ℝ, E) I ∞ (extChartAt I p).symm (F q) :=
      (contMDiffOn_extChartAt_symm p).contMDiffAt
        (mem_interior_iff_mem_nhds.mp hq.2.2)
    exact (hcq.comp q hfq).contMDiffWithinAt
  have henter : ∀ q ∈ V, I.IsInteriorPoint (R q) := by
    intro q hq
    exact DifferentialGeometry.Manifold.isInteriorPoint_of_mem_interiorChart_source I ∞
      (by simp) ((DifferentialGeometry.Manifold.interiorChart I ∞ p).map_target hq.2.2)
  have hgeo : ∀ q ∈ V, HasGeodesicEquationAt g (fun t => R (q.1, t)) q.2 := by
    intro q hq
    have hfq := hF.contMDiffAt (hDopen.mem_nhds hq.1)
    have hslice : ContMDiffAt 𝓘(ℝ) 𝓘(ℝ, E) ∞
        (boundaryPoleFlowFamily G y q.1) q.2 :=
      hfq.comp (f := fun t : ℝ => (q.1, t)) q.2
        (contMDiff_const.prodMk contMDiff_id).contMDiffAt
    have hi := Bundle.ContMDiffRiemannianMetric.isGeodesicOnWithInitial_geodesicFlow
      G y q.1
    have hnative := (hi.isGeodesicAt
      (isOpen_maximalIntegralCurveInterval.mem_nhds hq.1)).hasGeodesicEquationAt
    exact boundaryChart_geodesicEquation g p G O hG
      (boundaryPoleFlowFamily G y q.1) q.2 hq.2 hslice hnative
  have hcanonical : ∃ w : modelBoundary.boundaryE, ∃ c : ℝ, 0 < c ∧
      modelBoundary.inwardCoordE =
        fderiv ℝ (modelBoundaryParam I) b w + c • modelBoundary.inwardCoordE :=
    ⟨0, 1, zero_lt_one, by simp⟩
  obtain ⟨ε, hε, hcenter⟩ := hbirth modelBoundary.inwardCoordE hcanonical
  have hmid : ε / 2 ∈ Ioo 0 ε := by constructor <;> linarith
  obtain ⟨ρ, _σ, hval, hρ, _hσ, _hseed⟩ :=
    boundary_original_phase_seed V R hR henter modelBoundary.inwardCoordE (ε / 2)
      (hcenter (ε / 2) hmid)
  refine ⟨G, hcomplete, O, hpO, hG, V, ρ, hρ, ?_, hbirth⟩
  intro q hq
  refine ⟨hq.1, hq.2, hval q hq, ?_⟩
  have hslice : ContMDiffAt 𝓘(ℝ) 𝓘(ℝ, E) ∞ (fun t => ρ (q.1, t)) q.2 :=
    (hρ.contMDiffAt (V.isOpen.mem_nhds hq)).comp
      (f := fun t : ℝ => (q.1, t)) q.2
      (contMDiff_const.prodMk contMDiff_id).contMDiffAt
  have hnear : ∀ᶠ t in 𝓝 q.2, (q.1, t) ∈ V :=
    (V.isOpen.preimage (continuous_const.prodMk continuous_id)).mem_nhds hq
  have hev : (fun t => ((ρ (q.1, t) : U) : M)) =ᶠ[𝓝 q.2]
      (fun t => R (q.1, t)) := by
    filter_upwards [hnear] with t ht
    exact hval (q.1, t) ht
  have horig := HasGeodesicEquationAt.congr_of_eventuallyEq_at
    hev.eq_of_nhds hev (hgeo q hq)
  exact (boundaryInteriorAtlas_geodesicEquation_iff g (fun t => ρ (q.1, t)) q.2 hslice).mpr
    horig

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
