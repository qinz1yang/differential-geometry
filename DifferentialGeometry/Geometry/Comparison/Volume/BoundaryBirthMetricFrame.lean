import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryCommonPoleFamily
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryJointJacobiFrame
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryPoleJacobiFrame
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryInteriorMetric
import DifferentialGeometry.Geometry.Comparison.Variation.Jacobi.Gram

/-!
Actual common interior angular Jacobi frames have the metric density of the same pole frame.
Original chart and interior inclusion derivatives identify every column before Gram transport.
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set TopologicalSpace
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Boundary
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {E : Type*} [ambientNorm : NormedAddCommGroup E]
  [ambientSpace : NormedSpace ℝ E] [ambientFinite : FiniteDimensional ℝ E]
  {H : Type*} [modelTopology : TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [modelBoundary : HasSmoothBoundary E H I]
  {M : Type*} [manifoldTopology : TopologicalSpace M] [manifoldCharts : ChartedSpace H M]
  [manifoldSmooth : IsManifold I ∞ M] [manifoldT2 : T2Space M]

private theorem birthMetric_infty_ne_zero : (∞ : WithTop ℕ∞) ≠ 0 := by simp

theorem exists_boundary_common_metric_frame (g : SmoothRiemannianMetric I M) (p : M)
    (b : modelBoundary.boundaryE) (hb : extChartAt I p p = modelBoundaryParam I b) :
    let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
      birthMetric_infty_ne_zero (M := M)
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
          (∀ q ∈ V, (ρ q : M) = (extChartAt I p).symm
            (boundaryPoleFlowFamily G (extChartAt I p p) q.1 q.2) ∧
            ∀ w : E,
              IsJacobiAt k (fun t => ρ (q.1, t))
                (fun t => boundaryJointJacobiLinear (I := 𝓘(ℝ, E)) ρ q.1 t w) q.2 ∧
              ContMDiffAt 𝓘(ℝ) (𝓘(ℝ, E)).tangent ∞
                (fun t => (⟨ρ (q.1, t), boundaryJointJacobiLinear
                  (I := 𝓘(ℝ, E)) ρ q.1 t w⟩ : TangentBundle 𝓘(ℝ, E) U)) q.2) ∧
          (∀ q ∈ V, ∀ w z : E,
            k.inner (ρ q) (boundaryJointJacobiLinear (I := 𝓘(ℝ, E)) ρ q.1 q.2 w)
              (boundaryJointJacobiLinear (I := 𝓘(ℝ, E)) ρ q.1 q.2 z) =
              G.inner (boundaryPoleFlowFamily G (extChartAt I p p) q.1 q.2)
                (boundaryPoleJacobiLinear G (extChartAt I p p) q.1 q.2 w)
                (boundaryPoleJacobiLinear G (extChartAt I p p) q.1 q.2 z)) ∧
          (∀ q ∈ V, ∀ e : Fin 2 → E,
            curveDensity k (fun t => ρ (q.1, t))
              (fun i t => boundaryJointJacobiLinear (I := 𝓘(ℝ, E)) ρ q.1 t (e i)) q.2 =
              curveDensity G (boundaryPoleFlowFamily G (extChartAt I p p) q.1)
                (fun i t => boundaryPoleJacobiLinear G (extChartAt I p p) q.1 t (e i)) q.2) ∧
          (∀ v w : E, boundaryPoleJacobiLinear G (extChartAt I p p) v 0 w = 0 ∧
            covDerivAlong G (boundaryPoleFlowFamily G (extChartAt I p p) v)
              (fun t => boundaryPoleJacobiLinear G (extChartAt I p p) v t w) 0 = w) ∧
          ∀ v : E, (∃ w : modelBoundary.boundaryE, ∃ c : ℝ, 0 < c ∧
            v = fderiv ℝ (modelBoundaryParam I) b w + c • modelBoundary.inwardCoordE) →
            ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ Ioo 0 ε, (v, t) ∈ V := by
  let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
    birthMetric_infty_ne_zero (M := M)
  let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
  let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
  let k := boundaryInteriorAtlasMetric g
  dsimp only
  obtain ⟨G, hcomplete, O, hpO, hG, V, ρ, hρ, hall, hbirth⟩ :=
    exists_boundary_common_pole_family g p b hb
  let y := extChartAt I p p
  have hgeo : ∀ q ∈ V, HasGeodesicEquationAt k (fun t => ρ (q.1, t)) q.2 :=
    fun q hq => (hall q hq).2.2.2
  have hcolumn (q : E × ℝ) (hq : q ∈ V) (w : E) :
      (mfderiv 𝓘(ℝ, E) I (Subtype.val : U → M) (ρ q)
        (boundaryJointJacobiLinear (I := 𝓘(ℝ, E)) ρ q.1 q.2 w) : E) =
        mfderiv 𝓘(ℝ, E) I (extChartAt I p).symm
          (boundaryPoleFlowFamily G y q.1 q.2) (boundaryPoleJacobiLinear G y q.1 q.2 w) := by
    have hrho : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (fun u : E => ρ (u, q.2)) q.1 :=
      (hρ.contMDiffAt (V.isOpen.mem_nhds hq)).comp (f := fun u : E => (u, q.2)) q.1
        (contMDiffAt_id.prodMk contMDiffAt_const)
    have hval := DifferentialGeometry.Manifold.contMDiff_intrinsicInterior_val
      I ∞ birthMetric_infty_ne_zero (M := M)
    have hcomp := mfderiv_comp q.1
      ((hval.contMDiffAt (x := ρ q)).mdifferentiableAt (by simp))
      (hrho.mdifferentiableAt (by simp))
    have happ := congrArg (fun A : E →L[ℝ] E => A w) hcomp
    have hnear : ∀ᶠ u in 𝓝 q.1, (u, q.2) ∈ V :=
      (V.isOpen.preimage (continuous_id.prodMk continuous_const)).mem_nhds hq
    have hev : (fun u => ((ρ (u, q.2) : U) : M)) =ᶠ[𝓝 q.1]
        (fun u => (extChartAt I p).symm (boundaryPoleFlowFamily G y u q.2)) := by
      filter_upwards [hnear] with u hu
      exact (hall (u, q.2) hu).2.2.1
    have hder : mfderiv 𝓘(ℝ, E) I (fun u => ((ρ (u, q.2) : U) : M)) q.1 =
        mfderiv 𝓘(ℝ, E) I
          (fun u => (extChartAt I p).symm (boundaryPoleFlowFamily G y u q.2)) q.1 :=
      hev.mfderiv_eq
    have hderApplied := congrArg (fun A : E →L[ℝ] E => A w) hder
    obtain ⟨hDopen, hF⟩ := boundaryPoleFlowFamily_smooth G y
    have hpole : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞
        (fun u : E => boundaryPoleFlowFamily G y u q.2) q.1 :=
      (hF.contMDiffAt (hDopen.mem_nhds (hall q hq).1)).comp
        (f := fun u : E => (u, q.2)) q.1 (contMDiffAt_id.prodMk contMDiffAt_const)
    have hchart : ContMDiffAt 𝓘(ℝ, E) I ∞ (extChartAt I p).symm
        (boundaryPoleFlowFamily G y q.1 q.2) :=
      (contMDiffOn_extChartAt_symm p).contMDiffAt
        (mem_interior_iff_mem_nhds.mp (hall q hq).2.1.2)
    have hcompose := mfderiv_comp q.1 (hchart.mdifferentiableAt (by simp))
      (hpole.mdifferentiableAt (by simp))
    have hcomposeApplied := congrArg (fun A : E →L[ℝ] E => A w) hcompose
    exact happ.symm.trans (hderApplied.trans hcomposeApplied)
  have hgram (q : E × ℝ) (hq : q ∈ V) (w z : E) :
      k.inner (ρ q) (boundaryJointJacobiLinear (I := 𝓘(ℝ, E)) ρ q.1 q.2 w)
        (boundaryJointJacobiLinear (I := 𝓘(ℝ, E)) ρ q.1 q.2 z) =
        G.inner (boundaryPoleFlowFamily G y q.1 q.2)
          (boundaryPoleJacobiLinear G y q.1 q.2 w)
          (boundaryPoleJacobiLinear G y q.1 q.2 z) := by
    have hm := boundaryInteriorAtlasMetric_inner g (ρ q)
      (boundaryJointJacobiLinear (I := 𝓘(ℝ, E)) ρ q.1 q.2 w)
      (boundaryJointJacobiLinear (I := 𝓘(ℝ, E)) ρ q.1 q.2 z)
    rw [hcolumn q hq w, hcolumn q hq z, (hall q hq).2.2.1] at hm
    have htarget := (hall q hq).2.1.2
    have hcoeff := hG (boundaryPoleFlowFamily G y q.1 q.2)
      ⟨(hall q hq).2.1.1, extChartAt_target_subset_range p (interior_subset htarget)⟩
      (boundaryPoleJacobiLinear G y q.1 q.2 w) (boundaryPoleJacobiLinear G y q.1 q.2 z)
    have hc := boundaryChart_metric_inner_of_interior g p htarget
      (boundaryPoleJacobiLinear G y q.1 q.2 w) (boundaryPoleJacobiLinear G y q.1 q.2 z)
    exact hm.trans (hc.symm.trans hcoeff.symm)
  refine ⟨G, hcomplete, O, hpO, hG, V, ρ, hρ, ?_, hgram, ?_,
    (fun v w => boundaryPoleJacobiLinear_initial G y v w), hbirth⟩
  · intro q hq
    exact ⟨(hall q hq).2.2.1,
      fun w => boundaryJointJacobiLinear_jacobi k V ρ hρ hgeo q.1 w q.2 hq⟩
  · intro q hq e
    unfold curveDensity
    apply congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => Real.sqrt A.det)
    ext i j
    exact hgram q hq (e i) (e j)

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
