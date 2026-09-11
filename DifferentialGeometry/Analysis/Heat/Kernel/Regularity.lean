import DifferentialGeometry.Analysis.Heat.Kernel.Semigroup
import DifferentialGeometry.Analysis.Heat.Kernel.Smoothness

set_option autoImplicit false
noncomputable section
namespace DifferentialGeometry.Analysis.HeatEquation
open MeasureTheory Set
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Connection (LeviCivita LeviCivita_eq_leviCivitaConnectionOfMetric)
open DifferentialGeometry.Geometry.Curvature (laplacianAt RealTimeInterval stationaryMetricFamily)
open scoped Manifold ContDiff Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [T2Space M] [CompactSpace M]
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

private theorem exists_heatKernel_eq_scalarHeatFlow (g : SmoothRiemannianMetric I M)
    {a : Real} (ha : 0 < a) (y : M) :
    ∃ u₀ : Lp Real 2 (riemannianVolumeMeasure (I := I) (M := M) g),
      ∀ t : Real, a < t → ∀ x : M,
        heatKernel g t x y = scalarHeatFlow g u₀ (t - a) x := by
  let : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g
  have hcont : Continuous (fun z : M => heatKernel g a z y) :=
    (continuousOn_heatKernel g).comp_continuous
      (continuous_const.prodMk (continuous_id.prodMk continuous_const))
      (fun z => ⟨ha, Set.mem_univ _⟩)
  have hmem : MemLp (fun z : M => heatKernel g a z y) 2
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    hcont.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  refine ⟨hmem.toLp _, ?_⟩
  intro t hat x
  have hta : 0 < t - a := sub_pos.mpr hat
  calc
    _ = ∫ z, heatKernel g (t - a) x z * heatKernel g a z y
        ∂riemannianVolumeMeasure (I := I) (M := M) g := by
      rw [heatKernel_convolution g ha hta, sub_add_cancel]
    _ = ∫ z, heatKernel g (t - a) x z * hmem.toLp _ z
        ∂riemannianVolumeMeasure (I := I) (M := M) g := by
      apply integral_congr_ae
      filter_upwards [hmem.coeFn_toLp] with z hz
      rw [hz]
    _ = _ := integral_heatKernel_mul_eq_scalarHeatFlow g (hmem.toLp _) hta x

theorem contMDiffOn_heatKernel_left (g : SmoothRiemannianMetric I M) (y : M) :
    ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
      (fun q : Real × M => heatKernel g q.1 q.2 y) (Ioi 0 ×ˢ univ) := by
  exact (contMDiffOn_heatKernel g).comp
    (contMDiff_fst.prodMk (contMDiff_snd.prodMk contMDiff_const)).contMDiffOn
    (fun q hq => ⟨hq.1, mem_univ _⟩)

theorem heatKernel_left_contMDiff (g : SmoothRiemannianMetric I M)
    {t : Real} (ht : 0 < t) (y : M) :
    ContMDiff I 𝓘(Real, Real) ∞ (fun x => heatKernel g t x y) := by
  have h := (contMDiffOn_heatKernel_left g y).comp (s := univ)
    (contMDiff_const.prodMk contMDiff_id).contMDiffOn
    (fun x _ => ⟨ht, mem_univ _⟩)
  exact contMDiffOn_univ.mp h

theorem heatKernel_right_contMDiff (g : SmoothRiemannianMetric I M)
    {t : Real} (ht : 0 < t) (x : M) :
    ContMDiff I 𝓘(Real, Real) ∞ (fun y => heatKernel g t x y) := by
  simpa only [heatKernel_symm g t x] using heatKernel_left_contMDiff g ht x

theorem heatKernel_hasDerivAt (g : SmoothRiemannianMetric I M)
    {t : Real} (ht : 0 < t) (x y : M) :
    HasDerivAt (fun s => heatKernel g s x y)
      (laplacian (LeviCivita g) g (fun z => heatKernel g t z y) x) t := by
  obtain ⟨u₀, heq⟩ := exists_heatKernel_eq_scalarHeatFlow g (half_pos ht) y
  have hab : t / 4 < t + 1 := by linarith
  have hu := scalarHeatFlow_isHeatOnStationary g u₀ hab (by linarith : 0 < t / 4)
  have ht' : t - t / 2 ∈
      (RealTimeInterval.closed (t / 4) (t + 1) hab.le).regular := by
    change t / 4 < t - t / 2 ∧ t - t / 2 < t + 1
    constructor <;> linarith
  have hderiv := (hu.equation (t - t / 2) ht' x).comp t
    ((hasDerivAt_id t).sub_const (t / 2))
  have hEq : (fun s => heatKernel g s x y) =ᶠ[𝓝 t]
      (fun s => scalarHeatFlow g u₀ (s - t / 2) x) := by
    filter_upwards [Ioi_mem_nhds (half_lt_self ht)] with s hs
    exact heq s hs x
  have hfun : (fun z => heatKernel g t z y) = scalarHeatFlow g u₀ (t - t / 2) :=
    funext (heq t (half_lt_self ht))
  rw [hfun]
  simpa only [mul_one, zero_mul, add_zero, laplacianAt, stationaryMetricFamily,
    LeviCivita_eq_leviCivitaConnectionOfMetric] using hderiv.congr_of_eventuallyEq hEq


theorem heatKernel_isHeatOnStationary (g : SmoothRiemannianMetric I M)
    (D : RealTimeInterval) (hD : D.carrier ⊆ Ioi 0) (y : M) :
    Parabolic.IsHeatOnStationary D g (fun t x => heatKernel g t x y) where
  jointSmooth := (contMDiffOn_heatKernel_left g y).mono
    (prod_mono (D.regular_subset.trans hD) Subset.rfl)
  jointCont := (contMDiffOn_heatKernel_left g y).continuousOn.mono
    (prod_mono hD Subset.rfl)
  sliceSmooth t ht := heatKernel_left_contMDiff g (hD ht) y
  equation t ht x := by
    simpa only [zero_mul, add_zero, laplacianAt, stationaryMetricFamily,
      LeviCivita_eq_leviCivitaConnectionOfMetric] using
      heatKernel_hasDerivAt g (hD (D.regular_subset ht)) x y

end DifferentialGeometry.Analysis.HeatEquation
