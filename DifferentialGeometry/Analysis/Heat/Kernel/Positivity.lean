import DifferentialGeometry.Analysis.Heat.Kernel.Regularity
import Mathlib.Geometry.Manifold.BumpFunction

noncomputable section

namespace DifferentialGeometry.Analysis.HeatEquation

open MeasureTheory Set
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Laplacian (SmoothScalar smoothToLp)
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [T2Space M] [CompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem heatKernel_nonneg (g : SmoothRiemannianMetric I M)
    {t : Real} (ht : 0 < t) (x y : M) : 0 ≤ heatKernel g t x y := by
  classical
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  let : μ.IsOpenPosMeasure := riemannianVolumeMeasure_isOpenPosMeasure g
  have hK : Continuous (fun z => heatKernel g t x z) :=
    (continuousOn_heatKernel g).comp_continuous
      (continuous_const.prodMk (continuous_const.prodMk continuous_id))
      (fun z => ⟨ht, mem_univ _⟩)
  by_contra hn
  have hneg : heatKernel g t x y < 0 := lt_of_not_ge hn
  have hU : {z | heatKernel g t x z < 0} ∈ 𝓝 y :=
    hK.continuousAt.preimage_mem_nhds (Iio_mem_nhds hneg)
  obtain ⟨f, _, hf⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := I) y).mem_iff.mp hU
  let u : SmoothScalar g := ⟨f, f.contMDiff⟩
  have hu := scalarHeatFlow_smoothInitial_nonneg g u ht.le
    (fun z => f.nonneg (x := z)) t ⟨ht.le, le_rfl⟩ x
  have heq : (∫ z, heatKernel g t x z * f z ∂μ) =
      scalarHeatFlow g (smoothToLp g u) t x := by
    rw [← integral_heatKernel_mul_eq_scalarHeatFlow g (smoothToLp g u) ht x]
    apply integral_congr_ae
    filter_upwards [u.memLp_two.coeFn_toLp] with z hz
    rw [DifferentialGeometry.Analysis.Laplacian.smoothToLp_apply]
    exact congrArg (heatKernel g t x z * ·) hz.symm
  have hF : Continuous (fun z => -(heatKernel g t x z * f z)) :=
    (hK.mul f.contMDiff.continuous).neg
  have hFint : Integrable (fun z => -(heatKernel g t x z * f z)) μ :=
    DifferentialGeometry.Integral.DivergenceTheorem.Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure
      g hF (HasCompactSupport.of_compactSpace _)
  have hFnonneg : 0 ≤ (fun z => -(heatKernel g t x z * f z)) := by
    intro z
    change 0 ≤ -(heatKernel g t x z * f z)
    by_cases hz : z ∈ tsupport f
    · exact neg_nonneg.mpr (mul_nonpos_of_nonpos_of_nonneg (hf hz).le f.nonneg)
    · rw [image_eq_zero_of_notMem_tsupport hz, mul_zero, neg_zero]
  have hFy : -(heatKernel g t x y * f y) ≠ 0 := by
    rw [f.eq_one, mul_one]
    exact neg_ne_zero.mpr hneg.ne
  have hpos := integral_pos_of_integrable_nonneg_nonzero hF hFint hFnonneg hFy
  rw [integral_neg, heq] at hpos
  linarith

theorem integral_heatKernel (g : SmoothRiemannianMetric I M)
    {t : Real} (ht : 0 < t) (x : M) :
    (∫ y, heatKernel g t x y ∂riemannianVolumeMeasure (I := I) (M := M) g) = 1 := by
  let u : SmoothScalar g := ⟨fun _ => 1, contMDiff_const⟩
  have hv : Parabolic.IsHeatOnStationary
      (Geometry.Curvature.RealTimeInterval.closed 0 t ht.le) g (fun _ _ => 1) := by
    refine ⟨contMDiffOn_const, continuousOn_const, fun _ _ => contMDiff_const, ?_⟩
    intro s hs y
    simpa only [Geometry.Curvature.laplacianAt, Geometry.Curvature.stationaryMetricFamily,
      Geometry.Operator.laplacian_const, mul_one, add_zero] using
      hasDerivAt_const s (1 : Real)
  have hconst := scalarHeatFlow_smoothInitial_unique g u ht.le (fun _ _ => 1) hv
    (fun _ => rfl) t ⟨ht.le, le_rfl⟩ x
  rw [hconst]
  calc
    _ = ∫ y, heatKernel g t x y * smoothToLp g u y
        ∂riemannianVolumeMeasure (I := I) (M := M) g := by
      apply integral_congr_ae
      filter_upwards [u.memLp_two.coeFn_toLp] with y hy
      rw [DifferentialGeometry.Analysis.Laplacian.smoothToLp_apply, hy]
      exact (mul_one _).symm
    _ = _ := integral_heatKernel_mul_eq_scalarHeatFlow g (smoothToLp g u) ht x

theorem heatKernel_pos [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M) {t : Real} (ht : 0 < t) (x y : M) :
    0 < heatKernel g t x y := by
  let u : SmoothScalar g := ⟨fun z => heatKernel g (t / 2) x z,
    heatKernel_right_contMDiff g (half_pos ht) x⟩
  have hnonneg : ∀ z, 0 ≤ u.toFun z := heatKernel_nonneg g (half_pos ht) x
  obtain ⟨c, hc⟩ : ∃ c, 0 < u.toFun c := by
    by_contra h
    have hz : ∀ c, u.toFun c = 0 := fun c =>
      le_antisymm (not_lt.mp (not_exists.mp h c)) (hnonneg c)
    have hi := integral_heatKernel g (half_pos ht) x
    change (∫ z, u.toFun z ∂riemannianVolumeMeasure (I := I) (M := M) g) = 1 at hi
    simp_rw [hz, integral_zero] at hi
    exact zero_ne_one hi
  have hpos := scalarHeatFlow_smoothInitial_strict_pos_of_nonzero g u ht.le
    hnonneg hc (show t / 2 ∈ Ioo 0 t from ⟨half_pos ht, half_lt_self ht⟩) y
  rw [← integral_heatKernel_mul_eq_scalarHeatFlow g (smoothToLp g u) (half_pos ht) y] at hpos
  have heq : (∫ z, heatKernel g (t / 2) y z * smoothToLp g u z
      ∂riemannianVolumeMeasure (I := I) (M := M) g) = heatKernel g t x y := by
    calc
      _ = ∫ z, heatKernel g (t / 2) y z * heatKernel g (t / 2) z x
          ∂riemannianVolumeMeasure (I := I) (M := M) g := by
        apply integral_congr_ae
        filter_upwards [u.memLp_two.coeFn_toLp] with z hz
        rw [DifferentialGeometry.Analysis.Laplacian.smoothToLp_apply, hz]
        exact congrArg (heatKernel g (t / 2) y z * ·) (heatKernel_symm g (t / 2) x z)
      _ = _ := by
        rw [heatKernel_convolution g (half_pos ht) (half_pos ht), add_halves,
          heatKernel_symm g t y x]
  exact heq ▸ hpos

end DifferentialGeometry.Analysis.HeatEquation
