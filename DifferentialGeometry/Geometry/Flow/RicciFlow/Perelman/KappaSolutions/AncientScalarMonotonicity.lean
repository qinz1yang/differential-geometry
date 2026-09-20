import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientCurvatureBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TensorNormFinrankNeZero
import DifferentialGeometry.Geometry.Flow.RicciFlow.HamiltonHarnack.TraceCorollaries
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TerminalMetricLowerBound
import DifferentialGeometry.Geometry.Curvature.Bounds.RicciUpper

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.IsAncientKappaSolution

open Bundle Set
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open scoped Manifold ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} {F : PointedFlowData.{u, uE, uH} (I := I) D}

private local instance : TopologicalSpace F.M := F.topology
private local instance : ChartedSpace H F.M := F.charted
private local instance : IsManifold I ∞ F.M := F.smooth
private local instance : IsManifold I 1 F.M := IsManifold.of_le (n := ∞) (by decide)
private local instance : T2Space F.M := F.t2
private local instance : SigmaCompactSpace F.M := F.sigmaCompact

theorem scalar_monotoneOn {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (x : F.M) :
    MonotoneOn (fun t : ℝ => F.S.scalar t x) (Iic 0) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : NeZero (Module.finrank ℝ E) := ⟨by
    obtain ⟨t, ht, y, hy⟩ := hF.notFlat
    exact finrank_ne_zero_of_normSq0S_ne_zero (F.S.base.metric t) y (by norm_num : 0 < 4)
      (F.S.base.rm04 t y) hy⟩
  have hcomplete : ∀ t ∈ D.regular,
      RiemannianMetricComplete (I := I) (F.S.base.metric t) :=
    fun t ht => ⟨hF.complete t (D.regular_subset ht)⟩
  obtain ⟨K, hK⟩ := hF.exists_rmNormSq_le
  have hcurv : ∀ a b : ℝ, Icc a b ⊆ D.regular →
      ∃ C : ℝ, ∀ t ∈ Icc a b, ∀ y : F.M,
        normSq0S (I := I) (F.S.base.metric t) y 4 (F.S.base.rm04 t y) ≤ C := by
    intro a b hab
    exact ⟨K, fun t ht y => hK t (D.regular_subset (hab ht)) y⟩
  have hR : ∀ t ∈ D.regular, ∀ y : F.M,
      metricAlgebraicCurvatureTensorAt (I := I) (F.S.base.metric t) y ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := F.M) := by
    intro t ht y
    apply mem_algebraicCurvatureOperatorNonnegativeCone.mpr
    intro n c v w
    have h := hF.nonnegativeCurvatureOperator t (D.regular_subset ht) y n c v w
    simpa only [algebraicCurvatureOperatorQuadraticEval, metricAlgebraicCurvatureTensorAt,
      tensor04StandardAt, SolutionFamily.rm04, metricRm04_apply] using h
  have hcont : ContinuousOn (fun t : ℝ => F.S.scalar t x) (Iic 0) := by
    have hmap : Continuous (fun t : ℝ => (t, x)) := continuous_id.prodMk continuous_const
    have h := F.isSolution.scalarCont.comp hmap.continuousOn
      (fun t (ht : t ∈ Iic (0 : ℝ)) => ⟨by simpa only [hF.carrier_eq] using ht, mem_univ x⟩)
    simpa only [Function.comp_def] using h
  apply monotoneOn_of_deriv_nonneg (convex_Iic 0) hcont
  · intro t ht
    have htreg : t ∈ D.regular := by
      simpa only [hF.regular_eq, interior_Iic, mem_Iio] using ht
    exact ((F.isSolution.scalarTime (K := D.carrier)
      (D.regular_subset htreg) (fun _ hs => hs) x).differentiableAt
        (D.regular_mem_nhds htreg)).differentiableWithinAt
  · intro t ht
    have ht0 : t < 0 := by simpa only [interior_Iic, mem_Iio] using ht
    exact hamilton_ancient_scalar_deriv_nonneg F.S F.isSolution hcomplete hcurv hR
      (fun r hr => by simpa only [hF.regular_eq, mem_Iio] using hr.trans_lt ht0) x

theorem metric_inner_le_exp_scalar_bound {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F)
    {a b C : ℝ} (hab : a ≤ b) (hb : b ≤ 0)
    (x : F.M) (hC : F.S.scalar b x ≤ C) (v : TangentSpace I x) :
    (F.S.base.metric a).inner x v v ≤
      Real.exp (C * (b - a)) * (F.S.base.metric b).inner x v v := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hslab : Icc a b ⊆ D.carrier := by
    intro t ht
    simpa only [hF.carrier_eq, mem_Iic] using ht.2.trans hb
  have hreg : Ioo a b ⊆ D.regular := by
    intro t ht
    simpa only [hF.regular_eq, mem_Iio] using ht.2.trans_le hb
  have hRic : ∀ t ∈ Ioo a b, ∀ y ∈ ({x} : Set F.M), ∀ w : TangentSpace I y,
      F.S.ricciAt t y (vec2 w w) ≤ (C / 2) * (F.S.base.metric t).inner y w w := by
    intro t ht y hy w
    have hyx : y = x := mem_singleton_iff.mp hy
    subst y
    have ht0 : t ≤ 0 := ht.2.le.trans hb
    have hR : F.S.scalar t x ≤ C := (hF.scalar_monotoneOn x ht0 hb ht.2.le).trans hC
    have hcone : metricAlgebraicCurvatureTensorAt (I := I) (F.S.base.metric t) x ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := F.M) := by
      apply (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff
        (I := I) (F.S.base.metric t) x).mpr
      intro n c u w
      have htcar : t ∈ D.carrier := by simpa only [hF.carrier_eq, mem_Iic] using ht0
      simpa only [SolutionFamily.rm04, metricRm04StandardAt_apply, metricRm04_apply] using
        hF.nonnegativeCurvatureOperator t htcar x n c u w
    have hupper := metricRicciAt_le_half_scalar_mul_inner_of_curvatureOperator_nonnegative
      (F.S.base.metric t) x hcone w
    exact hupper.trans (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hR (by norm_num))
      (metric_inner_self_nonneg (F.S.base.metric t) x w))
  have hraw := metric_inner_lower_bound_of_ricci_upper_interior F.S F.isSolution
    hab hslab hreg hRic (mem_singleton x) v
  have heq : 2 * (C / 2) * (b - a) = C * (b - a) := by ring
  rw [heq] at hraw
  calc
    (F.S.base.metric a).inner x v v =
        Real.exp (C * (b - a)) *
          (Real.exp (-(C * (b - a))) * (F.S.base.metric a).inner x v v) := by
      rw [← mul_assoc, ← Real.exp_add]
      simp only [add_neg_cancel, Real.exp_zero, one_mul]
    _ ≤ Real.exp (C * (b - a)) * (F.S.base.metric b).inner x v v :=
      mul_le_mul_of_nonneg_left hraw (Real.exp_pos _).le

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.IsAncientKappaSolution
