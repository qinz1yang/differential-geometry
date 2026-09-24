import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientNonflatness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientCurvatureBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.HamiltonHarnack.TraceCorollaries
import DifferentialGeometry.Geometry.Curvature.Bounds.ScalarNorm
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TensorNormFinrankNeZero


noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.IsAncientKappaSolution

open Set
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} {F : PointedFlowData.{u, uE, uH} (I := I) D}

private local instance : TopologicalSpace F.M := F.topology
private local instance : ChartedSpace H F.M := F.charted
private local instance : IsManifold I ∞ F.M := F.smooth
private local instance : T2Space F.M := F.t2
private local instance : SigmaCompactSpace F.M := F.sigmaCompact

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_rmNormSq_ne_zero_at_of_negative
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    {b : ℝ} (hb : b < 0) :
    ∃ x : F.M, F.rmNormSq (I := I) b x ≠ 0 := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨t, htb, ht, y, hy⟩ := exists_rmNormSq_ne_zero_before hF b
  let _ : NeZero (Module.finrank ℝ E) :=
    ⟨finrank_ne_zero_of_normSq0S_ne_zero (I := I) (F.S.base.metric t) y
      (by decide : 0 < 4) (F.S.base.rm04 t y) hy⟩
  let _ : IsManifold I 1 F.M := IsManifold.of_le (n := ∞) (by decide)
  have hsqrt_t : 0 < Real.sqrt (F.rmNormSq (I := I) t y) := by
    apply Real.sqrt_pos.2
    exact lt_of_le_of_ne
      (by
        simpa only [PointedFlowData.rmNormSq, SolutionOn.family] using
          normSq0S_nonneg (I := I) (F.S.base.metric t) y 4 (F.S.base.rm04 t y))
      (Ne.symm hy)
  have hscalar_t : 0 < F.S.scalar t y := by
    have hbound := hF.rmNorm_le_scalar t ht y
    by_contra h
    have hnonpos : (Module.finrank ℝ E : ℝ) ^ 2 * F.S.scalar t y ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (le_of_not_gt h)
    exact (not_lt_of_ge (hbound.trans hnonpos)) hsqrt_t
  have hcomplete : ∀ s ∈ D.regular,
      RiemannianMetricComplete (I := I) (F.S.base.metric s) := by
    intro s hs
    exact ⟨hF.complete s (D.regular_subset hs)⟩
  obtain ⟨K, hK⟩ := hF.exists_rmNormSq_le
  have hcurv : ∀ a c : ℝ, Icc a c ⊆ D.regular →
      ∃ C : ℝ, ∀ s ∈ Icc a c, ∀ z : F.M,
        normSq0S (I := I) (F.S.base.metric s) z 4 (F.S.base.rm04 s z) ≤ C := by
    intro a c hslab
    exact ⟨K, fun s hs z => hK s (D.regular_subset (hslab hs)) z⟩
  have hR : ∀ s ∈ D.regular, ∀ z : F.M,
      metricAlgebraicCurvatureTensorAt (I := I) (F.S.base.metric s) z ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := F.M) := by
    intro s hs z
    apply mem_algebraicCurvatureOperatorNonnegativeCone.mpr
    intro n c v w
    simpa only [algebraicCurvatureOperatorQuadraticEval,
      metricAlgebraicCurvatureTensorAt, tensor04StandardAt, SolutionFamily.rm04,
      metricRm04_apply] using hF.nonnegativeCurvatureOperator s
      (D.regular_subset hs) z n c v w
  have hIic : Iic b ⊆ D.regular := by
    intro s hs
    simpa only [hF.regular_eq, mem_Iio] using hs.trans_lt hb
  have hscalar_b : 0 < F.S.scalar b y := by
    have hmono := hamilton_ancient_scalar_two_time (I := I) F.S F.isSolution
      hcomplete hcurv hR htb.le hIic y
    exact lt_of_lt_of_le hscalar_t hmono
  refine ⟨y, ?_⟩
  intro hzero
  have hbound := scalar_abs_le_rm (I := I) (M := F.M)
    (F.S.base.metric b) y
  have hz : normSq0S (I := I) (F.S.base.metric b) y 4
      (metricRm04At (I := I) (F.S.base.metric b) y) = 0 := hzero
  rw [hz, Real.sqrt_zero, mul_zero] at hbound
  have habs : |F.S.scalar b y| = 0 := le_antisymm hbound (abs_nonneg _)
  exact (ne_of_gt hscalar_b) (abs_eq_zero.mp habs)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.IsAncientKappaSolution

end
