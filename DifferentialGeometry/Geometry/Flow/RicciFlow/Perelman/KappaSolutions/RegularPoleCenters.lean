import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientPullback
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.NonnegativeCurvatureScalarNorm
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TensorNormFinrankNeZero
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedLength.Minimum.DimensionBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Naturality
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import DifferentialGeometry.Topology.Manifold.ModelWithCorners

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Filter Set
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open CanonicalNeighborhood
open scoped Manifold ContDiff _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)

private local instance centerTopology : TopologicalSpace F.M := F.topology
private local instance centerCharted : ChartedSpace H F.M := F.charted
private local instance centerSmooth : IsManifold I ∞ F.M := F.smooth
private local instance centerT2 : T2Space F.M := F.t2
private local instance centerTangentT2 : T2Space (TangentBundle I F.M) := F.t2TangentBundle
private local instance centerSigma : SigmaCompactSpace F.M := F.sigmaCompact

private theorem exists_redLength_le_half_finrank_of_innerProductSpace
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p : F.M) {b tau : ℝ} (hb : b < 0) (htau : 0 < tau) :
    ∃ q : F.M, redLength F.S b p q tau ≤ (Module.finrank ℝ E : ℝ) / 2 := by
  let _ : NeZero (Module.finrank ℝ E) := by
    obtain ⟨t, _ht, x, hx⟩ := hF.notFlat
    exact ⟨Tensor0SBundle.finrank_ne_zero_of_normSq0S_ne_zero
      (F.S.base.metric t) x (by decide : 0 < 4) (F.S.base.rm04 t x) hx⟩
  let _ : ConnectedSpace F.M := hF.connected
  let _ : TopologicalSpace.MetrizableSpace F.M := Manifold.metrizableSpace I F.M
  let _ : PseudoMetricSpace F.M :=
    TopologicalSpace.pseudoMetrizableSpacePseudoMetric F.M
  have hbmem : b ∈ D.carrier := by simpa only [hF.carrier_eq, mem_Iic] using hb.le
  have hcomplete : RiemannianMetricComplete (I := I) (F.S.base.metric b) :=
    ⟨hF.complete b hbmem⟩
  obtain ⟨C, hC⟩ := hF.globalScalarBound
  let K : ℝ := ((Module.finrank ℝ E : ℝ) ^ 2 * C) ^ 2
  have hreg : Icc (b - (tau + 1)) b ⊆ D.regular := by
    intro t ht
    simpa only [hF.regular_eq, mem_Iio] using ht.2.trans_lt hb
  have hRm : ∀ t ∈ Icc (b - (tau + 1)) b, ∀ z : F.M,
      normSq0S (I := I) (F.S.base.metric t) z 4 (F.S.base.rm04 t z) ≤ K := by
    intro t ht z
    have htc : t ∈ D.carrier := D.regular_subset (hreg ht)
    have hnonnegC : 0 ≤ C := (hC t htc z).1.trans (hC t htc z).2
    have hop : metricAlgebraicCurvatureTensorAt (I := I) (F.S.base.metric t) z ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := F.M) := by
      apply (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff
        (F.S.base.metric t) z).mpr
      intro n c a d
      simpa only [SolutionFamily.rm04, metricRm04StandardAt_apply, metricRm04_apply] using
        hF.nonnegativeCurvatureOperator t htc z n c a d
    have hsqrt := sqrt_metricRm_normSq_le_finrank_sq_mul_scalar (I := I)
      (F.S.base.metric t) z hop
    have hscalar : metricScalarAt (I := I) (F.S.base.metric t) z ≤ C := (hC t htc z).2
    have hn2 : 0 ≤ (Module.finrank ℝ E : ℝ) ^ 2 := sq_nonneg _
    have hs := hsqrt.trans (mul_le_mul_of_nonneg_left hscalar hn2)
    exact (Real.sqrt_le_left (mul_nonneg hn2 hnonnegC)).mp hs
  exact exists_redLen_le F.S F.isSolution K b (tau + 1) tau hcomplete
    htau (by linarith) hreg hRm p

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Filter Set
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open CanonicalNeighborhood
open scoped Manifold ContDiff _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)

private local instance normedCenterTopology : TopologicalSpace F.M := F.topology
private local instance normedCenterCharted : ChartedSpace H F.M := F.charted
private local instance normedCenterSmooth : IsManifold I ∞ F.M := F.smooth
private local instance normedCenterT2 : T2Space F.M := F.t2
private local instance normedCenterSigma : SigmaCompactSpace F.M := F.sigmaCompact

theorem exists_redLength_le_half_finrank_of_ancient_of_neg
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p : F.M) {b tau : ℝ} (hb : b < 0) (htau : 0 < tau) :
    ∃ q : F.M, redLength F.S b p q tau ≤ (Module.finrank ℝ E : ℝ) / 2 := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let e : E ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) := toEuclidean
  let J := I.transContinuousLinearEquiv e
  let Phi : F.M ≃ₘ⟮I, J⟯ F.M := ContinuousLinearEquiv.toTransContinuousLinearEquiv I F.M e
  let G := F.pullback Phi.symm
  have hG : IsAncientKappaSolution kappa G := F.pullback_isAncientKappaSolution Phi.symm hF
  obtain ⟨q, hq⟩ :=
    exists_redLength_le_half_finrank_of_innerProductSpace G hG p hb htau
  refine ⟨q, ?_⟩
  have hcost := lCost_pullback F.S Phi.symm b p q tau
  change lCost (F.S.pullback Phi.symm) b p q tau = lCost F.S b p q tau at hcost
  change lCost (F.S.pullback Phi.symm) b p q tau / (2 * Real.sqrt tau) ≤ _ at hq
  change lCost F.S b p q tau / (2 * Real.sqrt tau) ≤ _
  rw [hcost] at hq
  simpa only [finrank_euclideanSpace, Fintype.card_fin] using hq

theorem exists_eventually_redLength_le_half_finrank_of_ancient_of_neg
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p : F.M) {b : ℝ} (hb : b < 0)
    (tau : ℕ → ℝ) (hescape : Tendsto tau atTop atTop) :
    ∃ q : ℕ → F.M, ∀ᶠ i in atTop,
      0 < tau i + b ∧ redLength F.S b p (q i) (tau i + b) ≤
        (Module.finrank ℝ E : ℝ) / 2 := by
  classical
  have hpoint (i : ℕ) : ∃ q : F.M, 0 < tau i + b →
      redLength F.S b p q (tau i + b) ≤ (Module.finrank ℝ E : ℝ) / 2 := by
    by_cases ht : 0 < tau i + b
    · obtain ⟨q, hq⟩ := exists_redLength_le_half_finrank_of_ancient_of_neg F hF p hb ht
      exact ⟨q, fun _ ↦ hq⟩
    · exact ⟨p, fun h ↦ (ht h).elim⟩
  choose q hq using hpoint
  refine ⟨q, ?_⟩
  filter_upwards [hescape.eventually_gt_atTop (-b)] with i hi
  have ht : 0 < tau i + b := by linarith
  exact ⟨ht, hq i ht⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
