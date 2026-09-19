import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientTerminalBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TensorNormFinrankNeZero
import DifferentialGeometry.Geometry.Flow.RicciFlow.HamiltonHarnack.TraceCorollaries

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Set Filter
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open CanonicalNeighborhood
open scoped Manifold ContDiff _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)

private local instance ancientScalarTopology : TopologicalSpace F.M := F.topology
private local instance ancientScalarCharted : ChartedSpace H F.M := F.charted
private local instance ancientScalarSmooth : IsManifold I ∞ F.M := F.smooth
private local instance ancientScalarC1 : IsManifold I 1 F.M :=
  IsManifold.of_le (n := ∞) (by decide)
private local instance ancientScalarT2 : T2Space F.M := F.t2
private local instance ancientScalarTangentT2 : T2Space (TangentBundle I F.M) := F.t2TangentBundle
private local instance ancientScalarSigma : SigmaCompactSpace F.M := F.sigmaCompact

theorem ancientKappa_scalar_monotoneOn
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (x : F.M) :
    MonotoneOn (fun t : ℝ => F.S.scalar t x) (Set.Iic 0) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : NeZero (Module.finrank ℝ E) := by
    obtain ⟨t, _ht, z, hz⟩ := hF.notFlat
    exact ⟨Tensor0SBundle.finrank_ne_zero_of_normSq0S_ne_zero
      (F.S.base.metric t) z (by decide : 0 < 4) (F.S.base.rm04 t z) hz⟩
  have hcont : ContinuousOn (fun t : ℝ => F.S.scalar t x) (Set.Iic 0) := by
    have hmap : Continuous (fun t : ℝ => (t, x)) := continuous_id.prodMk continuous_const
    simpa only [Function.comp_def] using F.isSolution.scalarCont.comp hmap.continuousOn
      (fun t (ht : t ∈ Set.Iic (0 : ℝ)) => ⟨by simpa only [hF.carrier_eq] using ht, Set.mem_univ x⟩)
  have hoperator : ∀ t ∈ D.regular, ∀ y : F.M,
      metricAlgebraicCurvatureTensorAt (I := I) (F.S.base.metric t) y ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := F.M) := by
    intro t ht y
    apply (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff
      (I := I) (F.S.base.metric t) y).mpr
    intro n c v w
    simpa only [SolutionFamily.rm04, metricRm04StandardAt_apply, metricRm04_apply] using
      hF.nonnegativeCurvatureOperator t (D.regular_subset ht) y n c v w
  apply monotoneOn_of_deriv_nonneg (convex_Iic 0) hcont
  · intro t ht
    have htreg : t ∈ D.regular := by
      simpa only [hF.regular_eq, interior_Iic, Set.mem_Iio] using ht
    exact ((F.isSolution.scalarTime (K := D.carrier) (D.regular_subset htreg)
      (fun _ hs => hs) x).differentiableAt (D.regular_mem_nhds htreg)).differentiableWithinAt
  · intro t ht
    have htneg : t < 0 := by simpa only [interior_Iic, Set.mem_Iio] using ht
    apply hamilton_ancient_scalar_deriv_nonneg F.S F.isSolution
      (fun s hs => ⟨hF.complete s (D.regular_subset hs)⟩)
      (ancientKappa_regularSlabBound_finrank F hF) hoperator
    intro s hs
    simpa only [hF.regular_eq, Set.mem_Iio] using hs.trans_lt htneg

theorem exists_eventually_scalar_pos_of_ancient
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) :
    ∃ x : F.M, ∀ᶠ T in 𝓝[≤] (0 : ℝ), 0 < F.S.scalar T x := by
  obtain ⟨t, ht, x, hx⟩ := hF.notFlat
  have hnonneg : 0 ≤ F.rmNormSq (I := I) t x := by
    exact DifferentialGeometry.Tensor0SBundle.normSq0S_nonneg
      (I := I) (F.S.base.metric t) x 4 (F.S.base.rm04 t x)
  have hpos : 0 < F.S.scalar t x :=
    pos_of_mul_pos_right ((Real.sqrt_pos.mpr (lt_of_le_of_ne hnonneg hx.symm)).trans_le
      (ancientKappa_rmNormLeScalar_finrank F hF t ht x)) (sq_nonneg _)
  have ht0 : t ≤ 0 := by simpa only [hF.carrier_eq, mem_Iic] using ht
  have hzero : 0 < F.S.scalar 0 x := hpos.trans_le
    (ancientKappa_scalar_monotoneOn F hF x ht0 (mem_Iic.mpr le_rfl) ht0)
  have hc : ContinuousOn (fun T : ℝ => F.S.scalar T x) (Iic 0) := by
    have hmap : Continuous (fun T : ℝ => (T, x)) := continuous_id.prodMk continuous_const
    have hm : MapsTo (fun T : ℝ => (T, x)) (Iic 0) (D.carrier ×ˢ univ) := by
      intro T hT
      exact ⟨by simpa only [hF.carrier_eq, mem_Iic] using hT, mem_univ x⟩
    have hh := F.isSolution.scalarCont.comp hmap.continuousOn hm
    exact hh
  exact ⟨x, (hc 0 (mem_Iic.mpr le_rfl)).eventually (Ioi_mem_nhds hzero)⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
