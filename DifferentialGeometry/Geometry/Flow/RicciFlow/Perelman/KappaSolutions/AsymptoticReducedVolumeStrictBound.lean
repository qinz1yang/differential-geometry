import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.BackwardSliceMass
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientNonflatness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientCurvatureBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.Rigidity.Scalar


noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Set
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open CanonicalNeighborhood
open scoped _root_.Manifold ContDiff ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)

private local instance : TopologicalSpace F.M := F.topology
private local instance : ChartedSpace H F.M := F.charted
private local instance : IsManifold I ∞ F.M := F.smooth
private local instance : T2Space F.M := F.t2
private local instance : SigmaCompactSpace F.M := F.sigmaCompact

theorem asymptoticReducedVolume_lt_one_of_ancient
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p : F.M)
    {b : ℝ} (hb : b < 0) :
    asymptoticReducedVolume F.S b p < 1 := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : ConnectedSpace F.M := hF.connected
  obtain ⟨t, htb, ht, y, hy⟩ := hF.exists_rmNormSq_ne_zero_before b
  have hsqrt : 0 < Real.sqrt (F.rmNormSq (I := I) t y) := by
    apply Real.sqrt_pos.2
    exact lt_of_le_of_ne
      (by
        simpa only [PointedFlowData.rmNormSq, SolutionOn.family] using
          normSq0S_nonneg (I := I) (F.S.base.metric t) y 4 (F.S.base.rm04 t y))
      (Ne.symm hy)
  have hscalar : 0 < F.S.scalar t y := by
    have hbound := hF.rmNorm_le_scalar t ht y
    by_contra h
    have hnonpos : (Module.finrank ℝ E : ℝ) ^ 2 * F.S.scalar t y ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (le_of_not_gt h)
    exact (not_lt_of_ge (hbound.trans hnonpos)) hsqrt
  let s : ℝ := b - t
  have hs : 0 < s := sub_pos.mpr htb
  have htime : b - s = t := by
    dsimp only [s]
    ring
  have hbmem : b ∈ D.carrier := by
    simpa only [hF.carrier_eq, mem_Iic] using hb.le
  have hcomplete : RiemannianMetricComplete (I := I) (F.S.base.metric b) :=
    ⟨hF.complete b hbmem⟩
  have hslab : Icc (b - 2 * s) b ⊆ D.regular := by
    intro u hu
    simpa only [hF.regular_eq, mem_Iio] using hu.2.trans_lt hb
  obtain ⟨K, hK⟩ := hF.exists_rmNormSq_le
  have hstrict : intrinsicReducedVolume F.S b p (2 * s) < 1 := by
    change redVolume F.S b p (2 * s) < 1
    apply redVolume_lt_one_of_scalar_ne_zero F.S F.isSolution b hcomplete p
      (fun _ _ hreg => ⟨K, fun u hu z => hK u (D.regular_subset (hreg hu)) z⟩)
      hs (by linarith only [hs]) hslab y
    rw [htime]
    exact hscalar.ne'
  have hinf : asymptoticReducedVolume F.S b p ≤
      intrinsicReducedVolume F.S b p (2 * s) :=
    iInf_le (fun tau : Ioi (0 : ℝ) => intrinsicReducedVolume F.S b p tau)
      ⟨2 * s, mul_pos (by norm_num) hs⟩
  exact hinf.trans_lt hstrict

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
