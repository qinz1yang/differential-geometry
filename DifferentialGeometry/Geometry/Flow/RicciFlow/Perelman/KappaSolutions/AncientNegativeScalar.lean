import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ModelWitness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.NonnegativeCurvatureScalarNorm

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Filter Set
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open CanonicalNeighborhood
open scoped _root_.Manifold ContDiff _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)

private local instance scalarTopology : TopologicalSpace F.M := F.topology
private local instance scalarCharted : ChartedSpace H F.M := F.charted
private local instance scalarSmooth : IsManifold I ∞ F.M := F.smooth
private local instance scalarT2 : T2Space F.M := F.t2
private local instance scalarSigma : SigmaCompactSpace F.M := F.sigmaCompact

theorem exists_neg_time_scalar_pos_of_ancient
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) :
    ∃ b : ℝ, b < 0 ∧ ∃ x : F.M, 0 < F.S.scalar b x := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨t, ht, x, hx⟩ := hF.notFlat
  have hop : metricAlgebraicCurvatureTensorAt (I := I) (F.S.base.metric t) x ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I) (M := F.M) := by
    apply (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff
      (F.S.base.metric t) x).mpr
    intro n c a d
    simpa only [SolutionFamily.rm04, metricRm04StandardAt_apply, metricRm04_apply] using
      hF.nonnegativeCurvatureOperator t ht x n c a d
  have hsqrt := sqrt_metricRm_normSq_le_finrank_sq_mul_scalar (I := I)
    (F.S.base.metric t) x hop
  have hnorm : 0 < normSq0S (I := I) (F.S.base.metric t) x 4
      (F.S.base.rm04 t x) :=
    lt_of_le_of_ne (normSq0S_nonneg (F.S.base.metric t) x 4 _) (Ne.symm hx)
  have hscalar : 0 < F.S.scalar t x := by
    by_contra h
    have hnonpos : (Module.finrank ℝ E : ℝ) ^ 2 * F.S.scalar t x ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (le_of_not_gt h)
    have hpos := Real.sqrt_pos.mpr hnorm
    exact (not_lt_of_ge (hsqrt.trans hnonpos)) hpos
  have ht0 : t ≤ 0 := by simpa only [hF.carrier_eq, mem_Iic] using ht
  rcases lt_or_eq_of_le ht0 with htneg | rfl
  · exact ⟨t, htneg, x, hscalar⟩
  · have hcont : ContinuousWithinAt (fun s : ℝ => F.S.scalar s x) (Iic 0) 0 := by
      have h := F.isSolution.scalarCont (0, x) (show (0, x) ∈
          D.carrier ×ˢ (univ : Set F.M) from ⟨ht, mem_univ _⟩)
      have hpair : ContinuousWithinAt (fun s : ℝ => (s, x)) (Iic 0) 0 :=
        continuousWithinAt_id.prodMk continuousWithinAt_const
      exact h.comp (f := fun s : ℝ => (s, x)) (x := 0) hpair
        (fun s hs => ⟨by simpa only [hF.carrier_eq] using hs, mem_univ _⟩)
    have hleft : ContinuousWithinAt (fun s : ℝ => F.S.scalar s x) (Iio 0) 0 :=
      hcont.mono Iio_subset_Iic_self
    have hpos : ∀ᶠ s in 𝓝[<] (0 : ℝ), 0 < F.S.scalar s x :=
      hleft.eventually (isOpen_Ioi.mem_nhds hscalar)
    obtain ⟨b, hb, hbx⟩ := (hpos.and self_mem_nhdsWithin).exists
    exact ⟨b, hbx, x, hb⟩

theorem exists_neg_time_rmNormSq_ne_zero_of_ancient
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) :
    ∃ b : ℝ, b < 0 ∧ ∃ x : F.M,
      normSq0S (I := I) (F.S.base.metric b) x 4 (F.S.base.rm04 b x) ≠ 0 := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨b, hb, x, hx⟩ := exists_neg_time_scalar_pos_of_ancient F hF
  refine ⟨b, hb, x, ?_⟩
  intro hzero
  have hbound := scalar_abs_le_rm (I := I) (M := F.M) (F.S.base.metric b) x
  have hz : normSq0S (I := I) (F.S.base.metric b) x 4
      (metricRm04At (I := I) (M := F.M) (F.S.base.metric b) x) = 0 := hzero
  rw [hz, Real.sqrt_zero, mul_zero] at hbound
  have habs : |F.S.scalar b x| = 0 := le_antisymm hbound (abs_nonneg _)
  exact (ne_of_gt hx) (abs_eq_zero.mp habs)

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
