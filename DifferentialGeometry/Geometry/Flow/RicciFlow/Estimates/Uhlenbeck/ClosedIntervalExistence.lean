import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Uhlenbeck.FrameExistence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Restriction
import DifferentialGeometry.Analysis.Calculus.TimeJet.SliceSwap

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Set
open DifferentialGeometry.Geometry.Curvature
open scoped BigOperators Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M]
  {Idx : Type*} [Fintype Idx] [DecidableEq Idx] [Nonempty Idx]

theorem exists_uhlenbeckFrame_on_Icc
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b : ℝ} (hab : a < b) (hslab : Icc a b ⊆ D.carrier)
    (hreg : Ioo a b ⊆ D.regular)
    (basisAt : ∀ x : M, Module.Basis Idx ℝ (TangentSpace I x)) :
    ∃ ι : MatrixComp M Idx,
      (∀ x i k, ι a x i k = if i = k then 1 else 0) ∧
      (∀ x, ContinuousOn (fun t => ι t x) (Icc a b)) ∧
      (∀ t ∈ Icc a b, ∀ x i k, HasDerivWithinAt (fun s => ι s x i k)
        (∑ l : Idx, uhlenbeckRupOfSolution S (solutionInverseMetricComponents S basisAt)
          (fun j y => basisAt y j) t x l k * ι t x i l) (Icc a b) t) ∧
      ∀ t ∈ Icc a b, ∀ x i j,
        movingFrameGramInFrame (metricCompInFrame S (fun k y => basisAt y k)) ι t x i j =
          (S.family.metric a).inner x (basisAt x i) (basisAt x j) := by
  let T := b - a
  have hT : 0 < T := sub_pos.mpr hab
  let S₀ := (S.timeShift a).timeRestrict (RealTimeInterval.closed 0 T hT.le)
  have hS₀ : IsSolutionOn S₀ := by
    apply isSolutionOn_timeRestrict (isSolutionOn_timeShift hS a)
    · intro s hs
      change s + a ∈ D.carrier
      apply hslab
      change 0 ≤ s ∧ s ≤ T at hs
      constructor <;> dsimp only [T] at hs <;> linarith [hs.1, hs.2]
    · intro s hs
      change s + a ∈ D.regular
      apply hreg
      change 0 < s ∧ s < T at hs
      constructor <;> dsimp only [T] at hs <;> linarith [hs.1, hs.2]
  let ι₀ := solutionUhlenbeckIota hT S₀ hS₀ basisAt
  have hs := solutionUhlenbeckIota_spec hT S₀ hS₀ basisAt
  have hcont : ∀ x i k, ContinuousOn (fun t => ι₀ t x i k) (Icc 0 T) := by
    intro x i k t ht
    exact continuousWithinAt_pi.mp (continuousWithinAt_pi.mp (hs.2.1 x t ht) i) k
  have hrup : ∀ x i k, ContinuousOn
      (fun t => uhlenbeckRupOfSolution S₀ (solutionInverseMetricComponents S₀ basisAt)
        (fun j y => basisAt y j) t x i k) (Icc 0 T) := by
    intro x i k
    exact uhlenbeckRup_entry_continuousOn hT S₀ (solutionInverseMetricComponents S₀ basisAt)
      (fun x i j => solutionInverseMetricComponents_entry_continuousOn hT S₀ hS₀ basisAt x i j)
      (fun x v w => ricciAt_continuousOn_time hT S₀ hS₀ x v w)
      (fun j y => basisAt y j) i k
  have hder : ∀ t ∈ Icc 0 T, ∀ x i k, HasDerivWithinAt (fun s => ι₀ s x i k)
      (∑ l : Idx, uhlenbeckRupOfSolution S₀ (solutionInverseMetricComponents S₀ basisAt)
        (fun j y => basisAt y j) t x l k * ι₀ t x i l) (Icc 0 T) t := by
    intro t ht x i k
    apply DifferentialGeometry.Analysis.hasDerivIcc_of_int
      (f' := fun q => ∑ l : Idx,
        uhlenbeckRupOfSolution S₀ (solutionInverseMetricComponents S₀ basisAt)
          (fun j y => basisAt y j) q x l k * ι₀ q x i l) (t := t) hT (hcont x i k)
    · exact continuousOn_finsetSum Finset.univ fun l _ => (hrup x l k).mul (hcont x i l)
    · intro s hs'
      exact (hs.2.2.1 s ⟨hs'.1.le, hs'.2⟩ x i k).hasDerivAt
        (Ici_mem_nhds hs'.1)
    · exact ht
  let ι : MatrixComp M Idx := fun t => ι₀ (t - a)
  have hmap : MapsTo (fun t : ℝ => t - a) (Icc a b) (Icc 0 T) := by
    intro t ht
    exact ⟨sub_nonneg.mpr ht.1, sub_le_sub_right ht.2 a⟩
  refine ⟨ι, ?_, ?_, ?_, ?_⟩
  · intro x i k
    simpa only [ι, sub_self, ι₀] using hs.1 x i k
  · intro x
    exact (hs.2.1 x).comp (continuous_id.sub continuous_const).continuousOn hmap
  · intro t ht x i k
    have hd := (hder (t - a) (hmap ht) x i k).scomp t
      (((hasDerivAt_id t).sub_const a).hasDerivWithinAt) hmap
    have hR : ∀ l k,
        uhlenbeckRupOfSolution S₀ (solutionInverseMetricComponents S₀ basisAt)
          (fun j y => basisAt y j) (t - a) x l k =
        uhlenbeckRupOfSolution S (solutionInverseMetricComponents S basisAt)
          (fun j y => basisAt y j) t x l k := by
      intro l k
      change uhlenbeckRupOfSolution S (solutionInverseMetricComponents S basisAt)
        (fun j y => basisAt y j) (t - a + a) x l k = _
      rw [sub_add_cancel]
    simpa only [ι, Function.comp_def, id_eq, one_smul, hR] using hd
  · intro t ht x i j
    have hg := hs.2.2.2.2 (t - a) (hmap ht) x i j
    have hz : ∀ i k, ι₀ 0 x i k = if i = k then 1 else 0 := hs.1 x
    change (∑ k : Idx, ∑ l : Idx,
      ι₀ (t - a) x i k * ι₀ (t - a) x j l *
        (S.family.metric (t - a + a)).inner x (basisAt x k) (basisAt x l)) =
      ∑ k : Idx, ∑ l : Idx,
        ι₀ 0 x i k * ι₀ 0 x j l *
          (S.family.metric (0 + a)).inner x (basisAt x k) (basisAt x l) at hg
    simpa [movingFrameGramInFrame, ι, metricCompInFrame, hz] using hg

end DifferentialGeometry.PDE.RicciFlow
