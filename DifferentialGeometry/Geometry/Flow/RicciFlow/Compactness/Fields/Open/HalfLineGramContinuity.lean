import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Open.HalfLineExistence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.Regularity

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Bundle Filter Set
open DifferentialGeometry.Tensor.Coordinates
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : PointedFlowSeq (I := I)} {P : PointedRiemannianManifold (I := I)}
  {phi : ℕ → ℕ}

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact

namespace HalfLineMetricConvergenceData

theorem continuousOn_chartGramMatrix
    (Phi : PointedCGHMaps X P phi) {R : SmoothRiemannianMetric I P.M}
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (hcarrier : Iic (0 : ℝ) ⊆ X.D.carrier)
    (alpha : P.M) (i j : Fin (Module.finrank ℝ E)) :
    ContinuousOn (fun z : ℝ × P.M => chartGramMatrix (co.gInf z.1) alpha z.2 i j)
      (Iic (0 : ℝ) ×ˢ (chartAt H alpha).source) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : LocallyCompactSpace H := I.locallyCompactSpace
  let _ : LocallyCompactSpace P.M := ChartedSpace.locallyCompactSpace H P.M
  apply continuousOn_of_locally_continuousOn
  intro z hz
  obtain ⟨n, hn⟩ := exists_nat_gt (-z.1)
  have hlow : -(n : ℝ) < z.1 := by linarith
  have htime : z.1 < 1 := lt_of_le_of_lt hz.1 zero_lt_one
  refine ⟨Ioo (-(n : ℝ)) 1 ×ˢ (univ : Set P.M),
    isOpen_Ioo.prod isOpen_univ, ⟨⟨hlow, htime⟩, mem_univ _⟩, ?_⟩
  have hwin : Icc (-(n : ℝ)) 0 ⊆ X.D.carrier := fun _ ht => hcarrier ht.2
  have hgram : ContinuousOn
      (fun q : ℝ × P.M => chartGramMatrix (co.gInf q.1) alpha q.2 i j)
      (Icc (-(n : ℝ)) 0 ×ˢ (trivializationAt E (TangentSpace I) alpha).baseSet) := by
    refine chartGramLim_contOn (I := I)
      (fun k t => gSeqExt Phi R bf hsrc htgt (co.φ k) t) co.gInf R (-(n : ℝ)) 0
      ?_ alpha i j ?_
    · intro K hK ε hε
      obtain ⟨k₀, hk₀⟩ := (co.convergenceOn n).convergencePt K hK 0 ε hε
      exact ⟨k₀, fun k hk t ht y hy => hk₀ k hk t ht 0 le_rfl y hy⟩
    · intro k
      exact (gSeqExt_gram_cont Phi R bf hsrc htgt (co.φ k) alpha i j).mono
        (prod_mono hwin Subset.rfl)
  exact hgram.mono (by
    intro q hq
    exact ⟨⟨hq.2.1.1.le, hq.1.1⟩, hq.1.2⟩)

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness
