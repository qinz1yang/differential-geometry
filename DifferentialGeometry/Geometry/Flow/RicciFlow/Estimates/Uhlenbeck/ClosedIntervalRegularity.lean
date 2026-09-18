import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Uhlenbeck.ClosedIntervalExistence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Ricci.Regularity.ClosedInterval

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Set
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [NeZero (Module.finrank ℝ E)]
  {Idx : Type*} [Fintype Idx] [DecidableEq Idx]

theorem uhlenbeckEndomorphism_contMDiffOn_closed
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a c b : ℝ} (hac : a < c) (hcb : c < b)
    (hslab : Icc a b ⊆ D.carrier) (hregular : Ioo a b ⊆ D.regular)
    (basisAt : ∀ x : M, Module.Basis Idx ℝ (TangentSpace I x))
    (ι : MatrixComp M Idx)
    (hι₀ : ∀ x i k, ι c x i k = if i = k then 1 else 0)
    (hframe : ∀ t ∈ Icc c b, ∀ x i k, HasDerivWithinAt (fun s => ι s x i k)
      (∑ l : Idx, uhlenbeckRupOfSolution S (solutionInverseMetricComponents S basisAt)
        (fun j y => basisAt y j) t x l k * ι t x i l) (Icc c b) t) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun p : ℝ × M => (⟨p.2, uhlenbeckEndomorphismAt (basisAt p.2) ι p.1⟩ :
        TotalSpace (E →L[ℝ] E)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x)))
      (Icc c b ×ˢ (univ : Set M)) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact uhlenbeckEndomorphism_contMDiffOn S (solutionInverseMetricComponents S basisAt)
    basisAt ι (solutionInverseMetricComponents_mul_metric S basisAt)
    (solutionInverseMetricComponents_symm S basisAt) ordConnected_Icc ⟨le_rfl, hcb.le⟩
    (ricciSharp_family_contMDiffOn_closed S hS hac hcb hslab hregular) hι₀ hframe

theorem exists_uhlenbeckFrame_contMDiffOn_closed [Nonempty Idx]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a c b : ℝ} (hac : a < c) (hcb : c < b)
    (hslab : Icc a b ⊆ D.carrier) (hregular : Ioo a b ⊆ D.regular)
    (basisAt : ∀ x : M, Module.Basis Idx ℝ (TangentSpace I x)) :
    ∃ ι : MatrixComp M Idx,
      (∀ x i k, ι c x i k = if i = k then 1 else 0) ∧
      (∀ x, ContinuousOn (fun t => ι t x) (Icc c b)) ∧
      (∀ t ∈ Icc c b, ∀ x i k, HasDerivWithinAt (fun s => ι s x i k)
        (∑ l : Idx, uhlenbeckRupOfSolution S (solutionInverseMetricComponents S basisAt)
          (fun j y => basisAt y j) t x l k * ι t x i l) (Icc c b) t) ∧
      (∀ t ∈ Icc c b, ∀ x i j,
        movingFrameGramInFrame (metricCompInFrame S (fun k y => basisAt y k)) ι t x i j =
          (S.family.metric c).inner x (basisAt x i) (basisAt x j)) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
        (fun p : ℝ × M => (⟨p.2, uhlenbeckEndomorphismAt (basisAt p.2) ι p.1⟩ :
          TotalSpace (E →L[ℝ] E)
            (fun x => TangentSpace I x →L[ℝ] TangentSpace I x)))
        (Icc c b ×ˢ (univ : Set M)) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨ι, hι₀, hcont, hframe, hgram⟩ := exists_uhlenbeckFrame_on_Icc S hS hcb
    (fun t ht => hslab ⟨hac.le.trans ht.1, ht.2⟩)
    (fun t ht => hregular ⟨hac.trans ht.1, ht.2⟩) basisAt
  exact ⟨ι, hι₀, hcont, hframe, hgram,
    uhlenbeckEndomorphism_contMDiffOn_closed S hS hac hcb hslab hregular basisAt ι hι₀ hframe⟩

end DifferentialGeometry.PDE.RicciFlow
