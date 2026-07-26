import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Metric.LocalFrameInverse

/-!
# Restricting a Ricci-flow solution to a smaller time interval

This module reindexes a metric-only `SolutionOn` by a smaller real-time
interval and transports `IsSolutionOn` when the new carrier and regular set are
contained in the old ones.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Set
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

namespace SolutionOn

/-- Reindex a solution candidate by another time interval without changing its
underlying all-real metric family. -/
def timeRestrict
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (D' : DifferentialGeometry.Integral.Connection.RealTimeInterval) :
    SolutionOn (I := I) (M := M) D' where
  base := S.base

omit [FiniteDimensional Real E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem timeRestrict_base
    {D D' : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) :
    (S.timeRestrict D').base = S.base := by
  rfl

@[simp] theorem timeRestrict_metric
    {D D' : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    (S.timeRestrict D').family.metric t = S.family.metric t := by
  rfl

end SolutionOn

/-- Restrict a Ricci-flow solution to a time interval whose carrier and regular
set are contained in those of the original interval. -/
theorem isSoln_timeRestrict
    {D D' : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D}
    (hS : IsSolutionOn (I := I) S)
    (hcar : D'.carrier ⊆ D.carrier)
    (hreg : D'.regular ⊆ D.regular) :
    IsSolutionOn (I := I) (S.timeRestrict D') where
  smoothMetric := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x X Y
      simpa [SolutionOn.timeRestrict, SolutionOn.family] using
        (hS.smoothMetric.coeff x X Y).mono hreg
    · intro x X Y
      simpa [SolutionOn.timeRestrict, SolutionOn.family] using
        (hS.smoothMetric.coeff_cont x X Y).mono hcar
    · simpa [SolutionOn.timeRestrict, SolutionOn.family] using
        DifferentialGeometry.Integral.Connection.Tensor0SFamilyContinuousOnSet.mono
          (I := I) (M := M) hS.smoothMetric.metricTensor_cont hcar
    · intro Idx _ frame u hframe i j
      simpa [SolutionOn.timeRestrict, SolutionOn.family] using
        (hS.smoothMetric.frameCompSmooth frame hframe i j).mono
          (Set.prod_mono hreg Set.Subset.rfl)
  smoothConnection := by
    intro t
    let t' : DifferentialGeometry.Integral.Connection.RealTimeInterval.FlowTime D :=
      ⟨(t : Real), hcar t.2⟩
    simpa [t', SolutionOn.timeRestrict, SolutionOn.family,
      DifferentialGeometry.Integral.Connection.RealizedMetricFamilyOn.connectionAt] using
      hS.smoothConnection t'
  equation := by
    intro t x X Y
    let t' : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D :=
      ⟨(t : Real), hreg t.2⟩
    simpa [t', MetricVariationEquationOn, SolutionOn.timeRestrict, SolutionOn.family,
      SolutionOn.ricciAt, RicciAtFamily.toTensorField] using
      (hS.equation t' x X Y).mono hcar
  scalarCont := by
    simpa [SolutionOn.timeRestrict, SolutionOn.scalar] using
      hS.scalarCont.mono (Set.prod_mono hcar Set.Subset.rfl)
  scalarTime := by
    intro K t ht hK x
    simpa [SolutionOn.timeRestrict, SolutionOn.scalar] using
      hS.scalarTime ht (fun s hs => hcar (hK hs)) x
  ricciCont := by
    simpa [SolutionOn.timeRestrict, SolutionOn.ricci] using
      DifferentialGeometry.Integral.Connection.Tensor0SFamilyContinuousOnSet.mono
        (I := I) (M := M) hS.ricciCont hcar
  rm04Cont := by
    simpa [SolutionOn.timeRestrict] using
      DifferentialGeometry.Integral.Connection.Tensor0SFamilyContinuousOnSet.mono
        (I := I) (M := M) hS.rm04Cont hcar
  ricciNormSpace := by
    intro t ht x
    simpa [ricciNorm, SolutionOn.timeRestrict, SolutionOn.family, SolutionOn.ricci] using
      hS.ricciNormSpace t (hcar ht) x
  ricciNormGrad := by
    intro t ht x
    simpa [ricciNorm, SolutionOn.timeRestrict, SolutionOn.family, SolutionOn.ricci] using
      hS.ricciNormGrad t (hcar ht) x

/-- Restrict a half-open solution to a later half-open tail.  The new carrier
lies entirely in the original regular set. -/
theorem isSoln_tailRestrict
    {alpha t₀ omega : Real} {hαω : alpha < omega}
    {S : SolutionOn (I := I) (M := M)
      (DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen alpha omega hαω)}
    (hS : IsSolutionOn (I := I) S)
    (hαt₀ : alpha < t₀) (ht₀ω : t₀ < omega) :
    IsSolutionOn (I := I)
      (S.timeRestrict
        (DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen t₀ omega ht₀ω)) := by
  apply isSoln_timeRestrict (I := I) hS
  · intro t ht
    exact ⟨le_of_lt (lt_of_lt_of_le hαt₀ ht.1), ht.2⟩
  · intro t ht
    exact ⟨lt_trans hαt₀ ht.1, ht.2⟩

/-- On a later half-open tail, every local frame has carrier-level metric time
regularity.  The new closed-left carrier lies in the original open regular set,
so the canonical local-frame inverse and its time derivative require no
endpoint regularity black box. -/
theorem tailFrameTimeReg
    [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {n : WithTop ℕ∞} {u : Set M}
    {alpha t₀ omega : Real} {hαω : alpha < omega}
    {S : SolutionOn (I := I) (M := M)
      (DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen alpha omega hαω)}
    (hS : IsSolutionOn (I := I) S)
    (hαt₀ : alpha < t₀) (ht₀ω : t₀ < omega)
    (frame : Idx → (x : M) → TangentSpace I x)
    (hframe : IsLocalFrameOn I E n frame u) :
    MetricFrameTimeRegularityInFrameOnLocal
      (I := I)
      (S.timeRestrict
        (DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen t₀ omega ht₀ω))
      (localFrameInv (I := I)
        (S.timeRestrict
          (DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen t₀ omega ht₀ω))
        frame hframe)
      (localFrameInvDt (I := I)
        (S.timeRestrict
          (DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen t₀ omega ht₀ω))
        frame hframe)
      frame u := by
  apply localFrameTimeReg (I := I)
  · intro x _hx i j
    have hsmooth := hS.smoothMetric.coeff x (frame i x) (frame j x)
    have hsub :
        (DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen t₀ omega ht₀ω).carrier ⊆
          (DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen alpha omega hαω).regular := by
      intro t ht
      exact ⟨lt_of_lt_of_le hαt₀ ht.1, ht.2⟩
    simpa [metricCompInFrame, SolutionOn.timeRestrict, SolutionOn.family] using
      hsmooth.mono hsub
  · intro t
    exact (uniqueDiffOn_Ico t₀ omega).uniqueDiffWithinAt
      ((DifferentialGeometry.Integral.Connection.RealTimeInterval.closedOpen t₀ omega ht₀ω).regular_subset t.2)

end DifferentialGeometry.PDE.RicciFlow
