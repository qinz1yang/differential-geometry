import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.HalfLine
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.TimeLipschitz


noncomputable section

open Set Filter
open scoped Manifold ContDiff

namespace DifferentialGeometry.CheegerGromovCompactness

open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Geometry.Curvature

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : PointedFlowSeq.{u, uE, uH} (I := I)}
  {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {subseq : ℕ → ℕ}

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem HalfLineMetricConvergenceData.isSolutionOn
    (Phi : PointedCGHMaps X P subseq) {R : SmoothRiemannianMetric I P.M}
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (hcarrier : X.D.carrier = Iic 0) (hregular : Iio 0 ⊆ X.D.regular) :
    IsSolutionOn ({ base := { metric := co.gInf } } : SolutionOn (I := I) (M := P.M) X.D) := by
  apply HalfLineMetricConvergenceData.isSolutionOn_of_time_lipschitz
    Phi co hcarrier hregular
  intro n K hK p
  apply Eventually.of_forall
  intro k
  have hn : -(↑(n + 1) : ℝ) < 0 := neg_neg_of_pos (by positivity)
  have hslab : Icc (-(↑(n + 1) : ℝ)) 0 ⊆ X.D.carrier := by
    rw [hcarrier]
    exact Icc_subset_Iic_self
  have hreg : Ico (-(↑(n + 1) : ℝ)) 0 ⊆ X.D.regular :=
    Ico_subset_Iio_self.trans hregular
  obtain ⟨L, _, hL⟩ := exists_metric_extension_time_lipschitz_constant_on_closed_interval
    Phi R bf hsrc htgt hn hslab hreg k K hK p
  refine ⟨L, ?_⟩
  intro s hs t ht q hq x hx
  exact hL s ⟨by push_cast; linarith [hs.1], hs.2⟩
    t ⟨by push_cast; linarith [ht.1], ht.2⟩ q hq x hx

end DifferentialGeometry.CheegerGromovCompactness
