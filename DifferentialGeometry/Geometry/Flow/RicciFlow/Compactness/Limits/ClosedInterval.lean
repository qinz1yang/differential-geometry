import DifferentialGeometry.Tensor.RSTensor.Functoriality.Pullback
import DifferentialGeometry.Geometry.Metric.Convergence.Time.ChartJets
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.Regularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.FlowOfMetric
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extension.Regularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.Restriction

section

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Set Filter
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : PointedFlowSeq (I := I)} {P : PointedRiemannianManifold (I := I)}
  {subseq : ℕ → ℕ} {Φ : PointedCGHMaps (I := I) X P subseq}

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

theorem FlowMetricConvergenceData.isSolutionOn_closed
    {R : SmoothRiemannianMetric I P.M}
    {bf : BumpFamily Φ} {hsrc : SourceIsSigmaCompact Φ} {htgt : TargetIsSigmaCompact Φ}
    {a b : ℝ} (hab : a < b)
    (hcarrier : X.D.carrier = Icc a b) (hregular : Ioo a b ⊆ X.D.regular)
    (co : FlowMetricConvergenceData Φ R bf hsrc htgt a b)
    (htime : ∀ K : Set P.M, IsCompact K → ∀ p : ℕ, ∀ᶠ k in atTop,
      ∃ L : ℝ, ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, ∀ q ≤ p, ∀ x ∈ K,
        metricDerivNorm q (gSeqExt Φ R bf hsrc htgt k s)
          (gSeqExt Φ R bf hsrc htgt k t) R x ≤ L * |s - t|) :
    IsSolutionOn ({ base := { metric := co.gInf } } : SolutionOn (I := I) (M := P.M) X.D) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let : IsManifold I 1 P.M := IsManifold.of_le (n := ∞) (by decide)
  let : IsManifold I 2 P.M := IsManifold.of_le (n := ∞) (by decide)
  have hcar : X.D.carrier ⊆ Icc a b := hcarrier.subset
  have hjets := co.gramJets_of_stage (Φ := Φ) (by
    intro r p i j C hC hCt
    have hK : IsCompact ((extChartAt I p).symm '' C) :=
      hC.image_of_continuousOn ((continuousOn_extChartAt_symm (I := I) p).mono hCt)
    filter_upwards [co.strictMono.tendsto_atTop.eventually (htime _ hK r)] with k hk
    obtain ⟨L, hL⟩ := hk
    exact chartGram_jets_continuousOn_of_metric_time_lipschitz
      (gSeqExt Φ R bf hsrc htgt (co.φ k)) R (Icc a b) p r hC hCt hL i j)
  have hgram := co.gramSmoothIcc (Φ := Φ) hab hcar hregular hjets
  apply isSolutionOn_of_regularity co.gInf (FlowMetricConvergenceData.metricSmooth (Φ := Φ) hcarrier co)
    (fun t ht x v w => FlowMetricConvergenceData.metricPDE_regular (Φ := Φ) hcar co ht x v w)
  · simpa only [hcarrier] using scalarCont_of_joint co.gInf (Icc a b)
      (uniqueDiffOn_Icc hab) hgram
  · intro t ht x
    rw [hcarrier] at ht ⊢
    exact scalarTime_of_joint co.gInf (Icc a b) (uniqueDiffOn_Icc hab) hgram t ht x
  · simpa only [hcarrier] using ricciCont_of_joint co.gInf (Icc a b)
      (uniqueDiffOn_Icc hab) hgram
  · simpa only [hcarrier] using rm04Cont_of_joint co.gInf (Icc a b)
      (uniqueDiffOn_Icc hab) hgram

end DifferentialGeometry.CheegerGromovCompactness

end

end

section

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Set Filter
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.PDE.RicciFlow
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : PointedFlowSeq (I := I)} {P : PointedRiemannianManifold (I := I)}
  {subseq : ℕ → ℕ} {Φ : PointedCGHMaps (I := I) X P subseq}

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

theorem FlowMetricConvergenceData.isSolutionOn_closed_interval
    {R : SmoothRiemannianMetric I P.M}
    {bf : BumpFamily Φ} {hsrc : SourceIsSigmaCompact Φ} {htgt : TargetIsSigmaCompact Φ}
    {a b : ℝ} (hab : a < b)
    (hcarrier : Icc a b ⊆ X.D.carrier) (hregular : Ioo a b ⊆ X.D.regular)
    (co : FlowMetricConvergenceData Φ R bf hsrc htgt a b)
    (htime : ∀ K : Set P.M, IsCompact K → ∀ p : ℕ, ∀ᶠ k in atTop,
      ∃ L : ℝ, ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, ∀ q ≤ p, ∀ x ∈ K,
        metricDerivNorm q (gSeqExt Φ R bf hsrc htgt k s)
          (gSeqExt Φ R bf hsrc htgt k t) R x ≤ L * |s - t|) :
    IsSolutionOn ({ base := { metric := co.gInf } } : SolutionOn (I := I) (M := P.M)
      (RealTimeInterval.closed a b hab.le)) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let D := RealTimeInterval.closed a b hab.le
  let Y : PointedFlowSeq (I := I) := {
    D := D
    term := fun i => (X.term i).timeRestrict D hcarrier hregular }
  let Ψ : PointedCGHMaps (I := I) Y P subseq := {
    partialDiffeomorph := Φ.partialDiffeomorph
    source_exhausts := Φ.source_exhausts
    base_mem := Φ.base_mem
    basepoint_map := Φ.basepoint_map }
  let cut : BumpFamily Ψ := {
    grow := bf.grow
    grow_compact := bf.grow_compact
    grow_subset := bf.grow_subset
    grow_cover := bf.grow_cover
    chi := bf.chi
    chi_smooth := bf.chi_smooth
    chi01 := bf.chi01
    chi_support := bf.chi_support
    chi_one := bf.chi_one }
  have hsrc' : SourceIsSigmaCompact Ψ := hsrc
  have htgt' : TargetIsSigmaCompact Ψ := htgt
  have hG : gSeqExt Ψ R cut hsrc' htgt' = gSeqExt Φ R bf hsrc htgt := rfl
  let co' : FlowMetricConvergenceData Ψ R cut hsrc' htgt' a b := {
    φ := co.φ
    strictMono := co.strictMono
    gInf := co.gInf
    convergence := by simpa only [hG] using co.convergence
    convergencePt := by simpa only [hG] using co.convergencePt }
  exact co'.isSolutionOn_closed hab rfl Subset.rfl (by simpa only [hG] using htime)

end DifferentialGeometry.CheegerGromovCompactness

end

end
