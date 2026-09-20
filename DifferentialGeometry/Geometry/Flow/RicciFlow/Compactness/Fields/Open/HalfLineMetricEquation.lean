import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.Regularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Open.HalfLineExistence


noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Bundle Filter Set
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : PointedFlowSeq (I := I)} {P : PointedRiemannianManifold (I := I)}
  {subseq : ℕ → ℕ}
  (Φ : PointedCGHMaps X P subseq)

theorem FlowMetricConvergenceData.metric_hasDerivAt
    {R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M}
    {bf : BumpFamily Φ} {hsrc : SourceIsSigmaCompact Φ} {htgt : TargetIsSigmaCompact Φ}
    {a b : ℝ} (hwin : Icc a b ⊆ X.D.regular)
    (co : FlowMetricConvergenceData Φ R bf hsrc htgt a b)
    {t : ℝ} (ht : t ∈ Ioo a b) (x : P.M) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    ∀ v w : TangentSpace I x,
      HasDerivAt (fun s : ℝ => (co.gInf s).inner x v w)
        (-2 * ricciTensor (I := I) (co.gInf t) x v w) t := by
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : T2Space P.M := P.t2
  let : IsManifold I ∞ P.M := P.smooth
  let : SigmaCompactSpace P.M := P.sigmaCompact
  let : IsManifold I 1 P.M :=
    IsManifold.of_le (I := I) (M := P.M) (n := (∞ : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  let : IsManifold I 2 P.M :=
    IsManifold.of_le (I := I) (M := P.M) (n := (∞ : WithTop ℕ∞))
      (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  let : IsManifold I ((∞ : WithTop ℕ∞) + 1) P.M := by
    change IsManifold I ∞ P.M
    infer_instance
  classical
  intro v w
  have hxgood : x ∈ chartLeviCivitaGoodSet (I := I) x :=
    self_mem_chartLeviCivitaGoodSet (I := I) (α := x)
  have hy : extChartAt I x x ∈ interior (extChartAt I x).target :=
    chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hxgood
  have hbasis (i j : Fin (Module.finrank Real E)) :
      HasDerivAt
        (fun s => chartGramOnE (I := I) (co.gInf s) x i j (extChartAt I x x))
        (-2 * chartRicciTensor (I := I) (co.gInf t) x i j (extChartAt I x x)) t := by
    have hpde := (FlowMetricConvergenceData.gramPDE (I := I) (Φ := Φ)
      hwin co x i j (Set.Ioo_subset_Icc_self ht) hy).hasDerivAt
        (Icc_mem_nhds_iff.mpr ht)
    let gt : SmoothRiemannianMetric I P.M := co.gInf t
    have hStatic : ContDiffOn Real ∞ (chartGramPi (I := I) gt x)
        (interior (extChartAt I x).target) := by
      refine contDiffOn_pi.mpr fun a => contDiffOn_pi.mpr fun b => ?_
      exact (chartGramOnE_contDiffOn (I := I) gt x a b).mono interior_subset
    have hAt : ContDiffAt Real ∞ (chartGramPi (I := I) gt x) (extChartAt I x x) :=
      hStatic.contDiffAt (isOpen_interior.mem_nhds hy)
    have hG : DifferentiableAt Real (chartGramPi (I := I) gt x) (extChartAt I x x) :=
      hAt.differentiableAt (by simp)
    have hG1 : ∀ᶠ z in nhds (extChartAt I x x),
        DifferentiableAt Real (chartGramPi (I := I) gt x) z := by
      filter_upwards [isOpen_interior.mem_nhds hy] with z hz
      exact (hStatic.contDiffAt (isOpen_interior.mem_nhds hz)).differentiableAt
        (by simp)
    have hG2 : DifferentiableAt Real
        (fun z => fderiv Real (chartGramPi (I := I) gt x) z) (extChartAt I x x) :=
      (hAt.fderiv_right (m := ∞) le_rfl).differentiableAt (by simp)
    have hjet := jetRicciFlow_chartGram (I := I) gt x hy hG hG1 hG2 i j
    simpa only [gt] using hpde.congr_deriv hjet
  exact metricPDE_of_gram (I := I) co.gInf x hbasis v w

theorem HalfLineMetricConvergenceData.metric_hasDerivAt
    {R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M}
    {bf : BumpFamily Φ} {hsrc : SourceIsSigmaCompact Φ} {htgt : TargetIsSigmaCompact Φ}
    (co : HalfLineMetricConvergenceData Φ R bf hsrc htgt)
    (hreg : Iio 0 ⊆ X.D.regular) {t : ℝ} (ht : t < 0) (x : P.M) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    ∀ v w : TangentSpace I x,
      HasDerivAt (fun s : ℝ => (co.gInf s).inner x v w)
        (-2 * ricciTensor (I := I) (co.gInf t) x v w) t := by
  obtain ⟨n, hn⟩ := exists_nat_gt (-t)
  have hleft : -(n : ℝ) < t := by linarith
  have hmid : t < t / 2 := by linarith
  have hhalf : t / 2 < 0 := by linarith
  have hwin : Icc (-(n : ℝ)) (t / 2) ⊆ X.D.regular :=
    fun s hs => hreg (lt_of_le_of_lt hs.2 hhalf)
  have hsub : Icc (-(n : ℝ)) (t / 2) ⊆ Icc (-(n : ℝ)) 0 :=
    fun s hs => ⟨hs.1, (hs.2.trans_lt hhalf).le⟩
  exact FlowMetricConvergenceData.metric_hasDerivAt Φ hwin
    (FlowMetricConvergenceData.restrict (Φ := Φ)
      (HalfLineMetricConvergenceData.atWindow Φ co n) hsub) ⟨hleft, hmid⟩ x

end DifferentialGeometry.CheegerGromovCompactness
