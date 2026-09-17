import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.ClosedInterval
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Open.HalfLineExistence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Locality
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Open.HalfLineConvergence
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Norm.ReferenceChange
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.PointedPullbackExtensions
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Compactness.MetricExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Foundations.MetricSlices

section

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Filter Set
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type uH} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : PointedFlowSeq.{u, uE, uH} (I := I)}
  {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {subseq : ℕ → ℕ}

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem HalfLineMetricConvergenceData.isSolutionOn_of_time_lipschitz
    (Phi : PointedCGHMaps X P subseq) {R : SmoothRiemannianMetric I P.M}
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (hcarrier : X.D.carrier = Iic 0) (hregular : Iio 0 ⊆ X.D.regular)
    (htime : ∀ n : ℕ, ∀ K : Set P.M, IsCompact K → ∀ p : ℕ, ∀ᶠ k in atTop,
      ∃ L : ℝ, ∀ s ∈ Icc (-(n : ℝ)) 0, ∀ t ∈ Icc (-(n : ℝ)) 0,
        ∀ q ≤ p, ∀ x ∈ K,
          metricDerivNorm q (gSeqExt Phi R bf hsrc htgt k s)
            (gSeqExt Phi R bf hsrc htgt k t) R x ≤ L * |s - t|) :
    IsSolutionOn ({ base := { metric := co.gInf } } : SolutionOn (I := I) (M := P.M) X.D) := by
  let S : SolutionOn (I := I) (M := P.M) X.D := { base := { metric := co.gInf } }
  apply isSolutionOn_of_closed_backward_windows S hcarrier.subset
  intro n
  have hab : -((n + 1 : ℕ) : ℝ) < 0 := neg_neg_of_pos (by exact_mod_cast Nat.succ_pos n)
  have hcar : Icc (-((n + 1 : ℕ) : ℝ)) 0 ⊆ X.D.carrier := by
    rw [hcarrier]
    exact Icc_subset_Iic_self
  have hreg : Ioo (-((n + 1 : ℕ) : ℝ)) 0 ⊆ X.D.regular :=
    Ioo_subset_Iio_self.trans hregular
  have hsol := (HalfLineMetricConvergenceData.atWindow Phi co (n + 1)).isSolutionOn_closed_interval
    hab hcar hreg (htime (n + 1))
  have htransfer (a : ℝ) (ha : a ≤ 0) (heq : a = -((n + 1 : ℕ) : ℝ)) :
      IsSolutionOn ({ base := { metric := co.gInf } } : SolutionOn (I := I) (M := P.M)
        (RealTimeInterval.closed a 0 ha)) := by
    subst a
    exact hsol
  exact htransfer (0 - ((n + 1 : ℕ) : ℝ)) (sub_le_self _ (Nat.cast_nonneg _))
    (zero_sub _)

omit [I.Boundaryless] in
theorem HalfLineMetricConvergenceData.metricComplete_of_eventually_lower
    (Phi : PointedCGHMaps X P subseq) {R : SmoothRiemannianMetric I P.M}
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (hR : MetricComplete ({ P with metric := R } : PointedRiemannianManifold (I := I)))
    {t c : ℝ} (ht : t ≤ 0) (hc : 0 < c)
    (hlower : ∀ x : P.M, ∀ v : TangentSpace I x, ∀ᶠ k in atTop,
      c * R.inner x v v ≤ (gSeqExt Phi R bf hsrc htgt (co.φ k) t).inner x v v) :
    MetricComplete ({ P with metric := co.gInf t } : PointedRiemannianManifold (I := I)) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨n, hn⟩ := exists_nat_ge (-t)
  have htwin : t ∈ Icc (-(n : ℝ)) 0 := ⟨by linarith, ht⟩
  have hlow : ∀ x : P.M, ∀ v : TangentSpace I x,
      c * R.inner x v v ≤ (co.gInf t).inner x v v := by
    intro x v
    have hinner : Tendsto
        (fun k => (gSeqExt Phi R bf hsrc htgt (co.φ k) t).inner x v v)
        atTop (𝓝 ((co.gInf t).inner x v v)) := by
      apply metricInner_tendsto (fun k => gSeqExt Phi R bf hsrc htgt (co.φ k) t)
        (co.gInf t) R x
      intro epsilon hepsilon
      obtain ⟨N, hN⟩ := (co.convergenceOn n).convergencePt {x} isCompact_singleton 0
        epsilon hepsilon
      exact ⟨N, fun k hk => hN k hk t htwin 0 le_rfl x (mem_singleton x)⟩
    exact ge_of_tendsto hinner (hlower x v)
  exact MetricComplete.complete_of_lower ({ P with metric := R } : PointedRiemannianManifold (I := I))
    hR (co.gInf t) c hc hlow

end DifferentialGeometry.CheegerGromovCompactness

end

end

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Set
open scoped Manifold ContDiff _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type uH} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {X : PointedFlowSeq.{u, uE, uH} (I := I)}
  {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {subseq : ℕ → ℕ}

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact

theorem HalfLineMetricConvergenceData.canonical_metric_convergence
    (Phi : PointedCGHMaps X P subseq) {R : SmoothRiemannianMetric I P.M}
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    {t : ℝ} (ht : t ≤ 0) :
    MetricCInfConvergenceOnCompacts
      (fun k => gSeqExt Phi R bf hsrc htgt (co.φ k) t) (co.gInf t) (co.gInf t) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨n, hn⟩ := exists_nat_ge (-t)
  have htwin : t ∈ Icc (-(n : ℝ)) 0 := ⟨by linarith, ht⟩
  have hconv : MetricCInfConvergenceOnCompacts
      (fun k => gSeqExt Phi R bf hsrc htgt (co.φ k) t) (co.gInf t) R := by
    intro K hK p epsilon hepsilon
    obtain ⟨N, hN⟩ := (co.convergenceOn n).convergence K hK p epsilon hepsilon
    exact ⟨N, fun k hk => hN k hk t htwin⟩
  exact hconv.change_reference (co.gInf t)

end DifferentialGeometry.CheegerGromovCompactness

end

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Filter Set
open scoped Manifold ContDiff _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type uH} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedFlowData.topology PointedFlowData.charted PointedFlowData.smooth
  PointedFlowData.t2 PointedFlowData.sigmaCompact

theorem HalfLineMetricConvergenceData.exists_canonicalMetricConvergenceData
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {phi : ℕ → ℕ}
    (Phi : PointedCGHMaps X P phi) {R : SmoothRiemannianMetric I P.M}
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt) {t : ℝ} (ht : t ≤ 0) :
    let Psi := (Phi.compSubseq co.φ co.strictMono).atTimeWithMetric t (co.gInf t)
    ∃ C : MetricConvergenceData Psi,
      (∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData Psi k) ∧
      (∀ k,
        let D := C.domain k
        letI : TopologicalSpace (MetricSourceDomain Psi k) := D.topology
        letI : ChartedSpace H (MetricSourceDomain Psi k) := D.charted
        letI : IsManifold I ∞ (MetricSourceDomain Psi k) := D.smooth
        D.referenceMetric = D.limitMetric) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let Gseq : ℕ → SmoothRiemannianMetric I P.M :=
    fun k => gSeqExt (I := I) (X := X) (P := P) (subseq := phi)
      Phi R bf hsrc htgt (co.φ k) t
  have hconv : MetricCInfConvergenceOnCompacts (I := I) Gseq (co.gInf t) (co.gInf t) :=
    HalfLineMetricConvergenceData.canonical_metric_convergence
      (I := I) (X := X) (P := P) (subseq := phi) Phi co ht
  have hlocal : ∀ K : Set P.M, IsCompact K → ∀ᶠ k in atTop,
      ∃ U : Set P.M, IsOpen U ∧ K ⊆ U ∧ U ⊆ Phi.source (co.φ k) ∧
        ∀ x ∈ U, ∀ v w : TangentSpace I x,
          (Gseq k).inner x v w = ((X.term (phi (co.φ k))).S.base.metric t).inner
            (Phi.map (co.φ k) x) (mfderiv I I (Phi.map (co.φ k)) x v)
              (mfderiv I I (Phi.map (co.φ k)) x w) := by
    intro K hK
    have hG := co.strictMono.tendsto_atTop.eventually
      (DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.eventually_gSeqExt_eq_pullback
        Phi R bf hsrc htgt K hK)
    filter_upwards [hG] with k hk
    obtain ⟨U, hU, hKU, hUsrc, hGk⟩ := hk
    exact ⟨U, hU, hKU, hUsrc, hGk t⟩
  let Q : PointedRiemannianManifold.{u, uE, uH} (I := I) :=
    { P with metric := co.gInf t }
  let Psi : PointedRiemannianConvergenceMaps (I := I) (X.atTime t) Q (phi ∘ co.φ) :=
    (Phi.compSubseq co.φ co.strictMono).atTimeWithMetric t (co.gInf t)
  refine exists_canonicalMetricConvergenceData_of_metric_extension
    (I := I) (X := X.atTime t) (P := Q) (phi := phi ∘ co.φ) Psi Gseq ?_ ?_
  · change MetricCInfConvergenceOnCompacts Gseq (co.gInf t) (co.gInf t)
    exact hconv
  · exact hlocal


end DifferentialGeometry.CheegerGromovCompactness

end
