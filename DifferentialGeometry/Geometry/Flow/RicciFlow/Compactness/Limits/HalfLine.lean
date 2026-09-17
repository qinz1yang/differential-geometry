import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.ClosedInterval
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Open.HalfLineExistence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Locality

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
