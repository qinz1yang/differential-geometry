import DifferentialGeometry.Geometry.Metric.Convergence.Window.EventualBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Open.BumpFamilyChange
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Open.HalfLineConvergence

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Set Filter
open scoped Manifold ContDiff _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  {X : PointedFlowSeq.{u, uE, uH} (I := I)}
  {P : PointedRiemannianManifold.{u, uE, uH} (I := I)}
  {phi : ℕ → ℕ}

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact

theorem exists_bumpMetricConvergence_of_eventual_compact_bounds
    (Phi : PointedCGHMaps (I := I) X P phi)
    (R : SmoothRiemannianMetric I P.M)
    (bf : BumpFamily Phi) (hsrc : SourceIsSigmaCompact Phi)
    (htgt : TargetIsSigmaCompact Phi)
    {a b : ℝ} (hab : a ≤ b)
    (hind : ∀ i, ∀ K : Set P.M, IsCompact K → ∀ p : ℕ,
      ∃ L : ℝ, 0 ≤ L ∧ ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
        ∀ q ≤ p, ∀ x ∈ K,
          metricDerivNorm q (gSeqExt Phi R bf hsrc htgt i s)
            (gSeqExt Phi R bf hsrc htgt i t) R x ≤ L * |s - t|)
    (hlip : ∀ K : Set P.M, IsCompact K → ∀ p : ℕ,
      ∃ L : ℝ, 0 ≤ L ∧ ∀ᶠ i in atTop, ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
        ∀ q ≤ p, ∀ x ∈ K,
          metricDerivNorm q (gSeqExt Phi R bf hsrc htgt i s)
            (gSeqExt Phi R bf hsrc htgt i t) R x ≤ L * |s - t|)
    (hcov : ∀ t ∈ Icc a b, ∀ q : ℕ, ∀ K : Set P.M, IsCompact K →
      ∃ C : ℝ, ∀ᶠ i in atTop, ∀ x ∈ K,
        metricCovDerivNorm q (gSeqExt Phi R bf hsrc htgt i t) R x ≤ C)
    (hlower : ∀ t ∈ Icc a b, ∃ c : ℝ, 0 < c ∧
      ∀ i, ∀ x : P.M, ∀ v : TangentSpace I x,
        c * R.inner x v v ≤ (gSeqExt Phi R bf hsrc htgt i t).inner x v v) :
    ∃ tau : ℕ → ℕ, StrictMono tau ∧ ∃ g : ℝ → SmoothRiemannianMetric I P.M,
      BumpMetricConvergence Phi R bf hsrc htgt tau g a b := by
  obtain ⟨tau, htau, g, hg⟩ :=
    exists_metric_subsequence_tendsto_uniformly_on_time_interval_of_eventual_bounds
      hab R (gSeqExt Phi R bf hsrc htgt) hind hlip hcov hlower
  refine ⟨tau, htau, g, hg, ?_⟩
  intro K hK p epsilon hepsilon
  obtain ⟨N, hN⟩ := hg K hK p epsilon hepsilon
  exact ⟨N, fun k hk t ht q hq x hx =>
    (derivNorm_le_sup hK hq (gSeqExt Phi R bf hsrc htgt (tau k) t) (g t) R hx).trans_lt
      (hN k hk t ht)⟩

theorem exists_halfLineMetricConvergenceData_of_eventual_compact_bounds
    (Phi : PointedCGHMaps (I := I) X P phi)
    (R : SmoothRiemannianMetric I P.M)
    (bf : BumpFamily Phi) (hsrc : SourceIsSigmaCompact Phi)
    (htgt : TargetIsSigmaCompact Phi)
    (hind : ∀ n i : ℕ, ∀ K : Set P.M, IsCompact K → ∀ p : ℕ,
      ∃ L : ℝ, 0 ≤ L ∧ ∀ s ∈ Icc (-(n : ℝ)) 0, ∀ t ∈ Icc (-(n : ℝ)) 0,
        ∀ q ≤ p, ∀ x ∈ K,
          metricDerivNorm q (gSeqExt Phi R bf hsrc htgt i s)
            (gSeqExt Phi R bf hsrc htgt i t) R x ≤ L * |s - t|)
    (hlip : ∀ n : ℕ, ∀ K : Set P.M, IsCompact K → ∀ p : ℕ,
      ∃ L : ℝ, 0 ≤ L ∧ ∀ᶠ i in atTop,
        ∀ s ∈ Icc (-(n : ℝ)) 0, ∀ t ∈ Icc (-(n : ℝ)) 0,
          ∀ q ≤ p, ∀ x ∈ K,
            metricDerivNorm q (gSeqExt Phi R bf hsrc htgt i s)
              (gSeqExt Phi R bf hsrc htgt i t) R x ≤ L * |s - t|)
    (hcov : ∀ n : ℕ, ∀ t ∈ Icc (-(n : ℝ)) 0, ∀ q : ℕ,
      ∀ K : Set P.M, IsCompact K → ∃ C : ℝ, ∀ᶠ i in atTop, ∀ x ∈ K,
        metricCovDerivNorm q (gSeqExt Phi R bf hsrc htgt i t) R x ≤ C)
    (hlower : ∀ n : ℕ, ∀ t ∈ Icc (-(n : ℝ)) 0, ∃ c : ℝ, 0 < c ∧
      ∀ i, ∀ x : P.M, ∀ v : TangentSpace I x,
        c * R.inner x v v ≤ (gSeqExt Phi R bf hsrc htgt i t).inner x v v) :
    Nonempty (HalfLineMetricConvergenceData Phi R bf hsrc htgt) := by
  apply nonempty_halfLineMetricConvergenceData (Φ := Phi)
  intro n rho hrho
  obtain ⟨tau, htau, g, hg⟩ :=
    exists_metric_subsequence_tendsto_uniformly_on_time_interval_of_eventual_bounds
      (neg_nonpos.mpr (Nat.cast_nonneg n) : -(n : ℝ) ≤ 0) R (fun i => gSeqExt Phi R bf hsrc htgt (rho i))
      (fun i => hind n (rho i))
      (fun K hK p => by
        obtain ⟨L, hL, hb⟩ := hlip n K hK p
        exact ⟨L, hL, hrho.tendsto_atTop.eventually hb⟩)
      (fun t ht q K hK => by
        obtain ⟨C, hb⟩ := hcov n t ht q K hK
        exact ⟨C, hrho.tendsto_atTop.eventually hb⟩)
      (fun t ht => by
        obtain ⟨c, hc, hb⟩ := hlower n t ht
        exact ⟨c, hc, fun i => hb (rho i)⟩)
  refine ⟨tau, htau, g, hg, ?_⟩
  intro K hK p epsilon hepsilon
  obtain ⟨N, hN⟩ := hg K hK p epsilon hepsilon
  exact ⟨N, fun k hk t ht q hq x hx =>
    (derivNorm_le_sup hK hq (gSeqExt Phi R bf hsrc htgt (rho (tau k)) t) (g t) R hx).trans_lt
      (hN k hk t ht)⟩

theorem exists_halfLineMetricConvergenceData_of_window_cutoff_bounds
    (Phi : PointedCGHMaps (I := I) X P phi)
    (R : SmoothRiemannianMetric I P.M)
    (bf : BumpFamily Phi) (hsrc : SourceIsSigmaCompact Phi)
    (htgt : TargetIsSigmaCompact Phi)
    (bfWin : ∀ _n : ℕ, ∀ rho : ℕ → ℕ, ∀ hrho : StrictMono rho,
      BumpFamily (Phi.compSubseq rho hrho))
    (hind : ∀ n : ℕ, ∀ rho : ℕ → ℕ, ∀ hrho : StrictMono rho,
      let G := gSeqExt (Phi.compSubseq rho hrho) R (bfWin n rho hrho)
        (SourceIsSigmaCompact.compSubseq Phi hsrc rho hrho)
        (TargetIsSigmaCompact.compSubseq Phi htgt rho hrho)
      ∀ i, ∀ K : Set P.M, IsCompact K → ∀ p : ℕ,
        ∃ L : ℝ, 0 ≤ L ∧ ∀ s ∈ Icc (-(n : ℝ)) 0, ∀ t ∈ Icc (-(n : ℝ)) 0,
          ∀ q ≤ p, ∀ x ∈ K, metricDerivNorm q (G i s) (G i t) R x ≤ L * |s - t|)
    (hlip : ∀ n : ℕ, ∀ rho : ℕ → ℕ, ∀ hrho : StrictMono rho,
      let G := gSeqExt (Phi.compSubseq rho hrho) R (bfWin n rho hrho)
        (SourceIsSigmaCompact.compSubseq Phi hsrc rho hrho)
        (TargetIsSigmaCompact.compSubseq Phi htgt rho hrho)
      ∀ K : Set P.M, IsCompact K → ∀ p : ℕ,
        ∃ L : ℝ, 0 ≤ L ∧ ∀ᶠ i in atTop,
          ∀ s ∈ Icc (-(n : ℝ)) 0, ∀ t ∈ Icc (-(n : ℝ)) 0,
            ∀ q ≤ p, ∀ x ∈ K, metricDerivNorm q (G i s) (G i t) R x ≤ L * |s - t|)
    (hcov : ∀ n : ℕ, ∀ rho : ℕ → ℕ, ∀ hrho : StrictMono rho,
      let G := gSeqExt (Phi.compSubseq rho hrho) R (bfWin n rho hrho)
        (SourceIsSigmaCompact.compSubseq Phi hsrc rho hrho)
        (TargetIsSigmaCompact.compSubseq Phi htgt rho hrho)
      ∀ t ∈ Icc (-(n : ℝ)) 0, ∀ q : ℕ, ∀ K : Set P.M, IsCompact K →
        ∃ C : ℝ, ∀ᶠ i in atTop, ∀ x ∈ K, metricCovDerivNorm q (G i t) R x ≤ C)
    (hlower : ∀ n : ℕ, ∀ rho : ℕ → ℕ, ∀ hrho : StrictMono rho,
      let G := gSeqExt (Phi.compSubseq rho hrho) R (bfWin n rho hrho)
        (SourceIsSigmaCompact.compSubseq Phi hsrc rho hrho)
        (TargetIsSigmaCompact.compSubseq Phi htgt rho hrho)
      ∀ t ∈ Icc (-(n : ℝ)) 0, ∃ c : ℝ, 0 < c ∧
        ∀ i, ∀ x : P.M, ∀ v : TangentSpace I x, c * R.inner x v v ≤ (G i t).inner x v v) :
    Nonempty (HalfLineMetricConvergenceData Phi R bf hsrc htgt) := by
  apply nonempty_halfLineMetricConvergenceData (Φ := Phi)
  intro n rho hrho
  obtain ⟨tau, htau, g, hg⟩ := exists_bumpMetricConvergence_of_eventual_compact_bounds
    (Phi.compSubseq rho hrho) R (bfWin n rho hrho)
    (SourceIsSigmaCompact.compSubseq Phi hsrc rho hrho)
    (TargetIsSigmaCompact.compSubseq Phi htgt rho hrho)
    (neg_nonpos.mpr (Nat.cast_nonneg n))
    (hind n rho hrho) (hlip n rho hrho) (hcov n rho hrho) (hlower n rho hrho)
  exact ⟨tau, htau, g, BumpMetricConvergence.of_compSubseq (Φ := Phi) rho hrho
    (BumpMetricConvergence.change_bump_family
      (BumpFamily.compSubseq Phi bf rho hrho) htau hg)⟩

end DifferentialGeometry.CheegerGromovCompactness
