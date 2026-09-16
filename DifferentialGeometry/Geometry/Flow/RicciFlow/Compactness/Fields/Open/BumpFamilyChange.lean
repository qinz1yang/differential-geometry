import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Open.Convergence
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Norm.Continuity
import DifferentialGeometry.Topology.SigmaCompactOpen

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Set Filter
open scoped Manifold ContDiff _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : PointedFlowSeq.{u, uE, uH} (I := I)}
  {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {subseq : ℕ → ℕ}
  {Φ : PointedCGHMaps (I := I) X P subseq}

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact

private theorem eventually_bump_metric_deriv_eq
    (R : SmoothRiemannianMetric I P.M)
    (bf₁ bf₂ : BumpFamily Φ) (hsrc : SourceIsSigmaCompact Φ)
    (htgt : TargetIsSigmaCompact Φ)
    {K : Set P.M} (hK : IsCompact K) :
    ∀ᶠ i in atTop, ∀ t : ℝ, ∀ q : ℕ,
      ∀ g : SmoothRiemannianMetric I P.M, ∀ x ∈ K,
        metricDerivNorm q (gSeqExt Φ R bf₁ hsrc htgt i t) g R x =
          metricDerivNorm q (gSeqExt Φ R bf₂ hsrc htgt i t) g R x := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨N₁, hN₁⟩ := bf₁.grow_cover K hK
  obtain ⟨N₂, hN₂⟩ := bf₂.grow_cover K hK
  filter_upwards [eventually_ge_atTop (max N₁ N₂)] with i hi
  obtain ⟨U₁, hU₁, hKU₁, hχ₁⟩ := bf₁.chi_one i
  obtain ⟨U₂, hU₂, hKU₂, hχ₂⟩ := bf₂.chi_one i
  let U : TopologicalSpace.Opens P.M :=
    ⟨U₁ ∩ U₂ ∩ Φ.source i, (hU₁.inter hU₂).inter (Φ.source_open i)⟩
  let _ : SigmaCompactSpace U :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I U.isOpen)
  intro t q g x hx
  have hxU : x ∈ U :=
    ⟨⟨hKU₁ (hN₁ i ((le_max_left N₁ N₂).trans hi) hx),
      hKU₂ (hN₂ i ((le_max_right N₁ N₂).trans hi) hx)⟩,
      bf₁.grow_subset i (hN₁ i ((le_max_left N₁ N₂).trans hi) hx)⟩
  have heq : ∀ y : P.M, y ∈ U → ∀ v w : TangentSpace I y,
      (gSeqExt Φ R bf₁ hsrc htgt i t).inner y v w =
        (gSeqExt Φ R bf₂ hsrc htgt i t).inner y v w := by
    intro y hy v w
    rw [gSeqExt_inner_of_mem Φ R bf₁ hsrc htgt i t y hy.2 v w,
      gSeqExt_inner_of_mem Φ R bf₂ hsrc htgt i t y hy.2 v w,
      hχ₁ y hy.1.1, hχ₂ y hy.1.2]
  have hcov : metricCovDeriv (gSeqExt Φ R bf₁ hsrc htgt i t) R q x =
      metricCovDeriv (gSeqExt Φ R bf₂ hsrc htgt i t) R q x := by
    ext slots
    exact metricCovDeriv_eq_of_eqOn _ _ R U heq q ⟨x, hxU⟩ slots
  simp only [metricDerivNorm, metricDiffCovDerivAt, hcov]

theorem BumpMetricConvergence.change_bump_family
    {R : SmoothRiemannianMetric I P.M}
    {bf₁ : BumpFamily Φ} (bf₂ : BumpFamily Φ)
    {hsrc : SourceIsSigmaCompact Φ} {htgt : TargetIsSigmaCompact Φ}
    {ρ : ℕ → ℕ} (hρ : StrictMono ρ)
    {g : ℝ → SmoothRiemannianMetric I P.M} {a b : ℝ}
    (h : BumpMetricConvergence Φ R bf₁ hsrc htgt ρ g a b) :
    BumpMetricConvergence Φ R bf₂ hsrc htgt ρ g a b := by
  have hpt : ∀ K : Set P.M, IsCompact K → ∀ p : ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ i ≥ N, ∀ t ∈ Icc a b, ∀ q ≤ p, ∀ x ∈ K,
        metricDerivNorm q (gSeqExt Φ R bf₂ hsrc htgt (ρ i) t) (g t) R x < ε := by
    intro K hK p ε hε
    obtain ⟨N, hN⟩ := h.convergencePt K hK p ε hε
    obtain ⟨J, hJ⟩ := eventually_atTop.mp
      (eventually_bump_metric_deriv_eq R bf₁ bf₂ hsrc htgt hK)
    refine ⟨max N J, fun i hi t ht q hq x hx => ?_⟩
    rw [← hJ (ρ i) (((le_max_right N J).trans hi).trans (hρ.id_le i)) t q (g t) x hx]
    exact hN i ((le_max_left N J).trans hi) t ht q hq x hx
  refine ⟨?_, hpt⟩
  intro K hK p ε hε
  obtain ⟨N, hN⟩ := hpt K hK p (ε / 2) (by positivity)
  refine ⟨N, fun i hi t ht => ?_⟩
  have hle : metricDerivNormSupOn K p (gSeqExt Φ R bf₂ hsrc htgt (ρ i) t) (g t) R ≤ ε / 2 :=
    metricDerivNormSupOn_le_of_forall K p _ _ R (ε / 2) (by positivity)
      (fun q hq x hx => (hN i hi t ht q hq x hx).le)
  linarith

end DifferentialGeometry.CheegerGromovCompactness
