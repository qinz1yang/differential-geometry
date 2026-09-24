import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.InverseCapture
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.UrysohnsLemma

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Filter Set
open scoped Manifold ContDiff CompactlySupported Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
  {L : PointedRiemannianManifold.{u, uE, uH} (I := I)} {subseq : ℕ → ℕ}
  (Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq)

private local instance cutoffComplete : CompleteSpace E :=
  FiniteDimensional.complete ℝ E
private local instance cutoffLimitTopology : TopologicalSpace L.M := L.topology
private local instance cutoffLimitCharted : ChartedSpace H L.M := L.charted
private local instance cutoffLimitSmooth : IsManifold I ∞ L.M := L.smooth
private local instance cutoffLimitOne : IsManifold I 1 L.M :=
  IsManifold.of_le (I := I) (M := L.M) (n := ∞) (by decide)
private local instance cutoffLimitT2 : T2Space L.M := L.t2
private local instance cutoffLimitSigma : SigmaCompactSpace L.M := L.sigmaCompact
private local instance cutoffApproxTopology (k : ℕ) : TopologicalSpace (X.obj k).M :=
  (X.obj k).topology
private local instance cutoffApproxCharted (k : ℕ) : ChartedSpace H (X.obj k).M :=
  (X.obj k).charted
private local instance cutoffApproxSmooth (k : ℕ) : IsManifold I ∞ (X.obj k).M :=
  (X.obj k).smooth
private local instance cutoffApproxT2 (k : ℕ) : T2Space (X.obj k).M := (X.obj k).t2

theorem exists_pointed_inverse_capture_cutoff_at
    (z : L.M) (A : Set L.M) (hA : IsCompact A)
    {R s factor : ℝ} (hs : 0 ≤ s) (hfactor : 1 < factor)
    (hbuffer : factor * s < R)
    (hcompact : IsCompact (riemannianClosedBallOf L.metric z R))
    (hconv : metricSourceConvergesOn Φ
      (CanonicalMetricCompactness.canonicalSourceData Φ)
      (riemannianClosedBallOf L.metric z R) 0) :
    ∃ f : C_c(L.M, ℝ),
      (∀ x, f x ∈ Icc (0 : ℝ) 1) ∧
      EqOn (⇑f) 1 (A ∪ riemannianClosedBallOf L.metric z (factor * s)) ∧
      ∀ᶠ k in atTop,
        tsupport f ⊆ (Φ.partialDiffeomorph k).source ∧
        ∀ y ∈ riemannianClosedBallOf (X.obj (subseq k)).metric (Φ.map k z) s,
          y ∈ (Φ.partialDiffeomorph k).target ∧
          (Φ.partialDiffeomorph k).symm y ∈ (Φ.partialDiffeomorph k).source ∧
          (Φ.partialDiffeomorph k) ((Φ.partialDiffeomorph k).symm y) = y ∧
          f ((Φ.partialDiffeomorph k).symm y) = 1 := by
  let _ : LocallyCompactSpace H := I.locallyCompactSpace
  let _ : LocallyCompactSpace L.M := ChartedSpace.locallyCompactSpace H L.M
  have hKclosed : IsClosed (riemannianClosedBallOf L.metric z (factor * s)) :=
    isClosed_le (Geometry.Riemannian.continuous_riemannianEDist L.metric z) continuous_const
  have hK : IsCompact (riemannianClosedBallOf L.metric z (factor * s)) :=
    hcompact.of_isClosed_subset hKclosed
      (riemannianClosedBallOf_mono L.metric z hbuffer.le)
  have hcapture := pointed_metric_eventually_inverse_ball_capture
    (Φ := Φ) z hs hfactor hbuffer hcompact hconv
  obtain ⟨f, hfK, hfsupp, _, hfrange⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen
      (hA.union hK) isOpen_univ (subset_univ _)
  let fc : C_c(L.M, ℝ) := ⟨f, hasCompactSupport_def.mpr hfsupp⟩
  obtain ⟨ksupp, hksupp⟩ := Φ.source_subset hfsupp
  refine ⟨fc, hfrange, hfK, ?_⟩
  filter_upwards [hcapture, eventually_ge_atTop ksupp] with k hkcap hk
  refine ⟨hksupp k hk, ?_⟩
  intro y hy
  obtain ⟨hyt, hys, hyK, hmap⟩ := hkcap.2 y hy
  exact ⟨hyt, hys, hmap, hfK (Or.inr hyK)⟩

end DifferentialGeometry.CheegerGromovCompactness

end
