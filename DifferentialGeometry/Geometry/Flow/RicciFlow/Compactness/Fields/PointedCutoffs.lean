import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Cutoff
import DifferentialGeometry.Geometry.Comparison.HopfRinow.Proper
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.HalfLine

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Filter Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open scoped Manifold ContDiff CompactlySupported Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : PointedFlowSeq.{u, uE, uH} (I := I)}
  {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {phi : ℕ → ℕ}

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle
  PointedFlowData.topology PointedFlowData.charted PointedFlowData.smooth
  PointedFlowData.t2 PointedFlowData.sigmaCompact

theorem HalfLineMetricConvergenceData.exists_inverse_capture_cutoff_at
    (Phi : PointedCGHMaps X P phi) {R : SmoothRiemannianMetric I P.M}
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    {t : ℝ} (ht : t ≤ 0)
    (hcomplete : MetricComplete (I := I)
      ({ P with metric := co.gInf t } : PointedRiemannianManifold (I := I)))
    (z : P.M) (A : Set P.M) (hA : IsCompact A)
    {s epsilon : ℝ} (hs : 0 ≤ s) (hepsilon : 0 < epsilon) :
    ∃ f : C_c(P.M, ℝ),
      (∀ x, f x ∈ Icc (0 : ℝ) 1) ∧
      EqOn (⇑f) 1 (A ∪ riemannianClosedBallOf (co.gInf t) z ((1 + epsilon) * s)) ∧
      ∀ᶠ k in atTop,
        tsupport f ⊆ (Phi.partialDiffeomorph (co.φ k)).source ∧
        ∀ y ∈ riemannianClosedBallOf ((X.term (phi (co.φ k))).S.base.metric t)
            (Phi.map (co.φ k) z) s,
          y ∈ (Phi.partialDiffeomorph (co.φ k)).target ∧
          (Phi.partialDiffeomorph (co.φ k)).symm y ∈
            (Phi.partialDiffeomorph (co.φ k)).source ∧
          (Phi.partialDiffeomorph (co.φ k))
            ((Phi.partialDiffeomorph (co.φ k)).symm y) = y ∧
          f ((Phi.partialDiffeomorph (co.φ k)).symm y) = 1 := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let Q : PointedRiemannianManifold.{u, uE, uH} (I := I) :=
    { P with metric := co.gInf t }
  let Psi : PointedRiemannianConvergenceMaps (I := I) (X.atTime t) Q (phi ∘ co.φ) :=
    (Phi.compSubseq co.φ co.strictMono).atTimeWithMetric t (co.gInf t)
  have hmetricComplete : RiemannianMetricComplete (I := I) Q.metric :=
    ⟨MetricComplete.complete (I := I) Q hcomplete⟩
  let K := riemannianClosedBallOf Q.metric z ((1 + epsilon) * s + 1)
  have hK : IsCompact K :=
    RiemannianMetricComplete.closedEBall_isCompact hmetricComplete z _
  obtain ⟨C, hcanonical, _hreference⟩ :=
    co.exists_canonicalMetricConvergenceData Phi ht
  have hconv : metricSourceConvergesOn Psi
      (CanonicalMetricCompactness.canonicalSourceData Psi) K 0 := by
    have h := C.converges K hK 0
    rw [funext hcanonical] at h
    exact h
  exact exists_pointed_inverse_capture_cutoff_at Psi z A hA hs
    (by linarith : 1 < 1 + epsilon)
    (by linarith : (1 + epsilon) * s < (1 + epsilon) * s + 1) hK hconv

end DifferentialGeometry.CheegerGromovCompactness

end
