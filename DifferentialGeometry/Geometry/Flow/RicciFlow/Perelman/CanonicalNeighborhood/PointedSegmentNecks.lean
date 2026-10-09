import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NormalizedSegmentNecks
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Distance
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.AmbientQuadraticControl
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedScalarConvergence

set_option autoImplicit false
noncomputable section
open Filter Set
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

theorem exists_eventually_strongNeck_at_pointed_images_of_minimizing_segment_limits
    (kappa : ℝ) {alpha : ℝ} (ha : 0 < alpha) (hsmall : alpha < 1 / 32) :
    ∃ A epsStar : ℝ, 0 < A ∧ 0 < epsStar ∧
      ∀ eps sigma : ℝ, ∀ Phi : ℝ → ℝ, ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
        eps ≤ epsStar → ∀ (f : ℕ → ℕ) (γ : ∀ n, ℝ → (X.term (f n)).M)
          (ell : ℕ → ℝ) (rho tau : ℝ),
          Tendsto ell atTop (𝓝 rho) → 0 < tau → tau < rho →
          (∀ n, ∀ s ∈ Icc 0 (ell n), ∀ r ∈ Icc 0 (ell n),
            metricDistance ((X.term (f n)).S.base.metric 0) (γ n s) (γ n r) = |s - r|) →
          ∀ (L : PointedRiemannianManifold.{u, 0, 0} (I := I3))
            (maps : PointedRiemannianConvergenceMaps (X.toFlowSequence.atTime 0) L f)
            (C : MetricConvergenceData maps),
            (∀ n, C.domain n = CanonicalMetricCompactness.canonicalSourceData maps n) →
            ∀ x : L.M, 2 < metricScalarAt L.metric x →
              (∀ᶠ n in atTop, γ n tau ∈ maps.target n) →
              Tendsto (fun n => (maps.partialDiffeomorph n).symm (γ n tau)) atTop (𝓝 x) →
              A ^ 2 < metricScalarAt L.metric x * tau ^ 2 →
              A ^ 2 < metricScalarAt L.metric x * (rho - tau) ^ 2 →
              ∀ᶠ n in atTop, Nonempty (StrongNeck (X.term (f n)).S
                (2 * alpha) (maps.partialDiffeomorph n x) 0) := by
  obtain ⟨A, epsStar, hA, hepsStar, hneck⟩ :=
    exists_eventually_strongNeck_near_minimizing_segment_limits.{u} kappa ha hsmall
  refine ⟨A, epsStar, hA, hepsStar, ?_⟩
  intro eps sigma Phi X heps f γ ell rho tau hell htau htr hsegment
    L maps C hcanonical x hR hstay hconv hleft hright
  have hreference (n : ℕ) : (C.domain n).referenceMetric = (C.domain n).limitMetric := by
    rw [hcanonical n]
    rfl
  have hupper (K : Set L.M) (hK : IsCompact K) (D : ℝ) (hD : 1 < D) :
      ∀ᶠ n in atTop, ∀ y ∈ K, ∀ v : TangentSpace I3 y,
        ((X.term (f n)).S.base.metric 0).inner (maps.partialDiffeomorph n y)
          (mfderiv I3 I3 (maps.partialDiffeomorph n) y v)
          (mfderiv I3 I3 (maps.partialDiffeomorph n) y v) ≤ D ^ 2 * L.metric.inner y v v := by
    obtain ⟨N, hN⟩ := KappaSolutions.exists_pointed_full_ambient_quadratic_control
      C hreference K hK (D ^ 2 - 1) (by nlinarith)
    filter_upwards [eventually_ge_atTop N] with n hn
    intro y hy v
    have hh := (abs_le.mp ((hN n hn).2 y hy v)).2
    change ((X.term (f n)).S.base.metric 0).inner (maps.partialDiffeomorph n y)
      (mfderiv I3 I3 (maps.partialDiffeomorph n) y v)
      (mfderiv I3 I3 (maps.partialDiffeomorph n) y v) - L.metric.inner y v v ≤
        (D ^ 2 - 1) * L.metric.inner y v v at hh
    nlinarith
  have hdist := maps.tendsto_edist_map_zero hupper hconv
  have hsource : Tendsto (fun n => riemannianEDistOf ((X.term (f n)).S.base.metric 0)
      (maps.partialDiffeomorph n x) (γ n tau)) atTop (𝓝 0) := by
    apply hdist.congr'
    filter_upwards [hstay] with n hn
    have hinv : maps.partialDiffeomorph n ((maps.partialDiffeomorph n).symm (γ n tau)) =
        γ n tau := (maps.partialDiffeomorph n).right_inv hn
    change riemannianEDistOf _ _ (maps.partialDiffeomorph n
      ((maps.partialDiffeomorph n).symm (γ n tau))) = _
    rw [hinv]
    rfl
  have hnear : Tendsto (fun n => metricDistance ((X.term (f n)).S.base.metric 0)
      (maps.partialDiffeomorph n x) (γ n tau)) atTop (𝓝 0) := by
    simpa only [metricDistance, Function.comp_def, ENNReal.toReal_zero] using
      (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).comp hsource
  have hscalar := KappaSolutions.pointedScalar_tendsto_of_metricCG_canonical_domains C hcanonical x
  exact hneck eps sigma Phi X heps f γ (fun n => maps.partialDiffeomorph n x)
    ell rho tau (metricScalarAt L.metric x) hell htau htr hR hsegment hscalar hnear hleft hright

theorem exists_eventually_strongNeck_at_pointed_images_near_scalar_blowup_endpoint
    (kappa : ℝ) {alpha : ℝ} (ha : 0 < alpha) (hsmall : alpha < 1 / 32) :
    ∃ A epsStar : ℝ, 0 < A ∧ 0 < epsStar ∧
      ∀ eps sigma : ℝ, ∀ Phi : ℝ → ℝ, ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
        eps ≤ epsStar → ∀ (f : ℕ → ℕ) (γ : ∀ n, ℝ → (X.term (f n)).M)
          (ell : ℕ → ℝ) (rho : ℝ), 0 < rho → Tendsto ell atTop (𝓝 rho) →
          (∀ n, ∀ s ∈ Icc 0 (ell n), ∀ r ∈ Icc 0 (ell n),
            metricDistance ((X.term (f n)).S.base.metric 0) (γ n s) (γ n r) = |s - r|) →
          ∀ (L : PointedRiemannianManifold.{u, 0, 0} (I := I3))
            (maps : PointedRiemannianConvergenceMaps (X.toFlowSequence.atTime 0) L f)
            (C : MetricConvergenceData maps),
            (∀ n, C.domain n = CanonicalMetricCompactness.canonicalSourceData maps n) →
            ∀ g : Ico 0 rho → L.M,
              (∀ tau : Ico 0 rho, ∀ᶠ n in atTop, γ n tau ∈ maps.target n) →
              (∀ tau : Ico 0 rho,
                Tendsto (fun n => (maps.partialDiffeomorph n).symm (γ n tau))
                  atTop (𝓝 (g tau))) →
              Tendsto (fun tau => metricScalarAt L.metric (g tau))
                (comap (Subtype.val : Ico 0 rho → ℝ) (𝓝 rho)) atTop →
              (∀ tau : Ico 0 rho, 2 < metricScalarAt L.metric (g tau) →
                A ^ 2 ≤ metricScalarAt L.metric (g tau) * (rho - tau) ^ 2) →
              ∀ᶠ (tau : Ico 0 rho) in comap (Subtype.val : Ico 0 rho → ℝ) (𝓝 rho),
                ∀ᶠ n in atTop, Nonempty (StrongNeck (X.term (f n)).S
                  (2 * alpha) (maps.partialDiffeomorph n (g tau)) 0) := by
  obtain ⟨A, epsStar, hA, hepsStar, hneck⟩ :=
    exists_eventually_strongNeck_at_pointed_images_of_minimizing_segment_limits.{u}
      kappa ha hsmall
  refine ⟨2 * A, epsStar, by positivity, hepsStar, ?_⟩
  intro eps sigma Phi X heps f γ ell rho hrho hell hsegment L maps C hcanonical
    g hstay hconv hblow hquant
  have htime : Tendsto (Subtype.val : Ico 0 rho → ℝ)
      (comap (Subtype.val : Ico 0 rho → ℝ) (𝓝 rho)) (𝓝 rho) := tendsto_comap
  have hleft := hblow.atTop_mul_pos (sq_pos_of_pos hrho) (htime.pow 2)
  filter_upwards [htime.eventually (eventually_gt_nhds hrho),
    hblow.eventually (eventually_gt_atTop 2),
    hleft.eventually (eventually_gt_atTop (A ^ 2))] with tau ht hR hl
  have hr : A ^ 2 < metricScalarAt L.metric (g tau) * (rho - tau) ^ 2 := by
    have hh := hquant tau hR
    nlinarith [sq_pos_of_pos hA]
  exact hneck eps sigma Phi X heps f γ ell rho tau hell ht tau.property.2 hsegment
    L maps C hcanonical (g tau) hR (hstay tau) (hconv tau) hl hr

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
end
