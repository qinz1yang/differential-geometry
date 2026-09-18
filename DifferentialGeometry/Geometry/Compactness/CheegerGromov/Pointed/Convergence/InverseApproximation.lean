import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.MetricApproximation.Inverse
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Compactness.Construction
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Continuity

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Set Filter
open scoped Manifold ContDiff Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
  {L : PointedRiemannianManifold.{u, uE, uH} (I := I)} {subseq : ℕ → ℕ}
  {Phi : PointedRiemannianConvergenceMaps (I := I) X L subseq}

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact

theorem MetricConvergenceData.eventually_inverse_map_metric_approximation
    (C : MetricConvergenceData (I := I) Phi)
    (hcanonical : ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData Phi k)
    (K : Set L.M) (hK : IsCompact K) (p : ℕ)
    {eps : ℝ} (heps : 0 < eps) (heps1 : eps < 1) :
    ∀ᶠ k in atTop, K ⊆ Phi.source k ∧
      ∀ A : Set L.M, A ⊆ interior K →
        Nonempty (MapMetricApproximationOn (I := I) (Phi.map k '' A) eps p
          ((Phi.partialDiffeomorph k).symm : (X.obj (subseq k)).M → L.M)
          (X.obj (subseq k)).metric L.metric) := by
  obtain ⟨δ, hδ, _hδ1, hδdim, hδbudget⟩ :=
    exists_metric_reference_change_delta (E := E) p heps
  obtain ⟨k0, hk0⟩ := C.converges K hK p δ hδ
  refine eventually_atTop.2 ⟨k0, ?_⟩
  intro k hk
  obtain ⟨hsource, hsup⟩ := hk0 k hk
  rw [hcanonical k] at hsup
  let U := metricSourceOpenSubset (I := I) Phi k
  let _ : SigmaCompactSpace U :=
    metric_source_domain_sigma_compact Phi k (Phi.isSigmaCompact_source k)
  let G : SmoothRiemannianMetric I U := Diffeomorph.pullbackMetric (I := I)
    ((X.obj (subseq k)).metric.restrictOpen (I := I) (metricTargetOpenSubset Phi k))
    (metricSourceTargetDiffeomorph Phi k)
  have hG : ∀ (z : U) (v w : TangentSpace I z),
      G.inner z v w = (X.obj (subseq k)).metric.inner
        ((Phi.partialDiffeomorph k) z)
        (mfderiv I I (Phi.partialDiffeomorph k : L.M → (X.obj (subseq k)).M)
          (z : L.M) v)
        (mfderiv I I (Phi.partialDiffeomorph k : L.M → (X.obj (subseq k)).M)
          (z : L.M) w) := by
    intro z v w
    dsimp only [G]
    erw [Diffeomorph.pullbackMetric_inner]
    change (X.obj (subseq k)).metric.inner _ _ _ = _
    erw [metric_source_target_diffeomorph_mfderiv,
      metric_source_target_diffeomorph_mfderiv]
    rfl
  have hcompact : IsCompact (metricSourceCompactSet (I := I) Phi k K) :=
    metric_source_compact_set_is_compact (I := I) Phi k hK hsource
  change metricDerivNormSupOn (I := I)
    (metricSourceCompactSet (I := I) Phi k K) p G
      (L.metric.restrictOpen U) (L.metric.restrictOpen U) < δ at hsup
  let u : Set U := (Subtype.val : U → L.M) ⁻¹' interior K
  have hu : IsOpen u := isOpen_interior.preimage continuous_subtype_val
  have hclose : ∀ z ∈ u, ∀ a ≤ p,
      metricDerivNorm (I := I) a G (L.metric.restrictOpen U)
        (L.metric.restrictOpen U) z ≤ δ := by
    intro z hz a ha
    have hzK : z ∈ metricSourceCompactSet (I := I) Phi k K := by
      change (z : L.M) ∈ K
      exact interior_subset (show (z : L.M) ∈ interior K from hz)
    exact (derivNorm_le_sup (I := I) hcompact ha G
      (L.metric.restrictOpen U) (L.metric.restrictOpen U) hzK).trans hsup.le
  have hKimage : IsCompact (Phi.map k '' K) :=
    hK.image_of_continuousOn
      ((Phi.partialDiffeomorph k).contMDiffOn_toFun.continuousOn.mono hsource)
  have htarget : Phi.map k '' K ⊆ (Phi.partialDiffeomorph k).target := by
    rintro y ⟨x, hx, rfl⟩
    exact (Phi.partialDiffeomorph k).map_source (hsource hx)
  have hinterior : Phi.map k '' interior K ⊆ interior (Phi.map k '' K) :=
    interior_maximal (image_mono interior_subset)
      ((Phi.partialDiffeomorph k).toOpenPartialHomeomorph.isOpen_image_of_subset_source
        isOpen_interior (interior_subset.trans hsource))
  refine ⟨hsource, ?_⟩
  intro A hA
  have hcapture : Phi.map k '' A ⊆
      (fun z : U => (Phi.partialDiffeomorph k) z) '' u := by
    rintro y ⟨x, hx, rfl⟩
    exact ⟨⟨x, hsource (interior_subset (hA hx))⟩, hA hx, rfl⟩
  exact exists_inverse_map_metric_approximation_of_pullback_bound
    (Phi.partialDiffeomorph k) U (fun _ hx => hx)
    L.metric (X.obj (subseq k)).metric G hG hu heps heps1
    hδ.le hδdim hδbudget hclose hKimage
    ((image_mono hA).trans hinterior) htarget hcapture

end DifferentialGeometry.CheegerGromovCompactness
