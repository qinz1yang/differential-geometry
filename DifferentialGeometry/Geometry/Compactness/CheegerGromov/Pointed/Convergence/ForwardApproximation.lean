import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.InverseApproximation

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

theorem MetricConvergenceData.eventually_map_metric_approximation
    (C : MetricConvergenceData (I := I) Phi)
    (hcanonical : ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData Phi k)
    (K : Set L.M) (hK : IsCompact K) (p : ℕ)
    {eps : ℝ} (heps : 0 < eps) (heps1 : eps < 1) :
    ∀ᶠ k in atTop, K ⊆ Phi.source k ∧
      ∀ A : Set L.M, A ⊆ interior K →
        Nonempty (MapMetricApproximationOn (I := I) A eps p
          (Phi.map k) L.metric (X.obj (subseq k)).metric) := by
  obtain ⟨k0, hk0⟩ := C.converges K hK p eps heps
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
      (L.metric.restrictOpen U) (L.metric.restrictOpen U) < eps at hsup
  let Acore : Set U := (Subtype.val : U → L.M) ⁻¹' interior K
  have hclose : ∀ a ≤ p, ∀ z ∈ Acore,
      metricDerivNorm (I := I) a G (L.metric.restrictOpen U)
        (L.metric.restrictOpen U) z ≤ eps := by
    intro a ha z hz
    have hzK : z ∈ metricSourceCompactSet (I := I) Phi k K := by
      change (z : L.M) ∈ K
      exact interior_subset (show (z : L.M) ∈ interior K from hz)
    exact (derivNorm_le_sup (I := I) hcompact ha G
      (L.metric.restrictOpen U) (L.metric.restrictOpen U) hzK).trans hsup.le
  let R : PartialDiffeomorph I I L.M L.M ∞ := PartialDiffeomorph.refl L.M
  have hR : (U : Set L.M) ⊆ R.source := fun _ _ => mem_univ _
  have hRmetric (z : U) (v w : TangentSpace I z) :
      (L.metric.restrictOpen U).inner z v w = L.metric.inner (R z)
        (mfderiv I I (R : L.M → L.M) (z : L.M) v)
        (mfderiv I I (R : L.M → L.M) (z : L.M) w) := by
    change L.metric.inner z.val v w =
      L.metric.inner z.val (mfderiv I I id z.val v) (mfderiv I I id z.val w)
    rw [mfderiv_id]
    rfl
  have hsrc : K ⊆ (R.symm.trans (Phi.partialDiffeomorph k)).source := by
    intro x hx
    exact ⟨mem_univ _, hsource hx⟩
  refine ⟨hsource, ?_⟩
  intro A hA
  have hcapture : A ⊆ (fun z : U => (R : L.M → L.M) z) '' Acore := by
    intro x hx
    exact ⟨⟨x, hsource (interior_subset (hA hx))⟩, hA hx, rfl⟩
  exact exists_relative_map_metric_approximation_of_pullback_bound R
    (Phi.partialDiffeomorph k) U hR (fun _ hx => hx)
    L.metric (X.obj (subseq k)).metric (L.metric.restrictOpen U) G hRmetric hG
    hK hA hsrc hcapture heps heps1 hclose

end DifferentialGeometry.CheegerGromovCompactness
