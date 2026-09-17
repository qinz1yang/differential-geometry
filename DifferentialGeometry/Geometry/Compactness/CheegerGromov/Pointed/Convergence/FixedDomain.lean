import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.DomainMetric

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Set Filter
open scoped _root_.Manifold ContDiff _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact

theorem metricCInfConvergenceOnCompacts_of_pointed_pullback
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)} {f : ℕ → ℕ}
    (F : PointedRiemannianConvergenceMaps X L f) (C : MetricConvergenceData F)
    (hcanonical : ∀ i, C.domain i = CanonicalMetricCompactness.canonicalSourceData F i)
    (U : TopologicalSpace.Opens L.M) (N : ℕ)
    (hsource : ∀ i, (U : Set L.M) ⊆ (F.partialDiffeomorph (i + N)).source)
    (g : ℕ → SmoothRiemannianMetric I U)
    (hmetric : ∀ i (x : U) (v w : TangentSpace I x),
      (g i).inner x v w = (X.obj (f (i + N))).metric.inner
        (F.partialDiffeomorph (i + N) x)
        (mfderiv I I (F.partialDiffeomorph (i + N)) x v)
        (mfderiv I I (F.partialDiffeomorph (i + N)) x w)) :
    MetricCInfConvergenceOnCompacts g (L.metric.restrictOpen U) (L.metric.restrictOpen U) := by
  let _ : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I U.isOpen)
  let e : L.M ≃ₘ⟮I, I⟯ L.M := _root_.Diffeomorph.refl I L.M ∞
  have hU (i : ℕ) : e '' (U : Set L.M) ⊆ F.source (i + N) := by
    rintro _ ⟨x, hx, rfl⟩
    exact hsource i hx
  have heq (i : ℕ) : g i =
      PDE.RicciFlow.Perelman.KappaSolutions.immersionInducedMetric (X.obj (f (i + N))).metric
        (PDE.RicciFlow.Perelman.KappaSolutions.pointedMaps_restrict_isSmoothEmbedding
          F e U (i + N) (hU i)).isImmersion := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    have hval : MDifferentiableAt I I (Subtype.val : U → L.M) x :=
      (contMDiff_subtype_val (I := I) (U := U) (n := ∞)).mdifferentiable (by decide) x
    have hF : MDifferentiableAt I I (F.map (i + N)) (x : L.M) :=
      (F.partialDiffeomorph (i + N)).mdifferentiableAt (by decide) (hsource i x.property)
    have hd (z : TangentSpace I x) :
        mfderiv I I (fun y : U => F.map (i + N) (e y)) x z =
          mfderiv I I (F.map (i + N)) (x : L.M) z := by
      have hc := mfderiv_comp_apply x hF hval z
      exact hc.trans (congrArg (mfderiv I I (F.map (i + N)) (x : L.M))
        (mfderiv_subtype_val_apply (I := I) U x z))
    rw [PDE.RicciFlow.Perelman.KappaSolutions.immersionInducedMetric_inner]
    exact (hmetric i x v w).trans
      (congrArg₂ (fun v' w' => (X.obj (f (i + N))).metric.inner
        (F.map (i + N) (x : L.M)) v' w') (hd v) (hd w)).symm
  have hlimit : Diffeomorph.pullbackMetricCross L.metric e = L.metric := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    rw [Diffeomorph.pullbackMetricCross_inner]
    change L.metric.inner x (mfderiv I I id x v) (mfderiv I I id x w) =
      L.metric.inner x v w
    rw [mfderiv_id]
    rfl
  intro K hK p epsilon hepsilon
  have hKimage : IsCompact ((Subtype.val : U → L.M) '' K) :=
    hK.image continuous_subtype_val
  obtain ⟨k0, hk0⟩ := C.converges _ hKimage p epsilon hepsilon
  refine ⟨k0, fun i hi => ?_⟩
  have hs := PDE.RicciFlow.Perelman.KappaSolutions.canonicalSource_fixedDomain_sup_eq
    F e U (i + N) (hU i) K p
  have himage : e '' ((Subtype.val : U → L.M) '' K) =
      (Subtype.val : U → L.M) '' K := Set.image_id _
  rw [← heq i, hlimit, himage] at hs
  rw [hs, ← hcanonical (i + N)]
  exact (hk0 (i + N) (by omega)).2

end DifferentialGeometry.CheegerGromovCompactness

end
