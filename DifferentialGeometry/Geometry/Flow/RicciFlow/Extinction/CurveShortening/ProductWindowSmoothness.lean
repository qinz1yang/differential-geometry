import DifferentialGeometry.Geometry.Metric.Family.Descent
import DifferentialGeometry.Geometry.Metric.Family.DescentTensor
import DifferentialGeometry.Geometry.Metric.Family.Product
import DifferentialGeometry.Geometry.Metric.Family.Stationary
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Product

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Tensor0SBundle

namespace DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]

namespace MetricFamilySmoothOn

omit [FiniteDimensional ℝ F] in
private theorem inner_eq_of_localPullMetric
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric J N}
    (f : M → N) (hf : IsLocalDiffeomorph I J ∞ f) (x : M)
    (hpull : localPullMetric (I := I) (J := J) h f hf = g)
    (v w : TangentSpace J (f x)) :
    h.inner (f x) v w =
      g.inner x ((hf.mfderivToContinuousLinearEquiv (by simp) x).symm v)
        ((hf.mfderivToContinuousLinearEquiv (by simp) x).symm w) := by
  rw [← hpull, localPullMetric_inner, ← hf.mfderivToContinuousLinearEquiv_coe (by simp) x]
  simp

theorem of_surjective_localPullMetric
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I M}
    {h : ℝ → SmoothRiemannianMetric J N}
    (f : M → N) (hf : IsLocalDiffeomorph I J ∞ f) (hsurj : Function.Surjective f)
    (hg : MetricFamilySmoothOn (I := I) (M := M) D g)
    (hpull : ∀ t, localPullMetric (I := I) (J := J) (h t) f hf = g t) :
    MetricFamilySmoothOn (I := J) (M := N) D h := by
  have hreg : ContMDiffOn (𝓘(ℝ, ℝ).prod J)
      (J.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) ∞
      (fun p : ℝ × N => (⟨p.2, (h p.1).inner p.2⟩ : TotalSpace (F →L[ℝ] F →L[ℝ] ℝ)
        (fun y => TangentSpace J y →L[ℝ] TangentSpace J y →L[ℝ] ℝ)))
      (D.regular ×ˢ (Set.univ : Set N)) :=
    metricCLMSection_jointContMDiffOn_of_surjective_localPullMetric g D.regular
      (hg.metricCLMSection_contMDiffOn (Set.Subset.refl D.regular)) h f hf hsurj
      (fun t _ => hpull t)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro y v w
    obtain ⟨x, rfl⟩ := hsurj y
    exact (hg.coeff x _ _).congr fun t _ => inner_eq_of_localPullMetric f hf x (hpull t) v w
  · intro y v w
    obtain ⟨x, rfl⟩ := hsurj y
    exact (hg.coeff_cont x _ _).congr fun t _ =>
      inner_eq_of_localPullMetric f hf x (hpull t) v w
  · refine tensor0SFamilyContinuousOnSet.of_surjective_localPullMetric (I := I) (J := J)
      (s := 2) (K := D.carrier)
      (k := fun t x => metricTensorField (I := I) (g t) x) f hf hsurj
      hg.metricTensor_cont ?_
    intro t _ x v
    rw [metricTensorField_apply, metricTensorField_apply, ← hpull t, localPullMetric_inner]
  · intro Idx _ frame u hframe i j
    have hv (k : Idx) : ContMDiffOn (𝓘(ℝ, ℝ).prod J) (J.prod 𝓘(ℝ, F)) ∞
        (fun p : ℝ × N => TotalSpace.mk' F p.2 (frame k p.2)) (D.regular ×ˢ u) :=
      (hframe.contMDiffOn k).comp contMDiffOn_snd (fun p hp => hp.2)
    have hru := hreg.mono (Set.prod_mono (Set.Subset.refl D.regular) (Set.subset_univ u))
    have happ := ContMDiffOn.clm_bundle_apply₂ (F₁ := F) (F₂ := F) (F₃ := ℝ)
      (E₁ := TangentSpace J) (E₂ := TangentSpace J) (E₃ := Bundle.Trivial N ℝ)
      (b := fun p : ℝ × N => p.2) hru (hv i) (hv j)
    intro p hp
    have h := happ p hp
    rw [Bundle.contMDiffWithinAt_totalSpace] at h
    exact h.2

end MetricFamilySmoothOn

end DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

open DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [CompleteSpace E] in
theorem metricFamilySmoothOn_quotientProductMetric (A : QuotientProductAtlas I M) [I.Boundaryless]
    [T2Space M] {D : RealTimeInterval} {a b : ℝ}
    (B : SmoothMetricWindow (I := I) (M := M) D a b) (lambda : ℝ) (hlambda : 0 < lambda) :
    letI := A.charts
    letI := A.smoothManifold
    MetricFamilySmoothOn (I := I.prod 𝓘(ℝ, ℝ)) (M := M × Surgery.Topology.Circle) D
      (fun t => quotientProductMetric A (B.family.metric t) lambda hlambda) := by
  let := A.charts
  let := A.smoothManifold
  have hcover : MetricFamilySmoothOn (I := I.prod 𝓘(ℝ, ℝ)) (M := M × ℝ) D
      (fun t => coverProductMetric (B.family.metric t) lambda hlambda) :=
    MetricFamilySmoothOn.prod (g := B.family.metric)
      (h := fun _ : ℝ => DifferentialGeometry.scaleMetric (I := 𝓘(ℝ, ℝ)) (lambda ^ 2)
        (pow_pos hlambda 2) (DifferentialGeometry.euclideanMetric (E := ℝ)))
      B.smooth (metricFamilySmoothOn_stationary _ D)
  exact MetricFamilySmoothOn.of_surjective_localPullMetric (productCoverProjection (M := M))
    (isLocalDiffeomorph_productCoverProjection A) (surjective_productCoverProjection (M := M))
    hcover (fun t => quotientProductMetric_localPull A (B.family.metric t) lambda hlambda)

omit [CompleteSpace E] in
theorem exists_smoothMetricWindow_quotientProduct (A : QuotientProductAtlas I M) [I.Boundaryless]
    [SigmaCompactSpace M] [T2Space M] {D : RealTimeInterval} {a b : ℝ}
    (B : SmoothMetricWindow (I := I) (M := M) D a b) (lambda : ℝ) (hlambda : 0 < lambda) :
    letI := A.charts
    letI := A.smoothManifold
    ∃ Bhat : SmoothMetricWindow (I := I.prod 𝓘(ℝ, ℝ))
        (M := M × Surgery.Topology.Circle) D a b,
      Bhat.family = quotientProductFamily A B.family lambda hlambda ∧
      Bhat.family.metric =
        (fun t => quotientProductMetric A (B.family.metric t) lambda hlambda) ∧
      Bhat.lt = B.lt := by
  let := A.charts
  let := A.smoothManifold
  refine ⟨{ family := quotientProductFamily A B.family lambda hlambda
            smooth := ?_
            lt := B.lt
            regular := B.regular }, rfl, ?_, rfl⟩
  · exact metricFamilySmoothOn_quotientProductMetric A B lambda hlambda
  · rfl

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
