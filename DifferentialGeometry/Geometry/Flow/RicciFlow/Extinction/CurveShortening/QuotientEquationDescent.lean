import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.QuotientProductRicciBackground
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProductWindowSmoothness
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.LocalIterCov
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.ProductLine
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Descent

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G} [J.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N] [T2Space N]

private theorem continuousOn_metricScalarAt_of_surjective_localPullMetric
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (f : M → N) (hf : IsLocalDiffeomorph I J ∞ f) (hsurj : Function.Surjective f)
    (g : ℝ → SmoothRiemannianMetric J N)
    (hpull : ∀ s ∈ D.carrier, localPullMetric (g s) f hf = S.family.metric s) :
    ContinuousOn (fun q : ℝ × N => metricScalarAt (I := J) (g q.1) q.2)
      (D.carrier ×ˢ (univ : Set N)) := by
  intro q hq
  obtain ⟨x, hx⟩ := hsurj q.2
  let Y := (hf x).localInverse
  have hqY : q.2 ∈ Y.source := hx ▸ (hf x).localInverse_mem_source
  have hYat : ContinuousAt (fun r : ℝ × N => Y r.2) q :=
    (((hf x).localInverse_contMDiffOn.continuousOn).continuousAt
      (Y.open_source.mem_nhds hqY)).comp continuousAt_snd
  have hφ : ContinuousWithinAt (fun r : ℝ × N => ((r.1 : ℝ), Y r.2))
      (D.carrier ×ˢ (univ : Set N)) q :=
    (continuousAt_fst.prodMk hYat).continuousWithinAt
  have hSscalar := (hS.scalarCont ((q.1 : ℝ), Y q.2)) ⟨hq.1, mem_univ _⟩
  have hcomp : ContinuousWithinAt
      ((fun p : ℝ × M => S.scalar p.1 p.2) ∘ fun r : ℝ × N => ((r.1 : ℝ), Y r.2))
      (D.carrier ×ˢ (univ : Set N)) q :=
    hSscalar.comp (f := fun r : ℝ × N => ((r.1 : ℝ), Y r.2)) hφ
      (fun r hr => ⟨hr.1, mem_univ _⟩)
  have hsrc : ∀ᶠ r in 𝓝[D.carrier ×ˢ (univ : Set N)] q, r.2 ∈ Y.source :=
    Filter.Eventually.filter_mono
      nhdsWithin_le_nhds
      (show ∀ᶠ r in 𝓝 q, r.2 ∈ Y.source from
        continuous_snd.continuousAt.preimage_mem_nhds (Y.open_source.mem_nhds hqY))
  have hpoint : ∀ r : ℝ × N, r.1 ∈ D.carrier → r.2 ∈ Y.source →
      S.scalar r.1 (Y r.2) = metricScalarAt (I := J) (g r.1) r.2 := by
    intro r hr hrY
    have hfr : f (Y r.2) = r.2 := (hf x).localInverse_right_inv hrY
    rw [show S.scalar r.1 (Y r.2) =
        metricScalarAt (I := I) (S.family.metric r.1) (Y r.2) from rfl,
      ← hpull r.1 hr, metricScalarAt_localPull (I := I) (J := J) (g r.1) f hf (Y r.2), hfr]
  have hev : (fun r : ℝ × N => S.scalar r.1 (Y r.2))
      =ᶠ[𝓝[D.carrier ×ˢ (univ : Set N)] q]
      (fun r : ℝ × N => metricScalarAt (I := J) (g r.1) r.2) := by
    filter_upwards [self_mem_nhdsWithin, hsrc] with r hr hrY
    exact hpoint r hr.1 hrY
  exact hcomp.congr_of_eventuallyEq hev.symm (hpoint q hq.1 hqY).symm

private theorem differentiableWithinAt_metricScalarAt_of_surjective_localPullMetric
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (f : M → N) (hf : IsLocalDiffeomorph I J ∞ f) (hsurj : Function.Surjective f)
    (g : ℝ → SmoothRiemannianMetric J N)
    (hpull : ∀ s ∈ D.carrier, localPullMetric (g s) f hf = S.family.metric s)
    {K : Set ℝ} {t : ℝ} (ht : t ∈ K) (hK : K ⊆ D.carrier) (y : N) :
    DifferentiableWithinAt ℝ (fun s : ℝ => metricScalarAt (I := J) (g s) y) K t := by
  obtain ⟨x, rfl⟩ := hsurj y
  have hkey : ∀ s ∈ K, metricScalarAt (I := J) (g s) (f x) = S.scalar s x := by
    intro s hs
    rw [show S.scalar s x = metricScalarAt (I := I) (S.family.metric s) x from rfl,
      ← hpull s (hK hs), metricScalarAt_localPull (I := I) (J := J) (g s) f hf x]
  exact (hS.scalarTime ht hK x).congr hkey (hkey t ht)

private theorem tensor0SFamilyContinuousOnSet_ricciAt_of_surjective_localPullMetric
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (f : M → N) (hf : IsLocalDiffeomorph I J ∞ f) (hsurj : Function.Surjective f)
    (g : ℝ → SmoothRiemannianMetric J N)
    (hpull : ∀ s ∈ D.carrier, localPullMetric (g s) f hf = S.family.metric s) :
    tensor0SFamilyContinuousOnSet (I := J) (M := N) 2 D.carrier
      (fun t y => metricRicciAt (I := J) (g t) y) := by
  refine tensor0SFamilyContinuousOnSet.of_surjective_localPullMetric (I := I) (J := J)
    (s := 2) (K := D.carrier) (k := fun t x => metricRicciAt (I := I) (S.family.metric t) x)
    f hf hsurj ?_ ?_
  · simpa only [SolutionOn.ricci, SolutionFamily.ricci_apply, SolutionFamily.ricciAt,
      SolutionOn.family_metric] using hS.ricciCont
  · intro t ht x v
    rw [← hpull t ht]
    exact DifferentialGeometry.Geometry.Tensor.metricRicciAt_localPullMetric (I := I) (J := J)
      (g t) f hf x v

omit [I.Boundaryless] [J.Boundaryless] in
private theorem tensor0SFamilyContinuousOnSet_rm04At_of_surjective_localPullMetric
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (f : M → N) (hf : IsLocalDiffeomorph I J ∞ f) (hsurj : Function.Surjective f)
    (g : ℝ → SmoothRiemannianMetric J N)
    (hpull : ∀ s ∈ D.carrier, localPullMetric (g s) f hf = S.family.metric s) :
    tensor0SFamilyContinuousOnSet (I := J) (M := N) 4 D.carrier
      (fun t y => metricRm04At (I := J) (g t) y) := by
  refine tensor0SFamilyContinuousOnSet.of_surjective_localPullMetric (I := I) (J := J)
    (s := 4) (K := D.carrier) (k := fun t x => metricRm04At (I := I) (S.family.metric t) x)
    f hf hsurj ?_ ?_
  · simpa only [SolutionFamily.rm04, metricRm04_apply, SolutionOn.family_metric] using hS.rm04Cont
  · intro t ht x v
    rw [← hpull t ht]
    exact DifferentialGeometry.Geometry.Tensor.metricRm04At_localPullMetric (I := I) (J := J)
      (g t) f hf x v

theorem IsSolutionOn.of_surjective_localPullMetric_of_metricFamilySmoothOn
    {D : RealTimeInterval} {S : SolutionOn (I := I) (M := M) D} (hS : IsSolutionOn S)
    (f : M → N) (hf : IsLocalDiffeomorph I J ∞ f) (hsurj : Function.Surjective f)
    (g : ℝ → SmoothRiemannianMetric J N)
    (hsmooth : MetricFamilySmoothOn (I := J) (M := N) D g)
    (hpull : ∀ s ∈ D.carrier, localPullMetric (g s) f hf = S.family.metric s) :
    IsSolutionOn (I := J) ({ base := { metric := g } } : SolutionOn (I := J) (M := N) D) := by
  refine isSolutionOn_of_reg (I := J) g hsmooth ?_ ?_ ?_ ?_ ?_
  · intro t ht y v w
    exact (metric_hasDerivWithinAt_of_surjective_localPullMetric S hS f hf hsurj g
      (D.regular_subset ht) ht hpull y v w).hasDerivAt (D.regular_mem_nhds ht)
  · exact continuousOn_metricScalarAt_of_surjective_localPullMetric S hS f hf hsurj g hpull
  · intro t ht y
    exact differentiableWithinAt_metricScalarAt_of_surjective_localPullMetric S hS f hf hsurj g
      hpull (K := D.carrier) ht (Subset.refl _) y
  · exact tensor0SFamilyContinuousOnSet_ricciAt_of_surjective_localPullMetric S hS f hf hsurj g
      hpull
  · exact tensor0SFamilyContinuousOnSet_rm04At_of_surjective_localPullMetric S hS f hf hsurj g
      hpull

theorem IsSolutionOn.of_surjective_localPullMetric
    {D : RealTimeInterval} {S : SolutionOn (I := I) (M := M) D} (hS : IsSolutionOn S)
    (f : M → N) (hf : IsLocalDiffeomorph I J ∞ f) (hsurj : Function.Surjective f)
    (g : ℝ → SmoothRiemannianMetric J N)
    (hpull : ∀ t, localPullMetric (g t) f hf = S.family.metric t) :
    IsSolutionOn (I := J) ({ base := { metric := g } } : SolutionOn (I := J) (M := N) D) :=
  IsSolutionOn.of_surjective_localPullMetric_of_metricFamilySmoothOn hS f hf hsurj g
    (MetricFamilySmoothOn.of_surjective_localPullMetric f hf hsurj hS.smoothMetric hpull)
    (fun s _ => hpull s)

end DifferentialGeometry.PDE.RicciFlow

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

open DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem isSolutionOn_quotientProductFamily (A : QuotientProductAtlas I M) [I.Boundaryless]
    [SigmaCompactSpace M] [T2Space M] {D : RealTimeInterval} {a b : ℝ}
    (B : RicciBackground (I := I) (M := M) D a b) (lambda : ℝ) (hlambda : 0 < lambda) :
    letI := A.charts
    letI := A.smoothManifold
    IsSolutionOn (I := I.prod 𝓘(ℝ, ℝ)) (M := M × Surgery.Topology.Circle)
      (show SolutionOn (I := I.prod 𝓘(ℝ, ℝ)) (M := M × Surgery.Topology.Circle) D from
        ⟨quotientProductFamily A B.family lambda hlambda⟩) := by
  let := A.charts
  let := A.smoothManifold
  have hcover : IsSolutionOn (I := I.prod 𝓘(ℝ, ℝ)) (M := M × ℝ)
      ((show SolutionOn (I := I) (M := M) D from ⟨B.family⟩).prod
        (SolutionOn.const (DifferentialGeometry.scaleMetric (I := 𝓘(ℝ, ℝ)) (lambda ^ 2)
          (pow_pos hlambda 2) (DifferentialGeometry.euclideanMetric (E := ℝ))) D)) :=
    isSolutionOn_prod_scaleMetric_euclideanMetric
      (show SolutionOn (I := I) (M := M) D from ⟨B.family⟩) B.equation (lambda ^ 2)
      (pow_pos hlambda 2)
  have hdescent := IsSolutionOn.of_surjective_localPullMetric_of_metricFamilySmoothOn hcover
    (productCoverProjection (M := M)) (isLocalDiffeomorph_productCoverProjection A)
    (surjective_productCoverProjection (M := M))
    (fun t : ℝ => quotientProductMetric A (B.family.metric t) lambda hlambda)
    (metricFamilySmoothOn_quotientProductMetric A B.toSmoothMetricWindow lambda hlambda)
    (fun t _ => quotientProductMetric_localPull A (B.family.metric t) lambda hlambda)
  simpa only [quotientProductFamily] using hdescent

theorem exists_ricciBackground_quotientProduct (A : QuotientProductAtlas I M) [I.Boundaryless]
    [SigmaCompactSpace M] [T2Space M] {D : RealTimeInterval} {a b : ℝ}
    (B : RicciBackground (I := I) (M := M) D a b) (lambda : ℝ) (hlambda : 0 < lambda) :
    letI := A.charts
    letI := A.smoothManifold
    ∃ Bhat : RicciBackground (I := I.prod 𝓘(ℝ, ℝ))
        (M := M × Surgery.Topology.Circle) D a b,
      Bhat.family = quotientProductFamily A B.family lambda hlambda ∧
      Bhat.B₀ = B.B₀ ∧ Bhat.B₁ = B.B₁ ∧ Bhat.B₂ = B.B₂ :=
  exists_ricciBackground_quotientProduct_of_isSolutionOn A B lambda hlambda
    (isSolutionOn_quotientProductFamily A B lambda hlambda)

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
