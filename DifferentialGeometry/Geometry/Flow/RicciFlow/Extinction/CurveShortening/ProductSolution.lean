import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProductSliceSmoothness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProductCoveringDerivative
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Naturality.PullbackLocalIso

noncomputable section
open Bundle Manifold Set
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [I.Boundaryless]

theorem map_Ds_eq (c : ProductCurve M) (A : QuotientProductAtlas I M)
    (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ) (hlambda : 0 < lambda)
    {J : Set ℝ} (hc : c.SmoothOn (I := I) J) (t : ℝ) (ht : t ∈ J)
    (V : c.Field (I := I))
    (hV : ContMDiff 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)).tangent ∞
      (fun x => (⟨c.coverLift x t, V x t⟩ : TangentBundle (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))))
    (x : ℝ) :
    letI := A.charts
    letI := A.smoothManifold
    c.map.Ds (fun τ => quotientProductMetric A (g τ) lambda hlambda)
      (fun y τ => mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ))
        (productCoverProjection (M := M)) (c.coverLift y τ) (V y τ)) x t =
      mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ))
        (productCoverProjection (M := M)) (c.coverLift x t) (c.Ds g lambda V x t) := by
  let _ := A.charts
  let _ := A.smoothManifold
  have hfield := mdifferentiableAt_tangentField_iff.mp
    (hV.contMDiffAt.mdifferentiableAt (by simp) (x := x))
  have hn := covDerivAlong_map_of_eq_localPullMetric
    (quotientProductMetric A (g t) lambda hlambda)
    (isLocalDiffeomorph_productCoverProjection A) (coverProductMetric (g t) lambda hlambda)
    (quotientProductMetric_localPull A (g t) lambda hlambda)
    (fun y => c.coverLift y t) (fun y => V y t) x
    ((c.coverLift_space_contMDiff hc t ht).contMDiffAt) hfield.2
  rw [c.cover_covariantDerivative_of_boundaryless g lambda hlambda t V hV x] at hn
  have hcurve : (fun y => productCoverProjection (M := M) (c.coverLift y t)) =
      (fun y => c.map.lift y t) := funext (fun y => c.coverProjection_lift y t)
  rw [hcurve] at hn
  dsimp only [CurveMap.Ds, ProductCurve.Ds]
  rw [c.map_speed_eq A g lambda hlambda hc x t ht]
  exact (congrArg (fun z => (c.speed g lambda x t)⁻¹ • z) hn.symm).trans
    (ContinuousLinearMap.map_smul
      (mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ))
        (productCoverProjection (M := M)) (c.coverLift x t))
      ((c.speed g lambda x t)⁻¹) (c.Dx g V x t)).symm

theorem map_curvatureVector_eq_of_immersed (c : ProductCurve M) (A : QuotientProductAtlas I M)
    (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ) (hlambda : 0 < lambda)
    {J : Set ℝ} (hc : c.SmoothOn (I := I) J) (hi : c.ImmersedOn (I := I) J)
    (x t : ℝ) (ht : t ∈ J) :
    letI := A.charts
    letI := A.smoothManifold
    c.map.curvatureVector (fun τ => quotientProductMetric A (g τ) lambda hlambda) x t =
      mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ))
        (productCoverProjection (M := M)) (c.coverLift x t) (c.curvatureVector g lambda x t) := by
  let _ := A.charts
  let _ := A.smoothManifold
  have hU : (c.unitTangent g lambda).SmoothOn (I := I) J :=
    fun r hr => c.cover_unitTangent_contMDiff g lambda hlambda hc hi r hr
  exact (c.map_curvatureVector_eq (I := I) A g lambda hlambda hc hU x t ht).symm

theorem map_curvatureSq_eq (c : ProductCurve M) (A : QuotientProductAtlas I M)
    (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ) (hlambda : 0 < lambda)
    {J : Set ℝ} (hc : c.SmoothOn (I := I) J) (hi : c.ImmersedOn (I := I) J)
    (x t : ℝ) (ht : t ∈ J) :
    letI := A.charts
    letI := A.smoothManifold
    c.map.curvatureSq (fun τ => quotientProductMetric A (g τ) lambda hlambda) x t =
      c.curvatureSq g lambda x t := by
  let _ := A.charts
  let _ := A.smoothManifold
  have hinner := (localPullMetric_inner (quotientProductMetric A (g t) lambda hlambda)
    (productCoverProjection (M := M)) (isLocalDiffeomorph_productCoverProjection A)
    (c.coverLift x t) (c.curvatureVector g lambda x t) (c.curvatureVector g lambda x t)).symm
  rw [quotientProductMetric_localPull A (g t) lambda hlambda] at hinner
  have hcover := coverProductMetric_inner (g t) lambda hlambda (c.coverLift x t)
    (c.curvatureVector g lambda x t) (c.curvatureVector g lambda x t)
  dsimp only [CurveMap.curvatureSq, CurveMap.normSq, ProductCurve.curvatureSq, ProductCurve.normSq]
  rw [c.map_curvatureVector_eq_of_immersed A g lambda hlambda hc hi x t ht]
  have he (v : E × ℝ) :
      (quotientProductMetric A (g t) lambda hlambda).inner
        (productCoverProjection (M := M) (c.coverLift x t)) v v =
      (quotientProductMetric A (g t) lambda hlambda).inner (c.map.lift x t) v v :=
    congrArg (fun q => (quotientProductMetric A (g t) lambda hlambda).inner q v v)
      (c.coverProjection_lift x t)
  exact (he _).symm.trans (hinner.trans hcover)

theorem map_ds_eq (c : ProductCurve M) (A : QuotientProductAtlas I M)
    (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ) (hlambda : 0 < lambda)
    {J : Set ℝ} (hc : c.SmoothOn (I := I) J) (f : ℝ → ℝ → ℝ)
    (x t : ℝ) (ht : t ∈ J) :
    letI := A.charts
    letI := A.smoothManifold
    c.map.ds (fun τ => quotientProductMetric A (g τ) lambda hlambda) f x t =
      c.ds g lambda f x t := by
  let _ := A.charts
  let _ := A.smoothManifold
  dsimp only [CurveMap.ds, ProductCurve.ds]
  rw [c.map_speed_eq A g lambda hlambda hc x t ht]

theorem map_length_eq (c : ProductCurve M) (A : QuotientProductAtlas I M)
    (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ) (hlambda : 0 < lambda)
    {J : Set ℝ} (hc : c.SmoothOn (I := I) J) (t : ℝ) (ht : t ∈ J) :
    letI := A.charts
    letI := A.smoothManifold
    c.map.length (fun τ => quotientProductMetric A (g τ) lambda hlambda) t =
      c.length g lambda t := by
  let _ := A.charts
  let _ := A.smoothManifold
  simp only [CurveMap.length, CurveMap.integral, ProductCurve.length, ProductCurve.integral, one_mul]
  exact intervalIntegral.integral_congr (fun x _ => c.map_speed_eq A g lambda hlambda hc x t ht)

theorem map_totalCurvature_eq (c : ProductCurve M) (A : QuotientProductAtlas I M)
    (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ) (hlambda : 0 < lambda)
    {J : Set ℝ} (hc : c.SmoothOn (I := I) J) (hi : c.ImmersedOn (I := I) J)
    (t : ℝ) (ht : t ∈ J) :
    letI := A.charts
    letI := A.smoothManifold
    c.map.totalCurvature (fun τ => quotientProductMetric A (g τ) lambda hlambda) t =
      c.totalCurvature g lambda t := by
  let _ := A.charts
  let _ := A.smoothManifold
  simp only [CurveMap.totalCurvature, CurveMap.integral, ProductCurve.totalCurvature, ProductCurve.integral]
  apply intervalIntegral.integral_congr
  intro x _
  simp only [CurveMap.curvature, ProductCurve.curvature,
    c.map_curvatureSq_eq A g lambda hlambda hc hi x t ht, c.map_speed_eq A g lambda hlambda hc x t ht]

theorem isSolutionOn_map (c : ProductCurve M) (A : QuotientProductAtlas I M)
    (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ) (hlambda : 0 < lambda)
    {J : Set ℝ} (hJ : UniqueDiffOn ℝ J) (hc : c.IsSolutionOn g lambda J) :
    letI := A.charts
    letI := A.smoothManifold
    c.map.IsSolutionOn (fun τ => quotientProductMetric A (g τ) lambda hlambda) J := by
  let _ := A.charts
  let _ := A.smoothManifold
  refine ⟨c.smoothOn_map A hc.smooth, (c.map_immersedOn_iff A hc.smooth).mpr hc.immersed, ?_⟩
  intro x t ht
  rw [c.map_velocity_eq A J hc.smooth x t ht ((hJ t ht).uniqueMDiffWithinAt),
    c.map_curvatureVector_eq_of_immersed A g lambda hlambda hc.smooth hc.immersed x t ht, hc.equation x t ht]

theorem map_iteratedDs_curvatureVector_eq (c : ProductCurve M) (A : QuotientProductAtlas I M)
    (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ) (hlambda : 0 < lambda)
    {J : Set ℝ} (hc : c.SmoothOn (I := I) J) (hi : c.ImmersedOn (I := I) J)
    (t : ℝ) (ht : t ∈ J) (m : ℕ) (x : ℝ) :
    letI := A.charts
    letI := A.smoothManifold
    let ghat := fun τ => quotientProductMetric A (g τ) lambda hlambda
    c.map.iteratedDs ghat m (c.map.curvatureVector ghat) x t =
      mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ))
        (productCoverProjection (M := M)) (c.coverLift x t)
        (c.iteratedDs g lambda m (c.curvatureVector g lambda) x t) := by
  let _ := A.charts
  let _ := A.smoothManifold
  dsimp only
  induction m generalizing x with
  | zero => exact c.map_curvatureVector_eq_of_immersed A g lambda hlambda hc hi x t ht
  | succ m ih =>
    have hn := c.map_Ds_eq A g lambda hlambda hc t ht
      (c.iteratedDs g lambda m (c.curvatureVector g lambda))
      (c.cover_iteratedDs_contMDiff g lambda hlambda hc hi (c.curvatureVector g lambda) t ht
        (c.cover_curvatureVector_contMDiff g lambda hlambda hc hi t ht) m) x
    simp only [CurveMap.iteratedDs, ProductCurve.iteratedDs, Function.iterate_succ_apply']
    simp only [CurveMap.Ds, CurveMap.Dx] at hn ⊢
    erw [funext ih]
    exact hn

theorem map_iteratedDs_curvature_normSq (c : ProductCurve M) (A : QuotientProductAtlas I M)
    (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ) (hlambda : 0 < lambda)
    {J : Set ℝ} (hc : c.SmoothOn (I := I) J) (hi : c.ImmersedOn (I := I) J)
    (x t : ℝ) (ht : t ∈ J) (m : ℕ) :
    letI := A.charts
    letI := A.smoothManifold
    let ghat := fun τ => quotientProductMetric A (g τ) lambda hlambda
    c.map.normSq ghat (c.map.iteratedDs ghat m (c.map.curvatureVector ghat)) x t =
      c.normSq g lambda (c.iteratedDs g lambda m (c.curvatureVector g lambda)) x t := by
  let _ := A.charts
  let _ := A.smoothManifold
  dsimp only
  let V := c.iteratedDs g lambda m (c.curvatureVector g lambda)
  have hinner := (localPullMetric_inner (quotientProductMetric A (g t) lambda hlambda)
    (productCoverProjection (M := M)) (isLocalDiffeomorph_productCoverProjection A)
    (c.coverLift x t) (V x t) (V x t)).symm
  rw [quotientProductMetric_localPull A (g t) lambda hlambda] at hinner
  have hcover := coverProductMetric_inner (g t) lambda hlambda (c.coverLift x t) (V x t) (V x t)
  dsimp only [CurveMap.normSq, ProductCurve.normSq]
  rw [c.map_iteratedDs_curvatureVector_eq A g lambda hlambda hc hi t ht m x]
  have he (v : E × ℝ) :
      (quotientProductMetric A (g t) lambda hlambda).inner
        (productCoverProjection (M := M) (c.coverLift x t)) v v =
      (quotientProductMetric A (g t) lambda hlambda).inner (c.map.lift x t) v v :=
    congrArg (fun q => (quotientProductMetric A (g t) lambda hlambda).inner q v v)
      (c.coverProjection_lift x t)
  exact (he _).symm.trans (hinner.trans hcover)


end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve
