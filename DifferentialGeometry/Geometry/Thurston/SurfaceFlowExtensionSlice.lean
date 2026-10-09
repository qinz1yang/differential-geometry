import DifferentialGeometry.Geometry.Thurston.SurfaceFlowExtensionProduct
import DifferentialGeometry.Geometry.Metric.Family.Pullback

/-!
# Slicing the circle product

Chapter 7, surface lemma U1, route (a), step a1 (lane U1E2), tier T3 of route E2 (review 17 §3.2).
A metric `G` on `M × S¹` in the Euclidean model `circleProductModel` restricts to the slice
`i(x) = (x, θ)`: since `di(v) = (v, 0)` is injective, `i^*G` is a Riemannian metric on `M`.

* `circleSlice`, `contMDiff_circleSlice`, `mfderiv_circleSlice_apply`,
  `mfderiv_circleSlice_injective`: the slice and its differential.
* `sliceMetric`, `sliceMetric_inner`: `i^*G`, after moving `G` back to the product model.
* `sliceMetric_circleProductFlow`: the slice of the circle product flow is the surface flow.
* `metricFamilySmoothOn_sliceMetric`: slicing keeps joint smoothness of a family
  (`MetricFamilySmoothOn.pullback`, `MetricFamilySmoothOn.of_pullback`), so the slice family of a
  smooth flow on `M × S¹` is jointly smooth on the same regular times.
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow
open Bundle Set
open scoped Manifold ContDiff

namespace GC.Geometry

local notation "S1" => AddCircle (1 : ℝ)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

variable (M) in
def circleSlice (θ : S1) : M → M × S1 := fun x => (x, θ)

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] in
theorem contMDiff_circleSlice (θ : S1) :
    ContMDiff I (I.prod 𝓘(ℝ, ℝ)) ∞ (circleSlice M θ) :=
  contMDiff_id.prodMk contMDiff_const

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] in
theorem mfderiv_circleSlice_apply (θ : S1) (x : M) (v : TangentSpace I x) :
    mfderiv I (I.prod 𝓘(ℝ, ℝ)) (circleSlice M θ) x v = ((v, 0) : E × ℝ) := by
  erw [mfderiv_prodMk mdifferentiableAt_id mdifferentiableAt_const, mfderiv_id, mfderiv_const]
  rfl

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] in
theorem mfderiv_circleSlice_injective (θ : S1) (x : M) :
    Function.Injective (mfderiv I (I.prod 𝓘(ℝ, ℝ)) (circleSlice M θ) x) := by
  intro v w hvw
  rw [mfderiv_circleSlice_apply, mfderiv_circleSlice_apply] at hvw
  exact congrArg Prod.fst hvw

def sliceMetric (hdim : Module.finrank ℝ E = 2) (θ : S1)
    (G : SmoothRiemannianMetric (circleProductModel I hdim) (M × S1)) :
    SmoothRiemannianMetric I M :=
  (Diffeomorph.pullbackMetricCross G (circleProductChange I M hdim)).pullbackOfImmersion
    (circleSlice M θ) (contMDiff_circleSlice θ) (mfderiv_circleSlice_injective θ)

theorem sliceMetric_inner (hdim : Module.finrank ℝ E = 2) (θ : S1)
    (G : SmoothRiemannianMetric (circleProductModel I hdim) (M × S1)) (x : M)
    (v w : TangentSpace I x) :
    (sliceMetric hdim θ G).inner x v w =
      (Diffeomorph.pullbackMetricCross G (circleProductChange I M hdim)).inner (x, θ)
        ((v, 0) : E × ℝ) ((w, 0) : E × ℝ) := by
  rw [sliceMetric, SmoothRiemannianMetric.pullbackOfImmersion_inner, mfderiv_circleSlice_apply,
    mfderiv_circleSlice_apply]
  rfl

theorem sliceMetric_circleProductFlow (hdim : Module.finrank ℝ E = 2) (θ : S1)
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (t : ℝ) :
    sliceMetric hdim θ ((circleProductFlow hdim S).family.metric t) = S.family.metric t := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [sliceMetric_inner, circleProductFlow_metric_pullback]
  erw [SmoothRiemannianMetric.prod_inner]
  change (S.family.metric t).inner x v w + AddCircle.flatMetric.inner θ 0 0 = _
  simp

theorem metricFamilySmoothOn_sliceMetric (hdim : Module.finrank ℝ E = 2) (θ : S1)
    {D : RealTimeInterval} {G : ℝ → SmoothRiemannianMetric (circleProductModel I hdim) (M × S1)}
    (hG : MetricFamilySmoothOn D G) :
    MetricFamilySmoothOn D (fun t => sliceMetric hdim θ (G t)) :=
  (hG.pullback G (circleProductChange I M hdim)).of_pullback _ (circleSlice M θ)
    (contMDiff_circleSlice θ) (fun _ x v w =>
      SmoothRiemannianMetric.pullbackOfImmersion_inner _ _ _ _ x v w)

end GC.Geometry
