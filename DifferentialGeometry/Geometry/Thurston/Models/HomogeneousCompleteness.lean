import DifferentialGeometry.Geometry.Thurston.Models.CoordinateHomogeneity
import DifferentialGeometry.Geometry.Metric.PullbackCompleteness
import Mathlib.Topology.Compactness.LocallyCompact

set_option autoImplicit false
noncomputable section
open Bundle Manifold DifferentialGeometry Set Filter
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace GC.Geometry

theorem completeSpace_of_transitiveIsometries {X : Type*} [EMetricSpace X]
    [LocallyCompactSpace X] (o : X)
    (h : ∀ x : X, ∃ e : X ≃ᵢ X, e o = x) : CompleteSpace X := by
  obtain ⟨K, hK, ho⟩ := exists_compact_mem_nhds o
  obtain ⟨ε, hε, hball⟩ := EMetric.mem_nhds_iff.mp ho
  refine ⟨fun {f} hf => ?_⟩
  obtain ⟨t, ht, hsmall⟩ := (EMetric.cauchy_iff.mp hf).2 ε hε
  obtain ⟨x, hx⟩ := hf.1.nonempty_of_mem ht
  obtain ⟨e, he⟩ := h x
  have himage : e '' K ∈ f := mem_of_superset ht (by
    intro y hy
    refine ⟨e.symm y, hball ?_, e.apply_symm_apply y⟩
    change edist (e.symm y) o < ε
    rw [← e.edist_eq, e.apply_symm_apply, he]
    exact hsmall y hy x hx)
  obtain ⟨y, _, hy⟩ := (hK.image e.continuous).isComplete f hf
    (le_principal_iff.mpr himage)
  exact ⟨y, hy⟩

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [LocallyCompactSpace M]
  [Nonempty M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in

theorem homogeneousMetric_complete (g : SmoothRiemannianMetric I M)
    (hg : HomogeneousMetric g) : RiemannianMetricComplete g := by
  let : IsManifold I 1 M := IsManifold.of_le (I := I) (M := M)
    (n := ∞) (by norm_num)
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let : T3Space M := inferInstance
  refine ⟨?_⟩
  let : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let o : M := Classical.choice inferInstance
  apply completeSpace_of_transitiveIsometries o
  intro x
  obtain ⟨f, hfo, hf⟩ := hg o x
  have hmetric : Diffeomorph.pullbackMetricCross g f = g := by
    apply SmoothRiemannianMetric.ext_inner
    intro p v w
    rw [Diffeomorph.pullbackMetricCross_inner]
    exact hf p v w
  refine ⟨{ toEquiv := f.toEquiv, isometry_toFun := ?_ }, hfo⟩
  intro p q
  change riemannianEDistOf g (f p) (f q) = riemannianEDistOf g p q
  rw [← riemannianEDistOf_pullbackMetricCross g f, hmetric]

theorem coordinateModelMetric_complete (k : CoordinateModel) :
    RiemannianMetricComplete (coordinateModelMetric k) :=
  homogeneousMetric_complete _ (coordinateModelMetric_homogeneous k)

theorem coordinateModels_have_complete_atlases (k : CoordinateModel) :
    CompleteModelAtlas (coordinateModelMetric k) (coordinateModelMetric k) :=
  ⟨coordinateModelMetric_complete k, ModelAtlas.refl _⟩

def CoordinateModel.thurstonModel : CoordinateModel → ThurstonModel
  | .hyperbolic => .hyperbolic
  | .hyperbolicProduct => .hyperbolicProduct
  | .universalSL2 => .universalSL2
  | .nil => .nil
  | .sol => .sol

theorem coordinateModelMetric_hasThurstonAtlas (k : CoordinateModel) :
    HasThurstonAtlas (coordinateModelMetric k) k.thurstonModel := by
  cases k <;> exact coordinateModelMetric_atlas _

def coordinateGeometricStructure (k : CoordinateModel) (hk : k ≠ .hyperbolic) :
    GeometricStructure (𝓡 3) ModelCoordinates where
  model := k.thurstonModel
  metric := coordinateModelMetric k
  complete := coordinateModelMetric_complete k
  atlas := coordinateModelMetric_hasThurstonAtlas k
  hyperbolic_finite_volume := by cases k <;> simp_all [CoordinateModel.thurstonModel]

end GC.Geometry
