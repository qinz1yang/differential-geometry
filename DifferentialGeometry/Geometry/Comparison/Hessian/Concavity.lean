import DifferentialGeometry.Analysis.Convex.Concavity
import DifferentialGeometry.Bundle.FiberBundleHausdorff
import DifferentialGeometry.Geometry.Comparison.Hessian.AlongGeodesic
import DifferentialGeometry.Geometry.Exponential.Intrinsic.Geodesic.Smoothness
import DifferentialGeometry.Geometry.Exponential.MinimizingGeodesic
import DifferentialGeometry.Topology.Manifold.ZeroDimensional

open Set Bundle
open scoped Manifold ContDiff

namespace DifferentialGeometry

namespace Geometry.Riemannian

open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem eq_on_geodesic_of_hessFun_nonpos_of_bddBelow
    (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hH : ∀ x, ∀ v : TangentSpace I x, hessFun g f x v v ≤ 0)
    (hbounded : BddBelow (range f))
    {c : ℝ → M} (hc : ContMDiff 𝓘(ℝ, ℝ) I ∞ c)
    (hgeo : IsGeodesic g c) (a b : ℝ) : f (c a) = f (c b) := by
  have hfc : ContDiff ℝ ∞ (f ∘ c) := contMDiff_iff_contDiff.mp (hf.comp hc)
  have hsecond (t : ℝ) : deriv (deriv (f ∘ c)) t ≤ 0 := by
    have heq := deriv2_comp_geo_on g isOpen_univ hf.contMDiffOn hc hgeo
      (t := t) (mem_univ (c t))
    change deriv (deriv (f ∘ c)) t = hessFun g f (c t)
      (mfderiv 𝓘(ℝ, ℝ) I c t 1) (mfderiv 𝓘(ℝ, ℝ) I c t 1) at heq
    rw [heq]
    exact hH _ _
  have hbound : BddBelow (range (f ∘ c)) :=
    hbounded.mono (range_comp_subset_range c f)
  exact eq_of_deriv2_nonpos_of_bddBelow (hfc.differentiable (by simp))
    ((ContDiff.iterate_deriv 1 hfc).differentiable (by simp)) hsecond hbound a b

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem eq_of_hessFun_nonpos_of_bddBelow_of_complete
    [SigmaCompactSpace M] [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M) (hcomplete : RiemannianMetricComplete g)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hH : ∀ x, ∀ v : TangentSpace I x, hessFun g f x v v ≤ 0)
    (hbounded : BddBelow (range f)) (p q : M) : f p = f q := by
  by_cases hdim : Module.finrank ℝ E = 0
  · let : Subsingleton M := subsingleton_of_preconnected_of_finrank_eq_zero I hdim
    exact congrArg f (Subsingleton.elim p q)
  let : NeZero (Module.finrank ℝ E) := ⟨hdim⟩
  let : IsManifold I 1 M := IsManifold.of_le (I := I) (M := M) (n := ∞)
    (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let : T3Space M := inferInstance
  let : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let : PseudoEMetricSpace M :=
    (EMetricSpace.ofRiemannianMetric I M).toPseudoEMetricSpace
  let : CompleteSpace M := hcomplete.complete
  let : T2Space (TangentBundle I M) := inferInstance
  have hEnorm : IsMetricNorm g := by
    intro x v
    exact tensor0SBundle_enorm_eq_riemannianBundle_enorm g x v
  obtain ⟨v, hv, -⟩ :=
    hopf_rinow_expMapIntrinsic_surjective_minimizing g hEnorm p q
  have h := eq_on_geodesic_of_hessFun_nonpos_of_bddBelow g hf hH hbounded
    (intrinsicGeodesic_contMDiff g hEnorm p v)
    (intrinsicGeodesic_isGeodesic g hEnorm p v) 0 1
  simpa only [intrinsicGeodesic_zero, ← expMapIntrinsic_def, hv] using h

theorem eq_of_hessFun_nonpos_of_positive_of_complete
    [SigmaCompactSpace M] [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M) (hcomplete : RiemannianMetricComplete g)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hH : ∀ x, ∀ v : TangentSpace I x, hessFun g f x v v ≤ 0)
    (hpos : ∀ x, 0 < f x) (p q : M) : f p = f q := by
  apply eq_of_hessFun_nonpos_of_bddBelow_of_complete g hcomplete hf hH ?_ p q
  refine ⟨0, ?_⟩
  rintro _ ⟨x, rfl⟩
  exact (hpos x).le

end Geometry.Riemannian

end DifferentialGeometry
