import DifferentialGeometry.Geometry.Metric.Product
import DifferentialGeometry.Geometry.Operator.Gradient.Basic
import Mathlib.Geometry.Manifold.Riemannian.Basic

noncomputable section
open Bundle Manifold
open scoped Manifold ContDiff
open DifferentialGeometry DifferentialGeometry.Geometry.Operator

namespace Poincare.Geometry.Metric

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

private def lineMetric : SmoothRiemannianMetric 𝓘(ℝ) ℝ where
  inner := (riemannianMetricVectorSpace ℝ).inner
  symm := (riemannianMetricVectorSpace ℝ).symm
  pos := (riemannianMetricVectorSpace ℝ).pos
  isVonNBounded := (riemannianMetricVectorSpace ℝ).isVonNBounded
  contMDiff := (riemannianMetricVectorSpace ℝ).contMDiff.of_le le_top

def cylinderMetric (g : SmoothRiemannianMetric I M) :
    SmoothRiemannianMetric (I.prod 𝓘(ℝ)) (M × ℝ) := g.prod lineMetric

@[simp] theorem cylinderMetric_inner (g : SmoothRiemannianMetric I M) (x : M × ℝ)
    (v w : TangentSpace (I.prod 𝓘(ℝ)) x) :
    (cylinderMetric g).inner x v w = g.inner x.1 v.1 w.1 + v.2 * w.2 := by
  rw [cylinderMetric, SmoothRiemannianMetric.prod_inner]
  change _ + w.2 * v.2 = _
  rw [mul_comm w.2 v.2]

def cylinderAxis (x : M × ℝ) : TangentSpace (I.prod 𝓘(ℝ)) x := (0, 1)

omit [FiniteDimensional ℝ E] [T2Space M] in
theorem contMDiff_cylinderAxis :
    ContMDiff (I.prod 𝓘(ℝ)) (I.prod 𝓘(ℝ)).tangent ∞
      (fun x : M × ℝ ↦ (⟨x, cylinderAxis x⟩ : TangentBundle (I.prod 𝓘(ℝ)) (M × ℝ))) := by
  have h0 : ContMDiff I I.tangent ∞
      (fun x : M ↦ (⟨x, 0⟩ : TangentBundle I M)) := contMDiff_zeroSection ℝ (TangentSpace I)
  have h1 : ContMDiff 𝓘(ℝ) 𝓘(ℝ).tangent ∞
      (fun t : ℝ ↦ (⟨t, 1⟩ : TangentBundle 𝓘(ℝ) ℝ)) := by
    intro t
    rw [contMDiffAt_section]
    convert (contMDiffAt_const (I := 𝓘(ℝ)) (I' := 𝓘(ℝ)) (c := (1 : ℝ)) (x := t)) using 1
    funext s
    simp only [TangentBundle.trivializationAt_apply, mfld_simps]
    change (fderivWithin ℝ id Set.univ s) (1 : ℝ) = 1
    rw [fderivWithin_id uniqueDiffWithinAt_univ]
    rfl
  exact (contMDiff_equivTangentBundleProd_symm (I := I) (I' := 𝓘(ℝ))
    (M := M) (M' := ℝ)).comp (h0.prodMap h1)

theorem cylinderMetric_axis_inner (g : SmoothRiemannianMetric I M) (x : M × ℝ)
    (v : TangentSpace (I.prod 𝓘(ℝ)) x) :
    (cylinderMetric g).inner x (cylinderAxis x) v =
      mvfderiv (I.prod 𝓘(ℝ)) Prod.snd x v := by
  rw [cylinderMetric_inner]
  have hz : g.inner x.1 (0 : TangentSpace I x.1) v.1 = 0 := by
    rw [map_zero (g.inner x.1)]
    rfl
  change g.inner x.1 (0 : TangentSpace I x.1) v.1 + (1 : ℝ) * v.2 = _
  calc
    _ = v.2 := by rw [hz]; ring
    _ = mvfderiv (I.prod 𝓘(ℝ)) Prod.snd x v := by
      change v.2 = (show ℝ from mfderiv (I.prod 𝓘(ℝ)) 𝓘(ℝ) Prod.snd x v)
      rw [mfderiv_snd]
      rfl

theorem cylinderMetric_axis_unit (g : SmoothRiemannianMetric I M) (x : M × ℝ) :
    (cylinderMetric g).inner x (cylinderAxis x) (cylinderAxis x) = 1 := by
  rw [cylinderMetric_inner]
  change g.inner x.1 (0 : TangentSpace I x.1) 0 + (1 : ℝ) * 1 = 1
  simp

theorem gradFun_height_eq_cylinderAxis (g : SmoothRiemannianMetric I M) (x : M × ℝ) :
    gradFun (cylinderMetric g) Prod.snd x = cylinderAxis x := by
  let m := cylinderMetric g
  let z := gradFun m Prod.snd x - cylinderAxis x
  have htest (v : TangentSpace (I.prod 𝓘(ℝ)) x) :
      m.inner x (gradFun m Prod.snd x) v - m.inner x (cylinderAxis x) v = 0 := by
    rw [inner_gradFun, cylinderMetric_axis_inner]
    change mvfderiv (I.prod 𝓘(ℝ)) Prod.snd x v - mvfderiv (I.prod 𝓘(ℝ)) Prod.snd x v = 0
    exact sub_self _
  have hz : m.inner x z z = 0 := by
    change m.inner x (gradFun m Prod.snd x - cylinderAxis x) z = 0
    rw [map_sub (m.inner x), sub_apply]
    exact htest z
  have he : z = 0 := by
    by_contra hn
    exact (ne_of_gt (m.pos x z hn)) hz
  exact sub_eq_zero.mp he

end Poincare.Geometry.Metric
