import DifferentialGeometry.Geometry.Metric.LocalRealization
import DifferentialGeometry.Geometry.Metric.Conformal.Basic
import DifferentialGeometry.Geometry.Metric.Conformal.OfContDiff

set_option autoImplicit false
noncomputable section
open Set Bundle DifferentialGeometry DifferentialGeometry.Geometry
open scoped Manifold ContDiff
namespace DifferentialGeometry.Geometry.Metric
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

structure SmoothRiemannianMetricOn (s : Set M) [FiniteDimensional ℝ E] where
  inner : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ
  symm : ∀ x ∈ s, ∀ v w : TangentSpace I x, inner x v w = inner x w v
  pos : ∀ x ∈ s, ∀ v : TangentSpace I x, v ≠ 0 → 0 < inner x v v
  contMDiffOn : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
    (fun x => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) x (inner x)) s

namespace SmoothRiemannianMetricOn
variable [FiniteDimensional ℝ E] {s : Set M}

def ofMetric (g : SmoothRiemannianMetric I M) (s : Set M) :
    SmoothRiemannianMetricOn (I := I) s where
  inner := g.inner
  symm x _ := g.symm x
  pos x _ := g.pos x
  contMDiffOn := g.contMDiff.contMDiffOn

def restrictOpen [T2Space M] (h : SmoothRiemannianMetricOn (I := I) s)
    (U : TopologicalSpace.Opens M) (hU : (U : Set M) ⊆ s) : SmoothRiemannianMetric I U where
  inner x := h.inner (x : M)
  symm x := h.symm (x : M) (hU x.2)
  pos x := h.pos (x : M) (hU x.2)
  isVonNBounded x := posDef_isVonNBounded (E := E) (h.inner (x : M))
    (h.pos (x : M) (hU x.2))
  contMDiff := contMDiff_bilinear_restrictOpen h.inner U (h.contMDiffOn.mono hU)

@[simp] theorem restrictOpen_inner [T2Space M] (h : SmoothRiemannianMetricOn (I := I) s)
    (U : TopologicalSpace.Opens M) (hU : (U : Set M) ⊆ s)
    (x : U) (v w : TangentSpace I x) :
    (h.restrictOpen U hU).inner x v w = h.inner (x : M) v w := rfl

def conformal (h : SmoothRiemannianMetricOn (I := I) s) (F : M → ℝ)
    (hF : ContMDiffOn I 𝓘(ℝ) ∞ F s) : SmoothRiemannianMetricOn (I := I) s where
  inner x := Real.exp (2 * F x) • h.inner x
  symm x hx v w := by
    simp only [smul_apply, smul_eq_mul, h.symm x hx v w]
  pos x hx v hv := by
    simpa only [smul_apply, smul_eq_mul] using mul_pos (Real.exp_pos _) (h.pos x hx v hv)
  contMDiffOn := by
    let : ∀ x : M, ContinuousAdd (TangentSpace I x →L[ℝ] ℝ) := fun x => inferInstance
    have hs : ContMDiffOn I 𝓘(ℝ) ∞ (fun x => Real.exp (2 * F x)) s :=
      Real.contDiff_exp.contMDiff.comp_contMDiffOn (contMDiffOn_const.mul hF)
    exact hs.smul_section h.contMDiffOn

@[simp] theorem conformal_inner (h : SmoothRiemannianMetricOn (I := I) s) (F : M → ℝ)
    (hF : ContMDiffOn I 𝓘(ℝ) ∞ F s) (x : M) (v w : TangentSpace I x) :
    (h.conformal F hF).inner x v w = Real.exp (2 * F x) * h.inner x v w := rfl

theorem conformal_restrictOpen [T2Space M] (h : SmoothRiemannianMetricOn (I := I) s)
    (F : M → ℝ) (hF : ContMDiffOn I 𝓘(ℝ) ∞ F s)
    (U : TopologicalSpace.Opens M) (hU : (U : Set M) ⊆ s) :
    (h.conformal F hF).restrictOpen U hU =
      conformalMetricOfContDiff (h.restrictOpen U hU) (fun x : U => F (x : M))
        (hF.comp_contMDiff (contMDiff_subtype_val (I := I) (U := U)) (fun x => hU x.2)) := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rfl

end SmoothRiemannianMetricOn
end DifferentialGeometry.Geometry.Metric
