import DifferentialGeometry.Geometry.Metric.Perturbation.Pointwise
import DifferentialGeometry.Geometry.Metric.Basic
import DifferentialGeometry.Geometry.Metric.PointwiseInner.Bounds
import DifferentialGeometry.Geometry.Connection.TensorNabla.Differentiability.Cotangent
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

noncomputable section

open Bundle Set IsManifold ContinuousLinearMap
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Spectral
namespace MetricRealization


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]


theorem perturbedInner_contMDiff
    [T2Space M]
    (g : SmoothRiemannianMetric I M)
    (h : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (hsmooth : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun b : M => TotalSpace.mk'
        (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun b : M => TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ)
        b (h b))) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun b : M => TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ)
        x (perturbedInner g h x)) := by
  classical
  apply contMDiff_continuousLinearMap_section_of_apply
    (V₂ := fun x : M => TangentSpace I x →L[ℝ] ℝ)
    (φ := fun x : M => perturbedInner g h x)
  intro Y
  apply contMDiff_continuousLinearMap_section_of_apply
    (V₂ := fun _ : M => ℝ)
    (φ := fun x : M => perturbedInner g h x (Y x))
  intro W
  have hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := TangentSpace I) x (Y x)) := Y.contMDiff
  have hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := TangentSpace I) x (W x)) := W.contMDiff
  have hg_scalar : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => g.inner x (Y x) (W x)) := by
    have h_total : ContMDiff I (I.prod 𝓘(ℝ, ℝ)) ∞
        (fun x : M => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ)
          x (g.inner x (Y x) (W x))) :=
      ContMDiff.clm_bundle_apply₂
        (E₁ := fun x : M => TangentSpace I x)
        (E₂ := fun x : M => TangentSpace I x)
        (E₃ := fun _ : M => ℝ)
        (b := fun x : M => x)
        (ψ := fun x : M => g.inner x)
        (v := fun x : M => Y x)
        (w := fun x : M => W x)
        g.contMDiff hY hW
    intro x
    have h_at := h_total x
    rw [contMDiffAt_totalSpace] at h_at
    exact h_at.2
  have hh_scalar : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => h x (Y x) (W x)) := by
    have h_total : ContMDiff I (I.prod 𝓘(ℝ, ℝ)) ∞
        (fun x : M => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ)
          x (h x (Y x) (W x))) :=
      ContMDiff.clm_bundle_apply₂
        (E₁ := fun x : M => TangentSpace I x)
        (E₂ := fun x : M => TangentSpace I x)
        (E₃ := fun _ : M => ℝ)
        (b := fun x : M => x)
        (ψ := fun x : M => h x)
        (v := fun x : M => Y x)
        (w := fun x : M => W x)
        hsmooth hY hW
    intro x
    have h_at := h_total x
    rw [contMDiffAt_totalSpace] at h_at
    exact h_at.2
  have h_sum_scalar : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => perturbedInner g h x (Y x) (W x)) := by
    have h_eq : (fun x : M => perturbedInner g h x (Y x) (W x))
        = fun x : M => g.inner x (Y x) (W x) + h x (Y x) (W x) := by
      funext x; rw [perturbedInner_apply]
    rw [h_eq]; exact hg_scalar.add hh_scalar
  intro x
  rw [contMDiffAt_section]
  refine (h_sum_scalar.contMDiffAt).congr_of_eventuallyEq ?_
  filter_upwards with y
  change perturbedInner g h y (Y y) (W y) =
    (trivializationAt ℝ (Bundle.Trivial M ℝ) x
      ⟨y, perturbedInner g h y (Y y) (W y)⟩).2
  rfl

noncomputable def perturbedMetric
    [T2Space M]
    (g : SmoothRiemannianMetric I M)
    (h : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (hsymm : ∀ (x : M) (v w : TangentSpace I x), h x v w = h x w v)
    (hsmooth : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun b : M => TotalSpace.mk'
        (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun b : M => TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ)
        b (h b)))
    {δ : ℝ} (hδ_lt : δ < 1) (hδ : metricCauchySchwarzBound g h δ) :
    SmoothRiemannianMetric I M where
  inner x := perturbedInner g h x
  symm x v w := perturbedInner_symm (I := I) (M := M) g h hsymm x v w
  pos x v hv := perturbedInner_pos_of_metricCauchySchwarzBound (I := I) (M := M) g h hδ_lt hδ x v hv
  isVonNBounded x := perturbedInner_isVonNBounded (I := I) (M := M) g h hδ_lt hδ x
  contMDiff := perturbedInner_contMDiff (I := I) (M := M) g h hsmooth

@[simp] lemma perturbedMetric_inner
    [T2Space M] (g : SmoothRiemannianMetric I M)
    (h : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (hsymm : ∀ (x : M) (v w : TangentSpace I x), h x v w = h x w v)
    (hsmooth : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun b : M => TotalSpace.mk'
        (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun b : M => TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ)
        b (h b)))
    {δ : ℝ} (hδ_lt : δ < 1) (hδ : metricCauchySchwarzBound g h δ) (x : M) :
    (perturbedMetric g h hsymm hsmooth hδ_lt hδ).inner x = perturbedInner g h x :=
  rfl

theorem exists_posDef_perturbation_radius
    [T2Space M] (g : SmoothRiemannianMetric I M) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (h : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ),
        (∀ (x : M) (v w : TangentSpace I x), h x v w = h x w v) →
        (ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
          (fun b : M => TotalSpace.mk'
            (E →L[ℝ] E →L[ℝ] ℝ)
            (E := fun b : M => TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ)
            b (h b))) →
        ∀ δ' : ℝ, δ' < δ → metricCauchySchwarzBound g h δ' →
          ∃ g' : SmoothRiemannianMetric I M,
            ∀ (x : M) (v w : TangentSpace I x),
              g'.inner x v w = g.inner x v w + h x v w := by
  refine ⟨1, one_pos, ?_⟩
  intro h hsymm hsmooth δ' hδ'_lt hδ'
  refine ⟨perturbedMetric g h hsymm hsmooth hδ'_lt hδ', ?_⟩
  intro x v w
  rw [perturbedMetric_inner, perturbedInner_apply]

end MetricRealization
end Spectral
end Analysis
end DifferentialGeometry

end
