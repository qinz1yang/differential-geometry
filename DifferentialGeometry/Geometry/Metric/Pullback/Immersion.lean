import DifferentialGeometry.Geometry.Metric.Basic
import DifferentialGeometry.Bundle.ClmSectionSmooth
import DifferentialGeometry.Analysis.FiniteDimensional.Coercivity
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Analysis.Normed.Operator.Bilinear

namespace DifferentialGeometry

open Bundle
open scoped Manifold ContDiff

noncomputable section

variable {E F H G M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]

def SmoothRiemannianMetric.pullbackInner (g : SmoothRiemannianMetric J N)
    (f : M → N) (x : M) : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  (ContinuousLinearMap.precomp ℝ (mfderiv I J f x)).comp
    ((g.inner (f x)).comp (mfderiv I J f x))

omit [IsManifold I ∞ M] in
@[simp]
theorem SmoothRiemannianMetric.pullbackInner_apply (g : SmoothRiemannianMetric J N)
    (f : M → N) (x : M) (v w : TangentSpace I x) :
    g.pullbackInner (I := I) f x v w =
      g.inner (f x) (mfderiv I J f x v) (mfderiv I J f x w) := rfl

omit [IsManifold I ∞ M] in
theorem SmoothRiemannianMetric.pullbackInner_pos (g : SmoothRiemannianMetric J N)
    (f : M → N) (x : M) (himm : Function.Injective (mfderiv I J f x))
    (v : TangentSpace I x) (hv : v ≠ 0) :
    0 < g.pullbackInner (I := I) f x v v := by
  apply g.pos
  exact fun hz => hv (himm (by simpa using hz))

theorem SmoothRiemannianMetric.pullbackInner_contMDiff [FiniteDimensional ℝ E] [T2Space M]
    (g : SmoothRiemannianMetric J N) (f : M → N) (hf : ContMDiff I J ∞ f) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x => (⟨x, g.pullbackInner (I := I) f x⟩ :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ))) := by
  apply cotangentCov_clmSection_smooth_aux
    (V₂ := fun x => TangentSpace I x →L[ℝ] ℝ)
  intro Y
  apply cotangentCov_clmSection_smooth_aux (V₂ := fun _ => ℝ)
  intro W
  have ht : ContMDiff I.tangent J.tangent ∞ (tangentMap I J f) :=
    hf.contMDiff_tangentMap le_rfl
  have hv := ht.comp Y.contMDiff
  have hw := ht.comp W.contMDiff
  have hg := g.contMDiff.comp hf
  have he := ContMDiff.clm_bundle_apply₂
    (E₁ := fun b : N => TangentSpace J b)
    (E₂ := fun b : N => TangentSpace J b)
    (E₃ := fun _ : N => ℝ)
    (b := f) (ψ := fun x => g.inner (f x))
    (v := fun x => mfderiv I J f x (Y x))
    (w := fun x => mfderiv I J f x (W x)) hg hv hw
  have hs : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x => g.inner (f x) (mfderiv I J f x (Y x)) (mfderiv I J f x (W x))) := by
    intro x
    have h := he x
    rw [contMDiffAt_totalSpace] at h
    exact h.2
  intro x
  rw [contMDiffAt_section]
  apply (hs x).congr_of_eventuallyEq
  filter_upwards with y
  rfl

def SmoothRiemannianMetric.pullback [FiniteDimensional ℝ E] [T2Space M]
    (g : SmoothRiemannianMetric J N) (f : M → N) (hf : ContMDiff I J ∞ f)
    (himm : ∀ x, Function.Injective (mfderiv I J f x)) : SmoothRiemannianMetric I M where
  inner := g.pullbackInner f
  symm x v w := g.symm (f x) _ _
  pos x := g.pullbackInner_pos f x (himm x)
  isVonNBounded x := by
    let B : E →L[ℝ] E →L[ℝ] ℝ := g.pullbackInner (I := I) f x
    have hp : ∀ v : E, v ≠ 0 → 0 < B v v := g.pullbackInner_pos f x (himm x)
    have hc := B.isCoercive_of_posDef hp
    change Bornology.IsVonNBounded ℝ {v : E | B v v < 1}
    exact NormedSpace.isVonNBounded_of_isBounded ℝ
      ((hc.isBounded_le 1).subset (fun v hv => show B v v ≤ 1 from le_of_lt hv))
  contMDiff := g.pullbackInner_contMDiff f hf

@[simp]
theorem SmoothRiemannianMetric.pullback_inner [FiniteDimensional ℝ E] [T2Space M]
    (g : SmoothRiemannianMetric J N) (f : M → N) (hf : ContMDiff I J ∞ f)
    (himm : ∀ x, Function.Injective (mfderiv I J f x)) (x : M) (v w : TangentSpace I x) :
    (g.pullback f hf himm).inner x v w =
      g.inner (f x) (mfderiv I J f x v) (mfderiv I J f x w) := rfl

end

end DifferentialGeometry
