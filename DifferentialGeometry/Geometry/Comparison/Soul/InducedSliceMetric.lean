import DifferentialGeometry.Geometry.Comparison.Soul.NormalSplitting
import DifferentialGeometry.Geometry.Metric.Construction.Existence
import DifferentialGeometry.Bundle.ContinuousLinearMapSection.Basic
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Geometry.Topology

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {S : Set M} {d : ℕ}

private def inducedSliceInner (g : SmoothRiemannianMetric I M)
    (hS : IsEmbeddedSlice I d S) (p : S) :
    let _ := embeddedSliceChartedSpace hS
    TangentSpace 𝓘(ℝ, Fin d → ℝ) p →L[ℝ]
      TangentSpace 𝓘(ℝ, Fin d → ℝ) p →L[ℝ] ℝ := by
  let _ := embeddedSliceChartedSpace hS
  let L := mfderiv 𝓘(ℝ, Fin d → ℝ) I (Subtype.val : S → M) p
  exact (ContinuousLinearMap.precomp ℝ L).comp ((g.inner p.1).comp L)

private theorem inducedSliceInner_apply (g : SmoothRiemannianMetric I M)
    (hS : IsEmbeddedSlice I d S) (p : S) :
    let _ := embeddedSliceChartedSpace hS
    ∀ u v : TangentSpace 𝓘(ℝ, Fin d → ℝ) p,
      inducedSliceInner g hS p u v =
        g.inner p.1
          (mfderiv 𝓘(ℝ, Fin d → ℝ) I (Subtype.val : S → M) p u)
          (mfderiv 𝓘(ℝ, Fin d → ℝ) I (Subtype.val : S → M) p v) := by
  let _ := embeddedSliceChartedSpace hS
  change ∀ u v : TangentSpace 𝓘(ℝ, Fin d → ℝ) p,
    inducedSliceInner g hS p u v =
      g.inner p.1
        (mfderiv 𝓘(ℝ, Fin d → ℝ) I (Subtype.val : S → M) p u)
        (mfderiv 𝓘(ℝ, Fin d → ℝ) I (Subtype.val : S → M) p v)
  intro u v
  rfl

private theorem inducedSliceInner_pos (g : SmoothRiemannianMetric I M)
    (hS : IsEmbeddedSlice I d S) (p : S) :
    let _ := embeddedSliceChartedSpace hS
    ∀ u : TangentSpace 𝓘(ℝ, Fin d → ℝ) p,
      u ≠ 0 → 0 < inducedSliceInner g hS p u u := by
  let _ := embeddedSliceChartedSpace hS
  change ∀ u : TangentSpace 𝓘(ℝ, Fin d → ℝ) p,
    u ≠ 0 → 0 < inducedSliceInner g hS p u u
  intro u hu
  rw [inducedSliceInner_apply]
  apply g.pos p.1
  intro hzero
  apply hu
  apply embeddedSlice_inclusion_mfderiv_injective hS p
  rw [map_zero]
  exact hzero

private theorem inclusion_derivative_section_contMDiff
    (hS : IsEmbeddedSlice I d S) :
    let _ := embeddedSliceChartedSpace hS
    let _ := embeddedSlice_isManifold hS
    ∀ (Y : ∀ p : S, TangentSpace 𝓘(ℝ, Fin d → ℝ) p),
      ContMDiff 𝓘(ℝ, Fin d → ℝ)
        (ModelWithCorners.prod 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, Fin d → ℝ)) ∞
        (fun p : S => TotalSpace.mk' (Fin d → ℝ)
          (E := TangentSpace 𝓘(ℝ, Fin d → ℝ)) p (Y p)) →
      ContMDiff 𝓘(ℝ, Fin d → ℝ) (I.prod 𝓘(ℝ, E)) ∞
        (fun p : S => TotalSpace.mk' E
          (E := (TangentSpace I : M → Type _)) p.1
          (mfderiv 𝓘(ℝ, Fin d → ℝ) I (Subtype.val : S → M) p (Y p))) := by
  let _ := embeddedSliceChartedSpace hS
  let _ := embeddedSlice_isManifold hS
  dsimp only
  intro Y hY
  exact ((embeddedSlice_inclusion_contMDiff hS).contMDiff_tangentMap
    (m := ∞) (by simp)).comp hY

variable [T2Space M]

def inducedSliceMetric (g : SmoothRiemannianMetric I M)
    (hS : IsEmbeddedSlice I d S) :
    let _ := embeddedSliceChartedSpace hS
    let _ := embeddedSlice_isManifold hS
    SmoothRiemannianMetric 𝓘(ℝ, Fin d → ℝ) S := by
  classical
  let _ := embeddedSliceChartedSpace hS
  let _ := embeddedSlice_isManifold hS
  refine
    { inner := inducedSliceInner g hS
      symm := ?_
      pos := inducedSliceInner_pos g hS
      isVonNBounded := ?_
      contMDiff := ?_ }
  · intro p u v
    rw [inducedSliceInner_apply, inducedSliceInner_apply]
    exact g.symm p.1 _ _
  · intro p
    exact posDef_isVonNBounded (E := Fin d → ℝ) (inducedSliceInner g hS p)
      (inducedSliceInner_pos g hS p)
  · apply contMDiff_continuousLinearMap_section_of_apply
      (V₂ := fun p : S => TangentSpace 𝓘(ℝ, Fin d → ℝ) p →L[ℝ] ℝ)
      (φ := inducedSliceInner g hS)
    intro Y
    apply contMDiff_continuousLinearMap_section_of_apply
      (V₂ := fun _ : S => ℝ)
      (φ := fun p : S => inducedSliceInner g hS p (Y p))
    intro W
    have hv := inclusion_derivative_section_contMDiff hS (fun p => Y p) Y.contMDiff
    have hw := inclusion_derivative_section_contMDiff hS (fun p => W p) W.contMDiff
    have hg : ContMDiff 𝓘(ℝ, Fin d → ℝ)
        (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
        (fun p : S => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
          (E := fun q : M => TangentSpace I q →L[ℝ] TangentSpace I q →L[ℝ] ℝ)
          p.1 (g.inner p.1)) :=
      g.contMDiff.comp (embeddedSlice_inclusion_contMDiff hS)
    have htotal : ContMDiff 𝓘(ℝ, Fin d → ℝ) (I.prod 𝓘(ℝ, ℝ)) ∞
        (fun p : S => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) p.1
          (g.inner p.1
            (mfderiv 𝓘(ℝ, Fin d → ℝ) I (Subtype.val : S → M) p (Y p))
            (mfderiv 𝓘(ℝ, Fin d → ℝ) I (Subtype.val : S → M) p (W p)))) :=
      ContMDiff.clm_bundle_apply₂
        (E₁ := fun q : M => TangentSpace I q)
        (E₂ := fun q : M => TangentSpace I q)
        (E₃ := fun _ : M => ℝ)
        (b := fun p : S => p.1)
        (ψ := fun p : S => g.inner p.1)
        (v := fun p : S =>
          mfderiv 𝓘(ℝ, Fin d → ℝ) I (Subtype.val : S → M) p (Y p))
        (w := fun p : S =>
          mfderiv 𝓘(ℝ, Fin d → ℝ) I (Subtype.val : S → M) p (W p))
        hg hv hw
    have hscalar : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞
        (fun p : S => inducedSliceInner g hS p (Y p) (W p)) := by
      have heq : (fun p : S => inducedSliceInner g hS p (Y p) (W p)) =
          fun p : S => g.inner p.1
            (mfderiv 𝓘(ℝ, Fin d → ℝ) I (Subtype.val : S → M) p (Y p))
            (mfderiv 𝓘(ℝ, Fin d → ℝ) I (Subtype.val : S → M) p (W p)) := by
        funext p
        exact inducedSliceInner_apply g hS p (Y p) (W p)
      rw [heq]
      intro p
      have hp := htotal p
      rw [contMDiffAt_totalSpace] at hp
      exact hp.2
    intro p
    rw [contMDiffAt_section]
    refine hscalar.contMDiffAt.congr_of_eventuallyEq ?_
    filter_upwards with q
    rfl

@[simp] theorem inducedSliceMetric_inner (g : SmoothRiemannianMetric I M)
    (hS : IsEmbeddedSlice I d S) (p : S) :
    let _ := embeddedSliceChartedSpace hS
    let _ := embeddedSlice_isManifold hS
    ∀ u v : TangentSpace 𝓘(ℝ, Fin d → ℝ) p,
      (inducedSliceMetric g hS).inner p u v =
        g.inner p.1
          (mfderiv 𝓘(ℝ, Fin d → ℝ) I (Subtype.val : S → M) p u)
          (mfderiv 𝓘(ℝ, Fin d → ℝ) I (Subtype.val : S → M) p v) := by
  let _ := embeddedSliceChartedSpace hS
  let _ := embeddedSlice_isManifold hS
  change ∀ u v : TangentSpace 𝓘(ℝ, Fin d → ℝ) p,
    (inducedSliceMetric g hS).inner p u v =
      g.inner p.1
        (mfderiv 𝓘(ℝ, Fin d → ℝ) I (Subtype.val : S → M) p u)
        (mfderiv 𝓘(ℝ, Fin d → ℝ) I (Subtype.val : S → M) p v)
  intro u v
  exact inducedSliceInner_apply g hS p u v

end DifferentialGeometry.Geometry.Topology
