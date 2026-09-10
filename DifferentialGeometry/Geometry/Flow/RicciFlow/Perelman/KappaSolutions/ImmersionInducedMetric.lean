import DifferentialGeometry.Geometry.Metric.Construction.Existence
import DifferentialGeometry.Geometry.Metric.Basic
import DifferentialGeometry.Bundle.ContinuousLinearMapSection.Basic
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.Immersion
import Mathlib.Geometry.Manifold.LocalDiffeomorph

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Manifold Set
open scoped Topology ContDiff Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]

omit [IsManifold I ∞ M] [IsManifold J ∞ N] in
theorem immersionAt_mfderiv_injective [I.Boundaryless]
    {f : M → N} {x : M} (hf : IsImmersionAt I J ∞ f x) :
    Function.Injective (mfderiv I J f x) := by
  let h := hf.isImmersionAtOfComplement_complement
  let P : F →L[ℝ] E :=
    (ContinuousLinearMap.fst ℝ E hf.complement).comp h.equiv.symm.toContinuousLinearMap
  let d : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞ :=
    { toPartialEquiv := h.domChart.extend I
      open_source := h.domChart.isOpen_extend_source
      open_target := h.domChart.isOpen_extend_target
      contMDiffOn_toFun := by
        simpa only [OpenPartialHomeomorph.extend_source] using
          h.domChart.contMDiffOn_extend h.domChart_mem_maximalAtlas
      contMDiffOn_invFun := by
        have hsymm : ((h.domChart.extend I).symm : E → M) =
            (h.domChart.extend I).invFun := rfl
        rw [← hsymm]
        simpa only [OpenPartialHomeomorph.extend_target'] using
          contMDiffOn_extend_symm h.domChart_mem_maximalAtlas }
  have hx : x ∈ d.source := by
    change x ∈ (h.domChart.extend I).source
    rw [OpenPartialHomeomorph.extend_source]
    exact h.mem_domChart_source
  have hd : Function.Injective (mfderiv I 𝓘(ℝ, E) (h.domChart.extend I) x) :=
    ((d.isLocalDiffeomorphAt I 𝓘(ℝ, E) ∞ hx).mfderivToContinuousLinearEquiv
      (by simp)).injective
  have heq : (fun y : M => P (h.codChart.extend J (f y))) =ᶠ[𝓝 x]
      (h.domChart.extend I) := by
    filter_upwards [h.domChart.open_source.mem_nhds h.mem_domChart_source] with y hy
    have hy' : y ∈ (h.domChart.extend I).source := by
      rwa [OpenPartialHomeomorph.extend_source]
    have hchart := h.writtenInCharts ((h.domChart.extend I).map_source hy')
    dsimp only [Function.comp_apply] at hchart
    rw [h.domChart.extend_left_inv hy] at hchart
    rw [hchart]
    change (h.equiv.symm (h.equiv (h.domChart.extend I y, 0))).1 = _
    simp only [ContinuousLinearEquiv.symm_apply_apply]
  have hfD : MDifferentiableAt I J f x := h.contMDiffAt.mdifferentiableAt (by simp)
  have hc : MDifferentiableAt J 𝓘(ℝ, F) (h.codChart.extend J) (f x) :=
    (h.codChart.contMDiffAt_extend h.codChart_mem_maximalAtlas
      h.mem_codChart_source).mdifferentiableAt (by simp)
  have hP : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, E) P
      (h.codChart.extend J (f x)) := by
    have hPsmooth : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ P := P.contDiff.contMDiff
    exact hPsmooth.mdifferentiableAt (by simp)
  have hcomp := mfderiv_comp x hP (hc.comp x hfD)
  rw [mfderiv_comp x hc hfD] at hcomp
  have hder : mfderiv I 𝓘(ℝ, E) (fun y : M => P (h.codChart.extend J (f y))) x =
      mfderiv I 𝓘(ℝ, E) (h.domChart.extend I) x := heq.mfderiv_eq
  change mfderiv I 𝓘(ℝ, E) (P ∘ (h.codChart.extend J) ∘ f) x = _ at hder
  rw [hcomp] at hder
  intro v w hvw
  apply hd
  have hv := congrArg (fun L : E →L[ℝ] E => L v) hder
  have hw := congrArg (fun L : E →L[ℝ] E => L w) hder
  apply hv.symm.trans
  apply Eq.trans _ hw
  exact congrArg (fun z : TangentSpace J (f x) =>
    mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) P (h.codChart.extend J (f x))
      (mfderiv J 𝓘(ℝ, F) (h.codChart.extend J) (f x) z)) hvw

private def immersionInner (g : SmoothRiemannianMetric J N) (f : M → N) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  let L := mfderiv I J f x
  (ContinuousLinearMap.precomp ℝ L).comp ((g.inner (f x)).comp L)

omit [IsManifold I ∞ M] in
private theorem immersionInner_apply (g : SmoothRiemannianMetric J N)
    (f : M → N) (x : M) (v w : TangentSpace I x) :
    immersionInner g f x v w = g.inner (f x) (mfderiv I J f x v) (mfderiv I J f x w) := rfl

omit [IsManifold I ∞ M] in
private theorem immersionInner_pos [I.Boundaryless] (g : SmoothRiemannianMetric J N)
    {f : M → N} (hf : IsImmersion I J ∞ f) (x : M)
    (v : TangentSpace I x) (hv : v ≠ 0) : 0 < immersionInner g f x v v := by
  rw [immersionInner_apply]
  apply g.pos (f x)
  intro hzero
  apply hv
  apply immersionAt_mfderiv_injective (hf.isImmersionAt x)
  rw [map_zero]
  exact hzero

private theorem immersion_tangent_section_contMDiff
    {f : M → N} (hf : IsImmersion I J ∞ f)
    (Y : ∀ x : M, TangentSpace I x)
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := TangentSpace I) x (Y x))) :
    ContMDiff I (J.prod 𝓘(ℝ, F)) ∞
      (fun x : M => TotalSpace.mk' F (E := (TangentSpace J : N → Type _))
        (f x) (mfderiv I J f x (Y x))) :=
  (hf.contMDiff.contMDiff_tangentMap (m := ∞) (by simp)).comp hY

def immersionInducedMetric [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M]
    (g : SmoothRiemannianMetric J N) {f : M → N} (hf : IsImmersion I J ∞ f) :
    SmoothRiemannianMetric I M where
  inner := immersionInner g f
  symm x v w := g.symm (f x) _ _
  pos := immersionInner_pos g hf
  isVonNBounded x := DifferentialGeometry.Geometry.posDef_isVonNBounded
    (E := E) (immersionInner g f x)
    (immersionInner_pos g hf x)
  contMDiff := by
    classical
    apply contMDiff_continuousLinearMap_section_of_apply
      (V₂ := fun x : M => TangentSpace I x →L[ℝ] ℝ)
      (φ := fun x : M => immersionInner g f x)
    intro Y
    apply contMDiff_continuousLinearMap_section_of_apply
      (V₂ := fun _ : M => ℝ)
      (φ := fun x : M => immersionInner g f x (Y x))
    intro W
    have hv := immersion_tangent_section_contMDiff hf (fun x => Y x) Y.contMDiff
    have hw := immersion_tangent_section_contMDiff hf (fun x => W x) W.contMDiff
    have hg : ContMDiff I (J.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) ∞
        (fun x : M => TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ)
          (E := fun b : N => TangentSpace J b →L[ℝ] TangentSpace J b →L[ℝ] ℝ)
          (f x) (g.inner (f x))) :=
      g.contMDiff.comp hf.contMDiff
    have htotal : ContMDiff I (J.prod 𝓘(ℝ, ℝ)) ∞
        (fun x : M => TotalSpace.mk' ℝ (E := Bundle.Trivial N ℝ) (f x)
          (g.inner (f x) (mfderiv I J f x (Y x)) (mfderiv I J f x (W x)))) :=
      ContMDiff.clm_bundle_apply₂
        (E₁ := fun b : N => TangentSpace J b)
        (E₂ := fun b : N => TangentSpace J b)
        (E₃ := fun _ : N => ℝ)
        (b := f) (ψ := fun x : M => g.inner (f x))
        (v := fun x : M => mfderiv I J f x (Y x))
        (w := fun x : M => mfderiv I J f x (W x)) hg hv hw
    have hscalar : ContMDiff I 𝓘(ℝ, ℝ) ∞
        (fun x : M => immersionInner g f x (Y x) (W x)) := by
      intro x
      have hat := htotal x
      rw [contMDiffAt_totalSpace] at hat
      simpa [immersionInner_apply] using hat.2
    intro x
    rw [contMDiffAt_section]
    refine hscalar.contMDiffAt.congr_of_eventuallyEq ?_
    filter_upwards with y
    rfl

theorem immersionInducedMetric_inner [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M]
    (g : SmoothRiemannianMetric J N) {f : M → N} (hf : IsImmersion I J ∞ f)
    (x : M) (v w : TangentSpace I x) :
    (immersionInducedMetric g hf).inner x v w =
      g.inner (f x) (mfderiv I J f x v) (mfderiv I J f x w) := rfl

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
