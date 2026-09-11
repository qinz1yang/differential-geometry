import Mathlib.Geometry.Manifold.Immersion
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold IsManifold
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Topology.Manifold
variable {E F H H' M N : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [TopologicalSpace H] [TopologicalSpace H']
variable (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ F H')
variable [TopologicalSpace M] [ChartedSpace H M]
variable [TopologicalSpace N] [ChartedSpace H' N]

theorem injective_mfderiv_of_isImmersionAt (f : M → N) (x : M)
    (hf : IsImmersionAt I J ∞ f x) : Injective (mfderiv I J f x) := by
  let h := hf.isImmersionAtOfComplement_complement
  let C := hf.complement
  let e := h.domChart
  let D : PartialDiffeomorph I I M H ∞ :=
    { toPartialEquiv := e.toPartialEquiv
      open_source := e.open_source
      open_target := e.open_target
      contMDiffOn_toFun := contMDiffOn_of_mem_maximalAtlas h.domChart_mem_maximalAtlas
      contMDiffOn_invFun := contMDiffOn_symm_of_mem_maximalAtlas h.domChart_mem_maximalAtlas }
  let P : F →L[ℝ] E := (ContinuousLinearMap.fst ℝ E C).comp h.equiv.symm.toContinuousLinearMap
  let Φ : N → E := P ∘ J ∘ h.codChart
  have he : ContMDiffAt I I ∞ e x :=
    contMDiffAt_of_mem_maximalAtlas h.domChart_mem_maximalAtlas h.mem_domChart_source
  have hΦ : ContMDiffAt J 𝓘(ℝ, E) ∞ Φ (f x) :=
    P.contDiff.contMDiff.contMDiffAt.comp (f x)
      (J.contMDiff.contMDiffAt.comp (f x)
        (contMDiffAt_of_mem_maximalAtlas h.codChart_mem_maximalAtlas h.mem_codChart_source))
  have hn : (Φ ∘ f) =ᶠ[𝓝 x] (I ∘ e) := by
    apply Filter.eventuallyEq_of_mem (e.open_source.mem_nhds h.mem_domChart_source)
    intro y hy
    have hy' : y ∈ (e.extend I).source := by simpa only [OpenPartialHomeomorph.extend_source] using hy
    have hleft := (e.extend I).left_inv hy'
    have hn := h.writtenInCharts ((e.extend I).map_source hy')
    have hc : J (h.codChart (f y)) = h.equiv (I (e y), 0) := by
      change J (h.codChart (f ((e.extend I).symm ((e.extend I) y)))) = h.equiv (I (e y), 0) at hn
      rw [hleft] at hn
      exact hn
    change (h.equiv.symm (J (h.codChart (f y)))).1 = I (e y)
    rw [hc, h.equiv.symm_apply_apply]
  have hcomp := mfderiv_comp x (hΦ.mdifferentiableAt (by simp)) (h.contMDiffAt.mdifferentiableAt (by simp))
  have hcoord := mfderiv_comp x I.hasMFDerivAt.mdifferentiableAt (he.mdifferentiableAt (by simp))
  rw [I.hasMFDerivAt.mfderiv] at hcoord
  have hd : (mfderiv J 𝓘(ℝ, E) Φ (f x)).comp (mfderiv I J f x) = mfderiv I I e x :=
    hcomp.symm.trans (hn.mfderiv_eq.trans hcoord)
  intro v w hv
  apply ((PartialDiffeomorph.isLocalDiffeomorphAt I I ∞ D h.mem_domChart_source).mfderivToContinuousLinearEquiv (by simp)).injective
  change mfderiv I I e x v = mfderiv I I e x w
  rw [← hd]
  exact congrArg (mfderiv J 𝓘(ℝ, E) Φ (f x)) hv

theorem bijective_mfderiv_of_isImmersionAt [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (f : M → N) (x : M) (hf : IsImmersionAt I J ∞ f x)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F) : Bijective (mfderiv I J f x) := by
  let D : E →L[ℝ] F := mfderiv I J f x
  exact D.toLinearMap.linearEquivOfInjective (injective_mfderiv_of_isImmersionAt I J f x hf) hdim |>.bijective
end DifferentialGeometry.Topology.Manifold
