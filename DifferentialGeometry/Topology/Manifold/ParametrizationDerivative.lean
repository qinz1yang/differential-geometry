import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Topology.PartialHomeomorph.Basic

noncomputable section
open Set Topology Manifold
open scoped ContDiff

namespace Poincare.Topology.Manifold

variable {E F H H' P M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace H']
  [TopologicalSpace P] [ChartedSpace H P]
  [TopologicalSpace M] [ChartedSpace H' M]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}

set_option backward.isDefEq.respectTransparency false in
theorem injective_mfderiv_of_leftInverseOn
    {f : P → M} (hf : ContMDiff I J ∞ f) {g : M → P} {S : Set M}
    (hg : ContMDiffOn J I ∞ g S) (hmap : ∀ p, f p ∈ S)
    (hleft : Function.LeftInverse g f) (p : P) :
    Function.Injective (mfderiv I J f p) := by
  have heq : g ∘ f = id := funext hleft
  have hcomp := mfderivWithin_comp p
    ((hg (f p) (hmap p)).mdifferentiableWithinAt (by simp))
    ((hf p).mdifferentiableAt (by simp)).mdifferentiableWithinAt
    (s := univ) (fun x _ ↦ hmap x) (uniqueMDiffWithinAt_univ I)
  have hBA : (mfderivWithin J I g S (f p)).comp (mfderiv I J f p) =
      ContinuousLinearMap.id ℝ E := by
    have hcomp' : (mfderivWithin J I g S (f p)).comp (mfderiv I J f p) =
        (mfderiv I I (g ∘ f) p : E →L[ℝ] E) := by
      simpa only [mfderivWithin_univ] using hcomp.symm
    rw [heq, mfderiv_id] at hcomp'
    exact hcomp'
  intro u v huv
  have h := congrArg (mfderivWithin J I g S (f p)) huv
  change ((mfderivWithin J I g S (f p)).comp (mfderiv I J f p)) u =
    ((mfderivWithin J I g S (f p)).comp (mfderiv I J f p)) v at h
  change (mfderivWithin J I g S (f p)).comp (mfderiv I J f p) u =
    (mfderivWithin J I g S (f p)).comp (mfderiv I J f p) v at h
  have h' : (ContinuousLinearMap.id ℝ E) u = (ContinuousLinearMap.id ℝ E) v := hBA ▸ h
  exact h'

theorem isEmbedding_and_injective_mfderiv_of_smooth_partialEquiv
    (e : PartialEquiv P M) (hes : e.source = univ)
    (he : ContMDiff I J ∞ e) (hei : ContMDiffOn J I ∞ e.symm e.target) :
    IsEmbedding e ∧ ∀ p, Function.Injective (mfderiv I J e p) := by
  let h : PartialHomeomorph P M :=
    { toPartialEquiv := e
      continuousOn_toFun := he.continuous.continuousOn
      continuousOn_invFun := hei.continuousOn }
  refine ⟨h.isEmbedding hes, ?_⟩
  exact injective_mfderiv_of_leftInverseOn he hei
    (fun p ↦ e.map_source (hes ▸ mem_univ p)) (fun p ↦ e.left_inv (hes ▸ mem_univ p))

end Poincare.Topology.Manifold
