import DifferentialGeometry.Topology.VectorField.OpenPatch
import DifferentialGeometry.Topology.VectorField.Pushforward

set_option autoImplicit false
noncomputable section
open Bundle Set Filter
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.VectorField

variable {E F H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace H']
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace H' N]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  (U : TopologicalSpace.Opens M) (e : Diffeomorph J I N U ∞)
  (V : ∀ x : M, TangentSpace I x) (W : ∀ q : N, TangentSpace J q)


def patchThroughDiffeomorph (x : M) : TangentSpace I x :=
  patchOnOpen U V (_root_.VectorField.mpullback I J e.symm W) x


theorem patchThroughDiffeomorph_apply (q : N) :
    patchThroughDiffeomorph U e V W (e q).val = mfderiv J I e q (W q) := by
  rw [patchThroughDiffeomorph, patchOnOpen_of_mem U V _ (e q).property]
  exact mpullback_symm_partialDiffeomorph_apply e.toPartialDiffeomorph (by simp) W (by trivial)


theorem patchThroughDiffeomorph_eq_zero_iff (q : N) :
    patchThroughDiffeomorph U e V W (e q).val = 0 ↔ W q = 0 := by
  rw [patchThroughDiffeomorph, patchOnOpen_of_mem U V _ (e q).property]
  have hh := mpullback_diffeomorph_eq_zero_iff e.symm (by simp) W (e q)
  change _ ↔ (W (e.symm (e q)) : F) = 0 at hh
  erw [e.symm_apply_apply] at hh
  exact hh

private theorem pushed_section_eq_original_off {C : Set N}
    (hagree : ∀ q ∉ C, W q = _root_.VectorField.mpullback J I e (fun y : U => V y.val) q)
    (y : U) (hy : y.val ∉ (fun q : N => (e q).val) '' C) :
    _root_.VectorField.mpullback I J e.symm W y = V y.val := by
  have hq : e.symm y ∉ C := fun h => hy ⟨e.symm y, h, congrArg Subtype.val (e.apply_symm_apply y)⟩
  have hh := mpullback_symm_partialDiffeomorph_apply e.toPartialDiffeomorph (by simp) W
    (show e.symm y ∈ e.toPartialDiffeomorph.source from trivial)
  change _root_.VectorField.mpullback I J e.symm W (e (e.symm y)) =
    mfderiv J I e (e.symm y) (W (e.symm y)) at hh
  erw [e.apply_symm_apply] at hh
  rw [hh, hagree _ hq]
  change mfderiv J I e (e.symm y)
    ((mfderiv J I e (e.symm y)).inverse (V (e (e.symm y)).val)) = V y.val
  erw [e.apply_symm_apply]
  exact (isInvertible_mfderiv_diffeomorph e (by simp) (e.symm y)).self_apply_inverse _


theorem contMDiff_patchThroughDiffeomorph [IsManifold I 1 M] [IsManifold J 1 N] [T2Space M]
    (hV : ContMDiff I I.tangent ∞ (fun x => (⟨x, V x⟩ : TangentBundle I M)))
    (hW : ContMDiff J J.tangent ∞ (fun q => (⟨q, W q⟩ : TangentBundle J N)))
    {C : Set N} (hC : IsCompact C)
    (hagree : ∀ q ∉ C, W q = _root_.VectorField.mpullback J I e (fun y : U => V y.val) q) :
    ContMDiff I I.tangent ∞
      (fun x => (⟨x, patchThroughDiffeomorph U e V W x⟩ : TangentBundle I M)) := by
  apply contMDiff_patchOnOpen U hV
  · intro y
    exact contMDiffAt_mpullback_partialDiffeomorph e.symm.toPartialDiffeomorph (by simp)
      (by trivial) (hW (e.symm y))
  · exact (hC.image (continuous_subtype_val.comp e.contMDiff.continuous)).isClosed
  · rintro x ⟨q, _, rfl⟩
    exact (e q).property
  · exact pushed_section_eq_original_off U e V W hagree


theorem patchThroughDiffeomorph_eventuallyEq_self [T2Space M]
    {C : Set N} (hC : IsCompact C)
    (hagree : ∀ q ∉ C, W q = _root_.VectorField.mpullback J I e (fun y : U => V y.val) q)
    {x : M} (hx : x ∉ (fun q : N => (e q).val) '' C) :
    (fun y => (⟨y, patchThroughDiffeomorph U e V W y⟩ : TangentBundle I M)) =ᶠ[𝓝 x]
      (fun y => (⟨y, V y⟩ : TangentBundle I M)) :=
  patchOnOpen_eventuallyEq_self U V _
    (hC.image (continuous_subtype_val.comp e.contMDiff.continuous)).isClosed
    (pushed_section_eq_original_off U e V W hagree) hx


theorem patchThroughDiffeomorph_zeroSet :
    {x | patchThroughDiffeomorph U e V W x = 0} =
      (fun q : N => (e q).val) '' {q | W q = 0} ∪ ({x | V x = 0} \ U) := by
  change {x | patchOnOpen U V (_root_.VectorField.mpullback I J e.symm W) x = 0} = _
  rw [patchOnOpen_zeroSet]
  congr 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨e.symm y, (mpullback_diffeomorph_eq_zero_iff e.symm (by simp) W y).mp hy,
      congrArg Subtype.val (e.apply_symm_apply y)⟩
  · rintro ⟨q, hq, rfl⟩
    refine ⟨e q, ?_, rfl⟩
    apply (mpullback_diffeomorph_eq_zero_iff e.symm (by simp) W (e q)).mpr
    erw [e.symm_apply_apply]
    exact hq

end DifferentialGeometry.VectorField
