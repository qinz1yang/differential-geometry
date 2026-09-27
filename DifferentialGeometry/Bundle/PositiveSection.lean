import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Topology.VectorBundle.Hom

open Set Bundle Module Filter
open scoped Manifold ContDiff Topology
set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.VectorBundle

variable {EB HB B F : Type*}
  [NormedAddCommGroup EB] [NormedSpace ℝ EB] [FiniteDimensional ℝ EB]
  [TopologicalSpace HB] [TopologicalSpace B] [ChartedSpace HB B]
  (I : ModelWithCorners ℝ EB HB) [IsManifold I ∞ B]
  [T2Space B] [SigmaCompactSpace B]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  (V : B → Type*) [∀ x, AddCommGroup (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, Module ℝ (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]

theorem exists_contMDiff_section_covector_pos
    (ν : ∀ x : B, V x →L[ℝ] ℝ)
    (hν : Continuous (fun x => TotalSpace.mk' (F →L[ℝ] ℝ)
      (E := fun x : B => V x →L[ℝ] ℝ) x (ν x))) (hν0 : ∀ x, ν x ≠ 0) :
    ∃ W : ∀ x : B, V x,
      ContMDiff I (I.prod 𝓘(ℝ, F)) ∞ (fun x => TotalSpace.mk' F x (W x)) ∧
      ∀ x, 0 < ν x (W x) := by
  have hlocal (x : B) : ∃ U ∈ 𝓝 x, ∃ W : ∀ y : B, V y,
      ContMDiffOn I (I.prod 𝓘(ℝ, F)) ∞ (fun y => TotalSpace.mk' F y (W y)) U ∧
      ∀ y ∈ U, 0 < ν y (W y) := by
    have hs : Function.Surjective (ν x) := by
      apply LinearMap.surjective (f := (ν x).toLinearMap)
      intro hh
      apply hν0 x
      ext v
      exact congrArg (fun f : V x →ₗ[ℝ] ℝ => f v) hh
    obtain ⟨v, hv⟩ := hs 1
    let t := trivializationAt F V x
    have hx : x ∈ t.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
    let c := (t.continuousLinearEquivAt ℝ x hx) v
    let W := fun y => t.symmL ℝ y c
    have hW : ContMDiffOn I (I.prod 𝓘(ℝ, F)) ∞
        (fun y => TotalSpace.mk' F y (W y)) t.baseSet := by
      apply t.contMDiffOn_section_baseSet_iff.mpr
      apply (contMDiffOn_const (c := c)).congr
      intro y hy
      change (t ⟨y, t.symmL ℝ y c⟩).2 = c
      rw [t.apply_eq_prod_continuousLinearEquivAt ℝ y hy]
      change (t.continuousLinearEquivAt ℝ y hy) (t.symmL ℝ y c) = c
      rw [← t.symm_continuousLinearEquivAt_eq' (R := ℝ) hy]
      exact (t.continuousLinearEquivAt ℝ y hy).apply_symm_apply c
    have hWx : ν x (W x) = 1 := by
      dsimp only [W, c]
      rw [← t.symm_continuousLinearEquivAt_eq' (R := ℝ) hx]
      exact (congrArg (ν x) ((t.continuousLinearEquivAt ℝ x hx).symm_apply_apply v)).trans hv
    have hc := hν.continuousAt.clm_bundle_apply
      (hW.contMDiffAt (t.open_baseSet.mem_nhds hx)).continuousAt
    have hc' : ContinuousAt (fun y => ν y (W y)) x := by
      have hh := (FiberBundle.continuousAt_totalSpace ℝ _).mp hc |>.2
      exact hh
    let U := t.baseSet ∩ {y | 0 < ν y (W y)}
    refine ⟨U, inter_mem (t.open_baseSet.mem_nhds hx)
      (hc'.preimage_mem_nhds (isOpen_Ioi.mem_nhds (by rw [hWx]; norm_num))),
      W, hW.mono inter_subset_left, fun y hy => hy.2⟩
  obtain ⟨W, hW⟩ := exists_contMDiffSection_forall_mem_convex_of_local I V
    (fun x => {v : V x | 0 < ν x v})
    (fun x => (convex_Ioi (0 : ℝ)).linear_preimage (ν x).toLinearMap) hlocal
  exact ⟨W, W.contMDiff, hW⟩

end DifferentialGeometry.VectorBundle
