import DifferentialGeometry.Tensor.Alternating.Orientation
import DifferentialGeometry.Bundle.Orientation.Basic
import Mathlib.Geometry.Manifold.PartitionOfUnity

open Set Bundle Module DifferentialGeometry.ContinuousAlternatingMap
open scoped Manifold ContDiff Topology
set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.VectorBundle

variable {m : ℕ} {EB HB B F : Type*}
  [NormedAddCommGroup EB] [NormedSpace ℝ EB] [FiniteDimensional ℝ EB]
  [TopologicalSpace HB] [TopologicalSpace B] [ChartedSpace HB B]
  (I : ModelWithCorners ℝ EB HB) [IsManifold I ∞ B]
  [T2Space B] [SigmaCompactSpace B]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (V : B → Type*) [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]

include I in
theorem exists_continuous_topForm_of_isCompatibleOrientation
    (hm : finrank ℝ F = m) (o : ∀ x, Orientation ℝ (V x) (Fin m))
    (ho : IsCompatibleOrientation (F := F) V o) :
    ∃ η : ∀ x, V x [⋀^Fin m]→L[ℝ] ℝ,
      Continuous (fun x => TotalSpace.mk' (F [⋀^Fin m]→L[ℝ] ℝ) x (η x)) ∧
      ∀ x, η x ∈ positiveForms (o x) := by
  let W := fun x => V x [⋀^Fin m]→L[ℝ] ℝ
  have hlocal (x : B) : ∃ U ∈ 𝓝 x, ∃ η : ∀ y, W y,
      ContMDiffOn I (I.prod 𝓘(ℝ, F [⋀^Fin m]→L[ℝ] ℝ)) 0
        (fun y => TotalSpace.mk' (F [⋀^Fin m]→L[ℝ] ℝ) y (η y)) U ∧
      ∀ y ∈ U, η y ∈ positiveForms (o y) := by
    obtain ⟨t, ht, U, hUx, hU, p, hp⟩ := ho x
    obtain ⟨η, hη⟩ := nonempty_positiveForms hm p
    let : MemTrivializationAtlas (Bundle.Trivial.trivialization B ℝ) := ⟨mem_singleton _⟩
    let A := t.continuousAlternatingMap ℝ (Fin m) (Bundle.Trivial.trivialization B ℝ)
    let ηloc : ∀ y, W y := fun y =>
      η.compContinuousLinearMap (t.continuousLinearMapAt ℝ y)
    have heq (y : B) (hy : y ∈ t.baseSet) :
        A.symm y η = ηloc y := by
      change (Bundle.Pretrivialization.continuousAlternatingMap ℝ (Fin m)
        t (Bundle.Trivial.trivialization B ℝ)).symm y η = _
      rw [Bundle.Pretrivialization.continuousAlternatingMap_symm_apply' ⟨hy, mem_univ y⟩]
      rw [Bundle.Trivial.symmL_trivialization]
      rfl
    refine ⟨U, hUx, ηloc, contMDiffOn_zero_iff.mpr ?_, ?_⟩
    · have hcont := A.continuousOn_symm.comp
        (continuous_id.prodMk (continuous_const (y := η))).continuousOn
        (fun y (hy : y ∈ U) => show (y, η) ∈ A.baseSet ×ˢ univ from
          ⟨⟨hU hy, mem_univ y⟩, mem_univ η⟩)
      exact hcont.congr (fun y hy => congrArg (TotalSpace.mk' _ y) (heq y (hU hy)).symm)
    · intro y hy
      let e := t.continuousLinearEquivAt ℝ y (hU hy)
      have hpos := comp_mem_positiveForms hη e
      have hmap : Orientation.map (Fin m) e.symm.toLinearEquiv p = o y := by
        rw [← hp y hy]
        exact (Orientation.map (Fin m) e.toLinearEquiv).symm_apply_apply (o y)
      rw [hmap] at hpos
      simpa only [e, Trivialization.coe_continuousLinearEquivAt_eq'] using hpos
  obtain ⟨η, hη⟩ := exists_contMDiffSection_forall_mem_convex_of_local I W
    (fun x => positiveForms (o x)) (fun x => convex_positiveForms (o x)) hlocal
  exact ⟨η, η.contMDiff.continuous, hη⟩

end DifferentialGeometry.VectorBundle
