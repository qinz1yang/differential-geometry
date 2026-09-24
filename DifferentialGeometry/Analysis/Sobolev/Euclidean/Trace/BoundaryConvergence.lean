import DifferentialGeometry.Geometry.Measure.Area.EuclideanDisk
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

noncomputable section

open Filter ContinuousMap
open scoped Topology

namespace DifferentialGeometry.Geometry

open DifferentialGeometry.Topology

theorem tendstoUniformly_diskExtension_boundary_of_tendsto_diskTrace
    {ι A F : Type*} [UniformSpace F] {l : Filter ι}
    {u : ι → C(closedDisk, F)} {η : C(loopCircle, F)}
    (h : Tendsto (fun n => diskTrace (u n)) l (𝓝 η)) (c : A → Circle) :
    TendstoUniformly (fun n x => diskExtension (u n) (c x : ℂ))
      (fun x => η ((AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm (c x))) l := by
  have hu := ContinuousMap.tendsto_iff_tendstoUniformly.mp h
  let θ : A → loopCircle := fun x =>
    (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm (c x)
  have hb (x : A) : (diskBoundary (θ x) : ℂ) = (c x : ℂ) := by
    change (AddCircle.toCircle (θ x) : ℂ) = (c x : ℂ)
    rw [← AddCircle.homeomorphCircle_apply one_ne_zero]
    exact congrArg (fun z : Circle => (z : ℂ))
      ((AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).apply_symm_apply (c x))
  have hfun : (fun n x => diskExtension (u n) (c x : ℂ)) =
      fun n x => diskTrace (u n) (θ x) := by
    funext n x
    rw [← hb x, diskExtension_coe]
    rfl
  rw [hfun]
  exact hu.comp θ

end DifferentialGeometry.Geometry

end

noncomputable section

open Filter ContinuousMap Set
open scoped Topology

namespace DifferentialGeometry.Geometry

open DifferentialGeometry.Topology

private def semicirclePoint (upper : Bool) (x : Icc (-1 : ℝ) 1) : Circle :=
  ⟨⟨x, if upper then Real.sqrt (1 - (x : ℝ) ^ 2) else -Real.sqrt (1 - (x : ℝ) ^ 2)⟩, by
    apply mem_sphere_zero_iff_norm.mpr
    change ‖(⟨(x : ℝ), if upper then Real.sqrt (1 - (x : ℝ) ^ 2)
      else -Real.sqrt (1 - (x : ℝ) ^ 2)⟩ : ℂ)‖ = 1
    have hsq : 0 ≤ 1 - (x : ℝ) ^ 2 := by nlinarith [x.property.1, x.property.2]
    have he : (‖(⟨(x : ℝ), if upper then Real.sqrt (1 - (x : ℝ) ^ 2)
        else -Real.sqrt (1 - (x : ℝ) ^ 2)⟩ : ℂ)‖) ^ 2 = 1 := by
      rw [Complex.sq_norm]
      simp only [Complex.normSq_apply]
      cases upper <;> simp only [Bool.false_eq_true, ↓reduceIte, neg_mul_neg] <;>
        nlinarith [Real.sq_sqrt hsq]
    nlinarith [norm_nonneg (⟨(x : ℝ), if upper then Real.sqrt (1 - (x : ℝ) ^ 2)
      else -Real.sqrt (1 - (x : ℝ) ^ 2)⟩ : ℂ)]⟩

private def semicirclePointExtension (upper : Bool) (x : ℝ) : Circle :=
  semicirclePoint upper (projIcc (-1) 1 (by norm_num) x)

def semicircleBoundaryParameter (upper : Bool) (x : ℝ) : loopCircle :=
  (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm
    (semicirclePointExtension upper x)

theorem tendstoUniformlyOn_diskExtension_semicircle_of_tendsto_diskTrace
    {ι F : Type*} [UniformSpace F] {l : Filter ι}
    {u : ι → C(closedDisk, F)} {η : C(loopCircle, F)}
    (h : Tendsto (fun n => diskTrace (u n)) l (𝓝 η)) (upper : Bool) :
    TendstoUniformlyOn
      (fun n x => diskExtension (u n)
        (⟨x, if upper then Real.sqrt (1 - x ^ 2) else -Real.sqrt (1 - x ^ 2)⟩ : ℂ))
      (fun x => η (semicircleBoundaryParameter upper x)) l (Icc (-1 : ℝ) 1) := by
  have ht := (tendstoUniformly_diskExtension_boundary_of_tendsto_diskTrace h
    (semicirclePointExtension upper)).tendstoUniformlyOn (s := Icc (-1 : ℝ) 1)
  apply ht.congr
  apply Eventually.of_forall
  intro n x hx
  have he : (semicirclePointExtension upper x : ℂ) =
      (⟨x, if upper then Real.sqrt (1 - x ^ 2) else -Real.sqrt (1 - x ^ 2)⟩ : ℂ) := by
    dsimp only [semicirclePointExtension]
    rw [projIcc_of_mem _ hx]
    rfl
  exact congrArg (diskExtension (u n)) he

end DifferentialGeometry.Geometry

end
