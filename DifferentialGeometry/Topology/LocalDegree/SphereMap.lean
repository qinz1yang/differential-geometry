import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.Homotopy.Basic

set_option autoImplicit false

open Metric Set
open scoped Topology unitInterval

noncomputable section

namespace Poincare.LocalDegree

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem spherePoint_mem {x : E} {R : ℝ} (r : Ioc (0 : ℝ) R)
    (v : sphere (0 : E) 1) : x + (r : ℝ) • (v : E) ∈ sphere x r := by
  rw [mem_sphere, dist_eq_norm, add_sub_cancel_left, norm_smul,
    Real.norm_of_nonneg r.property.1.le, norm_eq_of_mem_sphere v, mul_one]

private theorem spherePoint_mem_closedBall {x : E} {R : ℝ} (r : Ioc (0 : ℝ) R)
    (v : sphere (0 : E) 1) : x + (r : ℝ) • (v : E) ∈ closedBall x R :=
  closedBall_subset_closedBall r.property.2 (sphere_subset_closedBall (spherePoint_mem r v))

private theorem spherePoint_ne_center {x : E} {R : ℝ} (r : Ioc (0 : ℝ) R)
    (v : sphere (0 : E) 1) : x + (r : ℝ) • (v : E) ≠ x :=
  ne_of_mem_sphere (spherePoint_mem r v) r.property.1.ne'

def sphereMapFamily (f : E → F) (x : E) (R : ℝ)
    (hf : ContinuousOn f (closedBall x R))
    (hzero : ∀ y ∈ closedBall x R, y ≠ x → f y ≠ 0) :
    C(Ioc (0 : ℝ) R × sphere (0 : E) 1, sphere (0 : F) 1) where
  toFun p := (homeomorphUnitSphereProd F
    ⟨f (x + (p.1 : ℝ) • (p.2 : E)),
      hzero _ (spherePoint_mem_closedBall p.1 p.2) (spherePoint_ne_center p.1 p.2)⟩).1
  continuous_toFun := by
    have hq : Continuous (fun p : Ioc (0 : ℝ) R × sphere (0 : E) 1 ↦
        x + (p.1 : ℝ) • (p.2 : E)) :=
      continuous_const.add ((continuous_subtype_val.comp continuous_fst).smul
        (continuous_subtype_val.comp continuous_snd))
    have hfp := hf.comp_continuous hq (fun p ↦ spherePoint_mem_closedBall p.1 p.2)
    exact (homeomorphUnitSphereProd F).continuous.fst.comp
      (hfp.subtype_mk (fun p ↦
        hzero _ (spherePoint_mem_closedBall p.1 p.2) (spherePoint_ne_center p.1 p.2)))


@[simp]
theorem sphereMapFamily_apply (f : E → F) (x : E) (R : ℝ)
    (hf : ContinuousOn f (closedBall x R))
    (hzero : ∀ y ∈ closedBall x R, y ≠ x → f y ≠ 0)
    (r : Ioc (0 : ℝ) R) (v : sphere (0 : E) 1) :
    (sphereMapFamily f x R hf hzero (r, v) : F) =
      ‖f (x + (r : ℝ) • (v : E))‖⁻¹ • f (x + (r : ℝ) • (v : E)) :=
  homeomorphUnitSphereProd_apply_fst_coe F _


def sphereMap (f : E → F) (x : E) (R : ℝ)
    (hf : ContinuousOn f (closedBall x R))
    (hzero : ∀ y ∈ closedBall x R, y ≠ x → f y ≠ 0)
    (r : Ioc (0 : ℝ) R) : C(sphere (0 : E) 1, sphere (0 : F) 1) :=
  (sphereMapFamily f x R hf hzero).curry r


@[simp]
theorem sphereMap_apply (f : E → F) (x : E) (R : ℝ)
    (hf : ContinuousOn f (closedBall x R))
    (hzero : ∀ y ∈ closedBall x R, y ≠ x → f y ≠ 0)
    (r : Ioc (0 : ℝ) R) (v : sphere (0 : E) 1) :
    (sphereMap f x R hf hzero r v : F) =
      ‖f (x + (r : ℝ) • (v : E))‖⁻¹ • f (x + (r : ℝ) • (v : E)) :=
  sphereMapFamily_apply f x R hf hzero r v

private def radiusPath {R : ℝ} (r₀ r₁ : Ioc (0 : ℝ) R) : Path r₀ r₁ where
  toFun t := ⟨Path.segment (r₀ : ℝ) (r₁ : ℝ) t,
    (convex_Ioc (0 : ℝ) R).segment_subset r₀.property r₁.property
      (by rw [← Path.range_segment]; exact mem_range_self t)⟩
  continuous_toFun := (Path.segment (r₀ : ℝ) (r₁ : ℝ)).continuous.subtype_mk _
  source' := Subtype.ext (Path.source _)
  target' := Subtype.ext (Path.target _)

def sphereMapHomotopy (f : E → F) (x : E) (R : ℝ)
    (hf : ContinuousOn f (closedBall x R))
    (hzero : ∀ y ∈ closedBall x R, y ≠ x → f y ≠ 0)
    (r₀ r₁ : Ioc (0 : ℝ) R) :
    (sphereMap f x R hf hzero r₀).Homotopy (sphereMap f x R hf hzero r₁) where
  toFun p := sphereMapFamily f x R hf hzero (radiusPath r₀ r₁ p.1, p.2)
  continuous_toFun := (sphereMapFamily f x R hf hzero).continuous.comp
    (((radiusPath r₀ r₁).continuous.comp continuous_fst).prodMk continuous_snd)
  map_zero_left v := by simp [sphereMap]
  map_one_left v := by simp [sphereMap]

@[simp]
theorem sphereMapHomotopy_apply (f : E → F) (x : E) (R : ℝ)
    (hf : ContinuousOn f (closedBall x R))
    (hzero : ∀ y ∈ closedBall x R, y ≠ x → f y ≠ 0)
    (r₀ r₁ : Ioc (0 : ℝ) R) (t : I) (v : sphere (0 : E) 1) :
    (sphereMapHomotopy f x R hf hzero r₀ r₁ (t, v) : F) =
      ‖f (x + (((1 - (t : ℝ)) * (r₀ : ℝ) + (t : ℝ) * (r₁ : ℝ)) • (v : E)))‖⁻¹ •
        f (x + (((1 - (t : ℝ)) * (r₀ : ℝ) + (t : ℝ) * (r₁ : ℝ)) • (v : E))) := by
  change (sphereMapFamily f x R hf hzero (radiusPath r₀ r₁ t, v) : F) = _
  simp [radiusPath, Path.segment_apply, AffineMap.lineMap_apply_module]

theorem sphereMap_id (R : ℝ) (r : Ioc (0 : ℝ) R) :
    sphereMap (fun y : E ↦ y) 0 R continuousOn_id (fun _ _ h ↦ h) r =
      ContinuousMap.id (sphere (0 : E) 1) := by
  apply ContinuousMap.ext
  intro v
  apply Subtype.ext
  simp only [sphereMap_apply, ContinuousMap.id_apply, zero_add, norm_smul,
    Real.norm_of_nonneg r.property.1.le, norm_eq_of_mem_sphere v, mul_one, smul_smul,
    inv_mul_cancel₀ r.property.1.ne', one_smul]

end Poincare.LocalDegree
