import DifferentialGeometry.Topology.LocalDegree.SphereMap

set_option autoImplicit false
open Metric Set
open scoped unitInterval
noncomputable section
namespace Poincare.LocalDegree
variable {E F K : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K]
  (f : E → F) (x : E) (R : ℝ)
  (hf : ContinuousOn f (closedBall x R))
  (hz : ∀ y ∈ closedBall x R, y ≠ x → f y ≠ 0)


def sphereMapParameter (r : C(K, Ioc (0 : ℝ) R)) (v : C(K, sphere (0 : E) 1)) :
    C(K, sphere (0 : F) 1) :=
  (sphereMapFamily f x R hf hz).comp
    ⟨fun z => (r z, v z), r.continuous.prodMk v.continuous⟩


@[simp]
theorem sphereMapParameter_apply (r : C(K, Ioc (0 : ℝ) R))
    (v : C(K, sphere (0 : E) 1)) (z : K) :
    (sphereMapParameter f x R hf hz r v z : F) =
      ‖f (x + (r z : ℝ) • (v z : E))‖⁻¹ • f (x + (r z : ℝ) • (v z : E)) :=
  sphereMapFamily_apply f x R hf hz (r z) (v z)


@[simp]
theorem sphereMapParameter_const (r : Ioc (0 : ℝ) R) (v : C(K, sphere (0 : E) 1)) :
    sphereMapParameter f x R hf hz (ContinuousMap.const K r) v =
      (sphereMap f x R hf hz r).comp v := rfl

private def interpolatedRadius (r₀ r₁ : C(K, Ioc (0 : ℝ) R)) :
    C(I × K, Ioc (0 : ℝ) R) where
  toFun p := ⟨(1 - (p.1 : ℝ)) * (r₀ p.2 : ℝ) + (p.1 : ℝ) * (r₁ p.2 : ℝ),
    (convex_Ioc (0 : ℝ) R) (r₀ p.2).property (r₁ p.2).property
      (sub_nonneg.mpr p.1.property.2) p.1.property.1 (sub_add_cancel _ _)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
      (continuous_subtype_val.comp (r₀.continuous.comp continuous_snd))).add
      ((continuous_subtype_val.comp continuous_fst).mul
        (continuous_subtype_val.comp (r₁.continuous.comp continuous_snd)))

def sphereMapParameterHomotopy (r₀ r₁ : C(K, Ioc (0 : ℝ) R))
    (v : C(K, sphere (0 : E) 1)) :
    (sphereMapParameter f x R hf hz r₀ v).Homotopy
      (sphereMapParameter f x R hf hz r₁ v) where
  toFun p := sphereMapFamily f x R hf hz (interpolatedRadius R r₀ r₁ p, v p.2)
  continuous_toFun := (sphereMapFamily f x R hf hz).continuous.comp
    ((interpolatedRadius R r₀ r₁).continuous.prodMk (v.continuous.comp continuous_snd))
  map_zero_left z := by
    change sphereMapFamily f x R hf hz (interpolatedRadius R r₀ r₁ (0, z), v z) =
      sphereMapFamily f x R hf hz (r₀ z, v z)
    congr 1
    apply Prod.ext
    · apply Subtype.ext
      simp [interpolatedRadius]
    · rfl
  map_one_left z := by
    change sphereMapFamily f x R hf hz (interpolatedRadius R r₀ r₁ (1, z), v z) =
      sphereMapFamily f x R hf hz (r₁ z, v z)
    congr 1
    apply Prod.ext
    · apply Subtype.ext
      simp [interpolatedRadius]
    · rfl


@[simp]
theorem sphereMapParameterHomotopy_apply (r₀ r₁ : C(K, Ioc (0 : ℝ) R))
    (v : C(K, sphere (0 : E) 1)) (t : I) (z : K) :
    (sphereMapParameterHomotopy f x R hf hz r₀ r₁ v (t, z) : F) =
      ‖f (x + ((1 - (t : ℝ)) * (r₀ z : ℝ) + (t : ℝ) * (r₁ z : ℝ)) • (v z : E))‖⁻¹ •
        f (x + ((1 - (t : ℝ)) * (r₀ z : ℝ) + (t : ℝ) * (r₁ z : ℝ)) • (v z : E)) :=
  sphereMapFamily_apply f x R hf hz (interpolatedRadius R r₀ r₁ (t, z)) (v z)

end Poincare.LocalDegree
