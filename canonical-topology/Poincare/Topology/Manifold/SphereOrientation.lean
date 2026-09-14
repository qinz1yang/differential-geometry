import Mathlib.Analysis.InnerProductSpace.Orientation
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.LinearAlgebra.Alternating.Curry

noncomputable section

open Metric Module
open scoped Manifold

universe u

namespace Poincare.Topology

theorem sphere_outward_volumeForm_ne_zero
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (n : ℕ) [Fact (finrank ℝ E = n + 1)]
    (ω : Orientation ℝ E (Fin (n + 1))) (x : sphere (0 : E) 1) :
    ((ω.volumeForm.curryLeft (x : E)).compLinearMap
      (mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x).toLinearMap) ≠ 0 := by
  let b := OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) n (ne_zero_of_mem_unit_sphere x)
  let L := mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x
  have hlift (i : Fin n) : ∃ v : TangentSpace (𝓡 n) x, L v = (b i : E) := by
    have hmem : (b i : E) ∈ L.range := by
      rw [show L.range = (ℝ ∙ (x : E))ᗮ from range_mvfderiv_subtypeVal x]
      exact (b i).property
    exact hmem
  choose v hv using hlift
  have hb : Orthonormal ℝ (fun i : Fin n => (b i : E)) := by
    exact b.orthonormal.comp_linearIsometry (ℝ ∙ (x : E))ᗮ.subtypeₗᵢ
  have hx : Orthonormal ℝ (Matrix.vecCons (x : E) (fun i : Fin n => (b i : E))) := by
    apply orthonormal_vecCons_iff.mpr
    refine ⟨norm_eq_of_mem_sphere x, ?_, hb⟩
    intro i
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp (b i).property
  have hvol : |ω.volumeForm (Matrix.vecCons (x : E) (fun i : Fin n => (b i : E)))| = 1 := by
    rw [ω.abs_volumeForm_apply_of_pairwise_orthogonal hx.2]
    simp only [hx.norm_eq_one, Finset.prod_const_one]
  intro hz
  have heval := congrArg (fun f => f v) hz
  change ω.volumeForm (Matrix.vecCons (x : E) (fun i => L (v i))) = 0 at heval
  simp only [hv] at heval
  rw [heval, abs_zero] at hvol
  norm_num at hvol

def sphereOutwardOrientation
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (n : ℕ) [Fact (finrank ℝ E = n + 1)]
    (ω : Orientation ℝ E (Fin (n + 1))) (x : sphere (0 : E) 1) :
    Orientation ℝ (TangentSpace (𝓡 n) x) (Fin n) :=
  rayOfNeZero ℝ ((ω.volumeForm.curryLeft (x : E)).compLinearMap
    (mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x).toLinearMap)
      (sphere_outward_volumeForm_ne_zero n ω x)

theorem sphereOutwardOrientation_neg
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (n : ℕ) [Fact (finrank ℝ E = n + 1)]
    (ω : Orientation ℝ E (Fin (n + 1))) (x : sphere (0 : E) 1) :
    sphereOutwardOrientation n (-ω) x = -sphereOutwardOrientation n ω x := by
  unfold sphereOutwardOrientation
  rw [neg_rayOfNeZero]
  congr 1
  ext v
  simp only [AlternatingMap.compLinearMap_apply, AlternatingMap.curryLeft_apply_apply,
    Orientation.volumeForm_neg_orientation, AlternatingMap.neg_apply]

end Poincare.Topology

end

noncomputable section

open Metric Module
open scoped Manifold

namespace Poincare.Topology

local instance : Fact (finrank ℝ ℝ = 0 + 1) := ⟨by simp⟩

private theorem real_sphere_outward_form_value
    (x : sphere (0 : ℝ) 1) (v : Fin 0 → TangentSpace (𝓡 0) x) :
    (((Basis.singleton (Fin 1) ℝ).orientation.volumeForm.curryLeft (x : ℝ)).compLinearMap
      (mvfderiv (𝓡 0) ((↑) : sphere (0 : ℝ) 1 → ℝ) x).toLinearMap) v = (x : ℝ) := by
  have horth : Orthonormal ℝ (Basis.singleton (Fin 1) ℝ : Fin 1 → ℝ) := by simp
  let b : OrthonormalBasis (Fin 1) ℝ ℝ :=
    (Basis.singleton (Fin 1) ℝ).toOrthonormalBasis horth
  have hb : b.toBasis = Basis.singleton (Fin 1) ℝ :=
    Basis.toBasis_toOrthonormalBasis _ horth
  have hvol : (Basis.singleton (Fin 1) ℝ).orientation.volumeForm =
      (Basis.singleton (Fin 1) ℝ).det :=
    ((Basis.singleton (Fin 1) ℝ).orientation.volumeForm_robust b
      (congrArg (fun e : Basis (Fin 1) ℝ ℝ => e.orientation) hb)).trans
        (congrArg (fun e : Basis (Fin 1) ℝ ℝ => e.det) hb)
  rw [AlternatingMap.compLinearMap_apply, AlternatingMap.curryLeft_apply_apply,
    hvol, Basis.det_apply, Matrix.det_fin_one]
  simp only [Basis.toMatrix_apply, Matrix.cons_val_zero, Basis.singleton_repr]

theorem sphereOutwardOrientation_real_positive :
    sphereOutwardOrientation 0 (Basis.singleton (Fin 1) ℝ).orientation
      (⟨1, by norm_num⟩ : sphere (0 : ℝ) 1) = positiveOrientation := by
  unfold sphereOutwardOrientation
  change rayOfNeZero ℝ _ _ =
    rayOfNeZero ℝ (AlternatingMap.constLinearEquivOfIsEmpty (1 : ℝ)) _
  congr 1
  ext v
  change (((Basis.singleton (Fin 1) ℝ).orientation.volumeForm.curryLeft (1 : ℝ)).compLinearMap
    (mvfderiv (𝓡 0) ((↑) : sphere (0 : ℝ) 1 → ℝ)
      (⟨1, by norm_num⟩ : sphere (0 : ℝ) 1)).toLinearMap) v = 1
  exact real_sphere_outward_form_value _ v

theorem sphereOutwardOrientation_real_negative :
    sphereOutwardOrientation 0 (Basis.singleton (Fin 1) ℝ).orientation
      (⟨-1, by norm_num⟩ : sphere (0 : ℝ) 1) = -positiveOrientation := by
  unfold sphereOutwardOrientation
  change rayOfNeZero ℝ _ _ =
    rayOfNeZero ℝ (-(AlternatingMap.constLinearEquivOfIsEmpty (1 : ℝ))) _
  congr 1
  ext v
  change (((Basis.singleton (Fin 1) ℝ).orientation.volumeForm.curryLeft (-1 : ℝ)).compLinearMap
    (mvfderiv (𝓡 0) ((↑) : sphere (0 : ℝ) 1 → ℝ)
      (⟨-1, by norm_num⟩ : sphere (0 : ℝ) 1)).toLinearMap) v = -1
  exact real_sphere_outward_form_value _ v

end Poincare.Topology

end
