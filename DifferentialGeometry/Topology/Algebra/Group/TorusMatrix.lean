import DifferentialGeometry.Topology.Algebra.Module.PrimitiveSlope
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.Diffeomorph

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff Topology
open Matrix

namespace Circle

def slopeMap (v : Fin 2 → ℤ) (z : Circle) : Circle × Circle := (z ^ v 0, z ^ v 1)

private theorem contMDiff_zpow (n : ℤ) : ContMDiff (𝓡 1) (𝓡 1) ∞ (fun z : Circle => z ^ n) := by
  cases n with
  | ofNat n =>
      change ContMDiff (𝓡 1) (𝓡 1) ∞ (fun z : Circle => z ^ (n : ℤ))
      simp only [zpow_natCast]
      exact contMDiff_id.pow n
  | negSucc n =>
      simp only [zpow_negSucc]
      exact (contMDiff_id.pow (n + 1)).inv

theorem slopeMap_contMDiff (v : Fin 2 → ℤ) :
    ContMDiff (𝓡 1) ((𝓡 1).prod (𝓡 1)) ∞ (slopeMap v) :=
  (contMDiff_zpow (v 0)).prodMk (contMDiff_zpow (v 1))

theorem slopeMap_injective (v : Fin 2 → ℤ) (hv : IsCoprime (v 0) (v 1)) :
    Function.Injective (slopeMap v) := by
  intro z w h
  exact hv.injective_smul_pair (Additive Circle) h

theorem slopeMap_isClosedEmbedding (v : Fin 2 → ℤ) (hv : IsCoprime (v 0) (v 1)) :
    Topology.IsClosedEmbedding (slopeMap v) :=
  (slopeMap_contMDiff v).continuous.isClosedEmbedding (slopeMap_injective v hv)

def matrixMap (A : Matrix (Fin 2) (Fin 2) ℤ) (z : Circle × Circle) : Circle × Circle :=
  (z.1 ^ A 0 0 * z.2 ^ A 0 1, z.1 ^ A 1 0 * z.2 ^ A 1 1)

theorem matrixMap_contMDiff (A : Matrix (Fin 2) (Fin 2) ℤ) :
    ContMDiff ((𝓡 1).prod (𝓡 1)) ((𝓡 1).prod (𝓡 1)) ∞ (matrixMap A) :=
  (((contMDiff_zpow (A 0 0)).comp contMDiff_fst).mul
    ((contMDiff_zpow (A 0 1)).comp contMDiff_snd)).prodMk
    (((contMDiff_zpow (A 1 0)).comp contMDiff_fst).mul
      ((contMDiff_zpow (A 1 1)).comp contMDiff_snd))

theorem matrixMap_one (z : Circle × Circle) : matrixMap 1 z = z := by
  simp [matrixMap]

theorem matrixMap_mul (A B : Matrix (Fin 2) (Fin 2) ℤ) (z : Circle × Circle) :
    matrixMap (A * B) z = matrixMap A (matrixMap B z) := by
  ext <;> simp only [matrixMap, Matrix.mul_apply, Fin.sum_univ_two,
    zpow_add, mul_zpow, ← zpow_mul]
  all_goals simp only [mul_comm, mul_left_comm, mul_assoc]

def matrixDiffeomorph (A : Matrix.GeneralLinearGroup (Fin 2) ℤ) :
    (Circle × Circle) ≃ₘ⟮(𝓡 1).prod (𝓡 1), (𝓡 1).prod (𝓡 1)⟯ (Circle × Circle) where
  toFun := matrixMap A.val
  invFun := matrixMap A⁻¹.val
  left_inv z := by rw [← matrixMap_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, matrixMap_one]
  right_inv z := by rw [← matrixMap_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, matrixMap_one]
  contMDiff_toFun := matrixMap_contMDiff A.val
  contMDiff_invFun := matrixMap_contMDiff A⁻¹.val

theorem matrixMap_slopeMap (A : Matrix (Fin 2) (Fin 2) ℤ) (v : Fin 2 → ℤ) (z : Circle) :
    matrixMap A (slopeMap v z) = slopeMap (A *ᵥ v) z := by
  ext <;> simp only [matrixMap, slopeMap, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    zpow_add, ← zpow_mul]
  all_goals simp only [mul_comm]


theorem slopeMap_range_neg (v : Fin 2 → ℤ) :
    Set.range (slopeMap (-v)) = Set.range (slopeMap v) := by
  have h : slopeMap (-v) = slopeMap v ∘ Inv.inv := by
    funext z
    simp [slopeMap]
  rw [h]
  exact inv_surjective.range_comp (slopeMap v)

def slopeSet (s : Int.PrimitiveSlope) : Set (Circle × Circle) :=
  Quotient.liftOn s (fun v => Set.range (slopeMap v.val)) (by
    intro v w h
    rcases h with h | h
    · rw [h]
    · rw [h, slopeMap_range_neg])

theorem slopeSet_mk (v : Fin 2 → ℤ) (hv : IsCoprime (v 0) (v 1)) :
    slopeSet (Int.PrimitiveSlope.mk v hv) = Set.range (slopeMap v) := rfl

theorem matrixDiffeomorph_image_slopeSet
    (A : Matrix.GeneralLinearGroup (Fin 2) ℤ) (s : Int.PrimitiveSlope) :
    matrixDiffeomorph A '' slopeSet s = slopeSet (Int.PrimitiveSlope.map A s) := by
  refine Quotient.inductionOn s fun v => ?_
  change matrixDiffeomorph A '' Set.range (slopeMap v.val) =
    Set.range (slopeMap (A.val *ᵥ v.val))
  rw [← Set.range_comp]
  congr 1
  funext z
  exact matrixMap_slopeMap A.val v.val z

theorem exists_matrixDiffeomorph_meridian (v : Fin 2 → ℤ) (hv : IsCoprime (v 0) (v 1)) :
    ∃ A : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      ∀ z : Circle, matrixDiffeomorph (Matrix.SpecialLinearGroup.toGL A) (z, 1) = slopeMap v z := by
  obtain ⟨A, ha, hb⟩ := hv.exists_SL2_col 0
  refine ⟨A, fun z => ?_⟩
  change matrixMap A.val (z, 1) = slopeMap v z
  simp [matrixMap, slopeMap, ha, hb]

theorem exists_slopeMap_smooth_retraction (v : Fin 2 → ℤ) (hv : IsCoprime (v 0) (v 1)) :
    ∃ r : C^∞⟮(𝓡 1).prod (𝓡 1), Circle × Circle; 𝓡 1, Circle⟯,
      Function.LeftInverse r (slopeMap v) := by
  obtain ⟨A, hA⟩ := exists_matrixDiffeomorph_meridian v hv
  let e := matrixDiffeomorph (Matrix.SpecialLinearGroup.toGL A)
  refine ⟨⟨fun z => (e.symm z).1, contMDiff_fst.comp e.contMDiff_invFun⟩, ?_⟩
  intro z
  change (e.symm (slopeMap v z)).1 = z
  rw [← hA z]
  exact congrArg Prod.fst (e.symm_apply_apply (z, 1))


theorem zpow_eq_one_forall_iff (n : ℤ) : (∀ z : Circle, z ^ n = 1) ↔ n = 0 := by
  constructor
  · intro h
    by_contra hn
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    have hh := h (Circle.exp (Real.pi / n))
    rw [← Circle.exp_intCast_mul, mul_div_cancel₀ _ hnR] at hh
    exact Circle.exp_pi_ne_one hh
  · rintro rfl z
    exact zpow_zero z

theorem det_eq_zero_of_slopeMap_range_subset (v w : Fin 2 → ℤ)
    (h : Set.range (slopeMap v) ⊆ Set.range (slopeMap w)) :
    v 0 * w 1 - v 1 * w 0 = 0 := by
  apply (zpow_eq_one_forall_iff _).mp
  intro z
  obtain ⟨y, hy⟩ := h ⟨z, rfl⟩
  have h₀ : z ^ v 0 = y ^ w 0 := (congrArg Prod.fst hy).symm
  have h₁ : z ^ v 1 = y ^ w 1 := (congrArg Prod.snd hy).symm
  rw [zpow_sub, zpow_mul, zpow_mul, h₀, h₁, ← zpow_mul, ← zpow_mul,
    mul_comm (w 0) (w 1), mul_inv_cancel]

theorem slopeSet_injective : Function.Injective slopeSet := by
  intro s t
  refine Quotient.inductionOn₂ s t fun v w h => ?_
  apply (Int.PrimitiveSlope.mk_eq_mk_iff_det_eq_zero _ _ _ _).mpr
  exact det_eq_zero_of_slopeMap_range_subset v.val w.val (le_of_eq h)

end Circle
