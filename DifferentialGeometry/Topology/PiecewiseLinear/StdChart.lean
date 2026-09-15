import DifferentialGeometry.Topology.PiecewiseLinear.OpenStar
import Mathlib.Analysis.InnerProductSpace.PiL2

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable (n : ℕ)

theorem mem_openSimplex_stdVertices_iff {x : Fin (n + 2) → ℝ} :
    x ∈ openSimplex (stdVertices n) ↔ (∀ i, 0 < x i) ∧ ∑ i, x i = 1 := by
  classical
  have hsum : ∀ l : Fin (n + 2) → ℝ,
      ∑ i, l i • (Pi.single i (1 : ℝ) : Fin (n + 2) → ℝ) = l := by
    intro l
    funext j
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [stdVertices, mem_openSimplex_image_iff (stdVertex_injective n).injOn]
  constructor
  · rintro ⟨l, hl₀, hl₁, hlx⟩
    rw [hsum] at hlx
    rw [← hlx]
    exact ⟨fun i => hl₀ i (Finset.mem_univ i), hl₁⟩
  · rintro ⟨hx₀, hx₁⟩
    exact ⟨x, fun i _ => hx₀ i, hx₁, hsum x⟩

noncomputable def stdProj : (Fin (n + 2) → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
  (WithLp.linearEquiv 2 ℝ (Fin (n + 1) → ℝ)).symm.toLinearMap ∘ₗ
    LinearMap.funLeft ℝ ℝ Fin.castSucc

theorem ofLp_stdProj (x : Fin (n + 2) → ℝ) (i : Fin (n + 1)) :
    WithLp.ofLp (stdProj n x) i = x i.castSucc := rfl

noncomputable def stdLiftLinear : EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] (Fin (n + 2) → ℝ) where
  toFun y := Fin.snoc (WithLp.ofLp y) (-∑ i, WithLp.ofLp y i)
  map_add' y y' := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.snoc_last, Pi.add_apply, WithLp.ofLp_add, Finset.sum_add_distrib, neg_add]
    · simp only [Fin.snoc_castSucc, Pi.add_apply, WithLp.ofLp_add]
  map_smul' c y := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.snoc_last, Pi.smul_apply, WithLp.ofLp_smul, RingHom.id_apply, smul_eq_mul,
        Finset.mul_sum, mul_neg]
    · simp only [Fin.snoc_castSucc, Pi.smul_apply, WithLp.ofLp_smul, RingHom.id_apply,
        smul_eq_mul]

noncomputable def stdLift : EuclideanSpace ℝ (Fin (n + 1)) →ᵃ[ℝ] (Fin (n + 2) → ℝ) :=
  (stdLiftLinear n).toAffineMap +
    AffineMap.const ℝ (EuclideanSpace ℝ (Fin (n + 1)))
      (Fin.snoc (0 : Fin (n + 1) → ℝ) (1 : ℝ) : Fin (n + 2) → ℝ)

theorem stdLift_apply_castSucc (y : EuclideanSpace ℝ (Fin (n + 1))) (i : Fin (n + 1)) :
    stdLift n y i.castSucc = WithLp.ofLp y i := by
  simp only [stdLift, AffineMap.coe_add, Pi.add_apply, LinearMap.coe_toAffineMap,
    AffineMap.const_apply, stdLiftLinear, LinearMap.coe_mk, AddHom.coe_mk, Fin.snoc_castSucc,
    Pi.zero_apply, add_zero]

theorem stdLift_apply_last (y : EuclideanSpace ℝ (Fin (n + 1))) :
    stdLift n y (Fin.last (n + 1)) = 1 - ∑ i, WithLp.ofLp y i := by
  simp only [stdLift, AffineMap.coe_add, Pi.add_apply, LinearMap.coe_toAffineMap,
    AffineMap.const_apply, stdLiftLinear, LinearMap.coe_mk, AddHom.coe_mk, Fin.snoc_last]
  ring

theorem stdProj_stdLift (y : EuclideanSpace ℝ (Fin (n + 1))) : stdProj n (stdLift n y) = y := by
  have h : WithLp.ofLp (stdProj n (stdLift n y)) = WithLp.ofLp y := by
    funext i
    rw [ofLp_stdProj, stdLift_apply_castSucc]
  calc stdProj n (stdLift n y) = WithLp.toLp 2 (WithLp.ofLp (stdProj n (stdLift n y))) := rfl
    _ = y := by rw [h]

theorem stdLift_stdProj {x : Fin (n + 2) → ℝ} (hx : ∑ i, x i = 1) :
    stdLift n (stdProj n x) = x := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [stdLift_apply_last]
    simp_rw [ofLp_stdProj]
    rw [Fin.sum_univ_castSucc] at hx
    linarith
  · rw [stdLift_apply_castSucc, ofLp_stdProj]

def stdTarget : Set (EuclideanSpace ℝ (Fin (n + 1))) :=
  {y | (∀ i, 0 < WithLp.ofLp y i) ∧ ∑ i, WithLp.ofLp y i < 1}

theorem convex_stdTarget : Convex ℝ (stdTarget n) := by
  intro x hx y hy a b ha hb hab
  change (∀ i, 0 < WithLp.ofLp x i) ∧ ∑ i, WithLp.ofLp x i < 1 at hx
  change (∀ i, 0 < WithLp.ofLp y i) ∧ ∑ i, WithLp.ofLp y i < 1 at hy
  change (∀ i, 0 < WithLp.ofLp (a • x + b • y) i) ∧ ∑ i, WithLp.ofLp (a • x + b • y) i < 1
  simp only [WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rcases ha.eq_or_lt with rfl | ha'
  · have hb' : b = 1 := by simpa using hab
    simpa only [hb', zero_mul, one_mul, zero_add] using hy
  · refine ⟨fun i => add_pos_of_pos_of_nonneg (mul_pos ha' (hx.1 i)) (mul_nonneg hb (hy.1 i).le), ?_⟩
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    calc
      a * ∑ i, WithLp.ofLp x i + b * ∑ i, WithLp.ofLp y i < a * 1 + b * 1 :=
        add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left hx.2 ha') (mul_le_mul_of_nonneg_left hy.2.le hb)
      _ = 1 := by simpa only [mul_one] using hab

theorem isOpen_stdTarget : IsOpen (stdTarget n) := by
  have h : stdTarget n = WithLp.ofLp ⁻¹'
      ((⋂ i, {v : Fin (n + 1) → ℝ | 0 < v i}) ∩ {v : Fin (n + 1) → ℝ | ∑ i, v i < 1}) := by
    ext y
    simp only [stdTarget, mem_ofPred_eq, mem_preimage, mem_inter_iff, mem_iInter]
  rw [h]
  refine ((isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_apply i)).inter
    (isOpen_lt (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const)).preimage
    (PiLp.continuous_ofLp 2 _)

theorem stdLift_mem_openSimplex {y : EuclideanSpace ℝ (Fin (n + 1))} (hy : y ∈ stdTarget n) :
    stdLift n y ∈ openSimplex (stdVertices n) := by
  rw [mem_openSimplex_stdVertices_iff]
  refine ⟨fun i => ?_, ?_⟩
  · refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [stdLift_apply_last]
      linarith [hy.2]
    · rw [stdLift_apply_castSucc]
      exact hy.1 j
  · rw [Fin.sum_univ_castSucc, stdLift_apply_last]
    simp_rw [stdLift_apply_castSucc]
    ring

theorem stdProj_mem_stdTarget {x : Fin (n + 2) → ℝ} (hx : x ∈ openSimplex (stdVertices n)) :
    stdProj n x ∈ stdTarget n := by
  rw [mem_openSimplex_stdVertices_iff] at hx
  refine ⟨fun i => ?_, ?_⟩
  · rw [ofLp_stdProj]
    exact hx.1 _
  · simp_rw [ofLp_stdProj]
    have h := hx.2
    rw [Fin.sum_univ_castSucc] at h
    linarith [hx.1 (Fin.last (n + 1))]

theorem stdLift_stdProj_of_mem {x : Fin (n + 2) → ℝ} (hx : x ∈ openSimplex (stdVertices n)) :
    stdLift n (stdProj n x) = x :=
  stdLift_stdProj n ((mem_openSimplex_stdVertices_iff n).mp hx).2

theorem continuous_stdProj : Continuous (stdProj n) :=
  (stdProj n).continuous_of_finiteDimensional

theorem continuous_stdLift : Continuous (stdLift n) :=
  (stdLift n).continuous_of_finiteDimensional

end DifferentialGeometry.Topology.PiecewiseLinear
