import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Tactic.FinCases

/-! # The original barycentric triangle as a planar convex body -/

noncomputable section

open Set Function
open scoped Topology

namespace Poincare.Topology

/-- The planar triangle with vertices 0, 1 and i. -/
def planeTriangle : Set ℂ := {z | 0 ≤ z.re ∧ 0 ≤ z.im ∧ z.re + z.im ≤ 1}

/-- The actual triangle is closed. -/
theorem isClosed_planeTriangle : IsClosed planeTriangle :=
  (isClosed_le continuous_const Complex.continuous_re).inter
    ((isClosed_le continuous_const Complex.continuous_im).inter
      (isClosed_le (Complex.continuous_re.add Complex.continuous_im) continuous_const))

/-- The actual triangle is convex over the reals. -/
theorem convex_planeTriangle : Convex ℝ planeTriangle := by
  intro z hz w hw a b ha hb hab
  change 0 ≤ (a • z + b • w).re ∧ 0 ≤ (a • z + b • w).im ∧
    (a • z + b • w).re + (a • z + b • w).im ≤ 1
  simp only [Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im, smul_eq_mul]
  exact ⟨add_nonneg (mul_nonneg ha hz.1) (mul_nonneg hb hw.1),
    add_nonneg (mul_nonneg ha hz.2.1) (mul_nonneg hb hw.2.1), by
      nlinarith [mul_nonneg ha (sub_nonneg.mpr hz.2.2),
        mul_nonneg hb (sub_nonneg.mpr hw.2.2)]⟩

/-- The same triangle is bounded in the original complex norm. -/
theorem isBounded_planeTriangle : Bornology.IsBounded planeTriangle := by
  apply (Metric.isBounded_closedBall : Bornology.IsBounded (Metric.closedBall (0 : ℂ) 1)).subset
  intro z hz
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (Complex.norm_le_abs_re_add_abs_im z).trans (by
    simpa only [abs_of_nonneg hz.1, abs_of_nonneg hz.2.1] using hz.2.2)

/-- Its interior contains the original barycenter. -/
theorem planeTriangle_interior_nonempty : (interior planeTriangle).Nonempty := by
  let U : Set ℂ := {z | 0 < z.re ∧ 0 < z.im ∧ z.re + z.im < 1}
  have hU : IsOpen U := (isOpen_lt continuous_const Complex.continuous_re).inter
    ((isOpen_lt continuous_const Complex.continuous_im).inter
      (isOpen_lt (Complex.continuous_re.add Complex.continuous_im) continuous_const))
  have hsub : U ⊆ planeTriangle := fun _ h => ⟨h.1.le, h.2.1.le, h.2.2.le⟩
  let z : ℂ := ⟨1 / 3, 1 / 3⟩
  have hz : z ∈ U := by norm_num [U, z]
  exact ⟨z, mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (hU.mem_nhds hz) hsub)⟩

/-- Every frontier point lies on one of the original three straight edges. -/
theorem planeTriangle_frontier_edges {z : ℂ} (hz : z ∈ frontier planeTriangle) :
    z.re = 0 ∨ z.im = 0 ∨ z.re + z.im = 1 := by
  change z ∈ frontier ({z : ℂ | 0 ≤ z.re} ∩ ({z : ℂ | 0 ≤ z.im} ∩
    {z : ℂ | z.re + z.im ≤ 1})) at hz
  rcases frontier_inter_subset _ _ hz with h | h
  · exact Or.inl (frontier_le_subset_eq continuous_const Complex.continuous_re h.1).symm
  · rcases frontier_inter_subset _ _ h.2 with hi | hs
    · exact Or.inr (Or.inl (frontier_le_subset_eq continuous_const Complex.continuous_im hi.1).symm)
    · exact Or.inr (Or.inr (frontier_le_subset_eq
        (Complex.continuous_re.add Complex.continuous_im) continuous_const hs.2))

/-- The original barycentric 2-simplex and the actual planar triangle are
homeomorphic by the affine coordinates z = t1 + i t2. -/
def simplexTriangleHomeomorph : stdSimplex ℝ (Fin 3) ≃ₜ planeTriangle where
  toFun t := ⟨⟨t.val 1, t.val 2⟩, t.property.1 1, t.property.1 2, by
    change t.val 1 + t.val 2 ≤ 1
    have ht : t.val 0 + t.val 1 + t.val 2 = 1 := by
      simpa [Fin.sum_univ_succ, add_assoc] using t.property.2
    linarith [t.property.1 0]⟩
  invFun z := ⟨![1 - z.val.re - z.val.im, z.val.re, z.val.im], by
    constructor
    · intro i
      fin_cases i
      · change 0 ≤ 1 - z.val.re - z.val.im
        linarith [z.property.2.2]
      · exact z.property.1
      · exact z.property.2.1
    · simp [Fin.sum_univ_succ]⟩
  left_inv t := by
    apply Subtype.ext
    funext i
    fin_cases i
    · change 1 - t.val 1 - t.val 2 = t.val 0
      have ht : t.val 0 + t.val 1 + t.val 2 = 1 := by
        simpa [Fin.sum_univ_succ, add_assoc] using t.property.2
      linarith
    · rfl
    · rfl
  right_inv z := by rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    have hc : Continuous (fun t : stdSimplex ℝ (Fin 3) =>
        (t.val 1 : ℂ) + (t.val 2 : ℂ) * Complex.I) :=
      (Complex.continuous_ofReal.comp ((continuous_apply 1).comp continuous_subtype_val)).add
        ((Complex.continuous_ofReal.comp ((continuous_apply 2).comp continuous_subtype_val)).mul
          continuous_const)
    apply hc.congr
    intro t
    apply Complex.ext <;> simp
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    fin_cases i <;> fun_prop

end Poincare.Topology
