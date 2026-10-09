import DifferentialGeometry.Topology.PiecewiseLinear.Polyhedral.Maps.PiecewiseLinear
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

namespace DifferentialGeometry.Topology.Engulfing

set_option linter.unusedSectionVars false

open Set _root_.Geometry
open scoped BigOperators

variable {E : Type*} [DecidableEq E] [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def weightMass : (E →₀ ℝ) →ₗ[ℝ] ℝ :=
  Finsupp.linearCombination ℝ (fun _ : E => (1 : ℝ))

noncomputable def weightPoint : (E →₀ ℝ) →ₗ[ℝ] E := Finsupp.linearCombination ℝ id

omit [DecidableEq E] in
theorem weightMass_eq_sum {w : E →₀ ℝ} {s : Finset E} (hs : w.support ⊆ s) :
    weightMass w = ∑ x ∈ s, w x := by
  classical
  rw [weightMass, Finsupp.linearCombination_apply]
  simpa only [smul_eq_mul, mul_one] using
    w.sum_of_support_subset hs (fun _ r => r) (fun _ _ => rfl)

omit [DecidableEq E] in
theorem weightPoint_eq_sum {w : E →₀ ℝ} {s : Finset E} (hs : w.support ⊆ s) :
    weightPoint w = ∑ x ∈ s, w x • x := by
  classical
  rw [weightPoint, Finsupp.linearCombination_apply]
  exact w.sum_of_support_subset hs (fun x r => r • x) (fun _ _ => zero_smul _ _)

omit [DecidableEq E] in
theorem mem_convexHull_iff_weights (s : Finset E) (x : E) :
    x ∈ convexHull ℝ (s : Set E) ↔ ∃ w : E →₀ ℝ,
      w.support ⊆ s ∧ (∀ v, 0 ≤ w v) ∧ weightMass w = 1 ∧ weightPoint w = x := by
  classical
  constructor
  · intro hx
    obtain ⟨a, ha, hsum, hpoint⟩ := Finset.mem_convexHull'.mp hx
    let w : E →₀ ℝ := Finsupp.onFinset s (fun v => if v ∈ s then a v else 0)
      (fun v hv => by by_contra hn; simp [hn] at hv)
    have hs : w.support ⊆ s := by
      intro v hv
      by_contra hn
      exact (Finsupp.mem_support_iff.mp hv) (by simp [w, hn])
    refine ⟨w, hs, ?_, ?_, ?_⟩
    · intro v
      by_cases hv : v ∈ s
      · simpa [w, hv] using ha v hv
      · simp [w, hv]
    · rw [weightMass_eq_sum hs]
      simpa [w] using hsum
    · rw [weightPoint_eq_sum hs]
      simpa [w] using hpoint
  · rintro ⟨w, hs, hw, hm, hp⟩
    exact Finset.mem_convexHull'.mpr ⟨w, fun v _ => hw v,
      (weightMass_eq_sum hs).symm.trans hm, (weightPoint_eq_sum hs).symm.trans hp⟩

omit [DecidableEq E] in
theorem affineMap_weightPoint (A : E →ᵃ[ℝ] ℝ) {w : E →₀ ℝ}
    (hw : weightMass w = 1) :
    A (weightPoint w) = w.sum (fun x r => r • A x) := by
  classical
  have hm : ∑ x ∈ w.support, w x = 1 := (weightMass_eq_sum subset_rfl).symm.trans hw
  rw [weightPoint_eq_sum subset_rfl,
    ← Finset.affineCombination_eq_linear_combination _ _ _ hm,
    Finset.map_affineCombination _ _ _ hm,
    Finset.affineCombination_eq_linear_combination _ _ _ hm]
  rfl

omit [DecidableEq E] in
theorem convexWeights_eq_of_complex (K : SimplicialComplex ℝ E)
    {s t : Finset E} (hs : s ∈ K.faces) (ht : t ∈ K.faces)
    {w z : E →₀ ℝ} (hws : w.support ⊆ s) (hzt : z.support ⊆ t)
    (hw : ∀ v, 0 ≤ w v) (hz : ∀ v, 0 ≤ z v)
    (hwm : weightMass w = 1) (hzm : weightMass z = 1)
    (hp : weightPoint w = weightPoint z) : w = z := by
  classical
  have hxs : weightPoint w ∈ convexHull ℝ (s : Set E) :=
    (mem_convexHull_iff_weights s _).mpr ⟨w, hws, hw, hwm, rfl⟩
  have hxt : weightPoint w ∈ convexHull ℝ (t : Set E) :=
    hp ▸ (mem_convexHull_iff_weights t _).mpr ⟨z, hzt, hz, hzm, rfl⟩
  have hxspan : weightPoint w ∈ affineSpan ℝ ((s : Set E) ∩ (t : Set E)) :=
    convexHull_subset_affineSpan _ (K.inter_subset_convexHull hs ht ⟨hxs, hxt⟩)
  ext v
  obtain ⟨A, hA⟩ := exists_affineMap_of_affineIndependent (K.indep hs)
    (fun u : E => if u = v then (1 : ℝ) else 0)
  obtain ⟨B, hB⟩ := exists_affineMap_of_affineIndependent (K.indep ht)
    (fun u : E => if u = v then (1 : ℝ) else 0)
  have hAw : A (weightPoint w) = w v := by
    rw [affineMap_weightPoint A hwm]
    calc
      w.sum (fun x r => r • A x) =
          w.sum (fun x r => r • if x = v then (1 : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro u hu
        change w u • A u = _
        rw [hA u (hws hu)]
      _ = w v := by simp only [smul_eq_mul, mul_ite, mul_one, mul_zero, Finsupp.sum_ite_eq', Finsupp.mem_support_iff, ne_eq, ite_not, ite_eq_right_iff]; exact fun h => h.symm
  have hBz : B (weightPoint z) = z v := by
    rw [affineMap_weightPoint B hzm]
    calc
      z.sum (fun x r => r • B x) =
          z.sum (fun x r => r • if x = v then (1 : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro u hu
        change z u • B u = _
        rw [hB u (hzt hu)]
      _ = z v := by simp only [smul_eq_mul, mul_ite, mul_one, mul_zero, Finsupp.sum_ite_eq', Finsupp.mem_support_iff, ne_eq, ite_not, ite_eq_right_iff]; exact fun h => h.symm
  rw [← hAw, ← hBz, ← hp]
  exact AffineMap.eqOn_affineSpan (fun u hu => (hA u hu.1).trans (hB u hu.2).symm) hxspan

omit [DecidableEq E] in
theorem weights_eq_zero_of_affineIndependent {s : Finset E}
    (hs : AffineIndependent ℝ ((↑) : s → E)) {w : E →₀ ℝ}
    (hws : w.support ⊆ s) (hm : weightMass w = 0) (hp : weightPoint w = 0) : w = 0 := by
  classical
  have hw := hs.eq_zero_of_sum_eq_zero_subtype
    ((weightMass_eq_sum hws).symm.trans hm) ((weightPoint_eq_sum hws).symm.trans hp)
  ext v
  by_cases hv : v ∈ s
  · exact hw v hv
  · exact Finsupp.notMem_support_iff.mp (fun h => hv (hws h))

omit [DecidableEq E] in
theorem affineIndependent_of_weights_eq_zero {s : Finset E}
    (h : ∀ w : E →₀ ℝ, w.support ⊆ s → weightMass w = 0 → weightPoint w = 0 → w = 0) :
    AffineIndependent ℝ ((↑) : s → E) := by
  classical
  by_contra hn
  obtain ⟨a, hp, hm, v, hv, hne⟩ := exists_nontrivial_relation_sum_zero_of_not_affine_ind hn
  let w : E →₀ ℝ := Finsupp.onFinset s (fun v => if v ∈ s then a v else 0)
    (fun v hv => by by_contra hn; simp [hn] at hv)
  have hs : w.support ⊆ s := by
    intro v hv
    by_contra hn
    exact (Finsupp.mem_support_iff.mp hv) (by simp [w, hn])
  have hwm : weightMass w = 0 := by rw [weightMass_eq_sum hs]; simpa [w] using hm
  have hwp : weightPoint w = 0 := by rw [weightPoint_eq_sum hs]; simpa [w] using hp
  have heq := DFunLike.congr_fun (h w hs hwm hwp) v
  exact hne (by simpa [w, hv] using heq)

noncomputable def expandEdgeWeights (a b p : E) (α β : ℝ) (w : E →₀ ℝ) : E →₀ ℝ :=
  w - Finsupp.single p (w p) + Finsupp.single a (α * w p) + Finsupp.single b (β * w p)

omit [DecidableEq E] in
theorem expandEdgeWeights_mass (a b p : E) {α β : ℝ} (hab : α + β = 1)
    (w : E →₀ ℝ) : weightMass (expandEdgeWeights a b p α β w) = weightMass w := by
  classical
  simp only [expandEdgeWeights, map_add, map_sub, weightMass,
    Finsupp.linearCombination_single, smul_eq_mul, mul_one]
  have hh := congrArg (fun r : ℝ => r * w p) hab
  nlinarith only [hh]

omit [DecidableEq E] in
theorem expandEdgeWeights_point {a b p : E} {α β : ℝ} (hp : p = α • a + β • b)
    (w : E →₀ ℝ) : weightPoint (expandEdgeWeights a b p α β w) = weightPoint w := by
  classical
  simp only [expandEdgeWeights, map_add, map_sub, weightPoint,
    Finsupp.linearCombination_single, id_eq]
  have hh : (w p) • p = (α * w p) • a + (β * w p) • b := by
    calc
      (w p) • p = (w p) • (α • a + β • b) := congrArg (fun x : E => (w p) • x) hp
      _ = _ := by simp [smul_add, smul_smul, mul_comm]
  rw [hh]
  abel

theorem expandEdgeWeights_apply (a b p : E) (α β : ℝ) (w : E →₀ ℝ) (v : E) :
    expandEdgeWeights a b p α β w v = w v - (if p = v then w p else 0) +
      (if a = v then α * w p else 0) + (if b = v then β * w p else 0) := by
  simp [expandEdgeWeights, Finsupp.single_apply]

omit [DecidableEq E] in
theorem expandEdgeWeights_nonneg {a b p : E} {α β : ℝ}
    (hpa : p ≠ a) (hpb : p ≠ b) (ha : 0 ≤ α) (hb : 0 ≤ β)
    {w : E →₀ ℝ} (hw : ∀ v, 0 ≤ w v) :
    ∀ v, 0 ≤ expandEdgeWeights a b p α β w v := by
  classical
  intro v
  rw [expandEdgeWeights_apply]
  by_cases hv : p = v
  · subst v
    simp [hpa.symm, hpb.symm]
  · simp only [hv, ite_false, sub_zero]
    exact add_nonneg (add_nonneg (hw v) (ite_nonneg (mul_nonneg ha (hw p)) le_rfl))
      (ite_nonneg (mul_nonneg hb (hw p)) le_rfl)

omit [DecidableEq E] in
theorem expandEdgeWeights_eq_of_apply_eq {a b p : E} {α β : ℝ} {w z : E →₀ ℝ}
    (hp : w p = z p) (h : expandEdgeWeights a b p α β w = expandEdgeWeights a b p α β z) :
    w = z := by
  classical
  unfold expandEdgeWeights at h
  rw [hp] at h
  exact sub_left_injective (add_right_cancel (add_right_cancel h))

omit [DecidableEq E] in
theorem expandEdgeWeights_inj {a b p : E} {α β : ℝ}
    (hab : a ≠ b) (hpa : p ≠ a) (hpb : p ≠ b) (ha : 0 < α) (hb : 0 < β)
    {w z : E →₀ ℝ} (hw : ∀ v, 0 ≤ w v) (hz : ∀ v, 0 ≤ z v)
    (hwend : w a = 0 ∨ w b = 0) (hzend : z a = 0 ∨ z b = 0)
    (h : expandEdgeWeights a b p α β w = expandEdgeWeights a b p α β z) : w = z := by
  classical
  have hea := DFunLike.congr_fun h a
  have heb := DFunLike.congr_fun h b
  simp only [expandEdgeWeights_apply, hpa, hpb, hab, hab.symm, ite_false, ite_true,
    sub_zero, add_zero] at hea heb
  have hp : w p = z p := by
    rcases hwend with hwa | hwb <;> rcases hzend with hza | hzb
    · nlinarith
    · nlinarith [hw b, hz a]
    · nlinarith [hw a, hz b]
    · nlinarith
  exact expandEdgeWeights_eq_of_apply_eq hp h

omit [DecidableEq E] in
theorem expandEdgeWeights_eq_zero {a b p : E} {α β : ℝ}
    (hab : a ≠ b) (hpa : p ≠ a) (hpb : p ≠ b) (ha : α ≠ 0) (hb : β ≠ 0)
    {w : E →₀ ℝ} (hwend : w a = 0 ∨ w b = 0)
    (h : expandEdgeWeights a b p α β w = 0) : w = 0 := by
  classical
  have hp : w p = 0 := by
    rcases hwend with hwa | hwb
    · have hea := DFunLike.congr_fun h a
      simp only [expandEdgeWeights_apply, hpa, hab.symm, ite_false, ite_true,
        sub_zero, add_zero, hwa, zero_add, Finsupp.zero_apply] at hea
      exact (mul_eq_zero.mp hea).resolve_left ha
    · have heb := DFunLike.congr_fun h b
      simp only [expandEdgeWeights_apply, hpb, hab, ite_false, ite_true,
        sub_zero, add_zero, hwb, zero_add, Finsupp.zero_apply] at heb
      exact (mul_eq_zero.mp heb).resolve_left hb
  simpa [expandEdgeWeights, hp] using h

end DifferentialGeometry.Topology.Engulfing
