import DifferentialGeometry.Topology.Simplex.Face

noncomputable section

namespace DifferentialGeometry.Simplex

def simplexCone (n : ℕ) :
    C(unitInterval × stdSimplex ℝ (Fin (n + 1)), stdSimplex ℝ (Fin (n + 2))) where
  toFun z := ⟨Fin.cons z.1.val (fun i => (1 - z.1.val) * z.2.val i), by
    constructor
    · intro i
      refine Fin.cases z.1.property.1 (fun j => ?_) i
      exact mul_nonneg (sub_nonneg.mpr z.1.property.2) (z.2.property.1 j)
    · rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, ← Finset.mul_sum]
      rw [z.2.property.2]
      ring⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact continuous_subtype_val.comp continuous_fst
    · exact (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
        ((continuous_apply j).comp (continuous_subtype_val.comp continuous_snd))

@[simp] theorem simplexCone_zero (n : ℕ) (p : stdSimplex ℝ (Fin (n + 1))) :
    simplexCone n (0, p) = stdSimplex.map (0 : Fin (n + 2)).succAbove p := by
  apply Subtype.ext
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [map_succAbove_apply_pivot]
    rfl
  · change (1 - (0 : ℝ)) * p.val j = _
    simpa only [Fin.succAbove_zero, sub_zero, one_mul] using
      (map_succAbove_apply_image (0 : Fin (n + 2)) p j).symm

@[simp] theorem simplexCone_one (n : ℕ) (p : stdSimplex ℝ (Fin (n + 1))) :
    simplexCone n (1, p) = stdSimplex.vertex (0 : Fin (n + 2)) := by
  apply Subtype.ext
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [simplexCone]

@[simp] theorem simplexCone_apply_zero (n : ℕ) (t : unitInterval)
    (p : stdSimplex ℝ (Fin (n + 1))) : (simplexCone n (t, p)).val 0 = t.val := rfl

@[simp] theorem simplexCone_apply_succ (n : ℕ) (t : unitInterval)
    (p : stdSimplex ℝ (Fin (n + 1))) (i : Fin (n + 1)) :
    (simplexCone n (t, p)).val i.succ = (1 - t.val) * p.val i := rfl

theorem simplexCone_map_succAbove (n : ℕ) (i : Fin (n + 2))
    (t : unitInterval) (p : stdSimplex ℝ (Fin (n + 1))) :
    simplexCone (n + 1) (t, stdSimplex.map i.succAbove p) =
      stdSimplex.map i.succ.succAbove (simplexCone n (t, p)) := by
  apply Subtype.ext
  funext j
  by_cases hji : j = i.succ
  · subst j
    rw [map_succAbove_apply_pivot, simplexCone_apply_succ, map_succAbove_apply_pivot, mul_zero]
  · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hji
    rw [map_succAbove_apply_image]
    refine Fin.cases ?_ (fun j => ?_) j
    · rw [Fin.succ_succAbove_zero]
      rfl
    · rw [Fin.succ_succAbove_succ, simplexCone_apply_succ, simplexCone_apply_succ,
        map_succAbove_apply_image]

end DifferentialGeometry.Simplex
