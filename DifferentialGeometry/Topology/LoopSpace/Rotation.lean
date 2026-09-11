import DifferentialGeometry.Topology.LoopSpace.BasedCircle
import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic



noncomputable section

open Set Function ContinuousMap
open scoped Topology

namespace DifferentialGeometry.Topology

variable {X : Type*} [TopologicalSpace X] {x y : X}


theorem pathToCircle_coe_eq_extend (p : Path x x) {t : ℝ} (ht : t ∈ Icc 0 1) :
    pathToCircle p (t : loopCircle) = p.extend t :=
  (pathToCircle_coe p ⟨t, ht⟩).trans (p.extend_extends' ⟨t, ht⟩).symm


theorem pathToCircle_homotopic {p q : Path x x} (h : p.Homotopic q) :
    (pathToCircle p).Homotopic (pathToCircle q) := by
  obtain ⟨H⟩ := h
  let P : Path p q :=
    ⟨⟨H.eval, Path.continuous_uncurry_iff.mp H.continuous⟩, H.eval_zero, H.eval_one⟩
  have hj : Joined p q := ⟨P⟩
  exact (FreeLoop.homotopic_iff_joined _ _).mpr (hj.map continuous_pathToCircle)



theorem pathToCircle_trans_rotate (p : Path x y) (q : Path y x) (θ : loopCircle) :
    pathToCircle (p.trans q) (θ + ((1 / 2 : ℝ) : loopCircle)) =
      pathToCircle (q.trans p) θ := by
  obtain ⟨s, rfl⟩ := unitInterval_to_loopCircle_surjective θ
  rw [← AddCircle.coe_add, pathToCircle_coe_eq_extend (q.trans p) s.property]
  by_cases hs : (s : ℝ) ≤ 1 / 2
  · rw [pathToCircle_coe_eq_extend (p.trans q) (by
      constructor <;> linarith [s.property.1, s.property.2]),
      Path.extend_trans_of_half_le p q (by linarith [s.property.1]),
      Path.extend_trans_of_le_half q p hs]
    congr 1
    ring
  · have heq : (((s : ℝ) + 1 / 2 : ℝ) : loopCircle) =
        (((s : ℝ) - 1 / 2 : ℝ) : loopCircle) := by
      have harith : (s : ℝ) + 1 / 2 = (s : ℝ) - 1 / 2 + 1 := by ring
      rw [harith, AddCircle.coe_add, AddCircle.coe_period, add_zero]
    rw [heq, pathToCircle_coe_eq_extend (p.trans q) (by
      constructor <;> linarith [s.property.1, s.property.2]),
      Path.extend_trans_of_le_half p q (by linarith [s.property.2]),
      Path.extend_trans_of_half_le q p (le_of_not_ge hs)]
    congr 1
    ring


theorem pathToCircle_trans_homotopic_comm (p : Path x y) (q : Path y x) :
    (pathToCircle (p.trans q)).Homotopic (pathToCircle (q.trans p)) := by
  refine ⟨⟨⟨fun z : unitInterval × loopCircle =>
    pathToCircle (p.trans q) (z.2 + ((z.1.val / 2 : ℝ) : loopCircle)),
    (pathToCircle (p.trans q)).continuous.comp
      (continuous_snd.add ((AddCircle.continuous_mk' (1 : ℝ)).comp
        ((continuous_subtype_val.comp continuous_fst).div_const 2)))⟩, ?_, ?_⟩⟩
  · intro θ
    change pathToCircle (p.trans q) (θ + ((0 / 2 : ℝ) : loopCircle)) = _
    rw [zero_div, AddCircle.coe_zero, add_zero]
  · intro θ
    exact pathToCircle_trans_rotate p q θ

end DifferentialGeometry.Topology
