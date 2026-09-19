/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.Manifold.CornerRounding
import DifferentialGeometry.Topology.PiecewiseLinear.PLBallSphere
import DifferentialGeometry.Topology.Manifold.Homeomorph.Transport
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-! Rounded half-space coordinates near an attaching corner of a simplex prism. -/

open Set Topology
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.PiecewiseLinear

open DifferentialGeometry.Manifold (cornerRoot cornerSquaring cornerRoot_nonneg
  cornerRoot_cornerSquaring cornerSquaring_cornerRoot continuous_cornerRoot)

def prismCornerMap (p : (Fin 3 → ℝ) × ℝ) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![2 * p.1 0 * p.2, (p.1 0) ^ 2 - p.2 ^ 2, p.1 1 - p.1 2]

noncomputable def prismCornerInv (q : EuclideanSpace ℝ (Fin 3)) : (Fin 3 → ℝ) × ℝ :=
  let a := (cornerRoot (q 0, q 1)).1
  (![a, (1 - a + q 2) / 2, (1 - a - q 2) / 2], (cornerRoot (q 0, q 1)).2)

theorem continuous_prismCornerMap : Continuous prismCornerMap := by
  unfold prismCornerMap
  fun_prop

theorem continuous_prismCornerInv : Continuous prismCornerInv := by
  have hr : Continuous (fun q : EuclideanSpace ℝ (Fin 3) => cornerRoot (q 0, q 1)) :=
    continuous_cornerRoot.comp (by fun_prop)
  unfold prismCornerInv
  apply Continuous.prodMk
  · apply continuous_pi
    intro i
    fin_cases i <;> dsimp <;> fun_prop
  · exact hr.snd

def prismCornerSource : TopologicalSpace.Opens
    (stdSimplex ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1 : Set ((Fin 3 → ℝ) × ℝ)) where
  carrier := {p | 0 < p.val.1 1 ∧ 0 < p.val.1 2 ∧ p.val.2 < 1}
  is_open' :=
    (isOpen_lt continuous_const ((continuous_apply 1).comp
      (continuous_fst.comp continuous_subtype_val))).inter
      ((isOpen_lt continuous_const ((continuous_apply 2).comp
        (continuous_fst.comp continuous_subtype_val))).inter
          (isOpen_lt (continuous_snd.comp continuous_subtype_val) continuous_const))

noncomputable def prismCornerTarget : TopologicalSpace.Opens (EuclideanHalfSpace 3) where
  carrier := {q | (cornerRoot (q.val 0, q.val 1)).1 + |q.val 2| < 1 ∧
    (cornerRoot (q.val 0, q.val 1)).2 < 1}
  is_open' := by
    have hr : Continuous (fun q : EuclideanHalfSpace 3 => cornerRoot (q.val 0, q.val 1)) :=
      continuous_cornerRoot.comp (by fun_prop)
    exact (isOpen_lt (hr.fst.add (by fun_prop)) continuous_const).inter
      (isOpen_lt hr.snd continuous_const)

theorem prismCornerMap_mem_halfSpace {p : (Fin 3 → ℝ) × ℝ}
    (hp : p ∈ stdSimplex ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1) : 0 ≤ prismCornerMap p 0 := by
  exact mul_nonneg (mul_nonneg (by norm_num) (hp.1.1 0)) hp.2.1

theorem prismCornerInv_map {p : (Fin 3 → ℝ) × ℝ}
    (hp : p ∈ stdSimplex ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1) :
    prismCornerInv (prismCornerMap p) = p := by
  have hr := cornerRoot_cornerSquaring (p := (p.1 0, p.2)) ⟨hp.1.1 0, hp.2.1⟩
  have hs : p.1 0 + p.1 1 + p.1 2 = 1 := by simpa [Fin.sum_univ_three] using hp.1.2
  change cornerRoot (2 * p.1 0 * p.2, (p.1 0) ^ 2 - p.2 ^ 2) = (p.1 0, p.2) at hr
  apply Prod.ext
  · funext i
    fin_cases i <;> simp [prismCornerInv, prismCornerMap, hr] <;> linarith
  · simp [prismCornerInv, prismCornerMap, hr]

theorem prismCornerMap_inv {q : EuclideanSpace ℝ (Fin 3)} (hq : 0 ≤ q 0) :
    prismCornerMap (prismCornerInv q) = q := by
  have hr := cornerSquaring_cornerRoot (p := (q 0, q 1)) hq
  have hr0 := congrArg Prod.fst hr
  have hr1 := congrArg Prod.snd hr
  ext i
  fin_cases i
  · exact hr0
  · exact hr1
  · simp [prismCornerMap, prismCornerInv]
    ring

theorem prismCornerInv_mem_source (q : prismCornerTarget) :
    prismCornerInv q.val.val ∈ stdSimplex ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1 ∧
      0 < (prismCornerInv q.val.val).1 1 ∧ 0 < (prismCornerInv q.val.val).1 2 ∧
        (prismCornerInv q.val.val).2 < 1 := by
  have hr := cornerRoot_nonneg (q.val.val 0, q.val.val 1)
  have hq := q.property
  change (cornerRoot (q.val.val 0, q.val.val 1)).1 + |q.val.val 2| < 1 ∧
    (cornerRoot (q.val.val 0, q.val.val 1)).2 < 1 at hq
  have hp : 0 < (1 - (cornerRoot (q.val.val 0, q.val.val 1)).1 + q.val.val 2) / 2 := by
    linarith [neg_abs_le (q.val.val 2)]
  have hm : 0 < (1 - (cornerRoot (q.val.val 0, q.val.val 1)).1 - q.val.val 2) / 2 := by
    linarith [le_abs_self (q.val.val 2)]
  refine ⟨⟨⟨?_, ?_⟩, hr.2, hq.2.le⟩, hp, hm, hq.2⟩
  · intro i
    fin_cases i
    · exact hr.1
    · exact hp.le
    · exact hm.le
  · simp [prismCornerInv, Fin.sum_univ_three]
    ring

theorem prismCornerMap_mem_target
    (p : (stdSimplex ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1 : Set ((Fin 3 → ℝ) × ℝ)))
    (hp : p ∈ prismCornerSource) :
    (⟨prismCornerMap p.val, prismCornerMap_mem_halfSpace p.property⟩ : EuclideanHalfSpace 3) ∈
      prismCornerTarget := by
  have hr := cornerRoot_cornerSquaring (p := (p.val.1 0, p.val.2))
    ⟨p.property.1.1 0, p.property.2.1⟩
  have hs : p.val.1 0 + p.val.1 1 + p.val.1 2 = 1 := by
    simpa [Fin.sum_univ_three] using p.property.1.2
  change 0 < p.val.1 1 ∧ 0 < p.val.1 2 ∧ p.val.2 < 1 at hp
  change cornerRoot (2 * p.val.1 0 * p.val.2, (p.val.1 0) ^ 2 - p.val.2 ^ 2) =
    (p.val.1 0, p.val.2) at hr
  change (cornerRoot _).1 + |p.val.1 1 - p.val.1 2| < 1 ∧ (cornerRoot _).2 < 1
  change (cornerRoot (2 * p.val.1 0 * p.val.2, (p.val.1 0) ^ 2 - p.val.2 ^ 2)).1 +
    |p.val.1 1 - p.val.1 2| < 1 ∧
      (cornerRoot (2 * p.val.1 0 * p.val.2, (p.val.1 0) ^ 2 - p.val.2 ^ 2)).2 < 1
  rw [hr]
  refine ⟨?_, hp.2.2⟩
  have h : |p.val.1 1 - p.val.1 2| < 1 - p.val.1 0 :=
    abs_lt.mpr ⟨by linarith [hp.2.1], by linarith [hp.1]⟩
  linarith

noncomputable def prismCornerHomeomorph : prismCornerSource ≃ₜ prismCornerTarget where
  toFun p := ⟨⟨prismCornerMap p.val.val, prismCornerMap_mem_halfSpace p.val.property⟩,
    prismCornerMap_mem_target p.val p.property⟩
  invFun q := ⟨⟨prismCornerInv q.val.val, (prismCornerInv_mem_source q).1⟩,
    (prismCornerInv_mem_source q).2⟩
  left_inv p := Subtype.ext (Subtype.ext (prismCornerInv_map p.val.property))
  right_inv q := Subtype.ext (Subtype.ext (prismCornerMap_inv q.val.property))
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_prismCornerMap.comp (continuous_subtype_val.comp continuous_subtype_val)
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_prismCornerInv.comp (continuous_subtype_val.comp continuous_subtype_val)

theorem prismCornerHomeomorph_attaching_iff (p : prismCornerSource) :
    p.val.val.1 ∈ stdSimplexBoundary 2 ↔
      (prismCornerHomeomorph p).val.val 0 = 0 ∧ (prismCornerHomeomorph p).val.val 1 ≤ 0 := by
  have hp := p.property
  change 0 < p.val.val.1 1 ∧ 0 < p.val.val.1 2 ∧ p.val.val.2 < 1 at hp
  change p.val.val.1 ∈ stdSimplexBoundary 2 ↔
    (cornerSquaring (p.val.val.1 0, p.val.val.2)).1 = 0 ∧
      (cornerSquaring (p.val.val.1 0, p.val.val.2)).2 ≤ 0
  rw [DifferentialGeometry.Manifold.cornerSquaring_first_face_iff
    ⟨p.val.property.1.1 0, p.val.property.2.1⟩]
  constructor
  · rintro ⟨_, i, hi⟩
    fin_cases i
    · exact hi
    · exact (ne_of_gt hp.1 hi).elim
    · exact (ne_of_gt hp.2.1 hi).elim
  · intro h
    exact ⟨p.val.property.1, 0, h⟩

theorem prismCornerHomeomorph_end_iff (p : prismCornerSource) :
    p.val.val.2 = 0 ↔
      (prismCornerHomeomorph p).val.val 0 = 0 ∧ 0 ≤ (prismCornerHomeomorph p).val.val 1 := by
  exact (DifferentialGeometry.Manifold.cornerSquaring_second_face_iff
    (p := (p.val.val.1 0, p.val.val.2))
    ⟨p.val.property.1.1 0, p.val.property.2.1⟩).symm

theorem prismCornerHomeomorph_corner_iff (p : prismCornerSource) :
    p.val.val.1 ∈ stdSimplexBoundary 2 ∧ p.val.val.2 = 0 ↔
      (prismCornerHomeomorph p).val.val 0 = 0 ∧ (prismCornerHomeomorph p).val.val 1 = 0 := by
  rw [prismCornerHomeomorph_attaching_iff, prismCornerHomeomorph_end_iff]
  constructor
  · rintro ⟨⟨h0, hn⟩, _, hp⟩
    exact ⟨h0, le_antisymm hn hp⟩
  · rintro ⟨h0, h1⟩
    exact ⟨⟨h0, h1.le⟩, h0, h1.ge⟩

@[instance_reducible]
noncomputable def prismCornerChartedSpace : ChartedSpace (EuclideanHalfSpace 3) prismCornerSource :=
  DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace prismCornerHomeomorph

theorem prismCorner_isManifold :
    let _ := prismCornerChartedSpace
    IsManifold (𝓡∂ 3) ∞ prismCornerSource :=
  DifferentialGeometry.Manifold.Homeomorph.instIsManifoldPullback prismCornerHomeomorph

noncomputable def prismCornerDiffeomorph :
    let _ := prismCornerChartedSpace
    Diffeomorph (𝓡∂ 3) (𝓡∂ 3) prismCornerSource prismCornerTarget ∞ :=
  DifferentialGeometry.Manifold.Homeomorph.pullbackDiffeomorph prismCornerHomeomorph

theorem prismCornerTarget_boundary_iff (q : prismCornerTarget) :
    q ∈ (𝓡∂ 3).boundary prismCornerTarget ↔ q.val.val 0 = 0 := by
  change (𝓡∂ 3).IsBoundaryPoint q ↔ _
  rw [ModelWithCorners.isBoundaryPoint_iff_isBoundaryPoint_val,
    ModelWithCorners.isBoundaryPoint_iff, frontier_range_modelWithCornersEuclideanHalfSpace]
  change 0 = q.val.val 0 ↔ q.val.val 0 = 0
  exact eq_comm

theorem prismCorner_boundary_iff (p : prismCornerSource) :
    let _ := prismCornerChartedSpace
    p ∈ (𝓡∂ 3).boundary prismCornerSource ↔
      p.val.val.1 ∈ stdSimplexBoundary 2 ∨ p.val.val.2 = 0 := by
  let _ := prismCornerChartedSpace
  dsimp only
  have hbd := prismCornerDiffeomorph.preimage_boundary (by simp)
  rw [← hbd]
  change prismCornerHomeomorph p ∈ (𝓡∂ 3).boundary prismCornerTarget ↔ _
  rw [prismCornerTarget_boundary_iff, prismCornerHomeomorph_attaching_iff,
    prismCornerHomeomorph_end_iff]
  exact ⟨fun h => (le_total _ 0).elim (fun hn => Or.inl ⟨h, hn⟩)
    (fun hp => Or.inr ⟨h, hp⟩), fun h => h.elim And.left And.left⟩

theorem prismCornerTarget_zero_mem : (0 : EuclideanHalfSpace 3) ∈ prismCornerTarget := by
  change (cornerRoot (0, 0)).1 + |(0 : ℝ)| < 1 ∧ (cornerRoot (0, 0)).2 < 1
  norm_num [cornerRoot]

theorem contDiff_prismCornerMap : ContDiff ℝ ∞ prismCornerMap := by
  apply (contDiff_piLp 2).2
  intro i
  fin_cases i <;> dsimp [prismCornerMap] <;> fun_prop

theorem contDiffOn_prismCornerInv :
    ContDiffOn ℝ ∞ prismCornerInv
      {q : EuclideanSpace ℝ (Fin 3) | 0 ≤ q 0 ∧ (q 0, q 1) ≠ 0} := by
  intro q hq
  have hr := (DifferentialGeometry.Manifold.contDiffWithinAt_cornerRoot hq.1 hq.2).comp q
    (show ContDiffWithinAt ℝ ∞ (fun r : EuclideanSpace ℝ (Fin 3) => (r 0, r 1))
      {r | 0 ≤ r 0 ∧ (r 0, r 1) ≠ 0} q from by fun_prop) (fun _ h => h.1)
  change ContDiffWithinAt ℝ ∞
    (fun r : EuclideanSpace ℝ (Fin 3) => cornerRoot (r 0, r 1)) _ q at hr
  unfold prismCornerInv
  apply ContDiffWithinAt.prodMk
  · apply contDiffWithinAt_pi.2
    intro i
    fin_cases i
    · exact hr.fst
    · exact ((contDiffWithinAt_const.sub hr.fst).add (by fun_prop)).div_const 2
    · exact ((contDiffWithinAt_const.sub hr.fst).sub (by fun_prop)).div_const 2
  · exact hr.snd

theorem prismCornerHomeomorph_symm_zero :
    (prismCornerHomeomorph.symm ⟨0, prismCornerTarget_zero_mem⟩).val.val =
      (![0, (1 : ℝ) / 2, 1 / 2], 0) := by
  change prismCornerInv (0 : EuclideanSpace ℝ (Fin 3)) = _
  simp [prismCornerInv, cornerRoot]

end DifferentialGeometry.Topology.PiecewiseLinear
