import DifferentialGeometry.Analysis.Schauder.Holder.Basic
import Mathlib.Topology.ContinuousMap.Compact

open Set
open scoped NNReal ENNReal

namespace DifferentialGeometry.Analysis.Schauder

variable {X F : Type*} [PseudoMetricSpace X] [PseudoMetricSpace F]

theorem holderOnWith_parabolicCylinder_of_slices
    {J : Set ℝ} {S : Set X} {alpha A B : NNReal} {f : ℝ → X → F}
    (ht : ∀ x ∈ S, HolderOnWith A (alpha / 2) (fun t => f t x) J)
    (hs : ∀ t ∈ J, HolderOnWith B alpha (f t) S) :
    HolderOnWith (A + B) alpha
      (fun p : ParabolicPoint X => f p.time p.space) (parabolicCylinder J S) := by
  intro p hp q hq
  have hdist : |p.time - q.time| ^ (1 / 2 : ℝ) ≤ dist p q := by
    rw [← parabolicPoint_time_space p, ← parabolicPoint_time_space q, dist_parabolicPoint]
    exact le_max_left _ _
  have htime : dist p.time q.time ^ ((alpha / 2 : NNReal) : ℝ) ≤
      dist p q ^ (alpha : ℝ) := by
    rw [Real.dist_eq]
    calc
      |p.time - q.time| ^ ((alpha / 2 : NNReal) : ℝ) =
          (|p.time - q.time| ^ (1 / 2 : ℝ)) ^ (alpha : ℝ) := by
        rw [← Real.rpow_mul (abs_nonneg _)]
        congr 1
        push_cast
        ring
      _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg (abs_nonneg _) _) hdist alpha.coe_nonneg
  have hspace : dist p.space q.space ^ (alpha : ℝ) ≤ dist p q ^ (alpha : ℝ) := by
    apply Real.rpow_le_rpow dist_nonneg _ alpha.coe_nonneg
    exact (LipschitzWith.prod_snd : LipschitzWith 1
      (fun p : ParabolicPoint X => p.space)).dist_le_mul p q |>.trans_eq (one_mul _)
  have hreal : dist (f p.time p.space) (f q.time q.space) ≤
      ((A + B : NNReal) : ℝ) * dist p q ^ (alpha : ℝ) := by
    calc
      _ ≤ dist (f p.time p.space) (f q.time p.space) +
          dist (f q.time p.space) (f q.time q.space) := dist_triangle _ _ _
      _ ≤ (A : ℝ) * dist p q ^ (alpha : ℝ) +
          (B : ℝ) * dist p q ^ (alpha : ℝ) :=
        add_le_add
          (((ht p.space hp.2).dist_le hp.1 hq.1).trans
            (mul_le_mul_of_nonneg_left htime A.coe_nonneg))
          (((hs q.time hq.1).dist_le hp.2 hq.2).trans
            (mul_le_mul_of_nonneg_left hspace B.coe_nonneg))
      _ = _ := by rw [NNReal.coe_add]; ring
  rw [edist_dist, edist_dist]
  calc
    ENNReal.ofReal (dist (f p.time p.space) (f q.time q.space)) ≤
        ENNReal.ofReal (((A + B : NNReal) : ℝ) * dist p q ^ (alpha : ℝ)) :=
      ENNReal.ofReal_le_ofReal hreal
    _ = _ := by
      rw [ENNReal.ofReal_mul (A + B).coe_nonneg, ENNReal.ofReal_coe_nnreal,
        ENNReal.ofReal_rpow_of_nonneg dist_nonneg alpha.coe_nonneg]

theorem holderOnWith_parabolicCylinder_of_continuousMap [CompactSpace X]
    {J : Set ℝ} {S : Set X} {alpha A B : NNReal} {f : ℝ → C(X, F)}
    (ht : HolderOnWith A (alpha / 2) f J)
    (hs : ∀ t ∈ J, HolderOnWith B alpha (f t) S) :
    HolderOnWith (A + B) alpha
      (fun p : ParabolicPoint X => f p.time p.space) (parabolicCylinder J S) := by
  apply holderOnWith_parabolicCylinder_of_slices _ hs
  intro x _
  have hx : LipschitzWith 1 (fun u : C(X, F) => u x) := by
    apply LipschitzWith.of_dist_le_mul
    intro u v
    simpa only [NNReal.coe_one, one_mul] using ContinuousMap.dist_apply_le_dist x
  have hc := hx.holderWith.comp_holderOnWith ht
  simpa only [Function.comp_apply, one_mul, NNReal.coe_one, NNReal.rpow_one] using! hc

end DifferentialGeometry.Analysis.Schauder
