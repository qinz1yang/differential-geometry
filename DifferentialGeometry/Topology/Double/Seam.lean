import DifferentialGeometry.Topology.Double.ClosedCover
import Mathlib.Topology.Order.ProjIcc

set_option autoImplicit false
noncomputable section
open Set Function Topology
namespace Poincare.Topology
variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  (B : Set X) (r : C(X, ℝ)) (hr : ∀ b : B, r b.val = 0)
  (hz : ∀ x, r x = 0 → x ∈ B)
  {ε : ℝ}
  (c : C(B × Icc (0 : ℝ) ε, X))
  (hheight : ∀ q, r (c q) = q.2.val)


def doubleSeam : C(B × Icc (-ε) ε, Double B) := by
  classical
  let a : B × Icc (-ε) ε → B × Icc (0 : ℝ) ε := fun q =>
    (q.1, ⟨|q.2.val|, abs_nonneg _, abs_le.mpr q.2.property⟩)
  let f : B × Icc (-ε) ε → Double B := fun q =>
    if 0 ≤ q.2.val then doublePositive B (c (a q)) else doubleNegative B (c (a q))
  have he (q : B × Icc (-ε) ε) :
      doubleRealization B r hr (f q) = (c (a q), q.2.val) := by
    by_cases ht : 0 ≤ q.2.val
    · dsimp only [f]
      rw [if_pos ht]
      refine Prod.ext ?_ ?_
      · rfl
      · change r (c (a q)) = q.2.val
        rw [hheight]
        exact abs_of_nonneg ht
    · dsimp only [f]
      rw [if_neg ht]
      refine Prod.ext ?_ ?_
      · rfl
      · change -r (c (a q)) = q.2.val
        rw [hheight]
        change -|q.2.val| = q.2.val
        rw [abs_of_neg (lt_of_not_ge ht), neg_neg]
  refine ⟨f, (isClosedEmbedding_doubleRealization B r hr hz).isEmbedding.continuous_iff.mpr ?_⟩
  have ha : Continuous a := by fun_prop
  exact ((c.continuous.comp ha).prodMk (continuous_subtype_val.comp continuous_snd)).congr
    (fun q => (he q).symm)


theorem doubleRealization_doubleSeam (q : B × Icc (-ε) ε) :
    doubleRealization B r hr (doubleSeam B r hr hz c hheight q) =
      (c (q.1, ⟨|q.2.val|, abs_nonneg _, abs_le.mpr q.2.property⟩), q.2.val) := by
  classical
  by_cases ht : 0 ≤ q.2.val
  · change doubleRealization B r hr
      (if 0 ≤ q.2.val then _ else _) = _
    rw [if_pos ht]
    refine Prod.ext ?_ ?_
    · rfl
    · change r (c _) = q.2.val
      rw [hheight]
      exact abs_of_nonneg ht
  · change doubleRealization B r hr
      (if 0 ≤ q.2.val then _ else _) = _
    rw [if_neg ht]
    refine Prod.ext ?_ ?_
    · rfl
    · change -r (c _) = q.2.val
      rw [hheight]
      change -|q.2.val| = q.2.val
      rw [abs_of_neg (lt_of_not_ge ht), neg_neg]


theorem isEmbedding_doubleSeam (hc : IsEmbedding c) :
    IsEmbedding (doubleSeam B r hr hz c hheight) := by
  have hB : IsClosed B := by
    have he : B = {x | r x = 0} := by
      ext x
      exact ⟨fun hx => hr ⟨x, hx⟩, hz x⟩
    rw [he]
    exact isClosed_eq r.continuous continuous_const
  let _ : CompactSpace B := isCompact_iff_compactSpace.mp hB.isCompact
  let _ : T2Space (Double B) := t2Space_double B r hr hz
  apply IsClosedEmbedding.isEmbedding
  apply (doubleSeam B r hr hz c hheight).continuous.isClosedEmbedding
  intro q p heq
  have hh := congrArg (doubleRealization B r hr) heq
  rw [doubleRealization_doubleSeam, doubleRealization_doubleSeam] at hh
  have hbase := congrArg Prod.fst (hc.injective (congrArg Prod.fst hh))
  exact Prod.ext hbase (Subtype.ext (congrArg Prod.snd hh))

end Poincare.Topology
