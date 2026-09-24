import DifferentialGeometry.Topology.Morse.OneSaddleOrder
import DifferentialGeometry.Topology.Morse.CriticalLevelComponents
import DifferentialGeometry.Topology.Compactness.ConnectedIntersection

open Set Metric Manifold
open scoped ContDiff Manifold

namespace DifferentialGeometry.Topology.Morse

local notation "S₂" => sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

theorem exists_superlevel_components_of_one_saddle
    {f : S₂ → ℝ} (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f)
    (hnd : ∀ x, IsCriticalPointAt (𝓡 2) f x → IsNondegenerateCriticalPointAt (𝓡 2) f x)
    (hinj : InjOn f {x | IsCriticalPointAt (𝓡 2) f x})
    (hone : {p | IsCriticalPointAt (𝓡 2) f p ∧ sigNeg (chartHessianAt
      (fun y => f ((extChartAt (𝓡 2) p).symm y)) (extChartAt (𝓡 2) p p)) = 1}.ncard = 1)
    (hconn : ∀ a : ℝ, IsPreconnected {x | f x < a}) :
    ∃ m s p q : S₂,
      f m < f s ∧ f s < f p ∧ f p < f q ∧
      IsMinOn f univ m ∧ IsMaxOn f univ q ∧ IsLocalMax f p ∧
      {x | IsCriticalPointAt (𝓡 2) f x} = {m, s, p, q} ∧
      sigNeg (chartHessianAt (fun y => f ((extChartAt (𝓡 2) s).symm y))
        (extChartAt (𝓡 2) s s)) = 1 ∧
      (∀ a ∈ Ioo (f s) (f p), ∀ x, f x ∈ Ico a (f p) →
        ¬ IsCriticalPointAt (𝓡 2) f x) ∧
      (∀ a ∈ Ico (f s) (f p),
        {x | a < f x} = connectedComponentIn {x | a < f x} p ∪
          connectedComponentIn {x | a < f x} q ∧
        Disjoint (connectedComponentIn {x | a < f x} p)
          (connectedComponentIn {x | a < f x} q) ∧
        IsMaxOn f (connectedComponentIn {x | a < f x} p) p) ∧
      closure (connectedComponentIn {x | f s < f x} p) ∩
        closure (connectedComponentIn {x | f s < f x} q) = {s} := by
  obtain ⟨m, s, p, q, hms, hsp, hpq, hm, hq, hpmax, hC, hsindex, hregular⟩ :=
    exists_ordered_criticalPoints_of_one_saddle hf hnd hinj hone hconn
  have hmc : IsCriticalPointAt (𝓡 2) f m := hC.symm.subset (by simp)
  have hsc : IsCriticalPointAt (𝓡 2) f s := hC.symm.subset (by simp)
  have hpc : IsCriticalPointAt (𝓡 2) f p := hC.symm.subset (by simp)
  have hcomponents (a : ℝ) (ha : a ∈ Ico (f s) (f p)) :
      {x | a < f x} = connectedComponentIn {x | a < f x} p ∪
        connectedComponentIn {x | a < f x} q ∧
      Disjoint (connectedComponentIn {x | a < f x} p)
        (connectedComponentIn {x | a < f x} q) ∧
      IsMaxOn f (connectedComponentIn {x | a < f x} p) p := by
    have hmax : IsMaxOn f (connectedComponentIn {x | a < f x} p) p := by
      apply isMaxOn_connectedComponentIn_gt_of_no_critical_values hf (hnd p hpc) hpmax
        (isClosed_Icc.preimage hf.continuous).isCompact
      intro x hx hc
      have hmem : x ∈ {y | IsCriticalPointAt (𝓡 2) f y} := hc
      rw [hC] at hmem
      change a < f x ∧ f x < f p at hx
      have hsa : f s ≤ a := ha.1
      rcases hmem with rfl | rfl | rfl | rfl <;> linarith
    refine ⟨?_, ?_, hmax⟩
    · apply Subset.antisymm _ (union_subset (connectedComponentIn_subset _ _)
        (connectedComponentIn_subset _ _))
      intro x hx
      obtain ⟨r, hr, _, hrc, _⟩ := exists_index_finrank_mem_connectedComponentIn_gt hf
        (isClosed_le continuous_const hf.continuous).isCompact (fun r _ hc => hnd r hc) hx
      have har : a < f r := connectedComponentIn_subset {y | a < f y} x hr
      have hrpq : r = p ∨ r = q := by
        have hmem : r ∈ {y | IsCriticalPointAt (𝓡 2) f y} := hrc
        rw [hC] at hmem
        have hsa : f s ≤ a := ha.1
        rcases hmem with rfl | rfl | rfl | rfl
        · exact False.elim (by linarith)
        · exact False.elim (by linarith)
        · exact Or.inl rfl
        · exact Or.inr rfl
      rcases hrpq with rfl | rfl
      · left
        rw [← connectedComponentIn_eq hr]
        exact mem_connectedComponentIn hx
      · right
        rw [← connectedComponentIn_eq hr]
        exact mem_connectedComponentIn hx
    · apply disjoint_left.mpr
      intro x hxp hxq
      have heq := (connectedComponentIn_eq hxp).trans (connectedComponentIn_eq hxq).symm
      have hqin : q ∈ connectedComponentIn {x | a < f x} p := by
        rw [heq]
        exact mem_connectedComponentIn (ha.2.trans hpq)
      exact hpq.not_ge (hmax hqin)
  refine ⟨m, s, p, q, hms, hsp, hpq, hm, hq, hpmax, hC, hsindex, hregular, hcomponents, ?_⟩
  have hmin (x : S₂) (hxm : x ≠ m) : f m < f x := by
    apply lt_of_le_of_ne (hm (mem_univ x))
    intro h
    exact hxm (eq_of_isMin_of_injOn_criticalPoints hinj
      (fun y => (show f x = f m from h.symm).le.trans (hm (mem_univ y)))
      (fun y => hm (mem_univ y)))
  have hclosed : IsPreconnected {x | f s ≤ f x} := by
    apply hf.continuous.isPreconnected_ge_of_isPreconnected_gt hms
      (isClosed_le continuous_const hf.continuous).isCompact
    intro t ht
    apply (isConnected_superlevel_of_no_critical_values_above_minimum
      1 hf (hnd m hmc) hmin ht.1 ?_).isPreconnected
    intro x hx hc
    have hmem : x ∈ {y | IsCriticalPointAt (𝓡 2) f y} := hc
    rw [hC] at hmem
    change f m < f x ∧ f x ≤ t at hx
    have hts : t < f s := ht.2
    rcases hmem with rfl | rfl | rfl | rfl <;> linarith
  have hsmax : ¬ IsLocalMax f s := by
    intro hsmax
    have hi := maximum_morse_index_eq_finrank hf (hnd s hsc) hsmax
    rw [hsindex] at hi
    norm_num at hi
  obtain ⟨hcover, hdisj, _⟩ := hcomponents (f s) ⟨le_rfl, hsp⟩
  apply inter_closure_superlevel_components_eq_singleton (𝓡 2) hf hsp (hsp.trans hpq)
    hclosed hsmax hcover
  · intro heq
    exact disjoint_left.mp hdisj (mem_connectedComponentIn hsp)
      (heq ▸ mem_connectedComponentIn hsp)
  · intro x hx hc
    exact hinj hc hsc hx

end DifferentialGeometry.Topology.Morse
