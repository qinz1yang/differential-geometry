import DifferentialGeometry.Topology.PiecewiseLinear.GeneralPosition
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedronIn
import Mathlib.SetTheory.Cardinal.Finite

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_reindexed_piercing_family_of_strict_decrease
    {E M ι : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [Finite ι] [Nonempty ι]
    {A B D A' B' D' : E → Set M} {cnt : E → ℕ} {Pg : E → ℕ → Set M}
    (e₀ : E) (C : ι → Set M)
    (htrace : ∀ e, 0 < cnt e ∧ A e ∩ B e = ⋃ i < cnt e, Pg e i)
    (hsphere : ∀ e, ∀ i < cnt e, IsPolyhedralSphere (n := 3) 1 (Pg e i) ∧ Pg e i ⊆ D e)
    (hdisj : ∀ e, ∀ i < cnt e, ∀ j < cnt e, i ≠ j → Disjoint (Pg e i) (Pg e j))
    (hcross : ∀ e, ∀ y ∈ A e ∩ B e,
      ∃ c ∈ (plGroupoid 3).maximalAtlas M, y ∈ c.source ∧
        HasPLCrossingAt (c '' (A e ∩ c.source)) (c '' (B e ∩ c.source)) (c y))
    (hforeign : ∀ e, e ≠ e₀ → A' e = A e ∧ B' e = B e ∧ D' e = D e)
    (hCtrace : A' e₀ ∩ B' e₀ = ⋃ i, C i)
    (hCsphere : ∀ i, IsPolyhedralSphere (n := 3) 1 (C i) ∧ C i ⊆ D' e₀)
    (hCdisj : Pairwise fun i j => Disjoint (C i) (C j))
    (hCcross : ∀ y ∈ A' e₀ ∩ B' e₀,
      ∃ c ∈ (plGroupoid 3).maximalAtlas M, y ∈ c.source ∧
        HasPLCrossingAt (c '' (A' e₀ ∩ c.source)) (c '' (B' e₀ ∩ c.source)) (c y))
    (hcard : Nat.card ι < cnt e₀) :
    ∃ (cnt' : E → ℕ) (Pg' : E → ℕ → Set M),
      cnt' e₀ = Nat.card ι ∧ cnt' e₀ < cnt e₀ ∧
      (∀ e, e ≠ e₀ → cnt' e = cnt e ∧ Pg' e = Pg e) ∧
      (∀ e, 0 < cnt' e ∧ A' e ∩ B' e = ⋃ i < cnt' e, Pg' e i) ∧
      (∀ e, ∀ i < cnt' e, IsPolyhedralSphere (n := 3) 1 (Pg' e i) ∧ Pg' e i ⊆ D' e) ∧
      (∀ e, ∀ i < cnt' e, ∀ j < cnt' e, i ≠ j → Disjoint (Pg' e i) (Pg' e j)) ∧
      ∀ e, ∀ y ∈ A' e ∩ B' e,
        ∃ c ∈ (plGroupoid 3).maximalAtlas M, y ∈ c.source ∧
          HasPLCrossingAt (c '' (A' e ∩ c.source)) (c '' (B' e ∩ c.source)) (c y) := by
  classical
  let r : ι ≃ Fin (Nat.card ι) := Nat.equivFinOfCardPos Nat.card_pos.ne'
  let Pc : ℕ → Set M := fun i =>
    if hi : i < Nat.card ι then C (r.symm ⟨i, hi⟩) else ∅
  have hPc (i : ℕ) (hi : i < Nat.card ι) : Pc i = C (r.symm ⟨i, hi⟩) := by
    simp only [Pc, dite_eq_left hi]
  have hcover : (⋃ i < Nat.card ι, Pc i) = ⋃ j, C j := by
    ext y
    constructor
    · intro hy
      obtain ⟨i, hi, hy⟩ := mem_iUnion₂.mp hy
      rw [hPc i hi] at hy
      exact mem_iUnion.mpr ⟨r.symm ⟨i, hi⟩, hy⟩
    · intro hy
      obtain ⟨j, hy⟩ := mem_iUnion.mp hy
      refine mem_iUnion₂.mpr ⟨(r j).val, (r j).isLt, ?_⟩
      simpa only [hPc _ (r j).isLt, r.symm_apply_apply] using hy
  have hPcdisj : ∀ i < Nat.card ι, ∀ j < Nat.card ι,
      i ≠ j → Disjoint (Pc i) (Pc j) := by
    intro i hi j hj hij
    rw [hPc i hi, hPc j hj]
    apply hCdisj
    intro heq
    exact hij (congrArg Fin.val (r.symm.injective heq))
  let cnt' := Function.update cnt e₀ (Nat.card ι)
  let Pg' := Function.update Pg e₀ Pc
  have hcnt : cnt' e₀ = Nat.card ι := Function.update_self _ _ _
  have hPg : Pg' e₀ = Pc := Function.update_self _ _ _
  have hother : ∀ e, e ≠ e₀ → cnt' e = cnt e ∧ Pg' e = Pg e := by
    intro e he
    exact ⟨Function.update_of_ne he _ _, Function.update_of_ne he _ _⟩
  refine ⟨cnt', Pg', hcnt, hcnt ▸ hcard, hother, ?_, ?_, ?_, ?_⟩
  · intro e
    by_cases he : e = e₀
    · subst e
      rw [hcnt, hPg]
      exact ⟨Nat.card_pos, hCtrace.trans hcover.symm⟩
    · rw [(hother e he).1, (hother e he).2,
        (hforeign e he).1, (hforeign e he).2.1]
      exact htrace e
  · intro e i hi
    by_cases he : e = e₀
    · subst e
      rw [hcnt] at hi
      rw [hPg, hPc i hi]
      exact hCsphere _
    · rw [(hother e he).1] at hi
      rw [(hother e he).2, (hforeign e he).2.2]
      exact hsphere e i hi
  · intro e i hi j hj hij
    by_cases he : e = e₀
    · subst e
      rw [hcnt] at hi hj
      rw [hPg]
      exact hPcdisj i hi j hj hij
    · rw [(hother e he).1] at hi hj
      rw [(hother e he).2]
      exact hdisj e i hi j hj hij
  · intro e y hy
    by_cases he : e = e₀
    · subst e
      exact hCcross y hy
    · rw [(hforeign e he).1, (hforeign e he).2.1] at hy ⊢
      exact hcross e y hy

end DifferentialGeometry.Topology.PiecewiseLinear
