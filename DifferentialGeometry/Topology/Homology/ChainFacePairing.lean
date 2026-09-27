import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SimplexBoundary
import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.Cycles
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.BigOperators.Ring.Finset

noncomputable section

open scoped Simplicial

universe u v w

namespace Module.Basis

private theorem exists_equiv_of_sum_eq {R A I J V : Type*} [Fintype I] [Fintype J]
    [Semiring R] [CharZero R] [AddCommMonoid V] [Module R V] (b : Basis A R V) (f : I → A) (g : J → A)
    (h : ∑ i, b (f i) = ∑ j, b (g j)) : ∃ e : I ≃ J, ∀ i, f i = g (e i) := by
  classical
  have hcard (a : A) : Fintype.card {i // f i = a} = Fintype.card {j // g j = a} := by
    have ha := congrArg (fun v => b.repr v a) h
    simpa [map_sum, Finsupp.finsetSum_apply, b.repr_self, Finsupp.single_apply,
      Finset.sum_boole, Fintype.card_subtype] using ha
  let e (a : A) := Fintype.equivOfCardEq (hcard a)
  exact ⟨Equiv.ofFiberEquiv e, fun i => (Equiv.ofFiberEquiv_map e i).symm⟩

end Module.Basis



namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

private theorem exists_fin_sum_sub_sum_basis {A V : Type u}
    [AddCommGroup V] [modV : Module ℤ V] (b : Module.Basis A ℤ V) (v : V) :
    ∃ m n : ℕ, ∃ f : Fin m → A, ∃ g : Fin n → A,
      v = (∑ i, b (f i)) - ∑ j, b (g j) := by
  classical
  let c := b.repr v
  let S := ↥c.support
  let P := (i : S) × Fin ((c i).toNat)
  let N := (i : S) × Fin ((-c i).toNat)
  let f : P → A := fun i => i.1.val
  let g : N → A := fun i => i.1.val
  have hv : v = (∑ i : P, b (f i)) - ∑ j : N, b (g j) := by
    rw [Fintype.sum_sigma, Fintype.sum_sigma]
    simp only [f, g, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    rw [← Finset.sum_sub_distrib]
    have heq (i : S) : (c i).toNat • b i.val - (-c i).toNat • b i.val = c i • b i.val := by
      generalize c i = k
      cases k <;> simp
    simp_rw [heq]
    change v = ∑ i : ↥c.support, (fun a => c a • b a) i.val
    have hrecon : v = ∑ i ∈ c.support, c i • b i := by
      have hrepr := (b.linearCombination_repr v).symm
      rw [Finsupp.linearCombination_apply, Finsupp.sum] at hrepr
      have hsmul : (∑ a ∈ c.support, @SMul.smul ℤ V modV.toSMul (c a) (b a)) =
          ∑ a ∈ c.support, c a • b a := by
        apply Finset.sum_congr rfl
        intro a ha
        exact int_smul_eq_zsmul modV _ _
      exact hrepr.trans hsmul
    exact hrecon.trans (Finset.sum_coe_sort c.support (fun a => c a • b a)).symm
  refine ⟨Fintype.card P, Fintype.card N,
    f ∘ (Fintype.equivFin P).symm, g ∘ (Fintype.equivFin N).symm, ?_⟩
  change v = (∑ i, b (f ((Fintype.equivFin P).symm i))) -
    ∑ j, b (g ((Fintype.equivFin N).symm j))
  rw [(Fintype.equivFin P).symm.sum_comp (fun i => b (f i)),
    (Fintype.equivFin N).symm.sum_comp (fun i => b (g i))]
  exact hv

theorem exists_integralSingularChain_eq_sum_sub_sum (n : ℕ)
    (z : (integralSingularChains X).X n) :
    ∃ a b : ℕ, ∃ σ : Fin a → integralSingularSimplex n X,
      ∃ τ : Fin b → integralSingularSimplex n X,
        z = (∑ i, integralSimplexChain n (σ i)) - ∑ j, integralSimplexChain n (τ j) := by
  obtain ⟨a, b, σ, τ, h⟩ := exists_fin_sum_sub_sum_basis (integralSingularChainBasis n X) z
  exact ⟨a, b, σ, τ, by simpa only [integralSingularChainBasis_apply] using h⟩


variable {A : Type v} {B : Type w} [Fintype A] [Fintype B]

theorem exists_signed_face_pairing_of_cycle
    (p : A → integralSingularSimplex 3 X) (q : B → integralSingularSimplex 3 X)
    (h : (integralSingularChains X).d 3 2
      ((∑ a, integralSimplexChain 3 (p a)) - (∑ b, integralSimplexChain 3 (q b))) = 0) :
    ∃ e : ((A × Fin 2) ⊕ (B × Fin 2)) ≃ ((A × Fin 2) ⊕ (B × Fin 2)),
      ∀ i,
        (match i with
        | Sum.inl a =>
          (TopCat.toSSet.obj (TopCat.of X)).δ (if a.2 = 0 then 0 else 2) (p a.1)
        | Sum.inr b =>
          (TopCat.toSSet.obj (TopCat.of X)).δ (if b.2 = 0 then 1 else 3) (q b.1)) =
        (match e i with
        | Sum.inl a =>
          (TopCat.toSSet.obj (TopCat.of X)).δ (if a.2 = 0 then 1 else 3) (p a.1)
        | Sum.inr b =>
          (TopCat.toSSet.obj (TopCat.of X)).δ (if b.2 = 0 then 0 else 2) (q b.1)) := by
  let even (σ : integralSingularSimplex 3 X) (j : Fin 2) : integralSingularSimplex 2 X :=
    if j = 0 then (TopCat.toSSet.obj (TopCat.of X)).δ 0 σ else
      (TopCat.toSSet.obj (TopCat.of X)).δ 2 σ
  let odd (σ : integralSingularSimplex 3 X) (j : Fin 2) : integralSingularSimplex 2 X :=
    if j = 0 then (TopCat.toSSet.obj (TopCat.of X)).δ 1 σ else
      (TopCat.toSSet.obj (TopCat.of X)).δ 3 σ
  let pos : ((A × Fin 2) ⊕ (B × Fin 2)) → integralSingularSimplex 2 X :=
    Sum.elim (fun a => even (p a.1) a.2) (fun b => odd (q b.1) b.2)
  let neg : ((A × Fin 2) ⊕ (B × Fin 2)) → integralSingularSimplex 2 X :=
    Sum.elim (fun a => odd (p a.1) a.2) (fun b => even (q b.1) b.2)
  have hbound (σ : integralSingularSimplex 3 X) :
      (integralSingularChains X).d 3 2 (integralSimplexChain 3 σ) =
        (∑ j : Fin 2, integralSimplexChain 2 (even σ j)) -
          (∑ j : Fin 2, integralSimplexChain 2 (odd σ j)) := by
    convert (integralSimplexChain_boundary 2 σ) using 1
    simp only [even, odd, Fin.sum_univ_succ]
    norm_num
    abel
  have h' : ((∑ a, ∑ j : Fin 2, integralSimplexChain 2 (even (p a) j)) -
      (∑ a, ∑ j : Fin 2, integralSimplexChain 2 (odd (p a) j))) -
      ((∑ b, ∑ j : Fin 2, integralSimplexChain 2 (even (q b) j)) -
      (∑ b, ∑ j : Fin 2, integralSimplexChain 2 (odd (q b) j))) = 0 := by
    simpa only [map_sub, map_sum, hbound, Finset.sum_sub_distrib] using h
  have hsum : (∑ i, (integralSingularChainBasis 2 X) (pos i)) =
      ∑ i, (integralSingularChainBasis 2 X) (neg i) := by
    apply sub_eq_zero.mp
    simp only [pos, neg, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      Fintype.sum_prod_type, integralSingularChainBasis_apply]
    convert h' using 1
    abel
  obtain ⟨e, he⟩ := Module.Basis.exists_equiv_of_sum_eq
    (integralSingularChainBasis 2 X) pos neg hsum
  refine ⟨e, ?_⟩
  intro i
  cases i with
  | inl a =>
    cases hEi : e (Sum.inl a) with
    | inl a' =>
      by_cases h0 : a.2 = 0 <;> by_cases h1 : a'.2 = 0 <;>
        simpa [pos, neg, even, odd, hEi, h0, h1] using he (Sum.inl a)
    | inr b' =>
      by_cases h0 : a.2 = 0 <;> by_cases h1 : b'.2 = 0 <;>
        simpa [pos, neg, even, odd, hEi, h0, h1] using he (Sum.inl a)
  | inr b =>
    cases hEi : e (Sum.inr b) with
    | inl a' =>
      by_cases h0 : b.2 = 0 <;> by_cases h1 : a'.2 = 0 <;>
        simpa [pos, neg, even, odd, hEi, h0, h1] using he (Sum.inr b)
    | inr b' =>
      by_cases h0 : b.2 = 0 <;> by_cases h1 : b'.2 = 0 <;>
        simpa [pos, neg, even, odd, hEi, h0, h1] using he (Sum.inr b)


omit [Fintype A] [Fintype B] in
theorem exists_signed_simplex_representation_of_three_cycle
    (z : integralSingularCycles 2 X) :
    ∃ a b : ℕ, ∃ p : Fin a → integralSingularSimplex 3 X,
      ∃ q : Fin b → integralSingularSimplex 3 X,
        z.val = (∑ i, integralSimplexChain 3 (p i)) - ∑ j, integralSimplexChain 3 (q j) ∧
        ∃ e : ((Fin a × Fin 2) ⊕ (Fin b × Fin 2)) ≃
            ((Fin a × Fin 2) ⊕ (Fin b × Fin 2)),
          ∀ i,
            (match i with
            | Sum.inl a =>
              (TopCat.toSSet.obj (TopCat.of X)).δ (if a.2 = 0 then 0 else 2) (p a.1)
            | Sum.inr b =>
              (TopCat.toSSet.obj (TopCat.of X)).δ (if b.2 = 0 then 1 else 3) (q b.1)) =
            (match e i with
            | Sum.inl a =>
              (TopCat.toSSet.obj (TopCat.of X)).δ (if a.2 = 0 then 1 else 3) (p a.1)
            | Sum.inr b =>
              (TopCat.toSSet.obj (TopCat.of X)).δ (if b.2 = 0 then 0 else 2) (q b.1)) := by
  obtain ⟨a, b, p, q, hz⟩ := exists_integralSingularChain_eq_sum_sub_sum 3 z.val
  have hc : (integralSingularChains X).d 3 2
      ((∑ i, integralSimplexChain 3 (p i)) - ∑ j, integralSimplexChain 3 (q j)) = 0 := by
    rw [← hz]
    exact z.property
  obtain ⟨e, he⟩ := exists_signed_face_pairing_of_cycle p q hc
  refine ⟨a, b, p, q, hz, e, ?_⟩
  intro i
  cases i with
  | inl i =>
    cases hi : e (Sum.inl i) <;> simpa only [hi] using he (Sum.inl i)
  | inr i =>
    cases hi : e (Sum.inr i) <;> simpa only [hi] using he (Sum.inr i)

end DifferentialGeometry.Topology
