import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakPartialTree.SmoothFiniteSource

noncomputable section

open Filter MeasureTheory Set
open scoped ContDiff ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem exists_lp_weak_partial_tree_of_weighted_gradient_source
    {p : ℝ≥0∞} (hp : 1 ≤ p)
    {I T : Set ℝ} (hI : IsOpen I) (hT : IsCompact T) (hTI : T ⊆ I)
    {O Ω : Set E} (hO : IsOpen O) (hΩ : IsOpen Ω)
    (hΩc : IsCompact (closure Ω)) (hΩO : closure Ω ⊆ O) (m : ℕ)
    (ρ : ℝ × E → ℝ) (A : Fin d → Fin d → ℝ × E → ℝ)
    (hρ : ContDiffOn ℝ (⊤ : ℕ∞) ρ (I ×ˢ O))
    (hA : ∀ i j, ContDiffOn ℝ (⊤ : ℕ∞) (A i j) (I ×ˢ O))
    (V F R : ∀ n : ℕ, (Fin n → Fin d) →
      Lp ℝ p ((volume.restrict T).prod (volume.restrict Ω)))
    (S : Fin d → Lp ℝ p ((volume.restrict T).prod (volume.restrict Ω)))
    (hV : ∀ n, n < m + 2 → ∀ α i, ∀ᵐ t ∂volume.restrict T,
      DeGiorgi.HasWeakPartialDeriv i
        (fun x => V (n + 1) (Fin.cons i α) (t, x))
        (fun x => V n α (t, x)) Ω)
    (hF : ∀ n, n < m + 1 → ∀ α i, ∀ᵐ t ∂volume.restrict T,
      DeGiorgi.HasWeakPartialDeriv i
        (fun x => F (n + 1) (Fin.cons i α) (t, x))
        (fun x => F n α (t, x)) Ω)
    (hR : ∀ n, n < m → ∀ α i, ∀ᵐ t ∂volume.restrict T,
      DeGiorgi.HasWeakPartialDeriv i
        (fun x => R (n + 1) (Fin.cons i α) (t, x))
        (fun x => R n α (t, x)) Ω)
    (hS :
      let e : Fin 0 → Fin d := fun i => Fin.elim0 i
      ∀ k, S k =ᵐ[(volume.restrict T).prod (volume.restrict Ω)] fun q =>
        F 1 (Fin.cons k e) q +
          (∑ i, ∑ j, (fderiv ℝ (A i j) q (0, EuclideanSpace.single k 1) *
            V 2 (Fin.cons j (Fin.cons i e)) q +
            fderiv ℝ (fun w => fderiv ℝ (A i j) w (0, EuclideanSpace.single k 1)) q
              (0, EuclideanSpace.single j 1) * V 1 (Fin.cons i e) q)) -
          (fderiv ℝ ρ q (0, EuclideanSpace.single k 1) * R 0 e q +
            fderiv ℝ (fun w => fderiv ℝ ρ w (0, EuclideanSpace.single k 1)) q (1, 0) *
              V 0 e q)) :
    ∃ W : Fin d → ∀ n : ℕ, (Fin n → Fin d) →
        Lp ℝ p ((volume.restrict T).prod (volume.restrict Ω)),
      (∀ k, W k 0 (fun i => Fin.elim0 i) = S k) ∧
        ∀ k n, n < m → ∀ α i, ∀ᵐ t ∂volume.restrict T,
          DeGiorgi.HasWeakPartialDeriv i
            (fun x => W k (n + 1) (Fin.cons i α) (t, x))
            (fun x => W k n α (t, x)) Ω := by
  classical
  let ν := (volume.restrict T).prod (volume.restrict Ω)
  let e : Fin 0 → Fin d := fun i => Fin.elim0 i
  let B := fun k i j (q : ℝ × E) => fderiv ℝ (A i j) q (0, EuclideanSpace.single k 1)
  let C := fun k i j (q : ℝ × E) => fderiv ℝ (B k i j) q (0, EuclideanSpace.single j 1)
  let r := fun k (q : ℝ × E) => fderiv ℝ ρ q (0, EuclideanSpace.single k 1)
  let s := fun k (q : ℝ × E) => fderiv ℝ (r k) q (1, 0)
  have hd (f : ℝ × E → ℝ) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (I ×ˢ O)) (v : ℝ × E) :
      ContDiffOn ℝ (⊤ : ℕ∞) (fun q => fderiv ℝ f q v) (I ×ˢ O) :=
    (hf.fderiv_of_isOpen (hI.prod hO) (by simp)).clm_apply contDiffOn_const
  have hB (k i j) : ContDiffOn ℝ (⊤ : ℕ∞) (B k i j) (I ×ˢ O) := hd _ (hA i j) _
  have hC (k i j) : ContDiffOn ℝ (⊤ : ℕ∞) (C k i j) (I ×ˢ O) := hd _ (hB k i j) _
  have hr (k) : ContDiffOn ℝ (⊤ : ℕ∞) (r k) (I ×ˢ O) := hd _ hρ _
  have hs (k) : ContDiffOn ℝ (⊤ : ℕ∞) (s k) (I ×ˢ O) := hd _ (hr k) _
  let ι := ((Fin d × Fin d) ⊕ (Fin d × Fin d)) ⊕ (Unit ⊕ Bool)
  let Y : Fin d → ι → ∀ n : ℕ, (Fin n → Fin d) → Lp ℝ p ν := fun k =>
    Sum.elim
      (Sum.elim (fun ij n α => V (n + 2) (Fin.snoc (Fin.snoc α ij.2) ij.1))
        (fun ij n α => V (n + 1) (Fin.snoc α ij.1)))
      (Sum.elim (fun _ n α => F (n + 1) (Fin.snoc α k))
        (fun z => if z then R else V))
  let D : Fin d → ι → ℝ × E → ℝ := fun k =>
    Sum.elim (Sum.elim (fun ij => B k ij.1 ij.2) (fun ij => C k ij.1 ij.2))
      (Sum.elim (fun _ _ => 1) (fun z q => if z then -r k q else -s k q))
  have hD (k) (j : ι) : ContDiffOn ℝ (⊤ : ℕ∞) (D k j) (I ×ˢ O) := by
    rcases j with (⟨i, j⟩ | ⟨i, j⟩) | (_ | z)
    · exact hB k i j
    · exact hC k i j
    · exact contDiffOn_const
    · cases z
      · exact (hs k).neg
      · exact (hr k).neg
  have hY (k) (j : ι) (n : ℕ) (hn : n < m) (α : Fin n → Fin d) (l : Fin d) :
      ∀ᵐ t ∂volume.restrict T, DeGiorgi.HasWeakPartialDeriv l
        (fun x => Y k j (n + 1) (Fin.cons l α) (t, x))
        (fun x => Y k j n α (t, x)) Ω := by
    rcases j with (⟨i, j⟩ | ⟨i, j⟩) | (_ | z)
    · simpa only [Y, Sum.elim_inl, Fin.cons_snoc_eq_snoc_cons] using
        hV (n + 2) (by omega) (Fin.snoc (Fin.snoc α j) i) l
    · simpa only [Y, Sum.elim_inl, Sum.elim_inr, Fin.cons_snoc_eq_snoc_cons] using
        hV (n + 1) (by omega) (Fin.snoc α i) l
    · simpa only [Y, Sum.elim_inl, Sum.elim_inr, Fin.cons_snoc_eq_snoc_cons] using
        hF (n + 1) (by omega) (Fin.snoc α k) l
    · cases z
      · exact hV n (by omega) α l
      · exact hR n hn α l
  have hsingle (i : Fin d) : Fin.snoc e i = (Fin.cons i e : Fin 1 → Fin d) := by
    funext j
    refine Fin.cases ?_ (fun k => Fin.elim0 k) j
    rfl
  have hdouble (i j : Fin d) :
      Fin.snoc (Fin.cons j e) i = (Fin.cons j (Fin.cons i e) : Fin 2 → Fin d) := by
    rw [← Fin.cons_snoc_eq_snoc_cons, hsingle]
  have hSsum (k) : S k =ᵐ[ν] fun q => ∑ j, D k j q * Y k j 0 e q := by
    filter_upwards [hS k] with q hq
    change S k q = F 1 (Fin.cons k e) q +
      (∑ i, ∑ j, (B k i j q * V 2 (Fin.cons j (Fin.cons i e)) q +
        C k i j q * V 1 (Fin.cons i e) q)) -
      (r k q * R 0 e q + s k q * V 0 e q) at hq
    rw [hq]
    change _ = ∑ j : ((Fin d × Fin d) ⊕ (Fin d × Fin d)) ⊕ (Unit ⊕ Bool),
      D k j q * Y k j 0 e q
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp only [D, Y, Fintype.sum_prod_type, Fintype.sum_bool, Fintype.sum_unique,
      Sum.elim_inl, Sum.elim_inr, Bool.false_eq_true, ↓reduceIte, hsingle, hdouble,
      one_mul, neg_mul, Finset.sum_add_distrib]
    ring
  choose W hroot hweak using fun k =>
    exists_lp_weak_partial_tree_of_smooth_finite_sum hp hI.uniqueDiffOn hT hTI
      hO hΩ hΩc hΩO m (S k) (D k) (Y k) (hD k) (hY k) (hSsum k)
  exact ⟨W, hroot, hweak⟩

end DifferentialGeometry.Analysis.Sobolev.Euclidean
