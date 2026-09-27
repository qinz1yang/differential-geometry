import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakPartialTree.SmoothFiniteSource

noncomputable section

open Filter MeasureTheory Set
open scoped ContDiff ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem exists_lp_weak_partial_tree_of_weighted_divergence_source
    {p : ℝ≥0∞} (hp : 1 ≤ p)
    {I T : Set ℝ} (hI : IsOpen I) (hT : IsCompact T) (hTI : T ⊆ I)
    {O Ω : Set E} (hO : IsOpen O) (hΩ : IsOpen Ω)
    (hΩc : IsCompact (closure Ω)) (hΩO : closure Ω ⊆ O) (m : ℕ)
    (ρ : ℝ × E → ℝ) (A : Fin d → Fin d → ℝ × E → ℝ)
    (hρ : ContDiffOn ℝ (⊤ : ℕ∞) ρ (I ×ˢ O))
    (hρne : ∀ q ∈ I ×ˢ O, ρ q ≠ 0)
    (hA : ∀ i j, ContDiffOn ℝ (⊤ : ℕ∞) (A i j) (I ×ˢ O))
    (V F : ∀ n : ℕ, (Fin n → Fin d) →
      Lp ℝ p ((volume.restrict T).prod (volume.restrict Ω)))
    (R : Lp ℝ p ((volume.restrict T).prod (volume.restrict Ω)))
    (hV : ∀ n, n < m + 2 → ∀ α i, ∀ᵐ t ∂volume.restrict T,
      DeGiorgi.HasWeakPartialDeriv i
        (fun x => V (n + 1) (Fin.cons i α) (t, x))
        (fun x => V n α (t, x)) Ω)
    (hF : ∀ n, n < m → ∀ α i, ∀ᵐ t ∂volume.restrict T,
      DeGiorgi.HasWeakPartialDeriv i
        (fun x => F (n + 1) (Fin.cons i α) (t, x))
        (fun x => F n α (t, x)) Ω)
    (hR :
      let e : Fin 0 → Fin d := fun i => Fin.elim0 i
      R =ᵐ[(volume.restrict T).prod (volume.restrict Ω)] fun q => (ρ q)⁻¹ *
        ((∑ i, ∑ j, (A i j q * V 2 (Fin.cons j (Fin.cons i e)) q +
          fderiv ℝ (fun x => A i j (q.1, x)) q.2 (EuclideanSpace.single j 1) *
            V 1 (Fin.cons i e) q)) +
          F 0 e q - fderiv ℝ ρ q (1, 0) * V 0 e q)) :
    ∃ W : ∀ n : ℕ, (Fin n → Fin d) →
        Lp ℝ p ((volume.restrict T).prod (volume.restrict Ω)),
      W 0 (fun i => Fin.elim0 i) = R ∧
        ∀ n, n < m → ∀ α i, ∀ᵐ t ∂volume.restrict T,
          DeGiorgi.HasWeakPartialDeriv i
            (fun x => W (n + 1) (Fin.cons i α) (t, x))
            (fun x => W n α (t, x)) Ω := by
  classical
  let ν := (volume.restrict T).prod (volume.restrict Ω)
  let e : Fin 0 → Fin d := fun i => Fin.elim0 i
  let DA := fun i j (q : ℝ × E) =>
    fderiv ℝ (fun x => A i j (q.1, x)) q.2 (EuclideanSpace.single j 1)
  have hρinv : ContDiffOn ℝ (⊤ : ℕ∞) (fun q => (ρ q)⁻¹) (I ×ˢ O) := hρ.inv hρne
  have hDA (i j) : ContDiffOn ℝ (⊤ : ℕ∞) (DA i j) (I ×ˢ O) :=
    (DifferentialGeometry.Analysis.spatialFDeriv_contDiffOn
      (G := fun t x => A i j (t, x)) hI.uniqueDiffOn hO (hA i j)).clm_apply
      contDiffOn_const
  have hρt : ContDiffOn ℝ (⊤ : ℕ∞) (fun q => fderiv ℝ ρ q (1, 0)) (I ×ˢ O) :=
    (hρ.fderiv_of_isOpen (hI.prod hO) (by simp)).clm_apply contDiffOn_const
  let ι := (Fin d × Fin d) ⊕ ((Fin d × Fin d) ⊕ Bool)
  let Y : ι → ∀ n : ℕ, (Fin n → Fin d) → Lp ℝ p ν :=
    Sum.elim (fun ij n α => V (n + 2) (Fin.snoc (Fin.snoc α ij.2) ij.1))
      (Sum.elim (fun ij n α => V (n + 1) (Fin.snoc α ij.1))
        (fun z => if z then F else V))
  let B : ι → ℝ × E → ℝ :=
    Sum.elim (fun ij q => (ρ q)⁻¹ * A ij.1 ij.2 q)
      (Sum.elim (fun ij q => (ρ q)⁻¹ * DA ij.1 ij.2 q)
        (fun z q => if z then (ρ q)⁻¹ else -((ρ q)⁻¹ * fderiv ℝ ρ q (1, 0))))
  have hB (j : ι) : ContDiffOn ℝ (⊤ : ℕ∞) (B j) (I ×ˢ O) := by
    rcases j with ⟨i, j⟩ | (⟨i, j⟩ | z)
    · exact hρinv.mul (hA i j)
    · exact hρinv.mul (hDA i j)
    · cases z
      · exact (hρinv.mul hρt).neg
      · exact hρinv
  have hY (j : ι) (n : ℕ) (hn : n < m) (α : Fin n → Fin d) (k : Fin d) :
      ∀ᵐ t ∂volume.restrict T, DeGiorgi.HasWeakPartialDeriv k
        (fun x => Y j (n + 1) (Fin.cons k α) (t, x))
        (fun x => Y j n α (t, x)) Ω := by
    rcases j with ⟨i, j⟩ | (⟨i, j⟩ | z)
    · simpa only [Y, Sum.elim_inl, Fin.cons_snoc_eq_snoc_cons] using
        hV (n + 2) (by omega) (Fin.snoc (Fin.snoc α j) i) k
    · simpa only [Y, Sum.elim_inr, Sum.elim_inl, Fin.cons_snoc_eq_snoc_cons] using
        hV (n + 1) (by omega) (Fin.snoc α i) k
    · cases z
      · exact hV n (by omega) α k
      · exact hF n hn α k
  have hsingle (i : Fin d) : Fin.snoc e i = (Fin.cons i e : Fin 1 → Fin d) := by
    funext j
    refine Fin.cases ?_ (fun k => Fin.elim0 k) j
    rfl
  have hdouble (i j : Fin d) :
      Fin.snoc (Fin.cons j e) i = (Fin.cons j (Fin.cons i e) : Fin 2 → Fin d) := by
    rw [← Fin.cons_snoc_eq_snoc_cons, hsingle]
  have hRsum : R =ᵐ[ν] fun q => ∑ j, B j q * Y j 0 e q := by
    filter_upwards [hR] with q hq
    change R q = (ρ q)⁻¹ *
      ((∑ i, ∑ j, (A i j q * V 2 (Fin.cons j (Fin.cons i e)) q +
        DA i j q * V 1 (Fin.cons i e) q)) +
          F 0 e q - fderiv ℝ ρ q (1, 0) * V 0 e q) at hq
    rw [hq]
    change _ = ∑ j : (Fin d × Fin d) ⊕ ((Fin d × Fin d) ⊕ Bool), B j q * Y j 0 e q
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp only [B, Y, Fintype.sum_prod_type, Fintype.sum_bool, Sum.elim_inl, Sum.elim_inr,
      Bool.false_eq_true, ↓reduceIte, hsingle, hdouble]
    simp only [mul_sub, mul_add, Finset.mul_sum, Finset.sum_add_distrib, mul_assoc]
    ring
  exact exists_lp_weak_partial_tree_of_smooth_finite_sum hp hI.uniqueDiffOn hT hTI
    hO hΩ hΩc hΩO m R B Y hB hY hRsum

end DifferentialGeometry.Analysis.Sobolev.Euclidean
