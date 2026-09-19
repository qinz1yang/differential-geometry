import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivativeProduct

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

private def mixedJetIndex : (n : ℕ) → (Fin n → Fin (d + 1)) →
    (ℕ × (Σ r : ℕ, Fin r → Fin d))
  | 0, _ => ⟨0, 0, fun i => Fin.elim0 i⟩
  | n + 1, α =>
      let z := mixedJetIndex n (Fin.tail α)
      Fin.cases ⟨z.1 + 1, z.2.1, z.2.2⟩
        (fun i => ⟨z.1, z.2.1 + 1, Fin.cons i z.2.2⟩) (α 0)

private theorem mixedJetIndex_add (n : ℕ) (α : Fin n → Fin (d + 1)) :
    (mixedJetIndex n α).1 + (mixedJetIndex n α).2.1 = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hz := ih (Fin.tail α)
      unfold mixedJetIndex
      generalize h : α 0 = i
      refine Fin.cases ?_ (fun i => ?_) i <;> simp only [Fin.cases_zero, Fin.cases_succ]
      · omega
      · omega

private theorem mixedJetIndex_cons_zero (n : ℕ) (α : Fin n → Fin (d + 1)) :
    mixedJetIndex (n + 1) (Fin.cons 0 α) =
      ⟨(mixedJetIndex n α).1 + 1, (mixedJetIndex n α).2⟩ := by
  conv_lhs => unfold mixedJetIndex
  rw [Fin.tail_cons, Fin.cons_zero]
  simp only [Fin.cases_zero]

private theorem mixedJetIndex_cons_succ (n : ℕ) (α : Fin n → Fin (d + 1)) (i : Fin d) :
    mixedJetIndex (n + 1) (Fin.cons i.succ α) =
      ⟨(mixedJetIndex n α).1,
        (mixedJetIndex n α).2.1 + 1, Fin.cons i (mixedJetIndex n α).2.2⟩ := by
  conv_lhs => unfold mixedJetIndex
  rw [Fin.tail_cons, Fin.cons_zero]
  simp only [Fin.cases_succ]

theorem exists_lp_mixed_weak_partial_tree
    {p : ℝ≥0∞} (hp : 1 ≤ p) {a b : ℝ} {Ω : Set E} (K : ℕ)
    (U : ℕ → ∀ n : ℕ, (Fin n → Fin d) →
      Lp ℝ p ((volume.restrict (Icc a b)).prod (volume.restrict Ω)))
    (hspace : ∀ j n, j + n < K → ∀ α i, ∀ᵐ t ∂volume.restrict (Icc a b),
      DeGiorgi.HasWeakPartialDeriv i
        (fun x => U j (n + 1) (Fin.cons i α) (t, x)) (fun x => U j n α (t, x)) Ω)
    (htime : ∀ j n, j + n < K → ∀ α (φ : ℝ × E → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ Ioo a b ×ˢ Ω →
      (∫ q, U j n α q * fderiv ℝ φ q (1, 0)
        ∂(volume.restrict (Icc a b)).prod (volume.restrict Ω)) =
        -∫ q, U (j + 1) n α q * φ q
          ∂(volume.restrict (Icc a b)).prod (volume.restrict Ω)) :
    let ν := (volume.restrict (Icc a b)).prod (volume.restrict Ω)
    ∃ Y : ∀ n : ℕ, (Fin n → Fin (d + 1)) → Lp ℝ p ν,
      Y 0 (fun i => Fin.elim0 i) = U 0 0 (fun i => Fin.elim0 i) ∧
      ∀ n < K, ∀ α i (φ : ℝ × E → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ →
        HasCompactSupport φ → tsupport φ ⊆ Ioo a b ×ˢ Ω →
        (∫ q, Y n α q * fderiv ℝ φ q
          (Fin.cases (1, 0) (fun l => (0, EuclideanSpace.single l 1)) i) ∂ν) =
          -∫ q, Y (n + 1) (Fin.cons i α) q * φ q ∂ν := by
  intro ν
  let Y : ∀ n : ℕ, (Fin n → Fin (d + 1)) → Lp ℝ p ν := fun n α =>
    U (mixedJetIndex n α).1 (mixedJetIndex n α).2.1 (mixedJetIndex n α).2.2
  refine ⟨Y, rfl, ?_⟩
  intro n hn α i φ hφ hφc hφs
  have hbudget := mixedJetIndex_add n α
  have hYtime : Y (n + 1) (Fin.cons 0 α) =
      U ((mixedJetIndex n α).1 + 1) (mixedJetIndex n α).2.1 (mixedJetIndex n α).2.2 :=
    congrArg (fun z : ℕ × (Σ r : ℕ, Fin r → Fin d) => U z.1 z.2.1 z.2.2)
      (mixedJetIndex_cons_zero n α)
  have hYspace (i : Fin d) : Y (n + 1) (Fin.cons i.succ α) =
      U (mixedJetIndex n α).1 ((mixedJetIndex n α).2.1 + 1)
        (Fin.cons i (mixedJetIndex n α).2.2) :=
    congrArg (fun z : ℕ × (Σ r : ℕ, Fin r → Fin d) => U z.1 z.2.1 z.2.2)
      (mixedJetIndex_cons_succ n α i)
  refine Fin.cases ?_ (fun i => ?_) i
  · rw [hYtime]
    simpa only [Y, Fin.cases_zero] using
      htime (mixedJetIndex n α).1 (mixedJetIndex n α).2.1 (by omega)
        (mixedJetIndex n α).2.2 φ hφ hφc hφs
  · have h := integral_fderiv_prod_eq_neg_of_hasWeakPartialDeriv
      ((Lp.memLp (Y n α)).locallyIntegrable hp)
      ((Lp.memLp (U (mixedJetIndex n α).1 ((mixedJetIndex n α).2.1 + 1)
        (Fin.cons i (mixedJetIndex n α).2.2))).locallyIntegrable hp)
      i (hspace (mixedJetIndex n α).1 (mixedJetIndex n α).2.1 (by omega)
        (mixedJetIndex n α).2.2 i) φ hφ hφc
      (hφs.trans (prod_mono (subset_univ _) Subset.rfl))
    rw [hYspace]
    simpa only [Y, Fin.cases_succ] using h

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem exists_lp_mixed_weak_partial_tree_of_finite_time_trees
    {p : ℝ≥0∞} (hp : 1 ≤ p) {a b : ℝ} {Ω : Set E} (K : ℕ)
    (U : Fin (K + 1) → ∀ n : ℕ, (Fin n → Fin d) →
      Lp ℝ p ((volume.restrict (Icc a b)).prod (volume.restrict Ω)))
    (hspace : ∀ j n, j.val + n < K → ∀ α i, ∀ᵐ t ∂volume.restrict (Icc a b),
      DeGiorgi.HasWeakPartialDeriv i
        (fun x => U j (n + 1) (Fin.cons i α) (t, x)) (fun x => U j n α (t, x)) Ω)
    (htime : ∀ (j : Fin K) n, j.val + n < K → ∀ α (φ : ℝ × E → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ Ioo a b ×ˢ Ω →
      (∫ q, U j.castSucc n α q * fderiv ℝ φ q (1, 0)
        ∂(volume.restrict (Icc a b)).prod (volume.restrict Ω)) =
        -∫ q, U j.succ n α q * φ q
          ∂(volume.restrict (Icc a b)).prod (volume.restrict Ω)) :
    let ν := (volume.restrict (Icc a b)).prod (volume.restrict Ω)
    ∃ Y : ∀ n : ℕ, (Fin n → Fin (d + 1)) → Lp ℝ p ν,
      Y 0 (fun i => Fin.elim0 i) = U 0 0 (fun i => Fin.elim0 i) ∧
      ∀ n < K, ∀ α i (φ : ℝ × E → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ →
        HasCompactSupport φ → tsupport φ ⊆ Ioo a b ×ˢ Ω →
        (∫ q, Y n α q * fderiv ℝ φ q
          (Fin.cases (1, 0) (fun l => (0, EuclideanSpace.single l 1)) i) ∂ν) =
          -∫ q, Y (n + 1) (Fin.cons i α) q * φ q ∂ν := by
  intro ν
  classical
  let V : ℕ → ∀ n : ℕ, (Fin n → Fin d) → Lp ℝ p ν :=
    fun j n α => if hj : j < K + 1 then U ⟨j, hj⟩ n α else 0
  have hVspace j n (hjn : j + n < K) :
      ∀ α i, ∀ᵐ t ∂volume.restrict (Icc a b), DeGiorgi.HasWeakPartialDeriv i
        (fun x => V j (n + 1) (Fin.cons i α) (t, x)) (fun x => V j n α (t, x)) Ω := by
    have hj : j < K + 1 := by omega
    simpa only [V, dif_pos hj] using hspace ⟨j, hj⟩ n hjn
  have hVtime j n (hjn : j + n < K) : ∀ α (φ : ℝ × E → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ Ioo a b ×ˢ Ω →
      (∫ q, V j n α q * fderiv ℝ φ q (1, 0) ∂ν) =
        -∫ q, V (j + 1) n α q * φ q ∂ν := by
    have hj : j < K := by omega
    have hj₀ : j < K + 1 := by omega
    have hj₁ : j + 1 < K + 1 := by omega
    have hcast : (⟨j, hj⟩ : Fin K).castSucc = ⟨j, hj₀⟩ := Fin.ext rfl
    have hsucc : (⟨j, hj⟩ : Fin K).succ = ⟨j + 1, hj₁⟩ := Fin.ext rfl
    simpa only [V, dif_pos hj₀, dif_pos hj₁, hcast, hsucc] using htime ⟨j, hj⟩ n hjn
  obtain ⟨Y, hYzero, hYweak⟩ := exists_lp_mixed_weak_partial_tree hp K V hVspace hVtime
  refine ⟨Y, ?_, hYweak⟩
  have hz : (⟨0, Nat.zero_lt_succ K⟩ : Fin (K + 1)) = 0 := Fin.ext rfl
  simpa only [V, dif_pos (Nat.zero_lt_succ K), hz] using hYzero

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end
