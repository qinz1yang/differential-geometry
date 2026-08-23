import DifferentialGeometry.Tensor.Multilinear.HsBoundOp
import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Fintype.Perm

noncomputable section

open Finset
open scoped BigOperators

namespace ContinuousMultilinearMap

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def IsSymmetric {n : ℕ}
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) F) : Prop :=
  ∀ σ : Equiv.Perm (Fin n), A.domDomCongr σ = A

theorem IsSymmetric.apply_perm {n : ℕ}
    {A : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) F}
    (hA : A.IsSymmetric) (σ : Equiv.Perm (Fin n)) (v : Fin n → E) :
    A (fun i => v (σ i)) = A v := by
  have h := congrArg (fun B => B v) (hA σ)
  simpa only [ContinuousMultilinearMap.domDomCongr_apply] using h

private def finRange {n : ℕ} (g : Fin n → Fin n) : Finset (Fin n) :=
  Finset.univ.image g

private theorem finRange_subset_iff {n : ℕ} (g : Fin n → Fin n)
    (s : Finset (Fin n)) :
    finRange g ⊆ s ↔ ∀ i, g i ∈ s := by
  classical
  constructor
  · intro h i
    exact h (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
  · intro h y hy
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy
    exact h i

private theorem finRange_eq_univ {n : ℕ} (g : Fin n → Fin n) :
    finRange g = Finset.univ ↔ Function.Surjective g := by
  classical
  constructor
  · intro h y
    have hy : y ∈ finRange g := by rw [h]; simp
    simpa [finRange] using hy
  · intro h
    apply Finset.eq_univ_of_forall
    intro y
    obtain ⟨x, rfl⟩ := h y
    simp [finRange]

private theorem mu_upper_sum {n : ℕ} (g : Fin n → Fin n) :
    (∑ s : Finset (Fin n),
        if finRange g ⊆ s then IncidenceAlgebra.mu ℝ s Finset.univ else 0) =
      if Function.Surjective g then 1 else 0 := by
  classical
  rw [Finset.sum_ite]
  simp only [Finset.sum_const_zero, add_zero]
  have hfilter :
      Finset.univ.filter (fun s : Finset (Fin n) => finRange g ⊆ s) =
        Finset.Icc (finRange g) Finset.univ := by
    ext s
    simp
  rw [hfilter, IncidenceAlgebra.sum_Icc_mu_left]
  simp only [finRange_eq_univ]

private def surjPermEquiv (n : ℕ) :
    {g : Fin n → Fin n // Function.Surjective g} ≃ Equiv.Perm (Fin n) where
  toFun g :=
    Equiv.ofBijective g.1
      ((Fintype.bijective_iff_surjective_and_card g.1).2 ⟨g.2, rfl⟩)
  invFun σ := ⟨σ, σ.surjective⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Equiv.ext fun _ => rfl

private theorem card_surj_maps (n : ℕ) :
    (Finset.univ.filter
      (Function.Surjective : (Fin n → Fin n) → Prop)).card = n.factorial := by
  classical
  have hcard :
      Fintype.card {g : Fin n → Fin n // Function.Surjective g} =
        (Finset.univ.filter
          (Function.Surjective : (Fin n → Fin n) → Prop)).card :=
    Fintype.card_ofFinset _ (by
      intro g
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      change Function.Surjective g ↔ Function.Surjective g
      rfl)
  calc
    (Finset.univ.filter
        (Function.Surjective : (Fin n → Fin n) → Prop)).card =
        Fintype.card {g : Fin n → Fin n // Function.Surjective g} :=
      hcard.symm
    _ = Fintype.card (Equiv.Perm (Fin n)) :=
      Fintype.card_congr (surjPermEquiv n)
    _ = n.factorial := by rw [Fintype.card_perm, Fintype.card_fin]

private theorem apply_surj
    {n : ℕ} {A : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) F}
    (hA : A.IsSymmetric) (g : Fin n → Fin n) (hg : Function.Surjective g)
    (v : Fin n → E) :
    A (fun i => v (g i)) = A v := by
  let σ : Equiv.Perm (Fin n) :=
    Equiv.ofBijective g
      ((Fintype.bijective_iff_surjective_and_card g).2 ⟨hg, rfl⟩)
  change A (fun i => v (σ i)) = A v
  exact hA.apply_perm σ v

private theorem sum_surj_apply
    {n : ℕ} {A : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) F}
    (hA : A.IsSymmetric) (v : Fin n → E) :
    (∑ g : Fin n → Fin n,
      if Function.Surjective g then A (fun i => v (g i)) else 0) =
        n.factorial • A v := by
  classical
  rw [Finset.sum_ite]
  simp only [Finset.sum_const_zero, add_zero]
  calc
    ∑ g ∈ Finset.univ.filter Function.Surjective,
        A (fun i => v (g i)) =
        ∑ _g ∈ Finset.univ.filter Function.Surjective, A v := by
      apply Finset.sum_congr rfl
      intro g hg
      exact apply_surj hA g (by simpa using (Finset.mem_filter.mp hg).2) v
    _ = n.factorial • A v := by
      rw [Finset.sum_const, card_surj_maps]

private theorem apply_diag_sum
    {n : ℕ} (A : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) F)
    (v : Fin n → E) (s : Finset (Fin n)) :
    A (fun _ => ∑ i ∈ s, v i) =
      ∑ g : Fin n → Fin n,
        if ∀ i, g i ∈ s then A (fun i => v (g i)) else 0 := by
  classical
  have harg :
      (fun _ : Fin n => ∑ i ∈ s, v i) =
        fun k : Fin n => ∑ i : Fin n, if i ∈ s then v i else 0 := by
    funext k
    simp
  rw [harg]
  change
    A.toMultilinearMap (fun k : Fin n => ∑ i : Fin n, if i ∈ s then v i else 0) =
      _
  have hsum := A.toMultilinearMap.map_sum
    (g := fun (_ : Fin n) (i : Fin n) => if i ∈ s then v i else 0)
  rw [hsum]
  refine Finset.sum_congr rfl ?_
  intro g _
  by_cases hg : ∀ i, g i ∈ s
  · rw [if_pos hg]
    change
      A.toMultilinearMap (fun i => if g i ∈ s then v (g i) else 0) =
        A.toMultilinearMap (fun i => v (g i))
    congr 1
    funext i
    rw [if_pos (hg i)]
  · rw [if_neg hg]
    push Not at hg
    obtain ⟨i, hi⟩ := hg
    exact A.map_coord_zero i (by simp [hi])

theorem polarization_eq
    {n : ℕ} {A : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) F}
    (hA : A.IsSymmetric) (v : Fin n → E) :
    (∑ s : Finset (Fin n),
      IncidenceAlgebra.mu ℝ s Finset.univ •
        A (fun _ => ∑ i ∈ s, v i)) =
      (n.factorial : ℝ) • A v := by
  classical
  calc
    (∑ s : Finset (Fin n),
      IncidenceAlgebra.mu ℝ s Finset.univ •
        A (fun _ => ∑ i ∈ s, v i)) =
        ∑ s : Finset (Fin n),
          IncidenceAlgebra.mu ℝ s Finset.univ •
            ∑ g : Fin n → Fin n,
              if ∀ i, g i ∈ s then A (fun i => v (g i)) else 0 := by
      apply Fintype.sum_congr
      intro s
      rw [apply_diag_sum]
    _ = ∑ s : Finset (Fin n),
          ∑ g : Fin n → Fin n,
            IncidenceAlgebra.mu ℝ s Finset.univ •
              (if ∀ i, g i ∈ s then A (fun i => v (g i)) else 0) := by
      apply Fintype.sum_congr
      intro s
      rw [Finset.smul_sum]
    _ = ∑ g : Fin n → Fin n,
          ∑ s : Finset (Fin n),
            IncidenceAlgebra.mu ℝ s Finset.univ •
              (if ∀ i, g i ∈ s then A (fun i => v (g i)) else 0) := by
      exact Finset.sum_comm
    _ = ∑ g : Fin n → Fin n,
          if Function.Surjective g then A (fun i => v (g i)) else 0 := by
      apply Fintype.sum_congr
      intro g
      calc
        (∑ s : Finset (Fin n),
          IncidenceAlgebra.mu ℝ s Finset.univ •
            (if ∀ i, g i ∈ s then A (fun i => v (g i)) else 0)) =
            ∑ s : Finset (Fin n),
              (if finRange g ⊆ s
                then IncidenceAlgebra.mu ℝ s Finset.univ else 0) •
                A (fun i => v (g i)) := by
          apply Fintype.sum_congr
          intro s
          by_cases hs : finRange g ⊆ s
          · have hg : ∀ i, g i ∈ s := (finRange_subset_iff g s).mp hs
            rw [if_pos hg, if_pos hs]
          · have hg : ¬ ∀ i, g i ∈ s := fun h => hs ((finRange_subset_iff g s).mpr h)
            rw [if_neg hg, if_neg hs]
            simp
        _ = (∑ s : Finset (Fin n),
              if finRange g ⊆ s
                then IncidenceAlgebra.mu ℝ s Finset.univ else 0) •
              A (fun i => v (g i)) := by
          rw [Finset.sum_smul]
        _ = (if Function.Surjective g then (1 : ℝ) else 0) •
              A (fun i => v (g i)) := by
          rw [mu_upper_sum]
        _ = if Function.Surjective g then A (fun i => v (g i)) else 0 := by
          by_cases hg : Function.Surjective g <;> simp [hg]
    _ = n.factorial • A v := sum_surj_apply hA v
    _ = (n.factorial : ℝ) • A v :=
      (Nat.cast_smul_eq_nsmul ℝ n.factorial (A v)).symm

def polarConst (n : ℕ) : ℝ :=
  ∑ s : Finset (Fin n),
    ‖IncidenceAlgebra.mu ℝ s Finset.univ‖ * (s.card : ℝ) ^ n

theorem polarConst_nonneg (n : ℕ) : 0 ≤ polarConst n := by
  classical
  apply Finset.sum_nonneg'
  intro s
  positivity

private theorem unit_apply_le
    {n : ℕ} {A : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) F}
    (hA : A.IsSymmetric) {C : ℝ} (hC : 0 ≤ C)
    (hdiag : ∀ x : E, ‖A (fun _ => x)‖ ≤ C * ‖x‖ ^ n)
    (v : Fin n → E) (hv : ∀ i, ‖v i‖ ≤ 1) :
    ‖A v‖ ≤ polarConst n * C := by
  classical
  have hsum_norm (s : Finset (Fin n)) :
      ‖∑ i ∈ s, v i‖ ≤ (s.card : ℝ) := by
    calc
      ‖∑ i ∈ s, v i‖ ≤ ∑ i ∈ s, ‖v i‖ :=
        norm_sum_le s v
      _ ≤ ∑ _i ∈ s, (1 : ℝ) := by
        exact Finset.sum_le_sum fun i _ => hv i
      _ = (s.card : ℝ) := by simp
  have hterm (s : Finset (Fin n)) :
      ‖IncidenceAlgebra.mu ℝ s Finset.univ •
          A (fun _ => ∑ i ∈ s, v i)‖ ≤
        (‖IncidenceAlgebra.mu ℝ s Finset.univ‖ * (s.card : ℝ) ^ n) * C := by
    have hpow :
        ‖∑ i ∈ s, v i‖ ^ n ≤ (s.card : ℝ) ^ n := by
      gcongr
      exact hsum_norm s
    calc
      ‖IncidenceAlgebra.mu ℝ s Finset.univ •
          A (fun _ => ∑ i ∈ s, v i)‖ =
          ‖IncidenceAlgebra.mu ℝ s Finset.univ‖ *
            ‖A (fun _ => ∑ i ∈ s, v i)‖ := by
              rw [norm_smul]
      _ ≤ ‖IncidenceAlgebra.mu ℝ s Finset.univ‖ *
            (C * ‖∑ i ∈ s, v i‖ ^ n) :=
        mul_le_mul_of_nonneg_left (hdiag _) (norm_nonneg _)
      _ ≤ ‖IncidenceAlgebra.mu ℝ s Finset.univ‖ *
            (C * (s.card : ℝ) ^ n) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hpow hC) (norm_nonneg _)
      _ = (‖IncidenceAlgebra.mu ℝ s Finset.univ‖ * (s.card : ℝ) ^ n) * C := by
        ring
  have hsum :
      ‖∑ s : Finset (Fin n),
          IncidenceAlgebra.mu ℝ s Finset.univ •
            A (fun _ => ∑ i ∈ s, v i)‖ ≤ polarConst n * C := by
    calc
      ‖∑ s : Finset (Fin n),
          IncidenceAlgebra.mu ℝ s Finset.univ •
            A (fun _ => ∑ i ∈ s, v i)‖ ≤
          ∑ s : Finset (Fin n),
            ‖IncidenceAlgebra.mu ℝ s Finset.univ •
              A (fun _ => ∑ i ∈ s, v i)‖ := by
                exact norm_sum_le Finset.univ _
      _ ≤ ∑ s : Finset (Fin n),
            (‖IncidenceAlgebra.mu ℝ s Finset.univ‖ * (s.card : ℝ) ^ n) * C := by
              exact Finset.sum_le_sum fun s _ => hterm s
      _ = polarConst n * C := by
        rw [polarConst, Finset.sum_mul]
  have hfac :
      (n.factorial : ℝ) * ‖A v‖ ≤ polarConst n * C := by
    calc
      (n.factorial : ℝ) * ‖A v‖ =
          ‖(n.factorial : ℝ) • A v‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg]
            positivity
      _ = ‖∑ s : Finset (Fin n),
            IncidenceAlgebra.mu ℝ s Finset.univ •
              A (fun _ => ∑ i ∈ s, v i)‖ := by
        rw [polarization_eq hA v]
      _ ≤ polarConst n * C := hsum
  calc
    ‖A v‖ = 1 * ‖A v‖ := by rw [one_mul]
    _ ≤ (n.factorial : ℝ) * ‖A v‖ := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast (Nat.succ_le_iff.mpr (Nat.factorial_pos n))
      · exact norm_nonneg _
    _ ≤ polarConst n * C := hfac

theorem opNorm_le_diag
    {n : ℕ} {A : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) F}
    (hA : A.IsSymmetric) {C : ℝ} (hC : 0 ≤ C)
    (hdiag : ∀ x : E, ‖A (fun _ => x)‖ ≤ C * ‖x‖ ^ n) :
    ‖A‖ ≤ polarConst n * C := by
  classical
  apply A.opNorm_le_bound (mul_nonneg (polarConst_nonneg n) hC)
  intro v
  by_cases hz : ∃ i, v i = 0
  · obtain ⟨i, hi⟩ := hz
    rw [A.map_coord_zero i hi, norm_zero]
    exact mul_nonneg (mul_nonneg (polarConst_nonneg n) hC)
      (Finset.prod_nonneg fun _ _ => norm_nonneg _)
  · have hv_ne (i : Fin n) : v i ≠ 0 := by
      intro hi
      exact hz ⟨i, hi⟩
    let u : Fin n → E := fun i => ‖v i‖⁻¹ • v i
    have hu_norm (i : Fin n) : ‖u i‖ = 1 := by
      simp [u, norm_smul, norm_inv, (norm_ne_zero_iff.mpr (hv_ne i))]
    have hv_eq : (fun i => ‖v i‖ • u i) = v := by
      funext i
      simp [u, smul_smul, (norm_ne_zero_iff.mpr (hv_ne i))]
    have hmap :
        A v = (∏ i, ‖v i‖) • A u := by
      calc
        A v = A (fun i => ‖v i‖ • u i) := congrArg A hv_eq.symm
        _ = (∏ i, ‖v i‖) • A u :=
          A.map_smul_univ (fun i => ‖v i‖) u
    have hprod : 0 ≤ ∏ i, ‖v i‖ :=
      Finset.prod_nonneg fun _ _ => norm_nonneg _
    have hunit : ‖A u‖ ≤ polarConst n * C :=
      unit_apply_le hA hC hdiag u fun i => (hu_norm i).le
    rw [hmap, norm_smul, Real.norm_eq_abs, abs_of_nonneg hprod]
    calc
      (∏ i, ‖v i‖) * ‖A u‖ ≤
          (∏ i, ‖v i‖) * (polarConst n * C) :=
        mul_le_mul_of_nonneg_left hunit hprod
      _ = (polarConst n * C) * ∏ i, ‖v i‖ := by ring

theorem opNorm_le_diag_unit
    {n : ℕ} {A : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) F}
    (hA : A.IsSymmetric) {C : ℝ} (hC : 0 ≤ C)
    (hdiag : ∀ x : E, ‖x‖ ≤ 1 → ‖A (fun _ => x)‖ ≤ C) :
    ‖A‖ ≤ polarConst n * C := by
  apply opNorm_le_diag hA hC
  intro x
  by_cases hx : x = 0
  · subst x
    by_cases hn : n = 0
    · subst n
      simpa using hdiag (0 : E) (by simp)
    · let i : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
      rw [A.map_coord_zero i (by simp), norm_zero]
      positivity
  · let y : E := ‖x‖⁻¹ • x
    have hy_norm : ‖y‖ = 1 := by
      simp [y, norm_smul, norm_inv, (norm_ne_zero_iff.mpr hx)]
    have hx_eq : ‖x‖ • y = x := by
      simp [y, smul_smul, (norm_ne_zero_iff.mpr hx)]
    have hmap :
        A (fun _ => x) = ‖x‖ ^ n • A (fun _ => y) := by
      calc
        A (fun _ => x) = A (fun _ => ‖x‖ • y) := by
          congr 1
          funext i
          exact hx_eq.symm
        _ = ‖x‖ ^ n • A (fun _ => y) := by
          simpa using
            A.map_smul_univ (fun _ : Fin n => ‖x‖) (fun _ : Fin n => y)
    rw [hmap, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (norm_nonneg x) n)]
    exact (mul_le_mul_of_nonneg_left (hdiag y hy_norm.le)
      (pow_nonneg (norm_nonneg x) n)).trans_eq (mul_comm _ _)

end ContinuousMultilinearMap

namespace ContinuousLinearMap

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem opNorm_le_diag2
    (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hsymm : ∀ v w, B v w = B w v)
    {C : ℝ} (hC : 0 ≤ C)
    (hdiag : ∀ x : E, ‖x‖ ≤ 1 → |B x x| ≤ C) :
    ‖B‖ ≤ 2 * C := by
  refine ContinuousLinearMap.opNorm_le_bound₂ B
    (mul_nonneg (by norm_num) hC) ?_
  intro v w
  by_cases hv : v = 0
  · subst v
    simp
  by_cases hw : w = 0
  · subst w
    simp
  let u : E := ‖v‖⁻¹ • v
  let q : E := ‖w‖⁻¹ • w
  have hu_norm : ‖u‖ = 1 := by
    simp [u, norm_smul, norm_inv, (norm_ne_zero_iff.mpr hv)]
  have hq_norm : ‖q‖ = 1 := by
    simp [q, norm_smul, norm_inv, (norm_ne_zero_iff.mpr hw)]
  have hv_eq : ‖v‖ • u = v := by
    simp [u, smul_smul, (norm_ne_zero_iff.mpr hv)]
  have hw_eq : ‖w‖ • q = w := by
    simp [q, smul_smul, (norm_ne_zero_iff.mpr hw)]
  let p : E := (1 / 2 : ℝ) • (u + q)
  let m : E := (1 / 2 : ℝ) • (u - q)
  have hp_norm : ‖p‖ ≤ 1 := by
    change ‖(1 / 2 : ℝ) • (u + q)‖ ≤ 1
    calc
      ‖(1 / 2 : ℝ) • (u + q)‖ =
          (1 / 2 : ℝ) * ‖u + q‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg]
        norm_num
      _ ≤ (1 / 2 : ℝ) * (‖u‖ + ‖q‖) := by
        gcongr
        exact norm_add_le u q
      _ = 1 := by rw [hu_norm, hq_norm]; norm_num
  have hm_norm : ‖m‖ ≤ 1 := by
    change ‖(1 / 2 : ℝ) • (u - q)‖ ≤ 1
    calc
      ‖(1 / 2 : ℝ) • (u - q)‖ =
          (1 / 2 : ℝ) * ‖u - q‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg]
        norm_num
      _ ≤ (1 / 2 : ℝ) * (‖u‖ + ‖q‖) := by
        gcongr
        exact norm_sub_le u q
      _ = 1 := by rw [hu_norm, hq_norm]; norm_num
  have hpolar : B u q = B p p - B m m := by
    have hqu : B q u = B u q := hsymm q u
    dsimp only [p, m]
    simp only [map_smul, map_add, map_sub,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.sub_apply, smul_eq_mul]
    rw [hqu]
    ring
  have huq : |B u q| ≤ 2 * C := by
    rw [hpolar]
    calc
      |B p p - B m m| ≤ |B p p| + |B m m| := abs_sub _ _
      _ ≤ C + C := add_le_add (hdiag p hp_norm) (hdiag m hm_norm)
      _ = 2 * C := by ring
  have hscale : B v w = (‖v‖ * ‖w‖) * B u q := by
    calc
      B v w = B (‖v‖ • u) (‖w‖ • q) := by rw [hv_eq, hw_eq]
      _ = (‖v‖ * ‖w‖) * B u q := by
        simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
        ring
  rw [hscale, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (mul_nonneg (norm_nonneg v) (norm_nonneg w))]
  calc
    (‖v‖ * ‖w‖) * |B u q| ≤ (‖v‖ * ‖w‖) * (2 * C) :=
      mul_le_mul_of_nonneg_left huq
        (mul_nonneg (norm_nonneg v) (norm_nonneg w))
    _ = 2 * C * ‖v‖ * ‖w‖ := by ring

end ContinuousLinearMap

end
