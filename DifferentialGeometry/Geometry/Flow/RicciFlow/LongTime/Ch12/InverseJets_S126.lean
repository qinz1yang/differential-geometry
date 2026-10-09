import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.InverseSetup_S126
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# CH12-S126 G2: jets of the local inverse of `id + u` (`[FROZEN] CH12-O58 R-E`)

`inverse_jets_S126` (statement = `[FROZEN] CH12-O58 R-E` verbatim): `V W ⊆ E` open, `u` smooth on
`V` with `id + u` `1/2`-approximating `id`, `Φ` a right inverse of `id + u` on `W` with values in
`V`.  Then `Φ` is `C^∞` on `W` and, for every `k` and `ε > 0`, there is `η > 0` (depending only on
`k, ε, E`) such that `‖D^j u‖ ≤ η` on `V` (`j ≤ k`) forces `‖D^j (Φ - id)‖ < ε` on `W` (`j ≤ k`).

Route (no compactness, no `Ring.inverse`): `Φ - id =: v` satisfies `Dv = -B - Dv ∘ B` with
`B = Du ∘ Φ`, `‖B‖ ≤ 1/2` (chain rule on `Φ ∘ (id + u) = id`), so
`D^n (Dv) = -D^n B - D^n (Dv ∘ B)`; Leibniz (`compL`) plus absorption of the top term
(`‖B‖ ≤ 1/2`) bounds `D^{n+1} v` by jets of `B` and lower jets of `v`; jets of `B = Du ∘ Φ` by
`norm_iteratedFDerivWithin_comp_le` with the small outer constant `η`. The estimate is linear in
`η` (`jets_aux_S126`), whence the `ε`/`η` form.
-/

set_option autoImplicit false

open Set Filter Topology
open scoped ContDiff NNReal Nat

namespace GC.LongTime.Ch12

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- jets of the identity map: `‖D^i id‖ ≤ 1` for `i ≥ 1`. -/
theorem norm_iteratedFDeriv_id_le_S126 (i : ℕ) (hi : 1 ≤ i) (x : E) :
    ‖iteratedFDeriv ℝ i (fun y : E => y) x‖ ≤ 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
  rcases m with _ | m
  · rw [norm_iteratedFDeriv_one, fderiv_fun_id]
    exact ContinuousLinearMap.norm_id_le
  · rw [iteratedFDeriv_succ_eq_comp_right]
    have h : (fun y : E => fderiv ℝ (fun y : E => y) y) = fun _ => ContinuousLinearMap.id ℝ E := by
      funext y; exact fderiv_fun_id
    rw [h, iteratedFDeriv_const_of_ne (by omega)]
    simp

/-- The first-order fixed-point inequality: if `Dv = -B - Dv ∘ B` on an open `W` and `‖B x‖ ≤ 1/2`
then the `(n+1)`-st jet of `v` is controlled by jets of `B` and the lower jets of `v`. -/
theorem jets_fixedpoint_S126 {W : Set E} (hW : IsOpen W) {v : E → E} {B : E → E →L[ℝ] E}
    (hv : ContDiffOn ℝ ∞ v W) (hB : ContDiffOn ℝ ∞ B W)
    (hF : ∀ z ∈ W, fderiv ℝ v z = -B z - (fderiv ℝ v z).comp (B z))
    {x : E} (hx : x ∈ W) (hBx : ‖B x‖ ≤ 1 / 2) (n : ℕ) :
    ‖iteratedFDeriv ℝ (n + 1) v x‖ ≤ 2 * (‖iteratedFDeriv ℝ n B x‖ +
      ∑ i ∈ Finset.range n, (n.choose i : ℝ) * ‖iteratedFDeriv ℝ (i + 1) v x‖ *
        ‖iteratedFDeriv ℝ (n - i) B x‖) := by
  have hdv : ContDiffOn ℝ ∞ (fderiv ℝ v) W := hv.fderiv_of_isOpen hW (by simp)
  have hnN : (n : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  obtain ⟨G, hG⟩ : ∃ G : E → E →L[ℝ] E, G = fun z => (ContinuousLinearMap.compL ℝ E E E)
      (fderiv ℝ v z) (B z) := ⟨_, rfl⟩
  have hGc : ContDiffOn ℝ ∞ G W := by
    rw [hG]
    exact (ContinuousLinearMap.compL ℝ E E E).isBoundedBilinearMap.contDiff.comp_contDiffOn
      (hdv.prodMk hB)
  have hEq : EqOn (fderiv ℝ v) (-B - G) W := by
    intro z hz
    rw [hF z hz, hG]
    simp [sub_eq_add_neg]
  have hnB : ContDiffOn ℝ ∞ (-B) W := hB.neg
  have h1 : ‖iteratedFDeriv ℝ (n + 1) v x‖ = ‖iteratedFDerivWithin ℝ n (-B - G) W x‖ := by
    rw [← norm_iteratedFDeriv_fderiv, ← iteratedFDerivWithin_of_isOpen n hW hx,
      iteratedFDerivWithin_congr hEq hx n]
  have h2 : ‖iteratedFDerivWithin ℝ n (-B - G) W x‖ ≤ ‖iteratedFDeriv ℝ n B x‖ +
      ‖iteratedFDerivWithin ℝ n G W x‖ := by
    rw [iteratedFDerivWithin_sub_apply (hnB.contDiffWithinAt hx |>.of_le hnN)
      ((hGc.contDiffWithinAt hx).of_le hnN) hW.uniqueDiffOn hx,
      iteratedFDerivWithin_neg_apply hW.uniqueDiffOn hx, iteratedFDerivWithin_of_isOpen n hW hx]
    calc ‖-iteratedFDeriv ℝ n B x - iteratedFDerivWithin ℝ n G W x‖
        ≤ ‖-iteratedFDeriv ℝ n B x‖ + ‖iteratedFDerivWithin ℝ n G W x‖ := norm_sub_le _ _
      _ = _ := by rw [norm_neg]
  have h3 : ‖iteratedFDerivWithin ℝ n G W x‖ ≤ ∑ i ∈ Finset.range (n + 1),
      (n.choose i : ℝ) * ‖iteratedFDeriv ℝ (i + 1) v x‖ * ‖iteratedFDeriv ℝ (n - i) B x‖ := by
    have := (ContinuousLinearMap.compL ℝ E E E).norm_iteratedFDerivWithin_le_of_bilinear_of_le_one
      (hdv.of_le (by exact_mod_cast le_top)) (hB.of_le (by exact_mod_cast le_top))
      hW.uniqueDiffOn hx hnN (ContinuousLinearMap.norm_compL_le ℝ E E E)
    rw [hG] at *
    refine this.trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
    rw [iteratedFDerivWithin_of_isOpen i hW hx, iteratedFDerivWithin_of_isOpen (n - i) hW hx,
      norm_iteratedFDeriv_fderiv]
  rw [Finset.sum_range_succ] at h3
  have h4 : (n.choose n : ℝ) * ‖iteratedFDeriv ℝ (n + 1) v x‖ * ‖iteratedFDeriv ℝ (n - n) B x‖ ≤
      ‖iteratedFDeriv ℝ (n + 1) v x‖ * (1 / 2) := by
    rw [Nat.choose_self, Nat.sub_self, norm_iteratedFDeriv_zero]
    simp only [Nat.cast_one, one_mul]
    exact mul_le_mul_of_nonneg_left hBx (norm_nonneg _)
  have h5 := norm_nonneg (iteratedFDeriv ℝ (n + 1) v x)
  linarith

/-- Jets of `(Du) ∘ Φ`: Faà di Bruno with the small factor `η` on the outer jets. -/
theorem jets_comp_fderiv_S126 {u Φ : E → E} {V W : Set E} (hV : IsOpen V) (hW : IsOpen W)
    (hu : ContDiffOn ℝ ∞ u V) (hΦc : ContDiffOn ℝ ∞ Φ W) (hmaps : ∀ x ∈ W, Φ x ∈ V)
    {x : E} (hx : x ∈ W) (l : ℕ) {η Dφ : ℝ}
    (hη : ∀ j : ℕ, j ≤ l + 1 → ‖iteratedFDeriv ℝ j u (Φ x)‖ ≤ η)
    (hD : ∀ i : ℕ, 1 ≤ i → i ≤ l → ‖iteratedFDeriv ℝ i Φ x‖ ≤ Dφ ^ i) :
    ‖iteratedFDeriv ℝ l (fun z => fderiv ℝ u (Φ z)) x‖ ≤ l ! * η * Dφ ^ l := by
  have hg : ContDiffOn ℝ ∞ (fderiv ℝ u) V := hu.fderiv_of_isOpen hV (by simp)
  have hn : (l : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  have hC : ∀ i : ℕ, i ≤ l → ‖iteratedFDerivWithin ℝ i (fderiv ℝ u) V (Φ x)‖ ≤ η := by
    intro i hi
    rw [iteratedFDerivWithin_of_isOpen i hV (hmaps x hx), norm_iteratedFDeriv_fderiv]
    exact hη (i + 1) (by omega)
  have hD' : ∀ i : ℕ, 1 ≤ i → i ≤ l → ‖iteratedFDerivWithin ℝ i Φ W x‖ ≤ Dφ ^ i := by
    intro i h1 hi
    rw [iteratedFDerivWithin_of_isOpen i hW hx]
    exact hD i h1 hi
  have := norm_iteratedFDerivWithin_comp_le hg hΦc hn hV.uniqueDiffOn hW.uniqueDiffOn hmaps hx hC hD'
  rw [iteratedFDerivWithin_of_isOpen l hW hx] at this
  exact this

/-- The algebraic relation `Dv = -B - Dv ∘ B` for `v = Φ - id`, `B = Du ∘ Φ`. -/
theorem fderiv_sub_id_eq_S126 {Φ : E → E} {B : E →L[ℝ] E} {x : E}
    (hΦd : DifferentiableAt ℝ Φ x) (hcomp : (fderiv ℝ Φ x).comp (1 + B) = 1) :
    fderiv ℝ (fun z => Φ z - z) x =
      -B - (fderiv ℝ (fun z => Φ z - z) x).comp B := by
  rw [fderiv_fun_sub hΦd differentiableAt_fun_id, fderiv_fun_id]
  rw [ContinuousLinearMap.one_def] at hcomp
  rw [ContinuousLinearMap.comp_add, ContinuousLinearMap.comp_id] at hcomp
  rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.id_comp]
  have h2 : (fderiv ℝ Φ x).comp B = ContinuousLinearMap.id ℝ E - fderiv ℝ Φ x := by
    rw [eq_sub_iff_add_eq, add_comm]; exact hcomp
  rw [h2]
  abel

/-- `‖D^i Φ‖ ≤ ‖D^i (Φ - id)‖ + 1` for `i ≥ 1`. -/
theorem norm_iteratedFDeriv_le_sub_id_S126 {Φ : E → E} {x : E} (hΦ : ContDiffAt ℝ ∞ Φ x)
    (i : ℕ) (hi : 1 ≤ i) :
    ‖iteratedFDeriv ℝ i Φ x‖ ≤ ‖iteratedFDeriv ℝ i (fun z => Φ z - z) x‖ + 1 := by
  have hi' : (i : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  have h : iteratedFDeriv ℝ i (fun z => Φ z - z) x = iteratedFDeriv ℝ i Φ x -
      iteratedFDeriv ℝ i (fun z : E => z) x :=
    iteratedFDeriv_sub_apply (hΦ.of_le hi') (contDiffAt_id.of_le hi')
  have h2 : iteratedFDeriv ℝ i Φ x = iteratedFDeriv ℝ i (fun z => Φ z - z) x +
      iteratedFDeriv ℝ i (fun z : E => z) x := by
    rw [h]; abel
  rw [h2]
  exact (norm_add_le _ _).trans (by linarith [norm_iteratedFDeriv_id_le_S126 i hi x])

/-- Real-number bookkeeping for the product of two small jets. -/
theorem term_bound_S126 {c b ch K m η : ℝ} (hb0 : 0 ≤ b) (hch : 0 ≤ ch)
    (hK : 0 ≤ K) (hm : 0 ≤ m) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hc : c ≤ K * η) (hb : b ≤ m * η) :
    ch * c * b ≤ η * (ch * (K * m)) := by
  calc ch * c * b ≤ ch * (K * η) * (m * η) := by gcongr
    _ = (η * (ch * (K * m))) * η := by ring
    _ ≤ η * (ch * (K * m)) := mul_le_of_le_one_right (by positivity) hη1

/-- Linear jet estimate for `Φ - id` by induction on the order: `‖D^j (Φ - id)‖ ≤ K_n · η`
whenever the jets of `u` of order `≤ n` are `≤ η ≤ 1`. -/
theorem jets_aux_S126 [CompleteSpace E] (n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (u Φ : E → E) (V W : Set E), IsOpen V → IsOpen W → ContDiffOn ℝ ∞ u V →
      ApproximatesLinearOn (fun y => y + u y)
        ((ContinuousLinearEquiv.refl ℝ E : E ≃L[ℝ] E) : E →L[ℝ] E) V (1 / 2 : ℝ≥0) →
      (∀ x ∈ W, Φ x ∈ V ∧ Φ x + u (Φ x) = x) →
      ∀ η : ℝ, 0 ≤ η → η ≤ 1 → (∀ j : ℕ, j ≤ n → ∀ y ∈ V, ‖iteratedFDeriv ℝ j u y‖ ≤ η) →
        ∀ j : ℕ, j ≤ n → ∀ x ∈ W, ‖iteratedFDeriv ℝ j (fun z => Φ z - z) x‖ ≤ K * η := by
  induction n with
  | zero =>
    refine ⟨1, zero_le_one, ?_⟩
    intro u Φ V W hV hW hu hA hΦ η hη0 hη1 hj j hj0 x hx
    obtain rfl : j = 0 := by omega
    obtain ⟨hy, hΨ⟩ := hΦ x hx
    rw [norm_iteratedFDeriv_zero, one_mul]
    have h1 : Φ x - x = -u (Φ x) := by
      calc Φ x - x = Φ x - (Φ x + u (Φ x)) := by rw [hΨ]
        _ = -u (Φ x) := by abel
    have h2 := hj 0 le_rfl (Φ x) hy
    rw [norm_iteratedFDeriv_zero] at h2
    change ‖Φ x - x‖ ≤ η
    rw [h1, norm_neg]
    exact h2
  | succ n ih =>
    obtain ⟨K, hK0, hK⟩ := ih
    obtain ⟨Dφ, hDφ⟩ : ∃ Dφ : ℝ, Dφ = K + 1 := ⟨_, rfl⟩
    have hDφ1 : 1 ≤ Dφ := by rw [hDφ]; linarith
    obtain ⟨S, hS⟩ : ∃ S : ℝ, S = ∑ i ∈ Finset.range n,
        (n.choose i : ℝ) * (K * (((n - i)! : ℕ) * Dφ ^ (n - i))) := ⟨_, rfl⟩
    have hS0 : 0 ≤ S := by
      rw [hS]
      refine Finset.sum_nonneg fun i _ => ?_
      have : 0 ≤ Dφ := by linarith
      positivity
    have hR0 : 0 ≤ 2 * (((n ! : ℕ) : ℝ) * Dφ ^ n + S) := by
      have : 0 ≤ Dφ := by linarith
      positivity
    refine ⟨K + 2 * (((n ! : ℕ) : ℝ) * Dφ ^ n + S), by linarith, ?_⟩
    intro u Φ V W hV hW hu hA hΦ η hη0 hη1 hj j hj' x hx
    have hΦc := contDiffOn_inverse_S126 hV hW hu hA hΦ
    have hDu := norm_fderiv_le_half_S126 hV hA
    have hcomp := fderiv_inverse_comp_S126 hV hW hu hA hΦ
    have hlow := hK u Φ V W hV hW hu hA hΦ η hη0 hη1 (fun j hj0 y hy => hj j (by omega) y hy)
    have hmaps : ∀ z ∈ W, Φ z ∈ V := fun z hz => (hΦ z hz).1
    rcases Nat.lt_or_ge j (n + 1) with hjn | hjn
    · refine (hlow j (by omega) x hx).trans ?_
      nlinarith [mul_nonneg hR0 hη0]
    · obtain rfl : j = n + 1 := by omega
      have hv : ContDiffOn ℝ ∞ (fun z => Φ z - z) W := hΦc.sub contDiffOn_id
      have hB : ContDiffOn ℝ ∞ (fun z => fderiv ℝ u (Φ z)) W :=
        (hu.fderiv_of_isOpen hV (by simp)).comp hΦc hmaps
      have hF : ∀ z ∈ W, fderiv ℝ (fun z => Φ z - z) z = -(fderiv ℝ u (Φ z)) -
          (fderiv ℝ (fun z => Φ z - z) z).comp (fderiv ℝ u (Φ z)) := fun z hz =>
        fderiv_sub_id_eq_S126 ((hΦc.contDiffAt (hW.mem_nhds hz)).differentiableAt (by simp))
          (hcomp z hz)
      have hBx : ‖fderiv ℝ u (Φ x)‖ ≤ 1 / 2 := hDu (Φ x) (hmaps x hx)
      have hfp := jets_fixedpoint_S126 hW hv hB hF hx hBx n
      have hb : ∀ l : ℕ, l ≤ n →
          ‖iteratedFDeriv ℝ l (fun z => fderiv ℝ u (Φ z)) x‖ ≤ (((l ! : ℕ) : ℝ) * Dφ ^ l) * η := by
        intro l hl
        have h := jets_comp_fderiv_S126 hV hW hu hΦc hmaps hx l (η := η) (Dφ := Dφ)
          (fun j hj1 => hj j (by omega) (Φ x) (hmaps x hx)) (fun i h1 hi => by
            have h1' := norm_iteratedFDeriv_le_sub_id_S126
              (hΦc.contDiffAt (hW.mem_nhds hx)) i h1
            have h2' := hlow i (by omega) x hx
            calc ‖iteratedFDeriv ℝ i Φ x‖ ≤ K * η + 1 := by linarith
              _ ≤ Dφ := by rw [hDφ]; nlinarith
              _ ≤ Dφ ^ i := le_self_pow₀ hDφ1 (by omega))
        calc _ ≤ _ := h
          _ = _ := by ring
      have hsum : ∑ i ∈ Finset.range n, (n.choose i : ℝ) *
            ‖iteratedFDeriv ℝ (i + 1) (fun z => Φ z - z) x‖ *
            ‖iteratedFDeriv ℝ (n - i) (fun z => fderiv ℝ u (Φ z)) x‖ ≤ η * S := by
        rw [hS, Finset.mul_sum]
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' := Finset.mem_range.1 hi
        have hDφ0 : 0 ≤ Dφ := by linarith
        exact term_bound_S126 (norm_nonneg _) (by positivity) hK0
          (by positivity) hη0 hη1 (hlow (i + 1) (by omega) x hx) (hb (n - i) (Nat.sub_le _ _))
      have hbn := hb n le_rfl
      have hfp' := hfp
      nlinarith [mul_nonneg hR0 hη0, mul_nonneg hK0 hη0]

/-- **`[FROZEN] CH12-O58 R-E`** (verbatim): smoothness and `C^k`-smallness of the local inverse
of `id + u`. -/
theorem inverse_jets_S126 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ (u Φ : E → E) (V W : Set E), IsOpen V → IsOpen W →
      ContDiffOn ℝ ∞ u V →
      ApproximatesLinearOn (fun y => y + u y) ((ContinuousLinearEquiv.refl ℝ E : E ≃L[ℝ] E) :
        E →L[ℝ] E) V (1 / 2 : ℝ≥0) →
      (∀ j : ℕ, j ≤ k → ∀ y ∈ V, ‖iteratedFDeriv ℝ j u y‖ ≤ η) →
      (∀ x ∈ W, Φ x ∈ V ∧ Φ x + u (Φ x) = x) →
      ContDiffOn ℝ ∞ Φ W ∧
        ∀ j : ℕ, j ≤ k → ∀ x ∈ W, ‖iteratedFDeriv ℝ j (fun z => Φ z - z) x‖ < ε := by
  obtain ⟨K, hK0, hK⟩ := jets_aux_S126 (E := E) k
  have hpos : 0 < ε / (2 * (K + 1)) := by positivity
  refine ⟨min 1 (ε / (2 * (K + 1))), lt_min one_pos hpos, ?_⟩
  intro u Φ V W hV hW hu hA hj hΦ
  refine ⟨contDiffOn_inverse_S126 hV hW hu hA hΦ, fun j hjk x hx => ?_⟩
  have hη0 : 0 ≤ min 1 (ε / (2 * (K + 1))) := le_min zero_le_one hpos.le
  have h := hK u Φ V W hV hW hu hA hΦ _ hη0 (min_le_left _ _) hj j hjk x hx
  have h2 : K * min 1 (ε / (2 * (K + 1))) ≤ ε / 2 := by
    calc K * min 1 (ε / (2 * (K + 1))) ≤ K * (ε / (2 * (K + 1))) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) hK0
      _ ≤ ε / 2 := by
          rw [← sub_nonneg]
          have : ε / 2 - K * (ε / (2 * (K + 1))) = ε / (2 * (K + 1)) := by field_simp; ring
          rw [this]; exact hpos.le
  linarith

end GC.LongTime.Ch12

