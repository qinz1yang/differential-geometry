import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.MeanValue

/-!
# CH12-S112 G1a: a Hadamard-type jet bound for `y ↦ Θ (y, ζ y)` with `Θ (·, 0) = 0`

Pure ℝ-calculus (no manifolds).  If `Θ : E × Z → W` is smooth with `Θ (y, 0) = 0`, then the
`l`-th derivative at `x` of `y ↦ Θ (y, ζ y)` is bounded by `C * ∑_{i ≤ l} ‖D^i ζ x‖`, where `C`
depends only on `l` and on a uniform bound `M` of the derivatives of `Θ` on `Ks × closedBall 0 1`
(`x ∈ Ks`, jets of `ζ` at `x` at most `1`).  Proof: induction on `l` using
`fderiv (Θ ∘ (id, ζ)) = Θ₁ ∘ (id, ζ) + (Θ₂ ∘ (id, ζ)) ∘ Dζ` with `Θ₁ = ∂_yΘ`, `Θ₂ = ∂_zΘ`
(again of the same type), mean value inequality for `l = 0`, `norm_iteratedFDerivWithin_comp_le`
and the Leibniz rule for the composition `compL`.  No parametric integral is needed.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace GC.LongTime.Ch12

section HadamardJets

variable {E Z : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- The identity has no jets of order `≥ 2` and first jet of norm `≤ 1`. -/
theorem norm_iteratedFDeriv_id_le_S112 (x : E) {i : ℕ} (hi : 1 ≤ i) :
    ‖iteratedFDeriv ℝ i (id : E → E) x‖ ≤ 1 := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  rw [← norm_iteratedFDeriv_fderiv]
  have h : fderiv ℝ (id : E → E) = fun _ => ContinuousLinearMap.id ℝ E :=
    funext fun y => fderiv_id
  rw [h]
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [norm_iteratedFDeriv_zero]
    exact ContinuousLinearMap.norm_id_le
  · rw [iteratedFDeriv_const_of_ne hj.ne']
    simp

/-- Jets of a pair of maps. -/
theorem norm_iteratedFDeriv_prodMk_le_S112 {A B : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] {f : E → A} {g : E → B} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x) (i : ℕ) :
    ‖iteratedFDeriv ℝ i (fun y => (f y, g y)) x‖ ≤
      ‖iteratedFDeriv ℝ i f x‖ + ‖iteratedFDeriv ℝ i g x‖ := by
  have h : (fun y => (f y, g y)) =
      (ContinuousLinearMap.inl ℝ A B) ∘ f + (ContinuousLinearMap.inr ℝ A B) ∘ g := by
    funext y; simp
  have hf' : ContDiffAt ℝ i ((ContinuousLinearMap.inl ℝ A B) ∘ f) x :=
    ((ContinuousLinearMap.inl ℝ A B).contDiff.contDiffAt.comp x (hf.of_le (by exact_mod_cast le_top)))
  have hg' : ContDiffAt ℝ i ((ContinuousLinearMap.inr ℝ A B) ∘ g) x :=
    ((ContinuousLinearMap.inr ℝ A B).contDiff.contDiffAt.comp x (hg.of_le (by exact_mod_cast le_top)))
  rw [h, iteratedFDeriv_add_apply hf' hg']
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine ((ContinuousLinearMap.inl ℝ A B).norm_iteratedFDeriv_comp_left
      (hf.of_le (by exact_mod_cast le_top)) le_rfl).trans ?_
    exact mul_le_of_le_one_left (norm_nonneg _) (ContinuousLinearMap.norm_inl_le_one ℝ A B)
  · refine ((ContinuousLinearMap.inr ℝ A B).norm_iteratedFDeriv_comp_left
      (hg.of_le (by exact_mod_cast le_top)) le_rfl).trans ?_
    exact mul_le_of_le_one_left (norm_nonneg _) (ContinuousLinearMap.norm_inr_le_one ℝ A B)

/-- Jets of the graph `y ↦ (y, ζ y)` of order `≥ 1`. -/
theorem norm_iteratedFDeriv_graph_le_S112 {ζ : E → Z} {x : E} (hζ : ContDiffAt ℝ ∞ ζ x)
    {i : ℕ} (hi : 1 ≤ i) :
    ‖iteratedFDeriv ℝ i (fun y => (y, ζ y)) x‖ ≤ 1 + ‖iteratedFDeriv ℝ i ζ x‖ := by
  have := norm_iteratedFDeriv_prodMk_le_S112 (f := (id : E → E)) (g := ζ) contDiffAt_id hζ i
  exact this.trans (add_le_add (norm_iteratedFDeriv_id_le_S112 x hi) le_rfl)

/-- The derivative of `y ↦ Θ (y, ζ y)`. -/
theorem fderiv_graph_S112 {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {Θ : E × Z → W} (hΘ : ContDiff ℝ ∞ Θ) {ζ : E → Z} {y : E} (hζ : DifferentiableAt ℝ ζ y) :
    fderiv ℝ (fun y => Θ (y, ζ y)) y =
      (fderiv ℝ Θ (y, ζ y)).comp (ContinuousLinearMap.inl ℝ E Z) +
        ((fderiv ℝ Θ (y, ζ y)).comp (ContinuousLinearMap.inr ℝ E Z)).comp (fderiv ℝ ζ y) := by
  have hΘd : DifferentiableAt ℝ Θ (y, ζ y) :=
    (hΘ.differentiable (by simp)) (y, ζ y)
  have hγ : HasFDerivAt (fun y => (y, ζ y))
      ((ContinuousLinearMap.id ℝ E).prod (fderiv ℝ ζ y)) y :=
    (hasFDerivAt_id y).prodMk hζ.hasFDerivAt
  have h := hΘd.hasFDerivAt.comp y hγ
  change fderiv ℝ (Θ ∘ fun y => (y, ζ y)) y = _
  rw [h.fderiv]
  ext v
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.coe_id', id_eq, add_apply,
    ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply]
  rw [← map_add]
  simp

/-- Precomposition with a map of norm `≤ 1` does not increase the iterated derivatives of
`fderiv Θ`: `‖D^i (q ↦ (fderiv Θ q) ∘ T)‖ ≤ ‖D^{i+1} Θ‖`. -/
theorem norm_iteratedFDeriv_precomp_le_S112 {A B W : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {Θ : B → W} (hΘ : ContDiff ℝ ∞ Θ) (T : A →L[ℝ] B) (hT : ‖T‖ ≤ 1) (p : B) (i : ℕ) :
    ‖iteratedFDeriv ℝ i (fun q => (fderiv ℝ Θ q).comp T) p‖ ≤
      ‖iteratedFDeriv ℝ (i + 1) Θ p‖ := by
  have hd : ContDiffAt ℝ ∞ (fderiv ℝ Θ) p :=
    (hΘ.fderiv_right (m := ∞) (by simp)).contDiffAt
  have hn : ‖iteratedFDeriv ℝ i (fderiv ℝ Θ) p‖ = ‖iteratedFDeriv ℝ (i + 1) Θ p‖ :=
    norm_iteratedFDeriv_fderiv
  let L : (B →L[ℝ] W) →L[ℝ] (A →L[ℝ] W) := (ContinuousLinearMap.compL ℝ A B W).flip T
  have hL : ‖L‖ ≤ 1 := by
    calc ‖L‖ ≤ ‖(ContinuousLinearMap.compL ℝ A B W).flip‖ * ‖T‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * 1 := by
          rw [ContinuousLinearMap.opNorm_flip]
          exact mul_le_mul (ContinuousLinearMap.norm_compL_le ℝ A B W) hT (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hfun : (fun q => (fderiv ℝ Θ q).comp T) = L ∘ fderiv ℝ Θ := rfl
  rw [hfun, ← hn]
  exact (L.norm_iteratedFDeriv_comp_left hd (by exact_mod_cast le_top)).trans (mul_le_of_le_one_left (norm_nonneg _) hL)

/-- **Hadamard jet bound.**  `C` depends only on `M` and `l` (not on `W`, `Θ`, `ζ`, `V`, `x`). -/
theorem hadamard_jets_S112 (Ks : Set E) (M : ℝ) (hM0 : 0 ≤ M) (l : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] (Θ : E × Z → W),
      ContDiff ℝ ∞ Θ → (∀ y, Θ (y, 0) = 0) →
      (∀ i ≤ l + 1, ∀ y ∈ Ks, ∀ z : Z, ‖z‖ ≤ 1 → ‖iteratedFDeriv ℝ i Θ (y, z)‖ ≤ M) →
      ∀ (ζ : E → Z) (V : Set E), IsOpen V → ContDiffOn ℝ ∞ ζ V → ∀ x ∈ V, x ∈ Ks →
        (∀ i ≤ l, ‖iteratedFDeriv ℝ i ζ x‖ ≤ 1) →
        ‖iteratedFDeriv ℝ l (fun y => Θ (y, ζ y)) x‖ ≤
          C * ∑ i ∈ Finset.range (l + 1), ‖iteratedFDeriv ℝ i ζ x‖ := by
  induction l with
  | zero =>
    refine ⟨M, hM0, fun W _ _ Θ hΘ hΘ0 hM ζ V hV hζ x hx hxK hj => ?_⟩
    have hz1 : ‖ζ x‖ ≤ 1 := by simpa [norm_iteratedFDeriv_zero] using hj 0 le_rfl
    simp only [norm_iteratedFDeriv_zero]
    have hdiff : ∀ z : Z, HasFDerivAt (fun z => Θ (x, z))
        ((fderiv ℝ Θ (x, z)).comp (ContinuousLinearMap.inr ℝ E Z)) z := fun z =>
      ((hΘ.differentiable (by simp)) (x, z)).hasFDerivAt.comp z (hasFDerivAt_prodMk_right x z)
    have hmv := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := fun z => Θ (x, z))
      (C := M) (s := Metric.closedBall (0 : Z) 1) (x := 0) (y := ζ x)
      (fun z _ => (hdiff z).differentiableAt)
      (fun z hz => by
        rw [(hdiff z).fderiv]
        refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
        have h1 := hM 1 (by omega) x hxK z (by simpa using hz)
        rw [norm_iteratedFDeriv_one] at h1
        calc _ ≤ M * 1 := mul_le_mul h1 (ContinuousLinearMap.norm_inr_le_one ℝ E Z)
              (norm_nonneg _) hM0
          _ = M := mul_one M)
      (convex_closedBall _ _) (by simp) (by simpa using hz1)
    simpa [hΘ0] using hmv
  | succ l ih =>
    obtain ⟨C₁, hC₁, h₁⟩ := ih
    set Q : ℝ := ∑ i ∈ Finset.range (l + 1), (l.choose i : ℝ) * ((i.factorial : ℝ) * M * 2 ^ i) with hQ
    have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun i _ => by positivity
    refine ⟨C₁ + Q, add_nonneg hC₁ hQ0, fun W _ _ Θ hΘ hΘ0 hM ζ V hV hζ x hx hxK hj => ?_⟩
    have hζx : ContDiffAt ℝ ∞ ζ x := (hζ x hx).contDiffAt (hV.mem_nhds hx)
    have hγx : ContDiffAt ℝ ∞ (fun y => (y, ζ y)) x := contDiffAt_id.prodMk hζx
    have hz1 : ‖ζ x‖ ≤ 1 := by simpa [norm_iteratedFDeriv_zero] using hj 0 (Nat.zero_le _)
    have hdΘ : ContDiff ℝ ∞ (fderiv ℝ Θ) := hΘ.fderiv_right (m := ∞) (by simp)
    set Θ₁ : E × Z → (E →L[ℝ] W) := fun q => (fderiv ℝ Θ q).comp (ContinuousLinearMap.inl ℝ E Z)
      with hΘ₁
    set Θ₂ : E × Z → (Z →L[ℝ] W) := fun q => (fderiv ℝ Θ q).comp (ContinuousLinearMap.inr ℝ E Z)
      with hΘ₂
    have hΘ₁c : ContDiff ℝ ∞ Θ₁ := hdΘ.clm_comp contDiff_const
    have hΘ₂c : ContDiff ℝ ∞ Θ₂ := hdΘ.clm_comp contDiff_const
    have hΘ₁0 : ∀ y, Θ₁ (y, 0) = 0 := by
      intro y
      have h1 : HasFDerivAt (fun y' : E => Θ (y', 0))
          ((fderiv ℝ Θ (y, 0)).comp (ContinuousLinearMap.inl ℝ E Z)) y :=
        ((hΘ.differentiable (by simp)) (y, 0)).hasFDerivAt.comp y (hasFDerivAt_prodMk_left y 0)
      have h2 : HasFDerivAt (fun y' : E => Θ (y', 0)) (0 : E →L[ℝ] W) y := by
        simp only [hΘ0]; exact hasFDerivAt_const _ _
      exact h1.unique h2
    have hM₁ : ∀ i ≤ l + 1, ∀ y ∈ Ks, ∀ z : Z, ‖z‖ ≤ 1 →
        ‖iteratedFDeriv ℝ i Θ₁ (y, z)‖ ≤ M := fun i hi y hy z hz =>
      (norm_iteratedFDeriv_precomp_le_S112 hΘ (ContinuousLinearMap.inl ℝ E Z)
        (ContinuousLinearMap.norm_inl_le_one ℝ E Z) (y, z) i).trans (hM (i + 1) (by omega) y hy z hz)
    have hIH := h₁ (E →L[ℝ] W) Θ₁ hΘ₁c hΘ₁0 hM₁ ζ V hV hζ x hx hxK
      (fun i hi => hj i (by omega))
    -- the derivative of `Θ ∘ (id, ζ)`
    have hdζ : ContDiffOn ℝ ∞ (fderiv ℝ ζ) V := hζ.fderiv_of_isOpen hV (by simp)
    have hdζx : ContDiffAt ℝ ∞ (fderiv ℝ ζ) x := (hdζ x hx).contDiffAt (hV.mem_nhds hx)
    have heq : fderiv ℝ (fun y => Θ (y, ζ y)) =ᶠ[𝓝 x]
        fun y => Θ₁ (y, ζ y) + (ContinuousLinearMap.compL ℝ E Z W) (Θ₂ (y, ζ y)) (fderiv ℝ ζ y) := by
      filter_upwards [hV.mem_nhds hx] with y hy
      exact fderiv_graph_S112 hΘ (((hζ.differentiableOn (by simp)).differentiableAt (hV.mem_nhds hy)))
    rw [← norm_iteratedFDeriv_fderiv, (heq.iteratedFDeriv ℝ l).eq_of_nhds]
    have hT₁ : ContDiffAt ℝ l (fun y => Θ₁ (y, ζ y)) x :=
      ((hΘ₁c.contDiffAt.comp x hγx).of_le (by exact_mod_cast le_top))
    have hT₂ : ContDiffAt ℝ l (fun y => (ContinuousLinearMap.compL ℝ E Z W) (Θ₂ (y, ζ y))
        (fderiv ℝ ζ y)) x :=
      ((hΘ₂c.contDiffAt.comp x hγx).clm_comp hdζx).of_le (by exact_mod_cast le_top)
    rw [show (fun y => Θ₁ (y, ζ y) + (ContinuousLinearMap.compL ℝ E Z W) (Θ₂ (y, ζ y)) (fderiv ℝ ζ y))
      = (fun y => Θ₁ (y, ζ y)) + (fun y => (ContinuousLinearMap.compL ℝ E Z W) (Θ₂ (y, ζ y))
        (fderiv ℝ ζ y)) from rfl, iteratedFDeriv_add_apply hT₁ hT₂]
    refine (norm_add_le _ _).trans ?_
    set S : ℝ := ∑ j ∈ Finset.range (l + 1 + 1), ‖iteratedFDeriv ℝ j ζ x‖ with hS
    have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => norm_nonneg _
    have hsub : ∑ i ∈ Finset.range (l + 1), ‖iteratedFDeriv ℝ i ζ x‖ ≤ S :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
        (fun _ _ _ => norm_nonneg _)
    -- second term: Leibniz for `compL`
    have hLeib := (ContinuousLinearMap.compL ℝ E Z W).norm_iteratedFDerivWithin_le_of_bilinear_of_le_one
      (f := fun y => Θ₂ (y, ζ y)) (g := fderiv ℝ ζ) (N := ∞) (s := V) (x := x) (n := l)
      ((hΘ₂c.contDiffOn.comp (contDiffOn_id.prodMk hζ) (fun y _ => mem_univ _)))
      hdζ hV.uniqueDiffOn hx (by exact_mod_cast le_top) (ContinuousLinearMap.norm_compL_le ℝ E Z W)
    rw [iteratedFDerivWithin_of_isOpen l hV hx] at hLeib
    have hterm : ∀ i ∈ Finset.range (l + 1),
        (l.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i (fun y => Θ₂ (y, ζ y)) V x‖ *
          ‖iteratedFDerivWithin ℝ (l - i) (fderiv ℝ ζ) V x‖ ≤
        (l.choose i : ℝ) * ((i.factorial : ℝ) * M * 2 ^ i) * S := by
      intro i hi
      have hil : i ≤ l := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      have hC : ∀ j ≤ i, ‖iteratedFDerivWithin ℝ j Θ₂ univ ((fun y => (y, ζ y)) x)‖ ≤ M := by
        intro j hjl
        rw [iteratedFDerivWithin_univ]
        exact (norm_iteratedFDeriv_precomp_le_S112 hΘ (ContinuousLinearMap.inr ℝ E Z)
          (ContinuousLinearMap.norm_inr_le_one ℝ E Z) (x, ζ x) j).trans
          (hM (j + 1) (by omega) x hxK (ζ x) hz1)
      have hD : ∀ j, 1 ≤ j → j ≤ i →
          ‖iteratedFDerivWithin ℝ j (fun y => (y, ζ y)) V x‖ ≤ (2 : ℝ) ^ j := by
        intro j hj1 hji
        rw [iteratedFDerivWithin_of_isOpen j hV hx]
        calc _ ≤ 1 + ‖iteratedFDeriv ℝ j ζ x‖ := norm_iteratedFDeriv_graph_le_S112 hζx hj1
          _ ≤ 1 + 1 := by linarith [hj j (by omega)]
          _ = (2 : ℝ) ^ 1 := by norm_num
          _ ≤ (2 : ℝ) ^ j := pow_le_pow_right₀ (by norm_num) hj1
      have h1 : ‖iteratedFDerivWithin ℝ i (fun y => Θ₂ (y, ζ y)) V x‖ ≤
          (i.factorial : ℝ) * M * 2 ^ i :=
        norm_iteratedFDerivWithin_comp_le (g := Θ₂) (f := fun y => (y, ζ y)) (n := i) (s := V)
          (t := univ) (x := x) (N := ∞) hΘ₂c.contDiffOn (contDiffOn_id.prodMk hζ)
          (by exact_mod_cast le_top) uniqueDiffOn_univ hV.uniqueDiffOn (fun y _ => mem_univ _) hx
          hC hD
      have h2 : ‖iteratedFDerivWithin ℝ (l - i) (fderiv ℝ ζ) V x‖ ≤ S := by
        rw [iteratedFDerivWithin_of_isOpen _ hV hx, norm_iteratedFDeriv_fderiv]
        exact Finset.single_le_sum (f := fun j => ‖iteratedFDeriv ℝ j ζ x‖)
          (fun _ _ => norm_nonneg _) (Finset.mem_range.2 (by omega))
      exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (by positivity)) h2 (norm_nonneg _)
        (by positivity)
    calc _ ≤ C₁ * S + Q * S := add_le_add (hIH.trans (mul_le_mul_of_nonneg_left hsub hC₁))
          (hLeib.trans ((Finset.sum_le_sum hterm).trans (by rw [hQ, Finset.sum_mul])))
      _ = (C₁ + Q) * S := by ring

end HadamardJets

end GC.LongTime.Ch12
