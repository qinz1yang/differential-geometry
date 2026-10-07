import DifferentialGeometry.Analysis.Calculus.IteratedDerivative.DirectionalJets
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Complex.Basic

/-!
# R3a-ω（`_R3AW`）F1：jets 层引理

实解析 `w : ℂ → ℝ` 的有限阶（G1）、1-D Leibniz（低阶 jets 为零时）、`fderiv` 的 iterated jets 与
`Fin.cons` 的对应、对称多线性型的 polarization 与对角导数。所有引理与平面 elliptic 方程无关，
供 `AnalyticNodalPrincipalR3AW`（G2）使用。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace DifferentialGeometry.Analysis

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem contDiffAt_deriv_R3AW {f : ℝ → ℝ} {m : ℕ} {x : ℝ}
    (hf : ContDiffAt ℝ ((m + 1 : ℕ) : WithTop ℕ∞) f x) :
    ContDiffAt ℝ (m : WithTop ℕ∞) (deriv f) x := by
  have h := hf.fderiv_right (m := m) (by norm_cast)
  have h2 := h.clm_apply (contDiffAt_const (c := (1 : ℝ)))
  exact h2

/-- 1-D Leibniz：`g` 的 `0` 点前 `m` 阶导数为零时，`(f g)^{(m)}(0) = f(0) g^{(m)}(0)`。 -/
theorem iteratedDeriv_mul_of_vanishing_R3AW :
    ∀ (m : ℕ) {f g : ℝ → ℝ}, ContDiffAt ℝ (m : WithTop ℕ∞) f 0 →
      ContDiffAt ℝ (m : WithTop ℕ∞) g 0 → (∀ l < m, iteratedDeriv l g 0 = 0) →
      iteratedDeriv m (fun s => f s * g s) 0 = f 0 * iteratedDeriv m g 0 := by
  intro m
  induction m with
  | zero => intro f g _ _ _; simp
  | succ m ih =>
    intro f g hf hg hz
    have hf1 : ContDiffAt ℝ (1 : WithTop ℕ∞) f 0 := hf.of_le (by norm_cast; omega)
    have hg1 : ContDiffAt ℝ (1 : WithTop ℕ∞) g 0 := hg.of_le (by norm_cast; omega)
    have hev : ∀ᶠ y in nhds (0 : ℝ), ContDiffAt ℝ ((m + 1 : ℕ) : WithTop ℕ∞) f y ∧
        ContDiffAt ℝ ((m + 1 : ℕ) : WithTop ℕ∞) g y :=
      (hf.eventually (by simp)).and (hg.eventually (by simp))
    have hder : deriv (fun s => f s * g s) =ᶠ[nhds 0]
        fun s => deriv f s * g s + f s * deriv g s := by
      filter_upwards [hev] with y hy
      have h1 := (hy.1.differentiableAt (by norm_cast)).hasDerivAt
      have h2 := (hy.2.differentiableAt (by norm_cast)).hasDerivAt
      exact (h1.mul h2).deriv
    rw [iteratedDeriv_succ', hder.iteratedDeriv_eq]
    have hf' := contDiffAt_deriv_R3AW hf
    have hg' := contDiffAt_deriv_R3AW hg
    have hfm : ContDiffAt ℝ (m : WithTop ℕ∞) f 0 := hf.of_le (by norm_cast; omega)
    have hgm : ContDiffAt ℝ (m : WithTop ℕ∞) g 0 := hg.of_le (by norm_cast; omega)
    rw [iteratedDeriv_fun_add (hf'.mul hgm) (hfm.mul hg'),
      ih hf' hgm (fun l hl => hz l (by omega)),
      ih hfm hg' (fun l hl => by
        rw [← iteratedDeriv_succ']
        exact hz (l + 1) (by omega)),
      ← iteratedDeriv_succ', hz m (by omega)]
    simp


theorem iteratedFDeriv_fderiv_apply_R3AW {f : E → F} {x : E} (hf : ContDiffAt ℝ ∞ f x)
    (j : ℕ) (u : E) (m : Fin j → E) :
    iteratedFDeriv ℝ j (fun y => fderiv ℝ f y u) x m =
      iteratedFDeriv ℝ (j + 1) f x (Fin.cons u m) := by
  rw [← fderiv_iter_apply hf j u, iteratedFDeriv_succ_apply_left]
  simp

theorem iteratedFDeriv_fderiv_fderiv_apply_R3AW {f : E → F} {x : E} (hf : ContDiffAt ℝ ∞ f x)
    (j : ℕ) (ξ η : E) (m : Fin j → E) :
    iteratedFDeriv ℝ j (fun y => fderiv ℝ (fderiv ℝ f) y ξ η) x m =
      iteratedFDeriv ℝ (j + 2) f x (Fin.cons η (Fin.cons ξ m)) := by
  have hd : ContDiffAt ℝ ∞ (fderiv ℝ f) x := hf.fderiv_right (by simp)
  have hdd : ContDiffAt ℝ ∞ (fderiv ℝ (fderiv ℝ f)) x := hd.fderiv_right (by simp)
  have h1 := iterFDeriv_clm_apply (c := fun y => fderiv ℝ (fderiv ℝ f) y ξ) (x := x)
    (hdd.clm_apply contDiffAt_const) j η m
  rw [h1]
  have h2 := iteratedFDeriv_fderiv_apply_R3AW hd j ξ m
  rw [h2]
  have h3 := iterFDeriv_clm_apply (c := fderiv ℝ f) (x := x) hd (j + 1) η (Fin.cons ξ m)
  rw [← h3]
  exact iteratedFDeriv_fderiv_apply_R3AW hf (j + 1) η (Fin.cons ξ m)

/-- G1：实解析且零点处不恒为零 ⇒ 有限阶：最低阶 jet 非零，更低阶 jet 全零。 -/
theorem analytic_finite_order_R3AW {w : ℂ → ℝ} {p : ℂ} (hw : AnalyticAt ℝ w p) (hz : w p = 0)
    (hnz : ¬ (w =ᶠ[𝓝 p] 0)) :
    ∃ k : ℕ, 1 ≤ k ∧ (∀ j < k, iteratedFDeriv ℝ j w p = 0) ∧ iteratedFDeriv ℝ k w p ≠ 0 := by
  have hex : ∃ n : ℕ, iteratedFDeriv ℝ n w p ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨pser, r, hr⟩ := hw
    apply hnz
    have hsum : ∀ y ∈ Metric.eball (0 : ℂ) r, w (p + y) = 0 := by
      intro y hy
      have h := hr.hasSum_iteratedFDeriv hy
      have h0 : (fun n : ℕ => ((n.factorial : ℝ))⁻¹ • iteratedFDeriv ℝ n w p fun _ => y) =
          fun _ => 0 := by
        funext n
        simp [hcon n]
      rw [h0] at h
      exact (hasSum_zero.unique h).symm
    have hev : ∀ᶠ y in 𝓝 (0 : ℂ), w (p + y) = 0 := by
      filter_upwards [Metric.isOpen_eball.mem_nhds (Metric.mem_eball_self hr.r_pos)] with y hy
      exact hsum y hy
    have hlim : Filter.Tendsto (fun z : ℂ => z - p) (𝓝 p) (𝓝 0) := by
      have := ((continuous_id.sub (continuous_const : Continuous fun _ : ℂ => p)).tendsto p)
      rw [show (0 : ℂ) = id p - p from by simp]
      exact this
    filter_upwards [hlim.eventually hev] with z hz'
    simpa using hz'
  classical
  refine ⟨Nat.find hex, ?_, ?_, Nat.find_spec hex⟩
  · by_contra hk
    have h0 : Nat.find hex = 0 := by omega
    apply Nat.find_spec hex
    rw [h0]
    ext m
    simp [hz]
  · intro j hj
    have := Nat.find_min hex hj
    push Not at this
    exact this

/-- 多线性型对角为零且对称 ⇒ 为零（polarization，借 `iteratedFDeriv_comp_diagonal`）。 -/
theorem multilinear_eq_zero_of_diag_zero_R3AW {n : ℕ}
    (S : ContinuousMultilinearMap ℝ (fun _ : Fin n => ℂ) ℝ)
    (hS : ∀ (σ : Equiv.Perm (Fin n)) (v : Fin n → ℂ), S (v ∘ σ) = S v)
    (h0 : ∀ y : ℂ, S (fun _ => y) = 0) : S = 0 := by
  ext v
  have key := S.iteratedFDeriv_comp_diagonal (0 : ℂ) v
  have hfun : (fun x : ℂ => S (fun _ => x)) = fun _ => 0 := funext h0
  rw [hfun] at key
  have hz : iteratedFDeriv ℝ n (fun _ : ℂ => (0 : ℝ)) 0 v = 0 := by
    simp
  rw [hz] at key
  have hsum : ∑ σ : Equiv.Perm (Fin n), S (fun i => v (σ i)) = (n.factorial : ℝ) * S v := by
    have : ∀ σ : Equiv.Perm (Fin n), S (fun i => v (σ i)) = S v := fun σ => hS σ v
    simp [this, Fintype.card_perm]
  rw [hsum] at key
  have hne : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  simpa [hne] using key.symm

/-- 对称多线性型：把一个位置换成 `b`，其余全是 `a`，值与位置无关。 -/
theorem multilinear_update_const_R3AW {n : ℕ}
    (S : ContinuousMultilinearMap ℝ (fun _ : Fin (n + 1) => ℂ) ℝ)
    (hS : ∀ (σ : Equiv.Perm (Fin (n + 1))) (v : Fin (n + 1) → ℂ), S (v ∘ σ) = S v)
    (a b : ℂ) (i : Fin (n + 1)) :
    S (Function.update (fun _ => a) i b) = S (Fin.cons b (fun _ : Fin n => a)) := by
  have hfun : Function.update (fun _ : Fin (n + 1) => a) i b =
      (Fin.cons b (fun _ : Fin n => a) : Fin (n + 1) → ℂ) ∘ Equiv.swap 0 i := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp
    · by_cases hj0 : j = 0
      · subst hj0
        have hi0 : i ≠ 0 := fun h => hj h.symm
        obtain ⟨i', rfl⟩ := Fin.exists_succ_eq.mpr hi0
        simp [Function.update_of_ne hj]
      · have hsw : Equiv.swap 0 i j = j := Equiv.swap_apply_of_ne_of_ne hj0 hj
        obtain ⟨j', rfl⟩ := Fin.exists_succ_eq.mpr hj0
        simp [Function.update_of_ne hj, hsw]
  rw [hfun, hS]

/-- 对角多线性型沿曲线的导数：`d/ds S(g s, …, g s) = (n+1) S(g', g, …, g)`。 -/
theorem hasDerivAt_diag_R3AW {n : ℕ}
    (S : ContinuousMultilinearMap ℝ (fun _ : Fin (n + 1) => ℂ) ℝ)
    (hS : ∀ (σ : Equiv.Perm (Fin (n + 1))) (v : Fin (n + 1) → ℂ), S (v ∘ σ) = S v)
    {g : ℝ → ℂ} {g' : ℂ} {t : ℝ} (hg : HasDerivAt g g' t) :
    HasDerivAt (fun s => S (fun _ => g s))
      (((n : ℝ) + 1) * S (Fin.cons g' (fun _ : Fin n => g t))) t := by
  have hv : HasDerivAt (fun s => (fun _ : Fin (n + 1) => g s)) (fun _ => g') t :=
    hasDerivAt_pi.mpr (fun _ => hg)
  have hS' : HasFDerivAt S (S.linearDeriv (fun _ : Fin (n + 1) => g t))
      (fun _ : Fin (n + 1) => g t) := S.hasFDerivAt _
  have h := hS'.comp_hasDerivAt t hv
  have hval : (S.linearDeriv (fun _ : Fin (n + 1) => g t)) (fun _ => g') =
      ((n : ℝ) + 1) * S (Fin.cons g' (fun _ : Fin n => g t)) := by
    rw [ContinuousMultilinearMap.linearDeriv_apply]
    simp only [multilinear_update_const_R3AW S hS (g t) g']
    simp
  rw [← hval]
  exact h

theorem update_cons_succ_eq_comp_swap_R3AW {n : ℕ} (c a b : ℂ) (j : Fin (n + 1)) :
    Function.update (Fin.cons c (fun _ : Fin (n + 1) => a) : Fin (n + 2) → ℂ) j.succ b =
      (Fin.cons c (Fin.cons b (fun _ : Fin n => a)) : Fin (n + 2) → ℂ) ∘
        Equiv.swap 1 j.succ := by
  funext x
  by_cases hx : x = j.succ
  · subst hx
    simp
  · by_cases hx1 : x = 1
    · subst hx1
      have hj : j ≠ 0 := by
        intro h
        apply hx
        rw [h]
        rfl
      obtain ⟨j', rfl⟩ := Fin.exists_succ_eq.mpr hj
      simp [Function.update_of_ne hx]
    · rw [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne hx1 hx, Function.update_of_ne hx]
      induction x using Fin.cases with
      | zero => simp
      | succ y =>
        have hy : y ≠ 0 := by
          intro h
          apply hx1
          rw [h]
          rfl
        obtain ⟨y', rfl⟩ := Fin.exists_succ_eq.mpr hy
        simp

/-- 带一个「速度槽」的对角多线性型的导数（第二次求导用）。 -/
theorem hasDerivAt_diag_cons_R3AW {n : ℕ}
    (S : ContinuousMultilinearMap ℝ (fun _ : Fin (n + 2) => ℂ) ℝ)
    (hS : ∀ (σ : Equiv.Perm (Fin (n + 2))) (v : Fin (n + 2) → ℂ), S (v ∘ σ) = S v)
    {g G : ℝ → ℂ} {G' : ℂ} {t : ℝ} (hg : HasDerivAt g (G t) t) (hG : HasDerivAt G G' t) :
    HasDerivAt (fun s => S (Fin.cons (G s) (fun _ : Fin (n + 1) => g s)))
      (S (Fin.cons G' (fun _ : Fin (n + 1) => g t)) +
        ((n : ℝ) + 1) * S (Fin.cons (G t) (Fin.cons (G t) (fun _ : Fin n => g t)))) t := by
  have hv : HasDerivAt (fun s => (Fin.cons (G s) (fun _ : Fin (n + 1) => g s) : Fin (n + 2) → ℂ))
      (Fin.cons G' (fun _ : Fin (n + 1) => G t) : Fin (n + 2) → ℂ) t := by
    rw [hasDerivAt_pi]
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using hG
    · simpa using hg
  have hS' : HasFDerivAt S (S.linearDeriv (Fin.cons (G t) (fun _ : Fin (n + 1) => g t)))
      (Fin.cons (G t) (fun _ : Fin (n + 1) => g t)) := S.hasFDerivAt _
  have h := hS'.comp_hasDerivAt t hv
  have hval : (S.linearDeriv (Fin.cons (G t) (fun _ : Fin (n + 1) => g t) : Fin (n + 2) → ℂ))
      (Fin.cons G' (fun _ : Fin (n + 1) => G t)) =
      S (Fin.cons G' (fun _ : Fin (n + 1) => g t)) +
        ((n : ℝ) + 1) * S (Fin.cons (G t) (Fin.cons (G t) (fun _ : Fin n => g t))) := by
    rw [ContinuousMultilinearMap.linearDeriv_apply, Fin.sum_univ_succ]
    congr 1
    · simp
    · have hj : ∀ j : Fin (n + 1),
          S (Function.update (Fin.cons (G t) (fun _ : Fin (n + 1) => g t) : Fin (n + 2) → ℂ)
            j.succ ((Fin.cons G' (fun _ : Fin (n + 1) => G t) : Fin (n + 2) → ℂ) j.succ)) =
          S (Fin.cons (G t) (Fin.cons (G t) (fun _ : Fin n => g t))) := by
        intro j
        simp only [Fin.cons_succ]
        rw [update_cons_succ_eq_comp_swap_R3AW, hS]
      simp only [hj, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      ring
  rw [← hval]
  exact h

end DifferentialGeometry.Analysis

end
