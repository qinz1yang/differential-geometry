import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

noncomputable section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem iteratedDeriv_pow_smul_zero {n : ℕ} {f : 𝕜 → F}
    (hf : ContDiffAt 𝕜 n f 0) (m : ℕ) :
    iteratedDeriv n (fun x => x ^ m • f x) 0 =
      ((n.choose m : 𝕜) * m.factorial) • iteratedDeriv (n - m) f 0 := by
  have h := iteratedDerivWithin_smul (Set.mem_univ (0 : 𝕜)) uniqueDiffOn_univ
    (contDiffWithinAt_id.pow m) hf.contDiffWithinAt
  simp only [iteratedDerivWithin_univ, id_eq, iteratedDeriv_fun_pow_zero] at h
  refine h.trans ?_
  rw [Finset.sum_eq_single m]
  · simp [← Nat.cast_smul_eq_nsmul 𝕜, smul_smul]
  · intro i hi him
    simp [if_neg him]
  · intro hm
    have hnm : n < m := by simpa using hm
    simp [Nat.choose_eq_zero_of_lt hnm]

theorem iteratedDeriv_pow_mul_zero {n : ℕ} {f : 𝕜 → 𝕜}
    (hf : ContDiffAt 𝕜 n f 0) (m : ℕ) :
    iteratedDeriv n (fun x => x ^ m * f x) 0 =
      (n.choose m : 𝕜) * m.factorial * iteratedDeriv (n - m) f 0 := by
  simpa only [smul_eq_mul] using iteratedDeriv_pow_smul_zero hf m
