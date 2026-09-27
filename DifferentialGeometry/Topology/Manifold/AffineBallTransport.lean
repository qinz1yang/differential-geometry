import DifferentialGeometry.Analysis.ODE.Flow.Planar.LinearGermRealization
import DifferentialGeometry.Topology.Manifold.SupportedBallTransport

set_option autoImplicit false
noncomputable section
open Set Metric Filter Topology
open scoped ContDiff Manifold Matrix

namespace DifferentialGeometry.Topology.Manifold

private abbrev Euc (n : ℕ) := EuclideanSpace ℝ (Fin n)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {n : ℕ}

private def modelTranslateDiffeomorph (t : E) : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞ where
  toEquiv :=
    { toFun := fun x => x + t
      invFun := fun x => x - t
      left_inv := fun x => by simp
      right_inv := fun x => by simp }
  contMDiff_toFun := contMDiff_id.add contMDiff_const
  contMDiff_invFun := contMDiff_id.sub contMDiff_const

omit [FiniteDimensional ℝ E] in
private theorem modelTranslateDiffeomorph_apply (t x : E) :
    modelTranslateDiffeomorph t x = x + t := rfl

private theorem translate_of_tube_aux (N : ℕ) :
    ∀ (p q : E) (ρ δ : ℝ) (V : Set E), 0 ≤ ρ → ρ < δ →
      ‖q - p‖ < 2 ^ N * (δ - ρ) →
      (∀ t ∈ Icc (0 : ℝ) 1, closedBall (p + t • (q - p)) δ ⊆ V) →
      ∃ T : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞,
        (∀ y ∈ closedBall p ρ, T y = y + (q - p)) ∧
        ∃ K : Set E, IsCompact K ∧ K ⊆ V ∧ ∀ y ∉ K, T y = y ∧ T.symm y = y := by
  induction N with
  | zero =>
      intro p q ρ δ V hρ hρδ hlen htube
      have hR : ρ + ‖q - p‖ < δ := by
        rw [pow_zero, one_mul] at hlen
        linarith
      obtain ⟨T, hT, hfix⟩ :=
        DifferentialGeometry.Analysis.exists_compact_diffeomorph_translate_on_closedBall
          p q hρ hR
      refine ⟨T, hT, closedBall p δ, isCompact_closedBall _ _, ?_, hfix⟩
      simpa using htube 0 ⟨le_refl 0, zero_le_one⟩
  | succ N ih =>
      intro p q ρ δ V hρ hρδ hlen htube
      set m : E := p + (1 / 2 : ℝ) • (q - p) with hm
      have hm_p : m - p = (1 / 2 : ℝ) • (q - p) := by rw [hm, add_sub_cancel_left]
      have hq_m : q - m = (1 / 2 : ℝ) • (q - p) := by
        have h : (1 : ℝ) • (q - p) - (1 / 2 : ℝ) • (q - p) = (1 / 2 : ℝ) • (q - p) := by
          rw [← sub_smul]
          norm_num
        rw [hm, sub_add_eq_sub_sub]
        simpa using h
      have hhalf : (1 / 2 : ℝ) * ‖q - p‖ < 2 ^ N * (δ - ρ) := by
        rw [pow_succ] at hlen
        nlinarith [hlen]
      have hm_p_norm : ‖m - p‖ = (1 / 2 : ℝ) * ‖q - p‖ := by
        rw [hm_p, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      have hq_m_norm : ‖q - m‖ = (1 / 2 : ℝ) * ‖q - p‖ := by
        rw [hq_m, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      have hsmul₁ : ∀ t : ℝ, t • (m - p) = (t / 2) • (q - p) := by
        intro t
        rw [hm_p, smul_smul]
        congr 1
        ring
      have hsmul₂ : ∀ t : ℝ, (1 / 2 : ℝ) • (q - p) + t • ((1 / 2 : ℝ) • (q - p))
          = ((1 + t) / 2) • (q - p) := by
        intro t
        rw [smul_smul, ← add_smul]
        congr 1
        ring
      have htube₁ : ∀ t ∈ Icc (0 : ℝ) 1, closedBall (p + t • (m - p)) δ ⊆ V := by
        intro t ht
        rw [hsmul₁ t]
        exact htube (t / 2) ⟨by linarith [ht.1], by linarith [ht.2]⟩
      have htube₂ : ∀ t ∈ Icc (0 : ℝ) 1, closedBall (m + t • (q - m)) δ ⊆ V := by
        intro t ht
        have hpt : m + t • (q - m) = p + ((1 + t) / 2) • (q - p) := by
          rw [hm, hq_m, add_assoc, hsmul₂ t]
        rw [hpt]
        exact htube ((1 + t) / 2) ⟨by linarith [ht.1], by linarith [ht.2]⟩
      obtain ⟨T₁, hT₁, K₁, hK₁c, hK₁V, hK₁fix⟩ :=
        ih p m ρ δ V hρ hρδ (by rw [hm_p_norm]; exact hhalf) htube₁
      obtain ⟨T₂, hT₂, K₂, hK₂c, hK₂V, hK₂fix⟩ :=
        ih m q ρ δ V hρ hρδ (by rw [hq_m_norm]; exact hhalf) htube₂
      refine ⟨T₁.trans T₂, ?_, K₁ ∪ K₂, hK₁c.union hK₂c, union_subset hK₁V hK₂V,
        ?_⟩
      · intro y hy
        have hy₁ : y + (m - p) ∈ closedBall m ρ := by
          rw [mem_closedBall, dist_eq_norm]
          have hsub : y + (m - p) - m = y - p := by abel
          rw [hsub, ← dist_eq_norm]
          exact hy
        rw [Diffeomorph.coe_trans, Function.comp_apply, hT₁ y hy, hT₂ _ hy₁]
        abel
      · intro y hy
        have hy₁ : y ∉ K₁ := fun h => hy (Or.inl h)
        have hy₂ : y ∉ K₂ := fun h => hy (Or.inr h)
        have hfix : (T₁.trans T₂) y = y := by
          rw [Diffeomorph.coe_trans, Function.comp_apply, (hK₁fix y hy₁).1,
            (hK₂fix y hy₂).1]
        refine ⟨hfix, ?_⟩
        have hs := Diffeomorph.symm_apply_apply (T₁.trans T₂) y
        rw [hfix] at hs
        exact hs

theorem exists_compact_diffeomorph_translate_of_tube {p q : E} {ρ δ : ℝ} (hρ : 0 ≤ ρ)
    (hρδ : ρ < δ) {V : Set E}
    (htube : ∀ t ∈ Icc (0 : ℝ) 1, closedBall (p + t • (q - p)) δ ⊆ V) :
    ∃ T : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞,
      (∀ y ∈ closedBall p ρ, T y = y + (q - p)) ∧
      ∃ K : Set E, IsCompact K ∧ K ⊆ V ∧ ∀ y ∉ K, T y = y ∧ T.symm y = y := by
  have hpos : 0 < δ - ρ := sub_pos.mpr hρδ
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (‖q - p‖ / (δ - ρ))
    (by norm_num : (1 : ℝ) < 2)
  refine translate_of_tube_aux N p q ρ δ V hρ hρδ ?_ htube
  rw [div_lt_iff₀ hpos] at hN
  linarith [hN]

private def modelScaleDiffeomorph (s : ℝ) (hs : s ≠ 0) :
    Diffeomorph 𝓘(ℝ, Euc n) 𝓘(ℝ, Euc n) (Euc n) (Euc n) ∞ where
  toEquiv :=
    { toFun := fun x => s • x
      invFun := fun x => s⁻¹ • x
      left_inv := fun x => by simp only [smul_smul, inv_mul_cancel₀ hs, one_smul]
      right_inv := fun x => by simp only [smul_smul, mul_inv_cancel₀ hs, one_smul] }
  contMDiff_toFun := (contDiff_const_smul s).contMDiff
  contMDiff_invFun := (contDiff_const_smul s⁻¹).contMDiff

omit [FiniteDimensional ℝ E] in
private theorem modelScaleDiffeomorph_apply (s : ℝ) (hs : s ≠ 0) (x : Euc n) :
    modelScaleDiffeomorph s hs x = s • x := rfl

theorem exists_compact_diffeomorph_eqOn_closedBall_of_linear
    (B : Euc n ≃L[ℝ] Euc n) (hB : 0 < (B : Euc n →L[ℝ] Euc n).det) {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ (σ : ℝ) (Ψ : Diffeomorph 𝓘(ℝ, Euc n) 𝓘(ℝ, Euc n) (Euc n) (Euc n) ∞),
      0 < σ ∧
      (∀ z, ‖z‖ ≤ σ → Ψ z = B z) ∧
      ∃ K : Set (Euc n), IsCompact K ∧ K ⊆ closedBall 0 δ ∧
        ∀ y ∉ K, Ψ y = y ∧ Ψ.symm y = y := by
  let M : Matrix (Fin n) (Fin n) ℝ :=
    (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).symm (B : Euc n →L[ℝ] Euc n)
  have hMA : DifferentialGeometry.Analysis.matEnd M = (B : Euc n →L[ℝ] Euc n) := by
    rw [DifferentialGeometry.Analysis.matEnd_eq_toEuclideanCLM]
    exact StarAlgEquiv.apply_symm_apply _ _
  have hMdet : 0 < M.det := by
    have h : M.det = (B : Euc n →L[ℝ] Euc n).det :=
      DifferentialGeometry.Analysis.det_toEuclideanCLM_symm _
    rw [h]
    exact hB
  obtain ⟨-, -, D, hDc, hDic, hD0, hDg, hDfix⟩ :=
    DifferentialGeometry.Analysis.realizesGerm_matEnd_of_det_pos M hMdet
  obtain ⟨ρ₁, hρ₁pos, hρ₁⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hDg
  have hρ₁' : ∀ z : Euc n, ‖z‖ ≤ ρ₁ → D 1 z = B z := by
    intro z hz
    have := hρ₁ (mem_closedBall_zero_iff.mpr hz)
    rw [hMA] at this
    exact this
  set s : ℝ := δ / 2 with hsdef
  have hspos : 0 < s := by rw [hsdef]; linarith
  have hsne : s ≠ 0 := ne_of_gt hspos
  have h2s : 2 * s = δ := by rw [hsdef]; ring
  let F : ℝ → Diffeomorph 𝓘(ℝ, Euc n) 𝓘(ℝ, Euc n) (Euc n) (Euc n) ∞ := fun t =>
    (modelScaleDiffeomorph s⁻¹ (inv_ne_zero hsne)).trans
      ((D t).trans (modelScaleDiffeomorph s hsne))
  have hFapply : ∀ t y, F t y = s • D t (s⁻¹ • y) := by
    intro t y
    simp only [F, Diffeomorph.coe_trans, Function.comp_apply, modelScaleDiffeomorph_apply]
  have hFfix : ∀ t y, y ∉ closedBall (0 : Euc n) δ → F t y = y ∧ (F t).symm y = y := by
    intro t y hy
    have hy2 : y ∉ closedBall (0 : Euc n) (2 * s) := by rw [h2s]; exact hy
    have h2 : 2 * s < ‖y‖ := not_le.mp (by simpa [mem_closedBall_zero_iff] using hy2)
    have hnorm : 2 < ‖s⁻¹ • y‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hspos)]
      calc (2 : ℝ) = s⁻¹ * (2 * s) := by field_simp
        _ < s⁻¹ * ‖y‖ := mul_lt_mul_of_pos_left h2 (inv_pos.mpr hspos)
    have hfix := (hDfix t (s⁻¹ • y) (by simpa [mem_closedBall_zero_iff] using hnorm)).1
    have hval : F t y = y := by
      rw [hFapply, hfix, smul_smul, mul_inv_cancel₀ hsne, one_smul]
    refine ⟨hval, ?_⟩
    have hs := Diffeomorph.symm_apply_apply (F t) y
    rw [hval] at hs
    exact hs
  have hFgerm : ∀ z : Euc n, ‖z‖ ≤ s * ρ₁ → F 1 z = B z := by
    intro z hz
    have hnorm : ‖s⁻¹ • z‖ ≤ ρ₁ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hspos), inv_mul_le_iff₀ hspos]
      linarith [hz]
    rw [hFapply, hρ₁' _ hnorm, map_smul]
    rw [smul_smul, mul_inv_cancel₀ hsne, one_smul]
  exact ⟨s * ρ₁, F 1, mul_pos hspos hρ₁pos, hFgerm, closedBall (0 : Euc n) δ,
    isCompact_closedBall _ _, subset_rfl, fun y hy => hFfix 1 y hy⟩

theorem exists_compact_diffeomorph_affine_of_subset
    (p q : Euc n) (A₀ A₁ : Euc n ≃L[ℝ] Euc n)
    (hA : 0 < ((A₀.symm.trans A₁ : Euc n ≃L[ℝ] Euc n) : Euc n →L[ℝ] Euc n).det)
    {V : Set (Euc n)} (hV : IsOpen V)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, p + t • (q - p) ∈ V) :
    ∃ (ρ : ℝ) (F : Diffeomorph 𝓘(ℝ, Euc n) 𝓘(ℝ, Euc n) (Euc n) (Euc n) ∞),
      0 < ρ ∧ (∀ x, ‖x‖ ≤ ρ → F (p + A₀ x) = q + A₁ x) ∧
      ∃ K : Set (Euc n), IsCompact K ∧ K ⊆ V ∧ ∀ y ∉ K, F y = y ∧ F.symm y = y := by
  have hγcont : Continuous fun t : ℝ => p + t • (q - p) := by fun_prop
  have hKV : (fun t : ℝ => p + t • (q - p)) '' Icc (0 : ℝ) 1 ⊆ V := by
    rintro y ⟨t, ht, rfl⟩
    exact hseg t ht
  obtain ⟨δ, hδpos, hδsub⟩ :=
    (isCompact_Icc.image hγcont).exists_cthickening_subset_open hV hKV
  have htube : ∀ t ∈ Icc (0 : ℝ) 1, closedBall (p + t • (q - p)) δ ⊆ V := by
    intro t ht z hz
    exact hδsub (mem_cthickening_of_dist_le z _ δ _ ⟨t, ht, rfl⟩ (by simpa using hz))
  have htube₀ : closedBall p δ ⊆ V := by simpa using htube 0 ⟨le_refl 0, zero_le_one⟩
  obtain ⟨σ, Ψ, hσpos, hΨgerm, KΨ, hKΨc, hKΨV, hKΨfix⟩ :=
    exists_compact_diffeomorph_eqOn_closedBall_of_linear (A₀.symm.trans A₁) hA hδpos
  let Ψp : Diffeomorph 𝓘(ℝ, Euc n) 𝓘(ℝ, Euc n) (Euc n) (Euc n) ∞ :=
    (modelTranslateDiffeomorph (-p)).trans (Ψ.trans (modelTranslateDiffeomorph p))
  have hΨpapply : ∀ y, Ψp y = p + Ψ (y - p) := by
    intro y
    simp only [Ψp, Diffeomorph.coe_trans, Function.comp_apply, modelTranslateDiffeomorph_apply,
      sub_eq_add_neg]
    exact add_comm _ _
  have hΨpfix : ∀ y ∉ closedBall p δ, Ψp y = y ∧ Ψp.symm y = y := by
    intro y hy
    have hy' : y - p ∉ closedBall (0 : Euc n) δ := by
      simpa [mem_closedBall, dist_eq_norm, sub_eq_add_neg] using hy
    have hfix := hKΨfix (y - p) (fun h => hy' (hKΨV h))
    have hval : Ψp y = y := by rw [hΨpapply, hfix.1, add_sub_cancel]
    refine ⟨hval, ?_⟩
    have hs := Diffeomorph.symm_apply_apply Ψp y
    rw [hval] at hs
    exact hs
  set a : ℝ := ‖(A₀ : Euc n →L[ℝ] Euc n)‖ with ha
  set b : ℝ := ‖(A₁ : Euc n →L[ℝ] Euc n)‖ with hb
  set m : ℝ := min σ δ with hm
  set d : ℝ := 2 * (a + b + 1) with hd
  have hmpos : 0 < m := by rw [hm]; exact lt_min hσpos hδpos
  have hmleσ : m ≤ σ := by rw [hm]; exact min_le_left _ _
  have hmleδ : m ≤ δ := by rw [hm]; exact min_le_right _ _
  have hdpos : 0 < d := by rw [hd]; positivity
  have hna : 0 ≤ a := by rw [ha]; exact norm_nonneg _
  have hnb : 0 ≤ b := by rw [hb]; exact norm_nonneg _
  have h4a : a ≤ a + b + 1 := by linarith
  have h4b : b ≤ a + b + 1 := by linarith
  have had : a / d ≤ 1 / 2 := by
    rw [div_le_iff₀ hdpos, hd]
    linarith
  have hbd : b / d ≤ 1 / 2 := by
    rw [div_le_iff₀ hdpos, hd]
    linarith
  have hρpos : 0 < m / d := div_pos hmpos hdpos
  have hρa : m / d * a ≤ m := by
    calc m / d * a = m * (a / d) := by ring
      _ ≤ m * (1 / 2) := mul_le_mul_of_nonneg_left had hmpos.le
      _ ≤ m := by linarith [hmpos]
  have hρb : m / d * b < δ := by
    have h1 : m / d * b = m * (b / d) := by ring
    have h2 : m * (b / d) ≤ m * (1 / 2) := mul_le_mul_of_nonneg_left hbd hmpos.le
    rw [h1]
    linarith [h2, hmleδ, hδpos]
  obtain ⟨T, hT, KT, hKTc, hKTV, hKTfix⟩ :=
    exists_compact_diffeomorph_translate_of_tube (p := p) (q := q) (ρ := m / d * b)
      (δ := δ) (mul_nonneg (div_pos hmpos hdpos).le hnb) hρb htube
  refine ⟨m / d, Ψp.trans T, hρpos, ?_, closedBall p δ ∪ KT,
    (isCompact_closedBall _ _).union hKTc, union_subset htube₀ hKTV, ?_⟩
  · intro x hx
    have hxσ : ‖A₀ x‖ ≤ σ := by
      have h1 : ‖A₀ x‖ ≤ a * ‖x‖ :=
        ContinuousLinearMap.le_opNorm (A₀ : Euc n →L[ℝ] Euc n) x
      have h2 : a * ‖x‖ ≤ m := by
        calc a * ‖x‖ ≤ a * (m / d) := mul_le_mul_of_nonneg_left hx (norm_nonneg _)
          _ = m / d * a := by ring
          _ ≤ m := hρa
      exact h1.trans (h2.trans hmleσ)
    have hxA₁ : ‖A₁ x‖ ≤ m / d * b := by
      have h1 : ‖A₁ x‖ ≤ b * ‖x‖ :=
        ContinuousLinearMap.le_opNorm (A₁ : Euc n →L[ℝ] Euc n) x
      calc ‖A₁ x‖ ≤ b * ‖x‖ := h1
        _ ≤ b * (m / d) := mul_le_mul_of_nonneg_left hx (norm_nonneg _)
        _ = m / d * b := by ring
    have hΨpx : Ψp (p + A₀ x) = p + A₁ x := by
      rw [hΨpapply, add_sub_cancel_left, hΨgerm (A₀ x) hxσ]
      congr 1
      simp only [ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.symm_apply_apply]
    have hmem : p + A₁ x ∈ closedBall p (m / d * b) := by
      rw [mem_closedBall, dist_eq_norm]
      have hsub : p + A₁ x - p = A₁ x := by abel
      rw [hsub]
      exact hxA₁
    rw [Diffeomorph.coe_trans, Function.comp_apply, hΨpx, hT _ hmem]
    abel
  · intro y hy
    have hy₁ : y ∉ closedBall p δ := fun h => hy (Or.inl h)
    have hy₂ : y ∉ KT := fun h => hy (Or.inr h)
    have hfix : (Ψp.trans T) y = y := by
      rw [Diffeomorph.coe_trans, Function.comp_apply, (hΨpfix y hy₁).1, (hKTfix y hy₂).1]
    refine ⟨hfix, ?_⟩
    have hs := Diffeomorph.symm_apply_apply (Ψp.trans T) y
    rw [hfix] at hs
    exact hs

private theorem det_mul_clm (f g : Euc n →L[ℝ] Euc n) : (f * g).det = f.det * g.det := by
  rw [ContinuousLinearMap.mul_def]
  have hcoe : (((f.comp g : Euc n →L[ℝ] Euc n)) : Euc n →ₗ[ℝ] Euc n)
      = ((f : Euc n →ₗ[ℝ] Euc n)).comp (g : Euc n →ₗ[ℝ] Euc n) :=
      LinearMap.ext fun x => rfl
  change LinearMap.det ((f.comp g : Euc n →L[ℝ] Euc n) : Euc n →ₗ[ℝ] Euc n)
      = LinearMap.det (f : Euc n →ₗ[ℝ] Euc n) * LinearMap.det (g : Euc n →ₗ[ℝ] Euc n)
  rw [hcoe, LinearMap.det_comp]

private theorem mul_symm_self (A : Euc n ≃L[ℝ] Euc n) :
    (A.symm : Euc n →L[ℝ] Euc n) * (A : Euc n →L[ℝ] Euc n) = 1 := by
  rw [ContinuousLinearMap.ext_iff]
  intro x
  rw [mul_apply_eq_comp, ContinuousLinearEquiv.coe_coe]
  simp

private theorem det_one_clm : (1 : Euc n →L[ℝ] Euc n).det = 1 := by
  change LinearMap.det (1 : Euc n →ₗ[ℝ] Euc n) = 1
  exact map_one _

private theorem coe_symm_trans (A₀ A₁ : Euc n ≃L[ℝ] Euc n) :
    ((A₀.symm.trans A₁ : Euc n ≃L[ℝ] Euc n) : Euc n →L[ℝ] Euc n)
      = (A₁ : Euc n →L[ℝ] Euc n) * (A₀.symm : Euc n →L[ℝ] Euc n) := rfl

private theorem det_pos_trans_symm (A₀ A₁ : Euc n ≃L[ℝ] Euc n)
    (h : 0 < (A₀ : Euc n →L[ℝ] Euc n).det * (A₁ : Euc n →L[ℝ] Euc n).det) :
    0 < ((A₀.symm.trans A₁ : Euc n ≃L[ℝ] Euc n) : Euc n →L[ℝ] Euc n).det := by
  have hdet : (A₀.symm : Euc n →L[ℝ] Euc n).det * (A₀ : Euc n →L[ℝ] Euc n).det = 1 := by
    rw [← det_mul_clm, mul_symm_self, det_one_clm]
  rw [coe_symm_trans, det_mul_clm]
  have ha : (A₀ : Euc n →L[ℝ] Euc n).det ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h
    exact lt_irrefl 0 h
  have hinv : (A₀.symm : Euc n →L[ℝ] Euc n).det = ((A₀ : Euc n →L[ℝ] Euc n).det)⁻¹ :=
    eq_inv_of_mul_eq_one_left hdet
  rw [hinv]
  have h2 : 0 < ((A₀ : Euc n →L[ℝ] Euc n).det) ^ 2 := by
    rw [sq]
    exact mul_self_pos.mpr ha
  have hmain : (A₁ : Euc n →L[ℝ] Euc n).det * ((A₀ : Euc n →L[ℝ] Euc n).det)⁻¹
      = ((A₀ : Euc n →L[ℝ] Euc n).det * (A₁ : Euc n →L[ℝ] Euc n).det)
        / ((A₀ : Euc n →L[ℝ] Euc n).det) ^ 2 := by
    field_simp
  rw [hmain]
  exact div_pos h h2
theorem exists_compact_diffeomorph_eqOn_closedBall_of_partialDiffeomorphs_of_subset
    (φ₀ φ₁ : PartialDiffeomorph 𝓘(ℝ, Euc n) 𝓘(ℝ, Euc n) (Euc n) (Euc n) ∞)
    (h₀ : closedBall (0 : Euc n) 2 ⊆ φ₀.source)
    (h₁ : closedBall (0 : Euc n) 2 ⊆ φ₁.source)
    {V : Set (Euc n)} (hV : IsOpen V)
    (hV₀ : φ₀ '' closedBall (0 : Euc n) 2 ⊆ V)
    (hV₁ : φ₁ '' closedBall (0 : Euc n) 2 ⊆ V)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, (1 - t) • φ₀ 0 + t • φ₁ 0 ∈ V)
    (hori : 0 < (fderiv ℝ (φ₀ : Euc n → Euc n) 0).det *
      (fderiv ℝ (φ₁ : Euc n → Euc n) 0).det) :
    ∃ F : Diffeomorph 𝓘(ℝ, Euc n) 𝓘(ℝ, Euc n) (Euc n) (Euc n) ∞,
      (∀ x ∈ closedBall (0 : Euc n) 2, F (φ₀ x) = φ₁ x) ∧
      ∃ K : Set (Euc n), IsCompact K ∧ K ⊆ V ∧ ∀ y ∉ K, F y = y ∧ F.symm y = y := by
  obtain ⟨A₀, -, -, hA₀, -, -, -, -, -, -, -⟩ :=
    exists_diffeomorph_straightening_embedded_closedBall_scale_le (μ := 1) φ₀ (by norm_num)
      h₀ hV hV₀ (by norm_num)
  obtain ⟨A₁, -, -, hA₁, -, -, -, -, -, -, -⟩ :=
    exists_diffeomorph_straightening_embedded_closedBall_scale_le (μ := 1) φ₁ (by norm_num)
      h₁ hV hV₁ (by norm_num)
  have hori' : 0 < (A₀ : Euc n →L[ℝ] Euc n).det * (A₁ : Euc n →L[ℝ] Euc n).det := by
    rw [hA₀, hA₁]
    exact hori
  have hseg' : ∀ t ∈ Icc (0 : ℝ) 1, φ₀ 0 + t • (φ₁ 0 - φ₀ 0) ∈ V := by
    intro t ht
    have hpq : (1 - t) • φ₀ 0 + t • φ₁ 0 = φ₀ 0 + t • (φ₁ 0 - φ₀ 0) := by
      rw [sub_smul, one_smul, smul_sub]
      abel
    rw [← hpq]
    exact hseg t ht
  obtain ⟨ρ_L, F_L, hρL, hFLgerm, K_L, hKLc, hKLV, hKLfix⟩ :=
    exists_compact_diffeomorph_affine_of_subset (φ₀ 0) (φ₁ 0) A₀ A₁
      (det_pos_trans_symm A₀ A₁ hori') hV hseg'
  have hγcont : Continuous fun t : ℝ => (1 - t) • φ₀ 0 + t • φ₁ 0 := by fun_prop
  have hKV : (fun t : ℝ => (1 - t) • φ₀ 0 + t • φ₁ 0) '' Icc (0 : ℝ) 1 ⊆ V := by
    rintro y ⟨t, ht, rfl⟩
    exact hseg t ht
  obtain ⟨δ, hδpos, hδsub⟩ :=
    (isCompact_Icc.image hγcont).exists_cthickening_subset_open hV hKV
  have htube : ∀ t ∈ Icc (0 : ℝ) 1,
      closedBall ((1 - t) • φ₀ 0 + t • φ₁ 0) δ ⊆ V := by
    intro t ht z hz
    exact hδsub (mem_cthickening_of_dist_le z _ δ _ ⟨t, ht, rfl⟩ (by simpa using hz))
  have hball₁ : closedBall (φ₁ 0) δ ⊆ V := by
    simpa using htube 1 ⟨zero_le_one, le_refl 1⟩
  by_cases hb0 : ‖(A₁ : Euc n →L[ℝ] Euc n)‖ = 0
  · have hzero : (A₁ : Euc n →L[ℝ] Euc n) = 0 := norm_eq_zero.mp hb0
    have hz : ∀ z : Euc n, A₁ z = 0 := fun z => by
      have hc := congrArg (fun f : Euc n →L[ℝ] Euc n => f z) hzero
      simpa using hc
    have hsub : ∀ x y : Euc n, x = y := fun x y => A₁.injective (by rw [hz x, hz y])
    exact ⟨Diffeomorph.refl 𝓘(ℝ, Euc n) (Euc n) ∞, fun x _ => hsub (φ₀ x) (φ₁ x),
      ∅, isCompact_empty, empty_subset _, fun y _ => ⟨rfl, rfl⟩⟩
  have hbpos : 0 < ‖(A₁ : Euc n →L[ℝ] Euc n)‖ :=
    lt_of_le_of_ne (norm_nonneg _) (Ne.symm hb0)
  set b : ℝ := ‖(A₁ : Euc n →L[ℝ] Euc n)‖ with hb
  set μ : ℝ := min (ρ_L / 2) (δ / (2 * (b + 1))) with hμ
  have hμpos : 0 < μ := by
    rw [hμ]
    exact lt_min (by linarith) (div_pos hδpos (by positivity))
  have hμρ : 2 * μ ≤ ρ_L := by
    have h1 : μ ≤ ρ_L / 2 := by rw [hμ]; exact min_le_left _ _
    linarith
  have hμδ : 2 * μ * b < δ := by
    have h1 : μ ≤ δ / (2 * (b + 1)) := by rw [hμ]; exact min_le_right _ _
    have h2 : 2 * μ * b ≤ 2 * (δ / (2 * (b + 1))) * b := by nlinarith [hμpos, hδpos]
    have h3 : 2 * (δ / (2 * (b + 1))) * b = δ * (b / (b + 1)) := by field_simp
    have h4 : b / (b + 1) < 1 := by
      rw [div_lt_one (by linarith)]
      linarith
    nlinarith [h2, h4, hδpos]
  obtain ⟨A₀', ε₀, F₀, hA₀', hε₀, hε₀μ, hF₀, K₀, hK₀c,
    hK₀V, hK₀fix⟩ :=
    exists_diffeomorph_straightening_embedded_closedBall_scale_le (μ := μ) φ₀
      (by norm_num) h₀ hV hV₀ hμpos
  obtain ⟨A₁', ε₁, F₁, hA₁', hε₁, hε₁μ, hF₁, K₁, hK₁c,
    hK₁V, hK₁fix⟩ :=
    exists_diffeomorph_straightening_embedded_closedBall_scale_le (μ := μ) φ₁
      (by norm_num) h₁ hV hV₁ hμpos
  have hA₀eq : (A₀' : Euc n → Euc n) = (A₀ : Euc n → Euc n) := by
    rw [← ContinuousLinearEquiv.coe_coe, ← ContinuousLinearEquiv.coe_coe, hA₀', hA₀]
  have hA₁eq : (A₁' : Euc n → Euc n) = (A₁ : Euc n → Euc n) := by
    rw [← ContinuousLinearEquiv.coe_coe, ← ContinuousLinearEquiv.coe_coe, hA₁', hA₁]
  have hF₀' : ∀ x ∈ closedBall (0 : Euc n) 2,
      F₀ (φ₀ x) = ε₀ • A₀ x + φ₀ 0 := by
    intro x hx
    have h := hF₀ x hx
    rw [hA₀eq] at h
    exact h
  have hFLgerm' : ∀ y, ‖y‖ ≤ ρ_L → F_L (φ₀ 0 + A₀' y) = φ₁ 0 + A₁' y := by
    intro y hy
    rw [hA₀eq, hA₁eq]
    exact hFLgerm y hy
  set c : ℝ := ε₀ / ε₁ with hcdef
  have hcpos : 0 < c := by rw [hcdef]; exact div_pos hε₀ hε₁
  have hrpos : 0 < 2 * ε₁ * b := by
    have : 0 < ε₁ := hε₁
    nlinarith
  have hrδ : 2 * ε₁ * b < δ := by nlinarith [hε₁μ, hμδ, hε₁, hbpos]
  have hcrδ : c * (2 * ε₁ * b) < δ := by
    have hcmul : c * ε₁ = ε₀ := by rw [hcdef]; field_simp
    have h2 : c * (2 * ε₁ * b) = 2 * ε₀ * b := by rw [← hcmul]; ring
    rw [h2]
    nlinarith [hε₀μ, hμδ, hε₀, hbpos]
  obtain ⟨Θ, hΘexact, hΘfix⟩ :=
    DifferentialGeometry.Analysis.exists_compact_diffeomorph_scale_at (φ₁ 0)
      (r := 2 * ε₁ * b) (R := δ) (c := c) hrpos hcpos hrδ hcrδ
  have hF₁'' : ∀ x ∈ closedBall (0 : Euc n) 2,
      (F₁.trans Θ) (φ₁ x) = ε₀ • A₁ x + φ₁ 0 := by
    intro x hx
    have hx2 : ‖x‖ ≤ 2 := by simpa using hx
    have hz : ε₁ • A₁' x + φ₁ 0 ∈ closedBall (φ₁ 0) (2 * ε₁ * b) := by
      rw [mem_closedBall, dist_eq_norm]
      have hsub : ε₁ • A₁' x + φ₁ 0 - φ₁ 0 = ε₁ • A₁' x := by abel
      rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hε₁]
      have hop : ‖A₁' x‖ ≤ b * ‖x‖ := by
        rw [hA₁eq]
        exact ContinuousLinearMap.le_opNorm (A₁ : Euc n →L[ℝ] Euc n) x
      have : ε₁ * ‖A₁' x‖ ≤ ε₁ * (b * ‖x‖) :=
        mul_le_mul_of_nonneg_left hop hε₁.le
      nlinarith
    rw [Diffeomorph.coe_trans, Function.comp_apply, hF₁ x hx, hΘexact _ hz]
    have hsub : ε₁ • A₁' x + φ₁ 0 - φ₁ 0 = ε₁ • A₁' x := by abel
    rw [hsub, smul_smul]
    have hcmul : c * ε₁ = ε₀ := by rw [hcdef]; field_simp
    rw [hcmul, hA₁eq]
    exact add_comm _ _
  refine ⟨F₀.trans (F_L.trans (F₁.trans Θ).symm), ?_,
    K₀ ∪ K_L ∪ K₁ ∪ closedBall (φ₁ 0) δ,
    ((hK₀c.union hKLc).union hK₁c).union (isCompact_closedBall _ _), ?_, ?_⟩
  · intro x hx
    have hx2 : ‖x‖ ≤ 2 := by simpa using hx
    have hy : ‖ε₀ • x‖ ≤ ρ_L := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε₀]
      have h2 : ε₀ * ‖x‖ ≤ μ * 2 := mul_le_mul hε₀μ hx2 (norm_nonneg x) hμpos.le
      linarith [h2, hμρ]
    have h1 : F_L (ε₀ • A₀ x + φ₀ 0) = ε₀ • A₁ x + φ₁ 0 := by
      have hA₀s : A₀ (ε₀ • x) = ε₀ • A₀ x := map_smul _ _ _
      have hA₁s : A₁ (ε₀ • x) = ε₀ • A₁ x := map_smul _ _ _
      rw [← hA₀s, add_comm, hFLgerm (ε₀ • x) hy, hA₁s, add_comm]
    rw [Diffeomorph.coe_trans, Function.comp_apply, Diffeomorph.coe_trans, Function.comp_apply,
      hF₀' x hx, h1, ← hF₁'' x hx]
    exact (F₁.trans Θ).symm_apply_apply (φ₁ x)
  · intro y hy
    rcases hy with ((hy | hy) | hy) | hy
    · exact hK₀V hy
    · exact hKLV hy
    · exact hK₁V hy
    · exact hball₁ hy
  · intro y hy
    have hy₀ : y ∉ K₀ := fun h => hy (Or.inl (Or.inl (Or.inl h)))
    have hyL : y ∉ K_L := fun h => hy (Or.inl (Or.inl (Or.inr h)))
    have hy₁ : y ∉ K₁ := fun h => hy (Or.inl (Or.inr h))
    have hyδ : y ∉ closedBall (φ₁ 0) δ := fun h => hy (Or.inr h)
    have hF₁''fix : (F₁.trans Θ) y = y ∧ (F₁.trans Θ).symm y = y := by
      have hval : (F₁.trans Θ) y = y := by
        rw [Diffeomorph.coe_trans, Function.comp_apply, (hK₁fix y hy₁).1, (hΘfix y hyδ).1]
      refine ⟨hval, ?_⟩
      have hs := Diffeomorph.symm_apply_apply (F₁.trans Θ) y
      rw [hval] at hs
      exact hs
    have hfix : (F₀.trans (F_L.trans (F₁.trans Θ).symm)) y = y := by
      rw [Diffeomorph.coe_trans, Function.comp_apply, Diffeomorph.coe_trans, Function.comp_apply,
        (hK₀fix y hy₀).1, (hKLfix y hyL).1, hF₁''fix.2]
    refine ⟨hfix, ?_⟩
    have hs := Diffeomorph.symm_apply_apply (F₀.trans (F_L.trans (F₁.trans Θ).symm)) y
    rw [hfix] at hs
    exact hs

end DifferentialGeometry.Topology.Manifold
