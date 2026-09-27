import DifferentialGeometry.Topology.Manifold.AffineBallTransport
import DifferentialGeometry.Topology.Manifold.EmbeddedBallContraction
import DifferentialGeometry.Analysis.ODE.Flow.Planar.LinearGermRealization

set_option autoImplicit false
noncomputable section
open Set Metric Filter Topology
open scoped ContDiff Manifold Matrix

namespace DifferentialGeometry.Analysis

private abbrev Euc (n : ℕ) := EuclideanSpace ℝ (Fin n)

theorem exists_compact_isotopy_translate_on_closedBall
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (a b : E) {r R : ℝ} (hr : 0 ≤ r) (hR : r + ‖b - a‖ < R) :
    ∃ D : ℝ → Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞,
      ContDiff ℝ ∞ (fun q : ℝ × E => D q.1 q.2) ∧
      ContDiff ℝ ∞ (fun q : ℝ × E => (D q.1).symm q.2) ∧
      D 0 = Diffeomorph.refl 𝓘(ℝ, E) E ∞ ∧
      (∀ x ∈ closedBall a r, D 1 x = x + (b - a)) ∧
      (∀ t x, x ∉ closedBall a R → D t x = x ∧ (D t).symm x = x) := by
  obtain ⟨rIn, hrIn₁, hrIn₂⟩ := exists_between hR
  have hrIn_pos : 0 < rIn := lt_of_le_of_lt (add_nonneg hr (norm_nonneg _)) hrIn₁
  let β : ContDiffBump a := ⟨rIn, R, hrIn_pos, hrIn₂⟩
  let v : E → E := fun x => β x • (b - a)
  have hv : ContDiff ℝ ∞ v := β.contDiff.smul contDiff_const
  have hvc : HasCompactSupport v := β.hasCompactSupport.smul_right
  obtain ⟨D, hD, hderiv, hzero, _hadd, hinv⟩ :=
    exists_smoothFlow_of_eq_const_off_compact hv 0 (by simpa using hvc)
  have hDi : ContDiff ℝ ∞ (fun q : ℝ × E => (D q.1).symm q.2) := by
    simp_rw [hinv]
    exact hD.comp (contDiff_fst.neg.prodMk contDiff_snd)
  have hv_on : ∀ x ∈ closedBall a rIn, v x = b - a := fun x hx =>
    by simp only [v, β.one_of_mem_closedBall hx, one_smul]
  have hsupport : tsupport v ⊆ closedBall a R := by
    have h1 : tsupport v ⊆ tsupport (β : E → ℝ) :=
      tsupport_smul_subset_left (β : E → ℝ) (fun _ : E => b - a)
    rw [β.tsupport_eq] at h1
    exact h1
  have hpoint : ∀ (x : E) (t : ℝ), x ∉ closedBall a R → D t x = x := by
    intro x t hx
    by_contra hne
    have hs := tsupport_integralCurveFamily_sub_subset (v := v) (hv.of_le (by simp))
      (Γ := fun y s => D s y) (fun y => by rw [hzero]; rfl) hderiv t
    exact hx (hsupport (hs (subset_closure (Function.mem_support.mpr (sub_ne_zero.mpr hne)))))
  have hclosed : ∀ x ∈ closedBall a r, D 1 x = x + (b - a) := by
    intro x hx
    have hxr : ‖x - a‖ ≤ r := by simpa [dist_eq_norm] using hx
    have hmem (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : x + t • (b - a) ∈ closedBall a rIn := by
      rw [mem_closedBall, dist_eq_norm]
      have hsplit : x + t • (b - a) - a = (x - a) + t • (b - a) := by abel
      rw [hsplit]
      have h1 : ‖(x - a) + t • (b - a)‖ ≤ ‖x - a‖ + ‖t • (b - a)‖ := norm_add_le _ _
      have h2 : ‖t • (b - a)‖ = t * ‖b - a‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      have h3 : t * ‖b - a‖ ≤ ‖b - a‖ :=
        mul_le_of_le_one_left (norm_nonneg _) ht.2
      linarith
    have hγ : IsIntegralCurveOn (fun t : ℝ => x + t • (b - a)) (fun _ : ℝ => v) (Icc 0 1) := by
      intro t ht
      have hder : HasDerivAt (fun s : ℝ => x + s • (b - a)) (v (x + t • (b - a))) t := by
        rw [hv_on _ (hmem t ht)]
        simpa using (((hasDerivAt_id t).smul_const (b - a)).const_add x)
      exact hder.hasDerivWithinAt
    have hDcur : IsIntegralCurveOn (fun t : ℝ => D t x) (fun _ : ℝ => v) (Icc 0 1) :=
      fun t ht => (hderiv x t).hasDerivWithinAt
    have hinit : (fun t : ℝ => D t x) 0 = (fun t : ℝ => x + t • (b - a)) 0 := by
      simp only [hzero, Diffeomorph.coe_refl, id_eq, zero_smul, add_zero]
    have he := DifferentialGeometry.Analysis.ODE.Flow.orbit_unique_Icc hv
      (a := 0) (b := 1) hDcur hγ hinit
    have h1 := he ⟨zero_le_one, le_refl (1 : ℝ)⟩
    simpa using h1
  refine ⟨D, hD, hDi, hzero, hclosed, ?_⟩
  intro t x hx
  refine ⟨hpoint x t hx, ?_⟩
  rw [hinv]
  exact hpoint x (-t) hx

private theorem translate_isotopy_aux (N : ℕ) {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    ∀ (p q : E) (ρ δ : ℝ) (V : Set E), 0 ≤ ρ → ρ < δ →
      ‖q - p‖ < 2 ^ N * (δ - ρ) →
      (∀ t ∈ Icc (0 : ℝ) 1, closedBall (p + t • (q - p)) δ ⊆ V) →
      ∃ T : ℝ → Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞,
        ContDiff ℝ ∞ (fun s : ℝ × E => T s.1 s.2) ∧
        ContDiff ℝ ∞ (fun s : ℝ × E => (T s.1).symm s.2) ∧
        T 0 = Diffeomorph.refl 𝓘(ℝ, E) E ∞ ∧
        (∀ y ∈ closedBall p ρ, T 1 y = y + (q - p)) ∧
        ∃ K : Set E, IsCompact K ∧ K ⊆ V ∧
          ∀ s y, y ∉ K → T s y = y ∧ (T s).symm y = y := by
  induction N with
  | zero =>
      intro p q ρ δ V hρ hρδ hlen htube
      have hR : ρ + ‖q - p‖ < δ := by
        rw [pow_zero, one_mul] at hlen
        linarith
      obtain ⟨D, hD, hDi, hD0, hD1, hDfix⟩ :=
        exists_compact_isotopy_translate_on_closedBall p q hρ hR
      refine ⟨D, hD, hDi, hD0, hD1, closedBall p δ, isCompact_closedBall _ _, ?_, ?_⟩
      · simpa using htube 0 ⟨le_refl 0, zero_le_one⟩
      · exact hDfix
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
      obtain ⟨T₁, hT₁, hT₁i, hT₁0, hT₁1, K₁, hK₁c, hK₁V, hK₁fix⟩ :=
        ih p m ρ δ V hρ hρδ (by rw [hm_p_norm]; exact hhalf) htube₁
      obtain ⟨T₂, hT₂, hT₂i, hT₂0, hT₂1, K₂, hK₂c, hK₂V, hK₂fix⟩ :=
        ih m q ρ δ V hρ hρδ (by rw [hq_m_norm]; exact hhalf) htube₂
      refine ⟨fun t : ℝ => (T₁ t).trans (T₂ t), ?_, ?_, ?_, ?_,
        K₁ ∪ K₂, hK₁c.union hK₂c, union_subset hK₁V hK₂V, ?_⟩
      · have hpair : ContDiff ℝ ∞ (fun s : ℝ × E => (s.1, T₁ s.1 s.2)) :=
          contDiff_fst.prodMk (hT₁.comp (contDiff_fst.prodMk contDiff_snd))
        have h := hT₂.comp hpair
        have he : (fun s : ℝ × E => ((T₁ s.1).trans (T₂ s.1)) s.2) =
            fun s : ℝ × E => T₂ s.1 (T₁ s.1 s.2) := rfl
        rw [he]
        simpa only [Function.comp_def] using h
      · have hpair : ContDiff ℝ ∞ (fun s : ℝ × E => (s.1, (T₂ s.1).symm s.2)) :=
          contDiff_fst.prodMk (hT₂i.comp (contDiff_fst.prodMk contDiff_snd))
        have h := hT₁i.comp hpair
        have he : (fun s : ℝ × E => ((T₁ s.1).trans (T₂ s.1)).symm s.2) =
            fun s : ℝ × E => (T₁ s.1).symm ((T₂ s.1).symm s.2) := by
          funext s
          rw [Diffeomorph.symm_trans']
          rfl
        rw [he]
        simpa only [Function.comp_def] using h
      · apply Diffeomorph.ext
        intro y
        change T₂ 0 (T₁ 0 y) = y
        rw [hT₁0, hT₂0]
        rfl
      · intro y hy
        have hy₁ : y + (m - p) ∈ closedBall m ρ := by
          rw [mem_closedBall, dist_eq_norm]
          have hsub : y + (m - p) - m = y - p := by abel
          rw [hsub, ← dist_eq_norm]
          exact hy
        change ((T₁ 1).trans (T₂ 1)) y = y + (q - p)
        rw [Diffeomorph.coe_trans, Function.comp_apply, hT₁1 y hy, hT₂1 _ hy₁]
        abel
      · intro s y hy
        have hy₁ : y ∉ K₁ := fun h => hy (Or.inl h)
        have hy₂ : y ∉ K₂ := fun h => hy (Or.inr h)
        have hfix : ((T₁ s).trans (T₂ s)) y = y := by
          rw [Diffeomorph.coe_trans, Function.comp_apply, (hK₁fix s y hy₁).1,
            (hK₂fix s y hy₂).1]
        refine ⟨hfix, ?_⟩
        have hs := Diffeomorph.symm_apply_apply ((T₁ s).trans (T₂ s)) y
        rw [hfix] at hs
        exact hs

theorem exists_compact_isotopy_translate_of_tube {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {p q : E} {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hρδ : ρ < δ) {V : Set E}
    (htube : ∀ t ∈ Icc (0 : ℝ) 1, closedBall (p + t • (q - p)) δ ⊆ V) :
    ∃ T : ℝ → Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞,
      ContDiff ℝ ∞ (fun s : ℝ × E => T s.1 s.2) ∧
      ContDiff ℝ ∞ (fun s : ℝ × E => (T s.1).symm s.2) ∧
      T 0 = Diffeomorph.refl 𝓘(ℝ, E) E ∞ ∧
      (∀ y ∈ closedBall p ρ, T 1 y = y + (q - p)) ∧
      ∃ K : Set E, IsCompact K ∧ K ⊆ V ∧
        ∀ s y, y ∉ K → T s y = y ∧ (T s).symm y = y := by
  have hpos : 0 < δ - ρ := sub_pos.mpr hρδ
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (‖q - p‖ / (δ - ρ))
    (by norm_num : (1 : ℝ) < 2)
  refine translate_isotopy_aux N p q ρ δ V hρ hρδ ?_ htube
  rw [div_lt_iff₀ hpos] at hN
  linarith [hN]

end DifferentialGeometry.Analysis

namespace DifferentialGeometry.Topology.Manifold

private abbrev Euc (n : ℕ) := EuclideanSpace ℝ (Fin n)

private def modelScaleDiffeomorph (n : ℕ) (s : ℝ) (hs : s ≠ 0) :
    Diffeomorph 𝓘(ℝ, Euc n) 𝓘(ℝ, Euc n) (Euc n) (Euc n) ∞ where
  toEquiv :=
    { toFun := fun x => s • x
      invFun := fun x => s⁻¹ • x
      left_inv := fun x => by simp only [smul_smul, inv_mul_cancel₀ hs, one_smul]
      right_inv := fun x => by simp only [smul_smul, mul_inv_cancel₀ hs, one_smul] }
  contMDiff_toFun := (contDiff_const_smul s).contMDiff
  contMDiff_invFun := (contDiff_const_smul s⁻¹).contMDiff

private theorem modelScaleDiffeomorph_apply (n : ℕ) (s : ℝ) (hs : s ≠ 0) (x : Euc n) :
    modelScaleDiffeomorph n s hs x = s • x := rfl

theorem exists_compact_isotopy_eqOn_closedBall_of_matEnd {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : 0 < M.det) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (σ : ℝ) (Ψ : ℝ → Diffeomorph 𝓘(ℝ, Euc n) 𝓘(ℝ, Euc n) (Euc n) (Euc n) ∞),
      0 < σ ∧
      ContDiff ℝ ∞ (fun q : ℝ × Euc n => Ψ q.1 q.2) ∧
      ContDiff ℝ ∞ (fun q : ℝ × Euc n => (Ψ q.1).symm q.2) ∧
      Ψ 0 = Diffeomorph.refl 𝓘(ℝ, Euc n) (Euc n) ∞ ∧
      (∀ z, ‖z‖ ≤ σ → Ψ 1 z = DifferentialGeometry.Analysis.matEnd M z) ∧
      (∀ t y, y ∉ closedBall (0 : Euc n) δ → Ψ t y = y ∧ (Ψ t).symm y = y) := by
  obtain ⟨-, -, D, hDc, hDic, hD0, hDg, hDfix⟩ :=
    DifferentialGeometry.Analysis.realizesGerm_matEnd_of_det_pos M hM
  obtain ⟨ρ₁, hρ₁pos, hρ₁⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hDg
  have hρ₁' : ∀ z : Euc n, ‖z‖ ≤ ρ₁ → D 1 z = DifferentialGeometry.Analysis.matEnd M z :=
    fun z hz => hρ₁ (mem_closedBall_zero_iff.mpr hz)
  set s : ℝ := δ / 2 with hsdef
  have hspos : 0 < s := by rw [hsdef]; linarith
  have hsne : s ≠ 0 := ne_of_gt hspos
  have h2s : 2 * s = δ := by rw [hsdef]; ring
  let Ψ : ℝ → Diffeomorph 𝓘(ℝ, Euc n) 𝓘(ℝ, Euc n) (Euc n) (Euc n) ∞ := fun t =>
    (modelScaleDiffeomorph n s⁻¹ (inv_ne_zero hsne)).trans
      ((D t).trans (modelScaleDiffeomorph n s hsne))
  have hΨapply : ∀ t y, Ψ t y = s • D t (s⁻¹ • y) := by
    intro t y
    simp only [Ψ, Diffeomorph.coe_trans, Function.comp_apply, modelScaleDiffeomorph_apply]
  have hΨsymm : ∀ t y, (Ψ t).symm y = s • (D t).symm (s⁻¹ • y) := by
    intro t y
    have h : Ψ t (s • (D t).symm (s⁻¹ • y)) = y := by
      rw [hΨapply]
      have h1 : s⁻¹ • (s • (D t).symm (s⁻¹ • y)) = (D t).symm (s⁻¹ • y) := by
        rw [inv_smul_smul₀ hsne]
      rw [h1, Diffeomorph.apply_symm_apply, smul_inv_smul₀ hsne]
    have hs2 := Diffeomorph.symm_apply_apply (Ψ t) (s • (D t).symm (s⁻¹ • y))
    rw [h] at hs2
    exact hs2
  have hΨfix : ∀ t y, y ∉ closedBall (0 : Euc n) δ → Ψ t y = y ∧ (Ψ t).symm y = y := by
    intro t y hy
    have hy2 : y ∉ closedBall (0 : Euc n) (2 * s) := by rw [h2s]; exact hy
    have h2 : 2 * s < ‖y‖ := not_le.mp (by simpa [mem_closedBall_zero_iff] using hy2)
    have hnorm : 2 < ‖s⁻¹ • y‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hspos)]
      calc (2 : ℝ) = s⁻¹ * (2 * s) := by field_simp
        _ < s⁻¹ * ‖y‖ := mul_lt_mul_of_pos_left h2 (inv_pos.mpr hspos)
    have hfix := (hDfix t (s⁻¹ • y) (by simpa [mem_closedBall_zero_iff] using hnorm)).1
    have hval : Ψ t y = y := by
      rw [hΨapply, hfix, smul_inv_smul₀ hsne]
    refine ⟨hval, ?_⟩
    have hs2 := Diffeomorph.symm_apply_apply (Ψ t) y
    rw [hval] at hs2
    exact hs2
  have hΨc : ContDiff ℝ ∞ (fun q : ℝ × Euc n => Ψ q.1 q.2) := by
    have hbody : ContDiff ℝ ∞ (fun q : ℝ × Euc n => s • D q.1 (s⁻¹ • q.2)) := by
      have hmap : ContDiff ℝ ∞ (fun q : ℝ × Euc n => (q.1, s⁻¹ • q.2)) := by fun_prop
      have h1 : ContDiff ℝ ∞ (fun q : ℝ × Euc n => D q.1 (s⁻¹ • q.2)) := by
        have h := hDc.comp hmap
        simpa only [Function.comp_def] using h
      exact h1.const_smul s
    have he : (fun q : ℝ × Euc n => Ψ q.1 q.2)
        = fun q : ℝ × Euc n => s • D q.1 (s⁻¹ • q.2) := by
      funext q
      exact hΨapply q.1 q.2
    rw [he]
    exact hbody
  have hΨi : ContDiff ℝ ∞ (fun q : ℝ × Euc n => (Ψ q.1).symm q.2) := by
    have hbody : ContDiff ℝ ∞ (fun q : ℝ × Euc n => s • (D q.1).symm (s⁻¹ • q.2)) := by
      have hmap : ContDiff ℝ ∞ (fun q : ℝ × Euc n => (q.1, s⁻¹ • q.2)) := by fun_prop
      have h1 : ContDiff ℝ ∞ (fun q : ℝ × Euc n => (D q.1).symm (s⁻¹ • q.2)) := by
        have h := hDic.comp hmap
        simpa only [Function.comp_def] using h
      exact h1.const_smul s
    have he : (fun q : ℝ × Euc n => (Ψ q.1).symm q.2)
        = fun q : ℝ × Euc n => s • (D q.1).symm (s⁻¹ • q.2) := by
      funext q
      exact hΨsymm q.1 q.2
    rw [he]
    exact hbody
  have hΨ0 : Ψ 0 = Diffeomorph.refl 𝓘(ℝ, Euc n) (Euc n) ∞ := by
    apply Diffeomorph.ext
    intro y
    rw [hΨapply]
    have h1 : D 0 (s⁻¹ • y) = s⁻¹ • y := by rw [hD0]; rfl
    rw [h1, smul_inv_smul₀ hsne]
    simp only [Diffeomorph.coe_refl, id_eq]
  have hΨgerm : ∀ z : Euc n, ‖z‖ ≤ s * ρ₁ → Ψ 1 z =
      DifferentialGeometry.Analysis.matEnd M z := by
    intro z hz
    have hnorm : ‖s⁻¹ • z‖ ≤ ρ₁ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hspos), inv_mul_le_iff₀ hspos]
      linarith [hz]
    rw [hΨapply, hρ₁' _ hnorm, map_smul, smul_inv_smul₀ hsne]
  exact ⟨s * ρ₁, Ψ, mul_pos hspos hρ₁pos, hΨc, hΨi, hΨ0, hΨgerm, hΨfix⟩

theorem exists_realizesGerm_of_det_pos_closedBall {n : ℕ}
    {f : Euc n → Euc n} {U : Set (Euc n)} (hU : IsOpen U) (h0U : (0 : Euc n) ∈ U)
    (hf : ContDiffOn ℝ ∞ f U) (hf0 : f 0 = 0) (hdet : 0 < (fderiv ℝ f 0).det)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ K : Set (Euc n), IsCompact K ∧ K ⊆ closedBall (0 : Euc n) ρ ∧
      DifferentialGeometry.Analysis.RealizesGerm f K := by
  let A : Euc n →L[ℝ] Euc n := fderiv ℝ f 0
  let M : Matrix (Fin n) (Fin n) ℝ :=
    (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).symm A
  have hA : A = fderiv ℝ f 0 := rfl
  have hMA : DifferentialGeometry.Analysis.matEnd M = A := by
    rw [DifferentialGeometry.Analysis.matEnd_eq_toEuclideanCLM]
    exact StarAlgEquiv.apply_symm_apply _ _
  have hMdet : 0 < M.det := by
    have h : M.det = A.det := DifferentialGeometry.Analysis.det_toEuclideanCLM_symm A
    rw [h, hA]
    exact hdet
  have hunit : IsUnit M.det := isUnit_iff_ne_zero.mpr (ne_of_gt hMdet)
  have hMinv' : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hunit
  have hMinv'' : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hunit
  have hmul : DifferentialGeometry.Analysis.matEnd M *
      DifferentialGeometry.Analysis.matEnd M⁻¹ = 1 := by
    rw [← DifferentialGeometry.Analysis.matEnd_mul, hMinv',
      DifferentialGeometry.Analysis.matEnd_one]
  have hfix : ∀ x, DifferentialGeometry.Analysis.matEnd M
      (DifferentialGeometry.Analysis.matEnd M⁻¹ (f x)) = f x := by
    intro x
    rw [← mul_apply_eq_comp, hmul, one_apply_eq_self]
  let g : Euc n → Euc n := fun x => DifferentialGeometry.Analysis.matEnd M⁻¹ (f x)
  have hg : ContDiffOn ℝ ∞ g U :=
    (DifferentialGeometry.Analysis.matEnd M⁻¹).contDiff.comp_contDiffOn hf
  have hg0 : g 0 = 0 := by simp only [g, hf0, map_zero]
  have hgderiv : HasFDerivAt g (1 : Euc n →L[ℝ] Euc n) 0 := by
    have hfat : HasFDerivAt f A 0 := by
      have hd : DifferentiableAt ℝ f 0 :=
        (hf.contDiffAt (hU.mem_nhds h0U)).differentiableAt (by simp)
      have hh := hd.hasFDerivAt
      rw [← hA] at hh
      exact hh
    have hcomp : HasFDerivAt g ((DifferentialGeometry.Analysis.matEnd M⁻¹).comp A) 0 :=
      (ContinuousLinearMap.hasFDerivAt (DifferentialGeometry.Analysis.matEnd M⁻¹)).comp 0 hfat
    have hderiv : ((DifferentialGeometry.Analysis.matEnd M⁻¹).comp A) = 1 := by
      refine ContinuousLinearMap.ext fun x => ?_
      rw [ContinuousLinearMap.comp_apply, ← hMA, ← mul_apply_eq_comp,
        ← DifferentialGeometry.Analysis.matEnd_mul, hMinv'',
        DifferentialGeometry.Analysis.matEnd_one, one_apply_eq_self]
    rw [← hderiv]
    exact hcomp
  have hU' : IsOpen (U ∩ Metric.ball (0 : Euc n) ρ) := hU.inter Metric.isOpen_ball
  have h0U' : (0 : Euc n) ∈ U ∩ Metric.ball (0 : Euc n) ρ := ⟨h0U, mem_ball_self hρ⟩
  have hgU' : ContDiffOn ℝ ∞ g (U ∩ Metric.ball (0 : Euc n) ρ) := hg.mono inter_subset_left
  obtain ⟨Kg, hKgU', hKg⟩ :=
    DifferentialGeometry.Analysis.exists_realizesGerm_of_identity_tangent hU' h0U'
      hgU' hg0 hgderiv
  obtain ⟨σ, Ψ, hσpos, hΨc, hΨi, hΨ0, hΨgerm, hΨfix⟩ :=
    exists_compact_isotopy_eqOn_closedBall_of_matEnd M hMdet (by linarith : 0 < ρ / 2)
  have hev : (Ψ 1 : Euc n → Euc n) =ᶠ[𝓝 0] DifferentialGeometry.Analysis.matEnd M :=
    Filter.mem_of_superset (Metric.closedBall_mem_nhds (0 : Euc n) hσpos)
      (fun z hz => hΨgerm z (by simpa [mem_closedBall_zero_iff] using hz))
  have hMreal : DifferentialGeometry.Analysis.RealizesGerm
      (fun x => DifferentialGeometry.Analysis.matEnd M x)
      (Metric.closedBall (0 : Euc n) (ρ / 2)) :=
    ⟨by simp, isCompact_closedBall _ _, Ψ, hΨc, hΨi, hΨ0, hev, hΨfix⟩
  have hcomp : DifferentialGeometry.Analysis.RealizesGerm
      (fun x => DifferentialGeometry.Analysis.matEnd M (g x))
      (Metric.closedBall (0 : Euc n) (ρ / 2) ∪ Kg) := hMreal.comp hKg
  have hfun : (fun x => DifferentialGeometry.Analysis.matEnd M (g x)) = f := by
    funext x
    exact hfix x
  refine ⟨Metric.closedBall (0 : Euc n) (ρ / 2) ∪ Kg,
    (isCompact_closedBall _ _).union hKg.2.1, ?_, ?_⟩
  · refine union_subset (Metric.closedBall_subset_closedBall (by linarith)) ?_
    intro x hx
    exact Metric.ball_subset_closedBall (hKgU' hx).2
  · exact DifferentialGeometry.Analysis.RealizesGerm.congr hfun hcomp

private def modelTranslateDiffeomorph (n : ℕ) (t : Euc n) :
    Diffeomorph 𝓘(ℝ, Euc n) 𝓘(ℝ, Euc n) (Euc n) (Euc n) ∞ where
  toEquiv :=
    { toFun := fun x => x + t
      invFun := fun x => x - t
      left_inv := fun x => by simp
      right_inv := fun x => by simp }
  contMDiff_toFun := (contDiff_id.add contDiff_const).contMDiff
  contMDiff_invFun := (contDiff_id.sub contDiff_const).contMDiff

private theorem modelTranslateDiffeomorph_apply (n : ℕ) (t x : Euc n) :
    modelTranslateDiffeomorph n t x = x + t := rfl

private theorem det_comp_clm {n : ℕ} (f g : Euc n →L[ℝ] Euc n) :
    (f.comp g).det = f.det * g.det := by
  have hcoe : (((f.comp g : Euc n →L[ℝ] Euc n)) : Euc n →ₗ[ℝ] Euc n)
      = ((f : Euc n →ₗ[ℝ] Euc n)).comp (g : Euc n →ₗ[ℝ] Euc n) :=
    LinearMap.ext fun x => rfl
  change LinearMap.det ((f.comp g : Euc n →L[ℝ] Euc n) : Euc n →ₗ[ℝ] Euc n)
      = LinearMap.det (f : Euc n →ₗ[ℝ] Euc n) * LinearMap.det (g : Euc n →ₗ[ℝ] Euc n)
  rw [hcoe, LinearMap.det_comp]

private theorem det_one_clm {n : ℕ} : (1 : Euc n →L[ℝ] Euc n).det = 1 := by
  change LinearMap.det (1 : Euc n →ₗ[ℝ] Euc n) = 1
  exact map_one _

theorem exists_isotopy_eqOn_closedBall_of_partialDiffeomorphs_of_subset {n : ℕ}
    (φ₀ φ₁ : PartialDiffeomorph 𝓘(ℝ, Euc n) 𝓘(ℝ, Euc n) (Euc n) (Euc n) ∞)
    (h₀ : closedBall (0 : Euc n) 2 ⊆ φ₀.source)
    (h₁ : closedBall (0 : Euc n) 2 ⊆ φ₁.source)
    {V : Set (Euc n)} (hV : IsOpen V)
    (hV₀ : φ₀ '' closedBall (0 : Euc n) 2 ⊆ V)
    (hV₁ : φ₁ '' closedBall (0 : Euc n) 2 ⊆ V)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, (1 - t) • φ₀ 0 + t • φ₁ 0 ∈ V)
    (hori : 0 < (fderiv ℝ (φ₀ : Euc n → Euc n) 0).det *
      (fderiv ℝ (φ₁ : Euc n → Euc n) 0).det) :
    ∃ J : ℝ → Diffeomorph 𝓘(ℝ, Euc n) 𝓘(ℝ, Euc n) (Euc n) (Euc n) ∞,
      ContDiff ℝ ∞ (fun q : ℝ × Euc n => J q.1 q.2) ∧
      ContDiff ℝ ∞ (fun q : ℝ × Euc n => (J q.1).symm q.2) ∧
      J 0 = Diffeomorph.refl 𝓘(ℝ, Euc n) (Euc n) ∞ ∧
      (∀ x ∈ closedBall (0 : Euc n) 2, J 1 (φ₀ x) = φ₁ x) ∧
      ∃ K : Set (Euc n), IsCompact K ∧ K ⊆ V ∧
        ∀ t y, y ∉ K → J t y = y ∧ (J t).symm y = y := by
  let c : Euc n := φ₀ 0
  let d : Euc n := φ₁ 0
  obtain ⟨C₀, hC₀c, hC₀i, hC₀0, hC₀rad, K₀, hK₀c, hK₀V, -, hK₀fix⟩ :=
    exists_diffeomorphs_contracting_embedded_closedBall φ₀ (r := 2) (by norm_num) h₀ hV hV₀
  obtain ⟨C₁, hC₁c, hC₁i, hC₁0, hC₁rad, K₁, hK₁c, hK₁V, -, hK₁fix⟩ :=
    exists_diffeomorphs_contracting_embedded_closedBall φ₁ (r := 2) (by norm_num) h₁ hV hV₁
  have hC₀cd : ContDiff ℝ ∞ (fun q : ℝ × Euc n => C₀ q.1 q.2) := by
    have h : ContMDiff (𝓘(ℝ, ℝ × Euc n)) (𝓘(ℝ, Euc n)) ∞
        (fun q : ℝ × Euc n => C₀ q.1 q.2) := by
      rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
      exact hC₀c
    exact contMDiff_iff_contDiff.mp h
  have hC₀id : ContDiff ℝ ∞ (fun q : ℝ × Euc n => (C₀ q.1).symm q.2) := by
    have h : ContMDiff (𝓘(ℝ, ℝ × Euc n)) (𝓘(ℝ, Euc n)) ∞
        (fun q : ℝ × Euc n => (C₀ q.1).symm q.2) := by
      rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
      exact hC₀i
    exact contMDiff_iff_contDiff.mp h
  have hC₁cd : ContDiff ℝ ∞ (fun q : ℝ × Euc n => C₁ q.1 q.2) := by
    have h : ContMDiff (𝓘(ℝ, ℝ × Euc n)) (𝓘(ℝ, Euc n)) ∞
        (fun q : ℝ × Euc n => C₁ q.1 q.2) := by
      rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
      exact hC₁c
    exact contMDiff_iff_contDiff.mp h
  have hC₁id : ContDiff ℝ ∞ (fun q : ℝ × Euc n => (C₁ q.1).symm q.2) := by
    have h : ContMDiff (𝓘(ℝ, ℝ × Euc n)) (𝓘(ℝ, Euc n)) ∞
        (fun q : ℝ × Euc n => (C₁ q.1).symm q.2) := by
      rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
      exact hC₁i
    exact contMDiff_iff_contDiff.mp h
  have hsegV : (fun t : ℝ => (1 - t) • φ₀ 0 + t • φ₁ 0) '' Icc (0 : ℝ) 1 ⊆ V := by
    rintro y ⟨t, ht, rfl⟩
    exact hseg t ht
  have hγcont : Continuous fun t : ℝ => (1 - t) • φ₀ 0 + t • φ₁ 0 := by fun_prop
  obtain ⟨δ, hδpos, hδsub⟩ := (isCompact_Icc.image hγcont).exists_cthickening_subset_open hV hsegV
  have htube : ∀ t ∈ Icc (0 : ℝ) 1, closedBall (c + t • (d - c)) δ ⊆ V := by
    intro t ht
    have hpt : (1 - t) • φ₀ 0 + t • φ₁ 0 = c + t • (d - c) := by
      rw [sub_smul, one_smul, smul_sub]
      abel
    rw [← hpt]
    intro z hz
    exact hδsub (mem_cthickening_of_dist_le z _ δ _ ⟨t, ht, rfl⟩ (by simpa using hz))
  obtain ⟨T, hTc, hTi, hT0, hT1, KT, hKTc, hKTV, hKTfix⟩ :=
    DifferentialGeometry.Analysis.exists_compact_isotopy_translate_of_tube
      (p := c) (q := d) (ρ := δ / 2)
      (by linarith : (0 : ℝ) ≤ δ / 2) (by linarith : δ / 2 < δ) htube
  have h0src : (0 : Euc n) ∈ φ₀.source := h₀ (mem_closedBall_self (by norm_num))
  have h1src : (0 : Euc n) ∈ φ₁.source := h₁ (mem_closedBall_self (by norm_num))
  have hsymmc : (φ₀.symm : Euc n → Euc n) c = 0 := φ₀.left_inv h0src
  have hφ₁zero : (φ₁ : Euc n → Euc n) 0 = d := rfl
  let χ : Euc n → Euc n := fun z => (T 1).symm (φ₁ ((φ₀.symm : Euc n → Euc n) z))
  let χtilde : Euc n → Euc n := fun y => χ (c + y) - c
  have hcsrc : c ∈ (φ₀.symm).source := φ₀.map_source h0src
  have hcsym : (φ₀.symm : Euc n → Euc n) c ∈ φ₁.source := by
    rw [hsymmc]; exact h1src
  let S : Set (Euc n) := (φ₀.symm).source ∩ ((φ₀.symm : Euc n → Euc n) ⁻¹' φ₁.source)
  have hSopen : IsOpen S := (φ₀.symm).toOpenPartialHomeomorph.isOpen_inter_preimage φ₁.open_source
  have hcS : c ∈ S := ⟨hcsrc, hcsym⟩
  let U' : Set (Euc n) := (fun y : Euc n => c + y) ⁻¹' S
  have hU'open : IsOpen U' := hSopen.preimage (by fun_prop : Continuous fun y : Euc n => c + y)
  have h0U' : (0 : Euc n) ∈ U' := by
    change c + 0 ∈ S
    simpa using hcS
  have hφ₀diff : DifferentiableAt ℝ (φ₀ : Euc n → Euc n) 0 :=
    (φ₀.contMDiffOn_toFun.contDiffOn.contDiffAt (φ₀.open_source.mem_nhds h0src)).differentiableAt
      (by simp)
  have hφ₁diff : DifferentiableAt ℝ (φ₁ : Euc n → Euc n) 0 :=
    (φ₁.contMDiffOn_toFun.contDiffOn.contDiffAt (φ₁.open_source.mem_nhds h1src)).differentiableAt
      (by simp)
  have hsymmdiff : DifferentiableAt ℝ ((φ₀.symm) : Euc n → Euc n) c :=
    ((φ₀.symm).contMDiffOn_toFun.contDiffOn.contDiffAt
      ((φ₀.symm).open_source.mem_nhds hcsrc)).differentiableAt (by simp)
  have hφ₁diff' : DifferentiableAt ℝ (φ₁ : Euc n → Euc n) ((φ₀.symm) c) := by
    rw [hsymmc]
    exact hφ₁diff
  have hχsmooth : ContDiffOn ℝ ∞ χtilde U' := by
    have hsymmcont : ContDiffOn ℝ ∞ ((φ₀.symm) : Euc n → Euc n) S :=
      ((φ₀.symm).contMDiffOn_toFun.contDiffOn).mono inter_subset_left
    have hφ₁cont : ContDiffOn ℝ ∞ (φ₁ : Euc n → Euc n) φ₁.source :=
      φ₁.contMDiffOn_toFun.contDiffOn
    have h1 : ContDiffOn ℝ ∞ (fun y : Euc n => c + y) U' := by fun_prop
    have h2 : ContDiffOn ℝ ∞ (fun y : Euc n => (φ₀.symm) (c + y)) U' :=
      hsymmcont.comp h1 (fun y hy => hy)
    have h3 : MapsTo (fun y : Euc n => (φ₀.symm) (c + y)) U' φ₁.source := fun y hy => hy.2
    have h4 : ContDiffOn ℝ ∞ (fun y : Euc n => φ₁ ((φ₀.symm) (c + y))) U' :=
      hφ₁cont.comp h2 h3
    have h5 : ContDiffOn ℝ ∞ (fun y : Euc n => (T 1).symm (φ₁ ((φ₀.symm) (c + y)))) U' :=
      ((T 1).symm.contDiff.contDiffOn).comp h4 (fun y _ => mem_univ _)
    have h6 : ContDiffOn ℝ ∞ (fun y : Euc n => (T 1).symm (φ₁ ((φ₀.symm) (c + y))) - c) U' :=
      h5.sub (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : Euc n => c) U')
    have he : (fun y : Euc n => (T 1).symm (φ₁ ((φ₀.symm) (c + y))) - c) = χtilde := rfl
    rw [← he]
    exact h6
  have hTinv_ball : ∀ y ∈ closedBall d (δ / 2), (T 1).symm y = y - (d - c) := by
    intro y hy
    have hyc : y - (d - c) ∈ closedBall c (δ / 2) := by
      rw [mem_closedBall, dist_eq_norm] at hy ⊢
      have hsub : y - (d - c) - c = y - d := by abel
      rw [hsub]
      exact hy
    have hTy : T 1 (y - (d - c)) = y := by
      rw [hT1 _ hyc]
      abel
    have hs := Diffeomorph.symm_apply_apply (T 1) (y - (d - c))
    rw [hTy] at hs
    exact hs
  have hTinv_eq : ((T 1).symm : Euc n → Euc n) =ᶠ[𝓝 d] (fun y : Euc n => y - (d - c)) :=
    Filter.mem_of_superset (Metric.closedBall_mem_nhds d (by linarith : (0:ℝ) < δ/2)) hTinv_ball
  have hχtilde0 : χtilde 0 = 0 := by
    have hχc : χ c = c := by
      change (T 1).symm (φ₁ ((φ₀.symm) c)) = c
      rw [hsymmc, hφ₁zero, hTinv_ball d (mem_closedBall_self (by linarith : (0:ℝ) ≤ δ/2))]
      abel
    change χ (c + 0) - c = 0
    rw [add_zero, hχc, sub_self]
  have hCdet : (fderiv ℝ ((T 1).symm : Euc n → Euc n) d).det = 1 := by
    rw [Filter.EventuallyEq.fderiv_eq hTinv_eq]
    have hlin : fderiv ℝ (fun y : Euc n => y - (d - c)) d = 1 :=
      ((hasFDerivAt_id (𝕜 := ℝ) d).sub_const (d - c)).fderiv
    rw [hlin]
    exact det_one_clm
  have hchain : (fderiv ℝ ((φ₀.symm) : Euc n → Euc n) c).comp
      (fderiv ℝ (φ₀ : Euc n → Euc n) 0) = 1 := by
    have hev : ((φ₀.symm : Euc n → Euc n) ∘ (φ₀ : Euc n → Euc n)) =ᶠ[𝓝 0] id := by
      refine Filter.mem_of_superset
        (Metric.closedBall_mem_nhds (0 : Euc n) (ε := 2) (by norm_num)) ?_
      intro x hx
      exact φ₀.left_inv (h₀ hx)
    have h2 : fderiv ℝ ((φ₀.symm : Euc n → Euc n) ∘ (φ₀ : Euc n → Euc n)) 0 = 1 := by
      rw [Filter.EventuallyEq.fderiv_eq hev, fderiv_id]
      exact ContinuousLinearMap.ext fun x => rfl
    have h := fderiv_comp (f := (φ₀ : Euc n → Euc n)) (g := (φ₀.symm : Euc n → Euc n))
      (x := 0) hsymmdiff hφ₀diff
    rw [h2] at h
    simpa only [Function.comp_def] using h.symm
  have hBdet : (fderiv ℝ ((φ₀.symm) : Euc n → Euc n) c).det =
      ((fderiv ℝ (φ₀ : Euc n → Euc n) 0).det)⁻¹ := by
    have := congrArg ContinuousLinearMap.det hchain
    rw [det_comp_clm, det_one_clm] at this
    exact eq_inv_of_mul_eq_one_left this
  have hTinv_diff : DifferentiableAt ℝ ((T 1).symm : Euc n → Euc n) d :=
    ((T 1).symm.contDiff.differentiable (by simp)).differentiableAt
  have hφ₁symm_diff : DifferentiableAt ℝ ((T 1).symm : Euc n → Euc n) (φ₁ ((φ₀.symm) c)) := by
    rw [hsymmc, hφ₁zero]
    exact hTinv_diff
  have hχfderiv : fderiv ℝ χ c = (fderiv ℝ ((T 1).symm : Euc n → Euc n) d).comp
      ((fderiv ℝ (φ₁ : Euc n → Euc n) 0).comp
        (fderiv ℝ ((φ₀.symm) : Euc n → Euc n) c)) := by
    have hinner : DifferentiableAt ℝ (fun z : Euc n => φ₁ ((φ₀.symm) z)) c :=
      hφ₁diff'.comp c hsymmdiff
    have hcomp1 : fderiv ℝ (fun z : Euc n => φ₁ ((φ₀.symm) z)) c =
        (fderiv ℝ (φ₁ : Euc n → Euc n) 0).comp
          (fderiv ℝ ((φ₀.symm) : Euc n → Euc n) c) := by
      have h := fderiv_comp (f := ((φ₀.symm) : Euc n → Euc n)) (g := (φ₁ : Euc n → Euc n))
        (x := c) hφ₁diff' hsymmdiff
      rw [hsymmc] at h
      simpa only [Function.comp_def] using h
    have h := fderiv_comp (f := (fun z : Euc n => φ₁ ((φ₀.symm) z)))
      (g := ((T 1).symm : Euc n → Euc n)) (x := c) hφ₁symm_diff hinner
    rw [hsymmc, hφ₁zero, hcomp1] at h
    simpa only [Function.comp_def, χ] using h
  have hχtilde_fderiv : fderiv ℝ χtilde 0 = fderiv ℝ χ c := by
    have hinner : DifferentiableAt ℝ χ c :=
      hφ₁symm_diff.comp c (hφ₁diff'.comp c hsymmdiff)
    have hshift : HasFDerivAt (fun y : Euc n => c + y) (1 : Euc n →L[ℝ] Euc n) 0 :=
      (hasFDerivAt_id (𝕜 := ℝ) 0).const_add c
    have hχshift : HasFDerivAt (fun y : Euc n => χ (c + y))
        ((fderiv ℝ χ c).comp (1 : Euc n →L[ℝ] Euc n)) 0 :=
      by
        have hinner' : DifferentiableAt ℝ χ (c + 0) := by
          rw [add_zero]
          exact hinner
        have h := HasFDerivAt.comp (x := (0 : Euc n)) (f := fun y : Euc n => c + y)
          (g := χ) hinner'.hasFDerivAt hshift
        rw [add_zero] at h
        simpa only [Function.comp_def] using h
    have h2 : HasFDerivAt (fun y : Euc n => χ (c + y) - c)
        ((fderiv ℝ χ c).comp (1 : Euc n →L[ℝ] Euc n)) 0 := hχshift.sub_const c
    have he : χtilde = fun y : Euc n => χ (c + y) - c := rfl
    rw [he, h2.fderiv]
    ext x
    simp
  have hdetχ : (fderiv ℝ χtilde 0).det =
      (fderiv ℝ (φ₁ : Euc n → Euc n) 0).det *
        ((fderiv ℝ (φ₀ : Euc n → Euc n) 0).det)⁻¹ := by
    rw [hχtilde_fderiv, hχfderiv, det_comp_clm, det_comp_clm, hCdet, hBdet, one_mul]
  have hpos : 0 < (fderiv ℝ χtilde 0).det := by
    rw [hdetχ]
    have hA0ne : (fderiv ℝ (φ₀ : Euc n → Euc n) 0).det ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hori
      exact lt_irrefl 0 hori
    have hsq : 0 < ((fderiv ℝ (φ₀ : Euc n → Euc n) 0).det) ^ 2 := by
      rw [sq]
      exact mul_self_pos.mpr hA0ne
    have hmain : (fderiv ℝ (φ₁ : Euc n → Euc n) 0).det *
        ((fderiv ℝ (φ₀ : Euc n → Euc n) 0).det)⁻¹ =
        ((fderiv ℝ (φ₀ : Euc n → Euc n) 0).det *
          (fderiv ℝ (φ₁ : Euc n → Euc n) 0).det) /
          ((fderiv ℝ (φ₀ : Euc n → Euc n) 0).det) ^ 2 := by
      field_simp
    rw [hmain]
    exact div_pos hori hsq
  obtain ⟨ρ', hρ'pos, hρ'V⟩ : ∃ ρ' : ℝ, 0 < ρ' ∧ closedBall c ρ' ⊆ V := by
    have hcV : c ∈ V := hV₀ ⟨0, mem_closedBall_self (by norm_num), rfl⟩
    obtain ⟨ρ₀, hρ₀pos, hρ₀V⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hcV)
    exact ⟨ρ₀ / 2, by linarith, fun z hz => hρ₀V (Metric.closedBall_subset_ball (by linarith) hz)⟩
  obtain ⟨Kg, hKgc, hKgsub, hKgerm⟩ :=
    exists_realizesGerm_of_det_pos_closedBall hU'open h0U' hχsmooth hχtilde0 hpos hρ'pos
  obtain ⟨-, -, E, hEc, hEi, hE0, hEgerm, hEfix⟩ := hKgerm
  obtain ⟨εg, hεgpos, hεgeq⟩ := Metric.eventually_nhds_iff.mp hEgerm
  let Dτ : ℝ → Diffeomorph 𝓘(ℝ, Euc n) 𝓘(ℝ, Euc n) (Euc n) (Euc n) ∞ := fun t =>
    (modelTranslateDiffeomorph n (-c)).trans ((E t).trans (modelTranslateDiffeomorph n c))
  have hDτapply : ∀ t z, Dτ t z = c + E t (z - c) := by
    intro t z
    simp only [Dτ, Diffeomorph.coe_trans, Function.comp_apply, modelTranslateDiffeomorph_apply]
    abel_nf
  have hDτsymm : ∀ t z, (Dτ t).symm z = c + (E t).symm (z - c) := by
    intro t z
    have h : Dτ t (c + (E t).symm (z - c)) = z := by
      rw [hDτapply]
      have h1 : c + (E t).symm (z - c) - c = (E t).symm (z - c) := by abel
      rw [h1, Diffeomorph.apply_symm_apply]
      abel
    have hs := Diffeomorph.symm_apply_apply (Dτ t) (c + (E t).symm (z - c))
    rw [h] at hs
    exact hs
  have hDτc : ContDiff ℝ ∞ (fun q : ℝ × Euc n => Dτ q.1 q.2) := by
    have hbody : ContDiff ℝ ∞ (fun q : ℝ × Euc n => c + E q.1 (q.2 - c)) := by
      have hmap : ContDiff ℝ ∞ (fun q : ℝ × Euc n => (q.1, q.2 - c)) := by fun_prop
      have h1 : ContDiff ℝ ∞ (fun q : ℝ × Euc n => E q.1 (q.2 - c)) := by
        have h := hEc.comp hmap
        simpa only [Function.comp_def] using h
      exact (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ × Euc n => c)).add h1
    have he : (fun q : ℝ × Euc n => Dτ q.1 q.2) =
        fun q : ℝ × Euc n => c + E q.1 (q.2 - c) := by
      funext q
      exact hDτapply q.1 q.2
    rw [he]
    exact hbody
  have hDτi : ContDiff ℝ ∞ (fun q : ℝ × Euc n => (Dτ q.1).symm q.2) := by
    have hbody : ContDiff ℝ ∞ (fun q : ℝ × Euc n => c + (E q.1).symm (q.2 - c)) := by
      have hmap : ContDiff ℝ ∞ (fun q : ℝ × Euc n => (q.1, q.2 - c)) := by fun_prop
      have h1 : ContDiff ℝ ∞ (fun q : ℝ × Euc n => (E q.1).symm (q.2 - c)) := by
        have h := hEi.comp hmap
        simpa only [Function.comp_def] using h
      exact (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ × Euc n => c)).add h1
    have he : (fun q : ℝ × Euc n => (Dτ q.1).symm q.2) =
        fun q : ℝ × Euc n => c + (E q.1).symm (q.2 - c) := by
      funext q
      exact hDτsymm q.1 q.2
    rw [he]
    exact hbody
  have hDτ0 : Dτ 0 = Diffeomorph.refl 𝓘(ℝ, Euc n) (Euc n) ∞ := by
    apply Diffeomorph.ext
    intro z
    rw [hDτapply]
    have h1 : E 0 (z - c) = z - c := by rw [hE0]; rfl
    rw [h1]
    abel
  have hDτfix : ∀ t z, z ∉ closedBall c ρ' → Dτ t z = z ∧ (Dτ t).symm z = z := by
    intro t z hz
    have hzc : z - c ∉ Metric.closedBall (0 : Euc n) ρ' := fun h =>
      hz (by simpa [Metric.mem_closedBall, dist_eq_norm] using h)
    have hK : z - c ∉ Kg := fun h => hzc (hKgsub h)
    have h1 := (hEfix t (z - c) hK).1
    have h2 := (hEfix t (z - c) hK).2
    refine ⟨?_, ?_⟩
    · rw [hDτapply, h1]
      abel
    · rw [hDτsymm, h2]
      abel
  have hDτgerm : ∀ z, dist z c < εg → Dτ 1 z = χ z := by
    intro z hz
    have hzc : dist (z - c) (0 : Euc n) < εg := by simpa [dist_eq_norm] using hz
    rw [hDτapply, hεgeq hzc]
    change c + (χ (c + (z - c)) - c) = χ z
    rw [show c + (z - c) = z from by abel]
    abel
  let G : ℝ → Diffeomorph 𝓘(ℝ, Euc n) 𝓘(ℝ, Euc n) (Euc n) (Euc n) ∞ :=
    fun t => (Dτ t).trans (T t)
  have hGapply : ∀ t x, G t x = T t (Dτ t x) := fun t x => rfl
  have hGsymm : ∀ t x, (G t).symm x = (Dτ t).symm ((T t).symm x) := by
    intro t x
    change ((Dτ t).trans (T t)).symm x = (Dτ t).symm ((T t).symm x)
    rw [Diffeomorph.symm_trans']
    rfl
  have hG0 : G 0 = Diffeomorph.refl 𝓘(ℝ, Euc n) (Euc n) ∞ := by
    apply Diffeomorph.ext
    intro x
    rw [hGapply]
    have h1 : Dτ 0 x = x := by rw [hDτ0]; rfl
    have h2 : T 0 x = x := by rw [hT0]; rfl
    rw [h1, h2]
    simp only [Diffeomorph.coe_refl, id_eq]
  have hGc : ContDiff ℝ ∞ (fun q : ℝ × Euc n => G q.1 q.2) := by
    have hmap : ContDiff ℝ ∞ (fun q : ℝ × Euc n => (q.1, Dτ q.1 q.2)) :=
      contDiff_fst.prodMk hDτc
    have h := hTc.comp hmap
    have he : (fun q : ℝ × Euc n => G q.1 q.2) =
        fun q : ℝ × Euc n => T q.1 (Dτ q.1 q.2) := by
      funext q
      exact hGapply q.1 q.2
    rw [he]
    simpa only [Function.comp_def] using h
  have hGi : ContDiff ℝ ∞ (fun q : ℝ × Euc n => (G q.1).symm q.2) := by
    have hmap : ContDiff ℝ ∞ (fun q : ℝ × Euc n => (q.1, (T q.1).symm q.2)) :=
      contDiff_fst.prodMk hTi
    have h := hDτi.comp hmap
    have he : (fun q : ℝ × Euc n => (G q.1).symm q.2) =
        fun q : ℝ × Euc n => (Dτ q.1).symm ((T q.1).symm q.2) := by
      funext q
      exact hGsymm q.1 q.2
    rw [he]
    simpa only [Function.comp_def] using h
  have hGfix : ∀ t z, z ∉ KT ∪ closedBall c ρ' → G t z = z ∧ (G t).symm z = z := by
    intro t z hz
    have hzT : z ∉ KT := fun h => hz (Or.inl h)
    have hzD : z ∉ closedBall c ρ' := fun h => hz (Or.inr h)
    have h1 := (hKTfix t z hzT).1
    have h2 := (hDτfix t z hzD).1
    refine ⟨?_, ?_⟩
    · rw [hGapply, h2, h1]
    · rw [hGsymm, (hKTfix t z hzT).2, (hDτfix t z hzD).2]
  have hGgerm : ∀ z, dist z c < εg → G 1 z = φ₁ ((φ₀.symm) z) := by
    intro z hz
    rw [hGapply, hDτgerm z hz]
    change T 1 ((T 1).symm (φ₁ ((φ₀.symm) z))) = φ₁ ((φ₀.symm) z)
    rw [Diffeomorph.apply_symm_apply]
  have hφ₀cont : ContinuousAt (φ₀ : Euc n → Euc n) 0 :=
    φ₀.contMDiffOn_toFun.continuousOn.continuousAt (φ₀.open_source.mem_nhds h0src)
  obtain ⟨η, hηpos, hηsub⟩ := Metric.mem_nhds_iff.mp (hφ₀cont (Metric.ball_mem_nhds c hεgpos))
  let s : ℝ := max 0 (Real.log (4 / η))
  have hs_nonneg : 0 ≤ s := le_max_left _ _
  have hexp_le : Real.exp (-s) ≤ η / 4 := by
    have h1 : Real.log (4 / η) ≤ s := le_max_right _ _
    have h2 : Real.exp (-s) ≤ Real.exp (-(Real.log (4 / η))) :=
      Real.exp_le_exp.mpr (by linarith)
    have h3 : Real.exp (-(Real.log (4 / η))) = η / 4 := by
      have h4 : -(Real.log (4 / η)) = Real.log (η / 4) := by
        rw [Real.log_div (by norm_num : (4 : ℝ) ≠ 0) hηpos.ne',
          Real.log_div hηpos.ne' (by norm_num : (4 : ℝ) ≠ 0)]
        ring
      rw [h4, Real.exp_log (by positivity : (0 : ℝ) < η / 4)]
    linarith [h2, h3.le, h3.ge]
  have hmemN : ∀ x ∈ closedBall (0 : Euc n) 2, φ₀ (Real.exp (-s) • x) ∈ Metric.ball c εg := by
    intro x hx
    refine hηsub ?_
    rw [Metric.mem_ball, dist_zero_right]
    have hxn : ‖x‖ ≤ 2 := by simpa [mem_closedBall_zero_iff] using hx
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos (-s))]
    nlinarith [hexp_le, hxn, Real.exp_pos (-s), hηpos]
  let J : ℝ → Diffeomorph 𝓘(ℝ, Euc n) 𝓘(ℝ, Euc n) (Euc n) (Euc n) ∞ := fun t =>
    (C₀ (s * t)).trans ((G t).trans ((C₁ (s * t)).symm))
  have hJapply : ∀ t x, J t x = (C₁ (s * t)).symm (G t (C₀ (s * t) x)) := fun t x => rfl
  have hJsymm : ∀ t y, (J t).symm y = (C₀ (s * t)).symm ((G t).symm (C₁ (s * t) y)) := by
    intro t y
    have h : J t ((C₀ (s * t)).symm ((G t).symm (C₁ (s * t) y))) = y := by
      rw [hJapply, Diffeomorph.apply_symm_apply, Diffeomorph.apply_symm_apply,
        Diffeomorph.symm_apply_apply]
    have hs := Diffeomorph.symm_apply_apply (J t)
      ((C₀ (s * t)).symm ((G t).symm (C₁ (s * t) y)))
    rw [h] at hs
    exact hs
  have hJ0 : J 0 = Diffeomorph.refl 𝓘(ℝ, Euc n) (Euc n) ∞ := by
    apply Diffeomorph.ext
    intro x
    rw [hJapply]
    have h1 : C₀ (s * 0) x = x := by rw [mul_zero, hC₀0]; rfl
    have h2 : G 0 x = x := by rw [hG0]; rfl
    have h3 : (C₁ (s * 0)).symm x = x := by rw [mul_zero, hC₁0]; rfl
    rw [h1, h2, h3]
    simp only [Diffeomorph.coe_refl, id_eq]
  have hJ1 : ∀ x ∈ closedBall (0 : Euc n) 2, J 1 (φ₀ x) = φ₁ x := by
    intro x hx
    rw [hJapply, mul_one]
    have hC0x : C₀ s (φ₀ x) = φ₀ (Real.exp (-s) • x) := by
      exact hC₀rad s x hs_nonneg hx
    rw [hC0x, hGgerm _ (hmemN x hx)]
    have hsrc : Real.exp (-s) • x ∈ φ₀.source := by
      refine h₀ ?_
      rw [mem_closedBall_zero_iff]
      have hxn : ‖x‖ ≤ 2 := by simpa [mem_closedBall_zero_iff] using hx
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos (-s))]
      have hexp1 : Real.exp (-s) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hs_nonneg)
      nlinarith [hexp1, hxn, norm_nonneg x, Real.exp_pos (-s)]
    have hsymm_apply : (φ₀.symm.toPartialEquiv : Euc n → Euc n)
        (φ₀.toPartialEquiv (Real.exp (-s) • x)) = Real.exp (-s) • x := φ₀.left_inv hsrc
    rw [hsymm_apply, ← hC₁rad s x hs_nonneg hx, Diffeomorph.symm_apply_apply]
  have hC₀cs : ContDiff ℝ ∞ (fun q : ℝ × Euc n => C₀ (s * q.1) q.2) := by
    have hmap : ContDiff ℝ ∞ (fun q : ℝ × Euc n => (s * q.1, q.2)) := by fun_prop
    have h := hC₀cd.comp hmap
    simpa only [Function.comp_def] using h
  have hC₀is : ContDiff ℝ ∞ (fun q : ℝ × Euc n => (C₀ (s * q.1)).symm q.2) := by
    have hmap : ContDiff ℝ ∞ (fun q : ℝ × Euc n => (s * q.1, q.2)) := by fun_prop
    have h := hC₀id.comp hmap
    simpa only [Function.comp_def] using h
  have hC₁cs : ContDiff ℝ ∞ (fun q : ℝ × Euc n => C₁ (s * q.1) q.2) := by
    have hmap : ContDiff ℝ ∞ (fun q : ℝ × Euc n => (s * q.1, q.2)) := by fun_prop
    have h := hC₁cd.comp hmap
    simpa only [Function.comp_def] using h
  have hC₁is : ContDiff ℝ ∞ (fun q : ℝ × Euc n => (C₁ (s * q.1)).symm q.2) := by
    have hmap : ContDiff ℝ ∞ (fun q : ℝ × Euc n => (s * q.1, q.2)) := by fun_prop
    have h := hC₁id.comp hmap
    simpa only [Function.comp_def] using h
  have hJc : ContDiff ℝ ∞ (fun q : ℝ × Euc n => J q.1 q.2) := by
    have hm1 : ContDiff ℝ ∞ (fun q : ℝ × Euc n => (q.1, C₀ (s * q.1) q.2)) :=
      contDiff_fst.prodMk hC₀cs
    have hinner : ContDiff ℝ ∞ (fun q : ℝ × Euc n => G q.1 (C₀ (s * q.1) q.2)) := by
      have h := hGc.comp hm1
      simpa only [Function.comp_def] using h
    have hm2 : ContDiff ℝ ∞ (fun q : ℝ × Euc n => (q.1, G q.1 (C₀ (s * q.1) q.2))) :=
      contDiff_fst.prodMk hinner
    have h := hC₁is.comp hm2
    have he : (fun q : ℝ × Euc n => J q.1 q.2) =
        fun q : ℝ × Euc n => (C₁ (s * q.1)).symm (G q.1 (C₀ (s * q.1) q.2)) := by
      funext q
      exact hJapply q.1 q.2
    rw [he]
    simpa only [Function.comp_def] using h
  have hJi : ContDiff ℝ ∞ (fun q : ℝ × Euc n => (J q.1).symm q.2) := by
    have hm1 : ContDiff ℝ ∞ (fun q : ℝ × Euc n => (q.1, C₁ (s * q.1) q.2)) :=
      contDiff_fst.prodMk hC₁cs
    have hinner : ContDiff ℝ ∞ (fun q : ℝ × Euc n => (G q.1).symm (C₁ (s * q.1) q.2)) := by
      have h := hGi.comp hm1
      simpa only [Function.comp_def] using h
    have hm2 : ContDiff ℝ ∞ (fun q : ℝ × Euc n => (q.1, (G q.1).symm (C₁ (s * q.1) q.2))) :=
      contDiff_fst.prodMk hinner
    have h := hC₀is.comp hm2
    have he : (fun q : ℝ × Euc n => (J q.1).symm q.2) =
        fun q : ℝ × Euc n => (C₀ (s * q.1)).symm ((G q.1).symm (C₁ (s * q.1) q.2)) := by
      funext q
      exact hJsymm q.1 q.2
    rw [he]
    simpa only [Function.comp_def] using h
  refine ⟨J, hJc, hJi, hJ0, hJ1, (K₀ ∪ K₁) ∪ (KT ∪ closedBall c ρ'), ?_, ?_, ?_⟩
  · exact (hK₀c.union hK₁c).union (hKTc.union (isCompact_closedBall _ _))
  · intro y hy
    exact (union_subset (union_subset hK₀V hK₁V) (union_subset hKTV hρ'V)) hy
  · intro t y hy
    have hy₀₁ : y ∉ K₀ ∪ K₁ := fun h => hy (Or.inl h)
    have hyG : y ∉ KT ∪ closedBall c ρ' := fun h => hy (Or.inr h)
    have hy₀ : y ∉ K₀ := fun h => hy₀₁ (Or.inl h)
    have hy₁ : y ∉ K₁ := fun h => hy₀₁ (Or.inr h)
    have hval : J t y = y := by
      rw [hJapply, (hK₀fix (s * t) y hy₀).1, (hGfix t y hyG).1, (hK₁fix (s * t) y hy₁).2]
    refine ⟨hval, ?_⟩
    have hs := Diffeomorph.symm_apply_apply (J t) y
    rw [hval] at hs
    exact hs

end DifferentialGeometry.Topology.Manifold
