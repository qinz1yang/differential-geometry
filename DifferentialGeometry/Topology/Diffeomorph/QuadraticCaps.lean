import DifferentialGeometry.Topology.Diffeomorph.Fiberwise
import DifferentialGeometry.Analysis.ODE.QuadraticLevelScaling
import DifferentialGeometry.Topology.Manifold.BallChartGluing

open Set Metric Manifold
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Analysis.ODE

namespace Diffeomorph

private theorem exists_rescaled_family
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : ℝ → E ≃ₘ[ℝ] E)
    (hG : ContDiff ℝ ∞ (fun z : ℝ × E => G z.1 z.2))
    (hGi : ContDiff ℝ ∞ (fun z : ℝ × E => (G z.1).symm z.2))
    {U : Set ℝ} (hU : IsOpen U) {R : ℝ → ℝ} (hR : ContDiffOn ℝ ∞ R U)
    (hRne : ∀ t ∈ U, R t ≠ 0) {r : ℝ} (hr : r ≠ 0) :
    ∃ φ : PartialDiffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E × ℝ) (E × ℝ) (E × ℝ) ∞,
      φ.source = Prod.snd ⁻¹' U ∧
      ∀ z, φ z = (G z.2 ((r / R z.2) • z.1), z.2) := by
  let S := PartialDiffeomorph.fiberwiseSmulOn (E := E) hU
    (contDiffOn_const.div hR hRne) (fun t ht => div_ne_zero hr (hRne t ht))
  let P : (E × ℝ) ≃ₘ[ℝ] (E × ℝ) :=
    { toEquiv := Equiv.prodCongrLeft (fun t => (G t).toEquiv)
      contMDiff_toFun :=
        ((hG.comp (contDiff_snd.prodMk contDiff_fst)).prodMk contDiff_snd).contMDiff
      contMDiff_invFun :=
        ((hGi.comp (contDiff_snd.prodMk contDiff_fst)).prodMk contDiff_snd).contMDiff }
  refine ⟨S.trans P.toPartialDiffeomorph, ?_, fun _ => rfl⟩
  change (Prod.snd ⁻¹' U) ∩ S ⁻¹' univ = Prod.snd ⁻¹' U
  simp

open DifferentialGeometry.Topology.Manifold in
theorem exists_diffeomorph_eqOn_quadratic_cap_charts
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    (Q : H ≃ₘ[ℝ] (E × ℝ)) (A₀ A₁ F : (E × ℝ) ≃ₘ[ℝ] (E × ℝ))
    (C : E ≃ₘ[ℝ] E) (G : ℝ → E ≃ₘ[ℝ] E)
    (hA₀ : ∀ z, (A₀ z).2 = z.2) (hA₁ : ∀ z, (A₁ z).2 = z.2)
    (hG : ContDiff ℝ ∞ (fun z : ℝ × E => G z.1 z.2))
    (hGi : ContDiff ℝ ∞ (fun z : ℝ × E => (G z.1).symm z.2))
    {a b c₀ c₁ r η τ ρ : ℝ} (hr : 0 < r) (hρ : 0 < ρ)
    (ha : a = c₀ + r ^ 2 / 2) (hb : b = c₁ - r ^ 2 / 2)
    (hτ : 0 < τ) (hτη : τ ≤ η) (hab : a + τ ≤ b - τ)
    {R : ℝ → ℝ} (hR : ContDiffOn ℝ ∞ R (Ioo c₀ c₁))
    (hRpos : ∀ t ∈ Ioo c₀ c₁, 0 < R t)
    (hR₀ : ∀ t ∈ Icc c₀ (a + τ), R t ^ 2 = 2 * (t - c₀))
    (hR₁ : ∀ t ∈ Icc (b - τ) c₁, R t ^ 2 = 2 * (c₁ - t))
    (hQ : ∀ z ∈ closedBall (0 : H) ρ,
      (Q z).2 ∈ Icc c₀ c₁ ∧ ‖(Q z).1‖ ≤ R (Q z).2)
    {V : Set E} (hV : IsOpen V) (hVr : closedBall 0 r ⊆ V)
    (h₀ : ∀ t ∈ Icc (a - η) (a + η), ∀ x ∈ V,
      G t x = (A₀ (quadraticLevelScaling a c₀ x t, t)).1)
    (h₁ : ∀ t ∈ Icc (b - η) (b + η), ∀ x ∈ V,
      G t x = (A₁ (quadraticLevelScaling b c₁ (C x) t, t)).1)
    (hF : ∀ z : E × ℝ, |z.2 - b| ≤ τ →
      F z = (Real.sqrt ((c₁ - z.2) / (r ^ 2 / 2)) •
        C ((Real.sqrt ((c₁ - z.2) / (r ^ 2 / 2)))⁻¹ • z.1), z.2))
    (hFside : ∀ z, b ≤ (F z).2 ↔ b ≤ z.2) :
    ∃ D : H ≃ₘ[ℝ] (E × ℝ),
      (∀ z ∈ closedBall (0 : H) ρ, (Q z).2 < a + τ → D z = A₀ (Q z)) ∧
      (∀ z ∈ closedBall (0 : H) ρ, (Q z).2 ∈ Ioo a b →
        D z = (G (Q z).2 ((r / R (Q z).2) • (Q z).1), (Q z).2)) ∧
      (∀ z ∈ closedBall (0 : H) ρ, b - τ < (Q z).2 → D z = A₁ (F (Q z))) := by
  have hca : c₀ < a := by rw [ha]; nlinarith [sq_pos_of_pos hr]
  have hbc : b < c₁ := by rw [hb]; nlinarith [sq_pos_of_pos hr]
  have hab' : a < b := by linarith
  have hsub : Ioo a b ⊆ Ioo c₀ c₁ := fun _ ht => ⟨hca.trans ht.1, ht.2.trans hbc⟩
  obtain ⟨M, hMs, hM⟩ := exists_rescaled_family G hG hGi isOpen_Ioo (hR.mono hsub)
    (fun t ht => (hRpos t (hsub ht)).ne') hr.ne'
  let W : Set (E × ℝ) := Prod.snd ⁻¹' Ioo c₀ c₁
  let N : E × ℝ → E := fun z => (r / R z.2) • z.1
  have hW : IsOpen W := isOpen_Ioo.preimage continuous_snd
  have hN : ContDiffOn ℝ ∞ N W :=
    (contDiffOn_const.div (hR.comp contDiff_snd.contDiffOn (fun _ hz => hz))
      (fun z hz => (hRpos z.2 hz).ne')).smul contDiff_fst.contDiffOn
  let Ω : Set (E × ℝ) := {z | z.2 < a} ∪ {z | b < z.2} ∪ (W ∩ N ⁻¹' V)
  have hΩ : IsOpen Ω := ((isOpen_lt continuous_snd continuous_const).union
    (isOpen_lt continuous_const continuous_snd)).union
      (hN.continuousOn.isOpen_inter_preimage hW hV)
  have hQΩ : ∀ z ∈ closedBall (0 : H) ρ, Q z ∈ Ω := by
    intro z hz
    by_cases hlow : (Q z).2 < a
    · exact Or.inl (Or.inl hlow)
    by_cases hhigh : b < (Q z).2
    · exact Or.inl (Or.inr hhigh)
    have ht : (Q z).2 ∈ Ioo c₀ c₁ :=
      ⟨hca.trans_le (le_of_not_gt hlow), (le_of_not_gt hhigh).trans_lt hbc⟩
    refine Or.inr ⟨ht, hVr ?_⟩
    rw [mem_closedBall_zero_iff]
    change ‖(r / R (Q z).2) • (Q z).1‖ ≤ r
    rw [norm_smul, Real.norm_of_nonneg (div_pos hr (hRpos _ ht)).le]
    calc
      _ ≤ (r / R (Q z).2) * R (Q z).2 :=
        mul_le_mul_of_nonneg_left (hQ z hz).2 (div_pos hr (hRpos _ ht)).le
      _ = r := div_mul_cancel₀ _ (hRpos _ ht).ne'
  have hΩmid {z : E × ℝ} (hz : z ∈ Ω) (ht : z.2 ∈ Ioo a b) : N z ∈ V := by
    rcases hz with (hz | hz) | hz
    · exact False.elim ((not_lt_of_gt ht.1) hz)
    · exact False.elim ((not_lt_of_gt ht.2) hz)
    · exact hz.2
  have hscale₀ (t : ℝ) (ht : t ∈ Ioo a (a + τ)) (x : E) :
      quadraticLevelScaling a c₀ ((r / R t) • x) t = x := by
    have htc : t ∈ Ioo c₀ c₁ := ⟨hca.trans ht.1, by linarith [ht.2]⟩
    apply quadraticLevelScaling_smul_div_of_sq hr (hRpos t htc)
    rw [hR₀ t ⟨htc.1.le, ht.2.le⟩, ha]
    field_simp
    ring
  have hscale₁ (t : ℝ) (ht : t ∈ Ioo (b - τ) b) (x : E) :
      quadraticLevelScaling b c₁ x t = (R t / r) • x := by
    have htc : t ∈ Ioo c₀ c₁ := ⟨by linarith [ht.1], ht.2.trans hbc⟩
    apply quadraticLevelScaling_eq_smul_of_sq hr (hRpos t htc).le
    rw [hR₁ t ⟨ht.1.le, htc.2.le⟩, hb]
    field_simp
    ring
  have hsqrt (t : ℝ) (ht : t ∈ Ioo (b - τ) b) :
      Real.sqrt ((c₁ - t) / (r ^ 2 / 2)) = R t / r := by
    have htc : t ∈ Ioo c₀ c₁ := ⟨by linarith [ht.1], ht.2.trans hbc⟩
    have heq : (c₁ - t) / (r ^ 2 / 2) = (R t / r) ^ 2 := by
      rw [div_pow, hR₁ t ⟨ht.1.le, htc.2.le⟩]
      field_simp
    rw [heq, Real.sqrt_sq (div_pos (hRpos t htc) hr).le]
  have hM₀ {z : E × ℝ} (hz : z ∈ Ω) (ht : z.2 ∈ Ioo a (a + τ)) : M z = A₀ z := by
    have htab : z.2 ∈ Ioo a b := ⟨ht.1, by linarith [ht.2]⟩
    rw [hM, h₀ z.2 ⟨by linarith [ht.1], by linarith [ht.2]⟩ _ (hΩmid hz htab), hscale₀ z.2 ht]
    exact Prod.ext rfl (hA₀ z).symm
  have hM₁ {z : E × ℝ} (hz : z ∈ Ω) (ht : z.2 ∈ Ioo (b - τ) b) : M z = A₁ (F z) := by
    have htab : z.2 ∈ Ioo a b := ⟨by linarith [ht.1], ht.2⟩
    rw [hM, h₁ z.2 ⟨by linarith [ht.1], by linarith [ht.2]⟩ _ (hΩmid hz htab), hscale₁ z.2 ht,
      hF z (abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩), hsqrt z.2 ht, inv_div]
    exact Prod.ext rfl (hA₁ ((R z.2 / r) • C ((r / R z.2) • z.1), z.2)).symm
  let S := Q
  let φ : Fin 3 → PartialDiffeomorph 𝓘(ℝ, H) 𝓘(ℝ, H) H H ∞ :=
    ![(Q.trans (A₀.trans S.symm)).toPartialDiffeomorph,
      (Q.toPartialDiffeomorph.trans M).trans S.symm.toPartialDiffeomorph,
      (Q.trans (F.trans (A₁.trans S.symm))).toPartialDiffeomorph]
  let f : H → ℝ := fun z => (Q z).2
  let g : H → ℝ := fun z => (S z).2
  let U : Fin 3 → Set H := fun i =>
    Q ⁻¹' (Ω ∩ Prod.snd ⁻¹' (![Iio (a + τ), Ioo a b, Ioi (b - τ)] i))
  have hU : ∀ i, IsOpen (U i) := by
    intro i
    fin_cases i
    · exact (hΩ.inter (isOpen_Iio.preimage continuous_snd)).preimage Q.continuous
    · exact (hΩ.inter (isOpen_Ioo.preimage continuous_snd)).preimage Q.continuous
    · exact (hΩ.inter (isOpen_Ioi.preimage continuous_snd)).preimage Q.continuous
  have hUs : ∀ i, U i ⊆ (φ i).source := by
    intro i z hz
    fin_cases i
    · exact mem_univ _
    · change (z ∈ univ ∧ Q z ∈ M.source) ∧ _ ∈ univ
      exact ⟨⟨mem_univ _, by rw [hMs]; exact hz.2⟩, mem_univ _⟩
    · exact mem_univ _
  have hband : ∀ i, ∀ z ∈ closedBall (0 : H) ρ,
      z ∈ U i ↔ f z ∈ ![Iio (a + τ), Ioo a b, Ioi (b - τ)] i := by
    intro i z hz
    exact and_iff_right (hQΩ z hz)
  have heq₀₁ : EqOn (φ 0) (φ 1) (U 0 ∩ U 1) := by
    intro z hz
    change S.symm (A₀ (Q z)) = S.symm (M (Q z))
    rw [hM₀ hz.1.1 ⟨hz.2.2.1, hz.1.2⟩]
  have heq₁₂ : EqOn (φ 1) (φ 2) (U 1 ∩ U 2) := by
    intro z hz
    change S.symm (M (Q z)) = S.symm (A₁ (F (Q z)))
    rw [hM₁ hz.1.1 ⟨hz.2.2, hz.1.2.2⟩]
  have hempty : U 0 ∩ U 2 = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro z hz
    have hlow : (Q z).2 < a + τ := hz.1.2
    have hhigh : b - τ < (Q z).2 := hz.2.2
    linarith
  have heq : ∀ i j, EqOn (φ i) (φ j) (U i ∩ U j) := by
    intro i j
    fin_cases i <;> fin_cases j
    · exact fun _ _ => rfl
    · exact heq₀₁
    · change EqOn (φ 0) (φ 2) (U 0 ∩ U 2)
      rw [hempty]; exact eqOn_empty _ _
    · exact fun _ hz => (heq₀₁ ⟨hz.2, hz.1⟩).symm
    · exact fun _ _ => rfl
    · exact heq₁₂
    · change EqOn (φ 2) (φ 0) (U 2 ∩ U 0)
      rw [inter_comm, hempty]; exact eqOn_empty _ _
    · exact fun _ hz => (heq₁₂ ⟨hz.2, hz.1⟩).symm
    · exact fun _ _ => rfl
  obtain ⟨D, hD⟩ :=
    exists_diffeomorph_eqOn_of_partialDiffeomorphs_closedBall_of_height_intervals
      φ f g hρ hτ hab hU hUs hband heq
      (by intro z _; change (S (S.symm (A₀ (Q z)))).2 = _; rw [S.apply_symm_apply, hA₀])
      (by intro z _; change (S (S.symm (M (Q z)))).2 = _; rw [S.apply_symm_apply, hM])
      (by intro z _; change (b ≤ (S (S.symm (A₁ (F (Q z))))).2 ↔ b ≤ (Q z).2)
          rw [S.apply_symm_apply, hA₁]; exact hFside (Q z))
  refine ⟨D.trans S, ?_, ?_, ?_⟩
  · intro z hz ht
    change S (D z) = A₀ (Q z)
    rw [hD 0 ⟨hz, (hband 0 z hz).mpr ht⟩]
    exact S.apply_symm_apply _
  · intro z hz ht
    change S (D z) = _
    rw [hD 1 ⟨hz, (hband 1 z hz).mpr ht⟩]
    change S (S.symm (M (Q z))) = _
    rw [S.apply_symm_apply, hM]
  · intro z hz ht
    change S (D z) = A₁ (F (Q z))
    rw [hD 2 ⟨hz, (hband 2 z hz).mpr ht⟩]
    exact S.apply_symm_apply _

end Diffeomorph
