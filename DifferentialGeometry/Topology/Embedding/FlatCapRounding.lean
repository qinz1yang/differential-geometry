import DifferentialGeometry.Topology.Embedding.CylinderCapRounding

open Set Metric
open scoped ContDiff Manifold

namespace Diffeomorph

private theorem range_cylinderCap
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {a : ℝ} (ha : 0 < a) :
    range (EuclideanGeometry.cylinderCap (E := E) a) =
      EuclideanGeometry.cylinderCap a '' closedBall (0 : E) 1 ∪ sphere (0 : E) 1 ×ˢ Ioi (0 : ℝ) := by
  ext p
  constructor
  · rintro ⟨x, rfl⟩
    by_cases hx : ‖x‖ ≤ 1
    · exact Or.inl ⟨x, mem_closedBall_zero_iff.mpr hx, rfl⟩
    · have hn : 1 < ‖x‖ := lt_of_not_ge hx
      have hxpos : 0 < ‖x‖ := lt_trans zero_lt_one hn
      rw [EuclideanGeometry.cylinderCap_of_norm_sq_ge a (by nlinarith)]
      refine Or.inr ⟨?_, ?_⟩
      · rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs, abs_inv,
          abs_of_pos hxpos, inv_mul_cancel₀ hxpos.ne']
      · exact mul_pos ha (by nlinarith)
  · rintro (⟨x, _, rfl⟩ | ⟨hp, ht⟩)
    · exact mem_range_self x
    · exact ⟨Real.sqrt (1 + p.2 / a) • p.1,
        EuclideanGeometry.cylinderCap_sqrt_smul ha.ne'
          (by have := div_pos ht ha; linarith) (mem_sphere_zero_iff_norm.mp hp)⟩

private theorem range_cap_replacement
    {M E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {e f : M → F} (Ψ : E × ℝ → F) (χ : E → M) {D : Set M} {a : ℝ}
    (hχD : χ '' closedBall (0 : E) 1 = D)
    (hcap : ∀ x ∈ closedBall (0 : E) 1, f (χ x) = Ψ (EuclideanGeometry.cylinderCap a x))
    (hfix : EqOn f e Dᶜ) :
    range f = Ψ '' (EuclideanGeometry.cylinderCap a '' closedBall (0 : E) 1) ∪ e '' Dᶜ := by
  ext z
  constructor
  · rintro ⟨y, rfl⟩
    by_cases hy : y ∈ D
    · obtain ⟨x, hx, rfl⟩ := hχD.symm.subset hy
      exact Or.inl ⟨EuclideanGeometry.cylinderCap a x, ⟨x, hx, rfl⟩, (hcap x hx).symm⟩
    · exact Or.inr ⟨y, hy, (hfix hy).symm⟩
  · rintro (⟨_, ⟨x, hx, rfl⟩, rfl⟩ | ⟨y, hy, rfl⟩)
    · exact ⟨χ x, hcap x hx⟩
    · exact ⟨y, hfix hy⟩

private theorem exists_replacement_rounding_of_pos
    {X E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {e f : X → F} (Ψ : (E × ℝ) ≃ₘ[ℝ] F) (χ : E → X)
    {D : Set X} {R b a ε : ℝ} (hR : 1 < R) (ha : 0 < a) (hab : a < b)
    (hε : 0 < ε) (hε1 : ε < 1) (hεb : ε < b)
    (hχD : χ '' closedBall (0 : E) 1 = D)
    (hcap : ∀ x ∈ closedBall (0 : E) 1,
      f (χ x) = Ψ (EuclideanGeometry.cylinderCap a x))
    (hfix : EqOn f e Dᶜ)
    (hret : ∀ p ∈ ball (0 : E) R ×ˢ Ioo (-b) b,
      Ψ p ∈ e '' Dᶜ ↔ ‖p.1‖ = 1 ∧ 0 < p.2) :
    ∃ Φ : F ≃ₘ[ℝ] F,
      range (Φ ∘ f) =
        (range f \ Ψ '' (ball (0 : E) R ×ˢ Ioo (-b) b)) ∪
        Ψ '' {p : E × ℝ | p ∈ ball 0 R ×ˢ Ioo (-b) b ∧
          Real.smoothAbs ε (1 - ‖p.1‖ ^ 2 - p.2) = 1 - ‖p.1‖ ^ 2 + p.2} ∧
      ∃ K : Set F, IsCompact K ∧
        K ⊆ Ψ '' (ball (0 : E) R ×ˢ Ioo (-b) b) ∧
        EqOn Φ id Kᶜ ∧ EqOn Φ.symm id Kᶜ := by
  let U := ball (0 : E) R ×ˢ Ioo (-b) b
  let T : Set (E × ℝ) :=
    {p | Real.smoothAbs ε (1 - ‖p.1‖ ^ 2 - p.2) = 1 - ‖p.1‖ ^ 2 + p.2}
  have hU : IsOpen U := isOpen_ball.prod isOpen_Ioo
  have hslab : closedBall (0 : E) 1 ×ˢ Icc (-a) ε ⊆ U := by
    intro p hp
    exact ⟨closedBall_subset_ball hR hp.1, by linarith [hp.2.1], by linarith [hp.2.2]⟩
  obtain ⟨H, hHrange, C, hC, hCU, hHfix, hHifix⟩ :=
    Diffeomorph.exists_diffeomorph_cylinderCap_rounding ha hε hε1 hU hslab
  have hHU (p : E × ℝ) : H p ∈ U ↔ p ∈ U := by
    constructor
    · intro hp
      by_contra hn
      have hpc : p ∉ C := fun h => hn (hCU h)
      rw [hHfix hpc] at hp
      exact hn hp
    · intro hp
      by_contra hn
      have hpc : H p ∉ C := fun h => hn (hCU h)
      have hh := hHifix hpc
      rw [H.symm_apply_apply] at hh
      exact hn ((congrArg (fun q => q ∈ U) hh).mp hp)
  have hHinvU (p : E × ℝ) : H.symm p ∈ U ↔ p ∈ U := by
    simpa only [H.apply_symm_apply] using (hHU (H.symm p)).symm
  have hfU (p : E × ℝ) (hp : p ∈ U) :
      Ψ p ∈ range f ↔ p ∈ range (EuclideanGeometry.cylinderCap a) := by
    rw [range_cap_replacement Ψ χ hχD hcap hfix, range_cylinderCap ha]
    simp only [mem_union, mem_prod, mem_Ioi, mem_sphere_zero_iff_norm]
    rw [hret p hp]
    constructor
    · rintro (⟨q, hq, hqp⟩ | hq)
      · exact Or.inl (Ψ.injective hqp ▸ hq)
      · exact Or.inr hq
    · rintro (hq | hq)
      · exact Or.inl ⟨p, hq, rfl⟩
      · exact Or.inr hq
  let Φ := Ψ.symm.trans (H.trans Ψ)
  have hmem (p : E × ℝ) :
      Ψ p ∈ range (Φ ∘ f) ↔ Ψ (H.symm p) ∈ range f := by
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨y, ?_⟩
      have hy' : Ψ (H (Ψ.symm (f y))) = Ψ p := hy
      have hh := congrArg H.symm (Ψ.injective hy')
      rw [H.symm_apply_apply] at hh
      exact (Ψ.apply_symm_apply (f y)).symm.trans (congrArg Ψ hh)
    · rintro ⟨y, hy⟩
      refine ⟨y, ?_⟩
      change Ψ (H (Ψ.symm (f y))) = Ψ p
      rw [hy, Ψ.symm_apply_apply, H.apply_symm_apply]
  have hlocal (p : E × ℝ) (hp : p ∈ U) :
      Ψ p ∈ range (Φ ∘ f) ↔ p ∈ T := by
    rw [hmem, hfU _ ((hHinvU p).mpr hp)]
    constructor
    · intro hh
      exact hHrange.subset ⟨H.symm p, hh, H.apply_symm_apply p⟩
    · intro hh
      obtain ⟨q, hq, hqp⟩ := hHrange.symm.subset hh
      simpa only [← hqp, H.symm_apply_apply] using hq
  have houter (p : E × ℝ) (hp : p ∉ U) :
      Ψ p ∈ range (Φ ∘ f) ↔ Ψ p ∈ range f := by
    rw [hmem, hHifix (fun h => hp (hCU h))]
    rfl
  refine ⟨Φ, ?_, Ψ '' C, hC.image Ψ.continuous, image_mono hCU, ?_, ?_⟩
  · ext y
    let p := Ψ.symm y
    have hpy : Ψ p = y := Ψ.apply_symm_apply y
    rw [← hpy]
    by_cases hp : p ∈ U
    · rw [hlocal p hp]
      constructor
      · intro hh
        exact Or.inr ⟨p, ⟨hp, hh⟩, rfl⟩
      · rintro (⟨_, hn⟩ | ⟨q, hq, hqp⟩)
        · exact False.elim (hn ⟨p, hp, rfl⟩)
        · exact Ψ.injective hqp ▸ hq.2
    · rw [houter p hp]
      constructor
      · intro hh
        refine Or.inl ⟨hh, ?_⟩
        rintro ⟨q, hq, hqp⟩
        exact hp (Ψ.injective hqp ▸ hq)
      · rintro (⟨hh, _⟩ | ⟨q, hq, hqp⟩)
        · exact hh
        · exact False.elim (hp (Ψ.injective hqp ▸ hq.1))
  · intro y hy
    have hc : Ψ.symm y ∉ C := by
      intro hc
      exact hy ⟨Ψ.symm y, hc, Ψ.apply_symm_apply y⟩
    change Ψ (H (Ψ.symm y)) = y
    rw [hHfix hc, id_eq, Ψ.apply_symm_apply]
  · intro y hy
    have hc : Ψ.symm y ∉ C := by
      intro hc
      exact hy ⟨Ψ.symm y, hc, Ψ.apply_symm_apply y⟩
    change Ψ (H.symm (Ψ.symm y)) = y
    rw [hHifix hc, id_eq, Ψ.apply_symm_apply]

theorem exists_cylinderCap_replacement_rounding
    {X E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {e f : X → F} (Ψ : (E × ℝ) ≃ₘ[ℝ] F) (χ : E → X)
    {D : Set X} {R b a ε σ : ℝ} (hR : 1 < R) (ha : 0 < a) (hab : a < b)
    (hε : 0 < ε) (hε1 : ε < 1) (hεb : ε < b) (hσ : σ = 1 ∨ σ = -1)
    (hχD : χ '' closedBall (0 : E) 1 = D)
    (hcap : ∀ x ∈ closedBall (0 : E) 1,
      f (χ x) = Ψ (EuclideanGeometry.cylinderCap (σ * a) x))
    (hfix : EqOn f e Dᶜ)
    (hret : ∀ p ∈ ball (0 : E) R ×ˢ Ioo (-b) b,
      Ψ p ∈ e '' Dᶜ ↔ ‖p.1‖ = 1 ∧ 0 < σ * p.2) :
    ∃ Φ : F ≃ₘ[ℝ] F,
      range (Φ ∘ f) =
        (range f \ Ψ '' (ball (0 : E) R ×ˢ Ioo (-b) b)) ∪
        Ψ '' {p : E × ℝ | p ∈ ball 0 R ×ˢ Ioo (-b) b ∧
          Real.smoothAbs ε (1 - ‖p.1‖ ^ 2 - σ * p.2) = 1 - ‖p.1‖ ^ 2 + σ * p.2} ∧
      ∃ K : Set F, IsCompact K ∧
        K ⊆ Ψ '' (ball (0 : E) R ×ˢ Ioo (-b) b) ∧
        EqOn Φ id Kᶜ ∧ EqOn Φ.symm id Kᶜ := by
  rcases hσ with rfl | rfl
  · simp only [one_mul] at hcap hret ⊢
    exact exists_replacement_rounding_of_pos Ψ χ hR ha hab hε hε1 hεb hχD hcap hfix hret
  · simp only [neg_one_mul] at hcap hret ⊢
    let J : (E × ℝ) ≃ₘ[ℝ] (E × ℝ) :=
      ((ContinuousLinearEquiv.refl ℝ E).prodCongr
        (ContinuousLinearEquiv.neg ℝ : ℝ ≃L[ℝ] ℝ)).toDiffeomorph
    have hJ (p : E × ℝ) : J p = (p.1, -p.2) := rfl
    have hJJ (p : E × ℝ) : J (J p) = p := by simp only [hJ, neg_neg]
    let Ψ' := J.trans Ψ
    let U := ball (0 : E) R ×ˢ Ioo (-b) b
    have hJU (p : E × ℝ) : J p ∈ U ↔ p ∈ U := by
      change (p.1 ∈ ball 0 R ∧ -p.2 ∈ Ioo (-b) b) ↔ p ∈ U
      constructor <;> intro hp <;> exact ⟨hp.1, by linarith [hp.2.2], by linarith [hp.2.1]⟩
    have hcap' : ∀ x ∈ closedBall (0 : E) 1,
        f (χ x) = Ψ' (EuclideanGeometry.cylinderCap a x) := by
      intro x hx
      change f (χ x) = Ψ ((EuclideanGeometry.cylinderCap a x).1,
        -(EuclideanGeometry.cylinderCap a x).2)
      simpa only [EuclideanGeometry.cylinderCap_neg] using hcap x hx
    have hret' : ∀ p ∈ U, Ψ' p ∈ e '' Dᶜ ↔ ‖p.1‖ = 1 ∧ 0 < p.2 := by
      intro p hp
      change Ψ (p.1, -p.2) ∈ e '' Dᶜ ↔ ‖p.1‖ = 1 ∧ 0 < p.2
      simpa only [hJ, neg_neg] using hret (J p) ((hJU p).mpr hp)
    have hUeq : Ψ' '' U = Ψ '' U := by
      ext y
      constructor
      · rintro ⟨p, hp, rfl⟩
        exact ⟨J p, (hJU p).mpr hp, rfl⟩
      · rintro ⟨p, hp, rfl⟩
        refine ⟨J p, (hJU p).mpr hp, ?_⟩
        change Ψ (J (J p)) = Ψ p
        rw [hJJ]
    have hTeq : Ψ' '' {p : E × ℝ | p ∈ U ∧
        Real.smoothAbs ε (1 - ‖p.1‖ ^ 2 - p.2) = 1 - ‖p.1‖ ^ 2 + p.2} =
        Ψ '' {p : E × ℝ | p ∈ U ∧
          Real.smoothAbs ε (1 - ‖p.1‖ ^ 2 - -p.2) = 1 - ‖p.1‖ ^ 2 + -p.2} := by
      ext y
      constructor
      · rintro ⟨p, hp, rfl⟩
        exact ⟨J p, ⟨(hJU p).mpr hp.1, by simpa only [hJ, neg_neg] using hp.2⟩, rfl⟩
      · rintro ⟨p, hp, rfl⟩
        refine ⟨J p, ⟨(hJU p).mpr hp.1, ?_⟩, ?_⟩
        · simpa only [hJ] using hp.2
        · change Ψ (J (J p)) = Ψ p
          rw [hJJ]
    obtain ⟨Φ, hΦ, K, hK, hKU, hfixΦ, hfixΦi⟩ :=
      exists_replacement_rounding_of_pos Ψ' χ hR ha hab hε hε1 hεb hχD hcap' hfix hret'
    refine ⟨Φ, ?_, K, hK, ?_, hfixΦ, hfixΦi⟩
    · change range (Φ ∘ f) = (range f \ Ψ '' U) ∪ _
      change range (Φ ∘ f) = (range f \ Ψ' '' U) ∪ _ at hΦ
      rw [hUeq, hTeq] at hΦ
      exact hΦ
    · exact hUeq ▸ hKU

theorem exists_flat_cap_rounding
    {X E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {e f g : X → F} (Ψ : (E × ℝ) ≃ₘ[ℝ] F) (χ : E → X)
    {D : Set X} {R b a ε σ : ℝ} (hR : 1 < R) (ha : 0 < a) (hab : a < b)
    (hε : 0 < ε) (hε1 : ε < 1) (hεb : ε < b) (hσ : σ = 1 ∨ σ = -1)
    (hχD : χ '' closedBall (0 : E) 1 = D)
    (hcap : ∀ x ∈ closedBall (0 : E) 1,
      f (χ x) = Ψ (EuclideanGeometry.cylinderCap (σ * a) x))
    (hflat : ∀ x ∈ closedBall (0 : E) 1, g (χ x) = Ψ (x, 0))
    (hfix : EqOn f e Dᶜ) (hgfix : EqOn g e Dᶜ)
    (hret : ∀ p ∈ ball (0 : E) R ×ˢ Ioo (-b) b,
      Ψ p ∈ e '' Dᶜ ↔ ‖p.1‖ = 1 ∧ 0 < σ * p.2) :
    ∃ Φ : F ≃ₘ[ℝ] F,
      range (Φ ∘ f) =
        (range g \ Ψ '' (ball (0 : E) R ×ˢ Ioo (-b) b)) ∪
        Ψ '' {p : E × ℝ | p ∈ ball 0 R ×ˢ Ioo (-b) b ∧
          Real.smoothAbs ε (1 - ‖p.1‖ ^ 2 - σ * p.2) = 1 - ‖p.1‖ ^ 2 + σ * p.2} ∧
      ∃ K : Set F, IsCompact K ∧
        K ⊆ Ψ '' (ball (0 : E) R ×ˢ Ioo (-b) b) ∧
        EqOn Φ id Kᶜ ∧ EqOn Φ.symm id Kᶜ := by
  let U := ball (0 : E) R ×ˢ Ioo (-b) b
  have hb : 0 < b := ha.trans hab
  have hcapU (x : E) (hx : x ∈ closedBall 0 1) :
      EuclideanGeometry.cylinderCap (σ * a) x ∈ U := by
    have hn := mem_closedBall_zero_iff.mp hx
    have ht := EuclideanGeometry.cylinderCap_snd_mem_Icc ha.le hn
    refine ⟨mem_ball_zero_iff.mpr ((EuclideanGeometry.norm_cylinderCap_fst_le_one _ _).trans_lt hR), ?_⟩
    rcases hσ with rfl | rfl
    · simp only [one_mul]
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    · simp only [neg_one_mul, EuclideanGeometry.cylinderCap_neg]
      exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hd (x : X) (hx : x ∈ D) : f x ∈ Ψ '' U ∧ g x ∈ Ψ '' U := by
    obtain ⟨y, hy, rfl⟩ := hχD.symm.subset hx
    constructor
    · exact ⟨_, hcapU y hy, (hcap y hy).symm⟩
    · exact ⟨(y, 0), ⟨closedBall_subset_ball hR hy, by linarith, hb⟩, (hflat y hy).symm⟩
  have houter : range f \ Ψ '' U = range g \ Ψ '' U := by
    ext y
    constructor
    · rintro ⟨⟨x, rfl⟩, hn⟩
      have hx : x ∈ Dᶜ := fun hx => hn (hd x hx).1
      exact ⟨⟨x, (hgfix hx).trans (hfix hx).symm⟩, hn⟩
    · rintro ⟨⟨x, rfl⟩, hn⟩
      have hx : x ∈ Dᶜ := fun hx => hn (hd x hx).2
      exact ⟨⟨x, (hfix hx).trans (hgfix hx).symm⟩, hn⟩
  obtain ⟨Φ, hΦ, hK⟩ :=
    exists_cylinderCap_replacement_rounding Ψ χ hR ha hab hε hε1 hεb hσ hχD hcap hfix hret
  exact ⟨Φ, houter ▸ hΦ, hK⟩

end Diffeomorph
