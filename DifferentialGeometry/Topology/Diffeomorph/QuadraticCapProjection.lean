import DifferentialGeometry.Topology.Diffeomorph.HeightReparametrization
import DifferentialGeometry.Analysis.ODE.QuadraticLevelScaling

open Set Metric
open scoped ContDiff Manifold
open DifferentialGeometry.Analysis.ODE

namespace Diffeomorph

private theorem cap_inverse_on_cylinder
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D T : (E × ℝ) ≃ₘ[ℝ] (E × ℝ)) (G : E ≃ₘ[ℝ] E)
    (H : ℝ → E ≃ₘ[ℝ] E) {b m : ℝ}
    (hD : ∀ t ≤ b, ∀ x, D (quadraticLevelScaling b m x t, t) = (H t x, t))
    (hT : ∀ z, T z = (G ((H z.2).symm z.1), z.2)) :
    ∀ t ≤ b, ∀ y, (D.trans T).symm (y, t) =
      (quadraticLevelScaling b m (G.symm y) t, t) := by
  intro t ht y
  apply (D.trans T).injective
  change (D.trans T) ((D.trans T).symm (y, t)) = (D.trans T) _
  rw [(D.trans T).apply_symm_apply]
  change (y, t) = T (D (quadraticLevelScaling b m (G.symm y) t, t))
  rw [hD t ht, hT]
  simp only [(H t).symm_apply_apply, G.apply_symm_apply]

theorem exists_exp_projection_quadratic_cylinder
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D T : (E × ℝ) ≃ₘ[ℝ] (E × ℝ)) (G : E ≃ₘ[ℝ] E)
    (H : ℝ → E ≃ₘ[ℝ] E) {a d b m r μ : ℝ}
    (had : a < d) (hdb : d ≤ b) (hbm : b < m) (hμ : 0 < μ)
    (hr : r ^ 2 = 2 * (m - b))
    (hDh : ∀ z, (D z).2 = z.2)
    (hD : ∀ t ≤ b, ∀ x, D (quadraticLevelScaling b m x t, t) = (H t x, t))
    (hT : ∀ z, T z = (G ((H z.2).symm z.1), z.2)) :
    ∃ (Q : (E × ℝ) ≃ₘ[ℝ] (E × ℝ)) (ψ : ℝ ≃ₘ[ℝ] ℝ) (α : ℝ),
      0 < α ∧ (∀ t, 0 < deriv ψ t) ∧
      (∀ t, d ≤ t → ψ t = t) ∧
      (∀ p, (Q p).2 = ψ p.2) ∧
      (∀ t ≤ a, ∀ y, Q (y, t) = ((α * Real.exp (-μ * t)) • G.symm y, ψ t)) ∧
      (∀ p, d ≤ p.2 → Q p = (D.trans T).symm p) ∧
      Q '' ((G '' sphere 0 r) ×ˢ Iic b) ⊆
        {p : E × ℝ | p.2 = m - ‖p.1‖ ^ 2 / 2} ∧
      Q '' ((D.trans T) '' {p : E × ℝ | b ≤ p.2 ∧ p.2 = m - ‖p.1‖ ^ 2 / 2}) =
        {p : E × ℝ | b ≤ p.2 ∧ p.2 = m - ‖p.1‖ ^ 2 / 2} ∧
      ∀ t ≤ b, ∀ y, Q (y, t) =
        (quadraticLevelScaling b m (G.symm y) (ψ t), ψ t) := by
  obtain ⟨ψ, hψd, hψlo, hψhi⟩ :=
    exists_eq_exponential_on_Iic
      had (hdb.trans_lt hbm) hμ
  let J : (E × ℝ) ≃ₘ[ℝ] (E × ℝ) :=
    { toEquiv := Equiv.prodCongr (Equiv.refl E) ψ.toEquiv
      contMDiff_toFun := (contDiff_fst.prodMk (ψ.contDiff.comp contDiff_snd)).contMDiff
      contMDiff_invFun := (contDiff_fst.prodMk (ψ.symm.contDiff.comp contDiff_snd)).contMDiff }
  let P := (D.trans T).symm
  let Q := J.trans P
  have hPh (p : E × ℝ) : (P p).2 = p.2 := by
    have he := (D.trans T).apply_symm_apply p
    have ht := congrArg Prod.snd he
    change (T (D (P p))).2 = p.2 at ht
    rw [hT, hDh] at ht
    exact ht
  have hQh (p : E × ℝ) : (Q p).2 = ψ p.2 := hPh (J p)
  have hfix (p : E × ℝ) (hp : d ≤ p.2) : Q p = P p := by
    change P (p.1, ψ p.2) = P p
    rw [hψhi p.2 hp]
  have hψb (t : ℝ) (ht : t ≤ b) : ψ t ≤ b := by
    have hle := (strictMono_of_deriv_pos hψd).monotone ht
    rwa [hψhi b hdb] at hle
  let α := Real.sqrt ((m - a + 1) / (m - b)) * Real.exp (μ * d)
  have hα : 0 < α := mul_pos (Real.sqrt_pos.mpr (div_pos (by linarith) (sub_pos.mpr hbm)))
    (Real.exp_pos _)
  have hlow (t : ℝ) (ht : t ≤ a) (y : E) :
      Q (y, t) = ((α * Real.exp (-μ * t)) • G.symm y, ψ t) := by
    change P (y, ψ t) = _
    rw [cap_inverse_on_cylinder D T G H hD hT (ψ t) (hψb t (ht.trans (had.le.trans hdb)))]
    congr 1
    dsimp only [quadraticLevelScaling]
    congr 1
    have hrati : (ψ t - m) / (b - m) =
        (m - a + 1) / (m - b) * (Real.exp (μ * d) * Real.exp (-μ * t)) ^ 2 := by
      rw [hψlo t ht]
      rw [← Real.exp_add, ← Real.exp_nat_mul]
      have he : -2 * μ * (t - d) = 2 * (μ * d + -μ * t) := by ring_nf
      rw [he]
      field_simp [sub_ne_zero.mpr hbm.ne, sub_ne_zero.mpr hbm.ne']
      ring_nf
    rw [hrati, Real.sqrt_mul (div_nonneg (by linarith) (sub_nonneg.mpr hbm.le)),
      Real.sqrt_sq (mul_pos (Real.exp_pos _) (Real.exp_pos _)).le]
    dsimp only [α]
    ring_nf
  refine ⟨Q, ψ, α, hα, hψd, hψhi, hQh, hlow, hfix, ?_, ?_, ?_⟩
  · rintro p ⟨⟨y, t⟩, ⟨⟨x, hx, rfl⟩, ht⟩, rfl⟩
    change (P (G x, ψ t)).2 = m - ‖(P (G x, ψ t)).1‖ ^ 2 / 2
    rw [cap_inverse_on_cylinder D T G H hD hT (ψ t) (hψb t ht), G.symm_apply_apply]
    have hnorm : ‖x‖ = r := mem_sphere_zero_iff_norm.mp hx
    have hs := norm_sq_quadraticLevelScaling b m x (t := ψ t)
      (div_nonneg_of_nonpos (by linarith [hψb t ht] : ψ t - m ≤ 0) (sub_neg.mpr hbm).le)
    rw [hnorm, hr] at hs
    have hsq : ‖quadraticLevelScaling b m x (ψ t)‖ ^ 2 = 2 * (m - ψ t) := by
      rw [hs]
      field_simp [sub_ne_zero.mpr hbm.ne]
      ring_nf
    change ψ t = m - ‖quadraticLevelScaling b m x (ψ t)‖ ^ 2 / 2
    rw [hsq]
    ring_nf
  · have hpoint (p : E × ℝ) (hp : b ≤ p.2) : Q ((D.trans T) p) = p := by
      rw [hfix _ (by change d ≤ (T (D p)).2; rw [hT, hDh]; exact hdb.trans hp)]
      exact (D.trans T).symm_apply_apply p
    ext p
    constructor
    · rintro ⟨q, ⟨z, hz, rfl⟩, rfl⟩
      rwa [hpoint z hz.1]
    · intro hp
      exact ⟨(D.trans T) p, mem_image_of_mem _ hp, hpoint p hp.1⟩
  · intro t ht y
    exact cap_inverse_on_cylinder D T G H hD hT (ψ t) (hψb t ht) y


private theorem quadraticLevelScaling_image_sphere_eq_height_level
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {b m r t : ℝ} (hbm : b < m) (hr : 0 ≤ r) (hrsq : r ^ 2 = 2 * (m - b))
    (ht : t ≤ b) :
    (fun x : E => quadraticLevelScaling b m x t) '' sphere 0 r =
      {x : E | t = m - ‖x‖ ^ 2 / 2} := by
  have hratio : 0 < (t - m) / (b - m) :=
    div_pos_of_neg_of_neg (sub_neg.mpr (ht.trans_lt hbm)) (sub_neg.mpr hbm)
  rw [quadraticLevelScaling_image_sphere b m hratio r]
  have hsquare : (Real.sqrt ((t - m) / (b - m)) * r) ^ 2 = 2 * (m - t) := by
    rw [mul_pow, Real.sq_sqrt hratio.le, hrsq]
    field_simp [sub_ne_zero.mpr hbm.ne]
    ring
  ext x
  simp only [mem_sphere_zero_iff_norm, mem_ofPred_eq]
  constructor
  · intro hx
    rw [← hx] at hsquare
    linarith
  · intro hx
    apply (sq_eq_sq₀ (norm_nonneg x) (mul_nonneg (Real.sqrt_nonneg _) hr)).mp
    rw [hsquare]
    linarith

theorem image_reference_cylinder
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Q : E × ℝ → E × ℝ) (G : E ≃ E) (ψ : ℝ ≃ ℝ)
    {b m r j : ℝ} (hbm : b < m) (hr : 0 ≤ r) (hrsq : r ^ 2 = 2 * (m - b))
    (hψ : StrictMono ψ) (hψb : ψ b = b)
    (hQ : ∀ t ≤ b, ∀ y, Q (y, t) =
      (quadraticLevelScaling b m (G.symm y) (ψ t), ψ t)) :
    Q '' ((G '' sphere 0 r) ×ˢ Icc j b) =
      {p : E × ℝ | ψ j ≤ p.2 ∧ p.2 ≤ b ∧ p.2 = m - ‖p.1‖ ^ 2 / 2} := by
  ext p
  constructor
  · rintro ⟨⟨y, t⟩, ⟨⟨x, hx, rfl⟩, ht⟩, rfl⟩
    have hψtb : ψ t ≤ b := by simpa only [hψb] using hψ.monotone ht.2
    rw [hQ t ht.2, G.symm_apply_apply]
    refine ⟨hψ.monotone ht.1, hψtb, ?_⟩
    exact (quadraticLevelScaling_image_sphere_eq_height_level hbm hr hrsq hψtb).subset
      (mem_image_of_mem _ hx)
  · rintro ⟨hpj, hpb, hplevel⟩
    have ht : ψ.symm p.2 ∈ Icc j b := by
      constructor
      · exact hψ.le_iff_le.mp (by simpa only [ψ.apply_symm_apply] using hpj)
      · exact hψ.le_iff_le.mp (by simpa only [ψ.apply_symm_apply, hψb] using hpb)
    obtain ⟨x, hx, hxscale⟩ :=
      (quadraticLevelScaling_image_sphere_eq_height_level hbm hr hrsq hpb).symm.subset hplevel
    change quadraticLevelScaling b m x p.2 = p.1 at hxscale
    refine ⟨(G x, ψ.symm p.2), ⟨mem_image_of_mem _ hx, ht⟩, ?_⟩
    rw [hQ _ ht.2, G.symm_apply_apply, ψ.apply_symm_apply, hxscale]

theorem image_reference_cylinder_union_cap
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Q : E × ℝ → E × ℝ) (G : E ≃ E) (ψ : ℝ ≃ ℝ)
    {b m r j : ℝ} (hbm : b < m) (hr : 0 ≤ r) (hrsq : r ^ 2 = 2 * (m - b))
    (hjb : j ≤ b) (hψ : StrictMono ψ) (hψb : ψ b = b)
    (hQ : ∀ t ≤ b, ∀ y, Q (y, t) =
      (quadraticLevelScaling b m (G.symm y) (ψ t), ψ t))
    {U : Set (E × ℝ)}
    (hcap : Q '' U = {p : E × ℝ | b ≤ p.2 ∧ p.2 = m - ‖p.1‖ ^ 2 / 2}) :
    Q '' (((G '' sphere 0 r) ×ˢ Icc j b) ∪ U) =
      {p : E × ℝ | ψ j ≤ p.2 ∧ p.2 = m - ‖p.1‖ ^ 2 / 2} := by
  have hψjb : ψ j ≤ b := by simpa only [hψb] using hψ.monotone hjb
  have hcylinder := image_reference_cylinder Q G ψ hbm hr hrsq hψ hψb hQ (j := j)
  rw [image_union, hcylinder, hcap]
  ext p
  constructor
  · rintro (⟨hpj, _, hplevel⟩ | ⟨hpb, hplevel⟩)
    · exact ⟨hpj, hplevel⟩
    · exact ⟨hψjb.trans hpb, hplevel⟩
  · rintro ⟨hpj, hplevel⟩
    rcases le_total p.2 b with hpb | hbp
    · exact Or.inl ⟨hpj, hpb, hplevel⟩
    · exact Or.inr ⟨hbp, hplevel⟩


theorem injOn_fst_of_exponential_formula
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : E ≃ₘ[ℝ] E) (Q : (E × ℝ) ≃ₘ[ℝ] (E × ℝ)) (ψ : ℝ ≃ₘ[ℝ] ℝ)
    (f : X → E) {α μ ℓ a : ℝ} (hα : α ≠ 0)
    (hQ : ∀ t ≤ ℓ + a, ∀ y, Q (y, t) = ((α * Real.exp (-μ * t)) • G.symm y, ψ t))
    {K : Set (X × ℝ)} (htime : ∀ p ∈ K, p.2 ≤ a)
    (hinj : InjOn (fun p : X × ℝ => Real.exp (-μ * p.2) • G.symm (f p.1)) K) :
    InjOn (fun p : X × ℝ => (Q (f p.1, ℓ + p.2)).1) K := by
  have hformula (p : X × ℝ) (hp : p ∈ K) :
      (Q (f p.1, ℓ + p.2)).1 =
        (α * Real.exp (-μ * ℓ)) • (Real.exp (-μ * p.2) • G.symm (f p.1)) := by
    rw [hQ (ℓ + p.2) (by linarith [htime p hp])]
    change (α * Real.exp (-μ * (ℓ + p.2))) • _ = _
    rw [show -μ * (ℓ + p.2) = -μ * ℓ + -μ * p.2 by ring,
      Real.exp_add, smul_smul, mul_assoc]
  intro p hp q hq heq
  apply hinj hp hq
  change (Q (f p.1, ℓ + p.2)).1 = (Q (f q.1, ℓ + q.2)).1 at heq
  rw [hformula p hp, hformula q hq] at heq
  exact smul_right_injective E (mul_ne_zero hα (Real.exp_ne_zero _)) heq


theorem exists_isOpen_graph_image_of_exponential_formula
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : E ≃ₘ[ℝ] E) (Q : (E × ℝ) ≃ₘ[ℝ] (E × ℝ)) (ψ : ℝ ≃ₘ[ℝ] ℝ)
    {k μ ℓ a : ℝ} (hk : k ≠ 0)
    (hQ : ∀ q : E × ℝ, q.2 < a →
      Q q = (k • (Real.exp (-μ * (q.2 - ℓ)) • G.symm q.1), ψ q.2))
    {O : Set E} (hO : IsOpen O) {g : E → ℝ} (hg : ContDiffOn ℝ ∞ g O)
    {W : Set (E × ℝ)} (hW : IsOpen W) (hWO : W ⊆ {p | p.1 ∈ O})
    {Z S K : Set (E × ℝ)} (hZ : IsOpen Z)
    (hgraph : ∀ q ∈ Z, (Real.exp (-μ * (q.2 - ℓ)) • G.symm q.1, q.2 - ℓ) ∈ W →
      (q ∈ S ↔ q.2 - ℓ = g (Real.exp (-μ * (q.2 - ℓ)) • G.symm q.1)))
    (hKZ : K ⊆ Z) (hKa : ∀ q ∈ K, q.2 < a)
    (hKW : ∀ q ∈ K, (Real.exp (-μ * (q.2 - ℓ)) • G.symm q.1, q.2 - ℓ) ∈ W) :
    ∃ O' : Set E, IsOpen O' ∧ ∃ g' : E → ℝ, ContDiffOn ℝ ∞ g' O' ∧
      ∃ W' : Set (E × ℝ), IsOpen W' ∧ Q '' K ⊆ W' ∧ W' ⊆ Q '' Z ∧
        W' ⊆ {p | p.1 ∈ O'} ∧
        W' ∩ Q '' S = W' ∩ {p | p.2 = g' p.1} := by
  let P : E × ℝ → E × ℝ := fun q =>
    (Real.exp (-μ * (q.2 - ℓ)) • G.symm q.1, q.2 - ℓ)
  have hP : Continuous P := by dsimp [P]; fun_prop
  let V : Set (E × ℝ) := Z ∩ ({q : E × ℝ | q.2 < a} ∩ P ⁻¹' W)
  have hV : IsOpen V := hZ.inter ((isOpen_lt continuous_snd continuous_const).inter (hW.preimage hP))
  let O' : Set E := {x | k⁻¹ • x ∈ O}
  let g' : E → ℝ := fun x => ψ (ℓ + g (k⁻¹ • x))
  have hO' : IsOpen O' := hO.preimage (continuous_const.smul continuous_id)
  have hg' : ContDiffOn ℝ ∞ g' O' := ψ.contDiff.comp_contDiffOn
    (contDiffOn_const.add (hg.comp (contDiff_const.smul contDiff_id).contDiffOn (fun _ hx => hx)))
  refine ⟨O', hO', g', hg', Q '' V, Q.toHomeomorph.isOpenMap _ hV, ?_, ?_, ?_, ?_⟩
  · exact image_mono (fun q hq => ⟨hKZ hq, hKa q hq, hKW q hq⟩)
  · exact image_mono inter_subset_left
  · rintro _ ⟨q, hq, rfl⟩
    change k⁻¹ • (Q q).1 ∈ O
    rw [hQ q hq.2.1]
    simpa only [P, mem_ofPred_eq, inv_smul_smul₀ hk] using hWO hq.2.2
  · ext p
    constructor
    · rintro ⟨hp, hS⟩
      obtain ⟨q, hq, rfl⟩ := hp
      have hqS : q ∈ S := Q.injective.mem_set_image.mp hS
      have heq := (hgraph q hq.1 hq.2.2).mp hqS
      refine ⟨mem_image_of_mem Q hq, ?_⟩
      change (Q q).2 = ψ (ℓ + g (k⁻¹ • (Q q).1))
      rw [hQ q hq.2.1]
      simp only [inv_smul_smul₀ hk]
      rw [← heq, add_sub_cancel]
    · rintro ⟨hp, heq⟩
      obtain ⟨q, hq, rfl⟩ := hp
      refine ⟨mem_image_of_mem Q hq, mem_image_of_mem Q ?_⟩
      apply (hgraph q hq.1 hq.2.2).mpr
      change (Q q).2 = ψ (ℓ + g (k⁻¹ • (Q q).1)) at heq
      rw [hQ q hq.2.1] at heq
      simp only [inv_smul_smul₀ hk] at heq
      have he := ψ.injective heq
      linarith


private theorem quadraticLevelScaling_height_le_of_le_norm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {b m r t : ℝ} (hbm : b < m) (hr : 0 ≤ r) (hrsq : r ^ 2 = 2 * (m - b))
    (ht : t ≤ b) {x : E} (hx : r ≤ ‖x‖) :
    m - ‖quadraticLevelScaling b m x t‖ ^ 2 / 2 ≤ t := by
  have hratio : 0 ≤ (t - m) / (b - m) :=
    (div_pos_of_neg_of_neg (sub_neg.mpr (ht.trans_lt hbm)) (sub_neg.mpr hbm)).le
  have hsquare : r ^ 2 ≤ ‖x‖ ^ 2 := by
    nlinarith only [mul_self_le_mul_self hr hx]
  have hle := mul_le_mul_of_nonneg_left hsquare hratio
  have heq : (t - m) / (b - m) * (2 * (m - b)) = 2 * (m - t) := by
    field_simp [sub_ne_zero.mpr hbm.ne]
    ring
  rw [hrsq, heq, ← norm_sq_quadraticLevelScaling b m x hratio] at hle
  linarith

theorem injOn_projection_union_quadratic_cap
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Q : E × ℝ → E × ℝ) (hQi : Function.Injective Q) (g : E → E)
    {ψ : ℝ → ℝ} {b m r j : ℝ}
    (hbm : b < m) (hr : 0 ≤ r) (hrsq : r ^ 2 = 2 * (m - b))
    (hjb : j ≤ b) (hψ : Monotone ψ) (hψb : ψ b = b)
    (hQ : ∀ t ≤ b, ∀ y, Q (y, t) = (quadraticLevelScaling b m (g y) (ψ t), ψ t))
    {K U : Set (E × ℝ)} (hK : ∀ q ∈ K, q.2 ≤ j ∧ r ≤ ‖g q.1‖)
    (hproj : InjOn (fun q => (Q q).1) K)
    (hcap : Q '' U ⊆ {p : E × ℝ | ψ j ≤ p.2 ∧ p.2 = m - ‖p.1‖ ^ 2 / 2}) :
    InjOn (fun q => (Q q).1) (K ∪ U) := by
  have hbound (q : E × ℝ) (hq : q ∈ K) :
      m - ‖(Q q).1‖ ^ 2 / 2 ≤ (Q q).2 ∧ (Q q).2 ≤ ψ j := by
    have hqt := (hK q hq).1.trans hjb
    have hψt : ψ q.2 ≤ b := by simpa only [hψb] using hψ hqt
    rcases q with ⟨y, t⟩
    rw [hQ t hqt y]
    exact ⟨quadraticLevelScaling_height_le_of_le_norm hbm hr hrsq hψt (hK (y, t) hq).2,
      hψ (hK (y, t) hq).1⟩
  have hupper (q : E × ℝ) (hq : q ∈ U) :
      ψ j ≤ (Q q).2 ∧ (Q q).2 = m - ‖(Q q).1‖ ^ 2 / 2 :=
    hcap (mem_image_of_mem Q hq)
  have hcross (q : E × ℝ) (hq : q ∈ K) (w : E × ℝ) (hw : w ∈ U)
      (heq : (Q q).1 = (Q w).1) : q = w := by
    obtain ⟨hqlo, hqhi⟩ := hbound q hq
    obtain ⟨hwlo, hweq⟩ := hupper w hw
    apply hQi
    apply Prod.ext heq
    rw [heq] at hqlo
    linarith
  intro q hq w hw heq
  change (Q q).1 = (Q w).1 at heq
  rcases hq with hq | hq <;> rcases hw with hw | hw
  · exact hproj hq hw heq
  · exact hcross q hq w hw heq
  · exact (hcross w hw q hq heq.symm).symm
  · apply hQi
    apply Prod.ext heq
    rw [(hupper q hq).2, (hupper w hw).2, heq]

theorem injOn_projection_union_quadratic_cap_of_disjoint_interior
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Q : E × ℝ → E × ℝ) (hQi : Function.Injective Q) (G : E ≃ₘ[ℝ] E)
    {ψ : ℝ → ℝ} {a b m r j : ℝ}
    (hbm : b < m) (hr : 0 ≤ r) (hrsq : r ^ 2 = 2 * (m - b))
    (hjb : j ≤ b) (hψ : Monotone ψ) (hψb : ψ b = b)
    (hQ : ∀ t ≤ b, ∀ y, Q (y, t) = (quadraticLevelScaling b m (G.symm y) (ψ t), ψ t))
    {K U : Set (E × ℝ)} (htime : ∀ q ∈ K, q.2 ∈ Icc a j)
    (hclear : Disjoint K (interior (G '' closedBall 0 r) ×ˢ Icc a j))
    (hproj : InjOn (fun q => (Q q).1) K)
    (hcap : Q '' U ⊆ {p : E × ℝ | ψ j ≤ p.2 ∧ p.2 = m - ‖p.1‖ ^ 2 / 2}) :
    InjOn (fun q => (Q q).1) (K ∪ U) := by
  apply injOn_projection_union_quadratic_cap Q hQi G.symm hbm hr hrsq hjb hψ hψb hQ _ hproj hcap
  intro q hq
  refine ⟨(htime q hq).2, ?_⟩
  by_contra hn
  have hinside : q.1 ∈ interior (G '' closedBall 0 r) := by
    apply interior_maximal (image_mono ball_subset_closedBall)
      (G.toHomeomorph.isOpenMap _ isOpen_ball)
    exact ⟨G.symm q.1, mem_ball_zero_iff.mpr (lt_of_not_ge hn), G.apply_symm_apply q.1⟩
  exact Set.disjoint_left.mp hclear hq ⟨hinside, htime q hq⟩

theorem symm_apply_fst_height_of_exponential_formula
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : E ≃ₘ[ℝ] E) (Q : (E × ℝ) ≃ₘ[ℝ] (E × ℝ)) (ψ : ℝ → ℝ)
    {α μ a s t : ℝ}
    (hQ : ∀ v ≤ a, ∀ y, Q (y, v) = ((α * Real.exp (-μ * v)) • G.symm y, ψ v))
    (hs : s ≤ a) (ht : t ≤ a) (y : E) :
    Q.symm ((Q (y, s)).1, ψ t) = (G (Real.exp (μ * (t - s)) • G.symm y), t) := by
  apply Q.injective
  change Q (Q.symm ((Q (y, s)).1, ψ t)) = Q (G (Real.exp (μ * (t - s)) • G.symm y), t)
  rw [Q.apply_symm_apply, hQ t ht, G.symm_apply_apply, hQ s hs]
  refine Prod.ext ?_ rfl
  change (α * Real.exp (-μ * s)) • G.symm y =
    (α * Real.exp (-μ * t)) • (Real.exp (μ * (t - s)) • G.symm y)
  rw [smul_smul, mul_assoc, ← Real.exp_add,
    show -μ * t + μ * (t - s) = -μ * s by ring]

theorem disjoint_vertical_trace_of_quadratic_cap
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P Q : (E × ℝ) ≃ₘ[ℝ] (E × ℝ)) (G : E ≃ₘ[ℝ] E) (ψ : ℝ ≃ₘ[ℝ] ℝ)
    {a b m r : ℝ} (hbm : b < m) (hr : 0 < r) (hrsq : r ^ 2 = 2 * (m - b))
    (hψ : StrictMono ψ) (hψb : ψ b = b)
    (hQheight : ∀ z, (Q z).2 = ψ z.2)
    (hQfull : ∀ t ≤ b, ∀ y, Q (y, t) =
      (quadraticLevelScaling b m (G.symm y) (ψ t), ψ t))
    (hQhi : ∀ z, b ≤ z.2 → Q z = P.symm z)
    {S : Set (E × ℝ)}
    (hlower : Disjoint S (interior (G '' closedBall 0 r) ×ˢ Icc a b))
    (hupper : Disjoint S (P '' {z : E × ℝ | b ≤ z.2 ∧ z.2 < m - ‖z.1‖ ^ 2 / 2})) :
    ∀ q : E × ℝ, (Q q).2 = m - ‖(Q q).1‖ ^ 2 / 2 →
      ∀ t ∈ Ico a q.2, Q.symm ((Q q).1, ψ t) ∉ S := by
  intro q hq t ht
  let w := Q.symm ((Q q).1, ψ t)
  have hQw : Q w = ((Q q).1, ψ t) := Q.apply_symm_apply _
  have hwtime : w.2 = t := hψ.injective
    ((hQheight w).symm.trans (congrArg Prod.snd hQw))
  have hbelow : ψ t < m - ‖(Q q).1‖ ^ 2 / 2 := by
    rw [← hq, hQheight]
    exact hψ ht.2
  by_cases htb : t ≤ b
  · have hψtb : ψ t ≤ b := by simpa only [hψb] using hψ.monotone htb
    have hscale : quadraticLevelScaling b m (G.symm w.1) (ψ t) = (Q q).1 := by
      have hw : w = (w.1, t) := Prod.ext rfl hwtime
      rw [hw, hQfull t htb] at hQw
      exact congrArg Prod.fst hQw
    have hnorm : ‖G.symm w.1‖ < r := by
      by_contra hn
      have hle := quadraticLevelScaling_height_le_of_le_norm hbm hr.le hrsq hψtb (le_of_not_gt hn)
      rw [hscale] at hle
      exact hbelow.not_ge hle
    intro hwS
    apply disjoint_left.mp hlower hwS
    refine ⟨?_, ?_, ?_⟩
    · change w.1 ∈ interior (G.toHomeomorph '' closedBall 0 r)
      rw [← G.toHomeomorph.image_interior, interior_closedBall (0 : E) hr.ne']
      exact ⟨G.symm w.1, mem_ball_zero_iff.mpr hnorm, G.apply_symm_apply w.1⟩
    · change a ≤ w.2
      rw [hwtime]
      exact ht.1
    · change w.2 ≤ b
      rw [hwtime]
      exact htb
  · have hbw : b ≤ w.2 := by rw [hwtime]; exact (lt_of_not_ge htb).le
    have hrepr : P ((Q q).1, ψ t) = w := by
      rw [← hQw, hQhi w hbw, P.apply_symm_apply]
    intro hwS
    apply disjoint_left.mp hupper hwS
    refine ⟨((Q q).1, ψ t), ⟨?_, hbelow⟩, hrepr⟩
    simpa only [hψb] using hψ.monotone (lt_of_not_ge htb).le

theorem image_projection_reference_cylinder
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Q : (E × ℝ) ≃ₘ[ℝ] (E × ℝ)) (G : E ≃ E) (ψ : ℝ ≃ ℝ)
    {a d b m r : ℝ} (hdb : d ≤ b)
    (hbm : b < m) (hr : 0 ≤ r) (hrsq : r ^ 2 = 2 * (m - b))
    (hψ : StrictMono ψ) (hψb : ψ b = b)
    (hQfull : ∀ t ≤ b, ∀ y, Q (y, t) =
      (quadraticLevelScaling b m (G.symm y) (ψ t), ψ t))
    (A : Set E) :
    (fun z : E × ℝ => (Q z).1) '' ((G '' sphere 0 r \ A) ×ˢ Ioo a d) =
      {y | ψ a < m - ‖y‖ ^ 2 / 2 ∧ m - ‖y‖ ^ 2 / 2 < ψ d ∧
        (Q.symm (y, m - ‖y‖ ^ 2 / 2)).1 ∉ A} := by
  have hψdb : ψ d ≤ b := by simpa only [hψb] using hψ.monotone hdb
  have himage := image_reference_cylinder Q G ψ hbm hr hrsq hψ hψb hQfull (j := a)
  have hQheight (z : E × ℝ) (hz : z.2 ≤ b) : (Q z).2 = ψ z.2 :=
    congrArg Prod.snd (hQfull z.2 hz z.1)
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hlevel : (Q z).2 = m - ‖(Q z).1‖ ^ 2 / 2 :=
      (himage.subset ⟨z, ⟨hz.1.1, hz.2.1.le, hz.2.2.le.trans hdb⟩, rfl⟩).2.2
    change ψ a < m - ‖(Q z).1‖ ^ 2 / 2 ∧ m - ‖(Q z).1‖ ^ 2 / 2 < ψ d ∧
      (Q.symm ((Q z).1, m - ‖(Q z).1‖ ^ 2 / 2)).1 ∉ A
    rw [← hlevel]
    refine ⟨?_, ?_, ?_⟩
    · rw [hQheight z (hz.2.2.le.trans hdb)]
      exact hψ hz.2.1
    · rw [hQheight z (hz.2.2.le.trans hdb)]
      exact hψ hz.2.2
    · simpa only [Prod.eta, Q.symm_apply_apply] using hz.1.2
  · intro hy
    obtain ⟨z, hz, hQz⟩ := himage.symm.subset
      (show (y, m - ‖y‖ ^ 2 / 2) ∈ {p : E × ℝ |
          ψ a ≤ p.2 ∧ p.2 ≤ b ∧ p.2 = m - ‖p.1‖ ^ 2 / 2}
        from ⟨hy.1.le, hy.2.1.le.trans hψdb, rfl⟩)
    have htime : ψ z.2 = m - ‖y‖ ^ 2 / 2 :=
      (hQheight z hz.2.2).symm.trans (congrArg Prod.snd hQz)
    have hzA : z.1 ∉ A := by
      have hsymm : Q.symm (y, m - ‖y‖ ^ 2 / 2) = z := by rw [← hQz, Q.symm_apply_apply]
      rw [← hsymm]
      exact hy.2.2
    have hzt : z.2 ∈ Ioo a d := by
      constructor
      · exact hψ.lt_iff_lt.mp (by rw [htime]; exact hy.1)
      · exact hψ.lt_iff_lt.mp (by rw [htime]; exact hy.2.1)
    exact ⟨z, ⟨⟨hz.1, hzA⟩, hzt⟩, congrArg Prod.fst hQz⟩

theorem isOpen_image_projection_reference_cylinder
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Q : (E × ℝ) ≃ₘ[ℝ] (E × ℝ)) (G : E ≃ E) (ψ : ℝ ≃ ℝ)
    {a d b m r : ℝ} (hdb : d ≤ b)
    (hbm : b < m) (hr : 0 ≤ r) (hrsq : r ^ 2 = 2 * (m - b))
    (hψ : StrictMono ψ) (hψb : ψ b = b)
    (hQfull : ∀ t ≤ b, ∀ y, Q (y, t) =
      (quadraticLevelScaling b m (G.symm y) (ψ t), ψ t))
    {A : Set E} (hA : IsClosed A) :
    IsOpen ((fun z : E × ℝ => (Q z).1) '' ((G '' sphere 0 r \ A) ×ˢ Ioo a d)) := by
  rw [image_projection_reference_cylinder Q G ψ hdb hbm hr hrsq hψ hψb hQfull A]
  have hq : Continuous (fun y : E => m - ‖y‖ ^ 2 / 2) := by fun_prop
  exact (isOpen_lt continuous_const hq).inter
    ((isOpen_lt hq continuous_const).inter
      (hA.isOpen_compl.preimage (Q.symm.continuous.comp (continuous_id.prodMk hq)).fst))

end Diffeomorph
