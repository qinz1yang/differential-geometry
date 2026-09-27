import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

open Set Metric

namespace Function

theorem eq_vertex_of_mem_image_quadratic_graph
    {E : Type*} [NormedAddCommGroup E]
    (A : E × ℝ → E × ℝ) (hA : ∀ z, (A z).2 = z.2)
    {c α : ℝ} (hα : α ≠ 0) {S : Set E} {z : E × ℝ}
    (hz : z ∈ (fun y => A (y, c + α / 2 * ‖y‖ ^ 2)) '' S)
    (hc : z.2 = c) : z = A (0, c) := by
  obtain ⟨y, _, hy⟩ := hz
  have hyh : c + α / 2 * ‖y‖ ^ 2 = c :=
    (hA _).symm.trans ((congrArg Prod.snd hy).trans hc)
  have hmul : α / 2 * ‖y‖ ^ 2 = 0 := by linarith
  have hnorm : ‖y‖ ^ 2 = 0 :=
    (mul_eq_zero.mp hmul).resolve_left (div_ne_zero hα (by norm_num))
  have hy0 : y = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm)
  simpa only [hy0, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, add_zero]
    using hy.symm

theorem image_level_eq_image_sphere_of_image_quadratic_graph_eq
    {M E : Type*} [NormedAddCommGroup E] (f : M → E × ℝ)
    (A : E × ℝ → E × ℝ) (hA : ∀ z, (A z).2 = z.2)
    {c α r : ℝ} (hα : α ≠ 0) (hr : 0 ≤ r) {K : Set M}
    (hK : {x | (f x).2 = c + α / 2 * r ^ 2} ⊆ K)
    (hcap : f '' K = (fun y => A (y, c + α / 2 * ‖y‖ ^ 2)) '' closedBall 0 r) :
    (fun x => (f x).1) '' {x | (f x).2 = c + α / 2 * r ^ 2} =
      (fun y => (A (y, c + α / 2 * r ^ 2)).1) '' sphere 0 r := by
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, _, hy⟩ := hcap.subset ⟨x, hK hx, rfl⟩
    have hyheight : c + α / 2 * ‖y‖ ^ 2 = c + α / 2 * r ^ 2 :=
      (hA _).symm.trans ((congrArg Prod.snd hy).trans hx)
    have hysq : ‖y‖ ^ 2 = r ^ 2 :=
      mul_left_cancel₀ (div_ne_zero hα (by norm_num)) (add_left_cancel hyheight)
    have hynorm : ‖y‖ = r := by nlinarith [norm_nonneg y]
    refine ⟨y, mem_sphere_zero_iff_norm.mpr hynorm, ?_⟩
    rw [← hyheight]
    exact congrArg Prod.fst hy
  · rintro _ ⟨y, hy, rfl⟩
    have hynorm : ‖y‖ = r := mem_sphere_zero_iff_norm.mp hy
    obtain ⟨x, _, hx⟩ := hcap.symm.subset ⟨y, sphere_subset_closedBall hy, rfl⟩
    have hxheight : (f x).2 = c + α / 2 * r ^ 2 := by
      rw [hx, hA, hynorm]
    refine ⟨x, hxheight, ?_⟩
    simpa only [hynorm] using congrArg Prod.fst hx


theorem image_eq_union_of_quadratic_cap_formulas
    {X E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Q D : X → E × ℝ) (S : Set X) (A₀ A₁ F : E × ℝ → E × ℝ)
    (G : ℝ → E → E) (C : E → E) (R : ℝ → ℝ)
    {c₀ c₁ r : ℝ} (hr : 0 < r) (hab : c₀ + r ^ 2 / 2 ≤ c₁ - r ^ 2 / 2)
    (hQ : Q '' S = {p | p.2 ∈ Icc c₀ c₁ ∧ ‖p.1‖ = R p.2})
    (hR : ∀ t ∈ Icc c₀ c₁, 0 ≤ R t)
    (hRpos : ∀ t ∈ Ioo (c₀ + r ^ 2 / 2) (c₁ - r ^ 2 / 2), 0 < R t)
    (hR₀ : ∀ t ∈ Icc c₀ (c₀ + r ^ 2 / 2), R t ^ 2 = 2 * (t - c₀))
    (hR₁ : ∀ t ∈ Icc (c₁ - r ^ 2 / 2) c₁, R t ^ 2 = 2 * (c₁ - t))
    (hC : C '' closedBall 0 r = closedBall 0 r)
    (hF : ∀ x ∈ closedBall (0 : E) r,
      F (x, c₁ - ‖x‖ ^ 2 / 2) = (C x, c₁ - ‖C x‖ ^ 2 / 2))
    (h₀ : ∀ z ∈ S, (Q z).2 ≤ c₀ + r ^ 2 / 2 → D z = A₀ (Q z))
    (hmid : ∀ z ∈ S, (Q z).2 ∈ Ioo (c₀ + r ^ 2 / 2) (c₁ - r ^ 2 / 2) →
      D z = (G (Q z).2 ((r / R (Q z).2) • (Q z).1), (Q z).2))
    (h₁ : ∀ z ∈ S, c₁ - r ^ 2 / 2 ≤ (Q z).2 → D z = A₁ (F (Q z))) :
    D '' S =
      (fun x => A₀ (x, c₀ + ‖x‖ ^ 2 / 2)) '' closedBall 0 r ∪
      (fun p : E × ℝ => (G p.2 p.1, p.2)) ''
        (sphere 0 r ×ˢ Ioo (c₀ + r ^ 2 / 2) (c₁ - r ^ 2 / 2)) ∪
      (fun x => A₁ (x, c₁ - ‖x‖ ^ 2 / 2)) '' closedBall 0 r := by
  have hr₂ : 0 < r ^ 2 := sq_pos_of_pos hr
  have hlower (x : E) (hx : x ∈ closedBall 0 r) :
      (x, c₀ + ‖x‖ ^ 2 / 2) ∈ Q '' S := by
    rw [hQ]
    have hxr : ‖x‖ ≤ r := mem_closedBall_zero_iff.mp hx
    have ht : c₀ + ‖x‖ ^ 2 / 2 ∈ Icc c₀ (c₀ + r ^ 2 / 2) := by
      constructor <;> nlinarith [sq_nonneg ‖x‖, norm_nonneg x]
    have htc : c₀ + ‖x‖ ^ 2 / 2 ∈ Icc c₀ c₁ := ⟨ht.1, by linarith [ht.2]⟩
    refine ⟨htc, ?_⟩
    have hs := hR₀ _ ht
    exact (sq_eq_sq₀ (norm_nonneg x) (hR _ htc)).mp (by nlinarith only [hs])
  have hupper (x : E) (hx : x ∈ closedBall 0 r) :
      (x, c₁ - ‖x‖ ^ 2 / 2) ∈ Q '' S := by
    rw [hQ]
    have hxr : ‖x‖ ≤ r := mem_closedBall_zero_iff.mp hx
    have ht : c₁ - ‖x‖ ^ 2 / 2 ∈ Icc (c₁ - r ^ 2 / 2) c₁ := by
      constructor <;> nlinarith [sq_nonneg ‖x‖, norm_nonneg x]
    have htc : c₁ - ‖x‖ ^ 2 / 2 ∈ Icc c₀ c₁ := ⟨by linarith [ht.1], ht.2⟩
    refine ⟨htc, ?_⟩
    have hs := hR₁ _ ht
    exact (sq_eq_sq₀ (norm_nonneg x) (hR _ htc)).mp (by nlinarith only [hs])
  apply Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    have hq := hQ.subset (mem_image_of_mem Q hz)
    change (Q z).2 ∈ Icc c₀ c₁ ∧ ‖(Q z).1‖ = R (Q z).2 at hq
    by_cases hlo : (Q z).2 ≤ c₀ + r ^ 2 / 2
    · have hsq := hR₀ _ ⟨hq.1.1, hlo⟩
      rw [← hq.2] at hsq
      have heq : Q z = ((Q z).1, c₀ + ‖(Q z).1‖ ^ 2 / 2) :=
        Prod.ext rfl (by nlinarith only [hsq])
      have hx : (Q z).1 ∈ closedBall 0 r := by
        rw [mem_closedBall_zero_iff]
        nlinarith [norm_nonneg (Q z).1]
      exact Or.inl (Or.inl ⟨(Q z).1, hx, by rw [h₀ z hz hlo, heq]⟩)
    · by_cases hhi : c₁ - r ^ 2 / 2 ≤ (Q z).2
      · have hsq := hR₁ _ ⟨hhi, hq.1.2⟩
        rw [← hq.2] at hsq
        have heq : Q z = ((Q z).1, c₁ - ‖(Q z).1‖ ^ 2 / 2) :=
          Prod.ext rfl (by nlinarith only [hsq])
        have hx : (Q z).1 ∈ closedBall 0 r := by
          rw [mem_closedBall_zero_iff]
          nlinarith [norm_nonneg (Q z).1]
        exact Or.inr ⟨C (Q z).1, hC.subset (mem_image_of_mem C hx), by
          rw [h₁ z hz hhi, heq, hF _ hx]⟩
      · have ht : (Q z).2 ∈ Ioo (c₀ + r ^ 2 / 2) (c₁ - r ^ 2 / 2) :=
          ⟨lt_of_not_ge hlo, lt_of_not_ge hhi⟩
        have hpos := hRpos _ ht
        refine Or.inl (Or.inr ⟨((r / R (Q z).2) • (Q z).1, (Q z).2), ⟨?_, ht⟩, ?_⟩)
        · rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_of_nonneg (div_pos hr hpos).le,
            hq.2, div_mul_cancel₀ r hpos.ne']
        · exact (hmid z hz ht).symm
  · rintro y ((hy | hy) | hy)
    · obtain ⟨x, hx, rfl⟩ := hy
      obtain ⟨z, hz, hq⟩ := hlower x hx
      refine ⟨z, hz, ?_⟩
      have hlo : (Q z).2 ≤ c₀ + r ^ 2 / 2 := by
        rw [hq]
        have := mem_closedBall_zero_iff.mp hx
        nlinarith [norm_nonneg x]
      rw [h₀ z hz hlo, hq]
    · obtain ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩ := hy
      have hpos := hRpos t ht
      have hqt : ((R t / r) • x, t) ∈ Q '' S := by
        rw [hQ]
        refine ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
        rw [norm_smul, Real.norm_of_nonneg (div_pos hpos hr).le,
          mem_sphere_zero_iff_norm.mp hx, div_mul_cancel₀ _ hr.ne']
      obtain ⟨z, hz, hq⟩ := hqt
      have ht' : (Q z).2 ∈ Ioo (c₀ + r ^ 2 / 2) (c₁ - r ^ 2 / 2) := by rw [hq]; exact ht
      refine ⟨z, hz, ?_⟩
      rw [hmid z hz ht', hq]
      dsimp only
      have hscale : r / R t * (R t / r) = 1 := by field_simp
      rw [smul_smul, hscale, one_smul]
    · obtain ⟨y, hy, rfl⟩ := hy
      obtain ⟨x, hx, hCx⟩ := hC.symm.subset hy
      obtain ⟨z, hz, hq⟩ := hupper x hx
      have hhi : c₁ - r ^ 2 / 2 ≤ (Q z).2 := by
        rw [hq]
        have := mem_closedBall_zero_iff.mp hx
        nlinarith [norm_nonneg x]
      refine ⟨z, hz, ?_⟩
      rw [h₁ z hz hhi, hq, hF x hx, hCx]

theorem image_paraboloid_cap_eq_union
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D A : E × ℝ → F) (G : ℝ → E → F)
    {a b c r : ℝ} (hr : 0 < r) (hab : a ≤ b) (hb : b = c - r ^ 2 / 2)
    (hlo : ∀ t ≤ b, ∀ x,
      D (Real.sqrt ((t - c) / (b - c)) • x, t) = G t x)
    (hhi : ∀ t, b ≤ t → ∀ x ∈ closedBall (0 : E) r, D (x, t) = A (x, t)) :
    D '' {p | a ≤ p.2 ∧ p.2 ≤ c - ‖p.1‖ ^ 2 / 2} =
      (fun p : E × ℝ => G p.2 p.1) '' (closedBall 0 r ×ˢ Icc a b) ∪
      A '' {p | p.1 ∈ closedBall (0 : E) r ∧ p.2 ∈ Icc b (c - ‖p.1‖ ^ 2 / 2)} := by
  have hbc : b < c := by rw [hb]; nlinarith [sq_pos_of_pos hr]
  have hratio (t : ℝ) (ht : t ≤ b) : 0 < (t - c) / (b - c) :=
    div_pos_of_neg_of_neg (sub_neg.mpr (ht.trans_lt hbc)) (sub_neg.mpr hbc)
  have hscale (t : ℝ) (ht : t ≤ b) (x : E) :
      ‖Real.sqrt ((t - c) / (b - c)) • x‖ ^ 2 = (t - c) / (b - c) * ‖x‖ ^ 2 := by
    rw [norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (hratio t ht).le]
  have htop (t : ℝ) : (t - c) / (b - c) * r ^ 2 = 2 * (c - t) := by
    rw [div_mul_eq_mul_div, div_eq_iff (sub_ne_zero.mpr hbc.ne)]
    rw [hb]
    ring
  have hbound (t : ℝ) (ht : t ≤ b) (x : E) :
      t ≤ c - ‖Real.sqrt ((t - c) / (b - c)) • x‖ ^ 2 / 2 ↔
        x ∈ closedBall (0 : E) r := by
    rw [mem_closedBall_zero_iff, ← sq_le_sq₀ (norm_nonneg x) hr.le, hscale t ht]
    have htop' := htop t
    constructor
    · intro h
      apply (mul_le_mul_iff_right₀ (hratio t ht)).mp
      nlinarith only [h, htop']
    · intro h
      have hh := mul_le_mul_of_nonneg_left h (hratio t ht).le
      nlinarith only [hh, htop']
  apply Subset.antisymm
  · rintro z ⟨⟨x, t⟩, ⟨hat, htc⟩, rfl⟩
    by_cases htb : t ≤ b
    · let y := (Real.sqrt ((t - c) / (b - c)))⁻¹ • x
      have hy : Real.sqrt ((t - c) / (b - c)) • y = x := by
        dsimp [y]
        rw [smul_smul, mul_inv_cancel₀ (Real.sqrt_pos.mpr (hratio t htb)).ne', one_smul]
      refine Or.inl ⟨(y, t), ⟨?_, hat, htb⟩, ?_⟩
      · exact (hbound t htb y).mp (by rwa [hy])
      · change G t y = D (x, t)
        rw [← hlo t htb y, hy]
    · have hx : x ∈ closedBall (0 : E) r := by
        rw [mem_closedBall_zero_iff]
        apply (sq_le_sq₀ (norm_nonneg x) hr.le).mp
        nlinarith [lt_of_not_ge htb]
      exact Or.inr ⟨(x, t), ⟨hx, (lt_of_not_ge htb).le, htc⟩,
        (hhi t (lt_of_not_ge htb).le x hx).symm⟩
  · rintro z (⟨⟨x, t⟩, ⟨hx, hat, htb⟩, rfl⟩ | ⟨⟨x, t⟩, ⟨hx, hbt, htc⟩, rfl⟩)
    · exact ⟨(Real.sqrt ((t - c) / (b - c)) • x, t),
        ⟨hat, (hbound t htb x).mpr hx⟩, hlo t htb x⟩
    · exact ⟨(x, t), ⟨hab.trans hbt, htc⟩, hhi t hbt x hx⟩

theorem image_paraboloid_graph_eq_union
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D A : E × ℝ → F) (G : ℝ → E → F)
    {a b c r : ℝ} (hr : 0 < r) (hab : a ≤ b) (hb : b = c - r ^ 2 / 2)
    (hlo : ∀ t ≤ b, ∀ x,
      D (Real.sqrt ((t - c) / (b - c)) • x, t) = G t x)
    (hhi : ∀ t, b ≤ t → ∀ x ∈ closedBall (0 : E) r, D (x, t) = A (x, t)) :
    D '' {p | a ≤ p.2 ∧ p.2 = c - ‖p.1‖ ^ 2 / 2} =
      (fun p : E × ℝ => G p.2 p.1) '' (sphere 0 r ×ˢ Icc a b) ∪
      (fun x => A (x, c - ‖x‖ ^ 2 / 2)) '' closedBall (0 : E) r := by
  have hbc : b < c := by rw [hb]; nlinarith [sq_pos_of_pos hr]
  have hratio (t : ℝ) (ht : t ≤ b) : 0 < (t - c) / (b - c) :=
    div_pos_of_neg_of_neg (sub_neg.mpr (ht.trans_lt hbc)) (sub_neg.mpr hbc)
  have hscale (t : ℝ) (ht : t ≤ b) (x : E) :
      ‖Real.sqrt ((t - c) / (b - c)) • x‖ ^ 2 = (t - c) / (b - c) * ‖x‖ ^ 2 := by
    rw [norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (hratio t ht).le]
  have htop (t : ℝ) : (t - c) / (b - c) * r ^ 2 = 2 * (c - t) := by
    rw [div_mul_eq_mul_div, div_eq_iff (sub_ne_zero.mpr hbc.ne), hb]
    ring
  have hbound (t : ℝ) (ht : t ≤ b) (x : E) :
      t = c - ‖Real.sqrt ((t - c) / (b - c)) • x‖ ^ 2 / 2 ↔
        x ∈ sphere (0 : E) r := by
    rw [mem_sphere_zero_iff_norm, ← sq_eq_sq₀ (norm_nonneg x) hr.le, hscale t ht]
    have htop' := htop t
    constructor
    · intro h
      apply mul_left_cancel₀ (hratio t ht).ne'
      linarith only [h, htop']
    · intro h
      rw [h]
      linarith only [htop']
  apply Subset.antisymm
  · rintro z ⟨⟨x, t⟩, ⟨hat, htc⟩, rfl⟩
    by_cases htb : t ≤ b
    · let y := (Real.sqrt ((t - c) / (b - c)))⁻¹ • x
      have hy : Real.sqrt ((t - c) / (b - c)) • y = x := by
        dsimp [y]
        rw [smul_smul, mul_inv_cancel₀ (Real.sqrt_pos.mpr (hratio t htb)).ne', one_smul]
      refine Or.inl ⟨(y, t), ⟨?_, hat, htb⟩, ?_⟩
      · exact (hbound t htb y).mp (by rwa [hy])
      · change G t y = D (x, t)
        rw [← hlo t htb y, hy]
    · have hx : x ∈ closedBall (0 : E) r := by
        rw [mem_closedBall_zero_iff]
        apply (sq_le_sq₀ (norm_nonneg x) hr.le).mp
        nlinarith [lt_of_not_ge htb]
      refine Or.inr ⟨x, hx, ?_⟩
      change A (x, c - ‖x‖ ^ 2 / 2) = D (x, t)
      rw [← htc]
      exact (hhi t (lt_of_not_ge htb).le x hx).symm
  · rintro z (⟨⟨x, t⟩, ⟨hx, hat, htb⟩, rfl⟩ | ⟨x, hx, rfl⟩)
    · exact ⟨(Real.sqrt ((t - c) / (b - c)) • x, t),
        ⟨hat, (hbound t htb x).mpr hx⟩, hlo t htb x⟩
    · have hbt : b ≤ c - ‖x‖ ^ 2 / 2 := by
        have hn := (sq_le_sq₀ (norm_nonneg x) hr.le).mpr (mem_closedBall_zero_iff.mp hx)
        rw [hb]
        linarith
      exact ⟨(x, c - ‖x‖ ^ 2 / 2), ⟨hab.trans hbt, rfl⟩, hhi _ hbt x hx⟩

end Function

namespace Equiv

theorem image_closedBall_inter_image_level_eq_of_quadratic_graph
    {M E : Type*} [NormedAddCommGroup E] (f : M → E × ℝ)
    (A : (E × ℝ) ≃ (E × ℝ)) (hA : ∀ z, (A z).2 = z.2)
    {c α r R : ℝ} {J : Set ℝ} (hα : α ≠ 0) (hr : 0 ≤ r) (hrR : r ≤ R)
    (hb : c + α / 2 * r ^ 2 ∈ J)
    (hgraph : (closedBall 0 R ×ˢ J) ∩ range (A.symm ∘ f) =
      (fun y => (y, c + α / 2 * ‖y‖ ^ 2)) '' closedBall 0 R) :
    ((fun y => (A (y, c + α / 2 * r ^ 2)).1) '' closedBall (0 : E) r) ∩
        ((fun x => (f x).1) '' {x | (f x).2 = c + α / 2 * r ^ 2}) =
      (fun y => (A (y, c + α / 2 * r ^ 2)).1) '' sphere 0 r := by
  apply Subset.antisymm
  · rintro z ⟨⟨y, hy, rfl⟩, x, hx, hxz⟩
    have hf : f x = A (y, c + α / 2 * r ^ 2) :=
      Prod.ext hxz (hx.trans (hA (y, c + α / 2 * r ^ 2)).symm)
    have hmem : (y, c + α / 2 * r ^ 2) ∈ (closedBall 0 R ×ˢ J) ∩ range (A.symm ∘ f) :=
      ⟨⟨(closedBall_subset_closedBall hrR) hy, hb⟩, x, by
        simp only [Function.comp_def, hf, A.symm_apply_apply]⟩
    obtain ⟨w, _, hw⟩ := hgraph.subset hmem
    have hwy : w = y := congrArg Prod.fst hw
    subst w
    have hq := congrArg Prod.snd hw
    have hsq : ‖y‖ ^ 2 = r ^ 2 :=
      mul_left_cancel₀ (div_ne_zero hα (by norm_num)) (add_left_cancel hq)
    exact ⟨y, mem_sphere_zero_iff_norm.mpr ((sq_eq_sq₀ (norm_nonneg y) hr).mp hsq), rfl⟩
  · rintro z ⟨y, hy, rfl⟩
    have hq : c + α / 2 * ‖y‖ ^ 2 = c + α / 2 * r ^ 2 := by
      rw [mem_sphere_zero_iff_norm.mp hy]
    have hmem := hgraph.symm.subset
      (mem_image_of_mem (fun y => (y, c + α / 2 * ‖y‖ ^ 2))
        ((closedBall_subset_closedBall hrR) (sphere_subset_closedBall hy)))
    obtain ⟨x, hx⟩ := hmem.2
    have hf : f x = A (y, c + α / 2 * r ^ 2) := by
      have hh := congrArg A hx
      simpa only [Function.comp_def, A.apply_symm_apply, hq] using hh
    refine ⟨mem_image_of_mem _ (sphere_subset_closedBall hy), x, ?_, ?_⟩
    · change (f x).2 = c + α / 2 * r ^ 2
      rw [hf, hA]
    · exact congrArg Prod.fst hf

end Equiv
