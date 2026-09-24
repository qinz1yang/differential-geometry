import DifferentialGeometry.Analysis.Calculus.Inverse.MonotoneGraph
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open Set Metric Filter Topology
open scoped ContDiff

namespace DifferentialGeometry.Analysis

private theorem pos_of_eq_zero_of_deriv_neg_at_zeros
    {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ∀ t ∈ Icc a b, DifferentiableAt ℝ f t)
    (hneg : ∀ t ∈ Icc a b, f t = 0 → deriv f t < 0)
    (hb : f b = 0) : 0 < f a := by
  by_contra hn
  have ha : f a ≤ 0 := le_of_not_gt hn
  have hnonpos : ∀ t ∈ Icc a b, f t ≤ 0 := by
    apply image_le_of_deriv_right_lt_deriv_boundary
      (fun t ht => (hf t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hf t ⟨ht.1, ht.2.le⟩).hasDerivAt.hasDerivWithinAt)
      (B := fun _ => (0 : ℝ)) (B' := fun _ => (0 : ℝ))
      ha (fun t => hasDerivAt_const t 0)
    intro t ht ht0
    exact hneg t ⟨ht.1, ht.2.le⟩ ht0
  have hlim : Tendsto (slope f b) (𝓝[<] b) (𝓝 (deriv f b)) :=
    (hasDerivWithinAt_iff_tendsto_slope' (show b ∉ Iio b from lt_irrefl b)).mp
      (hf b ⟨hab.le, le_rfl⟩).hasDerivAt.hasDerivWithinAt
  have hge : 0 ≤ deriv f b := by
    apply ge_of_tendsto hlim
    filter_upwards [Ico_mem_nhdsLT hab] with t ht
    rw [slope_def_field, hb, sub_zero]
    exact div_nonneg_of_nonpos (hnonpos t ⟨ht.1, ht.2.le⟩) (sub_neg.mpr ht.2).le
  exact (not_lt_of_ge hge) (hneg b ⟨hab.le, le_rfl⟩ hb)

private theorem eq_of_eq_zero_of_deriv_neg_at_zeros
    {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ t ∈ Icc a b, DifferentiableAt ℝ f t)
    (hneg : ∀ t ∈ Icc a b, f t = 0 → deriv f t < 0)
    (ha : f a = 0) (hb : f b = 0) : a = b := by
  rcases lt_or_eq_of_le hab with hlt | heq
  · exact ((ne_of_gt (pos_of_eq_zero_of_deriv_neg_at_zeros hlt hf hneg hb)) ha).elim
  · exact heq

private theorem exists_pos_mul_add_neg_on_isCompact
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {f g : X → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hg0 : ∀ x ∈ K, g x ≤ 0) (hf0 : ∀ x ∈ K, g x = 0 → f x < 0) :
    ∃ δ > 0, ∀ μ ∈ Ioo (0 : ℝ) δ, ∀ x ∈ K, μ * f x + g x < 0 := by
  let K₀ := K ∩ {x | 0 ≤ f x}
  have hK₀ : IsCompact K₀ := hK.inter_right (isClosed_le continuous_const hf)
  have hevent : ∀ᶠ μ in 𝓝 (0 : ℝ), ∀ x ∈ K₀, μ * f x + g x < 0 := by
    apply hK₀.eventually_forall_of_forall_eventually
    intro x hx
    have hneg : g x < 0 := lt_of_le_of_ne (hg0 x hx.1) (fun heq =>
      (not_lt_of_ge hx.2) (hf0 x hx.1 heq))
    have hc : Continuous (fun q : ℝ × X => q.1 * f q.2 + g q.2) :=
      (continuous_fst.mul (hf.comp continuous_snd)).add (hg.comp continuous_snd)
    exact (isOpen_lt hc continuous_const).mem_nhds (by simpa using hneg)
  obtain ⟨δ, hδ, hδbound⟩ := Metric.eventually_nhds_iff.mp hevent
  refine ⟨δ, hδ, fun μ hμ x hx => ?_⟩
  by_cases hfx : 0 ≤ f x
  · exact hδbound (by simpa [Real.dist_eq, abs_of_pos hμ.1] using hμ.2) x ⟨hx, hfx⟩
  · have hneg := mul_neg_of_pos_of_neg hμ.1 (lt_of_not_ge hfx)
    linarith [hg0 x hx]

theorem exists_injOn_exp_smul_zero_set_and_fderiv_neg
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E × ℝ → ℝ} (hF : ContDiff ℝ 1 F)
    {X Y : Set E} (hX : IsCompact X) (hY : IsCompact Y) (hYX : Y ⊆ interior X)
    {a b : ℝ}
    (hvertical : ∀ p ∈ X ×ˢ Icc a b, F p = 0 → fderiv ℝ F p (0, 1) ≤ 0)
    (hboundary : ∀ p ∈ X ×ˢ Icc a b, F p = 0 → fderiv ℝ F p (0, 1) = 0 →
      fderiv ℝ F p (p.1, 0) < 0) :
    ∃ δ > 0, ∀ μ ∈ Ioo (0 : ℝ) δ,
      InjOn (fun p : E × ℝ => Real.exp (-μ * p.2) • p.1)
        {p | p.1 ∈ Y ∧ p.2 ∈ Icc a b ∧ F p = 0} ∧
      ∀ p ∈ X ×ˢ Icc a b, F p = 0 → fderiv ℝ F p (μ • p.1, 1) < 0 := by
  let K : Set (E × ℝ) := (X ×ˢ Icc a b) ∩ {p | F p = 0}
  have hK : IsCompact K := (hX.prod isCompact_Icc).inter_right
    (isClosed_eq hF.continuous continuous_const)
  have hDf : Continuous (fun p : E × ℝ => fderiv ℝ F p (p.1, 0)) :=
    (hF.continuous_fderiv (by simp)).clm_apply (continuous_fst.prodMk continuous_const)
  have hDt : Continuous (fun p : E × ℝ => fderiv ℝ F p (0, 1)) :=
    (hF.continuous_fderiv (by simp)).clm_apply continuous_const
  obtain ⟨δ₁, hδ₁, hnegative⟩ := exists_pos_mul_add_neg_on_isCompact hK hDf hDt
    (fun p hp => hvertical p hp.1 hp.2)
    (fun p hp => hboundary p hp.1 hp.2)
  let L : Set (E × (ℝ × ℝ)) := Y ×ˢ (Icc a b ×ˢ Icc a b)
  have hL : IsCompact L := hY.prod (isCompact_Icc.prod isCompact_Icc)
  have hnear : ∀ᶠ μ in 𝓝 (0 : ℝ), ∀ p ∈ L,
      Real.exp (μ * (p.2.2 - p.2.1)) • p.1 ∈ interior X := by
    apply hL.eventually_forall_of_forall_eventually
    intro p hp
    have hcont : Continuous (fun q : ℝ × (E × (ℝ × ℝ)) =>
        Real.exp (q.1 * (q.2.2.2 - q.2.2.1)) • q.2.1) := by fun_prop
    exact (isOpen_interior.preimage hcont).mem_nhds (by simpa using hYX hp.1)
  obtain ⟨δ₂, hδ₂, hδ₂bound⟩ := Metric.eventually_nhds_iff.mp hnear
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun μ hμ => ?_⟩
  have hμ₁ : μ ∈ Ioo (0 : ℝ) δ₁ := ⟨hμ.1, hμ.2.trans_le (min_le_left _ _)⟩
  have hμ₂ : dist μ 0 < δ₂ := by
    simpa [Real.dist_eq, abs_of_pos hμ.1] using hμ.2.trans_le (min_le_right δ₁ δ₂)
  have hequal : ∀ p ∈ {p : E × ℝ | p.1 ∈ Y ∧ p.2 ∈ Icc a b ∧ F p = 0},
      ∀ q ∈ {p : E × ℝ | p.1 ∈ Y ∧ p.2 ∈ Icc a b ∧ F p = 0},
      p.2 ≤ q.2 → Real.exp (-μ * p.2) • p.1 = Real.exp (-μ * q.2) • q.1 → p = q := by
    intro p hp q hq hpq heq
    let z : ℝ → E := fun t => Real.exp (μ * (t - p.2)) • p.1
    have hz₀ : z p.2 = p.1 := by simp [z]
    have hz₁ : z q.2 = q.1 := by
      have heq' := congrArg (fun x : E => Real.exp (μ * q.2) • x) heq
      simpa only [smul_smul, ← Real.exp_add, show μ * q.2 + -μ * p.2 = μ * (q.2 - p.2) by ring,
        show μ * q.2 + -μ * q.2 = 0 by ring, Real.exp_zero, one_smul] using heq'
    have hzd (t : ℝ) : HasDerivAt z (μ • z t) t := by
      have hd := ((((hasDerivAt_id t).sub_const p.2).const_mul μ).exp).smul_const p.1
      convert hd using 1 <;> simp [z, smul_smul, mul_comm]
    let f : ℝ → ℝ := fun t => F (z t, t)
    have hfd (t : ℝ) : HasDerivAt f
        (μ * fderiv ℝ F (z t, t) (z t, 0) + fderiv ℝ F (z t, t) (0, 1)) t := by
      have hd := (hF.differentiable (by simp) (z t, t)).hasFDerivAt.comp_hasDerivAt t
        (f := fun s => (z s, s)) (HasDerivAt.prodMk (hzd t) (hasDerivAt_id t))
      have hv : (μ • z t, (1 : ℝ)) = μ • (z t, (0 : ℝ)) + (0, 1) := by
        ext <;> simp
      convert hd using 1 <;> first | rfl | rw [hv, map_add, map_smul, smul_eq_mul]
    have ht : p.2 = q.2 := eq_of_eq_zero_of_deriv_neg_at_zeros hpq
      (fun t _ => (hfd t).differentiableAt) (fun t ht ht0 => by
        have htI : t ∈ Icc a b := ⟨hp.2.1.1.trans ht.1, ht.2.trans hq.2.1.2⟩
        have hzX : z t ∈ X := interior_subset
          (hδ₂bound hμ₂ (p.1, p.2, t) ⟨hp.1, hp.2.1, htI⟩)
        rw [(hfd t).deriv]
        exact hnegative μ hμ₁ (z t, t) ⟨⟨hzX, htI⟩, ht0⟩)
      (by dsimp only [f]; rw [hz₀]; exact hp.2.2)
      (by dsimp only [f]; rw [hz₁]; exact hq.2.2)
    exact Prod.ext (by rw [← hz₀, ht, hz₁]) ht
  refine ⟨?_, ?_⟩
  · intro p hp q hq heq
    rcases le_total p.2 q.2 with hpq | hqp
    · exact hequal p hp q hq hpq heq
    · exact (hequal q hq p hp hqp heq.symm).symm
  · intro p hp hz
    have hv : (μ • p.1, (1 : ℝ)) = μ • (p.1, (0 : ℝ)) + (0, 1) := by
      ext <;> simp
    rw [hv, map_add, map_smul, smul_eq_mul]
    exact hnegative μ hμ₁ p ⟨hp, hz⟩


theorem exists_injOn_exp_smul_zero_set
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E × ℝ → ℝ} (hF : ContDiff ℝ 1 F)
    {X Y : Set E} (hX : IsCompact X) (hY : IsCompact Y) (hYX : Y ⊆ interior X)
    {a b : ℝ}
    (hvertical : ∀ p ∈ X ×ˢ Icc a b, F p = 0 → fderiv ℝ F p (0, 1) ≤ 0)
    (hboundary : ∀ p ∈ X ×ˢ Icc a b, F p = 0 → fderiv ℝ F p (0, 1) = 0 →
      fderiv ℝ F p (p.1, 0) < 0) :
    ∃ δ > 0, ∀ μ ∈ Ioo (0 : ℝ) δ,
      InjOn (fun p : E × ℝ => Real.exp (-μ * p.2) • p.1)
        {p | p.1 ∈ Y ∧ p.2 ∈ Icc a b ∧ F p = 0} := by
  obtain ⟨δ, hδ, hspec⟩ := exists_injOn_exp_smul_zero_set_and_fderiv_neg
    hF hX hY hYX hvertical hboundary
  exact ⟨δ, hδ, fun μ hμ => (hspec μ hμ).1⟩

private theorem vertical_radial_fderiv_add_mul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f κ : E → ℝ} {A : ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) (hκ : ContDiff ℝ 1 κ) (hA : ContDiff ℝ 1 A)
    (hκnonneg : ∀ x, 0 ≤ κ x)
    {X : Set E}
    {a b : ℝ} (hA' : ∀ t ∈ Icc a b, deriv A t ≤ 0)
    (hAz : ∀ t ∈ Icc a b, deriv A t = 0 → A t = 0)
    (hboundary : ∀ x ∈ X, f x = 0 → fderiv ℝ f x x < 0) :
    let F : E × ℝ → ℝ := fun p => f p.1 + κ p.1 * A p.2
    (∀ p ∈ X ×ˢ Icc a b, F p = 0 → fderiv ℝ F p (0, 1) ≤ 0) ∧
      ∀ p ∈ X ×ˢ Icc a b, F p = 0 → fderiv ℝ F p (0, 1) = 0 →
        fderiv ℝ F p (p.1, 0) < 0 := by
  intro F
  have hF : ContDiff ℝ 1 F := (hf.comp contDiff_fst).add
    ((hκ.comp contDiff_fst).mul (hA.comp contDiff_snd))
  have hvert (p : E × ℝ) : fderiv ℝ F p (0, 1) = κ p.1 * deriv A p.2 := by
    have h₁ := (hF.differentiable (by simp) p).hasFDerivAt.comp_hasDerivAt p.2
      (f := fun t => (p.1, t)) ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))
    have h₂ := ((hA.differentiable (by simp) p.2).hasDerivAt.const_mul (κ p.1)).const_add (f p.1)
    exact h₁.unique h₂
  have hhor (p : E × ℝ) (x : E) :
      fderiv ℝ F p (x, 0) = fderiv ℝ f p.1 x + A p.2 * fderiv ℝ κ p.1 x := by
    have h₁ := (hF.differentiable (by simp) p).hasFDerivAt.comp p.1
      (hasFDerivAt_prodMk_left (𝕜 := ℝ) p.1 p.2)
    have h₂ := (hf.differentiable (by simp) p.1).hasFDerivAt.add
      ((hκ.differentiable (by simp) p.1).hasFDerivAt.mul_const (A p.2))
    have heq := congrArg (fun L : E →L[ℝ] ℝ => L x) (h₁.unique h₂)
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply, ContinuousLinearMap.inl_apply,
      ContinuousLinearMap.id_apply, zero_apply, add_apply,
      smul_apply, smul_eq_mul] using heq
  refine ⟨?_, ?_⟩
  · intro p hp _
    rw [hvert]
    exact mul_nonpos_of_nonneg_of_nonpos (hκnonneg p.1) (hA' p.2 hp.2)
  · intro p hp hzero hvzero
    rw [hvert] at hvzero
    have hz : A p.2 = 0 ∨ κ p.1 = 0 := (mul_eq_zero.mp hvzero).elim Or.inr
      (fun h => Or.inl (hAz p.2 hp.2 h))
    have hfzero : f p.1 = 0 := by
      change f p.1 + κ p.1 * A p.2 = 0 at hzero
      rcases hz with ha | hk
      · simpa only [ha, mul_zero, add_zero] using hzero
      · simpa only [hk, zero_mul, add_zero] using hzero
    rw [hhor]
    have hproduct : A p.2 * fderiv ℝ κ p.1 p.1 = 0 := by
      rcases hz with ha | hk
      · rw [ha, zero_mul]
      · have hmin : IsLocalMin κ p.1 := Filter.Eventually.of_forall (fun x => by
          change κ p.1 ≤ κ x
          rw [hk]
          exact hκnonneg x)
        rw [hmin.fderiv_eq_zero, zero_apply, mul_zero]
    rw [hproduct, add_zero]
    exact hboundary p.1 hp.1 hfzero


theorem exists_injOn_exp_smul_add_mul_zero_set
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f κ : E → ℝ} {A : ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) (hκ : ContDiff ℝ 1 κ) (hA : ContDiff ℝ 1 A)
    (hκnonneg : ∀ x, 0 ≤ κ x)
    {X Y : Set E} (hX : IsCompact X) (hY : IsCompact Y) (hYX : Y ⊆ interior X)
    {a b : ℝ} (hA' : ∀ t ∈ Icc a b, deriv A t ≤ 0)
    (hAz : ∀ t ∈ Icc a b, deriv A t = 0 → A t = 0)
    (hboundary : ∀ x ∈ X, f x = 0 → fderiv ℝ f x x < 0) :
    ∃ δ > 0, ∀ μ ∈ Ioo (0 : ℝ) δ,
      InjOn (fun p : E × ℝ => Real.exp (-μ * p.2) • p.1)
        {p | p.1 ∈ Y ∧ p.2 ∈ Icc a b ∧ f p.1 + κ p.1 * A p.2 = 0} := by
  let F : E × ℝ → ℝ := fun p => f p.1 + κ p.1 * A p.2
  have hF : ContDiff ℝ 1 F := (hf.comp contDiff_fst).add
    ((hκ.comp contDiff_fst).mul (hA.comp contDiff_snd))
  obtain ⟨hv, hr⟩ := vertical_radial_fderiv_add_mul hf hκ hA hκnonneg hA' hAz hboundary
  exact exists_injOn_exp_smul_zero_set hF hX hY hYX hv hr

theorem exists_contDiffOn_exp_smul_zero_set_graph
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F : E × ℝ → ℝ} (hF : ContDiff ℝ ∞ F)
    {X Y : Set E} (hX : IsCompact X) (hY : IsCompact Y) (hYX : Y ⊆ interior X)
    {a b : ℝ}
    (hvertical : ∀ p ∈ X ×ˢ Icc a b, F p = 0 → fderiv ℝ F p (0, 1) ≤ 0)
    (hboundary : ∀ p ∈ X ×ˢ Icc a b, F p = 0 → fderiv ℝ F p (0, 1) = 0 →
      fderiv ℝ F p (p.1, 0) < 0) :
    ∃ δ > 0, ∀ μ ∈ Ioo (0 : ℝ) δ,
      ∃ O : Set E, IsOpen O ∧ ∃ g : E → ℝ, ContDiffOn ℝ ∞ g O ∧
        {p : E × ℝ | Real.exp (μ * p.2) • p.1 ∈ interior Y ∧ p.2 ∈ Ioo a b ∧
          F (Real.exp (μ * p.2) • p.1, p.2) = 0} =
            {p : E × ℝ | p.1 ∈ O ∧ p.2 = g p.1} := by
  obtain ⟨δ, hδ, hspec⟩ := exists_injOn_exp_smul_zero_set_and_fderiv_neg
    (hF.of_le (by simp)) hX hY hYX hvertical hboundary
  refine ⟨δ, hδ, fun μ hμ => ?_⟩
  let A : E × ℝ → E × ℝ := fun p => (Real.exp (μ * p.2) • p.1, p.2)
  let W : Set (E × ℝ) := {p | (A p).1 ∈ interior Y ∧ p.2 ∈ Ioo a b}
  have hA : ContDiff ℝ ∞ A := by dsimp [A]; fun_prop
  have hW : IsOpen W := (isOpen_interior.preimage hA.continuous.fst).inter
    (isOpen_Ioo.preimage continuous_snd)
  have hneg (p : E × ℝ) (hp : p ∈ W) (hz : (F ∘ A) p = 0) :
      fderiv ℝ (F ∘ A) p (0, 1) ≠ 0 := by
    have hmap : A p ∈ X ×ˢ Icc a b :=
      ⟨interior_subset (hYX (interior_subset hp.1)), Ioo_subset_Icc_self hp.2⟩
    have hdA : HasDerivAt (fun t => A (p.1, t)) (μ • (A p).1, 1) p.2 := by
      have hd := (((hasDerivAt_id p.2).const_mul μ).exp.smul_const p.1).prodMk
        (hasDerivAt_id p.2)
      convert hd using 1 <;> simp [A, smul_smul, mul_comm]
    have hd := (hF.differentiable (by simp) (A p)).hasFDerivAt.comp_hasDerivAt p.2
      (f := fun t => A (p.1, t)) hdA
    have hd' := ((hF.comp hA).differentiable (by simp) p).hasFDerivAt.comp_hasDerivAt p.2
      ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))
    have heq : fderiv ℝ (F ∘ A) p (0, 1) = fderiv ℝ F (A p) (μ • (A p).1, 1) :=
      hd'.unique hd
    rw [heq]
    exact ((hspec μ hμ).2 (A p) hmap hz).ne
  have hproj (p : E × ℝ) : Real.exp (-μ * (A p).2) • (A p).1 = p.1 := by
    simp only [A, smul_smul, ← Real.exp_add, show -μ * p.2 + μ * p.2 = 0 by ring,
      Real.exp_zero, one_smul]
  have hinj : InjOn (Prod.fst : E × ℝ → E) (W ∩ {p | (F ∘ A) p = 0}) := by
    intro p hp q hq heq
    have he := (hspec μ hμ).1
      (show (A p).1 ∈ Y ∧ (A p).2 ∈ Icc a b ∧ F (A p) = 0 from
        ⟨interior_subset hp.1.1, Ioo_subset_Icc_self hp.1.2, hp.2⟩)
      (show (A q).1 ∈ Y ∧ (A q).2 ∈ Icc a b ∧ F (A q) = 0 from
        ⟨interior_subset hq.1.1, Ioo_subset_Icc_self hq.1.2, hq.2⟩)
      (by change Real.exp (-μ * (A p).2) • (A p).1 = Real.exp (-μ * (A q).2) • (A q).1
          rw [hproj, hproj]; exact heq)
    have ht : (A p).2 = (A q).2 := congrArg Prod.snd he
    exact Prod.ext heq ht
  obtain ⟨O, hO, g, hg, hgraph⟩ := exists_isOpen_contDiffOn_implicit_graph_of_injOn
    (by simp : (∞ : ℕ∞ω) ≠ 0) hW (hF.comp hA).contDiffOn hneg hinj
  refine ⟨O, hO, g, hg, ?_⟩
  rw [← hgraph]
  ext p
  simp only [mem_ofPred_eq, mem_inter_iff, W, A, Function.comp_apply, and_assoc]



theorem exists_contDiffOn_exp_smul_add_mul_zero_set_graph
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f κ : E → ℝ} {A : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hκ : ContDiff ℝ ∞ κ) (hA : ContDiff ℝ ∞ A)
    (hκnonneg : ∀ x, 0 ≤ κ x)
    {X Y : Set E} (hX : IsCompact X) (hY : IsCompact Y) (hYX : Y ⊆ interior X)
    {a b : ℝ} (hA' : ∀ t ∈ Icc a b, deriv A t ≤ 0)
    (hAz : ∀ t ∈ Icc a b, deriv A t = 0 → A t = 0)
    (hboundary : ∀ x ∈ X, f x = 0 → fderiv ℝ f x x < 0) :
    ∃ δ > 0, ∀ μ ∈ Ioo (0 : ℝ) δ,
      ∃ O : Set E, IsOpen O ∧ ∃ g : E → ℝ, ContDiffOn ℝ ∞ g O ∧
        {p : E × ℝ | Real.exp (μ * p.2) • p.1 ∈ interior Y ∧ p.2 ∈ Ioo a b ∧
          f (Real.exp (μ * p.2) • p.1) + κ (Real.exp (μ * p.2) • p.1) * A p.2 = 0} =
            {p : E × ℝ | p.1 ∈ O ∧ p.2 = g p.1} := by
  let F : E × ℝ → ℝ := fun p => f p.1 + κ p.1 * A p.2
  have hF : ContDiff ℝ ∞ F := (hf.comp contDiff_fst).add
    ((hκ.comp contDiff_fst).mul (hA.comp contDiff_snd))
  obtain ⟨hv, hr⟩ := vertical_radial_fderiv_add_mul
    (hf.of_le (by simp)) (hκ.of_le (by simp)) (hA.of_le (by simp)) hκnonneg hA' hAz hboundary
  exact exists_contDiffOn_exp_smul_zero_set_graph hF hX hY hYX hv hr

theorem exists_exp_smul_eq_imp_mem_of_isCompact
    {E F : Type*} [TopologicalSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} (hf : Continuous f) (hfinj : Function.Injective f)
    {K : Set (E × ℝ)} (hK : IsCompact K) {C : Set E} (hC : IsCompact C)
    {J : Set ℝ} (hJ : IsCompact J) {O : Set E} (hO : IsOpen O)
    (hKO : (Prod.fst '' K) ∩ C ⊆ O) :
    ∃ δ > 0, ∀ μ ∈ Ioo (0 : ℝ) δ, ∀ p ∈ K, ∀ q ∈ C ×ˢ J,
      Real.exp (-μ * p.2) • f p.1 = Real.exp (-μ * q.2) • f q.1 → q.1 ∈ O := by
  let A : Set ((E × ℝ) × (E × ℝ)) := K ×ˢ ((C \ O) ×ˢ J)
  have hA : IsCompact A := hK.prod ((hC.inter_right hO.isClosed_compl).prod hJ)
  let N : Set (ℝ × ((E × ℝ) × (E × ℝ))) := {q |
    Real.exp (-q.1 * q.2.1.2) • f q.2.1.1 ≠
      Real.exp (-q.1 * q.2.2.2) • f q.2.2.1}
  have hN : IsOpen N := isOpen_ne_fun
    (((continuous_fst.neg.mul continuous_snd.fst.snd).rexp).smul
      (hf.comp continuous_snd.fst.fst))
    (((continuous_fst.neg.mul continuous_snd.snd.snd).rexp).smul
      (hf.comp continuous_snd.snd.fst))
  have hzero : ({0} : Set ℝ) ×ˢ A ⊆ N := by
    rintro ⟨μ, p, q⟩ ⟨rfl, hp, hq⟩ heq
    have he : p.1 = q.1 := hfinj (by simpa only [neg_zero, zero_mul, Real.exp_zero, one_smul] using heq)
    exact hq.1.2 (hKO ⟨⟨p, hp, he⟩, hq.1.1⟩)
  obtain ⟨U, V, hU, _, h0U, hAV, hUV⟩ :=
    generalized_tube_lemma isCompact_singleton hA hN hzero
  obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.mp hU 0 (h0U (mem_singleton 0))
  refine ⟨δ, hδ, ?_⟩
  intro μ hμ p hp q hq heq
  by_contra hqO
  have hμU : μ ∈ U := hδU (by simpa only [mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos hμ.1] using hμ.2)
  have hneq : (μ, p, q) ∈ N := hUV ⟨hμU, hAV ⟨hp, ⟨hq.1, hqO⟩, hq.2⟩⟩
  exact hneq heq

theorem injOn_exp_smul_sphere_prod
    {E F : Type*} [TopologicalSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (G : F ≃ₜ E) {r μ : ℝ} (hr : r ≠ 0) (hμ : μ ≠ 0) :
    InjOn (fun p : E × ℝ => Real.exp (-μ * p.2) • G.symm p.1)
      ((G '' sphere 0 r) ×ˢ (univ : Set ℝ)) := by
  intro p hp q hq heq
  have hnorm (y : E) (hy : y ∈ G '' sphere 0 r) : ‖G.symm y‖ = r := by
    obtain ⟨x, hx, rfl⟩ := hy
    rw [G.symm_apply_apply]
    exact mem_sphere_zero_iff_norm.mp hx
  have hn := congrArg norm heq
  change ‖Real.exp (-μ * p.2) • G.symm p.1‖ = ‖Real.exp (-μ * q.2) • G.symm q.1‖ at hn
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _), hnorm p.1 hp.1, hnorm q.1 hq.1] at hn
  have ht : p.2 = q.2 := by
    have he := Real.exp_injective (mul_right_cancel₀ hr hn)
    exact mul_left_cancel₀ (neg_ne_zero.mpr hμ) he
  apply Prod.ext _ ht
  apply G.symm.injective
  change Real.exp (-μ * p.2) • G.symm p.1 = Real.exp (-μ * q.2) • G.symm q.1 at heq
  rw [ht] at heq
  exact smul_right_injective F (Real.exp_ne_zero _) heq

theorem exists_pos_on_exp_smul_zero_set_trace
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E × ℝ → ℝ} (hF : ContDiff ℝ 1 F)
    {X Y : Set E} (hX : IsCompact X) (hY : IsCompact Y) (hYX : Y ⊆ interior X)
    {a b : ℝ}
    (hvertical : ∀ p ∈ X ×ˢ Icc a b, F p = 0 → fderiv ℝ F p (0, 1) ≤ 0)
    (hboundary : ∀ p ∈ X ×ˢ Icc a b, F p = 0 → fderiv ℝ F p (0, 1) = 0 →
      fderiv ℝ F p (p.1, 0) < 0) :
    ∃ δ > 0, ∀ μ ∈ Ioo (0 : ℝ) δ, ∀ p ∈ Y ×ˢ Icc a b, F p = 0 →
      ∀ t ∈ Ico a p.2,
        Real.exp (μ * (t - p.2)) • p.1 ∈ interior X ∧
          0 < F (Real.exp (μ * (t - p.2)) • p.1, t) := by
  obtain ⟨δ₁, hδ₁, hneg⟩ := exists_injOn_exp_smul_zero_set_and_fderiv_neg
    hF hX hY hYX hvertical hboundary
  have hnear : ∀ᶠ μ in 𝓝 (0 : ℝ), ∀ p ∈ Y ×ˢ (Icc a b ×ˢ Icc a b),
      Real.exp (μ * (p.2.2 - p.2.1)) • p.1 ∈ interior X := by
    apply (hY.prod (isCompact_Icc.prod isCompact_Icc)).eventually_forall_of_forall_eventually
    intro p hp
    have hcont : Continuous (fun q : ℝ × (E × (ℝ × ℝ)) =>
        Real.exp (q.1 * (q.2.2.2 - q.2.2.1)) • q.2.1) := by fun_prop
    exact (isOpen_interior.preimage hcont).mem_nhds (by simpa using hYX hp.1)
  obtain ⟨δ₂, hδ₂, hδ₂bound⟩ := Metric.eventually_nhds_iff.mp hnear
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun μ hμ p hp hpzero t ht => ?_⟩
  have hμ₁ : μ ∈ Ioo (0 : ℝ) δ₁ := ⟨hμ.1, hμ.2.trans_le (min_le_left _ _)⟩
  have hμ₂ : dist μ 0 < δ₂ := by
    simpa [Real.dist_eq, abs_of_pos hμ.1] using hμ.2.trans_le (min_le_right δ₁ δ₂)
  let z : ℝ → E := fun v => Real.exp (μ * (v - p.2)) • p.1
  have hzX (v : ℝ) (hv : v ∈ Icc a b) : z v ∈ interior X :=
    hδ₂bound hμ₂ (p.1, p.2, v) ⟨hp.1, hp.2, hv⟩
  have hzd (v : ℝ) : HasDerivAt z (μ • z v) v := by
    have hd := ((((hasDerivAt_id v).sub_const p.2).const_mul μ).exp).smul_const p.1
    convert hd using 1 <;> simp [z, smul_smul, mul_comm]
  have hfd (v : ℝ) : HasDerivAt (fun v => F (z v, v))
      (fderiv ℝ F (z v, v) (μ • z v, 1)) v :=
    (hF.differentiable (by simp) (z v, v)).hasFDerivAt.comp_hasDerivAt v
      (f := fun w => (z w, w)) ((hzd v).prodMk (hasDerivAt_id v))
  refine ⟨hzX t ⟨ht.1, ht.2.le.trans hp.2.2⟩, ?_⟩
  apply pos_of_eq_zero_of_deriv_neg_at_zeros ht.2 (fun v _ => (hfd v).differentiableAt)
  · intro v hv hvzero
    have hvab : v ∈ Icc a b := ⟨ht.1.trans hv.1, hv.2.trans hp.2.2⟩
    rw [(hfd v).deriv]
    exact (hneg μ hμ₁).2 (z v, v) ⟨interior_subset (hzX v hvab), hvab⟩ hvzero
  · simpa [z] using hpzero

theorem exists_pos_on_exp_smul_add_mul_zero_set_trace
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f κ : E → ℝ} {A : ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) (hκ : ContDiff ℝ 1 κ) (hA : ContDiff ℝ 1 A)
    (hκnonneg : ∀ x, 0 ≤ κ x)
    {X Y : Set E} (hX : IsCompact X) (hY : IsCompact Y) (hYX : Y ⊆ interior X)
    {a b : ℝ} (hA' : ∀ t ∈ Icc a b, deriv A t ≤ 0)
    (hAz : ∀ t ∈ Icc a b, deriv A t = 0 → A t = 0)
    (hboundary : ∀ x ∈ X, f x = 0 → fderiv ℝ f x x < 0) :
    ∃ δ > 0, ∀ μ ∈ Ioo (0 : ℝ) δ, ∀ p ∈ Y ×ˢ Icc a b, f p.1 + κ p.1 * A p.2 = 0 →
      ∀ t ∈ Ico a p.2,
        Real.exp (μ * (t - p.2)) • p.1 ∈ interior X ∧
          0 < f (Real.exp (μ * (t - p.2)) • p.1) +
            κ (Real.exp (μ * (t - p.2)) • p.1) * A t := by
  have hF : ContDiff ℝ 1 (fun p : E × ℝ => f p.1 + κ p.1 * A p.2) :=
    (hf.comp contDiff_fst).add ((hκ.comp contDiff_fst).mul (hA.comp contDiff_snd))
  obtain ⟨hv, hr⟩ := vertical_radial_fderiv_add_mul hf hκ hA hκnonneg hA' hAz hboundary
  exact exists_pos_on_exp_smul_zero_set_trace hF hX hY hYX hv hr

end DifferentialGeometry.Analysis
