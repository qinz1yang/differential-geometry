import DifferentialGeometry.Analysis.Calculus.Inverse.MonotoneGraph
import DifferentialGeometry.Analysis.Elliptic.Planar.PolarPhysicalArc
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

noncomputable section

open Set Filter Metric
open scoped Topology ContDiff

namespace DifferentialGeometry.Analysis

private theorem exists_negative_root_rectangle
    {ε : ℝ} (hε : 0 < ε) {F D : ℝ × ℝ → ℝ} {t₀ : ℝ}
    (hF : ContinuousOn F (Ico 0 ε ×ˢ (univ : Set ℝ)))
    (hD : ContinuousOn D (Ico 0 ε ×ˢ (univ : Set ℝ)))
    (hd : ∀ r ∈ Ico 0 ε, ∀ t, HasDerivAt (fun s => F (r, s)) (D (r, t)) t)
    (hz : F (0, t₀) = 0) (hneg : D (0, t₀) < 0) :
    ∃ ρ δ : ℝ, 0 < ρ ∧ ρ < ε ∧ 0 < δ ∧
      (∀ r ∈ Icc 0 ρ, ∀ t ∈ Icc (t₀ - δ) (t₀ + δ), D (r, t) < 0) ∧
      (∀ r ∈ Icc 0 ρ, 0 < F (r, t₀ - δ)) ∧
      (∀ r ∈ Icc 0 ρ, F (r, t₀ + δ) < 0) := by
  have h0 : (0, t₀) ∈ Ico 0 ε ×ˢ (univ : Set ℝ) := ⟨⟨le_rfl, hε⟩, mem_univ _⟩
  have hev : {p : ℝ × ℝ | D p < 0} ∈ 𝓝[Ico 0 ε ×ˢ (univ : Set ℝ)] (0, t₀) :=
    hD _ h0 (isOpen_Iio.mem_nhds hneg)
  obtain ⟨η, hη, hηD⟩ := Metric.mem_nhdsWithin_iff.mp hev
  let δ := η / 2
  let ρ₀ := min (ε / 2) (η / 2)
  have hδ : 0 < δ := half_pos hη
  have hρ₀ : 0 < ρ₀ := lt_min (half_pos hε) (half_pos hη)
  have hρ₀ε : ρ₀ < ε := (min_le_left _ _).trans_lt (half_lt_self hε)
  have hrect : ∀ r ∈ Icc 0 ρ₀, ∀ t ∈ Icc (t₀ - δ) (t₀ + δ), D (r, t) < 0 := by
    intro r hr t ht
    apply hηD
    refine ⟨?_, ⟨⟨hr.1, hr.2.trans_lt hρ₀ε⟩, mem_univ _⟩⟩
    rw [mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_zero]
    apply max_lt
    · rw [abs_of_nonneg hr.1]
      exact (hr.2.trans (min_le_right _ _)).trans_lt (half_lt_self hη)
    · have ht' : |t - t₀| ≤ δ := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
      exact ht'.trans_lt (half_lt_self hη)
  have hanti : StrictAntiOn (fun t => F (0, t)) (Icc (t₀ - δ) (t₀ + δ)) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _) (fun t _ => (hd 0 ⟨le_rfl, hε⟩ t).continuousAt.continuousWithinAt)
    intro t ht
    rw [(hd 0 ⟨le_rfl, hε⟩ t).deriv]
    exact hrect 0 ⟨le_rfl, hρ₀.le⟩ t (interior_subset ht)
  have ht₀ : t₀ ∈ Icc (t₀ - δ) (t₀ + δ) := ⟨by linarith, by linarith⟩
  have hleft : 0 < F (0, t₀ - δ) := by
    simpa only [hz] using hanti ⟨le_rfl, by linarith⟩ ht₀ (by linarith)
  have hright : F (0, t₀ + δ) < 0 := by
    simpa only [hz] using hanti ht₀ ⟨by linarith, le_rfl⟩ (by linarith)
  have hslice (t : ℝ) : ContinuousOn (fun r => F (r, t)) (Ico 0 ε) :=
    hF.comp (continuousOn_id.prodMk continuousOn_const) (fun r hr => ⟨hr, mem_univ _⟩)
  have hl : {r : ℝ | 0 < F (r, t₀ - δ)} ∈ 𝓝[Ico 0 ε] 0 :=
    hslice _ 0 ⟨le_rfl, hε⟩ (isOpen_Ioi.mem_nhds hleft)
  have hr : {r : ℝ | F (r, t₀ + δ) < 0} ∈ 𝓝[Ico 0 ε] 0 :=
    hslice _ 0 ⟨le_rfl, hε⟩ (isOpen_Iio.mem_nhds hright)
  obtain ⟨κ, hκ, hκspec⟩ := Metric.mem_nhdsWithin_iff.mp (inter_mem hl hr)
  let ρ := min ρ₀ (κ / 2)
  have hρ : 0 < ρ := lt_min hρ₀ (half_pos hκ)
  have hρsub : Icc (0 : ℝ) ρ ⊆ Icc 0 ρ₀ := Icc_subset_Icc_right (min_le_left _ _)
  have hsides (r : ℝ) (hr : r ∈ Icc 0 ρ) :
      0 < F (r, t₀ - δ) ∧ F (r, t₀ + δ) < 0 := by
    apply hκspec
    refine ⟨?_, ⟨hr.1, (hρsub hr).2.trans_lt hρ₀ε⟩⟩
    rw [mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hr.1]
    exact (hr.2.trans (min_le_right _ _)).trans_lt (half_lt_self hκ)
  exact ⟨ρ, δ, hρ, (min_le_left _ _).trans_lt hρ₀ε, hδ,
    fun r hr => hrect r (hρsub hr), fun r hr => (hsides r hr).1,
    fun r hr => (hsides r hr).2⟩

private theorem exists_continuous_root_on_rectangle
    {ρ l u : ℝ} (hlu : l < u) {F : ℝ × ℝ → ℝ}
    (hF : ContinuousOn F (Icc 0 ρ ×ˢ Icc l u))
    (hanti : ∀ r ∈ Icc 0 ρ, StrictAntiOn (fun t => F (r, t)) (Icc l u))
    (hl : ∀ r ∈ Icc 0 ρ, 0 < F (r, l))
    (hu : ∀ r ∈ Icc 0 ρ, F (r, u) < 0) :
    ∃ θ : ℝ → ℝ, ContinuousOn θ (Icc 0 ρ) ∧
      (∀ r ∈ Icc 0 ρ, θ r ∈ Ioo l u ∧ F (r, θ r) = 0) ∧
      ∀ r ∈ Icc 0 ρ, ∀ t ∈ Icc l u, F (r, t) = 0 ↔ t = θ r := by
  classical
  have hroot (r : ℝ) (hr : r ∈ Icc 0 ρ) : ∃ t ∈ Ioo l u, F (r, t) = 0 := by
    have hc : ContinuousOn (fun t => F (r, t)) (Icc l u) :=
      hF.comp (continuousOn_const.prodMk continuousOn_id) (fun t ht => ⟨hr, ht⟩)
    obtain ⟨t, ht, hFt⟩ := intermediate_value_Icc' hlu.le hc ⟨(hu r hr).le, (hl r hr).le⟩
    refine ⟨t, ⟨lt_of_le_of_ne ht.1 ?_, lt_of_le_of_ne ht.2 ?_⟩, hFt⟩
    · intro he
      rw [← he] at hFt
      exact (hl r hr).ne' hFt
    · intro he
      rw [he] at hFt
      exact (hu r hr).ne hFt
  let θ : ℝ → ℝ := fun r => if hr : r ∈ Icc 0 ρ then (hroot r hr).choose else 0
  have hspec (r : ℝ) (hr : r ∈ Icc 0 ρ) : θ r ∈ Ioo l u ∧ F (r, θ r) = 0 := by
    simp only [θ, dite_eq_left hr]
    exact (hroot r hr).choose_spec
  have huniq (r : ℝ) (hr : r ∈ Icc 0 ρ) (t : ℝ) (ht : t ∈ Icc l u) :
      F (r, t) = 0 ↔ t = θ r := by
    constructor
    · intro h
      exact (hanti r hr).injOn ht (Ioo_subset_Icc_self (hspec r hr).1)
        (h.trans (hspec r hr).2.symm)
    · rintro rfl
      exact (hspec r hr).2
  refine ⟨θ, ?_, hspec, huniq⟩
  let D := Icc (0 : ℝ) ρ ×ˢ Icc l u
  let : CompactSpace D := isCompact_iff_compactSpace.mp (isCompact_Icc.prod isCompact_Icc)
  let T : D → ℝ × ℝ := fun p => (p.1.1, F p.1)
  have hT : Continuous T := (continuous_fst.comp continuous_subtype_val).prodMk hF.domRestrict
  have hTi : Function.Injective T := by
    intro p q heq
    have hr := (Prod.mk.inj heq).1
    apply Subtype.ext
    apply Prod.ext hr
    apply (hanti p.1.1 p.2.1).injOn p.2.2 q.2.2
    have hf := (Prod.mk.inj heq).2
    change F (p.1.1, p.1.2) = F (q.1.1, q.1.2) at hf
    rwa [← hr] at hf
  let G : Icc (0 : ℝ) ρ → D := fun r =>
    ⟨(r.1, θ r.1), r.2, Ioo_subset_Icc_self (hspec r.1 r.2).1⟩
  have hTG : T ∘ G = (fun r : Icc (0 : ℝ) ρ => (r.1, (0 : ℝ))) := by
    funext r
    exact Prod.ext rfl (hspec r.1 r.2).2
  have hG : Continuous G := (hT.isClosedEmbedding hTi).isEmbedding.continuous_iff.mpr
    (hTG ▸ continuous_subtype_val.prodMk continuous_const)
  exact continuousOn_iff_continuous_domRestrict.mpr
    (continuous_snd.comp (continuous_subtype_val.comp hG))

private theorem weighted_derivative_tendsto_zero
    {ε : ℝ} (hε : 0 < ε) {W A R : ℝ × ℝ → ℝ} {θ : ℝ → ℝ} {θ₀ : ℝ}
    (hA : ContinuousOn A (Ico 0 ε ×ˢ (univ : Set ℝ)))
    (hR : ContinuousOn R (Ico 0 ε ×ˢ (univ : Set ℝ)))
    (hW : ContDiffOn ℝ 1 W (Ioo 0 ε ×ˢ (univ : Set ℝ)))
    (hd : ∀ r ∈ Ico 0 ε, ∀ t, HasDerivAt (fun s => W (r, s)) (A (r, t)) t)
    (hRzero : R (0, θ₀) = 0)
    (hReq : ∀ r ∈ Ioo 0 ε, ∀ t, R (r, t) = r * fderiv ℝ W (r, t) (1, 0))
    (hAne : A (0, θ₀) ≠ 0) (hθzero : θ 0 = θ₀)
    (hθc : ContinuousOn θ (Ico 0 ε)) (hθd : ContDiffOn ℝ 1 θ (Ioo 0 ε))
    (hroot : ∀ r ∈ Ico 0 ε, W (r, θ r) = 0) :
    Tendsto (fun r => r * deriv θ r) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hθt : Tendsto θ (𝓝[>] (0 : ℝ)) (𝓝 θ₀) := by
    have hc := (hθc 0 ⟨le_rfl, hε⟩).mono Ioo_subset_Ico_self
    rwa [ContinuousWithinAt, nhdsWithin_Ioo_eq_nhdsGT hε, hθzero] at hc
  have hp : Tendsto (fun r => (r, θ r)) (𝓝[>] (0 : ℝ))
      (𝓝[Ico 0 ε ×ˢ (univ : Set ℝ)] (0, θ₀)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨(tendsto_id.mono_left nhdsWithin_le_nhds).prodMk_nhds hθt, ?_⟩
    filter_upwards [Ioo_mem_nhdsGT hε] with r hr
    exact ⟨⟨hr.1.le, hr.2⟩, mem_univ _⟩
  have hAt := Filter.Tendsto.comp (hA (0, θ₀) ⟨⟨le_rfl, hε⟩, mem_univ _⟩) hp
  have hRt := Filter.Tendsto.comp (hR (0, θ₀) ⟨⟨le_rfl, hε⟩, mem_univ _⟩) hp
  have hlim : Tendsto (fun r => -R (r, θ r) / A (r, θ r)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    convert hRt.neg.div hAt hAne using 1
    · ext r
      rfl
    · simp only [hRzero, neg_zero, zero_div]
  apply hlim.congr'
  filter_upwards [Ioo_mem_nhdsGT hε, hAt.eventually_ne hAne] with r hr hAr
  have hwd : DifferentiableAt ℝ W (r, θ r) :=
    (hW.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨hr, mem_univ _⟩)).differentiableAt (by simp)
  have hθder : HasDerivAt θ (deriv θ r) r :=
    ((hθd.contDiffAt (isOpen_Ioo.mem_nhds hr)).differentiableAt (by simp)).hasDerivAt
  have hangular : fderiv ℝ W (r, θ r) (0, 1) = A (r, θ r) := by
    have hdcomp := hwd.hasFDerivAt.comp_hasDerivAt (θ r)
      ((hasDerivAt_const (θ r) r).prodMk (hasDerivAt_id (θ r)))
    exact hdcomp.unique (hd r ⟨hr.1.le, hr.2⟩ (θ r))
  have hchain := hwd.hasFDerivAt.comp_hasDerivAt r ((hasDerivAt_id r).prodMk hθder)
  have hconst : HasDerivAt (fun s => W (s, θ s)) 0 r := by
    apply (hasDerivAt_const r (0 : ℝ)).congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds hr] with s hs
    exact hroot s ⟨hs.1.le, hs.2⟩
  have hz : fderiv ℝ W (r, θ r) (1, deriv θ r) = 0 := hchain.unique hconst
  have hsplit : ((1 : ℝ), deriv θ r) = (1, 0) + deriv θ r • ((0 : ℝ), (1 : ℝ)) := by ext <;> simp
  rw [hsplit, map_add, map_smul, hangular, smul_eq_mul] at hz
  symm
  apply (eq_div_iff hAr).mpr
  calc
    (r * deriv θ r) * A (r, θ r) = r * (deriv θ r * A (r, θ r)) := by ring
    _ = r * (-fderiv ℝ W (r, θ r) (1, 0)) := by congr 1; linarith
    _ = -R (r, θ r) := by rw [hReq r hr]; ring

private theorem exists_continuous_polar_root_of_simple_angular_zero
    {ε : ℝ} (hε : 0 < ε) {W A R : ℝ × ℝ → ℝ} {θ₀ : ℝ}
    (hWc : ContinuousOn W (Ico 0 ε ×ˢ (univ : Set ℝ)))
    (hAc : ContinuousOn A (Ico 0 ε ×ˢ (univ : Set ℝ)))
    (hRc : ContinuousOn R (Ico 0 ε ×ˢ (univ : Set ℝ)))
    (hWd : ContDiffOn ℝ 1 W (Ioo 0 ε ×ˢ (univ : Set ℝ)))
    (hd : ∀ r ∈ Ico 0 ε, ∀ t, HasDerivAt (fun s => W (r, s)) (A (r, t)) t)
    (hRzero : ∀ t, R (0, t) = 0)
    (hReq : ∀ r ∈ Ioo 0 ε, ∀ t, R (r, t) = r * fderiv ℝ W (r, t) (1, 0))
    (hWzero : W (0, θ₀) = 0) (hAne : A (0, θ₀) ≠ 0) :
    ∃ ρ δ : ℝ, ∃ θ : ℝ → ℝ, 0 < ρ ∧ ρ ≤ ε ∧ 0 < δ ∧ θ 0 = θ₀ ∧
      ContinuousOn θ (Ico 0 ρ) ∧ ContDiffOn ℝ 1 θ (Ioo 0 ρ) ∧
      (∀ r ∈ Ico 0 ρ, |θ r - θ₀| < δ ∧ W (r, θ r) = 0) ∧
      (∀ r ∈ Ico 0 ρ, ∀ t, |t - θ₀| < δ → (W (r, t) = 0 ↔ t = θ r)) ∧
      Tendsto (fun r => r * deriv θ r) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  let F : ℝ × ℝ → ℝ := fun p => -A (0, θ₀) * W p
  let D : ℝ × ℝ → ℝ := fun p => -A (0, θ₀) * A p
  have hFc : ContinuousOn F (Ico 0 ε ×ˢ (univ : Set ℝ)) := continuousOn_const.mul hWc
  have hDc : ContinuousOn D (Ico 0 ε ×ˢ (univ : Set ℝ)) := continuousOn_const.mul hAc
  have hdF (r : ℝ) (hr : r ∈ Ico 0 ε) (t : ℝ) :
      HasDerivAt (fun s => F (r, s)) (D (r, t)) t := (hd r hr t).const_mul _
  have hFzero : F (0, θ₀) = 0 := by simp only [F, hWzero, mul_zero]
  have hDneg : D (0, θ₀) < 0 := by
    dsimp only [D]
    nlinarith [sq_pos_of_ne_zero hAne]
  have hFiff (p : ℝ × ℝ) : F p = 0 ↔ W p = 0 := by
    simp only [F, mul_eq_zero, neg_eq_zero, hAne, false_or]
  obtain ⟨ρ, δ, hρ, hρε, hδ, hneg, hl, hu⟩ :=
    exists_negative_root_rectangle hε hFc hDc hdF hFzero hDneg
  have hsub : Icc (0 : ℝ) ρ ⊆ Ico 0 ε := fun r hr => ⟨hr.1, hr.2.trans_lt hρε⟩
  have hrect : ContinuousOn F (Icc 0 ρ ×ˢ Icc (θ₀ - δ) (θ₀ + δ)) :=
    hFc.mono (prod_mono hsub (subset_univ _))
  have hslice (r : ℝ) (hr : r ∈ Icc 0 ρ) :
      ContinuousOn (fun t => F (r, t)) (Icc (θ₀ - δ) (θ₀ + δ)) :=
    fun t _ => (hdF r (hsub hr) t).continuousAt.continuousWithinAt
  have hanti (r : ℝ) (hr : r ∈ Icc 0 ρ) :
      StrictAntiOn (fun t => F (r, t)) (Icc (θ₀ - δ) (θ₀ + δ)) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _) (hslice r hr)
    intro t ht
    rw [(hdF r (hsub hr) t).deriv]
    exact hneg r hr t (interior_subset ht)
  obtain ⟨θ, hθc, hspec, huniq⟩ := exists_continuous_root_on_rectangle
    (by linarith : θ₀ - δ < θ₀ + δ) hrect hanti hl hu
  have hθzero : θ 0 = θ₀ :=
    ((huniq 0 ⟨le_rfl, hρ.le⟩ θ₀ ⟨by linarith, by linarith⟩).mp hFzero).symm
  have hFcd : ContDiffOn ℝ 1 F (Ioo 0 ρ ×ˢ Ioo (θ₀ - δ) (θ₀ + δ)) :=
    contDiffOn_const.mul (hWd.mono (fun p hp => ⟨⟨hp.1.1, hp.1.2.trans hρε⟩, mem_univ _⟩))
  obtain ⟨ψ, hψd, hψspec, _⟩ := exists_contDiffOn_implicit_graph_of_deriv_neg
    (by decide : (1 : ℕ∞ω) ≠ 0) isOpen_Ioo (by linarith : θ₀ - δ < θ₀ + δ)
    hFcd (fun r hr => hslice r (Ioo_subset_Icc_self hr))
    (fun r hr t ht => by
      rw [(hdF r ⟨hr.1.le, hr.2.trans hρε⟩ t).deriv]
      exact hneg r (Ioo_subset_Icc_self hr) t (Ioo_subset_Icc_self ht))
    (fun r hr => hl r (Ioo_subset_Icc_self hr))
    (fun r hr => hu r (Ioo_subset_Icc_self hr))
  have hθd : ContDiffOn ℝ 1 θ (Ioo 0 ρ) := by
    apply hψd.congr
    intro r hr
    exact ((huniq r (Ioo_subset_Icc_self hr) (ψ r)
      (Ioo_subset_Icc_self (hψspec r hr).1)).mp (hψspec r hr).2).symm
  have hθc' : ContinuousOn θ (Ico 0 ρ) := hθc.mono Ico_subset_Icc_self
  have hroot (r : ℝ) (hr : r ∈ Ico 0 ρ) : W (r, θ r) = 0 :=
    (hFiff _).mp (hspec r (Ico_subset_Icc_self hr)).2
  refine ⟨ρ, δ, θ, hρ, hρε.le, hδ, hθzero, hθc', hθd, ?_, ?_, ?_⟩
  · intro r hr
    have ht := (hspec r (Ico_subset_Icc_self hr)).1
    exact ⟨abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩, hroot r hr⟩
  · intro r hr t ht
    have ht' := abs_lt.mp ht
    exact (hFiff _).symm.trans (huniq r (Ico_subset_Icc_self hr) t
      ⟨by linarith [ht'.1], by linarith [ht'.2]⟩)
  · exact weighted_derivative_tendsto_zero hρ
      (hAc.mono (prod_mono (fun r hr => ⟨hr.1, hr.2.trans hρε⟩) (Subset.refl _)))
      (hRc.mono (prod_mono (fun r hr => ⟨hr.1, hr.2.trans hρε⟩) (Subset.refl _)))
      (hWd.mono (prod_mono (fun r hr => ⟨hr.1, hr.2.trans hρε⟩) (Subset.refl _)))
      (fun r hr => hd r ⟨hr.1, hr.2.trans hρε⟩) (hRzero θ₀)
      (fun r hr => hReq r ⟨hr.1, hr.2.trans hρε⟩) hAne hθzero hθc' hθd hroot

/-- A simple angular zero extends to a unique continuous polar root and a physical `C¹` arc.
Only the positive-radius equation is `C¹`; no radial differentiability at zero is assumed. -/
theorem exists_polar_root_arc_of_simple_angular_zero
    {ε : ℝ} (hε : 0 < ε) {W A R : ℝ × ℝ → ℝ} {θ₀ : ℝ}
    (hWc : ContinuousOn W (Ico 0 ε ×ˢ (univ : Set ℝ)))
    (hAc : ContinuousOn A (Ico 0 ε ×ˢ (univ : Set ℝ)))
    (hRc : ContinuousOn R (Ico 0 ε ×ˢ (univ : Set ℝ)))
    (hWd : ContDiffOn ℝ 1 W (Ioo 0 ε ×ˢ (univ : Set ℝ)))
    (hd : ∀ r ∈ Ico 0 ε, ∀ t, HasDerivAt (fun s => W (r, s)) (A (r, t)) t)
    (hRzero : ∀ t, R (0, t) = 0)
    (hReq : ∀ r ∈ Ioo 0 ε, ∀ t, R (r, t) = r * fderiv ℝ W (r, t) (1, 0))
    (hWzero : W (0, θ₀) = 0) (hAne : A (0, θ₀) ≠ 0) :
    ∃ ρ δ : ℝ, ∃ θ : ℝ → ℝ, ∃ Γ : ℝ → ℂ,
      0 < ρ ∧ ρ ≤ ε ∧ 0 < δ ∧ θ 0 = θ₀ ∧
      ContinuousOn θ (Ico 0 ρ) ∧ ContDiffOn ℝ 1 θ (Ioo 0 ρ) ∧
      (∀ r ∈ Ico 0 ρ, |θ r - θ₀| < δ ∧ W (r, θ r) = 0) ∧
      (∀ r ∈ Ico 0 ρ, ∀ t, |t - θ₀| < δ → (W (r, t) = 0 ↔ t = θ r)) ∧
      Tendsto (fun r => r * deriv θ r) (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
      Γ 0 = 0 ∧
      (∀ r ∈ Ico 0 ρ, Γ r = (r : ℂ) * Complex.exp ((θ r : ℂ) * Complex.I)) ∧
      ContDiffOn ℝ 1 Γ (Ioo (-ρ) ρ) ∧
      HasDerivAt Γ (Complex.exp ((θ₀ : ℂ) * Complex.I)) 0 := by
  obtain ⟨ρ, δ, θ, hρ, hρε, hδ, hθzero, hθc, hθd, hroot, huniq, hweighted⟩ :=
    exists_continuous_polar_root_of_simple_angular_zero
      hε hWc hAc hRc hWd hd hRzero hReq hWzero hAne
  obtain ⟨Γ, hΓzero, hΓeq, hΓd, hΓderiv⟩ :=
    exists_contDiff_polar_physical_arc hρ hθzero hθc hθd hweighted
  exact ⟨ρ, δ, θ, Γ, hρ, hρε, hδ, hθzero, hθc, hθd,
    hroot, huniq, hweighted, hΓzero, hΓeq, hΓd, hΓderiv⟩

end DifferentialGeometry.Analysis
