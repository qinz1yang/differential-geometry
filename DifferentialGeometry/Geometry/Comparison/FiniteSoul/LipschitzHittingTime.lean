import DifferentialGeometry.Geometry.Comparison.FiniteSoul.HittingTime
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Locally Lipschitz hitting times and Lipschitz level-set graphs (S-HIT, disposition D4)

Package CM-S (finite soul), lane CMS-T. Blueprint master207A LFR23 (A:26800–26806: "The hitting
time is unique and continuous. In each smooth flow box it is Lipschitz, because distance is
locally Lipschitz and the increase in the flow direction has a fixed positive lower bound. The
distance level is therefore a Lipschitz graph in that flow box.")

Kernel (metric space `X`, the data of lane CMS-H's `exists_hittingTime_band_product`): a jointly
continuous flow `Φ` with the group law, a continuous `η` increasing at rate `κ > 0` along orbit
segments inside an open `U ⊇ η⁻¹[a, b]`.

* `locallyLipschitzOn_hittingTime`: if `η` and the flow map `(t, x) ↦ Φ t x` are locally
  Lipschitz, the hitting time `(x, s) ↦ τ(x, s)` is locally Lipschitz on `η⁻¹[a, b] × [a, b]`:
  `κ |τ(x, s) − τ(y, s')| ≤ |s − s'| + L_η L_Φ d(x, y)`.
* `eq_iff_eq_hittingTime`: the level `{η = s}` read in flow coordinates `(x, t) ↦ Φ t x` is the
  graph `t = τ(x, s)` (uniqueness of the crossing time).
* `locallyLipschitz_hittingTime_comp`: for every locally Lipschitz transversal `σ : W → X` into
  the band, the graph function `w ↦ τ(σ w, s)` of the level in the flow box `(w, t) ↦ Φ t (σ w)` is
  locally Lipschitz.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped NNReal

namespace DifferentialGeometry.Geometry.FiniteSoul

variable {X : Type*} [MetricSpace X] {Φ : ℝ → X → X} {η : X → ℝ} {U : Set X} {a b κ : ℝ}

/-- **The level set in flow coordinates is the graph of the hitting time**: for a point `x` of
the band and an orbit segment `Φ_{[0, t]} x` inside `U`, `η (Φ t x) = s ↔ t = τ(x, s)`. -/
theorem eq_iff_eq_hittingTime (hΦ : Continuous (fun p : ℝ × X => Φ p.1 p.2))
    (hΦ0 : ∀ x, Φ 0 x = x) (hΦadd : ∀ s t x, Φ (s + t) x = Φ s (Φ t x))
    (hη : Continuous η) (hU : IsOpen U) (hκ : 0 < κ) (hbandU : η ⁻¹' Icc a b ⊆ U)
    (hrate : ∀ x t, 0 ≤ t → (∀ s ∈ Icc 0 t, Φ s x ∈ U) → η x + κ * t ≤ η (Φ t x))
    {x : X} (hx : η x ∈ Icc a b) {s : ℝ} (hs : s ∈ Icc a b) {t : ℝ}
    (htU : ∀ u ∈ uIcc 0 t, Φ u x ∈ U) : η (Φ t x) = s ↔ t = hittingTime Φ η x s := by
  constructor
  · intro hts
    exact (hittingTime_eq_of_forall_mem hΦ hΦ0 hΦadd hη hU hκ hbandU hrate hx hs htU hts).symm
  · rintro rfl
    exact (hittingTime_spec hΦ hΦ0 hΦadd hη hU hκ hbandU hrate hx hs).1

/-- **The hitting time is locally Lipschitz** when `η` and the flow map are locally Lipschitz. -/
theorem locallyLipschitzOn_hittingTime (hΦ : Continuous (fun p : ℝ × X => Φ p.1 p.2))
    (hΦ0 : ∀ x, Φ 0 x = x) (hΦadd : ∀ s t x, Φ (s + t) x = Φ s (Φ t x))
    (hη : Continuous η) (hU : IsOpen U) (hκ : 0 < κ) (hbandU : η ⁻¹' Icc a b ⊆ U)
    (hrate : ∀ x t, 0 ≤ t → (∀ s ∈ Icc 0 t, Φ s x ∈ U) → η x + κ * t ≤ η (Φ t x))
    (hηL : LocallyLipschitz η) (hΦL : LocallyLipschitz (fun p : ℝ × X => Φ p.1 p.2)) :
    LocallyLipschitzOn ((η ⁻¹' Icc a b) ×ˢ Icc a b)
      (fun p : X × ℝ => hittingTime Φ η p.1 p.2) := by
  rintro ⟨x₀, s₀⟩ ⟨hx₀, hs₀⟩
  set S := (η ⁻¹' Icc a b) ×ˢ Icc a b with hS
  set τ := fun p : X × ℝ => hittingTime Φ η p.1 p.2 with hτ
  set t₀ := hittingTime Φ η x₀ s₀ with ht₀
  obtain ⟨-, h2⟩ := hittingTime_spec hΦ hΦ0 hΦadd hη hU hκ hbandU hrate hx₀ hs₀
  rw [← ht₀] at h2
  -- a thickened orbit interval stays in `U`, uniformly near `x₀`
  have hW : IsOpen {u : ℝ | Φ u x₀ ∈ U} :=
    hU.preimage (hΦ.comp (continuous_id.prodMk continuous_const))
  obtain ⟨δ, hδ, hδW⟩ := exists_pos_Icc_sub_add_subset hW
    (fun u hu => hbandU (uIcc_subset_Icc hx₀ hs₀ (h2 u hu))) (min_le_max : min 0 t₀ ≤ max 0 t₀)
  set Hδ := Icc (min 0 t₀ - δ) (max 0 t₀ + δ) with hHδ
  have htube : ∀ᶠ x in 𝓝 x₀, ∀ u ∈ Hδ, Φ u x ∈ U := by
    refine isCompact_Icc.eventually_forall_of_forall_eventually fun u hu => ?_
    have hc : Continuous (fun z : X × ℝ => Φ z.2 z.1) := hΦ.comp (continuous_snd.prodMk continuous_fst)
    exact hc.continuousAt.preimage_mem_nhds (hU.mem_nhds (hδW hu))
  -- local Lipschitz constants
  obtain ⟨Lη, Nη, hNη, hLη⟩ := hηL (Φ t₀ x₀)
  obtain ⟨LΦ, NΦ, hNΦ, hLΦ⟩ := hΦL (t₀, x₀)
  have hbox : NΦ ∩ (fun p : ℝ × X => Φ p.1 p.2) ⁻¹' Nη ∈ 𝓝 ((t₀, x₀) : ℝ × X) :=
    inter_mem hNΦ (hΦ.continuousAt.preimage_mem_nhds hNη)
  obtain ⟨ρ, hρ, hρbox⟩ := Metric.mem_nhds_iff.mp hbox
  set ε' := min ρ δ / 2 with hε'
  have hε'pos : 0 < ε' := by positivity
  have hε'ρ : ε' < ρ := by have := min_le_left ρ δ; linarith
  have hε'δ : ε' < δ := by have := min_le_right ρ δ; linarith
  -- continuity of the hitting time
  have hτc := continuousOn_hittingTime hΦ hΦ0 hΦadd hη hU hκ hbandU hrate (x₀, s₀) ⟨hx₀, hs₀⟩
  have hτnear : ∀ᶠ p in 𝓝[S] ((x₀, s₀) : X × ℝ), τ p ∈ Ioo (t₀ - ε') (t₀ + ε') :=
    hτc (Ioo_mem_nhds (by linarith) (by linarith))
  have hxnear : ∀ᶠ p in 𝓝[S] ((x₀, s₀) : X × ℝ), p.1 ∈ ball x₀ ρ ∧ ∀ u ∈ Hδ, Φ u p.1 ∈ U :=
    nhdsWithin_le_nhds ((continuous_fst.tendsto ((x₀, s₀) : X × ℝ)).eventually
      ((show ∀ᶠ x in 𝓝 x₀, x ∈ ball x₀ ρ from ball_mem_nhds x₀ hρ).and htube))
  set N : Set (X × ℝ) := {p | p ∈ S ∧ τ p ∈ Ioo (t₀ - ε') (t₀ + ε') ∧
    p.1 ∈ ball x₀ ρ ∧ ∀ u ∈ Hδ, Φ u p.1 ∈ U} with hN
  have hNmem : N ∈ 𝓝[S] ((x₀, s₀) : X × ℝ) :=
    ((show ∀ᶠ p in 𝓝[S] ((x₀, s₀) : X × ℝ), p ∈ S from self_mem_nhdsWithin).and
      (hτnear.and hxnear)).mono fun p hp => ⟨hp.1, hp.2.1, hp.2.2⟩
  set K : ℝ≥0 := ⟨κ⁻¹ * (1 + Lη * LΦ), by positivity⟩ with hK
  refine ⟨K, N, hNmem, LipschitzOnWith.of_dist_le_mul fun p hp q hq => ?_⟩
  obtain ⟨⟨hpx, hps⟩, hpτ, hpρ, -⟩ := hp
  obtain ⟨⟨hqx, hqs⟩, hqτ, hqρ, hqU⟩ := hq
  set t := τ p with htdef
  set t' := τ q with ht'def
  have hpt : η (Φ t p.1) = p.2 := (hittingTime_spec hΦ hΦ0 hΦadd hη hU hκ hbandU hrate hpx hps).1
  have hqt : η (Φ t' q.1) = q.2 := (hittingTime_spec hΦ hΦ0 hΦadd hη hU hκ hbandU hrate hqx hqs).1
  -- both times lie in the thickened interval
  have hmemH : ∀ u, u ∈ Ioo (t₀ - ε') (t₀ + ε') → u ∈ Hδ := fun u hu =>
    ⟨by have := min_le_right 0 t₀; linarith [hu.1], by have := le_max_right 0 t₀; linarith [hu.2]⟩
  have hseg : ∀ u ∈ uIcc t t', Φ u q.1 ∈ U := fun u hu =>
    hqU u (by
      rcases le_total t t' with h | h
      · rw [uIcc_of_le h] at hu
        exact ⟨(hmemH t hpτ).1.trans hu.1, hu.2.trans (hmemH t' hqτ).2⟩
      · rw [uIcc_of_ge h] at hu
        exact ⟨(hmemH t' hqτ).1.trans hu.1, hu.2.trans (hmemH t hpτ).2⟩)
  -- the rate along the orbit of `q.1` between `t` and `t'`
  have hrate' : κ * |t - t'| ≤ |q.2 - η (Φ t q.1)| := by
    rcases le_total t t' with h | h
    · have hr := add_mul_le_of_forall_mem_Icc hΦadd hrate h
        (fun u hu => hseg u (by rw [uIcc_of_le h]; exact hu))
      rw [hqt] at hr
      rw [abs_of_nonpos (by linarith), abs_of_nonneg (by nlinarith)]
      linarith
    · have hr := add_mul_le_of_forall_mem_Icc hΦadd hrate h
        (fun u hu => hseg u (by rw [uIcc_of_ge h]; exact hu))
      rw [hqt] at hr
      rw [abs_of_nonneg (by linarith), abs_of_nonpos (by nlinarith)]
      linarith
  -- the Lipschitz estimate of `η ∘ Φ_t`
  have hboxp : ((t, p.1) : ℝ × X) ∈ NΦ ∩ (fun p : ℝ × X => Φ p.1 p.2) ⁻¹' Nη := hρbox (by
    rw [mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq]
    exact ⟨by rw [abs_lt]; constructor <;> linarith [hpτ.1, hpτ.2], hpρ⟩)
  have hboxq : ((t, q.1) : ℝ × X) ∈ NΦ ∩ (fun p : ℝ × X => Φ p.1 p.2) ⁻¹' Nη := hρbox (by
    rw [mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq]
    exact ⟨by rw [abs_lt]; constructor <;> linarith [hpτ.1, hpτ.2], hqρ⟩)
  have hΦd : dist (Φ t p.1) (Φ t q.1) ≤ LΦ * dist p.1 q.1 := by
    have := hLΦ.dist_le_mul _ hboxp.1 _ hboxq.1
    simpa [Prod.dist_eq] using this
  have hηd : |η (Φ t p.1) - η (Φ t q.1)| ≤ Lη * (LΦ * dist p.1 q.1) := by
    have := hLη.dist_le_mul _ hboxp.2 _ hboxq.2
    rw [Real.dist_eq] at this
    exact this.trans (mul_le_mul_of_nonneg_left hΦd Lη.coe_nonneg)
  -- conclusion
  have hd1 : dist p.1 q.1 ≤ dist p q := by rw [Prod.dist_eq]; exact le_max_left _ _
  have hd2 : |p.2 - q.2| ≤ dist p q := by
    rw [← Real.dist_eq, Prod.dist_eq]; exact le_max_right _ _
  have hsum : |q.2 - η (Φ t q.1)| ≤ |p.2 - q.2| + Lη * (LΦ * dist p.1 q.1) := by
    have e : q.2 - η (Φ t q.1) = (q.2 - p.2) + (η (Φ t p.1) - η (Φ t q.1)) := by
      rw [hpt]; ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_sub_comm q.2 p.2]
    linarith
  rw [Real.dist_eq]
  change |t - t'| ≤ κ⁻¹ * (1 + Lη * LΦ) * dist p q
  have hLL : 0 ≤ (Lη : ℝ) * LΦ := by positivity
  rw [mul_assoc, ← div_eq_inv_mul, le_div_iff₀ hκ]
  have : |p.2 - q.2| + Lη * (LΦ * dist p.1 q.1) ≤ (1 + Lη * LΦ) * dist p q := by
    have h3 : (Lη : ℝ) * (LΦ * dist p.1 q.1) ≤ Lη * LΦ * dist p q := by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_left hd1 hLL
    linarith
  linarith

/-- **Lipschitz level-set graphs in flow boxes**: for a locally Lipschitz transversal `σ` into the
band, the graph function `w ↦ τ(σ w, s)` of the level `{η = s}` in the flow box
`(w, t) ↦ Φ t (σ w)` (`eq_iff_eq_hittingTime`) is locally Lipschitz. -/
theorem locallyLipschitz_hittingTime_comp (hΦ : Continuous (fun p : ℝ × X => Φ p.1 p.2))
    (hΦ0 : ∀ x, Φ 0 x = x) (hΦadd : ∀ s t x, Φ (s + t) x = Φ s (Φ t x))
    (hη : Continuous η) (hU : IsOpen U) (hκ : 0 < κ) (hbandU : η ⁻¹' Icc a b ⊆ U)
    (hrate : ∀ x t, 0 ≤ t → (∀ s ∈ Icc 0 t, Φ s x ∈ U) → η x + κ * t ≤ η (Φ t x))
    (hηL : LocallyLipschitz η) (hΦL : LocallyLipschitz (fun p : ℝ × X => Φ p.1 p.2))
    {W : Type*} [MetricSpace W] {σ : W → X} (hσ : LocallyLipschitz σ)
    (hσband : ∀ w, η (σ w) ∈ Icc a b) {s : ℝ} (hs : s ∈ Icc a b) :
    LocallyLipschitz (fun w => hittingTime Φ η (σ w) s) := by
  intro w₀
  obtain ⟨K, N, hN, hKN⟩ := locallyLipschitzOn_hittingTime hΦ hΦ0 hΦadd hη hU hκ hbandU hrate
    hηL hΦL (show ((σ w₀, s) : X × ℝ) ∈ (η ⁻¹' Icc a b) ×ˢ Icc a b from ⟨hσband w₀, hs⟩)
  obtain ⟨Kσ, Nσ, hNσ, hKσ⟩ := hσ w₀
  have hσc : ContinuousAt σ w₀ := by
    obtain ⟨V, hVsub, hVo, hw₀V⟩ := _root_.mem_nhds_iff.mp hNσ
    exact ((hKσ.mono hVsub).continuousOn).continuousAt (hVo.mem_nhds hw₀V)
  have hmap : Tendsto (fun w => ((σ w, s) : X × ℝ)) (𝓝 w₀)
      (𝓝[(η ⁻¹' Icc a b) ×ˢ Icc a b] ((σ w₀, s) : X × ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨(hσc.prodMk continuousAt_const).tendsto,
      Eventually.of_forall fun w => ⟨hσband w, hs⟩⟩
  refine ⟨K * Kσ, Nσ ∩ (fun w => ((σ w, s) : X × ℝ)) ⁻¹' N, inter_mem hNσ (hmap hN),
    LipschitzOnWith.of_dist_le_mul fun w hw w' hw' => ?_⟩
  have h1 := hKN.dist_le_mul _ hw.2 _ hw'.2
  have h2 := hKσ.dist_le_mul _ hw.1 _ hw'.1
  have h3 : dist ((σ w, s) : X × ℝ) (σ w', s) = dist (σ w) (σ w') := by
    simp [Prod.dist_eq]
  rw [h3] at h1
  calc dist (hittingTime Φ η (σ w) s) (hittingTime Φ η (σ w') s) ≤ K * dist (σ w) (σ w') := h1
    _ ≤ K * (Kσ * dist w w') := mul_le_mul_of_nonneg_left h2 K.coe_nonneg
    _ = ↑(K * Kσ) * dist w w' := by push_cast; ring

end DifferentialGeometry.Geometry.FiniteSoul
