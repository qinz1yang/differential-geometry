import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The side of an arc end in a curve (lane O-G6C, G2l)

* `exists_strictMonoOn_of_deriv_pos_G6C`: a `C¹` real function with `h' 0 > 0` is strictly
  increasing near `0`;
* **`exists_side_of_arcEnd_G6C`**: let `B` be locally the curve `s : ℝ → H` near `a = s 0`
  (`range s = B ∩ O`, `s` an embedding), `χ : H → ℝ` continuous with `χ ∘ s` strictly increasing on
  `(-δ, δ)` and `χ a = 0`, and `γ` an arc injective on `[0, 1]` in `B` starting at `a`. Then for a
  sign `c = ±1` and an open `N ∋ a`, `γ([0, 1])` is `{c χ ≥ 0}` on `B ∩ N`.
-/

set_option autoImplicit false

open Set Function Topology Filter
open scoped ContDiff

namespace DifferentialGeometry.Topology

/-- **A `C¹` function with positive derivative at `0` is strictly increasing near `0`.** -/
theorem exists_strictMonoOn_of_deriv_pos_G6C {h : ℝ → ℝ} (hh : ContDiff ℝ 1 h)
    (h0 : 0 < deriv h 0) : ∃ δ > 0, StrictMonoOn h (Ioo (-δ) δ) := by
  have hc : Continuous (deriv h) := hh.continuous_deriv le_rfl
  have hmem : {r | 0 < deriv h r} ∈ 𝓝 (0 : ℝ) :=
    (isOpen_lt continuous_const hc).mem_nhds h0
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hmem
  refine ⟨δ, hδ, strictMonoOn_of_deriv_pos (convex_Ioo _ _) hh.continuous.continuousOn ?_⟩
  intro x hx
  rw [interior_Ioo] at hx
  apply hball
  rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
  exact hx

/-- **The side of an arc end in a curve.** -/
theorem exists_side_of_arcEnd_G6C {H : Type*} [TopologicalSpace H] [T2Space H] {B O : Set H}
    {s : ℝ → H}
    (hs : IsEmbedding s) (hO : IsOpen O) (hsr : range s = B ∩ O) {χ : H → ℝ} {δ : ℝ}
    (hδ : 0 < δ) (hmono : StrictMonoOn (χ ∘ s) (Ioo (-δ) δ)) (hχ0 : χ (s 0) = 0) {γ : ℝ → H}
    (hγc : ContinuousOn γ (Icc 0 1)) (hγi : InjOn γ (Icc 0 1)) (hγB : γ '' Icc 0 1 ⊆ B)
    (hγ0 : γ 0 = s 0) :
    ∃ c : ℝ, (c = 1 ∨ c = -1) ∧ ∃ N : Set H, IsOpen N ∧ s 0 ∈ N ∧
      ∀ b ∈ B ∩ N, (b ∈ γ '' Icc 0 1 ↔ 0 ≤ c * χ b) := by
  classical
  -- the curve chart around `a = s 0`
  obtain ⟨N₁, hN₁, hN₁s⟩ := hs.isOpen_iff.mp (isOpen_Ioo (a := -δ) (b := δ))
  have haN₁ : s 0 ∈ N₁ := by
    have : (0 : ℝ) ∈ s ⁻¹' N₁ := by rw [hN₁s]; exact ⟨by linarith, hδ⟩
    exact this
  -- an initial piece `[0, η]` of the arc inside `N₁ ∩ O`
  have hγ0c : ContinuousWithinAt γ (Icc 0 1) 0 := hγc 0 ⟨le_rfl, zero_le_one⟩
  have hmem : γ ⁻¹' (N₁ ∩ O) ∈ 𝓝[Icc 0 1] (0 : ℝ) := by
    apply hγ0c.preimage_mem_nhdsWithin
    have : s 0 ∈ O := by
      have h := mem_range_self (f := s) 0
      rw [hsr] at h
      exact h.2
    rw [hγ0]
    exact (hN₁.inter hO).mem_nhds ⟨haN₁, this⟩
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.mp hmem
  set η := min (ε / 2) (1 / 2) with hηdef
  have hη : 0 < η := lt_min (by linarith) (by norm_num)
  have hη1 : η < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hηε : η < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hI : Icc 0 η ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc le_rfl hη1.le
  have hγI : ∀ t ∈ Icc 0 η, γ t ∈ N₁ ∩ O := fun t ht => by
    apply hball
    refine ⟨?_, hI ht⟩
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
    constructor <;> linarith [ht.1, ht.2]
  have hrange : ∀ t ∈ Icc 0 η, γ t ∈ range s := fun t ht => by
    rw [hsr]
    exact ⟨hγB ⟨t, hI ht, rfl⟩, (hγI t ht).2⟩
  let g : ℝ → ℝ := fun t => if h : γ t ∈ range s then Classical.choose h else 0
  have hg : ∀ t ∈ Icc 0 η, s (g t) = γ t := fun t ht => by
    simp only [g, hrange t ht, ↓reduceDIte]
    exact Classical.choose_spec (hrange t ht)
  have hgδ : ∀ t ∈ Icc 0 η, g t ∈ Ioo (-δ) δ := fun t ht => by
    have : g t ∈ s ⁻¹' N₁ := by
      change s (g t) ∈ N₁
      rw [hg t ht]
      exact (hγI t ht).1
    rwa [hN₁s] at this
  have hgc : ContinuousOn g (Icc 0 η) :=
    hs.isInducing.continuousOn_iff.mpr ((hγc.mono hI).congr fun t ht => hg t ht)
  have hgi : InjOn g (Icc 0 η) := fun t ht t' ht' h =>
    hγi (hI ht) (hI ht') (by rw [← hg t ht, ← hg t' ht', h])
  have h0I : (0 : ℝ) ∈ Icc 0 η := ⟨le_rfl, hη.le⟩
  have hηI : η ∈ Icc 0 η := ⟨hη.le, le_rfl⟩
  have hg0 : g 0 = 0 := hs.injective (by rw [hg 0 h0I, hγ0])
  -- the sign `c`
  obtain ⟨c, hc, hcg, hcr, hivt⟩ : ∃ c : ℝ, (c = 1 ∨ c = -1) ∧
      (∀ t ∈ Icc 0 η, 0 ≤ c * g t) ∧ 0 < c * g η ∧
      (∀ r, 0 ≤ c * r → c * r ≤ c * g η → r ∈ g '' Icc 0 η) := by
    rcases hgc.strictMonoOn_of_injOn_Icc' hη.le hgi with hm | ha
    · refine ⟨1, Or.inl rfl, fun t ht => ?_, ?_, fun r hr0 hr1 => ?_⟩
      · rw [one_mul, ← hg0]
        exact hm.monotoneOn h0I ht ht.1
      · rw [one_mul, ← hg0]
        exact hm h0I hηI hη
      · simp only [one_mul] at hr0 hr1
        exact intermediate_value_Icc hη.le hgc ⟨by rw [hg0]; exact hr0, hr1⟩
    · refine ⟨-1, Or.inr rfl, fun t ht => ?_, ?_, fun r hr0 hr1 => ?_⟩
      · have := ha.antitoneOn h0I ht ht.1
        rw [hg0] at this
        linarith
      · have := ha h0I hηI hη
        rw [hg0] at this
        linarith
      · exact intermediate_value_Icc' hη.le hgc ⟨by linarith, by rw [hg0]; linarith⟩
  -- the sign of `χ ∘ s` is the sign of the parameter
  have hsign : ∀ r ∈ Ioo (-δ) δ, (0 ≤ c * χ (s r) ↔ 0 ≤ c * r) := by
    intro r hr
    have h0δ : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨by linarith, hδ⟩
    have key : (0 ≤ χ (s r) ↔ 0 ≤ r) := by
      constructor
      · intro h
        by_contra hneg
        have := hmono hr h0δ (lt_of_not_ge hneg)
        simp only [comp_apply, hχ0] at this
        linarith
      · intro h
        rcases eq_or_lt_of_le h with rfl | hpos
        · rw [hχ0]
        · have := hmono h0δ hr hpos
          simp only [comp_apply, hχ0] at this
          linarith
    have key' : (χ (s r) ≤ 0 ↔ r ≤ 0) := by
      constructor
      · intro h
        by_contra hpos
        have := hmono h0δ hr (lt_of_not_ge hpos)
        simp only [comp_apply, hχ0] at this
        linarith
      · intro h
        rcases eq_or_lt_of_le h with rfl | hneg
        · rw [hχ0]
        · have := hmono hr h0δ hneg
          simp only [comp_apply, hχ0] at this
          linarith
    rcases hc with rfl | rfl
    · simp only [one_mul]
      exact key
    · constructor
      · intro h
        have : χ (s r) ≤ 0 := by linarith
        linarith [key'.mp this]
      · intro h
        have : r ≤ 0 := by linarith
        linarith [key'.mpr this]
  -- the far part of the arc misses `a`
  have hFc : IsCompact (γ '' Icc η 1) :=
    isCompact_Icc.image_of_continuousOn (hγc.mono (Icc_subset_Icc hη.le le_rfl))
  have haF : s 0 ∉ γ '' Icc η 1 := by
    rintro ⟨t, ht, hts⟩
    have : t = 0 := hγi ⟨by linarith [ht.1], ht.2⟩ ⟨le_rfl, zero_le_one⟩ (by rw [hts, hγ0])
    linarith [ht.1]
  -- the parameter window `(-r₀, r₀)`
  obtain ⟨N₄, hN₄, hN₄s⟩ := hs.isOpen_iff.mp (isOpen_Ioo (a := -(c * g η)) (b := c * g η))
  have haN₄ : s 0 ∈ N₄ := by
    have : (0 : ℝ) ∈ s ⁻¹' N₄ := by rw [hN₄s]; exact ⟨by linarith, hcr⟩
    exact this
  refine ⟨c, hc, N₁ ∩ O ∩ (γ '' Icc η 1)ᶜ ∩ N₄,
    ((hN₁.inter hO).inter hFc.isClosed.isOpen_compl).inter hN₄, ⟨⟨⟨haN₁, ?_⟩, haF⟩, haN₄⟩, ?_⟩
  · have h := mem_range_self (f := s) 0
    rw [hsr] at h
    exact h.2
  rintro b ⟨hbB, ⟨⟨hbN₁, hbO⟩, hbF⟩, hbN₄⟩
  have hbr : b ∈ range s := by
    rw [hsr]
    exact ⟨hbB, hbO⟩
  obtain ⟨r, rfl⟩ := hbr
  have hrδ : r ∈ Ioo (-δ) δ := by
    have : r ∈ s ⁻¹' N₁ := hbN₁
    rwa [hN₁s] at this
  have hr₀ : r ∈ Ioo (-(c * g η)) (c * g η) := by
    have : r ∈ s ⁻¹' N₄ := hbN₄
    rwa [hN₄s] at this
  rw [hsign r hrδ]
  constructor
  · rintro ⟨t, ht, hts⟩
    have htη : t ∈ Icc 0 η := by
      refine ⟨ht.1, le_of_not_gt fun hlt => hbF ⟨t, ⟨hlt.le, ht.2⟩, hts⟩⟩
    have hrt : r = g t := hs.injective (by rw [hg t htη, hts])
    rw [hrt]
    exact hcg t htη
  · intro hr
    have hcr2 : c * r ≤ c * g η := by
      rcases hc with rfl | rfl
      · linarith [hr₀.2]
      · linarith [hr₀.1]
    obtain ⟨t, ht, htr⟩ := hivt r hr hcr2
    exact ⟨t, hI ht, by rw [← hg t ht, htr]⟩

/-- **An affine side function at the end of an arc in a smooth curve**: for a smooth immersed
embedded curve `σ : ℝ¹ → H` onto `B ∩ O` with `σ 0 = a`, an arc `γ` in `B` starting at `a` and a set
`K` agreeing with `γ([0, 1])` near `a`, some `χ = c · ℓ(· − a)` (`ℓ` continuous linear, `c = ±1`)
describes `K` as `{χ ≥ 0}` on `B` near `a`, vanishes on `B` near `a` only at `a`, and has
`(χ ∘ σ ∘ e)'(0) ≠ 0`, the sign of `χ ∘ σ ∘ e` being the sign of `c · r` near `0` (`e : ℝ ≃ ℝ¹`).
-/
theorem exists_side_function_G6C {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {B O K N₀ : Set H} {a : H} {σ : EuclideanSpace ℝ (Fin 1) → H} (hσs : ContDiff ℝ ∞ σ)
    (hσe : IsEmbedding σ) (hσd : ∀ x, Injective (fderiv ℝ σ x)) (hO : IsOpen O)
    (hrσ : range σ = B ∩ O) (hσ0 : σ 0 = a) {γ : ℝ → H} (hγc : ContinuousOn γ (Icc 0 1))
    (hγi : InjOn γ (Icc 0 1)) (hγB : γ '' Icc 0 1 ⊆ B) (hγ0 : γ 0 = a) (hN₀ : IsOpen N₀)
    (haN₀ : a ∈ N₀) (hK : K ∩ N₀ = γ '' Icc 0 1 ∩ N₀) :
    ∃ (ℓ : H →L[ℝ] ℝ) (c : ℝ), (c = 1 ∨ c = -1) ∧ ∃ δ > 0, ∃ N : Set H, IsOpen N ∧ a ∈ N ∧
      (∀ b ∈ B ∩ N, (b ∈ K ↔ 0 ≤ c * ℓ (b - a))) ∧
      (∀ b ∈ B ∩ N, c * ℓ (b - a) = 0 → b = a) ∧
      (∀ r ∈ Ioo (-δ) δ, σ ((ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ).symm.trans
          (EuclideanSpace.equiv (Fin 1) ℝ).symm r) ∈ N ∧
        (c * ℓ (σ ((ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ).symm.trans
          (EuclideanSpace.equiv (Fin 1) ℝ).symm r) - a) < 0 ↔ c * r < 0)) ∧
      ∃ d : ℝ, d ≠ 0 ∧ HasDerivAt (fun r => c * ℓ (σ ((ContinuousLinearEquiv.funUnique (Fin 1) ℝ
        ℝ).symm.trans (EuclideanSpace.equiv (Fin 1) ℝ).symm r) - a)) d 0 := by
  classical
  set e : ℝ ≃L[ℝ] EuclideanSpace ℝ (Fin 1) :=
    (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ).symm.trans (EuclideanSpace.equiv (Fin 1) ℝ).symm
    with he
  set s : ℝ → H := σ ∘ e with hsdef
  have hse : IsEmbedding s := hσe.comp e.toHomeomorph.isEmbedding
  have hsr : range s = B ∩ O := by
    rw [hsdef, e.surjective.range_comp]
    exact hrσ
  have hs0 : s 0 = a := by
    simp only [hsdef, comp_apply, map_zero, hσ0]
  -- the velocity `w = s'(0) ≠ 0` and a functional `ℓ` with `ℓ w > 0`
  have hsd : HasFDerivAt s ((fderiv ℝ σ (e 0)).comp (e : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1))) 0 :=
    ((hσs.differentiable (by simp)) (e 0)).hasFDerivAt.comp 0 e.hasFDerivAt
  set w : H := fderiv ℝ σ (e 0) (e 1) with hwdef
  have hw : w ≠ 0 := by
    intro h0
    have h1 : fderiv ℝ σ (e 0) (e 1) = fderiv ℝ σ (e 0) 0 := by rw [← hwdef, h0, map_zero]
    have := e.injective (hσd (e 0) h1)
    exact one_ne_zero this
  obtain ⟨ℓ, -, hℓw⟩ := exists_dual_vector ℝ w (norm_ne_zero_iff.mpr hw)
  have hℓw' : 0 < ℓ w := by
    rw [hℓw]
    exact_mod_cast norm_pos_iff.mpr hw
  -- `h = ℓ (s · - a)` is strictly increasing near `0`
  set h : ℝ → ℝ := fun r => ℓ (s r - a) with hhdef
  have hsc : ContDiff ℝ 1 s := (hσs.of_le (by simp)).comp e.contDiff
  have hhs : ContDiff ℝ 1 h := ℓ.contDiff.comp (ContDiff.sub hsc contDiff_const)
  have hhd : HasDerivAt h (ℓ w) 0 := by
    have h1 := (hsd.sub_const a).hasDerivAt
    have h2 := ℓ.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
    exact h2
  obtain ⟨δ₀, hδ₀, hmono⟩ :=
    exists_strictMonoOn_of_deriv_pos_G6C hhs (by rw [hhd.deriv]; exact hℓw')
  have hmono' : StrictMonoOn ((fun x => ℓ (x - a)) ∘ s) (Ioo (-δ₀) δ₀) := hmono
  have hχ0 : (fun x => ℓ (x - a)) (s 0) = 0 := by simp only [hs0, sub_self, map_zero]
  obtain ⟨c, hc, Nγ, hNγ, haNγ, hside⟩ := exists_side_of_arcEnd_G6C hse hO hsr hδ₀ hmono' hχ0
    hγc hγi hγB (hγ0.trans hs0.symm)
  rw [hs0] at haNγ
  -- the window `s((-δ₀, δ₀))`
  obtain ⟨N₁, hN₁, hN₁s⟩ := hse.isOpen_iff.mp (isOpen_Ioo (a := -δ₀) (b := δ₀))
  have haN₁ : a ∈ N₁ := by
    have : (0 : ℝ) ∈ s ⁻¹' N₁ := by rw [hN₁s]; exact ⟨by linarith, hδ₀⟩
    rw [← hs0]
    exact this
  have haO : a ∈ O := by
    have h := mem_range_self (f := s) 0
    rw [hsr, hs0] at h
    exact h.2
  set N : Set H := Nγ ∩ N₀ ∩ N₁ ∩ O with hNdef
  have hNo : IsOpen N := ((hNγ.inter hN₀).inter hN₁).inter hO
  have haN : a ∈ N := ⟨⟨⟨haNγ, haN₀⟩, haN₁⟩, haO⟩
  -- the parameters near `0` land in `N`
  have hpre : s ⁻¹' N ∈ 𝓝 (0 : ℝ) := by
    apply (hse.continuous.isOpen_preimage _ hNo).mem_nhds
    change s 0 ∈ N
    rw [hs0]
    exact haN
  obtain ⟨δ₁, hδ₁, hball⟩ := Metric.mem_nhds_iff.mp hpre
  have hh0 : h 0 = 0 := by simp only [hhdef, hs0, sub_self, map_zero]
  have h0δ : (0 : ℝ) ∈ Ioo (-δ₀) δ₀ := ⟨by linarith, hδ₀⟩
  have hsignh : ∀ r ∈ Ioo (-δ₀) δ₀, (h r < 0 ↔ r < 0) ∧ (0 < h r ↔ 0 < r) := by
    intro r hr
    refine ⟨⟨fun hlt => ?_, fun hlt => ?_⟩, ⟨fun hlt => ?_, fun hlt => ?_⟩⟩
    · by_contra hge
      rcases eq_or_lt_of_le (le_of_not_gt hge) with h0 | hpos
      · rw [← h0, hh0] at hlt
        exact lt_irrefl _ hlt
      · have := hmono h0δ hr hpos
        rw [hh0] at this
        linarith
    · have := hmono hr h0δ hlt
      rwa [hh0] at this
    · by_contra hle
      rcases eq_or_lt_of_le (le_of_not_gt hle) with h0 | hneg
      · rw [h0, hh0] at hlt
        exact lt_irrefl _ hlt
      · have := hmono hr h0δ hneg
        rw [hh0] at this
        linarith
    · have := hmono h0δ hr hlt
      rwa [hh0] at this
  refine ⟨ℓ, c, hc, min δ₀ δ₁, lt_min hδ₀ hδ₁, N, hNo, haN, ?_, ?_, ?_,
    ⟨c * ℓ w, mul_ne_zero (by rcases hc with rfl | rfl <;> norm_num) hℓw'.ne', hhd.const_mul c⟩⟩
  · rintro b ⟨hbB, ⟨⟨hbγ, hbN₀⟩, -⟩, -⟩
    rw [← hside b ⟨hbB, hbγ⟩]
    constructor
    · intro hbK
      exact (hK.subset ⟨hbK, hbN₀⟩).1
    · intro hbγ'
      exact (hK.symm.subset ⟨hbγ', hbN₀⟩).1
  · rintro b ⟨hbB, ⟨-, hbN₁⟩, hbO⟩ hb0
    have hbr : b ∈ range s := by
      rw [hsr]
      exact ⟨hbB, hbO⟩
    obtain ⟨r, rfl⟩ := hbr
    have hrδ : r ∈ Ioo (-δ₀) δ₀ := by
      have : r ∈ s ⁻¹' N₁ := hbN₁
      rwa [hN₁s] at this
    have hc0 : c ≠ 0 := by rcases hc with rfl | rfl <;> norm_num
    have hhr : h r = 0 := by
      rcases mul_eq_zero.mp hb0 with h1 | h1
      · exact absurd h1 hc0
      · exact h1
    have hr0 : r = 0 := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hneg | hpos
      · exact absurd hhr (ne_of_lt ((hsignh r hrδ).1.mpr hneg))
      · exact absurd hhr (ne_of_gt ((hsignh r hrδ).2.mpr hpos))
    rw [hr0, hs0]
  · intro r hr
    have hr₀ : r ∈ Ioo (-δ₀) δ₀ := ⟨lt_of_le_of_lt (neg_le_neg (min_le_left _ _)) hr.1,
      lt_of_lt_of_le hr.2 (min_le_left _ _)⟩
    have hr₁ : r ∈ Metric.ball (0 : ℝ) δ₁ := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
      exact ⟨lt_of_le_of_lt (neg_le_neg (min_le_right _ _)) hr.1,
        lt_of_lt_of_le hr.2 (min_le_right _ _)⟩
    refine ⟨hball hr₁, ?_⟩
    change c * h r < 0 ↔ c * r < 0
    rcases hc with rfl | rfl
    · simp only [one_mul]
      exact (hsignh r hr₀).1
    · constructor
      · intro hlt
        have : 0 < h r := by linarith
        linarith [(hsignh r hr₀).2.mp this]
      · intro hlt
        have : 0 < r := by linarith
        linarith [(hsignh r hr₀).2.mpr this]

end DifferentialGeometry.Topology
