import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.TorusBigonPush
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.TorusBigonDescent

/-!
# The controlled-support bigon push on the torus

Let `f : Circle → Torus` be a closed curve with a lift `γ` (`f (cexp t) = torusCover (γ t)`), and
let `γ '' [t₁, t₂]` together with a segment of the line `ℓ = c` (`ℓ` the second coordinate, or
the first one for vertical cuts) bound a bigon in the plane. Given an open neighbourhood `N` of
the closed bigon that projects injectively to the torus, lies in the strip `|ℓ - c| < 1`, and
meets the lifted curve only along `γ '' (t₁ - ε, t₂ + ε)` (the bigon is empty), there is a torus
diffeomorphism `Q` isotopic to the identity with support in a compact subset of the projection
of `N`, such that the level set `{z | ℓ (Q (f z)) = c}` is exactly the old level set with the two
corners `cexp t₁ ≠ cexp t₂` removed, and `Q` is the identity near every remaining crossing.

`Q` descends the planar push of `TorusBigonPush` (conjugated by the coordinate swap for vertical
cuts) through `exists_torus_push`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

namespace GC.Seifert

open AnnulusStraightening

def bigonSwap : (ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ) where
  toFun p := p.swap
  invFun p := p.swap
  left_inv p := Prod.swap_swap p
  right_inv p := Prod.swap_swap p
  contMDiff_toFun := (contDiff_snd.prodMk contDiff_fst).contMDiff
  contMDiff_invFun := (contDiff_snd.prodMk contDiff_fst).contMDiff

theorem bigonSwap_apply (p : ℝ × ℝ) : bigonSwap p = p.swap := rfl

theorem bigonSwap_symm_apply (p : ℝ × ℝ) : bigonSwap.symm p = p.swap := rfl

theorem bigonSwap_image_segment (a b : ℝ × ℝ) :
    bigonSwap '' segment ℝ a b = segment ℝ a.swap b.swap := by
  rw [segment_eq_image_lineMap, segment_eq_image_lineMap, image_image]
  refine image_congr fun s _ => ?_
  simp only [bigonSwap_apply, AffineMap.lineMap_apply_module, Prod.smul_swap, Prod.swap_add]

theorem exists_bigon_push_vertical {σ : ℝ} (hσ : σ ^ 2 = 1) {γ : ℝ → ℝ × ℝ}
    (hγ : ContDiff ℝ ∞ γ) {c t₁ t₂ ε : ℝ} (ht : t₁ < t₂) (hε : 0 < ε)
    (h₁ : (γ t₁).1 = c) (h₂ : (γ t₂).1 = c)
    (hin : ∀ t ∈ Ioo t₁ t₂, 0 < σ * ((γ t).1 - c))
    (hout : ∀ t ∈ Icc (t₁ - ε) (t₂ + ε), t < t₁ ∨ t₂ < t → σ * ((γ t).1 - c) < 0)
    (htr₁ : (deriv γ t₁).1 ≠ 0) (htr₂ : (deriv γ t₂).1 ≠ 0)
    (himm : ∀ t ∈ Icc (t₁ - ε) (t₂ + ε), deriv γ t ≠ 0)
    (hinj : InjOn γ (Icc (t₁ - ε) (t₂ + ε)))
    {N : Set (ℝ × ℝ)} (hN : IsOpen N) (hDN : bigonRegion γ t₁ t₂ ⊆ N) :
    ∃ H : ℝ → (ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ),
      ContDiff ℝ ∞ (fun q : ℝ × (ℝ × ℝ) => H q.1 q.2) ∧
      ContDiff ℝ ∞ (fun q : ℝ × (ℝ × ℝ) => (H q.1).symm q.2) ∧
      H 0 = Diffeomorph.refl 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) ∞ ∧
      (∃ K : Set (ℝ × ℝ), IsCompact K ∧ K ⊆ N ∧ ∀ s z, z ∉ K → H s z = z) ∧
      ∀ t ∈ Icc (t₁ - ε) (t₂ + ε), σ * ((H 1 (γ t)).1 - c) < 0 := by
  set S := bigonSwap
  set γ' : ℝ → ℝ × ℝ := fun t => (γ t).swap
  have hγ' : ContDiff ℝ ∞ γ' := hγ.snd.prodMk hγ.fst
  have hd (t : ℝ) : deriv γ' t = (deriv γ t).swap := by
    have h := (hγ.differentiable (by simp) t).hasDerivAt
    have h' := (ContinuousLinearEquiv.prodComm ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t h
    exact h'.deriv
  have hinj' : InjOn γ' (Icc (t₁ - ε) (t₂ + ε)) := fun t ht t' ht' he =>
    hinj ht ht' (Prod.swap_injective he)
  have hcurve : S.toHomeomorph '' bigonCurveSet γ t₁ t₂ = bigonCurveSet γ' t₁ t₂ := by
    unfold bigonCurveSet
    rw [image_union]
    congr 1
    · rw [image_image]
      rfl
    · exact bigonSwap_image_segment _ _
  have hregion := bigonRegion_image S.toHomeomorph hcurve
  have hDN' : bigonRegion γ' t₁ t₂ ⊆ S '' N := by
    rw [← hregion]
    exact image_mono hDN
  obtain ⟨H', hH', hH'', hH'0, ⟨K', hK'c, hK'N, hK'fix⟩, hpush⟩ :=
    exists_bigon_push_of_sign hσ hγ' ht hε h₁ h₂ hin hout (by rw [hd]; exact htr₁)
      (by rw [hd]; exact htr₂)
      (fun t ht h => by rw [hd] at h; exact himm t ht (Prod.swap_injective (h.trans rfl)))
      hinj' (S.toHomeomorph.isOpenMap N hN) hDN'
  have hSs : ContDiff ℝ ∞ (S : ℝ × ℝ → ℝ × ℝ) := contDiff_snd.prodMk contDiff_fst
  refine ⟨fun s => S.trans ((H' s).trans S.symm), ?_, ?_, ?_,
    ⟨S.symm '' K', hK'c.image S.symm.continuous, ?_, ?_⟩, ?_⟩
  · exact hSs.comp (hH'.comp (contDiff_fst.prodMk (hSs.comp contDiff_snd)))
  · exact hSs.comp (hH''.comp (contDiff_fst.prodMk (hSs.comp contDiff_snd)))
  · refine Diffeomorph.ext fun z => ?_
    change S.symm (H' 0 (S z)) = z
    rw [hH'0]
    exact Prod.swap_swap z
  · rintro _ ⟨z, hz, rfl⟩
    obtain ⟨y, hy, hyz⟩ := hK'N hz
    rw [← hyz]
    change (y.swap).swap ∈ N
    rw [Prod.swap_swap]
    exact hy
  · intro s z hz
    have hz' : S z ∉ K' := fun h => hz ⟨S z, h, Prod.swap_swap z⟩
    change S.symm (H' s (S z)) = z
    rw [hK'fix s _ hz']
    exact Prod.swap_swap z
  · intro t ht
    exact hpush t ht

section Core

variable {f : Circle → Torus} {γ : ℝ → ℝ × ℝ} {lv : Torus → Circle} {ℓ : ℝ × ℝ → ℝ}

theorem cexp_ne_cexp_of_abs_lt {a c : ℝ} (h : |a - c| < 1) (hne : a ≠ c) : cexp a ≠ cexp c := by
  intro he
  obtain ⟨n, hn⟩ := cexp_eq_cexp_iff.mp he
  have hn' : |(n : ℝ)| < 1 := by rw [show (n : ℝ) = a - c by linarith]; exact h
  have : n = 0 := by
    rw [← Int.cast_abs] at hn'
    have : |n| < 1 := by exact_mod_cast hn'
    rw [abs_lt] at this
    omega
  rw [this, Int.cast_zero, add_zero] at hn
  exact hne hn

theorem torus_push_level (hlift : ∀ t, f (cexp t) = torusCover (γ t))
    (hlv : ∀ y, lv (torusCover y) = cexp (ℓ y))
    {σ c t₁ t₂ ε : ℝ} (ht : t₁ < t₂) (h₁ : ℓ (γ t₁) = c) (h₂ : ℓ (γ t₂) = c)
    (hin : ∀ t ∈ Ioo t₁ t₂, 0 < σ * (ℓ (γ t) - c))
    (hout : ∀ t ∈ Icc (t₁ - ε) (t₂ + ε), t < t₁ ∨ t₂ < t → σ * (ℓ (γ t) - c) < 0)
    (hinj : InjOn γ (Icc (t₁ - ε) (t₂ + ε))) (hε : 0 < ε)
    {N : Set (ℝ × ℝ)} (hNc : ∀ y ∈ N, |ℓ y - c| < 1)
    (hsep : ∀ (m n : ℤ) (z : ℝ × ℝ), z ∈ N → (z.1 + (m : ℝ), z.2 + (n : ℝ)) ∈ N →
      m = 0 ∧ n = 0)
    (hemp : ∀ z (y : ℝ × ℝ), y ∈ N → f z = torusCover y →
      ∃ t ∈ Ioo (t₁ - ε) (t₂ + ε), cexp t = z ∧ γ t = y)
    {H : ℝ → (ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ)}
    (hH : ContDiff ℝ ∞ (fun q : ℝ × (ℝ × ℝ) => H q.1 q.2))
    (hH' : ContDiff ℝ ∞ (fun q : ℝ × (ℝ × ℝ) => (H q.1).symm q.2))
    (h0 : H 0 = Diffeomorph.refl 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) ∞)
    {K : Set (ℝ × ℝ)} (hKc : IsCompact K) (hKN : K ⊆ N) (hHK : ∀ s z, z ∉ K → H s z = z)
    (hpush : ∀ t ∈ Icc (t₁ - ε) (t₂ + ε), σ * (ℓ (H 1 (γ t)) - c) < 0) :
    ∃ Q : TDiff, IsotopicDiffeomorph torusRefl Q ∧
      (∃ C : Set Torus, IsCompact C ∧ C ⊆ torusCover '' N ∧ (∀ p ∉ C, Q p = p) ∧
        (∀ p ∈ C, Q p ∈ C) ∧
        ∀ z, lv (Q (f z)) = cexp c → f z ∉ C) ∧
      (∀ z, lv (Q (f z)) = cexp c ↔ lv (f z) = cexp c ∧ z ≠ cexp t₁ ∧ z ≠ cexp t₂) ∧
      cexp t₁ ≠ cexp t₂ ∧ lv (f (cexp t₁)) = cexp c ∧ lv (f (cexp t₂)) = cexp c := by
  have hsepK : ∀ (m n : ℤ) (z : ℝ × ℝ), z ∈ K → (z.1 + (m : ℝ), z.2 + (n : ℝ)) ∈ K →
      m = 0 ∧ n = 0 := fun m n z hz hz' => hsep m n z (hKN hz) (hKN hz')
  obtain ⟨Q, hQ, hQK, hQoff⟩ := exists_torus_push hH hH' h0 hKc hHK hsepK
  have hmaps (z : ℝ × ℝ) (hz : z ∈ K) : H 1 z ∈ K := by
    by_contra h
    have he : H 1 z = z := (H 1).injective (hHK 1 _ h)
    rw [he] at h
    exact h hz
  set C : Set Torus := torusCover '' K
  have hCc : IsCompact C := hKc.image continuous_torusCover
  have hCN : C ⊆ torusCover '' N := image_mono hKN
  have hQC : ∀ p ∉ C, Q p = p := by
    intro p hp
    obtain ⟨z, rfl⟩ := torusCover_surjective p
    refine hQoff z fun m n hmn => hp ⟨_, hmn, ?_⟩
    rw [torusCover_add_int]
  have ht₁I : t₁ ∈ Icc (t₁ - ε) (t₂ + ε) := ⟨by linarith, by linarith⟩
  have ht₂I : t₂ ∈ Icc (t₁ - ε) (t₂ + ε) := ⟨by linarith, by linarith⟩
  have hmemK (t : ℝ) (ht : t ∈ Icc (t₁ - ε) (t₂ + ε)) (hc : ℓ (γ t) = c) : γ t ∈ K := by
    by_contra h
    have := hpush t ht
    rw [hHK 1 _ h, hc, sub_self, mul_zero] at this
    exact lt_irrefl _ this
  have hK₁ := hmemK t₁ ht₁I h₁
  have hK₂ := hmemK t₂ ht₂I h₂
  have hlv₁ : lv (f (cexp t₁)) = cexp c := by rw [hlift, hlv, h₁]
  have hlv₂ : lv (f (cexp t₂)) = cexp c := by rw [hlift, hlv, h₂]
  have hC₁ : f (cexp t₁) ∈ C := ⟨_, hK₁, (hlift t₁).symm⟩
  have hC₂ : f (cexp t₂) ∈ C := ⟨_, hK₂, (hlift t₂).symm⟩
  have hinC : ∀ z, f z ∈ C → lv (Q (f z)) ≠ cexp c ∧ ¬ (lv (f z) = cexp c ∧ z ≠ cexp t₁ ∧
      z ≠ cexp t₂) := by
    rintro z ⟨y, hyK, hyz⟩
    obtain ⟨t, htI, rfl, rfl⟩ := hemp z y (hKN hyK) hyz.symm
    have htI' : t ∈ Icc (t₁ - ε) (t₂ + ε) := Ioo_subset_Icc_self htI
    have hσ0 : σ ≠ 0 := by
      intro h0'
      have := hpush t htI'
      rw [h0', zero_mul] at this
      exact lt_irrefl _ this
    refine ⟨?_, ?_⟩
    · rw [← hyz, hQK _ hyK, hlv]
      refine cexp_ne_cexp_of_abs_lt (hNc _ (hKN (hmaps _ hyK))) fun he => ?_
      have := hpush t htI'
      rw [he, sub_self, mul_zero] at this
      exact lt_irrefl _ this
    · rintro ⟨hlvz, hz₁, hz₂⟩
      rw [← hyz, hlv] at hlvz
      by_cases hc : ℓ (γ t) = c
      · rcases lt_trichotomy t t₁ with h | h | h
        · have := hout t htI' (Or.inl h)
          rw [hc, sub_self, mul_zero] at this
          exact lt_irrefl _ this
        · exact hz₁ (by rw [h])
        · rcases lt_trichotomy t t₂ with h' | h' | h'
          · have := hin t ⟨h, h'⟩
            rw [hc, sub_self, mul_zero] at this
            exact lt_irrefl _ this
          · exact hz₂ (by rw [h'])
          · have := hout t htI' (Or.inr h')
            rw [hc, sub_self, mul_zero] at this
            exact lt_irrefl _ this
      · exact cexp_ne_cexp_of_abs_lt (hNc _ (hKN hyK)) hc hlvz
  have hQCC : ∀ p ∈ C, Q p ∈ C := by
    intro p hp
    by_contra h
    have he : Q p = p := Q.injective (hQC _ h)
    exact h (he.symm ▸ hp)
  refine ⟨Q, hQ, ⟨C, hCc, hCN, hQC, hQCC, fun z hz hzC => (hinC z hzC).1 hz⟩, fun z => ?_,
    fun he => ?_, hlv₁, hlv₂⟩
  · by_cases hzC : f z ∈ C
    · exact iff_of_false (hinC z hzC).1 (hinC z hzC).2
    · rw [hQC _ hzC]
      constructor
      · intro h
        refine ⟨h, fun h₁' => hzC (h₁' ▸ hC₁), fun h₂' => hzC (h₂' ▸ hC₂)⟩
      · exact fun h => h.1
  · have hc : torusCover (γ t₁) = torusCover (γ t₂) := by rw [← hlift, ← hlift, he]
    obtain ⟨m, n, hmn⟩ := torusCover_eq_torusCover_iff.mp hc
    have h' : ((γ t₂).1 + (m : ℝ), (γ t₂).2 + (n : ℝ)) ∈ K := hmn ▸ hK₁
    obtain ⟨rfl, rfl⟩ := hsepK m n _ hK₂ h'
    simp only [Int.cast_zero, add_zero] at hmn
    exact ht.ne (hinj ht₁I ht₂I hmn)

end Core

theorem ncard_add_two_of_forall_iff {S S' : Set Circle} (hS : S.Finite) {a b : Circle}
    (hab : a ≠ b) (ha : a ∈ S) (hb : b ∈ S) (h : ∀ z, z ∈ S' ↔ z ∈ S ∧ z ≠ a ∧ z ≠ b) :
    S'.ncard + 2 = S.ncard := by
  have hS' : S' = S \ {a, b} := by
    ext z
    rw [h, Set.mem_sdiff, mem_insert_iff, mem_singleton_iff, not_or]
  rw [hS', ← ncard_pair hab]
  exact ncard_sdiff_add_ncard_of_subset (insert_subset ha (singleton_subset_iff.mpr hb)) hS

theorem eventuallyEq_of_not_mem_support {Q : TDiff} {C : Set Torus} (hC : IsCompact C)
    (hQ : ∀ p ∉ C, Q p = p) {f : Circle → Torus} (hf : Continuous f) {z : Circle}
    (hz : f z ∉ C) : (fun w => Q (f w)) =ᶠ[𝓝 z] f := by
  have hU : f ⁻¹' Cᶜ ∈ 𝓝 z := hf.continuousAt.preimage_mem_nhds
    (hC.isClosed.isOpen_compl.mem_nhds hz)
  filter_upwards [hU] with w hw
  exact hQ _ hw

theorem exists_torus_bigon_push {f : Circle → Torus} {γ : ℝ → ℝ × ℝ} (hγ : ContDiff ℝ ∞ γ)
    (hlift : ∀ t, f (cexp t) = torusCover (γ t)) {σ : ℝ} (hσ : σ ^ 2 = 1)
    {c t₁ t₂ ε : ℝ} (ht : t₁ < t₂) (hε : 0 < ε) (h₁ : (γ t₁).2 = c) (h₂ : (γ t₂).2 = c)
    (hin : ∀ t ∈ Ioo t₁ t₂, 0 < σ * ((γ t).2 - c))
    (hout : ∀ t ∈ Icc (t₁ - ε) (t₂ + ε), t < t₁ ∨ t₂ < t → σ * ((γ t).2 - c) < 0)
    (htr₁ : (deriv γ t₁).2 ≠ 0) (htr₂ : (deriv γ t₂).2 ≠ 0)
    (himm : ∀ t ∈ Icc (t₁ - ε) (t₂ + ε), deriv γ t ≠ 0)
    (hinj : InjOn γ (Icc (t₁ - ε) (t₂ + ε)))
    {N : Set (ℝ × ℝ)} (hN : IsOpen N) (hDN : bigonRegion γ t₁ t₂ ⊆ N)
    (hNc : ∀ y ∈ N, |y.2 - c| < 1)
    (hsep : ∀ (m n : ℤ) (z : ℝ × ℝ), z ∈ N → (z.1 + (m : ℝ), z.2 + (n : ℝ)) ∈ N →
      m = 0 ∧ n = 0)
    (hemp : ∀ z (y : ℝ × ℝ), y ∈ N → f z = torusCover y →
      ∃ t ∈ Ioo (t₁ - ε) (t₂ + ε), cexp t = z ∧ γ t = y) :
    ∃ Q : TDiff, IsotopicDiffeomorph torusRefl Q ∧
      (∃ C : Set Torus, IsCompact C ∧ C ⊆ torusCover '' N ∧ (∀ p ∉ C, Q p = p) ∧
        (∀ p ∈ C, Q p ∈ C) ∧
        ∀ z, (Q (f z)).2 = cexp c → f z ∉ C) ∧
      (∀ z, (Q (f z)).2 = cexp c ↔ (f z).2 = cexp c ∧ z ≠ cexp t₁ ∧ z ≠ cexp t₂) ∧
      cexp t₁ ≠ cexp t₂ ∧ (f (cexp t₁)).2 = cexp c ∧ (f (cexp t₂)).2 = cexp c := by
  obtain ⟨H, hH, hH', h0, ⟨K, hKc, hKN, hHK⟩, hpush⟩ :=
    exists_bigon_push_of_sign hσ hγ ht hε h₁ h₂ hin hout htr₁ htr₂ himm hinj hN hDN
  exact torus_push_level (lv := Prod.snd) (ℓ := Prod.snd) hlift
    (fun y => by rw [torusCover_eq]) ht h₁ h₂ hin hout hinj hε hNc hsep hemp hH hH' h0 hKc hKN
    hHK hpush

theorem exists_torus_bigon_push_vertical {f : Circle → Torus} {γ : ℝ → ℝ × ℝ}
    (hγ : ContDiff ℝ ∞ γ) (hlift : ∀ t, f (cexp t) = torusCover (γ t)) {σ : ℝ}
    (hσ : σ ^ 2 = 1) {c t₁ t₂ ε : ℝ} (ht : t₁ < t₂) (hε : 0 < ε) (h₁ : (γ t₁).1 = c)
    (h₂ : (γ t₂).1 = c) (hin : ∀ t ∈ Ioo t₁ t₂, 0 < σ * ((γ t).1 - c))
    (hout : ∀ t ∈ Icc (t₁ - ε) (t₂ + ε), t < t₁ ∨ t₂ < t → σ * ((γ t).1 - c) < 0)
    (htr₁ : (deriv γ t₁).1 ≠ 0) (htr₂ : (deriv γ t₂).1 ≠ 0)
    (himm : ∀ t ∈ Icc (t₁ - ε) (t₂ + ε), deriv γ t ≠ 0)
    (hinj : InjOn γ (Icc (t₁ - ε) (t₂ + ε)))
    {N : Set (ℝ × ℝ)} (hN : IsOpen N) (hDN : bigonRegion γ t₁ t₂ ⊆ N)
    (hNc : ∀ y ∈ N, |y.1 - c| < 1)
    (hsep : ∀ (m n : ℤ) (z : ℝ × ℝ), z ∈ N → (z.1 + (m : ℝ), z.2 + (n : ℝ)) ∈ N →
      m = 0 ∧ n = 0)
    (hemp : ∀ z (y : ℝ × ℝ), y ∈ N → f z = torusCover y →
      ∃ t ∈ Ioo (t₁ - ε) (t₂ + ε), cexp t = z ∧ γ t = y) :
    ∃ Q : TDiff, IsotopicDiffeomorph torusRefl Q ∧
      (∃ C : Set Torus, IsCompact C ∧ C ⊆ torusCover '' N ∧ (∀ p ∉ C, Q p = p) ∧
        (∀ p ∈ C, Q p ∈ C) ∧
        ∀ z, (Q (f z)).1 = cexp c → f z ∉ C) ∧
      (∀ z, (Q (f z)).1 = cexp c ↔ (f z).1 = cexp c ∧ z ≠ cexp t₁ ∧ z ≠ cexp t₂) ∧
      cexp t₁ ≠ cexp t₂ ∧ (f (cexp t₁)).1 = cexp c ∧ (f (cexp t₂)).1 = cexp c := by
  obtain ⟨H, hH, hH', h0, ⟨K, hKc, hKN, hHK⟩, hpush⟩ :=
    exists_bigon_push_vertical hσ hγ ht hε h₁ h₂ hin hout htr₁ htr₂ himm hinj hN hDN
  exact torus_push_level (lv := Prod.fst) (ℓ := Prod.fst) hlift
    (fun y => by rw [torusCover_eq]) ht h₁ h₂ hin hout hinj hε hNc hsep hemp hH hH' h0 hKc hKN
    hHK hpush

end GC.Seifert
