import DifferentialGeometry.Topology.Diffeomorph.Perturbation
import DifferentialGeometry.Topology.Diffeomorph.LocalFlowExtension
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Set
open scoped ContDiff Manifold NNReal Topology

namespace Diffeomorph

theorem exists_isotopy_translation_of_isBounded {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {K : Set E} (hK : Bornology.IsBounded K) (v : E) :
    ∃ H : ℝ → (E ≃ₘ[ℝ] E),
      ContDiff ℝ ∞ (fun z : ℝ × E => H z.1 z.2) ∧
      ContDiff ℝ ∞ (fun z : ℝ × E => (H z.1).symm z.2) ∧
      H 0 = Diffeomorph.refl 𝓘(ℝ, E) E ∞ ∧
      (∀ t : ℝ, ∀ x ∈ K, H t x = x + Real.smoothTransition t • v) ∧
      ∃ J : Set E, IsCompact J ∧ ∀ t : ℝ,
        Set.EqOn (H t) id Jᶜ ∧ Set.EqOn (H t).symm id Jᶜ := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let b : ContDiffBump (0 : E) := ⟨1, 2, by norm_num, by norm_num⟩
  obtain ⟨B, hB⟩ := ContDiff.lipschitzWith_of_hasCompactSupport b.hasCompactSupport
    b.contDiff (show (∞ : ℕ∞ω) ≠ 0 by simp)
  obtain ⟨R₀, hR₀, hKR₀⟩ := hK.exists_pos_norm_le
  let R : ℝ := R₀ + ‖v‖ * B + 1
  have hprod : 0 ≤ ‖v‖ * (B : ℝ) := mul_nonneg (norm_nonneg _) B.coe_nonneg
  have hR : 0 < R := by dsimp only [R]; linarith
  have hR₀R : R₀ ≤ R := by dsimp only [R]; linarith
  have hsmall : ‖v‖ * (B : ℝ) < R := by dsimp only [R]; linarith
  let f : E → E := fun x => b (R⁻¹ • x) • v
  have hf : ContDiff ℝ ∞ f :=
    (b.contDiff.comp (contDiff_const.smul contDiff_id)).smul contDiff_const
  let C : ℝ≥0 := ‖v‖₊ * (B * ‖R⁻¹‖₊)
  have hC : C < 1 := by
    rw [← NNReal.coe_lt_coe]
    change ‖v‖ * ((B : ℝ) * ‖R⁻¹‖) < 1
    rw [Real.norm_of_nonneg (inv_nonneg.mpr hR.le), ← mul_assoc]
    exact (mul_inv_lt_iff₀ hR).2 (by simpa only [one_mul] using hsmall)
  have hlip : LipschitzWith C f := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist (b (R⁻¹ • x) • v) (b (R⁻¹ • y) • v) ≤ (C : ℝ) * dist x y
    rw [dist_eq_norm, ← sub_smul, norm_smul]
    have hbxy := hB.norm_sub_le (R⁻¹ • x) (R⁻¹ • y)
    rw [← smul_sub, norm_smul] at hbxy
    calc
      ‖b (R⁻¹ • x) - b (R⁻¹ • y)‖ * ‖v‖ ≤
          ((B : ℝ) * (‖R⁻¹‖ * ‖x - y‖)) * ‖v‖ :=
        mul_le_mul_of_nonneg_right hbxy (norm_nonneg _)
      _ = (C : ℝ) * dist x y := by simp only [C, NNReal.coe_mul, coe_nnnorm, dist_eq_norm]; ring
  have hs : HasCompactSupport f :=
    (b.hasCompactSupport.comp_smul (inv_ne_zero hR.ne')).smul_right
  have heq : ∀ x ∈ K, f x = v := by
    intro x hx
    have hxball : R⁻¹ • x ∈ Metric.closedBall (0 : E) b.rIn := by
      change dist (R⁻¹ • x) 0 ≤ 1
      rw [dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hR.le)]
      calc
        R⁻¹ * ‖x‖ ≤ R⁻¹ * R :=
          mul_le_mul_of_nonneg_left ((hKR₀ x hx).trans hR₀R) (inv_nonneg.mpr hR.le)
        _ = 1 := inv_mul_cancel₀ hR.ne'
    dsimp only [f]
    rw [b.one_of_mem_closedBall hxball, one_smul]
  refine ⟨addLipschitzIsotopy hf hlip hC, contDiff_addLipschitzIsotopy hf hlip hC,
    contDiff_addLipschitzIsotopy_symm hf hlip hC, addLipschitzIsotopy_zero hf hlip hC,
    ?_, exists_isCompact_eqOn_addLipschitzIsotopy hf hlip hC hs⟩
  intro t x hx
  rw [addLipschitzIsotopy_apply, heq x hx]

theorem exists_isotopy_translation_in_open {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (v : E)
    (htrace : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ K, x + t • v ∈ U) :
    ∃ H : ℝ → (E ≃ₘ[ℝ] E),
      ContDiff ℝ ∞ (fun z : ℝ × E => H z.1 z.2) ∧
      ContDiff ℝ ∞ (fun z : ℝ × E => (H z.1).symm z.2) ∧
      H 0 = Diffeomorph.refl 𝓘(ℝ, E) E ∞ ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ K, H t x = x + t • v) ∧
      (∀ t x, H t x - x ∈ Submodule.span ℝ {v}) ∧
      ∃ J : Set E, IsCompact J ∧ J ⊆ U ∧ ∀ t : ℝ,
        EqOn (H t) id Jᶜ ∧ EqOn (H t).symm id Jᶜ := by
  let C := (fun p : ℝ × E => (p.1, p.2 + p.1 • v)) '' (Icc (0 : ℝ) 1 ×ˢ K)
  have hC : IsCompact C := (isCompact_Icc.prod hK).image
    (continuous_fst.prodMk (continuous_snd.add (continuous_fst.smul continuous_const)))
  have hCU : C ⊆ univ ×ˢ U := by
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨mem_univ _, htrace p.1 hp.1 p.2 hp.2⟩
  obtain ⟨H, hH, hHi, hH0, hmove, _, hspan, hsupport⟩ :=
    exists_contDiff_compact_isotopy_eqOn_integralCurve_of_mem_submodule hU isOpen_univ hC
      (by simpa only [univ_inter] using hCU) (W := fun _ => v) contDiff_const.contDiffOn
      (S := ∅) (fun _ _ h => h.elim) (Submodule.span ℝ {v})
      (fun _ _ => Submodule.mem_span_singleton_self v)
      (P := K) (γ := fun x t => (x : E) + t • v) (c := fun _ => 0) (d := fun _ => 1) 0
      (fun _ => (continuous_const.add (continuous_id.smul continuous_const)).continuousOn)
      (fun x t _ => by
        have h := (hasDerivAt_const t (x : E)).add ((hasDerivAt_id t).smul_const v)
        simp only [zero_add, one_smul] at h
        exact h.hasDerivWithinAt)
      (fun x t ht => ⟨(t, x), ⟨ht, x.property⟩, rfl⟩)
  refine ⟨H, hH, hHi, hH0, ?_, hspan, hsupport⟩
  intro t ht x hx
  simpa only [hH0, Diffeomorph.symm_refl, Diffeomorph.coe_refl, id_eq,
    zero_smul, add_zero] using hmove ⟨x, hx⟩ t ht

theorem exists_isotopy_vertical_translation_of_isCompact {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {K U : Set (E × ℝ)} (hK : IsCompact K) (hU : IsOpen U) (d : ℝ)
    (htrace : ∀ t ∈ Icc (0 : ℝ) 1, ∀ p ∈ K, (p.1, p.2 + t * d) ∈ U) :
    ∃ H : ℝ → ((E × ℝ) ≃ₘ[ℝ] (E × ℝ)),
      ContDiff ℝ ∞ (fun z : ℝ × (E × ℝ) => H z.1 z.2) ∧
      ContDiff ℝ ∞ (fun z : ℝ × (E × ℝ) => (H z.1).symm z.2) ∧
      H 0 = Diffeomorph.refl 𝓘(ℝ, E × ℝ) (E × ℝ) ∞ ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ p ∈ K, H t p = (p.1, p.2 + t * d)) ∧
      (∀ t z, (H t z).1 = z.1) ∧
      ∃ J : Set (E × ℝ), IsCompact J ∧ J ⊆ U ∧ ∀ t : ℝ,
        EqOn (H t) id Jᶜ ∧ EqOn (H t).symm id Jᶜ := by
  obtain ⟨H, hH, hHi, hH0, hmove, hspan, J, hJ, hJU, hfix⟩ :=
    exists_isotopy_translation_in_open hK hU ((0 : E), d) (by
      rintro t ht ⟨x, y⟩ hp
      simpa only [Prod.smul_mk, Prod.mk_add_mk, smul_zero, add_zero, smul_eq_mul] using
        htrace t ht (x, y) hp)
  refine ⟨H, hH, hHi, hH0, ?_, ?_, J, hJ, hJU, hfix⟩
  · rintro t ht ⟨x, y⟩ hp
    simpa only [Prod.smul_mk, Prod.mk_add_mk, smul_zero, add_zero, smul_eq_mul] using
      hmove t ht (x, y) hp
  · intro t z
    have hker : Submodule.span ℝ {((0 : E), d)} ≤
        (ContinuousLinearMap.fst ℝ E ℝ).ker := by
      apply Submodule.span_le.mpr
      rintro y (rfl : y = _)
      rfl
    have h := hker (hspan t z)
    change (H t z).1 - z.1 = 0 at h
    exact sub_eq_zero.mp h

theorem exists_isotopy_vertical_translation_in_open {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {K : Set E} (hK : IsCompact K) {U : Set (E × ℝ)} (hU : IsOpen U)
    (a b : ℝ) (htrace : K ×ˢ uIcc a b ⊆ U) :
    ∃ H : ℝ → ((E × ℝ) ≃ₘ[ℝ] (E × ℝ)),
      ContDiff ℝ ∞ (fun z : ℝ × (E × ℝ) => H z.1 z.2) ∧
      ContDiff ℝ ∞ (fun z : ℝ × (E × ℝ) => (H z.1).symm z.2) ∧
      H 0 = Diffeomorph.refl 𝓘(ℝ, E × ℝ) (E × ℝ) ∞ ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ K, H t (x, a) = (x, a + t * (b - a))) ∧
      (∀ t z, (H t z).1 = z.1) ∧
      ∃ J : Set (E × ℝ), IsCompact J ∧ J ⊆ U ∧ ∀ t : ℝ,
        EqOn (H t) id Jᶜ ∧ EqOn (H t).symm id Jᶜ := by
  obtain ⟨H, hH, hHi, hH0, hmove, hfst, hsupport⟩ :=
    exists_isotopy_vertical_translation_of_isCompact
      (hK.prod (isCompact_singleton (x := a))) hU (b - a) (by
        rintro t ht ⟨x, s⟩ ⟨hx, hs⟩
        have hs' : s = a := hs
        subst s
        apply htrace
        refine ⟨hx, ?_⟩
        change a + t * (b - a) ∈ uIcc a b
        rcases le_total a b with hab | hba
        · rw [uIcc_of_le hab]
          constructor <;> nlinarith [ht.1, ht.2]
        · rw [uIcc_of_ge hba]
          constructor <;> nlinarith [ht.1, ht.2])
  exact ⟨H, hH, hHi, hH0, fun t ht x hx => hmove t ht (x, a) ⟨hx, mem_singleton a⟩,
    hfst, hsupport⟩

theorem exists_isotopy_vertical_translation_of_local_product {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {K S U : Set (E × ℝ)} {C V : Set E} {W : Set ℝ}
    (hK : IsCompact K) (hS : S ∩ (V ×ˢ W) = (C ∩ V) ×ˢ W)
    (hU : IsOpen U) (hUV : U ⊆ V ×ˢ W) (d : ℝ)
    (htrace : ∀ t ∈ Icc (0 : ℝ) 1, ∀ p ∈ K, (p.1, p.2 + t * d) ∈ U) :
    ∃ H : ℝ → ((E × ℝ) ≃ₘ[ℝ] (E × ℝ)),
      ContDiff ℝ ∞ (fun z : ℝ × (E × ℝ) => H z.1 z.2) ∧
      ContDiff ℝ ∞ (fun z : ℝ × (E × ℝ) => (H z.1).symm z.2) ∧
      H 0 = Diffeomorph.refl 𝓘(ℝ, E × ℝ) (E × ℝ) ∞ ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ p ∈ K, H t p = (p.1, p.2 + t * d)) ∧
      (∀ t z, (H t z).1 = z.1) ∧ (∀ t, H t '' S = S) ∧
      ∃ J : Set (E × ℝ), IsCompact J ∧ J ⊆ U ∧ ∀ t : ℝ,
        EqOn (H t) id Jᶜ ∧ EqOn (H t).symm id Jᶜ := by
  obtain ⟨H, hH, hHi, hH0, hmove, hfst, J, hJ, hJU, hfix⟩ :=
    exists_isotopy_vertical_translation_of_isCompact hK hU d htrace
  refine ⟨H, hH, hHi, hH0, hmove, hfst, ?_, J, hJ, hJU, hfix⟩
  intro t
  have hmem (z : E × ℝ) : H t z ∈ S ↔ z ∈ S := by
    by_cases hz : z ∈ J
    · have hHz : H t z ∈ J := by
        by_contra hn
        have heq : H t (H t z) = H t z := (hfix t).1 hn
        have hzeq : H t z = z := (H t).injective heq
        exact hn (hzeq.symm ▸ hz)
      have hzW : z ∈ V ×ˢ W := hUV (hJU hz)
      have hHzW : H t z ∈ V ×ˢ W := hUV (hJU hHz)
      have hlocal (y : E × ℝ) (hy : y ∈ V ×ˢ W) : y ∈ S ↔ y.1 ∈ C := by
        constructor
        · intro hyS
          exact (hS.subset ⟨hyS, hy⟩).1.1
        · intro hyC
          exact (hS.symm.subset ⟨⟨hyC, hy.1⟩, hy.2⟩).1
      rw [hlocal _ hHzW, hlocal _ hzW, hfst]
    · rw [(hfix t).1 hz]
      rfl
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (hmem x).mpr hx
  · intro hz
    refine ⟨(H t).symm z, ?_, (H t).apply_symm_apply z⟩
    apply (hmem _).mp
    rwa [(H t).apply_symm_apply]

theorem exists_isotopy_vertical_translation_preserving_set {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {K : Set E} (hK : IsCompact K) {S : Set (E × ℝ)} {C : Set E} {W : Set ℝ}
    (hS : S ∩ (univ ×ˢ W) = C ×ˢ W)
    {U : Set (E × ℝ)} (hU : IsOpen U) (hUW : U ⊆ univ ×ˢ W)
    (a b : ℝ) (htrace : K ×ˢ uIcc a b ⊆ U) :
    ∃ H : ℝ → ((E × ℝ) ≃ₘ[ℝ] (E × ℝ)),
      ContDiff ℝ ∞ (fun z : ℝ × (E × ℝ) => H z.1 z.2) ∧
      ContDiff ℝ ∞ (fun z : ℝ × (E × ℝ) => (H z.1).symm z.2) ∧
      H 0 = Diffeomorph.refl 𝓘(ℝ, E × ℝ) (E × ℝ) ∞ ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ K, H t (x, a) = (x, a + t * (b - a))) ∧
      (∀ t z, (H t z).1 = z.1) ∧ (∀ t, H t '' S = S) ∧
      ∃ J : Set (E × ℝ), IsCompact J ∧ J ⊆ U ∧ ∀ t : ℝ,
        EqOn (H t) id Jᶜ ∧ EqOn (H t).symm id Jᶜ := by
  obtain ⟨H, hH, hHi, hH0, hmove, hfst, hHS, hsupport⟩ :=
    exists_isotopy_vertical_translation_of_local_product
      (hK.prod (isCompact_singleton (x := a))) (by simpa only [inter_univ] using hS)
      hU hUW (b - a) (by
        rintro t ht ⟨x, s⟩ ⟨hx, hs⟩
        have hs' : s = a := hs
        subst s
        apply htrace
        refine ⟨hx, ?_⟩
        change a + t * (b - a) ∈ uIcc a b
        rcases le_total a b with hab | hba
        · rw [uIcc_of_le hab]
          constructor <;> nlinarith [ht.1, ht.2]
        · rw [uIcc_of_ge hba]
          constructor <;> nlinarith [ht.1, ht.2])
  exact ⟨H, hH, hHi, hH0, fun t ht x hx => hmove t ht (x, a) ⟨hx, mem_singleton a⟩,
    hfst, hHS, hsupport⟩

end Diffeomorph
