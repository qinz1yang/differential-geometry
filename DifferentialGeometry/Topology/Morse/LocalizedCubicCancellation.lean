/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.Morse.CubicCancellation

open Set Filter Function
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Topology.Morse

namespace DifferentialGeometry.Morse

private noncomputable def cubicScale (t : ℝ) (ht : t ≠ 0) :
    Diffeomorph 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) (ℝ × ℝ) ∞ where
  toFun p := (t ^ 2 * p.1, t ^ 3 * p.2)
  invFun p := (p.1 / t ^ 2, p.2 / t ^ 3)
  left_inv p := by ext <;> dsimp <;> field_simp
  right_inv p := by ext <;> dsimp <;> field_simp
  contMDiff_toFun := by
    apply contMDiff_iff_contDiff.mpr
    change ContDiff ℝ ∞ (fun p : ℝ × ℝ => (t ^ 2 * p.1, t ^ 3 * p.2))
    fun_prop
  contMDiff_invFun := by
    apply contMDiff_iff_contDiff.mpr
    change ContDiff ℝ ∞ (fun p : ℝ × ℝ => (p.1 / t ^ 2, p.2 / t ^ 3))
    fun_prop

private theorem cubic_height_scale (t : ℝ) (p : ℝ × ℝ) :
    (t ^ 2 * p.1) ^ 3 / 3 - t ^ 4 * (t ^ 2 * p.1) + (t ^ 3 * p.2) ^ 2 =
      t ^ 6 * (p.1 ^ 3 / 3 - p.1 + p.2 ^ 2) := by ring

theorem exists_cubic_suspension_cancellation_tsupport_subset {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (h0 : (0 : ℝ × ℝ) ∈ U) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a : ℝ, 0 < a → a < δ →
      ∃ g : ℝ × ℝ → ℝ, ContDiff ℝ ∞ g ∧
        HasCompactSupport (fun p => g p - (p.1 ^ 3 / 3 - a * p.1 + p.2 ^ 2)) ∧
        tsupport (fun p => g p - (p.1 ^ 3 / 3 - a * p.1 + p.2 ^ 2)) ⊆ U ∧
        (∀ p, ¬ IsCriticalPointAt 𝓘(ℝ, ℝ × ℝ) g p) ∧
        ∃ N : Set (ℝ × ℝ), IsOpen N ∧ Uᶜ ⊆ N ∧
          EqOn g (fun p => p.1 ^ 3 / 3 - a * p.1 + p.2 ^ 2) N := by
  obtain ⟨g, hg, hgc, hreg⟩ :=
    exists_compactly_supported_cubic_suspension_cancellation (by norm_num : (0 : ℝ) < 1)
  simp only [one_mul] at hgc
  let K := tsupport (fun p : ℝ × ℝ => g p - (p.1 ^ 3 / 3 - p.1 + p.2 ^ 2))
  have hK : IsCompact K := hgc
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, ∀ p ∈ K, (t ^ 2 * p.1, t ^ 3 * p.2) ∈ U := by
    apply hK.eventually_forall_of_forall_eventually
    intro p _
    have hc : Continuous (fun q : ℝ × (ℝ × ℝ) =>
        (q.1 ^ 2 * q.2.1, q.1 ^ 3 * q.2.2)) := by fun_prop
    exact (hc.isOpen_preimage U hU).mem_nhds (by simpa using! h0)
  obtain ⟨r, hr, hsmall⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨r ^ 4, by positivity, fun a ha har => ?_⟩
  let t := Real.sqrt (Real.sqrt a)
  have ht : 0 < t := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr ha)
  have ht4 : t ^ 4 = a := by
    have h1 : t ^ 2 = Real.sqrt a := Real.sq_sqrt (Real.sqrt_nonneg a)
    calc
      t ^ 4 = (t ^ 2) ^ 2 := by ring
      _ = a := by rw [h1, Real.sq_sqrt ha.le]
  have htr : t < r := (pow_lt_pow_iff_left₀ ht.le hr.le (by decide : 4 ≠ 0)).mp
    (by simpa only [ht4] using har)
  let L := cubicScale t ht.ne'
  let G : ℝ × ℝ → ℝ := fun p => t ^ 6 * g (L.symm p)
  have hG : ContDiff ℝ ∞ G := contDiff_const.mul
    (hg.comp (contMDiff_iff_contDiff.mp L.symm.contMDiff))
  have hLK : L '' K ⊆ U := by
    rintro p ⟨q, hq, rfl⟩
    exact hsmall (by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht]
      using htr) q hq
  have hLc : IsCompact (L '' K) := hK.image L.continuous
  have hformula (q : ℝ × ℝ) :
      (L q).1 ^ 3 / 3 - a * (L q).1 + (L q).2 ^ 2 =
        t ^ 6 * (q.1 ^ 3 / 3 - q.1 + q.2 ^ 2) := by
    rw [← ht4]
    exact cubic_height_scale t q
  have hs : support (fun p : ℝ × ℝ => G p -
      (p.1 ^ 3 / 3 - a * p.1 + p.2 ^ 2)) ⊆ L '' K := by
    intro p hp
    refine ⟨L.symm p, ?_, L.apply_symm_apply p⟩
    apply subset_tsupport
    intro hz
    have heq : g (L.symm p) = (L.symm p).1 ^ 3 / 3 -
        (L.symm p).1 + (L.symm p).2 ^ 2 := sub_eq_zero.mp hz
    apply hp
    change t ^ 6 * g (L.symm p) - _ = 0
    rw [heq, ← hformula, L.apply_symm_apply, sub_self]
  have hts := closure_minimal hs hLc.isClosed
  have hregular (p : ℝ × ℝ) : ¬ IsCriticalPointAt 𝓘(ℝ, ℝ × ℝ) G p := by
    intro hc
    have hzero : fderiv ℝ G p = 0 := by
      unfold IsCriticalPointAt at hc
      rw [mfderiv_eq_fderiv] at hc
      exact hc
    have heq : G ∘ L = fun q => t ^ 6 * g q := by
      funext q
      simp only [G, comp_apply, Diffeomorph.symm_apply_apply]
    have hD : fderiv ℝ (G ∘ L) (L.symm p) = 0 := by
      rw [fderiv_comp _ (hG.differentiable (by simp) _)
        ((contMDiff_iff_contDiff.mp L.contMDiff).differentiable (by simp) _)]
      rw [L.apply_symm_apply, hzero, ContinuousLinearMap.zero_comp]
    rw [heq, fderiv_const_mul (hg.differentiable (by simp) _) ] at hD
    have hz : fderiv ℝ g (L.symm p) = 0 := by
      apply (smul_eq_zero.mp hD).resolve_left (pow_ne_zero _ ht.ne')
    apply hreg (L.symm p)
    unfold IsCriticalPointAt
    rw [mfderiv_eq_fderiv]
    exact hz
  refine ⟨G, hG, hLc.of_isClosed_subset (isClosed_tsupport _) hts,
    hts.trans hLK, hregular, (tsupport (fun p => G p -
      (p.1 ^ 3 / 3 - a * p.1 + p.2 ^ 2)))ᶜ, isOpen_compl_iff.mpr (isClosed_tsupport _),
    compl_subset_compl.mpr (hts.trans hLK), ?_⟩
  intro p hp
  have hz := image_eq_zero_of_notMem_tsupport
    (f := fun p : ℝ × ℝ => G p - (p.1 ^ 3 / 3 - a * p.1 + p.2 ^ 2)) hp
  exact sub_eq_zero.mp hz

end DifferentialGeometry.Morse
