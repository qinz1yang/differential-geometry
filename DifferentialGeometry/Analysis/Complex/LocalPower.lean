import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Topology.OpenPartialHomeomorph.IsImage
import Mathlib.Analysis.Calculus.Deriv.Mul

section

noncomputable section
open Set Filter
open scoped Topology

namespace Complex

theorem exists_analytic_root_of_ne_zero
    {g : ℂ → ℂ} {p : ℂ} (hg : AnalyticAt ℂ g p) (hgp : g p ≠ 0)
    {m : ℕ} (hm : m ≠ 0) :
    ∃ r : ℂ → ℂ, AnalyticAt ℂ r p ∧ r p ≠ 0 ∧ ∀ z, r z ^ m = g z := by
  let c := (g p) ^ ((m : ℂ)⁻¹)
  let r := fun z => c * (g z / g p) ^ ((m : ℂ)⁻¹)
  have hc : c ^ m = g p := cpow_nat_inv_pow _ hm
  have hc0 : c ≠ 0 := fun hz => hgp (by rw [← hc, hz, zero_pow hm])
  have hratio : AnalyticAt ℂ (fun z => g z / g p) p := hg.div_const
  have hr : AnalyticAt ℂ r p := analyticAt_const.mul
    (hratio.cpow analyticAt_const (by simp [hgp]))
  have hrp : r p = c := by simp [r, hgp]
  refine ⟨r, hr, hrp ▸ hc0, ?_⟩
  intro z
  change (c * (g z / g p) ^ ((m : ℂ)⁻¹)) ^ m = g z
  rw [mul_pow, hc, cpow_nat_inv_pow _ hm]
  exact mul_div_cancel₀ (g z) hgp

end Complex

end

end

section

noncomputable section
open Set Filter
open scoped Topology

namespace Complex

theorem exists_local_homeomorph_pow_of_analytic
    {f : ℂ → ℂ} {p : ℂ} (hf : AnalyticAt ℂ f p)
    (hnon : ¬ ∀ᶠ z in 𝓝 p, f z = f p) :
    ∃ (m : ℕ) (e : OpenPartialHomeomorph ℂ ℂ), 0 < m ∧ p ∈ e.source ∧ e p = 0 ∧
      AnalyticAt ℂ e p ∧ deriv e p ≠ 0 ∧
      ∀ z ∈ e.source, f z = f p + e z ^ m := by
  have hf0 : AnalyticAt ℂ (fun z => f z - f p) p := hf.sub analyticAt_const
  obtain ⟨m, g, hg, hgp, hfg⟩ := hf0.exists_eventuallyEq_pow_smul_nonzero_iff.mpr
    (by simpa only [sub_eq_zero] using hnon)
  have hm : m ≠ 0 := by
    intro h
    have he := hfg.self_of_nhds
    simp only [h, pow_zero, one_smul, sub_self] at he
    exact hgp he.symm
  obtain ⟨r, hr, hrp, hrpow⟩ := exists_analytic_root_of_ne_zero hg hgp hm
  let ψ := fun z => (z - p) * r z
  have hψ : AnalyticAt ℂ ψ p := (analyticAt_id.sub analyticAt_const).mul hr
  have hdψ : HasStrictDerivAt ψ (r p) p := by
    have hlin : HasStrictDerivAt (fun z : ℂ => z - p) 1 p :=
      (hasStrictDerivAt_id p).sub_const p
    have hh := hlin.mul hr.hasStrictDerivAt
    simpa only [sub_self, zero_mul, one_mul, add_zero, Pi.mul_apply, ψ] using! hh
  let e := (hdψ.hasStrictFDerivAt_equiv hrp).toOpenPartialHomeomorph ψ
  have hep : p ∈ e.source := (hdψ.hasStrictFDerivAt_equiv hrp).mem_toOpenPartialHomeomorph_source
  have hψp : ψ p = 0 := by simp [ψ]
  have hlocal : ∀ᶠ z in 𝓝 p, f z = f p + ψ z ^ m := by
    filter_upwards [hfg] with z hz
    rw [show ψ z ^ m = (z - p) ^ m * g z by
      change ((z - p) * r z) ^ m = _
      rw [mul_pow, hrpow]]
    change f z - f p = (z - p) ^ m * g z at hz
    linear_combination hz
  obtain ⟨U, hUp, hU⟩ := eventually_nhds_iff.mp hlocal
  let e' := e.restr U
  have he'p : p ∈ e'.source := by
    rw [OpenPartialHomeomorph.restr_source' _ _ hU.1]
    exact ⟨hep, hU.2⟩
  refine ⟨m, e', Nat.pos_of_ne_zero hm, he'p, hψp, hψ, hdψ.hasDerivAt.deriv ▸ hrp, ?_⟩
  intro z hz
  exact hUp z ((OpenPartialHomeomorph.restr_source' e U hU.1) ▸ hz).2


theorem exists_local_homeomorph_pow_of_analytic_deriv_eq_zero
    {f : ℂ → ℂ} {p : ℂ} (hf : AnalyticAt ℂ f p)
    (hnon : ¬ ∀ᶠ z in 𝓝 p, f z = f p) (hcrit : deriv f p = 0) :
    ∃ (m : ℕ) (e : OpenPartialHomeomorph ℂ ℂ), 2 ≤ m ∧ p ∈ e.source ∧ e p = 0 ∧
      AnalyticAt ℂ e p ∧ deriv e p ≠ 0 ∧
      ∀ z ∈ e.source, f z = f p + e z ^ m := by
  obtain ⟨m, e, hm, hp, he0, heA, heD, heq⟩ := exists_local_homeomorph_pow_of_analytic hf hnon
  have hm1 : m ≠ 1 := by
    intro h
    have hnear : f =ᶠ[𝓝 p] (fun z => f p + e z) := by
      filter_upwards [e.open_source.mem_nhds hp] with z hz
      simpa only [h, pow_one] using heq z hz
    have hd := hnear.deriv_eq
    have hr := (heA.hasStrictDerivAt.hasDerivAt.const_add (f p)).deriv
    rw [hcrit, hr] at hd
    exact heD hd.symm
  exact ⟨m, e, by omega, hp, he0, heA, heD, heq⟩

end Complex

end

end
