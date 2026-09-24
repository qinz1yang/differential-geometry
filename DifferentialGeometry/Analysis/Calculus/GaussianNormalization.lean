import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz

noncomputable section

open Set
open scoped Topology

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {X : Type*} [PseudoMetricSpace X]

theorem locallyLipschitzOn_exp_neg_add
    {a b : ℝ} {Ω : Set X} {f : ℝ × X → ℝ}
    (hf : LocallyLipschitzOn (Icc a b ×ˢ Ω) f)
    {c : ℝ → ℝ} (hc : LocallyLipschitzOn (Icc a b) c) :
    LocallyLipschitzOn (Icc a b ×ˢ Ω)
      (fun q : ℝ × X => Real.exp (-f q + c q.1)) := by
  obtain ⟨C, hC⟩ := hc.exists_lipschitzOnWith_of_compact isCompact_Icc
  have hp : LipschitzOnWith 1 (Prod.fst : ℝ × X → ℝ) (Icc a b ×ˢ Ω) :=
    LipschitzWith.prod_fst.lipschitzOnWith
  have hcp : LipschitzOnWith C (fun q : ℝ × X => c q.1) (Icc a b ×ˢ Ω) := by
    simpa only [mul_one, Function.comp_def] using hC.comp hp (fun _ hq => hq.1)
  have hcl : LocallyLipschitzOn (Icc a b ×ˢ Ω) (fun q : ℝ × X => c q.1) := by
    intro q hq
    exact ⟨C, Icc a b ×ˢ Ω, self_mem_nhdsWithin, hcp⟩
  apply locallyLipschitzOn_iff_restrict.mpr
  exact (Real.contDiff_exp : ContDiff ℝ 1 Real.exp).locallyLipschitz.comp
    (hf.neg.add hcl).restrict

theorem locallyLipschitzOn_exp_gaussian_normalization
    {a b : ℝ} (ha : 0 < a) {Ω : Set X} {f : ℝ × X → ℝ}
    (hf : LocallyLipschitzOn (Icc a b ×ˢ Ω) f) (n : ℝ) :
    LocallyLipschitzOn (Icc a b ×ˢ Ω) (fun q : ℝ × X =>
      Real.exp (-f q - n / 2 * Real.log q.1 - n / 2 * Real.log (4 * Real.pi))) := by
  have hc : LocallyLipschitzOn (Icc a b)
      (fun t : ℝ => -n / 2 * Real.log t - n / 2 * Real.log (4 * Real.pi)) := by
    intro t ht
    have ht0 : 0 < t := ha.trans_le ht.1
    have hd : ContDiffAt ℝ 1
        (fun t : ℝ => -n / 2 * Real.log t - n / 2 * Real.log (4 * Real.pi)) t :=
      (contDiffAt_const.mul (Real.contDiffAt_log.mpr ht0.ne')).sub contDiffAt_const
    obtain ⟨C, V, hV, hLip⟩ := hd.exists_lipschitzOnWith
    exact ⟨C, V, mem_nhdsWithin_of_mem_nhds hV, hLip⟩
  simpa only [sub_eq_add_neg, neg_div, neg_mul, add_assoc] using
    locallyLipschitzOn_exp_neg_add hf hc

end DifferentialGeometry.Analysis.Sobolev.Euclidean
