import DifferentialGeometry.Analysis.Viscosity.ColeHopf
import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.W.Potential.Defs

noncomputable section
open Filter
open scoped Topology ContDiff
namespace DifferentialGeometry.PDE.RicciFlow.Entropy
variable {E κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype κ]

theorem perelmanDensity_upper_test_of_conjugate_heat_lower_test
    (n : ℕ) (f : ℝ × E → ℝ) {z : ℝ × E} (ht : 0 < z.1)
    (d : E) (b : κ → E) (a : κ → κ → ℝ) (R : ℝ)
    (htests : ∀ psi : ℝ × E → ℝ, ContDiffAt ℝ 2 psi z →
      IsLocalMin (fun y => f y - psi y) z →
        0 ≤ fderiv ℝ psi z (1, d) -
          (∑ i, ∑ j, a i j * fderiv ℝ (fderiv ℝ psi) z (0, b i) (0, b j)) +
          (∑ i, ∑ j, a i j * fderiv ℝ psi z (0, b i) * fderiv ℝ psi z (0, b j)) -
          R + (n : ℝ) / (2 * z.1))
    (phi : ℝ × E → ℝ) (hphi : ContDiffAt ℝ 2 phi z)
    (hmax : IsLocalMax (fun y => perelmanDensity n y.1 f y - phi y) z) :
    fderiv ℝ phi z (1, d) -
      (∑ i, ∑ j, a i j * fderiv ℝ (fderiv ℝ phi) z (0, b i) (0, b j)) +
      R * perelmanDensity n z.1 f z ≤ 0 := by
  let q : ℝ → ℝ := fun t => (n : ℝ) / 2 * Real.log (4 * Real.pi * t)
  have hbase : 0 < 4 * Real.pi * z.1 := mul_pos (mul_pos (by norm_num) Real.pi_pos) ht
  have hq : ContDiffAt ℝ 2 q z.1 :=
    contDiffAt_const.mul ((contDiffAt_const.mul contDiffAt_id).log hbase.ne')
  have hqderiv : deriv q z.1 = (n : ℝ) / (2 * z.1) := by
    have hh := (((hasDerivAt_id z.1).const_mul (4 * Real.pi)).log hbase.ne').const_mul ((n : ℝ) / 2)
    have heq := hh.deriv
    change deriv q z.1 = _ at heq
    rw [heq]
    simp only [id_eq]
    field_simp
  have hu (w : ℝ × E) (hw : 0 < w.1) :
      Real.exp (-(f w + q w.1)) = perelmanDensity n w.1 f w := by
    rw [perelmanDensity, ← Real.exp_log (prefactor_pos n hw), log_prefactor n hw, ← Real.exp_add]
    congr 1
    dsimp only [q]
    ring
  have hmax' : IsLocalMax (fun w => Real.exp (-(f w + q w.1)) - phi w) z := by
    have hn : ∀ᶠ w : ℝ × E in 𝓝 z, 0 < w.1 :=
      continuous_fst.continuousAt.eventually (lt_mem_nhds ht)
    filter_upwards [hmax, hn] with w hw hwt
    rw [hu z ht, hu w hwt]
    exact hw
  have hh := Analysis.Viscosity.cole_hopf_upper_test_add_time f z d b a (-R) q hq
    (fun psi hpsi hm => by simpa only [hqderiv, sub_eq_add_neg] using htests psi hpsi hm)
    phi hphi hmax'
  simpa only [hu z ht, neg_mul, sub_neg_eq_add] using hh

end DifferentialGeometry.PDE.RicciFlow.Entropy
