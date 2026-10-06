import DifferentialGeometry.Analysis.Calculus.Hadamard.Parametric
import Mathlib.Topology.Compactness.Compact

set_option autoImplicit false
noncomputable section

open Set Filter
open scoped ContDiff Topology
open DifferentialGeometry.Analysis.Calculus

namespace DifferentialGeometry.Analysis.Calculus.Hadamard

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A smooth extension of the normalized positive-scale defining function.
Its relation to a quotient requires the actual center condition `r = d a`. -/
def normalizedFactor (d : V → ℝ) (dilation : ℝ) (a : V) (r : ℝ) (z : V) : ℝ :=
  1 + dilation * hadamardFactor (fun t : ℝ => d (a + t • z)) 0 (dilation * r)

theorem contDiff_normalizedFactor {d : V → ℝ} (hd : ContDiff ℝ ∞ d) :
    ContDiff ℝ ∞ (fun q : ℝ × ((V × ℝ) × V) =>
      normalizedFactor d q.1 q.2.1.1 q.2.1.2 q.2.2) := by
  let D : (V × V) × ℝ → ℝ := fun p => d (p.1.1 + p.2 • p.1.2)
  have hD : ContDiff ℝ ∞ D :=
    hd.comp (contDiff_fst.fst.add (contDiff_snd.smul contDiff_fst.snd))
  have hH := contDiff_hadamardFactor_param D hD 0
  have hP : ContDiff ℝ ∞ (fun q : ℝ × ((V × ℝ) × V) =>
      ((q.2.1.1, q.2.2), q.1 * q.2.1.2)) := by fun_prop
  exact contDiff_const.add (contDiff_fst.mul (hH.comp hP))

theorem defining_function_eq_scale_mul_normalizedFactor
    {d : V → ℝ} (hd : ContDiff ℝ ∞ d) (dilation : ℝ) (a : V) (r : ℝ) (z : V)
    (hr : r = d a) :
    d (a + (dilation * r) • z) = r * normalizedFactor d dilation a r z := by
  have hf : ContDiff ℝ ∞ (fun t : ℝ => d (a + t • z)) :=
    hd.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  have hh := hadamard_factorization (fun t : ℝ => d (a + t • z)) hf 0 (dilation * r)
  simp only [zero_smul, add_zero, sub_zero, smul_eq_mul] at hh
  rw [← hr] at hh
  dsimp only [normalizedFactor]
  nlinarith [hh]

theorem exists_uniform_small_scale_normalizedFactor
    {d : V → ℝ} (hd : ContDiff ℝ ∞ d) {K : Set (V × ℝ)} {Z : Set V}
    (hK : IsCompact K) (hZ : IsCompact Z) :
    ∃ η : ℝ, 0 < η ∧ ∀ dilation : ℝ, |dilation| < η → ∀ p ∈ K, ∀ z ∈ Z,
      (1 / 2 : ℝ) < normalizedFactor d dilation p.1 p.2 z ∧
        normalizedFactor d dilation p.1 p.2 z < 3 / 2 := by
  let R : ℝ × ((V × ℝ) × V) → ℝ := fun q =>
    normalizedFactor d q.1 q.2.1.1 q.2.1.2 q.2.2
  have hR : Continuous R := (contDiff_normalizedFactor hd).continuous
  have hnear : ∀ᶠ dilation : ℝ in 𝓝 0, ∀ p ∈ K ×ˢ Z,
      (1 / 2 : ℝ) < R (dilation, p) ∧ R (dilation, p) < 3 / 2 := by
    apply (hK.prod hZ).eventually_forall_of_forall_eventually
    intro p _
    have hRzero : R (0, p) = 1 := by simp [R, normalizedFactor]
    exact hR.continuousAt.eventually (isOpen_Ioo.mem_nhds (by
      change (1 / 2 : ℝ) < R (0, p) ∧ R (0, p) < 3 / 2
      rw [hRzero]
      constructor <;> norm_num))
  obtain ⟨η, hη, hball⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨η, hη, fun dilation hdilation p hp z hz => ?_⟩
  exact hball (by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hdilation)
    (p, z) ⟨hp, hz⟩

end DifferentialGeometry.Analysis.Calculus.Hadamard
