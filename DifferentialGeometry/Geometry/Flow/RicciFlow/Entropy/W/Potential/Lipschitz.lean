import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.W.Functional
import DifferentialGeometry.Geometry.Metric.ChartLipschitz.Spacetime
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

noncomputable section

open Manifold Set
open scoped Manifold ContDiff NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Entropy

private theorem locallyLipschitzOn_density_core (n : ℕ) :
    LocallyLipschitzOn (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))
      (fun q : ℝ × ℝ => perelmanDensityPrefactor n q.1 * Real.exp (-q.2)) := by
  apply ContDiffOn.locallyLipschitzOn ((convex_Ioi 0).prod convex_univ)
  intro q hq
  apply ContDiffAt.contDiffWithinAt
  apply ContDiffAt.mul
  · exact (contDiffAt_const.mul contDiffAt_fst).rpow_const_of_ne
      (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) (ne_of_gt hq.1))
  · exact contDiffAt_snd.neg.exp

theorem locallyLipschitzOn_perelmanDensity
    {X : Type*} [PseudoEMetricSpace X] {s : Set X} {t f : X → ℝ}
    (ht : LocallyLipschitzOn s t) (hf : LocallyLipschitzOn s f)
    (hpos : ∀ x ∈ s, 0 < t x) (n : ℕ) :
    LocallyLipschitzOn s (fun x => perelmanDensity n (t x) f x) :=
  (locallyLipschitzOn_density_core n).comp (ht.prodMk hf) (fun x hx => ⟨hpos x hx, mem_univ _⟩)

theorem locallyLipschitzOn_perelmanDensity_in_chart_of_spacetime_bounds
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RegularSpace M] [PreconnectedSpace M]
    (g : SmoothRiemannianMetric I M) (p : M) {a b : ℝ} (hab : a ≤ b)
    (ell : M × Icc a b → ℝ)
    (hell : ∀ R : ℝ, 0 ≤ R → ∃ K : ℝ≥0,
      ∀ x ∈ riemannianClosedBallOf g p R, ∀ y ∈ riemannianClosedBallOf g p R,
      ∀ s t : Icc a b, |ell (x, s) - ell (y, t)| ≤
        (K : ℝ) * ((riemannianEDistOf g x y).toReal + |(s : ℝ) - t|))
    (α : M) (n : ℕ) :
    LocallyLipschitzOn (Ioi (0 : ℝ) ×ˢ (extChartAt I α).target)
      (fun q : ℝ × E => perelmanDensity n q.1
        (fun x => ell (x, projIcc a b hab q.1)) ((extChartAt I α).symm q.2)) := by
  have h := Geometry.Riemannian.locallyLipschitzOn_comp_extChartAt_symm_of_spacetime_bounds g p hab ell hell α
  exact locallyLipschitzOn_perelmanDensity LipschitzWith.prod_fst.locallyLipschitz.locallyLipschitzOn
    (h.mono (Set.prod_mono (subset_univ _) Subset.rfl)) (fun _ hx => hx.1) n

end DifferentialGeometry.PDE.RicciFlow.Entropy
