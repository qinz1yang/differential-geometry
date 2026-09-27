import Mathlib.Analysis.Calculus.ContDiff.Comp

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff Topology BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

variable {P E F G : Type*} [TopologicalSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem continuousOn_spatial_jet_comp
    {U : Set E} (hU : IsOpen U) {V : Set F} (hV : IsOpen V)
    (f : P → E → F) (hf : ∀ p, ContDiffOn ℝ ∞ (f p) U)
    (Φ : F → G) (hΦ : ContDiffOn ℝ ∞ Φ V)
    {K : Set (P × E)} (hKU : ∀ q ∈ K, q.2 ∈ U)
    (hmap : ∀ q ∈ K, f q.1 q.2 ∈ V) (a : ℕ)
    (hjets : ∀ j, j ≤ a → ContinuousOn
      (fun q : P × E => iteratedFDeriv ℝ j (f q.1) q.2) K) :
    ContinuousOn (fun q : P × E => iteratedFDeriv ℝ a (fun x => Φ (f q.1 x)) q.2) K := by
  classical
  have hf0 : ContinuousOn (fun q : P × E => f q.1 q.2) K := by
    have h := (hjets 0 (Nat.zero_le a)).eval_const (fun i : Fin 0 => Fin.elim0 i)
    simpa only [iteratedFDeriv_zero_apply] using h
  have houter (j : ℕ) : ContinuousOn
      (fun q : P × E => iteratedFDeriv ℝ j Φ (f q.1 q.2)) K :=
    (ContinuousOn.continuousOn_iteratedFDeriv hΦ hV
      (by exact_mod_cast le_top)).comp hf0 hmap
  have hseries : ContinuousOn (fun q : P × E =>
      (ftaylorSeries ℝ Φ (f q.1 q.2)).taylorComp (ftaylorSeries ℝ (f q.1) q.2) a) K := by
    unfold FormalMultilinearSeries.taylorComp
    apply continuousOn_finsetSum
    intro c _
    let B := c.compAlongOrderedFinpartitionL ℝ E F G
    change ContinuousOn
      (fun q : P × E => B (iteratedFDeriv ℝ c.length Φ (f q.1 q.2))
        (fun i => iteratedFDeriv ℝ (c.partSize i) (f q.1) q.2)) K
    exact B.continuous_uncurry_of_multilinear.comp_continuousOn
      ((houter c.length).prodMk (continuousOn_pi.mpr fun i => hjets _ (c.partSize_le i)))
  refine hseries.congr ?_
  intro q hq
  exact iteratedFDeriv_comp
    (hΦ.contDiffAt (hV.mem_nhds (hmap q hq)))
    ((hf q.1).contDiffAt (hU.mem_nhds (hKU q hq)))
    (by exact_mod_cast le_top : (a : WithTop ℕ∞) ≤ ∞)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
