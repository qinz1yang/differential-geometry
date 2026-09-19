import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.TangentCone.Prod
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.Deriv.Comp









noncomputable section

open Set Function
open scoped ContDiff

namespace DifferentialGeometry.Analysis

variable {K E F : Type*} [TopologicalSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]


theorem continuous_deriv_family_comp {f : K × ℝ → E} {g : E → F} {U : Set E}
    (hU : IsOpen U) (hg : ContDiffOn ℝ 1 g U)
    (hf : ∀ k, Differentiable ℝ (fun t => f (k, t))) (hc : Continuous f)
    (hd : Continuous (fun p : K × ℝ => deriv (fun t => f (p.1, t)) p.2))
    (hmap : ∀ p, f p ∈ U) :
    Continuous (fun p : K × ℝ => deriv (fun t => g (f (p.1, t))) p.2) := by
  have heq (p : K × ℝ) : deriv (fun t => g (f (p.1, t))) p.2 =
      fderiv ℝ g (f p) (deriv (fun t => f (p.1, t)) p.2) := by
    exact (((hg _ (hmap p)).contDiffAt (hU.mem_nhds (hmap p))).differentiableAt
      one_ne_zero |>.hasFDerivAt.comp_hasDerivAt p.2 (hf p.1 p.2).hasDerivAt).deriv
  simp_rw [heq]
  exact ((hg.continuousOn_fderiv_of_isOpen hU le_rfl).comp_continuous hc hmap).clm_apply hd



theorem continuous_iteratedDeriv_family_comp {f : K × ℝ → E} {g : E → F} {U : Set E}
    (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U)
    (hf : ∀ k, ContDiff ℝ ∞ (fun t => f (k, t)))
    (hjet : ∀ n, Continuous (fun p : K × ℝ => iteratedDeriv n (fun t => f (p.1, t)) p.2))
    (hmap : ∀ p, f p ∈ U) (n : ℕ) :
    Continuous (fun p : K × ℝ => iteratedDeriv n (fun t => g (f (p.1, t))) p.2) := by
  have hc : Continuous f := by simpa only [iteratedDeriv_zero] using hjet 0
  have heq (p : K × ℝ) :
      iteratedDeriv n (fun t => g (f (p.1, t))) p.2 =
        ∑ c : OrderedFinpartition n,
          iteratedFDerivWithin ℝ c.length g U (f p)
            (fun j => iteratedDeriv (c.partSize j) (fun t => f (p.1, t)) p.2) := by
    simpa only [iteratedDerivWithin_univ, Function.comp_def, Prod.mk.eta] using
      iteratedDerivWithin_vcomp_eq_sum_orderedFinpartition (hg _ (hmap p))
        (hf p.1).contDiffAt.contDiffWithinAt hU.uniqueDiffOn uniqueDiffOn_univ
        (mem_univ p.2) (fun t _ => hmap (p.1, t)) (show (n : ℕ∞ω) ≤ ∞ by exact_mod_cast le_top)
  simp_rw [heq]
  apply continuous_finsetSum
  intro c _
  exact continuous_eval.comp
    (((hg.continuousOn_iteratedFDerivWithin (by exact_mod_cast le_top) hU.uniqueDiffOn).comp_continuous
      hc hmap).prodMk (continuous_pi (fun j => hjet (c.partSize j))))

end DifferentialGeometry.Analysis

namespace DifferentialGeometry.Analysis

theorem continuousOn_iteratedFDerivWithin_comp
    {𝕜 P E F G : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace P]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    {S : Set P} {K : Set E} {U : Set F} {f : P → E → F} {g : P → F → G} {n : ℕ}
    (hK : UniqueDiffOn 𝕜 K) (hU : UniqueDiffOn 𝕜 U)
    (hf : ∀ p ∈ S, ContDiffOn 𝕜 n (f p) K) (hg : ∀ p ∈ S, ContDiffOn 𝕜 n (g p) U)
    (hjet : ∀ k ≤ n, ContinuousOn
      (fun q : P × E => iteratedFDerivWithin 𝕜 k (f q.1) K q.2) (S ×ˢ K))
    (hgjet : ∀ k ≤ n, ContinuousOn
      (fun q : P × F => iteratedFDerivWithin 𝕜 k (g q.1) U q.2) (S ×ˢ U))
    (hmap : Set.MapsTo (fun q : P × E => f q.1 q.2) (S ×ˢ K) U) :
    ContinuousOn
      (fun q : P × E => iteratedFDerivWithin 𝕜 n (g q.1 ∘ f q.1) K q.2) (S ×ˢ K) := by
  classical
  have hvalue : ContinuousOn (fun q : P × E => f q.1 q.2) (S ×ˢ K) := by
    exact ((continuousMultilinearCurryFin0 𝕜 E F).continuous.comp_continuousOn
      (hjet 0 (Nat.zero_le n))).congr fun _ _ => rfl
  have hterm (c : OrderedFinpartition n) : ContinuousOn
      (fun q : P × E => c.compAlongOrderedFinpartition
        (iteratedFDerivWithin 𝕜 c.length (g q.1) U (f q.1 q.2))
        (fun i => iteratedFDerivWithin 𝕜 (c.partSize i) (f q.1) K q.2)) (S ×ˢ K) := by
    let B := c.compAlongOrderedFinpartitionL 𝕜 E F G
    change ContinuousOn
      ((fun r => B r.1 r.2) ∘ (fun q : P × E =>
        (iteratedFDerivWithin 𝕜 c.length (g q.1) U (f q.1 q.2),
          fun i => iteratedFDerivWithin 𝕜 (c.partSize i) (f q.1) K q.2))) (S ×ˢ K)
    apply B.continuous_uncurry_of_multilinear.comp_continuousOn
      (ContinuousOn.prodMk ?_ ?_)
    · exact (hgjet c.length c.length_le).comp
        (continuousOn_fst.prodMk hvalue) (fun q hq => ⟨hq.1, hmap hq⟩)
    · exact continuousOn_pi.mpr fun i => hjet (c.partSize i) (c.partSize_le i)
  have hsum : ContinuousOn
      (fun q : P × E => ∑ c : OrderedFinpartition n, c.compAlongOrderedFinpartition
        (iteratedFDerivWithin 𝕜 c.length (g q.1) U (f q.1 q.2))
        (fun i => iteratedFDerivWithin 𝕜 (c.partSize i) (f q.1) K q.2)) (S ×ˢ K) :=
    continuousOn_finsetSum _ fun c _ => hterm c
  refine hsum.congr fun q hq => ?_
  simpa only [FormalMultilinearSeries.taylorComp,
    FormalMultilinearSeries.compAlongOrderedFinpartition, ftaylorSeriesWithin] using
    iteratedFDerivWithin_comp (hg q.1 hq.1 _ (hmap hq)) (hf q.1 hq.1 q.2 hq.2) hU hK hq.2
      (fun x hx => hmap (x := (q.1, x)) ⟨hq.1, hx⟩) (i := n) le_rfl

end DifferentialGeometry.Analysis

namespace DifferentialGeometry.Analysis

theorem continuousOn_iteratedFDerivWithin_family_comp
    {𝕜 P E F G : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace P]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    {S : Set P} {K : Set E} {U : Set F} {f : P → E → F} {g : F → G} {n : ℕ}
    (hK : UniqueDiffOn 𝕜 K) (hU : UniqueDiffOn 𝕜 U)
    (hf : ∀ p ∈ S, ContDiffOn 𝕜 n (f p) K) (hg : ContDiffOn 𝕜 n g U)
    (hjet : ∀ k ≤ n, ContinuousOn
      (fun q : P × E => iteratedFDerivWithin 𝕜 k (f q.1) K q.2) (S ×ˢ K))
    (hmap : Set.MapsTo (fun q : P × E => f q.1 q.2) (S ×ˢ K) U) :
    ContinuousOn
      (fun q : P × E => iteratedFDerivWithin 𝕜 n (g ∘ f q.1) K q.2) (S ×ˢ K) := by
  apply continuousOn_iteratedFDerivWithin_comp hK hU hf (fun _ _ => hg) hjet ?_ hmap
  intro k hk
  exact (hg.continuousOn_iteratedFDerivWithin (by exact_mod_cast hk) hU).comp
    continuousOn_snd (fun _ hq => hq.2)

end DifferentialGeometry.Analysis

section


namespace DifferentialGeometry.Analysis

theorem continuousOn_iteratedFDerivWithin_prod
    {𝕜 P E F G : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace P]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    {S : Set P} {K : Set E} {f : P → E → F} {g : P → E → G}
    (hK : UniqueDiffOn 𝕜 K) (n : ℕ)
    (hf : ∀ p ∈ S, ContDiffOn 𝕜 n (f p) K)
    (hg : ∀ p ∈ S, ContDiffOn 𝕜 n (g p) K)
    (hfj : ContinuousOn
      (fun q : P × E => iteratedFDerivWithin 𝕜 n (f q.1) K q.2) (S ×ˢ K))
    (hgj : ContinuousOn
      (fun q : P × E => iteratedFDerivWithin 𝕜 n (g q.1) K q.2) (S ×ˢ K)) :
    ContinuousOn
      (fun q : P × E => iteratedFDerivWithin 𝕜 n
        (fun z => (f q.1 z, g q.1 z)) K q.2) (S ×ˢ K) := by
  have h := (ContinuousMultilinearMap.prodL 𝕜 (fun _ : Fin n => E) F G).continuous
    |>.comp_continuousOn (hfj.prodMk hgj)
  apply h.congr
  intro q hq
  exact (iteratedFDerivWithin_prodMk (hf q.1 hq.1 q.2 hq.2)
    (hg q.1 hq.1 q.2 hq.2) hK hq.2 le_rfl)

end DifferentialGeometry.Analysis

end

namespace DifferentialGeometry.Analysis


theorem continuousOn_iteratedFDerivWithin_comp_graph
    {P F : Type*} [TopologicalSpace P] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {S : Set P} {J V : Set ℝ} {γ : P → ℝ × ℝ → ℝ} {d : P → ℝ × ℝ → F}
    {n : ℕ} (hJ : UniqueDiffOn ℝ J) (hV : UniqueDiffOn ℝ V)
    (hγ : ∀ p ∈ S, ContDiffOn ℝ n (γ p) (J ×ˢ V))
    (hd : ∀ p ∈ S, ContDiffOn ℝ n (d p) (J ×ˢ univ))
    (hγjet : ∀ k ≤ n, ContinuousOn
      (fun q : P × ℝ × ℝ => iteratedFDerivWithin ℝ k (γ q.1) (J ×ˢ V) q.2)
      (S ×ˢ J ×ˢ V))
    (hdjet : ∀ k ≤ n, ContinuousOn
      (fun q : P × ℝ × ℝ => iteratedFDerivWithin ℝ k (d q.1) (J ×ˢ univ) q.2)
      (S ×ˢ J ×ˢ univ)) :
    ContinuousOn
      (fun q : P × ℝ × ℝ => iteratedFDerivWithin ℝ n
        (fun z => d q.1 (z.1, γ q.1 z)) (J ×ˢ V) q.2) (S ×ˢ J ×ˢ V) := by
  let Q := fun p (z : ℝ × ℝ) => (z.1, γ p z)
  have hQ (p : P) (hp : p ∈ S) : ContDiffOn ℝ n (Q p) (J ×ˢ V) :=
    contDiffOn_fst.prodMk (hγ p hp)
  have hQjet (k : ℕ) (hk : k ≤ n) : ContinuousOn
      (fun q : P × ℝ × ℝ => iteratedFDerivWithin ℝ k (Q q.1) (J ×ˢ V) q.2)
      (S ×ˢ J ×ˢ V) := by
    apply continuousOn_iteratedFDerivWithin_prod (hJ.prod hV) k
      (fun _ _ => contDiffOn_fst)
      (fun p hp => (hγ p hp).of_le (by exact_mod_cast hk)) ?_ (hγjet k hk)
    have hs : ContDiffOn ℝ k (fun z : ℝ × ℝ => z.1) (J ×ˢ V) := contDiffOn_fst
    exact (hs.continuousOn_iteratedFDerivWithin le_rfl (hJ.prod hV)).comp continuousOn_snd
        (fun _ hq => hq.2)
  exact continuousOn_iteratedFDerivWithin_comp (hJ.prod hV)
    (hJ.prod uniqueDiffOn_univ) hQ hd hQjet hdjet (fun _ hq => ⟨hq.2.1, mem_univ _⟩)

end DifferentialGeometry.Analysis
