import DifferentialGeometry.Analysis.Calculus.TimeJet.MixedJets
import DifferentialGeometry.Analysis.Calculus.TimeJet.SpatialDerivatives

noncomputable section

open Set
open scoped ContDiff Topology

namespace DifferentialGeometry.Analysis

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem hasDerivWithinAt_mixed_derivatives_comp_graph
    {J : Set ℝ} (hJ : UniqueDiffOn ℝ J)
    (hacc : J ⊆ closure (interior J)) {H : ℝ → ℝ → F}
    (hH : ContDiffOn ℝ ∞ (Function.uncurry H) (J ×ˢ univ))
    {γ : ℝ → ℝ} {v t : ℝ} (ht : t ∈ J)
    (hγ : HasDerivWithinAt γ v J t) (k j : ℕ) :
    HasDerivWithinAt
      (fun s => iteratedDerivWithin k (fun r => iteratedDeriv j (H r) (γ s)) J s)
      (iteratedDerivWithin (k + 1) (fun r => iteratedDeriv j (H r) (γ t)) J t +
        v • iteratedDerivWithin k (fun r => iteratedDeriv (j + 1) (H r) (γ t)) J t)
      J t := by
  have hs := contDiffOn_iteratedDerivWithin_iteratedDeriv hJ isOpen_univ hH k j
  have hd := (hs.differentiableOn (by simp) (t, γ t) ⟨ht, mem_univ _⟩).hasFDerivWithinAt
  rw [fderivWithin_iteratedDerivWithin_iteratedDeriv hJ hacc isOpen_univ hH k j
    ⟨ht, mem_univ _⟩] at hd
  have hpair : HasDerivWithinAt (fun s : ℝ => (s, γ s)) (1, v) J t :=
    (hasDerivWithinAt_id t J).prodMk hγ
  have hmaps : MapsTo (fun s : ℝ => (s, γ s)) J (J ×ˢ univ) :=
    fun s hs => ⟨hs, mem_univ _⟩
  have hh := hd.comp_hasDerivWithinAt t hpair hmaps
  simpa only [Function.comp_def, add_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', one_smul] using hh

theorem continuousOn_mixed_derivatives_comp_graph
    {P : Type*} [TopologicalSpace P] {S : Set P} {J V : Set ℝ}
    {H : P → ℝ → ℝ → F} {γ : P → ℝ → ℝ → ℝ}
    (hγ : ContinuousOn (fun q : P × ℝ × ℝ => γ q.1 q.2.1 q.2.2)
      (S ×ˢ J ×ˢ V))
    (hH : ∀ k j : ℕ, ContinuousOn
      (fun q : P × ℝ × ℝ =>
        iteratedDerivWithin k (fun t => iteratedDeriv j (H q.1 t) q.2.2) J q.2.1)
      (S ×ˢ J ×ˢ univ)) (k j : ℕ) :
    ContinuousOn
      (fun q : P × ℝ × ℝ => iteratedDerivWithin k
        (fun t => iteratedDeriv j (H q.1 t) (γ q.1 q.2.1 q.2.2)) J q.2.1)
      (S ×ˢ J ×ˢ V) := by
  exact (hH k j).comp
    (continuousOn_fst.prodMk
      (((by fun_prop) : ContinuousOn (fun q : P × ℝ × ℝ => q.2.1)
        (S ×ˢ J ×ˢ V)).prodMk hγ))
    (fun q hq => ⟨hq.1, hq.2.1, mem_univ _⟩)

theorem hasDerivWithinAt_iteratedDeriv_of_evolution
    {G R : ℝ → ℝ → F} {J V : Set ℝ}
    (hJ : UniqueDiffOn ℝ J) (hacc : J ⊆ closure (interior J))
    (hV : IsOpen V)
    (hG : ContDiffOn ℝ ∞ (Function.uncurry G) (J ×ˢ V))
    (hpde : ∀ t ∈ J, ∀ x ∈ V,
      HasDerivWithinAt (fun s => G s x) (R t x) J t)
    (j : ℕ) {t x : ℝ} (ht : t ∈ J) (hx : x ∈ V) :
    HasDerivWithinAt (fun s => iteratedDeriv j (G s) x)
      (iteratedDeriv j (R t) x) J t := by
  have hswap : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => G q.2 q.1) (V ×ˢ J) :=
    hG.comp (contDiff_snd.prodMk contDiff_fst).contDiffOn (fun q hq => ⟨hq.2, hq.1⟩)
  have hd := hasDerivWithinAt_iteratedDeriv_fst
    (G := fun x t => G t x) hV hJ hacc hswap j hx ht
  have heq : (fun y => derivWithin (fun s => G s y) J t) =ᶠ[𝓝 x] R t := by
    filter_upwards [hV.mem_nhds hx] with y hy
    exact (hpde t ht y hy).derivWithin (hJ t ht)
  rw [heq.iteratedDeriv_eq j] at hd
  exact hd

end DifferentialGeometry.Analysis
