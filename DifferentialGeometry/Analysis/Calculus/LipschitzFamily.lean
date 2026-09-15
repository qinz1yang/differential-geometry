import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Algebra.Support
import Mathlib.Tactic.NormNum

open scoped Topology NNReal

namespace ContDiff

theorem eventually_lipschitzWith_sub_slice
    {P V F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : P × V → F} (hG : ContDiff ℝ 1 G) (hGc : HasCompactSupport G)
    (p₀ : P) {ε : ℝ≥0} (hε : 0 < ε) :
    ∀ᶠ p in 𝓝 p₀, LipschitzWith ε (fun y => G (p, y) - G (p₀, y)) := by
  let H : P × V → F := fun q => G q - G (p₀, q.2)
  have hH : ContDiff ℝ 1 H :=
    hG.sub (hG.comp (contDiff_const.prodMk contDiff_snd))
  let D : P × V → V →L[ℝ] F := fun q => fderiv ℝ (fun y => H (q.1, y)) q.2
  have hD : Continuous D :=
    Continuous.fderiv (hH.comp (contDiff_fst.fst.prodMk contDiff_snd))
      continuous_snd le_rfl
  have hD₀ (y : V) : D (p₀, y) = 0 := by
    simp [D, H]
  let S : Set V := Prod.snd '' tsupport G
  have hS : IsCompact S := hGc.image continuous_snd
  have hzero (p : P) {y : V} (hy : y ∉ S) : G (p, y) = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hpy => hy ⟨(p, y), hpy, rfl⟩)
  have hDoff (p : P) {y : V} (hy : y ∉ S) : D (p, y) = 0 := by
    have hloc : (fun z => H (p, z)) =ᶠ[𝓝 y] 0 := by
      filter_upwards [hS.isClosed.isOpen_compl.mem_nhds hy] with z hz
      change G (p, z) - G (p₀, z) = 0
      rw [hzero p hz, hzero p₀ hz, sub_self]
    change fderiv ℝ (fun z => H (p, z)) y = 0
    rw [hloc.fderiv_eq, fderiv_zero, Pi.zero_apply]
  have hbound : ∀ᶠ p in 𝓝 p₀, ∀ y ∈ S, ‖D (p, y)‖₊ < ε := by
    apply hS.eventually_forall_of_forall_eventually
    intro y hy
    exact (isOpen_lt hD.nnnorm continuous_const).mem_nhds (by simpa [hD₀] using hε)
  filter_upwards [hbound] with p hp
  apply lipschitzWith_of_nnnorm_fderiv_le
    ((hH.comp (contDiff_const.prodMk contDiff_id)).differentiable (by norm_num))
  intro y
  change ‖D (p, y)‖₊ ≤ ε
  by_cases hy : y ∈ S
  · exact (hp y hy).le
  · rw [hDoff p hy, nnnorm_zero]
    exact zero_le

end ContDiff

set_option autoImplicit false
noncomputable section
open Filter

theorem exists_tendstoUniformly_nhdsLT_of_hasDerivAt_nnnorm_le
    {X F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {a b : ℝ} (hab : a < b) (Y : ℝ → X → F) (D : ℝ → X → F) (C : ℝ≥0)
    (hderiv : ∀ t, t ∈ Set.Ioo a b → ∀ x, HasDerivAt (fun s : ℝ => Y s x) (D t x) t)
    (hbound : ∀ t, t ∈ Set.Ioo a b → ∀ x, ‖D t x‖₊ ≤ C) :
    ∃ YT : X → F, TendstoUniformly Y YT (𝓝[<] b) := by
  have hL : ∀ x, LipschitzOnWith C (fun s : ℝ => Y s x) (Set.Ioo a b) := by
    intro x
    apply Convex.lipschitzOnWith_of_nnnorm_hasDerivWithin_le (convex_Ioo a b)
    · intro t ht
      exact (hderiv t ht x).hasDerivWithinAt
    · intro t ht
      exact hbound t ht x
  have hC : UniformCauchySeqOn Y (𝓝[<] b) (Set.univ : Set X) := by
    intro V hV
    obtain ⟨eps, heps, hsub⟩ := Metric.mem_uniformity_dist.mp hV
    have htime : Tendsto (fun t : ℝ => t) (𝓝[<] b) (𝓝 b) := nhdsWithin_le_nhds
    have ht : Tendsto (fun p : ℝ × ℝ => (C : ℝ) * dist p.1 p.2)
        ((𝓝[<] b) ×ˢ (𝓝[<] b)) (𝓝 0) := by
      simpa only [dist_self, mul_zero, Function.comp_def] using
        (tendsto_const_nhds.mul
          ((htime.comp tendsto_fst).dist (htime.comp tendsto_snd)))
    have hnear : ∀ᶠ t in 𝓝[<] b, t ∈ Set.Ioo a b := Ioo_mem_nhdsLT hab
    filter_upwards [ht.eventually (gt_mem_nhds heps), hnear.prod_mk hnear] with p hp hmem
    intro x hx
    exact hsub ((hL x).dist_le_mul p.1 hmem.1 p.2 hmem.2 |>.trans_lt hp)
  classical
  have hpoint : ∀ x, ∃ y, Tendsto (fun t : ℝ => Y t x) (𝓝[<] b) (𝓝 y) :=
    fun x => cauchy_map_iff_exists_tendsto.mp (hC.cauchy_map (Set.mem_univ x))
  choose YT hYT using hpoint
  exact ⟨YT, tendstoUniformlyOn_univ.mp (hC.tendstoUniformlyOn_of_tendsto (fun x _ => hYT x))⟩

end
