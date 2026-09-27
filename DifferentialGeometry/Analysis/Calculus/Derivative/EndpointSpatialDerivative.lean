import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.MetricSpace.Cauchy

set_option autoImplicit false

namespace DifferentialGeometry.Analysis

open Filter Set
open scoped Topology

theorem exists_tendstoUniformlyOn_right_endpoint_of_time_lipschitz
    {X F : Type*} [MetricSpace F] [CompleteSpace F]
    {a b C : ℝ} (hab : a < b) {U : Set X} (f : ℝ → X → F)
    (hLip : ∀ s ∈ Ioo a b, ∀ t ∈ Ioo a b, ∀ x ∈ U,
      dist (f s x) (f t x) ≤ C * |s - t|) :
    ∃ g : X → F, TendstoUniformlyOn f g (𝓝[Ioo a b] b) U := by
  classical
  let L := 𝓝[Ioo a b] b
  let : NeBot L := right_nhdsWithin_Ioo_neBot hab
  have hmod : Tendsto (fun st : ℝ × ℝ => C * |st.1 - st.2|) (L ×ˢ L) (𝓝 0) := by
    have hst : Tendsto (fun st : ℝ × ℝ => st) (L ×ˢ L) (𝓝 (b, b)) := by
      rw [nhds_prod_eq]
      exact (tendsto_fst.mono_right nhdsWithin_le_nhds).prodMk
        (tendsto_snd.mono_right nhdsWithin_le_nhds)
    have hcont : ContinuousAt (fun st : ℝ × ℝ => C * |st.1 - st.2|) (b, b) := by
      fun_prop
    simpa only [Function.comp_def, sub_self, abs_zero, mul_zero] using hcont.tendsto.comp hst
  have huc : UniformCauchySeqOn f L U := by
    intro V hV
    obtain ⟨ε, hε, hεV⟩ := Metric.mem_uniformity_dist.mp hV
    have hmem : ∀ᶠ st : ℝ × ℝ in L ×ˢ L, st.1 ∈ Ioo a b ∧ st.2 ∈ Ioo a b :=
      (tendsto_fst.eventually eventually_mem_nhdsWithin).and
        (tendsto_snd.eventually eventually_mem_nhdsWithin)
    filter_upwards [hmem, hmod.eventually_lt_const hε] with st hst hsmall x hx
    exact hεV ((hLip st.1 hst.1 st.2 hst.2 x hx).trans_lt hsmall)
  have hex : ∀ x : X, ∃ y : F, x ∈ U → Tendsto (fun t => f t x) L (𝓝 y) := by
    intro x
    by_cases hx : x ∈ U
    · obtain ⟨y, hy⟩ := cauchy_map_iff_exists_tendsto.mp (huc.cauchy_map hx)
      exact ⟨y, fun _ => hy⟩
    · exact ⟨f a x, fun hx' => False.elim (hx hx')⟩
  choose g hg using hex
  exact ⟨g, huc.tendstoUniformlyOn_of_tendsto hg⟩

variable {X F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem exists_tendstoUniformlyOn_right_endpoint_of_interior_deriv_bound
    {a b C : ℝ} (hab : a < b) {U : Set X} (f d : ℝ → X → F)
    (hderiv : ∀ t ∈ Ioo a b, ∀ x ∈ U, HasDerivAt (fun s => f s x) (d t x) t)
    (hbound : ∀ t ∈ Ioo a b, ∀ x ∈ U, ‖d t x‖ ≤ C) :
    ∃ g : X → F, TendstoUniformlyOn f g (𝓝[Ioo a b] b) U := by
  apply exists_tendstoUniformlyOn_right_endpoint_of_time_lipschitz (C := C) hab f
  intro s hs t ht x hx
  have hdiff : ∀ r ∈ Ioo a b, DifferentiableAt ℝ (fun r => f r x) r :=
    fun r hr => (hderiv r hr x hx).differentiableAt
  have hnorm : ∀ r ∈ Ioo a b, ‖deriv (fun r => f r x) r‖ ≤ C := by
    intro r hr
    rw [(hderiv r hr x hx).deriv]
    exact hbound r hr x hx
  simpa only [dist_eq_norm, Real.norm_eq_abs] using
    (convex_Ioo a b).norm_image_sub_le_of_norm_deriv_le hdiff hnorm ht hs

theorem tendstoUniformlyOn_fderiv_right_endpoint_of_time_lipschitz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b C : ℝ} (hab : a < b) {U : Set E} (hU : IsOpen U)
    (f : ℝ → E → F) (f' : ℝ → E → E →L[ℝ] F)
    (hderiv : ∀ t ∈ Ioo a b, ∀ x ∈ U, HasFDerivAt (f t) (f' t x) x)
    (hcont : ∀ x ∈ U, Tendsto (fun t => f t x) (𝓝[Ioo a b] b) (𝓝 (f b x)))
    (hLip : ∀ s ∈ Ioo a b, ∀ t ∈ Ioo a b, ∀ x ∈ U,
      dist (f' s x) (f' t x) ≤ C * |s - t|) :
    TendstoUniformlyOn f' (fderiv ℝ (f b)) (𝓝[Ioo a b] b) U := by
  obtain ⟨g, hg⟩ := exists_tendstoUniformlyOn_right_endpoint_of_time_lipschitz hab f' hLip
  let : NeBot (𝓝[Ioo a b] b) := right_nhdsWithin_Ioo_neBot hab
  have hdiff : ∀ x ∈ U, HasFDerivAt (f b) (g x) x := by
    intro x hx
    have hd : ∀ᶠ tx : ℝ × E in (𝓝[Ioo a b] b) ×ˢ 𝓝 x,
        HasFDerivAt (f tx.1) (f' tx.1 tx.2) tx.2 := by
      filter_upwards [tendsto_fst.eventually eventually_mem_nhdsWithin,
        tendsto_snd.eventually (hU.mem_nhds hx)] with tx ht hx'
      exact hderiv tx.1 ht tx.2 hx'
    apply hasFDerivAt_of_tendstoUniformlyOnFilter _ hd
      (eventually_of_mem (hU.mem_nhds hx) (fun y hy => hcont y hy))
    simpa only [IsOpen.nhdsWithin_eq hU hx] using
      tendstoLocallyUniformlyOn_iff_filter.mp hg.tendstoLocallyUniformlyOn x hx
  exact hg.congr_right (fun x hx => (hdiff x hx).fderiv.symm)

end DifferentialGeometry.Analysis
