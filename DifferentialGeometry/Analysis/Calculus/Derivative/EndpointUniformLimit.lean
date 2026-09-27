import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.UniformSpace.UniformConvergence

set_option autoImplicit false

namespace DifferentialGeometry.Analysis

open Filter Set
open scoped Topology

variable {X F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem exists_tendstoUniformlyOn_right_endpoint_of_deriv_bound
    {a b C : ℝ} (hab : a < b) {K : Set X}
    (f d : ℕ → ℝ → X → F) (g : ℝ → X → F)
    (hderiv : ∀ n x, x ∈ K → ∀ t ∈ Icc a b,
      HasDerivWithinAt (fun s => f n s x) (d n t x) (Icc a b) t)
    (hbound : ∀ n x, x ∈ K → ∀ t ∈ Ico a b, ‖d n t x‖ ≤ C)
    (hconv : ∀ t ∈ Ioo a b,
      TendstoUniformlyOn (fun n => f n t) (g t) atTop K) :
    ∃ gEnd : X → F,
      TendstoUniformlyOn (fun n => f n b) gEnd atTop K ∧
      TendstoUniformlyOn g gEnd (𝓝[Ioo a b] b) K := by
  classical
  have hnear : ∀ n t, t ∈ Ioo a b → ∀ x ∈ K,
      dist (f n b x) (f n t x) ≤ C * (b - t) := by
    intro n t ht x hx
    have hsub : Icc t b ⊆ Icc a b := Icc_subset_Icc ht.1.le le_rfl
    have h := norm_image_sub_le_of_norm_deriv_le_segment'
      (fun s hs => (hderiv n x hx s (hsub hs)).mono hsub)
      (fun s hs => hbound n x hx s ⟨ht.1.le.trans hs.1, hs.2⟩)
      b (right_mem_Icc.mpr ht.2.le)
    simpa only [dist_eq_norm] using h
  have hmod : Tendsto (fun t : ℝ => C * (b - t)) (𝓝[Ioo a b] b) (𝓝 0) := by
    have hc : ContinuousAt (fun t : ℝ => C * (b - t)) b := by fun_prop
    simpa only [sub_self, mul_zero] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have huc : UniformCauchySeqOn (fun n => f n b) atTop K := by
    rw [Metric.uniformCauchySeqOn_iff]
    intro ε hε
    let : NeBot (𝓝[Ioo a b] b) := right_nhdsWithin_Ioo_neBot hab
    obtain ⟨t, ht, hsmall⟩ :=
      (eventually_mem_nhdsWithin.and (hmod.eventually_lt_const (by positivity : 0 < ε / 4))).exists
    obtain ⟨N, hN⟩ := eventually_atTop.mp
      (Metric.tendstoUniformlyOn_iff.mp (hconv t ht) (ε / 4) (by positivity))
    refine ⟨N, fun n hn m hm x hx => ?_⟩
    have hnnear := (hnear n t ht x hx).trans_lt hsmall
    have hmnear : dist (f m t x) (f m b x) < ε / 4 := by
      simpa only [dist_comm] using (hnear m t ht x hx).trans_lt hsmall
    have hnconv : dist (f n t x) (g t x) < ε / 4 := by
      simpa only [dist_comm] using hN n hn x hx
    have hmconv := hN m hm x hx
    have hfirst := dist_triangle (f n b x) (f n t x) (f m b x)
    have hrest := dist_triangle4 (f n t x) (g t x) (f m t x) (f m b x)
    linarith
  have hpoint : ∀ x : X, ∃ y : F,
      x ∈ K → Tendsto (fun n => f n b x) atTop (𝓝 y) := by
    intro x
    by_cases hx : x ∈ K
    · obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete (huc.cauchySeq hx)
      exact ⟨y, fun _ => hy⟩
    · exact ⟨0, fun hx' => False.elim (hx hx')⟩
  choose gEnd hgEnd using hpoint
  have hend : TendstoUniformlyOn (fun n => f n b) gEnd atTop K :=
    huc.tendstoUniformlyOn_of_tendsto hgEnd
  refine ⟨gEnd, hend, ?_⟩
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [eventually_mem_nhdsWithin, hmod.eventually_lt_const hε] with t ht hsmall x hx
  have hlim : dist (gEnd x) (g t x) ≤ C * (b - t) :=
    le_of_tendsto ((hend.tendsto_at hx).dist ((hconv t ht).tendsto_at hx))
      (Eventually.of_forall fun n => hnear n t ht x hx)
  exact hlim.trans_lt hsmall

end DifferentialGeometry.Analysis
