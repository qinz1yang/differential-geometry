import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.SequentialCompactness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardPositiveCurvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardMetricControl
import DifferentialGeometry.Geometry.Curvature.RicciRayleighOperator
import DifferentialGeometry.Geometry.Metric.Convergence.Curvature.RicciLowerBound
import DifferentialGeometry.Geometry.Metric.Convergence.Metric.Evaluation

set_option autoImplicit false
noncomputable section
open Set Filter Manifold
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff Topology ENNReal
namespace DifferentialGeometry.PDE.RicciFlow
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

theorem exists_uniform_positive_standard_tip_ricci_bound
    {T : ℝ} (hT : 0 ≤ T) (hTl : ENNReal.ofReal T < uniformStandardLifetime) :
    ∃ c : ℝ, 0 < c ∧ ∀ S : StandardSolution, ∀ t ∈ Set.Icc 0 T,
      ∀ v : TangentSpace (𝓡 3) (0 : E3),
        c * (S.val.metric t).inner 0 v v ≤ Geometry.Curvature.ricciTensor (S.val.metric t) 0 v v := by
  classical
  by_contra! hnot
  have hbad (n : ℕ) : ∃ S : StandardSolution, ∃ t ∈ Set.Icc 0 T,
      ∃ v : TangentSpace (𝓡 3) (0 : E3),
        Geometry.Curvature.ricciTensor (S.val.metric t) 0 v v <
          (1 / ((n : ℝ) + 1)) * (S.val.metric t).inner 0 v v :=
    hnot (1 / ((n : ℝ) + 1)) (by positivity)
  choose S t ht v hv using hbad
  obtain ⟨T', _, hTT'enn, hT'life⟩ := ENNReal.lt_iff_exists_real_btwn.mp hTl
  have hT' : 0 < T' := (ENNReal.ofReal_lt_ofReal_iff'.mp hTT'enn).2
  have hTT' : T < T' := (ENNReal.ofReal_lt_ofReal_iff hT').mp hTT'enn
  obtain ⟨rho, hrho, Q, hTQ, hconv⟩ :=
    exists_standard_solution_subsequence_on_shorter_interval S hT' hT'life
  obtain ⟨a, ha, σ, hσ, htime⟩ := isCompact_Icc.tendsto_subseq (fun i => ht (rho i))
  have hTQl : ENNReal.ofReal T < Q.val.lifetime :=
    (ENNReal.ofReal_lt_ofReal_iff hT').mpr hTT' |>.trans_le hTQ
  obtain ⟨c, hc, htip⟩ := Q.val.exists_pos_leastUpperRicciAt_tip_lower_bound hT hTQl
  obtain ⟨C, hC, hRm⟩ := Q.val.curvature_bound T hT hTQl
  obtain ⟨Λ, hΛ, A, L, hA, hL, hmetric⟩ := standard_metric_bounds_on_shorter_windows T C hT hC
  have htimeLip := (hmetric Q.val T hT le_rfl hTQl hRm).2.2
  let L' := ∑ q ∈ Finset.range 3, L q
  have hL' : 0 ≤ L' := Finset.sum_nonneg (fun q _ => hL q)
  have hcp : MetricCPConvergenceOn {(0 : E3)} 2
      (fun i => (S (rho (σ i))).val.metric (t (rho (σ i))))
      (Q.val.metric a) StandardCap.metric := by
    apply metricCPConvergenceOn_of_uniform_approximation_of_lipschitz
      (G := fun i r => (S (rho (σ i))).val.metric r) (g := Q.val.metric)
      StandardCap.metric isCompact_singleton hL' ?_ ?_ (Eventually.of_forall fun i => ht (rho (σ i))) ha htime
    · intro ε hε
      obtain ⟨N, hN⟩ := hconv {0} isCompact_singleton 2 ε hε
      exact ⟨N, fun i hi r hr => hN (σ i) (hi.trans (hσ.id_le i)) r ⟨hr.1, hr.2.trans_lt hTT'⟩⟩
    · intro s hs r hr q hq x _
      have hqL : L q ≤ L' := Finset.single_le_sum (fun n _ => hL n)
        (Finset.mem_range.mpr (by omega))
      exact (htimeLip q s hs r hr x).trans
        (by rw [Real.dist_eq]; exact mul_le_mul_of_nonneg_right hqL (abs_nonneg _))
  have hRic : ∀ x ∈ ({0} : Set E3), ∀ w : TangentSpace (𝓡 3) x,
      (2 * c) * (Q.val.metric a).inner x w w ≤ ricciTensor (Q.val.metric a) x w w := by
    intro x hx w
    obtain rfl := mem_singleton_iff.mp hx
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (htip a ha) (by norm_num))
      (metric_inner_self_nonneg (Q.val.metric a) 0 w)).trans
      (two_mul_leastUpperRicciAt_mul_inner_le_ricciTensor (Q.val.metric a) 0 w)
  have hpos := hcp.eventually_ricciTensor_lower_bound isCompact_singleton
    (by positivity : 0 < 2 * c) hRic
  have hinv : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) := by
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hsmall := ((hinv.comp (hrho.comp hσ).tendsto_atTop).eventually (gt_mem_nhds hc))
  obtain ⟨i, hi, hci⟩ := (hpos.and hsmall).exists
  have hlow := hi 0 (mem_singleton 0) (v (rho (σ i)))
  have hfail := hv (rho (σ i))
  have hne : v (rho (σ i)) ≠ 0 := by
    intro heq
    simp only [heq, map_zero, mul_zero, lt_self_iff_false] at hfail
  have hnorm := ((S (rho (σ i))).val.metric (t (rho (σ i)))).pos 0 _ hne
  have hstrict := mul_lt_mul_of_pos_right hci hnorm
  have hhalf : 2 * c / 2 = c := by ring
  rw [hhalf] at hlow
  exact (not_lt_of_ge hlow) (hfail.trans hstrict)

end DifferentialGeometry.PDE.RicciFlow
