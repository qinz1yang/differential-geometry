import DifferentialGeometry.Analysis.Integration.Lp.SpatialDerivative
import Mathlib.Topology.Compactness.Compact


noncomputable section

namespace DifferentialGeometry.Analysis.Calculus

open Filter Set
open scoped NNReal ENNReal Topology

variable {ι E M F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [PseudoEMetricSpace M] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem exists_norm_fderiv_comp_inl_le_of_edist_bound
    {ψ : E → M} {W K : Set E} {D : Set M} {J : Set F}
    (hW : IsOpen W) (hK : IsCompact K) (hKW : K ⊆ W)
    (hψ : LocallyLipschitzOn W ψ) (hψD : MapsTo ψ W D)
    (f : ι → M × F → G) {C r : ℝ} (hC : 0 ≤ C) (hr : 0 < r)
    (hf : ∀ i, ∀ y ∈ D, ∀ z ∈ D, ∀ t ∈ J,
      edist y z < ENNReal.ofReal r →
      dist (f i (y, t)) (f i (z, t)) ≤ C * (edist y z).toReal) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ i, ∀ x ∈ K, ∀ t ∈ J,
      ‖(fderiv ℝ (fun z : E × F => f i (ψ z.1, z.2)) (x, t)).comp
        (ContinuousLinearMap.inl ℝ E F)‖ ≤ B := by
  classical
  have hlocal (x : K) : ∃ L : ℝ≥0, ∃ V : Set E,
      IsOpen V ∧ x.1 ∈ V ∧ ∀ i, ∀ t ∈ J,
        LipschitzOnWith L (fun y => f i (ψ y, t)) V := by
    obtain ⟨L, A, hA, hLA⟩ := hψ (hKW x.2)
    have hAn : A ∈ 𝓝 x.1 := by
      rwa [hW.nhdsWithin_eq (hKW x.2)] at hA
    have hcont : ContinuousAt ψ x.1 :=
      (hψ.continuousOn x.1 (hKW x.2)).continuousAt (hW.mem_nhds (hKW x.2))
    have hpre : ψ ⁻¹' Metric.eball (ψ x.1) (ENNReal.ofReal (r / 2)) ∈ 𝓝 x.1 :=
      hcont.preimage_mem_nhds
        (Metric.eball_mem_nhds _ (ENNReal.ofReal_pos.mpr (by positivity)))
    obtain ⟨V, hVsub, hVopen, hxV⟩ := mem_nhds_iff.mp
      (inter_mem (inter_mem hAn (hW.mem_nhds (hKW x.2))) hpre)
    refine ⟨Real.toNNReal (C * L), V, hVopen, hxV, ?_⟩
    intro i t ht
    apply LipschitzOnWith.of_dist_le_mul
    intro y hy z hz
    have hy' := hVsub hy
    have hz' := hVsub hz
    have hnear : edist (ψ y) (ψ z) < ENNReal.ofReal r := by
      calc
        edist (ψ y) (ψ z) ≤ edist (ψ y) (ψ x.1) + edist (ψ x.1) (ψ z) :=
          edist_triangle _ _ _
        _ < ENNReal.ofReal (r / 2) + ENNReal.ofReal (r / 2) :=
          ENNReal.add_lt_add hy'.2 (by
            have hzball : edist (ψ z) (ψ x.1) < ENNReal.ofReal (r / 2) := hz'.2
            simpa only [edist_comm] using hzball)
        _ = ENNReal.ofReal r := by
          rw [← ENNReal.ofReal_add (half_pos hr).le (half_pos hr).le]
          congr 1
          ring
    have hdist : (edist (ψ y) (ψ z)).toReal ≤ (L : ℝ) * dist y z := by
      have hfin : (L : ℝ≥0∞) * edist y z ≠ ⊤ := by finiteness
      have h := ENNReal.toReal_mono hfin (hLA hy'.1.1 hz'.1.1)
      simpa only [ENNReal.toReal_mul, ENNReal.coe_toReal, edist_dist,
        ENNReal.toReal_ofReal dist_nonneg] using h
    rw [Real.coe_toNNReal _ (mul_nonneg hC L.coe_nonneg)]
    exact (hf i (ψ y) (hψD hy'.1.2) (ψ z) (hψD hz'.1.2) t ht hnear).trans
      ((mul_le_mul_of_nonneg_left hdist hC).trans_eq (mul_assoc _ _ _).symm)
  choose L V hVopen hxV hLV using hlocal
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover V hVopen (by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩)
  refine ⟨∑ z ∈ s, (L z : ℝ), Finset.sum_nonneg (fun z _ => (L z).coe_nonneg), ?_⟩
  intro i x hx t ht
  obtain ⟨z, hz, hxz⟩ := mem_iUnion₂.mp (hs hx)
  exact (norm_fderiv_comp_inl_le_of_lipschitzOn
    (fun z : E × F => f i (ψ z.1, z.2)) (x, t)
    ((hVopen z).mem_nhds hxz) (hLV z i t ht)).trans
      (Finset.single_le_sum (fun z _ => (L z).coe_nonneg) hz)

end DifferentialGeometry.Analysis.Calculus
