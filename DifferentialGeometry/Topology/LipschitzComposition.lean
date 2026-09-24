import Mathlib.Topology.MetricSpace.Lipschitz

noncomputable section

open Filter Set
open scoped Topology ENNReal NNReal

variable {E M T F : Type*} [PseudoMetricSpace E] [PseudoEMetricSpace M]
  [PseudoMetricSpace T] [PseudoMetricSpace F]

theorem locallyLipschitzOn_comp_prod_of_edist_bound
    {ψ : E → M} {s : Set E} {K : Set M} {J : Set T} {f : M × T → F}
    (hψ : LocallyLipschitzOn s ψ) (hψK : MapsTo ψ s K)
    {C D r : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) (hr : 0 < r)
    (hf : ∀ x ∈ K, ∀ y ∈ K, ∀ a ∈ J, ∀ b ∈ J,
      edist x y < ENNReal.ofReal r →
      dist (f (x, a)) (f (y, b)) ≤ C * (edist x y).toReal + D * dist a b) :
    LocallyLipschitzOn (s ×ˢ J) (fun z : E × T => f (ψ z.1, z.2)) := by
  rintro ⟨x, a⟩ ⟨hx, _⟩
  obtain ⟨L, V, hV, hLV⟩ := hψ hx
  let W : Set E := (V ∩ s) ∩ ψ ⁻¹' Metric.eball (ψ x) (ENNReal.ofReal (r / 2))
  have hW : W ∈ 𝓝[s] x := by
    apply inter_mem (inter_mem hV self_mem_nhdsWithin)
    exact (hψ.continuousOn x hx).preimage_mem_nhdsWithin
      (Metric.eball_mem_nhds _ (ENNReal.ofReal_pos.mpr (half_pos hr)))
  have hnear {y z : E} (hy : y ∈ W) (hz : z ∈ W) :
      edist (ψ y) (ψ z) < ENNReal.ofReal r := by
    calc
      edist (ψ y) (ψ z) ≤ edist (ψ y) (ψ x) + edist (ψ x) (ψ z) :=
        edist_triangle _ _ _
      _ < ENNReal.ofReal (r / 2) + ENNReal.ofReal (r / 2) :=
        ENNReal.add_lt_add hy.2 (by
          simpa only [Set.mem_preimage, Metric.mem_eball, edist_comm] using hz.2)
      _ = ENNReal.ofReal r := by
        rw [← ENNReal.ofReal_add (half_pos hr).le (half_pos hr).le, add_halves]
  refine ⟨Real.toNNReal (C * L + D), W ×ˢ J,
    mem_nhdsWithin_prod_iff.mpr ⟨W, hW, J, self_mem_nhdsWithin, Subset.rfl⟩, ?_⟩
  apply LipschitzOnWith.of_dist_le_mul
  rintro ⟨y, b⟩ ⟨hy, hb⟩ ⟨z, c⟩ ⟨hz, hc⟩
  have hdist : (edist (ψ y) (ψ z)).toReal ≤ (L : ℝ) * dist y z := by
    have hfinite : (L : ℝ≥0∞) * edist y z ≠ ⊤ := by finiteness
    have h := ENNReal.toReal_mono hfinite (hLV hy.1.1 hz.1.1)
    simpa only [ENNReal.toReal_mul, ENNReal.coe_toReal, edist_dist,
      ENNReal.toReal_ofReal dist_nonneg] using h
  have hbound := hf (ψ y) (hψK hy.1.2) (ψ z) (hψK hz.1.2) b hb c hc (hnear hy hz)
  rw [Real.coe_toNNReal _ (add_nonneg (mul_nonneg hC L.coe_nonneg) hD)]
  calc
    dist (f (ψ y, b)) (f (ψ z, c)) ≤ C * ((L : ℝ) * dist y z) + D * dist b c :=
      hbound.trans (add_le_add (mul_le_mul_of_nonneg_left hdist hC) le_rfl)
    _ ≤ C * ((L : ℝ) * dist (y, b) (z, c)) + D * dist (y, b) (z, c) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (le_max_left _ _) L.coe_nonneg) hC
      · exact mul_le_mul_of_nonneg_left (le_max_right _ _) hD
    _ = (C * (L : ℝ) + D) * dist (y, b) (z, c) := by rw [add_mul, mul_assoc]
