import DifferentialGeometry.Geometry.Measure.Area.LeastAreaComposition
import DifferentialGeometry.Geometry.Measure.Area.RegularLeastArea



noncomputable section

open Set Function ContinuousMap Manifold DifferentialGeometry
open DifferentialGeometry.Topology
open scoped Topology ContDiff Manifold ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]



theorem metric_upper_lipschitz (g h : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {c : ℝ} (hc : 0 < c)
    (hgh : ∀ (x : M) (v : TangentSpace 𝓘(ℝ, E) x), h.inner x v v ≤ c * g.inner x v v)
    (x y : M) : riemannianEDistOf h x y ≤
      ENNReal.ofNNReal ⟨Real.sqrt c, Real.sqrt_nonneg c⟩ * riemannianEDistOf g x y := by
  simpa only [ENNReal.ofReal_eq_coe_nnreal (Real.sqrt_nonneg c)] using!
    edistOf_le_of_quad g h hc hgh x y

variable [FiniteDimensional ℝ E] [CompactSpace M] [T3Space M]

omit [FiniteDimensional ℝ E] [CompactSpace M] [T3Space M] in
theorem spanningDiskCompetitors_subset_of_metric_upper
    (g h : SmoothRiemannianMetric 𝓘(ℝ, E) M) {c : ℝ} (hc : 0 < c)
    (hgh : ∀ (x : M) (v : TangentSpace 𝓘(ℝ, E) x), h.inner x v v ≤ c * g.inner x v v)
    (γ : freeLoop M) : spanningDiskCompetitors g γ ⊆ spanningDiskCompetitors h γ := by
  rintro u ⟨ht, C, hC⟩
  let B : ℝ≥0 := ⟨Real.sqrt c, Real.sqrt_nonneg c⟩
  refine ⟨ht, B * C, ?_⟩
  simpa only [Function.comp_def, id_eq] using!
    riemannian_lipschitz_comp g h (f := id) (L := B) hC (metric_upper_lipschitz g h hc hgh)

omit [FiniteDimensional ℝ E] [CompactSpace M] [T3Space M] in
theorem metric_lower_inverse_upper
    (g h : SmoothRiemannianMetric 𝓘(ℝ, E) M) {c : ℝ} (hc : 0 < c)
    (hgh : ∀ (x : M) (v : TangentSpace 𝓘(ℝ, E) x), c * g.inner x v v ≤ h.inner x v v)
    (x : M) (v : TangentSpace 𝓘(ℝ, E) x) : g.inner x v v ≤ c⁻¹ * h.inner x v v := by
  rw [← div_eq_inv_mul]
  exact (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hgh x v)

omit [FiniteDimensional ℝ E] [CompactSpace M] [T3Space M] in
theorem spanningDiskCompetitors_eq_of_metric_bounds
    (g h : SmoothRiemannianMetric 𝓘(ℝ, E) M) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hlo : ∀ (x : M) (v : TangentSpace 𝓘(ℝ, E) x), a ^ 2 * g.inner x v v ≤ h.inner x v v)
    (hhi : ∀ (x : M) (v : TangentSpace 𝓘(ℝ, E) x), h.inner x v v ≤ b ^ 2 * g.inner x v v)
    (γ : freeLoop M) : spanningDiskCompetitors g γ = spanningDiskCompetitors h γ :=
  Subset.antisymm (spanningDiskCompetitors_subset_of_metric_upper g h (sq_pos_of_pos hb) hhi γ)
    (spanningDiskCompetitors_subset_of_metric_upper h g (inv_pos.mpr (sq_pos_of_pos ha))
      (metric_lower_inverse_upper g h (sq_pos_of_pos ha) hlo) γ)

variable [Nonempty M] [PreconnectedSpace M]



theorem leastSpanningArea_metric_upper
    (g h : SmoothRiemannianMetric 𝓘(ℝ, E) M) {c : ℝ} (hc : 0 < c)
    (hgh : ∀ (x : M) (v : TangentSpace 𝓘(ℝ, E) x), h.inner x v v ≤ c * g.inner x v v)
    (γ : lipschitzContractibleLoop g) (δ : lipschitzContractibleLoop h)
    (htrace : γ.val = δ.val) : leastSpanningArea h δ ≤ c * leastSpanningArea g γ := by
  have hb := leastSpanningArea_postcompose_le g h id (metric_upper_lipschitz g h hc hgh) γ
  have heq : postcomposeLipschitzContractibleLoop g h id (metric_upper_lipschitz g h hc hgh) γ = δ := by
    apply Subtype.ext
    exact htrace
  rw [heq] at hb
  change leastSpanningArea h δ ≤ (Real.sqrt c) ^ 2 * leastSpanningArea g γ at hb
  simpa only [Real.sq_sqrt hc.le] using hb



theorem leastSpanningArea_metric_bounds
    (g h : SmoothRiemannianMetric 𝓘(ℝ, E) M) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hlo : ∀ (x : M) (v : TangentSpace 𝓘(ℝ, E) x), a ^ 2 * g.inner x v v ≤ h.inner x v v)
    (hhi : ∀ (x : M) (v : TangentSpace 𝓘(ℝ, E) x), h.inner x v v ≤ b ^ 2 * g.inner x v v)
    (γ : lipschitzContractibleLoop g) (δ : lipschitzContractibleLoop h)
    (htrace : γ.val = δ.val) :
    a ^ 2 * leastSpanningArea g γ ≤ leastSpanningArea h δ ∧
      leastSpanningArea h δ ≤ b ^ 2 * leastSpanningArea g γ := by
  refine ⟨?_, leastSpanningArea_metric_upper g h (sq_pos_of_pos hb) hhi γ δ htrace⟩
  have hl := leastSpanningArea_metric_upper h g (inv_pos.mpr (sq_pos_of_pos ha))
    (metric_lower_inverse_upper g h (sq_pos_of_pos ha) hlo) δ γ htrace.symm
  rw [← div_eq_inv_mul] at hl
  simpa only [mul_comm] using (le_div_iff₀ (sq_pos_of_pos ha)).mp hl


theorem leastSpanningArea_scale (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (c : ℝ) (hc : 0 < c) (γ : lipschitzContractibleLoop g)
    (δ : lipschitzContractibleLoop (scaleMetric c hc g)) (htrace : γ.val = δ.val) :
    leastSpanningArea (scaleMetric c hc g) δ = c * leastSpanningArea g γ := by
  obtain ⟨hl, hu⟩ := leastSpanningArea_metric_bounds g (scaleMetric c hc g)
    (Real.sqrt_pos.mpr hc) (Real.sqrt_pos.mpr hc)
    (fun x v => by simp only [Real.sq_sqrt hc.le, scaleMetric_inner, le_refl])
    (fun x v => by simp only [Real.sq_sqrt hc.le, scaleMetric_inner, le_refl]) γ δ htrace
  rw [Real.sq_sqrt hc.le] at hl hu
  exact le_antisymm hu hl



theorem regularLeastArea_metric_upper
    (g h : SmoothRiemannianMetric 𝓘(ℝ, E) M) {c : ℝ} (hc : 0 < c)
    (hgh : ∀ (x : M) (v : TangentSpace 𝓘(ℝ, E) x), h.inner x v v ≤ c * g.inner x v v)
    (γ : regularContractibleLoop E M) : regularLeastArea h γ ≤ c * regularLeastArea g γ := by
  have hb := leastSpanningArea_postcompose_le g h id (metric_upper_lipschitz g h hc hgh)
    (regularContractibleToLipschitz g γ)
  have heq : postcomposeLipschitzContractibleLoop g h id (metric_upper_lipschitz g h hc hgh)
      (regularContractibleToLipschitz g γ) = regularContractibleToLipschitz h γ := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  rw [heq] at hb
  change regularLeastArea h γ ≤ (Real.sqrt c) ^ 2 * regularLeastArea g γ at hb
  simpa only [Real.sq_sqrt hc.le] using hb


theorem regularLeastArea_metric_bounds
    (g h : SmoothRiemannianMetric 𝓘(ℝ, E) M) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hlo : ∀ (x : M) (v : TangentSpace 𝓘(ℝ, E) x), a ^ 2 * g.inner x v v ≤ h.inner x v v)
    (hhi : ∀ (x : M) (v : TangentSpace 𝓘(ℝ, E) x), h.inner x v v ≤ b ^ 2 * g.inner x v v)
    (γ : regularContractibleLoop E M) :
    a ^ 2 * regularLeastArea g γ ≤ regularLeastArea h γ ∧
      regularLeastArea h γ ≤ b ^ 2 * regularLeastArea g γ := by
  refine ⟨?_, regularLeastArea_metric_upper g h (sq_pos_of_pos hb) hhi γ⟩
  have hl := regularLeastArea_metric_upper h g (inv_pos.mpr (sq_pos_of_pos ha))
    (metric_lower_inverse_upper g h (sq_pos_of_pos ha) hlo) γ
  rw [← div_eq_inv_mul] at hl
  simpa only [mul_comm] using (le_div_iff₀ (sq_pos_of_pos ha)).mp hl


theorem regularLeastArea_scale (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (c : ℝ) (hc : 0 < c) (γ : regularContractibleLoop E M) :
    regularLeastArea (scaleMetric c hc g) γ = c * regularLeastArea g γ := by
  obtain ⟨hl, hu⟩ := regularLeastArea_metric_bounds g (scaleMetric c hc g)
    (Real.sqrt_pos.mpr hc) (Real.sqrt_pos.mpr hc)
    (fun x v => by simp only [Real.sq_sqrt hc.le, scaleMetric_inner, le_refl])
    (fun x v => by simp only [Real.sq_sqrt hc.le, scaleMetric_inner, le_refl]) γ
  rw [Real.sq_sqrt hc.le] at hl hu
  exact le_antisymm hu hl

end DifferentialGeometry.Geometry
