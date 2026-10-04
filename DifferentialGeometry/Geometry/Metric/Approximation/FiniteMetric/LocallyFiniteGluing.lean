import DifferentialGeometry.Geometry.Metric.Approximation.FiniteMetric.Smoothing

/-!
# Gluing chart metrics along a locally finite smooth partition of unity

Lane CM-A (CM5.a). B7's `exists_smoothMetric_glued` glues finitely many chart metrics; on a
σ-compact manifold the partition of unity is only locally finite, so the glued form is a
`finsum`. This file gives the `finsum` gluing and the pointwise chart formulas: at a point where
only the indices of a finset `s` carry weight, the chart coefficients of the glued metric (and of
any finite-regularity metric) are the finite sums of the transformed chart terms, exactly as in
B7's `chartCoeff_glued` / `chartCoeff_eq_sum_transition`.
-/

set_option autoImplicit false

open Bundle Manifold Set Filter Function
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Geometry.MetricSmoothing

open DifferentialGeometry.CheegerGromovCompactness (pullbackForm pullbackForm_apply)

section Gluing

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] {ι : Type*}

omit [FiniteDimensional ℝ E] in
/-- Evaluation of a finitely supported `finsum` of bilinear forms. -/
theorem finsum_bilin_apply {F : ι → E →L[ℝ] E →L[ℝ] ℝ} (hF : (support F).Finite) (v w : E) :
    (∑ᶠ i, F i) v w = ∑ᶠ i, F i v w := by
  classical
  have hsub : support (fun i => F i v w) ⊆ hF.toFinset := by
    intro i hi
    rw [Finite.coe_toFinset]
    intro h0
    exact hi (by simp [h0])
  rw [finsum_eq_sum_of_support_subset F (s := hF.toFinset) (by rw [Finite.coe_toFinset]),
    finsum_eq_sum_of_support_subset _ hsub, _root_.sum_apply, _root_.sum_apply]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] in
/-- A smooth partition of unity of `univ` has some positive weight at every point. -/
theorem exists_partition_ne_zero (ρ : SmoothPartitionOfUnity ι I M univ) (x : M) :
    ∃ i, ρ i x ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have h := ρ.sum_eq_one (mem_univ x)
  rw [finsum_eq_zero_of_forall_eq_zero hcon] at h
  exact zero_ne_one h

/-- **Locally finite gluing.** Smooth symmetric positive bilinear fields on the model space, pulled
back by the charts at the points `c i` and glued by a (locally finite) smooth partition of unity
subordinate to the chart sources, form a smooth Riemannian metric. -/
theorem exists_smoothMetric_glued_finsum (c : ι → M) (ρ : SmoothPartitionOfUnity ι I M univ)
    (hρ : ρ.IsSubordinate fun i => (extChartAt I (c i)).source)
    (G : ι → E → E →L[ℝ] E →L[ℝ] ℝ) (hG : ∀ i, ContDiff ℝ ∞ (G i))
    (hsymm : ∀ i y v w, G i y v w = G i y w v) (hpos : ∀ i y (v : E), v ≠ 0 → 0 < G i y v v) :
    ∃ h : SmoothRiemannianMetric I M, ∀ x (v w : TangentSpace I x),
      h.inner x v w = ∑ᶠ i, ρ i x * G i (extChartAt I (c i) x)
        (mfderiv I 𝓘(ℝ, E) (extChartAt I (c i)) x v)
        (mfderiv I 𝓘(ℝ, E) (extChartAt I (c i)) x w) := by
  classical
  let gm : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ := fun x =>
    (∑ᶠ i, ρ i x • chartPullbackForm (I := I) (c i) (G i) x : E →L[ℝ] E →L[ℝ] ℝ)
  have hfin : ∀ x : M, (support fun i => ρ i x).Finite := fun x =>
    (ρ.locallyFinite.point_finite x).subset fun i hi => hi
  have happ : ∀ (x : M) (v w : TangentSpace I x), gm x v w = ∑ᶠ i, ρ i x * G i
      (extChartAt I (c i) x) (mfderiv I 𝓘(ℝ, E) (extChartAt I (c i)) x v)
      (mfderiv I 𝓘(ℝ, E) (extChartAt I (c i)) x w) := by
    intro x v w
    have hF : (support fun i => ρ i x • chartPullbackForm (I := I) (c i) (G i) x).Finite :=
      (hfin x).subset fun i hi =>
        mem_support.mpr fun h0 => (mem_support.mp hi) (by simp only [h0, zero_smul])
    exact (finsum_bilin_apply hF (show E from v) (show E from w)).trans
      (finsum_congr fun i => rfl)
  have hnn : ∀ i y (v : E), 0 ≤ G i y v v := by
    intro i y v
    by_cases hv : v = 0
    · simp [hv]
    · exact (hpos i y v hv).le
  have hgsymm : ∀ (x : M) (v w : TangentSpace I x), gm x v w = gm x w v := by
    intro x v w
    rw [happ, happ]
    exact finsum_congr fun i => congrArg (ρ i x * ·) (hsymm i _ _ _)
  have hgpos : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < gm x v v := by
    intro x v hv
    rw [happ]
    obtain ⟨i, hi⟩ := exists_partition_ne_zero ρ x
    have hipos : 0 < ρ i x := lt_of_le_of_ne (ρ.nonneg i x) (Ne.symm hi)
    have hxs : x ∈ (extChartAt I (c i)).source :=
      hρ i (subset_tsupport _ (mem_support.mpr hi))
    have hterm : 0 < ρ i x * G i (extChartAt I (c i) x)
        (mfderiv I 𝓘(ℝ, E) (extChartAt I (c i)) x v)
        (mfderiv I 𝓘(ℝ, E) (extChartAt I (c i)) x v) := by
      refine mul_pos hipos (hpos i _ _ ?_)
      intro h0
      exact hv (injective_mfderiv_extChartAt (I := I) (c i) hxs (h0.trans (map_zero _).symm))
    have hsub : (support fun j => ρ j x * G j (extChartAt I (c j) x)
        (mfderiv I 𝓘(ℝ, E) (extChartAt I (c j)) x v)
        (mfderiv I 𝓘(ℝ, E) (extChartAt I (c j)) x v)) ⊆ (hfin x).toFinset := by
      intro j hj
      rw [Finite.coe_toFinset]
      exact support_mul_subset_left _ _ hj
    rw [finsum_eq_sum_of_support_subset _ hsub]
    refine Finset.sum_pos' (fun j _ => mul_nonneg (ρ.nonneg j x) (hnn j _ _)) ⟨i, ?_, hterm⟩
    rw [Finite.mem_toFinset]
    exact hi
  have hcoeff : ∀ x₀ : M, ∀ k l : Fin (Module.finrank ℝ E),
      ContMDiffOn I 𝓘(ℝ) ∞
        (fun x => gm x (DifferentialGeometry.Geometry.frameVec (I := I) x₀ k x)
          (DifferentialGeometry.Geometry.frameVec (I := I) x₀ l x))
        (trivializationAt E (TangentSpace I) x₀).baseSet := by
    intro x₀ k l x hx
    have hsum : (fun x => gm x (DifferentialGeometry.Geometry.frameVec (I := I) x₀ k x)
          (DifferentialGeometry.Geometry.frameVec (I := I) x₀ l x)) =
        fun x => ∑ᶠ i, ρ i x * chartPullbackForm (I := I) (c i) (G i) x
          (DifferentialGeometry.Geometry.frameVec (I := I) x₀ k x)
          (DifferentialGeometry.Geometry.frameVec (I := I) x₀ l x) := by
      funext x
      exact happ x _ _
    rw [hsum]
    have hbase : (trivializationAt E (TangentSpace I) x₀).baseSet ∈ 𝓝 x :=
      (trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds hx
    refine (_root_.contMDiffAt_finsum (ρ.locallyFinite.subset fun i =>
      support_mul_subset_left _ _) fun i => ?_).contMDiffWithinAt
    exact (contMDiffOn_chartPullbackForm_coeff (c i) (hG i) (ρ i).contMDiff (hρ i) x₀ k l).contMDiffAt
      hbase
  obtain ⟨h, hh⟩ := DifferentialGeometry.Geometry.smoothMetric_of_localCoeff gm hgsymm hgpos hcoeff
  exact ⟨h, fun x v w => (hh x v w).trans (happ x v w)⟩

end Gluing

section ChartSums

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {ι : Type*}

/-- Pointwise chart formula for a glued metric: if at `x = φ_q⁻¹ y` the metric is the finite sum
over `s` of the chart terms, its chart coefficients at `y` are the finite sum of the transformed
terms. -/
theorem chartCoeff_eq_finset_sum_of_inner (s : Finset ι) (c : ι → M) (ρ : ι → M → ℝ)
    (hρ : ∀ i, tsupport (ρ i) ⊆ (extChartAt I (c i)).source)
    (G : ι → E → E →L[ℝ] E →L[ℝ] ℝ) (h : SmoothRiemannianMetric I M) (q : M) {y : E}
    (hy : y ∈ (extChartAt I q).target)
    (hh : ∀ v w : TangentSpace I ((extChartAt I q).symm y),
      h.inner ((extChartAt I q).symm y) v w = ∑ i ∈ s, ρ i ((extChartAt I q).symm y) *
        G i (extChartAt I (c i) ((extChartAt I q).symm y))
          (mfderiv I 𝓘(ℝ, E) (extChartAt I (c i)) ((extChartAt I q).symm y) v)
          (mfderiv I 𝓘(ℝ, E) (extChartAt I (c i)) ((extChartAt I q).symm y) w)) :
    chartCoeff h q y = ∑ i ∈ s, ρ i ((extChartAt I q).symm y) •
      pullbackForm (G i (chartTransition (I := I) (c i) q y),
        fderiv ℝ (chartTransition (I := I) (c i) q) y) := by
  ext v w
  rw [chartCoeff_apply, hh, _root_.sum_apply, _root_.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [_root_.smul_apply, _root_.smul_apply, smul_eq_mul, pullbackForm_apply]
  by_cases hi : ρ i ((extChartAt I q).symm y) = 0
  · rw [hi, zero_mul, zero_mul]
  · have hxs : (extChartAt I q).symm y ∈ (extChartAt I (c i)).source :=
      hρ i (subset_tsupport _ (mem_support.mpr hi))
    have hc := mfderiv_extChartAt_comp_symm (I := I) (c i) q ⟨hy, hxs⟩
    have hv : (mfderiv I 𝓘(ℝ, E) (extChartAt I (c i)) ((extChartAt I q).symm y) : E →L[ℝ] E)
        ((mfderiv 𝓘(ℝ, E) I (extChartAt I q).symm y : E →L[ℝ] E) v) =
        fderiv ℝ (chartTransition (I := I) (c i) q) y v := congrArg (fun L => L v) hc
    have hw : (mfderiv I 𝓘(ℝ, E) (extChartAt I (c i)) ((extChartAt I q).symm y) : E →L[ℝ] E)
        ((mfderiv 𝓘(ℝ, E) I (extChartAt I q).symm y : E →L[ℝ] E) w) =
        fderiv ℝ (chartTransition (I := I) (c i) q) y w := congrArg (fun L => L w) hc
    rw [hv, hw]
    rfl

/-- Pointwise chart formula for a finite-regularity metric: if the weights at `x = φ_q⁻¹ y` of
the indices in `s` sum to one, the chart coefficients at `y` are the finite sum of the transformed
chart coefficients. -/
theorem chartCoeff_eq_finset_sum_transition {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (s : Finset ι)
    (c : ι → M) (ρ : ι → M → ℝ) (hρ : ∀ i, tsupport (ρ i) ⊆ (extChartAt I (c i)).source)
    (q : M) {y : E} (hy : y ∈ (extChartAt I q).target)
    (hsum : ∑ i ∈ s, ρ i ((extChartAt I q).symm y) = 1) :
    chartCoeff g q y = ∑ i ∈ s, ρ i ((extChartAt I q).symm y) •
      pullbackForm (chartCoeff g (c i) (chartTransition (I := I) (c i) q y),
        fderiv ℝ (chartTransition (I := I) (c i) q) y) := by
  ext v w
  rw [_root_.sum_apply, _root_.sum_apply]
  simp only [_root_.smul_apply, smul_eq_mul]
  calc chartCoeff g q y v w
      = (∑ i ∈ s, ρ i ((extChartAt I q).symm y)) * chartCoeff g q y v w := by
        rw [hsum, one_mul]
    _ = ∑ i ∈ s, ρ i ((extChartAt I q).symm y) * chartCoeff g q y v w := Finset.sum_mul _ _ _
    _ = _ := by
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hi : ρ i ((extChartAt I q).symm y) = 0
      · rw [hi, zero_mul, zero_mul]
      · have hxs : (extChartAt I q).symm y ∈ (extChartAt I (c i)).source :=
          hρ i (subset_tsupport _ (mem_support.mpr hi))
        rw [chartCoeff_transition g (c i) q ⟨hy, hxs⟩]

end ChartSums

end DifferentialGeometry.Geometry.MetricSmoothing
