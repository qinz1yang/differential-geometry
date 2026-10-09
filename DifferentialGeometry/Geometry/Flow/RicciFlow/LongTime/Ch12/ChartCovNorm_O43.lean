import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ChartCovModel_O35
import DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetricContinuity
import DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetricIneq

/-!
# CH12-O43 chartCov-N / N' and the consumer forms of chartCov

On a compact set `K` of the chart target at `c`, the fibre norm `tensor0SFiberNorm g` and the
model norm of `tensor0SModelAt s c` are uniformly equivalent (`chartCovNorm_O43`,
`chartCovNormRev_O43`).  Combined with O35's chartCov-A / A' this gives the consumer forms
`chartCov_O43` (coordinate jets ≤ covariant fibre norms) and `chartCovRev_O43` (covariant fibre
norms ≤ coordinate jets, with a constant uniform in the open set `W` where `T` is smooth).
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Tensor.RSTensor DifferentialGeometry.TensorLieDeriv Bundle Set Filter Metric
open scoped Manifold ContDiff Topology

namespace GC.LongTime.Ch12

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [I.Boundaryless] in
theorem fiberNorm_smul_O43 (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ) (t : ℝ)
    (A : Tensor0SSpace s I x) :
    tensor0SFiberNorm g x s (t • A) = |t| * tensor0SFiberNorm g x s A := by
  unfold tensor0SFiberNorm normSq0S
  rw [inner0S_smul_left, inner0S_smul_right, ← mul_assoc, ← sq, Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq_eq_abs]

omit [I.Boundaryless] in
/-- Two-sided comparison of the fibre norm with the model norm (trivialization at `c`) on a
compact chart set: continuity of the fibre norm in the trivialization + compactness of
`K × sphere`. -/
theorem chartFiberNorm_equiv_O43 (g : SmoothRiemannianMetric I M) (c : M) {K : Set E}
    (hK : IsCompact K) (hKt : K ⊆ (extChartAt I c).target) (s : ℕ) :
    ∃ m C : ℝ, 0 < m ∧ 0 ≤ C ∧ ∀ y ∈ K, ∀ A : Tensor0SSpace s I ((extChartAt I c).symm y),
      m * ‖tensor0SModelAt s c ((extChartAt I c).symm y) A‖ ≤
          tensor0SFiberNorm g ((extChartAt I c).symm y) s A ∧
        tensor0SFiberNorm g ((extChartAt I c).symm y) s A ≤
          C * ‖tensor0SModelAt s c ((extChartAt I c).symm y) A‖ := by
  let e := trivializationAt (Tensor0SModel s ℝ E) (fun p : M => Tensor0SSpace s I p) c
  have hbase : ∀ y ∈ (extChartAt I c).target, (extChartAt I c).symm y ∈ e.baseSet := by
    intro y hy
    change (extChartAt I c).symm y ∈
      (trivializationAt E (TangentSpace I : M → Type _) c).baseSet
    simpa only [TangentBundle.trivializationAt_baseSet, extChartAt_source] using
      (extChartAt I c).map_target hy
  have hmap : ContinuousOn (fun z : E × Tensor0SModel s ℝ E =>
      (TotalSpace.mk' (Tensor0SModel s ℝ E) ((extChartAt I c).symm z.1)
        (e.symm ((extChartAt I c).symm z.1) z.2) :
        TotalSpace (Tensor0SModel s ℝ E) (fun p : M => Tensor0SSpace s I p)))
      ((extChartAt I c).target ×ˢ univ) := by
    have h1 : ContinuousOn (fun z : E × Tensor0SModel s ℝ E => ((extChartAt I c).symm z.1, z.2))
        ((extChartAt I c).target ×ˢ univ) :=
      ((continuousOn_extChartAt_symm c).comp continuousOn_fst
        (fun z (hz : z ∈ (extChartAt I c).target ×ˢ univ) => hz.1)).prodMk continuousOn_snd
    refine e.continuousOn_symm.comp h1 ?_
    intro z (hz : z ∈ (extChartAt I c).target ×ˢ univ)
    exact ⟨hbase z.1 hz.1, mem_univ _⟩
  let f : E × Tensor0SModel s ℝ E → ℝ := fun z =>
    tensor0SFiberNorm g ((extChartAt I c).symm z.1) s (e.symm ((extChartAt I c).symm z.1) z.2)
  have hf : ContinuousOn f ((extChartAt I c).target ×ˢ univ) :=
    Real.continuous_sqrt.comp_continuousOn
      ((normSq0S_total_cont (I := I) (s := s) g).comp_continuousOn hmap)
  have hS : IsCompact (K ×ˢ sphere (0 : Tensor0SModel s ℝ E) 1) :=
    hK.prod (isCompact_sphere 0 1)
  have hSsub : K ×ˢ sphere (0 : Tensor0SModel s ℝ E) 1 ⊆ (extChartAt I c).target ×ˢ univ :=
    prod_mono hKt (subset_univ _)
  have hsy : ∀ (b : M) (hb : b ∈ e.baseSet) (v : Tensor0SModel s ℝ E),
      e.symm b v = (e.continuousLinearEquivAt ℝ b hb).symm v := by
    intro b hb v
    rw [e.symm_continuousLinearEquivAt_eq hb, e.symmL_apply hb]
  have hL : ∀ y (h : y ∈ (extChartAt I c).target), ∀ A : Tensor0SSpace s I ((extChartAt I c).symm y),
      e.continuousLinearEquivAt ℝ _ (hbase y h) A =
        tensor0SModelAt s c ((extChartAt I c).symm y) A := fun y h A => rfl
  have hpos : ∀ z ∈ K ×ˢ sphere (0 : Tensor0SModel s ℝ E) 1, 0 < f z := by
    intro z hz
    have hz2 : z.2 ≠ 0 := ne_zero_of_mem_unit_sphere ⟨z.2, hz.2⟩
    have hne : e.symm ((extChartAt I c).symm z.1) z.2 ≠ 0 := by
      rw [hsy _ (hbase z.1 (hKt hz.1))]
      intro h0
      have h1 := congrArg (e.continuousLinearEquivAt ℝ _ (hbase z.1 (hKt hz.1))) h0
      rw [ContinuousLinearEquiv.apply_symm_apply, map_zero] at h1
      exact hz2 h1
    have h0 := normSq0S_nonneg g ((extChartAt I c).symm z.1) s
      (e.symm ((extChartAt I c).symm z.1) z.2)
    have h1 : normSq0S g ((extChartAt I c).symm z.1) s
        (e.symm ((extChartAt I c).symm z.1) z.2) ≠ 0 :=
      fun h => hne ((normSq0S_eq_zero_iff g _ s _).1 h)
    exact Real.sqrt_pos.2 (lt_of_le_of_ne h0 (Ne.symm h1))
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn (hf.mono hSsub)
  obtain ⟨m, hm0, hm⟩ : ∃ m : ℝ, 0 < m ∧ ∀ z ∈ K ×ˢ sphere (0 : Tensor0SModel s ℝ E) 1,
      m ≤ f z := by
    rcases (K ×ˢ sphere (0 : Tensor0SModel s ℝ E) 1).eq_empty_or_nonempty with h | h
    · exact ⟨1, one_pos, fun z hz => by simp [h] at hz⟩
    · obtain ⟨z0, hz0, hmin⟩ := hS.exists_isMinOn h (hf.mono hSsub)
      exact ⟨f z0, hpos z0 hz0, fun z hz => hmin hz⟩
  refine ⟨m, max C 0, hm0, le_max_right _ _, fun y hy A => ?_⟩
  have hp := hbase y (hKt hy)
  set L := e.continuousLinearEquivAt ℝ _ hp with hLdef
  rw [← hL y (hKt hy) A]
  have hA : A = e.symm ((extChartAt I c).symm y) (L A) := by
    rw [hsy _ hp, hLdef]
    exact (ContinuousLinearEquiv.symm_apply_apply _ A).symm
  by_cases hα : L A = 0
  · have hA0 : A = 0 := by rw [hA, hα, hsy _ hp, map_zero]
    rw [hα, hA0, norm_zero, mul_zero, mul_zero]
    have : tensor0SFiberNorm g ((extChartAt I c).symm y) s 0 = 0 := by
      rw [show (0 : Tensor0SSpace s I ((extChartAt I c).symm y)) = (0 : ℝ) • 0 from
        (zero_smul ℝ _).symm, fiberNorm_smul_O43, abs_zero, zero_mul]
    exact ⟨this.ge, this.le⟩
  · set r := ‖L A‖ with hr
    have hr0 : 0 < r := norm_pos_iff.2 hα
    set u : Tensor0SModel s ℝ E := r⁻¹ • L A with hu
    have humem : ((y, u) : E × Tensor0SModel s ℝ E) ∈ K ×ˢ sphere (0 : Tensor0SModel s ℝ E) 1 := by
      refine ⟨hy, ?_⟩
      rw [mem_sphere_zero_iff_norm, hu, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hr0.ne']
    have hAu : A = r • e.symm ((extChartAt I c).symm y) u := by
      rw [hsy _ hp, ← map_smul, hu, smul_smul, mul_inv_cancel₀ hr0.ne', one_smul, ← hsy _ hp]
      exact hA
    have hfA : tensor0SFiberNorm g ((extChartAt I c).symm y) s A = r * f (y, u) := by
      rw [hAu, fiberNorm_smul_O43, abs_of_pos hr0]
    have hCu : f (y, u) ≤ C := by
      have := hC (y, u) humem
      rw [Real.norm_eq_abs] at this
      exact (le_abs_self _).trans this
    rw [hfA]
    constructor
    · rw [mul_comm m r]
      exact mul_le_mul_of_nonneg_left (hm _ humem) hr0.le
    · rw [mul_comm (max C 0) r]
      exact mul_le_mul_of_nonneg_left (hCu.trans (le_max_left _ _)) hr0.le

omit [I.Boundaryless] in
/-- **chartCov-N** ([FROZEN] CH12-O35 chartCov-N): model norm ≤ C · fibre norm. -/
theorem chartCovNorm_O43 (g : SmoothRiemannianMetric I M) (c : M) {K : Set E} (hK : IsCompact K)
    (hKt : K ⊆ (extChartAt I c).target) (s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, ∀ A : Tensor0SSpace s I ((extChartAt I c).symm y),
      ‖tensor0SModelAt s c ((extChartAt I c).symm y) A‖ ≤
        C * tensor0SFiberNorm g ((extChartAt I c).symm y) s A := by
  obtain ⟨m, C, hm, -, h⟩ := chartFiberNorm_equiv_O43 g c hK hKt s
  refine ⟨m⁻¹, inv_nonneg.2 hm.le, fun y hy A => ?_⟩
  rw [inv_mul_eq_div, le_div_iff₀ hm, mul_comm]
  exact (h y hy A).1

omit [I.Boundaryless] in
/-- **chartCov-N'** ([FROZEN] CH12-O35 chartCov addendum): fibre norm ≤ C · model norm. -/
theorem chartCovNormRev_O43 (g : SmoothRiemannianMetric I M) (c : M) {K : Set E}
    (hK : IsCompact K) (hKt : K ⊆ (extChartAt I c).target) (s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, ∀ A : Tensor0SSpace s I ((extChartAt I c).symm y),
      tensor0SFiberNorm g ((extChartAt I c).symm y) s A ≤
        C * ‖tensor0SModelAt s c ((extChartAt I c).symm y) A‖ := by
  obtain ⟨m, C, -, hC, h⟩ := chartFiberNorm_equiv_O43 g c hK hKt s
  exact ⟨C, hC, fun y hy A => (h y hy A).2⟩

variable [T2Space M]

/-- **chartCov** (consumer form A + N, [FROZEN] CH12-O35 chartCov): coordinate jets of the model
representative ≤ C · Σ covariant fibre norms. -/
theorem chartCov_O43 (g : SmoothRiemannianMetric I M) (c : M) {W : Set M} (hW : IsOpen W)
    {K : Set E} (hK : IsCompact K)
    (hKW : K ⊆ (extChartAt I c).target ∩ (extChartAt I c).symm ⁻¹' W) (s k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : (p : M) → Tensor0SSpace s I p,
      ContMDiffOn I (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) ∞
        (fun p => (⟨p, T p⟩ : TotalSpace (Tensor0SModel s ℝ E)
          (fun q => Tensor0SSpace s I q))) W →
      ∀ y ∈ K, ∀ k' ≤ k, ‖iteratedFDeriv ℝ k' (tensor0SModelInChart s c T) y‖ ≤
        C * ∑ i ∈ Finset.range (k + 1), tensor0SFiberNorm g ((extChartAt I c).symm y) (s + i)
          (iteratedMetricCovariantDerivative g s T i ((extChartAt I c).symm y)) := by
  obtain ⟨CA, hCA, hA⟩ := chartCovModel_O35 g c hW hK hKW s k
  have hKt : K ⊆ (extChartAt I c).target := fun y hy => (hKW hy).1
  choose CN hCN hN using fun i : ℕ => chartCovNorm_O43 g c hK hKt (s + i)
  set B := ∑ i ∈ Finset.range (k + 1), CN i with hB
  have hB0 : 0 ≤ B := Finset.sum_nonneg (fun i _ => hCN i)
  refine ⟨CA * B, mul_nonneg hCA hB0, fun T hT y hy k' hk' => ?_⟩
  refine (hA T hT y hy k' hk').trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hCA
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun i hi => ?_)
  have hfib : 0 ≤ tensor0SFiberNorm g ((extChartAt I c).symm y) (s + i)
      (iteratedMetricCovariantDerivative g s T i ((extChartAt I c).symm y)) := Real.sqrt_nonneg _
  have hCi : CN i ≤ B := Finset.single_le_sum (fun i _ => hCN i) hi
  exact (hN i y hy _).trans (mul_le_mul_of_nonneg_right hCi hfib)

/-- chartCov-A' with a constant uniform in the open set `W` (induction of
`chartCovModelRev_within_O35` with `W` quantified after `C`; all derivatives are global since
`target ∩ symm⁻¹ W` is open). -/
theorem chartCovModelRevUnif_iter_O43 (g : SmoothRiemannianMetric I M) (c : M) {K : Set E}
    (hK : IsCompact K) (hKt : K ⊆ (extChartAt I c).target) (s j : ℕ) :
    ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ W : Set M, IsOpen W → K ⊆ (extChartAt I c).symm ⁻¹' W →
      ∀ T : (p : M) → Tensor0SSpace s I p,
      ContMDiffOn I (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) ∞
        (fun p => (⟨p, T p⟩ : TotalSpace (Tensor0SModel s ℝ E)
          (fun q => Tensor0SSpace s I q))) W →
      ∀ y ∈ K,
        ‖iteratedFDeriv ℝ k (tensor0SModelInChart (s + j) c
          (iteratedMetricCovariantDerivative g s T j)) y‖ ≤
        C * ∑ i ∈ Finset.range (j + k + 1), ‖iteratedFDeriv ℝ i
          (tensor0SModelInChart (s + 0) c (iteratedMetricCovariantDerivative g s T 0)) y‖ := by
  induction j with
  | zero =>
    intro k
    refine ⟨1, zero_le_one, fun W _ _ T _ y _ => ?_⟩
    rw [one_mul]
    exact Finset.single_le_sum (f := fun i => ‖iteratedFDeriv ℝ i
      (tensor0SModelInChart (s + 0) c (iteratedMetricCovariantDerivative g s T 0)) y‖)
      (fun i _ => norm_nonneg _) (Finset.mem_range.2 (by omega))
  | succ j ih =>
    intro k
    choose Cf hCf0 hCf using ih
    obtain ⟨MΓ, hMΓ, hΓ⟩ := connChart_bound_O35 g c hK hKt k
    have : CompleteSpace E := FiniteDimensional.complete ℝ E
    set b := ‖corrBilin_O35 (E := E) (s + j)‖
    set A := ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * Cf (k - i)
    have hA0 : 0 ≤ A := Finset.sum_nonneg (fun i _ => mul_nonneg (by positivity) (hCf0 _))
    refine ⟨Cf (k + 1) + b * MΓ * A,
      add_nonneg (hCf0 _) (mul_nonneg (mul_nonneg (norm_nonneg _) hMΓ) hA0),
      fun W hW hKW T hT y hy => ?_⟩
    have hV := isOpen_chartSet_O35 (I := I) c hW
    have hyV : y ∈ (extChartAt I c).target ∩ (extChartAt I c).symm ⁻¹' W := ⟨hKt hy, hKW hy⟩
    set G : ℕ → ℝ := fun n => ‖iteratedFDeriv ℝ n
      (tensor0SModelInChart (s + 0) c (iteratedMetricCovariantDerivative g s T 0)) y‖ with hGdef
    have hG : ∀ n, 0 ≤ G n := fun n => norm_nonneg _
    set S := ∑ i ∈ Finset.range (j + 1 + k + 1), G i
    have hstep := (iter_step_O35 g s T c hW hT hyV j k).2
    simp only at hstep
    rw [iteratedFDerivWithin_of_isOpen k hV hyV,
      iteratedFDerivWithin_of_isOpen (k + 1) hV hyV] at hstep
    have h1 : ‖iteratedFDeriv ℝ (k + 1) (tensor0SModelInChart (s + j) c
        (iteratedMetricCovariantDerivative g s T j)) y‖ ≤ Cf (k + 1) * S := by
      refine (hCf (k + 1) W hW hKW T hT y hy).trans (le_of_eq ?_)
      rw [show j + (k + 1) + 1 = j + 1 + k + 1 by omega]
    have hR : ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
        ‖iteratedFDerivWithin ℝ i (connectionEndomorphismInChartL
          (leviCivitaConnectionOfMetric g) c)
          ((extChartAt I c).target ∩ (extChartAt I c).symm ⁻¹' W) y‖ *
        ‖iteratedFDerivWithin ℝ (k - i) (tensor0SModelInChart (s + j) c
          (iteratedMetricCovariantDerivative g s T j))
          ((extChartAt I c).target ∩ (extChartAt I c).symm ⁻¹' W) y‖ ≤
        ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * Cf (k - i) * (MΓ * S) := by
      refine Finset.sum_le_sum (fun i hi => ?_)
      have hi' : i ≤ k := by simp at hi; omega
      have hΓi : ‖iteratedFDerivWithin ℝ i (connectionEndomorphismInChartL
          (leviCivitaConnectionOfMetric g) c)
          ((extChartAt I c).target ∩ (extChartAt I c).symm ⁻¹' W) y‖ ≤ MΓ := by
        rw [iteratedFDerivWithin_of_isOpen i hV hyV]
        exact hΓ i hi' y hy
      have hFi := (hCf (k - i) W hW hKW T hT y hy).trans
        (mul_le_mul_of_nonneg_left (sum_mono_O35 G hG (show j + (k - i) + 1 ≤ j + 1 + k + 1 by omega))
          (hCf0 _))
      rw [← iteratedFDerivWithin_of_isOpen (k - i) hV hyV] at hFi
      have hc : (0 : ℝ) ≤ k.choose i := by positivity
      calc (k.choose i : ℝ) * _ * _ ≤ (k.choose i : ℝ) * MΓ * (Cf (k - i) * S) := by gcongr
        _ = _ := by ring
    rw [← Finset.sum_mul] at hR
    have hb : 0 ≤ b := norm_nonneg _
    have hbR := mul_le_mul_of_nonneg_left hR hb
    calc _ ≤ _ := hstep
      _ ≤ Cf (k + 1) * S + b * (A * (MΓ * S)) := add_le_add h1 hbR
      _ = _ := by ring

/-- chartCov-A' (model norms) with a constant uniform in `W`. -/
theorem chartCovModelRevUnif_O43 (g : SmoothRiemannianMetric I M) (c : M) {K : Set E}
    (hK : IsCompact K) (hKt : K ⊆ (extChartAt I c).target) (s j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ W : Set M, IsOpen W → K ⊆ (extChartAt I c).symm ⁻¹' W →
      ∀ T : (p : M) → Tensor0SSpace s I p,
      ContMDiffOn I (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) ∞
        (fun p => (⟨p, T p⟩ : TotalSpace (Tensor0SModel s ℝ E)
          (fun q => Tensor0SSpace s I q))) W →
      ∀ y ∈ K, ‖tensor0SModelInChart (s + j) c (iteratedMetricCovariantDerivative g s T j) y‖ ≤
        C * ∑ i ∈ Finset.range (j + 1), ‖iteratedFDeriv ℝ i (tensor0SModelInChart s c T) y‖ := by
  obtain ⟨C, hC, h⟩ := chartCovModelRevUnif_iter_O43 g c hK hKt s j 0
  refine ⟨C, hC, fun W hW hKW T hT y hy => ?_⟩
  have h0 := h W hW hKW T hT y hy
  rw [norm_iteratedFDeriv_zero] at h0
  exact h0

/-- **S80 form** (A' + N'): covariant fibre norms ≤ C · Σ coordinate jets, `C` uniform in `W`. -/
theorem chartCovRev_O43 (g : SmoothRiemannianMetric I M) (c : M) {K : Set E}
    (hK : IsCompact K) (hKt : K ⊆ (extChartAt I c).target) (s j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ W : Set M, IsOpen W → K ⊆ (extChartAt I c).symm ⁻¹' W →
      ∀ T : (p : M) → Tensor0SSpace s I p,
      ContMDiffOn I (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) ∞
        (fun p => (⟨p, T p⟩ : TotalSpace (Tensor0SModel s ℝ E)
          (fun q => Tensor0SSpace s I q))) W →
      ∀ y ∈ K, tensor0SFiberNorm g ((extChartAt I c).symm y) (s + j)
          (iteratedMetricCovariantDerivative g s T j ((extChartAt I c).symm y)) ≤
        C * ∑ i ∈ Finset.range (j + 1), ‖iteratedFDeriv ℝ i (tensor0SModelInChart s c T) y‖ := by
  obtain ⟨CA, hCA, hA⟩ := chartCovModelRevUnif_O43 g c hK hKt s j
  obtain ⟨CN, hCN, hN⟩ := chartCovNormRev_O43 g c hK hKt (s + j)
  refine ⟨CN * CA, mul_nonneg hCN hCA, fun W hW hKW T hT y hy => ?_⟩
  refine (hN y hy _).trans ?_
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (hA W hW hKW T hT y hy) hCN

end GC.LongTime.Ch12
