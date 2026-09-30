import DifferentialGeometry.Topology.Manifold.PartitionDerivative
import DifferentialGeometry.Geometry.Operator.Gradient.NormSquared
import DifferentialGeometry.Geometry.Metric.PointwiseInner.Bounds

noncomputable section

open Set Filter Topology
open scoped ContDiff Manifold BigOperators

namespace DifferentialGeometry.Geometry.Operator

variable {ι E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [I.Boundaryless]

omit [I.Boundaryless] in
private theorem support_sqrt_normGradSqFun_subset (g : SmoothRiemannianMetric I M)
    (f : M → ℝ) :
    Function.support (fun x => Real.sqrt (normGradSqFun g f x)) ⊆ tsupport f := by
  intro x hx
  by_contra hn
  have hzero : f =ᶠ[𝓝 x] fun _ => (0 : ℝ) :=
    notMem_tsupport_iff_eventuallyEq.mp hn
  have hz : mfderiv I 𝓘(ℝ) f x = 0 := by
    ext v
    change (show ℝ from mfderiv I 𝓘(ℝ) f x v) = 0
    rw [hzero.mfderiv_eq, mfderiv_const]
    rfl
  have hg := gradFun_eq_zero_of_mfderiv_eq_zero g f hz
  apply hx
  simp only [normGradSqFun_def, hg, map_zero,
    Real.sqrt_zero]

omit [I.Boundaryless] in
private theorem abs_mvfderiv_le_normGrad (g : SmoothRiemannianMetric I M)
    (f : M → ℝ) (x : M) (v : TangentSpace I x) :
    |mvfderiv I f x v| ≤ Real.sqrt (normGradSqFun g f x) *
      Real.sqrt (g.inner x v v) := by
  rw [mvfderiv_real_eq_mfderiv, ← inner_gradFun g f x v]
  exact DifferentialGeometry.SmoothRiemannianMetric.abs_metric_inner_le_sqrt_metric_quadratic g x _ v

private theorem continuous_partition_gradient_sum
    (g : SmoothRiemannianMetric I M) (ρ : SmoothPartitionOfUnity ι I M) :
    Continuous (fun x => ∑ᶠ i, Real.sqrt (normGradSqFun g (ρ i) x)) := by
  apply continuous_finsum
  · intro i
    exact (normGradSqFun_continuous g (ρ i).contMDiff).sqrt
  · exact ρ.locallyFinite.closure.subset
      (fun i => support_sqrt_normGradSqFun_subset g (ρ i))

private theorem exists_positive_le_on_isCompact
    {f : M → ℝ} (hf : Continuous f) (hpos : ∀ x, 0 < f x)
    {K : Set M} (hK : IsCompact K) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ K, ε ≤ f x := by
  by_cases hne : K.Nonempty
  · obtain ⟨x, hx, hmin⟩ := hK.exists_isMinOn hne hf.continuousOn
    exact ⟨f x, hpos x, hmin⟩
  · refine ⟨1, zero_lt_one, ?_⟩
    intro x hx
    exact (hne ⟨x, hx⟩).elim


theorem exists_contMDiff_approx_with_mvfderiv_bound_of_local
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (L : ℝ)
    (hlocal : ∀ x : M, ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
      ∀ δ : ℝ, 0 < δ → ∃ u : M → ℝ,
        ContMDiffOn I 𝓘(ℝ) ∞ u U ∧
        (∀ y ∈ U, |u y - f y| ≤ δ) ∧
        ∀ y ∈ U, ∀ v : TangentSpace I y,
          |mvfderiv I u y v| ≤ L * Real.sqrt (g.inner y v v))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ F : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ F ∧
      (∀ x, |F x - f x| ≤ ε) ∧
      ∀ x, ∀ v : TangentSpace I x,
        |mvfderiv I F x v| ≤ (L + 1) * Real.sqrt (g.inner x v v) := by
  classical
  let : LocallyCompactSpace H := I.locallyCompactSpace
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let : RegularSpace M := inferInstance
  choose U hU hxU hloc using hlocal
  have href (x : M) : ∃ V : Set M, IsOpen V ∧ x ∈ V ∧
      closure V ⊆ U x ∧ IsCompact (closure V) := by
    obtain ⟨V, hVo, hxV, hVU, hVc⟩ :=
      exists_open_between_and_isCompact_closure isCompact_singleton (hU x)
        (singleton_subset_iff.mpr (hxU x))
    exact ⟨V, hVo, hxV (mem_singleton x), hVU, hVc⟩
  choose V hVo hxV hVU hVc using href
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate I isClosed_univ V hVo
    (fun x _ => mem_iUnion.mpr ⟨x, hxV x⟩)
  let B : M → ℝ := fun x => ∑ᶠ i, Real.sqrt (normGradSqFun g (ρ i) x)
  have hBcont : Continuous B := continuous_partition_gradient_sum g ρ
  have hBpos (x : M) : 0 ≤ B x := finsum_nonneg (fun _ => Real.sqrt_nonneg _)
  let θ : M → ℝ := fun x => min ε (1 / (1 + B x))
  have hθcont : Continuous θ := continuous_const.min
    (continuous_const.div (continuous_const.add hBcont) (fun x => by linarith [hBpos x]))
  have hθpos (x : M) : 0 < θ x := lt_min hε (one_div_pos.mpr (by linarith [hBpos x]))
  have hθeps (x : M) : θ x ≤ ε := min_le_left _ _
  have hθB (x : M) : B x * θ x ≤ 1 := by
    have h := (le_div_iff₀ (show 0 < 1 + B x by linarith [hBpos x])).mp
      (min_le_right ε (1 / (1 + B x)))
    change θ x * (1 + B x) ≤ 1 at h
    nlinarith [hθpos x]
  have hδ (i : M) : ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ closure (V i), δ ≤ θ x :=
    exists_positive_le_on_isCompact hθcont hθpos (hVc i)
  choose δ hδpos hδbound using hδ
  choose u hu happ hdu using fun i => hloc i (δ i) (hδpos i)
  have hsub (i : M) : tsupport (ρ i) ⊆ U i :=
    fun x hx => hVU i (subset_closure (hρ i hx))
  let F : M → ℝ := fun x => ∑ᶠ i, ρ i x * u i x
  have hFs : ContMDiff I 𝓘(ℝ) ∞ F := by
    exact ρ.contMDiff_finsum_smul (fun i x hx =>
      (hu i).contMDiffAt ((hU i).mem_nhds (hsub i hx)))
  refine ⟨F, hFs, ?_, ?_⟩
  · intro x
    have hball : F x ∈ Metric.closedBall (f x) ε := by
      apply ρ.finsum_smul_mem_convex (mem_univ x) _ (convex_closedBall _ _)
      intro i hi
      have hxs : x ∈ tsupport (ρ i) := subset_tsupport _ hi
      have herror : |u i x - f x| ≤ ε :=
        (happ i x (hsub i hxs)).trans ((hδbound i x (subset_closure (hρ i hxs))).trans (hθeps x))
      simpa only [Metric.mem_closedBall, Real.dist_eq] using herror
    simpa only [Metric.mem_closedBall, Real.dist_eq] using hball
  · intro x v
    have hnorm := Real.sqrt_nonneg (g.inner x v v)
    have hs (i : M) (hi : i ∈ ρ.fintsupport x) : x ∈ tsupport (ρ i) :=
      (ρ.mem_fintsupport_iff x i).mp hi
    have hsum : (∑ i ∈ ρ.fintsupport x, Real.sqrt (normGradSqFun g (ρ i) x)) = B x := by
      symm
      apply finsum_eq_sum_of_support_subset
      intro i hi
      exact (ρ.mem_fintsupport_iff x i).mpr (support_sqrt_normGradSqFun_subset g (ρ i) hi)
    have herr : (∑ i ∈ ρ.fintsupport x,
        |mvfderiv I (ρ i) x v| * |u i x - f x|) ≤ Real.sqrt (g.inner x v v) := by
      calc
        _ ≤ ∑ i ∈ ρ.fintsupport x,
            (Real.sqrt (normGradSqFun g (ρ i) x) * Real.sqrt (g.inner x v v)) * θ x := by
          apply Finset.sum_le_sum
          intro i hi
          exact mul_le_mul (abs_mvfderiv_le_normGrad g (ρ i) x v)
            ((happ i x (hsub i (hs i hi))).trans
              (hδbound i x (subset_closure (hρ i (hs i hi)))))
            (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hnorm)
        _ = B x * θ x * Real.sqrt (g.inner x v v) := by
          rw [← Finset.sum_mul, ← Finset.sum_mul, hsum]
          ring
        _ ≤ Real.sqrt (g.inner x v v) := by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right (hθB x) hnorm
    have hd := DifferentialGeometry.Topology.Manifold.abs_mvfderiv_partition_finsum_le
      ρ u x (fun i hx => ((hu i).contMDiffAt ((hU i).mem_nhds (hsub i hx))).mdifferentiableAt (by simp))
      v (f x) (L * Real.sqrt (g.inner x v v))
      (fun i hi => hdu i x (hsub i (subset_tsupport _ hi)) v)
    change |mvfderiv I F x v| ≤ _ at hd
    linarith

end DifferentialGeometry.Geometry.Operator
