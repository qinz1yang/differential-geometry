import DifferentialGeometry.Geometry.Metric.Convergence.Curvature.Scalar
import DifferentialGeometry.Geometry.Metric.DirectLimit.Curvature
import DifferentialGeometry.Geometry.Metric.Pullback.PartialDiffeomorph.Curvature
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Limit.Metric.QuadraticBounds

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Filter Set TopologicalSpace
open Geometry.Curvature
open scoped Manifold ContDiff _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : ℕ → Type*} [∀ j, MetricSpace (M j)] [∀ j, ChartedSpace H (M j)]
  [∀ j, IsManifold I ∞ (M j)]

section ScalarCompatibility

variable {M0 : Type*} [TopologicalSpace M0] [ChartedSpace H M0]
  [T2Space M0] [IsManifold I ∞ M0] [SigmaCompactSpace M0]

theorem MetricCPConvergenceOn.tendstoUniformlyOn_metricScalarAt
    {gSeq : ℕ → SmoothRiemannianMetric I M0} {gInf gRef : SmoothRiemannianMetric I M0}
    {K : Set M0} (hconv : MetricCPConvergenceOn K 2 gSeq gInf gRef) (hK : IsCompact K) :
    TendstoUniformlyOn (fun n x => metricScalarAt (I := I) (gSeq n) x)
      (fun x => metricScalarAt (I := I) gInf x) atTop K := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hzero : MetricCPConvergenceOn K 0 gSeq gInf gRef := by
    intro ε hε
    obtain ⟨n₀, hn₀⟩ := hconv (ε / 2) (by positivity)
    refine ⟨n₀, fun n hn => ?_⟩
    apply lt_of_le_of_lt (metricDerivNormSupOn_le_of_forall K 0 (gSeq n) gInf gRef
      (ε / 2) (by positivity) ?_) (by linarith)
    intro a ha x hx
    exact (derivNorm_le_sup hK (by omega : a ≤ 2) (gSeq n) gInf gRef hx).trans
      (hn₀ n hn).le
  obtain ⟨c, hc, hcBound⟩ := metric_lower_on hK gInf gRef
  have hquad := hzero.eventually_quadratic_bounds hK (show 0 < (1 / 2 : ℝ) by norm_num)
  have hlower : ∀ᶠ n in atTop, ∀ x ∈ K, ∀ v : TangentSpace I x,
      (c / 2) * gRef.inner x v v ≤ (gSeq n).inner x v v := by
    filter_upwards [hquad] with n hn
    intro x hx v
    have hb := hcBound x hx v
    have hq := (hn x hx v).1
    nlinarith
  obtain ⟨B₀, hB₀⟩ := metricCovDerivNorm_bddOn hK 0 gInf gRef
  obtain ⟨B₁, hB₁⟩ := metricCovDerivNorm_bddOn hK 1 gInf gRef
  obtain ⟨B₂, hB₂⟩ := metricCovDerivNorm_bddOn hK 2 gInf gRef
  let B := max 0 (max B₀ (max B₁ B₂)) + 1
  have hBlim : ∀ x ∈ K, ∀ a : ℕ, a ≤ 2 → metricCovDerivNorm a gInf gRef x ≤ B - 1 := by
    intro x hx a ha
    have h0 : B₀ ≤ B - 1 := by dsimp [B]; grind
    have h1 : B₁ ≤ B - 1 := by dsimp [B]; grind
    have h2 : B₂ ≤ B - 1 := by dsimp [B]; grind
    interval_cases a
    · exact (hB₀ x hx).trans h0
    · exact (hB₁ x hx).trans h1
    · exact (hB₂ x hx).trans h2
  obtain ⟨n₀, hn₀⟩ := hconv 1 zero_lt_one
  have hBseq : ∀ᶠ n in atTop, ∀ x ∈ K, ∀ a : ℕ, a ≤ 2 →
      metricCovDerivNorm a (gSeq n) gRef x ≤ B := by
    filter_upwards [eventually_ge_atTop n₀] with n hn
    intro x hx a ha
    have hb := covNorm_le_add a (gSeq n) gInf gRef x
    have hd := (derivNorm_le_sup hK ha (gSeq n) gInf gRef hx).trans_lt (hn₀ n hn)
    linarith [hBlim x hx a ha]
  obtain ⟨C, hC, hbound⟩ := exists_abs_metricScalarAt_sub_le gRef hK (c / 2) B (by positivity)
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  let δ := ε / (3 * C + 1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨n₁, hn₁⟩ := hconv δ hδ
  filter_upwards [hlower, hBseq, eventually_ge_atTop n₁] with n hnlow hnB hn
  intro x hx
  have hsmall : ∑ q ∈ Finset.range 3, metricDerivNorm q (gSeq n) gInf gRef x ≤ 3 * δ := by
    calc
      _ ≤ ∑ _q ∈ Finset.range 3, δ := Finset.sum_le_sum fun q hq =>
        ((derivNorm_le_sup hK (by have := Finset.mem_range.mp hq; omega : q ≤ 2) (gSeq n) gInf gRef hx).trans_lt
          (hn₁ n hn)).le
      _ = _ := by simp
  have hresult := hbound (gSeq n) gInf hnlow (fun y hy v => by
      have hnn := metric_inner_self_nonneg gRef y v
      have hb := hcBound y hy v
      nlinarith) hnB (fun y hy a ha => (hBlim y hy a ha).trans (by linarith)) x hx
  have hδC : C * (3 * δ) < ε := by
    have hid : δ * (3 * C + 1) = ε := by dsimp [δ]; field_simp
    nlinarith
  rw [Real.dist_eq, abs_sub_comm]
  exact hresult.trans_lt ((mul_le_mul_of_nonneg_left hsmall hC.le).trans_lt hδC)

theorem MetricCPConvergenceOn.tendsto_metricScalarAt_sub_of_eventually_mem
    {gSeq : ℕ → SmoothRiemannianMetric I M0} {gInf gRef : SmoothRiemannianMetric I M0}
    {K : Set M0} (hconv : MetricCPConvergenceOn K 2 gSeq gInf gRef) (hK : IsCompact K)
    {x : ℕ → M0} (hx : ∀ᶠ n in atTop, x n ∈ K) :
    Tendsto (fun n => metricScalarAt (I := I) (gSeq n) (x n) - metricScalarAt (I := I) gInf (x n))
      atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hu := Metric.tendstoUniformlyOn_iff.mp (hconv.tendstoUniformlyOn_metricScalarAt hK) ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hu.and hx)
  refine ⟨N, fun n hn => ?_⟩
  simpa only [Real.dist_eq, sub_zero, abs_sub_comm] using (hN n hn).1 (x n) (hN n hn).2

end ScalarCompatibility

theorem tendstoUniformlyOn_metricScalarAt_of_chain_pullback_convergence
    (U : ∀ j, Opens (M j)) [∀ j, Nonempty (U j)] [∀ j, SigmaCompactSpace (U j)]
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) ∞)
    (hUstep : ∀ j, (U j : Set (M j)) ⊆ (Ψ j).source)
    (hmap : ∀ j, (Ψ j : M j → M (j + 1)) '' (U j : Set (M j)) ⊆
      (U (j + 1) : Set (M (j + 1))))
    (hU : ∀ j l, (U j : Set (M j)) ⊆ (chainComp Ψ j l).source)
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    (gInf gRef : ∀ j, SmoothRiemannianMetric I (U j))
    (hg : (SmoothSeqSystem.ofPartialDiffeomorphs U Ψ hUstep hmap).MetricCocycle gInf)
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hconv : ∀ j, ∀ K : Set (U j), IsCompact K → MetricCPConvergenceOn K 2
      (fun k => chainPullbackSeq Ψ g (U j) (hU j) (φ k - j)) (gInf j) (gRef j)) :
    let S := SmoothSeqSystem.ofPartialDiffeomorphs U Ψ hUstep hmap
    let Φ : ∀ k, PartialDiffeomorph I I S.toSeqSystem.Lim (M (φ k)) ∞ :=
      fun k => PartialDiffeomorph.liftTargetOpen (S.inclPartialDiffeo (φ k)) rfl
    ∀ K : Set S.toSeqSystem.Lim, IsCompact K →
      TendstoUniformlyOn (fun k z => metricScalarAt (I := I) (g (φ k)) (Φ k z))
        (fun z => metricScalarAt (I := I) (S.limitMetric gInf hg) z) atTop K := by
  let S := SmoothSeqSystem.ofPartialDiffeomorphs U Ψ hUstep hmap
  let Φ : ∀ m, PartialDiffeomorph I I S.toSeqSystem.Lim (M m) ∞ :=
    fun m => PartialDiffeomorph.liftTargetOpen (S.inclPartialDiffeo m) rfl
  dsimp only
  intro K hK
  obtain ⟨j, Kj, hKj, rfl⟩ := S.toSeqSystem.exists_compact_stage_representation hK
  have hstage := (hconv j Kj hKj).tendstoUniformlyOn_metricScalarAt hKj
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hstage ε hε, eventually_ge_atTop j] with k hk hkj
  rintro z ⟨a, ha, rfl⟩
  have hj : j ≤ φ k := hkj.trans (hφ.id_le k)
  have hscalar : metricScalarAt (I := I)
      (chainPullbackSeq Ψ g (U j) (hU j) (φ k - j)) a =
        metricScalarAt (I := I) (g (φ k)) (Φ (φ k) (S.toSeqSystem.incl j a)) := by
    have hgeneral (l : ℕ) : metricScalarAt (I := I)
        (chainPullbackSeq Ψ g (U j) (hU j) l) a =
          metricScalarAt (I := I) (g (j + l)) (Φ (j + l) (S.toSeqSystem.incl j a)) := by
      rw [chainPullbackSeq, PartialDiffeomorph.metricScalarAt_pullbackMetricOn]
      have hpoint : Φ (j + l) (S.toSeqSystem.incl j a) = chainComp Ψ j l (a : M j) :=
        SmoothSeqSystem.ofPartialDiffeomorphs_invIncl_incl U Ψ hUstep hmap j l a
      rw [hpoint]
    generalize φ k = m at hj ⊢
    obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le hj
    simpa only [Nat.add_sub_cancel_left] using hgeneral l
  change dist (metricScalarAt (I := I) (S.limitMetric gInf hg) (S.toSeqSystem.incl j a))
    (metricScalarAt (I := I) (g (φ k)) (Φ (φ k) (S.toSeqSystem.incl j a))) < ε
  rw [S.metricScalarAt_limitMetric_incl gInf hg j a, ← hscalar]
  exact hk a ha

theorem tendsto_metricScalarAt_inverse_sub_of_chain_pullback_convergence
    (U : ∀ j, Opens (M j)) [∀ j, Nonempty (U j)] [∀ j, SigmaCompactSpace (U j)]
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) ∞)
    (hUstep : ∀ j, (U j : Set (M j)) ⊆ (Ψ j).source)
    (hmap : ∀ j, (Ψ j : M j → M (j + 1)) '' (U j : Set (M j)) ⊆
      (U (j + 1) : Set (M (j + 1))))
    (hU : ∀ j l, (U j : Set (M j)) ⊆ (chainComp Ψ j l).source)
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    (gInf gRef : ∀ j, SmoothRiemannianMetric I (U j))
    (hg : (SmoothSeqSystem.ofPartialDiffeomorphs U Ψ hUstep hmap).MetricCocycle gInf)
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hconv : ∀ j, ∀ K : Set (U j), IsCompact K → MetricCPConvergenceOn K 2
      (fun k => chainPullbackSeq Ψ g (U j) (hU j) (φ k - j)) (gInf j) (gRef j))
    (y : ∀ k, M (φ k)) :
    let S := SmoothSeqSystem.ofPartialDiffeomorphs U Ψ hUstep hmap
    let Φ : ∀ k, PartialDiffeomorph I I S.toSeqSystem.Lim (M (φ k)) ∞ :=
      fun k => PartialDiffeomorph.liftTargetOpen (S.inclPartialDiffeo (φ k)) rfl
    (∃ K : Set S.toSeqSystem.Lim, IsCompact K ∧ ∀ᶠ k in atTop,
      (Φ k).symm (y k) ∈ K ∧ Φ k ((Φ k).symm (y k)) = y k) →
    Tendsto (fun k => metricScalarAt (I := I) (g (φ k)) (y k) -
      metricScalarAt (I := I) (S.limitMetric gInf hg) ((Φ k).symm (y k))) atTop (𝓝 0) := by
  let S := SmoothSeqSystem.ofPartialDiffeomorphs U Ψ hUstep hmap
  let Φ : ∀ k, PartialDiffeomorph I I S.toSeqSystem.Lim (M (φ k)) ∞ :=
    fun k => PartialDiffeomorph.liftTargetOpen (S.inclPartialDiffeo (φ k)) rfl
  dsimp only
  rintro ⟨K, hK, htrap⟩
  have hu := tendstoUniformlyOn_metricScalarAt_of_chain_pullback_convergence
    U Ψ hUstep hmap hU g gInf gRef hg φ hφ hconv K hK
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((Metric.tendstoUniformlyOn_iff.mp hu ε hε).and htrap)
  refine ⟨N, fun k hk => ?_⟩
  have hb := (hN k hk).1 ((Φ k).symm (y k)) (hN k hk).2.1
  have hforward : Φ k ((Φ k).symm (y k)) = y k := (hN k hk).2.2
  change dist (metricScalarAt (I := I) (S.limitMetric gInf hg) ((Φ k).symm (y k)))
    (metricScalarAt (I := I) (g (φ k)) (Φ k ((Φ k).symm (y k)))) < ε at hb
  rw [hforward] at hb
  simpa only [Real.dist_eq, sub_zero, abs_sub_comm] using hb

end DifferentialGeometry.CheegerGromovCompactness
