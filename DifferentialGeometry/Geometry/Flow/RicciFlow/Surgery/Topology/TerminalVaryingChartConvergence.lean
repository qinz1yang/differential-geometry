import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Norm.ReferenceChange
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalScalarCurvature
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Norm.Comparison
import DifferentialGeometry.Topology.SigmaCompactOpen
import DifferentialGeometry.Geometry.Metric.Convergence.Naturality.PullbackCrossConvergence
import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.Restriction
import DifferentialGeometry.Geometry.Metric.DerivativeScaleENorm

noncomputable section

open Set Filter Manifold
open DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Metric
open scoped Manifold ContDiff Topology BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u
variable {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s}

private local instance terminalSigmaCompact : SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
      G.terminalRegularOpen.isOpen)

private local instance terminalOpenSigmaCompact
    (V : TopologicalSpace.Opens G.terminalRegularOpen) : SigmaCompactSpace V :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel V.isOpen)

private local instance pullbackCompleteSpace {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] : CompleteSpace E :=
  FiniteDimensional.complete ℝ E

private local instance terminalC1 : IsManifold ThreeModel 1 G.terminalRegularOpen :=
  IsManifold.of_le (n := ∞) (by decide)

private local instance terminalC2 : IsManifold ThreeModel 2 G.terminalRegularOpen :=
  IsManifold.of_le (n := ∞) (by decide)

theorem TerminalLimitMetric.eventually_metricDerivNorm_source_on_compact
    (L : G.TerminalLimitMetric) {K : Set G.terminalRegularOpen} (hK : IsCompact K)
    (p : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in 𝓝[<] s, ∀ j ≤ p, ∀ x ∈ K,
      metricDerivNorm j ((G.flow.base.metric t).restrictOpen G.terminalRegularOpen)
        L.metric ((G.flow.base.metric t).restrictOpen G.terminalRegularOpen) x < ε := by
  let _ : LocallyCompactSpace G.terminalRegularOpen :=
    ChartedSpace.locallyCompactSpace ThreeSpace G.terminalRegularOpen
  obtain ⟨K', hK', hKK'⟩ := exists_compact_superset hK
  obtain ⟨δ, hδ, hδ1, hδdim, hδbound⟩ :=
    exists_metric_reference_change_delta (E := ThreeSpace) p (half_pos hε)
  have hpoint (j : Fin (p + 1)) : ∀ᶠ t in 𝓝[<] s, ∀ x ∈ K',
      metricDerivNorm j ((G.flow.base.metric t).restrictOpen G.terminalRegularOpen)
        L.metric L.metric x < δ := by
    obtain ⟨d, hd, hb⟩ := L.converges K' hK' j δ hδ
    have htime : ∀ᶠ t in 𝓝[<] s, t ∈ Ioo d s := Ioo_mem_nhdsLT hd.2
    exact htime.mono fun t ht => hb t ht
  have hall := eventually_all.mpr hpoint
  filter_upwards [hall] with t ht
  intro j hj x hx
  let gt := (G.flow.base.metric t).restrictOpen G.terminalRegularOpen
  have hbound := metric_deriv_norm_reference_change_le (I := ThreeModel)
    (u := interior K') isOpen_interior L.metric gt L.metric p hδ.le hδ1.le hδdim hδbound
    (by intro y _ k _; rw [metricDerivNorm_self]; exact hδ.le)
    (by intro y hy k hk; exact (ht ⟨k, Nat.lt_succ_of_le hk⟩ y (interior_subset hy)).le)
    x (hKK' hx) j hj
  rw [metricDerivNorm_symm] at hbound
  exact hbound.trans_lt (by linarith)


theorem TerminalLimitMetric.eventually_metricDerivNormSupOn_varying_pullbacks
    (L : G.TerminalLimitMetric) {K : Set G.terminalRegularOpen} (hK : IsCompact K)
    {τ : ℕ → ℝ} (hτ : Tendsto τ atTop (𝓝[<] s))
    {E H X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [T2Space X]
    (V : ℕ → TopologicalSpace.Opens G.terminalRegularOpen)
    (Φ : ∀ n, X ≃ₘ⟮I, ThreeModel⟯ V n)
    (T : Set X) (U : ℕ → Set X) (hU : ∀ n, IsOpen (U n))
    (hTU : ∀ n, T ⊆ U n)
    (himage : ∀ᶠ n in atTop, ∀ x ∈ T, (Φ n x).1 ∈ K)
    (gRef : SmoothRiemannianMetric I X) (p : ℕ)
    {C B : ℝ} (hC : 1 ≤ C) (hB : 0 ≤ B)
    {Q : ℕ → ℝ} (hQ : ∀ n, 0 < Q n) {Qmax : ℝ}
    (hQmax : ∀ᶠ n in atTop, Q n ≤ Qmax) :
    let gSource := fun n => Diffeomorph.pullbackMetricCross
      (((G.flow.base.metric (τ n)).restrictOpen G.terminalRegularOpen).restrictOpen (V n))
      (Φ n)
    (∀ᶠ n in atTop, ∀ x ∈ U n, ∀ v : TangentSpace I x,
      C⁻¹ * (gSource n).inner x v v ≤ gRef.inner x v v ∧
        gRef.inner x v v ≤ C * (gSource n).inner x v v) →
    (∀ᶠ n in atTop, ∀ x ∈ U n, ∀ j : ℕ, 1 ≤ j → j ≤ p →
      Real.sqrt (normSq0S gRef x (2 + j)
        (iterCov (gSource n) 2 (metricTensorField gRef) j x)) ≤ B) →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      metricDerivNormSupOn T p (scaleMetric (Q n) (hQ n) (gSource n))
        (scaleMetric (Q n) (hQ n)
          (Diffeomorph.pullbackMetricCross (L.metric.restrictOpen (V n)) (Φ n))) gRef < ε := by
  intro gSource hequiv hjets ε hε
  let _ : SigmaCompactSpace X :=
    (Φ 0).toHomeomorph.isClosedEmbedding.sigmaCompactSpace
  have hQmax0 : 0 ≤ Qmax := by
    obtain ⟨n, hn⟩ := hQmax.exists
    exact (hQ n).le.trans hn
  obtain ⟨D, hD, hcompare⟩ :=
    exists_uniform_metric_deriv_norm_reference_bound (I := I) (M := X) p hC hB
  let α : ℝ := ε / (2 * ((Qmax + 1) * (D + 1) * ((p : ℝ) + 1)))
  have hα : 0 < α := by dsimp [α]; positivity
  have hsmall : Qmax * (D * (((p : ℝ) + 1) * α)) ≤ ε / 2 := by
    calc
      Qmax * (D * (((p : ℝ) + 1) * α)) =
          (Qmax * D) * (((p : ℝ) + 1) * α) := by ring
      _ ≤ ((Qmax + 1) * (D + 1)) * (((p : ℝ) + 1) * α) :=
        mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
      _ = ε / 2 := by dsimp [α]; field_simp
  have herr := hτ.eventually (L.eventually_metricDerivNorm_source_on_compact hK p hα)
  filter_upwards [hequiv, hjets, himage, hQmax, herr] with n he hjetn hi hq hn
  let gt := (G.flow.base.metric (τ n)).restrictOpen G.terminalRegularOpen
  let gTerm := Diffeomorph.pullbackMetricCross (L.metric.restrictOpen (V n)) (Φ n)
  have hnorm : ∀ j ≤ p, ∀ x ∈ T,
      metricDerivNorm j (gSource n) gTerm (gSource n) x < α := by
    let _ : IsManifold I 1 X := IsManifold.of_le (n := ∞) (by decide)
    let _ : IsManifold I 2 X := IsManifold.of_le (n := ∞) (by decide)
    let _ : IsManifold ThreeModel 1 (V n) := IsManifold.of_le (n := ∞) (by decide)
    let _ : IsManifold ThreeModel 2 (V n) := IsManifold.of_le (n := ∞) (by decide)
    intro j hj x hx
    change metricDerivNorm j
      (Diffeomorph.pullbackMetricCross (gt.restrictOpen (V n)) (Φ n))
      (Diffeomorph.pullbackMetricCross (L.metric.restrictOpen (V n)) (Φ n))
      (Diffeomorph.pullbackMetricCross (gt.restrictOpen (V n)) (Φ n)) x < α
    rw [metricDerivNorm_pullbackCross, metricDerivNorm_restrictOpen]
    exact hn j hj (Φ n x).1 (hi x hx)
  apply lt_of_le_of_lt
    (metricDerivNormSupOn_le_of_forall T p _ _ gRef (ε / 2) (half_pos hε).le ?_)
    (by linarith)
  intro j hj x hx
  rw [metricDerivNorm_scaleMetric_both_left]
  have hsum : (∑ k ∈ Finset.range (p + 1),
      metricDerivNorm k (gSource n) gTerm (gSource n) x) ≤ ((p : ℝ) + 1) * α := by
    calc
      _ ≤ ∑ _k ∈ Finset.range (p + 1), α := Finset.sum_le_sum fun k hk =>
        (hnorm k (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) x hx).le
      _ = _ := by simp
  have hbound := hcompare (U n) (hU n) (gSource n) gRef he
    (fun y hy k hk1 hkp => hjetn y hy k hk1 hkp) (gSource n) gTerm j hj x (hTU n hx)
  calc
    Q n * metricDerivNorm j (gSource n) gTerm gRef x ≤
        Q n * (D * (((p : ℝ) + 1) * α)) :=
      mul_le_mul_of_nonneg_left
        (hbound.trans (mul_le_mul_of_nonneg_left hsum hD)) (hQ n).le
    _ ≤ Qmax * (D * (((p : ℝ) + 1) * α)) :=
      mul_le_mul_of_nonneg_right hq (by positivity)
    _ ≤ ε / 2 := hsmall

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab
