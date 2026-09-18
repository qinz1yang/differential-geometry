import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.Endpoint.CovariantContinuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.CovariantDerivative.TimeLipschitz
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.CovariantDerivative.TerminalWindow
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Source.TerminalWindow
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.LocalPullback
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.CovariantDerivative.Terminal
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Curvature.MovingShi
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedFlowSlices
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ModelWitness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedExtensionJetControl
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.LocalPullback
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.Endpoint.CovariantEvolution

section

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Filter Set
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff _root_.Topology BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem exists_metric_time_lipschitz_constant_of_local_solution
    (U : TopologicalSpace.Opens M) [SigmaCompactSpace U]
    (gRef : SmoothRiemannianMetric I M) {B : ℝ} (hB : 1 ≤ B)
    (N : ℕ) (C : ℕ → ℝ) {K : ℝ} (hK : 0 ≤ K) :
    ∀ q ≤ N, ∃ L : ℝ, 0 ≤ L ∧
      ∀ (g : ℝ → SmoothRiemannianMetric I M)
        (D : RealTimeInterval) (S : SolutionOn (I := I) (M := U) D),
      IsSolutionOn S →
      (∀ t, S.family.metric t = (g t).restrictOpen U) →
      ∀ {a b : ℝ}, a < b → (Icc a b ⊆ D.carrier) → (Ico a b ⊆ D.regular) →
      (∀ t ∈ Ico a b, MetricUniformEquivalentOn U gRef (g t) B) →
      (∀ r, 1 ≤ r → r ≤ N → ∀ t ∈ Ico a b, ∀ x ∈ U,
        metricCovDerivNorm r (g t) gRef x ≤ C r) →
      (∀ ψ ∈ Ico a b, MovingShiBoundOn U a ψ (fun _ t => g t) N K) →
      ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, ∀ x ∈ U,
        metricDerivNorm q (g s) (g t) gRef x ≤ L * |s - t| := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)
  let _ : IsManifold I 2 M := IsManifold.of_le (n := ∞) (by decide)
  intro q hq
  obtain ⟨L, hL, hbound⟩ := exists_metric_time_lipschitz_constant_of_local_evolution
    U.isOpen gRef hB N C hK q hq
  refine ⟨L, hL, ?_⟩
  intro g D S hS hmet a b hab hslab hreg hequiv hcov hShi
  have hinter := hbound g hequiv hcov hShi
    (fun t ht x hx v =>
      Perelman.KappaSolutions.metricCovDeriv_hasDerivAt_of_local_solution
        g gRef U S hS hmet q (hreg ht) ⟨x, hx⟩ v)
  have hterminal (s : ℝ) (x : M) (hx : x ∈ U) :
      ContinuousWithinAt (fun t => metricDerivNorm q (g s) (g t) gRef x) (Iic b) b := by
    classical
    let R := gRef.restrictOpen U
    let y : U := ⟨x, hx⟩
    obtain ⟨basis, horth⟩ := exists_orthonormal_basis R y
    have hinv := metricInverseInBasis_of_orthonormal R basis horth
    have hnorm (h : SmoothRiemannianMetric I U) :
        metricDerivNorm q ((g s).restrictOpen U) h R y = Real.sqrt
          (∑ slots : Fin (q + 2) → Fin (Module.finrank ℝ (TangentSpace I y)),
            (component0S basis (metricCovDeriv ((g s).restrictOpen U) R q y) slots -
              component0S basis (metricCovDeriv h R q y) slots) ^ 2) := by
      rw [metricDerivNorm, metricDiffCovDerivAt,
        normSq0S_identity_eq_sum_sq R y (q + 2) basis hinv]
      congr 1
    have hc : ContinuousWithinAt
        (fun t => metricDerivNorm q ((g s).restrictOpen U) (S.base.metric t) R y)
        (Iic b) b := by
      simp only [hnorm]
      apply ContinuousWithinAt.sqrt
      apply tendsto_finsetSum
      intro slots _
      exact (continuousWithinAt_const.sub
        (solution_metricCovDeriv_component_continuousWithinAt_terminal S hS hab hslab
          (Ioo_subset_Ico_self.trans hreg) R q y basis slots)).pow 2
    have heq : (fun t => metricDerivNorm q ((g s).restrictOpen U) (S.base.metric t) R y) =
        (fun t => metricDerivNorm q (g s) (g t) gRef x) := by
      funext t
      change metricDerivNorm q ((g s).restrictOpen U) (S.family.metric t) R y = _
      rw [hmet t]
      exact metricDerivNorm_restrictOpen (g s) (g t) gRef U q y
    rwa [heq] at hc
  have hright (s : ℝ) (hs : s ∈ Ico a b) (x : M) (hx : x ∈ U) :
      metricDerivNorm q (g s) (g b) gRef x ≤ L * |s - b| := by
    have hleft := (hterminal s x hx).mono Iio_subset_Iic_self
    have hright : Tendsto (fun t : ℝ => L * |s - t|) (𝓝[<] b) (𝓝 (L * |s - b|)) :=
      (continuousAt_const.mul (continuousAt_const.sub continuousAt_id).abs).tendsto.mono_left
        nhdsWithin_le_nhds
    apply le_of_tendsto_of_tendsto hleft hright
    filter_upwards [Ico_mem_nhdsLT hab] with t ht
    exact hinter s hs t ht x hx
  intro s hs t ht x hx
  rcases hs.2.lt_or_eq with hsb | hsb
  · rcases ht.2.lt_or_eq with htb | htb
    · exact hinter s ⟨hs.1, hsb⟩ t ⟨ht.1, htb⟩ x hx
    · subst t
      exact hright s ⟨hs.1, hsb⟩ x hx
  · subst s
    rcases ht.2.lt_or_eq with htb | htb
    · rw [metricDerivNorm_symm, abs_sub_comm]
      exact hright t ⟨ht.1, htb⟩ x hx
    · subst t
      rw [metricDerivNorm_self, sub_self, abs_zero, mul_zero]

end DifferentialGeometry.PDE.RicciFlow

end

end

section

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open Set Filter
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff ENNReal _root_.Topology

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem StaticTerminalLimit.eventually_metric_time_lipschitz_of_local_pullbacks
    {X : FlowSequence.{u}} {depthBound : ℝ} (L : StaticTerminalLimit X depthBound)
    {width : ℝ} (hw : 0 < width) (hwd : width < depthBound)
    (G : ℕ → ℝ → SmoothRiemannianMetric I3 L.space.M)
    (hG : ∀ K : Set L.space.M, IsCompact K → ∀ᶠ i in atTop,
      ∃ U : Set L.space.M, IsOpen U ∧ K ⊆ U ∧
        U ⊆ (L.maps.partialDiffeomorph i).source ∧
        ∀ t : ℝ, ∀ x ∈ U, ∀ v w : TangentSpace I3 x,
          (G i t).inner x v w = ((X.term (L.subseq i)).S.base.metric t).inner
            (L.maps.partialDiffeomorph i x)
            (mfderiv I3 I3 (L.maps.partialDiffeomorph i) x v)
            (mfderiv I3 I3 (L.maps.partialDiffeomorph i) x w)) :
    ∀ K : Set L.space.M, IsCompact K → ∀ p : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ i in atTop,
        ∀ s ∈ Icc (-width) 0, ∀ t ∈ Icc (-width) 0, ∀ q ≤ p, ∀ x ∈ K,
          metricDerivNorm q (G i s) (G i t) L.space.metric x ≤ C * |s - t| := by
  classical
  intro K hK p
  let _ : LocallyCompactSpace L.space.M := Manifold.locallyCompact_of_finiteDimensional I3
  obtain ⟨Kbig, hKbig, hKint, _hbig⟩ := exists_compact_between hK isOpen_univ (subset_univ K)
  let U : TopologicalSpace.Opens L.space.M := ⟨interior Kbig, isOpen_interior⟩
  let _ : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I3 U.isOpen)
  obtain ⟨B, hB, hBsource⟩ := L.eventually_metric_uniformly_equivalent_on_compact hKbig hw hwd
  have hBbound : ∀ᶠ i in atTop, ∀ t ∈ Icc (-width) 0,
      MetricUniformEquivalentOn Kbig L.space.metric (G i t) B := by
    filter_upwards [hBsource, hG Kbig hKbig] with i hi hj
    obtain ⟨V, hV, hKV, hVs, hmet⟩ := hj
    intro t ht
    refine ⟨hB, ?_⟩
    intro x hx v
    rw [hmet t x (hKV hx) v v]
    exact hi.2 t ht x hx v
  obtain ⟨A, _hA0, hsourceJets⟩ := L.source_curvature_jets_uniform_on_compact hw hwd hKbig
  have hA : ∀ᶠ i in atTop, ∀ q ≤ p, ∀ t ∈ Icc (-width) 0, ∀ x ∈ Kbig,
      curvDerivNorm q (G i t) x ≤ A q := by
    filter_upwards [hsourceJets, hG Kbig hKbig] with i hi hj
    obtain ⟨V, hV, hKV, hVs, hmet⟩ := hj
    intro q _hq t ht x hx
    rw [curvDerivNorm_eq_of_local_pullback (G i t) ((X.term (L.subseq i)).S.base.metric t)
      (L.maps.partialDiffeomorph i) ⟨V, hV⟩ hVs (hmet t) q ⟨x, hKV hx⟩]
    dsimp only [curvDerivNorm]
    rw [curvNormSq_eq]
    exact hi q t ht x hx
  obtain ⟨KShi, hKShi, hShiOf⟩ := exists_movingShiBoundOn_constant_of_curvature_derivative_bounds
    (I := I3) (M := L.space.M) p A
  obtain ⟨C, _hC, hCbound⟩ := L.eventually_covariant_bounds_of_local_pullbacks hw hwd G hG Kbig hKbig p
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((hG Kbig hKbig).and (hBbound.and (hA.and hCbound)))
  let gSeq : ℕ → ℝ → SmoothRiemannianMetric I3 L.space.M := fun i t => G (i + N) t
  have hgate (i : ℕ) := hN (i + N) (by omega)
  have hUmap (i : ℕ) : (U : Set L.space.M) ⊆ (L.maps.partialDiffeomorph (i + N)).source :=
    interior_subset.trans ((hgate i).1.choose_spec.2.1.trans (hgate i).1.choose_spec.2.2.1)
  have hpair (i : ℕ) (t : ℝ) (x : L.space.M) (hx : x ∈ U)
      (v w : TangentSpace I3 x) :
      (gSeq i t).inner x v w = ((X.term (L.subseq (i + N))).S.base.metric t).inner
        (L.maps.partialDiffeomorph (i + N) x)
        (mfderiv I3 I3 (L.maps.partialDiffeomorph (i + N)) x v)
        (mfderiv I3 I3 (L.maps.partialDiffeomorph (i + N)) x w) :=
    (hgate i).1.choose_spec.2.2.2 t x
      ((hgate i).1.choose_spec.2.1 (interior_subset hx)) v w
  have hflow (i : ℕ) : ∃ S : SolutionOn (I := I3) (M := U) (X.interval (L.subseq (i + N))),
      IsSolutionOn S ∧ ∀ t : ℝ, S.family.metric t = (gSeq i t).restrictOpen U :=
    KappaSolutions.exists_local_solution_of_pullback
      (X.term (L.subseq (i + N))).S (X.term (L.subseq (i + N))).isSolution
      (L.maps.partialDiffeomorph (i + N)) U (hUmap i) (gSeq i) (hpair i)
  have hcarrier (i : ℕ) : Icc (-depthBound) 0 ⊆ (X.interval (L.subseq (i + N))).carrier :=
    L.carrier_window _
  have hregular (i : ℕ) : Ioo (-depthBound) 0 ⊆ (X.interval (L.subseq (i + N))).regular :=
    L.regular_window _
  choose S hS hmet using hflow
  have hex : ∀ q : Fin (p + 1), ∃ Lt : ℝ, 0 ≤ Lt ∧
      ∀ i, ∀ s ∈ Icc (-width) 0, ∀ t ∈ Icc (-width) 0, ∀ x ∈ U,
        metricDerivNorm (I := I3) q (gSeq i s) (gSeq i t) L.space.metric x ≤
          Lt * |s - t| := by
    intro q
    obtain ⟨Lt, hLt, hLip⟩ := exists_metric_time_lipschitz_constant_of_local_solution
      U L.space.metric hB p (fun _ => C) hKShi q (Nat.le_of_lt_succ q.isLt)
    refine ⟨Lt, hLt, ?_⟩
    intro i s hs t ht x hx
    apply hLip (gSeq i) _ (S i) (hS i) (hmet i)
      (show -width < 0 by linarith)
      (fun t ht => hcarrier i ⟨by linarith [ht.1], ht.2⟩)
      (fun t ht => hregular i ⟨by linarith [ht.1], ht.2⟩)
      (fun t ht => ⟨hB, fun x hx v =>
        (hgate i).2.1 t (Ico_subset_Icc_self ht) |>.2 x (interior_subset hx) v⟩)
      (fun q _hq hqp t ht x hx =>
        (hgate i).2.2.2 q hqp t (Ico_subset_Icc_self ht) x (interior_subset hx))
      ?_ s hs t ht x hx
    intro psi hpsi r hr _j t ht x hx
    exact hShiOf gSeq U (-width) 0
      (fun q hq i t ht x hx => (hgate i).2.2.1 q hq t ht x (interior_subset hx))
      r hr i t ⟨ht.1, ht.2.trans hpsi.2.le⟩ x hx
  choose Lt hLt hLip using hex
  refine ⟨∑ q, Lt q, Finset.sum_nonneg (fun q _ => hLt q), ?_⟩
  filter_upwards [eventually_ge_atTop N] with i hi
  intro s hs t ht q hq x hx
  have hh := hLip ⟨q, Nat.lt_succ_of_le hq⟩ (i - N) s hs t ht x (hKint hx)
  have hle : Lt ⟨q, Nat.lt_succ_of_le hq⟩ ≤ ∑ r, Lt r :=
    Finset.single_le_sum (fun r _ => hLt r) (Finset.mem_univ _)
  have hfinal := hh.trans (mul_le_mul_of_nonneg_right hle (abs_nonneg _))
  simpa only [gSeq, Nat.sub_add_cancel hi] using hfinal

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

end
