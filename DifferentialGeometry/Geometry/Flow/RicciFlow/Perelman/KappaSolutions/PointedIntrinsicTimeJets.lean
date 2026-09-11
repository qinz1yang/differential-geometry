import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedUniformTimeJets
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.UniformCovariantTensorNorm
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CompactPointedChartControl
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedMetricErrorJets


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.Tensor.Coordinates
open Bundle Filter Set
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open CanonicalNeighborhood
open scoped Manifold ContDiff _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

private local instance pointedIntrinsicTimeC1 {D : RealTimeInterval}
    (L : PointedFlowData.{u, uE, uH} (I := I) D) : IsManifold I 1 L.M :=
  IsManifold.of_le (I := I) (M := L.M) (n := ∞) (by decide)


theorem pointed_error_jets_uniform_on_compacts
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {L : PointedFlowData.{u, uE, uH} (I := I) X.D} {phi : ℕ → ℕ}
    (hdim : Module.finrank ℝ E = 3)
    (Phi : PointedCGHMaps (I := I) X (L.atTime (I := I) 0) phi)
    {κ : ℝ} (hsource : ∀ i, KLim (I := I) κ (X.term i))
    (hnormalized : ∀ i, (X.term i).S.scalar 0 (X.term i).basepoint = 1)
    (hcomplete : MetricComplete (I := I) (L.atTime (I := I) 0))
    (hconnected : ConnectedSpace L.M)
    (G : ℕ → ℝ → SmoothRiemannianMetric I L.M)
    (hG : ∀ K : Set L.M, IsCompact K → ∀ᶠ i in atTop,
      ∃ U : Set L.M, IsOpen U ∧ K ⊆ U ∧ U ⊆ Phi.source i ∧
      ∀ t : ℝ, ∀ x ∈ U, ∀ v w : TangentSpace I x,
        (G i t).inner x v w = ((X.term (phi i)).S.base.metric t).inner (Phi.map i x)
          (mfderiv I I (Phi.map i) x v) (mfderiv I I (Phi.map i) x w))
    (B : ℕ → ℕ → ℝ → Tensor0SField (I := I) (M := L.M) (n := ∞) 2)
    (C : ℕ → ℝ → Tensor0SField (I := I) (M := L.M) (n := ∞) 2)
    (hBzero : ∀ n s, B n 0 s = metricTensorField (G n s))
    (hCzero : ∀ s, C 0 s = metricTensorField (L.S.base.metric s))
    (hB : ∀ n q s, s ≤ 0 → ∀ x : L.M,
      HasDerivWithinAt (fun t => B n q t x) (B n (q + 1) s x) (Iic 0) s)
    (hC : ∀ q s, s ≤ 0 → ∀ x : L.M,
      HasDerivWithinAt (fun t => C q t x) (C (q + 1) s x) (Iic 0) s)
    {a : ℝ} (ha : a < 0)
    (hconv : ∀ t ∈ Icc a 0,
      ∃ D : MetricConvergenceData (I := I) (Phi.atTime (L := L) t),
        ∀ k, D.domain k = CanonicalMetricCompactness.canonicalSourceData
          (I := I) (Phi.atTime (L := L) t) k)
    (K : Set L.M) (hK : IsCompact K) (r q : ℕ) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ Icc a 0, ∀ x ∈ K,
      tensor02CovDerivNormWith (I := I) r (B n q t - C q t)
        (L.S.base.metric t) (L.S.base.metric t) x ≤ ε := by
  classical
  let : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  let : ConnectedSpace L.M := hconnected
  have hc : RiemannianMetricComplete (I := I) (L.S.base.metric 0) :=
    ⟨MetricComplete.complete (I := I) (L.atTime (I := I) 0) hcomplete⟩
  obtain ⟨V, hKV, hV, A, hA, hVA⟩ :=
    exists_precompact_bounded_comparison_open (L.S.base.metric 0) hc L.basepoint hK
  let F : ℕ → ℝ → Tensor0SField (I := I) (M := L.M) (n := ∞) 2 :=
    fun n t => B n q t - C q t
  apply uniform_on_compact_of_restricted_chart_bounds (I := I) V hK hKV
    (fun n t x => tensor02CovDerivNormWith (I := I) r (F n t)
      (L.S.base.metric t) (L.S.base.metric t) x) (Icc a 0)
  intro p Q hQ hQt
  have hU := isOpen_extChartAt_target (I := I) p
  have hUt := extChartAt_opens_target_subset (I := I) V p
  have hball : ∀ y ∈ (extChartAt I p).target, (extChartAt I (p : L.M)).symm y ∈
      riemannianClosedBallOf (I := I) (L.S.base.metric 0) L.basepoint A := by
    intro y hy
    rw [← extChartAt_opens_symm_coe (I := I) V p hy]
    exact hVA ((extChartAt I p).symm y).property
  have hcoord (slots : Fin 2 → Fin (Module.finrank ℝ E))
      (Q' : Set E) (hQ' : IsCompact Q') (hQ't : Q' ⊆ (extChartAt I p).target)
      (m : ℕ) (ε : ℝ) (hε : 0 < ε) :
      ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ Icc a 0, ∀ y ∈ Q',
        ‖iteratedFDeriv ℝ m (fun z => F n t ((extChartAt I (p : L.M)).symm z)
          (fun j => chartBasisVecFiber (I := I) (p : L.M) (slots j)
            ((extChartAt I (p : L.M)).symm z))) y‖ ≤ ε := by
    obtain ⟨N, hN⟩ := pointed_time_jets_uniform_on_closed_time hdim Phi hsource hnormalized
      hcomplete G hG B C hBzero hCzero hB hC ha hconv V hV p A hA.le hU
      (fun _ hy => hy) hball hQ' hQ't m q slots ε hε
    refine ⟨N, fun n hn t ht y hy => ?_⟩
    have hBc := tensor_field_chart_components_contDiffOn (B n q t) (p : L.M) hUt slots
    have hCc := tensor_field_chart_components_contDiffOn (C q t) (p : L.M) hUt slots
    have heq : (fun z => F n t ((extChartAt I (p : L.M)).symm z)
        (fun j => chartBasisVecFiber (I := I) (p : L.M) (slots j)
          ((extChartAt I (p : L.M)).symm z))) =
        (fun z => B n q t ((extChartAt I (p : L.M)).symm z)
          (fun j => chartBasisVecFiber (I := I) (p : L.M) (slots j)
            ((extChartAt I (p : L.M)).symm z)) -
        C q t ((extChartAt I (p : L.M)).symm z)
          (fun j => chartBasisVecFiber (I := I) (p : L.M) (slots j)
            ((extChartAt I (p : L.M)).symm z))) := by
      funext z
      rfl
    have hsub := iteratedFDeriv_sub_apply (i := m)
      ((hBc.contDiffAt (hU.mem_nhds (hQ't hy))).of_le (by exact_mod_cast le_top))
      ((hCc.contDiffAt (hU.mem_nhds (hQ't hy))).of_le (by exact_mod_cast le_top))
    rw [heq]
    have hh := hN n hn t ht y hy
    rw [← hsub] at hh
    exact hh
  exact uniform_tensor02_covariant_norm_on_compact_time L.S L.isSolution
    (hsource 0).carrier_eq (hsource 0).regular_eq isCompact_Icc
    (fun _ ht => ht.2) F (p : L.M) hU hUt hcoord hQ hQt r


theorem exists_pointed_uniform_error_jets
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {L : PointedFlowData.{u, uE, uH} (I := I) X.D} {phi : ℕ → ℕ}
    (hdim : Module.finrank ℝ E = 3)
    (Phi : PointedCGHMaps (I := I) X (L.atTime (I := I) 0) phi)
    {κ : ℝ} (hsource : ∀ i, KLim (I := I) κ (X.term i))
    (hnormalized : ∀ i, (X.term i).S.scalar 0 (X.term i).basepoint = 1)
    (hlimit : KLim (I := I) κ L)
    (hconv : ∀ t : ℝ, t ≤ 0 →
      ∃ D : MetricConvergenceData (I := I) (Phi.atTime (L := L) t),
        ∀ k, D.domain k = CanonicalMetricCompactness.canonicalSourceData
          (I := I) (Phi.atTime (L := L) t) k) :
    ∃ G : ℕ → ℝ → SmoothRiemannianMetric I L.M,
    ∃ J : ℕ → ℕ → ℝ → Tensor0SField (I := I) (M := L.M) (n := ∞) 2,
      (∀ i t, J i 0 t = metricTensorField (G i t) - metricTensorField (L.S.base.metric t)) ∧
      (∀ i q t, t ≤ 0 → ∀ x : L.M,
        HasDerivWithinAt (fun s => J i q s x) (J i (q + 1) t x) (Iic 0) t) ∧
      (∀ K : Set L.M, IsCompact K → ∀ᶠ i in atTop,
        ∃ U : Set L.M, IsOpen U ∧ K ⊆ U ∧ U ⊆ Phi.source i ∧
          ∀ t : ℝ, ∀ x ∈ U, ∀ v w : TangentSpace I x,
            (G i t).inner x v w = ((X.term (phi i)).S.base.metric t).inner (Phi.map i x)
              (mfderiv I I (Phi.map i) x v) (mfderiv I I (Phi.map i) x w)) ∧
      ∀ a : ℝ, a < 0 → ∀ K : Set L.M, IsCompact K → ∀ r q : ℕ,
        ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ i ≥ N, ∀ t ∈ Icc a 0, ∀ x ∈ K,
          tensor02CovDerivNormWith (I := I) r (J i q t)
            (L.S.base.metric t) (L.S.base.metric t) x ≤ ε := by
  let : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  obtain ⟨G, B, hBzero, hBderiv, hG⟩ :=
    exists_pointed_extension_time_jets Phi hlimit.carrier_eq hlimit.regular_eq
  obtain ⟨C, hCzero, hCderiv⟩ :=
    exists_ancient_ordinary_metric_time_jets L.S L.isSolution hlimit.carrier_eq hlimit.regular_eq
  let B' : ℕ → ℕ → ℝ → Tensor0SField (I := I) (M := L.M) (n := ∞) 2 := B
  let C' : ℕ → ℝ → Tensor0SField (I := I) (M := L.M) (n := ∞) 2 := C
  let J : ℕ → ℕ → ℝ → Tensor0SField (I := I) (M := L.M) (n := ∞) 2 :=
    fun i q t => B' i q t - C' q t
  refine ⟨G, J, ?_, ?_, hG, ?_⟩
  · intro i t
    change B' i 0 t - C' 0 t = _
    exact congrArg₂ (fun A C : Tensor0SField (I := I) (M := L.M) (n := ∞) 2 => A - C)
      (hBzero i t) (hCzero t)
  · intro i q t ht x
    change HasDerivWithinAt (fun s => B' i q s x - C' q s x)
      (B' i (q + 1) t x - C' (q + 1) t x) (Iic 0) t
    exact (hBderiv i q t ht x).sub (hCderiv q t ht x).2
  · intro a ha K hK r q
    exact pointed_error_jets_uniform_on_compacts hdim Phi hsource hnormalized
      (hlimit.complete 0 (by rw [hlimit.carrier_eq]; exact (le_rfl : (0 : ℝ) ≤ 0)))
      hlimit.connected G hG
      B' C' hBzero hCzero hBderiv (fun q t ht x => (hCderiv q t ht x).2)
      ha (fun t ht => hconv t ht.2) K hK r q

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
