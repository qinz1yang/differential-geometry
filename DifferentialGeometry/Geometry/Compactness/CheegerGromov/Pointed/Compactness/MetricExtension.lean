import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Compactness.Construction
import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.Locality

section

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open scoped Manifold ContDiff Topology BigOperators
open DifferentialGeometry.Geometry.Curvature

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

section CanonicalSourceData

variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
variable {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
variable {phi : ℕ → ℕ}

omit [I.Boundaryless] in
theorem exists_metricConvergenceData_canonicalSourceData
    (Ψ : PointedRiemannianConvergenceMaps (I := I) X L phi)
    (hconv : ∀ K : Set L.M,
      (letI : TopologicalSpace L.M := L.topology; IsCompact K) →
      ∀ p : ℕ, ∀ ε : ℝ, 0 < ε → ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
        (CanonicalMetricCompactness.canonicalSourceData (I := I) Ψ k).derivNormSupOn
          (I := I) K p < ε) :
    ∃ C : MetricConvergenceData (I := I) Ψ,
      (∀ k : ℕ, C.domain k = CanonicalMetricCompactness.canonicalSourceData (I := I) Ψ k) ∧
      (∀ k : ℕ,
        let D := C.domain k
        letI : TopologicalSpace (MetricSourceDomain (I := I) Ψ k) := D.topology
        letI : ChartedSpace H (MetricSourceDomain (I := I) Ψ k) := D.charted
        letI : IsManifold I ∞ (MetricSourceDomain (I := I) Ψ k) := D.smooth
        D.referenceMetric = D.limitMetric) := by
  classical
  refine ⟨⟨fun k => CanonicalMetricCompactness.canonicalSourceData (I := I) Ψ k,
    fun K hK p ε hε => ?_⟩, fun k => rfl, fun k => ?_⟩
  · obtain ⟨k0, hk0⟩ := hconv K hK p ε hε
    obtain ⟨kS, hS⟩ := Ψ.source_subset hK
    refine ⟨max kS k0, fun k hk => ⟨hS k (le_trans (Nat.le_max_left _ _) hk),
      hk0 k (le_trans (Nat.le_max_right _ _) hk)⟩⟩
  · with_unfolding_all
    rfl

omit [I.Boundaryless] [CompleteSpace E] in
theorem canonicalSourceData_referenceMetric_eq_limitMetric
    (Ψ : PointedRiemannianConvergenceMaps (I := I) X L phi) (k : ℕ) :
    let D := CanonicalMetricCompactness.canonicalSourceData (I := I) Ψ k
    letI : TopologicalSpace (MetricSourceDomain (I := I) Ψ k) := D.topology
    letI : ChartedSpace H (MetricSourceDomain (I := I) Ψ k) := D.charted
    letI : IsManifold I ∞ (MetricSourceDomain (I := I) Ψ k) := D.smooth
    D.referenceMetric = D.limitMetric := by
  with_unfolding_all
    rfl

omit [I.Boundaryless] in
theorem exists_metricConvergenceData_canonicalSourceData_iff
    (Ψ : PointedRiemannianConvergenceMaps (I := I) X L phi) :
    (∃ C : MetricConvergenceData (I := I) Ψ,
      (∀ k : ℕ, C.domain k = CanonicalMetricCompactness.canonicalSourceData (I := I) Ψ k) ∧
      (∀ k : ℕ,
        let D := C.domain k
        letI : TopologicalSpace (MetricSourceDomain (I := I) Ψ k) := D.topology
        letI : ChartedSpace H (MetricSourceDomain (I := I) Ψ k) := D.charted
        letI : IsManifold I ∞ (MetricSourceDomain (I := I) Ψ k) := D.smooth
        D.referenceMetric = D.limitMetric)) ↔
      (∀ K : Set L.M,
        (letI : TopologicalSpace L.M := L.topology; IsCompact K) →
        ∀ p : ℕ, ∀ ε : ℝ, 0 < ε → ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
          (CanonicalMetricCompactness.canonicalSourceData (I := I) Ψ k).derivNormSupOn
            (I := I) K p < ε) := by
  constructor
  · rintro ⟨C, hC, _⟩ K hK p ε hε
    obtain ⟨k0, hk0⟩ := C.converges K hK p ε hε
    refine ⟨k0, fun k hk => ?_⟩
    obtain ⟨_, hlt⟩ := hk0 k hk
    rwa [hC k] at hlt
  · intro hconv
    obtain ⟨C, hC, _⟩ :=
      exists_metricConvergenceData_canonicalSourceData (I := I) Ψ hconv
    refine ⟨C, hC, fun k => ?_⟩
    rw [hC k]
    exact canonicalSourceData_referenceMetric_eq_limitMetric (I := I) Ψ k

end CanonicalSourceData

end CheegerGromovCompactness
end DifferentialGeometry

end

end

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Filter Set
open scoped Manifold ContDiff _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type uH} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact

theorem canonicalSourceData_derivNormSupOn_eq_of_pullback
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {phi : ℕ → ℕ}
    (Psi : PointedRiemannianConvergenceMaps X P phi) (k : ℕ)
    (G : SmoothRiemannianMetric I P.M) (K U : Set P.M) (p : ℕ)
    (hU : IsOpen U) (hKU : K ⊆ U) (hUsrc : U ⊆ Psi.source k)
    (hG : ∀ x ∈ U, ∀ v w : TangentSpace I x,
      G.inner x v w = (X.obj (phi k)).metric.inner (Psi.map k x)
        (mfderiv I I (Psi.map k) x v) (mfderiv I I (Psi.map k) x w)) :
    (CanonicalMetricCompactness.canonicalSourceData Psi k).derivNormSupOn K p =
      metricDerivNormSupOn K p G P.metric P.metric := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let D := CanonicalMetricCompactness.canonicalSourceData Psi k
  let V : TopologicalSpace.Opens P.M := metricSourceOpenSubset Psi k
  let : ChartedSpace H V := TopologicalSpace.Opens.instChartedSpace (H := H) (M := P.M)
    (s := V)
  let : IsManifold I ∞ V := { V.instHasGroupoid (contDiffGroupoid ∞ I) with }
  let : SigmaCompactSpace V := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I V.isOpen)
  let A : SmoothRiemannianMetric I V := D.pullbackMetric
  have hpt (x : V) (hx : (x : P.M) ∈ K) (a : ℕ) :
      metricDerivNorm a A (P.metric.restrictOpen V) (P.metric.restrictOpen V) x =
        metricDerivNorm a G P.metric P.metric (x : P.M) := by
    have hlocal : ∀ᶠ y in 𝓝 x, ∀ v w : TangentSpace I y,
        A.inner y v w = (G.restrictOpen V).inner y v w := by
      have hmem : ∀ᶠ y : V in 𝓝 x, (y : P.M) ∈ U :=
        (hU.preimage continuous_subtype_val).mem_nhds (hKU hx)
      filter_upwards [hmem] with y hy
      intro v w
      rw [SmoothRiemannianMetric.restrictOpen_inner]
      have hval : MDifferentiableAt I I (fun z : V => (z : P.M)) y :=
        ((contMDiff_subtype_val (I := I) (U := V) (n := ∞)).contMDiffAt).mdifferentiableAt
          (by simp)
      have hPsi : MDifferentiableAt I I (Psi.map k) (y : P.M) :=
        (Psi.partialDiffeomorph k).mdifferentiableAt (by simp) y.property
      have hderiv (z : TangentSpace I y) :
          mfderiv I I (fun w : V => Psi.map k (w : P.M)) y z =
            mfderiv I I (Psi.map k) (y : P.M) z := by
        exact (mfderiv_comp_apply y hPsi hval z).trans
          (congrArg (mfderiv I I (Psi.map k) (y : P.M))
            (mfderiv_subtype_val_apply (I := I) V y z))
      have hpull := D.pullback_inner y v w
      exact hpull.trans ((congrArg₂
        (fun v' w' => (X.obj (phi k)).metric.inner (Psi.map k (y : P.M)) v' w')
        (hderiv v) (hderiv w)).trans (hG y hy v w).symm)
    calc
      metricDerivNorm a A (P.metric.restrictOpen V) (P.metric.restrictOpen V) x =
          metricDerivNorm a (G.restrictOpen V)
            (P.metric.restrictOpen V) (P.metric.restrictOpen V) x :=
        metricDerivNorm_eq_of_metric_eventuallyEq a _ _ _ _ x hlocal
      _ = metricDerivNorm a G P.metric P.metric (x : P.M) :=
        metricDerivNorm_restrictOpen G P.metric P.metric V a x
  change metricDerivNormSupOn (Subtype.val ⁻¹' K : Set V) p
    A (P.metric.restrictOpen V) (P.metric.restrictOpen V) = _
  unfold metricDerivNormSupOn
  congr 1
  ext r
  constructor
  · rintro ⟨a, ha, x, hx, hr⟩
    exact ⟨a, ha, (x : P.M), hx, (hpt x hx a).symm.trans hr⟩
  · rintro ⟨a, ha, x, hx, hr⟩
    let y : V := ⟨x, hUsrc (hKU hx)⟩
    exact ⟨a, ha, y, hx, (hpt y hx a).trans hr⟩


theorem exists_canonicalMetricConvergenceData_of_metric_extension
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {phi : ℕ → ℕ}
    (Psi : PointedRiemannianConvergenceMaps X P phi)
    (G : ℕ → SmoothRiemannianMetric I P.M)
    (hconv : MetricCInfConvergenceOnCompacts G P.metric P.metric)
    (hG : ∀ K : Set P.M, IsCompact K → ∀ᶠ k in atTop,
      ∃ U : Set P.M, IsOpen U ∧ K ⊆ U ∧ U ⊆ Psi.source k ∧
        ∀ x ∈ U, ∀ v w : TangentSpace I x,
          (G k).inner x v w = (X.obj (phi k)).metric.inner (Psi.map k x)
            (mfderiv I I (Psi.map k) x v) (mfderiv I I (Psi.map k) x w)) :
    ∃ C : MetricConvergenceData Psi,
      (∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData Psi k) ∧
      (∀ k,
        let D := C.domain k
        letI : TopologicalSpace (MetricSourceDomain Psi k) := D.topology
        letI : ChartedSpace H (MetricSourceDomain Psi k) := D.charted
        letI : IsManifold I ∞ (MetricSourceDomain Psi k) := D.smooth
        D.referenceMetric = D.limitMetric) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  apply exists_metricConvergenceData_canonicalSourceData Psi
  intro K hK p epsilon hepsilon
  obtain ⟨N, hN⟩ := hconv K hK p epsilon hepsilon
  obtain ⟨J, hJ⟩ := eventually_atTop.mp (hG K hK)
  refine ⟨max N J, fun k hk => ?_⟩
  obtain ⟨U, hU, hKU, hUsrc, hGk⟩ := hJ k ((le_max_right N J).trans hk)
  rw [canonicalSourceData_derivNormSupOn_eq_of_pullback Psi k (G k) K U p
    hU hKU hUsrc hGk]
  exact hN k ((le_max_left N J).trans hk)

end DifferentialGeometry.CheegerGromovCompactness

end
