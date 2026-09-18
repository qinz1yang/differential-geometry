import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Compactness.Construction
import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.Flat

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

theorem canonicalSourceData_derivNormSupOn_eq_of_open_pullback
    {X : PointedRiemannianSeq.{u, uE, uH} I}
    {P : PointedRiemannianManifold.{u, uE, uH} I} {f : ℕ → ℕ}
    (Psi : PointedRiemannianConvergenceMaps X P f) (i : ℕ)
    (U : TopologicalSpace.Opens P.M) (hUsrc : (U : Set P.M) ⊆ Psi.source i)
    (G : SmoothRiemannianMetric I U) (K : Set P.M) (hKU : K ⊆ U) (p : ℕ)
    (hG : ∀ (x : U) (v w : TangentSpace I x),
      G.inner x v w = (X.obj (f i)).metric.inner (Psi.map i x)
        (mfderiv I I (Psi.map i) x v) (mfderiv I I (Psi.map i) x w)) :
    (CanonicalMetricCompactness.canonicalSourceData Psi i).derivNormSupOn K p =
      metricDerivNormSupOn (Subtype.val ⁻¹' K) p G
        (P.metric.restrictOpen U) (P.metric.restrictOpen U) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let D := CanonicalMetricCompactness.canonicalSourceData Psi i
  let V : TopologicalSpace.Opens P.M := metricSourceOpenSubset Psi i
  let : SigmaCompactSpace V := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I V.isOpen)
  let A : SmoothRiemannianMetric I V := D.pullbackMetric
  have hA : A.restrictOpenOfSubset hUsrc = G := by
    apply SmoothRiemannianMetric.ext_inner
    intro y v w
    have hpull := D.pullback_inner (⟨y, hUsrc y.property⟩ : V) v w
    have hval : MDifferentiableAt I I (fun z : V => (z : P.M))
        (⟨y, hUsrc y.property⟩ : V) :=
      ((contMDiff_subtype_val (I := I) (U := V) (n := ∞)).contMDiffAt).mdifferentiableAt
        (by simp)
    have hPsi : MDifferentiableAt I I (Psi.map i) (y : P.M) :=
      (Psi.partialDiffeomorph i).mdifferentiableAt (by simp) (hUsrc y.property)
    have hderiv (z : TangentSpace I y) :
        mfderiv I I (fun q : V => Psi.map i (q : P.M))
          (⟨y, hUsrc y.property⟩ : V) z = mfderiv I I (Psi.map i) (y : P.M) z := by
      exact (mfderiv_comp_apply (⟨y, hUsrc y.property⟩ : V) hPsi hval z).trans
        (congrArg (mfderiv I I (Psi.map i) (y : P.M))
          (mfderiv_subtype_val_apply (I := I) V (⟨y, hUsrc y.property⟩ : V) z))
    exact hpull.trans ((congrArg₂
      (fun v' w' => (X.obj (f i)).metric.inner (Psi.map i (y : P.M)) v' w')
      (hderiv v) (hderiv w)).trans (hG y v w).symm)
  have hreference : (P.metric.restrictOpen V).restrictOpenOfSubset hUsrc =
      P.metric.restrictOpen U := by
    apply SmoothRiemannianMetric.ext_inner
    intro y v w
    rfl
  have hpt (y : U) (a : ℕ) :
      metricDerivNorm a A (P.metric.restrictOpen V) (P.metric.restrictOpen V)
          (⟨y, hUsrc y.property⟩ : V) =
        metricDerivNorm a G (P.metric.restrictOpen U) (P.metric.restrictOpen U) y := by
    have h := metricDerivNorm_flat hUsrc A (P.metric.restrictOpen V)
      (P.metric.restrictOpen V) a y
    rw [hA, hreference] at h
    exact h.symm
  change metricDerivNormSupOn (Subtype.val ⁻¹' K : Set V) p
    A (P.metric.restrictOpen V) (P.metric.restrictOpen V) = _
  unfold metricDerivNormSupOn
  congr 1
  ext r
  constructor
  · rintro ⟨a, ha, y, hy, hr⟩
    let z : U := ⟨y, hKU hy⟩
    exact ⟨a, ha, z, hy, (hpt z a).symm.trans hr⟩
  · rintro ⟨a, ha, y, hy, hr⟩
    exact ⟨a, ha, (⟨y, hUsrc y.property⟩ : V), hy, (hpt y a).trans hr⟩

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
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let V : TopologicalSpace.Opens P.M := ⟨U, hU⟩
  let : SigmaCompactSpace V := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I V.isOpen)
  rw [canonicalSourceData_derivNormSupOn_eq_of_open_pullback Psi k V hUsrc
    (G.restrictOpen V) K hKU p (fun x v w => hG x x.property v w),
    metricDerivNormSupOn_restrictOpen]
  have himage : (Subtype.val : V → P.M) '' (Subtype.val ⁻¹' K) = K := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hKU hx⟩, hx, rfl⟩
  rw [himage]


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

theorem exists_canonicalMetricConvergenceData_of_local_pullback
    {X : PointedRiemannianSeq.{u, uE, uH} I}
    {P : PointedRiemannianManifold.{u, uE, uH} I} {f : ℕ → ℕ}
    (Psi : PointedRiemannianConvergenceMaps X P f)
    (hlocal : ∀ K : Set P.M, IsCompact K →
      ∃ U : TopologicalSpace.Opens P.M, K ⊆ U ∧
        ∃ G : ℕ → SmoothRiemannianMetric I U,
          MetricCInfConvergenceOnCompacts G (P.metric.restrictOpen U) (P.metric.restrictOpen U) ∧
          ∀ᶠ i in atTop, (U : Set P.M) ⊆ Psi.source i ∧
            ∀ (x : U) (v w : TangentSpace I x),
              (G i).inner x v w = (X.obj (f i)).metric.inner (Psi.map i x)
                (mfderiv I I (Psi.map i) x v) (mfderiv I I (Psi.map i) x w)) :
    ∃ C : MetricConvergenceData Psi,
      ∀ i, C.domain i = CanonicalMetricCompactness.canonicalSourceData Psi i := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨C, hC, _href⟩ := exists_metricConvergenceData_canonicalSourceData Psi (by
    intro K hK p epsilon hepsilon
    obtain ⟨U, hKU, G, hconv, hG⟩ := hlocal K hK
    have hK' : IsCompact ((Subtype.val : U → P.M) ⁻¹' K) :=
      Topology.IsInducing.subtypeVal.isCompact_preimage' hK
        (by simpa only [Subtype.range_coe_subtype, Set.ofPred_mem_eq] using hKU)
    obtain ⟨N, hN⟩ := hconv _ hK' p epsilon hepsilon
    obtain ⟨J, hJ⟩ := eventually_atTop.mp hG
    refine ⟨max N J, fun i hi => ?_⟩
    have hJi := hJ i ((le_max_right _ _).trans hi)
    rw [canonicalSourceData_derivNormSupOn_eq_of_open_pullback
      Psi i U hJi.1 (G i) K hKU p hJi.2]
    exact hN i ((le_max_left _ _).trans hi))
  exact ⟨C, hC⟩

end DifferentialGeometry.CheegerGromovCompactness

end
