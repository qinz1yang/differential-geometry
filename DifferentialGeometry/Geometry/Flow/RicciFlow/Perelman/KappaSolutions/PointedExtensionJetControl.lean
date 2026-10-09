import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedDomainMetricConvergence
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Self


set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter Set
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
  {L : PointedRiemannianManifold.{u, uE, uH} (I := I)} {phi : ℕ → ℕ}

private local instance extensionJetTopology : TopologicalSpace L.M := L.topology
private local instance extensionJetCharted : ChartedSpace H L.M := L.charted
private local instance extensionJetSmooth : IsManifold I ∞ L.M := L.smooth
private local instance extensionJetT2 : T2Space L.M := L.t2
private local instance extensionJetSigma : SigmaCompactSpace L.M := L.sigmaCompact
private local instance extensionJetSourceTopology (i : ℕ) :
    TopologicalSpace (X.obj i).M := (X.obj i).topology
private local instance extensionJetSourceCharted (i : ℕ) :
    ChartedSpace H (X.obj i).M := (X.obj i).charted
private local instance extensionJetSourceSmooth (i : ℕ) :
    IsManifold I ∞ (X.obj i).M := (X.obj i).smooth
private local instance extensionJetSourceT2 (i : ℕ) : T2Space (X.obj i).M := (X.obj i).t2


theorem canonicalSource_extension_sup_eq
    (Phi : PointedRiemannianConvergenceMaps (I := I) X L phi) (i : ℕ)
    (g : SmoothRiemannianMetric I L.M) (U : TopologicalSpace.Opens L.M)
    (hU : (U : Set L.M) ⊆ Phi.source i)
    (hmet : ∀ x ∈ U, ∀ v w : TangentSpace I x,
      g.inner x v w = (X.obj (phi i)).metric.inner (Phi.map i x)
        (mfderiv I I (Phi.map i) x v) (mfderiv I I (Phi.map i) x w))
    (K : Set L.M) (hKU : K ⊆ U) (p : ℕ) :
    metricDerivNormSupOn (I := I) K p g L.metric L.metric =
      (CanonicalMetricCompactness.canonicalSourceData Phi i).derivNormSupOn
        (I := I) K p := by
  let : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I U.isOpen)
  let e : L.M ≃ₘ⟮I, I⟯ L.M := _root_.Diffeomorph.refl I L.M ∞
  have hU' : e '' (U : Set L.M) ⊆ Phi.source i := by
    rintro _ ⟨x, hx, rfl⟩
    exact hU hx
  let hf := pointedMaps_restrict_isSmoothEmbedding Phi e U i hU'
  have hmetric : g.restrictOpen (I := I) U =
      immersionInducedMetric (X.obj (phi i)).metric hf.isImmersion := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    have hval : MDifferentiableAt I I (Subtype.val : U → L.M) x :=
      (contMDiff_subtype_val (I := I) (U := U) (n := ∞)).mdifferentiable
        (by decide) x
    have hPhi : MDifferentiableAt I I (Phi.map i) (x : L.M) :=
      (Phi.partialDiffeomorph i).mdifferentiableAt (by decide) (hU x.property)
    have hd (z : TangentSpace I x) :
        mfderiv I I (fun y : U => Phi.map i (e y)) x z =
          mfderiv I I (Phi.map i) (x : L.M) z := by
      have hc := mfderiv_comp_apply x hPhi hval z
      exact hc.trans (congrArg (mfderiv I I (Phi.map i) (x : L.M))
        (mfderiv_subtype_val_apply (I := I) U x z))
    rw [SmoothRiemannianMetric.restrictOpen_inner, immersionInducedMetric_inner]
    exact (hmet (x : L.M) x.property v w).trans
      (congrArg₂ (fun v' w' => (X.obj (phi i)).metric.inner (Phi.map i (x : L.M))
        v' w') (hd v) (hd w)).symm
  have hlimit : Diffeomorph.pullbackMetricCross L.metric e = L.metric := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    rw [Diffeomorph.pullbackMetricCross_inner]
    change L.metric.inner x (mfderiv I I id x v) (mfderiv I I id x w) =
      L.metric.inner x v w
    rw [mfderiv_id]
    rfl
  let KU : Set U := {x | (x : L.M) ∈ K}
  have himage : (Subtype.val : U → L.M) '' KU = K := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hKU hx⟩, hx, rfl⟩
  have heimage : e '' ((Subtype.val : U → L.M) '' KU) = K := by
    rw [himage]
    exact Set.image_id K
  have hs := canonicalSource_fixedDomain_sup_eq Phi e U i hU' KU p
  rw [← hmetric, hlimit, metricDerivNormSupOn_restrictOpen, heimage, himage] at hs
  exact hs


theorem eventually_pointed_extension_metric_close
    (Phi : PointedRiemannianConvergenceMaps (I := I) X L phi)
    (C : MetricConvergenceData (I := I) Phi)
    (hcanonical : ∀ i, C.domain i = CanonicalMetricCompactness.canonicalSourceData Phi i)
    (g : ℕ → SmoothRiemannianMetric I L.M) (K : Set L.M) (hK : IsCompact K)
    (hmet : ∀ᶠ i in atTop, ∃ U : TopologicalSpace.Opens L.M,
      K ⊆ U ∧ (U : Set L.M) ⊆ Phi.source i ∧
      ∀ x ∈ U, ∀ v w : TangentSpace I x,
        (g i).inner x v w = (X.obj (phi i)).metric.inner (Phi.map i x)
          (mfderiv I I (Phi.map i) x v) (mfderiv I I (Phi.map i) x w))
    (p : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ i in atTop, metricDerivNormSupOn (I := I) K p (g i) L.metric L.metric <
      epsilon := by
  obtain ⟨N, hN⟩ := C.converges K hK p epsilon hepsilon
  filter_upwards [hmet, Filter.eventually_ge_atTop N] with i hi hNi
  obtain ⟨U, hKU, hU, hpair⟩ := hi
  rw [canonicalSource_extension_sup_eq Phi i (g i) U hU hpair K hKU p]
  rw [← hcanonical i]
  exact (hN i hNi).2


theorem eventually_pointed_extension_positive_covariant_bound
    (Phi : PointedRiemannianConvergenceMaps (I := I) X L phi)
    (C : MetricConvergenceData (I := I) Phi)
    (hcanonical : ∀ i, C.domain i = CanonicalMetricCompactness.canonicalSourceData Phi i)
    (g : ℕ → SmoothRiemannianMetric I L.M) (K : Set L.M) (hK : IsCompact K)
    (hmet : ∀ᶠ i in atTop, ∃ U : TopologicalSpace.Opens L.M,
      K ⊆ U ∧ (U : Set L.M) ⊆ Phi.source i ∧
      ∀ x ∈ U, ∀ v w : TangentSpace I x,
        (g i).inner x v w = (X.obj (phi i)).metric.inner (Phi.map i x)
          (mfderiv I I (Phi.map i) x v) (mfderiv I I (Phi.map i) x w))
    (p : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ i in atTop, ∀ q : ℕ, 1 ≤ q → q ≤ p → ∀ x ∈ K,
      metricCovDerivNorm (I := I) q (g i) L.metric x ≤ epsilon := by
  filter_upwards [eventually_pointed_extension_metric_close Phi C hcanonical
    g K hK hmet p epsilon hepsilon] with i hi
  intro q hq hqp x hx
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
  have hbound := covNorm_le_add (I := I) (r + 1) (g i) L.metric L.metric x
  rw [covNorm_self_succ, zero_add] at hbound
  exact hbound.trans ((derivNorm_le_sup (I := I) hK hqp
    (g i) L.metric L.metric hx).trans hi.le)

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
