import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Criterion
import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.CurvatureTrace
import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.TensorDecomposition
import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.DensityRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.CurvatureRegularity
import DifferentialGeometry.Analysis.Integration.Measure.FamilyContinuity
import DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetricIneq

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Manifold MeasureTheory Set DifferentialGeometry.Tensor0SBundle
open _root_.Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.RSTensor

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [T2Space M]
variable [CompactSpace M] [I.Boundaryless]

section SlabSup

variable {a c : Real}

omit [T2Space M] in
theorem slabBound (F : Real → M → Real)
    (hF : ContinuousOn (fun p : Real × M => F p.1 p.2) (Icc a c ×ˢ (univ : Set M))) :
    ∃ C : Real, 0 ≤ C ∧ ∀ t ∈ Icc a c, ∀ x : M, |F t x| ≤ C := by
  obtain ⟨C, hC⟩ :=
    (isCompact_Icc.prod (isCompact_univ : IsCompact (univ : Set M))).exists_bound_of_continuousOn hF
  refine ⟨max C 0, le_max_right _ _, fun t ht x => ?_⟩
  have h := hC (t, x) ⟨ht, mem_univ x⟩
  rw [Real.norm_eq_abs] at h
  exact h.trans (le_max_left _ _)

omit [T2Space M] in
theorem slabBound_ioo (F : Real → M → Real)
    (hF : ContinuousOn (fun p : Real × M => F p.1 p.2) (Icc a c ×ˢ (univ : Set M))) :
    ∃ C : Real, 0 ≤ C ∧ ∀ t ∈ Ioo a c, ∀ x : M, F t x ≤ C := by
  obtain ⟨C, hC0, hC⟩ := slabBound (M := M) F hF
  exact ⟨C, hC0, fun t ht x => (le_abs_self _).trans (hC t (Ioo_subset_Icc_self ht) x)⟩

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] in
theorem normSqSlabBound {s : Nat} (g : Real → SmoothRiemannianMetric I M)
    (A : Real → (x : M) → Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (hA : ContinuousOn (fun p : Real × M => normSq0S (I := I) (g p.1) p.2 s (A p.1 p.2))
      (Icc a c ×ˢ (univ : Set M))) :
    ∃ B : Real, 0 ≤ B ∧
      ∀ t ∈ Icc a c, ∀ x : M, normSq0S (I := I) (g t) x s (A t x) ≤ B := by
  obtain ⟨B, hB0, hB⟩ := slabBound (M := M) (fun t x => normSq0S (I := I) (g t) x s (A t x)) hA
  exact ⟨B, hB0, fun t ht x => (le_abs_self _).trans (hB t ht x)⟩

end SlabSup

section RicciField

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [CompactSpace M] [I.Boundaryless] in
theorem ricciSlabLe (g₁ g₂ : Real → SmoothRiemannianMetric I M) (t : Real) (x : M) :
    normSq0S (I := I) (g₁ t) x 2
        (metricRicciAt (I := I) (g₁ t) x - metricRicciAt (I := I) (g₂ t) x) ≤
      (Module.finrank Real E : Real) ^ 4 * forwardUniqueDensity (I := I) g₁ g₂ t x := by
  have hrep : normSq0S (I := I) (g₁ t) x 4
      ((rmDiffLowAt (I := I) (g₁ t) (g₂ t) x).domDomCongr rm04TraceSlots) ≤
      rmDiffSq (I := I) (g₁ t) (g₂ t) x + (0 : Real) * metricDiffSq (I := I) (g₁ t) (g₂ t) x := by
    rw [normSq_ricciTraceRep (I := I) (g₁ t) (g₂ t) x]
    exact le_of_eq (by ring)
  refine (ricciDiffSq_le (I := I) (g₁ t) (g₂ t) x
    ((rmDiffLowAt (I := I) (g₁ t) (g₂ t) x).domDomCongr rm04TraceSlots)
    (ricciDiff_eq_trace (I := I) (g₁ t) (g₂ t) x) hrep).trans ?_
  have hdens := rmDiffSq_le_dens (I := I) g₁ g₂ t x
  have hpow : (0 : Real) ≤ (Module.finrank Real E : Real) ^ 4 := by positivity
  nlinarith [hdens, hpow]

end RicciField

section FluxField

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [T2Space M] [CompactSpace M] [I.Boundaryless] in
private theorem onFrame_inv {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hON : ∀ i j, g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0) :
    MetricInverseInBasisGen (I := I) g x basis (identityInvMetric (Idx := Idx)) := by
  intro i j
  constructor <;> simp [identityInvMetric, diagonalInvMetric, hON]

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [CompactSpace M] [I.Boundaryless] in
theorem reLowerPairSq_le (g : SmoothRiemannianMetric I M) {s : ℕ}
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1))
    (K : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 3)
    (x : M) :
    normSq0S (I := I) g x (s + 2) (reLowerPair (I := I) g T K x) ≤
      (Module.finrank Real E : Real) ^ (s + 4) *
        (normSq0S (I := I) g x (s + 1) (T x) * normSq0S (I := I) g x 3 (K x)) := by
  classical
  obtain ⟨basis, hON⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis (I := I) g x
  have hinv := onFrame_inv (I := I) g basis hON
  have hprod : normSq0S (I := I) g x (s + 1 + 3)
      (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
        (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := s + 1) (q := 3) T K x) =
      normSq0S (I := I) g x (s + 1) (T x) * normSq0S (I := I) g x 3 (K x) :=
    normSq0S_product (I := I) g x basis hinv T K
  have hcongr : normSq0S (I := I) g x (s + 1 + 3)
      (ContinuousMultilinearMap.domDomCongr (reLowerPermutationWithThreeInputs s)
        (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
          (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := s + 1) (q := 3) T K x)) =
      normSq0S (I := I) g x (s + 1 + 3)
        (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
          (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := s + 1) (q := 3) T K x) :=
    normSq0S_domDomCongr (I := I) g x basis hinv (reLowerPermutationWithThreeInputs s) _
  have htr := traceNormSq_le (I := I) (s := s + 2) g x
    (ContinuousMultilinearMap.domDomCongr (reLowerPermutationWithThreeInputs s)
      (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
        (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := s + 1) (q := 3) T K x))
  rw [hcongr, hprod] at htr
  exact htr

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem sdecFluxSq_le (g₁ g₂ : SmoothRiemannianMetric I M)
    (Rm2 P : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (x : M) {B₂ BP Background : Real}
    (hB₂ : normSq0S (I := I) g₁ x 4 (Rm2 x) ≤ B₂)
    (hBP : normSq0S (I := I) g₁ x 4 (P x) ≤ BP)
    (hBackground : normSq0S (I := I) g₁ x 2 (metricTensorField (I := I) g₂ x) ≤ Background) :
    normSq0S (I := I) g₁ x 5 (sdecFlux (I := I) g₁ g₂ Rm2 P x) ≤
      32 * (Module.finrank Real E : Real) ^ 5 * connectionDifferenceSq (I := I) g₁ g₂ x * B₂ +
        8 * (Module.finrank Real E : Real) ^ 10 * connectionDifferenceSq (I := I) g₁ g₂ x * (BP * Background) := by
  classical
  have hcd : 0 ≤ connectionDifferenceSq (I := I) g₁ g₂ x := by
    rw [connectionDifferenceSq_def]; exact normSq0S_nonneg (I := I) g₁ x 3 _
  have hn : (0 : Real) ≤ (Module.finrank Real E : Real) := by positivity
  have hsplit : sdecFlux (I := I) g₁ g₂ Rm2 P x =
      lapDiffFlux (I := I) g₁ g₂ Rm2 x -
        reLowerPair (I := I) g₁ P
          (lapDiffFlux (I := I) g₁ g₂ (metricTensorField (I := I) g₂)) x := rfl
  rw [hsplit]
  refine (normSq0S_sub_le (I := I) g₁ x 5 _ _).trans ?_
  have hfirst : normSq0S (I := I) g₁ x 5 (lapDiffFlux (I := I) g₁ g₂ Rm2 x) ≤
      16 * (Module.finrank Real E : Real) ^ 5 * connectionDifferenceSq (I := I) g₁ g₂ x * B₂ := by
    refine (fluxNormSq_le (I := I) g₁ g₂ (s := 4) Rm2 x).trans ?_
    have hfac : (0 : Real) ≤ (4 : Real) ^ 2 * (Module.finrank Real E : Real) ^ 5 *
        connectionDifferenceSq (I := I) g₁ g₂ x := by positivity
    have h := mul_le_mul_of_nonneg_left hB₂ hfac
    calc (4 : Real) ^ 2 * (Module.finrank Real E : Real) ^ 5 *
            connectionDifferenceSq (I := I) g₁ g₂ x * normSq0S (I := I) g₁ x 4 (Rm2 x)
        ≤ (4 : Real) ^ 2 * (Module.finrank Real E : Real) ^ 5 *
            connectionDifferenceSq (I := I) g₁ g₂ x * B₂ := h
      _ = _ := by norm_num
  have hK : normSq0S (I := I) g₁ x 3
      (lapDiffFlux (I := I) g₁ g₂ (metricTensorField (I := I) g₂) x) ≤
      4 * (Module.finrank Real E : Real) ^ 3 * connectionDifferenceSq (I := I) g₁ g₂ x * Background := by
    refine (fluxNormSq_le (I := I) g₁ g₂ (s := 2) (metricTensorField (I := I) g₂) x).trans ?_
    have hfac : (0 : Real) ≤ (2 : Real) ^ 2 * (Module.finrank Real E : Real) ^ 3 *
        connectionDifferenceSq (I := I) g₁ g₂ x := by positivity
    have h := mul_le_mul_of_nonneg_left hBackground hfac
    calc (2 : Real) ^ 2 * (Module.finrank Real E : Real) ^ 3 *
            connectionDifferenceSq (I := I) g₁ g₂ x *
            normSq0S (I := I) g₁ x 2 (metricTensorField (I := I) g₂ x)
        ≤ (2 : Real) ^ 2 * (Module.finrank Real E : Real) ^ 3 *
            connectionDifferenceSq (I := I) g₁ g₂ x * Background := h
      _ = _ := by norm_num
  have hPnn : 0 ≤ normSq0S (I := I) g₁ x 4 (P x) := normSq0S_nonneg (I := I) g₁ x 4 _
  have hKnn : 0 ≤ normSq0S (I := I) g₁ x 3
      (lapDiffFlux (I := I) g₁ g₂ (metricTensorField (I := I) g₂) x) :=
    normSq0S_nonneg (I := I) g₁ x 3 _
  have hsecond : normSq0S (I := I) g₁ x 5
      (reLowerPair (I := I) g₁ P
        (lapDiffFlux (I := I) g₁ g₂ (metricTensorField (I := I) g₂)) x) ≤
      (Module.finrank Real E : Real) ^ 7 *
        (BP * (4 * (Module.finrank Real E : Real) ^ 3 *
          connectionDifferenceSq (I := I) g₁ g₂ x * Background)) := by
    refine (reLowerPairSq_le (I := I) (s := 3) g₁ P
      (lapDiffFlux (I := I) g₁ g₂ (metricTensorField (I := I) g₂)) x).trans ?_
    have hpow : (0 : Real) ≤ (Module.finrank Real E : Real) ^ 7 := by positivity
    refine mul_le_mul_of_nonneg_left ?_ hpow
    have h1 : normSq0S (I := I) g₁ x 4 (P x) *
        normSq0S (I := I) g₁ x 3
          (lapDiffFlux (I := I) g₁ g₂ (metricTensorField (I := I) g₂) x) ≤
        BP * normSq0S (I := I) g₁ x 3
          (lapDiffFlux (I := I) g₁ g₂ (metricTensorField (I := I) g₂) x) :=
      mul_le_mul_of_nonneg_right hBP hKnn
    have hBPnn : 0 ≤ BP := le_trans hPnn hBP
    exact h1.trans (mul_le_mul_of_nonneg_left hK hBPnn)
  have hpow10 : (Module.finrank Real E : Real) ^ 7 * (4 * (Module.finrank Real E : Real) ^ 3) =
      4 * (Module.finrank Real E : Real) ^ 10 := by ring
  nlinarith [hfirst, hsecond, hcd, hpow10]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem fluxSlabLe (g₁ g₂ : Real → SmoothRiemannianMetric I M)
    (Rm2 P : Real → Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (t : Real) (x : M) {B₂ BP Background : Real}
    (hB₂0 : 0 ≤ B₂) (hBP0 : 0 ≤ BP) (hBackground0 : 0 ≤ Background)
    (hB₂ : normSq0S (I := I) (g₁ t) x 4 (Rm2 t x) ≤ B₂)
    (hBP : normSq0S (I := I) (g₁ t) x 4 (P t x) ≤ BP)
    (hBackground : normSq0S (I := I) (g₁ t) x 2 (metricTensorField (I := I) (g₂ t) x) ≤ Background) :
    normSq0S (I := I) (g₁ t) x 5 (sdecFlux (I := I) (g₁ t) (g₂ t) (Rm2 t) (P t) x) ≤
      (32 * (Module.finrank Real E : Real) ^ 5 * B₂ +
          8 * (Module.finrank Real E : Real) ^ 10 * (BP * Background)) *
        forwardUniqueDensity (I := I) g₁ g₂ t x := by
  have hbr : (0 : Real) ≤ 32 * (Module.finrank Real E : Real) ^ 5 * B₂ +
      8 * (Module.finrank Real E : Real) ^ 10 * (BP * Background) := by
    have h1 : (0 : Real) ≤ 32 * (Module.finrank Real E : Real) ^ 5 := by positivity
    have h2 : (0 : Real) ≤ 8 * (Module.finrank Real E : Real) ^ 10 := by positivity
    have h3 := mul_nonneg h1 hB₂0
    have h4 := mul_nonneg h2 (mul_nonneg hBP0 hBackground0)
    linarith
  refine (sdecFluxSq_le (I := I) (g₁ t) (g₂ t) (Rm2 t) (P t) x hB₂ hBP hBackground).trans ?_
  calc 32 * (Module.finrank Real E : Real) ^ 5 * connectionDifferenceSq (I := I) (g₁ t) (g₂ t) x * B₂ +
        8 * (Module.finrank Real E : Real) ^ 10 *
          connectionDifferenceSq (I := I) (g₁ t) (g₂ t) x * (BP * Background)
      = (32 * (Module.finrank Real E : Real) ^ 5 * B₂ +
          8 * (Module.finrank Real E : Real) ^ 10 * (BP * Background)) *
        connectionDifferenceSq (I := I) (g₁ t) (g₂ t) x := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (connectionDifferenceSq_le_dens (I := I) g₁ g₂ t x) hbr

end FluxField

section BackgroundSups

variable {a c : Real}

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] in
theorem normSqSlabSup {s : Nat} (g : Real → SmoothRiemannianMetric I M)
    (A : Real → (x : M) → Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (Icc a c ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hA : ∀ (x₀ : M) (K : Fin s → Fin (Module.finrank Real E)) {t : Real}, t ∈ Icc a c →
      ContMDiffWithinAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M =>
          A p.1 p.2 (fun i : Fin s => DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ (K i) p.2))
        (Icc a c ×ˢ (univ : Set M)) (t, x₀)) :
    ∃ B : Real, 0 ≤ B ∧
      ∀ t ∈ Icc a c, ∀ x : M, normSq0S (I := I) (g t) x s (A t x) ≤ B :=
  normSqSlabBound (I := I) g A
    ((normSq0S_jointContMDiffOn (I := I) g A hgram hA).continuousOn)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] in
theorem metricDiffSlabSup (g₁ g₂ : Real → SmoothRiemannianMetric I M)
    (hgram₁ : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g₁ p.1) x₀ p.2 i j)
        (Icc a c ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hgram₂ : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g₂ p.1) x₀ p.2 i j)
        (Icc a c ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) :
    ∃ B : Real, 0 ≤ B ∧ ∀ t ∈ Icc a c, ∀ x : M,
      metricDiffSq (I := I) (g₁ t) (g₂ t) x ≤ B := by
  obtain ⟨B, hB0, hB⟩ := slabBound (M := M)
    (fun t x => metricDiffSq (I := I) (g₁ t) (g₂ t) x)
    ((metricDiffSq_jointContMDiffOn (I := I) g₁ g₂ hgram₁ hgram₂).continuousOn)
  exact ⟨B, hB0, fun t ht x => (le_abs_self _).trans (hB t ht x)⟩

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] in
theorem metricSlabSup (g₁ g₂ : Real → SmoothRiemannianMetric I M)
    (hgram₁ : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g₁ p.1) x₀ p.2 i j)
        (Icc a c ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hgram₂ : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g₂ p.1) x₀ p.2 i j)
        (Icc a c ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) :
    ∃ B : Real, 0 ≤ B ∧ ∀ t ∈ Icc a c, ∀ x : M,
      normSq0S (I := I) (g₁ t) x 2 (metricTensorField (I := I) (g₂ t) x) ≤ B :=
  normSqSlabSup (I := I) g₁ (fun t x => metricTensorField (I := I) (g₂ t) x) hgram₁
    (fun x₀ K _ ht => metricChartJoint (I := I) g₂ x₀ (hgram₂ x₀) K ht)

omit [NeZero (Module.finrank ℝ E)] in
theorem rm04SlabSup (gN gL gC : Real → SmoothRiemannianMetric I M)
    (hgramN : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (gN p.1) x₀ p.2 i j)
        (Icc a c ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hgramL : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (gL p.1) x₀ p.2 i j)
        (Icc a c ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hgramC : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (gC p.1) x₀ p.2 i j)
        (Icc a c ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) :
    ∃ B : Real, 0 ≤ B ∧ ∀ t ∈ Icc a c, ∀ x : M,
      normSq0S (I := I) (gN t) x 4
        (CovariantDerivative.riemannCurvature04At (I := I) (gL t) (metricCov (I := I) (gC t))
          (metricCov_smooth (I := I) (gC t)) x) ≤ B :=
  normSqSlabSup (I := I) gN
    (fun t x => CovariantDerivative.riemannCurvature04At (I := I) (gL t)
      (metricCov (I := I) (gC t)) (metricCov_smooth (I := I) (gC t)) x) hgramN
    (fun x₀ K _ ht => rm04ChartJoint (I := I) gL gC x₀ (hgramL x₀) (hgramC x₀) K ht)

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [CompactSpace M] [I.Boundaryless] in
theorem ricciSq_le_rm04 (g₁ g₂ : SmoothRiemannianMetric I M) (x : M) :
    normSq0S (I := I) g₁ x 2 (metricRicciAt (I := I) g₂ x) ≤
      (Module.finrank Real E : Real) ^ 4 *
        normSq0S (I := I) g₁ x 4
          (CovariantDerivative.riemannCurvature04At (I := I) g₁ (metricCov (I := I) g₂)
            (metricCov_smooth (I := I) g₂) x) := by
  classical
  obtain ⟨basis, hON⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis (I := I) g₁ x
  have hinv := onFrame_inv (I := I) g₁ basis hON
  have htr := traceNormSq_le (I := I) (s := 2) g₁ x
    ((CovariantDerivative.riemannCurvature04At (I := I) g₁ (metricCov (I := I) g₂)
      (metricCov_smooth (I := I) g₂) x).domDomCongr rm04TraceSlots)
  rw [normSq0S_domDomCongr (I := I) g₁ x basis hinv rm04TraceSlots _] at htr
  rw [metricRicci_eq_trace_cross (I := I) g₁ g₂ x]
  exact htr

omit [NeZero (Module.finrank ℝ E)] in
theorem ricciSlabSup (g₁ g₂ : Real → SmoothRiemannianMetric I M)
    (hgram₁ : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g₁ p.1) x₀ p.2 i j)
        (Icc a c ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hgram₂ : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g₂ p.1) x₀ p.2 i j)
        (Icc a c ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) :
    ∃ B : Real, 0 ≤ B ∧ ∀ t ∈ Icc a c, ∀ x : M,
      normSq0S (I := I) (g₁ t) x 2 (metricRicciAt (I := I) (g₂ t) x) ≤ B := by
  obtain ⟨B, hB0, hB⟩ := rm04SlabSup (I := I) g₁ g₁ g₂ hgram₁ hgram₁ hgram₂
  have hpow : (0 : Real) ≤ (Module.finrank Real E : Real) ^ 4 := by positivity
  refine ⟨(Module.finrank Real E : Real) ^ 4 * B, mul_nonneg hpow hB0, fun t ht x => ?_⟩
  exact (ricciSq_le_rm04 (I := I) (g₁ t) (g₂ t) x).trans
    (mul_le_mul_of_nonneg_left (hB t ht x) hpow)

omit [NeZero (Module.finrank ℝ E)] in
theorem nablaRicSlabSup (gN gC : Real → SmoothRiemannianMetric I M)
    (hgramN : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (gN p.1) x₀ p.2 i j)
        (Icc a c ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hgramC : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (gC p.1) x₀ p.2 i j)
        (Icc a c ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) :
    ∃ B : Real, 0 ≤ B ∧ ∀ t ∈ Icc a c, ∀ x : M,
      normSq0S (I := I) (gN t) x 3
        (metricNabla0S (I := I) (gC t)
          (CovariantDerivative.ricciSection (I := I)
            (metricCov (I := I) (gC t)) (metricCov_smooth (I := I) (gC t))) x) ≤ B :=
  normSqSlabSup (I := I) gN
    (fun t x =>
      metricNabla0S (I := I) (gC t)
        (CovariantDerivative.ricciSection (I := I)
          (metricCov (I := I) (gC t)) (metricCov_smooth (I := I) (gC t))) x)
    hgramN
    (fun x₀ K _ ht => nablaRicChartJoint (I := I) gC x₀ (hgramC x₀) K ht)

omit [NeZero (Module.finrank ℝ E)] in
theorem nablaKRmSlabSup (gN gC : Real → SmoothRiemannianMetric I M)
    (hgramN : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (gN p.1) x₀ p.2 i j)
        (Icc a c ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hgramC : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (gC p.1) x₀ p.2 i j)
        (Icc a c ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (k : ℕ) :
    ∃ B : Real, 0 ≤ B ∧ ∀ t ∈ Icc a c, ∀ x : M,
      normSq0S (I := I) (gN t) x (4 + k)
        (nablaKRm04Field (I := I)
          (solOfMetric (I := I) (D := RealTimeInterval.univ 0) gC) t k x) ≤ B :=
  normSqSlabSup (I := I) gN
    (fun t x =>
      nablaKRm04Field (I := I)
        (solOfMetric (I := I) (D := RealTimeInterval.univ 0) gC) t k x)
    hgramN
    (fun x₀ K _ ht => nablaKRmChartJoint (I := I) gC x₀ (hgramC x₀) k K ht)

omit [NeZero (Module.finrank ℝ E)] in
theorem crossRm1SlabSup
    (gN gL gC gD : Real → SmoothRiemannianMetric I M)
    (hgramN : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (gN p.1) x₀ p.2 i j)
        (Icc a c ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hgramL : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (gL p.1) x₀ p.2 i j)
        (Icc a c ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hgramC : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (gC p.1) x₀ p.2 i j)
        (Icc a c ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hgramD : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (gD p.1) x₀ p.2 i j)
        (Icc a c ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) :
    ∃ B : Real, 0 ≤ B ∧ ∀ t ∈ Icc a c, ∀ x : M,
      normSq0S (I := I) (gN t) x 5
        (metricNabla0S (I := I) (gD t)
          (CovariantDerivative.rm04Section (I := I) (gL t)
            (metricCov (I := I) (gC t))
            (metricCov_smooth (I := I) (gC t))) x) ≤ B :=
  normSqSlabSup (I := I) gN
    (fun t =>
      metricNabla0S (I := I) (gD t)
        (CovariantDerivative.rm04Section (I := I) (gL t)
          (metricCov (I := I) (gC t))
          (metricCov_smooth (I := I) (gC t))))
    hgramN
    (fun x₀ K _ ht =>
      crossRm1ChartJoint (I := I) gL gC gD x₀
        (hgramL x₀) (hgramC x₀) (hgramD x₀) K ht)

omit [NeZero (Module.finrank ℝ E)] in
theorem crossRm2SlabSup
    (gN gL gC gD : Real → SmoothRiemannianMetric I M)
    (hgramN : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (gN p.1) x₀ p.2 i j)
        (Icc a c ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hgramL : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (gL p.1) x₀ p.2 i j)
        (Icc a c ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hgramC : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (gC p.1) x₀ p.2 i j)
        (Icc a c ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hgramD : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (gD p.1) x₀ p.2 i j)
        (Icc a c ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) :
    ∃ B : Real, 0 ≤ B ∧ ∀ t ∈ Icc a c, ∀ x : M,
      normSq0S (I := I) (gN t) x 6
        (metricNabla0S (I := I) (gD t)
          (metricNabla0S (I := I) (gD t)
            (CovariantDerivative.rm04Section (I := I) (gL t)
              (metricCov (I := I) (gC t))
              (metricCov_smooth (I := I) (gC t)))) x) ≤ B :=
  normSqSlabSup (I := I) gN
    (fun t =>
      metricNabla0S (I := I) (gD t)
        (metricNabla0S (I := I) (gD t)
          (CovariantDerivative.rm04Section (I := I) (gL t)
            (metricCov (I := I) (gC t))
            (metricCov_smooth (I := I) (gC t)))))
    hgramN
    (fun x₀ K _ ht =>
      crossRm2ChartJoint (I := I) gL gC gD x₀
        (hgramL x₀) (hgramC x₀) (hgramD x₀) K ht)

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [CompactSpace M] [I.Boundaryless] in
theorem fu_metric_comp_le (g₁ g₂ : SmoothRiemannianMetric I M) (x : M)
    (v : TangentSpace I x) :
    g₁.inner x v v ≤
      Real.sqrt (normSq0S (I := I) g₂ x 2 (metricTensorField (I := I) g₁ x)) *
        g₂.inner x v v := by
  classical
  have hvv : (0 : Real) ≤ g₂.inner x v v := by
    rcases eq_or_ne v 0 with hv0 | hv0
    · rw [hv0]; simp
    · exact (g₂.pos x v hv0).le
  obtain ⟨basis, hON⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis (I := I) g₂ x
  have h := abs_apply_le_sqrt_normSq0S (I := I) g₂ x 2 basis hON
    (metricTensorField (I := I) g₁ x) (fun _ : Fin 2 => v)
  have hval : metricTensorField (I := I) g₁ x (fun _ : Fin 2 => v) = g₁.inner x v v :=
    metricTensorField_apply (I := I) g₁ x (fun _ : Fin 2 => v)
  have hprod : (∏ _d : Fin 2, Real.sqrt (g₂.inner x v v)) = g₂.inner x v v := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [sq]
    exact Real.mul_self_sqrt hvv
  rw [hval, hprod] at h
  exact (le_abs_self _).trans h

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] in
theorem metricCompSlab (g₁ g₂ : Real → SmoothRiemannianMetric I M)
    (hgram₁ : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g₁ p.1) x₀ p.2 i j)
        (Icc a c ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hgram₂ : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g₂ p.1) x₀ p.2 i j)
        (Icc a c ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) :
    ∃ Λ : Real, 0 ≤ Λ ∧ ∀ t ∈ Icc a c, ∀ (x : M) (v : TangentSpace I x),
      (g₁ t).inner x v v ≤ Λ * (g₂ t).inner x v v := by
  obtain ⟨B, hB0, hB⟩ := metricSlabSup (I := I) g₂ g₁ hgram₂ hgram₁
  refine ⟨Real.sqrt B, Real.sqrt_nonneg _, fun t ht x v => ?_⟩
  have hvv : (0 : Real) ≤ (g₂ t).inner x v v := by
    rcases eq_or_ne v 0 with hv0 | hv0
    · rw [hv0]; simp
    · exact ((g₂ t).pos x v hv0).le
  refine (fu_metric_comp_le (I := I) (g₁ t) (g₂ t) x v).trans ?_
  exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (hB t ht x)) hvv

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] in
theorem metricEquivSlab (g₁ g₂ : Real → SmoothRiemannianMetric I M)
    (hgram₁ : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g₁ p.1) x₀ p.2 i j)
        (Icc a c ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hgram₂ : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g₂ p.1) x₀ p.2 i j)
        (Icc a c ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) :
    ∃ C : Real, 1 ≤ C ∧ ∀ t ∈ Icc a c, ∀ (x : M) (v : TangentSpace I x),
      C⁻¹ * (g₁ t).inner x v v ≤ (g₂ t).inner x v v ∧
        (g₂ t).inner x v v ≤ C * (g₁ t).inner x v v := by
  obtain ⟨Λ₁₂, hΛ₁₂0, hΛ₁₂⟩ := metricCompSlab (I := I) g₁ g₂ hgram₁ hgram₂
  obtain ⟨Λ₂₁, hΛ₂₁0, hΛ₂₁⟩ := metricCompSlab (I := I) g₂ g₁ hgram₂ hgram₁
  let C : Real := 1 + Λ₁₂ + Λ₂₁
  have hC : 1 ≤ C := by
    dsimp [C]
    linarith
  have hΛ₁₂C : Λ₁₂ ≤ C := by
    dsimp [C]
    linarith
  have hΛ₂₁C : Λ₂₁ ≤ C := by
    dsimp [C]
    linarith
  refine ⟨C, hC, fun t ht x v => ?_⟩
  have hv₁ : 0 ≤ (g₁ t).inner x v v := by
    rcases eq_or_ne v 0 with hv | hv
    · rw [hv]
      simp
    · exact ((g₁ t).pos x v hv).le
  have hv₂ : 0 ≤ (g₂ t).inner x v v := by
    rcases eq_or_ne v 0 with hv | hv
    · rw [hv]
      simp
    · exact ((g₂ t).pos x v hv).le
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have h₁₂ : (g₁ t).inner x v v ≤ C * (g₂ t).inner x v v :=
    (hΛ₁₂ t ht x v).trans (mul_le_mul_of_nonneg_right hΛ₁₂C hv₂)
  constructor
  · calc
      C⁻¹ * (g₁ t).inner x v v ≤ C⁻¹ * (C * (g₂ t).inner x v v) :=
        mul_le_mul_of_nonneg_left h₁₂ (inv_nonneg.mpr hCpos.le)
      _ = (g₂ t).inner x v v := by field_simp [hCpos.ne']
  · exact (hΛ₂₁ t ht x v).trans
      (mul_le_mul_of_nonneg_right hΛ₂₁C hv₁)

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [CompactSpace M] [I.Boundaryless] in
theorem tracePairSq_le (g : SmoothRiemannianMetric I M) (x : M)
    (Q : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :
    (metricTracePair0SAt (I := I) g Q) ^ 2 ≤
      (Module.finrank Real E : Real) * normSq0S (I := I) g x 2 Q := by
  classical
  obtain ⟨basis, hON⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis (I := I) g x
  have h := metricTracePair0SAt_sq_le_card_mul_normSq0S (I := I) g basis
    (identityInvMetric (Idx := Fin (Module.finrank Real (TangentSpace I x))))
    (onFrame_inv (I := I) g basis hON) Q
  rw [show Module.finrank Real (TangentSpace I x) = Module.finrank Real E from rfl] at h
  simp only [Fintype.card_fin] at h
  exact h

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [CompactSpace M] [I.Boundaryless] in
theorem volSlabSup (g₁ : Real → SmoothRiemannianMetric I M) {B : Real}
    (htr : ∀ t ∈ Ioo a c, ∀ x : M, traceTimeDerivMetric (I := I) g₁ t x =
      (-2 : Real) * metricTracePair0SAt (I := I) (g₁ t) (metricRicciAt (I := I) (g₁ t) x))
    (hric : ∀ t ∈ Ioo a c, ∀ x : M,
      normSq0S (I := I) (g₁ t) x 2 (metricRicciAt (I := I) (g₁ t) x) ≤ B) :
    ∃ C_V : Real, 0 ≤ C_V ∧ ∀ t ∈ Ioo a c, ∀ x : M,
      (1 / 2 : Real) * traceTimeDerivMetric (I := I) g₁ t x ≤ C_V := by
  refine ⟨Real.sqrt ((Module.finrank Real E : Real) * B), Real.sqrt_nonneg _,
    fun t ht x => ?_⟩
  set S : Real := metricTracePair0SAt (I := I) (g₁ t) (metricRicciAt (I := I) (g₁ t) x) with hS
  have hsq : S ^ 2 ≤ (Module.finrank Real E : Real) * B := by
    refine (tracePairSq_le (I := I) (g₁ t) x (metricRicciAt (I := I) (g₁ t) x)).trans ?_
    exact mul_le_mul_of_nonneg_left (hric t ht x) (by positivity)
  have habs : |S| ≤ Real.sqrt ((Module.finrank Real E : Real) * B) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt hsq
  have hneg : -S ≤ Real.sqrt ((Module.finrank Real E : Real) * B) :=
    (neg_le_abs S).trans habs
  rw [htr t ht x]
  linarith

end BackgroundSups

section ReactField

variable {a c : Real}

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [CompactSpace M] [I.Boundaryless] in
private theorem reactOrtho {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {s : Nat} {x : M} {t : Real}
    (g : Real → SmoothRiemannianMetric I M)
    (Q : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (W : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hON : ∀ i j, (g t).inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (hg : ∀ X Y : TangentSpace I x,
      HasDerivAt (fun r : Real => (g r).inner x X Y)
        ((-2 : Real) * Q (fun d : Fin 2 => if d = 0 then X else Y)) t) :
    movingReact0S (I := I) (g t) x s Q W =
      ricReactionContract (identityInvMetric (Idx := Idx))
        (fun i j => Q (fun d : Fin 2 => if d = 0 then basis i else basis j))
        (fun I0 => tensor0SComponent (I := I) W (fun i => basis i) I0)
        (fun J0 => tensor0SComponent (I := I) W (fun i => basis i) J0) := by
  classical
  have hz : inner0S (I := I) (g t) x s
      (0 : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x) W = 0 := by
    simpa using inner0S_smul_left (I := I) (g t) x s (0 : Real) W W
  have hL : HasDerivAt (fun r : Real => normSq0S (I := I) (g r) x s W)
      (movingReact0S (I := I) (g t) x s Q W) t := by
    have hT : ∀ v : Fin s → TangentSpace I x,
        HasDerivAt (fun _ : Real => W v)
          ((0 : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x) v) t := by
      intro v
      rw [Tensor0SSpace.zero_apply (I := I) s x v]
      exact hasDerivAt_const t (W v)
    have h := normSq0S_moving_deriv (I := I) g Q (fun _ => W) 0 hg hT
    rw [hz, mul_zero, add_zero] at h
    exact h
  set ric : Idx → Idx → Real := fun i j =>
    Q (fun d : Fin 2 => if d = 0 then basis i else basis j) with hricdef
  set gI : Real → Idx → Idx → Real := fun r => basisInvMetric (I := I) (g r) x basis with hgIdef
  set gIDt : Idx → Idx → Real := fun i j =>
    -(∑ p : Idx, ∑ q : Idx, gI t i p * ((-2 : Real) * ric p q) * gI t q j) with hgIDtdef
  have hinvAll : ∀ r : Real, MetricInverseInBasis (I := I) (g r) x basis (gI r) := by
    intro r
    simpa only [gI, MetricInverseInBasis, MetricInverseInBasisGen] using
      basisInvMetric_real (I := I) (g r) x basis
  have hgI : ∀ i j : Idx,
      HasDerivWithinAt (fun r : Real => gI r i j) (gIDt i j) Set.univ t := by
    intro i j
    simpa [gI, gIDt, ric] using
      (basisInv_time (I := I) g (fun p q => (-2 : Real) * ric p q) basis
        (fun p q => by simpa [ric] using hg (basis p) (basis q)) i j)
  have hflow : ∀ i j : Idx,
      gIDt i j = 2 * (∑ p : Idx, ∑ q : Idx, gI t i p * gI t j q * ric p q) := by
    intro i j
    have hterm : (∑ p : Idx, ∑ q : Idx, gI t i p * ((-2 : Real) * ric p q) * gI t q j) =
        ∑ p : Idx, ∑ q : Idx, (-2 : Real) * (gI t i p * gI t j q * ric p q) := by
      refine Finset.sum_congr rfl fun p _ => ?_
      refine Finset.sum_congr rfl fun q _ => ?_
      simp only [gI]
      rw [basisInvMetric_symm (I := I) (g t) x basis q j]
      ring
    have hfactor : (∑ p : Idx, ∑ q : Idx, (-2 : Real) * (gI t i p * gI t j q * ric p q)) =
        (-2 : Real) * (∑ p : Idx, ∑ q : Idx, gI t i p * gI t j q * ric p q) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Finset.mul_sum]
    simp only [gIDt]
    rw [hterm, hfactor]
    ring
  have hTcomp : ∀ I0 : Fin s → Idx,
      HasDerivWithinAt
        (fun r : Real => tensor0SComponent (I := I) ((fun _ : Real => W) r)
          (fun i => basis i) I0) ((fun _ : Fin s → Idx => (0 : Real)) I0) Set.univ t :=
    fun I0 => hasDerivWithinAt_const _ _ _
  have hTdot : ∀ I0 : Fin s → Idx,
      tensor0SComponent (I := I)
          (0 : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
          (fun i => basis i) I0 = (0 : Real) :=
    fun I0 => Tensor0SSpace.zero_apply (I := I) s x _
  have hR := hasDerivWithinAt_normSq0S_ricciFlow (I := I) (s := s) (u := Set.univ) (t := t)
    g gI gIDt ric (fun _ : Real => W) (fun _ : Fin s → Idx => (0 : Real)) 0 basis
    hinvAll hgI hTcomp hTdot hflow
  rw [hz, mul_zero, add_zero] at hR
  have hid : gI t = identityInvMetric (Idx := Idx) := by
    funext i j
    have h := (hinvAll t i j).1
    simp only [hON, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true] at h
    simpa [identityInvMetric, diagonalInvMetric] using h
  rw [hid] at hR
  exact hL.unique (hR.hasDerivAt (by simp))

private theorem ricReactAbs_le {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {s : Nat}
    (ric : Idx → Idx → Real) (cc : (Fin s → Idx) → Real) {Bq N : Real}
    (hBq0 : 0 ≤ Bq) (hN0 : 0 ≤ N)
    (hBq : ∀ i j, |ric i j| ≤ Bq) (hc : ∀ I0, |cc I0| ≤ N) :
    |ricReactionContract (identityInvMetric (Idx := Idx)) ric cc cc| ≤
      2 * ((Fintype.card (Fin s → Idx) : Real) ^ 2 *
        ((s : Real) * (Fintype.card Idx : Real) ^ 2 * Bq * N ^ 2)) := by
  classical
  have hδ : ∀ i j : Idx, |identityInvMetric (Idx := Idx) i j| ≤ 1 := by
    intro i j
    by_cases h : i = j
    · subst h; simp [identityInvMetric]
    · simp [identityInvMetric, diagonalInvMetric, h]
  have hδ0 : ∀ i j : Idx, (0 : Real) ≤ |identityInvMetric (Idx := Idx) i j| := fun i j =>
    abs_nonneg _
  have hinner : ∀ i j : Idx,
      |∑ p : Idx, ∑ q : Idx, identityInvMetric (Idx := Idx) i p *
        identityInvMetric (Idx := Idx) j q * ric p q| ≤
        (Fintype.card Idx : Real) ^ 2 * Bq := by
    intro i j
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hrow : ∀ p : Idx, |∑ q : Idx, identityInvMetric (Idx := Idx) i p *
        identityInvMetric (Idx := Idx) j q * ric p q| ≤ (Fintype.card Idx : Real) * Bq := by
      intro p
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have hterm : ∀ q : Idx, |identityInvMetric (Idx := Idx) i p *
          identityInvMetric (Idx := Idx) j q * ric p q| ≤ Bq := by
        intro q
        rw [abs_mul, abs_mul]
        calc |identityInvMetric (Idx := Idx) i p| * |identityInvMetric (Idx := Idx) j q| *
              |ric p q|
            ≤ 1 * 1 * Bq := by
              refine mul_le_mul (mul_le_mul (hδ i p) (hδ j q) (hδ0 j q) zero_le_one)
                (hBq p q) (abs_nonneg _) (by norm_num)
          _ = Bq := by ring
      refine (Finset.sum_le_sum fun q _ => hterm q).trans ?_
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    refine (Finset.sum_le_sum fun p _ => hrow p).trans ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [sq]
    ring_nf
    exact le_refl _
  have hslot : ∀ I0 J0 : Fin s → Idx,
      |∑ b : Fin s, (∏ α ∈ (Finset.univ : Finset (Fin s)).erase b,
          identityInvMetric (Idx := Idx) (I0 α) (J0 α)) *
        (∑ p : Idx, ∑ q : Idx, identityInvMetric (Idx := Idx) (I0 b) p *
          identityInvMetric (Idx := Idx) (J0 b) q * ric p q)| ≤
        (s : Real) * ((Fintype.card Idx : Real) ^ 2 * Bq) := by
    intro I0 J0
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ b : Fin s,
        |(∏ α ∈ (Finset.univ : Finset (Fin s)).erase b,
            identityInvMetric (Idx := Idx) (I0 α) (J0 α)) *
          (∑ p : Idx, ∑ q : Idx, identityInvMetric (Idx := Idx) (I0 b) p *
            identityInvMetric (Idx := Idx) (J0 b) q * ric p q)| ≤
          (Fintype.card Idx : Real) ^ 2 * Bq := by
      intro b
      rw [abs_mul]
      have hprod : |∏ α ∈ (Finset.univ : Finset (Fin s)).erase b,
          identityInvMetric (Idx := Idx) (I0 α) (J0 α)| ≤ 1 := by
        rw [Finset.abs_prod]
        exact Finset.prod_le_one (fun α _ => hδ0 _ _) (fun α _ => hδ _ _)
      calc |∏ α ∈ (Finset.univ : Finset (Fin s)).erase b,
              identityInvMetric (Idx := Idx) (I0 α) (J0 α)| *
            |∑ p : Idx, ∑ q : Idx, identityInvMetric (Idx := Idx) (I0 b) p *
              identityInvMetric (Idx := Idx) (J0 b) q * ric p q|
          ≤ 1 * ((Fintype.card Idx : Real) ^ 2 * Bq) := by
            refine mul_le_mul hprod (hinner _ _) (abs_nonneg _) zero_le_one
        _ = (Fintype.card Idx : Real) ^ 2 * Bq := by ring
    refine (Finset.sum_le_sum fun b _ => hterm b).trans ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  unfold ricReactionContract
  rw [abs_mul, abs_two]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have houter : ∀ I0 : Fin s → Idx,
      |∑ J0 : Fin s → Idx,
        (∑ b : Fin s, (∏ α ∈ (Finset.univ : Finset (Fin s)).erase b,
            identityInvMetric (Idx := Idx) (I0 α) (J0 α)) *
          (∑ p : Idx, ∑ q : Idx, identityInvMetric (Idx := Idx) (I0 b) p *
            identityInvMetric (Idx := Idx) (J0 b) q * ric p q)) * cc I0 * cc J0| ≤
        (Fintype.card (Fin s → Idx) : Real) *
          ((s : Real) * (Fintype.card Idx : Real) ^ 2 * Bq * N ^ 2) := by
    intro I0
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ J0 : Fin s → Idx,
        |(∑ b : Fin s, (∏ α ∈ (Finset.univ : Finset (Fin s)).erase b,
            identityInvMetric (Idx := Idx) (I0 α) (J0 α)) *
          (∑ p : Idx, ∑ q : Idx, identityInvMetric (Idx := Idx) (I0 b) p *
            identityInvMetric (Idx := Idx) (J0 b) q * ric p q)) * cc I0 * cc J0| ≤
          (s : Real) * (Fintype.card Idx : Real) ^ 2 * Bq * N ^ 2 := by
      intro J0
      rw [abs_mul, abs_mul]
      calc |∑ b : Fin s, (∏ α ∈ (Finset.univ : Finset (Fin s)).erase b,
              identityInvMetric (Idx := Idx) (I0 α) (J0 α)) *
            (∑ p : Idx, ∑ q : Idx, identityInvMetric (Idx := Idx) (I0 b) p *
              identityInvMetric (Idx := Idx) (J0 b) q * ric p q)| * |cc I0| * |cc J0|
          ≤ ((s : Real) * ((Fintype.card Idx : Real) ^ 2 * Bq)) * N * N := by
            refine mul_le_mul (mul_le_mul (hslot I0 J0) (hc I0) (abs_nonneg _) ?_)
              (hc J0) (abs_nonneg _) ?_
            · positivity
            · positivity
        _ = (s : Real) * (Fintype.card Idx : Real) ^ 2 * Bq * N ^ 2 := by ring
    refine (Finset.sum_le_sum fun J0 _ => hterm J0).trans ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  refine (Finset.sum_le_sum fun I0 _ => houter I0).trans ?_
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [sq]
  ring_nf
  exact le_refl _

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [CompactSpace M] [I.Boundaryless] in
theorem movingReactAbs_le {s : Nat} {x : M} {t : Real}
    (g : Real → SmoothRiemannianMetric I M)
    (Q : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (W : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (hg : ∀ X Y : TangentSpace I x,
      HasDerivAt (fun r : Real => (g r).inner x X Y)
        ((-2 : Real) * Q (fun d : Fin 2 => if d = 0 then X else Y)) t) :
    |movingReact0S (I := I) (g t) x s Q W| ≤
      2 * (s : Real) * (Module.finrank Real E : Real) ^ (2 * s + 2) *
        Real.sqrt (normSq0S (I := I) (g t) x 2 Q) * normSq0S (I := I) (g t) x s W := by
  classical
  obtain ⟨basis, hON⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis (I := I) (g t) x
  have hinv := onFrame_inv (I := I) (g t) basis hON
  set NQ : Real := Real.sqrt (normSq0S (I := I) (g t) x 2 Q) with hNQ
  set NW : Real := Real.sqrt (normSq0S (I := I) (g t) x s W) with hNW
  have hNQ0 : 0 ≤ NQ := Real.sqrt_nonneg _
  have hNW0 : 0 ≤ NW := Real.sqrt_nonneg _
  have hQc : ∀ i j : Fin (Module.finrank Real (TangentSpace I x)),
      |Q (fun d : Fin 2 => if d = 0 then basis i else basis j)| ≤ NQ := by
    intro i j
    have h := abs_apply_le_sqrt_normSq0S (I := I) (g t) x 2 basis hON Q
      (fun d : Fin 2 => if d = 0 then basis i else basis j)
    have hprod : (∏ d : Fin 2, Real.sqrt ((g t).inner x
        (if d = 0 then basis i else basis j) (if d = 0 then basis i else basis j))) = 1 := by
      refine Finset.prod_eq_one fun d _ => ?_
      by_cases hd : d = 0
      · simp [hd, hON i i]
      · simp [hd, hON j j]
    rw [hprod, mul_one] at h
    exact h
  have hWc : ∀ I0 : Fin s → Fin (Module.finrank Real (TangentSpace I x)),
      |tensor0SComponent (I := I) W (fun i => basis i) I0| ≤ NW := by
    intro I0
    have h := abs_apply_le_sqrt_normSq0S (I := I) (g t) x s basis hON W
      (fun d : Fin s => basis (I0 d))
    have hprod : (∏ d : Fin s, Real.sqrt ((g t).inner x (basis (I0 d)) (basis (I0 d)))) = 1 := by
      refine Finset.prod_eq_one fun d _ => ?_
      simp [hON (I0 d) (I0 d)]
    rw [hprod, mul_one] at h
    change |W (fun a ↦ basis (I0 a))| ≤ NW
    rw [hNW]
    exact h
  rw [reactOrtho (I := I) g Q W basis hON hg]
  refine (ricReactAbs_le (Idx := Fin (Module.finrank Real (TangentSpace I x)))
    (s := s) _ _ hNQ0 hNW0 hQc hWc).trans (le_of_eq ?_)
  have hcard : (Fintype.card (Fin s → Fin (Module.finrank Real (TangentSpace I x))) : Real)
      = (Module.finrank Real E : Real) ^ s := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    push_cast
    rfl
  have hcard1 : (Fintype.card (Fin (Module.finrank Real (TangentSpace I x))) : Real)
      = (Module.finrank Real E : Real) := by
    rw [Fintype.card_fin]
    rfl
  have hNW2 : NW ^ 2 = normSq0S (I := I) (g t) x s W :=
    Real.sq_sqrt (normSq0S_nonneg (I := I) (g t) x s W)
  rw [hcard, hcard1, hNW2, show 2 * s + 2 = s * 2 + 2 from by ring, pow_add, pow_mul]
  ring

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [CompactSpace M] [I.Boundaryless] in
theorem reactSlabLe (g₁ g₂ : Real → SmoothRiemannianMetric I M) {Λric : Real}
    (hpde : ∀ t ∈ Ioo a c, ∀ (x : M) (X Y : TangentSpace I x),
      HasDerivAt (fun r : Real => (g₁ r).inner x X Y)
        ((-2 : Real) * metricRicciAt (I := I) (g₁ t) x
          (fun d : Fin 2 => if d = 0 then X else Y)) t)
    (hric : ∀ t ∈ Ioo a c, ∀ x : M,
      normSq0S (I := I) (g₁ t) x 2 (metricRicciAt (I := I) (g₁ t) x) ≤ Λric) :
    ∃ C_R : Real, 0 ≤ C_R ∧ ∀ t ∈ Ioo a c, ∀ x : M,
      movingReact0S (I := I) (g₁ t) x 2 (metricRicciAt (I := I) (g₁ t) x)
          (metricDiffAt (I := I) (g₁ t) (g₂ t) x) +
        movingReact0S (I := I) (g₁ t) x 3 (metricRicciAt (I := I) (g₁ t) x)
          (connectionDifferenceLowAt (I := I) (g₁ t) (g₂ t) x) +
        movingReact0S (I := I) (g₁ t) x 4 (metricRicciAt (I := I) (g₁ t) x)
          (rmDiffLowAt (I := I) (g₁ t) (g₂ t) x) ≤
      C_R * forwardUniqueDensity (I := I) g₁ g₂ t x := by
  refine ⟨(4 * (Module.finrank Real E : Real) ^ 6 + 6 * (Module.finrank Real E : Real) ^ 8 +
      8 * (Module.finrank Real E : Real) ^ 10) * Real.sqrt Λric, by positivity,
    fun t ht x => ?_⟩
  have hSΛ0 : (0 : Real) ≤ Real.sqrt Λric := Real.sqrt_nonneg _
  have hS : Real.sqrt (normSq0S (I := I) (g₁ t) x 2 (metricRicciAt (I := I) (g₁ t) x)) ≤
      Real.sqrt Λric := Real.sqrt_le_sqrt (hric t ht x)
  have hstep : ∀ (s : Nat)
      (W : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x),
      normSq0S (I := I) (g₁ t) x s W ≤ forwardUniqueDensity (I := I) g₁ g₂ t x →
      movingReact0S (I := I) (g₁ t) x s (metricRicciAt (I := I) (g₁ t) x) W ≤
        2 * (s : Real) * (Module.finrank Real E : Real) ^ (2 * s + 2) * Real.sqrt Λric *
          forwardUniqueDensity (I := I) g₁ g₂ t x := by
    intro s W hW
    have hcoef : (0 : Real) ≤
        2 * (s : Real) * (Module.finrank Real E : Real) ^ (2 * s + 2) := by positivity
    have hprod : Real.sqrt (normSq0S (I := I) (g₁ t) x 2 (metricRicciAt (I := I) (g₁ t) x)) *
        normSq0S (I := I) (g₁ t) x s W ≤
        Real.sqrt Λric * forwardUniqueDensity (I := I) g₁ g₂ t x :=
      mul_le_mul hS hW (normSq0S_nonneg (I := I) (g₁ t) x s W) hSΛ0
    refine le_trans (le_abs_self _)
      ((movingReactAbs_le (I := I) g₁ (metricRicciAt (I := I) (g₁ t) x) W (hpde t ht x)).trans ?_)
    exact le_trans (le_of_eq (by ring))
      (le_trans (mul_le_mul_of_nonneg_left hprod hcoef) (le_of_eq (by ring)))
  have h2 := hstep 2 (metricDiffAt (I := I) (g₁ t) (g₂ t) x)
    (by simpa [metricDiffSq_def] using metricDiffSq_le_dens (I := I) g₁ g₂ t x)
  have h3 := hstep 3 (connectionDifferenceLowAt (I := I) (g₁ t) (g₂ t) x)
    (by simpa [connectionDifferenceSq_def] using connectionDifferenceSq_le_dens (I := I) g₁ g₂ t x)
  have h4 := hstep 4 (rmDiffLowAt (I := I) (g₁ t) (g₂ t) x)
    (by simpa [rmDiffSq_def] using rmDiffSq_le_dens (I := I) g₁ g₂ t x)
  norm_num at h2 h3 h4
  linarith

end ReactField

section EdgeContinuity

omit [NeZero (Module.finrank ℝ E)] in
theorem energyEdgeCont (g₁ g₂ : Real → SmoothRiemannianMetric I M) {a b : Real} (hab : a < b)
    (hgram₁ : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g₁ p.1) x₀ p.2 i j)
        (Ico a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hgram₂ : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g₂ p.1) x₀ p.2 i j)
        (Ico a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) :
    ContinuousWithinAt (forwardUniqueEnergy (I := I) (M := M) g₁ g₂) (Ico a b) a := by
  set c : Real := (a + b) / 2 with hcdef
  have hac : a < c := by rw [hcdef]; linarith
  have hcb : c < b := by rw [hcdef]; linarith
  have hsub : Icc a c ⊆ Ico a b := fun x hx => ⟨hx.1, lt_of_le_of_lt hx.2 hcb⟩
  have hres₁ : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g₁ p.1) x₀ p.2 i j)
        (Icc a c ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) :=
    fun x₀ i j => (hgram₁ x₀ i j).mono (Set.prod_mono hsub (Set.Subset.refl _))
  have hres₂ : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g₂ p.1) x₀ p.2 i j)
        (Icc a c ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) :=
    fun x₀ i j => (hgram₂ x₀ i j).mono (Set.prod_mono hsub (Set.Subset.refl _))
  have hdens : ContinuousOn
      (fun p : Real × M => forwardUniqueDensity (I := I) g₁ g₂ p.1 p.2)
      (Icc a c ×ˢ (univ : Set M)) :=
    (dens_jointContMDiffOn (I := I) g₁ g₂ hres₁ hres₂).continuousOn
  have hE : ContinuousOn
      (fun t : Real => ∫ x, forwardUniqueDensity (I := I) g₁ g₂ t x
        ∂(riemannianMeasureFamily (I := I) (M := M) g₁ t)) (Icc a c) :=
    integral_family_cont (I := I) isCompact_Icc
      (fun x₀ i j => (hres₁ x₀ i j).continuousOn) hdens
  have hmem : Icc a c ∈ 𝓝[Ico a b] a := by
    refine Filter.mem_of_superset
      (inter_mem_nhdsWithin (Ico a b) (isOpen_Iio.mem_nhds hac)) ?_
    rintro p ⟨hp1, hp2⟩
    exact ⟨hp1.1, le_of_lt hp2⟩
  exact (hE a ⟨le_refl a, hac.le⟩).mono_of_mem_nhdsWithin hmem

end EdgeContinuity

end DifferentialGeometry.PDE.RicciFlow

end
