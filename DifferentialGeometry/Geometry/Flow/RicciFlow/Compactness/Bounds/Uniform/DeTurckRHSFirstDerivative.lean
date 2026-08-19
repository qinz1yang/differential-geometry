import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Uniform.CurvatureJetOne

import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Uniform.DeTurckRHS
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Uniform.ThirdCovariantDerivativeComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Uniform.ReverseJetSecondDerivative
import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNormArity
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckVectorFieldCovariantDerivative
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.RicciTowerTrace
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.RoughLaplacianOperatorFieldApplicationCommutation
import DifferentialGeometry.Tensor.RSTensor.MetricTrace.NormBound

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.HCGCompactness

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem centeredBasis
    (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x),
      (∀ i, basis i = smoothOrthoFrame (I := I) g x i x) ∧
      ∀ i j, g.inner x (basis i) (basis j) = if i = j then (1 : ℝ) else 0 := by
  classical
  have horth : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner x (smoothOrthoFrame (I := I) g x i x)
          (smoothOrthoFrame (I := I) g x j x) =
        if i = j then (1 : ℝ) else 0 :=
    fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g x i j
  have hli : LinearIndependent ℝ
      (fun i : Fin (Module.finrank ℝ E) => smoothOrthoFrame (I := I) g x i x) := by
    rw [linearIndependent_iff']
    intro fs c hsum k hk
    have hzero : g.inner x (smoothOrthoFrame (I := I) g x k x)
        (∑ j ∈ fs, c j • smoothOrthoFrame (I := I) g x j x) = 0 := by
      rw [hsum]
      simp
    rw [map_sum] at hzero
    have hpull : ∀ j ∈ fs,
        g.inner x (smoothOrthoFrame (I := I) g x k x)
            (c j • smoothOrthoFrame (I := I) g x j x) =
          c j * g.inner x (smoothOrthoFrame (I := I) g x k x)
            (smoothOrthoFrame (I := I) g x j x) := by
      intro j _
      rw [(g.inner x (smoothOrthoFrame (I := I) g x k x)).map_smul,
        smul_eq_mul]
    rw [Finset.sum_congr rfl hpull] at hzero
    have hpull' : ∀ j ∈ fs,
        c j * g.inner x (smoothOrthoFrame (I := I) g x k x)
            (smoothOrthoFrame (I := I) g x j x) =
          c j * (if k = j then (1 : ℝ) else 0) := by
      intro j _
      rw [horth k j]
    rw [Finset.sum_congr rfl hpull'] at hzero
    rw [Finset.sum_eq_single_of_mem k hk] at hzero
    · simpa using hzero
    · intro j _ hjk
      rw [if_neg (fun h => hjk h.symm), mul_zero]
  have hcard :
      Fintype.card (Fin (Module.finrank ℝ E)) =
        Module.finrank ℝ E := by
    rw [Fintype.card_fin]
  let basis := basisOfLinearIndependentOfCardEqFinrank hli hcard
  refine ⟨basis, ?_, ?_⟩
  · intro i
    dsimp [basis]
    rw [coe_basisOfLinearIndependentOfCardEqFinrank]
  · intro i j
    rw [show basis i = smoothOrthoFrame (I := I) g x i x by
        dsimp [basis]
        rw [coe_basisOfLinearIndependentOfCardEqFinrank],
      show basis j = smoothOrthoFrame (I := I) g x j x by
        dsimp [basis]
        rw [coe_basisOfLinearIndependentOfCardEqFinrank]]
    exact horth i j

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem cometricTrace_eq
    (g : SmoothRiemannianMetric I M) (p : ℕ) (x : M)
    (D : Tensor0SSpace (p + 2) I x) :
    cometricDoubleTraceFib (I := I) g p x D =
      metricTraceFirstTwo0STensor (I := I) g D := by
  classical
  obtain ⟨basis, hbasis, horth⟩ := centeredBasis (I := I) g x
  have hinv : MetricInverseInBasis_gen (I := I) g x basis
      (identityInvMetric (Idx := Fin (Module.finrank ℝ E))) := by
    simpa [identityInvMetric, diagonalInvMetric] using
      metricInverseInBasis_of_orthonormal (I := I) g basis horth
  apply tensor0SSpace_ext (𝕜 := ℝ) p x
  intro tail
  rw [cometricDoubleTraceFib_eq_orthoFrame_diag (I := I) g p x
    (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x) D]
  rw [metricTraceFirstTwo0STensor_apply,
    metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g basis
      (identityInvMetric (Idx := Fin (Module.finrank ℝ E))) hinv D tail]
  simp only [tensor0SSpace_sum_apply]
  simp only [metricTrace0S2InBasis, identityInvMetric, diagonalInvMetric, hbasis,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rfl

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem exists_trace31
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 3) (k : ℕ) :
    ∃ e : Fin (3 + k) ≃ Fin ((1 + k) + 2),
      iterCov (I := I) g 1
          (metricTraceFirstTwoField (I := I) (M := M) g A) k =
        metricTraceFirstTwoField (I := I) (M := M) g
          (MultilinearSection.domDomCongr (𝕜 := ℝ) (F := E) (IB := I)
            (E := TangentSpace I) (∞ : WithTop ℕ∞) e
            (iterCov (I := I) g 3 A k)) := by
  classical
  induction k with
  | zero =>
      refine ⟨Equiv.refl _, ?_⟩
      change metricTraceFirstTwoField (I := I) (M := M) g A =
        metricTraceFirstTwoField (I := I) (M := M) g
          (MultilinearSection.domDomCongr (𝕜 := ℝ) (F := E) (IB := I)
            (E := TangentSpace I) (∞ : WithTop ℕ∞) (Equiv.refl (Fin 3)) A)
      rw [MultilinearSection.domDomCongr_refl]
  | succ k ih =>
      obtain ⟨e, he⟩ := ih
      let cov := leviCivitaConnectionOfMetric (I := I) g
      have hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov 1 := by
        exact leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally_one
          (I := I) (M := M) g
      have hmc : IsMetricCompatible_gen (I := I) cov g := by
        exact leviCivitaConnectionOfMetric_isMetricCompatible (I := I) g
      have hA := iterCov_realizes (I := I) g A k
      have hreindex := totalNabla0SRealizes_domDomCongr (I := I) cov e _ _ hA
      have htrace := nablaRealizes_metricTraceFirstTwo (I := I) (M := M)
        (s := 1 + k) cov hcov g hmc _ _ hreindex
      rw [← he] at htrace
      have hout₀ := iterCov_realizes (I := I) g
        (metricTraceFirstTwoField (I := I) (M := M) g A) k
      have hout := Tensor0SBundle.totalNabla0SRealizes_unique (I := I) hout₀ htrace
      refine ⟨(frontExtendEquiv e).trans (traceNablaShuffle (1 + k)), ?_⟩
      rw [← MultilinearSection.domDomCongr_trans]
      exact hout

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem trace31_norm_le
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 3) (k : ℕ) (x : M) :
    normSq0S (I := I) g x (1 + k)
        (iterCov (I := I) g 1
          (metricTraceFirstTwoField (I := I) (M := M) g A) k x) ≤
      (Module.finrank ℝ E : ℝ) ^ ((1 + k) + 2) *
        normSq0S (I := I) g x (3 + k)
          (iterCov (I := I) g 3 A k x) := by
  classical
  obtain ⟨e, he⟩ := exists_trace31 (I := I) g A k
  rw [he]
  have htrace := trace_normSq_rank_le (I := I) g
    ((MultilinearSection.domDomCongr (𝕜 := ℝ) (F := E) (IB := I)
      (E := TangentSpace I) (∞ : WithTop ℕ∞) e
      (iterCov (I := I) g 3 A k)) x)
  rw [MultilinearSection.domDomCongr_apply] at htrace
  obtain ⟨basis, hON⟩ := exists_gOrthonormalBasis (I := I) g x
  have hinv : MetricInverseInBasis_gen (I := I) g x basis
      (identityInvMetric
        (Idx := Fin (Module.finrank ℝ (TangentSpace I x)))) := by
    have h' := metricInverseInBasis_of_orthonormal (I := I) g basis hON
    intro i j
    simpa [identityInvMetric, diagonalInvMetric] using h' i j
  have hperm :
      normSq0S (I := I) g x ((1 + k) + 2)
          ((iterCov (I := I) g 3 A k x).domDomCongr e) =
        normSq0S (I := I) g x (3 + k)
          (iterCov (I := I) g 3 A k x) :=
    normSq0S_domDomCongr (I := I) g x basis hinv e
      (iterCov (I := I) g 3 A k x)
  rw [metricTraceFirstTwoField_apply]
  exact htrace.trans_eq
    (congrArg
      (fun z => (Module.finrank ℝ E : ℝ) ^ ((1 + k) + 2) * z) hperm)

noncomputable def revJetThreeC (Λ : ℝ) : ℝ :=
  let L₁ := max (revJetOneC (E := E) Λ) Λ
  let D := thirdIteratedCovariantDerivativeComparisonConstant (E := E) 2 Λ L₁ Λ Λ
  Real.sqrt (Λ ^ 5) * (D * Real.sqrt (Module.finrank ℝ E : ℝ))

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem reverseJetThree
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ}
    (hEq : MetricUniformEquivalentOn (I := I) Set.univ gBase g₀ Λ)
    (hjet1 : MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g₀ gBase Λ)
    (hjet2 : MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g₀ gBase Λ)
    (hjet3 : MetricCovDerivOrderBoundOn (I := I) Set.univ 3 g₀ gBase Λ) :
    MetricCovDerivOrderBoundOn (I := I) Set.univ 3 gBase g₀
      (revJetThreeC (E := E) Λ) := by
  let C₁ : ℝ := revJetOneC (E := E) Λ
  have hrev1 := reverseJetOne (I := I) gBase g₀ hEq hjet1
  let L₁ : ℝ := max C₁ Λ
  have hrev1' :
      MetricCovDerivOrderBoundOn (I := I) Set.univ 1 gBase g₀ L₁ :=
    fun x hx => (hrev1 x hx).trans (le_max_left _ _)
  have hfwd1' :
      MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g₀ gBase L₁ :=
    fun x hx => (hjet1 x hx).trans (le_max_right _ _)
  let D : ℝ := thirdIteratedCovariantDerivativeComparisonConstant (E := E) 2 Λ L₁ Λ Λ
  have hD := third_iterated_covariant_derivative_le_comparison_constant (I := I) (K := Set.univ)
    g₀ gBase 2 (metricUniformEquivalentOn_symm (I := I) hEq)
      hrev1' hfwd1' hjet2 hjet3
  intro x _
  obtain ⟨basis, hON⟩ := exists_gOrthonormalBasis (I := I) g₀ x
  have hinv : MetricInverseInBasis_gen (I := I) g₀ x basis
      (identityInvMetric (Idx := Fin (Module.finrank ℝ (TangentSpace I x)))) :=
    metricInverseInBasis_of_orthonormal (I := I) g₀ basis hON
  rw [metricCovDerivNorm_eq_iterCov (I := I) gBase g₀ 3 basis hinv]
  have hcomp := sqrt_normSq0S_comp (I := I) hEq (Set.mem_univ x) 5
    (iterCov (I := I) g₀ 2 (metricTensorField (I := I) gBase) 3 x)
  have hthree := hD (metricTensorField (I := I) gBase) x (Set.mem_univ x)
  rw [metric_self_sum (I := I) gBase x 3] at hthree
  have hthree' :
      Real.sqrt (normSq0S (I := I) gBase x 5
        (iterCov (I := I) g₀ 2 (metricTensorField (I := I) gBase) 3 x)) ≤
        D * Real.sqrt (Module.finrank ℝ E : ℝ) := by
    simpa using hthree
  refine hcomp.trans ?_
  simpa [revJetThreeC, C₁, L₁, D] using
    (mul_le_mul_of_nonneg_left hthree' (Real.sqrt_nonneg (Λ ^ 5)))

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] in
private theorem connLowOne_eval
    (gBase g₀ : SmoothRiemannianMetric I M)
    (X Y Z W : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _)) (x : M) :
    covStep (I := I) g₀ 3 (metricLoweredConnectionDifferenceField (I := I) g₀ gBase) x
        (vec4 (I := I) (X x) (Y x) (Z x) (W x)) =
      g₀.inner x
        (covDerivConnectionDifference (I := I) g₀ gBase X Z Y x) (W x) := by
  classical
  let cov := leviCivitaConnectionOfMetric (I := I) g₀
  let hcov :=
    leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
      (I := I) (M := M) g₀
  let A : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _) :=
    ⟨fun p => PDE.DeTurck.connectionDifference (I := I) gBase g₀ p (Y p) (Z p),
      PDE.DeTurck.connectionDifference_contMDiff (I := I) gBase g₀ Y.contMDiff Z.contMDiff⟩
  let DY : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _) :=
    ⟨fun p => (cov (fun q => Y q) p) (X p), by
      intro p
      exact CovariantDerivative.cov_smooth_apply_contMDiffAt
        (I := I) cov hcov X Y p⟩
  let DZ : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _) :=
    ⟨fun p => (cov (fun q => Z q) p) (X p), by
      intro p
      exact CovariantDerivative.cov_smooth_apply_contMDiffAt
        (I := I) cov hcov X Z p⟩
  let DW : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _) :=
    ⟨fun p => (cov (fun q => W q) p) (X p), by
      intro p
      exact CovariantDerivative.cov_smooth_apply_contMDiffAt
        (I := I) cov hcov X W p⟩
  let slots : Fin 3 → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _)
    | ⟨0, _⟩ => Y
    | ⟨1, _⟩ => Z
    | ⟨2, _⟩ => W
  have hvec :
      vec4 (I := I) (X x) (Y x) (Z x) (W x) =
        Fin.cons (X x) (fun q : Fin 3 => slots q x) := by
    funext q
    fin_cases q <;> rfl
  have hfun :
      (fun p : M =>
        metricLoweredConnectionDifferenceField (I := I) g₀ gBase p
          (fun q : Fin 3 => slots q p)) =
        fun p : M => g₀.inner p (A p) (W p) := by
    funext p
    rfl
  have hpairfun :
      (fun p : M => g₀.inner p (A p) (W p)) =
        fun p : M =>
          metricTensorField (I := I) g₀ p
            (fun q : Fin 2 => (![A, W] : Fin 2 →
              ContMDiffSection I E (∞ : WithTop ℕ∞)
                (TangentSpace I : M → Type _)) q p) := by
    funext p
    rfl
  have hderiv :
      extDerivFun (I := I)
          (fun p : M =>
            metricLoweredConnectionDifferenceField (I := I) g₀ gBase p
              (fun q : Fin 3 => slots q p))
          x (X x) =
        g₀.inner x ((cov (fun p : M => A p) x) (X x)) (W x) +
          g₀.inner x (A x) (DW x) := by
    rw [hfun, hpairfun,
      metric_leibniz_extDeriv (I := I) g₀ g₀ ![A, W] X x,
      nabla_metric_zero (I := I) (LeviCivita (I := I) g₀) g₀
        (leviCivitaConnectionOfMetric_isMetricCompatible (I := I) g₀) X x]
    simp [Fin.sum_univ_two, metricTensorField_apply, cov, DW,
      LeviCivita_eq_leviCivitaConnectionOfMetric]
  have hcorr :
      (∑ q : Fin 3,
        metricLoweredConnectionDifferenceField (I := I) g₀ gBase x
          (Function.update (fun b : Fin 3 => slots b x) q
            ((cov (fun p : M => slots q p) x) (X x)))) =
        g₀.inner x
            (PDE.DeTurck.connectionDifference (I := I) gBase g₀ x (DY x) (Z x)) (W x) +
          g₀.inner x
            (PDE.DeTurck.connectionDifference (I := I) gBase g₀ x (Y x) (DZ x)) (W x) +
          g₀.inner x (A x) (DW x) := by
    rw [Fin.sum_univ_three]
    rfl
  rw [hvec, covStep_eval_smooth_slots (I := I) g₀ 3
    (metricLoweredConnectionDifferenceField (I := I) g₀ gBase) X slots x]
  rw [hderiv, hcorr]
  have hvalue :
      covDerivConnectionDifference (I := I) g₀ gBase X Z Y x =
        (cov (fun p : M => A p) x) (X x) -
          PDE.DeTurck.connectionDifference (I := I) gBase g₀ x (Y x) (DZ x) -
          PDE.DeTurck.connectionDifference (I := I) gBase g₀ x (DY x) (Z x) := by
    rw [covDerivConnectionDifference_eq]
    unfold covDerivDiff
    rw [LeviCivita_eq_leviCivitaConnectionOfMetric]
    dsimp only [A, DY, DZ, cov]
    rfl
  rw [hvalue]
  simp only [map_sub, ContinuousLinearMap.sub_apply]
  ring

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] in
private theorem connLowTwo_eval
    (gBase g₀ : SmoothRiemannianMetric I M)
    (D X Y Z W : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _)) (x : M) :
    iterCov (I := I) g₀ 3 (metricLoweredConnectionDifferenceField (I := I) g₀ gBase) 2 x
        (vec5 (I := I) (D x) (X x) (Y x) (Z x) (W x)) =
      g₀.inner x
        (Integral.Connection.covDerivConnectionDifference2
          (I := I) g₀ gBase D X Z Y x) (W x) := by
  classical
  let cov := leviCivitaConnectionOfMetric (I := I) g₀
  let hcov :=
    leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
      (I := I) (M := M) g₀
  let R : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _) :=
    ⟨fun p => covDerivConnectionDifference (I := I) g₀ gBase X Z Y p,
      covDerivConnectionDifference_contMDiff (I := I) g₀ gBase X Z Y⟩
  let DX : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _) :=
    ⟨fun p => (cov (fun q => X q) p) (D p), by
      intro p
      exact CovariantDerivative.cov_smooth_apply_contMDiffAt
        (I := I) cov hcov D X p⟩
  let DY : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _) :=
    ⟨fun p => (cov (fun q => Y q) p) (D p), by
      intro p
      exact CovariantDerivative.cov_smooth_apply_contMDiffAt
        (I := I) cov hcov D Y p⟩
  let DZ : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _) :=
    ⟨fun p => (cov (fun q => Z q) p) (D p), by
      intro p
      exact CovariantDerivative.cov_smooth_apply_contMDiffAt
        (I := I) cov hcov D Z p⟩
  let DW : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _) :=
    ⟨fun p => (cov (fun q => W q) p) (D p), by
      intro p
      exact CovariantDerivative.cov_smooth_apply_contMDiffAt
        (I := I) cov hcov D W p⟩
  let slots : Fin 4 → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _)
    | ⟨0, _⟩ => X
    | ⟨1, _⟩ => Y
    | ⟨2, _⟩ => Z
    | ⟨3, _⟩ => W
  have hvec :
      vec5 (I := I) (D x) (X x) (Y x) (Z x) (W x) =
        Fin.cons (D x) (fun q : Fin 4 => slots q x) := by
    funext q
    fin_cases q <;> rfl
  have hfun :
      (fun p : M =>
        covStep (I := I) g₀ 3 (metricLoweredConnectionDifferenceField (I := I) g₀ gBase) p
          (fun q : Fin 4 => slots q p)) =
        fun p : M => g₀.inner p (R p) (W p) := by
    funext p
    have ht :
        (fun q : Fin 4 => slots q p) =
          vec4 (I := I) (X p) (Y p) (Z p) (W p) := by
      funext q
      fin_cases q <;> rfl
    rw [ht]
    exact connLowOne_eval (I := I) gBase g₀ X Y Z W p
  have hpairfun :
      (fun p : M => g₀.inner p (R p) (W p)) =
        fun p : M =>
          metricTensorField (I := I) g₀ p
            (fun q : Fin 2 => (![R, W] : Fin 2 →
              ContMDiffSection I E (∞ : WithTop ℕ∞)
                (TangentSpace I : M → Type _)) q p) := by
    funext p
    rfl
  have hderiv :
      extDerivFun (I := I)
          (fun p : M =>
            covStep (I := I) g₀ 3
              (metricLoweredConnectionDifferenceField (I := I) g₀ gBase) p
              (fun q : Fin 4 => slots q p))
          x (D x) =
        g₀.inner x ((cov (fun p : M => R p) x) (D x)) (W x) +
          g₀.inner x (R x) (DW x) := by
    rw [hfun, hpairfun,
      metric_leibniz_extDeriv (I := I) g₀ g₀ ![R, W] D x,
      nabla_metric_zero (I := I) (LeviCivita (I := I) g₀) g₀
        (leviCivitaConnectionOfMetric_isMetricCompatible (I := I) g₀) D x]
    simp [Fin.sum_univ_two, metricTensorField_apply, cov, DW,
      LeviCivita_eq_leviCivitaConnectionOfMetric]
  have hcorr0 :
      covStep (I := I) g₀ 3 (metricLoweredConnectionDifferenceField (I := I) g₀ gBase) x
          (Function.update (fun b : Fin 4 => slots b x) 0
            ((cov (fun p : M => slots 0 p) x) (D x))) =
        g₀.inner x
          (covDerivConnectionDifference (I := I) g₀ gBase DX Z Y x) (W x) := by
    have ht :
        Function.update (fun b : Fin 4 => slots b x) 0
            ((cov (fun p : M => slots 0 p) x) (D x)) =
          vec4 (I := I) (DX x) (Y x) (Z x) (W x) := by
      funext q
      fin_cases q <;> simp [slots, DX, vec4]
    rw [ht]
    exact connLowOne_eval (I := I) gBase g₀ DX Y Z W x
  have hcorr1 :
      covStep (I := I) g₀ 3 (metricLoweredConnectionDifferenceField (I := I) g₀ gBase) x
          (Function.update (fun b : Fin 4 => slots b x) 1
            ((cov (fun p : M => slots 1 p) x) (D x))) =
        g₀.inner x
          (covDerivConnectionDifference (I := I) g₀ gBase X Z DY x) (W x) := by
    have ht :
        Function.update (fun b : Fin 4 => slots b x) 1
            ((cov (fun p : M => slots 1 p) x) (D x)) =
          vec4 (I := I) (X x) (DY x) (Z x) (W x) := by
      funext q
      fin_cases q <;> simp [slots, DY, vec4]
    rw [ht]
    exact connLowOne_eval (I := I) gBase g₀ X DY Z W x
  have hcorr2 :
      covStep (I := I) g₀ 3 (metricLoweredConnectionDifferenceField (I := I) g₀ gBase) x
          (Function.update (fun b : Fin 4 => slots b x) 2
            ((cov (fun p : M => slots 2 p) x) (D x))) =
        g₀.inner x
          (covDerivConnectionDifference (I := I) g₀ gBase X DZ Y x) (W x) := by
    have ht :
        Function.update (fun b : Fin 4 => slots b x) 2
            ((cov (fun p : M => slots 2 p) x) (D x)) =
          vec4 (I := I) (X x) (Y x) (DZ x) (W x) := by
      funext q
      fin_cases q <;> simp [slots, DZ, vec4]
    rw [ht]
    exact connLowOne_eval (I := I) gBase g₀ X Y DZ W x
  have hcorr3 :
      covStep (I := I) g₀ 3 (metricLoweredConnectionDifferenceField (I := I) g₀ gBase) x
          (Function.update (fun b : Fin 4 => slots b x) 3
            ((cov (fun p : M => slots 3 p) x) (D x))) =
        g₀.inner x (R x) (DW x) := by
    have ht :
        Function.update (fun b : Fin 4 => slots b x) 3
            ((cov (fun p : M => slots 3 p) x) (D x)) =
          vec4 (I := I) (X x) (Y x) (Z x) (DW x) := by
      funext q
      fin_cases q <;> simp [slots, DW, vec4]
    rw [ht]
    exact connLowOne_eval (I := I) gBase g₀ X Y Z DW x
  have hcorr :
      (∑ q : Fin 4,
        covStep (I := I) g₀ 3 (metricLoweredConnectionDifferenceField (I := I) g₀ gBase) x
          (Function.update (fun b : Fin 4 => slots b x) q
            ((cov (fun p : M => slots q p) x) (D x)))) =
        g₀.inner x
            (covDerivConnectionDifference (I := I) g₀ gBase DX Z Y x) (W x) +
          g₀.inner x
            (covDerivConnectionDifference (I := I) g₀ gBase X Z DY x) (W x) +
          g₀.inner x
            (covDerivConnectionDifference (I := I) g₀ gBase X DZ Y x) (W x) +
          g₀.inner x (R x) (DW x) := by
    rw [Fin.sum_univ_four, hcorr0, hcorr1, hcorr2, hcorr3]
  change covStep (I := I) g₀ 4
      (covStep (I := I) g₀ 3 (metricLoweredConnectionDifferenceField (I := I) g₀ gBase)) x
        (vec5 (I := I) (D x) (X x) (Y x) (Z x) (W x)) = _
  rw [hvec, covStep_eval_smooth_slots (I := I) g₀ 4
    (covStep (I := I) g₀ 3 (metricLoweredConnectionDifferenceField (I := I) g₀ gBase))
      D slots x]
  rw [hderiv, hcorr]
  have hvalue :
      Integral.Connection.covDerivConnectionDifference2 (I := I) g₀ gBase D X Z Y x =
        (cov (fun p : M => R p) x) (D x) -
          covDerivConnectionDifference (I := I) g₀ gBase DX Z Y x -
          covDerivConnectionDifference (I := I) g₀ gBase X DZ Y x -
          covDerivConnectionDifference (I := I) g₀ gBase X Z DY x := by
    rw [Integral.Connection.covDerivConnectionDifference2_eq]
    rw [LeviCivita_eq_leviCivitaConnectionOfMetric]
    dsimp only [R, DX, DY, DZ, cov]
    rfl
  rw [hvalue]
  simp only [map_sub, ContinuousLinearMap.sub_apply]
  ring

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
private theorem connLow_unit
    (g₀ gBase : SmoothRiemannianMetric I M) :
    ccUnitField (I := I) g₀ 3 (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ gBase) =
      metricLoweredConnectionDifferenceField (I := I) g₀ gBase :=
  MixedSection.toMultilinearSection_fromMultilinearSection
    (𝕜 := ℝ) (F := E) (IB := I)
    (E := (TangentSpace I : M → Type _)) ∞
      (metricLoweredConnectionDifferenceField (I := I) g₀ gBase)

noncomputable def connectionDifferenceZeroSqC (Λ : ℝ) : ℝ :=
  let C₁ := revJetOneC (E := E) Λ
  let C := 3 / 2 * Λ ^ 3 * C₁
  (Module.finrank ℝ E : ℝ) ^ 3 * C ^ 2


theorem uniformConnectionDifferenceZero
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ}
    (hΛ : 1 ≤ Λ)
    (hcomp : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ Λ * gBase.inner x v v)
    (hjet1 : MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g₀ gBase Λ) :
    ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + 0) x
          ((iteratedCovGrad (I := I) g₀ 1 2 0
            (connectionDifferenceSection (I := I) gBase g₀)).toSection x) ≤
        connectionDifferenceZeroSqC (E := E) Λ := by
  classical
  have hEq : MetricUniformEquivalentOn (I := I) Set.univ gBase g₀ Λ :=
    ⟨hΛ, fun x _ v => hcomp x v⟩
  have hEq' := metricUniformEquivalentOn_symm (I := I) hEq
  let C₁ : ℝ := revJetOneC (E := E) Λ
  have hrev1 := reverseJetOne (I := I) gBase g₀ hEq hjet1
  have hC₁0 : 0 ≤ C₁ := by
    dsimp [C₁, revJetOneC]
    positivity
  let C : ℝ := 3 / 2 * Λ ^ 3 * C₁
  have hC0 : 0 ≤ C := by
    dsimp [C]
    positivity
  let d : ℝ := Module.finrank ℝ E
  have hd0 : 0 ≤ d := by
    dsimp [d]
    positivity
  intro x
  obtain ⟨basis, _hbasis, horth⟩ := centeredBasis (I := I) g₀ x
  have hinv : MetricInverseInBasis_gen (I := I) g₀ x basis
      (identityInvMetric (Idx := Fin (Module.finrank ℝ E))) := by
    simpa [identityInvMetric, diagonalInvMetric] using
      metricInverseInBasis_of_orthonormal (I := I) g₀ basis horth
  have hunit : ∀ i, g₀.inner x (basis i) (basis i) = 1 := by
    intro i
    rw [horth i i]
    simp
  let T : Tensor0SSpace 3 I x :=
    metricLoweredConnectionDifferenceField (I := I) g₀ gBase x
  have hcompB : ∀ slots : Fin 3 → Fin (Module.finrank ℝ E),
      |component0S (I := I) basis T slots| ≤ C := by
    intro slots
    let N : TangentSpace I x :=
      PDE.DeTurck.connectionDifference (I := I) gBase g₀ x
        (basis (slots 0)) (basis (slots 1))
    have hNN : Real.sqrt (g₀.inner x N N) ≤ C := by
      have h := connectionDifference_gJet_le (I := I) hEq' hrev1 (Set.mem_univ x)
        (basis (slots 1)) (basis (slots 0))
      rw [hunit (slots 1), hunit (slots 0)] at h
      simpa [C, N, PDE.DeTurck.connectionDifference] using h
    have hval :
        component0S (I := I) basis T slots =
          g₀.inner x N (basis (slots 2)) := by
      rfl
    rw [hval]
    calc
      |g₀.inner x N (basis (slots 2))| ≤
          Real.sqrt (g₀.inner x N N) *
            Real.sqrt (g₀.inner x (basis (slots 2)) (basis (slots 2))) :=
        abs_metric_inner_le_sqrt_metric_quadratic
          (I := I) (M := M) g₀ x N (basis (slots 2))
      _ = Real.sqrt (g₀.inner x N N) := by
        rw [hunit (slots 2)]
        simp
      _ ≤ C := hNN
  have hcard :=
    normSq0S_le_card_of_component_bound (I := I) g₀ x 3 basis hinv T C hC0 hcompB
  have hcardval :
      (Fintype.card (Fin 3 → Fin (Module.finrank ℝ E)) : ℝ) =
        (Module.finrank ℝ E : ℝ) ^ 3 := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    push_cast
    ring
  rw [hcardval] at hcard
  calc
    riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + 0) x
          ((iteratedCovGrad (I := I) g₀ 1 2 0
            (connectionDifferenceSection (I := I) gBase g₀)).toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + 0) x
          ((iteratedCovGrad (I := I) g₀ 0 3 0
            (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ gBase)).toSection x) :=
      (metricLoweredConnectionDifferenceCoefficient_fiber_norm_sq_eq (I := I) (M := M) g₀ gBase 0 x).symm
    _ = normSq0S (I := I) g₀ x 3 T := by
      rw [riemannianFiberNormSq_iterCovGrad_eq (I := I) g₀ 3 0
        (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ gBase) x,
        connLow_unit (I := I) g₀ gBase]
      rfl
    _ ≤ d ^ 3 * C ^ 2 := by
      simpa [d] using hcard
    _ = connectionDifferenceZeroSqC (E := E) Λ := rfl

noncomputable def connectionDifferenceOneSqC (Λ : ℝ) : ℝ :=
  let C₁ := revJetOneC (E := E) Λ
  let C₂ := revJetTwoC (E := E) Λ
  let C := 3 / 2 * Λ ^ 4 * (C₂ + Λ * C₁ ^ 2)
  (Module.finrank ℝ E : ℝ) ^ 4 * C ^ 2


theorem uniformConnectionDifferenceOne
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ}
    (hΛ : 1 ≤ Λ)
    (hcomp : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ Λ * gBase.inner x v v)
    (hjet1 : MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g₀ gBase Λ)
    (hjet2 : MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g₀ gBase Λ) :
    ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + 1) x
          ((iteratedCovGrad (I := I) g₀ 1 2 1
            (connectionDifferenceSection (I := I) gBase g₀)).toSection x) ≤
        connectionDifferenceOneSqC (E := E) Λ := by
  classical
  have hEq : MetricUniformEquivalentOn (I := I) Set.univ gBase g₀ Λ :=
    ⟨hΛ, fun x _ v => hcomp x v⟩
  have hEq' := metricUniformEquivalentOn_symm (I := I) hEq
  let C₁ : ℝ := revJetOneC (E := E) Λ
  let C₂ : ℝ := revJetTwoC (E := E) Λ
  have hrev1 := reverseJetOne (I := I) gBase g₀ hEq hjet1
  have hrev2 := reverseJetTwo (I := I) gBase g₀ hEq hjet1 hjet2
  have hC₁0 : 0 ≤ C₁ := by
    dsimp [C₁, revJetOneC]
    positivity
  have hC₂0 : 0 ≤ C₂ := by
    dsimp [C₂, revJetTwoC]
    exact le_max_left _ _
  let C : ℝ := 3 / 2 * Λ ^ 4 * (C₂ + Λ * C₁ ^ 2)
  have hC0 : 0 ≤ C := by
    dsimp [C]
    positivity
  let d : ℝ := Module.finrank ℝ E
  have hd0 : 0 ≤ d := by
    dsimp [d]
    positivity
  intro x
  obtain ⟨basis, _hbasis, horth⟩ := centeredBasis (I := I) g₀ x
  have hinv : MetricInverseInBasis_gen (I := I) g₀ x basis
      (identityInvMetric (Idx := Fin (Module.finrank ℝ E))) := by
    simpa [identityInvMetric, diagonalInvMetric] using
      metricInverseInBasis_of_orthonormal (I := I) g₀ basis horth
  have hunit : ∀ i, g₀.inner x (basis i) (basis i) = 1 := by
    intro i
    rw [horth i i]
    simp
  let T : Tensor0SSpace 4 I x :=
    iterCov (I := I) g₀ 3 (metricLoweredConnectionDifferenceField (I := I) g₀ gBase) 1 x
  have hcompB : ∀ slots : Fin 4 → Fin (Module.finrank ℝ E),
      |component0S (I := I) basis T slots| ≤ C := by
    intro slots
    let X : ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _) :=
      ⟨smoothExtensionTangent (I := I) x (basis (slots 0)),
        smoothExtensionTangent_contMDiff (I := I) x (basis (slots 0))⟩
    let Y : ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _) :=
      ⟨smoothExtensionTangent (I := I) x (basis (slots 1)),
        smoothExtensionTangent_contMDiff (I := I) x (basis (slots 1))⟩
    let Z : ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _) :=
      ⟨smoothExtensionTangent (I := I) x (basis (slots 2)),
        smoothExtensionTangent_contMDiff (I := I) x (basis (slots 2))⟩
    let W : ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _) :=
      ⟨smoothExtensionTangent (I := I) x (basis (slots 3)),
        smoothExtensionTangent_contMDiff (I := I) x (basis (slots 3))⟩
    have hX : X x = basis (slots 0) :=
      smoothExtensionTangent_eq (I := I) x (basis (slots 0))
    have hY : Y x = basis (slots 1) :=
      smoothExtensionTangent_eq (I := I) x (basis (slots 1))
    have hZ : Z x = basis (slots 2) :=
      smoothExtensionTangent_eq (I := I) x (basis (slots 2))
    have hW : W x = basis (slots 3) :=
      smoothExtensionTangent_eq (I := I) x (basis (slots 3))
    have hvec : (fun a : Fin 4 => basis (slots a)) =
        vec4 (I := I) (basis (slots 0)) (basis (slots 1))
          (basis (slots 2)) (basis (slots 3)) := by
      funext a
      fin_cases a <;> simp [vec4]
    have hval :
        component0S (I := I) basis T slots =
          g₀.inner x
            (covDerivConnectionDifference (I := I) g₀ gBase X Z Y x) (W x) := by
      rw [component0S]
      rw [show (fun a : Fin 4 => basis (slots a)) =
          vec4 (I := I) (X x) (Y x) (Z x) (W x) by
        rw [hX, hY, hZ, hW]
        exact hvec]
      exact connLowOne_eval (I := I) gBase g₀ X Y Z W x
    let N : TangentSpace I x :=
      covDerivConnectionDifference (I := I) g₀ gBase X Z Y x
    have hNN : Real.sqrt (g₀.inner x N N) ≤ C := by
      have h := covDerivConnectionDifference_gJet_le (I := I)
        hEq' hrev1 hrev2 (Set.mem_univ x)
        (basis (slots 0)) (basis (slots 2)) (basis (slots 1))
      rw [hunit (slots 0), hunit (slots 2), hunit (slots 1)] at h
      simpa [C, N, X, Y, Z] using h
    rw [hval]
    change |g₀.inner x N (W x)| ≤ C
    calc
      |g₀.inner x N (W x)| ≤
          Real.sqrt (g₀.inner x N N) *
            Real.sqrt (g₀.inner x (W x) (W x)) :=
        abs_metric_inner_le_sqrt_metric_quadratic
          (I := I) (M := M) g₀ x N (W x)
      _ = Real.sqrt (g₀.inner x N N) := by
        rw [hW, hunit (slots 3)]
        simp
      _ ≤ C := hNN
  have hcard :=
    normSq0S_le_card_of_component_bound (I := I) g₀ x 4 basis hinv T C hC0 hcompB
  have hcardval :
      (Fintype.card (Fin 4 → Fin (Module.finrank ℝ E)) : ℝ) =
        (Module.finrank ℝ E : ℝ) ^ 4 := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    push_cast
    ring
  rw [hcardval] at hcard
  calc
    riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + 1) x
          ((iteratedCovGrad (I := I) g₀ 1 2 1
            (connectionDifferenceSection (I := I) gBase g₀)).toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + 1) x
          ((iteratedCovGrad (I := I) g₀ 0 3 1
            (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ gBase)).toSection x) :=
      (metricLoweredConnectionDifferenceCoefficient_fiber_norm_sq_eq (I := I) (M := M) g₀ gBase 1 x).symm
    _ = normSq0S (I := I) g₀ x 4 T := by
      rw [riemannianFiberNormSq_iterCovGrad_eq (I := I) g₀ 3 1
        (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ gBase) x,
        connLow_unit (I := I) g₀ gBase]
    _ ≤ d ^ 4 * C ^ 2 := by
      simpa [d] using hcard
    _ = connectionDifferenceOneSqC (E := E) Λ := rfl

noncomputable def connectionDifferenceTwoC (Λ : ℝ) : ℝ :=
  let C₁ := revJetOneC (E := E) Λ
  let C₂ := revJetTwoC (E := E) Λ
  let C₃ := revJetThreeC (E := E) Λ
  let C :=
    3 / 2 * Λ ^ 5 * C₃ +
      9 / 2 * Λ ^ 6 * C₁ * C₂ +
      3 * Λ ^ 7 * C₁ ^ 3
  (Module.finrank ℝ E : ℝ) ^ 5 * C ^ 2


theorem uniformConnectionDifferenceTwo
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ}
    (hΛ : 1 ≤ Λ)
    (hcomp : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ Λ * gBase.inner x v v)
    (hjet1 : MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g₀ gBase Λ)
    (hjet2 : MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g₀ gBase Λ)
    (hjet3 : MetricCovDerivOrderBoundOn (I := I) Set.univ 3 g₀ gBase Λ) :
    ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + 2) x
          ((iteratedCovGrad (I := I) g₀ 1 2 2
            (connectionDifferenceSection (I := I) gBase g₀)).toSection x) ≤
        connectionDifferenceTwoC (E := E) Λ := by
  classical
  have hEq : MetricUniformEquivalentOn (I := I) Set.univ gBase g₀ Λ :=
    ⟨hΛ, fun x _ v => hcomp x v⟩
  have hEq' := metricUniformEquivalentOn_symm (I := I) hEq
  let C₁ : ℝ := revJetOneC (E := E) Λ
  let C₂ : ℝ := revJetTwoC (E := E) Λ
  let C₃ : ℝ := revJetThreeC (E := E) Λ
  have hrev1 := reverseJetOne (I := I) gBase g₀ hEq hjet1
  have hrev2 := reverseJetTwo (I := I) gBase g₀ hEq hjet1 hjet2
  have hrev3 := reverseJetThree (I := I) gBase g₀ hEq hjet1 hjet2 hjet3
  have hC₁0 : 0 ≤ C₁ := by
    dsimp [C₁, revJetOneC]
    positivity
  have hC₂0 : 0 ≤ C₂ := by
    dsimp [C₂, revJetTwoC]
    exact le_max_left _ _
  have hC₃0 : 0 ≤ C₃ := by
    dsimp [C₃, revJetThreeC]
    exact mul_nonneg (Real.sqrt_nonneg _) <|
      mul_nonneg (le_max_left _ _) (Real.sqrt_nonneg _)
  let C : ℝ :=
    3 / 2 * Λ ^ 5 * C₃ +
      9 / 2 * Λ ^ 6 * C₁ * C₂ +
      3 * Λ ^ 7 * C₁ ^ 3
  have hC0 : 0 ≤ C := by
    dsimp [C]
    positivity
  let d : ℝ := Module.finrank ℝ E
  have hd0 : 0 ≤ d := by
    dsimp [d]
    positivity
  intro x
  obtain ⟨basis, _hbasis, horth⟩ := centeredBasis (I := I) g₀ x
  have hinv : MetricInverseInBasis_gen (I := I) g₀ x basis
      (identityInvMetric (Idx := Fin (Module.finrank ℝ E))) := by
    simpa [identityInvMetric, diagonalInvMetric] using
      metricInverseInBasis_of_orthonormal (I := I) g₀ basis horth
  have hunit : ∀ i, g₀.inner x (basis i) (basis i) = 1 := by
    intro i
    rw [horth i i]
    simp
  let T : Tensor0SSpace 5 I x :=
    iterCov (I := I) g₀ 3 (metricLoweredConnectionDifferenceField (I := I) g₀ gBase) 2 x
  have hcompB : ∀ slots : Fin 5 → Fin (Module.finrank ℝ E),
      |component0S (I := I) basis T slots| ≤ C := by
    intro slots
    let D : ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _) :=
      ⟨smoothExtensionTangent (I := I) x (basis (slots 0)),
        smoothExtensionTangent_contMDiff (I := I) x (basis (slots 0))⟩
    let X : ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _) :=
      ⟨smoothExtensionTangent (I := I) x (basis (slots 1)),
        smoothExtensionTangent_contMDiff (I := I) x (basis (slots 1))⟩
    let Y : ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _) :=
      ⟨smoothExtensionTangent (I := I) x (basis (slots 2)),
        smoothExtensionTangent_contMDiff (I := I) x (basis (slots 2))⟩
    let Z : ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _) :=
      ⟨smoothExtensionTangent (I := I) x (basis (slots 3)),
        smoothExtensionTangent_contMDiff (I := I) x (basis (slots 3))⟩
    let W : ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _) :=
      ⟨smoothExtensionTangent (I := I) x (basis (slots 4)),
        smoothExtensionTangent_contMDiff (I := I) x (basis (slots 4))⟩
    have hD : D x = basis (slots 0) := by
      exact smoothExtensionTangent_eq (I := I) x (basis (slots 0))
    have hX : X x = basis (slots 1) := by
      exact smoothExtensionTangent_eq (I := I) x (basis (slots 1))
    have hY : Y x = basis (slots 2) := by
      exact smoothExtensionTangent_eq (I := I) x (basis (slots 2))
    have hZ : Z x = basis (slots 3) := by
      exact smoothExtensionTangent_eq (I := I) x (basis (slots 3))
    have hW : W x = basis (slots 4) := by
      exact smoothExtensionTangent_eq (I := I) x (basis (slots 4))
    have hvec : (fun a : Fin 5 => basis (slots a)) =
        vec5 (I := I) (basis (slots 0)) (basis (slots 1))
          (basis (slots 2)) (basis (slots 3)) (basis (slots 4)) := by
      funext a
      fin_cases a <;> simp [vec5]
    have hval :
        component0S (I := I) basis T slots =
          g₀.inner x
            (Integral.Connection.covDerivConnectionDifference2
              (I := I) g₀ gBase D X Z Y x) (W x) := by
      rw [component0S]
      rw [show (fun a : Fin 5 => basis (slots a)) =
          vec5 (I := I) (D x) (X x) (Y x) (Z x) (W x) by
        rw [hD, hX, hY, hZ, hW]
        exact hvec]
      exact connLowTwo_eval (I := I) gBase g₀ D X Y Z W x
    let N : TangentSpace I x :=
      Integral.Connection.covDerivConnectionDifference2
        (I := I) g₀ gBase D X Z Y x
    have hNN : Real.sqrt (g₀.inner x N N) ≤ C := by
      have h := covDConnectionDifference2_gJet_le (I := I)
        hEq' hrev1 hrev2 hrev3 (Set.mem_univ x)
        (basis (slots 0)) (basis (slots 1))
        (basis (slots 3)) (basis (slots 2))
      rw [hunit (slots 0), hunit (slots 1),
        hunit (slots 3), hunit (slots 2)] at h
      simpa [C, N, D, X, Y, Z] using h
    rw [hval]
    change |g₀.inner x N (W x)| ≤ C
    calc
      |g₀.inner x N (W x)| ≤
          Real.sqrt (g₀.inner x N N) *
            Real.sqrt (g₀.inner x (W x) (W x)) :=
        abs_metric_inner_le_sqrt_metric_quadratic
          (I := I) (M := M) g₀ x N (W x)
      _ = Real.sqrt (g₀.inner x N N) := by
        rw [hW, hunit (slots 4)]
        simp
      _ ≤ C := hNN
  have hcard :=
    normSq0S_le_card_of_component_bound (I := I) g₀ x 5 basis hinv T C hC0 hcompB
  have hcardval :
      (Fintype.card (Fin 5 → Fin (Module.finrank ℝ E)) : ℝ) =
        (Module.finrank ℝ E : ℝ) ^ 5 := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    push_cast
    ring
  rw [hcardval] at hcard
  calc
    riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + 2) x
          ((iteratedCovGrad (I := I) g₀ 1 2 2
            (connectionDifferenceSection (I := I) gBase g₀)).toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + 2) x
          ((iteratedCovGrad (I := I) g₀ 0 3 2
            (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ gBase)).toSection x) :=
      (metricLoweredConnectionDifferenceCoefficient_fiber_norm_sq_eq (I := I) (M := M) g₀ gBase 2 x).symm
    _ = normSq0S (I := I) g₀ x 5 T := by
      rw [riemannianFiberNormSq_iterCovGrad_eq (I := I) g₀ 3 2
        (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ gBase) x,
        connLow_unit (I := I) g₀ gBase]
    _ ≤ d ^ 5 * C ^ 2 := by
      simpa [d] using hcard
    _ = connectionDifferenceTwoC (E := E) Λ := rfl

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
private theorem connLow_self_zero
    (g : SmoothRiemannianMetric I M) :
    metricLoweredConnectionDifferenceCoefficient (I := I) g g = 0 := by
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g
  intro x
  apply ContinuousMultilinearMap.ext
  intro m
  change unitModel (I := I) (M := M) g 3
      (metricLoweredConnectionDifferenceCoefficient (I := I) g g) x m = 0
  rw [connectionDifferenceLoweredCc_unitModel_apply']
  rw [PDE.DeTurck.connectionDifference_self]
  simp

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private theorem wXi_base_eq
    (gBase g₀ : SmoothRiemannianMetric I M) :
    metricLoweredConnectionDifference (I := I) (M := M) g₀ g₀ gBase =
      -metricLoweredConnectionDifferenceCoefficient (I := I) g₀ gBase := by
  unfold metricLoweredConnectionDifference
  rw [connLow_self_zero (I := I) g₀, zero_sub]

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem cometricCast_self
    (g : SmoothRiemannianMetric I M) :
    cometricCastG0 (I := I) g g =
      cometricDoubleTraceField (I := I) g 1 := by
  apply SmoothCcTensor.ext
  rfl

omit [NeZero (Module.finrank ℝ E)] in
private theorem wOmega_base_eq
    (gBase g₀ : SmoothRiemannianMetric I M) :
    deTurckVectorFieldCovector (I := I) (M := M) g₀ g₀ gBase =
      operatorFieldApply (I := I) (M := M) g₀ 3 1
        (cometricDoubleTraceField (I := I) g₀ 1)
        (-metricLoweredConnectionDifferenceCoefficient (I := I) g₀ gBase) := by
  unfold deTurckVectorFieldCovector
  rw [wXi_base_eq (I := I) gBase g₀, cometricCast_self (I := I) g₀]

private theorem wOmega_trace
    (gBase g₀ : SmoothRiemannianMetric I M) :
    ccUnitField (I := I) g₀ 1
        (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₀ gBase) =
      metricTraceFirstTwoField (I := I) (M := M) g₀
        (ccUnitField (I := I) g₀ 3
          (-metricLoweredConnectionDifferenceCoefficient (I := I) g₀ gBase)) := by
  refine DFunLike.ext _ _ (fun x => ?_)
  rw [wOmega_base_eq (I := I) gBase g₀]
  rw [ccUnitField_apply, operatorFieldApplication_toSection, ContinuousLinearMap.comp_apply,
    metricTraceFirstTwoField_apply, ccUnitField_apply,
    cometricDoubleTraceField_toSection]
  exact cometricTrace_eq (I := I) g₀ 1 x
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
      (-metricLoweredConnectionDifferenceCoefficient (I := I) g₀ gBase).toSection x)
      (unitZeroSec (I := I) (M := M) x))

omit [NeZero (Module.finrank ℝ E)] in
private theorem wAlphaA_shift
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (i : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 0 2 i
          (deTurckVectorFieldCovariantDerivativeLoweredBase (I := I) (M := M) g₀ g₁ g_bg)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (1 + (i + 1)) x
        ((iteratedCovGrad (I := I) g₀ 0 1 (i + 1)
          (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g_bg)).toSection x) := by
  calc
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 0 2 i
          (deTurckVectorFieldCovariantDerivativeLoweredBase (I := I) (M := M) g₀ g₁ g_bg)).toSection x)
        =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 0 2 i
          (covGrad (I := I) (M := M) g₀ 0 1
            (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g_bg))).toSection x) := by
          rw [deTurckVectorFieldCovariantDerivativeLoweredBase]
          exact riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection
            (I := I) (M := M) g₀ (Equiv.swap (0 : Fin 2) 1)
            (covGrad (I := I) (M := M) g₀ 0 1
              (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g_bg)) i x
    _ =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (1 + (i + 1)) x
        ((iteratedCovGrad (I := I) g₀ 0 1 (i + 1)
          (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g_bg)).toSection x) :=
      riemannianFiberNormSq_iteratedCovGrad_covGrad_comm_rs (I := I) (M := M) g₀ 0 1 i
        (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g_bg) x

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem riemannianFiberNormSq_neg
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (v : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (-v) =
      riemannianFiberNormSq (I := I) (M := M) g r s x v := by
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise
      (I := I) (M := M) g r s x (-v),
    riemannianFiberNormSq_eq_tensorInnerPointwise
      (I := I) (M := M) g r s x v]
  rw [TensorRSSpace.toModel_neg]
  rw [← neg_one_smul ℝ
    (TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
      (r := r) (s := s) (x := x) v),
    tensorInnerPointwise_smul_left, tensorInnerPointwise_smul_right]
  ring

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem riemannianFiberNormSq_iter_neg
    (g : SmoothRiemannianMetric I M) (r s j : ℕ)
    (W : SmoothCcTensor g r s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g r (s + j) x
        ((iteratedCovGrad (I := I) g r s j (-W)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g r (s + j) x
        ((iteratedCovGrad (I := I) g r s j W).toSection x) := by
  rw [iteratedCovGrad_neg]
  rw [show
    ((-(iteratedCovGrad (I := I) g r s j W)).toSection x) =
        -((iteratedCovGrad (I := I) g r s j W).toSection x) from by
      rw [SmoothCcTensor.toSection_neg]
      rfl]
  exact riemannianFiberNormSq_neg (I := I) g r (s + j) x _


noncomputable def alphaOneC (Λ : ℝ) : ℝ :=
  Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 5 * connectionDifferenceTwoC (E := E) Λ)

private theorem uniformOmegaTwo_of
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ}
    (hΛ : 1 ≤ Λ)
    (hcomp : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ Λ * gBase.inner x v v)
    (hjet1 : MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g₀ gBase Λ)
    (hjet2 : MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g₀ gBase Λ)
    (hjet3 : MetricCovDerivOrderBoundOn (I := I) Set.univ 3 g₀ gBase Λ) :
    ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (1 + 2) x
        ((iteratedCovGrad (I := I) g₀ 0 1 2
          (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₀ gBase)).toSection x) ≤
        alphaOneC (E := E) Λ ^ 2 := by
  let KC : ℝ := connectionDifferenceTwoC (E := E) Λ
  have hKC0 : 0 ≤ KC := by
    dsimp [KC, connectionDifferenceTwoC]
    positivity
  have hC := uniformConnectionDifferenceTwo (I := I) gBase g₀
    hΛ hcomp hjet1 hjet2 hjet3
  let d : ℝ := Module.finrank ℝ E
  have hd0 : 0 ≤ d := by
    dsimp [d]
    positivity
  intro x
  rw [riemannianFiberNormSq_iterCovGrad_eq (I := I) g₀ 1 2
    (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₀ gBase) x,
    wOmega_trace (I := I) gBase g₀]
  calc
    normSq0S (I := I) g₀ x (1 + 2)
        (iterCov (I := I) g₀ 1
          (metricTraceFirstTwoField (I := I) (M := M) g₀
            (ccUnitField (I := I) g₀ 3
              (-metricLoweredConnectionDifferenceCoefficient (I := I) g₀ gBase))) 2 x)
        ≤ d ^ 5 *
          normSq0S (I := I) g₀ x (3 + 2)
            (iterCov (I := I) g₀ 3
              (ccUnitField (I := I) g₀ 3
                (-metricLoweredConnectionDifferenceCoefficient (I := I) g₀ gBase)) 2 x) := by
          simpa [d] using trace31_norm_le (I := I) g₀
            (ccUnitField (I := I) g₀ 3
              (-metricLoweredConnectionDifferenceCoefficient (I := I) g₀ gBase)) 2 x
    _ = d ^ 5 *
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + 2) x
          ((iteratedCovGrad (I := I) g₀ 0 3 2
            (-metricLoweredConnectionDifferenceCoefficient (I := I) g₀ gBase)).toSection x) := by
          rw [riemannianFiberNormSq_iterCovGrad_eq (I := I) g₀ 3 2
            (-metricLoweredConnectionDifferenceCoefficient (I := I) g₀ gBase) x]
    _ = d ^ 5 *
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + 2) x
          ((iteratedCovGrad (I := I) g₀ 0 3 2
            (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ gBase)).toSection x) := by
          exact congrArg (fun z : ℝ => d ^ 5 * z)
            (riemannianFiberNormSq_iter_neg (I := I) g₀ 0 3 2
              (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ gBase) x)
    _ = d ^ 5 *
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + 2) x
          ((iteratedCovGrad (I := I) g₀ 1 2 2
            (connectionDifferenceSection (I := I) gBase g₀)).toSection x) := by
          exact congrArg (fun z : ℝ => d ^ 5 * z)
            (metricLoweredConnectionDifferenceCoefficient_fiber_norm_sq_eq (I := I) (M := M) g₀ gBase 2 x)
    _ ≤ d ^ 5 * KC :=
      mul_le_mul_of_nonneg_left (hC x) (pow_nonneg hd0 5)
    _ = alphaOneC (E := E) Λ ^ 2 := by
      change d ^ 5 * KC = (Real.sqrt (d ^ 5 * KC)) ^ 2
      rw [Real.sq_sqrt (mul_nonneg (pow_nonneg hd0 5) hKC0)]

private theorem uniformOmegaTwo
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ}
    (hΛ : 1 ≤ Λ)
    (hcomp : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ Λ * gBase.inner x v v)
    (hjet1 : MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g₀ gBase Λ)
    (hjet2 : MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g₀ gBase Λ)
    (hjet3 : MetricCovDerivOrderBoundOn (I := I) Set.univ 3 g₀ gBase Λ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (1 + 2) x
        ((iteratedCovGrad (I := I) g₀ 0 1 2
          (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₀ gBase)).toSection x) ≤ K ^ 2 := by
  exact ⟨alphaOneC (E := E) Λ, Real.sqrt_nonneg _,
    uniformOmegaTwo_of (I := I) gBase g₀ hΛ hcomp hjet1 hjet2 hjet3⟩

private theorem uniformAlphaOne_of
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ}
    (hΛ : 1 ≤ Λ)
    (hcomp : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ Λ * gBase.inner x v v)
    (hjet1 : MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g₀ gBase Λ)
    (hjet2 : MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g₀ gBase Λ)
    (hjet3 : MetricCovDerivOrderBoundOn (I := I) Set.univ 3 g₀ gBase Λ) :
    ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 1) x
        ((iteratedCovGrad (I := I) g₀ 0 2 1
          (deTurckVectorFieldCovariantDerivativeLoweredBase (I := I) (M := M) g₀ g₀ gBase)).toSection x) ≤
        alphaOneC (E := E) Λ ^ 2 := by
  have hK := uniformOmegaTwo_of (I := I) gBase g₀
    hΛ hcomp hjet1 hjet2 hjet3
  intro x
  rw [wAlphaA_shift (I := I) g₀ g₀ gBase 1 x]
  simpa using hK x

private theorem uniformAlphaOne
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ}
    (hΛ : 1 ≤ Λ)
    (hcomp : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ Λ * gBase.inner x v v)
    (hjet1 : MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g₀ gBase Λ)
    (hjet2 : MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g₀ gBase Λ)
    (hjet3 : MetricCovDerivOrderBoundOn (I := I) Set.univ 3 g₀ gBase Λ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 1) x
        ((iteratedCovGrad (I := I) g₀ 0 2 1
          (deTurckVectorFieldCovariantDerivativeLoweredBase (I := I) (M := M) g₀ g₀ gBase)).toSection x) ≤ K ^ 2 := by
  exact ⟨alphaOneC (E := E) Λ, Real.sqrt_nonneg _,
    uniformAlphaOne_of (I := I) gBase g₀ hΛ hcomp hjet1 hjet2 hjet3⟩


noncomputable def ricciOneC (Λ Kb₀ Kb₁ : ℝ) : ℝ :=
  Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 5 *
    rmOneC (E := E) Λ Kb₀ Kb₁ ^ 2)

omit [NeZero (Module.finrank ℝ E)] in
private theorem uniformRicOne_of
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ}
    (hΛ : 1 ≤ Λ)
    {Kb₀ Kb₁ : ℝ} (hKb₀0 : 0 ≤ Kb₀)
    (hKb₀ : ∀ (x : M) (v w u : TangentSpace I x),
      gBase.inner x (riemannOp (cov := LeviCivita (I := I) gBase) x v w u)
          (riemannOp (cov := LeviCivita (I := I) gBase) x v w u) ≤
        Kb₀ * gBase.inner x v v * gBase.inner x w w * gBase.inner x u u)
    (hKb₁0 : 0 ≤ Kb₁)
    (hKb₁ : ∀ x : M,
      Real.sqrt (normSq0S (I := I) gBase x 5
        (iterCov (I := I) gBase 4
          (metricRm04 (I := I) (M := M) gBase) 1 x)) ≤ Kb₁)
    (hcomp : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ Λ * gBase.inner x v v)
    (hjet1 : MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g₀ gBase Λ)
    (hjet2 : MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g₀ gBase Λ)
    (hjet3 : MetricCovDerivOrderBoundOn (I := I) Set.univ 3 g₀ gBase Λ) :
    ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 1) x
        ((iteratedCovGrad (I := I) g₀ 0 2 1
          (ccOfField (I := I) g₀ 2
            (metricRicci (I := I) (M := M) g₀))).toSection x) ≤
        ricciOneC (E := E) Λ Kb₀ Kb₁ ^ 2 := by
  let KR : ℝ := rmOneC (E := E) Λ Kb₀ Kb₁
  have hRm := uniformRmSecOne_of (I := I) (M := M) gBase g₀ hΛ
    hKb₀0 hKb₀ hKb₁0 hKb₁ hcomp hjet1 hjet2 hjet3
  let d : ℝ := Module.finrank ℝ E
  let K : ℝ := ricciOneC (E := E) Λ Kb₀ Kb₁
  have hd0 : 0 ≤ d := by
    dsimp [d]
    positivity
  intro x
  have hcan :
      metricRicci (I := I) (M := M) g₀ =
        trace04Field (I := I) (M := M) g₀
          (metricRm04 (I := I) (M := M) g₀) := by
    simpa [metricRicci, metricRm04, metricCov] using
      (canRicField (I := I) (M := M) g₀)
  rw [riemannianFiberNormSq_iterCovGrad_eq (I := I) g₀ 2 1
      (ccOfField (I := I) g₀ 2
        (metricRicci (I := I) (M := M) g₀)) x,
    ccOfField_unit, hcan]
  calc
    normSq0S (I := I) g₀ x (2 + 1)
        (iterCov (I := I) g₀ 2
          (trace04Field (I := I) (M := M) g₀
            (metricRm04 (I := I) (M := M) g₀)) 1 x)
        ≤ d ^ 5 *
          normSq0S (I := I) g₀ x (4 + 1)
            (iterCov (I := I) g₀ 4
              (metricRm04 (I := I) (M := M) g₀) 1 x) := by
          simpa [d] using
            (iterRic_normSq_le (I := I) g₀
              (metricRm04 (I := I) (M := M) g₀) 1 x)
    _ = d ^ 5 *
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + 1) x
          ((iteratedCovGrad (I := I) g₀ 0 4 1
            (rmSection (I := I) (M := M) g₀)).toSection x) := by
          rw [riemannianFiberNormSq_rmSection_eq (I := I) g₀ 1 x]
    _ ≤ d ^ 5 * KR ^ 2 :=
      mul_le_mul_of_nonneg_left (hRm x) (pow_nonneg hd0 5)
    _ = K ^ 2 := by
      dsimp [K, ricciOneC, KR, d]
      rw [Real.sq_sqrt (mul_nonneg (pow_nonneg hd0 5) (sq_nonneg KR))]

private theorem uniformRicOne
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ}
    (hΛ : 1 ≤ Λ)
    (hcomp : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ Λ * gBase.inner x v v)
    (hjet1 : MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g₀ gBase Λ)
    (hjet2 : MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g₀ gBase Λ)
    (hjet3 : MetricCovDerivOrderBoundOn (I := I) Set.univ 3 g₀ gBase Λ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 1) x
        ((iteratedCovGrad (I := I) g₀ 0 2 1
          (ccOfField (I := I) g₀ 2
            (metricRicci (I := I) (M := M) g₀))).toSection x) ≤ K ^ 2 := by
  obtain ⟨Kb₀, hKb₀0, hKb₀⟩ :=
    exists_uniform_riemannOp_LeviCivita_gNorm_bound (I := I) (M := M) gBase
  obtain ⟨Kb₁, hKb₁0, hKb₁⟩ :=
    exists_curvJet_sup (I := I) (M := M) gBase 1
  refine ⟨ricciOneC (E := E) Λ Kb₀ Kb₁, Real.sqrt_nonneg _, ?_⟩
  exact uniformRicOne_of (I := I) gBase g₀ hΛ
    hKb₀0 hKb₀ hKb₁0 hKb₁ hcomp hjet1 hjet2 hjet3

private def ricciCc
    (g : SmoothRiemannianMetric I M) : SmoothCcTensor g 0 2 :=
  ccOfField (I := I) g 2 (metricRicci (I := I) (M := M) g)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma unit_add2
    (g : SmoothRiemannianMetric I M)
    (S T : SmoothCcTensor g 0 2) (x : M) :
    unitModel (I := I) (M := M) g 2 (S + T) x =
      unitModel (I := I) (M := M) g 2 S x +
        unitModel (I := I) (M := M) g 2 T x := by
  rw [unitModel, unitModel, unitModel]
  have hsec : (S + T).toSection x = S.toSection x + T.toSection x := by
    rw [SmoothCcTensor.toSection_add]
    rfl
  rw [show
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
      (S + T).toSection x) (unitTensor (I := I) (M := M) x)) =
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          S.toSection x) (unitTensor (I := I) (M := M) x) +
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          T.toSection x) (unitTensor (I := I) (M := M) x) from by
      rw [hsec]
      rfl]
  rw [Tensor0SSpace.toModel_add]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma unit_add2_apply
    (g : SmoothRiemannianMetric I M)
    (S T : SmoothCcTensor g 0 2) (x : M)
    (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g 2 (S + T) x v =
      unitModel (I := I) (M := M) g 2 S x v +
        unitModel (I := I) (M := M) g 2 T x v := by
  rw [unit_add2, ContinuousMultilinearMap.add_apply]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma unit_smul2
    (g : SmoothRiemannianMetric I M)
    (c : ℝ) (T : SmoothCcTensor g 0 2) (x : M) :
    unitModel (I := I) (M := M) g 2 (c • T) x =
      c • unitModel (I := I) (M := M) g 2 T x := by
  rw [unitModel, unitModel]
  have hsec : (c • T).toSection x = c • T.toSection x := by
    rw [SmoothCcTensor.toSection_smul]
    rfl
  rw [show
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
      (c • T).toSection x) (unitTensor (I := I) (M := M) x)) =
        c • (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          T.toSection x) (unitTensor (I := I) (M := M) x) from by
      rw [hsec]
      rfl]
  rw [Tensor0SSpace.toModel_smul]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma unit_smul2_apply
    (g : SmoothRiemannianMetric I M)
    (c : ℝ) (T : SmoothCcTensor g 0 2) (x : M)
    (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g 2 (c • T) x v =
      c * unitModel (I := I) (M := M) g 2 T x v := by
  rw [unit_smul2, ContinuousMultilinearMap.smul_apply, smul_eq_mul]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
private theorem rhs_unit
    (gBase g : SmoothRiemannianMetric I M) (x : M)
    (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g 2
        (deTurckRHSSection (I := I) gBase g) x v =
      deTurckRicciRHS (I := I) gBase g x (v 0) (v 1) := by
  rw [unitModel]
  exact deTurckRHSSection_toModel_apply (I := I) gBase g x v

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
private theorem ricci_unit
    (g : SmoothRiemannianMetric I M) (x : M)
    (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g 2
        (ricciCc (I := I) (M := M) g) x v =
      ricciTensor (I := I) g x (v 0) (v 1) := by
  rw [unitModel]
  change Tensor0SSpace.toModel
    (ccUnitField (I := I) g 2 (ricciCc (I := I) (M := M) g) x) v = _
  rw [ricciCc, ccOfField_unit]
  change metricRicci (I := I) (M := M) g x v = _
  have hcmm : metricRicciAt (I := I) (M := M) g x v =
      metricRicciAt (I := I) (M := M) g x (vec2 (v 0) (v 1)) :=
    congrArg _ (by
      funext i
      fin_cases i <;> rfl)
  rw [metricRicci_apply, hcmm]
  exact metricRicciAt_apply_eq_ricciTensor (I := I) g x (v 0) (v 1)

private theorem rhs_split
    (gBase g : SmoothRiemannianMetric I M) :
    deTurckRHSSection (I := I) gBase g =
      ((-2 : ℝ) • ricciCc (I := I) (M := M) g +
        deTurckVectorFieldCovariantDerivativeLoweredBase (I := I) (M := M) g g gBase) +
      domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1)
        (deTurckVectorFieldCovariantDerivativeLoweredBase (I := I) (M := M) g g gBase) := by
  classical
  refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g (fun x => ?_)
  refine ContinuousMultilinearMap.ext (fun v => ?_)
  have hv : v = ![v 0, v 1] := by
    funext i
    fin_cases i <;> rfl
  have hswap :
      (fun i => v ((Equiv.swap (0 : Fin 2) 1) i)) = ![v 1, v 0] := by
    funext i
    fin_cases i <;> rfl
  rw [rhs_unit, unit_add2_apply, unit_add2_apply,
    unit_smul2_apply, ricci_unit]
  rw [domDomCongrSection_unitModel, ContinuousMultilinearMap.domDomCongr_apply]
  rw [hswap, hv]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [deTurckVectorFieldCovariantDerivativeLoweredBase_unitModel_apply, deTurckVectorFieldCovariantDerivativeLoweredBase_unitModel_apply,
    deTurckRicciRHS_apply,
    DifferentialGeometry.PDE.RicciFlow.Pullback.cartan_formula_for_lie_deriv_metric]
  rw [g.symm x (v 0)]
  unfold deTurckVectorFieldSection
  ring

private theorem rhs_one_split
    (gBase g : SmoothRiemannianMetric I M) :
    iteratedCovGrad (I := I) g 0 2 1
        (deTurckRHSSection (I := I) gBase g) =
      ((-2 : ℝ) • iteratedCovGrad (I := I) g 0 2 1
          (ricciCc (I := I) (M := M) g) +
        iteratedCovGrad (I := I) g 0 2 1
          (deTurckVectorFieldCovariantDerivativeLoweredBase (I := I) (M := M) g g gBase)) +
      iteratedCovGrad (I := I) g 0 2 1
        (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1)
          (deTurckVectorFieldCovariantDerivativeLoweredBase (I := I) (M := M) g g gBase)) := by
  rw [rhs_split, iteratedCovGrad_add, iteratedCovGrad_add,
    iteratedCovGrad_smul]


noncomputable def ksupOneC (Λ Kb₀ Kb₁ : ℝ) : ℝ :=
  4 * (ricciOneC (E := E) Λ Kb₀ Kb₁ + alphaOneC (E := E) Λ)


theorem uniformKsupOne_of
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ}
    (hΛ : 1 ≤ Λ)
    {Kb₀ Kb₁ : ℝ} (hKb₀0 : 0 ≤ Kb₀)
    (hKb₀ : ∀ (x : M) (v w u : TangentSpace I x),
      gBase.inner x (riemannOp (cov := LeviCivita (I := I) gBase) x v w u)
          (riemannOp (cov := LeviCivita (I := I) gBase) x v w u) ≤
        Kb₀ * gBase.inner x v v * gBase.inner x w w * gBase.inner x u u)
    (hKb₁0 : 0 ≤ Kb₁)
    (hKb₁ : ∀ x : M,
      Real.sqrt (normSq0S (I := I) gBase x 5
        (iterCov (I := I) gBase 4
          (metricRm04 (I := I) (M := M) gBase) 1 x)) ≤ Kb₁)
    (hcomp : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ Λ * gBase.inner x v v)
    (hjet1 : MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g₀ gBase Λ)
    (hjet2 : MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g₀ gBase Λ)
    (hjet3 : MetricCovDerivOrderBoundOn (I := I) Set.univ 3 g₀ gBase Λ) :
    ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 1) x
        ((iteratedCovGrad (I := I) g₀ 0 2 1
          (deTurckRHSSection (I := I) gBase g₀)).toSection x) ≤
        ksupOneC (E := E) Λ Kb₀ Kb₁ ^ 2 := by
  let KR : ℝ := ricciOneC (E := E) Λ Kb₀ Kb₁
  let KA : ℝ := alphaOneC (E := E) Λ
  have hKR0 : 0 ≤ KR := by
    dsimp [KR, ricciOneC]
    positivity
  have hKA0 : 0 ≤ KA := by
    dsimp [KA, alphaOneC]
    positivity
  have hRic := uniformRicOne_of (I := I) gBase g₀ hΛ
    hKb₀0 hKb₀ hKb₁0 hKb₁ hcomp hjet1 hjet2 hjet3
  have hAlpha := uniformAlphaOne_of (I := I) gBase g₀
    hΛ hcomp hjet1 hjet2 hjet3
  intro x
  let R1 := (iteratedCovGrad (I := I) g₀ 0 2 1
    (ricciCc (I := I) (M := M) g₀)).toSection x
  let A1 := (iteratedCovGrad (I := I) g₀ 0 2 1
    (deTurckVectorFieldCovariantDerivativeLoweredBase (I := I) (M := M) g₀ g₀ gBase)).toSection x
  let P1 := (iteratedCovGrad (I := I) g₀ 0 2 1
    (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1)
      (deTurckVectorFieldCovariantDerivativeLoweredBase (I := I) (M := M) g₀ g₀ gBase))).toSection x
  have hR :
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 1) x R1 ≤
        KR ^ 2 := by
    simpa [R1, ricciCc] using hRic x
  have hA :
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 1) x A1 ≤
        KA ^ 2 := by
    simpa [A1] using hAlpha x
  have hP :
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 1) x P1 =
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 1) x A1 := by
    simpa [P1, A1] using
      (riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection
        (I := I) (M := M) g₀ (Equiv.swap (0 : Fin 2) 1)
        (deTurckVectorFieldCovariantDerivativeLoweredBase (I := I) (M := M) g₀ g₀ gBase) 1 x)
  have hS :
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 1) x
          ((-2 : ℝ) • R1) =
        4 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 1) x R1 := by
    rw [DifferentialGeometry.Analysis.Elliptic.riemannianFiberNormSq_smul]
    norm_num
  have hRA :=
    riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (2 + 1) x
      ((-2 : ℝ) • R1) A1
  have hRAP :=
    riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (2 + 1) x
      (((-2 : ℝ) • R1) + A1) P1
  have hsum :
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 1) x
          (((-2 : ℝ) • R1) + A1 + P1) ≤
        16 * KR ^ 2 + 6 * KA ^ 2 := by
    nlinarith [hRA, hRAP, hR, hA, hS, hP]
  rw [rhs_one_split (I := I) gBase g₀]
  have hout :
      (((-2 : ℝ) • iteratedCovGrad (I := I) g₀ 0 2 1
          (ricciCc (I := I) (M := M) g₀) +
        iteratedCovGrad (I := I) g₀ 0 2 1
          (deTurckVectorFieldCovariantDerivativeLoweredBase (I := I) (M := M) g₀ g₀ gBase)) +
        iteratedCovGrad (I := I) g₀ 0 2 1
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1)
            (deTurckVectorFieldCovariantDerivativeLoweredBase (I := I) (M := M) g₀ g₀ gBase))).toSection x =
        ((-2 : ℝ) • R1) + A1 + P1 := by
    rw [SmoothCcTensor.toSection_add, SmoothCcTensor.toSection_add,
      SmoothCcTensor.toSection_smul]
    rfl
  rw [hout]
  exact hsum.trans (by
    dsimp [ksupOneC, KR, KA]
    nlinarith [mul_nonneg hKR0 hKA0, sq_nonneg KA])


theorem uniformKsupOne
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ}
    (hΛ : 1 ≤ Λ)
    (hcomp : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ Λ * gBase.inner x v v)
    (hjet1 : MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g₀ gBase Λ)
    (hjet2 : MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g₀ gBase Λ)
    (hjet3 : MetricCovDerivOrderBoundOn (I := I) Set.univ 3 g₀ gBase Λ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 1) x
        ((iteratedCovGrad (I := I) g₀ 0 2 1
          (deTurckRHSSection (I := I) gBase g₀)).toSection x) ≤ K ^ 2 := by
  obtain ⟨Kb₀, hKb₀0, hKb₀⟩ :=
    exists_uniform_riemannOp_LeviCivita_gNorm_bound (I := I) (M := M) gBase
  obtain ⟨Kb₁, hKb₁0, hKb₁⟩ :=
    exists_curvJet_sup (I := I) (M := M) gBase 1
  refine ⟨ksupOneC (E := E) Λ Kb₀ Kb₁, ?_, ?_⟩
  · dsimp [ksupOneC]
    exact mul_nonneg (by norm_num) <|
      add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  · exact uniformKsupOne_of (I := I) gBase g₀ hΛ
      hKb₀0 hKb₀ hKb₁0 hKb₁ hcomp hjet1 hjet2 hjet3


theorem uniformKsupLeOne
    (gBase : SmoothRiemannianMetric I M) {Λ : ℝ}
    (hΛ : 1 ≤ Λ) :
    ∃ Kstar : ℝ, 0 ≤ Kstar ∧
      ∀ g₀ : SmoothRiemannianMetric I M,
        (∀ (x : M) (v : TangentSpace I x),
          Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
            g₀.inner x v v ≤ Λ * gBase.inner x v v) →
        MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g₀ gBase Λ →
        MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g₀ gBase Λ →
        MetricCovDerivOrderBoundOn (I := I) Set.univ 3 g₀ gBase Λ →
        ∀ j : ℕ, j ≤ 1 → ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
            ((iteratedCovGrad (I := I) g₀ 0 2 j
              (deTurckRHSSection (I := I) gBase g₀)).toSection x) ≤ Kstar ^ 2 := by
  obtain ⟨Kb₀, hKb₀0, hKb₀⟩ :=
    exists_uniform_riemannOp_LeviCivita_gNorm_bound (I := I) (M := M) gBase
  obtain ⟨Kb₁, hKb₁0, hKb₁⟩ :=
    exists_curvJet_sup (I := I) (M := M) gBase 1
  let K₀ : ℝ := ksupZeroC (E := E) Λ Kb₀
  let K₁ : ℝ := ksupOneC (E := E) Λ Kb₀ Kb₁
  have hK₀0 : 0 ≤ K₀ := by
    dsimp [K₀]
    exact ksupZeroC_nonneg (E := E) hΛ
  have hK₁0 : 0 ≤ K₁ := by
    dsimp [K₁, ksupOneC]
    exact mul_nonneg (by norm_num) <|
      add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  refine ⟨K₀ + K₁, add_nonneg hK₀0 hK₁0, ?_⟩
  intro g₀ hcomp hjet1 hjet2 hjet3 j hj x
  have h0 := uniformKsupZero_of (I := I) (M := M) gBase g₀ hΛ
    hKb₀0 hKb₀ hcomp hjet1 hjet2
  have h1 := uniformKsupOne_of (I := I) gBase g₀ hΛ
    hKb₀0 hKb₀ hKb₁0 hKb₁ hcomp hjet1 hjet2 hjet3
  interval_cases j
  · exact (h0 x).trans (by
      nlinarith [mul_nonneg hK₀0 hK₁0, sq_nonneg K₁])
  · exact (h1 x).trans (by
      nlinarith [mul_nonneg hK₀0 hK₁0, sq_nonneg K₀])


theorem uniformKsupLow
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ}
    (hΛ : 1 ≤ Λ)
    (hcomp : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ Λ * gBase.inner x v v)
    (hjet1 : MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g₀ gBase Λ)
    (hjet2 : MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g₀ gBase Λ)
    (hjet3 : MetricCovDerivOrderBoundOn (I := I) Set.univ 3 g₀ gBase Λ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ j : ℕ, j ≤ 1 → ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 0 2 j
            (deTurckRHSSection (I := I) gBase g₀)).toSection x) ≤ K ^ 2 := by
  obtain ⟨K₀, hK₀, h0⟩ :=
    uniformKsupZero (I := I) (M := M) gBase g₀
      hΛ hcomp hjet1 hjet2
  obtain ⟨K₁, hK₁, h1⟩ :=
    uniformKsupOne (I := I) gBase g₀
      hΛ hcomp hjet1 hjet2 hjet3
  refine ⟨K₀ + K₁, add_nonneg hK₀ hK₁, ?_⟩
  intro j hj x
  interval_cases j
  · exact (h0 x).trans (by
      nlinarith [mul_nonneg hK₀ hK₁, sq_nonneg K₁])
  · exact (h1 x).trans (by
      nlinarith [mul_nonneg hK₀ hK₁, sq_nonneg K₀])

end RicciFlow
end PDE
end DifferentialGeometry

end
