import DifferentialGeometry.Geometry.Metric.Convergence.IntrinsicCovariantDerivativeNormComparison
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivativeRecurrenceNorm
import DifferentialGeometry.Geometry.Metric.Convergence.GoodFrame
import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNormArity
import DifferentialGeometry.Geometry.Metric.Convergence.UniformEquivalence
import DifferentialGeometry.Geometry.Curvature.Components.RicciTrace
import DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetricIneq
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

set_option autoImplicit false

universe u

noncomputable section

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff Topology BigOperators
open Bundle DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Tensor.Coordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]
variable [IsManifold I 1 M] [IsManifold I 2 M]

noncomputable def metricCovariantDerivativeComparisonConstant (q₂ p : ℕ) : Real :=
  iteratedRecurrenceConstant
    (fun c => inverseContractionRecurrenceConstant
      (Real.sqrt (Module.finrank Real E) * 2)
      (|(1 / 2 : Real)| + |(1 / 2 : Real)| + |-(1 / 2 : Real)|)
      (4 ^ (2 + p)) c)
    p q₂

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem metric_covariant_derivative_comparison_constant_nonneg (q₂ p : ℕ) : 0 ≤ metricCovariantDerivativeComparisonConstant (E := E) q₂ p := by
  apply iterated_recurrence_constant_nonneg
  intro c
  exact inverse_contraction_recurrence_constant_nonneg (by positivity : (0 : Real) ≤ 4 ^ (2 + p)) c

omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem iterated_covariant_derivative_norm_comparison_bound
    {q₂ : ℕ} {u : Set M} (hu : IsOpen u)
    (g gRef : SmoothRiemannianMetric I M)
    (T : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) q₂)
    (p : ℕ) (eps : Real) (heps0 : 0 ≤ eps) (heps1 : eps ≤ 1)
    (hequiv : ∀ x ∈ u, ∀ v : TangentSpace I x,
      (1 + eps)⁻¹ * gRef.inner x v v ≤ g.inner x v v ∧
        g.inner x v v ≤ (1 + eps) * gRef.inner x v v)
    (hgK : ∀ x ∈ u, ∀ j, 1 ≤ j → j ≤ p →
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef x (2 + j)
        (iterCov (I := I) gRef 2 (Tensor0SBundle.metricTensorField (I := I) g) j x)) ≤ eps) :
    ∀ x ∈ u, ∀ r : ℕ, 0 < r → r ≤ p →
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x (q₂ + r)
          (iterCov (I := I) g q₂ T r x)) ≤
        Real.sqrt ((1 + eps) ^ (q₂ + r)) *
          (Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef x (q₂ + r)
              (iterCov (I := I) gRef q₂ T r x)) +
            eps * metricCovariantDerivativeComparisonConstant (E := E) q₂ p * ∑ k ∈ Finset.range r,
              Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef x (q₂ + k)
                (iterCov (I := I) gRef q₂ T k x))) := by
  classical
  intro x hx r hr0 hrp
  let e₀ := trivializationAt E (TangentSpace I : M → Type _) x
  obtain ⟨basisE, u', η, hu', hxu', hsub, hη0, hsmall, hnear, hON, hcomp, _⟩ :=
    exists_goodFrame_compBound (I := I) g x
  let frame : Fin (Module.finrank Real E) → (y : M) → TangentSpace I y :=
    fun a y => e₀.localFrame basisE a y
  let w : Set M := u' ∩ u
  have hwopen : IsOpen w := hu'.inter hu
  have hxw : x ∈ w := ⟨hxu', hx⟩
  have hwsub : w ⊆ e₀.baseSet := fun _ hz => hsub hz.1
  let hframe : IsLocalFrameOn I E (1 : WithTop ℕ∞) frame w :=
    (e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE).mono hwsub
  have hframeS : ∀ d : Fin (Module.finrank Real E),
      ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
        (fun y => TotalSpace.mk' E (E := TangentSpace I) y (frame d y)) w :=
    fun d => (frame_e_mdiffOn e₀ basisE d).mono hwsub
  have hchrG : ∀ d i j : Fin (Module.finrank Real E), ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun y => christoffelSymbolInFrame (leviCivitaConnectionOfMetric (I := I) g)
        frame hframe y d i j) w :=
    fun d i j => ((lcChrist_e_mdiffOn e₀ g basisE d i j).mono hwsub).congr
      (fun z hz => chrInFrame_mono (I := I) (leviCivitaConnectionOfMetric (I := I) g)
        frame (e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE) hwsub hz d i j)
  have hchrH : ∀ d i j : Fin (Module.finrank Real E), ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun y => christoffelSymbolInFrame (leviCivitaConnectionOfMetric (I := I) gRef)
        frame hframe y d i j) w :=
    fun d i j => ((lcChrist_e_mdiffOn e₀ gRef basisE d i j).mono hwsub).congr
      (fun z hz => chrInFrame_mono (I := I) (leviCivitaConnectionOfMetric (I := I) gRef)
        frame (e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE) hwsub hz d i j)
  have hgsm := fun k => (gCompField_mdiffOn e₀ g basisE k).mono hwsub
  have hTsm := fun k => (tensorComp_mdiffOn e₀ T basisE k).mono hwsub
  let C0 : Real := Real.sqrt (Module.finrank Real E) * 2
  have hGinv : ∀ z ∈ w, compL2 (ginvCompField (I := I) e₀ g basisE z) ≤ C0 := by
    intro z hz
    have h := movingGinv_le (I := I) e₀ g g basisE 1 zero_lt_one
      (fun v => by simp) η hη0 hsmall (fun i j => hnear z hz.1 i j)
    simpa only [C0, Fintype.card_fin, mul_one] using h
  have hinv : ∀ z ∈ w, ∀ c e : Fin (Module.finrank Real E),
      (∑ l, frameComp0S (I := I) (metricTensorField (I := I) g) frame z
          (Fin.snoc (fun _ : Fin 1 => l) c) *
        ginvCompField (I := I) e₀ g basisE z (Fin.snoc (fun _ : Fin 1 => e) l)) =
          if c = e then 1 else 0 :=
    fun z hz c e => ginv_hinv (I := I) e₀ g basisE (hwsub hz) c e
  let L : Real := 4 ^ (2 + p)
  have hL0 : 0 ≤ L := by positivity
  have hgKcomp : ∀ z ∈ w, ∀ j, 1 ≤ j → j ≤ p →
      compL2 (iterCovComp (I := I) frame
        (fun y => christoffelSymbolInFrame (leviCivitaConnectionOfMetric (I := I) gRef)
          frame hframe y)
        (frameComp0S (I := I) (metricTensorField (I := I) g) frame) j z) ≤ L * eps := by
    intro z hz j _ hjp
    exact metricComp_mul (I := I) g gRef frame hframe hwopen hz
      (fun s A => hcomp z (hwsub hz) hz.1 s A)
      (1 + eps) (by linarith) (by linarith)
      (hequiv z hz.2) p j hjp heps0 (hgK z hz.2 j (by omega) hjp)
  have hcompF3 := iterated_covariant_derivative_comparison_bound hwopen g gRef frame hframe hframeS hchrG hchrH
    hgsm (frameComp0S (I := I) T frame) hTsm
    (ginvCompField (I := I) e₀ g basisE) hinv C0 L eps hL0 heps0 heps1 hGinv p hgKcomp
  have hON' : ∀ i j : Fin (Module.finrank Real E),
      g.inner x (hframe.toBasisAt hxw i) (hframe.toBasisAt hxw j) =
        if i = j then 1 else 0 := by
    intro i j
    simpa only [IsLocalFrameOn.toBasisAt_coe] using hON i j
  have hinvON := DifferentialGeometry.Tensor0SBundle.metricInverseInBasis_of_orthonormal (I := I) g
    (hframe.toBasisAt hxw) hON'
  have hF3 : ∀ s : ℕ, 0 < s → s ≤ p →
      Real.sqrt (normSq0S (I := I) g x (q₂ + s) (iterCov (I := I) g q₂ T s x)) ≤
        Real.sqrt (normSq0S (I := I) g x (q₂ + s) (iterCov (I := I) gRef q₂ T s x)) +
        eps * metricCovariantDerivativeComparisonConstant (E := E) q₂ p * ∑ k ∈ Finset.range s,
          Real.sqrt (normSq0S (I := I) g x (q₂ + k) (iterCov (I := I) gRef q₂ T k x)) := by
    intro s hs0 hsp
    apply sqrt_norm_sq_iter_cov_le_of_component_bound
      hwopen g gRef T frame hframe hxw hinvON eps
      (metricCovariantDerivativeComparisonConstant (E := E) q₂ p) s
    simpa only [metricCovariantDerivativeComparisonConstant, C0, L] using hcompF3 x hxw s hs0 hsp
  exact covariant_derivative_norm_comparison_of_intrinsic_metric_equivalence g gRef T p (x := x) (C := 1 + eps)
    (by linarith) (hequiv x hx) eps (metricCovariantDerivativeComparisonConstant (E := E) q₂ p) heps0
    (metric_covariant_derivative_comparison_constant_nonneg (E := E) q₂ p) hF3 r hr0 hrp

omit [I.Boundaryless] in
theorem metric_deriv_norm_change_le
    {N : Type u} [TopologicalSpace N] [ChartedSpace H N]
    [T2Space N] [IsManifold I ∞ N]
    [IsManifold I 1 N] [IsManifold I 2 N]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) N]
    {u : Set N} (hu : IsOpen u)
    (A B gInf gBase : SmoothRiemannianMetric I N)
    (p r : ℕ) (eps : ℝ) (heps0 : 0 ≤ eps) (heps1 : eps ≤ 1)
    (hequiv : ∀ x ∈ u, ∀ v : TangentSpace I x,
      (1 + eps)⁻¹ * gBase.inner x v v ≤ gInf.inner x v v ∧
        gInf.inner x v v ≤ (1 + eps) * gBase.inner x v v)
    (hInf : ∀ x ∈ u, ∀ j, 1 ≤ j → j ≤ p →
      metricDerivNorm (I := I) j gInf gBase gBase x ≤ eps)
    (x : N) (hx : x ∈ u) (hr0 : 0 < r) (hrp : r ≤ p) :
    metricDerivNorm (I := I) r A B gInf x ≤
      Real.sqrt ((1 + eps) ^ (2 + r)) *
        (metricDerivNorm (I := I) r A B gBase x +
          eps * metricCovariantDerivativeComparisonConstant (E := E) 2 p * ∑ k ∈ Finset.range r,
            metricDerivNorm (I := I) k A B gBase x) := by
  classical
  obtain ⟨bBase, hBaseON⟩ :=
    DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis (I := I) gBase x
  have hBaseInv : Tensor0SBundle.MetricInverseInBasisGen (I := I) gBase x bBase
      (Tensor0SBundle.identityInvMetric
        (Idx := Fin (Module.finrank Real (TangentSpace I x)))) := by
    have h := DifferentialGeometry.Tensor0SBundle.metricInverseInBasis_of_orthonormal
      (I := I) gBase bBase hBaseON
    intro i j
    simpa [Tensor0SBundle.identityInvMetric, Tensor0SBundle.diagonalInvMetric] using h i j
  obtain ⟨bInf, hInfON⟩ :=
    DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis (I := I) gInf x
  have hInfInv : Tensor0SBundle.MetricInverseInBasisGen (I := I) gInf x bInf
      (Tensor0SBundle.identityInvMetric
        (Idx := Fin (Module.finrank Real (TangentSpace I x)))) := by
    have h := DifferentialGeometry.Tensor0SBundle.metricInverseInBasis_of_orthonormal
      (I := I) gInf bInf hInfON
    intro i j
    simpa [Tensor0SBundle.identityInvMetric, Tensor0SBundle.diagonalInvMetric] using h i j
  have hInfIter : ∀ y ∈ u, ∀ j, 1 ≤ j → j ≤ p →
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) gBase y (2 + j)
        (iterCov (I := I) gBase 2
          (Tensor0SBundle.metricTensorField (I := I) gInf) j y)) ≤ eps := by
    intro y hy j hj1 hjp
    obtain ⟨b, hON⟩ :=
      DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis (I := I) gBase y
    have hinv : Tensor0SBundle.MetricInverseInBasisGen (I := I) gBase y b
        (Tensor0SBundle.identityInvMetric
          (Idx := Fin (Module.finrank Real (TangentSpace I y)))) := by
      have h := DifferentialGeometry.Tensor0SBundle.metricInverseInBasis_of_orthonormal
        (I := I) gBase b hON
      intro i k
      simpa [Tensor0SBundle.identityInvMetric, Tensor0SBundle.diagonalInvMetric] using h i k
    have heq := metricDerivNorm_eq_iterCov (I := I) gInf gBase gBase j b hinv
    have hiter : iterCov (I := I) gBase 2
        (Tensor0SBundle.metricTensorField (I := I) gInf -
          Tensor0SBundle.metricTensorField (I := I) gBase) j y =
        iterCov (I := I) gBase 2
          (Tensor0SBundle.metricTensorField (I := I) gInf) j y := by
      obtain ⟨j', rfl⟩ := Nat.exists_eq_add_of_le hj1
      rw [show 1 + j' = j' + 1 by omega, iterCov_sub, iterCov_metric_zero, sub_zero]
    rw [hiter] at heq
    rw [← heq]
    exact hInf y hy j hj1 hjp
  let T : Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H)
      (I := I) (M := N) (n := (∞ : WithTop ℕ∞)) 2 :=
    Tensor0SBundle.metricTensorField (I := I) A -
      Tensor0SBundle.metricTensorField (I := I) B
  have hcor := iterated_covariant_derivative_norm_comparison_bound (I := I) hu gInf gBase T
    p eps heps0 heps1 hequiv hInfIter x hx r hr0 hrp
  dsimp only [T] at hcor
  have hleft := metricDerivNorm_eq_iterCov (I := I) A B gInf r bInf hInfInv
  have hright : ∀ k, Real.sqrt (Tensor0SBundle.normSq0S (I := I) gBase x (2 + k)
      (iterCov (I := I) gBase 2
        (Tensor0SBundle.metricTensorField (I := I) A -
          Tensor0SBundle.metricTensorField (I := I) B) k x)) =
      metricDerivNorm (I := I) k A B gBase x :=
    fun k => (metricDerivNorm_eq_iterCov (I := I) A B gBase k bBase hBaseInv).symm
  rw [← hleft] at hcor
  simp_rw [hright] at hcor
  exact hcor

noncomputable def metricReferenceChangeFactor (p : ℕ) : ℝ :=
  4 + ∑ r ∈ Finset.range (p + 1),
    Real.sqrt ((2 : ℝ) ^ (2 + r)) *
      (2 + 2 * metricCovariantDerivativeComparisonConstant (E := E) 2 p * (r : ℝ))

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem metric_reference_change_factor_pos (p : ℕ) :
    0 < metricReferenceChangeFactor (E := E) p := by
  have hterm : ∀ r : ℕ, 0 ≤ Real.sqrt ((2 : ℝ) ^ (2 + r)) *
      (2 + 2 * metricCovariantDerivativeComparisonConstant (E := E) 2 p * (r : ℝ)) := by
    intro r
    apply mul_nonneg (Real.sqrt_nonneg _)
    have hC := metric_covariant_derivative_comparison_constant_nonneg (E := E) 2 p
    positivity
  have hsum : 0 ≤ ∑ r ∈ Finset.range (p + 1),
      Real.sqrt ((2 : ℝ) ^ (2 + r)) *
        (2 + 2 * metricCovariantDerivativeComparisonConstant (E := E) 2 p * (r : ℝ)) := by
    exact Finset.sum_nonneg fun r _ => hterm r
  unfold metricReferenceChangeFactor
  linarith

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem four_le_metric_reference_change_factor (p : ℕ) :
    4 ≤ metricReferenceChangeFactor (E := E) p := by
  have hterm : ∀ r : ℕ, 0 ≤ Real.sqrt ((2 : ℝ) ^ (2 + r)) *
      (2 + 2 * metricCovariantDerivativeComparisonConstant (E := E) 2 p * (r : ℝ)) := by
    intro r
    apply mul_nonneg (Real.sqrt_nonneg _)
    have hC := metric_covariant_derivative_comparison_constant_nonneg (E := E) 2 p
    positivity
  have hsum : 0 ≤ ∑ r ∈ Finset.range (p + 1),
      Real.sqrt ((2 : ℝ) ^ (2 + r)) *
        (2 + 2 * metricCovariantDerivativeComparisonConstant (E := E) 2 p * (r : ℝ)) := by
    exact Finset.sum_nonneg fun r _ => hterm r
  unfold metricReferenceChangeFactor
  linarith

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem metric_reference_change_term_le_factor (p r : ℕ) (hrp : r ≤ p) :
    Real.sqrt ((2 : ℝ) ^ (2 + r)) *
        (2 + 2 * metricCovariantDerivativeComparisonConstant (E := E) 2 p * (r : ℝ)) ≤
      metricReferenceChangeFactor (E := E) p := by
  have hterm : ∀ q : ℕ, 0 ≤ Real.sqrt ((2 : ℝ) ^ (2 + q)) *
      (2 + 2 * metricCovariantDerivativeComparisonConstant (E := E) 2 p * (q : ℝ)) := by
    intro q
    apply mul_nonneg (Real.sqrt_nonneg _)
    have hC := metric_covariant_derivative_comparison_constant_nonneg (E := E) 2 p
    positivity
  have hmem : r ∈ Finset.range (p + 1) := by simp only [Finset.mem_range]; omega
  have hsum : Real.sqrt ((2 : ℝ) ^ (2 + r)) *
        (2 + 2 * metricCovariantDerivativeComparisonConstant (E := E) 2 p * (r : ℝ)) ≤
      ∑ q ∈ Finset.range (p + 1), Real.sqrt ((2 : ℝ) ^ (2 + q)) *
        (2 + 2 * metricCovariantDerivativeComparisonConstant (E := E) 2 p * (q : ℝ)) := by
    exact Finset.single_le_sum (fun q _ => hterm q) hmem
  unfold metricReferenceChangeFactor
  linarith

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem exists_metric_reference_change_delta (p : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      (Module.finrank ℝ E : ℝ) * δ ≤ 1 / 2 ∧
      metricReferenceChangeFactor (E := E) p * δ ≤ ε := by
  let n : ℝ := Module.finrank ℝ E
  let F : ℝ := metricReferenceChangeFactor (E := E) p
  have hn : 0 ≤ n := by dsimp only [n]; positivity
  have hn1 : 0 < n + 1 := by linarith
  have hF : 0 < F := by exact metric_reference_change_factor_pos (E := E) p
  let δ : ℝ := min (1 / (4 * (n + 1))) (ε / (2 * F))
  have hleft : 0 < 1 / (4 * (n + 1)) := by positivity
  have hright : 0 < ε / (2 * F) := by positivity
  have hδpos : 0 < δ := by simpa only [δ] using lt_min hleft hright
  have hδleft : δ ≤ 1 / (4 * (n + 1)) := min_le_left _ _
  have hδright : δ ≤ ε / (2 * F) := min_le_right _ _
  refine ⟨δ, hδpos, ?_, ?_, ?_⟩
  · have hden_ge : (4 : ℝ) ≤ 4 * (n + 1) := by nlinarith
    have hinv : 1 / (4 * (n + 1)) ≤ (1 : ℝ) / 4 :=
      one_div_le_one_div_of_le (by norm_num) hden_ge
    nlinarith
  · change n * δ ≤ 1 / 2
    have hmul := mul_le_mul_of_nonneg_left hδleft hn
    have hden : 0 < 4 * (n + 1) := by positivity
    have hfrac : n * (1 / (4 * (n + 1))) ≤ (1 : ℝ) / 4 := by
      calc
        n * (1 / (4 * (n + 1))) = n / (4 * (n + 1)) := by ring
        _ ≤ (1 : ℝ) / 4 := (div_le_iff₀ hden).2 (by nlinarith)
    linarith
  · change F * δ ≤ ε
    calc
      F * δ ≤ F * (ε / (2 * F)) := mul_le_mul_of_nonneg_left hδright hF.le
      _ = ε / 2 := by field_simp [ne_of_gt hF]
      _ ≤ ε := by linarith

omit [I.Boundaryless] in
theorem metric_deriv_norm_reference_change_le
    {N : Type u} [TopologicalSpace N] [ChartedSpace H N]
    [T2Space N] [IsManifold I ∞ N] [SigmaCompactSpace N]
    [IsManifold I 1 N] [IsManifold I 2 N]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) N]
    {u : Set N} (hu : IsOpen u)
    (A gInf gBase : SmoothRiemannianMetric I N)
    (p : ℕ) {δ ε : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hδdim : (Module.finrank ℝ E : ℝ) * δ ≤ 1 / 2)
    (hδbudget : metricReferenceChangeFactor (E := E) p * δ ≤ ε)
    (hA : ∀ x ∈ u, ∀ q, q ≤ p →
      metricDerivNorm (I := I) q A gBase gBase x ≤ δ)
    (hInf : ∀ x ∈ u, ∀ q, q ≤ p →
      metricDerivNorm (I := I) q gInf gBase gBase x ≤ δ)
    (x : N) (hx : x ∈ u) (q : ℕ) (hqp : q ≤ p) :
    metricDerivNorm (I := I) q A gInf gInf x ≤ ε := by
  let _ := (inferInstance : (SigmaCompactSpace N))
  classical
  have hBaseNN (y : N) (v : TangentSpace I y) : 0 ≤ gBase.inner y v v := by
    by_cases hv : v = 0
    · subst hv
      simp
    · exact (gBase.pos y v hv).le
  have hnorm0 (y : N) (hy : y ∈ u) : (Module.finrank ℝ E : ℝ) *
      metricDerivNorm (I := I) 0 gInf gBase gBase y ≤ 1 / 2 := by
    have hn : (0 : ℝ) ≤ Module.finrank ℝ E := by positivity
    exact le_trans (mul_le_mul_of_nonneg_left (hInf y hy 0 (Nat.zero_le p)) hn) hδdim
  have hequiv : ∀ y ∈ u, ∀ v : TangentSpace I y,
      ((2 : ℝ)⁻¹ * gBase.inner y v v ≤ gInf.inner y v v) ∧
        gInf.inner y v v ≤ 2 * gBase.inner y v v := by
    intro y hy v
    have hquad := metricQuadFormDiff_le_metricDerivNorm
      (I := I) gInf gBase gBase y v
    have habs : |gInf.inner y v v - gBase.inner y v v| ≤
        (1 / 2 : ℝ) * gBase.inner y v v :=
      le_trans hquad (mul_le_mul_of_nonneg_right (hnorm0 y hy) (hBaseNN y v))
    rw [abs_le] at habs
    constructor <;> norm_num at habs ⊢ <;> linarith
  have hsymm (a : ℕ) : metricDerivNorm (I := I) a gBase gInf gBase x =
      metricDerivNorm (I := I) a gInf gBase gBase x := by
    have hneg : metricDiffCovDerivAt (I := I) a gBase gInf gBase x =
        -metricDiffCovDerivAt (I := I) a gInf gBase gBase x := by
      simp [metricDiffCovDerivAt]
    rw [metricDerivNorm, metricDerivNorm, hneg, Tensor0SBundle.normSq0S_neg]
  have hbase (a : ℕ) (hap : a ≤ p) :
      metricDerivNorm (I := I) a A gInf gBase x ≤ 2 * δ := by
    calc
      metricDerivNorm (I := I) a A gInf gBase x ≤
          metricDerivNorm (I := I) a A gBase gBase x +
            metricDerivNorm (I := I) a gBase gInf gBase x :=
        metricDerivNorm_triangle (I := I) a A gBase gInf gBase x
      _ ≤ δ + δ := by rw [hsymm]; exact add_le_add (hA x hx a hap) (hInf x hx a hap)
      _ = 2 * δ := by ring
  by_cases hq0 : q = 0
  · subst q
    have hzero := diffNorm_zero_change (I := I) A gInf gInf gBase x
      (C := (2 : ℝ)) (by norm_num) (hequiv x hx)
    norm_num at hzero
    calc
      metricDerivNorm (I := I) 0 A gInf gInf x ≤
          2 * metricDerivNorm (I := I) 0 A gInf gBase x := hzero
      _ ≤ 4 * δ := by nlinarith [hbase 0 (Nat.zero_le p)]
      _ ≤ metricReferenceChangeFactor (E := E) p * δ :=
        mul_le_mul_of_nonneg_right (four_le_metric_reference_change_factor (E := E) p) hδ0
      _ ≤ ε := hδbudget
  · have hqpos : 0 < q := Nat.pos_of_ne_zero hq0
    have hInf1 : ∀ y ∈ u, ∀ j, 1 ≤ j → j ≤ p →
        metricDerivNorm (I := I) j gInf gBase gBase y ≤ 1 := by
      intro y hy j _ hjp
      exact le_trans (hInf y hy j hjp) hδ1
    have hequiv1 : ∀ y ∈ u, ∀ v : TangentSpace I y,
        ((1 : ℝ) + 1)⁻¹ * gBase.inner y v v ≤ gInf.inner y v v ∧
          gInf.inner y v v ≤ ((1 : ℝ) + 1) * gBase.inner y v v := by
      intro y hy v
      norm_num
      simpa only [one_div] using hequiv y hy v
    have hchange := metric_deriv_norm_change_le (I := I) hu A gInf gInf gBase p q 1
      (by norm_num) (by norm_num) hequiv1 hInf1 x hx hqpos hqp
    norm_num at hchange
    have hsum : ∑ k ∈ Finset.range q,
        metricDerivNorm (I := I) k A gInf gBase x ≤ (q : ℝ) * (2 * δ) := by
      calc
        (∑ k ∈ Finset.range q, metricDerivNorm (I := I) k A gInf gBase x) ≤
            ∑ _k ∈ Finset.range q, 2 * δ := by
          apply Finset.sum_le_sum
          intro k hk
          exact hbase k (Nat.le_trans (Nat.le_of_lt (Finset.mem_range.mp hk)) hqp)
        _ = (q : ℝ) * (2 * δ) := by simp
    have hC : 0 ≤ metricCovariantDerivativeComparisonConstant (E := E) 2 p := metric_covariant_derivative_comparison_constant_nonneg (E := E) 2 p
    have hinside : metricDerivNorm (I := I) q A gInf gBase x +
          metricCovariantDerivativeComparisonConstant (E := E) 2 p *
            (∑ k ∈ Finset.range q, metricDerivNorm (I := I) k A gInf gBase x) ≤
        (2 + 2 * metricCovariantDerivativeComparisonConstant (E := E) 2 p * (q : ℝ)) * δ := by
      calc
        _ ≤ 2 * δ + metricCovariantDerivativeComparisonConstant (E := E) 2 p * ((q : ℝ) * (2 * δ)) :=
          add_le_add (hbase q hqp) (mul_le_mul_of_nonneg_left hsum hC)
        _ = _ := by ring
    calc
      metricDerivNorm (I := I) q A gInf gInf x ≤
          Real.sqrt ((2 : ℝ) ^ (2 + q)) *
            (metricDerivNorm (I := I) q A gInf gBase x +
              metricCovariantDerivativeComparisonConstant (E := E) 2 p *
                (∑ k ∈ Finset.range q,
                  metricDerivNorm (I := I) k A gInf gBase x)) := hchange
      _ ≤ Real.sqrt ((2 : ℝ) ^ (2 + q)) *
          ((2 + 2 * metricCovariantDerivativeComparisonConstant (E := E) 2 p * (q : ℝ)) * δ) :=
        mul_le_mul_of_nonneg_left hinside (Real.sqrt_nonneg _)
      _ = (Real.sqrt ((2 : ℝ) ^ (2 + q)) *
          (2 + 2 * metricCovariantDerivativeComparisonConstant (E := E) 2 p * (q : ℝ))) * δ := by ring
      _ ≤ metricReferenceChangeFactor (E := E) p * δ :=
        mul_le_mul_of_nonneg_right (metric_reference_change_term_le_factor (E := E) p q hqp) hδ0
      _ ≤ ε := hδbudget

omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem exists_iterated_covariant_derivative_norm_comparison_bound
    {q₂ : ℕ} {u : Set M} (hu : IsOpen u)
    (g gRef : SmoothRiemannianMetric I M)
    (T : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) q₂)
    (p : ℕ) (eps : Real) (heps0 : 0 ≤ eps) (heps1 : eps ≤ 1)
    (hequiv : ∀ x ∈ u, ∀ v : TangentSpace I x,
      (1 + eps)⁻¹ * gRef.inner x v v ≤ g.inner x v v ∧
        g.inner x v v ≤ (1 + eps) * gRef.inner x v v)
    (hgK : ∀ x ∈ u, ∀ j, 1 ≤ j → j ≤ p →
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef x (2 + j)
        (iterCov (I := I) gRef 2 (Tensor0SBundle.metricTensorField (I := I) g) j x)) ≤ eps) :
    ∃ Cc : Real, 0 ≤ Cc ∧ ∀ x ∈ u, ∀ r : ℕ, 0 < r → r ≤ p →
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x (q₂ + r)
          (iterCov (I := I) g q₂ T r x)) ≤
        Real.sqrt ((1 + eps) ^ (q₂ + r)) *
          (Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef x (q₂ + r)
              (iterCov (I := I) gRef q₂ T r x)) +
            eps * Cc * ∑ k ∈ Finset.range r,
              Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef x (q₂ + k)
                (iterCov (I := I) gRef q₂ T k x))) := by
  refine ⟨metricCovariantDerivativeComparisonConstant (E := E) q₂ p, metric_covariant_derivative_comparison_constant_nonneg (E := E) q₂ p, ?_⟩
  exact iterated_covariant_derivative_norm_comparison_bound hu g gRef T p eps heps0 heps1 hequiv hgK

omit [I.Boundaryless] in
theorem exists_uniform_iterated_covariant_derivative_norm_comparison_bound (q₂ p : ℕ) :
    ∃ Cc : Real, 0 ≤ Cc ∧
      ∀ {M' : Type u} [TopologicalSpace M'] [ChartedSpace H M']
        [T2Space M'] [IsManifold I ∞ M'] [SigmaCompactSpace M']
        [IsManifold I 1 M'] [IsManifold I 2 M']
        [IsManifold I ((∞ : WithTop ℕ∞) + 1) M']
        {u : Set M'} (_ : IsOpen u)
        (g gRef : SmoothRiemannianMetric I M')
        (T : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M') (n := (∞ : WithTop ℕ∞)) q₂)
        (eps : Real), 0 ≤ eps → eps ≤ 1 →
        (∀ x ∈ u, ∀ v : TangentSpace I x,
          (1 + eps)⁻¹ * gRef.inner x v v ≤ g.inner x v v ∧
            g.inner x v v ≤ (1 + eps) * gRef.inner x v v) →
        (∀ x ∈ u, ∀ j, 1 ≤ j → j ≤ p →
          Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef x (2 + j)
            (iterCov (I := I) gRef 2
              (Tensor0SBundle.metricTensorField (I := I) g) j x)) ≤ eps) →
        ∀ x ∈ u, ∀ r : ℕ, 0 < r → r ≤ p →
          Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x (q₂ + r)
              (iterCov (I := I) g q₂ T r x)) ≤
            Real.sqrt ((1 + eps) ^ (q₂ + r)) *
              (Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef x (q₂ + r)
                  (iterCov (I := I) gRef q₂ T r x)) +
                eps * Cc * ∑ k ∈ Finset.range r,
                  Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef x (q₂ + k)
                    (iterCov (I := I) gRef q₂ T k x))) := by
  refine ⟨metricCovariantDerivativeComparisonConstant (E := E) q₂ p, metric_covariant_derivative_comparison_constant_nonneg (E := E) q₂ p, ?_⟩
  intro M' instTop instChart instT2 instMan instSigma instMan1 instMan2 instManSucc
    u hu g gRef T eps heps0 heps1 hequiv hgK
  exact iterated_covariant_derivative_norm_comparison_bound hu g gRef T p eps heps0 heps1 hequiv hgK

end HCGCompactness
end DifferentialGeometry
