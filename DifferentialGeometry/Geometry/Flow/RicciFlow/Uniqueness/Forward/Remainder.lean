import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.TensorDecomposition
import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.CurvatureBounds
import DifferentialGeometry.Tensor.RSTensor.NormSqProduct
import DifferentialGeometry.Tensor.RSTensor.FiberMetric.Tensor0SMetricIneq

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle DifferentialGeometry.Tensor0SBundle
open _root_.Tensor0SBundle
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.RSTensor
open scoped Manifold ContDiff BigOperators Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]


section Fiber

variable {Idx : Type*} [Fintype Idx] {x : M}

omit [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
theorem lowOfComp_ext (g : SmoothRiemannianMetric I M)
    (b : Module.Basis Idx Real (TangentSpace I x))
    (c : Idx → Idx → Idx → Idx → Real)
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x)
    (hcomp : ∀ i j k l,
      Tensor0SSpace.eval T (vec4 (I := I) (b i) (b j) (b k) (b l)) = c i j k l) :
    lowOfComp (I := I) g b c = T := by
  classical
  refine ContinuousMultilinearMap.toMultilinearMap_injective
    (Module.Basis.ext_multilinear (fun _ : Fin 4 => b) fun w => ?_)
  have hw : (fun p : Fin 4 => b (w p)) =
      vec4 (I := I) (b (w 0)) (b (w 1)) (b (w 2)) (b (w 3)) := by
    funext p
    fin_cases p <;> simp [vec4]
  change Tensor0SSpace.eval (lowOfComp (I := I) g b c) (fun p => b (w p)) =
    Tensor0SSpace.eval T (fun p => b (w p))
  rw [hw]
  rw [lowOfComp_eval]
  exact (hcomp (w 0) (w 1) (w 2) (w 3)).symm

omit [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
theorem lowerTri_low (g : SmoothRiemannianMetric I M)
    (q : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (A : TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x →L[Real]
      TangentSpace I x)
    (b : Module.Basis Idx Real (TangentSpace I x)) :
    lowOfComp (I := I) g b
        (fun i j k l =>
          q (fun a : Fin 2 => if a = 0 then ((A (b i)) (b j)) (b k) else b l)) =
      lowerTri (I := I) q A := by
  apply lowOfComp_ext (I := I)
  intro i j k l
  exact lowerTri_apply (I := I) q A
    (vec4 (I := I) (b i) (b j) (b k) (b l))

end Fiber

section ComponentRemainder

variable {Idx : Type*} [Fintype Idx]

omit [SigmaCompactSpace M] [I.Boundaryless] in
theorem rmDotRem_low
    (g₁ g₂ : SmoothRiemannianMetric I M)
    (T₂ : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (basisAt : (y : M) → Module.Basis Idx Real (TangentSpace I y))
    (Rm₁ Rm₂ B₁ B₂ : FourComp M Idx) (Ric₁ Ric₂ : MatrixComp M Idx)
    (t : Real) (x : M) :
    lowOfComp (I := I) g₁ (basisAt x)
        (rmDotRem (I := I) g₁ g₂ T₂ Rm₁ Rm₂ B₁ B₂ Ric₁ Ric₂
          (fun m z => basisAt z m) t x) =
      lapDiffRem (I := I) g₁ g₂ T₂ x -
        (2 : Real) • lowOfComp (I := I) g₁ (basisAt x)
          (fun i j k l =>
            (B₁ t x i j k l - B₂ t x i j k l) -
              (B₁ t x i j l k - B₂ t x i j l k) +
            (B₁ t x i k j l - B₂ t x i k j l) -
              (B₁ t x i l j k - B₂ t x i l j k)) -
        lowOfComp (I := I) g₁ (basisAt x)
          (fun i j k l =>
            riemann04RicciDriftInFrame Ric₁ Rm₁ t x i j k l -
              riemann04RicciDriftInFrame Ric₂ Rm₂ t x i j k l) := by
  apply lowOfComp_ext (I := I)
  intro i j k l
  rw [Tensor0SSpace.eval_sub,
    Tensor0SSpace.eval_sub,
    Tensor0SSpace.eval_smul,
    lowOfComp_eval, lowOfComp_eval]
  rfl

variable [NeZero (Module.finrank Real E)]


omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] [I.Boundaryless] in
theorem rmDotRemSq_le
    (g₁ g₂ : SmoothRiemannianMetric I M)
    (T₂ : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (basisAt : (y : M) → Module.Basis Idx Real (TangentSpace I y))
    (Rm₁ Rm₂ B₁ B₂ : FourComp M Idx) (Ric₁ Ric₂ : MatrixComp M Idx)
    (t : Real) (x : M) {Λ B₅ B₆ BQ BD : Real}
    (hΛ0 : 0 ≤ Λ)
    (hΛ : ∀ v : TangentSpace I x, g₁.inner x v v ≤ Λ * g₂.inner x v v)
    (hB₅ : normSq0S (I := I) g₁ x 5 (metricNabla0S (I := I) g₂ T₂ x) ≤ B₅)
    (hB₆ : normSq0S (I := I) g₁ x 6
      (metricNabla0S (I := I) g₂ (metricNabla0S (I := I) g₂ T₂) x) ≤ B₆)
    (hBQ : normSq0S (I := I) g₁ x 4
      (lowOfComp (I := I) g₁ (basisAt x)
        (fun i j k l =>
          (B₁ t x i j k l - B₂ t x i j k l) -
            (B₁ t x i j l k - B₂ t x i j l k) +
          (B₁ t x i k j l - B₂ t x i k j l) -
            (B₁ t x i l j k - B₂ t x i l j k))) ≤ BQ)
    (hBD : normSq0S (I := I) g₁ x 4
      (lowOfComp (I := I) g₁ (basisAt x)
        (fun i j k l =>
          riemann04RicciDriftInFrame Ric₁ Rm₁ t x i j k l -
            riemann04RicciDriftInFrame Ric₂ Rm₂ t x i j k l)) ≤ BD) :
    normSq0S (I := I) g₁ x 4
      (lowOfComp (I := I) g₁ (basisAt x)
        (rmDotRem (I := I) g₁ g₂ T₂ Rm₁ Rm₂ B₁ B₂ Ric₁ Ric₂
          (fun m z => basisAt z m) t x)) ≤
      4 * (50 * (Module.finrank Real E : Real) ^ 12 *
          connectionDifferenceSq (I := I) g₁ g₂ x * B₅ +
        2 * (Module.finrank Real E : Real) ^ 10 * Λ ^ 2 *
          metricDiffSq (I := I) g₁ g₂ x * B₆) +
      16 * BQ + 2 * BD := by
  let Q : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x :=
    lowOfComp (I := I) g₁ (basisAt x)
      (fun i j k l =>
        (B₁ t x i j k l - B₂ t x i j k l) -
          (B₁ t x i j l k - B₂ t x i j l k) +
        (B₁ t x i k j l - B₂ t x i k j l) -
          (B₁ t x i l j k - B₂ t x i l j k))
  let D : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x :=
    lowOfComp (I := I) g₁ (basisAt x)
      (fun i j k l =>
        riemann04RicciDriftInFrame Ric₁ Rm₁ t x i j k l -
          riemann04RicciDriftInFrame Ric₂ Rm₂ t x i j k l)
  have hL := rmRemNormSq_le (I := I) g₁ g₂ T₂ x hΛ0 hΛ hB₅ hB₆
  have houter := normSq0S_sub_le (I := I) g₁ x 4
    (lapDiffRem (I := I) g₁ g₂ T₂ x - (2 : Real) • Q) D
  have hinner := normSq0S_sub_le (I := I) g₁ x 4
    (lapDiffRem (I := I) g₁ g₂ T₂ x) ((2 : Real) • Q)
  have hscale :
      normSq0S (I := I) g₁ x 4 ((2 : Real) • Q) =
        4 * normSq0S (I := I) g₁ x 4 Q := by
    rw [normSq0S_eq_inner, inner0S_smul_left, inner0S_smul_right,
      ← normSq0S_eq_inner]
    ring
  rw [rmDotRem_low (I := I) g₁ g₂ T₂ basisAt Rm₁ Rm₂ B₁ B₂ Ric₁ Ric₂ t x]
  change normSq0S (I := I) g₁ x 4
      (lapDiffRem (I := I) g₁ g₂ T₂ x - (2 : Real) • Q - D) ≤ _
  calc
    normSq0S (I := I) g₁ x 4
        (lapDiffRem (I := I) g₁ g₂ T₂ x - (2 : Real) • Q - D)
        ≤ 2 * normSq0S (I := I) g₁ x 4
            (lapDiffRem (I := I) g₁ g₂ T₂ x - (2 : Real) • Q) +
          2 * normSq0S (I := I) g₁ x 4 D := houter
    _ ≤ 4 * normSq0S (I := I) g₁ x 4 (lapDiffRem (I := I) g₁ g₂ T₂ x) +
          4 * normSq0S (I := I) g₁ x 4 ((2 : Real) • Q) +
          2 * normSq0S (I := I) g₁ x 4 D := by linarith
    _ = 4 * normSq0S (I := I) g₁ x 4 (lapDiffRem (I := I) g₁ g₂ T₂ x) +
          16 * normSq0S (I := I) g₁ x 4 Q +
          2 * normSq0S (I := I) g₁ x 4 D := by rw [hscale]; ring
    _ ≤ 4 * (50 * (Module.finrank Real E : Real) ^ 12 *
            connectionDifferenceSq (I := I) g₁ g₂ x * B₅ +
          2 * (Module.finrank Real E : Real) ^ 10 * Λ ^ 2 *
            metricDiffSq (I := I) g₁ g₂ x * B₆) +
        16 * BQ + 2 * BD := by
      dsimp [Q, D] at hBQ hBD ⊢
      gcongr

end ComponentRemainder

section ReLowerRemainder

variable [NeZero (Module.finrank Real E)]

omit [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] [NeZero (Module.finrank ℝ E)] in
private theorem rem_onFrame (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ b : Module.Basis (Fin (Module.finrank Real (TangentSpace I x))) Real
        (TangentSpace I x),
      ∀ i j, g.inner x (b i) (b j) = if i = j then (1 : Real) else 0 := by
  classical
  let D := (tangentMetricDataGen (I := I) g x).metric
  let : InnerProductSpace.Core Real (TangentSpace I x) := D.toCore
  let : NormedAddCommGroup (TangentSpace I x) :=
    @InnerProductSpace.Core.toNormedAddCommGroup Real (TangentSpace I x) _ _ _ D.toCore
  let : InnerProductSpace Real (TangentSpace I x) :=
    @InnerProductSpace.ofCore Real (TangentSpace I x) _ _ _ D.toCore.toCore
  let ob := stdOrthonormalBasis Real (TangentSpace I x)
  refine ⟨ob.toBasis, ?_⟩
  intro i j
  have hinner : Inner.inner Real (ob i) (ob j) = D.inner (ob i) (ob j) :=
    MetricFiberData.toCore_inner D (ob i) (ob j)
  change g.inner x (ob.toBasis i) (ob.toBasis j) = if i = j then (1 : Real) else 0
  rw [← TangentMetricDataGen.inner_eq_gen
    (tangentMetricDataGen (I := I) g x) (ob.toBasis i) (ob.toBasis j)]
  change D.inner (ob i) (ob j) = if i = j then (1 : Real) else 0
  rw [← hinner]
  exact ob.inner_eq_ite i j

omit [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] [NeZero (Module.finrank ℝ E)] in
private theorem rem_repr_inner {Idx : Type*} [Finite Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hON : ∀ i j, g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (v : TangentSpace I x) (k : Idx) :
    basis.repr v k = g.inner x v (basis k) := by
  classical
  let := Fintype.ofFinite Idx
  have hval : g.inner x v (basis k) =
      metricTensorField (I := I) g x (fun a : Fin 2 => if a = 0 then v else basis k) := by
    rw [metricTensorField_apply]
    simp
  rw [hval, tensor02_expand (I := I) (metricTensorField (I := I) g x) basis v (basis k)]
  have hbb : ∀ l : Idx,
      metricTensorField (I := I) g x
          (fun a : Fin 2 => if a = 0 then basis l else basis k) =
        (if l = k then (1 : Real) else 0) := by
    intro l
    rw [metricTensorField_apply]
    simpa using hON l k
  simp only [hbb, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]


omit [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] [NeZero (Module.finrank ℝ E)] in
theorem reLowerDefSq_le (g₁ g₂ : SmoothRiemannianMetric I M) {s : ℕ}
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1))
    (x : M) :
    normSq0S (I := I) g₁ x (s + 1)
        (reLower (I := I) g₂ g₁ T x - T x) ≤
      (Module.finrank Real E : Real) ^ (s + 3) *
        (normSq0S (I := I) g₁ x (s + 1) (T x) *
          metricDiffSq (I := I) g₁ g₂ x) := by
  classical
  obtain ⟨basis, hON⟩ := rem_onFrame (I := I) g₁ x
  have hinv : MetricInverseInBasisGen (I := I) g₁ x basis
      (identityInvMetric (Idx := Fin (Module.finrank Real (TangentSpace I x)))) :=
    DifferentialGeometry.Tensor0SBundle.metricInverseInBasis_of_orthonormal (I := I) g₁ basis hON
  let Hdiff : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2 :=
    metricTensorField (I := I) g₂ - metricTensorField (I := I) g₁
  let V : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 1 + 2) x :=
    (Tensor0SSpace.product (T x) (Hdiff x)).domDomCongr
      (reLowerPermutationWithTwoInputs s)
  have hself : reLower (I := I) g₁ g₁ T x = T x := by
    refine ContinuousMultilinearMap.ext fun tail => ?_
    change Tensor0SSpace.eval (reLower (I := I) g₁ g₁ T x) tail =
      Tensor0SSpace.eval (T x) tail
    rw [reLower_apply (I := I) g₁ g₁ T x, sharpFlat_self]
    rw [Function.update_eq_self]
  have htrace : reLower (I := I) g₂ g₁ T x - T x =
      metricTraceFirstTwo0STensor (I := I) g₁ V := by
    rw [← hself]
    refine ContinuousMultilinearMap.ext fun tail => ?_
    change Tensor0SSpace.eval
        (reLower (I := I) g₂ g₁ T x - reLower (I := I) g₁ g₁ T x) tail =
      Tensor0SSpace.eval (metricTraceFirstTwo0STensor (I := I) g₁ V) tail
    have htraceBasis :
        Tensor0SSpace.eval (metricTraceFirstTwo0STensor (I := I) g₁ V) tail =
          metricTrace0S2InBasis (I := I) basis identityInvMetric V tail := by
      change metricTraceFirstTwo0STensor (I := I) g₁ V tail = _
      rw [metricTraceFirstTwo0STensor_apply,
        metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g₁ basis _ hinv]
    rw [Tensor0SSpace.eval_sub,
      reLower_eval (I := I) g₂ g₁ T basis _ hinv tail,
      reLower_eval (I := I) g₁ g₁ T basis _ hinv tail,
      htraceBasis]
    unfold metricTrace0S2InBasis
    change
      (∑ i, ∑ j, identityInvMetric i j *
          (Tensor0SSpace.eval (T x) (Function.update tail (Fin.last s) (basis i)) *
            g₂.inner x (basis j) (tail (Fin.last s)))) -
        (∑ i, ∑ j, identityInvMetric i j *
          (Tensor0SSpace.eval (T x) (Function.update tail (Fin.last s) (basis i)) *
            g₁.inner x (basis j) (tail (Fin.last s)))) =
      ∑ i, ∑ j, identityInvMetric i j *
        Tensor0SSpace.eval V (metricTraceInput (I := I) (basis i) (basis j) tail)
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    change
      identityInvMetric i j *
          (Tensor0SSpace.eval (T x) (Function.update tail (Fin.last s) (basis i)) *
            g₂.inner x (basis j) (tail (Fin.last s))) -
        identityInvMetric i j *
          (Tensor0SSpace.eval (T x) (Function.update tail (Fin.last s) (basis i)) *
            g₁.inner x (basis j) (tail (Fin.last s))) =
      identityInvMetric i j *
        Tensor0SSpace.eval V (metricTraceInput (I := I) (basis i) (basis j) tail)
    rw [show V = (Tensor0SSpace.product (T x) (Hdiff x)).domDomCongr
      (reLowerPermutationWithTwoInputs s) from rfl,
      Tensor0SSpace.eval_domDomCongr]
    have hproduct := Tensor0SSpace.product_apply (T x) (Hdiff x)
      (metricTraceInput (I := I) (basis i) (basis j) tail ∘
        reLowerPermutationWithTwoInputs s)
    change Tensor0SSpace.eval (Tensor0SSpace.product (T x) (Hdiff x)) _ =
      Tensor0SSpace.eval (T x) _ * Tensor0SSpace.eval (Hdiff x) _ at hproduct
    rw [hproduct]
    have hfirst :
        ((metricTraceInput (I := I) (basis i) (basis j) tail ∘
          reLowerPermutationWithTwoInputs s) ∘ Fin.castAdd 2) =
            Function.update tail (Fin.last s) (basis i) := by
      funext k
      exact reLowerPermutationWithTwoInputs_first_block (I := I) (basis i) (basis j) tail k
    rw [hfirst]
    change
      _ = identityInvMetric i j *
        (T x (Function.update tail (Fin.last s) (basis i)) *
          ((metricTensorField (I := I) g₂ - metricTensorField (I := I) g₁) x)
            (fun p : Fin 2 =>
              metricTraceInput (I := I) (basis i) (basis j) tail
                (reLowerPermutationWithTwoInputs s (Fin.natAdd (s + 1) p))))
    have hsnd :
        (fun p : Fin 2 =>
          metricTraceInput (I := I) (basis i) (basis j) tail
            (reLowerPermutationWithTwoInputs s (Fin.natAdd (s + 1) p))) =
          fun p : Fin 2 => if p = 0 then basis j else tail (Fin.last s) := by
      funext p
      fin_cases p
      · simpa using reLowerPermutationWithTwoInputs_tail_zero (I := I) (basis i) (basis j) tail
      · simpa using reLowerPermutationWithTwoInputs_tail_one (I := I) (basis i) (basis j) tail
    have hHdiff :
        (metricTensorField (I := I) g₂ - metricTensorField (I := I) g₁) x =
          metricTensorField (I := I) g₂ x - metricTensorField (I := I) g₁ x := rfl
    rw [hsnd, hHdiff, Tensor0SSpace.sub_apply (I := I) 2 x,
      metricTensorField_apply, metricTensorField_apply]
    have h10 : (1 : Fin 2) ≠ 0 := by decide
    simp only [if_true, h10, if_false]
    rw [Tensor0SSpace.eval_eq]
    ring
  have hprod :
      normSq0S (I := I) g₁ x (s + 1 + 2)
          (Tensor0SSpace.product (T x) (Hdiff x)) =
        normSq0S (I := I) g₁ x (s + 1) (T x) *
          normSq0S (I := I) g₁ x 2 (Hdiff x) :=
    normSq0S_prod (I := I) g₁ x basis hinv (T x) (Hdiff x)
  have hcongr :
      normSq0S (I := I) g₁ x (s + 1 + 2) V =
        normSq0S (I := I) g₁ x (s + 1 + 2)
          (Tensor0SSpace.product (T x) (Hdiff x)) :=
    normSq0S_domDomCongr (I := I) g₁ x basis hinv (reLowerPermutationWithTwoInputs s) _
  have hH :
      normSq0S (I := I) g₁ x 2 (Hdiff x) = metricDiffSq (I := I) g₁ g₂ x := by
    rw [metricDiffSq_def]
    have heq : Hdiff x = -metricDiffAt (I := I) g₁ g₂ x := by
      dsimp [Hdiff, metricDiffAt]
      abel
    rw [heq, Tensor0SBundle.normSq0S_neg]
  rw [htrace]
  have htr := traceNormSq_le (I := I) (s := s + 1) g₁ x V
  rw [hcongr, hprod, hH] at htr
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htr

end ReLowerRemainder

section LowerTriBound

omit [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
theorem metricDiffSwap_le (g₁ g₂ : SmoothRiemannianMetric I M) (x : M)
    {C : Real} (hC : 1 ≤ C)
    (hequiv : ∀ v : TangentSpace I x,
      C⁻¹ * g₁.inner x v v ≤ g₂.inner x v v ∧
        g₂.inner x v v ≤ C * g₁.inner x v v) :
    metricDiffSq (I := I) g₂ g₁ x ≤
      C ^ 2 * metricDiffSq (I := I) g₁ g₂ x := by
  have hswap :
      metricDiffAt (I := I) g₂ g₁ x = -metricDiffAt (I := I) g₁ g₂ x := by
    dsimp only [metricDiffAt]
    abel
  rw [metricDiffSq_def, metricDiffSq_def, hswap, Tensor0SBundle.normSq0S_neg]
  exact normSq0S_upper_le_of_equiv (I := I) g₁ g₂ x 2 hC hequiv _

variable [NeZero (Module.finrank Real E)]

omit [SigmaCompactSpace M] [I.Boundaryless] [NeZero (Module.finrank ℝ E)] in
theorem roughLapSq_le (g : SmoothRiemannianMetric I M) {s : ℕ}
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (x : M) :
    normSq0S (I := I) g x s (roughLap0SField (I := I) g T x) ≤
      (Module.finrank Real E : Real) ^ (s + 2) *
        normSq0S (I := I) g x (s + 2)
          (metricNabla0S (I := I) g (metricNabla0S (I := I) g T) x) := by
  simpa only [roughLap0SField_apply, roughLap0STensor] using
    (traceNormSq_le (I := I) (s := s) g x
      (metricNabla0S (I := I) g (metricNabla0S (I := I) g T) x))

private def lowerTriPerm : Equiv.Perm (Fin 6) :=
  Equiv.ofBijective ![2, 3, 4, 0, 1, 5] (by decide)


omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
theorem lowerTriSq_le (g : SmoothRiemannianMetric I M)
    {x : M}
    (Q : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (A : TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x →L[Real]
      TangentSpace I x) :
    normSq0S (I := I) g x 4 (lowerTri (I := I) Q A) ≤
      (Module.finrank Real E : Real) ^ 6 *
        (normSq0S (I := I) g x 2 Q *
          normSq0S (I := I) g x 4
            (lowerTri (I := I) (metricTensorField (I := I) g x) A)) := by
  classical
  obtain ⟨basis, hON⟩ := rem_onFrame (I := I) g x
  have hinv : MetricInverseInBasisGen (I := I) g x basis
      (identityInvMetric (Idx := Fin (Module.finrank Real (TangentSpace I x)))) :=
    DifferentialGeometry.Tensor0SBundle.metricInverseInBasis_of_orthonormal (I := I) g basis hON
  let P : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x :=
    lowerTri (I := I) (metricTensorField (I := I) g x) A
  let V : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 6 x :=
    (Tensor0SSpace.product P Q).domDomCongr lowerTriPerm
  have htrace :
      lowerTri (I := I) Q A =
        metricTraceFirstTwo0STensor (I := I) g V := by
    refine ContinuousMultilinearMap.ext fun u => ?_
    change Tensor0SSpace.eval (lowerTri (I := I) Q A) u =
      Tensor0SSpace.eval (metricTraceFirstTwo0STensor (I := I) g V) u
    have htraceBasis :
        Tensor0SSpace.eval (metricTraceFirstTwo0STensor (I := I) g V) u =
          metricTrace0S2InBasis (I := I) basis identityInvMetric V u := by
      change metricTraceFirstTwo0STensor (I := I) g V u = _
      rw [metricTraceFirstTwo0STensor_apply,
        metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g basis _ hinv]
    rw [lowerTri_apply, htraceBasis]
    unfold metricTrace0S2InBasis
    change Tensor0SSpace.eval Q
        (fun a : Fin 2 => if a = 0 then ((A (u 0)) (u 1)) (u 2) else u 3) =
      ∑ i, ∑ j, identityInvMetric i j *
        Tensor0SSpace.eval V (metricTraceInput (I := I) (basis i) (basis j) u)
    have hV : ∀ i j,
        Tensor0SSpace.eval V (metricTraceInput (I := I) (basis i) (basis j) u) =
          Tensor0SSpace.eval (lowerTri (I := I) (metricTensorField (I := I) g x) A)
              ![u 0, u 1, u 2, basis i] *
            Tensor0SSpace.eval Q (fun a : Fin 2 => if a = 0 then basis j else u 3) := by
      intro i j
      dsimp only [V, P]
      rw [Tensor0SSpace.eval_domDomCongr]
      have hproduct := Tensor0SSpace.product_apply
        (lowerTri (I := I) (metricTensorField (I := I) g x) A) Q
        (metricTraceInput (I := I) (basis i) (basis j) u ∘ lowerTriPerm)
      change Tensor0SSpace.eval
          (Tensor0SSpace.product
            (lowerTri (I := I) (metricTensorField (I := I) g x) A) Q) _ =
        Tensor0SSpace.eval
            (lowerTri (I := I) (metricTensorField (I := I) g x) A) _ *
          Tensor0SSpace.eval Q _ at hproduct
      rw [hproduct]
      have hPslots :
          ((metricTraceInput (I := I) (basis i) (basis j) u ∘ lowerTriPerm) ∘
            Fin.castAdd 2) =
            ![u 0, u 1, u 2, basis i] := by
        funext p
        fin_cases p <;>
          simp [Function.comp_apply, lowerTriPerm, Equiv.ofBijective, Fin.castAdd,
            metricTraceInput_apply]
      have hQslots :
          ((metricTraceInput (I := I) (basis i) (basis j) u ∘ lowerTriPerm) ∘
            Fin.natAdd 4) =
            fun a : Fin 2 => if a = 0 then basis j else u 3 := by
        funext p
        fin_cases p <;>
          simp [Function.comp_apply, lowerTriPerm, Equiv.ofBijective, Fin.natAdd,
            metricTraceInput_apply]
      rw [hPslots, hQslots]
    simp_rw [hV]
    simp only [identityInvMetric, diagonalInvMetric, ite_mul, one_mul, zero_mul]
    have hQ := tensor02_expand (I := I) Q basis
      (((A (u 0)) (u 1)) (u 2)) (u 3)
    change Tensor0SSpace.eval Q
        (fun a : Fin 2 => if a = 0 then ((A (u 0)) (u 1)) (u 2) else u 3) =
      ∑ k, basis.repr (((A (u 0)) (u 1)) (u 2)) k *
        Tensor0SSpace.eval Q (fun a : Fin 2 => if a = 0 then basis k else u 3) at hQ
    rw [hQ]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [rem_repr_inner (I := I) g basis hON]
    simp [lowerTri_apply]
  rw [htrace]
  have htr := traceNormSq_le (I := I) (s := 4) g x V
  have hcongr :
      normSq0S (I := I) g x 6 V =
        normSq0S (I := I) g x 6 (Tensor0SSpace.product P Q) :=
    normSq0S_domDomCongr (I := I) g x basis hinv lowerTriPerm _
  have hprod :
      normSq0S (I := I) g x 6 (Tensor0SSpace.product P Q) =
        normSq0S (I := I) g x 4 P * normSq0S (I := I) g x 2 Q :=
    normSq0S_prod (I := I) g x basis hinv P Q
  rw [hcongr, hprod] at htr
  simpa [P, mul_comm] using htr


omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
theorem lowerTriDiffSq_le (g₁ g₂ : SmoothRiemannianMetric I M)
    {x : M}
    (A : TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x →L[Real]
      TangentSpace I x) :
    normSq0S (I := I) g₁ x 4
        (lowerTri (I := I) (metricDiffAt (I := I) g₁ g₂ x) A) ≤
      (Module.finrank Real E : Real) ^ 6 *
        (normSq0S (I := I) g₁ x 4
            (lowerTri (I := I) (metricTensorField (I := I) g₁ x) A) *
          metricDiffSq (I := I) g₁ g₂ x) := by
  simpa only [metricDiffSq_def, mul_comm] using
    (lowerTriSq_le (I := I) g₁ (metricDiffAt (I := I) g₁ g₂ x) A)


omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
theorem lowerTriSwapSq_le (g₁ g₂ : SmoothRiemannianMetric I M)
    {x : M}
    (A : TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x →L[Real]
      TangentSpace I x)
    {C : Real} (hC : 1 ≤ C)
    (hequiv : ∀ v : TangentSpace I x,
      C⁻¹ * g₁.inner x v v ≤ g₂.inner x v v ∧
        g₂.inner x v v ≤ C * g₁.inner x v v) :
    normSq0S (I := I) g₁ x 4
        (lowerTri (I := I) (metricDiffAt (I := I) g₁ g₂ x) A) ≤
      C ^ 6 * (Module.finrank Real E : Real) ^ 6 *
        (normSq0S (I := I) g₂ x 4
            (lowerTri (I := I) (metricTensorField (I := I) g₂ x) A) *
          metricDiffSq (I := I) g₁ g₂ x) := by
  have hlow :
      lowerTri (I := I) (metricDiffAt (I := I) g₁ g₂ x) A =
        -lowerTri (I := I) (metricDiffAt (I := I) g₂ g₁ x) A := by
    refine ContinuousMultilinearMap.ext fun v => ?_
    change Tensor0SSpace.eval
        (lowerTri (I := I) (metricDiffAt (I := I) g₁ g₂ x) A) v =
      Tensor0SSpace.eval
        (-lowerTri (I := I) (metricDiffAt (I := I) g₂ g₁ x) A) v
    rw [lowerTri_apply, Tensor0SSpace.eval_neg, lowerTri_apply]
    rw [Tensor0SSpace.eval_eq, Tensor0SSpace.eval_eq,
      metricDiffAt_apply, metricDiffAt_apply]
    ring
  have hsymm := metric_equiv_symm (I := I) g₁ g₂ x hC hequiv
  have hcmp := normSq0S_upper_le_of_equiv (I := I) g₂ g₁ x 4 hC hsymm
    (lowerTri (I := I) (metricDiffAt (I := I) g₁ g₂ x) A)
  have hraw := lowerTriDiffSq_le (I := I) g₂ g₁ A
  have hswap := metricDiffSwap_le (I := I) g₁ g₂ x hC hequiv
  have hA0 : 0 ≤ normSq0S (I := I) g₂ x 4
      (lowerTri (I := I) (metricTensorField (I := I) g₂ x) A) :=
    normSq0S_nonneg (I := I) g₂ x 4 _
  have hraw' :
      normSq0S (I := I) g₂ x 4
          (lowerTri (I := I) (metricDiffAt (I := I) g₁ g₂ x) A) ≤
        (Module.finrank Real E : Real) ^ 6 *
          (normSq0S (I := I) g₂ x 4
              (lowerTri (I := I) (metricTensorField (I := I) g₂ x) A) *
            metricDiffSq (I := I) g₂ g₁ x) := by
    rw [hlow, Tensor0SBundle.normSq0S_neg]
    exact hraw
  calc
    normSq0S (I := I) g₁ x 4
        (lowerTri (I := I) (metricDiffAt (I := I) g₁ g₂ x) A)
        ≤ C ^ 4 * normSq0S (I := I) g₂ x 4
            (lowerTri (I := I) (metricDiffAt (I := I) g₁ g₂ x) A) := hcmp
    _ ≤ C ^ 4 * ((Module.finrank Real E : Real) ^ 6 *
          (normSq0S (I := I) g₂ x 4
              (lowerTri (I := I) (metricTensorField (I := I) g₂ x) A) *
            metricDiffSq (I := I) g₂ g₁ x)) :=
      mul_le_mul_of_nonneg_left hraw' (by positivity)
    _ ≤ C ^ 4 * ((Module.finrank Real E : Real) ^ 6 *
          (normSq0S (I := I) g₂ x 4
              (lowerTri (I := I) (metricTensorField (I := I) g₂ x) A) *
            (C ^ 2 * metricDiffSq (I := I) g₁ g₂ x))) := by
      gcongr
    _ = C ^ 6 * (Module.finrank Real E : Real) ^ 6 *
          (normSq0S (I := I) g₂ x 4
              (lowerTri (I := I) (metricTensorField (I := I) g₂ x) A) *
            metricDiffSq (I := I) g₁ g₂ x) := by ring


omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem ownRmDiffSq_le (g₁ g₂ : SmoothRiemannianMetric I M) (x : M)
    {BP : Real}
    (hP : normSq0S (I := I) g₁ x 4
      (CovariantDerivative.riemannCurvature04At (I := I) g₁
        (metricCov (I := I) g₂) (metricCov_smooth (I := I) g₂) x) ≤ BP) :
    normSq0S (I := I) g₁ x 4
        (metricRm04At (I := I) g₁ x - metricRm04At (I := I) g₂ x) ≤
      2 * rmDiffSq (I := I) g₁ g₂ x +
        2 * (Module.finrank Real E : Real) ^ 6 * BP *
          metricDiffSq (I := I) g₁ g₂ x := by
  let A : TangentSpace I x →L[Real] TangentSpace I x →L[Real]
      TangentSpace I x →L[Real] TangentSpace I x :=
    riemannOp (metricCov (I := I) g₂) x
  let P : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x :=
    CovariantDerivative.riemannCurvature04At (I := I) g₁
      (metricCov (I := I) g₂) (metricCov_smooth (I := I) g₂) x
  have hgap :
      lowerTri (I := I) (metricDiffAt (I := I) g₁ g₂ x) A =
        P - metricRm04At (I := I) g₂ x := by
    refine ContinuousMultilinearMap.ext fun v => ?_
    change Tensor0SSpace.eval
        (lowerTri (I := I) (metricDiffAt (I := I) g₁ g₂ x) A) v =
      Tensor0SSpace.eval (P - metricRm04At (I := I) g₂ x) v
    have hv : v = vec4 (I := I) (v 0) (v 1) (v 2) (v 3) := by
      funext i
      fin_cases i <;> rfl
    have hmix := rm04mix_inner (I := I) g₁ g₂ x (v 0) (v 1) (v 2) (v 3)
    change Tensor0SSpace.eval P
      (vec4 (I := I) (v 0) (v 1) (v 2) (v 3)) = _ at hmix
    have hmetric := metricRm04At_inner (I := I) g₂ x (v 0) (v 1) (v 2) (v 3)
    change Tensor0SSpace.eval (metricRm04At (I := I) g₂ x)
      (vec4 (I := I) (v 0) (v 1) (v 2) (v 3)) = _ at hmetric
    rw [hv, lowerTri_apply, Tensor0SSpace.eval_sub, hmix, hmetric]
    have hmetricDiff := metricDiffAt_apply (I := I) g₁ g₂ x
      (fun a : Fin 2 => if a = 0 then ((A (v 0)) (v 1)) (v 2) else v 3)
    change Tensor0SSpace.eval (metricDiffAt (I := I) g₁ g₂ x) _ = _ at hmetricDiff
    exact hmetricDiff
  have hsplit :
      metricRm04At (I := I) g₁ x - metricRm04At (I := I) g₂ x =
        rmDiffLowAt (I := I) g₁ g₂ x +
          lowerTri (I := I) (metricDiffAt (I := I) g₁ g₂ x) A := by
    refine ContinuousMultilinearMap.ext fun v => ?_
    change Tensor0SSpace.eval
        (metricRm04At (I := I) g₁ x - metricRm04At (I := I) g₂ x) v =
      Tensor0SSpace.eval
        (rmDiffLowAt (I := I) g₁ g₂ x +
          lowerTri (I := I) (metricDiffAt (I := I) g₁ g₂ x) A) v
    have hdiff := rmDiffLowAt_apply (I := I) g₁ g₂ x v
    change Tensor0SSpace.eval (rmDiffLowAt (I := I) g₁ g₂ x) v =
      Tensor0SSpace.eval (metricRm04At (I := I) g₁ x) v -
        Tensor0SSpace.eval P v at hdiff
    rw [Tensor0SSpace.eval_sub, Tensor0SSpace.eval_add, hdiff]
    have hg := congrArg (fun T => Tensor0SSpace.eval T v) hgap
    simp only [Tensor0SSpace.eval_sub] at hg
    rw [hg]
    ring
  have hadd := normSq0S_add_le (I := I) g₁ x 4
    (rmDiffLowAt (I := I) g₁ g₂ x)
    (lowerTri (I := I) (metricDiffAt (I := I) g₁ g₂ x) A)
  have hlow := lowerTriDiffSq_le (I := I) g₁ g₂ A
  have hP' :
      normSq0S (I := I) g₁ x 4
          (lowerTri (I := I) (metricTensorField (I := I) g₁ x) A) ≤ BP := by
    have heq :
        lowerTri (I := I) (metricTensorField (I := I) g₁ x) A = P := by
      refine ContinuousMultilinearMap.ext fun v => ?_
      change Tensor0SSpace.eval
          (lowerTri (I := I) (metricTensorField (I := I) g₁ x) A) v =
        Tensor0SSpace.eval P v
      have hv : v = vec4 (I := I) (v 0) (v 1) (v 2) (v 3) := by
        funext i
        fin_cases i <;> rfl
      have hmix := rm04mix_inner (I := I) g₁ g₂ x (v 0) (v 1) (v 2) (v 3)
      change Tensor0SSpace.eval P
        (vec4 (I := I) (v 0) (v 1) (v 2) (v 3)) = _ at hmix
      rw [hv, lowerTri_apply, hmix]
      have hmetric := metricTensorField_apply (I := I) g₁ x
        (fun a : Fin 2 => if a = 0 then ((A (v 0)) (v 1)) (v 2) else v 3)
      change Tensor0SSpace.eval (metricTensorField (I := I) g₁ x) _ = _ at hmetric
      exact hmetric
    rw [heq]
    exact hP
  rw [hsplit]
  calc
    normSq0S (I := I) g₁ x 4
        (rmDiffLowAt (I := I) g₁ g₂ x +
          lowerTri (I := I) (metricDiffAt (I := I) g₁ g₂ x) A)
        ≤ 2 * normSq0S (I := I) g₁ x 4 (rmDiffLowAt (I := I) g₁ g₂ x) +
          2 * normSq0S (I := I) g₁ x 4
            (lowerTri (I := I) (metricDiffAt (I := I) g₁ g₂ x) A) := hadd
    _ ≤ 2 * rmDiffSq (I := I) g₁ g₂ x +
          2 * ((Module.finrank Real E : Real) ^ 6 *
            (BP * metricDiffSq (I := I) g₁ g₂ x)) := by
      rw [rmDiffSq_def]
      have hmetric0 : 0 ≤ metricDiffSq (I := I) g₁ g₂ x := by
        rw [metricDiffSq_def]
        exact normSq0S_nonneg (I := I) g₁ x 2 _
      have hprod :
          normSq0S (I := I) g₁ x 4
                (lowerTri (I := I) (metricTensorField (I := I) g₁ x) A) *
              metricDiffSq (I := I) g₁ g₂ x ≤
            BP * metricDiffSq (I := I) g₁ g₂ x :=
        mul_le_mul_of_nonneg_right hP' hmetric0
      have hlow' := hlow.trans
        (mul_le_mul_of_nonneg_left hprod (by positivity))
      have hscaled :
          2 * normSq0S (I := I) g₁ x 4
                (lowerTri (I := I) (metricDiffAt (I := I) g₁ g₂ x) A) ≤
            2 * ((Module.finrank Real E : Real) ^ 6 *
              (BP * metricDiffSq (I := I) g₁ g₂ x)) :=
        mul_le_mul_of_nonneg_left hlow' (by norm_num)
      have hsum :
          2 * normSq0S (I := I) g₁ x 4 (rmDiffLowAt (I := I) g₁ g₂ x) +
              2 * normSq0S (I := I) g₁ x 4
                (lowerTri (I := I) (metricDiffAt (I := I) g₁ g₂ x) A) ≤
            2 * normSq0S (I := I) g₁ x 4 (rmDiffLowAt (I := I) g₁ g₂ x) +
              2 * ((Module.finrank Real E : Real) ^ 6 *
                (BP * metricDiffSq (I := I) g₁ g₂ x)) :=
        add_le_add le_rfl hscaled
      exact hsum
    _ = 2 * rmDiffSq (I := I) g₁ g₂ x +
          2 * (Module.finrank Real E : Real) ^ 6 * BP *
            metricDiffSq (I := I) g₁ g₂ x := by ring


omit [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] [NeZero (Module.finrank ℝ E)] in
theorem traceProdSq_le (g : SmoothRiemannianMetric I M) {a b r : ℕ}
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) a)
    (B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) b)
    (σ : Fin (a + b) ≃ Fin (r + 2)) (x : M) :
    normSq0S (I := I) g x r
        (metricTraceFirstTwoField (I := I) (M := M) (s := r) g
          (MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
            (E := TangentSpace I) (∞ : WithTop ℕ∞) σ
            (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
              (E := TangentSpace I) (n := (∞ : WithTop ℕ∞))
              (s := a) (q := b) A B)) x) ≤
      (Module.finrank Real E : Real) ^ (r + 2) *
        (normSq0S (I := I) g x a (A x) * normSq0S (I := I) g x b (B x)) := by
  classical
  obtain ⟨basis, hON⟩ := rem_onFrame (I := I) g x
  have hinv : MetricInverseInBasisGen (I := I) g x basis
      (identityInvMetric (Idx := Fin (Module.finrank Real (TangentSpace I x)))) :=
    DifferentialGeometry.Tensor0SBundle.metricInverseInBasis_of_orthonormal (I := I) g basis hON
  let W : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (r + 2) :=
    MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
      (E := TangentSpace I) (∞ : WithTop ℕ∞) σ
      (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
        (E := TangentSpace I) (n := (∞ : WithTop ℕ∞))
        (s := a) (q := b) A B)
  rw [show metricTraceFirstTwoField (I := I) (M := M) (s := r) g W x =
      metricTraceFirstTwo0STensor (I := I) g (W x) from rfl]
  have htr := traceNormSq_le (I := I) (s := r) g x (W x)
  have hcongr :
      normSq0S (I := I) g x (r + 2) (W x) =
        normSq0S (I := I) g x (a + b)
          (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
            (E := TangentSpace I) (n := (∞ : WithTop ℕ∞))
            (s := a) (q := b) A B x) := by
    change normSq0S (I := I) g x (r + 2)
        (ContinuousMultilinearMap.domDomCongr σ
          (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
            (E := TangentSpace I) (n := (∞ : WithTop ℕ∞))
            (s := a) (q := b) A B x)) = _
    exact normSq0S_domDomCongr (I := I) g x basis hinv σ
      (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
        (E := TangentSpace I) (n := (∞ : WithTop ℕ∞))
        (s := a) (q := b) A B x)
  have hprod :
      normSq0S (I := I) g x (a + b)
          (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
            (E := TangentSpace I) (n := (∞ : WithTop ℕ∞))
            (s := a) (q := b) A B x) =
        normSq0S (I := I) g x a (A x) * normSq0S (I := I) g x b (B x) :=
    normSq0S_product (I := I) g x basis hinv A B
  rw [hcongr, hprod] at htr
  exact htr

end LowerTriBound

section GapRemainder

variable {Idx : Type*} [Fintype Idx]

omit [SigmaCompactSpace M] in
theorem uhlSpeed_low
    (g : Real → SmoothRiemannianMetric I M)
    (basisAt : (y : M) → Module.Basis Idx Real (TangentSpace I y))
    (Rm04 roughLapRm04 B : FourComp M Idx) (ricciOneUp : MatrixComp M Idx)
    (t : Real) (x : M) :
    lowOfComp (I := I) (g t) (basisAt x)
        (fun i j k l =>
          (roughLapRm04 t x i j k l -
              2 * (B t x i j k l - B t x i j l k + B t x i k j l - B t x i l j k) -
              riemann04RicciDriftInFrame ricciOneUp Rm04 t x i j k l) +
            2 * metricRicciAt (I := I) (g t) x
              (fun q : Fin 2 =>
                if q = 0 then
                  riemannOp (metricCov (I := I) (g t)) x
                    (basisAt x i) (basisAt x j) (basisAt x k)
                else basisAt x l)) =
      lowerTri (I := I) (metricTensorField (I := I) (g t) x)
        (uhlRm2Vec (I := I) g basisAt Rm04 roughLapRm04 B ricciOneUp t x) := by
  apply lowOfComp_ext (I := I)
  intro i j k l
  rw [lowerTri_apply, Tensor0SSpace.eval_eq, metricTensorField_apply]
  have hv :
      ((uhlRm2Vec (I := I) g basisAt Rm04 roughLapRm04 B ricciOneUp t x
        (basisAt x i)) (basisAt x j)) (basisAt x k) =
          uhlRaisedDeriv (I := I) g basisAt Rm04 roughLapRm04 B ricciOneUp t x i j k :=
    quadOfComp_vec (I := I) (basisAt x) _ i j k
  change (g t).inner x
      (((uhlRm2Vec (I := I) g basisAt Rm04 roughLapRm04 B ricciOneUp t x
        (basisAt x i)) (basisAt x j)) (basisAt x k)) (basisAt x l) = _
  rw [hv]
  unfold uhlRaisedDeriv
  rw [inner_raiseAt]

omit [SigmaCompactSpace M] in
theorem gapDot_uhl
    (g₁ g₂ : Real → SmoothRiemannianMetric I M)
    (basisAt : (y : M) → Module.Basis Idx Real (TangentSpace I y))
    (Rm04₂ roughLapRm04₂ B₂ : FourComp M Idx) (ricciOneUp₂ : MatrixComp M Idx)
    (t : Real) (x : M) :
    gapDot (I := I) (g₁ t) (g₂ t)
        (uhlRm2Vec (I := I) g₂ basisAt Rm04₂ roughLapRm04₂ B₂ ricciOneUp₂ t x) =
      (2 : Real) • lowOfComp (I := I) (g₁ t) (basisAt x)
        (fun i j k l =>
          (metricRicciAt (I := I) (g₁ t) x - metricRicciAt (I := I) (g₂ t) x)
            (fun a : Fin 2 =>
              if a = 0 then
                riemannOp (metricCov (I := I) (g₂ t)) x
                  (basisAt x i) (basisAt x j) (basisAt x k)
              else basisAt x l)) -
      lowOfComp (I := I) (g₁ t) (basisAt x)
        (fun i j k l =>
          metricDiffAt (I := I) (g₁ t) (g₂ t) x
            (fun a : Fin 2 =>
              if a = 0 then
                uhlRaisedDeriv (I := I) g₂ basisAt Rm04₂ roughLapRm04₂ B₂ ricciOneUp₂
                  t x i j k
              else basisAt x l)) := by
  have hRic :
      lowOfComp (I := I) (g₁ t) (basisAt x)
          (fun i j k l =>
            (metricRicciAt (I := I) (g₁ t) x - metricRicciAt (I := I) (g₂ t) x)
              (fun a : Fin 2 =>
                if a = 0 then
                  riemannOp (metricCov (I := I) (g₂ t)) x
                    (basisAt x i) (basisAt x j) (basisAt x k)
                else basisAt x l)) =
        lowerTri (I := I)
          (metricRicciAt (I := I) (g₁ t) x - metricRicciAt (I := I) (g₂ t) x)
          (riemannOp (metricCov (I := I) (g₂ t)) x) :=
    lowerTri_low (I := I) (g₁ t)
      (metricRicciAt (I := I) (g₁ t) x - metricRicciAt (I := I) (g₂ t) x)
      (riemannOp (metricCov (I := I) (g₂ t)) x) (basisAt x)
  have hSpeed :
      lowOfComp (I := I) (g₁ t) (basisAt x)
          (fun i j k l =>
            metricDiffAt (I := I) (g₁ t) (g₂ t) x
              (fun a : Fin 2 =>
                if a = 0 then
                  uhlRaisedDeriv (I := I) g₂ basisAt Rm04₂ roughLapRm04₂ B₂ ricciOneUp₂
                    t x i j k
                else basisAt x l)) =
        lowerTri (I := I) (metricDiffAt (I := I) (g₁ t) (g₂ t) x)
          (uhlRm2Vec (I := I) g₂ basisAt Rm04₂ roughLapRm04₂ B₂ ricciOneUp₂ t x) := by
    apply lowOfComp_ext (I := I)
    intro i j k l
    rw [lowerTri_apply]
    have hv :
        ((uhlRm2Vec (I := I) g₂ basisAt Rm04₂ roughLapRm04₂ B₂ ricciOneUp₂ t x
          (basisAt x i)) (basisAt x j)) (basisAt x k) =
            uhlRaisedDeriv (I := I) g₂ basisAt Rm04₂ roughLapRm04₂ B₂ ricciOneUp₂
              t x i j k :=
      quadOfComp_vec (I := I) (basisAt x) _ i j k
    congr 1
    funext a
    fin_cases a <;> simp [vec4, hv]
  rw [gapDot, ← hRic, ← hSpeed]

end GapRemainder

end DifferentialGeometry.PDE.RicciFlow
