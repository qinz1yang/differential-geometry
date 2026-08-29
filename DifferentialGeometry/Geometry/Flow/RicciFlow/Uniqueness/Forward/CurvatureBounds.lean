import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.CurvatureDifference
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian.Comparison
import DifferentialGeometry.Geometry.Metric.SmoothVectorFieldExtGlobal
import DifferentialGeometry.Tensor.RSTensor.TangentMetric

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [SigmaCompactSpace M] [T2Space M]

section Frame

omit [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] in
private theorem innerSelfNonneg (g : SmoothRiemannianMetric I M) (x : M)
    (v : TangentSpace I x) : 0 ≤ g.inner x v v := by
  rcases eq_or_ne v 0 with hv | hv
  · simp [hv]
  · exact (g.pos x v hv).le

omit [SigmaCompactSpace M] [T2Space M] in
private theorem exists_onFrame (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ b : Module.Basis (Fin (Module.finrank Real (TangentSpace I x))) Real
        (TangentSpace I x),
      ∀ i j, g.inner x (b i) (b j) = if i = j then (1 : Real) else 0 := by
  classical
  let D := (tangentMetricDataGen (I := I) g x).metric
  let _ : InnerProductSpace.Core Real (TangentSpace I x) := D.toCore
  let _ : NormedAddCommGroup (TangentSpace I x) :=
    @InnerProductSpace.Core.toNormedAddCommGroup Real (TangentSpace I x) _ _ _ D.toCore
  let _ : InnerProductSpace Real (TangentSpace I x) :=
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

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] in
private theorem frankEq (x : M) :
    (Module.finrank Real (TangentSpace I x) : Real) = (Module.finrank Real E : Real) := rfl

omit [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] in
private theorem onFrame_inv {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hON : ∀ i j, g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0) :
    MetricInverseInBasisGen (I := I) g x basis (identityInvMetric (Idx := Idx)) := by
  intro i j
  constructor <;> simp [identityInvMetric, diagonalInvMetric, hON]

omit [SigmaCompactSpace M] [T2Space M] in
private theorem metricCS (g : SmoothRiemannianMetric I M) (x : M)
    (u v : TangentSpace I x) :
    |g.inner x u v| ≤ Real.sqrt (g.inner x u u) * Real.sqrt (g.inner x v v) := by
  classical
  obtain ⟨basis, hON⟩ := exists_onFrame (I := I) g x
  set α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x :=
    dualToCotangentGen (I := I) (tangentFlatLinearGen (I := I) g x u) with hα
  have hαnorm : normSq0S (I := I) g x 1 α = g.inner x u u := by
    rw [hα, normSq0S_eq_inner, inner0S_one_eq_cotangent]
    exact cotangentInner_dualToCotangent_tangentFlat_gen (I := I) g x u u
  have hαv : Tensor0SSpace.eval α (fun _ : Fin 1 => v) = g.inner x u v := by
    rw [hα, dualToCotangent_apply_gen, tangentFlatLinear_apply_gen]
  have h := abs_apply_le_sqrt_normSq0S (I := I) g x 1 basis hON α (fun _ : Fin 1 => v)
  change |Tensor0SSpace.eval α (fun _ : Fin 1 => v)| ≤ _ at h
  rw [hαv, hαnorm] at h
  simpa using h

omit [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] in
private theorem onFrame_coord {Idx : Type*} [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hON : ∀ i j, g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (i : Idx) (v : TangentSpace I x) :
    basis.coord i v = g.inner x (basis i) v := by
  classical
  have hlin : basis.coord i = (g.inner x (basis i)).toLinearMap := by
    refine basis.ext fun j => ?_
    rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    change (if j = i then (1 : Real) else 0) = g.inner x (basis i) (basis j)
    rw [hON i j]
    by_cases h : i = j
    · subst h; simp
    · rw [if_neg h, if_neg (fun hh : j = i => h hh.symm)]
  exact congrArg (fun L : (TangentSpace I x) →ₗ[Real] Real => L v) hlin

omit [SigmaCompactSpace M] [T2Space M] in
private theorem absBasis_le {Idx : Type*} [Finite Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) {x : M} {k : ℕ}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hON : ∀ i j, g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) k x)
    (u : Fin k -> TangentSpace I x) (hu : ∀ b, ∃ i, u b = basis i) :
    |T u| ≤ Real.sqrt (normSq0S (I := I) g x k T) := by
  have _ : Fintype Idx := Fintype.ofFinite Idx
  have h := abs_apply_le_sqrt_normSq0S (I := I) g x k basis hON T u
  have hprod : (∏ a : Fin k, Real.sqrt (g.inner x (u a) (u a))) = 1 := by
    refine Finset.prod_eq_one fun a _ => ?_
    obtain ⟨i, hi⟩ := hu a
    rw [hi, hON i i]; simp
  rw [hprod, mul_one] at h
  exact h

omit [SigmaCompactSpace M] [T2Space M] in
private theorem normSqAdd_le {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) {x : M} {k : ℕ}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv : MetricInverseInBasisGen (I := I) g x basis (identityInvMetric (Idx := Idx)))
    (A B : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) k x) :
    normSq0S (I := I) g x k (A + B) ≤
      2 * normSq0S (I := I) g x k A + 2 * normSq0S (I := I) g x k B := by
  classical
  rw [normSq0S_identity_eq_sum_sq (I := I) g x k basis hinv,
    normSq0S_identity_eq_sum_sq (I := I) g x k basis hinv A,
    normSq0S_identity_eq_sum_sq (I := I) g x k basis hinv B,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun φ _ => ?_
  have hsplit : component0S (I := I) basis (A + B) φ =
      component0S (I := I) basis A φ + component0S (I := I) basis B φ := by
    rw [component0S_apply, component0S_apply, component0S_apply]
    exact Tensor0SSpace.add_apply (I := I) k x A B _
  rw [hsplit]
  nlinarith [sq_nonneg (component0S (I := I) basis A φ - component0S (I := I) basis B φ)]

end Frame

section Flux

variable {s : ℕ}

omit [SigmaCompactSpace M] in
theorem lapDiffFlux_eval (g₁ g₂ : SmoothRiemannianMetric I M)
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (x : M) (v : TangentSpace I x) (slots : Fin s -> TangentSpace I x) :
    lapDiffFlux (I := I) g₁ g₂ T x (Fin.cons v slots) =
      -∑ a : Fin s,
        (T x) (Function.update slots a
          (((CovariantDerivative.difference (metricCov (I := I) g₁)
              (metricCov (I := I) g₂) x) (slots a)) v)) := by
  classical
  have _ : IsManifold I (1 + 1) M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by decide : ((1 : WithTop ℕ∞) + 1) ≤ ∞)
  have _ : ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I :=
    TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := 1)
  obtain ⟨Xf, hXsm, hXv⟩ :=
    DifferentialGeometry.Geometry.Riemannian.exists_contMDiff_vectorField_eq (I := I) x v
  choose Vf hVsm hVv using fun a : Fin s =>
    DifferentialGeometry.Geometry.Riemannian.exists_contMDiff_vectorField_eq (I := I) x (slots a)
  set X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    ContMDiffSection.mk Xf hXsm with hX
  set V : Fin s -> ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    fun a => ContMDiffSection.mk (Vf a) (hVsm a) with hV
  have hXx : X x = v := by rw [hX]; simpa using hXv
  have hVx : ∀ a, V a x = slots a := by
    intro a; rw [hV]; simpa using hVv a
  have hslots : (fun a : Fin s => V a x) = slots := by funext a; exact hVx a
  have key := nabla0SFun_sub_cov (I := I) (metricCov (I := I) g₁) (metricCov (I := I) g₂)
    X V T x
  have hsplit :
      ((nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s
            (metricCov (I := I) g₁) X T x) -
          nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s
            (metricCov (I := I) g₂) X T x) (fun a : Fin s => V a x) =
        (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s
            (metricCov (I := I) g₁) X T x) (fun a : Fin s => V a x) -
          (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s
            (metricCov (I := I) g₂) X T x) (fun a : Fin s => V a x) :=
    Tensor0SSpace.sub_apply (I := I) s x _ _ _
  rw [hsplit] at key
  simp only [hXx, hVx] at key
  have hflux :
      lapDiffFlux (I := I) g₁ g₂ T x (Fin.cons (X x) (fun a : Fin s => V a x)) =
        totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s
            (metricCov (I := I) g₁) T x (Fin.cons (X x) (fun a : Fin s => V a x)) -
          totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s
            (metricCov (I := I) g₂) T x (Fin.cons (X x) (fun a : Fin s => V a x)) := by
    rw [lapDiffFlux_apply]
    exact Tensor0SSpace.sub_apply (I := I) (s + 1) x _ _ _
  rw [totalNabla0SFun_apply_section, totalNabla0SFun_apply_section] at hflux
  rw [hXx, hslots] at hflux
  rw [hflux, key]

omit [SigmaCompactSpace M] [T2Space M] in
theorem connectionDifferenceVec_le (g₁ g₂ : SmoothRiemannianMetric I M) (x : M)
    (X Y : TangentSpace I x) :
    Real.sqrt (g₁.inner x
        (CovariantDerivative.difference (metricCov (I := I) g₁) (metricCov (I := I) g₂) x Y X)
        (CovariantDerivative.difference (metricCov (I := I) g₁) (metricCov (I := I) g₂) x Y X))
      ≤ Real.sqrt (connectionDifferenceSq (I := I) g₁ g₂ x) *
          Real.sqrt (g₁.inner x X X) * Real.sqrt (g₁.inner x Y Y) := by
  classical
  set w : TangentSpace I x :=
    CovariantDerivative.difference (metricCov (I := I) g₁) (metricCov (I := I) g₂) x Y X with hw
  obtain ⟨basis, hON⟩ := exists_onFrame (I := I) g₁ x
  set v : Fin 3 -> TangentSpace I x := ![X, Y, w] with hv
  have h0 : v 0 = X := by simp [hv]
  have h1 : v 1 = Y := by simp [hv]
  have h2 : v 2 = w := by simp [hv]
  have hvalEval :
      Tensor0SSpace.eval (connectionDifferenceLowAt (I := I) g₁ g₂ x) v =
        g₁.inner x w w := by
    rw [connectionDifferenceLowAt_apply, h0, h1, h2, ← hw]
  have hval : connectionDifferenceLowAt (I := I) g₁ g₂ x v = g₁.inner x w w :=
    (Tensor0SSpace.eval_eq (connectionDifferenceLowAt (I := I) g₁ g₂ x) v).symm.trans hvalEval
  have habs := abs_apply_le_sqrt_normSq0S (I := I) g₁ x 3 basis hON
    (connectionDifferenceLowAt (I := I) g₁ g₂ x) v
  rw [← connectionDifferenceSq_def] at habs
  have hprod :
      (∏ a : Fin 3, Real.sqrt (g₁.inner x (v a) (v a))) =
        Real.sqrt (g₁.inner x X X) * Real.sqrt (g₁.inner x Y Y) *
          Real.sqrt (g₁.inner x w w) := by
    rw [Fin.prod_univ_three, h0, h1, h2]
  rw [hval, hprod] at habs
  have hwnn : 0 ≤ g₁.inner x w w := innerSelfNonneg (I := I) g₁ x w
  have habs' : g₁.inner x w w ≤
      Real.sqrt (connectionDifferenceSq (I := I) g₁ g₂ x) *
        (Real.sqrt (g₁.inner x X X) * Real.sqrt (g₁.inner x Y Y)) *
        Real.sqrt (g₁.inner x w w) := by
    calc g₁.inner x w w ≤ |g₁.inner x w w| := le_abs_self _
      _ ≤ _ := by
          refine le_trans habs (le_of_eq ?_); ring
  have hsq : Real.sqrt (g₁.inner x w w) ^ 2 = g₁.inner x w w := Real.sq_sqrt hwnn
  have hnn0 : 0 ≤ Real.sqrt (g₁.inner x w w) := Real.sqrt_nonneg _
  have hC : 0 ≤ Real.sqrt (connectionDifferenceSq (I := I) g₁ g₂ x) *
      (Real.sqrt (g₁.inner x X X) * Real.sqrt (g₁.inner x Y Y)) := by positivity
  rcases eq_or_lt_of_le hnn0 with h0 | hpos
  · rw [← h0]
    exact hC.trans_eq (by ring)
  · have := habs'
    rw [← hsq] at this
    nlinarith [this, hpos]

omit [SigmaCompactSpace M] in
theorem fluxNormSq_le (g₁ g₂ : SmoothRiemannianMetric I M)
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (x : M) :
    normSq0S (I := I) g₁ x (s + 1) (lapDiffFlux (I := I) g₁ g₂ T x) ≤
      (s : Real) ^ 2 * (Module.finrank Real E : Real) ^ (s + 1) *
        connectionDifferenceSq (I := I) g₁ g₂ x * normSq0S (I := I) g₁ x s (T x) := by
  classical
  obtain ⟨basis, hON⟩ := exists_onFrame (I := I) g₁ x
  have hinv := onFrame_inv (I := I) g₁ basis hON
  have hbnorm : ∀ i, Real.sqrt (g₁.inner x (basis i) (basis i)) = 1 := by
    intro i; rw [hON i i]; simp
  set NA := Real.sqrt (connectionDifferenceSq (I := I) g₁ g₂ x) with hNA
  set NT := Real.sqrt (normSq0S (I := I) g₁ x s (T x)) with hNT
  have hNAnn : 0 ≤ NA := Real.sqrt_nonneg _
  have hNTnn : 0 ≤ NT := Real.sqrt_nonneg _
  set B : Real := (s : Real) * NA * NT with hB
  have hBnn : 0 ≤ B := by rw [hB]; positivity
  have hcomp : ∀ φ : Fin (s + 1) -> Fin (Module.finrank Real (TangentSpace I x)),
      |component0S (I := I) basis (lapDiffFlux (I := I) g₁ g₂ T x) φ| ≤ B := by
    intro φ
    rw [component0S_apply]
    have hcons : (fun a : Fin (s + 1) => basis (φ a)) =
        Fin.cons (basis (φ 0)) (fun a : Fin s => basis (φ a.succ)) := by
      funext a
      refine Fin.cases ?_ ?_ a
      · rfl
      · intro i; rfl
    rw [hcons, lapDiffFlux_eval, abs_neg]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hterm : ∀ a : Fin s,
        |(T x) (Function.update (fun a' : Fin s => basis (φ a'.succ)) a
            (((CovariantDerivative.difference (metricCov (I := I) g₁)
                (metricCov (I := I) g₂) x) (basis (φ a.succ))) (basis (φ 0))))| ≤ NA * NT := by
      intro a
      set wa : TangentSpace I x :=
        ((CovariantDerivative.difference (metricCov (I := I) g₁)
            (metricCov (I := I) g₂) x) (basis (φ a.succ))) (basis (φ 0)) with hwa
      have hins : Real.sqrt (g₁.inner x wa wa) ≤ NA := by
        have h := connectionDifferenceVec_le (I := I) g₁ g₂ x (basis (φ 0)) (basis (φ a.succ))
        rw [hbnorm (φ 0), hbnorm (φ a.succ), mul_one, mul_one, ← hNA, ← hwa] at h
        exact h
      have hcs := abs_apply_le_sqrt_normSq0S (I := I) g₁ x s basis hON (T x)
        (Function.update (fun a' : Fin s => basis (φ a'.succ)) a wa)
      have hprod :
          (∏ b : Fin s, Real.sqrt (g₁.inner x
              ((Function.update (fun a' : Fin s => basis (φ a'.succ)) a wa) b)
              ((Function.update (fun a' : Fin s => basis (φ a'.succ)) a wa) b)))
            = Real.sqrt (g₁.inner x wa wa) := by
        rw [Finset.prod_eq_single a
          (fun b _ hb => by rw [Function.update_of_ne hb]; exact hbnorm (φ b.succ))
          (fun ha => absurd (Finset.mem_univ a) ha), Function.update_self]
      rw [hprod, ← hNT] at hcs
      calc |(T x) (Function.update (fun a' : Fin s => basis (φ a'.succ)) a wa)|
          ≤ NT * Real.sqrt (g₁.inner x wa wa) := hcs
        _ ≤ NT * NA := mul_le_mul_of_nonneg_left hins hNTnn
        _ = NA * NT := by ring
    calc (∑ a : Fin s,
            |(T x) (Function.update (fun a' : Fin s => basis (φ a'.succ)) a
                (((CovariantDerivative.difference (metricCov (I := I) g₁)
                    (metricCov (I := I) g₂) x) (basis (φ a.succ))) (basis (φ 0))))|)
          ≤ ∑ _a : Fin s, NA * NT := Finset.sum_le_sum (fun a _ => hterm a)
      _ = B := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, hB]
          simp [nsmul_eq_mul]; ring
  have hcard := normSq0S_le_card_of_component_bound (I := I) g₁ x (s + 1) basis hinv
    (lapDiffFlux (I := I) g₁ g₂ T x) B hBnn hcomp
  have hcard_eq :
      (Fintype.card (Fin (s + 1) -> Fin (Module.finrank Real (TangentSpace I x))) : Real)
        = (Module.finrank Real E : Real) ^ (s + 1) := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    push_cast
    rfl
  rw [hcard_eq] at hcard
  refine hcard.trans (le_of_eq ?_)
  rw [hB]
  have hA2 : NA ^ 2 = connectionDifferenceSq (I := I) g₁ g₂ x :=
    Real.sq_sqrt (normSq0S_nonneg (I := I) g₁ x 3 _)
  have hT2 : NT ^ 2 = normSq0S (I := I) g₁ x s (T x) :=
    Real.sq_sqrt (normSq0S_nonneg (I := I) g₁ x s _)
  rw [show ((s : Real) * NA * NT) ^ 2 = (s : Real) ^ 2 * NA ^ 2 * NT ^ 2 by ring, hA2, hT2]
  ring

end Flux

section Trace

variable {s : ℕ}

omit [SigmaCompactSpace M] [T2Space M] in
theorem traceNormSq_le (g : SmoothRiemannianMetric I M) (x : M)
    (V : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (s + 2) x) :
    normSq0S (I := I) g x s (metricTraceFirstTwo0STensor (I := I) g V) ≤
      (Module.finrank Real E : Real) ^ (s + 2) * normSq0S (I := I) g x (s + 2) V := by
  classical
  obtain ⟨basis, hON⟩ := exists_onFrame (I := I) g x
  have hinv := onFrame_inv (I := I) g basis hON
  set NV := Real.sqrt (normSq0S (I := I) g x (s + 2) V) with hNV
  have hNVnn : 0 ≤ NV := Real.sqrt_nonneg _
  set B : Real := (Module.finrank Real E : Real) * NV with hB
  have hBnn : 0 ≤ B := by rw [hB]; positivity
  have hcomp : ∀ φ : Fin s -> Fin (Module.finrank Real (TangentSpace I x)),
      |component0S (I := I) basis (metricTraceFirstTwo0STensor (I := I) g V) φ| ≤ B := by
    intro φ
    rw [component0S_apply, metricTraceFirstTwo0STensor_apply,
      metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g basis
        (identityInvMetric (Idx := Fin (Module.finrank Real (TangentSpace I x)))) hinv]
    have hcollapse :
        metricTrace0S2InBasis (I := I) basis
            (identityInvMetric (Idx := Fin (Module.finrank Real (TangentSpace I x)))) V
            (fun a : Fin s => basis (φ a)) =
          ∑ i, V (metricTraceInput (I := I) (basis i) (basis i)
            (fun a : Fin s => basis (φ a))) := by
      unfold metricTrace0S2InBasis
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_eq_single i]
      · rw [identityInvMetric_apply_self, one_mul]
      · intro k _ hk
        rw [show identityInvMetric
              (Idx := Fin (Module.finrank Real (TangentSpace I x))) i k = 0 from
          diagonalInvMetric_eq_zero_of_ne (Ne.symm hk), zero_mul]
      · intro hni; exact absurd (Finset.mem_univ i) hni
    rw [hcollapse]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hterm : ∀ i, |V (metricTraceInput (I := I) (basis i) (basis i)
        (fun a : Fin s => basis (φ a)))| ≤ NV := by
      intro i
      refine absBasis_le (I := I) g basis hON V _ ?_
      intro b
      refine Fin.cases ?_ ?_ b
      · exact ⟨i, rfl⟩
      · intro c
        refine Fin.cases ?_ ?_ c
        · exact ⟨i, rfl⟩
        · intro d; exact ⟨φ d, rfl⟩
    calc (∑ i, |V (metricTraceInput (I := I) (basis i) (basis i)
              (fun a : Fin s => basis (φ a)))|)
        ≤ ∑ _i : Fin (Module.finrank Real (TangentSpace I x)), NV :=
          Finset.sum_le_sum fun i _ => hterm i
      _ = B := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, hB]
          simp only [nsmul_eq_mul]
          rw [frankEq (I := I) x]
  have hcard := normSq0S_le_card_of_component_bound (I := I) g x s basis hinv
    (metricTraceFirstTwo0STensor (I := I) g V) B hBnn hcomp
  have hcard_eq :
      (Fintype.card (Fin s -> Fin (Module.finrank Real (TangentSpace I x))) : Real)
        = (Module.finrank Real E : Real) ^ s := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    push_cast
    rfl
  rw [hcard_eq] at hcard
  refine hcard.trans (le_of_eq ?_)
  rw [hB]
  have hV2 : NV ^ 2 = normSq0S (I := I) g x (s + 2) V :=
    Real.sq_sqrt (normSq0S_nonneg (I := I) g x (s + 2) _)
  rw [show ((Module.finrank Real E : Real) * NV) ^ 2
      = (Module.finrank Real E : Real) ^ 2 * NV ^ 2 by ring, hV2]
  rw [pow_add]
  ring

end Trace

section InverseMetric

omit [SigmaCompactSpace M] [T2Space M] in
private theorem invDiag_le (g₁ g₂ : SmoothRiemannianMetric I M) {x : M} {Λ : Real}
    (hΛ0 : 0 ≤ Λ) (hΛ : ∀ v : TangentSpace I x, g₁.inner x v v ≤ Λ * g₂.inner x v v)
    {Idx : Type*} [DecidableEq Idx]
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hON : ∀ i j, g₁.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (k : Idx) :
    0 ≤ basisInvMetric (I := I) g₂ x basis k k ∧
      basisInvMetric (I := I) g₂ x basis k k ≤ Λ := by
  classical
  set u : TangentSpace I x :=
    (tangentFlatEquivGen (I := I) g₂ x).symm (basis.coord k) with hu
  have hflat : ∀ w : TangentSpace I x, g₂.inner x u w = basis.coord k w := by
    intro w
    change (tangentFlatEquivGen (I := I) g₂ x u) w = basis.coord k w
    rw [hu, (tangentFlatEquivGen (I := I) g₂ x).apply_symm_apply]
  have hQ : basisInvMetric (I := I) g₂ x basis k k = g₂.inner x u u := by
    simp only [basisInvMetric]
    rw [← hu]
    exact (hflat u).symm
  have hQ1 : basisInvMetric (I := I) g₂ x basis k k = g₁.inner x (basis k) u := by
    simp only [basisInvMetric]
    rw [← hu]
    exact onFrame_coord (I := I) g₁ basis hON k u
  have hnn : 0 ≤ g₂.inner x u u := innerSelfNonneg (I := I) g₂ x u
  refine ⟨by rw [hQ]; exact hnn, ?_⟩
  have hcs : g₁.inner x (basis k) u ≤ Real.sqrt (g₁.inner x u u) := by
    have h := metricCS (I := I) g₁ x (basis k) u
    rw [hON k k] at h
    simpa using le_trans (le_abs_self _) h
  have hle : Real.sqrt (g₁.inner x u u) ≤ Real.sqrt (Λ * g₂.inner x u u) :=
    Real.sqrt_le_sqrt (hΛ u)
  have heq : g₂.inner x u u = g₁.inner x (basis k) u := by rw [← hQ, hQ1]
  have hkey : g₂.inner x u u ≤ Real.sqrt (Λ * g₂.inner x u u) :=
    calc g₂.inner x u u = g₁.inner x (basis k) u := heq
      _ ≤ Real.sqrt (g₁.inner x u u) := hcs
      _ ≤ Real.sqrt (Λ * g₂.inner x u u) := hle
  have hsqrt : Real.sqrt (Λ * g₂.inner x u u) ^ 2 = Λ * g₂.inner x u u :=
    Real.sq_sqrt (mul_nonneg hΛ0 hnn)
  rcases eq_or_lt_of_le hnn with h0 | hpos
  · rw [hQ, ← h0]; exact hΛ0
  · rw [hQ]
    nlinarith [hkey, hsqrt, hpos, Real.sqrt_nonneg (Λ * g₂.inner x u u)]

omit [SigmaCompactSpace M] [T2Space M] in
private theorem invEntry_le (g₁ g₂ : SmoothRiemannianMetric I M) {x : M} {Λ : Real}
    (hΛ0 : 0 ≤ Λ) (hΛ : ∀ v : TangentSpace I x, g₁.inner x v v ≤ Λ * g₂.inner x v v)
    {Idx : Type*} [DecidableEq Idx]
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hON : ∀ i j, g₁.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (i j : Idx) :
    |basisInvMetric (I := I) g₂ x basis i j| ≤ Λ := by
  classical
  set ui : TangentSpace I x :=
    (tangentFlatEquivGen (I := I) g₂ x).symm (basis.coord i) with hui
  set uj : TangentSpace I x :=
    (tangentFlatEquivGen (I := I) g₂ x).symm (basis.coord j) with huj
  have hflat : ∀ (m : Idx) (w : TangentSpace I x),
      g₂.inner x ((tangentFlatEquivGen (I := I) g₂ x).symm (basis.coord m)) w
        = basis.coord m w := by
    intro m w
    change (tangentFlatEquivGen (I := I) g₂ x
      ((tangentFlatEquivGen (I := I) g₂ x).symm (basis.coord m))) w = basis.coord m w
    rw [(tangentFlatEquivGen (I := I) g₂ x).apply_symm_apply]
  have hval : basisInvMetric (I := I) g₂ x basis i j = g₂.inner x uj ui := by
    simp only [basisInvMetric]
    rw [← hui, huj]
    exact (hflat j ui).symm
  have hdi := invDiag_le (I := I) g₁ g₂ hΛ0 hΛ basis hON i
  have hdj := invDiag_le (I := I) g₁ g₂ hΛ0 hΛ basis hON j
  have hQi : basisInvMetric (I := I) g₂ x basis i i = g₂.inner x ui ui := by
    simp only [basisInvMetric]; rw [← hui]; exact (hflat i ui).symm
  have hQj : basisInvMetric (I := I) g₂ x basis j j = g₂.inner x uj uj := by
    simp only [basisInvMetric]; rw [← huj]; exact (hflat j uj).symm
  rw [hQi] at hdi
  rw [hQj] at hdj
  rw [hval]
  calc |g₂.inner x uj ui|
      ≤ Real.sqrt (g₂.inner x uj uj) * Real.sqrt (g₂.inner x ui ui) :=
        metricCS (I := I) g₂ x uj ui
    _ ≤ Real.sqrt Λ * Real.sqrt Λ :=
        mul_le_mul (Real.sqrt_le_sqrt hdj.2) (Real.sqrt_le_sqrt hdi.2)
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = Λ := Real.mul_self_sqrt hΛ0

omit [SigmaCompactSpace M] [T2Space M] in
private theorem invDiff_le (g₁ g₂ : SmoothRiemannianMetric I M) {x : M} {Λ : Real}
    (hΛ0 : 0 ≤ Λ) (hΛ : ∀ v : TangentSpace I x, g₁.inner x v v ≤ Λ * g₂.inner x v v)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hON : ∀ i j, g₁.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (i j : Idx) :
    |(if i = j then (1 : Real) else 0) - basisInvMetric (I := I) g₂ x basis i j| ≤
      (Fintype.card Idx : Real) * Λ * Real.sqrt (metricDiffSq (I := I) g₁ g₂ x) := by
  classical
  have hrow := (basisInvMetric_real (I := I) g₂ x basis i j).1
  have hH : ∀ k : Idx, g₂.inner x (basis k) (basis j)
      = (if k = j then (1 : Real) else 0) -
        metricDiffAt (I := I) g₁ g₂ x ![basis k, basis j] := by
    intro k
    rw [metricDiffAt_apply]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [hON k j]; ring
  have hstep : ∀ k : Idx,
      basisInvMetric (I := I) g₂ x basis i k * g₂.inner x (basis k) (basis j)
        = basisInvMetric (I := I) g₂ x basis i k * (if k = j then (1 : Real) else 0) -
          basisInvMetric (I := I) g₂ x basis i k *
            metricDiffAt (I := I) g₁ g₂ x ![basis k, basis j] := by
    intro k; rw [hH k]; ring
  have h1 : (∑ k : Idx, basisInvMetric (I := I) g₂ x basis i k *
      (if k = j then (1 : Real) else 0)) = basisInvMetric (I := I) g₂ x basis i j := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hk; simp [hk]
    · intro h; exact absurd (Finset.mem_univ j) h
  have h2 : (if i = j then (1 : Real) else 0)
      = basisInvMetric (I := I) g₂ x basis i j -
        ∑ k : Idx, basisInvMetric (I := I) g₂ x basis i k *
          metricDiffAt (I := I) g₁ g₂ x ![basis k, basis j] := by
    rw [← hrow, Finset.sum_congr rfl (fun k _ => hstep k), Finset.sum_sub_distrib, h1]
  rw [h2, show basisInvMetric (I := I) g₂ x basis i j -
        (∑ k : Idx, basisInvMetric (I := I) g₂ x basis i k *
          metricDiffAt (I := I) g₁ g₂ x ![basis k, basis j]) -
        basisInvMetric (I := I) g₂ x basis i j
      = -∑ k : Idx, basisInvMetric (I := I) g₂ x basis i k *
          metricDiffAt (I := I) g₁ g₂ x ![basis k, basis j] by ring, abs_neg]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hterm : ∀ k : Idx,
      |basisInvMetric (I := I) g₂ x basis i k *
        metricDiffAt (I := I) g₁ g₂ x ![basis k, basis j]|
        ≤ Λ * Real.sqrt (metricDiffSq (I := I) g₁ g₂ x) := by
    intro k
    rw [abs_mul]
    have hH2 : |metricDiffAt (I := I) g₁ g₂ x ![basis k, basis j]|
        ≤ Real.sqrt (metricDiffSq (I := I) g₁ g₂ x) := by
      rw [metricDiffSq_def]
      refine absBasis_le (I := I) g₁ basis hON (metricDiffAt (I := I) g₁ g₂ x) _ ?_
      intro b
      refine Fin.cases ?_ ?_ b
      · exact ⟨k, rfl⟩
      · intro c; exact ⟨j, by fin_cases c; rfl⟩
    exact mul_le_mul (invEntry_le (I := I) g₁ g₂ hΛ0 hΛ basis hON i k) hH2
      (abs_nonneg _) hΛ0
  calc (∑ k : Idx, |basisInvMetric (I := I) g₂ x basis i k *
          metricDiffAt (I := I) g₁ g₂ x ![basis k, basis j]|)
      ≤ ∑ _k : Idx, Λ * Real.sqrt (metricDiffSq (I := I) g₁ g₂ x) :=
        Finset.sum_le_sum fun k _ => hterm k
    _ = (Fintype.card Idx : Real) * Λ * Real.sqrt (metricDiffSq (I := I) g₁ g₂ x) := by
        rw [Finset.sum_const, Finset.card_univ]
        simp [nsmul_eq_mul]; ring

omit [SigmaCompactSpace M] [T2Space M] in
theorem traceDiffNormSq_le (g₁ g₂ : SmoothRiemannianMetric I M) (x : M) {s : ℕ} {Λ : Real}
    (hΛ0 : 0 ≤ Λ) (hΛ : ∀ v : TangentSpace I x, g₁.inner x v v ≤ Λ * g₂.inner x v v)
    (W : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (s + 2) x) :
    normSq0S (I := I) g₁ x s
        (metricTraceFirstTwo0STensor (I := I) g₁ W -
          metricTraceFirstTwo0STensor (I := I) g₂ W) ≤
      (Module.finrank Real E : Real) ^ (s + 6) * Λ ^ 2 *
        metricDiffSq (I := I) g₁ g₂ x * normSq0S (I := I) g₁ x (s + 2) W := by
  classical
  obtain ⟨basis, hON⟩ := exists_onFrame (I := I) g₁ x
  have hinv1 := onFrame_inv (I := I) g₁ basis hON
  have hinv2 := basisInvMetric_real (I := I) g₂ x basis
  set nR : Real := (Module.finrank Real E : Real) with hnR
  have hnRnn : 0 ≤ nR := by rw [hnR]; positivity
  set NW := Real.sqrt (normSq0S (I := I) g₁ x (s + 2) W) with hNW
  have hNWnn : 0 ≤ NW := Real.sqrt_nonneg _
  set NH := Real.sqrt (metricDiffSq (I := I) g₁ g₂ x) with hNH
  have hNHnn : 0 ≤ NH := Real.sqrt_nonneg _
  set B : Real := nR ^ 3 * Λ * NH * NW with hB
  have hBnn : 0 ≤ B := by rw [hB]; positivity
  have hcardIdx : (Fintype.card (Fin (Module.finrank Real (TangentSpace I x))) : Real) = nR := by
    rw [Fintype.card_fin, hnR]
    exact frankEq (I := I) x
  have hcomp : ∀ φ : Fin s -> Fin (Module.finrank Real (TangentSpace I x)),
      |component0S (I := I) basis
        (metricTraceFirstTwo0STensor (I := I) g₁ W -
          metricTraceFirstTwo0STensor (I := I) g₂ W) φ| ≤ B := by
    intro φ
    rw [component0S_apply]
    have hval : (metricTraceFirstTwo0STensor (I := I) g₁ W -
          metricTraceFirstTwo0STensor (I := I) g₂ W) (fun a : Fin s => basis (φ a)) =
        ∑ i, ∑ j, ((if i = j then (1 : Real) else 0) -
            basisInvMetric (I := I) g₂ x basis i j) *
          W (metricTraceInput (I := I) (basis i) (basis j)
            (fun a : Fin s => basis (φ a))) := by
      rw [Tensor0SSpace.sub_apply (I := I) s x _ _ _,
        metricTraceFirstTwo0STensor_apply, metricTraceFirstTwo0STensor_apply,
        metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g₁ basis
          (identityInvMetric (Idx := Fin (Module.finrank Real (TangentSpace I x)))) hinv1,
        metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g₂ basis _ hinv2]
      unfold metricTrace0S2InBasis
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hid : identityInvMetric
          (Idx := Fin (Module.finrank Real (TangentSpace I x))) i j
          = if i = j then (1 : Real) else 0 := by
        simp [identityInvMetric, diagonalInvMetric]
      rw [hid]; ring
    rw [hval]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hrow : ∀ i, |∑ j, ((if i = j then (1 : Real) else 0) -
          basisInvMetric (I := I) g₂ x basis i j) *
        W (metricTraceInput (I := I) (basis i) (basis j)
          (fun a : Fin s => basis (φ a)))| ≤ nR * (nR * Λ * NH * NW) := by
      intro i
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      have hterm : ∀ j, |((if i = j then (1 : Real) else 0) -
            basisInvMetric (I := I) g₂ x basis i j) *
          W (metricTraceInput (I := I) (basis i) (basis j)
            (fun a : Fin s => basis (φ a)))| ≤ nR * Λ * NH * NW := by
        intro j
        rw [abs_mul]
        have hW : |W (metricTraceInput (I := I) (basis i) (basis j)
            (fun a : Fin s => basis (φ a)))| ≤ NW := by
          rw [hNW]
          refine absBasis_le (I := I) g₁ basis hON W _ ?_
          intro b
          refine Fin.cases ?_ ?_ b
          · exact ⟨i, rfl⟩
          · intro c
            refine Fin.cases ?_ ?_ c
            · exact ⟨j, rfl⟩
            · intro d; exact ⟨φ d, rfl⟩
        have hQ := invDiff_le (I := I) g₁ g₂ hΛ0 hΛ basis hON i j
        rw [hcardIdx, ← hNH] at hQ
        exact mul_le_mul hQ hW (abs_nonneg _) (by positivity)
      calc (∑ j, |((if i = j then (1 : Real) else 0) -
              basisInvMetric (I := I) g₂ x basis i j) *
            W (metricTraceInput (I := I) (basis i) (basis j)
              (fun a : Fin s => basis (φ a)))|)
          ≤ ∑ _j : Fin (Module.finrank Real (TangentSpace I x)), nR * Λ * NH * NW :=
            Finset.sum_le_sum fun j _ => hterm j
        _ = nR * (nR * Λ * NH * NW) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
            simp only [nsmul_eq_mul]
            rw [frankEq (I := I) x, ← hnR]
    calc (∑ i, |∑ j, ((if i = j then (1 : Real) else 0) -
            basisInvMetric (I := I) g₂ x basis i j) *
          W (metricTraceInput (I := I) (basis i) (basis j)
            (fun a : Fin s => basis (φ a)))|)
        ≤ ∑ _i : Fin (Module.finrank Real (TangentSpace I x)), nR * (nR * Λ * NH * NW) :=
          Finset.sum_le_sum fun i _ => hrow i
      _ = B := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, hB]
          simp only [nsmul_eq_mul]
          rw [frankEq (I := I) x, ← hnR]
          ring
  have hcard := normSq0S_le_card_of_component_bound (I := I) g₁ x s basis hinv1
    (metricTraceFirstTwo0STensor (I := I) g₁ W -
      metricTraceFirstTwo0STensor (I := I) g₂ W) B hBnn hcomp
  have hcard_eq :
      (Fintype.card (Fin s -> Fin (Module.finrank Real (TangentSpace I x))) : Real)
        = nR ^ s := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, hnR]
    push_cast
    rfl
  rw [hcard_eq] at hcard
  refine hcard.trans (le_of_eq ?_)
  have hH2 : NH ^ 2 = metricDiffSq (I := I) g₁ g₂ x := by
    rw [hNH, metricDiffSq_def]
    exact Real.sq_sqrt (normSq0S_nonneg (I := I) g₁ x 2 _)
  have hW2 : NW ^ 2 = normSq0S (I := I) g₁ x (s + 2) W :=
    Real.sq_sqrt (normSq0S_nonneg (I := I) g₁ x (s + 2) _)
  rw [hB, show (nR ^ 3 * Λ * NH * NW) ^ 2 = nR ^ 6 * Λ ^ 2 * NH ^ 2 * NW ^ 2 by ring,
    hH2, hW2, pow_add]
  ring

end InverseMetric

section Remainder

omit [SigmaCompactSpace M] in
theorem remNormSq_le (g₁ g₂ : SmoothRiemannianMetric I M) {s : ℕ}
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (x : M) {Λ B₁ B₂ : Real}
    (hΛ0 : 0 ≤ Λ) (hΛ : ∀ v : TangentSpace I x, g₁.inner x v v ≤ Λ * g₂.inner x v v)
    (hB₁ : normSq0S (I := I) g₁ x (s + 1) (metricNabla0S (I := I) g₂ T x) ≤ B₁)
    (hB₂ : normSq0S (I := I) g₁ x (s + 2)
      (metricNabla0S (I := I) g₂ (metricNabla0S (I := I) g₂ T) x) ≤ B₂) :
    normSq0S (I := I) g₁ x s (lapDiffRem (I := I) g₁ g₂ T x) ≤
      2 * ((s : Real) + 1) ^ 2 * (Module.finrank Real E : Real) ^ (2 * s + 4) *
          connectionDifferenceSq (I := I) g₁ g₂ x * B₁ +
        2 * (Module.finrank Real E : Real) ^ (s + 6) * Λ ^ 2 *
          metricDiffSq (I := I) g₁ g₂ x * B₂ := by
  classical
  obtain ⟨basis, hON⟩ := exists_onFrame (I := I) g₁ x
  have hinv := onFrame_inv (I := I) g₁ basis hON
  set W : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 2) :=
    metricNabla0S (I := I) g₂ (metricNabla0S (I := I) g₂ T) with hW
  set U : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 2) :=
    lapDiffFlux (I := I) g₁ g₂ (metricNabla0S (I := I) g₂ T) with hU
  have hsplit : lapDiffRem (I := I) g₁ g₂ T x =
      metricTraceFirstTwo0STensor (I := I) g₁ (U x) +
        (metricTraceFirstTwo0STensor (I := I) g₁ (W x) -
          metricTraceFirstTwo0STensor (I := I) g₂ (W x)) := rfl
  rw [hsplit]
  refine le_trans (normSqAdd_le (I := I) g₁ basis hinv _ _) ?_
  have hnn : (0 : Real) ≤ (Module.finrank Real E : Real) := by positivity
  have hfirst : normSq0S (I := I) g₁ x s
      (metricTraceFirstTwo0STensor (I := I) g₁ (U x)) ≤
        ((s : Real) + 1) ^ 2 * (Module.finrank Real E : Real) ^ (2 * s + 4) *
          connectionDifferenceSq (I := I) g₁ g₂ x * B₁ := by
    refine le_trans (traceNormSq_le (I := I) g₁ x (U x)) ?_
    have hflux := fluxNormSq_le (I := I) g₁ g₂ (metricNabla0S (I := I) g₂ T) x
    rw [← hU] at hflux
    have hcd : 0 ≤ connectionDifferenceSq (I := I) g₁ g₂ x := by
      rw [connectionDifferenceSq_def]; exact normSq0S_nonneg (I := I) g₁ x 3 _
    have hchain : normSq0S (I := I) g₁ x (s + 2) (U x) ≤
        ((s : Real) + 1) ^ 2 * (Module.finrank Real E : Real) ^ (s + 2) *
          connectionDifferenceSq (I := I) g₁ g₂ x * B₁ := by
      refine le_trans hflux ?_
      have hfac : (0 : Real) ≤ ((s : Real) + 1) ^ 2 *
          (Module.finrank Real E : Real) ^ (s + 2) * connectionDifferenceSq (I := I) g₁ g₂ x := by
        positivity
      have hcast : (((s : ℕ) + 1 : ℕ) : Real) = (s : Real) + 1 := by push_cast; ring
      rw [hcast]
      exact mul_le_mul_of_nonneg_left hB₁ hfac
    refine le_trans (mul_le_mul_of_nonneg_left hchain (by positivity)) (le_of_eq ?_)
    rw [show 2 * s + 4 = (s + 2) + (s + 2) by ring, pow_add]
    ring
  have hsecond : normSq0S (I := I) g₁ x s
      (metricTraceFirstTwo0STensor (I := I) g₁ (W x) -
        metricTraceFirstTwo0STensor (I := I) g₂ (W x)) ≤
        (Module.finrank Real E : Real) ^ (s + 6) * Λ ^ 2 *
          metricDiffSq (I := I) g₁ g₂ x * B₂ := by
    refine le_trans (traceDiffNormSq_le (I := I) g₁ g₂ x hΛ0 hΛ (W x)) ?_
    have hfac : (0 : Real) ≤ (Module.finrank Real E : Real) ^ (s + 6) * Λ ^ 2 *
        metricDiffSq (I := I) g₁ g₂ x := by
      have : 0 ≤ metricDiffSq (I := I) g₁ g₂ x := by
        rw [metricDiffSq_def]; exact normSq0S_nonneg (I := I) g₁ x 2 _
      positivity
    exact mul_le_mul_of_nonneg_left hB₂ hfac
  calc 2 * normSq0S (I := I) g₁ x s (metricTraceFirstTwo0STensor (I := I) g₁ (U x)) +
        2 * normSq0S (I := I) g₁ x s
          (metricTraceFirstTwo0STensor (I := I) g₁ (W x) -
            metricTraceFirstTwo0STensor (I := I) g₂ (W x))
      ≤ 2 * (((s : Real) + 1) ^ 2 * (Module.finrank Real E : Real) ^ (2 * s + 4) *
            connectionDifferenceSq (I := I) g₁ g₂ x * B₁) +
          2 * ((Module.finrank Real E : Real) ^ (s + 6) * Λ ^ 2 *
            metricDiffSq (I := I) g₁ g₂ x * B₂) :=
        add_le_add (by linarith [hfirst]) (by linarith [hsecond])
    _ = _ := by ring

end Remainder

section Curvature

omit [SigmaCompactSpace M] in
theorem rmFluxNormSq_le (g₁ g₂ : SmoothRiemannianMetric I M)
    (Rm2 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (x : M) {B : Real} (hB : normSq0S (I := I) g₁ x 4 (Rm2 x) ≤ B) :
    normSq0S (I := I) g₁ x 5 (rmDiffFlux (I := I) g₁ g₂ Rm2 x) ≤
      16 * (Module.finrank Real E : Real) ^ 5 * connectionDifferenceSq (I := I) g₁ g₂ x * B := by
  have hmain := fluxNormSq_le (I := I) g₁ g₂ (s := 4) Rm2 x
  have hfac : (0 : Real) ≤ (4 : Real) ^ 2 * (Module.finrank Real E : Real) ^ 5 *
      connectionDifferenceSq (I := I) g₁ g₂ x := by
    have := normSq0S_nonneg (I := I) g₁ x 3 (connectionDifferenceLowAt (I := I) g₁ g₂ x)
    rw [connectionDifferenceSq_def]
    positivity
  refine hmain.trans ?_
  have : (16 : Real) = (4 : Real) ^ 2 := by norm_num
  rw [this]
  exact mul_le_mul_of_nonneg_left hB hfac

omit [SigmaCompactSpace M] in
theorem rmRemNormSq_le (g₁ g₂ : SmoothRiemannianMetric I M)
    (Rm2 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (x : M) {Λ B₁ B₂ : Real}
    (hΛ0 : 0 ≤ Λ) (hΛ : ∀ v : TangentSpace I x, g₁.inner x v v ≤ Λ * g₂.inner x v v)
    (hB₁ : normSq0S (I := I) g₁ x 5 (metricNabla0S (I := I) g₂ Rm2 x) ≤ B₁)
    (hB₂ : normSq0S (I := I) g₁ x 6
      (metricNabla0S (I := I) g₂ (metricNabla0S (I := I) g₂ Rm2) x) ≤ B₂) :
    normSq0S (I := I) g₁ x 4 (lapDiffRem (I := I) g₁ g₂ Rm2 x) ≤
      50 * (Module.finrank Real E : Real) ^ 12 * connectionDifferenceSq (I := I) g₁ g₂ x * B₁ +
        2 * (Module.finrank Real E : Real) ^ 10 * Λ ^ 2 *
          metricDiffSq (I := I) g₁ g₂ x * B₂ := by
  have h := remNormSq_le (I := I) g₁ g₂ (s := 4) Rm2 x hΛ0 hΛ hB₁ hB₂
  refine h.trans (le_of_eq ?_)
  norm_num

end Curvature

end DifferentialGeometry.PDE.RicciFlow

end
