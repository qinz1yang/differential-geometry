import DifferentialGeometry.Geometry.Connection.LeviCivita.DifferenceNorm
import DifferentialGeometry.Geometry.Connection.TensorNabla.Tensor0S.MetricConnectionDifference
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.MetricComparison
import DifferentialGeometry.Geometry.Metric.VectorField.SmoothGlobalExtension
import DifferentialGeometry.Geometry.Metric.TensorInner.Tangent.Riemannian

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
  obtain ⟨basis, hON⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis (I := I) g₁ x
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
  have hwnn : 0 ≤ g₁.inner x w w := by
    rcases eq_or_ne w 0 with hw0 | hw0
    · simp [hw0]
    · exact (g₁.pos x w hw0).le
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
  obtain ⟨basis, hON⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis (I := I) g₁ x
  have hinv := metricInverseInBasis_of_orthonormal (I := I) g₁ basis hON
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


end DifferentialGeometry.PDE.RicciFlow
