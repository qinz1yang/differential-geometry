import DifferentialGeometry.Geometry.Metric.Convergence.Defs

import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivativeAlgebra
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivativeBounds
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivativeComponents
import DifferentialGeometry.Geometry.Curvature.Naturality.OpenSubtype
import DifferentialGeometry.Geometry.Curvature.Bounds.RicciOperatorNorm
import DifferentialGeometry.Geometry.Coordinates.FixedBaseDerivative


open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}

section FixedManifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]

omit [SigmaCompactSpace M] in
theorem metricCovDeriv_zero_restrictOpen_apply
    (g gRef : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    [T2Space U] (x : U)
    (slots : Fin 2 -> TangentSpace I x) :
    metricCovDeriv (I := I) (g.restrictOpen (I := I) U)
        (gRef.restrictOpen (I := I) U) 0 x slots =
      metricCovDeriv (I := I) g gRef 0 (x : M) slots := by
  simp [metricCovDeriv, Tensor0SBundle.metricTensorField]
  rfl

omit [SigmaCompactSpace M] in
theorem metricCovDeriv_restrictOpen_apply
    (h gRef : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    [SigmaCompactSpace U] [T2Space U] :
    ∀ a : Nat, ∀ x : U, ∀ slots : Fin (a + 2) -> TangentSpace I x,
      metricCovDeriv (I := I) (h.restrictOpen (I := I) U)
          (gRef.restrictOpen (I := I) U) a x slots =
        metricCovDeriv (I := I) h gRef a (x : M) slots := by
  let _ := (inferInstance : (SigmaCompactSpace ↥U))
  classical
  intro a
  induction a with
  | zero =>
      intro x slots
      exact metricCovDeriv_zero_restrictOpen_apply (I := I) h gRef U x slots
  | succ a ih =>
      intro x slots
      obtain ⟨X, hX⟩ :=
        ContMDiffSection.exists_eq_at (I := I) (F := E) (V := TangentSpace I)
          (n := (⊤ : ℕ∞)) (x : M) (slots 0)
      let V : Fin (a + 2) ->
          ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
        fun q =>
          (ContMDiffSection.exists_eq_at (I := I) (F := E) (V := TangentSpace I)
            (n := (⊤ : ℕ∞)) (x : M) (slots q.succ)).choose
      have hV : ∀ q : Fin (a + 2), V q (x : M) = slots q.succ := by
        intro q
        exact
          (ContMDiffSection.exists_eq_at (I := I) (F := E) (V := TangentSpace I)
            (n := (⊤ : ℕ∞)) (x : M) (slots q.succ)).choose_spec
      let XU : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : U -> Type _) :=
        restrictOpenTangentSection (I := I) U X
      let VU : Fin (a + 2) ->
          ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : U -> Type _) :=
        fun q => restrictOpenTangentSection (I := I) U (V q)
      let hU : SmoothRiemannianMetric I U := h.restrictOpen (I := I) U
      let refU : SmoothRiemannianMetric I U := gRef.restrictOpen (I := I) U
      have hsmooth :
          metricCovDeriv (I := I) hU refU (a + 1) x
              (Fin.cons (XU x) (fun q : Fin (a + 2) => VU q x)) =
            metricCovDeriv (I := I) h gRef (a + 1) (x : M)
              (Fin.cons (X (x : M)) (fun q : Fin (a + 2) => V q (x : M))) := by
        have hleft :=
          metricCovDeriv_succ_eval_smooth_slots_gen
            (I := I) (M := U) hU refU a XU VU x
        have hright :=
          metricCovDeriv_succ_eval_smooth_slots_gen
            (I := I) (M := M) h gRef a X V (x : M)
        rw [hleft, hright]
        have hderiv :
            mvfderiv (I := I)
                (fun y : U => metricCovDeriv (I := I) hU refU a y
                  (fun q : Fin (a + 2) => VU q y)) x (XU x) =
              mvfderiv (I := I)
                (fun y : M => metricCovDeriv (I := I) h gRef a y
                  (fun q : Fin (a + 2) => V q y)) (x : M) (X (x : M)) := by
          have hscalar :
              (fun y : U => metricCovDeriv (I := I) hU refU a y
                (fun q : Fin (a + 2) => VU q y)) =
                fun y : U => metricCovDeriv (I := I) h gRef a (y : M)
                  (fun q : Fin (a + 2) => V q (y : M)) := by
            funext y
            simpa [hU, refU, VU] using ih y (fun q : Fin (a + 2) => V q (y : M))
          have hf :
              MDifferentiableAt I 𝓘(Real, Real)
                (fun y : M => metricCovDeriv (I := I) h gRef a y
                  (fun q : Fin (a + 2) => V q y)) (x : M) :=
            (Tensor0SBundle.tensor0SField_eval_smooth_slots_contMDiffAt
              (I := I) (metricCovDeriv (I := I) h gRef a) V (x : M)).mdifferentiableAt
              (by simp)
          rw [hscalar]
          simpa [XU] using
            DifferentialGeometry.Geometry.Curvature.mvfderiv_restrictOpen
              (I := I) U
              (fun y : M => metricCovDeriv (I := I) h gRef a y
                (fun q : Fin (a + 2) => V q y)) x (X (x : M)) hf
        have hsum :
            (∑ p : Fin (a + 2),
              metricCovDeriv (I := I) hU refU a x
                (Function.update (fun q : Fin (a + 2) => VU q x) p
                  (((leviCivitaConnectionOfMetric (I := I) refU)
                      (fun y : U => VU p y) x) (XU x)))) =
              ∑ p : Fin (a + 2),
                metricCovDeriv (I := I) h gRef a (x : M)
                  (Function.update (fun q : Fin (a + 2) => V q (x : M)) p
                    (((leviCivitaConnectionOfMetric (I := I) gRef)
                        (fun y : M => V p y) (x : M)) (X (x : M)))) := by
          apply Finset.sum_congr rfl
          intro p _
          set covU : TangentSpace I x :=
            ((leviCivitaConnectionOfMetric (I := I) refU)
              (fun y : U => VU p y) x) (XU x) with hcovU_def
          set covM : TangentSpace I (x : M) :=
            ((leviCivitaConnectionOfMetric (I := I) gRef)
              (fun y : M => V p y) (x : M)) (X (x : M)) with hcovM_def
          have hcov : covU = covM := by
            have hcov' :=
              metricCov_restrictOpen_globalSection (I := I) gRef U (V p) x (X (x : M))
            rw [hcovU_def, hcovM_def]
            have hXU : XU x = X (x : M) :=
              restrictOpenTangentSection_apply (I := I) U X x
            rw [hXU]
            exact hcov'
          have hVU : ∀ q : Fin (a + 2), VU q x = V q (x : M) := by
            intro q
            simp only [VU, restrictOpenTangentSection_apply]
            rfl
          have hslots :
              Function.update (fun q : Fin (a + 2) => VU q x) p covU =
                Function.update (fun q : Fin (a + 2) => V q (x : M)) p covM := by
            funext q
            by_cases hqp : q = p
            · subst q
              simp only [Function.update_self]
              exact hcov
            · rw [Function.update_of_ne hqp, Function.update_of_ne hqp]
              exact hVU q
          calc
            metricCovDeriv (I := I) hU refU a x
                (Function.update (fun q : Fin (a + 2) => VU q x) p covU) =
              metricCovDeriv (I := I) h gRef a (x : M)
                (Function.update (fun q : Fin (a + 2) => VU q x) p covU) := by
                exact ih x _
            _ =
              metricCovDeriv (I := I) h gRef a (x : M)
                (Function.update (fun q : Fin (a + 2) => V q (x : M)) p covM) := by
                exact congrArg (fun s =>
                  metricCovDeriv (I := I) h gRef a (x : M) s) hslots
        rw [hderiv, hsum]
      have hslots :
          slots = Fin.cons (slots 0) (fun q : Fin (a + 2) => slots q.succ) := by
        funext q
        refine Fin.cases ?_ (fun p => ?_) q
        · rw [Fin.cons_zero]
        · rw [Fin.cons_succ]
      rw [hslots]
      have hleftSlots :
          (Fin.cons (XU x) (fun q : Fin (a + 2) => VU q x) :
            Fin (a + 1 + 2) -> TangentSpace I x) =
            (Fin.cons (slots 0) (fun q : Fin (a + 2) => slots q.succ) :
              Fin (a + 1 + 2) -> TangentSpace I x) := by
        funext q
        refine Fin.cases ?_ (fun p => ?_) q
        · rw [Fin.cons_zero, Fin.cons_zero]
          simp [XU, hX]
        · rw [Fin.cons_succ, Fin.cons_succ]
          simp [VU, hV p]
      have hrightSlots :
          (Fin.cons (X (x : M)) (fun q : Fin (a + 2) => V q (x : M)) :
            Fin (a + 1 + 2) -> TangentSpace I (x : M)) =
            (Fin.cons (slots 0) (fun q : Fin (a + 2) => slots q.succ) :
              Fin (a + 1 + 2) -> TangentSpace I (x : M)) := by
        funext q
        refine Fin.cases ?_ (fun p => ?_) q
        · change X (x : M) = slots 0
          exact hX
        · change V p (x : M) = slots p.succ
          exact hV p
      calc
        metricCovDeriv (I := I) (h.restrictOpen (I := I) U)
            (gRef.restrictOpen (I := I) U) (a + 1) x
            (Fin.cons (slots 0) (fun q : Fin (a + 2) => slots q.succ)) =
          metricCovDeriv (I := I) hU refU (a + 1) x
            (Fin.cons (XU x) (fun q : Fin (a + 2) => VU q x)) := by
            change metricCovDeriv (I := I) hU refU (a + 1) x
                (Fin.cons (slots 0) (fun q : Fin (a + 2) => slots q.succ)) =
              metricCovDeriv (I := I) hU refU (a + 1) x
                (Fin.cons (XU x) (fun q : Fin (a + 2) => VU q x))
            rw [← hleftSlots]
        _ =
          metricCovDeriv (I := I) h gRef (a + 1) (x : M)
            (Fin.cons (X (x : M)) (fun q : Fin (a + 2) => V q (x : M))) := hsmooth
        _ =
          metricCovDeriv (I := I) h gRef (a + 1) (x : M)
            (Fin.cons (slots 0) (fun q : Fin (a + 2) => slots q.succ)) := by
            rw [hrightSlots]

omit [SigmaCompactSpace M] in
theorem metricDiffCovDerivAt_restrictOpen_apply
    (gk gInf gRef : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    [SigmaCompactSpace U] [T2Space U] (a : Nat) (x : U) :
      metricDiffCovDerivAt (I := I) a (gk.restrictOpen (I := I) U)
        (gInf.restrictOpen (I := I) U) (gRef.restrictOpen (I := I) U) x =
      metricDiffCovDerivAt (I := I) a gk gInf gRef (x : M) := by
  ext slots
  unfold metricDiffCovDerivAt
  calc
    (metricCovDeriv (I := I) (gk.restrictOpen (I := I) U)
          (gRef.restrictOpen (I := I) U) a x -
        metricCovDeriv (I := I) (gInf.restrictOpen (I := I) U)
          (gRef.restrictOpen (I := I) U) a x) slots =
        metricCovDeriv (I := I) (gk.restrictOpen (I := I) U)
            (gRef.restrictOpen (I := I) U) a x slots -
          metricCovDeriv (I := I) (gInf.restrictOpen (I := I) U)
            (gRef.restrictOpen (I := I) U) a x slots :=
      Tensor0SBundle.Tensor0SSpace.sub_apply (a + 2) x _ _ slots
    _ = metricCovDeriv (I := I) gk gRef a (x : M) slots -
        metricCovDeriv (I := I) gInf gRef a (x : M) slots := by
      rw [metricCovDeriv_restrictOpen_apply, metricCovDeriv_restrictOpen_apply]
    _ = (metricCovDeriv (I := I) gk gRef a (x : M) -
          metricCovDeriv (I := I) gInf gRef a (x : M)) slots :=
      (Tensor0SBundle.Tensor0SSpace.sub_apply (a + 2) (x : M) _ _ slots).symm

omit [CompleteSpace E] [T2Space M] [SigmaCompactSpace M] in
theorem normSq0S_restrictOpen_apply
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    [T2Space U] (s : Nat) (x : U)
    (A : Tensor0SBundle.Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := U) s x) :
    Tensor0SBundle.normSq0S (I := I) (M := U) (g.restrictOpen (I := I) U) x s A =
      Tensor0SBundle.normSq0S (I := I) (M := M) g (x : M) s A := by
  classical
  obtain ⟨basis, hON⟩ :=
    DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis (I := I) (M := M) g (x : M)
  have hONU :
      ∀ i j,
        (g.restrictOpen (I := I) U).inner x (basis i) (basis j) =
          if i = j then (1 : Real) else 0 := by
    intro i j
    exact hON i j
  have hinvU :
      Tensor0SBundle.MetricInverseInBasisGen (I := I) (M := U)
        (g.restrictOpen (I := I) U) x basis
        (Tensor0SBundle.identityInvMetric
          (Idx := Fin (Module.finrank Real (TangentSpace I x)))) := by
    have h' :=
      DifferentialGeometry.Tensor0SBundle.metricInverseInBasis_of_orthonormal
        (I := I) (M := U) (g.restrictOpen (I := I) U) basis hONU
    change Tensor0SBundle.MetricInverseInBasisGen (I := I) (M := U)
      (g.restrictOpen (I := I) U) x basis
        (fun a k => if a = k then (1 : Real) else 0)
    exact h'
  have hinvM :
      Tensor0SBundle.MetricInverseInBasisGen (I := I) (M := M)
        g (x : M) basis
        (Tensor0SBundle.identityInvMetric
          (Idx := Fin (Module.finrank Real (TangentSpace I x)))) := by
    have h' := DifferentialGeometry.Tensor0SBundle.metricInverseInBasis_of_orthonormal (I := I) g basis hON
    change Tensor0SBundle.MetricInverseInBasisGen (I := I) (M := M)
      g (x : M) basis (fun a k => if a = k then (1 : Real) else 0)
    exact h'
  rw [Tensor0SBundle.normSq0S_identity_eq_sum_sq
      (I := I) (M := U) (g.restrictOpen (I := I) U) x s basis hinvU A,
    Tensor0SBundle.normSq0S_identity_eq_sum_sq
      (I := I) (M := M) g (x : M) s basis hinvM A]
  rfl

omit [SigmaCompactSpace M] in
theorem metricDerivNorm_restrictOpen
    (gk gInf gRef : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    [SigmaCompactSpace U] [T2Space U] (a : Nat) (x : U) :
    metricDerivNorm (I := I) a (gk.restrictOpen (I := I) U)
        (gInf.restrictOpen (I := I) U) (gRef.restrictOpen (I := I) U) x =
      metricDerivNorm (I := I) a gk gInf gRef (x : M) := by
  rw [metricDerivNorm]
  rw [metricDerivNorm]
  rw [metricDiffCovDerivAt_restrictOpen_apply]
  apply congrArg Real.sqrt
  exact normSq0S_restrictOpen_apply (I := I) gRef U (a + 2) x _

omit [SigmaCompactSpace M] in
theorem metricDerivNormSupOn_restrictOpen
    (gk gInf gRef : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    [SigmaCompactSpace U] [T2Space U] (K : Set U) (p : Nat) :
    metricDerivNormSupOn (I := I) K p (gk.restrictOpen (I := I) U)
        (gInf.restrictOpen (I := I) U) (gRef.restrictOpen (I := I) U) =
      metricDerivNormSupOn (I := I) (Subtype.val '' K) p gk gInf gRef := by
  unfold metricDerivNormSupOn
  congr 1
  ext r
  simp only [Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · rintro ⟨a, ha, x, hxK, hr⟩
    exact ⟨a, ha, (x : M), ⟨x, hxK, rfl⟩, by
      rw [← metricDerivNorm_restrictOpen (I := I) gk gInf gRef U a x]; exact hr⟩
  · rintro ⟨a, ha, y, ⟨x, hxK, rfl⟩, hr⟩
    exact ⟨a, ha, x, hxK, by
      rw [metricDerivNorm_restrictOpen (I := I) gk gInf gRef U a x]; exact hr⟩

omit [SigmaCompactSpace M] in
theorem covNorm_restrictOpen
    (h gRef : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    [SigmaCompactSpace U] [T2Space U] (a : Nat) (x : U) :
    metricCovDerivNorm (I := I) a (h.restrictOpen (I := I) U)
        (gRef.restrictOpen (I := I) U) x =
      metricCovDerivNorm (I := I) a h gRef (x : M) := by
  have hcov :
      metricCovDeriv (I := I) (h.restrictOpen (I := I) U)
          (gRef.restrictOpen (I := I) U) a x =
        metricCovDeriv (I := I) h gRef a (x : M) := by
    ext slots
    exact metricCovDeriv_restrictOpen_apply (I := I) h gRef U a x slots
  unfold metricCovDerivNorm
  rw [normSq0S_restrictOpen_apply, hcov]

end FixedManifold

end HCGCompactness
end DifferentialGeometry

namespace DifferentialGeometry.PDE.RicciFlow

open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {Idx : Type*} [Fintype Idx]

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem iterCovComp_restrict {r : Nat} (U : TopologicalSpace.Opens E)
    (e : Idx → E) (chr : E → Idx → Idx → Idx → Real)
    (base : E → (Fin r → Idx) → Real)
    (hdiff : ∀ (a : Nat) (x : U) (n : Fin (r + a) → Idx),
      MDifferentiableAt 𝓘(Real, E) 𝓘(Real, Real)
        (fun y : E ↦ iterCovComp (I := 𝓘(Real, E))
          (fun i z ↦
            (tangentSpaceModelContinuousLinearEquiv (I := 𝓘(Real, E)) z).symm (e i))
          chr base a y n) (x : E)) :
    ∀ (a : Nat) (x : U) (n : Fin (r + a) → Idx),
      iterCovComp (I := 𝓘(Real, E)) (M := U)
          (fun i z ↦
            (tangentSpaceModelContinuousLinearEquiv (I := 𝓘(Real, E)) z).symm (e i))
          (fun z ↦ chr (z : E))
          (fun z ↦ base (z : E)) a x n =
        iterCovComp (I := 𝓘(Real, E))
          (fun i z ↦
            (tangentSpaceModelContinuousLinearEquiv (I := 𝓘(Real, E)) z).symm (e i))
          chr base a (x : E) n := by
  classical
  intro a
  induction a with
  | zero =>
      intro x n
      rfl
  | succ a ih =>
      intro x n
      rw [iterCovComp_succ, iterCovComp_succ]
      unfold covDerivStepComp frameExtData
      have hscalar :
          (fun y : U ↦
            iterCovComp (I := 𝓘(Real, E)) (M := U)
              (fun i z ↦
                (tangentSpaceModelContinuousLinearEquiv (I := 𝓘(Real, E)) z).symm (e i))
              (fun z ↦ chr (z : E))
              (fun z ↦ base (z : E)) a y (Fin.tail n)) =
            fun y : U ↦
              iterCovComp (I := 𝓘(Real, E))
                (fun i z ↦
                  (tangentSpaceModelContinuousLinearEquiv (I := 𝓘(Real, E)) z).symm (e i))
                chr base a (y : E) (Fin.tail n) := by
        funext y
        exact ih y (Fin.tail n)
      rw [hscalar]
      rw [mvfderiv_restrictOpen U
        (fun y : E ↦ iterCovComp (I := 𝓘(Real, E))
          (fun i z ↦
            (tangentSpaceModelContinuousLinearEquiv (I := 𝓘(Real, E)) z).symm (e i))
          chr base a y (Fin.tail n))
        x ((tangentSpaceModelContinuousLinearEquiv (I := 𝓘(Real, E)) x).symm (e (n 0)))
        (hdiff a x (Fin.tail n))]
      simp_rw [ih, tangentSpaceModelContinuousLinearEquiv_symm_apply]

end DifferentialGeometry.PDE.RicciFlow
