import DifferentialGeometry.Geometry.Connection.LeviCivita.Curvature.Hamilton
import DifferentialGeometry.Geometry.Curvature.CurvatureRicciContraction
import DifferentialGeometry.Geometry.Operator.WeightedLaplacian

set_option autoImplicit false

noncomputable section

open Bundle Manifold
open scoped Manifold ContDiff BigOperators

namespace DifferentialGeometry.Geometry.Operator

open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]

omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] [I.Boundaryless] in
theorem weightedRoughLaplacian0S_metricRicci_apply_eq_sum_orthonormalBasis
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯) (x : M)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (horth : ∀ i j : Idx,
      g.inner x (basis i) (basis j) = if i = j then 1 else 0)
    (v w : TangentSpace I x) :
    weightedRoughLaplacian0S (I := I) g f
        (metricRicci (I := I) (M := M) g) x (vec2 (I := I) v w) =
      let cov := LeviCivita (I := I) g
      let hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
          (∞ : WithTop ℕ∞) := by
        simpa [cov, LeviCivita] using
          (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
            (I := I) (M := M) g)
      let Ric := metricRicci (I := I) (M := M) g
      let nablaRic :=
        totalNabla0S (I := I) 2 cov Ric
          (totalNabla0S_regularity (I := I) 2 cov hcov Ric)
      let nabla2Ric := totalNabla0SFun (I := I) 3 cov nablaRic x
      (∑ i : Idx, nabla2Ric (vec4 (I := I) (basis i) (basis i) v w)) -
        nablaRic x (vec3 (I := I) (gradFun (I := I) g f x) v w) := by
  classical
  have hinv : MetricInverseInBasis (I := I) g x basis
      (identityInvMetric (Idx := Idx)) :=
    metricInverseInBasis_identity_of_orthonormal (I := I) g basis horth
  rw [weightedRoughLaplacian0S]
  dsimp only
  rw [Tensor0SSpace.sub_apply]
  rw [roughLap0STensor_apply]
  rw [metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g basis
    (identityInvMetric (Idx := Idx)) hinv]
  unfold metricTrace0S2InBasis
  rw [show (∑ i : Idx, ∑ j : Idx,
      identityInvMetric i j *
        totalNabla0SFun (I := I) 3 (LeviCivita (I := I) g)
          (totalNabla0S (I := I) 2 (LeviCivita (I := I) g)
            (metricRicci (I := I) (M := M) g)
            (totalNabla0S_regularity (I := I) 2 (LeviCivita (I := I) g)
              (by
                simpa [LeviCivita] using
                  (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
                    (I := I) (M := M) g))
              (metricRicci (I := I) (M := M) g))) x
          (metricTraceInput (I := I) (basis i) (basis j) (vec2 (I := I) v w))) =
      ∑ i : Idx,
        totalNabla0SFun (I := I) 3 (LeviCivita (I := I) g)
          (totalNabla0S (I := I) 2 (LeviCivita (I := I) g)
            (metricRicci (I := I) (M := M) g)
            (totalNabla0S_regularity (I := I) 2 (LeviCivita (I := I) g)
              (by
                simpa [LeviCivita] using
                  (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
                    (I := I) (M := M) g))
              (metricRicci (I := I) (M := M) g))) x
          (metricTraceInput (I := I) (basis i) (basis i) (vec2 (I := I) v w)) by
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_eq_single i]
    · simp [identityInvMetric, diagonalInvMetric]
    · intro j _ hji
      simp [identityInvMetric, diagonalInvMetric, Ne.symm hji]
    · simp]
  apply congrArg₂ (fun a b : Real => a - b)
  · apply Finset.sum_congr rfl
    intro i _
    apply congrArg _
    funext q
    fin_cases q <;> rfl
  · rw [tensor0S_curry_apply_cons]
    apply congrArg _
    funext q
    fin_cases q <;> rfl

end DifferentialGeometry.Geometry.Operator
