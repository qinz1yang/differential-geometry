import DifferentialGeometry.Geometry.Curvature.Bounds.RicciOperatorNorm
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Scaling

set_option autoImplicit false

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

noncomputable section

open Bundle
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [IsManifold I 1 M] [T2Space M]

local instance surfaceRicciAlgebra_manifoldTwo : IsManifold I 2 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞)
    (by decide : (2 : WithTop ℕ∞) ≤ ∞)

local instance surfaceRicciAlgebra_manifoldThree : IsManifold I 3 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞)
    (by decide : (3 : WithTop ℕ∞) ≤ ∞)

theorem metricRicciAt_eq_half_scalar_smul_metric_of_finrank_two
    (g : SmoothRiemannianMetric I M) (hdim : Module.finrank Real E = 2) (x : M) :
    metricRicciAt (I := I) g x =
      (metricScalarAt (I := I) g x / 2) • metricTensor0S (I := I) g x := by
  classical
  have hdimT : Module.finrank Real (TangentSpace I x) = 2 := hdim
  have hb := exists_orthonormal_basis (I := I) g x
  rw [hdimT] at hb
  obtain ⟨basis, hON⟩ := hb
  let curvature := metricCurvatureSections (I := I) g
  let Rm : Tensor04At (I := I) (M := M) x := metricRm04 (I := I) g x
  let K := Rm (vec4 (basis 1) (basis 0) (basis 0) (basis 1))
  have hLower : Rm04LowersRm13At (I := I) g x
      (metricRm13 (I := I) g x) (metricRm04 (I := I) g x) :=
    rm04LowersRm13At_of_realizes (I := I) g (metricCov (I := I) g)
      (metricRm13 (I := I) g) (metricRm04 (I := I) g)
      curvature.rm13Realizes curvature.rm04Realizes x
  have hTrace := ricci_diag_eq_sum_rm04_diag_of_orthonormal
    (I := I) g basis (metricRicci (I := I) g) (metricRm13 (I := I) g)
      (metricRm04 (I := I) g) curvature.ricciRealizes hLower hON
  have hInput : ∀ X Y Z W : TangentSpace I x,
      Rm (vec4 Y X Z W) = -Rm (vec4 X Y Z W) :=
    rm04InputSkewAt_of_leviCivita_realizes (I := I) g
      (metricRm04 (I := I) g) curvature.rm04Realizes
  have hOutput : ∀ X Y Z W : TangentSpace I x,
      Rm (vec4 X Y Z W) = -Rm (vec4 X Y W Z) :=
    rm04OutputSkewAt_of_leviCivita_realizes (I := I) g
      (metricRm04 (I := I) g) curvature.rm04Realizes
  have hfirstZero : ∀ X Z W : TangentSpace I x, Rm (vec4 X X Z W) = 0 := by
    intro X Z W
    have h := hInput X X Z W
    linarith
  have hlastZero : ∀ X Y Z : TangentSpace I x, Rm (vec4 X Y Z Z) = 0 := by
    intro X Y Z
    have h := hOutput X Y Z Z
    linarith
  have hsectional : Rm (vec4 (basis 0) (basis 1) (basis 1) (basis 0)) = K := by
    have hi := hInput (basis 1) (basis 0) (basis 1) (basis 0)
    have ho := hOutput (basis 1) (basis 0) (basis 1) (basis 0)
    change Rm (vec4 (basis 1) (basis 0) (basis 1) (basis 0)) = -K at ho
    linarith
  have hcomp : ∀ i j : Fin 2,
      metricRicciAt (I := I) g x (vec2 (basis i) (basis j)) =
        K * (if i = j then (1 : Real) else 0) := by
    intro i j
    have h := hTrace i j
    change metricRicciAt (I := I) g x (vec2 (basis i) (basis j)) =
      ∑ a : Fin 2, Rm (vec4 (basis a) (basis i) (basis j) (basis a)) at h
    rw [Fin.sum_univ_two] at h
    fin_cases i <;> fin_cases j <;>
      simpa [hfirstZero, hlastZero, hsectional, K] using h
  have hRic : metricRicciAt (I := I) g x = K • metricTensor0S (I := I) g x := by
    apply ext0S_basis (I := I) basis
    intro slots
    rw [component0S_apply, component0S_apply]
    have hslots : (fun a : Fin 2 => basis (slots a)) =
        vec2 (basis (slots 0)) (basis (slots 1)) := by
      funext a
      fin_cases a <;> rfl
    rw [Tensor0SSpace.smul_apply, metricTensor0S_apply]
    calc
      metricRicciAt (I := I) g x (fun a => basis (slots a)) =
          K * (if slots 0 = slots 1 then (1 : Real) else 0) := by
        rw [hslots]
        exact hcomp (slots 0) (slots 1)
      _ = K * g.inner x (basis (slots 0)) (basis (slots 1)) := by rw [hON]
  have hscalar : metricScalarAt (I := I) g x = 2 * K := by
    rw [metricScalarAt_def, hRic, metricTracePair0SAt_smul,
      metricTracePair0SAt_metric, hdim]
    norm_num
    ring
  calc
    metricRicciAt (I := I) g x = K • metricTensor0S (I := I) g x := hRic
    _ = (metricScalarAt (I := I) g x / 2) • metricTensor0S (I := I) g x := by
      rw [hscalar]
      congr 1
      ring


theorem metricRicciAt_apply_of_finrank_two
    (g : SmoothRiemannianMetric I M) (hdim : Module.finrank Real E = 2)
    (x : M) (v w : TangentSpace I x) :
    metricRicciAt (I := I) g x (vec2 v w) =
      (metricScalarAt (I := I) g x / 2) * g.inner x v w := by
  have h := congrArg (fun T : Tensor02At (I := I) (M := M) x => T (vec2 v w))
    (metricRicciAt_eq_half_scalar_smul_metric_of_finrank_two g hdim x)
  norm_num only [Tensor0SSpace.smul_apply, metricTensor0S_apply, vec2, smul_eq_mul] at h
  exact h

theorem ricciTensor_apply_of_finrank_two [BoundarylessManifold I M]
    (g : SmoothRiemannianMetric I M) (hdim : Module.finrank Real E = 2)
    (x : M) (v w : TangentSpace I x) :
    ricciTensor (I := I) g x v w =
      (metricScalarAt (I := I) g x / 2) * g.inner x v w := by
  rw [← DifferentialGeometry.metricRicciAt_apply_eq_ricciTensor (I := I) g x v w]
  exact metricRicciAt_apply_of_finrank_two g hdim x v w

theorem two_mul_metricRicci_normSq_eq_scalar_sq_of_finrank_two
    (g : SmoothRiemannianMetric I M) (hdim : Module.finrank Real E = 2) (x : M) :
    2 * normSq0S (I := I) g x 2 (metricRicciAt (I := I) g x) =
      metricScalarAt (I := I) g x ^ 2 := by
  have hmetric : normSq0S (I := I) g x 2 (metricTensor0S (I := I) g x) = 2 := by
    change metricTracePair0SAt (I := I) g (metricTensor0S (I := I) g x) = 2
    simpa only [hdim, Nat.cast_ofNat] using metricTracePair0SAt_metric (I := I) g x
  rw [metricRicciAt_eq_half_scalar_smul_metric_of_finrank_two g hdim x,
    normSq0S_smul, hmetric]
  ring

end

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
