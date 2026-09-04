import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.AllTimesBounds

import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Algebra
import DifferentialGeometry.Geometry.Connection.Convergence.DifferenceDerivativeBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Uniform.CovariantSumCross
import DifferentialGeometry.Geometry.Connection.LeviCivita.ChristoffelDiffKoszulDeriv2

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor.RicciIdentity

namespace DifferentialGeometry
namespace HCGCompactness

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M]
variable [CompactSpace M] [I.Boundaryless]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem covStepDiff2_opLeibniz
    (g₁ g₂ : SmoothRiemannianMetric I M) (s : ℕ)
    (S : Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s) :
    covStep (I := I) g₂ (s + 2)
        (covStep (I := I) g₂ (s + 1) (diffStep (I := I) g₁ g₂ s S))
      = diffStep (I := I) g₁ g₂ (s + 2)
          (covStep (I := I) g₂ (s + 1) (covStep (I := I) g₂ s S))
        + (covStep (I := I) g₂ (s + 2)
              (covStep (I := I) g₁ (s + 1) (covStep (I := I) g₂ s S))
            - covStep (I := I) g₁ (s + 2)
              (covStep (I := I) g₂ (s + 1) (covStep (I := I) g₂ s S)))
        + (covStep (I := I) g₂ (s + 2)
              (covStep (I := I) g₂ (s + 1) (covStep (I := I) g₁ s S))
            - covStep (I := I) g₂ (s + 2)
              (covStep (I := I) g₁ (s + 1) (covStep (I := I) g₂ s S))) := by
  rw [diffStep_leibniz (I := I) g₁ g₂ s S, covStep_add, covStep_sub,
    diffStep_leibniz (I := I) g₁ g₂ (s + 1) (covStep (I := I) g₂ s S)]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem field1_eq_mcd1
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    [hContMDiffBundle : ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
    (g₁ g₂ : SmoothRiemannianMetric I M) :
    (Tensor0SBundle.totalNabla0S (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
        (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g₂)
        (Tensor0SBundle.metricTensorField (I := I) g₁)
        (DifferentialGeometry.Geometry.Connection.metricField_totalReg (I := I) g₁ g₂))
      = metricCovDeriv (I := I) g₁ g₂ 1 := by
  let _ := hContMDiffBundle
  have : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  have : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by change IsManifold I ∞ M; infer_instance
  apply DFunLike.ext
  intro x
  rw [Tensor0SBundle.totalNabla0S_apply]
  exact (metricCovDerivStep_apply (I := I) g₂ 0
    (Tensor0SBundle.metricTensorField (I := I) g₁) x).symm

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem field2_eq_mcd2
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
    (g₁ g₂ : SmoothRiemannianMetric I M) :
    (Tensor0SBundle.totalNabla0S (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 3
        (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g₂)
        (Tensor0SBundle.totalNabla0S (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
          (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g₂)
          (Tensor0SBundle.metricTensorField (I := I) g₁)
          (DifferentialGeometry.Geometry.Connection.metricField_totalReg (I := I) g₁ g₂))
        (DifferentialGeometry.Integral.Connection.metricField_totalReg2 (I := I) g₁ g₂))
      = metricCovDeriv (I := I) g₁ g₂ 2 := by
  have : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  have : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by change IsManifold I ∞ M; infer_instance
  apply DFunLike.ext
  intro x
  rw [Tensor0SBundle.totalNabla0S_apply, field1_eq_mcd1 (I := I) g₁ g₂]
  exact (metricCovDerivStep_apply (I := I) g₂ 1 (metricCovDeriv (I := I) g₁ g₂ 1) x).symm

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem nabla3_eq_mcd2
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
    (g₁ g₂ : SmoothRiemannianMetric I M)
    (W : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (x : M) (slots : Fin 3 → TangentSpace I x) :
    Tensor0SBundle.nabla0SFun (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 3
        (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g₂) W
        (Tensor0SBundle.totalNabla0S (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
          (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g₂)
          (Tensor0SBundle.metricTensorField (I := I) g₁)
          (DifferentialGeometry.Geometry.Connection.metricField_totalReg (I := I) g₁ g₂)) x slots
      = metricCovDeriv (I := I) g₁ g₂ 2 x (Fin.cons (W x) slots) := by
  rw [field1_eq_mcd1 (I := I) g₁ g₂,
    show metricCovDeriv (I := I) g₁ g₂ 2
        = metricCovDerivStep (I := I) g₂ 1 (metricCovDeriv (I := I) g₁ g₂ 1) from rfl,
    metricCovDerivStep_apply]
  exact (Tensor0SBundle.totalNabla0SFun_apply_section (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
    3 (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g₂) W
    (metricCovDeriv (I := I) g₁ g₂ 1) x slots).symm

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem nabla4_eq_mcd3
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
    (g₁ g₂ : SmoothRiemannianMetric I M)
    (V : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (x : M) (slots : Fin 4 → TangentSpace I x) :
    Tensor0SBundle.nabla0SFun (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 4
        (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g₂) V
        (Tensor0SBundle.totalNabla0S (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 3
          (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g₂)
          (Tensor0SBundle.totalNabla0S (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
            (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g₂)
            (Tensor0SBundle.metricTensorField (I := I) g₁)
            (DifferentialGeometry.Geometry.Connection.metricField_totalReg (I := I) g₁ g₂))
          (DifferentialGeometry.Integral.Connection.metricField_totalReg2 (I := I) g₁ g₂)) x slots
      = metricCovDeriv (I := I) g₁ g₂ 3 x (Fin.cons (V x) slots) := by
  rw [field2_eq_mcd2 (I := I) g₁ g₂,
    show metricCovDeriv (I := I) g₁ g₂ 3
        = metricCovDerivStep (I := I) g₂ 2 (metricCovDeriv (I := I) g₁ g₂ 2) from rfl,
    metricCovDerivStep_apply]
  exact (Tensor0SBundle.totalNabla0SFun_apply_section (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
    4 (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g₂) V
    (metricCovDeriv (I := I) g₁ g₂ 2) x slots).symm

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem nabla2_eq_mcd1
    [hVectorBundle : VectorBundle ℝ E (TangentSpace I : M → Type _)]
    (g₁ g₂ : SmoothRiemannianMetric I M)
    (W : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (x : M) (slots : Fin 2 → TangentSpace I x) :
    Tensor0SBundle.nabla0SFun (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
        (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g₂) W
        (Tensor0SBundle.metricTensorField (I := I) g₁) x slots
      = metricCovDeriv (I := I) g₁ g₂ 1 x (Fin.cons (W x) slots) := by
  let _ := hVectorBundle
  exact (metricCovDeriv_one_apply_section (I := I) g₁ g₂ W x slots).symm

def covDerivConnectionDifference2 (g₂ g₁ : SmoothRiemannianMetric I M)
    (V W X Y : Π b : M, TangentSpace I b) (x : M) : TangentSpace I x :=
  DifferentialGeometry.Geometry.Curvature.covApply
      (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g₂) V
      (fun p => DifferentialGeometry.Geometry.Curvature.covDerivConnectionDifference (I := I) g₂ g₁ W X Y p) x
    - DifferentialGeometry.Geometry.Curvature.covDerivConnectionDifference (I := I) g₂ g₁
        (DifferentialGeometry.Geometry.Curvature.covApply
          (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g₂) V W) X Y x
    - DifferentialGeometry.Geometry.Curvature.covDerivConnectionDifference (I := I) g₂ g₁ W
        (DifferentialGeometry.Geometry.Curvature.covApply
          (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g₂) V X) Y x
    - DifferentialGeometry.Geometry.Curvature.covDerivConnectionDifference (I := I) g₂ g₁ W X
        (DifferentialGeometry.Geometry.Curvature.covApply
          (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g₂) V Y) x

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [CompactSpace M] [I.Boundaryless] in
theorem covDerivConnectionDifference2_eq (g₂ g₁ : SmoothRiemannianMetric I M)
    (V W X Y : Π b : M, TangentSpace I b) (x : M) :
    covDerivConnectionDifference2 (I := I) g₂ g₁ V W X Y x =
      DifferentialGeometry.Geometry.Curvature.covApply
          (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g₂) V
          (fun p => DifferentialGeometry.Geometry.Curvature.covDerivConnectionDifference (I := I) g₂ g₁ W X Y p)
          x
        - DifferentialGeometry.Geometry.Curvature.covDerivConnectionDifference (I := I) g₂ g₁
            (DifferentialGeometry.Geometry.Curvature.covApply
              (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g₂) V W) X Y x
        - DifferentialGeometry.Geometry.Curvature.covDerivConnectionDifference (I := I) g₂ g₁ W
            (DifferentialGeometry.Geometry.Curvature.covApply
              (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g₂) V X) Y x
        - DifferentialGeometry.Geometry.Curvature.covDerivConnectionDifference (I := I) g₂ g₁ W X
            (DifferentialGeometry.Geometry.Curvature.covApply
              (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g₂) V Y) x :=
  rfl

open DifferentialGeometry.Integral.Connection in
omit [NeZero (Module.finrank ℝ E)] [T2Space M] [CompactSpace M] [I.Boundaryless] in
theorem covDerivConnectionDifference_contMDiff
    (g₂ g₁ : SmoothRiemannianMetric I M)
    (W X Y : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _)) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) (∞ : WithTop ℕ∞)
      (T% (fun p => covDerivConnectionDifference (I := I) g₂ g₁
        (fun b => W b) (fun b => X b) (fun b => Y b) p)) := by
  have : CovariantDerivative.ContMDiffCovariantDerivative
      (LeviCivita (I := I) g₂) (∞ : WithTop ℕ∞) :=
    leviCivitaConnectionOfMetric_contMDiffCovariantDerivative (I := I) g₂
  have : CovariantDerivative.ContMDiffCovariantDerivative
      (LeviCivita (I := I) g₁) (∞ : WithTop ℕ∞) :=
    leviCivitaConnectionOfMetric_contMDiffCovariantDerivative (I := I) g₁
  have hcast : ∀ (S : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _)),
      ContMDiff I (I.prod 𝓘(ℝ, E)) ((∞ : WithTop ℕ∞) + 1) (T% (fun b => S b)) := by
    intro S
    rw [show ((∞ : WithTop ℕ∞) + 1) = (∞ : WithTop ℕ∞) from by rw [ENat.coe_top_add_one]]
    exact S.contMDiff
  have hDXY : ContMDiff I (I.prod 𝓘(ℝ, E)) (∞ : WithTop ℕ∞)
      (T% (diffSec (LeviCivita (I := I) g₂) (LeviCivita (I := I) g₁)
        (fun b => X b) (fun b => Y b))) :=
    diffSec_contMDiff (LeviCivita (I := I) g₂) (LeviCivita (I := I) g₁) X.contMDiff (hcast Y)
  have hDXYc : ContMDiff I (I.prod 𝓘(ℝ, E)) ((∞ : WithTop ℕ∞) + 1)
      (T% (diffSec (LeviCivita (I := I) g₂) (LeviCivita (I := I) g₁)
        (fun b => X b) (fun b => Y b))) := by
    rw [show ((∞ : WithTop ℕ∞) + 1) = (∞ : WithTop ℕ∞) from by rw [ENat.coe_top_add_one]]
    exact hDXY
  have hA : ContMDiffOn I (I.prod 𝓘(ℝ, E)) (∞ : WithTop ℕ∞)
      (T% (covApply (LeviCivita (I := I) g₂) (fun b => W b)
        (diffSec (LeviCivita (I := I) g₂) (LeviCivita (I := I) g₁)
          (fun b => X b) (fun b => Y b)))) Set.univ :=
    covApply_contMDiffOn (cov := LeviCivita (I := I) g₂) W.contMDiff hDXYc
  have hWX : ContMDiff I (I.prod 𝓘(ℝ, E)) (∞ : WithTop ℕ∞)
      (T% (covApply (LeviCivita (I := I) g₂) (fun b => W b) (fun b => X b))) :=
    contMDiffOn_univ.mp
      (covApply_contMDiffOn (cov := LeviCivita (I := I) g₂) W.contMDiff (hcast X))
  have hWY : ContMDiff I (I.prod 𝓘(ℝ, E)) (∞ : WithTop ℕ∞)
      (T% (covApply (LeviCivita (I := I) g₂) (fun b => W b) (fun b => Y b))) :=
    contMDiffOn_univ.mp
      (covApply_contMDiffOn (cov := LeviCivita (I := I) g₂) W.contMDiff (hcast Y))
  have hWYc : ContMDiff I (I.prod 𝓘(ℝ, E)) ((∞ : WithTop ℕ∞) + 1)
      (T% (covApply (LeviCivita (I := I) g₂) (fun b => W b) (fun b => Y b))) := by
    rw [show ((∞ : WithTop ℕ∞) + 1) = (∞ : WithTop ℕ∞) from by rw [ENat.coe_top_add_one]]
    exact hWY
  have hB : ContMDiff I (I.prod 𝓘(ℝ, E)) (∞ : WithTop ℕ∞)
      (T% (diffSec (LeviCivita (I := I) g₂) (LeviCivita (I := I) g₁)
        (covApply (LeviCivita (I := I) g₂) (fun b => W b) (fun b => X b)) (fun b => Y b))) :=
    diffSec_contMDiff (LeviCivita (I := I) g₂) (LeviCivita (I := I) g₁) hWX (hcast Y)
  have hC : ContMDiff I (I.prod 𝓘(ℝ, E)) (∞ : WithTop ℕ∞)
      (T% (diffSec (LeviCivita (I := I) g₂) (LeviCivita (I := I) g₁)
        (fun b => X b) (covApply (LeviCivita (I := I) g₂) (fun b => W b) (fun b => Y b)))) :=
    diffSec_contMDiff (LeviCivita (I := I) g₂) (LeviCivita (I := I) g₁) X.contMDiff hWYc
  rw [← contMDiffOn_univ]
  refine ((hA.sub_section hB.contMDiffOn).sub_section hC.contMDiffOn).congr (fun p _hp => ?_)
  rfl

open DifferentialGeometry.Integral.Connection in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
theorem koszul2
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
    (g₁ g₂ : SmoothRiemannianMetric I M)
    (V W X Y Z : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (x : M) :
    2 * g₁.inner x (covDerivConnectionDifference2 (I := I) g₂ g₁
        (fun b => V b) (fun b => W b) (fun b => X b) (fun b => Y b) x) (Z x)
      = metricCovDeriv (I := I) g₁ g₂ 3 x ![V x, W x, X x, Y x, Z x]
        + metricCovDeriv (I := I) g₁ g₂ 3 x ![V x, W x, Y x, X x, Z x]
        - metricCovDeriv (I := I) g₁ g₂ 3 x ![V x, W x, Z x, X x, Y x]
        - 2 * metricCovDeriv (I := I) g₁ g₂ 2 x
            ![V x, W x,
              CovariantDerivative.difference
                (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g₁)
                (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g₂) x (Y x) (X x),
              Z x]
        - 2 * metricCovDeriv (I := I) g₁ g₂ 1 x
            ![W x,
              DifferentialGeometry.Geometry.Curvature.covDerivConnectionDifference (I := I) g₂ g₁
                (fun b => V b) (fun b => X b) (fun b => Y b) x,
              Z x]
        - 2 * metricCovDeriv (I := I) g₁ g₂ 1 x
            ![V x,
              DifferentialGeometry.Geometry.Curvature.covDerivConnectionDifference (I := I) g₂ g₁
                (fun b => W b) (fun b => X b) (fun b => Y b) x,
              Z x] := by
  classical
  have : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  have : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by change IsManifold I ∞ M; infer_instance
  have hcov2 : CovariantDerivative.ContMDiffCovariantDerivative
      (LeviCivita (I := I) g₂) (∞ : WithTop ℕ∞) :=
    leviCivitaConnectionOfMetric_contMDiffCovariantDerivative (I := I) g₂
  have hZcast : ∀ (S : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _)),
      ContMDiff I (I.prod 𝓘(ℝ, E)) ((∞ : WithTop ℕ∞) + 1) (T% (fun b => S b)) := by
    intro S
    rw [show ((∞ : WithTop ℕ∞) + 1) = (∞ : WithTop ℕ∞) from by rw [ENat.coe_top_add_one]]
    exact S.contMDiff
  have hsmW : ContMDiff I (I.prod 𝓘(ℝ, E)) (∞ : WithTop ℕ∞)
      (T% (covApply (LeviCivita (I := I) g₂) (fun b => V b) (fun b => W b))) :=
    contMDiffOn_univ.mp (covApply_contMDiffOn (cov := LeviCivita (I := I) g₂) V.contMDiff (hZcast W))
  have hsmX : ContMDiff I (I.prod 𝓘(ℝ, E)) (∞ : WithTop ℕ∞)
      (T% (covApply (LeviCivita (I := I) g₂) (fun b => V b) (fun b => X b))) :=
    contMDiffOn_univ.mp (covApply_contMDiffOn (cov := LeviCivita (I := I) g₂) V.contMDiff (hZcast X))
  have hsmY : ContMDiff I (I.prod 𝓘(ℝ, E)) (∞ : WithTop ℕ∞)
      (T% (covApply (LeviCivita (I := I) g₂) (fun b => V b) (fun b => Y b))) :=
    contMDiffOn_univ.mp (covApply_contMDiffOn (cov := LeviCivita (I := I) g₂) V.contMDiff (hZcast Y))
  have hsmZ : ContMDiff I (I.prod 𝓘(ℝ, E)) (∞ : WithTop ℕ∞)
      (T% (covApply (LeviCivita (I := I) g₂) (fun b => V b) (fun b => Z b))) :=
    contMDiffOn_univ.mp (covApply_contMDiffOn (cov := LeviCivita (I := I) g₂) V.contMDiff (hZcast Z))
  set DVW : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
    ContMDiffSection.mk (covApply (LeviCivita (I := I) g₂) (fun b => V b) (fun b => W b)) hsmW
    with hDVWdef
  set DVX : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
    ContMDiffSection.mk (covApply (LeviCivita (I := I) g₂) (fun b => V b) (fun b => X b)) hsmX
    with hDVXdef
  set DVY : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
    ContMDiffSection.mk (covApply (LeviCivita (I := I) g₂) (fun b => V b) (fun b => Y b)) hsmY
    with hDVYdef
  set DVZ : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
    ContMDiffSection.mk (covApply (LeviCivita (I := I) g₂) (fun b => V b) (fun b => Z b)) hsmZ
    with hDVZdef
  set Qsec : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
    ContMDiffSection.mk
      (fun p => covDerivConnectionDifference (I := I) g₂ g₁ (fun b => W b) (fun b => X b) (fun b => Y b) p)
      (covDerivConnectionDifference_contMDiff (I := I) g₂ g₁ W X Y) with hQdef
  have hDVWval : DVW x = ((LeviCivita (I := I) g₂) (fun p => W p) x) (V x) := rfl
  have hDVXval : DVX x = ((LeviCivita (I := I) g₂) (fun p => X p) x) (V x) := rfl
  have hDVYval : DVY x = ((LeviCivita (I := I) g₂) (fun p => Y p) x) (V x) := rfl
  have hDVZval : DVZ x = ((LeviCivita (I := I) g₂) (fun p => Z p) x) (V x) := rfl
  have hQxval : Qsec x = covDerivConnectionDifference (I := I) g₂ g₁ W X Y x := rfl
  have hAvec : ((LeviCivita (I := I) g₂)
        (fun p => CovariantDerivative.difference (LeviCivita (I := I) g₁)
          (LeviCivita (I := I) g₂) p (Y p) (X p)) x) (V x)
      = covDerivConnectionDifference (I := I) g₂ g₁ V X Y x
        + CovariantDerivative.difference (LeviCivita (I := I) g₁) (LeviCivita (I := I) g₂) x (Y x)
            (((LeviCivita (I := I) g₂) (fun p => X p) x) (V x))
        + CovariantDerivative.difference (LeviCivita (I := I) g₁) (LeviCivita (I := I) g₂) x
            (((LeviCivita (I := I) g₂) (fun p => Y p) x) (V x)) (X x) := by
    have hcd : covDerivConnectionDifference (I := I) g₂ g₁ V X Y x
        = ((LeviCivita (I := I) g₂)
            (fun p => CovariantDerivative.difference (LeviCivita (I := I) g₁)
              (LeviCivita (I := I) g₂) p (Y p) (X p)) x) (V x)
          - CovariantDerivative.difference (LeviCivita (I := I) g₁) (LeviCivita (I := I) g₂) x (Y x)
              (((LeviCivita (I := I) g₂) (fun p => X p) x) (V x))
          - CovariantDerivative.difference (LeviCivita (I := I) g₁) (LeviCivita (I := I) g₂) x
              (((LeviCivita (I := I) g₂) (fun p => Y p) x) (V x)) (X x) := rfl
    rw [hcd]; abel
  have hmcd1_add3 : ∀ (a b c d e : TangentSpace I x),
      metricCovDeriv (I := I) g₁ g₂ 1 x ![a, b + c + d, e]
        = metricCovDeriv (I := I) g₁ g₂ 1 x ![a, b, e]
          + metricCovDeriv (I := I) g₁ g₂ 1 x ![a, c, e]
          + metricCovDeriv (I := I) g₁ g₂ 1 x ![a, d, e] := by
    intro a b c d e
    have e1 : ∀ v : TangentSpace I x,
        (![a, v, e] : Fin 3 → TangentSpace I x) = Function.update ![a, b, e] 1 v := by
      intro v; funext i; fin_cases i <;> simp
    rw [e1 (b + c + d),
      Tensor0SBundle.Tensor0SSpace.map_update_add (metricCovDeriv (I := I) g₁ g₂ 1 x) ![a, b, e] 1
        (b + c) d,
      Tensor0SBundle.Tensor0SSpace.map_update_add (metricCovDeriv (I := I) g₁ g₂ 1 x) ![a, b, e] 1
        b c, ← e1 b, ← e1 c, ← e1 d]
  have g_sub : ∀ (a b : TangentSpace I x),
      g₁.inner x (a - b) (Z x) = g₁.inner x a (Z x) - g₁.inner x b (Z x) := by
    intro a b; rw [map_sub (g₁.inner x), sub_apply]
  have hcons3 : ∀ (a b c : TangentSpace I x),
      Fin.cons a (![b, c] : Fin 2 → TangentSpace I x) = (![a, b, c] : Fin 3 → TangentSpace I x) := by
    intro a b c; funext i; fin_cases i <;> rfl
  have hcons4 : ∀ (a b c d : TangentSpace I x),
      Fin.cons a (![b, c, d] : Fin 3 → TangentSpace I x)
        = (![a, b, c, d] : Fin 4 → TangentSpace I x) := by
    intro a b c d; funext i; fin_cases i <;> rfl
  have hcons5 : ∀ (a b c d e : TangentSpace I x),
      Fin.cons a (![b, c, d, e] : Fin 4 → TangentSpace I x)
        = (![a, b, c, d, e] : Fin 5 → TangentSpace I x) := by
    intro a b c d e; funext i; fin_cases i <;> rfl
  have hup4_0 : ∀ (v a b c d : TangentSpace I x),
      Function.update (![a, b, c, d] : Fin 4 → TangentSpace I x) 0 v = ![v, b, c, d] := by
    intro v a b c d; funext i; fin_cases i <;> simp
  have hup4_1 : ∀ (v a b c d : TangentSpace I x),
      Function.update (![a, b, c, d] : Fin 4 → TangentSpace I x) 1 v = ![a, v, c, d] := by
    intro v a b c d; funext i; fin_cases i <;> simp
  have hup4_2 : ∀ (v a b c d : TangentSpace I x),
      Function.update (![a, b, c, d] : Fin 4 → TangentSpace I x) 2 v = ![a, b, v, d] := by
    intro v a b c d; funext i; fin_cases i <;> simp
  have hup4_3 : ∀ (v a b c d : TangentSpace I x),
      Function.update (![a, b, c, d] : Fin 4 → TangentSpace I x) 3 v = ![a, b, c, v] := by
    intro v a b c d; funext i; fin_cases i <;> simp
  have hup2_0 : ∀ (v a b : TangentSpace I x),
      Function.update (![a, b] : Fin 2 → TangentSpace I x) 0 v = ![v, b] := by
    intro v a b; funext i; fin_cases i <;> simp
  have hup2_1 : ∀ (v a b : TangentSpace I x),
      Function.update (![a, b] : Fin 2 → TangentSpace I x) 1 v = ![a, v] := by
    intro v a b; funext i; fin_cases i <;> simp
  have e4x : ∀ (a b c d : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _)),
      (fun i : Fin 4 => ((![a, b, c, d] : Fin 4 → ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _)) i) x) = ![a x, b x, c x, d x] := by
    intro a b c d; funext i; fin_cases i <;> rfl
  have e2x : ∀ (a b : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _)),
      (fun i : Fin 2 => ((![a, b] : Fin 2 → ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _)) i) x) = ![a x, b x] := by
    intro a b; funext i; fin_cases i <;> rfl
  have hmaster := connectionDifference_koszul_deriv2 (I := I) g₁ g₂ V W X Y Z x
  have hkW := connectionDifference_koszul_deriv (I := I) g₁ g₂ DVW X Y Z x
  have hkX := connectionDifference_koszul_deriv (I := I) g₁ g₂ W DVX Y Z x
  have hkY := connectionDifference_koszul_deriv (I := I) g₁ g₂ W X DVY Z x
  have hkZ := connectionDifference_koszul_deriv (I := I) g₁ g₂ W X Y DVZ x
  have hLHSfun : (fun p => g₁.inner p (Qsec p) (Z p))
      = (fun p => Tensor0SBundle.metricTensorField (I := I) g₁ p
          (fun c : Fin 2 => (![Qsec, Z] c) p)) := by
    funext p
    rw [Tensor0SBundle.metricTensorField_apply]
    simp [Matrix.cons_val_zero, Matrix.cons_val_one]
  have hQZdiff : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun p => g₁.inner p (Qsec p) (Z p)) x := by
    rw [hLHSfun]
    exact (Tensor0SBundle.tensor0SField_eval_smooth_slots_contMDiffAt (𝕜 := ℝ) (E := E) (H := H)
      (I := I) (M := M) (Tensor0SBundle.metricTensorField (I := I) g₁) ![Qsec, Z] x).mdifferentiableAt
      (by simp)
  have hLeib := metric_leibniz_extDeriv (I := I) g₁ g₂ ![Qsec, Z] V x
  rw [← hLHSfun] at hLeib
  rw [show (fun p : M => 2 * g₁.inner p
        (covDerivConnectionDifference (I := I) g₂ g₁ (fun b => W b) (fun b => X b) (fun b => Y b) p) (Z p))
      = (fun p : M => 2 * g₁.inner p (Qsec p) (Z p)) from rfl,
    mvfderiv_const_mul I (2 : ℝ) hQZdiff] at hmaster
  simp only [smul_apply, smul_eq_mul] at hmaster
  rw [hLeib] at hmaster
  simp only [nabla4_eq_mcd3, nabla3_eq_mcd2, nabla2_eq_mcd1] at hmaster hkW hkX hkY hkZ
  simp only [field2_eq_mcd2] at hmaster
  simp only [field1_eq_mcd1] at hmaster
  simp only [Fin.sum_univ_four, Fin.sum_univ_two, e4x, e2x, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three, hup4_0, hup4_1,
    hup4_2, hup4_3, hup2_0, hup2_1, hcons3, hcons4, hcons5, Tensor0SBundle.metricTensorField_apply,
    hDVWval, hDVXval, hDVYval, hDVZval, hQxval] at hmaster hkW hkX hkY hkZ
  rw [hAvec, hmcd1_add3] at hmaster
  have hcdc2 : covDerivConnectionDifference2 (I := I) g₂ g₁
        (fun b => V b) (fun b => W b) (fun b => X b) (fun b => Y b) x
      = ((LeviCivita (I := I) g₂) (fun p => Qsec p) x) (V x)
        - covDerivConnectionDifference (I := I) g₂ g₁ DVW X Y x
        - covDerivConnectionDifference (I := I) g₂ g₁ W DVX Y x
        - covDerivConnectionDifference (I := I) g₂ g₁ W X DVY x := by
    rw [covDerivConnectionDifference2_eq]; rfl
  rw [hcdc2, g_sub, g_sub, g_sub,
    show covDerivConnectionDifference (I := I) g₂ g₁ (fun b => V b) (fun b => X b) (fun b => Y b) x
      = covDerivConnectionDifference (I := I) g₂ g₁ V X Y x from rfl,
    show covDerivConnectionDifference (I := I) g₂ g₁ (fun b => W b) (fun b => X b) (fun b => Y b) x
      = covDerivConnectionDifference (I := I) g₂ g₁ W X Y x from rfl]
  linarith [hmaster, hkW, hkX, hkY, hkZ]

open DifferentialGeometry.Geometry.Curvature
  (smoothExtensionTangent smoothExtensionTangent_eq smoothExtensionTangent_contMDiff) in
open DifferentialGeometry.Geometry.Connection (leviCivitaConnectionOfMetric) in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
theorem covDConnectionDifference2_g1_le
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
    (g₂ g₁ : SmoothRiemannianMetric I M) (x : M) (v' v w u : TangentSpace I x) :
    Real.sqrt (g₁.inner x
        (covDerivConnectionDifference2 (I := I) g₂ g₁
          (smoothExtensionTangent (I := I) x v') (smoothExtensionTangent (I := I) x v)
          (smoothExtensionTangent (I := I) x w) (smoothExtensionTangent (I := I) x u) x)
        (covDerivConnectionDifference2 (I := I) g₂ g₁
          (smoothExtensionTangent (I := I) x v') (smoothExtensionTangent (I := I) x v)
          (smoothExtensionTangent (I := I) x w) (smoothExtensionTangent (I := I) x u) x)) ≤
      (3 / 2 * Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x 5
            (metricCovDeriv (I := I) g₁ g₂ 3 x))
        + Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x 4 (metricCovDeriv (I := I) g₁ g₂ 2 x))
            * Real.sqrt (Tensor0SBundle.normSqRS (I := I) (g := g₁) (x := x) 1 2
                (Tensor0SBundle.connectionDifferenceTensorAt (I := I)
                  (leviCivitaConnectionOfMetric (I := I) g₁)
                  (leviCivitaConnectionOfMetric (I := I) g₂) x))
        + 2 * Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x 3 (metricCovDeriv (I := I) g₁ g₂ 1 x))
            * (3 / 2 * Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x 4
                  (metricCovDeriv (I := I) g₁ g₂ 2 x))
              + Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x 3 (metricCovDeriv (I := I) g₁ g₂ 1 x))
                  * Real.sqrt (Tensor0SBundle.normSqRS (I := I) (g := g₁) (x := x) 1 2
                      (Tensor0SBundle.connectionDifferenceTensorAt (I := I)
                        (leviCivitaConnectionOfMetric (I := I) g₁)
                        (leviCivitaConnectionOfMetric (I := I) g₂) x)))) *
        Real.sqrt (g₁.inner x v' v') * Real.sqrt (g₁.inner x v v) *
          Real.sqrt (g₁.inner x w w) * Real.sqrt (g₁.inner x u u) := by
  classical
  have : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  have : IsManifold I (1 + 1) M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide : ((1 : WithTop ℕ∞) + 1) ≤ ∞)
  obtain ⟨basis, hON⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis (I := I) g₁ x
  set NA : ℝ := Real.sqrt (Tensor0SBundle.normSqRS (I := I) (g := g₁) (x := x) 1 2
    (Tensor0SBundle.connectionDifferenceTensorAt (I := I)
      (leviCivitaConnectionOfMetric (I := I) g₁)
      (leviCivitaConnectionOfMetric (I := I) g₂) x)) with hNAdef
  set M1 : ℝ := Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x 3
    (metricCovDeriv (I := I) g₁ g₂ 1 x)) with hM1def
  set M2 : ℝ := Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x 4
    (metricCovDeriv (I := I) g₁ g₂ 2 x)) with hM2def
  set M3 : ℝ := Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x 5
    (metricCovDeriv (I := I) g₁ g₂ 3 x)) with hM3def
  set B2 : TangentSpace I x :=
    covDerivConnectionDifference2 (I := I) g₂ g₁
      (smoothExtensionTangent (I := I) x v') (smoothExtensionTangent (I := I) x v)
      (smoothExtensionTangent (I := I) x w) (smoothExtensionTangent (I := I) x u) x with hB2def
  set Vsec : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
    ContMDiffSection.mk (smoothExtensionTangent (I := I) x v')
      (smoothExtensionTangent_contMDiff (I := I) x v') with hVsec
  set Wsec : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
    ContMDiffSection.mk (smoothExtensionTangent (I := I) x v)
      (smoothExtensionTangent_contMDiff (I := I) x v) with hWsec
  set Xsec : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
    ContMDiffSection.mk (smoothExtensionTangent (I := I) x w)
      (smoothExtensionTangent_contMDiff (I := I) x w) with hXsec
  set Ysec : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
    ContMDiffSection.mk (smoothExtensionTangent (I := I) x u)
      (smoothExtensionTangent_contMDiff (I := I) x u) with hYsec
  set Zsec : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
    ContMDiffSection.mk (smoothExtensionTangent (I := I) x B2)
      (smoothExtensionTangent_contMDiff (I := I) x B2) with hZsec
  have hVx : Vsec x = v' := smoothExtensionTangent_eq (I := I) x v'
  have hWx : Wsec x = v := smoothExtensionTangent_eq (I := I) x v
  have hXx : Xsec x = w := smoothExtensionTangent_eq (I := I) x w
  have hYx : Ysec x = u := smoothExtensionTangent_eq (I := I) x u
  have hZx : Zsec x = B2 := smoothExtensionTangent_eq (I := I) x B2
  have hAbr2 : covDerivConnectionDifference2 (I := I) g₂ g₁
      (fun b => Vsec b) (fun b => Wsec b) (fun b => Xsec b) (fun b => Ysec b) x = B2 := by
    rw [hB2def]; rfl
  have hkos := koszul2 (I := I) g₁ g₂ Vsec Wsec Xsec Ysec Zsec x
  rw [hAbr2, hVx, hWx, hXx, hYx, hZx] at hkos
  set D5 : TangentSpace I x :=
    DifferentialGeometry.Geometry.Curvature.covDerivConnectionDifference (I := I) g₂ g₁
      (fun b => Vsec b) (fun b => Xsec b) (fun b => Ysec b) x with hD5def
  set D6 : TangentSpace I x :=
    DifferentialGeometry.Geometry.Curvature.covDerivConnectionDifference (I := I) g₂ g₁
      (fun b => Wsec b) (fun b => Xsec b) (fun b => Ysec b) x with hD6def
  set Avec : TangentSpace I x :=
    CovariantDerivative.difference
      (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g₁)
      (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g₂) x u w with hAvec
  clear_value B2 D5 D6 Avec
  have hcs5 : ∀ a b c d e : TangentSpace I x,
      |metricCovDeriv (I := I) g₁ g₂ 3 x ![a, b, c, d, e]| ≤
        M3 * (Real.sqrt (g₁.inner x a a) * Real.sqrt (g₁.inner x b b) *
          Real.sqrt (g₁.inner x c c) * Real.sqrt (g₁.inner x d d) * Real.sqrt (g₁.inner x e e)) := by
    intro a b c d e
    have h := Tensor0SBundle.abs_apply_le_sqrt_normSq0S (I := I) g₁ x 5 basis hON
      (metricCovDeriv (I := I) g₁ g₂ 3 x) ![a, b, c, d, e]
    rw [hM3def]
    refine le_trans h (le_of_eq ?_)
    congr 1
    change (∏ i : Fin 5, Real.sqrt (g₁.inner x (![a, b, c, d, e] i) (![a, b, c, d, e] i))) = _
    simp [Fin.prod_univ_five]
  have hcs4 : ∀ a b c d : TangentSpace I x,
      |metricCovDeriv (I := I) g₁ g₂ 2 x ![a, b, c, d]| ≤
        M2 * (Real.sqrt (g₁.inner x a a) * Real.sqrt (g₁.inner x b b) *
          Real.sqrt (g₁.inner x c c) * Real.sqrt (g₁.inner x d d)) := by
    intro a b c d
    have h := Tensor0SBundle.abs_apply_le_sqrt_normSq0S (I := I) g₁ x 4 basis hON
      (metricCovDeriv (I := I) g₁ g₂ 2 x) ![a, b, c, d]
    rw [hM2def]
    refine le_trans h (le_of_eq ?_)
    congr 1
    change (∏ i : Fin 4, Real.sqrt (g₁.inner x (![a, b, c, d] i) (![a, b, c, d] i))) = _
    simp [Fin.prod_univ_four]
  have hcs3 : ∀ a b c : TangentSpace I x,
      |metricCovDeriv (I := I) g₁ g₂ 1 x ![a, b, c]| ≤
        M1 * (Real.sqrt (g₁.inner x a a) * Real.sqrt (g₁.inner x b b) *
          Real.sqrt (g₁.inner x c c)) := by
    intro a b c
    have h := Tensor0SBundle.abs_apply_le_sqrt_normSq0S (I := I) g₁ x 3 basis hON
      (metricCovDeriv (I := I) g₁ g₂ 1 x) ![a, b, c]
    rw [hM1def]
    refine le_trans h (le_of_eq ?_)
    congr 1
    change (∏ i : Fin 3, Real.sqrt (g₁.inner x (![a, b, c] i) (![a, b, c] i))) = _
    simp [Fin.prod_univ_three]
  have hSA : Real.sqrt (g₁.inner x Avec Avec) ≤
      NA * Real.sqrt (g₁.inner x w w) * Real.sqrt (g₁.inner x u u) := by
    rw [hAvec, hNAdef]
    exact Tensor0SBundle.connectionDifferenceVec_norm_le (I := I) g₁
      (leviCivitaConnectionOfMetric (I := I) g₁)
      (leviCivitaConnectionOfMetric (I := I) g₂) w u
  have hSD5 : Real.sqrt (g₁.inner x D5 D5) ≤
      (3 / 2 * M2 + M1 * NA) *
        Real.sqrt (g₁.inner x v' v') * Real.sqrt (g₁.inner x w w) * Real.sqrt (g₁.inner x u u) := by
    rw [hD5def, hM2def, hM1def, hNAdef]
    exact DifferentialGeometry.Geometry.Curvature.covDerivConnectionDifference_g1_le (I := I) g₂ g₁ x v' w u
  have hSD6 : Real.sqrt (g₁.inner x D6 D6) ≤
      (3 / 2 * M2 + M1 * NA) *
        Real.sqrt (g₁.inner x v v) * Real.sqrt (g₁.inner x w w) * Real.sqrt (g₁.inner x u u) := by
    rw [hD6def, hM2def, hM1def, hNAdef]
    exact DifferentialGeometry.Geometry.Curvature.covDerivConnectionDifference_g1_le (I := I) g₂ g₁ x v w u
  have hBB_nn : 0 ≤ g₁.inner x B2 B2 := metric_inner_self_nonneg (I := I) (M := M) g₁ x B2
  have hBBsq : g₁.inner x B2 B2 = Real.sqrt (g₁.inner x B2 B2) ^ 2 := (Real.sq_sqrt hBB_nn).symm
  rw [hBBsq] at hkos
  have hM1nn : (0:ℝ) ≤ M1 := hM1def ▸ Real.sqrt_nonneg _
  have hM2nn : (0:ℝ) ≤ M2 := hM2def ▸ Real.sqrt_nonneg _
  have hM3nn : (0:ℝ) ≤ M3 := hM3def ▸ Real.sqrt_nonneg _
  have hNAnn : (0:ℝ) ≤ NA := hNAdef ▸ Real.sqrt_nonneg _
  have hSBnn : (0:ℝ) ≤ Real.sqrt (g₁.inner x B2 B2) := Real.sqrt_nonneg _
  have hT1 := hcs5 v' v w u B2
  have hT2 := hcs5 v' v u w B2
  have hT3 := hcs5 v' v B2 w u
  have hTA : |metricCovDeriv (I := I) g₁ g₂ 2 x ![v', v, Avec, B2]| ≤
      M2 * NA * (Real.sqrt (g₁.inner x v' v') * Real.sqrt (g₁.inner x v v) *
        Real.sqrt (g₁.inner x w w) * Real.sqrt (g₁.inner x u u) *
          Real.sqrt (g₁.inner x B2 B2)) := by
    refine le_trans (hcs4 v' v Avec B2) ?_
    have hpre : (0:ℝ) ≤ M2 * Real.sqrt (g₁.inner x v' v') * Real.sqrt (g₁.inner x v v) *
        Real.sqrt (g₁.inner x B2 B2) :=
      mul_nonneg (mul_nonneg (mul_nonneg hM2nn (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
        (Real.sqrt_nonneg _)
    linarith [mul_le_mul_of_nonneg_left hSA hpre, hM2nn, hNAnn,
      Real.sqrt_nonneg (g₁.inner x Avec Avec), Real.sqrt_nonneg (g₁.inner x v' v'),
      Real.sqrt_nonneg (g₁.inner x v v), Real.sqrt_nonneg (g₁.inner x w w),
      Real.sqrt_nonneg (g₁.inner x u u), Real.sqrt_nonneg (g₁.inner x B2 B2)]
  have hTD5 : |metricCovDeriv (I := I) g₁ g₂ 1 x ![v, D5, B2]| ≤
      M1 * (3 / 2 * M2 + M1 * NA) * (Real.sqrt (g₁.inner x v' v') * Real.sqrt (g₁.inner x v v) *
        Real.sqrt (g₁.inner x w w) * Real.sqrt (g₁.inner x u u) *
          Real.sqrt (g₁.inner x B2 B2)) := by
    refine le_trans (hcs3 v D5 B2) ?_
    have hpre : (0:ℝ) ≤ M1 * Real.sqrt (g₁.inner x v v) * Real.sqrt (g₁.inner x B2 B2) :=
      mul_nonneg (mul_nonneg hM1nn (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
    linarith [mul_le_mul_of_nonneg_left hSD5 hpre, hM1nn, hM2nn, hNAnn,
      Real.sqrt_nonneg (g₁.inner x D5 D5), Real.sqrt_nonneg (g₁.inner x v' v'),
      Real.sqrt_nonneg (g₁.inner x v v), Real.sqrt_nonneg (g₁.inner x w w),
      Real.sqrt_nonneg (g₁.inner x u u), Real.sqrt_nonneg (g₁.inner x B2 B2)]
  have hTD6 : |metricCovDeriv (I := I) g₁ g₂ 1 x ![v', D6, B2]| ≤
      M1 * (3 / 2 * M2 + M1 * NA) * (Real.sqrt (g₁.inner x v' v') * Real.sqrt (g₁.inner x v v) *
        Real.sqrt (g₁.inner x w w) * Real.sqrt (g₁.inner x u u) *
          Real.sqrt (g₁.inner x B2 B2)) := by
    refine le_trans (hcs3 v' D6 B2) ?_
    have hpre : (0:ℝ) ≤ M1 * Real.sqrt (g₁.inner x v' v') * Real.sqrt (g₁.inner x B2 B2) :=
      mul_nonneg (mul_nonneg hM1nn (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
    linarith [mul_le_mul_of_nonneg_left hSD6 hpre, hM1nn, hM2nn, hNAnn,
      Real.sqrt_nonneg (g₁.inner x D6 D6), Real.sqrt_nonneg (g₁.inner x v' v'),
      Real.sqrt_nonneg (g₁.inner x v v), Real.sqrt_nonneg (g₁.inner x w w),
      Real.sqrt_nonneg (g₁.inner x u u), Real.sqrt_nonneg (g₁.inner x B2 B2)]
  have habs1 := le_abs_self (metricCovDeriv (I := I) g₁ g₂ 3 x ![v', v, w, u, B2])
  have habs2 := le_abs_self (metricCovDeriv (I := I) g₁ g₂ 3 x ![v', v, u, w, B2])
  have habs3 := neg_le_abs (metricCovDeriv (I := I) g₁ g₂ 3 x ![v', v, B2, w, u])
  have habsA := neg_le_abs (metricCovDeriv (I := I) g₁ g₂ 2 x ![v', v, Avec, B2])
  have habsD5 := neg_le_abs (metricCovDeriv (I := I) g₁ g₂ 1 x ![v, D5, B2])
  have habsD6 := neg_le_abs (metricCovDeriv (I := I) g₁ g₂ 1 x ![v', D6, B2])
  rcases eq_or_lt_of_le hSBnn with hSB0 | hSBpos
  · rw [← hSB0]
    have hcoef : (0:ℝ) ≤ 3 / 2 * M3 + M2 * NA + 2 * M1 * (3 / 2 * M2 + M1 * NA) := by
      have hca : (0:ℝ) ≤ 3 / 2 * M2 + M1 * NA := by linarith [hM2nn, mul_nonneg hM1nn hNAnn]
      linarith [hM3nn, mul_nonneg hM2nn hNAnn, mul_nonneg hM1nn hca]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hcoef (Real.sqrt_nonneg _))
      (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  · have hmul : Real.sqrt (g₁.inner x B2 B2) * (2 * Real.sqrt (g₁.inner x B2 B2)) ≤
        Real.sqrt (g₁.inner x B2 B2) *
          ((3 * M3 + 2 * (M2 * NA) + 4 * (M1 * (3 / 2 * M2 + M1 * NA))) *
            (Real.sqrt (g₁.inner x v' v') * Real.sqrt (g₁.inner x v v) *
              Real.sqrt (g₁.inner x w w) * Real.sqrt (g₁.inner x u u))) := by
      linarith [hkos, hT1, hT2, hT3, hTA, hTD5, hTD6,
        habs1, habs2, habs3, habsA, habsD5, habsD6,
        Real.sqrt_nonneg (g₁.inner x B2 B2), Real.sqrt_nonneg (g₁.inner x v' v'),
        Real.sqrt_nonneg (g₁.inner x v v), Real.sqrt_nonneg (g₁.inner x w w),
        Real.sqrt_nonneg (g₁.inner x u u), hM1nn, hM2nn, hM3nn, hNAnn]
    have hdiv := le_of_mul_le_mul_left hmul hSBpos
    linarith [hdiv]

open DifferentialGeometry.Integral.Connection in
noncomputable def mixedCommC (s : ℕ) (Λ Λ' Λ'' Λ''' : ℝ) : ℝ :=
  max 0 (Real.sqrt ((Module.finrank ℝ E : ℝ) ^ (s + 3)) *
    ((s : ℝ) *
        (3 / 2 * Λ ^ 5 * Λ''' + 9 / 2 * Λ ^ 6 * Λ' * Λ'' + 3 * Λ ^ 7 * Λ' ^ 3) +
      (3 * (s : ℝ) + 1) * (3 / 2 * Λ ^ 4 * (Λ'' + Λ * Λ' ^ 2)) +
      (2 * (s : ℝ) + 1) * (3 / 2 * Λ ^ 3 * Λ')))

open DifferentialGeometry.Integral.Connection in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
theorem covDConnectionDifference2_gJet_le
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
    {K : Set M} {g₂ g₁ : SmoothRiemannianMetric I M} {Λ Λ' Λ'' Λ''' : ℝ}
    (hEq : MetricUniformEquivalentOn (I := I) K g₂ g₁ Λ)
    (hJet1 : MetricCovDerivOrderBoundOn (I := I) K 1 g₁ g₂ Λ')
    (hJet2 : MetricCovDerivOrderBoundOn (I := I) K 2 g₁ g₂ Λ'')
    (hJet3 : MetricCovDerivOrderBoundOn (I := I) K 3 g₁ g₂ Λ''')
    {x : M} (hx : x ∈ K) (v' v w u : TangentSpace I x) :
    Real.sqrt (g₂.inner x
        (covDerivConnectionDifference2 (I := I) g₂ g₁
          (smoothExtensionTangent (I := I) x v') (smoothExtensionTangent (I := I) x v)
          (smoothExtensionTangent (I := I) x w) (smoothExtensionTangent (I := I) x u) x)
        (covDerivConnectionDifference2 (I := I) g₂ g₁
          (smoothExtensionTangent (I := I) x v') (smoothExtensionTangent (I := I) x v)
          (smoothExtensionTangent (I := I) x w) (smoothExtensionTangent (I := I) x u) x)) ≤
      (3 / 2 * Λ ^ 5 * Λ''' + 9 / 2 * Λ ^ 6 * Λ' * Λ'' + 3 * Λ ^ 7 * Λ' ^ 3) *
        Real.sqrt (g₂.inner x v' v') * Real.sqrt (g₂.inner x v v) *
          Real.sqrt (g₂.inner x w w) * Real.sqrt (g₂.inner x u u) := by
  classical
  have hL1 : (1 : ℝ) ≤ Λ := hEq.1
  have hL0 : (0 : ℝ) < Λ := lt_of_lt_of_le zero_lt_one hL1
  have hLnn : (0 : ℝ) ≤ Λ := le_of_lt hL0
  have hJ1 : metricCovDerivNorm (I := I) 1 g₁ g₂ x ≤ Λ' := hJet1 x hx
  have hJ2 : metricCovDerivNorm (I := I) 2 g₁ g₂ x ≤ Λ'' := hJet2 x hx
  have hJ3 : metricCovDerivNorm (I := I) 3 g₁ g₂ x ≤ Λ''' := hJet3 x hx
  have hL'nn : (0 : ℝ) ≤ Λ' := le_trans (Real.sqrt_nonneg _) hJ1
  have hL''nn : (0 : ℝ) ≤ Λ'' := le_trans (Real.sqrt_nonneg _) hJ2
  have hL'''nn : (0 : ℝ) ≤ Λ''' := le_trans (Real.sqrt_nonneg _) hJ3
  have hs2 : Real.sqrt Λ ^ 2 = Λ := Real.sq_sqrt hLnn
  have hs3 : Real.sqrt (Λ ^ 3) = Λ * Real.sqrt Λ := by
    rw [show Λ ^ 3 = Λ ^ 2 * Λ by ring, Real.sqrt_mul (by positivity), Real.sqrt_sq hLnn]
  have hs4 : Real.sqrt (Λ ^ 4) = Λ ^ 2 := by
    rw [show Λ ^ 4 = (Λ ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have hs5 : Real.sqrt (Λ ^ 5) = Λ ^ 2 * Real.sqrt Λ := by
    rw [show Λ ^ 5 = (Λ ^ 2) ^ 2 * Λ by ring, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by positivity)]
  have hcore := covDConnectionDifference2_g1_le (I := I) g₂ g₁ x v' v w u
  have hM3 : Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x 5
      (metricCovDeriv (I := I) g₁ g₂ 3 x)) ≤ Λ ^ 2 * Real.sqrt Λ * Λ''' := by
    have hcomp := DifferentialGeometry.Geometry.Curvature.sqrt_normSq0S_comp (I := I) hEq hx 5
      (metricCovDeriv (I := I) g₁ g₂ 3 x)
    rw [hs5] at hcomp
    refine le_trans hcomp ?_
    exact mul_le_mul_of_nonneg_left (show Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₂ x 5
        (metricCovDeriv (I := I) g₁ g₂ 3 x)) ≤ Λ''' from hJ3)
      (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
  have hM2 : Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x 4
      (metricCovDeriv (I := I) g₁ g₂ 2 x)) ≤ Λ ^ 2 * Λ'' := by
    have hcomp := DifferentialGeometry.Geometry.Curvature.sqrt_normSq0S_comp (I := I) hEq hx 4
      (metricCovDeriv (I := I) g₁ g₂ 2 x)
    rw [hs4] at hcomp
    refine le_trans hcomp ?_
    exact mul_le_mul_of_nonneg_left (show Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₂ x 4
        (metricCovDeriv (I := I) g₁ g₂ 2 x)) ≤ Λ'' from hJ2) (by positivity)
  have hM1 : Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x 3
      (metricCovDeriv (I := I) g₁ g₂ 1 x)) ≤ Λ * Real.sqrt Λ * Λ' := by
    have hcomp := DifferentialGeometry.Geometry.Curvature.sqrt_normSq0S_comp (I := I) hEq hx 3
      (metricCovDeriv (I := I) g₁ g₂ 1 x)
    rw [hs3] at hcomp
    refine le_trans hcomp ?_
    exact mul_le_mul_of_nonneg_left (show Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₂ x 3
        (metricCovDeriv (I := I) g₁ g₂ 1 x)) ≤ Λ' from hJ1)
      (mul_nonneg hLnn (Real.sqrt_nonneg _))
  have hNA : Real.sqrt (Tensor0SBundle.normSqRS (I := I) (g := g₁) (x := x) 1 2
        (Tensor0SBundle.connectionDifferenceTensorAt (I := I)
          (leviCivitaConnectionOfMetric (I := I) g₁)
          (leviCivitaConnectionOfMetric (I := I) g₂) x)) ≤ 3 / 2 * (Λ * Real.sqrt Λ * Λ') := by
    obtain ⟨_, basis₁, hhinv₁, _, _, _⟩ :=
      exists_diagInv_of_metricUniformEquivalentOn (I := I)
        (metricUniformEquivalentOn_symm (I := I) hEq) hx
    have h := diff_le_covOne_basis_ref_lc (I := I) g₁ g₂ hx Λ hEq basis₁ hhinv₁
    rw [hs3] at h
    refine le_trans h ?_
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hJ1 (mul_nonneg hLnn (Real.sqrt_nonneg _)))
      (by norm_num : (0 : ℝ) ≤ 3 / 2)
  set M3 := Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x 5
    (metricCovDeriv (I := I) g₁ g₂ 3 x)) with hM3def
  set M2 := Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x 4
    (metricCovDeriv (I := I) g₁ g₂ 2 x)) with hM2def
  set M1 := Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x 3
    (metricCovDeriv (I := I) g₁ g₂ 1 x)) with hM1def
  set NA := Real.sqrt (Tensor0SBundle.normSqRS (I := I) (g := g₁) (x := x) 1 2
    (Tensor0SBundle.connectionDifferenceTensorAt (I := I)
      (leviCivitaConnectionOfMetric (I := I) g₁)
      (leviCivitaConnectionOfMetric (I := I) g₂) x)) with hNAdef
  have hM3nn : (0 : ℝ) ≤ M3 := Real.sqrt_nonneg _
  have hM2nn : (0 : ℝ) ≤ M2 := Real.sqrt_nonneg _
  have hM1nn : (0 : ℝ) ≤ M1 := Real.sqrt_nonneg _
  have hNAnn : (0 : ℝ) ≤ NA := Real.sqrt_nonneg _
  clear_value M3 M2 M1 NA
  have hc1nn : (0 : ℝ) ≤ Λ * Real.sqrt Λ * Λ' :=
    mul_nonneg (mul_nonneg hLnn (Real.sqrt_nonneg _)) hL'nn
  have hc2nn : (0 : ℝ) ≤ Λ ^ 2 * Λ'' := mul_nonneg (by positivity) hL''nn
  have hc3nn : (0 : ℝ) ≤ 3 / 2 * (Λ * Real.sqrt Λ * Λ') :=
    mul_nonneg (by norm_num) hc1nn
  have hp1 : M2 * NA ≤ 3 / 2 * (Λ ^ 3 * Real.sqrt Λ * Λ' * Λ'') := by
    have h := mul_le_mul hM2 hNA hNAnn hc2nn
    refine le_trans h (le_of_eq ?_)
    ring
  have hp2 : M1 * M2 ≤ Λ ^ 3 * Real.sqrt Λ * Λ' * Λ'' := by
    have h := mul_le_mul hM1 hM2 hM2nn hc1nn
    refine le_trans h (le_of_eq ?_)
    ring
  have hp3 : M1 * (M1 * NA) ≤ 3 / 2 * (Λ ^ 4 * Real.sqrt Λ * Λ' ^ 3) := by
    have h := mul_le_mul hM1 (mul_le_mul hM1 hNA hNAnn hc1nn)
      (mul_nonneg hM1nn hNAnn) hc1nn
    refine le_trans h (le_of_eq ?_)
    linear_combination (3 / 2 * Λ ^ 3 * Λ' ^ 3 * Real.sqrt Λ) * hs2
  have hexp : 2 * M1 * (3 / 2 * M2 + M1 * NA) = 3 * (M1 * M2) + 2 * (M1 * (M1 * NA)) := by
    ring
  have hbr : 3 / 2 * M3 + M2 * NA + 2 * M1 * (3 / 2 * M2 + M1 * NA) ≤
      Real.sqrt Λ * (3 / 2 * Λ ^ 2 * Λ''' + 9 / 2 * Λ ^ 3 * Λ' * Λ'' + 3 * Λ ^ 4 * Λ' ^ 3) := by
    nlinarith [hM3, hp1, hp2, hp3, hexp]
  have hbrnn : (0 : ℝ) ≤ 3 / 2 * M3 + M2 * NA + 2 * M1 * (3 / 2 * M2 + M1 * NA) :=
    add_nonneg (add_nonneg (by linarith) (mul_nonneg hM2nn hNAnn))
      (mul_nonneg (by linarith) (add_nonneg (by linarith) (mul_nonneg hM1nn hNAnn)))
  set B2 : TangentSpace I x :=
    covDerivConnectionDifference2 (I := I) g₂ g₁
      (smoothExtensionTangent (I := I) x v') (smoothExtensionTangent (I := I) x v)
      (smoothExtensionTangent (I := I) x w) (smoothExtensionTangent (I := I) x u) x with hB2def
  clear_value B2
  have hvec : ∀ z : TangentSpace I x,
      Real.sqrt (g₁.inner x z z) ≤ Real.sqrt Λ * Real.sqrt (g₂.inner x z z) := by
    intro z
    calc Real.sqrt (g₁.inner x z z) ≤ Real.sqrt (Λ * g₂.inner x z z) :=
          Real.sqrt_le_sqrt (hEq.2 x hx z).2
      _ = Real.sqrt Λ * Real.sqrt (g₂.inner x z z) := Real.sqrt_mul hLnn _
  have hBcomp : Real.sqrt (g₂.inner x B2 B2) ≤ Real.sqrt Λ * Real.sqrt (g₁.inner x B2 B2) := by
    have h := (hEq.2 x hx B2).1
    have h' : g₂.inner x B2 B2 ≤ Λ * g₁.inner x B2 B2 := by
      have h2 := mul_le_mul_of_nonneg_left h hLnn
      rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hL0), one_mul] at h2
      exact h2
    calc Real.sqrt (g₂.inner x B2 B2) ≤ Real.sqrt (Λ * g₁.inner x B2 B2) := Real.sqrt_le_sqrt h'
      _ = Real.sqrt Λ * Real.sqrt (g₁.inner x B2 B2) := Real.sqrt_mul hLnn _
  have hv4 : Real.sqrt (g₁.inner x v' v') * Real.sqrt (g₁.inner x v v) *
        Real.sqrt (g₁.inner x w w) * Real.sqrt (g₁.inner x u u) ≤
      Real.sqrt Λ * Real.sqrt (g₂.inner x v' v') * (Real.sqrt Λ * Real.sqrt (g₂.inner x v v)) *
        (Real.sqrt Λ * Real.sqrt (g₂.inner x w w)) *
          (Real.sqrt Λ * Real.sqrt (g₂.inner x u u)) := by
    have p1 : Real.sqrt (g₁.inner x v' v') * Real.sqrt (g₁.inner x v v) ≤
        Real.sqrt Λ * Real.sqrt (g₂.inner x v' v') *
          (Real.sqrt Λ * Real.sqrt (g₂.inner x v v)) :=
      mul_le_mul (hvec v') (hvec v) (Real.sqrt_nonneg _) (by positivity)
    have p2 : Real.sqrt (g₁.inner x v' v') * Real.sqrt (g₁.inner x v v) *
          Real.sqrt (g₁.inner x w w) ≤
        Real.sqrt Λ * Real.sqrt (g₂.inner x v' v') * (Real.sqrt Λ * Real.sqrt (g₂.inner x v v)) *
          (Real.sqrt Λ * Real.sqrt (g₂.inner x w w)) :=
      mul_le_mul p1 (hvec w) (Real.sqrt_nonneg _) (by positivity)
    exact mul_le_mul p2 (hvec u) (Real.sqrt_nonneg _) (by positivity)
  have hfin : Real.sqrt (g₁.inner x B2 B2) ≤
      Real.sqrt Λ * (3 / 2 * Λ ^ 2 * Λ''' + 9 / 2 * Λ ^ 3 * Λ' * Λ'' + 3 * Λ ^ 4 * Λ' ^ 3) *
        (Real.sqrt Λ * Real.sqrt (g₂.inner x v' v') *
          (Real.sqrt Λ * Real.sqrt (g₂.inner x v v)) *
          (Real.sqrt Λ * Real.sqrt (g₂.inner x w w)) *
          (Real.sqrt Λ * Real.sqrt (g₂.inner x u u))) := by
    refine le_trans hcore ?_
    have h1 := mul_le_mul_of_nonneg_left hv4 hbrnn
    have h2 := mul_le_mul_of_nonneg_right hbr
      (show (0 : ℝ) ≤ Real.sqrt Λ * Real.sqrt (g₂.inner x v' v') *
          (Real.sqrt Λ * Real.sqrt (g₂.inner x v v)) *
          (Real.sqrt Λ * Real.sqrt (g₂.inner x w w)) *
          (Real.sqrt Λ * Real.sqrt (g₂.inner x u u)) by positivity)
    linarith [h1, h2]
  calc Real.sqrt (g₂.inner x B2 B2)
      ≤ Real.sqrt Λ * Real.sqrt (g₁.inner x B2 B2) := hBcomp
    _ ≤ Real.sqrt Λ *
          (Real.sqrt Λ * (3 / 2 * Λ ^ 2 * Λ''' + 9 / 2 * Λ ^ 3 * Λ' * Λ'' + 3 * Λ ^ 4 * Λ' ^ 3) *
            (Real.sqrt Λ * Real.sqrt (g₂.inner x v' v') *
              (Real.sqrt Λ * Real.sqrt (g₂.inner x v v)) *
              (Real.sqrt Λ * Real.sqrt (g₂.inner x w w)) *
              (Real.sqrt Λ * Real.sqrt (g₂.inner x u u)))) :=
        mul_le_mul_of_nonneg_left hfin (Real.sqrt_nonneg _)
    _ = (3 / 2 * Λ ^ 5 * Λ''' + 9 / 2 * Λ ^ 6 * Λ' * Λ'' + 3 * Λ ^ 7 * Λ' ^ 3) *
          Real.sqrt (g₂.inner x v' v') * Real.sqrt (g₂.inner x v v) *
            Real.sqrt (g₂.inner x w w) * Real.sqrt (g₂.inner x u u) := by
        linear_combination ((3 / 2 * Λ ^ 2 * Λ''' + 9 / 2 * Λ ^ 3 * Λ' * Λ'' +
            3 * Λ ^ 4 * Λ' ^ 3) *
          (Real.sqrt Λ ^ 4 + Real.sqrt Λ ^ 2 * Λ + Λ ^ 2) *
          (Real.sqrt (g₂.inner x v' v') * Real.sqrt (g₂.inner x v v) *
            Real.sqrt (g₂.inner x w w) * Real.sqrt (g₂.inner x u u))) * hs2

open DifferentialGeometry.Integral.Connection in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem covStep2_diffStep_peel
    (g₁ g₂ : SmoothRiemannianMetric I M) (s : Nat)
    (S : Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s)
    (U W V : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (Vslots : Fin s -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (x : M) :
    covStep (I := I) g₂ (s + 2)
        (covStep (I := I) g₂ (s + 1) (diffStep (I := I) g₁ g₂ s S)) x
        (Fin.cons (U x) (Fin.cons (W x) (Fin.cons (V x) (fun a : Fin s => Vslots a x))))
      = mvfderiv (I := I)
            (fun y : M =>
              (-∑ a : Fin s, (S y) (Function.update (fun b : Fin s => Vslots b y) a
                  (covDerivConnectionDifference (I := I) g₂ g₁
                    (fun z => W z) (fun z => V z) (fun z => Vslots a z) y)))
              - ∑ a : Fin s, covStep (I := I) g₂ s S y
                  (Fin.cons (W y) (Function.update (fun b : Fin s => Vslots b y) a
                    ((CovariantDerivative.difference
                        (leviCivitaConnectionOfMetric (I := I) g₁)
                        (leviCivitaConnectionOfMetric (I := I) g₂) y
                        (Vslots a y)) (V y))))) x (U x)
        - ∑ q : Fin (s + 2),
            (covStep (I := I) g₂ (s + 1) (diffStep (I := I) g₁ g₂ s S)) x
              (Function.update
                (fun b : Fin (s + 2) =>
                  (Fin.cons W (Fin.cons V Vslots) :
                    Fin (s + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
                      (TangentSpace I : M -> Type _)) b x) q
                ((leviCivitaConnectionOfMetric (I := I) g₂
                    (fun y : M =>
                      (Fin.cons W (Fin.cons V Vslots) :
                        Fin (s + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
                          (TangentSpace I : M -> Type _)) q y) x) (U x))) := by
  classical
  have : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  have : IsManifold I 2 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  have : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
    change IsManifold I ∞ M
    infer_instance
  have : IsManifold I (1 + 1) M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by decide : ((1 : WithTop ℕ∞) + 1) ≤ ∞)
  have : ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I :=
    TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := 1)
  set RR : Fin (s + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _) := Fin.cons W (Fin.cons V Vslots) with hRRdef
  have hRRpt : ∀ y : M, (fun q : Fin (s + 2) => RR q y)
      = Fin.cons (W y) (Fin.cons (V y) (fun a : Fin s => Vslots a y)) := by
    intro y
    funext q
    refine Fin.cases ?_ (fun i => ?_) q
    · simp [hRRdef]
    · refine Fin.cases ?_ (fun j => ?_) i <;> simp [hRRdef]
  rw [show Fin.cons (W x) (Fin.cons (V x) (fun a : Fin s => Vslots a x))
        = (fun q : Fin (s + 2) => RR q x) from (hRRpt x).symm,
    covStep_eval_smooth_slots (I := I) g₂ (s + 2)
      (covStep (I := I) g₂ (s + 1) (diffStep (I := I) g₁ g₂ s S)) U RR x]
  have hInner :
      (fun y : M => (covStep (I := I) g₂ (s + 1) (diffStep (I := I) g₁ g₂ s S)) y
          (fun q : Fin (s + 2) => RR q y))
        = (fun y : M =>
            (-∑ a : Fin s, (S y) (Function.update (fun b : Fin s => Vslots b y) a
                (covDerivConnectionDifference (I := I) g₂ g₁
                  (fun z => W z) (fun z => V z) (fun z => Vslots a z) y)))
            - ∑ a : Fin s, covStep (I := I) g₂ s S y
                (Fin.cons (W y) (Function.update (fun b : Fin s => Vslots b y) a
                  ((CovariantDerivative.difference
                      (leviCivitaConnectionOfMetric (I := I) g₁)
                      (leviCivitaConnectionOfMetric (I := I) g₂) y
                      (Vslots a y)) (V y))))) := by
    funext y
    rw [hRRpt y]
    exact diffStep_leibniz_eval (I := I) g₁ g₂ s S W V Vslots y
  rw [hInner]

open DifferentialGeometry.Integral.Connection in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem covStep2_diffStep_branch1
    (g₁ g₂ : SmoothRiemannianMetric I M) (s : Nat)
    (S : Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s)
    (U W V : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (Vslots : Fin s -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (a : Fin s) (x : M) :
    mvfderiv (I := I)
        (fun y : M => (S y) (Function.update (fun b : Fin s => Vslots b y) a
          (covDerivConnectionDifference (I := I) g₂ g₁
            (fun z => W z) (fun z => V z) (fun z => Vslots a z) y))) x (U x)
      = covStep (I := I) g₂ s S x
          (Fin.cons (U x) (Function.update (fun b : Fin s => Vslots b x) a
            (covDerivConnectionDifference (I := I) g₂ g₁
              (fun z => W z) (fun z => V z) (fun z => Vslots a z) x)))
        + (S x) (Function.update (fun b : Fin s => Vslots b x) a
            (covDerivConnectionDifference2 (I := I) g₂ g₁
                (fun z => U z) (fun z => W z) (fun z => V z) (fun z => Vslots a z) x
              + covDerivConnectionDifference (I := I) g₂ g₁
                  (covApply (LeviCivita (I := I) g₂) (fun z => U z) (fun z => W z))
                  (fun z => V z) (fun z => Vslots a z) x
              + covDerivConnectionDifference (I := I) g₂ g₁ (fun z => W z)
                  (covApply (LeviCivita (I := I) g₂) (fun z => U z) (fun z => V z))
                  (fun z => Vslots a z) x
              + covDerivConnectionDifference (I := I) g₂ g₁ (fun z => W z) (fun z => V z)
                  (covApply (LeviCivita (I := I) g₂) (fun z => U z) (fun z => Vslots a z)) x))
        + ∑ b ∈ Finset.univ.erase a, (S x) (Function.update
            (Function.update (fun c : Fin s => Vslots c x) a
              (covDerivConnectionDifference (I := I) g₂ g₁
                (fun z => W z) (fun z => V z) (fun z => Vslots a z) x)) b
            ((leviCivitaConnectionOfMetric (I := I) g₂
                (fun y : M => Vslots b y) x) (U x))) := by
  classical
  have : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  have : IsManifold I 2 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  have : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
    change IsManifold I ∞ M
    infer_instance
  have : IsManifold I (1 + 1) M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by decide : ((1 : WithTop ℕ∞) + 1) ≤ ∞)
  have : ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I :=
    TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := 1)
  have hcov₁ : CovariantDerivative.ContMDiffCovariantDerivative
      (leviCivitaConnectionOfMetric (I := I) g₁) (∞ : WithTop ℕ∞) :=
    leviCivitaConnectionOfMetric_contMDiffCovariantDerivative (I := I) g₁
  have hcov₂ : CovariantDerivative.ContMDiffCovariantDerivative
      (leviCivitaConnectionOfMetric (I := I) g₂) (∞ : WithTop ℕ∞) :=
    leviCivitaConnectionOfMetric_contMDiffCovariantDerivative (I := I) g₂
  set CDCsec : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    ContMDiffSection.mk
      (fun p => covDerivConnectionDifference (I := I) g₂ g₁
        (fun z => W z) (fun z => V z) (fun z => Vslots a z) p)
      (covDerivConnectionDifference_contMDiff (I := I) g₂ g₁ W V (Vslots a)) with hCDCdef
  set σ : Fin s → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    Function.update Vslots a CDCsec with hσdef
  have hCDCcoe : ∀ p : M, (CDCsec) p
      = covDerivConnectionDifference (I := I) g₂ g₁
          (fun z => W z) (fun z => V z) (fun z => Vslots a z) p := by
    intro p
    rw [hCDCdef]
    rfl
  have hσeval : ∀ y : M, (fun b : Fin s => (σ b) y)
      = Function.update (fun b : Fin s => Vslots b y) a
          (covDerivConnectionDifference (I := I) g₂ g₁
            (fun z => W z) (fun z => V z) (fun z => Vslots a z) y) := by
    intro y
    funext b
    rcases eq_or_ne b a with hb | hb
    · subst hb
      simp only [hσdef, Function.update_self]
      exact hCDCcoe y
    · simp only [hσdef, Function.update_of_ne hb]
  have hInnerFun : (fun y : M => (S y) (Function.update (fun b : Fin s => Vslots b y) a
        (covDerivConnectionDifference (I := I) g₂ g₁
          (fun z => W z) (fun z => V z) (fun z => Vslots a z) y)))
      = (fun y : M => (S y) (fun b : Fin s => (σ b) y)) := by
    funext y
    rw [hσeval y]
  rw [hInnerFun]
  have hpeel := covStep_eval_smooth_slots (I := I) g₂ s S U σ x
  have hpeel' : mvfderiv (I := I) (fun y : M => (S y) (fun b : Fin s => (σ b) y)) x (U x)
      = covStep (I := I) g₂ s S x (Fin.cons (U x) (fun b : Fin s => (σ b) x))
        + ∑ q : Fin s, (S x) (Function.update (fun b : Fin s => (σ b) x) q
            ((leviCivitaConnectionOfMetric (I := I) g₂ (fun y : M => (σ q) y) x) (U x))) := by
    rw [hpeel]
    ring
  have hσa : (fun y : M => (σ a) y)
      = (fun p : M => covDerivConnectionDifference (I := I) g₂ g₁
          (fun z => W z) (fun z => V z) (fun z => Vslots a z) p) := by
    funext y
    simp only [hσdef, Function.update_self]
    exact hCDCcoe y
  have hdiag : (leviCivitaConnectionOfMetric (I := I) g₂ (fun y : M => (σ a) y) x) (U x)
      = covDerivConnectionDifference2 (I := I) g₂ g₁
          (fun z => U z) (fun z => W z) (fun z => V z) (fun z => Vslots a z) x
        + covDerivConnectionDifference (I := I) g₂ g₁
            (covApply (LeviCivita (I := I) g₂) (fun z => U z) (fun z => W z))
            (fun z => V z) (fun z => Vslots a z) x
        + covDerivConnectionDifference (I := I) g₂ g₁ (fun z => W z)
            (covApply (LeviCivita (I := I) g₂) (fun z => U z) (fun z => V z))
            (fun z => Vslots a z) x
        + covDerivConnectionDifference (I := I) g₂ g₁ (fun z => W z) (fun z => V z)
            (covApply (LeviCivita (I := I) g₂) (fun z => U z) (fun z => Vslots a z)) x := by
    rw [hσa, covDerivConnectionDifference2_eq]
    simp only [covApply, LeviCivita_eq_leviCivitaConnectionOfMetric]
    abel
  have hoff : (∑ b ∈ Finset.univ.erase a, (S x) (Function.update
        (Function.update (fun c : Fin s => Vslots c x) a
          (covDerivConnectionDifference (I := I) g₂ g₁
            (fun z => W z) (fun z => V z) (fun z => Vslots a z) x)) b
        ((leviCivitaConnectionOfMetric (I := I) g₂ (fun y : M => (σ b) y) x) (U x))))
      = ∑ b ∈ Finset.univ.erase a, (S x) (Function.update
          (Function.update (fun c : Fin s => Vslots c x) a
            (covDerivConnectionDifference (I := I) g₂ g₁
              (fun z => W z) (fun z => V z) (fun z => Vslots a z) x)) b
          ((leviCivitaConnectionOfMetric (I := I) g₂ (fun y : M => Vslots b y) x) (U x))) := by
    refine Finset.sum_congr rfl (fun b hb => ?_)
    have hbne : (fun y : M => (σ b) y) = (fun y : M => Vslots b y) := by
      funext y
      simp only [hσdef, Function.update_of_ne (Finset.ne_of_mem_erase hb)]
    rw [hbne]
  rw [hpeel', hσeval x, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ a),
    Function.update_idem, hdiag, hoff]
  abel

open DifferentialGeometry.Integral.Connection in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem covStep2_diffStep_branch2
    (g₁ g₂ : SmoothRiemannianMetric I M) (s : Nat)
    (S : Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s)
    (U W V : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (Vslots : Fin s -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (a : Fin s) (x : M) :
    mvfderiv (I := I)
        (fun y : M => covStep (I := I) g₂ s S y
          (Fin.cons (W y) (Function.update (fun b : Fin s => Vslots b y) a
            ((CovariantDerivative.difference
                (leviCivitaConnectionOfMetric (I := I) g₁)
                (leviCivitaConnectionOfMetric (I := I) g₂) y
                (Vslots a y)) (V y))))) x (U x)
      = covStep (I := I) g₂ (s + 1) (covStep (I := I) g₂ s S) x
          (Fin.cons (U x) (Fin.cons (W x) (Function.update (fun b : Fin s => Vslots b x) a
            ((CovariantDerivative.difference
                (leviCivitaConnectionOfMetric (I := I) g₁)
                (leviCivitaConnectionOfMetric (I := I) g₂) x
                (Vslots a x)) (V x)))))
        + covStep (I := I) g₂ s S x
            (Fin.cons ((leviCivitaConnectionOfMetric (I := I) g₂ (fun y : M => W y) x) (U x))
              (Function.update (fun b : Fin s => Vslots b x) a
                ((CovariantDerivative.difference
                    (leviCivitaConnectionOfMetric (I := I) g₁)
                    (leviCivitaConnectionOfMetric (I := I) g₂) x
                    (Vslots a x)) (V x))))
        + covStep (I := I) g₂ s S x
            (Fin.cons (W x) (Function.update (fun b : Fin s => Vslots b x) a
              (covDerivConnectionDifference (I := I) g₂ g₁
                  (fun z => U z) (fun z => V z) (fun z => Vslots a z) x
                + (CovariantDerivative.difference
                    (leviCivitaConnectionOfMetric (I := I) g₁)
                    (leviCivitaConnectionOfMetric (I := I) g₂) x (Vslots a x))
                    ((leviCivitaConnectionOfMetric (I := I) g₂ (fun y : M => V y) x) (U x))
                + (CovariantDerivative.difference
                    (leviCivitaConnectionOfMetric (I := I) g₁)
                    (leviCivitaConnectionOfMetric (I := I) g₂) x
                    ((leviCivitaConnectionOfMetric (I := I) g₂ (fun y : M => Vslots a y) x) (U x)))
                    (V x))))
        + ∑ b ∈ Finset.univ.erase a, covStep (I := I) g₂ s S x
            (Fin.cons (W x) (Function.update
              (Function.update (fun c : Fin s => Vslots c x) a
                ((CovariantDerivative.difference
                    (leviCivitaConnectionOfMetric (I := I) g₁)
                    (leviCivitaConnectionOfMetric (I := I) g₂) x
                    (Vslots a x)) (V x))) b
              ((leviCivitaConnectionOfMetric (I := I) g₂ (fun y : M => Vslots b y) x) (U x)))) := by
  classical
  have : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  have : IsManifold I 2 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  have : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
    change IsManifold I ∞ M
    infer_instance
  have : IsManifold I (1 + 1) M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by decide : ((1 : WithTop ℕ∞) + 1) ≤ ∞)
  have : ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I :=
    TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := 1)
  have hcov₁ : CovariantDerivative.ContMDiffCovariantDerivative
      (leviCivitaConnectionOfMetric (I := I) g₁) (∞ : WithTop ℕ∞) :=
    leviCivitaConnectionOfMetric_contMDiffCovariantDerivative (I := I) g₁
  have hcov₂ : CovariantDerivative.ContMDiffCovariantDerivative
      (leviCivitaConnectionOfMetric (I := I) g₂) (∞ : WithTop ℕ∞) :=
    leviCivitaConnectionOfMetric_contMDiffCovariantDerivative (I := I) g₂
  set Asec : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    ContMDiffSection.mk
      (diffSec (leviCivitaConnectionOfMetric (I := I) g₂)
        (leviCivitaConnectionOfMetric (I := I) g₁) (fun y : M => V y) (fun y : M => Vslots a y))
      (diffSec_contMDiff (leviCivitaConnectionOfMetric (I := I) g₂)
        (leviCivitaConnectionOfMetric (I := I) g₁) V.contMDiff
        (by simpa using (Vslots a).contMDiff)) with hAsecdef
  set ρ : Fin (s + 1) → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    Fin.cons W (Function.update Vslots a Asec) with hρdef
  have hAcoe : ∀ y : M, (Asec) y
      = (CovariantDerivative.difference
          (leviCivitaConnectionOfMetric (I := I) g₁)
          (leviCivitaConnectionOfMetric (I := I) g₂) y (Vslots a y)) (V y) := by
    intro y
    rw [hAsecdef]
    rfl
  have hρpt : ∀ y : M, (fun p : Fin (s + 1) => (ρ p) y)
      = Fin.cons (W y) (Function.update (fun b : Fin s => Vslots b y) a
          ((CovariantDerivative.difference
              (leviCivitaConnectionOfMetric (I := I) g₁)
              (leviCivitaConnectionOfMetric (I := I) g₂) y (Vslots a y)) (V y))) := by
    intro y
    funext p
    refine Fin.cases ?_ (fun i => ?_) p
    · simp only [hρdef, Fin.cons_zero]
    · rcases eq_or_ne i a with hi | hi
      · subst hi
        simp only [hρdef, Fin.cons_succ, Function.update_self]
        exact hAcoe y
      · simp only [hρdef, Fin.cons_succ, Function.update_of_ne hi]
  have hInnerFun : (fun y : M => covStep (I := I) g₂ s S y
        (Fin.cons (W y) (Function.update (fun b : Fin s => Vslots b y) a
          ((CovariantDerivative.difference
              (leviCivitaConnectionOfMetric (I := I) g₁)
              (leviCivitaConnectionOfMetric (I := I) g₂) y
              (Vslots a y)) (V y)))))
      = (fun y : M => covStep (I := I) g₂ s S y (fun p : Fin (s + 1) => (ρ p) y)) := by
    funext y
    rw [hρpt y]
  rw [hInnerFun]
  have hpeel := covStep_eval_smooth_slots (I := I) g₂ (s + 1) (covStep (I := I) g₂ s S) U ρ x
  have hpeel' : mvfderiv (I := I)
        (fun y : M => covStep (I := I) g₂ s S y (fun p : Fin (s + 1) => (ρ p) y)) x (U x)
      = covStep (I := I) g₂ (s + 1) (covStep (I := I) g₂ s S) x
          (Fin.cons (U x) (fun p : Fin (s + 1) => (ρ p) x))
        + ∑ p : Fin (s + 1), (covStep (I := I) g₂ s S x) (Function.update
            (fun b : Fin (s + 1) => (ρ b) x) p
            ((leviCivitaConnectionOfMetric (I := I) g₂ (fun y : M => (ρ p) y) x) (U x))) := by
    rw [hpeel]
    ring
  have hfact : (leviCivitaConnectionOfMetric (I := I) g₂ (fun y : M => (Asec) y) x) (U x)
      = covDerivConnectionDifference (I := I) g₂ g₁
          (fun z => U z) (fun z => V z) (fun z => Vslots a z) x
        + (CovariantDerivative.difference
            (leviCivitaConnectionOfMetric (I := I) g₁)
            (leviCivitaConnectionOfMetric (I := I) g₂) x (Vslots a x))
            ((leviCivitaConnectionOfMetric (I := I) g₂ (fun y : M => V y) x) (U x))
        + (CovariantDerivative.difference
            (leviCivitaConnectionOfMetric (I := I) g₁)
            (leviCivitaConnectionOfMetric (I := I) g₂) x
            ((leviCivitaConnectionOfMetric (I := I) g₂ (fun y : M => Vslots a y) x) (U x)))
            (V x) := by
    rw [covDerivConnectionDifference_eq]
    simp only [covDerivDiff, covApply, hAsecdef, ContMDiffSection.coeFn_mk,
      LeviCivita_eq_leviCivitaConnectionOfMetric]
    abel
  have hρ0 : (fun y : M => (ρ (0 : Fin (s + 1))) y) = (fun y : M => W y) := by
    funext y
    simp only [hρdef, Fin.cons_zero]
  have hoff : (∑ i ∈ Finset.univ.erase a, (covStep (I := I) g₂ s S x) (Fin.cons (W x)
        (Function.update (Function.update (fun c : Fin s => Vslots c x) a
            ((CovariantDerivative.difference
                (leviCivitaConnectionOfMetric (I := I) g₁)
                (leviCivitaConnectionOfMetric (I := I) g₂) x (Vslots a x)) (V x))) i
          ((leviCivitaConnectionOfMetric (I := I) g₂ (fun y : M => (ρ i.succ) y) x) (U x)))))
      = ∑ i ∈ Finset.univ.erase a, (covStep (I := I) g₂ s S x) (Fin.cons (W x)
          (Function.update (Function.update (fun c : Fin s => Vslots c x) a
              ((CovariantDerivative.difference
                  (leviCivitaConnectionOfMetric (I := I) g₁)
                  (leviCivitaConnectionOfMetric (I := I) g₂) x (Vslots a x)) (V x))) i
            ((leviCivitaConnectionOfMetric (I := I) g₂ (fun y : M => Vslots i y) x) (U x)))) := by
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hine : (fun y : M => (ρ i.succ) y) = (fun y : M => Vslots i y) := by
      funext y
      simp only [hρdef, Fin.cons_succ, Function.update_of_ne (Finset.ne_of_mem_erase hi)]
    rw [hine]
  rw [hpeel', hρpt x, Fin.sum_univ_succ]
  simp only [Fin.update_cons_zero, ← Fin.cons_update, hρ0]
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ a)]
  have hρa : (fun y : M => (ρ a.succ) y) = (fun y : M => (Asec) y) := by
    funext y
    simp only [hρdef, Fin.cons_succ, Function.update_self]
  rw [Function.update_idem, hρa, hfact, hoff]
  abel

open DifferentialGeometry.Integral.Connection in
omit [NeZero (Module.finrank ℝ E)] [T2Space M] [CompactSpace M] [I.Boundaryless] in
theorem covStep2_branch1_mdiff
    (g₁ g₂ : SmoothRiemannianMetric I M) (s : Nat)
    (S : Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s)
    (W V : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (Vslots : Fin s -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (a : Fin s) (x : M) :
    MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun y : M => (S y) (Function.update (fun b : Fin s => Vslots b y) a
        (covDerivConnectionDifference (I := I) g₂ g₁
          (fun z => W z) (fun z => V z) (fun z => Vslots a z) y))) x := by
  classical
  have : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  have : IsManifold I 2 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  have : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
    change IsManifold I ∞ M
    infer_instance
  have : IsManifold I (1 + 1) M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by decide : ((1 : WithTop ℕ∞) + 1) ≤ ∞)
  have : ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I :=
    TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := 1)
  have hcov₁ : CovariantDerivative.ContMDiffCovariantDerivative
      (leviCivitaConnectionOfMetric (I := I) g₁) (∞ : WithTop ℕ∞) :=
    leviCivitaConnectionOfMetric_contMDiffCovariantDerivative (I := I) g₁
  have hcov₂ : CovariantDerivative.ContMDiffCovariantDerivative
      (leviCivitaConnectionOfMetric (I := I) g₂) (∞ : WithTop ℕ∞) :=
    leviCivitaConnectionOfMetric_contMDiffCovariantDerivative (I := I) g₂
  set CDCsec : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    ContMDiffSection.mk
      (fun p => covDerivConnectionDifference (I := I) g₂ g₁
        (fun z => W z) (fun z => V z) (fun z => Vslots a z) p)
      (covDerivConnectionDifference_contMDiff (I := I) g₂ g₁ W V (Vslots a)) with hCDCdef
  set σ : Fin s → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    Function.update Vslots a CDCsec with hσdef
  have hCDCcoe : ∀ p : M, (CDCsec) p
      = covDerivConnectionDifference (I := I) g₂ g₁
          (fun z => W z) (fun z => V z) (fun z => Vslots a z) p := by
    intro p
    rw [hCDCdef]
    rfl
  have hσeval : ∀ y : M, (fun b : Fin s => (σ b) y)
      = Function.update (fun b : Fin s => Vslots b y) a
          (covDerivConnectionDifference (I := I) g₂ g₁
            (fun z => W z) (fun z => V z) (fun z => Vslots a z) y) := by
    intro y
    funext b
    rcases eq_or_ne b a with hb | hb
    · subst hb
      simp only [hσdef, Function.update_self]
      exact hCDCcoe y
    · simp only [hσdef, Function.update_of_ne hb]
  have hEq : (fun y : M => (S y) (Function.update (fun b : Fin s => Vslots b y) a
        (covDerivConnectionDifference (I := I) g₂ g₁
          (fun z => W z) (fun z => V z) (fun z => Vslots a z) y)))
      = (fun y : M => (S y) (fun b : Fin s => (σ b) y)) := by
    funext y
    rw [hσeval y]
  rw [hEq]
  have hS := (S.contMDiff x).of_le (le_refl (∞ : WithTop ℕ∞))
  have hEval := TensorMultilinear.contMDiffAt_section_apply (I := I) (M := M) (n := s) (x₀ := x)
    (T := fun y : M => S y) hS (v := fun b : Fin s => fun y : M => (σ b) y)
    (hv := fun b => ((σ b).contMDiff.contMDiffAt))
  have hSAt : ContMDiffAt I 𝓘(ℝ, ℝ) (∞ : WithTop ℕ∞)
      (fun y : M => (S y) (fun b : Fin s => (σ b) y)) x := by
    change ContMDiffAt I 𝓘(ℝ, ℝ) (∞ : WithTop ℕ∞)
      (fun y : M => Tensor0SSpace.eval (S y) (fun b : Fin s => (σ b) y)) x
    exact hEval
  exact hSAt.mdifferentiableAt (by simp)

open DifferentialGeometry.Integral.Connection in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem covStep2_branch2_mdiff
    (g₁ g₂ : SmoothRiemannianMetric I M) (s : Nat)
    (S : Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s)
    (W V : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (Vslots : Fin s -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (a : Fin s) (x : M) :
    MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun y : M => covStep (I := I) g₂ s S y
        (Fin.cons (W y) (Function.update (fun b : Fin s => Vslots b y) a
          ((CovariantDerivative.difference
              (leviCivitaConnectionOfMetric (I := I) g₁)
              (leviCivitaConnectionOfMetric (I := I) g₂) y
              (Vslots a y)) (V y))))) x := by
  classical
  have : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  have : IsManifold I 2 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  have : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
    change IsManifold I ∞ M
    infer_instance
  have : IsManifold I (1 + 1) M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by decide : ((1 : WithTop ℕ∞) + 1) ≤ ∞)
  have : ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I :=
    TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := 1)
  have hcov₁ : CovariantDerivative.ContMDiffCovariantDerivative
      (leviCivitaConnectionOfMetric (I := I) g₁) (∞ : WithTop ℕ∞) :=
    leviCivitaConnectionOfMetric_contMDiffCovariantDerivative (I := I) g₁
  have hcov₂ : CovariantDerivative.ContMDiffCovariantDerivative
      (leviCivitaConnectionOfMetric (I := I) g₂) (∞ : WithTop ℕ∞) :=
    leviCivitaConnectionOfMetric_contMDiffCovariantDerivative (I := I) g₂
  set Asec : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    ContMDiffSection.mk
      (diffSec (leviCivitaConnectionOfMetric (I := I) g₂)
        (leviCivitaConnectionOfMetric (I := I) g₁) (fun y : M => V y) (fun y : M => Vslots a y))
      (diffSec_contMDiff (leviCivitaConnectionOfMetric (I := I) g₂)
        (leviCivitaConnectionOfMetric (I := I) g₁) V.contMDiff
        (by simpa using (Vslots a).contMDiff)) with hAsecdef
  set ρ : Fin (s + 1) → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    Fin.cons W (Function.update Vslots a Asec) with hρdef
  have hAcoe : ∀ y : M, (Asec) y
      = (CovariantDerivative.difference
          (leviCivitaConnectionOfMetric (I := I) g₁)
          (leviCivitaConnectionOfMetric (I := I) g₂) y (Vslots a y)) (V y) := by
    intro y
    rw [hAsecdef]
    rfl
  have hρpt : ∀ y : M, (fun p : Fin (s + 1) => (ρ p) y)
      = Fin.cons (W y) (Function.update (fun b : Fin s => Vslots b y) a
          ((CovariantDerivative.difference
              (leviCivitaConnectionOfMetric (I := I) g₁)
              (leviCivitaConnectionOfMetric (I := I) g₂) y (Vslots a y)) (V y))) := by
    intro y
    funext p
    refine Fin.cases ?_ (fun i => ?_) p
    · simp only [hρdef, Fin.cons_zero]
    · rcases eq_or_ne i a with hi | hi
      · subst hi
        simp only [hρdef, Fin.cons_succ, Function.update_self]
        exact hAcoe y
      · simp only [hρdef, Fin.cons_succ, Function.update_of_ne hi]
  have hEq : (fun y : M => covStep (I := I) g₂ s S y
        (Fin.cons (W y) (Function.update (fun b : Fin s => Vslots b y) a
          ((CovariantDerivative.difference
              (leviCivitaConnectionOfMetric (I := I) g₁)
              (leviCivitaConnectionOfMetric (I := I) g₂) y
              (Vslots a y)) (V y)))))
      = (fun y : M => covStep (I := I) g₂ s S y (fun p : Fin (s + 1) => (ρ p) y)) := by
    funext y
    rw [hρpt y]
  rw [hEq]
  have hS := ((covStep (I := I) g₂ s S).contMDiff x).of_le (le_refl (∞ : WithTop ℕ∞))
  have hEval := TensorMultilinear.contMDiffAt_section_apply (I := I) (M := M) (n := s + 1) (x₀ := x)
    (T := fun y : M => covStep (I := I) g₂ s S y) hS (v := fun p : Fin (s + 1) => fun y : M => (ρ p) y)
    (hv := fun p => ((ρ p).contMDiff.contMDiffAt))
  have hSAt : ContMDiffAt I 𝓘(ℝ, ℝ) (∞ : WithTop ℕ∞)
      (fun y : M => covStep (I := I) g₂ s S y (fun p : Fin (s + 1) => (ρ p) y)) x := by
    change ContMDiffAt I 𝓘(ℝ, ℝ) (∞ : WithTop ℕ∞)
      (fun y : M => Tensor0SSpace.eval (covStep (I := I) g₂ s S y)
        (fun p : Fin (s + 1) => (ρ p) y)) x
    exact hEval
  exact hSAt.mdifferentiableAt (by simp)

open DifferentialGeometry.Integral.Connection in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem covStep2_diffStep_split
    (g₁ g₂ : SmoothRiemannianMetric I M) (s : Nat)
    (S : Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s)
    (U W V : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (Vslots : Fin s -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (x : M) :
    mvfderiv (I := I)
        (fun y : M =>
          (-∑ a : Fin s, (S y) (Function.update (fun b : Fin s => Vslots b y) a
              (covDerivConnectionDifference (I := I) g₂ g₁
                (fun z => W z) (fun z => V z) (fun z => Vslots a z) y)))
          - ∑ a : Fin s, covStep (I := I) g₂ s S y
              (Fin.cons (W y) (Function.update (fun b : Fin s => Vslots b y) a
                ((CovariantDerivative.difference
                    (leviCivitaConnectionOfMetric (I := I) g₁)
                    (leviCivitaConnectionOfMetric (I := I) g₂) y
                    (Vslots a y)) (V y))))) x (U x)
      = (-∑ a : Fin s, mvfderiv (I := I)
            (fun y : M => (S y) (Function.update (fun b : Fin s => Vslots b y) a
              (covDerivConnectionDifference (I := I) g₂ g₁
                (fun z => W z) (fun z => V z) (fun z => Vslots a z) y))) x (U x))
        - ∑ a : Fin s, mvfderiv (I := I)
            (fun y : M => covStep (I := I) g₂ s S y
              (Fin.cons (W y) (Function.update (fun b : Fin s => Vslots b y) a
                ((CovariantDerivative.difference
                    (leviCivitaConnectionOfMetric (I := I) g₁)
                    (leviCivitaConnectionOfMetric (I := I) g₂) y
                    (Vslots a y)) (V y))))) x (U x) := by
  classical
  have hT1 : ∀ a : Fin s, MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun y : M => (S y) (Function.update (fun b : Fin s => Vslots b y) a
        (covDerivConnectionDifference (I := I) g₂ g₁
          (fun z => W z) (fun z => V z) (fun z => Vslots a z) y))) x :=
    fun a => covStep2_branch1_mdiff (I := I) g₁ g₂ s S W V Vslots a x
  have hT2 : ∀ a : Fin s, MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun y : M => covStep (I := I) g₂ s S y
        (Fin.cons (W y) (Function.update (fun b : Fin s => Vslots b y) a
          ((CovariantDerivative.difference
              (leviCivitaConnectionOfMetric (I := I) g₁)
              (leviCivitaConnectionOfMetric (I := I) g₂) y
              (Vslots a y)) (V y))))) x :=
    fun a => covStep2_branch2_mdiff (I := I) g₁ g₂ s S W V Vslots a x
  have hsum2 : (fun y : M => ∑ a : Fin s, covStep (I := I) g₂ s S y
        (Fin.cons (W y) (Function.update (fun b : Fin s => Vslots b y) a
          ((CovariantDerivative.difference
              (leviCivitaConnectionOfMetric (I := I) g₁)
              (leviCivitaConnectionOfMetric (I := I) g₂) y
              (Vslots a y)) (V y)))))
      = Finset.univ.sum (fun a : Fin s => fun y : M => covStep (I := I) g₂ s S y
          (Fin.cons (W y) (Function.update (fun b : Fin s => Vslots b y) a
            ((CovariantDerivative.difference
                (leviCivitaConnectionOfMetric (I := I) g₁)
                (leviCivitaConnectionOfMetric (I := I) g₂) y
                (Vslots a y)) (V y))))) := by
    funext y
    simp only [Finset.sum_apply]
  have hf1 : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun y : M => ∑ a : Fin s, (S y) (Function.update (fun b : Fin s => Vslots b y) a
        (covDerivConnectionDifference (I := I) g₂ g₁
          (fun z => W z) (fun z => V z) (fun z => Vslots a z) y))) x := by
    rw [show (fun y : M => ∑ a : Fin s, (S y) (Function.update (fun b : Fin s => Vslots b y) a
          (covDerivConnectionDifference (I := I) g₂ g₁
            (fun z => W z) (fun z => V z) (fun z => Vslots a z) y)))
        = Finset.univ.sum (fun a : Fin s => fun y : M => (S y)
            (Function.update (fun b : Fin s => Vslots b y) a
              (covDerivConnectionDifference (I := I) g₂ g₁
                (fun z => W z) (fun z => V z) (fun z => Vslots a z) y))) from by
        funext y; simp only [Finset.sum_apply]]
    exact mdiffAt_finset_sum (I := I) Finset.univ _ (fun a _ => hT1 a)
  have hf2 : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun y : M => ∑ a : Fin s, covStep (I := I) g₂ s S y
        (Fin.cons (W y) (Function.update (fun b : Fin s => Vslots b y) a
          ((CovariantDerivative.difference
              (leviCivitaConnectionOfMetric (I := I) g₁)
              (leviCivitaConnectionOfMetric (I := I) g₂) y
              (Vslots a y)) (V y))))) x := by
    rw [hsum2]
    exact mdiffAt_finset_sum (I := I) Finset.univ _ (fun a _ => hT2 a)
  have e1 : mvfderiv (I := I)
        (fun y : M => -∑ a : Fin s, (S y) (Function.update (fun b : Fin s => Vslots b y) a
          (covDerivConnectionDifference (I := I) g₂ g₁
            (fun z => W z) (fun z => V z) (fun z => Vslots a z) y))) x (U x)
      = -∑ a : Fin s, mvfderiv (I := I)
          (fun y : M => (S y) (Function.update (fun b : Fin s => Vslots b y) a
            (covDerivConnectionDifference (I := I) g₂ g₁
              (fun z => W z) (fun z => V z) (fun z => Vslots a z) y))) x (U x) := by
    have hneg : (fun y : M => -∑ a : Fin s, (S y) (Function.update (fun b : Fin s => Vslots b y) a
          (covDerivConnectionDifference (I := I) g₂ g₁
            (fun z => W z) (fun z => V z) (fun z => Vslots a z) y)))
        = (fun y : M => -(Finset.univ.sum (fun a : Fin s => fun y' : M => (S y')
            (Function.update (fun b : Fin s => Vslots b y') a
              (covDerivConnectionDifference (I := I) g₂ g₁
                (fun z => W z) (fun z => V z) (fun z => Vslots a z) y'))) y)) := by
      funext y
      simp only [Finset.sum_apply]
    rw [hneg,
      mvfderiv_neg_at (I := I) (U x)
        (mdiffAt_finset_sum (I := I) Finset.univ _ (fun a _ => hT1 a)),
      mvfderiv_finset_sum_at (I := I) Finset.univ _ (U x) (fun a _ => hT1 a)]
  have e2 : mvfderiv (I := I)
        (fun y : M => ∑ a : Fin s, covStep (I := I) g₂ s S y
          (Fin.cons (W y) (Function.update (fun b : Fin s => Vslots b y) a
            ((CovariantDerivative.difference
                (leviCivitaConnectionOfMetric (I := I) g₁)
                (leviCivitaConnectionOfMetric (I := I) g₂) y
                (Vslots a y)) (V y))))) x (U x)
      = ∑ a : Fin s, mvfderiv (I := I)
          (fun y : M => covStep (I := I) g₂ s S y
            (Fin.cons (W y) (Function.update (fun b : Fin s => Vslots b y) a
              ((CovariantDerivative.difference
                  (leviCivitaConnectionOfMetric (I := I) g₁)
                  (leviCivitaConnectionOfMetric (I := I) g₂) y
                  (Vslots a y)) (V y))))) x (U x) := by
    rw [hsum2, mvfderiv_finset_sum_at (I := I) Finset.univ _ (U x) (fun a _ => hT2 a)]
  have hsub : mvfderiv (I := I)
        (fun y : M =>
          (-∑ a : Fin s, (S y) (Function.update (fun b : Fin s => Vslots b y) a
              (covDerivConnectionDifference (I := I) g₂ g₁
                (fun z => W z) (fun z => V z) (fun z => Vslots a z) y)))
          - ∑ a : Fin s, covStep (I := I) g₂ s S y
              (Fin.cons (W y) (Function.update (fun b : Fin s => Vslots b y) a
                ((CovariantDerivative.difference
                    (leviCivitaConnectionOfMetric (I := I) g₁)
                    (leviCivitaConnectionOfMetric (I := I) g₂) y
                    (Vslots a y)) (V y))))) x (U x)
      = mvfderiv (I := I)
            (fun y : M => -∑ a : Fin s, (S y) (Function.update (fun b : Fin s => Vslots b y) a
              (covDerivConnectionDifference (I := I) g₂ g₁
                (fun z => W z) (fun z => V z) (fun z => Vslots a z) y))) x (U x)
        - mvfderiv (I := I)
            (fun y : M => ∑ a : Fin s, covStep (I := I) g₂ s S y
              (Fin.cons (W y) (Function.update (fun b : Fin s => Vslots b y) a
                ((CovariantDerivative.difference
                    (leviCivitaConnectionOfMetric (I := I) g₁)
                    (leviCivitaConnectionOfMetric (I := I) g₂) y
                    (Vslots a y)) (V y))))) x (U x) :=
    mvfderiv_sub_at (I := I) (U x) hf1.neg hf2
  rw [hsub, e1, e2]

open DifferentialGeometry.Integral.Connection in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem covStep2_diffStep_OCsplit
    (g₁ g₂ : SmoothRiemannianMetric I M) (s : Nat)
    (S : Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s)
    (U W V : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (Vslots : Fin s -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (x : M) :
    (∑ q : Fin (s + 2),
        (covStep (I := I) g₂ (s + 1) (diffStep (I := I) g₁ g₂ s S)) x
          (Function.update
            (fun b : Fin (s + 2) =>
              (Fin.cons W (Fin.cons V Vslots) :
                Fin (s + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
                  (TangentSpace I : M -> Type _)) b x) q
            ((leviCivitaConnectionOfMetric (I := I) g₂
                (fun y : M =>
                  (Fin.cons W (Fin.cons V Vslots) :
                    Fin (s + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
                      (TangentSpace I : M -> Type _)) q y) x) (U x))))
      = (covStep (I := I) g₂ (s + 1) (diffStep (I := I) g₁ g₂ s S)) x
          (Fin.cons ((leviCivitaConnectionOfMetric (I := I) g₂ (fun z => W z) x) (U x))
            (Fin.cons (V x) (fun a : Fin s => Vslots a x)))
        + (covStep (I := I) g₂ (s + 1) (diffStep (I := I) g₁ g₂ s S)) x
            (Fin.cons (W x)
              (Fin.cons ((leviCivitaConnectionOfMetric (I := I) g₂ (fun z => V z) x) (U x))
                (fun a : Fin s => Vslots a x)))
        + ∑ a₀ : Fin s, (covStep (I := I) g₂ (s + 1) (diffStep (I := I) g₁ g₂ s S)) x
            (Fin.cons (W x)
              (Fin.cons (V x)
                (Function.update (fun b : Fin s => Vslots b x) a₀
                  ((leviCivitaConnectionOfMetric (I := I) g₂ (fun z => Vslots a₀ z) x) (U x))))) := by
  classical
  set RR : Fin (s + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _) := Fin.cons W (Fin.cons V Vslots) with hRRdef
  have hRR0 : (fun y : M => (RR 0) y) = (fun y : M => W y) := by
    simp only [hRRdef, Fin.cons_zero]
  have hRR1 : (fun y : M => (RR (Fin.succ 0)) y) = (fun y : M => V y) := by
    simp only [hRRdef, Fin.cons_succ, Fin.cons_zero]
  have hRRss : ∀ a₀ : Fin s, (fun y : M => (RR (Fin.succ (Fin.succ a₀))) y)
      = (fun y : M => Vslots a₀ y) := by
    intro a₀
    simp only [hRRdef, Fin.cons_succ]
  have hRRptx : (fun b : Fin (s + 2) => (RR b) x)
      = Fin.cons (W x) (Fin.cons (V x) (fun a : Fin s => Vslots a x)) := by
    funext b
    refine Fin.cases ?_ (fun i => ?_) b
    · simp only [hRRdef, Fin.cons_zero]
    · refine Fin.cases ?_ (fun j => ?_) i <;> simp only [hRRdef, Fin.cons_succ, Fin.cons_zero]
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [hRRptx, hRR0, hRR1, hRRss, Fin.update_cons_zero, ← Fin.cons_update]
  ring

open DifferentialGeometry.Integral.Connection in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem covStep2_OC_q0
    (g₁ g₂ : SmoothRiemannianMetric I M) (s : Nat)
    (S : Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s)
    (U W V : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (Vslots : Fin s -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (x : M) :
    (covStep (I := I) g₂ (s + 1) (diffStep (I := I) g₁ g₂ s S)) x
        (Fin.cons ((leviCivitaConnectionOfMetric (I := I) g₂ (fun z => W z) x) (U x))
          (Fin.cons (V x) (fun a : Fin s => Vslots a x)))
      = (-∑ a : Fin s, (S x) (Function.update (fun b : Fin s => Vslots b x) a
            (covDerivConnectionDifference (I := I) g₂ g₁
              (covApply (LeviCivita (I := I) g₂) (fun z => U z) (fun z => W z))
              (fun z => V z) (fun z => Vslots a z) x)))
        - ∑ a : Fin s, covStep (I := I) g₂ s S x
            (Fin.cons ((leviCivitaConnectionOfMetric (I := I) g₂ (fun z => W z) x) (U x))
              (Function.update (fun b : Fin s => Vslots b x) a
                ((CovariantDerivative.difference
                    (leviCivitaConnectionOfMetric (I := I) g₁)
                    (leviCivitaConnectionOfMetric (I := I) g₂) x
                    (Vslots a x)) (V x)))) := by
  classical
  have : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  have : IsManifold I 2 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  have : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
    change IsManifold I ∞ M
    infer_instance
  have : IsManifold I (1 + 1) M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by decide : ((1 : WithTop ℕ∞) + 1) ≤ ∞)
  have : ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I :=
    TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := 1)
  have hcov₂ : CovariantDerivative.ContMDiffCovariantDerivative
      (LeviCivita (I := I) g₂) (∞ : WithTop ℕ∞) :=
    leviCivitaConnectionOfMetric_contMDiffCovariantDerivative (I := I) g₂
  have hcast : ∀ (P : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _)),
      ContMDiff I (I.prod 𝓘(ℝ, E)) ((∞ : WithTop ℕ∞) + 1) (T% (fun b => P b)) := by
    intro P
    rw [show ((∞ : WithTop ℕ∞) + 1) = (∞ : WithTop ℕ∞) from by rw [ENat.coe_top_add_one]]
    exact P.contMDiff
  set NW : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    ContMDiffSection.mk
      (covApply (LeviCivita (I := I) g₂) (fun z => U z) (fun z => W z))
      (contMDiffOn_univ.mp
        (covApply_contMDiffOn (cov := LeviCivita (I := I) g₂) U.contMDiff (hcast W))) with hNWdef
  have hNWfun : (fun y : M => NW y)
      = covApply (LeviCivita (I := I) g₂) (fun z => U z) (fun z => W z) := by
    rw [hNWdef]
    rfl
  have hNWx : NW x = (leviCivitaConnectionOfMetric (I := I) g₂ (fun z => W z) x) (U x) := by
    rw [hNWdef]
    rfl
  have key := diffStep_leibniz_eval (I := I) g₁ g₂ s S NW V Vslots x
  rw [hNWfun, hNWx] at key
  exact key

open DifferentialGeometry.Integral.Connection in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem covStep2_OC_q1
    (g₁ g₂ : SmoothRiemannianMetric I M) (s : Nat)
    (S : Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s)
    (U W V : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (Vslots : Fin s -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (x : M) :
    (covStep (I := I) g₂ (s + 1) (diffStep (I := I) g₁ g₂ s S)) x
        (Fin.cons (W x)
          (Fin.cons ((leviCivitaConnectionOfMetric (I := I) g₂ (fun z => V z) x) (U x))
            (fun a : Fin s => Vslots a x)))
      = (-∑ a : Fin s, (S x) (Function.update (fun b : Fin s => Vslots b x) a
            (covDerivConnectionDifference (I := I) g₂ g₁ (fun z => W z)
              (covApply (LeviCivita (I := I) g₂) (fun z => U z) (fun z => V z))
              (fun z => Vslots a z) x)))
        - ∑ a : Fin s, covStep (I := I) g₂ s S x
            (Fin.cons (W x)
              (Function.update (fun b : Fin s => Vslots b x) a
                ((CovariantDerivative.difference
                    (leviCivitaConnectionOfMetric (I := I) g₁)
                    (leviCivitaConnectionOfMetric (I := I) g₂) x
                    (Vslots a x))
                  ((leviCivitaConnectionOfMetric (I := I) g₂ (fun z => V z) x) (U x))))) := by
  classical
  have : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  have : IsManifold I 2 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  have : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
    change IsManifold I ∞ M
    infer_instance
  have : IsManifold I (1 + 1) M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by decide : ((1 : WithTop ℕ∞) + 1) ≤ ∞)
  have : ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I :=
    TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := 1)
  have hcov₂ : CovariantDerivative.ContMDiffCovariantDerivative
      (LeviCivita (I := I) g₂) (∞ : WithTop ℕ∞) :=
    leviCivitaConnectionOfMetric_contMDiffCovariantDerivative (I := I) g₂
  have hcast : ∀ (P : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _)),
      ContMDiff I (I.prod 𝓘(ℝ, E)) ((∞ : WithTop ℕ∞) + 1) (T% (fun b => P b)) := by
    intro P
    rw [show ((∞ : WithTop ℕ∞) + 1) = (∞ : WithTop ℕ∞) from by rw [ENat.coe_top_add_one]]
    exact P.contMDiff
  set NV : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    ContMDiffSection.mk
      (covApply (LeviCivita (I := I) g₂) (fun z => U z) (fun z => V z))
      (contMDiffOn_univ.mp
        (covApply_contMDiffOn (cov := LeviCivita (I := I) g₂) U.contMDiff (hcast V))) with hNVdef
  have hNVfun : (fun y : M => NV y)
      = covApply (LeviCivita (I := I) g₂) (fun z => U z) (fun z => V z) := by
    rw [hNVdef]
    rfl
  have hNVx : NV x = (leviCivitaConnectionOfMetric (I := I) g₂ (fun z => V z) x) (U x) := by
    rw [hNVdef]
    rfl
  have key := diffStep_leibniz_eval (I := I) g₁ g₂ s S W NV Vslots x
  rw [hNVfun, hNVx] at key
  exact key

open DifferentialGeometry.Integral.Connection in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem covStep2_OC_int
    (g₁ g₂ : SmoothRiemannianMetric I M) (s : Nat)
    (S : Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s)
    (U W V : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (Vslots : Fin s -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (a₀ : Fin s) (x : M) :
    (covStep (I := I) g₂ (s + 1) (diffStep (I := I) g₁ g₂ s S)) x
        (Fin.cons (W x)
          (Fin.cons (V x)
            (Function.update (fun b : Fin s => Vslots b x) a₀
              ((leviCivitaConnectionOfMetric (I := I) g₂ (fun z => Vslots a₀ z) x) (U x)))))
      = (-((S x) (Function.update (fun b : Fin s => Vslots b x) a₀
              (covDerivConnectionDifference (I := I) g₂ g₁ (fun z => W z) (fun z => V z)
                (covApply (LeviCivita (I := I) g₂) (fun z => U z) (fun z => Vslots a₀ z)) x))
            + ∑ a ∈ Finset.univ.erase a₀, (S x) (Function.update
                (Function.update (fun c : Fin s => Vslots c x) a₀
                  ((leviCivitaConnectionOfMetric (I := I) g₂ (fun z => Vslots a₀ z) x) (U x))) a
                (covDerivConnectionDifference (I := I) g₂ g₁
                  (fun z => W z) (fun z => V z) (fun z => Vslots a z) x))))
        - (covStep (I := I) g₂ s S x
              (Fin.cons (W x) (Function.update (fun b : Fin s => Vslots b x) a₀
                ((CovariantDerivative.difference
                    (leviCivitaConnectionOfMetric (I := I) g₁)
                    (leviCivitaConnectionOfMetric (I := I) g₂) x
                    ((leviCivitaConnectionOfMetric (I := I) g₂ (fun z => Vslots a₀ z) x) (U x)))
                  (V x))))
            + ∑ a ∈ Finset.univ.erase a₀, covStep (I := I) g₂ s S x
                (Fin.cons (W x) (Function.update
                  (Function.update (fun c : Fin s => Vslots c x) a₀
                    ((leviCivitaConnectionOfMetric (I := I) g₂ (fun z => Vslots a₀ z) x) (U x))) a
                  ((CovariantDerivative.difference
                      (leviCivitaConnectionOfMetric (I := I) g₁)
                      (leviCivitaConnectionOfMetric (I := I) g₂) x
                      (Vslots a x)) (V x))))) := by
  classical
  have : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  have : IsManifold I 2 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  have : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
    change IsManifold I ∞ M
    infer_instance
  have : IsManifold I (1 + 1) M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by decide : ((1 : WithTop ℕ∞) + 1) ≤ ∞)
  have : ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I :=
    TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := 1)
  have hcov₂ : CovariantDerivative.ContMDiffCovariantDerivative
      (LeviCivita (I := I) g₂) (∞ : WithTop ℕ∞) :=
    leviCivitaConnectionOfMetric_contMDiffCovariantDerivative (I := I) g₂
  have hcast : ∀ (P : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _)),
      ContMDiff I (I.prod 𝓘(ℝ, E)) ((∞ : WithTop ℕ∞) + 1) (T% (fun b => P b)) := by
    intro P
    rw [show ((∞ : WithTop ℕ∞) + 1) = (∞ : WithTop ℕ∞) from by rw [ENat.coe_top_add_one]]
    exact P.contMDiff
  set NS : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    ContMDiffSection.mk
      (covApply (LeviCivita (I := I) g₂) (fun z => U z) (fun z => Vslots a₀ z))
      (contMDiffOn_univ.mp
        (covApply_contMDiffOn (cov := LeviCivita (I := I) g₂) U.contMDiff
          (hcast (Vslots a₀)))) with hNSdef
  set σ : Fin s → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    Function.update Vslots a₀ NS with hσdef
  have hNSx : NS x
      = (leviCivitaConnectionOfMetric (I := I) g₂ (fun z => Vslots a₀ z) x) (U x) := by
    rw [hNSdef]
    rfl
  have hσx : (fun b : Fin s => σ b x)
      = Function.update (fun b : Fin s => Vslots b x) a₀
          ((leviCivitaConnectionOfMetric (I := I) g₂ (fun z => Vslots a₀ z) x) (U x)) := by
    funext b
    rcases eq_or_ne b a₀ with hb | hb
    · subst hb
      simp only [hσdef, Function.update_self]
      exact hNSx
    · simp only [hσdef, Function.update_of_ne hb]
  have hσa₀ : (fun y : M => σ a₀ y)
      = covApply (LeviCivita (I := I) g₂) (fun z => U z) (fun z => Vslots a₀ z) := by
    funext y
    simp only [hσdef, Function.update_self]
    rw [hNSdef]
    rfl
  have hσa₀x : σ a₀ x
      = (leviCivitaConnectionOfMetric (I := I) g₂ (fun z => Vslots a₀ z) x) (U x) := by
    simp only [hσdef, Function.update_self]
    exact hNSx
  have key := diffStep_leibniz_eval (I := I) g₁ g₂ s S W V σ x
  rw [hσx] at key
  rw [key]
  have hs1 : (∑ a : Fin s, (S x) (Function.update
        (Function.update (fun b : Fin s => Vslots b x) a₀
          ((leviCivitaConnectionOfMetric (I := I) g₂ (fun z => Vslots a₀ z) x) (U x))) a
        (covDerivConnectionDifference (I := I) g₂ g₁
          (fun y => W y) (fun y => V y) (fun y => σ a y) x)))
      = (S x) (Function.update (fun b : Fin s => Vslots b x) a₀
            (covDerivConnectionDifference (I := I) g₂ g₁ (fun z => W z) (fun z => V z)
              (covApply (LeviCivita (I := I) g₂) (fun z => U z) (fun z => Vslots a₀ z)) x))
        + ∑ a ∈ Finset.univ.erase a₀, (S x) (Function.update
            (Function.update (fun c : Fin s => Vslots c x) a₀
              ((leviCivitaConnectionOfMetric (I := I) g₂ (fun z => Vslots a₀ z) x) (U x))) a
            (covDerivConnectionDifference (I := I) g₂ g₁
              (fun z => W z) (fun z => V z) (fun z => Vslots a z) x)) := by
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ a₀), hσa₀,
      Function.update_idem]
    refine congrArg _ (Finset.sum_congr rfl (fun a ha => ?_))
    rw [show (fun y : M => σ a y) = (fun y : M => Vslots a y) from by
      funext y
      simp only [hσdef, Function.update_of_ne (Finset.ne_of_mem_erase ha)]]
  have hs2 : (∑ a : Fin s, covStep (I := I) g₂ s S x
        (Fin.cons (W x) (Function.update
          (Function.update (fun b : Fin s => Vslots b x) a₀
            ((leviCivitaConnectionOfMetric (I := I) g₂ (fun z => Vslots a₀ z) x) (U x))) a
          ((CovariantDerivative.difference
              (leviCivitaConnectionOfMetric (I := I) g₁)
              (leviCivitaConnectionOfMetric (I := I) g₂) x
              (σ a x)) (V x)))))
      = covStep (I := I) g₂ s S x
            (Fin.cons (W x) (Function.update (fun b : Fin s => Vslots b x) a₀
              ((CovariantDerivative.difference
                  (leviCivitaConnectionOfMetric (I := I) g₁)
                  (leviCivitaConnectionOfMetric (I := I) g₂) x
                  ((leviCivitaConnectionOfMetric (I := I) g₂ (fun z => Vslots a₀ z) x) (U x)))
                (V x))))
        + ∑ a ∈ Finset.univ.erase a₀, covStep (I := I) g₂ s S x
            (Fin.cons (W x) (Function.update
              (Function.update (fun c : Fin s => Vslots c x) a₀
                ((leviCivitaConnectionOfMetric (I := I) g₂ (fun z => Vslots a₀ z) x) (U x))) a
              ((CovariantDerivative.difference
                  (leviCivitaConnectionOfMetric (I := I) g₁)
                  (leviCivitaConnectionOfMetric (I := I) g₂) x
                  (Vslots a x)) (V x)))) := by
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ a₀), hσa₀x,
      Function.update_idem]
    refine congrArg _ (Finset.sum_congr rfl (fun a ha => ?_))
    rw [show σ a x = Vslots a x from by
      simp only [hσdef, Function.update_of_ne (Finset.ne_of_mem_erase ha)]]
  rw [hs1, hs2]

open DifferentialGeometry.Integral.Connection in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem covStep2_pieceB_eval
    (g₁ g₂ : SmoothRiemannianMetric I M) (s : Nat)
    (S : Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s)
    (U W V : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (Vslots : Fin s -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (x : M) :
    covStep (I := I) g₂ (s + 2)
        (diffStep (I := I) g₁ g₂ (s + 1) (covStep (I := I) g₂ s S)) x
        (Fin.cons (U x) (Fin.cons (W x) (Fin.cons (V x) (fun a : Fin s => Vslots a x))))
      = (-∑ j : Fin (s + 1), (covStep (I := I) g₂ s S x)
            (Function.update (Fin.cons (V x) (fun b : Fin s => Vslots b x)) j
              (covDerivConnectionDifference (I := I) g₂ g₁ (fun z => U z) (fun z => W z)
                (fun z => (Fin.cons V Vslots :
                  Fin (s + 1) → ContMDiffSection I E (∞ : WithTop ℕ∞)
                    (TangentSpace I : M -> Type _)) j z) x)))
        - ∑ j : Fin (s + 1), covStep (I := I) g₂ (s + 1) (covStep (I := I) g₂ s S) x
            (Fin.cons (U x)
              (Function.update (Fin.cons (V x) (fun b : Fin s => Vslots b x)) j
                ((CovariantDerivative.difference
                    (leviCivitaConnectionOfMetric (I := I) g₁)
                    (leviCivitaConnectionOfMetric (I := I) g₂) x
                    ((Fin.cons V Vslots :
                      Fin (s + 1) → ContMDiffSection I E (∞ : WithTop ℕ∞)
                        (TangentSpace I : M -> Type _)) j x)) (W x)))) := by
  classical
  set VV : Fin (s + 1) → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _) := Fin.cons V Vslots with hVVdef
  have hVVx : (fun b : Fin (s + 1) => VV b x)
      = Fin.cons (V x) (fun b : Fin s => Vslots b x) := by
    funext b
    refine Fin.cases ?_ (fun i => ?_) b
    · simp only [hVVdef, Fin.cons_zero]
    · simp only [hVVdef, Fin.cons_succ]
  have key := diffStep_leibniz_eval (I := I) g₁ g₂ (s + 1)
    (covStep (I := I) g₂ s S) U W VV x
  rw [hVVx] at key
  exact key

open DifferentialGeometry.Integral.Connection in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem covStep2_diffStep_eval
    (g₁ g₂ : SmoothRiemannianMetric I M) (s : Nat)
    (S : Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s)
    (U W V : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (Vslots : Fin s -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (x : M) :
    covStep (I := I) g₂ (s + 2)
        (covStep (I := I) g₂ (s + 1) (diffStep (I := I) g₁ g₂ s S)) x
        (Fin.cons (U x) (Fin.cons (W x) (Fin.cons (V x) (fun a : Fin s => Vslots a x))))
      = (-∑ a : Fin s, (S x) (Function.update (fun b : Fin s => Vslots b x) a
            (covDerivConnectionDifference2 (I := I) g₂ g₁
              (fun z => U z) (fun z => W z) (fun z => V z) (fun z => Vslots a z) x)))
        - ∑ a : Fin s, covStep (I := I) g₂ s S x
            (Fin.cons (U x) (Function.update (fun b : Fin s => Vslots b x) a
              (covDerivConnectionDifference (I := I) g₂ g₁
                (fun z => W z) (fun z => V z) (fun z => Vslots a z) x)))
        - ∑ a : Fin s, covStep (I := I) g₂ s S x
            (Fin.cons (W x) (Function.update (fun b : Fin s => Vslots b x) a
              (covDerivConnectionDifference (I := I) g₂ g₁
                (fun z => U z) (fun z => V z) (fun z => Vslots a z) x)))
        - ∑ a : Fin s, covStep (I := I) g₂ (s + 1) (covStep (I := I) g₂ s S) x
            (Fin.cons (U x) (Fin.cons (W x) (Function.update (fun b : Fin s => Vslots b x) a
              ((CovariantDerivative.difference
                  (leviCivitaConnectionOfMetric (I := I) g₁)
                  (leviCivitaConnectionOfMetric (I := I) g₂) x
                  (Vslots a x)) (V x))))) := by
  classical
  have hsplitS : (∑ a : Fin s, (S x) (Function.update (fun b : Fin s => Vslots b x) a
        (covDerivConnectionDifference2 (I := I) g₂ g₁
            (fun z => U z) (fun z => W z) (fun z => V z) (fun z => Vslots a z) x
          + covDerivConnectionDifference (I := I) g₂ g₁
              (covApply (LeviCivita (I := I) g₂) (fun z => U z) (fun z => W z))
              (fun z => V z) (fun z => Vslots a z) x
          + covDerivConnectionDifference (I := I) g₂ g₁ (fun z => W z)
              (covApply (LeviCivita (I := I) g₂) (fun z => U z) (fun z => V z))
              (fun z => Vslots a z) x
          + covDerivConnectionDifference (I := I) g₂ g₁ (fun z => W z) (fun z => V z)
              (covApply (LeviCivita (I := I) g₂) (fun z => U z) (fun z => Vslots a z)) x)))
      = (∑ a : Fin s, (S x) (Function.update (fun b : Fin s => Vslots b x) a
            (covDerivConnectionDifference2 (I := I) g₂ g₁
              (fun z => U z) (fun z => W z) (fun z => V z) (fun z => Vslots a z) x)))
        + (∑ a : Fin s, (S x) (Function.update (fun b : Fin s => Vslots b x) a
            (covDerivConnectionDifference (I := I) g₂ g₁
              (covApply (LeviCivita (I := I) g₂) (fun z => U z) (fun z => W z))
              (fun z => V z) (fun z => Vslots a z) x)))
        + (∑ a : Fin s, (S x) (Function.update (fun b : Fin s => Vslots b x) a
            (covDerivConnectionDifference (I := I) g₂ g₁ (fun z => W z)
              (covApply (LeviCivita (I := I) g₂) (fun z => U z) (fun z => V z))
              (fun z => Vslots a z) x)))
        + (∑ a : Fin s, (S x) (Function.update (fun b : Fin s => Vslots b x) a
            (covDerivConnectionDifference (I := I) g₂ g₁ (fun z => W z) (fun z => V z)
              (covApply (LeviCivita (I := I) g₂) (fun z => U z) (fun z => Vslots a z)) x))) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Tensor0SBundle.Tensor0SSpace.map_update_add,
      Tensor0SBundle.Tensor0SSpace.map_update_add,
      Tensor0SBundle.Tensor0SSpace.map_update_add]
  have hsplitD : (∑ a : Fin s, covStep (I := I) g₂ s S x
        (Fin.cons (W x) (Function.update (fun b : Fin s => Vslots b x) a
          (covDerivConnectionDifference (I := I) g₂ g₁
              (fun z => U z) (fun z => V z) (fun z => Vslots a z) x
            + (CovariantDerivative.difference
                (leviCivitaConnectionOfMetric (I := I) g₁)
                (leviCivitaConnectionOfMetric (I := I) g₂) x (Vslots a x))
                ((leviCivitaConnectionOfMetric (I := I) g₂ (fun y : M => V y) x) (U x))
            + (CovariantDerivative.difference
                (leviCivitaConnectionOfMetric (I := I) g₁)
                (leviCivitaConnectionOfMetric (I := I) g₂) x
                ((leviCivitaConnectionOfMetric (I := I) g₂ (fun y : M => Vslots a y) x) (U x)))
                (V x)))))
      = (∑ a : Fin s, covStep (I := I) g₂ s S x
            (Fin.cons (W x) (Function.update (fun b : Fin s => Vslots b x) a
              (covDerivConnectionDifference (I := I) g₂ g₁
                (fun z => U z) (fun z => V z) (fun z => Vslots a z) x))))
        + (∑ a : Fin s, covStep (I := I) g₂ s S x
            (Fin.cons (W x) (Function.update (fun b : Fin s => Vslots b x) a
              ((CovariantDerivative.difference
                  (leviCivitaConnectionOfMetric (I := I) g₁)
                  (leviCivitaConnectionOfMetric (I := I) g₂) x (Vslots a x))
                ((leviCivitaConnectionOfMetric (I := I) g₂ (fun y : M => V y) x) (U x))))))
        + (∑ a : Fin s, covStep (I := I) g₂ s S x
            (Fin.cons (W x) (Function.update (fun b : Fin s => Vslots b x) a
              ((CovariantDerivative.difference
                  (leviCivitaConnectionOfMetric (I := I) g₁)
                  (leviCivitaConnectionOfMetric (I := I) g₂) x
                  ((leviCivitaConnectionOfMetric (I := I) g₂ (fun y : M => Vslots a y) x) (U x)))
                (V x))))) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Fin.cons_update, Tensor0SBundle.Tensor0SSpace.map_update_add,
      Tensor0SBundle.Tensor0SSpace.map_update_add]
    simp only [← Fin.cons_update]
  have hFub1 : (∑ a₀ : Fin s, ∑ a ∈ Finset.univ.erase a₀, (S x) (Function.update
        (Function.update (fun c : Fin s => Vslots c x) a₀
          ((leviCivitaConnectionOfMetric (I := I) g₂ (fun z => Vslots a₀ z) x) (U x))) a
        (covDerivConnectionDifference (I := I) g₂ g₁
          (fun z => W z) (fun z => V z) (fun z => Vslots a z) x)))
      = ∑ a : Fin s, ∑ b ∈ Finset.univ.erase a, (S x) (Function.update
          (Function.update (fun c : Fin s => Vslots c x) a
            (covDerivConnectionDifference (I := I) g₂ g₁
              (fun z => W z) (fun z => V z) (fun z => Vslots a z) x)) b
          ((leviCivitaConnectionOfMetric (I := I) g₂ (fun y : M => Vslots b y) x) (U x))) := by
    rw [Finset.sum_comm' (s := Finset.univ) (t := fun a₀ : Fin s => Finset.univ.erase a₀)
      (t' := Finset.univ) (s' := fun a : Fin s => Finset.univ.erase a)
      (h := fun p q => by
        simp only [Finset.mem_univ, Finset.mem_erase, true_and, and_true]
        exact ⟨Ne.symm, Ne.symm⟩)]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun a₀ ha₀ => ?_))
    rw [Function.update_comm (Finset.ne_of_mem_erase ha₀)]
  have hFub2 : (∑ a₀ : Fin s, ∑ a ∈ Finset.univ.erase a₀, covStep (I := I) g₂ s S x
        (Fin.cons (W x) (Function.update
          (Function.update (fun c : Fin s => Vslots c x) a₀
            ((leviCivitaConnectionOfMetric (I := I) g₂ (fun z => Vslots a₀ z) x) (U x))) a
          ((CovariantDerivative.difference
              (leviCivitaConnectionOfMetric (I := I) g₁)
              (leviCivitaConnectionOfMetric (I := I) g₂) x
              (Vslots a x)) (V x)))))
      = ∑ a : Fin s, ∑ b ∈ Finset.univ.erase a, covStep (I := I) g₂ s S x
          (Fin.cons (W x) (Function.update
            (Function.update (fun c : Fin s => Vslots c x) a
              ((CovariantDerivative.difference
                  (leviCivitaConnectionOfMetric (I := I) g₁)
                  (leviCivitaConnectionOfMetric (I := I) g₂) x
                  (Vslots a x)) (V x))) b
            ((leviCivitaConnectionOfMetric (I := I) g₂ (fun y : M => Vslots b y) x) (U x)))) := by
    rw [Finset.sum_comm' (s := Finset.univ) (t := fun a₀ : Fin s => Finset.univ.erase a₀)
      (t' := Finset.univ) (s' := fun a : Fin s => Finset.univ.erase a)
      (h := fun p q => by
        simp only [Finset.mem_univ, Finset.mem_erase, true_and, and_true]
        exact ⟨Ne.symm, Ne.symm⟩)]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun a₀ ha₀ => ?_))
    rw [Function.update_comm (Finset.ne_of_mem_erase ha₀)]
  rw [covStep2_diffStep_peel (I := I) g₁ g₂ s S U W V Vslots x,
    covStep2_diffStep_split (I := I) g₁ g₂ s S U W V Vslots x,
    covStep2_diffStep_OCsplit (I := I) g₁ g₂ s S U W V Vslots x,
    covStep2_OC_q0 (I := I) g₁ g₂ s S U W V Vslots x,
    covStep2_OC_q1 (I := I) g₁ g₂ s S U W V Vslots x]
  simp only [covStep2_OC_int (I := I) g₁ g₂ s S U W V Vslots,
    covStep2_diffStep_branch1 (I := I) g₁ g₂ s S U W V Vslots,
    covStep2_diffStep_branch2 (I := I) g₁ g₂ s S U W V Vslots]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  rw [hsplitS, hsplitD, hFub1, hFub2]
  abel

open DifferentialGeometry.Integral.Connection in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem diffStep_rank0_eq_zero
    (g₁ g₂ : SmoothRiemannianMetric I M)
    (S : Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 0) :
    diffStep (I := I) g₁ g₂ 0 S = 0 := by
  refine DFunLike.ext _ _ (fun x => ?_)
  refine tensor0SSpace_ext 1 x (fun v => ?_)
  have hev := diffStep_eval (I := I) g₁ g₂ 0 S x (v 0) (Fin.tail v)
  rw [Fin.cons_self_tail] at hev
  rw [hev]
  simp

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem covStep2_mixedComm_split
    (g₁ g₂ : SmoothRiemannianMetric I M) (s : ℕ)
    (S : Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s) :
    covStep (I := I) g₂ (s + 2)
        (covStep (I := I) g₂ (s + 1) (covStep (I := I) g₁ s S)
          - covStep (I := I) g₁ (s + 1) (covStep (I := I) g₂ s S))
      = covStep (I := I) g₂ (s + 2)
          (covStep (I := I) g₂ (s + 1) (diffStep (I := I) g₁ g₂ s S))
        - covStep (I := I) g₂ (s + 2)
          (diffStep (I := I) g₁ g₂ (s + 1) (covStep (I := I) g₂ s S)) := by
  rw [← covStep_sub]
  congr 1
  rw [diffStep_leibniz (I := I) g₁ g₂ s S]
  abel

open DifferentialGeometry.Integral.Connection in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem covStep2_mixedComm_eval_sub
    (g₁ g₂ : SmoothRiemannianMetric I M) (s : ℕ)
    (S : Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s)
    (U W V : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (Vslots : Fin s -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (x : M) :
    covStep (I := I) g₂ (s + 2)
        (covStep (I := I) g₂ (s + 1) (covStep (I := I) g₁ s S)
          - covStep (I := I) g₁ (s + 1) (covStep (I := I) g₂ s S)) x
        (Fin.cons (U x) (Fin.cons (W x) (Fin.cons (V x) (fun a : Fin s => Vslots a x))))
      = covStep (I := I) g₂ (s + 2)
            (covStep (I := I) g₂ (s + 1) (diffStep (I := I) g₁ g₂ s S)) x
            (Fin.cons (U x) (Fin.cons (W x) (Fin.cons (V x) (fun a : Fin s => Vslots a x))))
        - covStep (I := I) g₂ (s + 2)
            (diffStep (I := I) g₁ g₂ (s + 1) (covStep (I := I) g₂ s S)) x
            (Fin.cons (U x) (Fin.cons (W x) (Fin.cons (V x) (fun a : Fin s => Vslots a x)))) := by
  rw [covStep2_mixedComm_split (I := I) g₁ g₂ s S, ContMDiffSection.coe_sub, Pi.sub_apply,
    Tensor0SSpace.sub_apply]

open DifferentialGeometry.Integral.Connection in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem covStep2_mixedComm_eval
    (g₁ g₂ : SmoothRiemannianMetric I M) (s : ℕ)
    (S : Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s)
    (U W V : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (Vslots : Fin s -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (x : M) :
    covStep (I := I) g₂ (s + 2)
        (covStep (I := I) g₂ (s + 1) (covStep (I := I) g₁ s S)
          - covStep (I := I) g₁ (s + 1) (covStep (I := I) g₂ s S)) x
        (Fin.cons (U x) (Fin.cons (W x) (Fin.cons (V x) (fun a : Fin s => Vslots a x))))
      = (-∑ a : Fin s, (S x) (Function.update (fun b : Fin s => Vslots b x) a
            (covDerivConnectionDifference2 (I := I) g₂ g₁
              (fun z => U z) (fun z => W z) (fun z => V z) (fun z => Vslots a z) x)))
        - ∑ a : Fin s, covStep (I := I) g₂ s S x
            (Fin.cons (U x) (Function.update (fun b : Fin s => Vslots b x) a
              (covDerivConnectionDifference (I := I) g₂ g₁
                (fun z => W z) (fun z => V z) (fun z => Vslots a z) x)))
        - ∑ a : Fin s, covStep (I := I) g₂ s S x
            (Fin.cons (W x) (Function.update (fun b : Fin s => Vslots b x) a
              (covDerivConnectionDifference (I := I) g₂ g₁
                (fun z => U z) (fun z => V z) (fun z => Vslots a z) x)))
        - ∑ a : Fin s, covStep (I := I) g₂ (s + 1) (covStep (I := I) g₂ s S) x
            (Fin.cons (U x) (Fin.cons (W x) (Function.update (fun b : Fin s => Vslots b x) a
              ((CovariantDerivative.difference
                  (leviCivitaConnectionOfMetric (I := I) g₁)
                  (leviCivitaConnectionOfMetric (I := I) g₂) x
                  (Vslots a x)) (V x)))))
        + ∑ j : Fin (s + 1), (covStep (I := I) g₂ s S x)
            (Function.update (Fin.cons (V x) (fun b : Fin s => Vslots b x)) j
              (covDerivConnectionDifference (I := I) g₂ g₁ (fun z => U z) (fun z => W z)
                (fun z => (Fin.cons V Vslots :
                  Fin (s + 1) → ContMDiffSection I E (∞ : WithTop ℕ∞)
                    (TangentSpace I : M -> Type _)) j z) x))
        + ∑ j : Fin (s + 1), covStep (I := I) g₂ (s + 1) (covStep (I := I) g₂ s S) x
            (Fin.cons (U x)
              (Function.update (Fin.cons (V x) (fun b : Fin s => Vslots b x)) j
                ((CovariantDerivative.difference
                    (leviCivitaConnectionOfMetric (I := I) g₁)
                    (leviCivitaConnectionOfMetric (I := I) g₂) x
                    ((Fin.cons V Vslots :
                      Fin (s + 1) → ContMDiffSection I E (∞ : WithTop ℕ∞)
                        (TangentSpace I : M -> Type _)) j x)) (W x)))) := by
  rw [covStep2_mixedComm_eval_sub (I := I) g₁ g₂ s S U W V Vslots x,
    covStep2_diffStep_eval (I := I) g₁ g₂ s S U W V Vslots x,
    covStep2_pieceB_eval (I := I) g₁ g₂ s S U W V Vslots x]
  abel

open DifferentialGeometry.Integral.Connection in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
private theorem mixedComm_le
    {K : Set M} (g₁ g₂ : SmoothRiemannianMetric I M) (s : ℕ)
    {Λ Λ' Λ'' Λ''' : ℝ}
    (hEq : MetricUniformEquivalentOn (I := I) K g₂ g₁ Λ)
    (hJet1 : MetricCovDerivOrderBoundOn (I := I) K 1 g₁ g₂ Λ')
    (hJet2 : MetricCovDerivOrderBoundOn (I := I) K 2 g₁ g₂ Λ'')
    (hJet3 : MetricCovDerivOrderBoundOn (I := I) K 3 g₁ g₂ Λ''') :
    ∀ (S : Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H)
          (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s) (x : M), x ∈ K →
      Real.sqrt (normSq0S (I := I) g₂ x (s + 3)
          (covStep (I := I) g₂ (s + 2)
            (covStep (I := I) g₂ (s + 1) (covStep (I := I) g₁ s S)
              - covStep (I := I) g₁ (s + 1) (covStep (I := I) g₂ s S)) x)) ≤
        mixedCommC (E := E) s Λ Λ' Λ'' Λ''' *
          (Real.sqrt (normSq0S (I := I) g₂ x s (S x))
            + Real.sqrt (normSq0S (I := I) g₂ x (s + 1) (covStep (I := I) g₂ s S x))
            + Real.sqrt (normSq0S (I := I) g₂ x (s + 2)
                (covStep (I := I) g₂ (s + 1) (covStep (I := I) g₂ s S) x))) := by
  classical
  have : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  have : IsManifold I 2 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  have : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
    change IsManifold I ∞ M
    infer_instance
  have : IsManifold I (1 + 1) M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by decide : ((1 : WithTop ℕ∞) + 1) ≤ ∞)
  have : ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I :=
    TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := 1)
  set CA2 : ℝ := 3 / 2 * Λ ^ 5 * Λ''' + 9 / 2 * Λ ^ 6 * Λ' * Λ'' + 3 * Λ ^ 7 * Λ' ^ 3 with hCA2def
  set CA1 : ℝ := 3 / 2 * Λ ^ 4 * (Λ'' + Λ * Λ' ^ 2) with hCA1def
  set NAb : ℝ := 3 / 2 * Λ ^ 3 * Λ' with hNAbdef
  intro S x hx
  have hL1 : (1 : ℝ) ≤ Λ := hEq.1
  have hLnn : (0 : ℝ) ≤ Λ := le_trans zero_le_one hL1
  have hL'nn : (0 : ℝ) ≤ Λ' := le_trans (Real.sqrt_nonneg _) (hJet1 x hx)
  have hL''nn : (0 : ℝ) ≤ Λ'' := le_trans (Real.sqrt_nonneg _) (hJet2 x hx)
  have hL'''nn : (0 : ℝ) ≤ Λ''' := le_trans (Real.sqrt_nonneg _) (hJet3 x hx)
  have hs2 : Real.sqrt Λ ^ 2 = Λ := Real.sq_sqrt hLnn
  have hCA2nn : (0 : ℝ) ≤ CA2 := by
    rw [hCA2def]
    have h1 : (0 : ℝ) ≤ Λ ^ 5 * Λ''' := mul_nonneg (by positivity) hL'''nn
    have h2 : (0 : ℝ) ≤ Λ ^ 6 * Λ' * Λ'' := mul_nonneg (mul_nonneg (by positivity) hL'nn) hL''nn
    have h3 : (0 : ℝ) ≤ Λ ^ 7 * Λ' ^ 3 := mul_nonneg (by positivity) (pow_nonneg hL'nn 3)
    nlinarith [h1, h2, h3]
  have hCA1nn : (0 : ℝ) ≤ CA1 := by
    rw [hCA1def]
    exact mul_nonneg (mul_nonneg (by norm_num) (by positivity))
      (add_nonneg hL''nn (mul_nonneg hLnn (sq_nonneg Λ')))
  have hNAbnn : (0 : ℝ) ≤ NAb := by
    rw [hNAbdef]
    exact mul_nonneg (mul_nonneg (by norm_num) (by positivity)) hL'nn
  obtain ⟨basis, hON⟩ :=
    DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis (I := I) g₂ x
  have hbnorm : ∀ i, Real.sqrt (g₂.inner x (basis i) (basis i)) = 1 := by
    intro i; rw [hON i i]; simp
  have hinv : MetricInverseInBasisGen (I := I) g₂ x basis
      (identityInvMetric (Idx := Fin (Module.finrank Real (TangentSpace I x)))) := by
    intro i j; constructor <;> simp [identityInvMetric, diagonalInvMetric, hON]
  set NS := Real.sqrt (normSq0S (I := I) g₂ x s (S x)) with hNSdef
  set N1 := Real.sqrt (normSq0S (I := I) g₂ x (s + 1) (covStep (I := I) g₂ s S x)) with hN1def
  set N2 := Real.sqrt (normSq0S (I := I) g₂ x (s + 2)
    (covStep (I := I) g₂ (s + 1) (covStep (I := I) g₂ s S) x)) with hN2def
  have hNSnn : (0 : ℝ) ≤ NS := Real.sqrt_nonneg _
  have hN1nn : (0 : ℝ) ≤ N1 := Real.sqrt_nonneg _
  have hN2nn : (0 : ℝ) ≤ N2 := Real.sqrt_nonneg _
  have hA2 := fun (v' v w u : TangentSpace I x) =>
    covDConnectionDifference2_gJet_le (I := I) hEq hJet1 hJet2 hJet3 hx v' v w u
  have hA1 := fun (v w u : TangentSpace I x) =>
    DifferentialGeometry.Geometry.Curvature.covDerivConnectionDifference_gJet_le (I := I)
      hEq hJet1 hJet2 hx v w u
  have hvec : ∀ z : TangentSpace I x,
      Real.sqrt (g₁.inner x z z) ≤ Real.sqrt Λ * Real.sqrt (g₂.inner x z z) := by
    intro z
    calc Real.sqrt (g₁.inner x z z) ≤ Real.sqrt (Λ * g₂.inner x z z) :=
          Real.sqrt_le_sqrt (hEq.2 x hx z).2
      _ = Real.sqrt Λ * Real.sqrt (g₂.inner x z z) := Real.sqrt_mul hLnn _
  have hout : ∀ z : TangentSpace I x,
      Real.sqrt (g₂.inner x z z) ≤ Real.sqrt Λ * Real.sqrt (g₁.inner x z z) := by
    intro z
    have h := (hEq.2 x hx z).1
    have h' : g₂.inner x z z ≤ Λ * g₁.inner x z z := by
      have h2 := mul_le_mul_of_nonneg_left h hLnn
      rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt (lt_of_lt_of_le zero_lt_one hL1)), one_mul] at h2
      exact h2
    calc Real.sqrt (g₂.inner x z z) ≤ Real.sqrt (Λ * g₁.inner x z z) := Real.sqrt_le_sqrt h'
      _ = Real.sqrt Λ * Real.sqrt (g₁.inner x z z) := Real.sqrt_mul hLnn _
  have hNAg1 : Real.sqrt (Tensor0SBundle.normSqRS (I := I) (g := g₁) (x := x) 1 2
        (Tensor0SBundle.connectionDifferenceTensorAt (I := I)
          (leviCivitaConnectionOfMetric (I := I) g₁)
          (leviCivitaConnectionOfMetric (I := I) g₂) x)) ≤
      3 / 2 * (Λ * Real.sqrt Λ * Λ') := by
    obtain ⟨_, basis₁, hhinv₁, _, _, _⟩ :=
      exists_diagInv_of_metricUniformEquivalentOn (I := I)
        (metricUniformEquivalentOn_symm (I := I) hEq) hx
    have h := diff_le_covOne_basis_ref_lc (I := I) g₁ g₂ hx Λ hEq basis₁ hhinv₁
    rw [show Real.sqrt (Λ ^ 3) = Λ * Real.sqrt Λ from by
      rw [show Λ ^ 3 = Λ ^ 2 * Λ by ring, Real.sqrt_mul (by positivity),
        Real.sqrt_sq hLnn]] at h
    refine le_trans h ?_
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (hJet1 x hx) (mul_nonneg hLnn (Real.sqrt_nonneg _)))
      (by norm_num : (0 : ℝ) ≤ 3 / 2)
  have hA0 : ∀ (Yv Xv : TangentSpace I x),
      Real.sqrt (g₂.inner x
          ((CovariantDerivative.difference
              (leviCivitaConnectionOfMetric (I := I) g₁)
              (leviCivitaConnectionOfMetric (I := I) g₂) x Yv) Xv)
          ((CovariantDerivative.difference
              (leviCivitaConnectionOfMetric (I := I) g₁)
              (leviCivitaConnectionOfMetric (I := I) g₂) x Yv) Xv)) ≤
        NAb * Real.sqrt (g₂.inner x Xv Xv) * Real.sqrt (g₂.inner x Yv Yv) := by
    intro Yv Xv
    have hg1 := connectionDifferenceVec_norm_le (I := I) g₁
      (leviCivitaConnectionOfMetric (I := I) g₁)
      (leviCivitaConnectionOfMetric (I := I) g₂) Xv Yv
    have hstep1 : Real.sqrt (g₁.inner x
          ((CovariantDerivative.difference
              (leviCivitaConnectionOfMetric (I := I) g₁)
              (leviCivitaConnectionOfMetric (I := I) g₂) x Yv) Xv)
          ((CovariantDerivative.difference
              (leviCivitaConnectionOfMetric (I := I) g₁)
              (leviCivitaConnectionOfMetric (I := I) g₂) x Yv) Xv)) ≤
        3 / 2 * (Λ * Real.sqrt Λ * Λ') *
          (Real.sqrt Λ * Real.sqrt (g₂.inner x Xv Xv)) *
          (Real.sqrt Λ * Real.sqrt (g₂.inner x Yv Yv)) := by
      refine le_trans hg1 ?_
      have hmono1 : Real.sqrt (Tensor0SBundle.normSqRS (I := I) (g := g₁) (x := x) 1 2
            (Tensor0SBundle.connectionDifferenceTensorAt (I := I)
              (leviCivitaConnectionOfMetric (I := I) g₁)
              (leviCivitaConnectionOfMetric (I := I) g₂) x)) *
            Real.sqrt (g₁.inner x Xv Xv) * Real.sqrt (g₁.inner x Yv Yv) ≤
          3 / 2 * (Λ * Real.sqrt Λ * Λ') *
            (Real.sqrt Λ * Real.sqrt (g₂.inner x Xv Xv)) *
            (Real.sqrt Λ * Real.sqrt (g₂.inner x Yv Yv)) := by
        have p1 := mul_le_mul (mul_le_mul hNAg1 (hvec Xv) (Real.sqrt_nonneg _)
          (by positivity)) (hvec Yv) (Real.sqrt_nonneg _) (by positivity)
        exact p1
      exact hmono1
    calc Real.sqrt (g₂.inner x
          ((CovariantDerivative.difference
              (leviCivitaConnectionOfMetric (I := I) g₁)
              (leviCivitaConnectionOfMetric (I := I) g₂) x Yv) Xv)
          ((CovariantDerivative.difference
              (leviCivitaConnectionOfMetric (I := I) g₁)
              (leviCivitaConnectionOfMetric (I := I) g₂) x Yv) Xv))
        ≤ Real.sqrt Λ * Real.sqrt (g₁.inner x
            ((CovariantDerivative.difference
                (leviCivitaConnectionOfMetric (I := I) g₁)
                (leviCivitaConnectionOfMetric (I := I) g₂) x Yv) Xv)
            ((CovariantDerivative.difference
                (leviCivitaConnectionOfMetric (I := I) g₁)
                (leviCivitaConnectionOfMetric (I := I) g₂) x Yv) Xv)) := hout _
      _ ≤ Real.sqrt Λ * (3 / 2 * (Λ * Real.sqrt Λ * Λ') *
            (Real.sqrt Λ * Real.sqrt (g₂.inner x Xv Xv)) *
            (Real.sqrt Λ * Real.sqrt (g₂.inner x Yv Yv))) :=
          mul_le_mul_of_nonneg_left hstep1 (Real.sqrt_nonneg _)
      _ = NAb * Real.sqrt (g₂.inner x Xv Xv) * Real.sqrt (g₂.inner x Yv Yv) := by
          rw [hNAbdef]
          linear_combination (3 / 2 * Λ' * (Real.sqrt Λ ^ 2 + Λ) *
            (Real.sqrt (g₂.inner x Xv Xv) * Real.sqrt (g₂.inner x Yv Yv)) * Λ) * hs2
  have habs : ∀ (r : ℕ)
      (T : Tensor0SBundle.Tensor0SSpace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r x)
      (tup : Fin r → TangentSpace I x) (j : Fin r),
      (∀ b : Fin r, b ≠ j → Real.sqrt (g₂.inner x (tup b) (tup b)) = 1) →
      |T tup| ≤ Real.sqrt (normSq0S (I := I) g₂ x r T) *
        Real.sqrt (g₂.inner x (tup j) (tup j)) := by
    intro r T tup j hb
    have hcs := Tensor0SBundle.abs_apply_le_sqrt_normSq0S (I := I) g₂ x r basis hON T tup
    rwa [Finset.prod_eq_single j (fun b _ hbj => hb b hbj)
      (fun hj => absurd (Finset.mem_univ j) hj)] at hcs
  set B : ℝ := (s : ℝ) * (NS * CA2) + (3 * (s : ℝ) + 1) * (N1 * CA1) +
    (2 * (s : ℝ) + 1) * (N2 * NAb) with hBdef
  have hBnn : (0 : ℝ) ≤ B := by
    rw [hBdef]
    have b1 : (0 : ℝ) ≤ (s : ℝ) * (NS * CA2) :=
      mul_nonneg (by positivity) (mul_nonneg hNSnn hCA2nn)
    have b2 : (0 : ℝ) ≤ (3 * (s : ℝ) + 1) * (N1 * CA1) :=
      mul_nonneg (by positivity) (mul_nonneg hN1nn hCA1nn)
    have b3 : (0 : ℝ) ≤ (2 * (s : ℝ) + 1) * (N2 * NAb) :=
      mul_nonneg (by positivity) (mul_nonneg hN2nn hNAbnn)
    linarith
  have hcomp : ∀ φ : Fin (s + 3) → Fin (Module.finrank Real (TangentSpace I x)),
      |Tensor0SBundle.component0S (I := I) basis
        (covStep (I := I) g₂ (s + 2)
          (covStep (I := I) g₂ (s + 1) (covStep (I := I) g₁ s S)
            - covStep (I := I) g₁ (s + 1) (covStep (I := I) g₂ s S)) x) φ| ≤ B := by
    intro φ
    rw [Tensor0SBundle.component0S_apply]
    set Usec : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
      ContMDiffSection.mk (smoothExtensionTangent (I := I) x (basis (φ 0)))
        (smoothExtensionTangent_contMDiff (I := I) x (basis (φ 0))) with hUsec
    set Wsec : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
      ContMDiffSection.mk (smoothExtensionTangent (I := I) x (basis (φ (Fin.succ 0))))
        (smoothExtensionTangent_contMDiff (I := I) x (basis (φ (Fin.succ 0)))) with hWsec
    set Vsec : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
      ContMDiffSection.mk
        (smoothExtensionTangent (I := I) x (basis (φ (Fin.succ (Fin.succ 0)))))
        (smoothExtensionTangent_contMDiff (I := I) x
          (basis (φ (Fin.succ (Fin.succ 0))))) with hVsec
    set Zsec : Fin s → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
      fun a => ContMDiffSection.mk
        (smoothExtensionTangent (I := I) x (basis (φ a.succ.succ.succ)))
        (smoothExtensionTangent_contMDiff (I := I) x (basis (φ a.succ.succ.succ))) with hZsec
    have hUval : Usec x = basis (φ 0) := smoothExtensionTangent_eq (I := I) x _
    have hWval : Wsec x = basis (φ (Fin.succ 0)) := smoothExtensionTangent_eq (I := I) x _
    have hVval : Vsec x = basis (φ (Fin.succ (Fin.succ 0))) :=
      smoothExtensionTangent_eq (I := I) x _
    have hZval : ∀ a : Fin s, Zsec a x = basis (φ a.succ.succ.succ) :=
      fun a => smoothExtensionTangent_eq (I := I) x _
    have hnU : Real.sqrt (g₂.inner x (Usec x) (Usec x)) = 1 := by rw [hUval]; exact hbnorm _
    have hnW : Real.sqrt (g₂.inner x (Wsec x) (Wsec x)) = 1 := by rw [hWval]; exact hbnorm _
    have hnV : Real.sqrt (g₂.inner x (Vsec x) (Vsec x)) = 1 := by rw [hVval]; exact hbnorm _
    have hnZ : ∀ a : Fin s, Real.sqrt (g₂.inner x (Zsec a x) (Zsec a x)) = 1 :=
      fun a => by rw [hZval a]; exact hbnorm _
    have htuple : (fun j : Fin (s + 3) => basis (φ j)) =
        Fin.cons (Usec x) (Fin.cons (Wsec x)
          (Fin.cons (Vsec x) (fun a : Fin s => Zsec a x))) := by
      funext j
      refine Fin.cases ?_ (fun i => ?_) j
      · exact hUval.symm
      · refine Fin.cases ?_ (fun k => ?_) i
        · exact hWval.symm
        · refine Fin.cases ?_ (fun a => ?_) k
          · exact hVval.symm
          · exact (hZval a).symm
    rw [htuple, covStep2_mixedComm_eval (I := I) g₁ g₂ s S Usec Wsec Vsec Zsec x]
    have hI : ∀ a : Fin s, |(S x) (Function.update (fun b : Fin s => Zsec b x) a
        (covDerivConnectionDifference2 (I := I) g₂ g₁
          (fun z => Usec z) (fun z => Wsec z) (fun z => Vsec z) (fun z => Zsec a z) x))| ≤
        NS * CA2 := by
      intro a
      have hb := habs s (S x)
        (Function.update (fun b : Fin s => Zsec b x) a
          (covDerivConnectionDifference2 (I := I) g₂ g₁
            (fun z => Usec z) (fun z => Wsec z) (fun z => Vsec z) (fun z => Zsec a z) x)) a
        (fun b hbne => by rw [Function.update_of_ne hbne]; exact hnZ b)
      rw [Function.update_self, ← hNSdef] at hb
      refine le_trans hb (mul_le_mul_of_nonneg_left ?_ hNSnn)
      rw [hCA2def]
      have h := hA2 (basis (φ 0)) (basis (φ (Fin.succ 0))) (basis (φ (Fin.succ (Fin.succ 0))))
        (basis (φ a.succ.succ.succ))
      rw [hbnorm (φ 0), hbnorm (φ (Fin.succ 0)), hbnorm (φ (Fin.succ (Fin.succ 0))),
        hbnorm (φ a.succ.succ.succ), mul_one, mul_one, mul_one, mul_one] at h
      exact h
    have hII : ∀ a : Fin s, |covStep (I := I) g₂ s S x
        (Fin.cons (Usec x) (Function.update (fun b : Fin s => Zsec b x) a
          (covDerivConnectionDifference (I := I) g₂ g₁
            (fun z => Wsec z) (fun z => Vsec z) (fun z => Zsec a z) x)))| ≤ N1 * CA1 := by
      intro a
      set tup : Fin (s + 1) → TangentSpace I x :=
        Fin.cons (Usec x) (Function.update (fun b : Fin s => Zsec b x) a
          (covDerivConnectionDifference (I := I) g₂ g₁
            (fun z => Wsec z) (fun z => Vsec z) (fun z => Zsec a z) x)) with htup
      have hbase : ∀ b : Fin (s + 1), b ≠ Fin.succ a →
          Real.sqrt (g₂.inner x (tup b) (tup b)) = 1 := by
        intro b
        refine Fin.cases ?_ (fun c => ?_) b
        · intro _
          rw [htup, Fin.cons_zero]
          exact hnU
        · intro hbne
          have hca : c ≠ a := fun h => hbne (by rw [h])
          rw [htup, Fin.cons_succ, Function.update_of_ne hca]
          exact hnZ c
      have hb := habs (s + 1) (covStep (I := I) g₂ s S x) tup (Fin.succ a) hbase
      have htupj : tup (Fin.succ a) = covDerivConnectionDifference (I := I) g₂ g₁
          (fun z => Wsec z) (fun z => Vsec z) (fun z => Zsec a z) x := by
        rw [htup, Fin.cons_succ, Function.update_self]
      rw [htupj, ← hN1def] at hb
      refine le_trans hb (mul_le_mul_of_nonneg_left ?_ hN1nn)
      rw [hCA1def]
      have h := hA1 (basis (φ (Fin.succ 0))) (basis (φ (Fin.succ (Fin.succ 0))))
        (basis (φ a.succ.succ.succ))
      rw [hbnorm (φ (Fin.succ 0)), hbnorm (φ (Fin.succ (Fin.succ 0))),
        hbnorm (φ a.succ.succ.succ), mul_one, mul_one, mul_one] at h
      exact h
    have hIII : ∀ a : Fin s, |covStep (I := I) g₂ s S x
        (Fin.cons (Wsec x) (Function.update (fun b : Fin s => Zsec b x) a
          (covDerivConnectionDifference (I := I) g₂ g₁
            (fun z => Usec z) (fun z => Vsec z) (fun z => Zsec a z) x)))| ≤ N1 * CA1 := by
      intro a
      set tup : Fin (s + 1) → TangentSpace I x :=
        Fin.cons (Wsec x) (Function.update (fun b : Fin s => Zsec b x) a
          (covDerivConnectionDifference (I := I) g₂ g₁
            (fun z => Usec z) (fun z => Vsec z) (fun z => Zsec a z) x)) with htup
      have hbase : ∀ b : Fin (s + 1), b ≠ Fin.succ a →
          Real.sqrt (g₂.inner x (tup b) (tup b)) = 1 := by
        intro b
        refine Fin.cases ?_ (fun c => ?_) b
        · intro _
          rw [htup, Fin.cons_zero]
          exact hnW
        · intro hbne
          have hca : c ≠ a := fun h => hbne (by rw [h])
          rw [htup, Fin.cons_succ, Function.update_of_ne hca]
          exact hnZ c
      have hb := habs (s + 1) (covStep (I := I) g₂ s S x) tup (Fin.succ a) hbase
      have htupj : tup (Fin.succ a) = covDerivConnectionDifference (I := I) g₂ g₁
          (fun z => Usec z) (fun z => Vsec z) (fun z => Zsec a z) x := by
        rw [htup, Fin.cons_succ, Function.update_self]
      rw [htupj, ← hN1def] at hb
      refine le_trans hb (mul_le_mul_of_nonneg_left ?_ hN1nn)
      rw [hCA1def]
      have h := hA1 (basis (φ 0)) (basis (φ (Fin.succ (Fin.succ 0))))
        (basis (φ a.succ.succ.succ))
      rw [hbnorm (φ 0), hbnorm (φ (Fin.succ (Fin.succ 0))),
        hbnorm (φ a.succ.succ.succ), mul_one, mul_one, mul_one] at h
      exact h
    have hV : ∀ a : Fin s, |covStep (I := I) g₂ (s + 1) (covStep (I := I) g₂ s S) x
        (Fin.cons (Usec x) (Fin.cons (Wsec x) (Function.update (fun b : Fin s => Zsec b x) a
          ((CovariantDerivative.difference
              (leviCivitaConnectionOfMetric (I := I) g₁)
              (leviCivitaConnectionOfMetric (I := I) g₂) x
              (Zsec a x)) (Vsec x)))))| ≤ N2 * NAb := by
      intro a
      set tup : Fin (s + 2) → TangentSpace I x :=
        Fin.cons (Usec x) (Fin.cons (Wsec x) (Function.update (fun b : Fin s => Zsec b x) a
          ((CovariantDerivative.difference
              (leviCivitaConnectionOfMetric (I := I) g₁)
              (leviCivitaConnectionOfMetric (I := I) g₂) x
              (Zsec a x)) (Vsec x)))) with htup
      have hbase : ∀ b : Fin (s + 2), b ≠ Fin.succ (Fin.succ a) →
          Real.sqrt (g₂.inner x (tup b) (tup b)) = 1 := by
        intro b
        refine Fin.cases ?_ (fun c => ?_) b
        · intro _
          rw [htup, Fin.cons_zero]
          exact hnU
        · refine Fin.cases ?_ (fun d => ?_) c
          · intro _
            rw [htup, Fin.cons_succ, Fin.cons_zero]
            exact hnW
          · intro hbne
            have hda : d ≠ a := fun h => hbne (by rw [h])
            rw [htup, Fin.cons_succ, Fin.cons_succ, Function.update_of_ne hda]
            exact hnZ d
      have hb := habs (s + 2) (covStep (I := I) g₂ (s + 1) (covStep (I := I) g₂ s S) x) tup
        (Fin.succ (Fin.succ a)) hbase
      have htupj : tup (Fin.succ (Fin.succ a)) =
          (CovariantDerivative.difference
            (leviCivitaConnectionOfMetric (I := I) g₁)
            (leviCivitaConnectionOfMetric (I := I) g₂) x
            (Zsec a x)) (Vsec x) := by
        rw [htup, Fin.cons_succ, Fin.cons_succ, Function.update_self]
      rw [htupj, ← hN2def] at hb
      refine le_trans hb (mul_le_mul_of_nonneg_left ?_ hN2nn)
      have h := hA0 (Zsec a x) (Vsec x)
      rw [hnV, hnZ a, mul_one, mul_one] at h
      exact h
    have hIV : ∀ j : Fin (s + 1), |(covStep (I := I) g₂ s S x)
        (Function.update (Fin.cons (Vsec x) (fun b : Fin s => Zsec b x)) j
          (covDerivConnectionDifference (I := I) g₂ g₁ (fun z => Usec z) (fun z => Wsec z)
            (fun z => (Fin.cons Vsec Zsec :
              Fin (s + 1) → ContMDiffSection I E (∞ : WithTop ℕ∞)
                (TangentSpace I : M -> Type _)) j z) x))| ≤ N1 * CA1 := by
      intro j
      set tup : Fin (s + 1) → TangentSpace I x :=
        Function.update (Fin.cons (Vsec x) (fun b : Fin s => Zsec b x)) j
          (covDerivConnectionDifference (I := I) g₂ g₁ (fun z => Usec z) (fun z => Wsec z)
            (fun z => (Fin.cons Vsec Zsec :
              Fin (s + 1) → ContMDiffSection I E (∞ : WithTop ℕ∞)
                (TangentSpace I : M -> Type _)) j z) x) with htup
      have hbase : ∀ b : Fin (s + 1), b ≠ j →
          Real.sqrt (g₂.inner x (tup b) (tup b)) = 1 := by
        intro b hbj
        rw [htup, Function.update_of_ne hbj]
        refine Fin.cases ?_ (fun c => ?_) b
        · rw [Fin.cons_zero]
          exact hnV
        · rw [Fin.cons_succ]
          exact hnZ c
      have hb := habs (s + 1) (covStep (I := I) g₂ s S x) tup j hbase
      have htupj : tup j = covDerivConnectionDifference (I := I) g₂ g₁
          (fun z => Usec z) (fun z => Wsec z)
          (fun z => (Fin.cons Vsec Zsec :
            Fin (s + 1) → ContMDiffSection I E (∞ : WithTop ℕ∞)
              (TangentSpace I : M -> Type _)) j z) x := by
        rw [htup, Function.update_self]
      rw [htupj, ← hN1def] at hb
      refine le_trans hb (mul_le_mul_of_nonneg_left ?_ hN1nn)
      rw [hCA1def]
      refine Fin.cases ?_ (fun c => ?_) j
      · have h := hA1 (basis (φ 0)) (basis (φ (Fin.succ 0)))
          (basis (φ (Fin.succ (Fin.succ 0))))
        rw [hbnorm (φ 0), hbnorm (φ (Fin.succ 0)), hbnorm (φ (Fin.succ (Fin.succ 0))),
          mul_one, mul_one, mul_one] at h
        exact h
      · have h := hA1 (basis (φ 0)) (basis (φ (Fin.succ 0))) (basis (φ c.succ.succ.succ))
        rw [hbnorm (φ 0), hbnorm (φ (Fin.succ 0)), hbnorm (φ c.succ.succ.succ),
          mul_one, mul_one, mul_one] at h
        exact h
    have hnVV : ∀ j : Fin (s + 1),
        Real.sqrt (g₂.inner x
          ((Fin.cons Vsec Zsec :
            Fin (s + 1) → ContMDiffSection I E (∞ : WithTop ℕ∞)
              (TangentSpace I : M -> Type _)) j x)
          ((Fin.cons Vsec Zsec :
            Fin (s + 1) → ContMDiffSection I E (∞ : WithTop ℕ∞)
              (TangentSpace I : M -> Type _)) j x)) = 1 := by
      intro j
      refine Fin.cases ?_ (fun c => ?_) j
      · rw [Fin.cons_zero]
        exact hnV
      · rw [Fin.cons_succ]
        exact hnZ c
    have hVI : ∀ j : Fin (s + 1), |covStep (I := I) g₂ (s + 1) (covStep (I := I) g₂ s S) x
        (Fin.cons (Usec x)
          (Function.update (Fin.cons (Vsec x) (fun b : Fin s => Zsec b x)) j
            ((CovariantDerivative.difference
                (leviCivitaConnectionOfMetric (I := I) g₁)
                (leviCivitaConnectionOfMetric (I := I) g₂) x
                ((Fin.cons Vsec Zsec :
                  Fin (s + 1) → ContMDiffSection I E (∞ : WithTop ℕ∞)
                    (TangentSpace I : M -> Type _)) j x)) (Wsec x))))| ≤ N2 * NAb := by
      intro j
      set tup : Fin (s + 2) → TangentSpace I x :=
        Fin.cons (Usec x)
          (Function.update (Fin.cons (Vsec x) (fun b : Fin s => Zsec b x)) j
            ((CovariantDerivative.difference
                (leviCivitaConnectionOfMetric (I := I) g₁)
                (leviCivitaConnectionOfMetric (I := I) g₂) x
                ((Fin.cons Vsec Zsec :
                  Fin (s + 1) → ContMDiffSection I E (∞ : WithTop ℕ∞)
                    (TangentSpace I : M -> Type _)) j x)) (Wsec x))) with htup
      have hbase : ∀ b : Fin (s + 2), b ≠ Fin.succ j →
          Real.sqrt (g₂.inner x (tup b) (tup b)) = 1 := by
        intro b
        refine Fin.cases ?_ (fun c => ?_) b
        · intro _
          rw [htup, Fin.cons_zero]
          exact hnU
        · intro hbne
          have hcj : c ≠ j := fun h => hbne (by rw [h])
          rw [htup, Fin.cons_succ, Function.update_of_ne hcj]
          refine Fin.cases ?_ (fun d => ?_) c
          · rw [Fin.cons_zero]
            exact hnV
          · rw [Fin.cons_succ]
            exact hnZ d
      have hb := habs (s + 2) (covStep (I := I) g₂ (s + 1) (covStep (I := I) g₂ s S) x) tup
        (Fin.succ j) hbase
      have htupj : tup (Fin.succ j) =
          (CovariantDerivative.difference
            (leviCivitaConnectionOfMetric (I := I) g₁)
            (leviCivitaConnectionOfMetric (I := I) g₂) x
            ((Fin.cons Vsec Zsec :
              Fin (s + 1) → ContMDiffSection I E (∞ : WithTop ℕ∞)
                (TangentSpace I : M -> Type _)) j x)) (Wsec x) := by
        rw [htup, Fin.cons_succ, Function.update_self]
      rw [htupj, ← hN2def] at hb
      refine le_trans hb (mul_le_mul_of_nonneg_left ?_ hN2nn)
      have h := hA0 ((Fin.cons Vsec Zsec :
        Fin (s + 1) → ContMDiffSection I E (∞ : WithTop ℕ∞)
          (TangentSpace I : M -> Type _)) j x) (Wsec x)
      rw [hnW, hnVV j, mul_one, mul_one] at h
      exact h
    have habs_sub : ∀ p q : ℝ, |p - q| ≤ |p| + |q| := by
      intro p q
      calc |p - q| = |p + -q| := by rw [sub_eq_add_neg]
        _ ≤ |p| + |-q| := abs_add_le _ _
        _ = |p| + |q| := by rw [abs_neg]
    have h6 : ∀ A B' C' D' E' F' : ℝ,
        |A - B' - C' - D' + E' + F'| ≤ |A| + |B'| + |C'| + |D'| + |E'| + |F'| := by
      intro A B' C' D' E' F'
      have h1 : |A - B' - C' - D' + E' + F'| ≤ |A - B' - C' - D' + E'| + |F'| :=
        abs_add_le _ _
      have h2 : |A - B' - C' - D' + E'| ≤ |A - B' - C' - D'| + |E'| := abs_add_le _ _
      have h3 : |A - B' - C' - D'| ≤ |A - B' - C'| + |D'| := habs_sub _ _
      have h4 : |A - B' - C'| ≤ |A - B'| + |C'| := habs_sub _ _
      have h5 : |A - B'| ≤ |A| + |B'| := habs_sub _ _
      linarith
    have esum : ∀ {r : ℕ} (f : Fin r → ℝ) (c : ℝ), (∀ a, |f a| ≤ c) →
        |∑ a, f a| ≤ (r : ℝ) * c := by
      intro r f c hf
      calc |∑ a, f a| ≤ ∑ a, |f a| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _a : Fin r, c := Finset.sum_le_sum (fun a _ => hf a)
        _ = (r : ℝ) * c := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    refine le_trans (h6 _ _ _ _ _ _) ?_
    rw [abs_neg]
    refine le_trans (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
      (esum _ _ hI) (esum _ _ hII)) (esum _ _ hIII)) (esum _ _ hV)) (esum _ _ hIV))
      (esum _ _ hVI)) ?_
    rw [hBdef]
    refine le_of_eq ?_
    push_cast
    ring
  have hcard := Tensor0SBundle.normSq0S_le_card_of_component_bound (I := I) g₂ x (s + 3) basis hinv
    (covStep (I := I) g₂ (s + 2)
      (covStep (I := I) g₂ (s + 1) (covStep (I := I) g₁ s S)
        - covStep (I := I) g₁ (s + 1) (covStep (I := I) g₂ s S)) x) B hBnn hcomp
  have hcard_eq :
      (Fintype.card (Fin (s + 3) → Fin (Module.finrank Real (TangentSpace I x))) : ℝ)
        = (Module.finrank ℝ E : ℝ) ^ (s + 3) := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    push_cast
    rfl
  have hstep : B ≤ ((s : ℝ) * CA2 + (3 * (s : ℝ) + 1) * CA1 + (2 * (s : ℝ) + 1) * NAb) *
      (NS + N1 + N2) := by
    rw [hBdef]
    have hc1 : (0 : ℝ) ≤ (s : ℝ) * CA2 := mul_nonneg (by positivity) hCA2nn
    have hc2 : (0 : ℝ) ≤ (3 * (s : ℝ) + 1) * CA1 := mul_nonneg (by positivity) hCA1nn
    have hc3 : (0 : ℝ) ≤ (2 * (s : ℝ) + 1) * NAb := mul_nonneg (by positivity) hNAbnn
    linarith [mul_nonneg hc1 (add_nonneg hN1nn hN2nn),
      mul_nonneg hc2 (add_nonneg hNSnn hN2nn),
      mul_nonneg hc3 (add_nonneg hNSnn hN1nn)]
  calc Real.sqrt (normSq0S (I := I) g₂ x (s + 3)
        (covStep (I := I) g₂ (s + 2)
          (covStep (I := I) g₂ (s + 1) (covStep (I := I) g₁ s S)
            - covStep (I := I) g₁ (s + 1) (covStep (I := I) g₂ s S)) x))
      ≤ Real.sqrt
          ((Fintype.card (Fin (s + 3) → Fin (Module.finrank Real (TangentSpace I x))) : ℝ)
            * B ^ 2) := Real.sqrt_le_sqrt hcard
    _ = Real.sqrt ((Module.finrank ℝ E : ℝ) ^ (s + 3)) * B := by
        rw [hcard_eq, Real.sqrt_mul (by positivity), Real.sqrt_sq hBnn]
    _ ≤ Real.sqrt ((Module.finrank ℝ E : ℝ) ^ (s + 3)) *
          (((s : ℝ) * CA2 + (3 * (s : ℝ) + 1) * CA1 + (2 * (s : ℝ) + 1) * NAb) *
            (NS + N1 + N2)) :=
        mul_le_mul_of_nonneg_left hstep (Real.sqrt_nonneg _)
    _ ≤ max 0 (Real.sqrt ((Module.finrank ℝ E : ℝ) ^ (s + 3)) *
          ((s : ℝ) * CA2 + (3 * (s : ℝ) + 1) * CA1 + (2 * (s : ℝ) + 1) * NAb)) *
          (NS + N1 + N2) := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right (le_max_right 0 _)
          (add_nonneg (add_nonneg hNSnn hN1nn) hN2nn)

open DifferentialGeometry.Integral.Connection in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
theorem covStepDiff2_mixedComm_le
    {K : Set M} (g₁ g₂ : SmoothRiemannianMetric I M) (s : ℕ)
    {Λ Λ' Λ'' Λ''' : ℝ}
    (hEq : MetricUniformEquivalentOn (I := I) K g₂ g₁ Λ)
    (hJet1 : MetricCovDerivOrderBoundOn (I := I) K 1 g₁ g₂ Λ')
    (hJet2 : MetricCovDerivOrderBoundOn (I := I) K 2 g₁ g₂ Λ'')
    (hJet3 : MetricCovDerivOrderBoundOn (I := I) K 3 g₁ g₂ Λ''') :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H)
            (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s) (x : M), x ∈ K →
        Real.sqrt (normSq0S (I := I) g₂ x (s + 3)
            (covStep (I := I) g₂ (s + 2)
              (covStep (I := I) g₂ (s + 1) (covStep (I := I) g₁ s S)
                - covStep (I := I) g₁ (s + 1) (covStep (I := I) g₂ s S)) x)) ≤
          C * (Real.sqrt (normSq0S (I := I) g₂ x s (S x))
            + Real.sqrt (normSq0S (I := I) g₂ x (s + 1) (covStep (I := I) g₂ s S x))
            + Real.sqrt (normSq0S (I := I) g₂ x (s + 2)
                (covStep (I := I) g₂ (s + 1) (covStep (I := I) g₂ s S) x))) := by
  refine ⟨mixedCommC (E := E) s Λ Λ' Λ'' Λ''', le_max_left _ _, ?_⟩
  exact mixedComm_le (I := I) g₁ g₂ s hEq hJet1 hJet2 hJet3

noncomputable def covStepDiff2C (s : ℕ) (Λ Λ' Λ'' Λ''' : ℝ) : ℝ :=
  max 0 ((((s + 1 : ℕ) : ℝ) *
      Real.sqrt ((Module.finrank ℝ E : ℝ) ^ (s + 3)) *
      (3 / 2 * Λ ^ 4 * (Λ'' + Λ * Λ' ^ 2) +
        3 / 2 * (Real.sqrt (Λ ^ 3) * Λ'))) +
    mixedCommC (E := E) s Λ Λ' Λ'' Λ''')

omit [NeZero (Module.finrank ℝ E)] in
omit [CompactSpace M] in
theorem covStepDiff2_le
    {K : Set M} (g₁ g₂ : SmoothRiemannianMetric I M) (s : ℕ)
    {Λ Λ' Λ'' Λ''' : ℝ}
    (hEq : MetricUniformEquivalentOn (I := I) K g₂ g₁ Λ)
    (hJet1 : MetricCovDerivOrderBoundOn (I := I) K 1 g₁ g₂ Λ')
    (hJet2 : MetricCovDerivOrderBoundOn (I := I) K 2 g₁ g₂ Λ'')
    (hJet3 : MetricCovDerivOrderBoundOn (I := I) K 3 g₁ g₂ Λ''')
    (hJet1' : MetricCovDerivOrderBoundOn (I := I) K 1 g₂ g₁ Λ') :
    ∀ (S : Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H)
          (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s) (x : M), x ∈ K →
      Real.sqrt (normSq0S (I := I) g₂ x (s + 3)
          (covStep (I := I) g₂ (s + 2)
            (covStep (I := I) g₂ (s + 1) (diffStep (I := I) g₁ g₂ s S)) x)) ≤
        covStepDiff2C (E := E) s Λ Λ' Λ'' Λ''' *
          (Real.sqrt (normSq0S (I := I) g₂ x s (S x))
            + Real.sqrt (normSq0S (I := I) g₂ x (s + 1) (covStep (I := I) g₂ s S x))
            + Real.sqrt (normSq0S (I := I) g₂ x (s + 2)
                (covStep (I := I) g₂ (s + 1) (covStep (I := I) g₂ s S) x))) := by
  classical
  have : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  have : IsManifold I (1 + 1) M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide : ((1 : WithTop ℕ∞) + 1) ≤ ∞)
  let Cbr : ℝ := mixedCommC (E := E) s Λ Λ' Λ'' Λ'''
  have hCbr_nn : 0 ≤ Cbr := by
    dsimp [Cbr, mixedCommC]
    exact le_max_left _ _
  have hCbr := mixedComm_le (I := I) g₁ g₂ s hEq hJet1 hJet2 hJet3
  set K1 : ℝ := ((s + 1 : ℕ) : ℝ) * Real.sqrt ((Module.finrank ℝ E : ℝ) ^ (s + 3)) *
    (3 / 2 * Λ ^ 4 * (Λ'' + Λ * Λ' ^ 2) + 3 / 2 * (Real.sqrt (Λ ^ 3) * Λ')) with hK1def
  intro S x hx
  have hLnn : (0 : ℝ) ≤ Λ := le_trans zero_le_one hEq.1
  have hL'nn : (0 : ℝ) ≤ Λ' := le_trans (Real.sqrt_nonneg _) (hJet1 x hx)
  have hL''nn : (0 : ℝ) ≤ Λ'' := le_trans (Real.sqrt_nonneg _) (hJet2 x hx)
  have hK1nn : 0 ≤ K1 := by
    have hP : 0 ≤ 3 / 2 * Λ ^ 4 * (Λ'' + Λ * Λ' ^ 2) + 3 / 2 * (Real.sqrt (Λ ^ 3) * Λ') := by
      have h1 : 0 ≤ Λ ^ 4 := by positivity
      nlinarith [hL''nn, hL'nn, hLnn, h1, mul_nonneg hLnn (sq_nonneg Λ'),
        mul_nonneg (Real.sqrt_nonneg (Λ ^ 3)) hL'nn]
    rw [hK1def]
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)) hP
  have hop : covStep (I := I) g₂ (s + 2)
        (covStep (I := I) g₂ (s + 1) (diffStep (I := I) g₁ g₂ s S))
      = covStep (I := I) g₂ (s + 2)
          (diffStep (I := I) g₁ g₂ (s + 1) (covStep (I := I) g₂ s S))
        + covStep (I := I) g₂ (s + 2)
          (covStep (I := I) g₂ (s + 1) (covStep (I := I) g₁ s S)
            - covStep (I := I) g₁ (s + 1) (covStep (I := I) g₂ s S)) := by
    rw [diffStep_leibniz (I := I) g₁ g₂ s S, covStep_add]
  have hFx : (covStep (I := I) g₂ (s + 2)
        (covStep (I := I) g₂ (s + 1) (diffStep (I := I) g₁ g₂ s S))) x
      = (covStep (I := I) g₂ (s + 2)
          (diffStep (I := I) g₁ g₂ (s + 1) (covStep (I := I) g₂ s S))) x
        + (covStep (I := I) g₂ (s + 2)
          (covStep (I := I) g₂ (s + 1) (covStep (I := I) g₁ s S)
            - covStep (I := I) g₁ (s + 1) (covStep (I := I) g₂ s S))) x := by
    rw [hop]; rfl
  obtain ⟨basis, hON⟩ :=
    DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis (I := I) g₂ x
  have hinv : MetricInverseInBasisGen (I := I) g₂ x basis
      (identityInvMetric (Idx := Fin (Module.finrank Real (TangentSpace I x)))) := by
    intro i j; constructor <;> simp [identityInvMetric, diagonalInvMetric, hON]
  have hp1 := DifferentialGeometry.PDE.RicciFlow.covStepDiff_of_jets (I := I) g₁ g₂ (s + 1)
    (covStep (I := I) g₂ s S) x hEq hJet1 hJet2 hJet1' hx
  simp only [show s + 1 + 2 = s + 3 from rfl, ← hK1def] at hp1
  have hp2 := hCbr S x hx
  set a : ℝ := Real.sqrt (normSq0S (I := I) g₂ x s (S x)) with hadef
  set b : ℝ := Real.sqrt (normSq0S (I := I) g₂ x (s + 1) (covStep (I := I) g₂ s S x)) with hbdef
  set c : ℝ := Real.sqrt (normSq0S (I := I) g₂ x (s + 2)
    (covStep (I := I) g₂ (s + 1) (covStep (I := I) g₂ s S) x)) with hcdef
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have hb : 0 ≤ b := Real.sqrt_nonneg _
  have hc : 0 ≤ c := Real.sqrt_nonneg _
  rw [hFx]
  refine le_trans (sqrt_normSq0S_add_le (I := I) g₂ _ _ basis hinv) ?_
  refine le_trans (add_le_add hp1 hp2) ?_
  change K1 * (b + c) + Cbr * (a + b + c) ≤
    max 0 (K1 + Cbr) * (a + b + c)
  nlinarith [mul_nonneg hK1nn ha, mul_nonneg hCbr_nn hc,
    mul_nonneg (sub_nonneg.mpr (le_max_right 0 (K1 + Cbr)))
      (add_nonneg (add_nonneg ha hb) hc), ha, hb, hc, hK1nn, hCbr_nn]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
theorem covStepDiff2_exists_const
    {K : Set M} (g₁ g₂ : SmoothRiemannianMetric I M) (s : ℕ)
    {Λ Λ' Λ'' Λ''' : ℝ}
    (hEq : MetricUniformEquivalentOn (I := I) K g₂ g₁ Λ)
    (hJet1 : MetricCovDerivOrderBoundOn (I := I) K 1 g₁ g₂ Λ')
    (hJet2 : MetricCovDerivOrderBoundOn (I := I) K 2 g₁ g₂ Λ'')
    (hJet3 : MetricCovDerivOrderBoundOn (I := I) K 3 g₁ g₂ Λ''')
    (hJet1' : MetricCovDerivOrderBoundOn (I := I) K 1 g₂ g₁ Λ') :
    ∃ C₂ : ℝ, 0 ≤ C₂ ∧
      ∀ (S : Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H)
            (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s) (x : M), x ∈ K →
        Real.sqrt (normSq0S (I := I) g₂ x (s + 3)
            (covStep (I := I) g₂ (s + 2)
              (covStep (I := I) g₂ (s + 1) (diffStep (I := I) g₁ g₂ s S)) x)) ≤
          C₂ * (Real.sqrt (normSq0S (I := I) g₂ x s (S x))
            + Real.sqrt (normSq0S (I := I) g₂ x (s + 1) (covStep (I := I) g₂ s S x))
            + Real.sqrt (normSq0S (I := I) g₂ x (s + 2)
                (covStep (I := I) g₂ (s + 1) (covStep (I := I) g₂ s S) x))) := by
  refine ⟨covStepDiff2C (E := E) s Λ Λ' Λ'' Λ''', ?_, ?_⟩
  · dsimp [covStepDiff2C]
    exact le_max_left _ _
  · exact covStepDiff2_le (I := I) g₁ g₂ s hEq hJet1 hJet2 hJet3 hJet1'

end HCGCompactness
end DifferentialGeometry

end
