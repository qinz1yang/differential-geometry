import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Uniform.CurvatureJetDifference

import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.ConnectionSecondDerivative
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.PointwiseCurvatureDerivative
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.SecondBianchi

set_option autoImplicit false

noncomputable section


open Bundle Manifold Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Geometry.Connection
  (LeviCivita connectionDifference_koszul_deriv
   leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally)
open DifferentialGeometry.Geometry.Curvature
  (connectionRiemannCurvatureField covDerivConnectionDifference curvCovDerivOpAt
   exists_gOrthonormalBasis metricInverseInBasis_of_orthonormal metricRm04
   smoothExtensionTangent smoothExtensionTangent_contMDiff smoothExtensionTangent_eq vec5)

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
omit [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem curvJet1_eval (g : SmoothRiemannianMetric I M) (x : M)
    (D X Y Z W : TangentSpace I x) :
    iterCov (I := I) g 4 (metricRm04 (I := I) (M := M) g) 1 x
        (vec5 (I := I) D X Y Z W) =
      g.inner x W (nablaRiemannOp (I := I) g x D X Y Z) :=
  nablaRm04_apply (I := I) (M := M) g x D X Y Z W


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem curvJet1_normSq_le_of_op
    (g : SmoothRiemannianMetric I M) {K : ℝ} (hK : 0 ≤ K)
    (hop : ∀ (x : M) (D X Y Z : TangentSpace I x),
      Real.sqrt (g.inner x (nablaRiemannOp (I := I) g x D X Y Z)
          (nablaRiemannOp (I := I) g x D X Y Z)) ≤
        K * Real.sqrt (g.inner x D D) * Real.sqrt (g.inner x X X) *
          Real.sqrt (g.inner x Y Y) * Real.sqrt (g.inner x Z Z))
    (x : M) :
    Real.sqrt (normSq0S (I := I) g x 5
        (iterCov (I := I) g 4 (metricRm04 (I := I) (M := M) g) 1 x)) ≤
      Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 5) * K := by
  classical
  obtain ⟨basis, hON⟩ := exists_gOrthonormalBasis (I := I) g x
  have hinv : MetricInverseInBasis_gen (I := I) g x basis
      (identityInvMetric (Idx := Fin (Module.finrank Real (TangentSpace I x)))) := by
    have h := metricInverseInBasis_of_orthonormal (I := I) g basis hON
    intro i j
    simpa [identityInvMetric, diagonalInvMetric] using h i j
  have hunit : ∀ i, g.inner x (basis i) (basis i) = 1 := by
    intro i; rw [hON i i]; simp
  have hcompB : ∀ slots : Fin 5 → Fin (Module.finrank Real (TangentSpace I x)),
      |component0S (I := I) basis
        (iterCov (I := I) g 4 (metricRm04 (I := I) (M := M) g) 1 x) slots| ≤ K := by
    intro slots
    have hvec : (fun a : Fin 5 => basis (slots a)) =
        vec5 (I := I) (basis (slots 0)) (basis (slots 1)) (basis (slots 2))
          (basis (slots 3)) (basis (slots 4)) := by
      funext a
      fin_cases a <;> simp [vec5]
    have hval : component0S (I := I) basis
        (iterCov (I := I) g 4 (metricRm04 (I := I) (M := M) g) 1 x) slots =
        g.inner x (basis (slots 4))
          (nablaRiemannOp (I := I) g x (basis (slots 0)) (basis (slots 1))
            (basis (slots 2)) (basis (slots 3))) := by
      rw [component0S, hvec]
      exact curvJet1_eval (I := I) (M := M) g x _ _ _ _ _
    rw [hval]
    set N : TangentSpace I x :=
      nablaRiemannOp (I := I) g x (basis (slots 0)) (basis (slots 1))
        (basis (slots 2)) (basis (slots 3)) with hN
    have hNN : Real.sqrt (g.inner x N N) ≤ K := by
      have h := hop x (basis (slots 0)) (basis (slots 1)) (basis (slots 2))
        (basis (slots 3))
      rw [hunit (slots 0), hunit (slots 1), hunit (slots 2), hunit (slots 3)] at h
      simpa [hN] using h
    calc |g.inner x (basis (slots 4)) N|
        ≤ Real.sqrt (g.inner x (basis (slots 4)) (basis (slots 4))) *
            Real.sqrt (g.inner x N N) :=
          abs_metric_inner_le_sqrt_metric_quadratic (I := I) (M := M) g x _ _
      _ = Real.sqrt (g.inner x N N) := by rw [hunit (slots 4)]; simp
      _ ≤ K := hNN
  have hcard := normSq0S_le_card_of_component_bound (I := I) g x 5 basis hinv
    (iterCov (I := I) g 4 (metricRm04 (I := I) (M := M) g) 1 x) K hK hcompB
  have hfr : Module.finrank Real (TangentSpace I x) = Module.finrank ℝ E := rfl
  have hcardval :
      (Fintype.card (Fin 5 → Fin (Module.finrank Real (TangentSpace I x))) : ℝ) =
        (Module.finrank ℝ E : ℝ) ^ 5 := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, hfr]
    push_cast
    ring
  rw [hcardval] at hcard
  calc Real.sqrt (normSq0S (I := I) g x 5
        (iterCov (I := I) g 4 (metricRm04 (I := I) (M := M) g) 1 x))
      ≤ Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 5 * K ^ 2) := Real.sqrt_le_sqrt hcard
    _ = Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 5) * K := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hK]


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] in
theorem covDerivConnectionDifference_congr
    (g₂ g₁ : SmoothRiemannianMetric I M)
    (W X Y W' X' Y' : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    {x : M} (hW : W x = W' x) (hX : X x = X' x) (hY : Y x = Y' x) :
    covDerivConnectionDifference (I := I) g₂ g₁ W X Y x =
      covDerivConnectionDifference (I := I) g₂ g₁ W' X' Y' x := by
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
  have : ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := 1)
  have hpair : ∀ Z : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _),
      g₁.inner x (covDerivConnectionDifference (I := I) g₂ g₁ W X Y x) (Z x) =
        g₁.inner x (covDerivConnectionDifference (I := I) g₂ g₁ W' X' Y' x) (Z x) := by
    intro Z
    have h1 := connectionDifference_koszul_deriv (I := I) g₁ g₂ W X Y Z x
    have h2 := connectionDifference_koszul_deriv (I := I) g₁ g₂ W' X' Y' Z x
    simp only [← Tensor0SBundle.totalNabla0SFun_apply_section] at h1 h2
    rw [hW, hX, hY] at h1
    have h3 := h1.trans h2.symm
    linarith [h3]
  set a : TangentSpace I x := covDerivConnectionDifference (I := I) g₂ g₁ W X Y x with ha
  set b : TangentSpace I x := covDerivConnectionDifference (I := I) g₂ g₁ W' X' Y' x with hb
  have hZ := hpair (ContMDiffSection.mk (smoothExtensionTangent (I := I) x (a - b))
    (smoothExtensionTangent_contMDiff (I := I) x (a - b)))
  rw [ContMDiffSection.coeFn_mk, smoothExtensionTangent_eq] at hZ
  have hsym1 : g₁.inner x a (a - b) = g₁.inner x (a - b) a := g₁.symm x a (a - b)
  have hsym2 : g₁.inner x b (a - b) = g₁.inner x (a - b) b := g₁.symm x b (a - b)
  have hzero : g₁.inner x (a - b) (a - b) = 0 := by
    rw [map_sub, ← hsym1, ← hsym2, hZ, sub_self]
  have hsub : a - b = 0 := by
    by_contra hne
    exact (ne_of_gt (g₁.pos x (a - b) hne)) hzero
  exact sub_eq_zero.mp hsub


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] in
theorem covDerivConnectionDifference_eq_ext
    (g₂ g₁ : SmoothRiemannianMetric I M)
    (W X Y : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _)) (x : M) :
    covDerivConnectionDifference (I := I) g₂ g₁ W X Y x =
      covDerivConnectionDifference (I := I) g₂ g₁
        (smoothExtensionTangent (I := I) x (W x))
        (smoothExtensionTangent (I := I) x (X x))
        (smoothExtensionTangent (I := I) x (Y x)) x := by
  refine covDerivConnectionDifference_congr (I := I) g₂ g₁ W X Y
    (ContMDiffSection.mk (smoothExtensionTangent (I := I) x (W x))
      (smoothExtensionTangent_contMDiff (I := I) x (W x)))
    (ContMDiffSection.mk (smoothExtensionTangent (I := I) x (X x))
      (smoothExtensionTangent_contMDiff (I := I) x (X x)))
    (ContMDiffSection.mk (smoothExtensionTangent (I := I) x (Y x))
      (smoothExtensionTangent_contMDiff (I := I) x (Y x)))
    ?_ ?_ ?_ <;>
  · exact (smoothExtensionTangent_eq (I := I) _ _).symm

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem cov_apply_sub
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    {S T : Π b : M, TangentSpace I b} {x : M}
    (hS : MDiffAt (T% S) x) (hT : MDiffAt (T% T) x) (v : TangentSpace I x) :
    cov.toFun (fun p => S p - T p) x v = cov.toFun S x v - cov.toFun T x v := by
  have h := DifferentialGeometry.Geometry.Curvature.cov_toFun_sub
    (I := I) cov hS hT
  exact congrArg (fun L => L v) h

noncomputable def curvCovDerivOpAtOf
    (covD covR : CovariantDerivative I E (TangentSpace I : M → Type _))
    (D X Y Z : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _)) (x : M) : TangentSpace I x :=
  (covD (fun p : M =>
      connectionRiemannCurvatureField (I := I) covR
        (fun q : M => X q) (fun q : M => Y q) (fun q : M => Z q) p) x) (D x) -
    connectionRiemannCurvatureField (I := I) covR
      (fun p : M => (covD (fun q : M => X q) p) (D p))
      (fun p : M => Y p) (fun p : M => Z p) x -
    connectionRiemannCurvatureField (I := I) covR
      (fun p : M => X p)
      (fun p : M => (covD (fun q : M => Y q) p) (D p))
      (fun p : M => Z p) x -
    connectionRiemannCurvatureField (I := I) covR
      (fun p : M => X p) (fun p : M => Y p)
      (fun p : M => (covD (fun q : M => Z q) p) (D p)) x


omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem curvCovDerivOpAtOf_self
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (D X Y Z : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _)) (x : M) :
    curvCovDerivOpAtOf (I := I) cov cov D X Y Z x =
      curvCovDerivOpAt (I := I) cov D X Y Z x := rfl

noncomputable def palSec (gB g₀ : SmoothRiemannianMetric I M)
    (X Y Z : Π b : M, TangentSpace I b) : Π b : M, TangentSpace I b :=
  fun p =>
    connectionRiemannCurvatureField (I := I) (LeviCivita (I := I) g₀) X Y Z p -
      connectionRiemannCurvatureField (I := I) (LeviCivita (I := I) gB) X Y Z p

noncomputable def covDerivPal (gB g₀ : SmoothRiemannianMetric I M)
    (D X Y Z : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _)) (x : M) : TangentSpace I x :=
  (LeviCivita (I := I) gB).toFun (palSec (I := I) gB g₀
      (fun q : M => X q) (fun q : M => Y q) (fun q : M => Z q)) x (D x) -
    palSec (I := I) gB g₀
      (fun p : M => ((LeviCivita (I := I) gB) (fun q : M => X q) p) (D p))
      (fun p : M => Y p) (fun p : M => Z p) x -
    palSec (I := I) gB g₀ (fun p : M => X p)
      (fun p : M => ((LeviCivita (I := I) gB) (fun q : M => Y q) p) (D p))
      (fun p : M => Z p) x -
    palSec (I := I) gB g₀ (fun p : M => X p) (fun p : M => Y p)
      (fun p : M => ((LeviCivita (I := I) gB) (fun q : M => Z q) p) (D p)) x


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem curvCovDerivOf_sub_base (gB g₀ : SmoothRiemannianMetric I M)
    (D X Y Z : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _)) (x : M) :
    curvCovDerivOpAtOf (I := I) (LeviCivita (I := I) gB) (LeviCivita (I := I) g₀)
        D X Y Z x -
      curvCovDerivOpAt (I := I) (LeviCivita (I := I) gB) D X Y Z x =
      covDerivPal (I := I) gB g₀ D X Y Z x := by
  classical
  have hcov₀ : CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (I := I) (E := E) (M := M) (LeviCivita (I := I) gB) (∞ : WithTop ℕ∞) :=
    leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally (I := I) (M := M) gB
  have hcov₁ : CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (I := I) (E := E) (M := M) (LeviCivita (I := I) g₀) (∞ : WithTop ℕ∞) :=
    leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally (I := I) (M := M) g₀
  have hR₁ : MDiffAt (T% (fun p : M =>
      connectionRiemannCurvatureField (I := I) (LeviCivita (I := I) g₀)
        (fun q : M => X q) (fun q : M => Y q) (fun q : M => Z q) p)) x :=
    (DifferentialGeometry.Geometry.Curvature.CovariantDerivative.curvField_contMDiffAt (I := I)
      (LeviCivita (I := I) g₀) hcov₁ X Y Z x).mdifferentiableAt (by simp)
  have hR₀ : MDiffAt (T% (fun p : M =>
      connectionRiemannCurvatureField (I := I) (LeviCivita (I := I) gB)
        (fun q : M => X q) (fun q : M => Y q) (fun q : M => Z q) p)) x :=
    (DifferentialGeometry.Geometry.Curvature.CovariantDerivative.curvField_contMDiffAt (I := I)
      (LeviCivita (I := I) gB) hcov₀ X Y Z x).mdifferentiableAt (by simp)
  unfold curvCovDerivOpAtOf curvCovDerivOpAt covDerivPal
  rw [show (palSec (I := I) gB g₀ (fun q : M => X q) (fun q : M => Y q)
        (fun q : M => Z q)) =
      (fun p : M =>
        connectionRiemannCurvatureField (I := I) (LeviCivita (I := I) g₀)
          (fun q : M => X q) (fun q : M => Y q) (fun q : M => Z q) p -
        connectionRiemannCurvatureField (I := I) (LeviCivita (I := I) gB)
          (fun q : M => X q) (fun q : M => Y q) (fun q : M => Z q) p) from rfl,
    cov_apply_sub (I := I) (LeviCivita (I := I) gB) hR₁ hR₀ (D x)]
  simp only [palSec]
  abel

end RicciFlow
end PDE
end DifferentialGeometry
