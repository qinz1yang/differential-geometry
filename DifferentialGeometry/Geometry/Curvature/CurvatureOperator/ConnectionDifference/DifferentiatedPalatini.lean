import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.ConnectionDifference.RicciPalatini
import DifferentialGeometry.Geometry.Connection.LeviCivita.Smooth.CovariantDerivative
import DifferentialGeometry.Geometry.Curvature.Bianchi

set_option autoImplicit false

noncomputable section


open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle

namespace DifferentialGeometry
namespace Integral
namespace Connection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
private local instance : IsManifold I 1 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞)
    (by decide : (1 : WithTop ℕ∞) ≤ ∞)
private local instance : IsManifold I 2 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞)
    (by decide : (2 : WithTop ℕ∞) ≤ ∞)
private local instance : IsManifold I (1 + 1) M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞)
    (by decide : ((1 : WithTop ℕ∞) + 1) ≤ ∞)
private local instance :
    ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I :=
  TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := 1)

noncomputable def covDerivConnectionDifference2 (gB g₀ : SmoothRiemannianMetric I M)
    (D X Y Z : Π b : M, TangentSpace I b) (x : M) : TangentSpace I x :=
  covApply (LeviCivita (I := I) gB) D
      (fun p => covDerivConnectionDifference (I := I) gB g₀ X Y Z p) x -
    covDerivConnectionDifference (I := I) gB g₀
      (covApply (LeviCivita (I := I) gB) D X) Y Z x -
    covDerivConnectionDifference (I := I) gB g₀ X
      (covApply (LeviCivita (I := I) gB) D Y) Z x -
    covDerivConnectionDifference (I := I) gB g₀ X Y
      (covApply (LeviCivita (I := I) gB) D Z) x

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem covDerivConnectionDifference2_eq (gB g₀ : SmoothRiemannianMetric I M)
    (D X Y Z : Π b : M, TangentSpace I b) (x : M) :
    covDerivConnectionDifference2 (I := I) gB g₀ D X Y Z x =
      covApply (LeviCivita (I := I) gB) D
          (fun p => covDerivConnectionDifference (I := I) gB g₀ X Y Z p) x -
        covDerivConnectionDifference (I := I) gB g₀
          (covApply (LeviCivita (I := I) gB) D X) Y Z x -
        covDerivConnectionDifference (I := I) gB g₀ X
          (covApply (LeviCivita (I := I) gB) D Y) Z x -
        covDerivConnectionDifference (I := I) gB g₀ X Y
          (covApply (LeviCivita (I := I) gB) D Z) x :=
  rfl

noncomputable def palatiniDiffSec (gB g₀ : SmoothRiemannianMetric I M)
    (X Y Z : Π b : M, TangentSpace I b) : Π b : M, TangentSpace I b :=
  fun p =>
    connectionRiemannCurvatureField (I := I) (LeviCivita (I := I) g₀) X Y Z p -
      connectionRiemannCurvatureField (I := I) (LeviCivita (I := I) gB) X Y Z p

private noncomputable def palQuad (gB g₀ : SmoothRiemannianMetric I M)
    (X Y Z : Π b : M, TangentSpace I b) : Π b : M, TangentSpace I b :=
  diffSec (LeviCivita (I := I) gB) (LeviCivita (I := I) g₀) X
    (diffSec (LeviCivita (I := I) gB) (LeviCivita (I := I) g₀) Y Z)

private noncomputable def palRhs (gB g₀ : SmoothRiemannianMetric I M)
    (X Y Z : Π b : M, TangentSpace I b) : Π b : M, TangentSpace I b :=
  fun p =>
    covDerivConnectionDifference (I := I) gB g₀ X Y Z p -
        covDerivConnectionDifference (I := I) gB g₀ Y X Z p +
      (palQuad (I := I) gB g₀ X Y Z p - palQuad (I := I) gB g₀ Y X Z p)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] in
private theorem palSec_eq_rhs
    (gB g₀ : SmoothRiemannianMetric I M)
    {X Y Z : Π p : M, TangentSpace I p}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) (∞ : WithTop ℕ∞) (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) (∞ : WithTop ℕ∞) (T% Y))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) (∞ : WithTop ℕ∞) (T% Z)) :
    palatiniDiffSec (I := I) gB g₀ X Y Z =
      palRhs (I := I) gB g₀ X Y Z := by
  funext p
  have htor :
      (LeviCivita (I := I) gB).torsion = 0 :=
    LeviCivita_torsion_eq_zero (I := I) gB
  have hpal := riemannSec_difference
    (LeviCivita (I := I) gB) (LeviCivita (I := I) g₀)
    hX hY hZ htor p
  change
    riemannSec (LeviCivita (I := I) g₀) X Y Z p -
        riemannSec (LeviCivita (I := I) gB) X Y Z p =
      _
  rw [hpal]
  simp only [palRhs, palQuad, covDerivConnectionDifference_eq]
  abel

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] in
private theorem palQuad_smooth
    (gB g₀ : SmoothRiemannianMetric I M)
    (X Y Z : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _)) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) (∞ : WithTop ℕ∞)
      (T% (palQuad (I := I) gB g₀ (fun p => X p) (fun p => Y p) (fun p => Z p))) := by
  have htop : ((∞ : WithTop ℕ∞) + 1) = (∞ : WithTop ℕ∞) := by
    rw [ENat.coe_top_add_one]
  have hinner : ContMDiff I (I.prod 𝓘(ℝ, E)) (∞ : WithTop ℕ∞)
      (T% (diffSec (LeviCivita (I := I) gB) (LeviCivita (I := I) g₀)
        (fun p => Y p) (fun p => Z p))) := by
    apply diffSec_contMDiff
    · exact Y.contMDiff
    · simpa [htop] using Z.contMDiff
  unfold palQuad
  apply diffSec_contMDiff
  · exact X.contMDiff
  · simpa [htop] using hinner

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem covDConnectionDifference_smooth
    (gB g₀ : SmoothRiemannianMetric I M)
    (D X Y : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _)) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) (∞ : WithTop ℕ∞)
      (T% (fun p => covDerivConnectionDifference (I := I) gB g₀
        (fun b => D b) (fun b => X b) (fun b => Y b) p)) := by
  let _ : CovariantDerivative.ContMDiffCovariantDerivative
      (LeviCivita (I := I) gB) (∞ : WithTop ℕ∞) :=
    leviCivitaConnectionOfMetric_contMDiffCovariantDerivative (I := I) gB
  let _ : CovariantDerivative.ContMDiffCovariantDerivative
      (LeviCivita (I := I) g₀) (∞ : WithTop ℕ∞) :=
    leviCivitaConnectionOfMetric_contMDiffCovariantDerivative (I := I) g₀
  have hcast : ∀ (S : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _)),
      ContMDiff I (I.prod 𝓘(ℝ, E)) ((∞ : WithTop ℕ∞) + 1)
        (T% (fun b => S b)) := by
    intro S
    rw [show ((∞ : WithTop ℕ∞) + 1) = (∞ : WithTop ℕ∞) from by
      rw [ENat.coe_top_add_one]]
    exact S.contMDiff
  have hDXY : ContMDiff I (I.prod 𝓘(ℝ, E)) (∞ : WithTop ℕ∞)
      (T% (diffSec (LeviCivita (I := I) gB) (LeviCivita (I := I) g₀)
        (fun b => X b) (fun b => Y b))) :=
    diffSec_contMDiff (LeviCivita (I := I) gB) (LeviCivita (I := I) g₀)
      X.contMDiff (hcast Y)
  have hDXYc : ContMDiff I (I.prod 𝓘(ℝ, E)) ((∞ : WithTop ℕ∞) + 1)
      (T% (diffSec (LeviCivita (I := I) gB) (LeviCivita (I := I) g₀)
        (fun b => X b) (fun b => Y b))) := by
    rw [show ((∞ : WithTop ℕ∞) + 1) = (∞ : WithTop ℕ∞) from by
      rw [ENat.coe_top_add_one]]
    exact hDXY
  have hA : ContMDiffOn I (I.prod 𝓘(ℝ, E)) (∞ : WithTop ℕ∞)
      (T% (covApply (LeviCivita (I := I) gB) (fun b => D b)
        (diffSec (LeviCivita (I := I) gB) (LeviCivita (I := I) g₀)
          (fun b => X b) (fun b => Y b)))) Set.univ :=
    covApply_contMDiffOn (cov := LeviCivita (I := I) gB) D.contMDiff hDXYc
  have hDX : ContMDiff I (I.prod 𝓘(ℝ, E)) (∞ : WithTop ℕ∞)
      (T% (covApply (LeviCivita (I := I) gB) (fun b => D b) (fun b => X b))) :=
    contMDiffOn_univ.mp
      (covApply_contMDiffOn (cov := LeviCivita (I := I) gB) D.contMDiff (hcast X))
  have hDY : ContMDiff I (I.prod 𝓘(ℝ, E)) (∞ : WithTop ℕ∞)
      (T% (covApply (LeviCivita (I := I) gB) (fun b => D b) (fun b => Y b))) :=
    contMDiffOn_univ.mp
      (covApply_contMDiffOn (cov := LeviCivita (I := I) gB) D.contMDiff (hcast Y))
  have hDYc : ContMDiff I (I.prod 𝓘(ℝ, E)) ((∞ : WithTop ℕ∞) + 1)
      (T% (covApply (LeviCivita (I := I) gB) (fun b => D b) (fun b => Y b))) := by
    rw [show ((∞ : WithTop ℕ∞) + 1) = (∞ : WithTop ℕ∞) from by
      rw [ENat.coe_top_add_one]]
    exact hDY
  have hB : ContMDiff I (I.prod 𝓘(ℝ, E)) (∞ : WithTop ℕ∞)
      (T% (diffSec (LeviCivita (I := I) gB) (LeviCivita (I := I) g₀)
        (covApply (LeviCivita (I := I) gB) (fun b => D b) (fun b => X b))
        (fun b => Y b))) :=
    diffSec_contMDiff (LeviCivita (I := I) gB) (LeviCivita (I := I) g₀)
      hDX (hcast Y)
  have hC : ContMDiff I (I.prod 𝓘(ℝ, E)) (∞ : WithTop ℕ∞)
      (T% (diffSec (LeviCivita (I := I) gB) (LeviCivita (I := I) g₀)
        (fun b => X b)
        (covApply (LeviCivita (I := I) gB) (fun b => D b) (fun b => Y b)))) :=
    diffSec_contMDiff (LeviCivita (I := I) gB) (LeviCivita (I := I) g₀)
      X.contMDiff hDYc
  rw [← contMDiffOn_univ]
  refine ((hA.sub_section hB.contMDiffOn).sub_section hC.contMDiffOn).congr
    (fun p _hp => ?_)
  rfl

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem cov_sub_apply
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    {S T : Π b : M, TangentSpace I b} {x : M}
    (hS : ContMDiff I (I.prod 𝓘(ℝ, E)) (∞ : WithTop ℕ∞) (T% S))
    (hT : ContMDiff I (I.prod 𝓘(ℝ, E)) (∞ : WithTop ℕ∞) (T% T))
    (v : TangentSpace I x) :
    cov.toFun (fun p => S p - T p) x v =
      cov.toFun S x v - cov.toFun T x v := by
  have hSx := (hS x).mdifferentiableAt (by simp)
  have hTx := (hT x).mdifferentiableAt (by simp)
  have hST : (fun p => S p - T p) = S + (-T) := by
    funext p
    simp [sub_eq_add_neg]
  have hneg : cov.toFun (-T) x = (-1 : ℝ) • cov.toFun T x := by
    simpa using cov.isCovariantDerivativeOnUniv.smul_const (-1 : ℝ) hTx
  rw [hST, cov.isCovariantDerivativeOnUniv.add hSx
    (mdifferentiableAt_neg_section hTx), hneg]
  rw [add_apply]
  have hsmul :
      (((-1 : ℝ) • cov.toFun T x) v) =
        (-1 : ℝ) • cov.toFun T x v := rfl
  rw [hsmul, neg_one_smul]
  simp only [sub_eq_add_neg]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem cov_add_apply
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    {S T : Π b : M, TangentSpace I b} {x : M}
    (hS : ContMDiff I (I.prod 𝓘(ℝ, E)) (∞ : WithTop ℕ∞) (T% S))
    (hT : ContMDiff I (I.prod 𝓘(ℝ, E)) (∞ : WithTop ℕ∞) (T% T))
    (v : TangentSpace I x) :
    cov.toFun (fun p => S p + T p) x v =
      cov.toFun S x v + cov.toFun T x v := by
  have hSx := (hS x).mdifferentiableAt (by simp)
  have hTx := (hT x).mdifferentiableAt (by simp)
  have hST : (fun p => S p + T p) = S + T := by
    funext p
    rfl
  rw [hST]
  exact congrArg (fun L => L v) (cov.isCovariantDerivativeOnUniv.add hSx hTx)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem diffSec_sub
    (cov₀ cov₁ : CovariantDerivative I E (TangentSpace I : M → Type _))
    {X S T : Π b : M, TangentSpace I b} (x : M) :
    diffSec cov₀ cov₁ X (fun p => S p - T p) x =
      diffSec cov₀ cov₁ X S x - diffSec cov₀ cov₁ X T x := by
  simp only [diffSec, map_sub, sub_apply]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem cov_palQuad
    (gB g₀ : SmoothRiemannianMetric I M)
    (D X Y Z : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _)) (x : M) :
    (LeviCivita (I := I) gB).toFun
          (palQuad (I := I) gB g₀ (fun p => X p) (fun p => Y p) (fun p => Z p))
          x (D x) -
        palQuad (I := I) gB g₀
          (fun p => ((LeviCivita (I := I) gB) (fun q => X q) p) (D p))
          (fun p => Y p) (fun p => Z p) x -
      palQuad (I := I) gB g₀ (fun p => X p)
          (fun p => ((LeviCivita (I := I) gB) (fun q => Y q) p) (D p))
          (fun p => Z p) x -
      palQuad (I := I) gB g₀ (fun p => X p) (fun p => Y p)
          (fun p => ((LeviCivita (I := I) gB) (fun q => Z q) p) (D p)) x =
      covDerivConnectionDifference (I := I) gB g₀ D X
          (fun p => diffSec (LeviCivita (I := I) gB) (LeviCivita (I := I) g₀)
            (fun q => Y q) (fun q => Z q) p) x +
        diffSec (LeviCivita (I := I) gB) (LeviCivita (I := I) g₀)
          (fun p => X p)
          (fun p => covDerivConnectionDifference (I := I) gB g₀ D Y Z p) x := by
  have hYZ :
      diffSec (LeviCivita (I := I) gB) (LeviCivita (I := I) g₀)
          (fun p => Y p) (fun p => Z p) =
        (fun p =>
          CovariantDerivative.difference
            (LeviCivita (I := I) g₀) (LeviCivita (I := I) gB) p (Z p) (Y p)) :=
    rfl
  unfold palQuad covDerivConnectionDifference covDerivDiff covApply
  rw [diffSec_sub (I := I), diffSec_sub (I := I)]
  rw [hYZ]
  simp only [diffSec]
  abel

noncomputable def covDerivPalatini (gB g₀ : SmoothRiemannianMetric I M)
    (D X Y Z : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _)) (x : M) : TangentSpace I x :=
  (LeviCivita (I := I) gB).toFun
      (palatiniDiffSec (I := I) gB g₀
        (fun p => X p) (fun p => Y p) (fun p => Z p)) x (D x) -
    palatiniDiffSec (I := I) gB g₀
      (fun p => ((LeviCivita (I := I) gB) (fun q => X q) p) (D p))
      (fun p => Y p) (fun p => Z p) x -
    palatiniDiffSec (I := I) gB g₀ (fun p => X p)
      (fun p => ((LeviCivita (I := I) gB) (fun q => Y q) p) (D p))
      (fun p => Z p) x -
    palatiniDiffSec (I := I) gB g₀ (fun p => X p) (fun p => Y p)
      (fun p => ((LeviCivita (I := I) gB) (fun q => Z q) p) (D p)) x

noncomputable def mixedCurvDeriv (gD gR : SmoothRiemannianMetric I M)
    (D X Y Z : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _)) (x : M) : TangentSpace I x :=
  (LeviCivita (I := I) gD).toFun
      (fun p : M =>
        connectionRiemannCurvatureField (I := I) (LeviCivita (I := I) gR)
          (fun q : M => X q) (fun q : M => Y q) (fun q : M => Z q) p)
      x (D x) -
    connectionRiemannCurvatureField (I := I) (LeviCivita (I := I) gR)
      (fun p : M => ((LeviCivita (I := I) gD) (fun q => X q) p) (D p))
      (fun p : M => Y p) (fun p : M => Z p) x -
    connectionRiemannCurvatureField (I := I) (LeviCivita (I := I) gR)
      (fun p : M => X p)
      (fun p : M => ((LeviCivita (I := I) gD) (fun q => Y q) p) (D p))
      (fun p : M => Z p) x -
    connectionRiemannCurvatureField (I := I) (LeviCivita (I := I) gR)
      (fun p : M => X p) (fun p : M => Y p)
      (fun p : M => ((LeviCivita (I := I) gD) (fun q => Z q) p) (D p)) x

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem mixed_sub_eq_pal
    (gB g₀ : SmoothRiemannianMetric I M)
    (D X Y Z : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _)) (x : M) :
    mixedCurvDeriv (I := I) gB g₀ D X Y Z x -
        curvCovDerivOpAt (I := I) (LeviCivita (I := I) gB) D X Y Z x =
      covDerivPalatini (I := I) gB g₀ D X Y Z x := by
  have hcov₀ : CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (I := I) (E := E) (M := M) (LeviCivita (I := I) gB)
      (∞ : WithTop ℕ∞) :=
    leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
      (I := I) (M := M) gB
  have hcov₁ : CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (I := I) (E := E) (M := M) (LeviCivita (I := I) g₀)
      (∞ : WithTop ℕ∞) :=
    leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
      (I := I) (M := M) g₀
  have hR₁ : ContMDiff I (I.prod 𝓘(ℝ, E)) (∞ : WithTop ℕ∞)
      (T% (fun p : M =>
        connectionRiemannCurvatureField (I := I) (LeviCivita (I := I) g₀)
          (fun q : M => X q) (fun q : M => Y q) (fun q : M => Z q) p)) :=
    fun y => CovariantDerivative.curvField_contMDiffAt
      (I := I) (LeviCivita (I := I) g₀) hcov₁ X Y Z y
  have hR₀ : ContMDiff I (I.prod 𝓘(ℝ, E)) (∞ : WithTop ℕ∞)
      (T% (fun p : M =>
        connectionRiemannCurvatureField (I := I) (LeviCivita (I := I) gB)
          (fun q : M => X q) (fun q : M => Y q) (fun q : M => Z q) p)) :=
    fun y => CovariantDerivative.curvField_contMDiffAt
      (I := I) (LeviCivita (I := I) gB) hcov₀ X Y Z y
  unfold mixedCurvDeriv curvCovDerivOpAt covDerivPalatini
  rw [show palatiniDiffSec (I := I) gB g₀
        (fun q : M => X q) (fun q : M => Y q) (fun q : M => Z q) =
      (fun p : M =>
        connectionRiemannCurvatureField (I := I) (LeviCivita (I := I) g₀)
            (fun q : M => X q) (fun q : M => Y q) (fun q : M => Z q) p -
          connectionRiemannCurvatureField (I := I) (LeviCivita (I := I) gB)
            (fun q : M => X q) (fun q : M => Y q) (fun q : M => Z q) p) from rfl,
    cov_sub_apply (I := I) (LeviCivita (I := I) gB) hR₁ hR₀ (D x)]
  simp only [palatiniDiffSec]
  abel

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] in
theorem covDerivPal_eq
    (gB g₀ : SmoothRiemannianMetric I M)
    (D X Y Z : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _)) (x : M) :
    covDerivPalatini (I := I) gB g₀ D X Y Z x =
      covDerivConnectionDifference2 (I := I) gB g₀ D X Y Z x -
          covDerivConnectionDifference2 (I := I) gB g₀ D Y X Z x +
        (covDerivConnectionDifference (I := I) gB g₀ D X
            (fun p => diffSec (LeviCivita (I := I) gB) (LeviCivita (I := I) g₀)
              (fun q => Y q) (fun q => Z q) p) x +
          diffSec (LeviCivita (I := I) gB) (LeviCivita (I := I) g₀)
            (fun p => X p)
            (fun p => covDerivConnectionDifference (I := I) gB g₀ D Y Z p) x) -
        (covDerivConnectionDifference (I := I) gB g₀ D Y
            (fun p => diffSec (LeviCivita (I := I) gB) (LeviCivita (I := I) g₀)
              (fun q => X q) (fun q => Z q) p) x +
          diffSec (LeviCivita (I := I) gB) (LeviCivita (I := I) g₀)
            (fun p => Y p)
            (fun p => covDerivConnectionDifference (I := I) gB g₀ D X Z p) x) := by
  have htop : ((∞ : WithTop ℕ∞) + 1) = (∞ : WithTop ℕ∞) := by
    rw [ENat.coe_top_add_one]
  have hDX : ContMDiff I (I.prod 𝓘(ℝ, E)) (∞ : WithTop ℕ∞)
      (T% (fun p : M =>
        ((LeviCivita (I := I) gB) (fun q : M => X q) p) (D p))) := by
    rw [← contMDiffOn_univ]
    apply covApply_contMDiffOn
    · exact D.contMDiff
    · simpa [htop] using X.contMDiff
  have hDY : ContMDiff I (I.prod 𝓘(ℝ, E)) (∞ : WithTop ℕ∞)
      (T% (fun p : M =>
        ((LeviCivita (I := I) gB) (fun q : M => Y q) p) (D p))) := by
    rw [← contMDiffOn_univ]
    apply covApply_contMDiffOn
    · exact D.contMDiff
    · simpa [htop] using Y.contMDiff
  have hDZ : ContMDiff I (I.prod 𝓘(ℝ, E)) (∞ : WithTop ℕ∞)
      (T% (fun p : M =>
        ((LeviCivita (I := I) gB) (fun q : M => Z q) p) (D p))) := by
    rw [← contMDiffOn_univ]
    apply covApply_contMDiffOn
    · exact D.contMDiff
    · simpa [htop] using Z.contMDiff
  have hCXY := covDConnectionDifference_smooth (I := I) gB g₀ X Y Z
  have hCYX := covDConnectionDifference_smooth (I := I) gB g₀ Y X Z
  have hQXY := palQuad_smooth (I := I) gB g₀ X Y Z
  have hQYX := palQuad_smooth (I := I) gB g₀ Y X Z
  have hCsub : ContMDiff I (I.prod 𝓘(ℝ, E)) (∞ : WithTop ℕ∞)
      (T% (fun p =>
        covDerivConnectionDifference (I := I) gB g₀ X Y Z p -
          covDerivConnectionDifference (I := I) gB g₀ Y X Z p)) := by
    simpa only [Pi.sub_apply] using hCXY.sub_section hCYX
  have hQsub : ContMDiff I (I.prod 𝓘(ℝ, E)) (∞ : WithTop ℕ∞)
      (T% (fun p =>
        palQuad (I := I) gB g₀ (fun q => X q) (fun q => Y q) (fun q => Z q) p -
          palQuad (I := I) gB g₀ (fun q => Y q) (fun q => X q) (fun q => Z q) p)) := by
    simpa only [Pi.sub_apply] using hQXY.sub_section hQYX
  have hpal := palSec_eq_rhs (I := I) gB g₀ X.contMDiff Y.contMDiff Z.contMDiff
  have hpalX := palSec_eq_rhs (I := I) gB g₀ hDX Y.contMDiff Z.contMDiff
  have hpalY := palSec_eq_rhs (I := I) gB g₀ X.contMDiff hDY Z.contMDiff
  have hpalZ := palSec_eq_rhs (I := I) gB g₀ X.contMDiff Y.contMDiff hDZ
  have hpalXx := congrFun hpalX x
  have hpalYx := congrFun hpalY x
  have hpalZx := congrFun hpalZ x
  unfold covDerivPalatini
  rw [hpal, hpalXx, hpalYx, hpalZx]
  unfold palRhs
  rw [cov_add_apply (I := I) (LeviCivita (I := I) gB)
    hCsub hQsub (D x)]
  rw [cov_sub_apply (I := I) (LeviCivita (I := I) gB) hCXY hCYX (D x)]
  rw [cov_sub_apply (I := I) (LeviCivita (I := I) gB) hQXY hQYX (D x)]
  rw [covDerivConnectionDifference2_eq (I := I) gB g₀ D X Y Z x,
    covDerivConnectionDifference2_eq (I := I) gB g₀ D Y X Z x]
  rw [← cov_palQuad (I := I) gB g₀ D X Y Z x,
    ← cov_palQuad (I := I) gB g₀ D Y X Z x]
  unfold covApply
  abel

end Connection
end Integral
end DifferentialGeometry
