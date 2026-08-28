import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Uniform.PalatiniFirstDerivative

import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Uniform.CurvaturePackage
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.PointwiseCurvatureDerivative
import DifferentialGeometry.Geometry.Connection.ConnectionDifference

set_option autoImplicit false

noncomputable section


open Bundle Manifold Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Analysis.Laplacian

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow

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
private local instance : IsManifold I (1 + 1) M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞)
    (by decide : ((1 : WithTop ℕ∞) + 1) ≤ ∞)
private local instance :
    ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I :=
  TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := 1)

private noncomputable def extSec1 (x : M) (v : TangentSpace I x) :
    ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
  ContMDiffSection.mk (smoothExtensionTangent (I := I) x v)
    (smoothExtensionTangent_contMDiff (I := I) x v)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
@[simp] private theorem extSec1_apply (x : M) (v : TangentSpace I x) :
    extSec1 (I := I) x v x = v :=
  smoothExtensionTangent_eq (I := I) x v

noncomputable def curvConnAt
    (gBase g₀ : SmoothRiemannianMetric I M) (x : M)
    (D X Y Z : TangentSpace I x) : TangentSpace I x :=
  let A := DeTurck.connectionDifference (I := I) g₀ gBase x
  let R := riemannOp (cov := LeviCivita (I := I) g₀) x
  A (R X Y Z) D -
      R (A X D) Y Z -
    R X (A Y D) Z -
  R X Y (A Z D)


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] in
theorem nablaRm_split
    (gBase g₀ : SmoothRiemannianMetric I M) (x : M)
    (D X Y Z : TangentSpace I x) :
    nablaRiemannOp (I := I) g₀ x D X Y Z =
      curvConnAt (I := I) gBase g₀ x D X Y Z +
        covDerivPalatini (I := I) gBase g₀
          (extSec1 (I := I) x D) (extSec1 (I := I) x X)
          (extSec1 (I := I) x Y) (extSec1 (I := I) x Z) x +
        nablaRiemannOp (I := I) gBase x D X Y Z := by
  classical
  let Ds := extSec1 (I := I) x D
  let Xs := extSec1 (I := I) x X
  let Ys := extSec1 (I := I) x Y
  let Zs := extSec1 (I := I) x Z
  let covB := LeviCivita (I := I) gBase
  let cov₀ := LeviCivita (I := I) g₀
  let Rsec : Π p : M, TangentSpace I p := fun p =>
    connectionRiemannCurvatureField (I := I) cov₀
      (fun q : M => Xs q) (fun q : M => Ys q) (fun q : M => Zs q) p
  have hcov₀ : CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (I := I) (E := E) (M := M) cov₀ (∞ : WithTop ℕ∞) := by
    dsimp only [cov₀]
    rw [LeviCivita_eq_leviCivitaConnectionOfMetric]
    exact leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
      (I := I) (M := M) g₀
  have hR : ContMDiff I (I.prod 𝓘(ℝ, E)) (∞ : WithTop ℕ∞) (T% Rsec) :=
    fun p => by
      simpa [Rsec] using
        CovariantDerivative.curvField_contMDiffAt
          (I := I) cov₀ hcov₀ Xs Ys Zs p
  have houter0 := DeTurck.connectionDifference_apply (I := I) g₀ gBase
    ((hR x).mdifferentiableAt (by simp)) (Ds x)
  have hX0 := DeTurck.connectionDifference_apply (I := I) g₀ gBase
    (Xs.contMDiff.contMDiffAt.mdifferentiableAt (by simp)) (Ds x)
  have hY0 := DeTurck.connectionDifference_apply (I := I) g₀ gBase
    (Ys.contMDiff.contMDiffAt.mdifferentiableAt (by simp)) (Ds x)
  have hZ0 := DeTurck.connectionDifference_apply (I := I) g₀ gBase
    (Zs.contMDiff.contMDiffAt.mdifferentiableAt (by simp)) (Ds x)
  have houter :
      cov₀.toFun Rsec x (Ds x) =
        covB.toFun Rsec x (Ds x) +
          DeTurck.connectionDifference (I := I) g₀ gBase x (Rsec x) (Ds x) := by
    have h := (sub_eq_iff_eq_add).mp houter0.symm
    simpa [covB, cov₀, add_comm] using h
  have hX :
      covApply cov₀ (fun p => Ds p) (fun p => Xs p) x =
        covApply covB (fun p => Ds p) (fun p => Xs p) x +
          DeTurck.connectionDifference (I := I) g₀ gBase x (Xs x) (Ds x) := by
    have h := (sub_eq_iff_eq_add).mp hX0.symm
    simpa [covApply, covB, cov₀, add_comm] using h
  have hY :
      covApply cov₀ (fun p => Ds p) (fun p => Ys p) x =
        covApply covB (fun p => Ds p) (fun p => Ys p) x +
          DeTurck.connectionDifference (I := I) g₀ gBase x (Ys x) (Ds x) := by
    have h := (sub_eq_iff_eq_add).mp hY0.symm
    simpa [covApply, covB, cov₀, add_comm] using h
  have hZ :
      covApply cov₀ (fun p => Ds p) (fun p => Zs p) x =
        covApply covB (fun p => Ds p) (fun p => Zs p) x +
          DeTurck.connectionDifference (I := I) g₀ gBase x (Zs x) (Ds x) := by
    have h := (sub_eq_iff_eq_add).mp hZ0.symm
    simpa [covApply, covB, cov₀, add_comm] using h
  have houterRaw :
      (LeviCivita (I := I) g₀).toFun
          (fun p : M =>
            connectionRiemannCurvatureField (I := I) (LeviCivita (I := I) g₀)
              (fun q : M => Xs q) (fun q : M => Ys q) (fun q : M => Zs q) p)
          x (Ds x) =
        (LeviCivita (I := I) gBase).toFun
            (fun p : M =>
              connectionRiemannCurvatureField (I := I) (LeviCivita (I := I) g₀)
                (fun q : M => Xs q) (fun q : M => Ys q) (fun q : M => Zs q) p)
            x (Ds x) +
          DeTurck.connectionDifference (I := I) g₀ gBase x
            (connectionRiemannCurvatureField (I := I) (LeviCivita (I := I) g₀)
              (fun q : M => Xs q) (fun q : M => Ys q) (fun q : M => Zs q) x)
            (Ds x) := by
    simpa [covB, cov₀, Rsec] using houter
  have hconn :
      curvCovDerivOpAt (I := I) cov₀ Ds Xs Ys Zs x -
          mixedCurvDeriv (I := I) gBase g₀ Ds Xs Ys Zs x =
        curvConnAt (I := I) gBase g₀ x D X Y Z := by
    let : NormedAddCommGroup
        (TangentSpace I x →L[ℝ] TangentSpace I x) :=
      ContinuousLinearMap.toNormedAddCommGroup
    let : NormedAddCommGroup
        (TangentSpace I x →L[ℝ]
          TangentSpace I x →L[ℝ] TangentSpace I x) :=
      ContinuousLinearMap.toNormedAddCommGroup
    have hDX₀ : ContMDiff I (I.prod 𝓘(ℝ, E)) (∞ : WithTop ℕ∞)
        (T% (covApply cov₀ (fun p => Ds p) (fun p => Xs p))) :=
      covApply_contMDiff (cov := cov₀) Ds.contMDiff Xs.contMDiff
    have hDY₀ : ContMDiff I (I.prod 𝓘(ℝ, E)) (∞ : WithTop ℕ∞)
        (T% (covApply cov₀ (fun p => Ds p) (fun p => Ys p))) :=
      covApply_contMDiff (cov := cov₀) Ds.contMDiff Ys.contMDiff
    have hDZ₀ : ContMDiff I (I.prod 𝓘(ℝ, E)) (∞ : WithTop ℕ∞)
        (T% (covApply cov₀ (fun p => Ds p) (fun p => Zs p))) :=
      covApply_contMDiff (cov := cov₀) Ds.contMDiff Zs.contMDiff
    have hDXB : ContMDiff I (I.prod 𝓘(ℝ, E)) (∞ : WithTop ℕ∞)
        (T% (covApply covB (fun p => Ds p) (fun p => Xs p))) :=
      covApply_contMDiff (cov := covB) Ds.contMDiff Xs.contMDiff
    have hDYB : ContMDiff I (I.prod 𝓘(ℝ, E)) (∞ : WithTop ℕ∞)
        (T% (covApply covB (fun p => Ds p) (fun p => Ys p))) :=
      covApply_contMDiff (cov := covB) Ds.contMDiff Ys.contMDiff
    have hDZB : ContMDiff I (I.prod 𝓘(ℝ, E)) (∞ : WithTop ℕ∞)
        (T% (covApply covB (fun p => Ds p) (fun p => Zs p))) :=
      covApply_contMDiff (cov := covB) Ds.contMDiff Zs.contMDiff
    have hRop_of
        (A B C : (p : M) → TangentSpace I p)
        (hA : ContMDiff I (I.prod 𝓘(ℝ, E)) (∞ : WithTop ℕ∞) (T% A))
        (hB : ContMDiff I (I.prod 𝓘(ℝ, E)) (∞ : WithTop ℕ∞) (T% B))
        (hC : ContMDiff I (I.prod 𝓘(ℝ, E)) (∞ : WithTop ℕ∞) (T% C)) :
        connectionRiemannCurvatureField (I := I) cov₀ A B C x =
          riemannOp (cov := cov₀) x (A x) (B x) (C x) := by
      change riemannSec cov₀ A B C x =
        riemannOp (cov := cov₀) x (A x) (B x) (C x)
      exact (riemannOp_apply_smooth (cov := cov₀) hA hB hC).symm
    have hRXYZ := hRop_of (fun p => Xs p) (fun p => Ys p) (fun p => Zs p)
      Xs.contMDiff Ys.contMDiff Zs.contMDiff
    have hRDX₀ := hRop_of
      (fun p => cov₀.toFun (fun q => Xs q) p (Ds p))
      (fun p => Ys p) (fun p => Zs p)
      (by simpa only [covApply] using hDX₀) Ys.contMDiff Zs.contMDiff
    have hRDXB := hRop_of
      (fun p => covB.toFun (fun q => Xs q) p (Ds p))
      (fun p => Ys p) (fun p => Zs p)
      (by simpa only [covApply] using hDXB) Ys.contMDiff Zs.contMDiff
    have hRDY₀ := hRop_of
      (fun p => Xs p) (fun p => cov₀.toFun (fun q => Ys q) p (Ds p))
      (fun p => Zs p) Xs.contMDiff
      (by simpa only [covApply] using hDY₀) Zs.contMDiff
    have hRDYB := hRop_of
      (fun p => Xs p) (fun p => covB.toFun (fun q => Ys q) p (Ds p))
      (fun p => Zs p) Xs.contMDiff
      (by simpa only [covApply] using hDYB) Zs.contMDiff
    have hRDZ₀ := hRop_of
      (fun p => Xs p) (fun p => Ys p)
      (fun p => cov₀.toFun (fun q => Zs q) p (Ds p))
      Xs.contMDiff Ys.contMDiff (by simpa only [covApply] using hDZ₀)
    have hRDZB := hRop_of
      (fun p => Xs p) (fun p => Ys p)
      (fun p => covB.toFun (fun q => Zs q) p (Ds p))
      Xs.contMDiff Ys.contMDiff (by simpa only [covApply] using hDZB)
    have hXRaw :
        cov₀.toFun (fun p => Xs p) x (Ds x) =
          covB.toFun (fun p => Xs p) x (Ds x) +
            DeTurck.connectionDifference (I := I) g₀ gBase x (Xs x) (Ds x) := by
      simpa only [covApply] using hX
    have hYRaw :
        cov₀.toFun (fun p => Ys p) x (Ds x) =
          covB.toFun (fun p => Ys p) x (Ds x) +
            DeTurck.connectionDifference (I := I) g₀ gBase x (Ys x) (Ds x) := by
      simpa only [covApply] using hY
    have hZRaw :
        cov₀.toFun (fun p => Zs p) x (Ds x) =
          covB.toFun (fun p => Zs p) x (Ds x) +
            DeTurck.connectionDifference (I := I) g₀ gBase x (Zs x) (Ds x) := by
      simpa only [covApply] using hZ
    unfold curvCovDerivOpAt mixedCurvDeriv curvConnAt
    simp only [cov₀]
    rw [houterRaw, hRXYZ, hRDX₀, hRDXB, hRDY₀, hRDYB, hRDZ₀, hRDZB]
    rw [hXRaw, hYRaw, hZRaw]
    simp only [map_add, add_apply]
    simp only [Ds, Xs, Ys, Zs, cov₀, extSec1_apply]
    abel
  have hpal := mixed_sub_eq_pal (I := I) gBase g₀ Ds Xs Ys Zs x
  have h₀ := nablaRiemannOp_eq (I := I) g₀ Ds Xs Ys Zs x
  have hB := nablaRiemannOp_eq (I := I) gBase Ds Xs Ys Zs x
  have hB' :
      curvCovDerivOpAt (I := I) covB Ds Xs Ys Zs x =
        nablaRiemannOp (I := I) gBase x (Ds x) (Xs x) (Ys x) (Zs x) := by
    dsimp only [covB]
    rw [LeviCivita_eq_leviCivitaConnectionOfMetric]
    exact hB.symm
  simpa [Ds, Xs, Ys, Zs, covB, cov₀] using
    calc
      nablaRiemannOp (I := I) g₀ x (Ds x) (Xs x) (Ys x) (Zs x) =
          curvCovDerivOpAt (I := I) cov₀ Ds Xs Ys Zs x := by
            dsimp only [cov₀]
            rw [LeviCivita_eq_leviCivitaConnectionOfMetric]
            exact h₀
      _ = (curvCovDerivOpAt (I := I) cov₀ Ds Xs Ys Zs x -
            mixedCurvDeriv (I := I) gBase g₀ Ds Xs Ys Zs x) +
          (mixedCurvDeriv (I := I) gBase g₀ Ds Xs Ys Zs x -
            curvCovDerivOpAt (I := I) covB Ds Xs Ys Zs x) +
          curvCovDerivOpAt (I := I) covB Ds Xs Ys Zs x := by abel
      _ = curvConnAt (I := I) gBase g₀ x D X Y Z +
          covDerivPalatini (I := I) gBase g₀ Ds Xs Ys Zs x +
          nablaRiemannOp (I := I) gBase x (Ds x) (Xs x) (Ys x) (Zs x) := by
            rw [hconn, hpal, hB']

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem jet1_eval (g : SmoothRiemannianMetric I M) (x : M)
    (D X Y Z W : TangentSpace I x) :
    iterCov (I := I) g 4 (metricRm04 (I := I) (M := M) g) 1 x
        (vec5 (I := I) D X Y Z W) =
      g.inner x W (nablaRiemannOp (I := I) g x D X Y Z) :=
  nablaRm04_apply (I := I) (M := M) g x D X Y Z W

private theorem sqrt_cancel {q A : ℝ}
    (hq : 0 ≤ q) (hA : 0 ≤ A) (h : q ^ 2 ≤ A * q) :
    q ≤ A := by
  rcases hq.eq_or_lt with hq0 | hqpos
  · rw [← hq0]
    exact hA
  · exact le_of_mul_le_mul_right (by simpa [pow_two] using h) hqpos

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem base_le_scaled
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ)
    (hcomp : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ Λ * gBase.inner x v v)
    (x : M) (v : TangentSpace I x) :
    gBase.inner x v v ≤ Λ * g₀.inner x v v := by
  have hΛ0 : (0 : ℝ) < Λ := lt_of_lt_of_le one_pos hΛ
  have hz := mul_le_mul_of_nonneg_left (hcomp x v).1 hΛ0.le
  rwa [← mul_assoc, mul_inv_cancel₀ hΛ0.ne', one_mul] at hz

private theorem sqrt_scaled {a b Λ : ℝ}
    (hΛ : 0 ≤ Λ) (h : a ≤ Λ * b) :
    Real.sqrt a ≤ Real.sqrt Λ * Real.sqrt b := by
  calc
    Real.sqrt a ≤ Real.sqrt (Λ * b) := Real.sqrt_le_sqrt h
    _ = Real.sqrt Λ * Real.sqrt b := Real.sqrt_mul hΛ b

private theorem sqrt_sq_mul3 {F a b c : ℝ}
    (hF : 0 ≤ F) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (F ^ 2 * a * b * c) =
      F * Real.sqrt a * Real.sqrt b * Real.sqrt c := by
  rw [show F ^ 2 * a * b * c = F ^ 2 * (a * (b * c)) by ring,
    Real.sqrt_mul (sq_nonneg F), Real.sqrt_sq hF,
    Real.sqrt_mul ha, Real.sqrt_mul hb]
  ring

noncomputable def curvConnC (Λ Kb : ℝ) : ℝ :=
  4 * (Real.sqrt Λ) ^ 3 * (3 / 2 * Λ ^ 3 * Λ) *
    (Λ ^ 2 * (riemannDiffC Λ Λ Λ + Real.sqrt Kb))

noncomputable def rmOneOpC (Λ Kb₀ Kb₁ : ℝ) : ℝ :=
  curvConnC Λ Kb₀ + (Real.sqrt Λ) ^ 5 * palatiniOneC Λ +
    (Real.sqrt Λ) ^ 5 * Kb₁

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma curv_aux_outer
    (S C₀ F a b c d e f g h i : ℝ)
    (hS : 0 ≤ S) (hC : 0 ≤ C₀)
    (hd : 0 ≤ d) (he : 0 ≤ e) (hf : 0 ≤ f)
    (h1 : a ≤ S * b) (h2 : b ≤ C₀ * c * d)
    (h3 : c ≤ S * e) (h4 : d ≤ S * f)
    (h5 : e ≤ F * g * h * i) :
    a ≤ S ^ 3 * C₀ * F * f * g * h * i := by
  calc
    a ≤ S * b := h1
    _ ≤ S * (C₀ * c * d) := by gcongr
    _ ≤ S * (C₀ * (S * e) * (S * f)) := by gcongr
    _ ≤ S * (C₀ * (S * (F * g * h * i)) * (S * f)) := by gcongr
    _ = S ^ 3 * C₀ * F * f * g * h * i := by ring

private lemma curv_aux_x
    (S C₀ F a b c d e f g h i : ℝ)
    (hS : 0 ≤ S) (hC : 0 ≤ C₀) (hF : 0 ≤ F)
    (hd : 0 ≤ d) (hg : 0 ≤ g) (hh : 0 ≤ h) (hi : 0 ≤ i)
    (h1 : a ≤ F * e * h * i)
    (h2 : e ≤ S * b)
    (h3 : b ≤ C₀ * c * d)
    (h4 : c ≤ S * g)
    (h5 : d ≤ S * f) :
    a ≤ S ^ 3 * C₀ * F * f * g * h * i := by
  calc
    a ≤ F * e * h * i := h1
    _ ≤ F * (S * b) * h * i := by gcongr
    _ ≤ F * (S * (C₀ * c * d)) * h * i := by gcongr
    _ ≤ F * (S * (C₀ * (S * g) * (S * f))) * h * i := by gcongr
    _ = S ^ 3 * C₀ * F * f * g * h * i := by ring

private lemma curv_aux_y
    (S C₀ F a b c d e f g h i : ℝ)
    (hS : 0 ≤ S) (hC : 0 ≤ C₀) (hF : 0 ≤ F)
    (hd : 0 ≤ d) (hg : 0 ≤ g) (hh : 0 ≤ h) (hi : 0 ≤ i)
    (h1 : a ≤ F * g * e * i)
    (h2 : e ≤ S * b)
    (h3 : b ≤ C₀ * c * d)
    (h4 : c ≤ S * h)
    (h5 : d ≤ S * f) :
    a ≤ S ^ 3 * C₀ * F * f * g * h * i := by
  calc
    a ≤ F * g * e * i := h1
    _ ≤ F * g * (S * b) * i := by gcongr
    _ ≤ F * g * (S * (C₀ * c * d)) * i := by gcongr
    _ ≤ F * g * (S * (C₀ * (S * h) * (S * f))) * i := by gcongr
    _ = S ^ 3 * C₀ * F * f * g * h * i := by ring

private lemma curv_aux_z
    (S C₀ F a b c d e f g h i : ℝ)
    (hS : 0 ≤ S) (hC : 0 ≤ C₀) (hF : 0 ≤ F)
    (hd : 0 ≤ d) (hg : 0 ≤ g) (hh : 0 ≤ h) (hi : 0 ≤ i)
    (h1 : a ≤ F * g * h * e)
    (h2 : e ≤ S * b)
    (h3 : b ≤ C₀ * c * d)
    (h4 : c ≤ S * i)
    (h5 : d ≤ S * f) :
    a ≤ S ^ 3 * C₀ * F * f * g * h * i := by
  calc
    a ≤ F * g * h * e := h1
    _ ≤ F * g * h * (S * b) := by gcongr
    _ ≤ F * g * h * (S * (C₀ * c * d)) := by gcongr
    _ ≤ F * g * h * (S * (C₀ * (S * i) * (S * f))) := by gcongr
    _ = S ^ 3 * C₀ * F * f * g * h * i := by ring

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma sqrt_sub_le
    (g₀ : SmoothRiemannianMetric I M) {x : M} (u v : TangentSpace I x) :
    Real.sqrt (g₀.inner x (u - v) (u - v)) ≤
      Real.sqrt (g₀.inner x u u) + Real.sqrt (g₀.inner x v v) := by
  have hneg : Real.sqrt (g₀.inner x (-v) (-v)) = Real.sqrt (g₀.inner x v v) := by
    simpa only [neg_one_smul, abs_neg, abs_one, one_mul] using
      Geometry.Riemannian.sqrt_inner_smul (I := I) g₀ x (-1 : ℝ) v
  calc
    Real.sqrt (g₀.inner x (u - v) (u - v))
        = Real.sqrt (g₀.inner x (u + -v) (u + -v)) := by rw [sub_eq_add_neg]
    _ ≤ Real.sqrt (g₀.inner x u u) + Real.sqrt (g₀.inner x (-v) (-v)) :=
      Geometry.Riemannian.sqrt_inner_add_le (I := I) g₀ x u (-v)
    _ = Real.sqrt (g₀.inner x u u) + Real.sqrt (g₀.inner x v v) := by rw [hneg]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma curv_conn_tail
    (g₀ : SmoothRiemannianMetric I M) {x : M}
    (L₀ : TangentSpace I x → ℝ) (u v w z : TangentSpace I x) (B : ℝ)
    (hL₀ : ∀ a, L₀ a = Real.sqrt (g₀.inner x a a))
    (hu : L₀ u ≤ B) (hv : L₀ v ≤ B) (hw : L₀ w ≤ B) (hz : L₀ z ≤ B) :
    Real.sqrt (g₀.inner x (u - v - w - z) (u - v - w - z)) ≤ 4 * B := by
  have hsub : ∀ a b : TangentSpace I x, L₀ (a - b) ≤ L₀ a + L₀ b := by
    intro a b
    rw [hL₀ (a - b), hL₀ a, hL₀ b]
    exact sqrt_sub_le (I := I) (M := M) g₀ a b
  have hle : L₀ (u - v - w - z) ≤ 4 * B := by
    calc
      L₀ (u - v - w - z) ≤ L₀ (u - v - w) + L₀ z := hsub (u - v - w) z
      _ ≤ (L₀ (u - v) + L₀ w) + L₀ z := by
        nlinarith [hsub (u - v) w]
      _ ≤ ((L₀ u + L₀ v) + L₀ w) + L₀ z := by
        nlinarith [hsub u v]
      _ ≤ (B + B + B) + B := by
        gcongr
      _ = 4 * B := by ring
  rw [hL₀ (u - v - w - z)] at hle
  exact hle

theorem rmOneOpC_nonneg {Λ Kb₀ Kb₁ : ℝ}
    (hΛ : 0 ≤ Λ) (hKb₁ : 0 ≤ Kb₁) :
    0 ≤ rmOneOpC Λ Kb₀ Kb₁ := by
  unfold rmOneOpC curvConnC palatiniOneC riemannDiffC
  positivity

noncomputable def rmOneC (Λ Kb₀ Kb₁ : ℝ) : ℝ :=
  Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 5) * rmOneOpC Λ Kb₀ Kb₁

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] in
private theorem curvConn_le_of
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ}
    (hΛ : 1 ≤ Λ)
    {Kb : ℝ} (hKb0 : 0 ≤ Kb)
    (hKb : ∀ (x : M) (v w u : TangentSpace I x),
      gBase.inner x (riemannOp (cov := LeviCivita (I := I) gBase) x v w u)
          (riemannOp (cov := LeviCivita (I := I) gBase) x v w u) ≤
        Kb * gBase.inner x v v * gBase.inner x w w * gBase.inner x u u)
    (hcomp : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ Λ * gBase.inner x v v)
    (hjet1 : MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g₀ gBase Λ)
    (hjet2 : MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g₀ gBase Λ) :
    ∀ (x : M) (D X Y Z : TangentSpace I x),
      Real.sqrt (g₀.inner x
          (curvConnAt (I := I) gBase g₀ x D X Y Z)
          (curvConnAt (I := I) gBase g₀ x D X Y Z)) ≤
        curvConnC Λ Kb * Real.sqrt (g₀.inner x D D) *
          Real.sqrt (g₀.inner x X X) *
          Real.sqrt (g₀.inner x Y Y) *
          Real.sqrt (g₀.inner x Z Z) := by
  classical
  have hEq : MetricUniformEquivalentOn (I := I) Set.univ gBase g₀ Λ :=
    ⟨hΛ, fun x _ => hcomp x⟩
  let C₀ : ℝ := 3 / 2 * Λ ^ 3 * Λ
  have hC₀0 : 0 ≤ C₀ := by
    dsimp [C₀]
    positivity
  have hC₀ : ∀ (x : M) (v w : TangentSpace I x),
      Real.sqrt (gBase.inner x
          (DifferentialGeometry.PDE.DeTurck.connectionDifference (I := I) g₀ gBase x v w)
          (DifferentialGeometry.PDE.DeTurck.connectionDifference (I := I) g₀ gBase x v w)) ≤
        C₀ * Real.sqrt (gBase.inner x v v) * Real.sqrt (gBase.inner x w w) := by
    intro x v w
    have h := connectionDifference_gJet_le (I := I) hEq hjet1 (Set.mem_univ x) w v
    simpa [C₀, DifferentialGeometry.PDE.DeTurck.connectionDifference,
      LeviCivita_eq_leviCivitaConnectionOfMetric,
      mul_assoc, mul_left_comm, mul_comm] using h
  let F : ℝ := Λ ^ 2 * (riemannDiffC Λ Λ Λ + Real.sqrt Kb)
  have hF0 : 0 ≤ F := by
    dsimp [F, riemannDiffC]
    positivity
  have hF := uniformCurvSup_of (I := I) (M := M) gBase g₀ hΛ
    hKb0 hKb hcomp hjet1 hjet2
  let S : ℝ := Real.sqrt Λ
  intro x D X Y Z
  let L₀ : TangentSpace I x → ℝ := fun v => Real.sqrt (g₀.inner x v v)
  let LB : TangentSpace I x → ℝ := fun v => Real.sqrt (gBase.inner x v v)
  let A := DeTurck.connectionDifference (I := I) g₀ gBase x
  let R := riemannOp (cov := LeviCivita (I := I) g₀) x
  let B : ℝ := S ^ 3 * C₀ * F * L₀ D * L₀ X * L₀ Y * L₀ Z
  have hΛ0 : 0 ≤ Λ := le_trans zero_le_one hΛ
  have h0B : ∀ v : TangentSpace I x, L₀ v ≤ S * LB v := by
    intro v
    exact sqrt_scaled hΛ0 (hcomp x v).2
  have hB0 : ∀ v : TangentSpace I x, LB v ≤ S * L₀ v := by
    intro v
    exact sqrt_scaled hΛ0 (base_le_scaled (I := I) (M := M)
      gBase g₀ hΛ hcomp x v)
  have hA : ∀ v w : TangentSpace I x,
      LB (A v w) ≤ C₀ * LB v * LB w := by
    intro v w
    simpa [LB, A] using hC₀ x v w
  have hR : ∀ v w u : TangentSpace I x,
      L₀ (R v w u) ≤ F * L₀ v * L₀ w * L₀ u := by
    intro v w u
    have h := hF x v w u
    calc
      L₀ (R v w u) ≤
          Real.sqrt (F ^ 2 * g₀.inner x v v *
            g₀.inner x w w * g₀.inner x u u) := by
        dsimp [L₀, R]
        exact Real.sqrt_le_sqrt h
      _ = F * L₀ v * L₀ w * L₀ u := by
        simpa [L₀] using sqrt_sq_mul3 hF0
          (metric_inner_self_nonneg (I := I) (M := M) g₀ x v)
          (metric_inner_self_nonneg (I := I) (M := M) g₀ x w)
  have houter : L₀ (A (R X Y Z) D) ≤ B := by
    dsimp [B]
    exact curv_aux_outer S C₀ F (L₀ (A (R X Y Z) D))
      (LB (A (R X Y Z) D)) (LB (R X Y Z)) (LB D)
      (L₀ (R X Y Z)) (L₀ D) (L₀ X) (L₀ Y) (L₀ Z)
      (by positivity) hC₀0
      (by positivity) (by positivity) (by positivity)
      (h0B _) (hA _ _) (hB0 _) (hB0 _) (hR _ _ _)
  have hX : L₀ (R (A X D) Y Z) ≤ B := by
    dsimp [B]
    exact curv_aux_x S C₀ F (L₀ (R (A X D) Y Z))
      (LB (A X D)) (LB X) (LB D) (L₀ (A X D))
      (L₀ D) (L₀ X) (L₀ Y) (L₀ Z)
      (by positivity) hC₀0 hF0
      (by positivity) (by positivity) (by positivity) (by positivity)
      (hR _ _ _) (h0B _) (hA _ _) (hB0 _) (hB0 _)
  have hY : L₀ (R X (A Y D) Z) ≤ B := by
    dsimp [B]
    exact curv_aux_y S C₀ F (L₀ (R X (A Y D) Z))
      (LB (A Y D)) (LB Y) (LB D) (L₀ (A Y D))
      (L₀ D) (L₀ X) (L₀ Y) (L₀ Z)
      (by positivity) hC₀0 hF0
      (by positivity) (by positivity) (by positivity) (by positivity)
      (hR _ _ _) (h0B _) (hA _ _) (hB0 _) (hB0 _)
  have hZ : L₀ (R X Y (A Z D)) ≤ B := by
    dsimp [B]
    exact curv_aux_z S C₀ F (L₀ (R X Y (A Z D)))
      (LB (A Z D)) (LB Z) (LB D) (L₀ (A Z D))
      (L₀ D) (L₀ X) (L₀ Y) (L₀ Z)
      (by positivity) hC₀0 hF0
      (by positivity) (by positivity) (by positivity) (by positivity)
      (hR _ _ _) (h0B _) (hA _ _) (hB0 _) (hB0 _)
  have hsqrt :
      Real.sqrt (g₀.inner x
        (A (R X Y Z) D - R (A X D) Y Z -
          R X (A Y D) Z - R X Y (A Z D))
        (A (R X Y Z) D - R (A X D) Y Z -
          R X (A Y D) Z - R X Y (A Z D))) ≤ 4 * B :=
    curv_conn_tail g₀ L₀
      (A (R X Y Z) D) (R (A X D) Y Z) (R X (A Y D) Z) (R X Y (A Z D)) B
      (fun _ => rfl) houter hX hY hZ
  calc
    Real.sqrt (g₀.inner x
        (curvConnAt (I := I) gBase g₀ x D X Y Z)
        (curvConnAt (I := I) gBase g₀ x D X Y Z)) ≤ 4 * B := by
      simpa [curvConnAt, A, R, L₀] using hsqrt
    _ = (4 * S ^ 3 * C₀ * F) * Real.sqrt (g₀.inner x D D) *
        Real.sqrt (g₀.inner x X X) *
        Real.sqrt (g₀.inner x Y Y) *
        Real.sqrt (g₀.inner x Z Z) := by
      dsimp [B, L₀]
      ring
    _ = curvConnC Λ Kb * Real.sqrt (g₀.inner x D D) *
        Real.sqrt (g₀.inner x X X) *
        Real.sqrt (g₀.inner x Y Y) *
        Real.sqrt (g₀.inner x Z Z) := by
      dsimp [curvConnC, S, C₀, F]

private theorem curvConn_le
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ}
    (hΛ : 1 ≤ Λ)
    (hcomp : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ Λ * gBase.inner x v v)
    (hjet1 : MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g₀ gBase Λ)
    (hjet2 : MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g₀ gBase Λ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (x : M) (D X Y Z : TangentSpace I x),
        Real.sqrt (g₀.inner x
            (curvConnAt (I := I) gBase g₀ x D X Y Z)
            (curvConnAt (I := I) gBase g₀ x D X Y Z)) ≤
          C * Real.sqrt (g₀.inner x D D) *
            Real.sqrt (g₀.inner x X X) *
            Real.sqrt (g₀.inner x Y Y) *
            Real.sqrt (g₀.inner x Z Z) := by
  obtain ⟨Kb, hKb0, hKb⟩ :=
    exists_uniform_riemannOp_LeviCivita_gNorm_bound (I := I) (M := M) gBase
  refine ⟨curvConnC Λ Kb, ?_, ?_⟩
  · have hΛ0 : 0 ≤ Λ := le_trans zero_le_one hΛ
    dsimp [curvConnC, riemannDiffC]
    positivity
  · exact curvConn_le_of (I := I) (M := M) gBase g₀ hΛ
      hKb0 hKb hcomp hjet1 hjet2

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem fixedRmOpOne_of (g : SmoothRiemannianMetric I M)
    {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ x : M,
      Real.sqrt (normSq0S (I := I) g x 5
        (iterCov (I := I) g 4 (metricRm04 (I := I) (M := M) g) 1 x)) ≤ K) :
    ∀ (x : M) (D X Y Z : TangentSpace I x),
      Real.sqrt (g.inner x
          (nablaRiemannOp (I := I) g x D X Y Z)
          (nablaRiemannOp (I := I) g x D X Y Z)) ≤
        K * Real.sqrt (g.inner x D D) *
          Real.sqrt (g.inner x X X) *
          Real.sqrt (g.inner x Y Y) *
          Real.sqrt (g.inner x Z Z) := by
  classical
  intro x D X Y Z
  let R : TangentSpace I x := nablaRiemannOp (I := I) g x D X Y Z
  let q : ℝ := Real.sqrt (g.inner x R R)
  let A : ℝ :=
    K * Real.sqrt (g.inner x D D) *
      Real.sqrt (g.inner x X X) *
      Real.sqrt (g.inner x Y Y) *
      Real.sqrt (g.inner x Z Z)
  have hRR : 0 ≤ g.inner x R R :=
    metric_inner_self_nonneg (I := I) (M := M) g x R
  have hA0 : 0 ≤ A := by
    dsimp [A]
    positivity
  have hraw := Tensor0SBundle.abs_apply_le_norm0S (I := I) g x 5
    (iterCov (I := I) g 4 (metricRm04 (I := I) (M := M) g) 1 x)
    (vec5 (I := I) D X Y Z R)
  rw [jet1_eval] at hraw
  have hprod :
      (∏ a : Fin 5,
          Real.sqrt (g.inner x
            (vec5 (I := I) D X Y Z R a)
            (vec5 (I := I) D X Y Z R a))) =
        Real.sqrt (g.inner x D D) *
          Real.sqrt (g.inner x X X) *
          Real.sqrt (g.inner x Y Y) *
          Real.sqrt (g.inner x Z Z) * q := by
    simp [vec5, Fin.prod_univ_succ, q, mul_assoc]
  have hprod0 : 0 ≤
      (∏ a : Fin 5,
        Real.sqrt (g.inner x
          (vec5 (I := I) D X Y Z R a)
          (vec5 (I := I) D X Y Z R a))) :=
    Finset.prod_nonneg fun _ _ => Real.sqrt_nonneg _
  have hbound := hraw.trans (mul_le_mul_of_nonneg_right (hK x) hprod0)
  rw [hprod, abs_of_nonneg hRR] at hbound
  have hquad : q ^ 2 ≤ A * q := by
    rw [show q ^ 2 = g.inner x R R from Real.sq_sqrt hRR]
    simpa [A, mul_assoc] using hbound
  have hq := sqrt_cancel (Real.sqrt_nonneg _) hA0 hquad
  simpa [q, A, R] using hq

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem fixedRmOpOne (g : SmoothRiemannianMetric I M) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (x : M) (D X Y Z : TangentSpace I x),
        Real.sqrt (g.inner x
            (nablaRiemannOp (I := I) g x D X Y Z)
            (nablaRiemannOp (I := I) g x D X Y Z)) ≤
          K * Real.sqrt (g.inner x D D) *
            Real.sqrt (g.inner x X X) *
            Real.sqrt (g.inner x Y Y) *
            Real.sqrt (g.inner x Z Z) := by
  obtain ⟨K, hK0, hK⟩ := exists_curvJet_sup (I := I) (M := M) g 1
  exact ⟨K, hK0, fixedRmOpOne_of (I := I) (M := M) g hK0 hK⟩

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem jet1_norm_le
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
    intro i
    rw [hON i i]
    simp
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
      exact jet1_eval (I := I) (M := M) g x _ _ _ _ _
    rw [hval]
    set N : TangentSpace I x :=
      nablaRiemannOp (I := I) g x (basis (slots 0)) (basis (slots 1))
        (basis (slots 2)) (basis (slots 3)) with hN
    have hNN : Real.sqrt (g.inner x N N) ≤ K := by
      have h := hop x (basis (slots 0)) (basis (slots 1)) (basis (slots 2))
        (basis (slots 3))
      rw [hunit (slots 0), hunit (slots 1), hunit (slots 2), hunit (slots 3)] at h
      simpa [hN] using h
    calc
      |g.inner x (basis (slots 4)) N| ≤
          Real.sqrt (g.inner x (basis (slots 4)) (basis (slots 4))) *
            Real.sqrt (g.inner x N N) :=
        abs_metric_inner_le_sqrt_metric_quadratic (I := I) (M := M) g x _ _
      _ = Real.sqrt (g.inner x N N) := by
        rw [hunit (slots 4)]
        simp
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
  calc
    Real.sqrt (normSq0S (I := I) g x 5
        (iterCov (I := I) g 4 (metricRm04 (I := I) (M := M) g) 1 x)) ≤
      Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 5 * K ^ 2) :=
        Real.sqrt_le_sqrt hcard
    _ = Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 5) * K := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hK]


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M] in
theorem uniformRmOpOne_of
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ}
    (hΛ : 1 ≤ Λ)
    {Kb₀ Kb₁ : ℝ} (hKb₀0 : 0 ≤ Kb₀)
    (hKb₀ : ∀ (x : M) (v w u : TangentSpace I x),
      gBase.inner x (riemannOp (cov := LeviCivita (I := I) gBase) x v w u)
          (riemannOp (cov := LeviCivita (I := I) gBase) x v w u) ≤
        Kb₀ * gBase.inner x v v * gBase.inner x w w * gBase.inner x u u)
    (hKb₁0 : 0 ≤ Kb₁)
    (hKb₁ : ∀ x : M,
      Real.sqrt (normSq0S (I := I) gBase x 5
        (iterCov (I := I) gBase 4
          (metricRm04 (I := I) (M := M) gBase) 1 x)) ≤ Kb₁)
    (hcomp : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ Λ * gBase.inner x v v)
    (hjet1 : MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g₀ gBase Λ)
    (hjet2 : MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g₀ gBase Λ)
    (hjet3 : MetricCovDerivOrderBoundOn (I := I) Set.univ 3 g₀ gBase Λ) :
    ∀ (x : M) (D X Y Z : TangentSpace I x),
      Real.sqrt (g₀.inner x
          (nablaRiemannOp (I := I) g₀ x D X Y Z)
          (nablaRiemannOp (I := I) g₀ x D X Y Z)) ≤
        rmOneOpC Λ Kb₀ Kb₁ * Real.sqrt (g₀.inner x D D) *
          Real.sqrt (g₀.inner x X X) *
          Real.sqrt (g₀.inner x Y Y) *
          Real.sqrt (g₀.inner x Z Z) := by
  classical
  let Cc : ℝ := curvConnC Λ Kb₀
  let Cp : ℝ := palatiniOneC Λ
  let Cb : ℝ := Kb₁
  have hCc0 : 0 ≤ Cc := by
    have hΛ0 : 0 ≤ Λ := le_trans zero_le_one hΛ
    dsimp [Cc, curvConnC, riemannDiffC]
    positivity
  have hCp0 : 0 ≤ Cp := by
    dsimp [Cp, palatiniOneC]
    positivity
  have hCb0 : 0 ≤ Cb := by simpa [Cb] using hKb₁0
  have hCc := curvConn_le_of (I := I) (M := M) gBase g₀ hΛ
    hKb₀0 hKb₀ hcomp hjet1 hjet2
  have hCp := uniformPalatini1_le (I := I) (M := M) gBase g₀
    hΛ hcomp hjet1 hjet2 hjet3
  have hCb := fixedRmOpOne_of (I := I) (M := M) gBase hKb₁0 hKb₁
  let S : ℝ := Real.sqrt Λ
  intro x D X Y Z
  let L₀ : TangentSpace I x → ℝ := fun v => Real.sqrt (g₀.inner x v v)
  let LB : TangentSpace I x → ℝ := fun v => Real.sqrt (gBase.inner x v v)
  let Vc : TangentSpace I x := curvConnAt (I := I) gBase g₀ x D X Y Z
  let Vp : TangentSpace I x :=
    covDerivPalatini (I := I) gBase g₀
      (extSec1 (I := I) x D) (extSec1 (I := I) x X)
      (extSec1 (I := I) x Y) (extSec1 (I := I) x Z) x
  let Vb : TangentSpace I x := nablaRiemannOp (I := I) gBase x D X Y Z
  have hΛ0 : 0 ≤ Λ := le_trans zero_le_one hΛ
  have h0B : ∀ v : TangentSpace I x, L₀ v ≤ S * LB v := by
    intro v
    exact sqrt_scaled hΛ0 (hcomp x v).2
  have hB0 : ∀ v : TangentSpace I x, LB v ≤ S * L₀ v := by
    intro v
    exact sqrt_scaled hΛ0 (base_le_scaled (I := I) (M := M)
      gBase g₀ hΛ hcomp x v)
  have hc : L₀ Vc ≤ Cc * L₀ D * L₀ X * L₀ Y * L₀ Z := by
    simpa [L₀, Vc] using hCc x D X Y Z
  have hpB : LB Vp ≤ Cp * LB D * LB X * LB Y * LB Z := by
    with_unfolding_all
      exact hCp x D X Y Z
  have hbB : LB Vb ≤ Cb * LB D * LB X * LB Y * LB Z := by
    simpa [LB, Vb] using hCb x D X Y Z
  have hp : L₀ Vp ≤ S ^ 5 * Cp * L₀ D * L₀ X * L₀ Y * L₀ Z := by
    calc
      L₀ Vp ≤ S * LB Vp := h0B _
      _ ≤ S * (Cp * LB D * LB X * LB Y * LB Z) := by
        gcongr
      _ ≤ S * (Cp * (S * L₀ D) * (S * L₀ X) *
          (S * L₀ Y) * (S * L₀ Z)) := by
        gcongr
        · exact hB0 _
        · exact hB0 _
        · exact hB0 _
        · exact hB0 _
      _ = S ^ 5 * Cp * L₀ D * L₀ X * L₀ Y * L₀ Z := by ring
  have hb : L₀ Vb ≤ S ^ 5 * Cb * L₀ D * L₀ X * L₀ Y * L₀ Z := by
    calc
      L₀ Vb ≤ S * LB Vb := h0B _
      _ ≤ S * (Cb * LB D * LB X * LB Y * LB Z) := by
        gcongr
      _ ≤ S * (Cb * (S * L₀ D) * (S * L₀ X) *
          (S * L₀ Y) * (S * L₀ Z)) := by
        gcongr
        · exact hB0 _
        · exact hB0 _
        · exact hB0 _
        · exact hB0 _
      _ = S ^ 5 * Cb * L₀ D * L₀ X * L₀ Y * L₀ Z := by ring
  have hsplit :
      nablaRiemannOp (I := I) g₀ x D X Y Z = Vc + Vp + Vb := by
    simpa [Vc, Vp, Vb] using
      nablaRm_split (I := I) (M := M) gBase g₀ x D X Y Z
  have hadd :
      L₀ (Vc + Vp + Vb) ≤ (L₀ Vc + L₀ Vp) + L₀ Vb := by
    calc
      L₀ (Vc + Vp + Vb) ≤ L₀ (Vc + Vp) + L₀ Vb := by
        simpa [L₀] using
          Geometry.Riemannian.sqrt_inner_add_le (I := I) g₀ x (Vc + Vp) Vb
      _ ≤ (L₀ Vc + L₀ Vp) + L₀ Vb := by
        gcongr
        simpa [L₀] using
          Geometry.Riemannian.sqrt_inner_add_le (I := I) g₀ x Vc Vp
  calc
    Real.sqrt (g₀.inner x
        (nablaRiemannOp (I := I) g₀ x D X Y Z)
        (nablaRiemannOp (I := I) g₀ x D X Y Z)) =
        L₀ (Vc + Vp + Vb) := by rw [hsplit]
    _ ≤ (L₀ Vc + L₀ Vp) + L₀ Vb := hadd
    _ ≤ (Cc * L₀ D * L₀ X * L₀ Y * L₀ Z +
          S ^ 5 * Cp * L₀ D * L₀ X * L₀ Y * L₀ Z) +
        S ^ 5 * Cb * L₀ D * L₀ X * L₀ Y * L₀ Z := by
      gcongr
    _ = (Cc + S ^ 5 * Cp + S ^ 5 * Cb) *
          Real.sqrt (g₀.inner x D D) *
          Real.sqrt (g₀.inner x X X) *
          Real.sqrt (g₀.inner x Y Y) *
          Real.sqrt (g₀.inner x Z Z) := by
      dsimp [L₀]
      ring
    _ = rmOneOpC Λ Kb₀ Kb₁ * Real.sqrt (g₀.inner x D D) *
          Real.sqrt (g₀.inner x X X) *
          Real.sqrt (g₀.inner x Y Y) *
          Real.sqrt (g₀.inner x Z Z) := by
      dsimp [rmOneOpC, Cc, Cp, Cb, S]

private theorem uniformRmOpOne
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ}
    (hΛ : 1 ≤ Λ)
    (hcomp : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ Λ * gBase.inner x v v)
    (hjet1 : MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g₀ gBase Λ)
    (hjet2 : MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g₀ gBase Λ)
    (hjet3 : MetricCovDerivOrderBoundOn (I := I) Set.univ 3 g₀ gBase Λ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (x : M) (D X Y Z : TangentSpace I x),
        Real.sqrt (g₀.inner x
            (nablaRiemannOp (I := I) g₀ x D X Y Z)
            (nablaRiemannOp (I := I) g₀ x D X Y Z)) ≤
          C * Real.sqrt (g₀.inner x D D) *
            Real.sqrt (g₀.inner x X X) *
            Real.sqrt (g₀.inner x Y Y) *
            Real.sqrt (g₀.inner x Z Z) := by
  obtain ⟨Kb₀, hKb₀0, hKb₀⟩ :=
    exists_uniform_riemannOp_LeviCivita_gNorm_bound (I := I) (M := M) gBase
  obtain ⟨Kb₁, hKb₁0, hKb₁⟩ :=
    exists_curvJet_sup (I := I) (M := M) gBase 1
  refine ⟨rmOneOpC Λ Kb₀ Kb₁, ?_, ?_⟩
  · have hΛ0 : 0 ≤ Λ := le_trans zero_le_one hΛ
    dsimp [rmOneOpC, curvConnC, palatiniOneC, riemannDiffC]
    positivity
  · exact uniformRmOpOne_of (I := I) (M := M) gBase g₀ hΛ
      hKb₀0 hKb₀ hKb₁0 hKb₁ hcomp hjet1 hjet2 hjet3


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M] in
theorem uniformRmJetOne_of
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ Kb₀ Kb₁ : ℝ}
    (hΛ : 1 ≤ Λ)
    (hKb₀0 : 0 ≤ Kb₀)
    (hKb₀ : ∀ (x : M) (v w u : TangentSpace I x),
      gBase.inner x (riemannOp (cov := LeviCivita (I := I) gBase) x v w u)
          (riemannOp (cov := LeviCivita (I := I) gBase) x v w u) ≤
        Kb₀ * gBase.inner x v v * gBase.inner x w w * gBase.inner x u u)
    (hKb₁0 : 0 ≤ Kb₁)
    (hKb₁ : ∀ x : M,
      Real.sqrt (normSq0S (I := I) gBase x 5
        (iterCov (I := I) gBase 4
          (metricRm04 (I := I) (M := M) gBase) 1 x)) ≤ Kb₁)
    (hcomp : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ Λ * gBase.inner x v v)
    (hjet1 : MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g₀ gBase Λ)
    (hjet2 : MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g₀ gBase Λ)
    (hjet3 : MetricCovDerivOrderBoundOn (I := I) Set.univ 3 g₀ gBase Λ) :
    ∀ x : M,
      Real.sqrt (normSq0S (I := I) g₀ x 5
        (iterCov (I := I) g₀ 4
          (metricRm04 (I := I) (M := M) g₀) 1 x)) ≤
        rmOneC (E := E) Λ Kb₀ Kb₁ := by
  have hOp0 : 0 ≤ rmOneOpC Λ Kb₀ Kb₁ := by
    have hΛ0 : 0 ≤ Λ := le_trans zero_le_one hΛ
    dsimp [rmOneOpC, curvConnC, palatiniOneC, riemannDiffC]
    positivity
  have hOp := uniformRmOpOne_of (I := I) (M := M) gBase g₀ hΛ
    hKb₀0 hKb₀ hKb₁0 hKb₁ hcomp hjet1 hjet2 hjet3
  intro x
  simpa [rmOneC] using
    jet1_norm_le (I := I) (M := M) g₀ hOp0 hOp x


theorem uniformRmJetOne
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ}
    (hΛ : 1 ≤ Λ)
    (hcomp : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ Λ * gBase.inner x v v)
    (hjet1 : MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g₀ gBase Λ)
    (hjet2 : MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g₀ gBase Λ)
    (hjet3 : MetricCovDerivOrderBoundOn (I := I) Set.univ 3 g₀ gBase Λ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ x : M,
        Real.sqrt (normSq0S (I := I) g₀ x 5
          (iterCov (I := I) g₀ 4
            (metricRm04 (I := I) (M := M) g₀) 1 x)) ≤ K := by
  obtain ⟨C, hC0, hC⟩ :=
    uniformRmOpOne (I := I) (M := M) gBase g₀
      hΛ hcomp hjet1 hjet2 hjet3
  refine ⟨Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 5) * C, by positivity, ?_⟩
  intro x
  exact jet1_norm_le (I := I) (M := M) g₀ hC0 hC x

private theorem sq_le_of_sqrt_le {a K : ℝ}
    (ha : 0 ≤ a) (h : Real.sqrt a ≤ K) :
    a ≤ K ^ 2 := by
  nlinarith [Real.sq_sqrt ha, Real.sqrt_nonneg a]


omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem uniformRmSecOne_of
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ Kb₀ Kb₁ : ℝ}
    (hΛ : 1 ≤ Λ)
    (hKb₀0 : 0 ≤ Kb₀)
    (hKb₀ : ∀ (x : M) (v w u : TangentSpace I x),
      gBase.inner x (riemannOp (cov := LeviCivita (I := I) gBase) x v w u)
          (riemannOp (cov := LeviCivita (I := I) gBase) x v w u) ≤
        Kb₀ * gBase.inner x v v * gBase.inner x w w * gBase.inner x u u)
    (hKb₁0 : 0 ≤ Kb₁)
    (hKb₁ : ∀ x : M,
      Real.sqrt (normSq0S (I := I) gBase x 5
        (iterCov (I := I) gBase 4
          (metricRm04 (I := I) (M := M) gBase) 1 x)) ≤ Kb₁)
    (hcomp : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ Λ * gBase.inner x v v)
    (hjet1 : MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g₀ gBase Λ)
    (hjet2 : MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g₀ gBase Λ)
    (hjet3 : MetricCovDerivOrderBoundOn (I := I) Set.univ 3 g₀ gBase Λ) :
    ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + 1) x
          ((iteratedCovGrad (I := I) g₀ 0 4 1
            (rmSection (I := I) (M := M) g₀)).toSection x) ≤
        rmOneC (E := E) Λ Kb₀ Kb₁ ^ 2 := by
  intro x
  apply sq_le_of_sqrt_le
    (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (4 + 1) x _)
  rw [riemannianFiberNormSq_rmSection_eq (I := I) g₀ 1 x]
  exact uniformRmJetOne_of (I := I) (M := M) gBase g₀ hΛ
    hKb₀0 hKb₀ hKb₁0 hKb₁ hcomp hjet1 hjet2 hjet3 x


theorem uniformRmSecOne
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ}
    (hΛ : 1 ≤ Λ)
    (hcomp : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ Λ * gBase.inner x v v)
    (hjet1 : MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g₀ gBase Λ)
    (hjet2 : MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g₀ gBase Λ)
    (hjet3 : MetricCovDerivOrderBoundOn (I := I) Set.univ 3 g₀ gBase Λ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + 1) x
          ((iteratedCovGrad (I := I) g₀ 0 4 1
            (rmSection (I := I) (M := M) g₀)).toSection x) ≤ K ^ 2 := by
  obtain ⟨K, hK0, hK⟩ :=
    uniformRmJetOne (I := I) (M := M) gBase g₀
      hΛ hcomp hjet1 hjet2 hjet3
  refine ⟨K, hK0, fun x => ?_⟩
  apply sq_le_of_sqrt_le
    (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (4 + 1) x _)
  rw [riemannianFiberNormSq_rmSection_eq (I := I) g₀ 1 x]
  exact hK x

end RicciFlow
end PDE
end DifferentialGeometry
