import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.DifferentiatedPalatini

import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Uniform.CurvatureJetDifference
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.ConnectionSecondDerivative

set_option autoImplicit false

noncomputable section


open Bundle Manifold Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.HCGCompactness

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

private noncomputable def extSec (x : M) (v : TangentSpace I x) :
    ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
  ContMDiffSection.mk (smoothExtensionTangent (I := I) x v)
    (smoothExtensionTangent_contMDiff (I := I) x v)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
@[simp] private theorem extSec_apply (x : M) (v : TangentSpace I x) :
    extSec (I := I) x v x = v :=
  smoothExtensionTangent_eq (I := I) x v

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] in
private theorem covD_congr
    (g₂ g₁ : SmoothRiemannianMetric I M)
    (W X Y W' X' Y' : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    {x : M} (hW : W x = W' x) (hX : X x = X' x) (hY : Y x = Y' x) :
    covDerivConnectionDifference (I := I) g₂ g₁ W X Y x =
      covDerivConnectionDifference (I := I) g₂ g₁ W' X' Y' x := by
  classical
  have : IsManifold I 2 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  have : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
    change IsManifold I ∞ M
    infer_instance
  have : IsManifold I (1 + 1) M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by decide : ((1 : WithTop ℕ∞) + 1) ≤ ∞)
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
  have hZ := hpair (extSec (I := I) x (a - b))
  rw [extSec_apply] at hZ
  have hsym1 : g₁.inner x a (a - b) = g₁.inner x (a - b) a :=
    g₁.symm x a (a - b)
  have hsym2 : g₁.inner x b (a - b) = g₁.inner x (a - b) b :=
    g₁.symm x b (a - b)
  have hzero : g₁.inner x (a - b) (a - b) = 0 := by
    rw [map_sub, ← hsym1, ← hsym2, hZ, sub_self]
  have hsub : a - b = 0 := by
    by_contra hne
    exact (ne_of_gt (g₁.pos x (a - b) hne)) hzero
  exact sub_eq_zero.mp hsub

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] in
private theorem covD_eq_ext
    (g₂ g₁ : SmoothRiemannianMetric I M)
    (W X Y : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _)) (x : M) :
    covDerivConnectionDifference (I := I) g₂ g₁ W X Y x =
      covDerivConnectionDifference (I := I) g₂ g₁
        (extSec (I := I) x (W x))
        (extSec (I := I) x (X x))
        (extSec (I := I) x (Y x)) x := by
  apply covD_congr (I := I) g₂ g₁ W X Y
    (extSec (I := I) x (W x))
    (extSec (I := I) x (X x))
    (extSec (I := I) x (Y x))
  all_goals simp

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem covD2_eq_hcg
    (gB g₀ : SmoothRiemannianMetric I M)
    (D X Y Z : Π b : M, TangentSpace I b) (x : M) :
    Integral.Connection.covDerivConnectionDifference2 (I := I) gB g₀ D X Y Z x =
      HCGCompactness.covDerivConnectionDifference2 (I := I) gB g₀ D X Y Z x :=
  rfl

noncomputable def palatiniJet1At
    (gBase g₀ : SmoothRiemannianMetric I M) (x : M)
    (D X Y Z : TangentSpace I x) : TangentSpace I x :=
  covDerivPalatini (I := I) gBase g₀
    (extSec (I := I) x D) (extSec (I := I) x X)
    (extSec (I := I) x Y) (extSec (I := I) x Z) x

def palatiniOneC (Λ : ℝ) : ℝ :=
  2 * (3 / 2 * Λ ^ 5 * Λ + 9 / 2 * Λ ^ 6 * Λ * Λ + 3 * Λ ^ 7 * Λ ^ 3) +
    4 * (3 / 2 * Λ ^ 3 * Λ) * (3 / 2 * Λ ^ 4 * (Λ + Λ * Λ ^ 2))


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma palatini_aux_p
    (C₀ C₁ a b d x y z : ℝ)
    (hC₁0 : 0 ≤ C₁)
    (hd : 0 ≤ d) (hx : 0 ≤ x)
    (h1 : a ≤ C₁ * d * x * b)
    (h2 : b ≤ C₀ * y * z) :
    a ≤ C₀ * C₁ * (d * x * y * z) := by
  have hmul := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ C₁ * d * x)
  calc
    a ≤ C₁ * d * x * b := h1
    _ ≤ C₁ * d * x * (C₀ * y * z) := hmul
    _ = C₀ * C₁ * (d * x * y * z) := by ring

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma palatini_aux_r
    (C₀ C₁ a b d x y z : ℝ)
    (hC₁0 : 0 ≤ C₁)
    (hd : 0 ≤ d) (hx : 0 ≤ x)
    (h1 : a ≤ C₁ * d * x * b)
    (h2 : b ≤ C₀ * y * z) :
    a ≤ C₀ * C₁ * (d * y * x * z) := by
  have hmul := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ C₁ * d * x)
  calc
    a ≤ C₁ * d * x * b := h1
    _ ≤ C₁ * d * x * (C₀ * y * z) := hmul
    _ = C₀ * C₁ * (d * y * x * z) := by ring

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma palatini_aux_q
    (C₀ C₁ a b d x y z : ℝ)
    (hC₀0 : 0 ≤ C₀) (hx : 0 ≤ x)
    (h1 : a ≤ C₀ * b * x)
    (h2 : b ≤ C₁ * d * y * z) :
    a ≤ C₀ * C₁ * (d * x * y * z) := by
  have hmul := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ C₀ * x)
  calc
    a ≤ C₀ * b * x := h1
    _ ≤ C₀ * x * (C₁ * d * y * z) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
    _ = C₀ * C₁ * (d * x * y * z) := by ring

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma palatini_aux_s
    (C₀ C₁ a b d x y z : ℝ)
    (hC₀0 : 0 ≤ C₀) (hy : 0 ≤ y)
    (h1 : a ≤ C₀ * b * y)
    (h2 : b ≤ C₁ * d * x * z) :
    a ≤ C₀ * C₁ * (d * x * y * z) := by
  have hmul := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ C₀ * y)
  calc
    a ≤ C₀ * b * y := h1
    _ ≤ C₀ * y * (C₁ * d * x * z) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
    _ = C₀ * C₁ * (d * x * y * z) := by ring

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma palatini_P1
    (gBase g₀ : SmoothRiemannianMetric I M) {x : M}
    (L : TangentSpace I x → ℝ) (D X : TangentSpace I x)
    (Ds Xs AYZs : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (P : TangentSpace I x) (C₁ : ℝ)
    (hL : ∀ v, L v = Real.sqrt (gBase.inner x v v))
    (hP : P = covDerivConnectionDifference (I := I) gBase g₀ Ds Xs AYZs x)
    (hD : Ds x = D) (hX : Xs x = X)
    (h : Real.sqrt (gBase.inner x (covDerivConnectionDifference (I := I) gBase g₀ Ds Xs AYZs x)
          (covDerivConnectionDifference (I := I) gBase g₀ Ds Xs AYZs x)) ≤
        C₁ * Real.sqrt (gBase.inner x (Ds x) (Ds x)) *
          Real.sqrt (gBase.inner x (Xs x) (Xs x)) *
          Real.sqrt (gBase.inner x (AYZs x) (AYZs x))) :
    L P ≤ C₁ * L D * L X * L (AYZs x) := by
  rw [hL P, hL D, hL X, hL (AYZs x)]
  simpa [hP, hD, hX] using h

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma palatini_R1
    (gBase g₀ : SmoothRiemannianMetric I M) {x : M}
    (L : TangentSpace I x → ℝ) (D Y : TangentSpace I x)
    (Ds Ys AXZs : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (R : TangentSpace I x) (C₁ : ℝ)
    (hL : ∀ v, L v = Real.sqrt (gBase.inner x v v))
    (hR : R = covDerivConnectionDifference (I := I) gBase g₀ Ds Ys AXZs x)
    (hD : Ds x = D) (hY : Ys x = Y)
    (h : Real.sqrt (gBase.inner x (covDerivConnectionDifference (I := I) gBase g₀ Ds Ys AXZs x)
          (covDerivConnectionDifference (I := I) gBase g₀ Ds Ys AXZs x)) ≤
        C₁ * Real.sqrt (gBase.inner x (Ds x) (Ds x)) *
          Real.sqrt (gBase.inner x (Ys x) (Ys x)) *
          Real.sqrt (gBase.inner x (AXZs x) (AXZs x))) :
    L R ≤ C₁ * L D * L Y * L (AXZs x) := by
  rw [hL R, hL D, hL Y, hL (AXZs x)]
  simpa [hR, hD, hY] using h

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma palatini_conn_tail
    (gBase : SmoothRiemannianMetric I M) {x : M}
    (L : TangentSpace I x → ℝ)
    (A B P Q R S : TangentSpace I x)
    (C₂ C₀ C₁ prod : ℝ)
    (hL : ∀ v, L v = Real.sqrt (gBase.inner x v v))
    (hA : L A ≤ C₂ * prod) (hB : L B ≤ C₂ * prod)
    (hP : L P ≤ C₀ * C₁ * prod) (hQ : L Q ≤ C₀ * C₁ * prod)
    (hR : L R ≤ C₀ * C₁ * prod) (hS : L S ≤ C₀ * C₁ * prod) :
    Real.sqrt (gBase.inner x ((A - B) + ((P + Q) - (R + S)))
      ((A - B) + ((P + Q) - (R + S)))) ≤
      (2 * C₂ + 4 * C₀ * C₁) * prod := by
  have hsub : ∀ u v : TangentSpace I x, L (u - v) ≤ L u + L v := by
    intro u v
    rw [hL (u - v), hL u, hL v]
    have hneg : Real.sqrt (gBase.inner x (-v) (-v)) = Real.sqrt (gBase.inner x v v) := by
      simpa only [neg_one_smul, abs_neg, abs_one, one_mul] using
        Geometry.Riemannian.sqrt_inner_smul (I := I) gBase x (-1 : ℝ) v
    calc
      Real.sqrt (gBase.inner x (u - v) (u - v))
          = Real.sqrt (gBase.inner x (u + -v) (u + -v)) := by rw [sub_eq_add_neg]
      _ ≤ Real.sqrt (gBase.inner x u u) + Real.sqrt (gBase.inner x (-v) (-v)) :=
        Geometry.Riemannian.sqrt_inner_add_le (I := I) gBase x u (-v)
      _ = Real.sqrt (gBase.inner x u u) + Real.sqrt (gBase.inner x v v) := by rw [hneg]
  have hleft : L (A - B) ≤ L A + L B := hsub A B
  have hpq : L (P + Q) ≤ L P + L Q := by
    rw [hL (P + Q), hL P, hL Q]
    exact Geometry.Riemannian.sqrt_inner_add_le (I := I) gBase x P Q
  have hrs : L (R + S) ≤ L R + L S := by
    rw [hL (R + S), hL R, hL S]
    exact Geometry.Riemannian.sqrt_inner_add_le (I := I) gBase x R S
  have hright : L ((P + Q) - (R + S)) ≤ (L P + L Q) + (L R + L S) :=
    le_trans (hsub (P + Q) (R + S)) (add_le_add hpq hrs)
  calc
    Real.sqrt (gBase.inner x ((A - B) + ((P + Q) - (R + S)))
        ((A - B) + ((P + Q) - (R + S)))) = L ((A - B) + ((P + Q) - (R + S))) := by
      rw [hL ((A - B) + ((P + Q) - (R + S)))]
    _ ≤ L (A - B) + L ((P + Q) - (R + S)) := by
      rw [hL ((A - B) + ((P + Q) - (R + S))), hL (A - B), hL ((P + Q) - (R + S))]
      exact Geometry.Riemannian.sqrt_inner_add_le (I := I) gBase x (A - B) ((P + Q) - (R + S))
    _ ≤ (L A + L B) + ((L P + L Q) + (L R + L S)) := by
      exact add_le_add hleft hright
    _ ≤ (C₂ * prod + C₂ * prod) +
        ((C₀ * C₁ * prod + C₀ * C₁ * prod) +
          (C₀ * C₁ * prod + C₀ * C₁ * prod)) := by
      gcongr
    _ = (2 * C₂ + 4 * C₀ * C₁) * prod := by ring

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M] in
theorem uniformPalatini1_le
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ}
    (hΛ : 1 ≤ Λ)
    (hcomp : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ Λ * gBase.inner x v v)
    (hjet1 : MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g₀ gBase Λ)
    (hjet2 : MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g₀ gBase Λ)
    (hjet3 : MetricCovDerivOrderBoundOn (I := I) Set.univ 3 g₀ gBase Λ) :
    ∀ (x : M) (D X Y Z : TangentSpace I x),
      Real.sqrt (gBase.inner x
          (palatiniJet1At (I := I) gBase g₀ x D X Y Z)
          (palatiniJet1At (I := I) gBase g₀ x D X Y Z)) ≤
        palatiniOneC Λ * Real.sqrt (gBase.inner x D D) *
          Real.sqrt (gBase.inner x X X) *
          Real.sqrt (gBase.inner x Y Y) *
          Real.sqrt (gBase.inner x Z Z) := by
  classical
  have hEq : MetricUniformEquivalentOn (I := I) Set.univ gBase g₀ Λ :=
    ⟨hΛ, fun x _hx v => hcomp x v⟩
  let C₀ : ℝ := 3 / 2 * Λ ^ 3 * Λ
  have hC₀0 : 0 ≤ C₀ := by
    dsimp [C₀]
    positivity
  have hC₀ : ∀ (x : M) (v w : TangentSpace I x),
      Real.sqrt (gBase.inner x
          (DifferentialGeometry.PDE.DeTurck.connectionDifference (I := I) g₀ gBase x v w)
          (DifferentialGeometry.PDE.DeTurck.connectionDifference (I := I) g₀ gBase x v w)) ≤
        C₀ * Real.sqrt (gBase.inner x v v) *
          Real.sqrt (gBase.inner x w w) := by
    intro x v w
    have h := connectionDifference_gJet_le (I := I) hEq hjet1 (Set.mem_univ x) w v
    unfold DifferentialGeometry.PDE.DeTurck.connectionDifference
      DifferentialGeometry.Geometry.Connection.LeviCivita
    simpa [C₀, mul_assoc, mul_left_comm, mul_comm] using h
  let C₁ : ℝ := 3 / 2 * Λ ^ 4 * (Λ + Λ * Λ ^ 2)
  have hC₁0 : 0 ≤ C₁ := by
    dsimp [C₁]
    positivity
  have hC₁ : ∀ (x : M) (v w u : TangentSpace I x),
      Real.sqrt (gBase.inner x
          (covDerivConnectionDifference (I := I) gBase g₀
            (smoothExtensionTangent (I := I) x v)
            (smoothExtensionTangent (I := I) x w)
            (smoothExtensionTangent (I := I) x u) x)
          (covDerivConnectionDifference (I := I) gBase g₀
            (smoothExtensionTangent (I := I) x v)
            (smoothExtensionTangent (I := I) x w)
            (smoothExtensionTangent (I := I) x u) x)) ≤
        C₁ * Real.sqrt (gBase.inner x v v) *
          Real.sqrt (gBase.inner x w w) *
          Real.sqrt (gBase.inner x u u) := by
    intro x v w u
    simpa [C₁] using
      covDerivConnectionDifference_gJet_le (I := I) hEq hjet1 hjet2
        (Set.mem_univ x) v w u
  let C₂ : ℝ :=
    3 / 2 * Λ ^ 5 * Λ + 9 / 2 * Λ ^ 6 * Λ * Λ + 3 * Λ ^ 7 * Λ ^ 3
  have hC₂0 : 0 ≤ C₂ := by
    dsimp [C₂]
    positivity
  intro x D X Y Z
  let Ds := extSec (I := I) x D
  let Xs := extSec (I := I) x X
  let Ys := extSec (I := I) x Y
  let Zs := extSec (I := I) x Z
  let A₂xy : TangentSpace I x :=
    Integral.Connection.covDerivConnectionDifference2 (I := I) gBase g₀ Ds Xs Ys Zs x
  let A₂yx : TangentSpace I x :=
    Integral.Connection.covDerivConnectionDifference2 (I := I) gBase g₀ Ds Ys Xs Zs x
  let AYZs : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _) :=
    ContMDiffSection.mk
      (diffSec (LeviCivita (I := I) gBase) (LeviCivita (I := I) g₀) Ys Zs)
      (by
        apply diffSec_contMDiff
        · exact Ys.contMDiff
        · simpa using Zs.contMDiff)
  let AXZs : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _) :=
    ContMDiffSection.mk
      (diffSec (LeviCivita (I := I) gBase) (LeviCivita (I := I) g₀) Xs Zs)
      (by
        apply diffSec_contMDiff
        · exact Xs.contMDiff
        · simpa using Zs.contMDiff)
  let Cdyzs : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _) :=
    ContMDiffSection.mk
      (fun p => covDerivConnectionDifference (I := I) gBase g₀ Ds Ys Zs p)
      (by
        simpa [Ds, Ys, Zs] using
          covDerivConnectionDifference_contMDiff (I := I) gBase g₀ Ds Ys Zs)
  let Cdxzs : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _) :=
    ContMDiffSection.mk
      (fun p => covDerivConnectionDifference (I := I) gBase g₀ Ds Xs Zs p)
      (by
        simpa [Ds, Xs, Zs] using
          covDerivConnectionDifference_contMDiff (I := I) gBase g₀ Ds Xs Zs)
  let P : TangentSpace I x :=
    covDerivConnectionDifference (I := I) gBase g₀ Ds Xs AYZs x
  let Q : TangentSpace I x :=
    diffSec (LeviCivita (I := I) gBase) (LeviCivita (I := I) g₀) Xs Cdyzs x
  let R : TangentSpace I x :=
    covDerivConnectionDifference (I := I) gBase g₀ Ds Ys AXZs x
  let S : TangentSpace I x :=
    diffSec (LeviCivita (I := I) gBase) (LeviCivita (I := I) g₀) Ys Cdxzs x
  let L : TangentSpace I x → ℝ := fun v => Real.sqrt (gBase.inner x v v)
  let prod4 : ℝ := L D * L X * L Y * L Z
  have hsplit :
      palatiniJet1At (I := I) gBase g₀ x D X Y Z =
        A₂xy - A₂yx + (P + Q) - (R + S) := by
    simpa [palatiniJet1At, Ds, Xs, Ys, Zs, A₂xy, A₂yx,
      AYZs, AXZs, Cdyzs, Cdxzs, P, Q, R, S] using
      covDerivPal_eq (I := I) gBase g₀ Ds Xs Ys Zs x
  have hprod40 : 0 ≤ prod4 := by
    dsimp [prod4, L]
    positivity
  have hA₂xy : L A₂xy ≤ C₂ * prod4 := by
    simpa [A₂xy, Ds, Xs, Ys, Zs, extSec, L, prod4, C₂, covD2_eq_hcg,
      mul_assoc] using
      HCGCompactness.covDConnectionDifference2_gJet_le (I := I) hEq hjet1 hjet2 hjet3
        (Set.mem_univ x) D X Y Z
  have hA₂yx : L A₂yx ≤ C₂ * prod4 := by
    have h := HCGCompactness.covDConnectionDifference2_gJet_le (I := I)
      hEq hjet1 hjet2 hjet3 (Set.mem_univ x) D Y X Z
    simpa [A₂yx, Ds, Xs, Ys, Zs, extSec, L, prod4, C₂, covD2_eq_hcg, mul_assoc,
      mul_left_comm, mul_comm] using h
  have hAYZ : L (AYZs x) ≤ C₀ * L Y * L Z := by
    have h := hC₀ x Z Y
    simpa [AYZs, Ys, Zs, L, DifferentialGeometry.PDE.DeTurck.connectionDifference,
      diffSec, mul_assoc, mul_left_comm, mul_comm] using h
  have hAXZ : L (AXZs x) ≤ C₀ * L X * L Z := by
    have h := hC₀ x Z X
    simpa [AXZs, Xs, Zs, L, DifferentialGeometry.PDE.DeTurck.connectionDifference,
      diffSec, mul_assoc, mul_left_comm, mul_comm] using h
  have hCdyz : L (Cdyzs x) ≤ C₁ * L D * L Y * L Z := by
    have h := hC₁ x D Y Z
    change Real.sqrt (gBase.inner x
        (covDerivConnectionDifference (I := I) gBase g₀
          (extSec (I := I) x D) (extSec (I := I) x Y) (extSec (I := I) x Z) x)
        (covDerivConnectionDifference (I := I) gBase g₀
          (extSec (I := I) x D) (extSec (I := I) x Y) (extSec (I := I) x Z) x)) ≤
      C₁ * Real.sqrt (gBase.inner x D D) * Real.sqrt (gBase.inner x Y Y) *
        Real.sqrt (gBase.inner x Z Z)
    have hD :
        (extSec (I := I) x D : (p : M) → TangentSpace I p) =
          smoothExtensionTangent (I := I) x D := rfl
    have hY :
        (extSec (I := I) x Y : (p : M) → TangentSpace I p) =
          smoothExtensionTangent (I := I) x Y := rfl
    have hZ :
        (extSec (I := I) x Z : (p : M) → TangentSpace I p) =
          smoothExtensionTangent (I := I) x Z := rfl
    rw [hD, hY, hZ]
    exact h
  have hCdxz : L (Cdxzs x) ≤ C₁ * L D * L X * L Z := by
    have h := hC₁ x D X Z
    change Real.sqrt (gBase.inner x
        (covDerivConnectionDifference (I := I) gBase g₀
          (extSec (I := I) x D) (extSec (I := I) x X) (extSec (I := I) x Z) x)
        (covDerivConnectionDifference (I := I) gBase g₀
          (extSec (I := I) x D) (extSec (I := I) x X) (extSec (I := I) x Z) x)) ≤
      C₁ * Real.sqrt (gBase.inner x D D) * Real.sqrt (gBase.inner x X X) *
        Real.sqrt (gBase.inner x Z Z)
    have hD :
        (extSec (I := I) x D : (p : M) → TangentSpace I p) =
          smoothExtensionTangent (I := I) x D := rfl
    have hX :
        (extSec (I := I) x X : (p : M) → TangentSpace I p) =
          smoothExtensionTangent (I := I) x X := rfl
    have hZ :
        (extSec (I := I) x Z : (p : M) → TangentSpace I p) =
          smoothExtensionTangent (I := I) x Z := rfl
    rw [hD, hX, hZ]
    exact h
  have hR : L R ≤ C₀ * C₁ * prod4 := by
    have heq :
        covDerivConnectionDifference (I := I) gBase g₀ Ds Ys AXZs x =
          covDerivConnectionDifference (I := I) gBase g₀
            (smoothExtensionTangent (I := I) x (Ds x))
            (smoothExtensionTangent (I := I) x (Ys x))
            (smoothExtensionTangent (I := I) x (AXZs x)) x := by
      simpa [extSec] using covD_eq_ext (I := I) gBase g₀ Ds Ys AXZs x
    have h := hC₁ x (Ds x) (Ys x) (AXZs x)
    rw [← heq] at h
    have hR1 : L R ≤ C₁ * L D * L Y * L (AXZs x) :=
      palatini_R1 gBase g₀ L D Y Ds Ys AXZs R C₁
        (fun _ => rfl) rfl (by simp [Ds]) (by simp [Ys]) h
    exact palatini_aux_r C₀ C₁ (L R) (L (AXZs x)) (L D) (L Y) (L X) (L Z)
      hC₁0 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hR1 hAXZ
  have hP : L P ≤ C₀ * C₁ * prod4 := by
    have heq :
        covDerivConnectionDifference (I := I) gBase g₀ Ds Xs AYZs x =
          covDerivConnectionDifference (I := I) gBase g₀
            (smoothExtensionTangent (I := I) x (Ds x))
            (smoothExtensionTangent (I := I) x (Xs x))
            (smoothExtensionTangent (I := I) x (AYZs x)) x := by
      simpa [extSec] using covD_eq_ext (I := I) gBase g₀ Ds Xs AYZs x
    have h := hC₁ x (Ds x) (Xs x) (AYZs x)
    rw [← heq] at h
    have hP1 : L P ≤ C₁ * L D * L X * L (AYZs x) :=
      palatini_P1 gBase g₀ L D X Ds Xs AYZs P C₁
        (fun _ => rfl) rfl (by simp [Ds]) (by simp [Xs]) h
    exact palatini_aux_p C₀ C₁ (L P) (L (AYZs x)) (L D) (L X) (L Y) (L Z)
      hC₁0 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hP1 hAYZ
  have hQ : L Q ≤ C₀ * C₁ * prod4 := by
    have h := hC₀ x (Cdyzs x) (Xs x)
    exact palatini_aux_q C₀ C₁ (L Q) (L (Cdyzs x)) (L D) (L X) (L Y) (L Z)
      hC₀0 (Real.sqrt_nonneg _)
      (by simpa [Q, Cdyzs, Xs, L, DifferentialGeometry.PDE.DeTurck.connectionDifference,
        diffSec] using h)
      hCdyz
  have hS : L S ≤ C₀ * C₁ * prod4 := by
    have h := hC₀ x (Cdxzs x) (Ys x)
    exact palatini_aux_s C₀ C₁ (L S) (L (Cdxzs x)) (L D) (L X) (L Y) (L Z)
      hC₀0 (Real.sqrt_nonneg _)
      (by simpa [S, Cdxzs, Ys, L, DifferentialGeometry.PDE.DeTurck.connectionDifference,
        diffSec] using h)
      hCdxz
  have hcore :
      Real.sqrt (gBase.inner x
        ((A₂xy - A₂yx) + ((P + Q) - (R + S)))
        ((A₂xy - A₂yx) + ((P + Q) - (R + S)))) ≤
        (2 * C₂ + 4 * C₀ * C₁) * prod4 :=
    palatini_conn_tail gBase L A₂xy A₂yx P Q R S C₂ C₀ C₁ prod4
      (fun _ => rfl) hA₂xy hA₂yx hP hQ hR hS
  calc
    Real.sqrt (gBase.inner x
        (palatiniJet1At (I := I) gBase g₀ x D X Y Z)
        (palatiniJet1At (I := I) gBase g₀ x D X Y Z)) =
        Real.sqrt (gBase.inner x
          ((A₂xy - A₂yx) + ((P + Q) - (R + S)))
          ((A₂xy - A₂yx) + ((P + Q) - (R + S)))) := by
          rw [hsplit]
          congr 1
          abel_nf
    _ ≤ (2 * C₂ + 4 * C₀ * C₁) * prod4 := hcore
    _ = (2 * C₂ + 4 * C₀ * C₁) *
        Real.sqrt (gBase.inner x D D) *
        Real.sqrt (gBase.inner x X X) *
        Real.sqrt (gBase.inner x Y Y) *
        Real.sqrt (gBase.inner x Z Z) := by
      dsimp [prod4, L]
      ring
    _ = palatiniOneC Λ * Real.sqrt (gBase.inner x D D) *
        Real.sqrt (gBase.inner x X X) *
        Real.sqrt (gBase.inner x Y Y) *
        Real.sqrt (gBase.inner x Z Z) := by
      dsimp [palatiniOneC, C₀, C₁, C₂]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M] in
theorem uniformPalatini1
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
        Real.sqrt (gBase.inner x
            (palatiniJet1At (I := I) gBase g₀ x D X Y Z)
            (palatiniJet1At (I := I) gBase g₀ x D X Y Z)) ≤
          C * Real.sqrt (gBase.inner x D D) *
            Real.sqrt (gBase.inner x X X) *
            Real.sqrt (gBase.inner x Y Y) *
            Real.sqrt (gBase.inner x Z Z) := by
  refine ⟨palatiniOneC Λ, ?_, ?_⟩
  · unfold palatiniOneC
    positivity
  · exact uniformPalatini1_le (I := I) (M := M) gBase g₀
      hΛ hcomp hjet1 hjet2 hjet3

end RicciFlow
end PDE
end DifferentialGeometry
