import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.KoszulDifference
import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.HigherOrder
import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.Regularity.Tensor0S
import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.Regularity.TotalNabla0S
import DifferentialGeometry.Geometry.Connection.LeviCivita.Smooth.Connection
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciConnDiffPalatini

/-!
# Toward the differentiated Christoffel-difference Koszul identity (B2 P2.a)

This leaf builds the covariant derivative of the Christoffel-difference Koszul identity, the crux of the
UNGATED order-1 connection-difference-derivative norm bound (mission B2; see
`HCGCompactness/UNIF_ITEM6_RECON.md` §4b for the full route).

The target identity (differentiating `connDiff_koszul` covariantly along `W` under `∇₂ = LeviCivita g₂`):
```
2·g₁(covDerivConnDiff g₂ g₁ W X Y x, Z) = [∇₂²g₁ combo] − 2·(∇₂_W g₁)(A(X,Y), Z),
```
with `A = connDiff g₁ g₂ = difference (LC g₁) (LC g₂)`.  The differentiation base is the Tensor-layer
`koszul_difference` (`Tensor/RSTensor/NablaOnTensors/KoszulDifference.lean`) in the
`nabla0SFun (metricTensorField g₁)` currency, whose derivative is differentiable via
`nabla0SFun_eval_smooth_slots`.

**Landed so far:** the a=0 differentiation base `connDiff_koszul_nabla` — `koszul_difference` specialised
to the Levi-Civita pair `(LC g₁, LC g₂)`, in the `nabla0SFun` currency that the covariant differentiation
consumes.  The full differentiated identity is the multi-brick continuation (recon §4b, 6-step plan).
-/

noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
/-- **The Christoffel-difference Koszul identity in `nabla0SFun` currency** (the a=0 differentiation
base).  Specialisation of the Tensor-layer `koszul_difference` to the Levi-Civita pair `(LC g₁, LC g₂)`:
pairing the connection difference `A = difference (LC g₁) (LC g₂)` against `g₁` equals the symmetric
Koszul combination of the `∇₂`-covariant derivative of `g₁`, expressed as
`nabla0SFun 2 (LC g₂) · (metricTensorField g₁)` (= `∇₂g₁`).

This is `connDiff_koszul` in the currency whose covariant derivative is Tensor-layer differentiable
(`nabla0SFun_eval_smooth_slots`); the differentiated identity (B2 P2.a) is obtained by applying that
engine to the right-hand side and metric-compatibility to the left. -/
theorem connDiff_koszul_nabla
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
    (g₁ g₂ : SmoothRiemannianMetric I M)
    (X Y Z : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    {x : M} :
    g₁.inner x
        ((CovariantDerivative.difference (LeviCivita (I := I) g₁) (LeviCivita (I := I) g₂) x)
          (Y x) (X x)) (Z x) =
      (1 / 2) * Tensor0SBundle.nabla0SFun (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
          (LeviCivita (I := I) g₂) X (Tensor0SBundle.metricTensorField (I := I) g₁) x
          (fun q : Fin 2 => if q = 0 then Y x else Z x) +
        (1 / 2) * Tensor0SBundle.nabla0SFun (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
          (LeviCivita (I := I) g₂) Y (Tensor0SBundle.metricTensorField (I := I) g₁) x
          (fun q : Fin 2 => if q = 0 then X x else Z x) -
        (1 / 2) * Tensor0SBundle.nabla0SFun (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
          (LeviCivita (I := I) g₂) Z (Tensor0SBundle.metricTensorField (I := I) g₁) x
          (fun q : Fin 2 => if q = 0 then X x else Y x) := by
  haveI : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by change IsManifold I ∞ M; infer_instance
  have hmc : IsMetricCompatible_gen (I := I) (LeviCivita (I := I) g₁) g₁ := by
    simpa [LeviCivita] using
      leviCivitaConnectionOfMetric_isMetricCompatible (I := I) g₁
  have htf : IsTorsionFreeAt (I := I) (LeviCivita (I := I) g₁) x :=
    (leviCivitaConnectionOfMetric_isTorsionFree (I := I) g₁) x
  have htf' : IsTorsionFreeAt (I := I) (LeviCivita (I := I) g₂) x :=
    (leviCivitaConnectionOfMetric_isTorsionFree (I := I) g₂) x
  exact Tensor0SBundle.koszul_difference (I := I)
    (LeviCivita (I := I) g₁) (LeviCivita (I := I) g₂) g₁ hmc htf htf' X Y Z

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
/-- Smoothness of `∇₂g₁ = totalNabla0SFun 2 (LC g₂) (metricTensorField g₁)` as a `(0,3)`-field, so it
can be bundled via `totalNabla0S` and differentiated a second time.  From `totalNabla0S_reg` and the
local smoothness of the `g₂`-Levi-Civita connection. -/
theorem metricField_totalReg
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
    (g₁ g₂ : SmoothRiemannianMetric I M) :
    Tensor0SBundle.TotalNabla0SRegular (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
      (LeviCivita (I := I) g₂) (Tensor0SBundle.metricTensorField (I := I) g₁) :=
  Tensor0SBundle.totalNabla0S_reg (I := I) 2 (LeviCivita (I := I) g₂)
    (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally (I := I) g₂)
    (Tensor0SBundle.metricTensorField (I := I) g₁)

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
/-- **One combo term of the differentiated Koszul RHS.**  The directional derivative along `W` of a
`∇₂g₁` combo term (direction `V 0`, slots `V 1, V 2`) equals the second covariant derivative `∇₂²g₁`
(`nabla0SFun 3 (LC g₂) W (∇₂g₁-field)`) plus the Leibniz slot corrections, by
`nabla0SFun_eval_smooth_slots` on the bundled `∇₂g₁` field, bridged to the first-order combo term via
`totalNabla0SFun_apply_section`.  This is the RHS engine step of the B2 P2.a differentiated identity; the
three combo terms of `connDiff_koszul_nabla` are its instances at `V = ![X,Y,Z]`, `![Y,X,Z]`, `![Z,X,Y]`. -/
theorem nablaMetric_combo_extDeriv
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
    (g₁ g₂ : SmoothRiemannianMetric I M)
    (V : Fin 3 → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (W : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (x : M) :
    extDerivFun (I := I)
        (fun p : M => Tensor0SBundle.nabla0SFun (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
          (LeviCivita (I := I) g₂) (V 0) (Tensor0SBundle.metricTensorField (I := I) g₁) p
          (fun q : Fin 2 => V q.succ p)) x (W x) =
      Tensor0SBundle.nabla0SFun (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 3
          (LeviCivita (I := I) g₂) W
          (Tensor0SBundle.totalNabla0S (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
            (LeviCivita (I := I) g₂) (Tensor0SBundle.metricTensorField (I := I) g₁)
            (metricField_totalReg (I := I) g₁ g₂)) x
          (fun a : Fin 3 => V a x) +
        ∑ a : Fin 3,
          (Tensor0SBundle.totalNabla0S (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
            (LeviCivita (I := I) g₂) (Tensor0SBundle.metricTensorField (I := I) g₁)
            (metricField_totalReg (I := I) g₁ g₂)) x
            (Function.update (fun b : Fin 3 => V b x) a
              (((LeviCivita (I := I) g₂) (fun p : M => V a p) x) (W x))) := by
  classical
  set α := Tensor0SBundle.totalNabla0S (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
    (LeviCivita (I := I) g₂) (Tensor0SBundle.metricTensorField (I := I) g₁)
    (metricField_totalReg (I := I) g₁ g₂) with hαdef
  have hbridge : (fun p : M => α p (fun a : Fin 3 => V a p)) =
      (fun p : M => Tensor0SBundle.nabla0SFun (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
        (LeviCivita (I := I) g₂) (V 0) (Tensor0SBundle.metricTensorField (I := I) g₁) p
        (fun q : Fin 2 => V q.succ p)) := by
    funext p
    rw [hαdef, Tensor0SBundle.totalNabla0S_apply,
      show (fun a : Fin 3 => V a p) =
          Fin.cons ((V 0) p) (fun q : Fin 2 => (V q.succ) p) from
        (Fin.cons_self_tail (fun a : Fin 3 => V a p)).symm,
      Tensor0SBundle.totalNabla0SFun_apply_section]
  rw [Tensor0SBundle.nabla0SFun_eval_smooth_slots (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
    (LeviCivita (I := I) g₂) W V α x, hbridge]
  abel

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
/-- **The LHS metric-compatibility Leibniz** for the differentiated Koszul identity.  The directional
derivative along `W` of the `g₁`-contraction `p ↦ g₁(a p, b p)` (slots `a = V 0`, `b = V 1`) equals the
first covariant derivative `(∇₂g₁)(a,b)` (`nabla0SFun 2 (LC g₂) W (metricTensorField g₁)`) plus the two
`g₁(∇₂_W ·, ·)` Leibniz corrections.  Direct application of `nabla0SFun_eval_smooth_slots` to
`metricTensorField g₁`; this expands the LHS of `connDiff_koszul_nabla` under differentiation. -/
theorem metric_leibniz_extDeriv
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
    (g₁ g₂ : SmoothRiemannianMetric I M)
    (V : Fin 2 → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (W : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (x : M) :
    extDerivFun (I := I)
        (fun p : M => Tensor0SBundle.metricTensorField (I := I) g₁ p
          (fun c : Fin 2 => V c p)) x (W x) =
      Tensor0SBundle.nabla0SFun (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
          (LeviCivita (I := I) g₂) W (Tensor0SBundle.metricTensorField (I := I) g₁) x
          (fun c : Fin 2 => V c x) +
        ∑ c : Fin 2,
          Tensor0SBundle.metricTensorField (I := I) g₁ x
            (Function.update (fun d : Fin 2 => V d x) c
              (((LeviCivita (I := I) g₂) (fun p : M => V c p) x) (W x))) := by
  rw [Tensor0SBundle.nabla0SFun_eval_smooth_slots (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
    (LeviCivita (I := I) g₂) W V (Tensor0SBundle.metricTensorField (I := I) g₁) x]
  abel

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
/-- **Field-eval form of the a=0 Koszul identity.**  Pairing the connection difference
`A = difference (LC g₁) (LC g₂)` against `g₁` equals the symmetric Koszul combination of the bundled
`∇₂g₁` field `totalNabla0S 2 (LC g₂) (metricTensorField g₁)`, evaluated on the three cyclic slot
tuples.  This is `connDiff_koszul_nabla` bridged to the `(0,3)`-field currency (via
`totalNabla0SFun_apply_section`), the form in which the differentiated identity's slot corrections
cancel against the RHS second-derivative combos. -/
private theorem koszul_field
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
    (g₁ g₂ : SmoothRiemannianMetric I M)
    (P Q R : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (x : M) :
    g₁.inner x
        ((CovariantDerivative.difference (LeviCivita (I := I) g₁) (LeviCivita (I := I) g₂) x)
          (P x) (Q x)) (R x) =
      (1 / 2) * Tensor0SBundle.totalNabla0S (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
          (LeviCivita (I := I) g₂) (Tensor0SBundle.metricTensorField (I := I) g₁)
          (metricField_totalReg (I := I) g₁ g₂) x ![Q x, P x, R x] +
        (1 / 2) * Tensor0SBundle.totalNabla0S (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
          (LeviCivita (I := I) g₂) (Tensor0SBundle.metricTensorField (I := I) g₁)
          (metricField_totalReg (I := I) g₁ g₂) x ![P x, Q x, R x] -
        (1 / 2) * Tensor0SBundle.totalNabla0S (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
          (LeviCivita (I := I) g₂) (Tensor0SBundle.metricTensorField (I := I) g₁)
          (metricField_totalReg (I := I) g₁ g₂) x ![R x, Q x, P x] := by
  have hslot : ∀ a b : TangentSpace I x,
      (fun q : Fin 2 => if q = 0 then a else b) = ![a, b] := by
    intro a b; funext q; fin_cases q <;> simp
  have hbr : ∀ (S : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
      (a b : TangentSpace I x),
      Tensor0SBundle.nabla0SFun (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
          (LeviCivita (I := I) g₂) S (Tensor0SBundle.metricTensorField (I := I) g₁) x
          (fun q : Fin 2 => if q = 0 then a else b) =
        Tensor0SBundle.totalNabla0S (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
          (LeviCivita (I := I) g₂) (Tensor0SBundle.metricTensorField (I := I) g₁)
          (metricField_totalReg (I := I) g₁ g₂) x ![S x, a, b] := by
    intro S a b
    rw [hslot a b, Tensor0SBundle.totalNabla0S_apply]
    exact (Tensor0SBundle.totalNabla0SFun_apply_section (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      2 (LeviCivita (I := I) g₂) S (Tensor0SBundle.metricTensorField (I := I) g₁) x ![a, b]).symm
  rw [connDiff_koszul_nabla (I := I) g₁ g₂ Q P R,
    hbr Q (P x) (R x), hbr P (Q x) (R x), hbr R (Q x) (P x)]

/-- **The differentiated Christoffel-difference Koszul identity (B2 P2.a).**  Differentiating the a=0
Koszul identity `2 g₁(A(X,Y), Z) = ∇₂g₁ combo` covariantly along `W` under `∇₂ = LeviCivita g₂`:
`2 g₁(covDerivConnDiff g₂ g₁ W X Y x, Z) = [∇₂²g₁ combo] − 2 (∇₂_W g₁)(A(X,Y), Z)`, with
`A(X,Y) = difference (LC g₁)(LC g₂) x (Y x)(X x)`.  The second-derivative combo is the `nabla0SFun 3`
directional derivative (along `W`) of the bundled `∇₂g₁` field `totalNabla0S 2 (LC g₂)(mtf g₁)`, and the
quadratic term is the first covariant derivative of `g₁` paired against the connection difference. -/
theorem connDiff_koszul_deriv
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
    (g₁ g₂ : SmoothRiemannianMetric I M)
    (W X Y Z : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (x : M) :
    2 * g₁.inner x (covDerivConnDiff (I := I) g₂ g₁ W X Y x) (Z x) =
      Tensor0SBundle.nabla0SFun (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 3
          (LeviCivita (I := I) g₂) W
          (Tensor0SBundle.totalNabla0S (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
            (LeviCivita (I := I) g₂) (Tensor0SBundle.metricTensorField (I := I) g₁)
            (metricField_totalReg (I := I) g₁ g₂)) x ![X x, Y x, Z x] +
        Tensor0SBundle.nabla0SFun (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 3
          (LeviCivita (I := I) g₂) W
          (Tensor0SBundle.totalNabla0S (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
            (LeviCivita (I := I) g₂) (Tensor0SBundle.metricTensorField (I := I) g₁)
            (metricField_totalReg (I := I) g₁ g₂)) x ![Y x, X x, Z x] -
        Tensor0SBundle.nabla0SFun (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 3
          (LeviCivita (I := I) g₂) W
          (Tensor0SBundle.totalNabla0S (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
            (LeviCivita (I := I) g₂) (Tensor0SBundle.metricTensorField (I := I) g₁)
            (metricField_totalReg (I := I) g₁ g₂)) x ![Z x, X x, Y x] -
        2 * Tensor0SBundle.nabla0SFun (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
          (LeviCivita (I := I) g₂) W (Tensor0SBundle.metricTensorField (I := I) g₁) x
          ![(CovariantDerivative.difference (LeviCivita (I := I) g₁) (LeviCivita (I := I) g₂) x)
              (Y x) (X x), Z x] := by
  classical
  haveI : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by change IsManifold I ∞ M; infer_instance
  set field := Tensor0SBundle.totalNabla0S (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
    (LeviCivita (I := I) g₂) (Tensor0SBundle.metricTensorField (I := I) g₁)
    (metricField_totalReg (I := I) g₁ g₂) with hfield
  -- The connection-difference section `A(X,Y) = ∇₂-difference of X against Y`.
  have hAsm : ContMDiff I (I.prod 𝓘(ℝ, E)) (∞ : WithTop ℕ∞)
      (T% (diffSec (LeviCivita (I := I) g₂) (LeviCivita (I := I) g₁)
        (fun b => X b) (fun b => Y b))) :=
    diffSec_contMDiff (LeviCivita (I := I) g₂) (LeviCivita (I := I) g₁) X.contMDiff
      (by rw [show ((∞ : WithTop ℕ∞) + 1) = (∞ : WithTop ℕ∞) from by rw [ENat.coe_top_add_one]]
          exact Y.contMDiff)
  set Adiff : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
    ContMDiffSection.mk (diffSec (LeviCivita (I := I) g₂) (LeviCivita (I := I) g₁)
      (fun b => X b) (fun b => Y b)) hAsm with hAdiff
  -- The three covariant-derivative sections `∇₂_W X`, `∇₂_W Y`, `∇₂_W Z`.
  have hZcast : ∀ (S : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _)),
      ContMDiff I (I.prod 𝓘(ℝ, E)) ((∞ : WithTop ℕ∞) + 1) (T% (fun b => S b)) := by
    intro S
    rw [show ((∞ : WithTop ℕ∞) + 1) = (∞ : WithTop ℕ∞) from by rw [ENat.coe_top_add_one]]
    exact S.contMDiff
  have hDWXsm : ContMDiff I (I.prod 𝓘(ℝ, E)) (∞ : WithTop ℕ∞)
      (T% (covApply (LeviCivita (I := I) g₂) (fun b => W b) (fun b => X b))) := by
    rw [← contMDiffOn_univ]
    exact covApply_contMDiffOn (cov := LeviCivita (I := I) g₂) W.contMDiff (hZcast X)
  have hDWYsm : ContMDiff I (I.prod 𝓘(ℝ, E)) (∞ : WithTop ℕ∞)
      (T% (covApply (LeviCivita (I := I) g₂) (fun b => W b) (fun b => Y b))) := by
    rw [← contMDiffOn_univ]
    exact covApply_contMDiffOn (cov := LeviCivita (I := I) g₂) W.contMDiff (hZcast Y)
  have hDWZsm : ContMDiff I (I.prod 𝓘(ℝ, E)) (∞ : WithTop ℕ∞)
      (T% (covApply (LeviCivita (I := I) g₂) (fun b => W b) (fun b => Z b))) := by
    rw [← contMDiffOn_univ]
    exact covApply_contMDiffOn (cov := LeviCivita (I := I) g₂) W.contMDiff (hZcast Z)
  set DWX : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
    ContMDiffSection.mk (covApply (LeviCivita (I := I) g₂) (fun b => W b) (fun b => X b))
      hDWXsm with hDWX
  set DWY : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
    ContMDiffSection.mk (covApply (LeviCivita (I := I) g₂) (fun b => W b) (fun b => Y b))
      hDWYsm with hDWY
  set DWZ : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
    ContMDiffSection.mk (covApply (LeviCivita (I := I) g₂) (fun b => W b) (fun b => Z b))
      hDWZsm with hDWZ
  -- LHS: differentiate `p ↦ g₁(A(X,Y)(p), Z(p))` along `W` (metric-compatibility Leibniz).
  have hLHSfun : (fun p : M => g₁.inner p (Adiff p) (Z p))
      = (fun p : M => Tensor0SBundle.metricTensorField (I := I) g₁ p
          (fun c : Fin 2 =>
            (![Adiff, Z] : Fin 2 → ContMDiffSection I E (∞ : WithTop ℕ∞)
              (TangentSpace I : M → Type _)) c p)) := by
    funext p
    rw [metricTensorField_apply]
    simp [Matrix.cons_val_zero, Matrix.cons_val_one]
  have hLHS := metric_leibniz_extDeriv (I := I) g₁ g₂ ![Adiff, Z] W x
  rw [← hLHSfun] at hLHS
  -- The funext identity from the a=0 Koszul base.
  have hfun : (fun p : M => g₁.inner p (Adiff p) (Z p))
      = (fun p : M =>
          (1 / 2) * Tensor0SBundle.nabla0SFun (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
              (LeviCivita (I := I) g₂) X (Tensor0SBundle.metricTensorField (I := I) g₁) p
              (fun q : Fin 2 => if q = 0 then Y p else Z p) +
            (1 / 2) * Tensor0SBundle.nabla0SFun (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
              (LeviCivita (I := I) g₂) Y (Tensor0SBundle.metricTensorField (I := I) g₁) p
              (fun q : Fin 2 => if q = 0 then X p else Z p) -
            (1 / 2) * Tensor0SBundle.nabla0SFun (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
              (LeviCivita (I := I) g₂) Z (Tensor0SBundle.metricTensorField (I := I) g₁) p
              (fun q : Fin 2 => if q = 0 then X p else Y p)) := by
    funext p
    rw [hAdiff]
    change g₁.inner p
        ((CovariantDerivative.difference (LeviCivita (I := I) g₁) (LeviCivita (I := I) g₂) p)
          (Y p) (X p)) (Z p) = _
    rw [connDiff_koszul_nabla (I := I) g₁ g₂ X Y Z]
  have hmaster := congrArg (fun f : M → ℝ => extDerivFun (I := I) f x (W x)) hfun
  simp only [] at hmaster
  rw [hLHS] at hmaster
  -- Differentiability of a `∇₂g₁`-field evaluated on a smooth slot tuple.
  have hMDcombo : ∀ (V : Fin 3 → ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _)),
      MDifferentiableAt I 𝓘(ℝ, ℝ) (fun p : M => field p (fun a : Fin 3 => V a p)) x := by
    intro V
    exact (Tensor0SBundle.tensor0SField_eval_smooth_slots_contMDiffAt (𝕜 := ℝ) (E := E) (H := H)
      (I := I) (M := M) field V x).mdifferentiableAt (by simp)
  -- The `∇₂g₁`-field-eval / first-covariant-derivative bridge and the slot-form normalisation.
  have hbrgen : ∀ (V : Fin 3 → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _)),
      (fun p : M => field p (fun a : Fin 3 => V a p))
        = (fun p : M => Tensor0SBundle.nabla0SFun (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
            (LeviCivita (I := I) g₂) (V 0) (Tensor0SBundle.metricTensorField (I := I) g₁) p
            (fun q : Fin 2 => V q.succ p)) := by
    intro V
    funext p
    rw [hfield, Tensor0SBundle.totalNabla0S_apply,
      show (fun a : Fin 3 => V a p) = Fin.cons ((V 0) p) (fun q : Fin 2 => (V q.succ) p) from
        (Fin.cons_self_tail (fun a : Fin 3 => V a p)).symm,
      Tensor0SBundle.totalNabla0SFun_apply_section]
  have hVgen : ∀ (a bb cc : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _)),
      (fun p : M => Tensor0SBundle.nabla0SFun (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
          (LeviCivita (I := I) g₂)
          ((![a, bb, cc] : Fin 3 → ContMDiffSection I E (∞ : WithTop ℕ∞)
            (TangentSpace I : M → Type _)) 0)
          (Tensor0SBundle.metricTensorField (I := I) g₁) p
          (fun q : Fin 2 =>
            (![a, bb, cc] : Fin 3 → ContMDiffSection I E (∞ : WithTop ℕ∞)
              (TangentSpace I : M → Type _)) q.succ p))
        = (fun p : M => Tensor0SBundle.nabla0SFun (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
            (LeviCivita (I := I) g₂) a (Tensor0SBundle.metricTensorField (I := I) g₁) p
            (fun q : Fin 2 => if q = 0 then bb p else cc p)) := by
    intro a bb cc
    funext p
    have hs : (fun q : Fin 2 =>
        (![a, bb, cc] : Fin 3 → ContMDiffSection I E (∞ : WithTop ℕ∞)
          (TangentSpace I : M → Type _)) q.succ p) = (fun q : Fin 2 => if q = 0 then bb p else cc p) := by
      funext q; fin_cases q <;> simp
    rw [hs, Matrix.cons_val_zero]
  -- Bridges to `cX`, `cY`, `cZ` (the three `if`-form combos of `hfun`).
  have hbrX := (hbrgen ![X, Y, Z]).trans (hVgen X Y Z)
  have hbrY := (hbrgen ![Y, X, Z]).trans (hVgen Y X Z)
  have hbrZ := (hbrgen ![Z, X, Y]).trans (hVgen Z X Y)
  have hMDcX := hbrX ▸ hMDcombo ![X, Y, Z]
  have hMDcY := hbrY ▸ hMDcombo ![Y, X, Z]
  have hMDcZ := hbrZ ▸ hMDcombo ![Z, X, Y]
  -- The three nablaMetric second-derivative results, converted to `cX`, `cY`, `cZ` form.
  have hRX := nablaMetric_combo_extDeriv (I := I) g₁ g₂ ![X, Y, Z] W x
  have hRY := nablaMetric_combo_extDeriv (I := I) g₁ g₂ ![Y, X, Z] W x
  have hRZ := nablaMetric_combo_extDeriv (I := I) g₁ g₂ ![Z, X, Y] W x
  rw [hVgen X Y Z] at hRX
  rw [hVgen Y X Z] at hRY
  rw [hVgen Z X Y] at hRZ
  -- Linearity of the exterior derivative over the (scaled) sum of the three combos.
  have hdc : ∀ (c : M → ℝ), MDifferentiableAt I 𝓘(ℝ, ℝ) c x →
      MDifferentiableAt I 𝓘(ℝ, ℝ) (fun p : M => (1 / 2 : ℝ) * c p) x := by
    intro c hc
    exact (mdifferentiableAt_const (I := I) (I' := 𝓘(ℝ, ℝ)) (c := (1 / 2 : ℝ))).mul hc
  -- Name the three `if`-form combos and fold them into the master equation.
  set cX : M → ℝ := fun p : M => Tensor0SBundle.nabla0SFun (𝕜 := ℝ) (E := E) (H := H) (I := I)
    (M := M) 2 (LeviCivita (I := I) g₂) X (Tensor0SBundle.metricTensorField (I := I) g₁) p
    (fun q : Fin 2 => if q = 0 then Y p else Z p) with hcXdef
  set cY : M → ℝ := fun p : M => Tensor0SBundle.nabla0SFun (𝕜 := ℝ) (E := E) (H := H) (I := I)
    (M := M) 2 (LeviCivita (I := I) g₂) Y (Tensor0SBundle.metricTensorField (I := I) g₁) p
    (fun q : Fin 2 => if q = 0 then X p else Z p) with hcYdef
  set cZ : M → ℝ := fun p : M => Tensor0SBundle.nabla0SFun (𝕜 := ℝ) (E := E) (H := H) (I := I)
    (M := M) 2 (LeviCivita (I := I) g₂) Z (Tensor0SBundle.metricTensorField (I := I) g₁) p
    (fun q : Fin 2 => if q = 0 then X p else Y p) with hcZdef
  have hcX_app : ∀ p : M, cX p = Tensor0SBundle.nabla0SFun (𝕜 := ℝ) (E := E) (H := H) (I := I)
      (M := M) 2 (LeviCivita (I := I) g₂) X (Tensor0SBundle.metricTensorField (I := I) g₁) p
      (fun q : Fin 2 => if q = 0 then Y p else Z p) := fun p => rfl
  have hcY_app : ∀ p : M, cY p = Tensor0SBundle.nabla0SFun (𝕜 := ℝ) (E := E) (H := H) (I := I)
      (M := M) 2 (LeviCivita (I := I) g₂) Y (Tensor0SBundle.metricTensorField (I := I) g₁) p
      (fun q : Fin 2 => if q = 0 then X p else Z p) := fun p => rfl
  have hcZ_app : ∀ p : M, cZ p = Tensor0SBundle.nabla0SFun (𝕜 := ℝ) (E := E) (H := H) (I := I)
      (M := M) 2 (LeviCivita (I := I) g₂) Z (Tensor0SBundle.metricTensorField (I := I) g₁) p
      (fun q : Fin 2 => if q = 0 then X p else Y p) := fun p => rfl
  simp only [← hcX_app, ← hcY_app, ← hcZ_app] at hmaster
  have hsub' : ∀ {f g : M → ℝ}, MDifferentiableAt I 𝓘(ℝ, ℝ) f x →
      MDifferentiableAt I 𝓘(ℝ, ℝ) g x →
      extDerivFun (I := I) (f - g) x = extDerivFun (I := I) f x - extDerivFun (I := I) g x := by
    intro f g hf hg
    have h := extDerivFun_add (I := I) (g := f - g) (g' := g) (hf.sub hg) hg
    rw [sub_add_cancel] at h
    exact eq_sub_of_add_eq h.symm
  -- Linearity split of the exterior derivative of the combined RHS, applied to `W x`.
  rw [show (fun p : M => (1 / 2) * cX p + (1 / 2) * cY p - (1 / 2) * cZ p)
        = ((fun p : M => (1 / 2) * cX p) + (fun p : M => (1 / 2) * cY p))
          - (fun p : M => (1 / 2) * cZ p) from rfl,
    hsub' ((hdc _ hMDcX).add (hdc _ hMDcY)) (hdc _ hMDcZ),
    extDerivFun_add (hdc _ hMDcX) (hdc _ hMDcY),
    extDerivFun_const_mul I (1 / 2 : ℝ) hMDcX, extDerivFun_const_mul I (1 / 2 : ℝ) hMDcY,
    extDerivFun_const_mul I (1 / 2 : ℝ) hMDcZ] at hmaster
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul] at hmaster
  rw [hRX, hRY, hRZ] at hmaster
  rw [← hfield] at hmaster
  -- Normalise the slot functions and `Function.update`s to explicit matrices.
  have e3 : ∀ (a b c : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _)),
      (fun i : Fin 3 => (![a, b, c] i) x) = ![a x, b x, c x] := by
    intro a b c; funext i; fin_cases i <;> rfl
  have e2 : ∀ (a b : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _)),
      (fun i : Fin 2 => (![a, b] i) x) = ![a x, b x] := by
    intro a b; funext i; fin_cases i <;> rfl
  have hup30 : ∀ (v a b c : TangentSpace I x),
      Function.update (![a, b, c] : Fin 3 → TangentSpace I x) 0 v = ![v, b, c] := by
    intro v a b c; funext i; fin_cases i <;> simp
  have hup31 : ∀ (v a b c : TangentSpace I x),
      Function.update (![a, b, c] : Fin 3 → TangentSpace I x) 1 v = ![a, v, c] := by
    intro v a b c; funext i; fin_cases i <;> simp
  have hup32 : ∀ (v a b c : TangentSpace I x),
      Function.update (![a, b, c] : Fin 3 → TangentSpace I x) 2 v = ![a, b, v] := by
    intro v a b c; funext i; fin_cases i <;> simp
  have hup20 : ∀ (v a b : TangentSpace I x),
      Function.update (![a, b] : Fin 2 → TangentSpace I x) 0 v = ![v, b] := by
    intro v a b; funext i; fin_cases i <;> simp
  have hup21 : ∀ (v a b : TangentSpace I x),
      Function.update (![a, b] : Fin 2 → TangentSpace I x) 1 v = ![a, v] := by
    intro v a b; funext i; fin_cases i <;> simp
  have hc2 : ∀ (a b c : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _)),
      (![a, b, c] : Fin 3 → ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M → Type _)) 2 = c := fun _ _ _ => rfl
  simp only [Fin.sum_univ_two, Fin.sum_univ_three, e3, e2, hup30, hup31, hup32, hup20, hup21,
    hc2, metricTensorField_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at hmaster
  -- Realize the coercion values by the packaged covariant-derivative sections.
  have hDWXval : DWX x = ((LeviCivita (I := I) g₂) (fun p : M => X p) x) (W x) := rfl
  have hDWYval : DWY x = ((LeviCivita (I := I) g₂) (fun p : M => Y p) x) (W x) := rfl
  have hDWZval : DWZ x = ((LeviCivita (I := I) g₂) (fun p : M => Z p) x) (W x) := rfl
  have hAx : Adiff x = (CovariantDerivative.difference (LeviCivita (I := I) g₁)
      (LeviCivita (I := I) g₂) x) (Y x) (X x) := rfl
  -- Covariant derivative of the connection-difference section, via `covDerivConnDiff`.
  have hB : ((LeviCivita (I := I) g₂) (fun p : M => Adiff p) x) (W x)
      = covDerivConnDiff (I := I) g₂ g₁ W X Y x
        + (CovariantDerivative.difference (LeviCivita (I := I) g₁) (LeviCivita (I := I) g₂) x)
            (Y x) (DWX x)
        + (CovariantDerivative.difference (LeviCivita (I := I) g₁) (LeviCivita (I := I) g₂) x)
            (DWY x) (X x) := by
    have hcd : covDerivConnDiff (I := I) g₂ g₁ W X Y x
        = ((LeviCivita (I := I) g₂) (fun p : M => Adiff p) x) (W x)
          - (CovariantDerivative.difference (LeviCivita (I := I) g₁) (LeviCivita (I := I) g₂) x)
              (Y x) (DWX x)
          - (CovariantDerivative.difference (LeviCivita (I := I) g₁) (LeviCivita (I := I) g₂) x)
              (DWY x) (X x) := rfl
    rw [hcd]; abel
  -- Koszul identity on the three correction pairings.
  have hk1 := koszul_field (I := I) g₁ g₂ Y DWX Z x
  have hk2 := koszul_field (I := I) g₁ g₂ DWY X Z x
  have hk3 := koszul_field (I := I) g₁ g₂ Y X DWZ x
  simp only [hDWXval, hDWYval, hDWZval] at hB hk1 hk2 hk3
  rw [← hfield] at hk1 hk2 hk3
  have g_add_left : ∀ (v w y : TangentSpace I x),
      g₁.inner x (v + w) y = g₁.inner x v y + g₁.inner x w y := by
    intro v w y; rw [map_add (g₁.inner x), ContinuousLinearMap.add_apply]
  rw [hB] at hmaster
  simp only [g_add_left, hAx] at hmaster hk3 ⊢
  linarith [hmaster, hk1, hk2, hk3]

end Connection
end Integral
end DifferentialGeometry

end
