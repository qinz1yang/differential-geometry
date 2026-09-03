import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.Pairing.TopOrder.Decomposition
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Metric.CometricDoubleTrace
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricPerturbation.CometricSlotPairing
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricPerturbation.InverseCometricMultiplier

noncomputable section


open Bundle Manifold DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open scoped BigOperators Manifold ContDiff

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.PDE.DeTurck.RicciLinearization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete Real E

def topOrderBilinearPairingAdjointCoefficient (g gm : SmoothRiemannianMetric I M)
    (P V : SmoothCcTensor g 0 2) (sigma : Equiv.Perm (Fin 4)) :
    SmoothCcTensor g 0 4 :=
  domDomCongrSection (I := I) g sigma.symm
    (fourTensorProductCoefficient (I := I) (M := M) g
      (secondSlotMetricComparisonCoefficient (I := I) (M := M) g gm P) V)

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
theorem topOrderBilinearPairingAdjointCoefficient_self (g gm : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g 0 2) (sigma : Equiv.Perm (Fin 4)) :
    topOrderBilinearPairingAdjointCoefficient (I := I) (M := M) g gm S S sigma =
      topOrderPairingAdjointCoefficient (I := I) (M := M) g gm S sigma := rfl

private lemma edge_sum4_comm
    {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (F : A → B → C → D → Real) :
    (∑ a, ∑ b, ∑ c, ∑ d, F a b c d) =
      ∑ c, ∑ d, ∑ a, ∑ b, F a b c d := by
  classical
  calc
    (∑ a, ∑ b, ∑ c, ∑ d, F a b c d) =
        ∑ p : A × B, ∑ q : C × D, F p.1 p.2 q.1 q.2 := by
          simp only [Fintype.sum_prod_type]
    _ = ∑ q : C × D, ∑ p : A × B, F p.1 p.2 q.1 q.2 := Finset.sum_comm
    _ = ∑ c, ∑ d, ∑ a, ∑ b, F a b c d := by
          simp only [Fintype.sum_prod_type]

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma edge_bitrace_move
    (g gm : SmoothRiemannianMetric I M) (x : M)
    (S Z : TangentSpace I x →L[Real] TangentSpace I x →L[Real] Real)
    (e : Fin (Module.finrank Real E) → TangentSpace I x)
    (he : ∀ i j, g.inner x (e i) (e j) = if i = j then (1 : Real) else 0) :
    (∑ a : Fin (Module.finrank Real E), ∑ b : Fin (Module.finrank Real E),
        S (smoothOrthoFrame (I := I) gm x a x)
            (smoothOrthoFrame (I := I) gm x b x) *
          Z (smoothOrthoFrame (I := I) gm x a x)
            (smoothOrthoFrame (I := I) gm x b x)) =
      ∑ i : Fin (Module.finrank Real E), ∑ j : Fin (Module.finrank Real E),
        S (metricComparisonEndomorphism (I := I) g gm x (e i))
            (metricComparisonEndomorphism (I := I) g gm x (e j)) * Z (e i) (e j) := by
  classical
  let f : Fin (Module.finrank Real E) → TangentSpace I x :=
    fun a => smoothOrthoFrame (I := I) gm x a x
  let c : Fin (Module.finrank Real E) → Fin (Module.finrank Real E) → Real :=
    fun i a => g.inner x (e i) (f a)
  have hf : ∀ a b, gm.inner x (f a) (f b) = if a = b then (1 : Real) else 0 := by
    intro a b
    exact smoothOrthoFrame_orthonormal_at_center (I := I) gm x a b
  have hraise : ∀ i, metricComparisonEndomorphism (I := I) g gm x (e i) =
      ∑ a, c i a • f a := by
    intro i
    have hrep := orthonormal_tangent_expansion (I := I) (M := M) gm x f hf
      (metricComparisonEndomorphism (I := I) g gm x (e i))
    rw [← hrep]
    refine Finset.sum_congr rfl fun a _ => ?_
    congr 1
    rw [gm.symm x (f a) (metricComparisonEndomorphism (I := I) g gm x (e i))]
    rw [metricComparisonEndomorphism_apply]
    rw [inverseMetricSharpFib_inner (I := I) gm x
      (g0FlatCLM (I := I) g x (e i)) (f a)]
    rw [show cotangentToDualLinear (I := I) (x := x)
        (g0FlatCLM (I := I) g x (e i)) (f a) =
        cotangentToDual (I := I) (x := x)
          (g0FlatCLM (I := I) g x (e i)) (f a) from rfl]
    rw [cotangentToDual_g0FlatCLM]
  have hframe : ∀ a, f a = ∑ i, c i a • e i := by
    intro a
    exact (orthonormal_tangent_expansion (I := I) (M := M) g x e he (f a)).symm
  have hS : ∀ i j,
      S (metricComparisonEndomorphism (I := I) g gm x (e i))
          (metricComparisonEndomorphism (I := I) g gm x (e j)) =
        ∑ a, ∑ b, (c i a * c j b) * S (f a) (f b) := by
    intro i j
    rw [hraise i, hraise j]
    calc
      S (∑ a, c i a • f a) (∑ b, c j b • f b) =
          (∑ a, S (c i a • f a)) (∑ b, c j b • f b) := by
            exact congrArg
              (fun L : TangentSpace I x →L[Real] Real =>
                L (∑ b, c j b • f b))
              (map_sum S (fun a => c i a • f a) Finset.univ)
      _ = ∑ a, S (c i a • f a) (∑ b, c j b • f b) := by
            rw [sum_apply]
      _ = ∑ a, ∑ b, S (c i a • f a) (c j b • f b) := by
            refine Finset.sum_congr rfl fun a _ => ?_
            exact map_sum (S (c i a • f a))
              (fun b => c j b • f b) Finset.univ
      _ = ∑ a, ∑ b, (c i a * c j b) * S (f a) (f b) := by
            refine Finset.sum_congr rfl fun a _ => ?_
            refine Finset.sum_congr rfl fun b _ => ?_
            simp only [map_smul, smul_apply, smul_eq_mul]
            ring
  have hZ : ∀ a b, Z (f a) (f b) =
      ∑ i, ∑ j, (c i a * c j b) * Z (e i) (e j) := by
    intro a b
    rw [hframe a, hframe b]
    calc
      Z (∑ i, c i a • e i) (∑ j, c j b • e j) =
          (∑ i, Z (c i a • e i)) (∑ j, c j b • e j) := by
            exact congrArg
              (fun L : TangentSpace I x →L[Real] Real =>
                L (∑ j, c j b • e j))
              (map_sum Z (fun i => c i a • e i) Finset.univ)
      _ = ∑ i, Z (c i a • e i) (∑ j, c j b • e j) := by
            rw [sum_apply]
      _ = ∑ i, ∑ j, Z (c i a • e i) (c j b • e j) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            exact map_sum (Z (c i a • e i))
              (fun j => c j b • e j) Finset.univ
      _ = ∑ i, ∑ j, (c i a * c j b) * Z (e i) (e j) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            refine Finset.sum_congr rfl fun j _ => ?_
            simp only [map_smul, smul_apply, smul_eq_mul]
            ring
  calc
    (∑ a, ∑ b, S (f a) (f b) * Z (f a) (f b)) =
        ∑ a, ∑ b, ∑ i, ∑ j,
          (c i a * c j b) * (S (f a) (f b) * Z (e i) (e j)) := by
      refine Finset.sum_congr rfl fun a _ => ?_
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [hZ a b, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    _ = ∑ i, ∑ j, ∑ a, ∑ b,
          (c i a * c j b) * (S (f a) (f b) * Z (e i) (e j)) :=
      edge_sum4_comm (fun a b i j =>
        (c i a * c j b) * (S (f a) (f b) * Z (e i) (e j)))
    _ = ∑ i, ∑ j,
        S (metricComparisonEndomorphism (I := I) g gm x (e i))
            (metricComparisonEndomorphism (I := I) g gm x (e j)) * Z (e i) (e j) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hS i j, Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun b _ => ?_
      ring

private def edgeEvalCLM (s : Nat) (x : M) (v : Fin s → E) :
    Tensor0SSpace s I x →L[Real] Real :=
  haveI : FiniteDimensional Real (Tensor0SSpace s I x) := inferInstance
  LinearMap.toContinuousLinearMap
    { toFun := fun D => Tensor0SSpace.toModel D v
      map_add' := fun D₁ D₂ => by
        rw [Tensor0SSpace.toModel_add, add_apply]
      map_smul' := fun c D => by
        rw [Tensor0SSpace.toModel_smul]
        rfl }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma edgeEvalCLM_apply (s : Nat) (x : M) (v : Fin s → E)
    (D : Tensor0SSpace s I x) :
    edgeEvalCLM (I := I) (M := M) s x v D = Tensor0SSpace.toModel D v := rfl

private def edgeFeedCLM (s : Nat) (x : M) (G : Tensor0SSpace (s + 2) I x)
    (v : Fin s → E) :
    TangentSpace I x →L[Real] TangentSpace I x →L[Real] Real :=
  haveI : FiniteDimensional Real (TangentSpace I x) :=
    inferInstanceAs (FiniteDimensional Real E)
  LinearMap.toContinuousLinearMap
    { toFun := fun p => (edgeEvalCLM (I := I) (M := M) s x v).comp
        (tensor0SCurry (𝕜 := Real) (I := I) (M := M) s x
          ((tensor0SCurry (𝕜 := Real) (I := I) (M := M) (s + 1) x G) p))
      map_add' := fun p p' => by
        rw [map_add, map_add, ContinuousLinearMap.comp_add]
      map_smul' := fun c p => by
        rw [map_smul, map_smul, RingHom.id_apply]
        ext q
        simp only [ContinuousLinearMap.comp_apply, smul_apply,
          map_smul] }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma edgeFeedCLM_apply (s : Nat) (x : M)
    (G : Tensor0SSpace (s + 2) I x) (v : Fin s → E)
    (p q : TangentSpace I x) :
    edgeFeedCLM (I := I) (M := M) s x G v p q =
      Tensor0SSpace.toModel G
        (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x p)
          (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x q) v)) := by
  rw [edgeFeedCLM, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk,
    AddHom.coe_mk, ContinuousLinearMap.comp_apply, edgeEvalCLM_apply,
    TensorMultilinear.tensor0S_curry_toModel_apply_tangent (I := I) (M := M)
      (T := tensor0SCurry (𝕜 := Real) (I := I) (M := M) (s + 1) x G p)
      (v0 := q) (vs := v),
    TensorMultilinear.tensor0S_curry_toModel_apply_tangent (I := I) (M := M)
      (T := G) (v0 := p)
      (vs := Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x q) v)]

private lemma edge_sum_succ {A R : Type*} [Fintype A] [AddCommMonoid R]
    (s : Nat) (F : (Fin (s + 1) → A) → R) :
    (∑ J : Fin (s + 1) → A, F J) =
      ∑ a : A, ∑ J : Fin s → A, F (Fin.cons a J) := by
  classical
  calc
    (∑ J : Fin (s + 1) → A, F J) =
        ∑ p : A × (Fin s → A),
          F ((Fin.consEquiv (fun _ : Fin (s + 1) => A)) p) :=
      ((Fin.consEquiv (fun _ : Fin (s + 1) => A)).sum_comp F).symm
    _ = ∑ a : A, ∑ J : Fin s → A, F (Fin.cons a J) := by
      rw [Fintype.sum_prod_type]
      rfl

private lemma edge_sum2 {A : Type*} [Fintype A] (F : (Fin 2 → A) → Real) :
    (∑ J : Fin 2 → A, F J) = ∑ a : A, ∑ b : A, F ![a, b] := by
  classical
  calc
    (∑ J : Fin 2 → A, F J) =
        ∑ p : A × A, F ((finTwoArrowEquiv A).symm p) :=
      ((finTwoArrowEquiv A).symm.sum_comp F).symm
    _ = ∑ a : A, ∑ b : A, F ![a, b] := by
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun a _ => ?_
      refine Finset.sum_congr rfl fun b _ => ?_
      congr 1

private lemma edge_sum4 {A : Type*} [Fintype A] (F : (Fin 4 → A) → Real) :
    (∑ J : Fin 4 → A, F J) =
      ∑ a : A, ∑ b : A, ∑ c : A, ∑ d : A, F ![a, b, c, d] := by
  classical
  rw [edge_sum_succ (s := 3)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [edge_sum_succ (s := 2)]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [edge_sum_succ (s := 1)]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [edge_sum_succ (s := 0)]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.sum_eq_single (fun i : Fin 0 => i.elim0)]
  · congr 1
  · intro q _ hq
    exact absurd (Subsingleton.elim q (fun i : Fin 0 => i.elim0)) hq
  · intro h
    exact absurd (Finset.mem_univ _) h

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
theorem topOrderBilinearPairingAdjointCoefficient_apply (g gm : SmoothRiemannianMetric I M)
    (P V : SmoothCcTensor g 0 2) (σ : Equiv.Perm (Fin 4))
    (x : M) (v : Fin 4 → E) :
    unitModel (I := I) (M := M) g 4
        (topOrderBilinearPairingAdjointCoefficient (I := I) (M := M) g gm P V σ) x v =
      unitModel (I := I) (M := M) g 2 P x
          ![metricComparisonEndomorphismField (I := I) (M := M) g gm x (v (σ.symm 0)),
            metricComparisonEndomorphismField (I := I) (M := M) g gm x (v (σ.symm 1))] *
        unitModel (I := I) (M := M) g 2 V x
          ![v (σ.symm 2), v (σ.symm 3)] := by
  rw [topOrderBilinearPairingAdjointCoefficient, domDomCongrSection_unitModel,
    ContinuousMultilinearMap.domDomCongr_apply, fourTensorProductCoefficient_apply,
    secondSlotMetricComparisonCoefficient_apply]
  congr 2
  all_goals
    funext k
    fin_cases k <;> rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma edge_inner0 (g : SmoothRiemannianMetric I M) (s : Nat)
    (A B : SmoothCcTensor g 0 s) (x : M)
    (e : Fin (Module.finrank Real E) → TangentSpace I x)
    (bse : Module.Basis (Fin (Module.finrank Real E)) Real (TangentSpace I x))
    (hbse : ∀ i, bse i = e i)
    (horth : ∀ a b, g.inner x (e a) (e b) = if a = b then (1 : Real) else 0) :
    tensorInnerPointwise (I := I) (M := M) g 0 s x (A.toFun x) (B.toFun x) =
      ∑ J : Fin s → Fin (Module.finrank Real E),
        unitModel (I := I) (M := M) g s A x (fun k => (e (J k) : E)) *
          unitModel (I := I) (M := M) g s B x (fun k => (e (J k) : E)) := by
  classical
  rw [SmoothCcTensor.toFun_apply, SmoothCcTensor.toFun_apply]
  rw [tensorInnerPointwise_eq_sum_componentS_mul
    (I := I) (M := M) g 0 s x e bse rfl hbse horth
    (A.toSection x) (B.toSection x)]
  have hcomp : ∀ (T : SmoothCcTensor g 0 s)
      (K : Fin 0 → Fin (Module.finrank Real E))
      (J : Fin s → Fin (Module.finrank Real E)),
      fiberNormSqComponent (I := I) (M := M) g x 0 s
          (T.toSection x) (Module.finrank Real E) e K J =
        unitModel (I := I) (M := M) g s T x
          (fun k => (e (J k) : E)) := by
    intro T K J
    rw [show fiberNormSqComponent (I := I) (M := M) g x 0 s
        (T.toSection x) (Module.finrank Real E) e K J =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace s I x from
          T.toSection x) (coframeS (I := I) (M := M) g x 0 e K))
        (fun k => (e (J k) : E)) from rfl]
    rw [coframeS_zero_eq_unitZeroSec (I := I) (M := M) g x e K]
    rfl
  have hK : ∀ F : (Fin 0 → Fin (Module.finrank Real E)) → Real,
      (∑ K : Fin 0 → Fin (Module.finrank Real E), F K) = F Fin.elim0 := by
    intro F
    rw [Finset.sum_eq_single Fin.elim0]
    · intro q _ hq
      exact absurd (Subsingleton.elim q Fin.elim0) hq
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [hK]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [hcomp A Fin.elim0 J, hcomp B Fin.elim0 J]

omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
theorem topOrderBilinearPairing_pointwise (g gm : SmoothRiemannianMetric I M)
    (P V : SmoothCcTensor g 0 2) (G : SmoothCcTensor g 0 4)
    (σ : Equiv.Perm (Fin 4)) (x : M) :
    tensorInnerPointwise (I := I) (M := M) g 0 2 x (V.toFun x)
        ((operatorFieldApply (I := I) (M := M) g 2 2
          (topOrderPairingCoefficient (I := I) (M := M) g gm G σ) P).toFun x) =
      tensorInnerPointwise (I := I) (M := M) g 0 4 x
        ((topOrderBilinearPairingAdjointCoefficient (I := I) (M := M) g gm P V σ).toFun x)
        (G.toFun x) := by
  classical
  obtain ⟨e, bse, hbse, horth⟩ :=
    exists_orthoFrame_basis_E (I := I) (M := M) g x
  let eE : Fin (Module.finrank Real E) → E := fun i =>
    tangentSpaceModelContinuousLinearEquiv (I := I) x (e i)
  let fE : Fin (Module.finrank Real E) → E := fun i =>
    tangentSpaceModelContinuousLinearEquiv (I := I) x
      (smoothOrthoFrame (I := I) gm x i x)
  let mE : Fin (Module.finrank Real E) → E := fun i =>
    tangentSpaceModelContinuousLinearEquiv (I := I) x
      (metricComparisonEndomorphism (I := I) g gm x (e i))
  have heE : ∀ i : Fin (Module.finrank Real E), (e i : E) = eE i := by
    intro i
    with_unfolding_all rfl
  rw [edge_inner0 (I := I) (M := M) g 2 V
      (operatorFieldApply (I := I) (M := M) g 2 2
        (topOrderPairingCoefficient (I := I) (M := M) g gm G σ) P) x e bse hbse horth,
    edge_inner0 (I := I) (M := M) g 4
      (topOrderBilinearPairingAdjointCoefficient (I := I) (M := M) g gm P V σ) G x e bse hbse horth,
    edge_sum2]
  simp_rw [heE]
  have hvec2 : ∀ i j : Fin (Module.finrank Real E),
      (fun k => eE (![i, j] k)) = ![eE i, eE j] := by
    intro i j
    funext k
    fin_cases k <;> rfl
  have hcons2 : ∀ u w : E, (Fin.cons u (Fin.cons w ![]) : Fin 2 → E) = ![u, w] := by
    intro u w
    funext k
    fin_cases k <;> rfl
  have hvec4 : ∀ a b i j : Fin (Module.finrank Real E),
      (Fin.cons (eE a)
          (Fin.cons (eE b) ![eE i, eE j]) : Fin 4 → E) =
        fun k => eE (![a, b, i, j] k) := by
    intro a b i j
    funext k
    fin_cases k <;> rfl
  simp_rw [hvec2]
  have hmove : ∀ i j : Fin (Module.finrank Real E),
      (∑ a : Fin (Module.finrank Real E),
        ∑ b : Fin (Module.finrank Real E),
          unitModel (I := I) (M := M) g 2 P x
              ![fE a, fE b] *
            unitModel (I := I) (M := M) g 4 G x
              (fun k => (Fin.cons
                (fE a)
                (Fin.cons (fE b)
                  ![eE i, eE j]) : Fin 4 → E) (σ k))) =
        ∑ a : Fin (Module.finrank Real E),
        ∑ b : Fin (Module.finrank Real E),
          unitModel (I := I) (M := M) g 2 P x
              ![mE a, mE b] *
            unitModel (I := I) (M := M) g 4 G x
              (fun k => (Fin.cons (eE a)
                (Fin.cons (eE b) ![eE i, eE j]) : Fin 4 → E)
                (σ k)) := by
    intro i j
    let Px : Tensor0SSpace 2 I x :=
      (show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace 2 I x from P.toSection x)
        (unitTensor (I := I) (M := M) x)
    let Gx : Tensor0SSpace 4 I x :=
      (show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace 4 I x from G.toSection x)
        (unitTensor (I := I) (M := M) x)
    have hm := edge_bitrace_move (I := I) (M := M) g gm x
      (edgeFeedCLM (I := I) (M := M) 0 x Px ![])
      (edgeFeedCLM (I := I) (M := M) 2 x
        (slotPerm4Fib (I := I) (M := M) x σ Gx) ![eE i, eE j])
      e horth
    simp only [edgeFeedCLM_apply, slotPerm4Fib_toModel,
      ContinuousMultilinearMap.domDomCongr_apply] at hm
    have hPx (v : Fin 2 → E) : Tensor0SSpace.toModel Px v =
        unitModel (I := I) (M := M) g 2 P x v := by
      rfl
    have hGx (v : Fin 4 → E) : Tensor0SSpace.toModel Gx v =
        unitModel (I := I) (M := M) g 4 G x v := by
      rfl
    simpa only [hPx, hGx, eE, fE, mE, hcons2] using hm
  have hmE : ∀ i : Fin (Module.finrank Real E),
      metricComparisonEndomorphismField (I := I) (M := M) g gm x (eE i) = mE i := by
    intro i
    with_unfolding_all rfl
  calc
    (∑ i, ∑ j,
        unitModel (I := I) (M := M) g 2 V x ![eE i, eE j] *
          unitModel (I := I) (M := M) g 2
            (operatorFieldApply (I := I) (M := M) g 2 2
              (topOrderPairingCoefficient (I := I) (M := M) g gm G σ) P) x
            ![eE i, eE j]) =
      ∑ i, ∑ j,
        unitModel (I := I) (M := M) g 2 V x ![eE i, eE j] *
          (∑ a, ∑ b,
            unitModel (I := I) (M := M) g 2 P x
                ![fE a, fE b] *
              unitModel (I := I) (M := M) g 4 G x
                (fun k => (Fin.cons (fE a)
                  (Fin.cons (fE b) ![eE i, eE j]) : Fin 4 → E) (σ k))) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [topOrderPairingCoefficient_apply (I := I) (M := M) g gm P G σ x]
        simp only [fE, tangentSpaceModelContinuousLinearEquiv_apply]
    _ = ∑ i, ∑ j,
        unitModel (I := I) (M := M) g 2 V x ![eE i, eE j] *
          (∑ a, ∑ b,
            unitModel (I := I) (M := M) g 2 P x
                ![mE a, mE b] *
              unitModel (I := I) (M := M) g 4 G x
                (fun k => (Fin.cons (eE a)
                  (Fin.cons (eE b) ![eE i, eE j]) : Fin 4 → E) (σ k))) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hmove i j]
    _ = ∑ a, ∑ b, ∑ i, ∑ j,
        (unitModel (I := I) (M := M) g 2 P x
              ![mE a, mE b] *
            unitModel (I := I) (M := M) g 2 V x ![eE i, eE j]) *
          unitModel (I := I) (M := M) g 4 G x
            (fun k => (Fin.cons (eE a)
              (Fin.cons (eE b) ![eE i, eE j]) : Fin 4 → E) (σ k)) := by
        rw [show (∑ i, ∑ j,
            unitModel (I := I) (M := M) g 2 V x ![eE i, eE j] *
              (∑ a, ∑ b,
                unitModel (I := I) (M := M) g 2 P x
                    ![mE a, mE b] *
                  unitModel (I := I) (M := M) g 4 G x
                    (fun k => (Fin.cons (eE a)
                      (Fin.cons (eE b) ![eE i, eE j]) : Fin 4 → E) (σ k)))) =
            ∑ i, ∑ j, ∑ a, ∑ b,
              unitModel (I := I) (M := M) g 2 V x ![eE i, eE j] *
                (unitModel (I := I) (M := M) g 2 P x
                    ![mE a, mE b] *
                  unitModel (I := I) (M := M) g 4 G x
                    (fun k => (Fin.cons (eE a)
                      (Fin.cons (eE b) ![eE i, eE j]) : Fin 4 → E) (σ k))) from by
              refine Finset.sum_congr rfl fun i _ => ?_
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun a _ => ?_
              rw [Finset.mul_sum]]
        rw [edge_sum4_comm (fun i j a b =>
          unitModel (I := I) (M := M) g 2 V x ![eE i, eE j] *
            (unitModel (I := I) (M := M) g 2 P x
                ![mE a, mE b] *
              unitModel (I := I) (M := M) g 4 G x
                (fun k => (Fin.cons (eE a)
                  (Fin.cons (eE b) ![eE i, eE j]) : Fin 4 → E) (σ k))))]
        refine Finset.sum_congr rfl fun a _ => ?_
        refine Finset.sum_congr rfl fun b _ => ?_
        refine Finset.sum_congr rfl fun i _ => ?_
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
    _ = ∑ K : Fin 4 → Fin (Module.finrank Real E),
        (unitModel (I := I) (M := M) g 2 P x
              ![mE (K 0), mE (K 1)] *
            unitModel (I := I) (M := M) g 2 V x ![eE (K 2), eE (K 3)]) *
          unitModel (I := I) (M := M) g 4 G x (fun k => eE (K (σ k))) := by
        rw [edge_sum4]
        refine Finset.sum_congr rfl fun a _ => ?_
        refine Finset.sum_congr rfl fun b _ => ?_
        refine Finset.sum_congr rfl fun i _ => ?_
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hvec4 a b i j]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.cons_val_three,
          Matrix.head_cons, Matrix.tail_cons]
    _ = ∑ J : Fin 4 → Fin (Module.finrank Real E),
        unitModel (I := I) (M := M) g 4
            (topOrderBilinearPairingAdjointCoefficient (I := I) (M := M) g gm P V σ) x
            (fun k => eE (J k)) *
          unitModel (I := I) (M := M) g 4 G x (fun k => eE (J k)) := by
        refine Fintype.sum_equiv
          (Equiv.arrowCongr σ.symm
            (Equiv.refl (Fin (Module.finrank Real E))))
          (fun K =>
            (unitModel (I := I) (M := M) g 2 P x
                  ![mE (K 0), mE (K 1)] *
                unitModel (I := I) (M := M) g 2 V x ![eE (K 2), eE (K 3)]) *
              unitModel (I := I) (M := M) g 4 G x (fun k => eE (K (σ k))))
          (fun J =>
            unitModel (I := I) (M := M) g 4
                (topOrderBilinearPairingAdjointCoefficient (I := I) (M := M) g gm P V σ) x
                (fun k => eE (J k)) *
              unitModel (I := I) (M := M) g 4 G x (fun k => eE (J k)))
          (fun K => ?_)
        have heqv :
            (Equiv.arrowCongr σ.symm
              (Equiv.refl (Fin (Module.finrank Real E)))) K =
              (fun k => K (σ k)) := by
          funext k
          simp [Equiv.arrowCongr]
        rw [heqv]
        congr 1
        simpa only [hmE, Equiv.apply_symm_apply] using
          (topOrderBilinearPairingAdjointCoefficient_apply
            (I := I) (M := M) g gm P V σ x
            (fun k => eE (K (σ k)))).symm

omit [BoundarylessManifold I M] in
omit [I.Boundaryless] in
theorem topOrderBilinearPairing_l2 (g gm : SmoothRiemannianMetric I M)
    (P V : SmoothCcTensor g 0 2) (G : SmoothCcTensor g 0 4)
    (σ : Equiv.Perm (Fin 4)) :
    tensorL2Inner (I := I) (M := M) g 0 2 V.toFun
        (operatorFieldApply (I := I) (M := M) g 2 2
          (topOrderPairingCoefficient (I := I) (M := M) g gm G σ) P).toFun =
      tensorL2Inner (I := I) (M := M) g 0 4
        (topOrderBilinearPairingAdjointCoefficient (I := I) (M := M) g gm P V σ).toFun G.toFun := by
  classical
  unfold tensorL2Inner
  refine MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall fun x => ?_)
  exact topOrderBilinearPairing_pointwise (I := I) (M := M) g gm P V G σ x

omit [BoundarylessManifold I M] in
omit [I.Boundaryless] in
theorem topOrderBilinearPairing_inner (g gm : SmoothRiemannianMetric I M)
    (P V : SmoothCcTensor g 0 2) (G : SmoothCcTensor g 0 4)
    (σ : Equiv.Perm (Fin 4)) :
    Inner.inner Real V
        (operatorFieldApply (I := I) (M := M) g 2 2
          (topOrderPairingCoefficient (I := I) (M := M) g gm G σ) P) =
      Inner.inner Real
        (topOrderBilinearPairingAdjointCoefficient (I := I) (M := M) g gm P V σ) G := by
  rw [SmoothCcTensor.inner_def, SmoothCcTensor.inner_def]
  exact topOrderBilinearPairing_l2 (I := I) (M := M) g gm P V G σ

theorem topOrderBilinearPairing_green (g gm : SmoothRiemannianMetric I M)
    (P U V : SmoothCcTensor g 0 2) (σ : Equiv.Perm (Fin 4)) :
    Inner.inner Real V
        (operatorFieldApply (I := I) (M := M) g 2 2
          (topOrderPairingCoefficient (I := I) (M := M) g gm
            (iteratedCovGrad (I := I) g 0 2 2 U) σ) P) =
      -Inner.inner Real
        (covDivergence (I := I) (M := M) g 3
          (topOrderBilinearPairingAdjointCoefficient (I := I) (M := M) g gm P V σ))
        (iteratedCovGrad (I := I) g 0 2 1 U) := by
  let Q : SmoothCcTensor g 0 4 :=
    topOrderBilinearPairingAdjointCoefficient (I := I) (M := M) g gm P V σ
  let U₁ : SmoothCcTensor g 0 3 := iteratedCovGrad (I := I) g 0 2 1 U
  have hjet : iteratedCovGrad (I := I) g 0 2 2 U =
      covGrad (I := I) (M := M) g 0 3 U₁ := by
    simpa only [U₁] using iteratedCovGrad_succ g 0 2 1 U
  have hgreen :
      Inner.inner Real (covGrad (I := I) (M := M) g 0 3 U₁) Q =
        -Inner.inner Real U₁
          (covDivergence (I := I) (M := M) g 3 Q) := by
    rw [SmoothCcTensor.inner_def, SmoothCcTensor.inner_def]
    exact tensorL2Inner_covGrad_eq_neg_tensorL2Inner_covDivergence
      (I := I) (M := M) g 3 U₁ Q
  calc
    Inner.inner Real V
        (operatorFieldApply (I := I) (M := M) g 2 2
          (topOrderPairingCoefficient (I := I) (M := M) g gm
            (iteratedCovGrad (I := I) g 0 2 2 U) σ) P) =
        Inner.inner Real Q (iteratedCovGrad (I := I) g 0 2 2 U) := by
      exact topOrderBilinearPairing_inner (I := I) (M := M) g gm P V
        (iteratedCovGrad (I := I) g 0 2 2 U) σ
    _ = Inner.inner Real (covGrad (I := I) (M := M) g 0 3 U₁) Q := by
      rw [hjet, real_inner_comm]
    _ = -Inner.inner Real U₁
        (covDivergence (I := I) (M := M) g 3 Q) := hgreen
    _ = -Inner.inner Real
        (covDivergence (I := I) (M := M) g 3 Q) U₁ := by
      rw [real_inner_comm]

def ricciDeTurckTopOrderPairingCoefficientForJet (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2) (G : SmoothCcTensor g 0 4) {delta : Real}
    (hdelta : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) delta)
    (hdeltaZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) delta)
    (qA qB : Fin 4 → Equiv.Perm (Fin 4))
    (q : Fin 3 → Equiv.Perm (Fin 4)) (epsilon : Fin 3 → Real)
    (s : Real) : SmoothCcTensor g 2 2 :=
  let gm := metricPerturbationPath (I := I) g T 0 hdelta hdeltaZ s
  (2 : Real) • (s • ((1 / 2 : Real) •
      (riemannTopOrderPairingCoefficient (I := I) (M := M) g gm G qA +
        riemannTopOrderPairingCoefficient (I := I) (M := M) g gm G qB))) +
    s • ∑ i : Fin 3, epsilon i • ((1 / 2 : Real) •
      (topOrderPairingCoefficient (I := I) (M := M) g gm G (q i) +
        topOrderPairingCoefficient (I := I) (M := M) g gm G
          ((q i).trans (Equiv.swap (0 : Fin 4) 1))))

def ricciDeTurckTopOrderBilinearPairingCoefficient (g : SmoothRiemannianMetric I M)
    (T U : SmoothCcTensor g 0 2) {delta : Real}
    (hdelta : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) delta)
    (hdeltaZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) delta)
    (qA qB : Fin 4 → Equiv.Perm (Fin 4))
    (q : Fin 3 → Equiv.Perm (Fin 4)) (epsilon : Fin 3 → Real)
    (s : Real) : SmoothCcTensor g 2 2 :=
  ricciDeTurckTopOrderPairingCoefficientForJet (I := I) (M := M) g T
    (iteratedCovGrad (I := I) g 0 2 2 U) hdelta hdeltaZ qA qB q epsilon s

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem ricciDeTurckTopOrderBilinearPairingCoefficient_eq_coefficientForJet (g : SmoothRiemannianMetric I M)
    (T U : SmoothCcTensor g 0 2) {delta : Real}
    (hdelta : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) delta)
    (hdeltaZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) delta)
    (qA qB : Fin 4 → Equiv.Perm (Fin 4))
    (q : Fin 3 → Equiv.Perm (Fin 4)) (epsilon : Fin 3 → Real)
    (s : Real) :
    ricciDeTurckTopOrderBilinearPairingCoefficient (I := I) (M := M) g T U hdelta hdeltaZ qA qB q epsilon s =
      ricciDeTurckTopOrderPairingCoefficientForJet (I := I) (M := M) g T
        (iteratedCovGrad (I := I) g 0 2 2 U)
        hdelta hdeltaZ qA qB q epsilon s := rfl

omit [SigmaCompactSpace M] in
omit [BoundarylessManifold I M] in
omit [I.Boundaryless] in
theorem ricciDeTurckTopOrderPairingCoefficientForJet_apply
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (G : SmoothCcTensor g 0 4) {delta : Real}
    (hdelta : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) delta)
    (hdeltaZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) delta)
    (qA qB : Fin 4 → Equiv.Perm (Fin 4))
    (q : Fin 3 → Equiv.Perm (Fin 4)) (epsilon : Fin 3 → Real)
    (s : Real) :
    operatorFieldApply (I := I) (M := M) g 2 2
        (ricciDeTurckTopOrderPairingCoefficientForJet (I := I) (M := M) g T G hdelta hdeltaZ
          qA qB q epsilon s) T =
      operatorFieldApply (I := I) (M := M) g 4 2
        ((2 : Real) • riemannPalatiniDecompositionC2Family
            (I := I) (M := M) g T hdelta hdeltaZ qA qB s +
          deTurckLieCovariantDerivativeDecompositionC2Family
            (I := I) (M := M) g T hdelta hdeltaZ q epsilon s) G := by
  rw [ricciDeTurckTopOrderPairingCoefficientForJet, riemannPalatiniDecompositionC2Family,
    deTurckLieCovariantDerivativeDecompositionC2Family,
    Fin.sum_univ_three, Fin.sum_univ_three]
  simp only [operatorFieldApplication_add_left, operatorFieldApplication_smul_left]
  rw [riemannTopOrderPairing_apply (I := I) (M := M) g
      (metricPerturbationPath (I := I) g T 0 hdelta hdeltaZ s) T G qA,
    riemannTopOrderPairing_apply (I := I) (M := M) g
      (metricPerturbationPath (I := I) g T 0 hdelta hdeltaZ s) T G qB,
    topOrderPairingCoefficient_decomposition (I := I) (M := M) g
      (metricPerturbationPath (I := I) g T 0 hdelta hdeltaZ s) T G (q 0),
    topOrderPairingCoefficient_decomposition (I := I) (M := M) g
      (metricPerturbationPath (I := I) g T 0 hdelta hdeltaZ s) T G
      ((q 0).trans (Equiv.swap (0 : Fin 4) 1)),
    topOrderPairingCoefficient_decomposition (I := I) (M := M) g
      (metricPerturbationPath (I := I) g T 0 hdelta hdeltaZ s) T G (q 1),
    topOrderPairingCoefficient_decomposition (I := I) (M := M) g
      (metricPerturbationPath (I := I) g T 0 hdelta hdeltaZ s) T G
      ((q 1).trans (Equiv.swap (0 : Fin 4) 1)),
    topOrderPairingCoefficient_decomposition (I := I) (M := M) g
      (metricPerturbationPath (I := I) g T 0 hdelta hdeltaZ s) T G (q 2),
    topOrderPairingCoefficient_decomposition (I := I) (M := M) g
      (metricPerturbationPath (I := I) g T 0 hdelta hdeltaZ s) T G
      ((q 2).trans (Equiv.swap (0 : Fin 4) 1))]

def ricciDeTurckTopOrderBilinearPairingAdjoint (g : SmoothRiemannianMetric I M)
    (T P V : SmoothCcTensor g 0 2) {delta : Real}
    (hdelta : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) delta)
    (hdeltaZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) delta)
    (qA qB : Fin 4 → Equiv.Perm (Fin 4))
    (q : Fin 3 → Equiv.Perm (Fin 4)) (epsilon : Fin 3 → Real)
    (s : Real) : SmoothCcTensor g 0 4 :=
  let gm := metricPerturbationPath (I := I) g T 0 hdelta hdeltaZ s
  (2 : Real) • (s • ((1 / 2 : Real) •
      ((1 / 2 : Real) •
          (topOrderBilinearPairingAdjointCoefficient (I := I) (M := M) g gm P V (qA 0) +
            topOrderBilinearPairingAdjointCoefficient (I := I) (M := M) g gm P V (qA 1) -
            topOrderBilinearPairingAdjointCoefficient (I := I) (M := M) g gm P V (qA 2) -
            topOrderBilinearPairingAdjointCoefficient (I := I) (M := M) g gm P V (qA 3)) +
        (1 / 2 : Real) •
          (topOrderBilinearPairingAdjointCoefficient (I := I) (M := M) g gm P V (qB 0) +
            topOrderBilinearPairingAdjointCoefficient (I := I) (M := M) g gm P V (qB 1) -
            topOrderBilinearPairingAdjointCoefficient (I := I) (M := M) g gm P V (qB 2) -
            topOrderBilinearPairingAdjointCoefficient (I := I) (M := M) g gm P V (qB 3))))) +
    s • ∑ i : Fin 3, epsilon i • ((1 / 2 : Real) •
      (topOrderBilinearPairingAdjointCoefficient (I := I) (M := M) g gm P V (q i) +
        topOrderBilinearPairingAdjointCoefficient (I := I) (M := M) g gm P V
          ((q i).trans (Equiv.swap (0 : Fin 4) 1))))

omit [SigmaCompactSpace M] in
omit [BoundarylessManifold I M] in
theorem ricciDeTurckTopOrderBilinearPairing_pointwise
    (g : SmoothRiemannianMetric I M) (T P U V : SmoothCcTensor g 0 2)
    {delta : Real}
    (hdelta : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) delta)
    (hdeltaZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) delta)
    (qA qB : Fin 4 → Equiv.Perm (Fin 4))
    (q : Fin 3 → Equiv.Perm (Fin 4)) (epsilon : Fin 3 → Real)
    (s : Real) (x : M) :
    tensorInnerPointwise (I := I) (M := M) g 0 2 x (V.toFun x)
        ((operatorFieldApply (I := I) (M := M) g 2 2
          (ricciDeTurckTopOrderBilinearPairingCoefficient (I := I) (M := M) g T U hdelta hdeltaZ
            qA qB q epsilon s) P).toFun x) =
      tensorInnerPointwise (I := I) (M := M) g 0 4 x
        ((ricciDeTurckTopOrderBilinearPairingAdjoint (I := I) (M := M) g T P V hdelta hdeltaZ
          qA qB q epsilon s).toFun x)
        ((iteratedCovGrad (I := I) g 0 2 2 U).toFun x) := by
  have hsub_left : ∀ (r t : ℕ) (A B C : TensorRSModel r t Real E),
      tensorInnerPointwise (I := I) (M := M) g r t x (A - B) C =
        tensorInnerPointwise (I := I) (M := M) g r t x A C -
          tensorInnerPointwise (I := I) (M := M) g r t x B C := by
    intro r t A B C
    rw [sub_eq_add_neg, tensorInnerPointwise_add_left,
      ← neg_one_smul Real B, tensorInnerPointwise_smul_left]
    ring
  have hsub_right : ∀ (r t : ℕ) (A B C : TensorRSModel r t Real E),
      tensorInnerPointwise (I := I) (M := M) g r t x A (B - C) =
        tensorInnerPointwise (I := I) (M := M) g r t x A B -
          tensorInnerPointwise (I := I) (M := M) g r t x A C := by
    intro r t A B C
    rw [sub_eq_add_neg, tensorInnerPointwise_add_right,
      ← neg_one_smul Real C, tensorInnerPointwise_smul_right]
    ring
  rw [ricciDeTurckTopOrderBilinearPairingCoefficient, ricciDeTurckTopOrderPairingCoefficientForJet, ricciDeTurckTopOrderBilinearPairingAdjoint]
  rw [Fin.sum_univ_three, Fin.sum_univ_three]
  simp only [riemannTopOrderPairingCoefficient,
    operatorFieldApplication_add_left, operatorFieldApplication_sub_left, operatorFieldApplication_smul_left,
    SmoothCcTensor.toFun_add, SmoothCcTensor.toFun_sub,
    SmoothCcTensor.toFun_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    tensorInnerPointwise_add_left, tensorInnerPointwise_add_right,
    tensorInnerPointwise_smul_left, tensorInnerPointwise_smul_right]
  simp_rw [hsub_left, hsub_right]
  simp_rw [tensorInnerPointwise_add_left, tensorInnerPointwise_add_right]
  simp_rw [topOrderBilinearPairing_pointwise (I := I) (M := M) g]

omit [BoundarylessManifold I M] in
theorem ricciDeTurckTopOrderBilinearPairing_inner
    (g : SmoothRiemannianMetric I M) (T P U V : SmoothCcTensor g 0 2)
    {delta : Real}
    (hdelta : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) delta)
    (hdeltaZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) delta)
    (qA qB : Fin 4 → Equiv.Perm (Fin 4))
    (q : Fin 3 → Equiv.Perm (Fin 4)) (epsilon : Fin 3 → Real)
    (s : Real) :
    Inner.inner Real V
        (operatorFieldApply (I := I) (M := M) g 2 2
          (ricciDeTurckTopOrderBilinearPairingCoefficient (I := I) (M := M) g T U hdelta hdeltaZ
            qA qB q epsilon s) P) =
      Inner.inner Real
        (ricciDeTurckTopOrderBilinearPairingAdjoint (I := I) (M := M) g T P V hdelta hdeltaZ
          qA qB q epsilon s)
        (iteratedCovGrad (I := I) g 0 2 2 U) := by
  rw [ricciDeTurckTopOrderBilinearPairingCoefficient, ricciDeTurckTopOrderPairingCoefficientForJet, ricciDeTurckTopOrderBilinearPairingAdjoint]
  rw [Fin.sum_univ_three, Fin.sum_univ_three]
  simp only [riemannTopOrderPairingCoefficient,
    operatorFieldApplication_add_left, operatorFieldApplication_sub_left, operatorFieldApplication_smul_left,
    inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right]
  simp_rw [topOrderBilinearPairing_inner (I := I) (M := M) g]

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
