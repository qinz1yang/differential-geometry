import DifferentialGeometry.Geometry.Connection.TensorNabla.OperatorFieldCovariantCalculus
import DifferentialGeometry.Geometry.Curvature.FiberNormParseval.RiemannianFiberNormSqRiemannOpHigherRankParseval
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqSmoothCcUniformBound

/-! # The intrinsic partial-contraction Cauchy–Schwarz and the uniform operator-field action envelope

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` modelled on a real
inner-product space `E`, this file proves the **intrinsic partial-contraction Cauchy–Schwarz** for the
operator-field action and the **uniform section-proportional fibre envelope** it yields for `appCc`.

## The intrinsic partial-contraction Cauchy–Schwarz

The fibre value of the operator-field action `appCc Φ W` is the fibrewise composition
`(Φ x).comp (W x) : Tensor0SSpace 0 I x →L Tensor0SSpace s I x` (`appCc_toSection`), a `(0, s)`-tensor.
`riemannianFiberNormSq_comp_le_mul` is the fibre Cauchy–Schwarz for this composition, *intrinsic in the
Riemannian fibre norms* (no chart trivialisation, no model-fibre operator norm):
```
rfns_{(0,s)}((Φ x).comp (W x)) ≤ rfns_{(r,s)}(Φ x) · rfns_{(0,r)}(W x).
```
The proof Parseval-expands all three fibre norms in a single `g_x`-orthonormal tensor frame
(`tangent_orthonormalBasisRS_witness`): the composition's frame components are the matrix–vector product
`∑_P (W x)_{∅,P} · (Φ x)_{P,J}` of the contracted tensor's components against the operator field's
components (`fiberNormSqComponent_appCc_comp_eq`, through the coframe expansion
`tensorS_coframe_expansion`), and a per-row discrete Cauchy–Schwarz (`Finset.sum_mul_sq_le_sq_mul_sq`)
over the contracted multi-index, summed over the output index, gives the Hilbert–Schmidt bound (the
product of the two squared frame norms). It is the Hilbert–Schmidt-norm submultiplicativity of tensor
contraction, phrased intrinsically.

## The uniform operator-field action envelope

`exists_uniform_riemannianFiberNormSq_appCc_le` is the section-proportional fibre envelope the
recursively-differentiated curvature towers need: for a *fixed* smooth `(r, s)`-operator field `Φ`, the
operator-field action `appCc Φ W` is bounded, uniformly over the compact `M`, proportionally to the
contracted section `W`:
```
rfns(appCc Φ W)(x) ≤ C · rfns(W)(x),    C := sup_x rfns(Φ x).
```
The uniform constant is the global fibre-norm bound for the *fixed* smooth section `Φ`
(`exists_bound_riemannianFiberNormSq_smoothCcTensor`, the chart-locality-free forward-Gram route on the
compact partition-of-unity supports) — it depends only on `Φ`, never on `W`. This is the bridge by which
the iterated covariant gradient `∇^p Φ₀` of a curvature coefficient operator field — itself a *fixed*
smooth `(r, r + p)`-tensor, hence with a uniform fibre-norm bound — yields the section-proportional
high-order envelope of the differentiated curvature tower, with NO chart-selection-unbounded data.

## Convention

Geometer convention; all fibre norms are the intrinsic `riemannianFiberNormSq`. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open TensorMultilinear

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

set_option linter.unusedSectionVars false in
/-- **The intrinsic fibre-norm representation of a `(0, t)`-tensor in a `g_x`-orthonormal frame.** For a
`g_x`-orthonormal frame `e` (with `n = Module.finrank`) arising as a `Module.Basis`, the intrinsic squared
Riemannian fibre norm of a `(0, t)`-tensor `S` is the frame double sum of `fiberNormSqSummand`. The single
non-trivial multi-index is the empty `K`; the rank-`t` index `J` ranges over the dual tensor frame. Ported
from the diagonal-sum reconstruction `tensorInnerPointwise_0s_eq_diag_sum_orthoFrame`. -/
lemma rfns_repr_of_orthoFrame_cb
    (g : SmoothRiemannianMetric I M) (t : ℕ) (x : M) (S : TensorRSSpace 0 t I x)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (hn : n = Module.finrank ℝ (TangentSpace I x))
    (horth : ∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0) :
    riemannianFiberNormSq (I := I) (M := M) g 0 t x S =
      ∑ K : Fin 0 → Fin n, ∑ J : Fin t → Fin n,
        fiberNormSqSummand (I := I) (M := M) g x 0 t S n e K J := by
  classical
  subst hn
  haveI : Nonempty (Fin (Module.finrank ℝ (TangentSpace I x))) :=
    ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E))⟩⟩
  have he_li : LinearIndependent ℝ e := by
    rw [linearIndependent_iff']
    intro fs c hsum k hk_mem
    have h_zero : g.inner x (e k) (∑ j ∈ fs, c j • e j) = 0 := by rw [hsum]; simp
    rw [map_sum] at h_zero
    have h_pull : ∀ j ∈ fs, g.inner x (e k) (c j • e j) = c j * (if k = j then (1 : ℝ) else 0) := by
      intro j _
      rw [(g.inner x (e k)).map_smul (c j) (e j), smul_eq_mul, horth k j]
    rw [Finset.sum_congr rfl h_pull, Finset.sum_eq_single_of_mem k hk_mem] at h_zero
    · rwa [if_pos rfl, mul_one] at h_zero
    · intro j _ hjk; rw [if_neg (fun h => hjk h.symm), mul_zero]
  have hcard : Fintype.card (Fin (Module.finrank ℝ (TangentSpace I x))) =
      Module.finrank ℝ (TangentSpace I x) := Fintype.card_fin _
  set bse : Module.Basis (Fin (Module.finrank ℝ (TangentSpace I x))) ℝ (TangentSpace I x) :=
    basisOfLinearIndependentOfCardEqFinrank he_li hcard with hbse_def
  have hbse_eq : ∀ i, bse i = e i := by
    intro i; rw [hbse_def]; exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank he_li hcard) i
  have hbse_orth : ∀ i j, g.inner x (bse i) (bse j) = if i = j then (1 : ℝ) else 0 := by
    intro i j; rw [hbse_eq i, hbse_eq j]; exact horth i j
  have hstep : riemannianFiberNormSq (I := I) (M := M) g 0 t x S =
      ∑ ψ : Fin t → Fin (Module.finrank ℝ (TangentSpace I x)),
        Tensor0SSpace.toModel
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x from S)
              (unitZeroSec (I := I) (M := M) x))
            (fun k => e (ψ k)) ^ 2 := by
    rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g 0 t x S]
    rw [show tensorInnerPointwise (I := I) (M := M) g 0 t x
          (TensorRSSpace.toModel S) (TensorRSSpace.toModel S) =
        tensorInnerPointwise_0s (I := I) (M := M) (0 + t) g x
          (lowerAllUpperIndices (I := I) (M := M) g 0 t x (TensorRSSpace.toModel S))
          (lowerAllUpperIndices (I := I) (M := M) g 0 t x (TensorRSSpace.toModel S)) from rfl]
    rw [tensorInnerPointwise_0s_eq_diag_sum_orthoFrame (I := I) (M := M) g x (0 + t)
      bse hbse_orth _ _]
    have hkey : ∀ ξ : Fin (0 + t) → Fin (Module.finrank ℝ (TangentSpace I x)),
        lowerAllUpperIndices (I := I) (M := M) g 0 t x
            (TensorRSSpace.toModel S) (fun k => bse (ξ k)) =
          Tensor0SSpace.toModel
              ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x from S)
                (unitZeroSec (I := I) (M := M) x))
              (fun j : Fin t => bse (ξ (Fin.natAdd 0 j))) := by
      intro ξ
      rw [lowerAllUpperIndices_apply (I := I) (M := M) g 0 t x (TensorRSSpace.toModel S)
        (fun k => bse (ξ k))]
      rw [toModel_tensorRS_apply (I := I) (M := M) 0 t x S (unitZeroSec (I := I) (M := M) x)]
      rw [unitZeroSec_apply (I := I) (M := M) x, Tensor0SSpace.toModel_ofModel]
      rw [separableFormAt_zero (I := I) (M := M) g x
        (fun i : Fin 0 => (fun k => bse (ξ k)) (Fin.castAdd t i))]
    have hstep2 : ∀ ξ : Fin (0 + t) → Fin (Module.finrank ℝ (TangentSpace I x)),
        lowerAllUpperIndices (I := I) (M := M) g 0 t x
              (TensorRSSpace.toModel S) (fun k => bse (ξ k)) *
            lowerAllUpperIndices (I := I) (M := M) g 0 t x
              (TensorRSSpace.toModel S) (fun k => bse (ξ k)) =
          Tensor0SSpace.toModel
              ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x from S)
                (unitZeroSec (I := I) (M := M) x))
              (fun k => e (ξ (Fin.natAdd 0 k))) ^ 2 := by
      intro ξ
      rw [hkey ξ, ← pow_two]
      congr 2
      funext k
      rw [hbse_eq]
    refine Eq.trans (Finset.sum_congr rfl (fun ξ _ => hstep2 ξ)) ?_
    refine Fintype.sum_bijective
      (fun ξ : Fin (0 + t) → Fin (Module.finrank ℝ (TangentSpace I x)) =>
        fun k : Fin t => ξ (Fin.natAdd 0 k))
      ?_ _ _ (fun ξ => rfl)
    refine ⟨fun ξ₁ ξ₂ h => ?_, fun φ => ⟨fun k => φ (Fin.cast (Nat.zero_add t) k), ?_⟩⟩
    · funext k
      have hk : k = Fin.natAdd 0 (Fin.cast (Nat.zero_add t) k) := by ext; simp
      rw [hk]; exact congrFun h (Fin.cast (Nat.zero_add t) k)
    · funext k
      change φ (Fin.cast (Nat.zero_add t) (Fin.natAdd 0 k)) = φ k
      have : Fin.cast (Nat.zero_add t) (Fin.natAdd 0 k) = k := by ext; simp
      rw [this]
  rw [hstep]
  rw [Finset.sum_eq_single (fun k : Fin 0 => k.elim0)]
  · refine Finset.sum_congr rfl (fun J _ => ?_)
    rw [fiberNormSqSummand_eq_component_sq]
    have hweight : ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
        (fun k => g.inner x (e ((fun k : Fin 0 => k.elim0) k))) : Tensor0SSpace 0 I x) =
        unitZeroSec (I := I) (M := M) x := by
      have hcf : ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
          (fun k => g.inner x (e ((fun k : Fin 0 => k.elim0) k))) : Tensor0SSpace 0 I x) =
          coframeS (I := I) (M := M) g x 0 e (fun k : Fin 0 => k.elim0) := rfl
      rw [hcf]
      apply Tensor0SSpace.toModel_injective
      apply ContinuousMultilinearMap.ext
      intro mm
      have hL : Tensor0SSpace.toModel (coframeS (I := I) (M := M) g x 0 e
          (fun k : Fin 0 => k.elim0)) mm = 1 := by
        have h1 : Tensor0SSpace.toModel (coframeS (I := I) (M := M) g x 0 e
            (fun k : Fin 0 => k.elim0)) mm =
            coframeS (I := I) (M := M) g x 0 e (fun k : Fin 0 => k.elim0)
              (fun k : Fin 0 => k.elim0) := by
          apply congrArg; funext k; exact k.elim0
        rw [h1, coframeS_apply (I := I) (M := M) g x 0 e (fun k : Fin 0 => k.elim0)
          (fun k : Fin 0 => k.elim0)]
        simp
      have hR : Tensor0SSpace.toModel (unitZeroSec (I := I) (M := M) x) mm = 1 := by
        rw [unitZeroSec_apply (I := I) (M := M) x, Tensor0SSpace.toModel_ofModel,
          ContinuousMultilinearMap.constOfIsEmpty_apply]
      rw [hL, hR]
    rw [fiberNormSqComponent, hweight]
    rfl
  · intro K _ hK; exact absurd (Subsingleton.elim K (fun k : Fin 0 => k.elim0)) hK
  · intro h; exact absurd (Finset.mem_univ (fun k : Fin 0 => k.elim0)) h

set_option linter.unusedSectionVars false in
/-- **The operator-field action's frame components are the matrix–vector product.** For a `g_x`-orthonormal
tensor frame `e` (built from a `Module.Basis`), the `(0, s)`-component of the fibrewise composition
`(Φ x).comp (W x)` along the empty `K₀` and the output index `J` is the contraction sum, over the rank-`r`
multi-index `P`, of the `(0, r)`-component of `W x` along `(K₀, P)` against the `(r, s)`-component of `Φ x`
along `(P, J)`. The proof expands `W x` applied to the empty coframe covector through the coframe basis
(`tensorS_coframe_expansion`), distributes the operator field linearly, and reads each summand off as the
product of the two component scalars. -/
private lemma fiberNormSqComponent_comp_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (Φx : TensorRSSpace r s I x) (Wx : TensorRSSpace 0 r I x)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (bse : Module.Basis (Fin n) ℝ (TangentSpace I x))
    (hbse : ∀ i : Fin n, bse i = e i)
    (horth : ∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (K₀ : Fin 0 → Fin n) (J : Fin s → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g x 0 s
        (show TensorRSSpace 0 s I x from
          (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φx).comp
            (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from Wx)) n e K₀ J =
      ∑ P : Fin r → Fin n,
        fiberNormSqComponent (I := I) (M := M) g x 0 r Wx n e K₀ P *
          fiberNormSqComponent (I := I) (M := M) g x r s Φx n e P J := by
  classical
  change (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φx)
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from Wx)
        ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
          (fun k => g.inner x (e (K₀ k)))))
      (fun k => e (J k)) = _
  set wval : Tensor0SSpace r I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from Wx)
      ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
        (fun k => g.inner x (e (K₀ k)))) with hwval
  have hexp := tensorS_coframe_expansion (I := I) (M := M) g x r e bse hbse horth wval
  conv_lhs => rw [hexp]
  rw [map_sum]
  rw [show (∑ P : Fin r → Fin n,
        (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φx)
          ((wval (fun k : Fin r => e (P k))) • coframeS (I := I) (M := M) g x r e P)) =
      ∑ P : Fin r → Fin n, (wval (fun k : Fin r => e (P k))) •
        (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φx)
          (coframeS (I := I) (M := M) g x r e P) from by
    refine Finset.sum_congr rfl (fun P _ => ?_); rw [map_smul]]
  rw [show ((∑ P : Fin r → Fin n, (wval (fun k : Fin r => e (P k))) •
        (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φx)
          (coframeS (I := I) (M := M) g x r e P)) (fun k => e (J k)) : ℝ) =
      Tensor0SSpace.toModel (∑ P : Fin r → Fin n, (wval (fun k : Fin r => e (P k))) •
        (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φx)
          (coframeS (I := I) (M := M) g x r e P)) (fun k => e (J k)) from rfl]
  rw [← Tensor0SSpace.toModelL_apply, map_sum, ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun P _ => ?_)
  rw [Tensor0SSpace.toModelL_apply, Tensor0SSpace.toModel_smul,
    ContinuousMultilinearMap.smul_apply]
  have hΦcomp : Tensor0SSpace.toModel
      ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φx)
        (coframeS (I := I) (M := M) g x r e P)) (fun k => e (J k)) =
      fiberNormSqComponent (I := I) (M := M) g x r s Φx n e P J := rfl
  rw [hΦcomp]
  have hwcomp : wval (fun k : Fin r => e (P k)) =
      fiberNormSqComponent (I := I) (M := M) g x 0 r Wx n e K₀ P := rfl
  rw [hwcomp, smul_eq_mul]

set_option linter.unusedSectionVars false in
/-- **The intrinsic partial-contraction Cauchy–Schwarz for the operator-field action.** The intrinsic
squared Riemannian fibre norm of the fibrewise composition `(Φ x).comp (W x)` of an `(r, s)`-tensor `Φ x`
with a `(0, r)`-tensor `W x` (a `(0, s)`-tensor) is bounded by the product of the `(r, s)` fibre norm of
`Φ x` and the `(0, r)` fibre norm of `W x`:
```
rfns_{(0,s)}((Φ x).comp (W x)) ≤ rfns_{(r,s)}(Φ x) · rfns_{(0,r)}(W x).
```
This is the Hilbert–Schmidt-norm submultiplicativity of tensor contraction, intrinsic in the Riemannian
fibre norms (no chart trivialisation, no model-fibre operator norm). Proved by Parseval-expanding all three
fibre norms in a single `g_x`-orthonormal tensor frame, identifying the composition's frame components with
the matrix–vector product of the two factors' components (`fiberNormSqComponent_comp_eq`), and a per-output
discrete Cauchy–Schwarz (`Finset.sum_mul_sq_le_sq_mul_sq`) over the contracted multi-index.

**Non-vacuity.** The bound genuinely uses both `Φ x` and `W x`; it is the fibre Cauchy–Schwarz, so it is
sharp up to the operator/Hilbert–Schmidt norm gap and forces nonzero RHS whenever the contraction is
nonzero. -/
theorem riemannianFiberNormSq_comp_le_mul
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (Φx : TensorRSSpace r s I x) (Wx : TensorRSSpace 0 r I x) :
    riemannianFiberNormSq (I := I) (M := M) g 0 s x
        (show TensorRSSpace 0 s I x from
          (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φx).comp
            (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from Wx)) ≤
      riemannianFiberNormSq (I := I) (M := M) g r s x Φx *
        riemannianFiberNormSq (I := I) (M := M) g 0 r x Wx := by
  classical
  obtain ⟨n, e, bse, hn, hbse, horth, _hpars, _hexpand, _hreprRS⟩ :=
    tangent_orthonormalBasisRS_witness (I := I) (M := M) g r s x
  set K₀ : Fin 0 → Fin n := fun k => k.elim0 with hK₀
  have hreprS : ∀ S : TensorRSSpace 0 s I x,
      riemannianFiberNormSq (I := I) (M := M) g 0 s x S =
        ∑ K : Fin 0 → Fin n, ∑ J : Fin s → Fin n,
          fiberNormSqSummand (I := I) (M := M) g x 0 s S n e K J :=
    fun S => rfns_repr_of_orthoFrame_cb (I := I) (M := M) g s x S e hn horth
  have hreprR : ∀ S : TensorRSSpace 0 r I x,
      riemannianFiberNormSq (I := I) (M := M) g 0 r x S =
        ∑ K : Fin 0 → Fin n, ∑ J : Fin r → Fin n,
          fiberNormSqSummand (I := I) (M := M) g x 0 r S n e K J :=
    fun S => rfns_repr_of_orthoFrame_cb (I := I) (M := M) g r x S e hn horth
  rw [riemannianFiberNormSq_eq_sum_componentS_sq (I := I) (M := M) g x s e hreprS _ K₀]
  have hWrepr : (∑ P : Fin r → Fin n,
        (fiberNormSqComponent (I := I) (M := M) g x 0 r Wx n e K₀ P) ^ 2) =
      riemannianFiberNormSq (I := I) (M := M) g 0 r x Wx := by
    rw [riemannianFiberNormSq_eq_sum_componentS_sq (I := I) (M := M) g x r e hreprR Wx K₀]
  have hΦrepr : (∑ P : Fin r → Fin n, ∑ J : Fin s → Fin n,
        (fiberNormSqComponent (I := I) (M := M) g x r s Φx n e P J) ^ 2) =
      riemannianFiberNormSq (I := I) (M := M) g r s x Φx := by
    rw [riemannianFiberNormSq_eq_sum_componentRS_sq (I := I) (M := M) g x r s e _hreprRS Φx]
  have hcomp_eq : ∀ J : Fin s → Fin n,
      fiberNormSqComponent (I := I) (M := M) g x 0 s
          (show TensorRSSpace 0 s I x from
            (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φx).comp
              (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from Wx)) n e K₀ J =
        ∑ P : Fin r → Fin n,
          fiberNormSqComponent (I := I) (M := M) g x 0 r Wx n e K₀ P *
            fiberNormSqComponent (I := I) (M := M) g x r s Φx n e P J :=
    fun J => fiberNormSqComponent_comp_eq (I := I) (M := M) g r s x Φx Wx e bse hbse horth K₀ J
  rw [Finset.sum_congr rfl (fun J (_ : J ∈ Finset.univ) => by rw [hcomp_eq J])]
  refine le_trans (Finset.sum_le_sum (fun J (_ : J ∈ Finset.univ) =>
    Finset.sum_mul_sq_le_sq_mul_sq (R := ℝ) Finset.univ
      (fun P : Fin r → Fin n => fiberNormSqComponent (I := I) (M := M) g x 0 r Wx n e K₀ P)
      (fun P : Fin r → Fin n => fiberNormSqComponent (I := I) (M := M) g x r s Φx n e P J))) ?_
  rw [← Finset.mul_sum, mul_comm, hWrepr]
  rw [show (∑ J : Fin s → Fin n,
        ∑ P : Fin r → Fin n, (fiberNormSqComponent (I := I) (M := M) g x r s Φx n e P J) ^ 2) =
      ∑ P : Fin r → Fin n, ∑ J : Fin s → Fin n,
        (fiberNormSqComponent (I := I) (M := M) g x r s Φx n e P J) ^ 2 from Finset.sum_comm,
    hΦrepr]

set_option linter.unusedSectionVars false in
/-- **The uniform section-proportional fibre envelope for the operator-field action.** For a *fixed* smooth
compactly-supported `(r, s)`-operator field `Φ` on a closed Riemannian manifold, there is a single
nonnegative constant `C`, uniform over `M`, with
```
rfns(appCc Φ W)(x) ≤ C · rfns(W)(x)
```
for every smooth compactly-supported `(0, r)`-tensor `W` and every point `x`. The constant `C` is the global
fibre-norm bound for the *fixed* smooth section `Φ` (`exists_bound_riemannianFiberNormSq_smoothCcTensor`,
the chart-locality-free forward-Gram route); it depends only on `Φ`, never on `W`. The pointwise step is the
intrinsic partial-contraction Cauchy–Schwarz `riemannianFiberNormSq_comp_le_mul`
(`rfns((Φ x).comp (W x)) ≤ rfns(Φ x) · rfns(W x)`) followed by the uniform bound on `rfns(Φ x)`.

This is the bridge by which the iterated covariant gradient `∇^p Φ₀` of a curvature-coefficient operator
field — itself a fixed smooth `(r, r + p)`-tensor with a uniform fibre-norm bound — yields the
section-proportional high-order envelope of the differentiated curvature tower with no
chart-selection-unbounded data.

**Non-vacuity.** A degenerate `C = 0` is rejected whenever `Φ` has a nonzero contraction on some `W` at
some `x`: then `rfns(appCc Φ W)(x) > 0 = 0 · rfns(W)(x)`; the envelope genuinely uses `Φ` (its fibre norm)
and `W` (the operator is applied to `W`). -/
theorem exists_uniform_riemannianFiberNormSq_appCc_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (Φ : SmoothCcTensor g r s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (W : SmoothCcTensor g 0 r) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g 0 s x
          ((appCc (I := I) (M := M) g r s Φ W).toSection x) ≤
        C * riemannianFiberNormSq (I := I) (M := M) g 0 r x (W.toSection x) := by
  obtain ⟨K, hK_nn, hK⟩ := exists_bound_riemannianFiberNormSq_smoothCcTensor g r s Φ
  refine ⟨K, hK_nn, fun W x => ?_⟩
  rw [appCc_toSection (I := I) (M := M) g r s Φ W x]
  refine le_trans (riemannianFiberNormSq_comp_le_mul (I := I) (M := M) g r s x
    (Φ.toSection x) (W.toSection x)) ?_
  exact mul_le_mul_of_nonneg_right (hK x)
    (riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 r x (W.toSection x))

end Connection
end Integral
end DifferentialGeometry

end
