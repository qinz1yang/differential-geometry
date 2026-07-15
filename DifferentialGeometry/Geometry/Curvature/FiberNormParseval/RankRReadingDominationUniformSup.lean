import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.CovGradBundleEquivFiberNormFrameSum
import DifferentialGeometry.Geometry.Curvature.FiberNormParseval.RiemannianFiberNormSqRiemannOpHigherRankParseval
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqTensorInnerBridge
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.TensorCurvatureUnitEvalBridge
import DifferentialGeometry.Geometry.Connection.TensorNabla.TensorSlotwiseCurvatureRS

/-!
# Contravariant-valence-`r` slot-`0` reading domination and uniform curvature sup

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` this file lifts to a fixed
but generic *contravariant* valence `r` two facts that the existing library carries only at
contravariant rank `0`, both consumed by the order-`0` layer of the frame-free pure-Riemann
differentiated curvature tower at valence `r` (`RankRPureRCurvatureTower`):

* **The slot-`0` reading domination**
  `riemannianFiberNormSq_covGradBundleEquiv_symm_reading_le_rs`: the slot-`0` reading
  `(covGradBundleEquiv r s x).symm T (B i x)` of an `(r, s + 1)`-tensor `T` along a `g_x`-orthonormal
  frame direction `B i x` — an `(r, s)`-tensor — is fibre-dominated by the full `(r, s + 1)` fibre
  norm of `T`.  At contravariant rank `0` this is
  `riemannianFiberNormSq_covGradBundleEquiv_symm_reading_le`
  (`CovGradBundleEquivFiberNormFrameSum`), which routes through the slot-`0` curry chain
  (`slot0Curry`, hard-locked to contravariant `0`); the valence-`r` version below is proved instead
  by the **rank-generic component Parseval** (`riemannianFiberNormSq_eq_tensorInnerPointwise` +
  `tensorInnerPointwise_eq_sum_componentS_mul`) and the rank-generic slot-`0` evaluation bridge
  `covGradBundleEquiv_symm_apply_eval`, never touching the contravariant-`0`-only slot-`0` curry.

* **The uniform-over-`M` proportional curvature-operator fibre bound**
  `exists_uniform_riemannianFiberNormSq_riemannOp_tensorCovRS_proportional`: a single nonnegative
  constant `C`, independent of the base point, with
  `rfns(R_x(v, w) T) ≤ C · g(v, v) · g(w, w) · rfns(T)` at every `x` and every `(v, w, T)` at
  valence `(r, s)`.  At contravariant rank `0` this is
  `exists_continuous_riemannianFiberNormSq_riemannOp_tensorCov_proportional` (uniformised over the
  compact `M`); at valence `r` it is built here from the per-point bound
  `exists_Cx_riemannianFiberNormSq_riemannOp_tensorCovS_le_rs` and the **uniform dual-frame
  curvature energy** `exists_uniform_riemannOp_tensorCovRS_dualFrameEnergy_const`, whose single
  dual-frame term is dominated, through the rank-generic slot-wise curvature formula
  `riemannSec_tensorCov_apply_eval` (covariant `(0, s)` slots and contravariant `(0, r)` slots), by
  the valence-free Levi-Civita base-curvature bound `exists_uniform_riemannOp_LeviCivita_gNorm_bound`
  (`Kbase`) — exactly the valence-`r` mirror of the contravariant-`0` dual-frame energy constant
  `exists_uniform_riemannOp_tensorCovS_dualFrameEnergy_const`.

## Convention

All fibre norms are the intrinsic Riemannian fibre norm `riemannianFiberNormSq` (`rfns`).
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set FiberBundle NormedSpace Filter CovariantDerivative
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open Tensor0SBundle Tensor0SNabla

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-! ## The valence-`r` slot-`0` reading domination -/

/-- **The slot-`0` reading frame component equals a slot-shifted full-tensor frame component.** For a
`g_x`-orthonormal frame `e`, the `(K, J)` frame component of the slot-`0` reading
`(covGradBundleEquiv r s x).symm T (e a)` (an `(r, s)`-tensor) equals the `(K, Fin.cons a J)` frame
component of the full `(r, s + 1)`-tensor `T`: through the rank-generic evaluation bridge
`covGradBundleEquiv_symm_apply_eval`, reading `T` at the slot-`0` direction `e a` prepends `a` to the
covariant multi-index. -/
private lemma reading_fiberNormSqComponent_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (T : TensorRSSpace r (s + 1) I x)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (K : Fin r → Fin n) (J : Fin s → Fin n) (a : Fin n) :
    fiberNormSqComponent (I := I) (M := M) g x r s
        ((covGradBundleEquiv (I := I) (M := M) r s x).symm T (e a)) n e K J =
      fiberNormSqComponent (I := I) (M := M) g x r (s + 1) T n e K (Fin.cons a J) := by
  unfold fiberNormSqComponent
  set ωK : Tensor0SSpace r I x :=
    (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin r) ℝ).compContinuousLinearMap
      (fun k => g.inner x (e (K k))) with hωK
  rw [show (((covGradBundleEquiv (I := I) (M := M) r s x).symm T (e a)) ωK
        (fun k => e (J k)) : ℝ) =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
          ((covGradBundleEquiv (I := I) (M := M) r s x).symm T) (e a)) ωK)
        (fun k => e (J k)) from rfl]
  rw [covGradBundleEquiv_symm_apply_eval (I := I) (M := M) r s x T (e a) ωK (fun k => e (J k))]
  congr 1
  exact (Fin.comp_cons e a J).symm

/-- **The intrinsic `(r, s)` fibre norm is the frame component square sum in any `g_x`-orthonormal
frame.** For any `g_x`-orthonormal frame `e` (packaged as a `Module.Basis bse`,
`n = Module.finrank ℝ E`), the intrinsic Riemannian fibre norm squared of an `(r, s)`-tensor `S` is
the double-multi-index sum of squared frame components.  This is the rank-`(r, s)` lift of
`rfns_eq_sum_fiberNormSqSummand_of_orthoFrame` (contravariant `0` only), obtained from the bilinear
fibre-inner frame bridge `tensorInnerPointwise_eq_sum_componentS_mul` (diagonal) through
`riemannianFiberNormSq_eq_tensorInnerPointwise`. -/
private lemma rfns_rs_eq_sum_fiberNormSqComponent_sq_of_basis
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) (S : TensorRSSpace r s I x)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (bse : Module.Basis (Fin n) ℝ (TangentSpace I x))
    (hn : n = Module.finrank ℝ E) (hbse : ∀ i : Fin n, bse i = e i)
    (horth : ∀ a b : Fin n, g.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0) :
    riemannianFiberNormSq (I := I) (M := M) g r s x S =
      ∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
        (fiberNormSqComponent (I := I) (M := M) g x r s S n e K J) ^ 2 := by
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x S]
  rw [tensorInnerPointwise_eq_sum_componentS_mul (I := I) (M := M) g r s x e bse hn hbse horth S S]
  refine Finset.sum_congr rfl (fun K _ => Finset.sum_congr rfl (fun J _ => ?_))
  rw [pow_two]

/-- **The slot-`0` reading of an `(r, s + 1)`-tensor along a `g_x`-orthonormal frame direction is
fibre-dominated by the whole (valence `r`).** For a `g_x`-orthonormal frame `B` (δ-form Gram, so each
`B i x` a unit direction), the slot-`0` reading `(covGradBundleEquiv r s x).symm T (B i x)` — an
`(r, s)`-tensor — has intrinsic fibre norm at most the full `(r, s + 1)` fibre norm of `T`.  This is
the verbatim contravariant-valence-`r` mirror of the contravariant-`0`
`riemannianFiberNormSq_covGradBundleEquiv_symm_reading_le`; the proof Parseval-expands both fibre
norms in the frame `eC i := B i x` (`rfns_rs_eq_sum_fiberNormSqComponent_sq_of_basis`), rewrites each
reading component as the `Fin.cons i`-shifted full-tensor component (`reading_fiberNormSqComponent_eq`),
and dominates the shifted-index sum by the full multi-index sum (the map `J ↦ Fin.cons i J` is
injective). -/
theorem riemannianFiberNormSq_covGradBundleEquiv_symm_reading_le_rs
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (T : TensorRSSpace r (s + 1) I x)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hBorth : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner x (B i x) (B j x) = if i = j then (1 : ℝ) else 0)
    (i : Fin (Module.finrank ℝ E)) :
    riemannianFiberNormSq (I := I) (M := M) g r s x
        ((covGradBundleEquiv (I := I) (M := M) r s x).symm T (B i x)) ≤
      riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x T := by
  classical
  set eC : Fin (Module.finrank ℝ E) → TangentSpace I x := fun j => B j x with heC_def
  have horthC : ∀ a b : Fin (Module.finrank ℝ E),
      g.inner x (eC a) (eC b) = if a = b then (1 : ℝ) else 0 := fun a b => hBorth a b
  haveI : Nonempty (Fin (Module.finrank ℝ E)) :=
    ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E))⟩⟩

  have he_li : LinearIndependent ℝ eC := by
    rw [linearIndependent_iff']
    intro fs c hsum k hk_mem
    have h_zero : g.inner x (eC k) (∑ j ∈ fs, c j • eC j) = 0 := by rw [hsum]; simp
    rw [map_sum] at h_zero
    have h_pull : ∀ j ∈ fs,
        g.inner x (eC k) (c j • eC j) = c j * (if k = j then (1 : ℝ) else 0) := by
      intro j _
      rw [map_smul, horthC k j, smul_eq_mul]
    rw [Finset.sum_congr rfl h_pull] at h_zero
    rw [Finset.sum_eq_single k (fun j _ hj => by rw [if_neg (Ne.symm hj), mul_zero])
      (fun hk => absurd hk_mem hk)] at h_zero
    rwa [if_pos rfl, mul_one] at h_zero
  have hcard : Fintype.card (Fin (Module.finrank ℝ E)) = Module.finrank ℝ (TangentSpace I x) := by
    rw [Fintype.card_fin]; rfl
  set bse : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
    basisOfLinearIndependentOfCardEqFinrank he_li hcard with hbse_def
  have hbse : ∀ i : Fin (Module.finrank ℝ E), bse i = eC i := fun i => by
    rw [hbse_def, coe_basisOfLinearIndependentOfCardEqFinrank]
  have hnd : Module.finrank ℝ E = Module.finrank ℝ E := rfl
  rw [rfns_rs_eq_sum_fiberNormSqComponent_sq_of_basis (I := I) (M := M) g r s x _ eC bse hnd hbse
    horthC]
  rw [rfns_rs_eq_sum_fiberNormSqComponent_sq_of_basis (I := I) (M := M) g r (s + 1) x T eC bse hnd
    hbse horthC]
  have hBix : B i x = eC i := rfl
  rw [hBix]

  have hcomp : ∀ K : Fin r → Fin (Module.finrank ℝ E), ∀ J : Fin s → Fin (Module.finrank ℝ E),
      (fiberNormSqComponent (I := I) (M := M) g x r s
          ((covGradBundleEquiv (I := I) (M := M) r s x).symm T (eC i))
          (Module.finrank ℝ E) eC K J) ^ 2 =
        (fiberNormSqComponent (I := I) (M := M) g x r (s + 1) T
          (Module.finrank ℝ E) eC K (Fin.cons i J)) ^ 2 := by
    intro K J
    rw [reading_fiberNormSqComponent_eq (I := I) (M := M) g r s x T eC K J i]
  rw [Finset.sum_congr rfl (fun K _ => Finset.sum_congr rfl (fun J _ => hcomp K J))]

  refine Finset.sum_le_sum (fun K _ => ?_)
  let consi : (Fin s → Fin (Module.finrank ℝ E)) → (Fin (s + 1) → Fin (Module.finrank ℝ E)) :=
    fun J => Fin.cons i J
  let fJ : (Fin (s + 1) → Fin (Module.finrank ℝ E)) → ℝ :=
    fun J' => (fiberNormSqComponent (I := I) (M := M) g x r (s + 1) T
      (Module.finrank ℝ E) eC K J') ^ 2
  have hinj : Function.Injective consi := Fin.cons_right_injective (α := fun _ => _) i
  have hsumeq : (∑ J : Fin s → Fin (Module.finrank ℝ E),
        (fiberNormSqComponent (I := I) (M := M) g x r (s + 1) T (Module.finrank ℝ E)
          eC K (Fin.cons i J)) ^ 2) =
      ∑ J' ∈ (Finset.univ.image consi), fJ J' :=
    (Finset.sum_image (s := (Finset.univ : Finset (Fin s → Fin (Module.finrank ℝ E))))
      (g := consi) (f := fJ) (fun J1 _ J2 _ hJ => hinj hJ)).symm
  rw [hsumeq]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun J' _ _ => sq_nonneg _)

end Connection
end Integral
end DifferentialGeometry
