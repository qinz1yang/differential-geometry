import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameCurvatureTraceSmooth
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.MetricContractionLeibnizGrid
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedDiffOpProportionalBound
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.UniformCurvatureSup
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.UniformProportionalCurvatureSup
import DifferentialGeometry.Geometry.Curvature.FiberNormParseval.Slot0SliceFiberNormDomination
import DifferentialGeometry.Geometry.Connection.TensorNabla.OperatorFieldDifferentiatedTowerNormalForm

/-!
# The frozen-frame pure-Riemann curvature endomorphism tower and its iterated-gradient grid

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` modelled on a real
inner-product space `E`, and a *fixed* smooth tangent frame `B`, this file builds the recursive
differentiated-operator tower of the **frozen-frame pure-Riemann curvature endomorphism**

```
v ↦ ∑ᵢ R(B_iˣ, v)(slot0_{B_iˣ} W),   slot0_{B_iˣ} W := (tensor0S_curry r x (W x)) (B_iˣ),
```

uncurried through `covGradBundleEquiv 0 r`, packaged as a `DiffBilinOp` (the abstract differentiated
bilinear-contraction engine of `MetricContractionLeibnizGrid`), and uses the engine's *proved*
binomial covariant-Leibniz grid to bound the iterated covariant gradients of the frozen-frame
pure-Riemann section `fixedFramePureRSection` (`MovingFrameCurvatureTraceSmooth`).

## The endomorphism is a rank-generic fibrewise-linear operator

The order-`0` operator `pureRFrozenEndo g r B : SmoothCcTensor g 0 r → SmoothCcTensor g 0 r` reads the
leftmost (slot-`0`) component of its rank-`r` input `W` along each frame vector `B_iˣ`
(`tensor0SPartialEval`), contracts it through the curvature operator `R(B_iˣ, ·)`, and uncurries the
resulting curvature-direction continuous-linear map back into a rank-`r` tensor through
`covGradBundleEquiv 0 (r-1)`. It is defined for every rank `r ≥ 1`; at rank `0` (no slot to read) it
is the zero operator, which keeps the `DiffBilinOp` totality without affecting the grid (the recursion
only ever increases the rank, so rank `0` is never reached from the base rank `s + 1`). It is a fixed
(`B`-, `g`-, `R`-built) smooth fibrewise-`ℝ`-linear operator, exactly the shape `DiffBilinOp`
abstracts.

The differentiated tower `op (p + 1) r W := ∇(op p r W) − (rank-cast) op p (r + 1) (∇W)` is the exact
covariant-Leibniz remainder, so the structure field `covGrad_op` holds by `sub_add_cancel` — *proved*,
not posited. The bridge `op 0 (s + 1) (∇S) = fixedFramePureRSection g s S B` is definitional
bookkeeping through the slot-`0` reading of the differentiated section `∇S = covGrad g 0 s S`
(`covGrad_toSection_apply_eval`).

## The sound, FRAME-FREE route (the frozen high-order tower is excised as FALSE)

The differentiated *frozen*-frame tower at order `p ≥ 1` is **unsound**: its diagonal carries the
quadratic frame jet `(∇B)²` of the centre frame `B = smoothOrthoFrame g x₀`, which is
chart-selection-unbounded on a multi-chart manifold (no atlas-finiteness hypothesis). The former
`exists_proportional_pureRFrozenFrameDiffOp(_highOrder)(_centreDiag)` and the frozen grid bound
`exists_fixedFramePureRSection_iteratedCovGrad_grid_bound` are therefore **deleted**. Only the SOUND
order-`0` frozen layer `exists_proportional_pureRFrozenFrameDiffOp_orderZero` (value-only; holds for any
frame orthonormal at the evaluation point) is kept, and reused below.

The replacement is the **frame-free pure-Riemann trace tower** `pureRGenuineDiffOp`, whose order-`0`
base is the *moving*-frame endomorphism (frame chosen at the evaluation point, orthonormal at its own
centre) — its fibre *value* is a genuine `g`-metric trace (`pureRFrozenDirCLM_frame_independent`), hence
frame-free, built from `g` and `R` alone. The differentiated tower
`op (p + 1) r W := ∇(op p r W) − (rank-cast) op p (r + 1) (∇W)` is the exact covariant-Leibniz remainder
(`covGrad_pureRGenuineDiffOp_eq`, `sub_add_cancel`), so it differentiates only the frame-free curvature
factor — never a frame jet. The single genuinely-irreducible analytic primitive is its FRAME-FREE
per-`(p, r)` envelope `exists_proportional_pureRGenuineDiffOp` (order `0` proved from
`…_orderZero`; order `p ≥ 1` the lone posited node `exists_proportional_pureRGenuineDiffOp_highOrder`,
controlled by `‖∇^{≤ p + 1} R‖_∞`); consumers transitively depend on `sorryAx` through it.

Everything else — the moving-frame endomorphism construction and its smoothness (frame-independence
freeze), the order-`0` bridge `pureRGenuineDiffOp0_eq_GcurvSection` (the order-`0` operator on `∇S` is
the moving-centre section `GcurvSection`), the grid
`DiffBilinOp.exists_rfns_iteratedCovGrad_singleSum_le_at`, and the rank-shift `∇^q(∇S) ≅ ∇^{q + 1}S`
re-indexing — is *proved* here. The headline output `exists_GcurvSection_iteratedCovGrad_grid_bound` is
the `(p, w) = (1, 1)` grid the moving-centre curvature-jet induction (`OrderSeparatedCurvatureJet`)
consumes *directly*, with no frozen-frame locality detour.

## Convention

Geometer convention; all fibre norms are the intrinsic `riemannianFiberNormSq`. The endomorphism is
genuinely `rfns(W)`-order (it is a fixed operator applied to `W`), so its order-`0` instance on `∇S`
makes the grid genuinely `rfns(∇S) = rfns(∇^{·+1}S)`-order — lowest contracted order `1`.
-/

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
open DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- **The slot-`i` frozen-frame pure-Riemann curvature direction linear map (rank `m + 1`).** Fixing
the frame index `i` and a smooth tangent frame `B`, the linear map in the curvature direction
```
v ↦ riemannOp (tensorCov g 0 m) x (B_iˣ) v (((covGradBundleEquiv 0 m x).symm (W x)) (B_iˣ)),
```
the slot-`i` summand of the frozen-frame pure-Riemann curvature endomorphism on the rank-`(m + 1)`
tensor `W`. The contracted argument `((covGradBundleEquiv 0 m x).symm (W x)) (B_iˣ)` is the slot-`0`
reading of `W` along the frame vector `B_iˣ` — a `(0, m)`-tensor; `B_i` is contracted *twice* (as the
slot-`1` argument of `R` and as the slot-`0` reading direction). -/
private def pureRFrozenDirLMSummand
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (W : Π b : M, TensorRSSpace 0 (m + 1) I b) (x : M)
    (i : Fin (Module.finrank ℝ E)) :
    TangentSpace I x →ₗ[ℝ] TensorRSSpace 0 m I x where
  toFun v := riemannOp (tensorCov (I := I) g 0 m) x (B i x) v
    ((covGradBundleEquiv (I := I) (M := M) 0 m x).symm (W x) (B i x))
  map_add' v v' := by
    rw [map_add (riemannOp (tensorCov (I := I) g 0 m) x (B i x)) v v']
    rfl
  map_smul' c v := by
    rw [map_smul (riemannOp (tensorCov (I := I) g 0 m) x (B i x)) c v]
    rfl

private noncomputable def pureRFrozenDirCLMSummand
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (W : Π b : M, TensorRSSpace 0 (m + 1) I b) (x : M)
    (i : Fin (Module.finrank ℝ E)) :
    TangentSpace I x →L[ℝ] TensorRSSpace 0 m I x :=
  haveI : T2Space (TangentSpace I x) := inferInstanceAs (T2Space E)
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap (pureRFrozenDirLMSummand (I := I) (M := M) g m B W x i)

/-- **The frozen-frame pure-Riemann curvature direction continuous-linear map (rank `m + 1`).** The
frame sum over `i` of `pureRFrozenDirCLMSummand`: the curvature-direction-linear map
`v ↦ ∑ᵢ riemannOp (tensorCov g 0 m) x (B_iˣ) v (slot0_{B_iˣ} W)` whose slot-`0` uncurry is the
frozen-frame pure-Riemann curvature endomorphism on `W`. -/
private noncomputable def pureRFrozenDirCLM
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (W : Π b : M, TensorRSSpace 0 (m + 1) I b) (x : M) :
    TangentSpace I x →L[ℝ] TensorRSSpace 0 m I x :=
  ∑ i : Fin (Module.finrank ℝ E), pureRFrozenDirCLMSummand (I := I) (M := M) g m B W x i

/-- The defining apply formula for `pureRFrozenDirCLM`: the frame sum of curvature contractions of
the slot-`0` readings of `W`. -/
private lemma pureRFrozenDirCLM_apply
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (W : Π b : M, TensorRSSpace 0 (m + 1) I b) (x : M) (v : TangentSpace I x) :
    pureRFrozenDirCLM (I := I) (M := M) g m B W x v =
      ∑ i : Fin (Module.finrank ℝ E),
        riemannOp (tensorCov (I := I) g 0 m) x (B i x) v
          ((covGradBundleEquiv (I := I) (M := M) 0 m x).symm (W x) (B i x)) := by
  classical
  rw [pureRFrozenDirCLM, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [pureRFrozenDirCLMSummand, LinearMap.coe_toContinuousLinearMap', pureRFrozenDirLMSummand,
    LinearMap.coe_mk, AddHom.coe_mk]

/-- **The order-`0` frozen-frame pure-Riemann curvature endomorphism fibre value (rank `m + 1`).**
The slot-`0` uncurry, through `covGradBundleEquiv 0 m x`, of the frozen-frame pure-Riemann curvature
direction CLM `pureRFrozenDirCLM g m B (W.toSection) x` — the unique `(0, m + 1)`-tensor whose slot-`0`
curry along `v` is `∑ᵢ R(B_iˣ, v)(slot0_{B_iˣ} W)`. -/
private noncomputable def pureRFrozenEndoFib
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (W : SmoothCcTensor g 0 (m + 1)) (x : M) :
    TensorRSSpace 0 (m + 1) I x :=
  covGradBundleEquiv (I := I) (M := M) 0 m x
    (pureRFrozenDirCLM (I := I) (M := M) g m B (fun y : M => W.toSection y) x)

/-- **The slot-`0` reading of `W` along `B_i` is a smooth `(0, m)`-tensor section.** For a smooth
frame field `B_i` and a smooth `(0, m + 1)`-tensor section `W`, the section
`x ↦ ((covGradBundleEquiv 0 m x).symm (W.toSection x)) (B_iˣ)` is `C^∞`. The smooth
`Hom(TM, T^{(0,m)})`-section `x ↦ ⟨x, (covGradBundleEquiv 0 m x).symm (W.toSection x)⟩` (W smooth,
transported through the inverse smooth bundle equivalence
`covGradBundleEquiv_symm_contMDiff_totalSpace`) is evaluated at the smooth field `B_i`
(`ContMDiff.clm_bundle_apply`). -/
private theorem pureRFrozenSlot0Sec_contMDiff
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    {B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b}
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    (W : SmoothCcTensor g 0 (m + 1)) (i : Fin (Module.finrank ℝ E)) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 m ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 0 m ℝ E)
        (E := fun z : M => TensorRSSpace 0 m I z) x
        ((covGradBundleEquiv (I := I) (M := M) 0 m x).symm (W.toSection x) (B i x))) := by
  classical
  have hHom : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] TensorRSModel 0 m ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] TensorRSModel 0 m ℝ E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TensorRSSpace 0 m I z) x
        ((covGradBundleEquiv (I := I) (M := M) 0 m x).symm (W.toSection x))) := by
    have hWtot : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 (m + 1) ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (TensorRSModel 0 (m + 1) ℝ E)
          (E := fun z : M => TensorRSSpace 0 (m + 1) I z) x (W.toSection x)) :=
      W.toSection.contMDiff_toFun
    exact (covGradBundleEquiv_symm_contMDiff_totalSpace (I := I) (M := M) 0 m).comp hWtot
  exact ContMDiff.clm_bundle_apply (b := fun x : M => x)
    (ϕ := fun x => (covGradBundleEquiv (I := I) (M := M) 0 m x).symm (W.toSection x))
    (v := fun x => B i x) hHom (hB i)

/-- **The frozen-frame pure-Riemann curvature direction CLM is a smooth `Hom(TM, T^{(0,m)})`-bundle
section.** For a smooth frame `B`, the section `x ↦ ⟨x, pureRFrozenDirCLM g m B (W.toSection) x⟩` is
`C^∞`. On every smooth tangent field `Y`, the section
`x ↦ ⟨x, pureRFrozenDirCLM g m B (W.toSection) x (Y x)⟩` is the frame sum (over `i`) of the
curvature contractions `riemannSec (B_i) Y (slot0_{B_i} W)`, each smooth by `riemannSec_contMDiff`
on the smooth `B_i`, `Y`, and the smooth slot-`0` reading `pureRFrozenSlot0Sec_contMDiff`; bridged to
the bundle by `cotangentCov_clmSection_smooth_aux`. -/
private theorem pureRFrozenDirCLM_homSection_contMDiff
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    {B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b}
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    (W : SmoothCcTensor g 0 (m + 1)) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] TensorRSModel 0 m ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] TensorRSModel 0 m ℝ E)
        (E := fun y : M => TangentSpace I y →L[ℝ] TensorRSSpace 0 m I y) x
        (pureRFrozenDirCLM (I := I) (M := M) g m B (fun y : M => W.toSection y) x)) := by
  classical
  refine cotangentCov_clmSection_smooth_aux
    (φ := fun x : M => pureRFrozenDirCLM (I := I) (M := M) g m B (fun y : M => W.toSection y) x)
    (fun Y => ?_)
  have hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (fun b : M => (Y : Π b : M, TangentSpace I b) b)) :=
    Y.contMDiff

  have hsum : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 m ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 0 m ℝ E)
        (E := fun z : M => TensorRSSpace 0 m I z) x
        (∑ i : Fin (Module.finrank ℝ E),
          riemannSec (tensorCov (I := I) g 0 m) (B i) (fun b : M => Y b)
            (fun y : M => (covGradBundleEquiv (I := I) (M := M) 0 m y).symm (W.toSection y) (B i y))
            x)) := by
    refine ContMDiff.sum_section (s := Finset.univ) (fun i _ => ?_)
    exact riemannSec_contMDiff (cov := tensorCov (I := I) g 0 m) (hB i) hY
      (pureRFrozenSlot0Sec_contMDiff (I := I) (M := M) g m hB W i)
  refine hsum.congr ?_
  intro x
  refine congrArg (TotalSpace.mk' (TensorRSModel 0 m ℝ E)
    (E := fun z : M => TensorRSSpace 0 m I z) x) ?_
  rw [pureRFrozenDirCLM_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact (riemannOp_apply_smooth (cov := tensorCov (I := I) g 0 m) (X := B i) (Y := fun b : M => Y b)
    (Z := fun y : M => (covGradBundleEquiv (I := I) (M := M) 0 m y).symm (W.toSection y) (B i y))
    (x := x) (hB i) hY (pureRFrozenSlot0Sec_contMDiff (I := I) (M := M) g m hB W i)).symm ▸ rfl

/-- **Base-point smoothness of the order-`0` frozen-frame pure-Riemann curvature endomorphism fibre
field.** For a smooth frame `B`, the `(0, m + 1)`-tensor fibre field
`x ↦ pureRFrozenEndoFib g m B W x` is a smooth section. The smooth `Hom(TM, T^{(0,m)})`-section
`pureRFrozenDirCLM_homSection_contMDiff` is transported, fibrewise through the smooth bundle
equivalence `covGradBundleSmoothEquiv 0 m`, into the `(0, m + 1)`-tensor bundle. -/
private theorem pureRFrozenEndoFib_contMDiff
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    {B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b}
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    (W : SmoothCcTensor g 0 (m + 1)) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 (m + 1) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 0 (m + 1) ℝ E)
        (E := fun z : M => TensorRSSpace 0 (m + 1) I z) x
        (pureRFrozenEndoFib (I := I) (M := M) g m B W x)) := by
  classical
  have hcomp :
      ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 (m + 1) ℝ E)) ∞
        ((covGradBundleSmoothEquiv (I := I) (M := M) 0 m).toDiffeomorph ∘
          (fun x : M => TotalSpace.mk' (E →L[ℝ] TensorRSModel 0 m ℝ E)
            (E := fun y : M => TangentSpace I y →L[ℝ] TensorRSSpace 0 m I y) x
            (pureRFrozenDirCLM (I := I) (M := M) g m B (fun y : M => W.toSection y) x))) :=
    (covGradBundleSmoothEquiv (I := I) (M := M) 0 m).toDiffeomorph.contMDiff.comp
      (pureRFrozenDirCLM_homSection_contMDiff (I := I) (M := M) g m hB W)
  refine hcomp.congr ?_
  intro x
  rw [Function.comp_apply]
  exact covGradBundleSmoothEquiv_toDiffeomorph_apply (I := I) (M := M) 0 m x
    (pureRFrozenDirCLM (I := I) (M := M) g m B (fun y : M => W.toSection y) x)

/-- **The order-`0` frozen-frame pure-Riemann curvature endomorphism at rank `m + 1`**, a smooth
compactly-supported `(0, m + 1)`-tensor section: the slot-`0` uncurry of the frozen-frame pure-Riemann
curvature direction CLM `pureRFrozenDirCLM g m B (W.toSection)`. It is `B`-, `g`-, `R`-built and
fibrewise-`ℝ`-linear in `W`; smoothness `pureRFrozenEndoFib_contMDiff`, compact support on the closed
manifold. -/
private noncomputable def pureRFrozenEndoSucc
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    (W : SmoothCcTensor g 0 (m + 1)) :
    SmoothCcTensor g 0 (m + 1) where
  toSection :=
    { toFun := fun x : M => pureRFrozenEndoFib (I := I) (M := M) g m B W x
      contMDiff_toFun := pureRFrozenEndoFib_contMDiff (I := I) (M := M) g m hB W }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

@[simp] private lemma pureRFrozenEndoSucc_toSection
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    (W : SmoothCcTensor g 0 (m + 1)) (x : M) :
    (pureRFrozenEndoSucc (I := I) (M := M) g m B hB W).toSection x =
      pureRFrozenEndoFib (I := I) (M := M) g m B W x := rfl

/-- **The order-`0` frozen-frame pure-Riemann curvature endomorphism at every rank** (totalised).
For rank `r = m + 1 ≥ 1` it is the genuine endomorphism `pureRFrozenEndoSucc`; for rank `0` (no
slot-`0` to read) it is the zero operator. The zero junk at rank `0` is never reached by the grid
(the differentiated tower's recursion only increases the rank, starting from the base rank `s + 1`),
but it makes the `DiffBilinOp` totality hold. -/
private noncomputable def pureRFrozenEndo0
    (g : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i))) :
    ∀ (r : ℕ), SmoothCcTensor g 0 r → SmoothCcTensor g 0 r
  | 0 => fun _ => 0
  | (m + 1) => fun W => pureRFrozenEndoSucc (I := I) (M := M) g m B hB W

/-- **The order-`p` differentiated frozen-frame pure-Riemann curvature operator.** Acting on a smooth
compactly-supported `(0, r)`-tensor section `W`, `pureRFrozenDiffOp g B hB p r W` is the `p`-times
covariantly-differentiated frozen-frame pure-Riemann curvature endomorphism `(∇^p R(B, ·))W`, a smooth
compactly-supported `(0, r + p)`-tensor, defined recursively as the exact covariant-Leibniz remainder:

* `p = 0`: the order-`0` endomorphism `pureRFrozenEndo0 g B hB r W`;
* `p + 1`: `∇(pureRFrozenDiffOp p r W) − (rank-cast) pureRFrozenDiffOp p (r + 1) (∇W)` (the
  differentiated curvature: the part of `∇(∇^p R(B,·) W)` not captured by `∇^p R(B,·)(∇W)`); the
  right summand carries covariant rank `(r + 1) + p`, rank-cast to the differentiated rank `(r + p) + 1`
  via `castRankCc_db`.

By construction the single-step covariant Leibniz `∇(op p r W) = op (p + 1) r W + (rank-cast)
op p (r + 1) (∇W)` holds by `sub_add_cancel`. -/
private noncomputable def pureRFrozenDiffOp
    (g : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i))) :
    ∀ (p r : ℕ), SmoothCcTensor g 0 r → SmoothCcTensor g 0 (r + p)
  | 0, r => fun W => pureRFrozenEndo0 (I := I) (M := M) g B hB r W
  | (p + 1), r => fun W =>
      covGrad (I := I) (M := M) g 0 (r + p)
          (pureRFrozenDiffOp g B hB p r W) -
        castRankCc_db g 0 (by omega : (r + 1) + p = r + (p + 1))
          (pureRFrozenDiffOp g B hB p (r + 1) (covGrad (I := I) (M := M) g 0 r W))

/-- **`fiberNormSqSummand` representation of the fibre norm in an arbitrary `g_{x}`-orthonormal frame.**
For a `(0, s)`-tensor `S` at `x` and any `g_x`-orthonormal frame `e` with `n = Module.finrank`, the
intrinsic fibre norm squared is the double frame sum of `fiberNormSqSummand`. The single non-trivial
multi-index is the empty one (`K : Fin 0 → Fin n`); the rank-`s` index `J` ranges over the dual
tensor frame. Ported from the diagonal-sum reconstruction
`tensorInnerPointwise_0s_eq_diag_sum_orthoFrame`. -/
private lemma rfns_eq_sum_fiberNormSqSummand_of_orthoFrame
    (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M) (S : TensorRSSpace 0 s I x)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (hn : n = Module.finrank ℝ (TangentSpace I x))
    (horth : ∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0) :
    riemannianFiberNormSq (I := I) (M := M) g 0 s x S =
      ∑ K : Fin 0 → Fin n, ∑ J : Fin s → Fin n,
        fiberNormSqSummand (I := I) (M := M) g x 0 s S n e K J := by
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

  have hstep : riemannianFiberNormSq (I := I) (M := M) g 0 s x S =
      ∑ ψ : Fin s → Fin (Module.finrank ℝ (TangentSpace I x)),
        Tensor0SSpace.toModel
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from S)
              (unitZeroSec (I := I) (M := M) x))
            (fun k => e (ψ k)) ^ 2 := by
    rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g 0 s x S]
    rw [show tensorInnerPointwise (I := I) (M := M) g 0 s x
          (TensorRSSpace.toModel S) (TensorRSSpace.toModel S) =
        tensorInnerPointwise_0s (I := I) (M := M) (0 + s) g x
          (lowerAllUpperIndices (I := I) (M := M) g 0 s x (TensorRSSpace.toModel S))
          (lowerAllUpperIndices (I := I) (M := M) g 0 s x (TensorRSSpace.toModel S)) from rfl]
    rw [tensorInnerPointwise_0s_eq_diag_sum_orthoFrame (I := I) (M := M) g x (0 + s)
      bse hbse_orth _ _]
    have hkey : ∀ ξ : Fin (0 + s) → Fin (Module.finrank ℝ (TangentSpace I x)),
        lowerAllUpperIndices (I := I) (M := M) g 0 s x
            (TensorRSSpace.toModel S) (fun k => bse (ξ k)) =
          Tensor0SSpace.toModel
              ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from S)
                (unitZeroSec (I := I) (M := M) x))
              (fun j : Fin s => bse (ξ (Fin.natAdd 0 j))) := by
      intro ξ
      rw [lowerAllUpperIndices_apply (I := I) (M := M) g 0 s x (TensorRSSpace.toModel S)
        (fun k => bse (ξ k))]
      rw [toModel_tensorRS_apply (I := I) (M := M) 0 s x S (unitZeroSec (I := I) (M := M) x)]
      rw [unitZeroSec_apply (I := I) (M := M) x, Tensor0SSpace.toModel_ofModel]
      rw [separableFormAt_zero (I := I) (M := M) g x
        (fun i : Fin 0 => (fun k => bse (ξ k)) (Fin.castAdd s i))]
    have hstep2 : ∀ ξ : Fin (0 + s) → Fin (Module.finrank ℝ (TangentSpace I x)),
        lowerAllUpperIndices (I := I) (M := M) g 0 s x
              (TensorRSSpace.toModel S) (fun k => bse (ξ k)) *
            lowerAllUpperIndices (I := I) (M := M) g 0 s x
              (TensorRSSpace.toModel S) (fun k => bse (ξ k)) =
          Tensor0SSpace.toModel
              ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from S)
                (unitZeroSec (I := I) (M := M) x))
              (fun k => e (ξ (Fin.natAdd 0 k))) ^ 2 := by
      intro ξ
      rw [hkey ξ, ← pow_two]
      congr 2
      funext k
      rw [hbse_eq]
    refine Eq.trans (Finset.sum_congr rfl (fun ξ _ => hstep2 ξ)) ?_
    refine Fintype.sum_bijective
      (fun ξ : Fin (0 + s) → Fin (Module.finrank ℝ (TangentSpace I x)) =>
        fun k : Fin s => ξ (Fin.natAdd 0 k))
      ?_ _ _ (fun ξ => rfl)
    refine ⟨fun ξ₁ ξ₂ h => ?_, fun φ => ⟨fun k => φ (Fin.cast (Nat.zero_add s) k), ?_⟩⟩
    · funext k
      have hk : k = Fin.natAdd 0 (Fin.cast (Nat.zero_add s) k) := by ext; simp
      rw [hk]; exact congrFun h (Fin.cast (Nat.zero_add s) k)
    · funext k
      change φ (Fin.cast (Nat.zero_add s) (Fin.natAdd 0 k)) = φ k
      have : Fin.cast (Nat.zero_add s) (Fin.natAdd 0 k) = k := by ext; simp
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

/-- **Uniform-over-`M` rank-`m` proportional curvature-operator fibre bound.** The supremum over the
compact `M` of the continuous per-point proportional curvature envelope
`exists_continuous_riemannianFiberNormSq_riemannOp_tensorCov_proportional`: a single nonnegative
constant `Csup` with, for every point `x`, tangent vectors `v, w`, and `(0, m)`-tensor `T`,
`rfns(R_x(v, w) T)(x) ≤ Csup · g(v, v) · g(w, w) · rfns(T)(x)`. It is the rank-`m` curvature
operator's base-point-uniform proportional fibre constant. -/
private lemma exists_uniform_riemannOp_tensorCov_proportional
    (g : SmoothRiemannianMetric I M) (m : ℕ) :
    ∃ Csup : ℝ, 0 ≤ Csup ∧
      ∀ (x : M) (v w : TangentSpace I x) (T : TensorRSSpace 0 m I x),
        riemannianFiberNormSq (I := I) (M := M) g 0 m x
            (riemannOp (tensorCov (I := I) g 0 m) x v w T) ≤
          Csup * g.inner x v v * g.inner x w w *
            riemannianFiberNormSq (I := I) (M := M) g 0 m x T := by
  classical
  obtain ⟨Ccurv, hCcurv_cont, hCcurv_nonneg, hCcurv_bound⟩ :=
    exists_continuous_riemannianFiberNormSq_riemannOp_tensorCov_proportional (I := I) (M := M) g m
  have hCpt := (isCompact_univ (X := M)).image hCcurv_cont
  obtain ⟨C₀, hC₀⟩ := hCpt.bddAbove
  refine ⟨max C₀ 0, le_max_right _ _, fun x v w T => ?_⟩
  have hCcurv_le : Ccurv x ≤ max C₀ 0 :=
    le_trans (hC₀ ⟨x, Set.mem_univ _, rfl⟩) (le_max_left _ _)
  have hvv_nonneg : 0 ≤ g.inner x v v := by
    rcases eq_or_ne v 0 with hv0 | hv0
    · rw [hv0]; simp
    · exact (g.pos x v hv0).le
  have hww_nonneg : 0 ≤ g.inner x w w := by
    rcases eq_or_ne w 0 with hw0 | hw0
    · rw [hw0]; simp
    · exact (g.pos x w hw0).le
  have hfactor_nonneg :
      0 ≤ g.inner x v v * g.inner x w w *
        riemannianFiberNormSq (I := I) (M := M) g 0 m x T :=
    mul_nonneg (mul_nonneg hvv_nonneg hww_nonneg)
      (riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 m x T)
  calc
    riemannianFiberNormSq (I := I) (M := M) g 0 m x
        (riemannOp (tensorCov (I := I) g 0 m) x v w T)
        ≤ Ccurv x * g.inner x v v * g.inner x w w *
            riemannianFiberNormSq (I := I) (M := M) g 0 m x T :=
          hCcurv_bound x v w T
    _ = Ccurv x * (g.inner x v v * g.inner x w w *
            riemannianFiberNormSq (I := I) (M := M) g 0 m x T) := by ring
    _ ≤ max C₀ 0 * (g.inner x v v * g.inner x w w *
            riemannianFiberNormSq (I := I) (M := M) g 0 m x T) :=
          mul_le_mul_of_nonneg_right hCcurv_le hfactor_nonneg
    _ = max C₀ 0 * g.inner x v v * g.inner x w w *
            riemannianFiberNormSq (I := I) (M := M) g 0 m x T := by ring

/-- **The slot-`0` curry slice of the order-`0` frozen-frame endomorphism fibre is the curvature
direction CLM applied to the slice direction.** For a `g_{x}`-orthonormal frame `e` (built from a
`Module.Basis`) representing the rank-`m` fibre norm, the slot-`0` curry of
`pureRFrozenEndoFib g m B W x` along the frame direction `e a` has the same intrinsic `(0, m)` fibre
norm as the curvature direction CLM `pureRFrozenDirCLM g m B (W.toSection) x (e a)`. The slot-`0`
curry reads the leftmost covariant slot at `e a`; through `covGradBundleEquiv_apply_eval` this is
exactly the value of the direction CLM at `e a`, so the two `(0, m)`-tensors agree component-by-frame
component (`fiberNormSqComponent`), hence have equal fibre norm. -/
private lemma pureRFrozenEndoFib_slot0Curry_rfns_eq
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (W : SmoothCcTensor g 0 (m + 1)) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x) (K₀ : Fin 0 → Fin n)
    (hreprS : ∀ S : TensorRSSpace 0 m I x,
      riemannianFiberNormSq (I := I) (M := M) g 0 m x S =
        ∑ K : Fin 0 → Fin n, ∑ J : Fin m → Fin n,
          fiberNormSqSummand (I := I) (M := M) g x 0 m S n e K J)
    (a : Fin n) :
    riemannianFiberNormSq (I := I) (M := M) g 0 m x
        (slot0Curry (I := I) (M := M) g x m e K₀
          (pureRFrozenEndoFib (I := I) (M := M) g m B W x) a) =
      riemannianFiberNormSq (I := I) (M := M) g 0 m x
        (pureRFrozenDirCLM (I := I) (M := M) g m B (fun y : M => W.toSection y) x (e a)) := by
  classical
  rw [riemannianFiberNormSq_eq_sum_componentS_sq (I := I) (M := M) g x m e hreprS _ K₀,
    riemannianFiberNormSq_eq_sum_componentS_sq (I := I) (M := M) g x m e hreprS _ K₀]
  refine Finset.sum_congr rfl (fun J _ => ?_)
  congr 1

  unfold fiberNormSqComponent
  set ωK : Tensor0SSpace 0 I x :=
    (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
      (fun k => g.inner x (e (K₀ k))) with hωK

  have hslot : (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace m I x from
          slot0Curry (I := I) (M := M) g x m e K₀
            (pureRFrozenEndoFib (I := I) (M := M) g m B W x) a) ωK =
        tensor0S_curry (I := I) (M := M) m x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from
            pureRFrozenEndoFib (I := I) (M := M) g m B W x) ωK) (e a) := by
    rw [slot0Curry_apply (I := I) (M := M) g x m e K₀
      (pureRFrozenEndoFib (I := I) (M := M) g m B W x) a ωK]
    have hscalar : tensor00Scalar (I := I) (M := M) x ωK = 1 := by
      rw [hωK,
        show ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
            (fun k => g.inner x (e (K₀ k))) : Tensor0SSpace 0 I x) =
          coframeS (I := I) (M := M) g x 0 e K₀ from rfl,
        tensor00Scalar_apply (I := I) (M := M) x _ (fun k : Fin 0 => k.elim0),
        coframeS_apply (I := I) (M := M) g x 0 e K₀]
      simp
    rw [hscalar, one_smul]
  rw [hslot]

  rw [show (tensor0S_curry (I := I) (M := M) m x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from
          pureRFrozenEndoFib (I := I) (M := M) g m B W x) ωK) (e a)
        (fun k => e (J k)) : ℝ) =
      Tensor0SSpace.toModel
        (tensor0S_curry (I := I) (M := M) m x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from
            pureRFrozenEndoFib (I := I) (M := M) g m B W x) ωK) (e a))
        (fun k => e (J k)) from rfl]
  rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
    (T := (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from
      pureRFrozenEndoFib (I := I) (M := M) g m B W x) ωK) (v0 := e a) (vs := fun k => e (J k))]

  rw [pureRFrozenEndoFib]
  rw [covGradBundleEquiv_apply_eval (I := I) (M := M) 0 m x
    (pureRFrozenDirCLM (I := I) (M := M) g m B (fun y : M => W.toSection y) x) ωK
    (Fin.cons (e a) (fun k => e (J k)))]
  rw [Fin.cons_zero]
  congr 1

/-- **The slot-`0` reading of a `(0, m+1)`-tensor along a frame vector is fibre-dominated by the whole.**
For a `g_{x}`-orthonormal frame `e` (representing the rank-`m`/rank-`(m+1)` fibre norms), the slot-`0`
reading `(covGradBundleEquiv 0 m x).symm T (e a)` — a `(0, m)`-tensor — has the same fibre norm as the
slot-`0` curry `slot0Curry g x m e K₀ T a` (both read the leftmost covariant slot at `e a`, agreeing
component-by-frame-component through `covGradBundleEquiv_symm_apply_eval`), hence by the slot-`0`
Parseval domination is bounded by the full `(0, m+1)` fibre norm of `T`. -/
private lemma covGradBundleEquiv_symm_reading_rfns_le
    (g : SmoothRiemannianMetric I M) (m : ℕ) (x : M)
    (T : TensorRSSpace 0 (m + 1) I x)
    {n : ℕ} (e : Fin n → TangentSpace I x) (K₀ : Fin 0 → Fin n)
    (hreprS : ∀ S : TensorRSSpace 0 m I x,
      riemannianFiberNormSq (I := I) (M := M) g 0 m x S =
        ∑ K : Fin 0 → Fin n, ∑ J : Fin m → Fin n,
          fiberNormSqSummand (I := I) (M := M) g x 0 m S n e K J)
    (hreprSucc : ∀ S : TensorRSSpace 0 (m + 1) I x,
      riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) x S =
        ∑ K : Fin 0 → Fin n, ∑ J : Fin (m + 1) → Fin n,
          fiberNormSqSummand (I := I) (M := M) g x 0 (m + 1) S n e K J)
    (a : Fin n) :
    riemannianFiberNormSq (I := I) (M := M) g 0 m x
        ((covGradBundleEquiv (I := I) (M := M) 0 m x).symm T (e a)) ≤
      riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) x T := by
  classical
  have heq : riemannianFiberNormSq (I := I) (M := M) g 0 m x
        ((covGradBundleEquiv (I := I) (M := M) 0 m x).symm T (e a)) =
      riemannianFiberNormSq (I := I) (M := M) g 0 m x
        (slot0Curry (I := I) (M := M) g x m e K₀ T a) := by
    rw [riemannianFiberNormSq_eq_sum_componentS_sq (I := I) (M := M) g x m e hreprS _ K₀,
      riemannianFiberNormSq_eq_sum_componentS_sq (I := I) (M := M) g x m e hreprS _ K₀]
    refine Finset.sum_congr rfl (fun J _ => ?_)
    congr 1
    unfold fiberNormSqComponent
    set ωK : Tensor0SSpace 0 I x :=
      (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
        (fun k => g.inner x (e (K₀ k))) with hωK

    have hslot : (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace m I x from
            slot0Curry (I := I) (M := M) g x m e K₀ T a) ωK =
          tensor0S_curry (I := I) (M := M) m x
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from T) ωK) (e a) := by
      rw [slot0Curry_apply (I := I) (M := M) g x m e K₀ T a ωK]
      have hscalar : tensor00Scalar (I := I) (M := M) x ωK = 1 := by
        rw [hωK,
          show ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
              (fun k => g.inner x (e (K₀ k))) : Tensor0SSpace 0 I x) =
            coframeS (I := I) (M := M) g x 0 e K₀ from rfl,
          tensor00Scalar_apply (I := I) (M := M) x _ (fun k : Fin 0 => k.elim0),
          coframeS_apply (I := I) (M := M) g x 0 e K₀]
        simp
      rw [hscalar, one_smul]

    rw [show ((((covGradBundleEquiv (I := I) (M := M) 0 m x).symm T (e a)) ωK)
          (fun k => e (J k)) : ℝ) =
        Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace m I x from
            (covGradBundleEquiv (I := I) (M := M) 0 m x).symm T (e a)) ωK)
          (fun k => e (J k)) from rfl]
    rw [covGradBundleEquiv_symm_apply_eval (I := I) (M := M) 0 m x T (e a) ωK (fun k => e (J k))]

    rw [hslot]
    rw [show ((tensor0S_curry (I := I) (M := M) m x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from T) ωK) (e a))
          (fun k => e (J k)) : ℝ) =
        Tensor0SSpace.toModel
          (tensor0S_curry (I := I) (M := M) m x
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from T) ωK) (e a))
          (fun k => e (J k)) from rfl]
    rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from T) ωK)
      (v0 := e a) (vs := fun k => e (J k))]
  rw [heq]
  exact riemannianFiberNormSq_slot0Curry_le_of_frame (I := I) (M := M) g m x e K₀
    hreprS hreprSucc T a

/-- **The slot-`0` reading of a `(0, m+1)`-tensor along a centre-frame curvature direction is
fibre-dominated by the whole.** Specialisation of `covGradBundleEquiv_symm_reading_rfns_le` to the
`g_{x₀}`-orthonormal centre frame `eC i := B i x₀` (orthonormal at its own centre by `hBorth`): the
slot-`0` reading `(covGradBundleEquiv 0 m x₀).symm T (B i x₀)` is bounded by the full `(0, m+1)` fibre
norm of `T`. -/
private lemma covGradBundleEquiv_symm_reading_rfns_le_centreFrame
    (g : SmoothRiemannianMetric I M) (m : ℕ) (x₀ : M)
    (T : TensorRSSpace 0 (m + 1) I x₀)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hBorth : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner x₀ (B i x₀) (B j x₀) = if i = j then (1 : ℝ) else 0)
    (i : Fin (Module.finrank ℝ E)) :
    riemannianFiberNormSq (I := I) (M := M) g 0 m x₀
        ((covGradBundleEquiv (I := I) (M := M) 0 m x₀).symm T (B i x₀)) ≤
      riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) x₀ T := by
  classical
  set eC : Fin (Module.finrank ℝ E) → TangentSpace I x₀ := fun j => B j x₀ with heC_def
  have hnC : Module.finrank ℝ E = Module.finrank ℝ (TangentSpace I x₀) := rfl
  have horthC : ∀ a b : Fin (Module.finrank ℝ E),
      g.inner x₀ (eC a) (eC b) = if a = b then (1 : ℝ) else 0 := fun a b => hBorth a b
  set K₀ : Fin 0 → Fin (Module.finrank ℝ E) := fun k => k.elim0 with hK₀
  have hreprS : ∀ S : TensorRSSpace 0 m I x₀,
      riemannianFiberNormSq (I := I) (M := M) g 0 m x₀ S =
        ∑ K : Fin 0 → Fin (Module.finrank ℝ E), ∑ J : Fin m → Fin (Module.finrank ℝ E),
          fiberNormSqSummand (I := I) (M := M) g x₀ 0 m S (Module.finrank ℝ E) eC K J :=
    fun S => rfns_eq_sum_fiberNormSqSummand_of_orthoFrame (I := I) (M := M) g m x₀ S eC hnC horthC
  have hreprSucc : ∀ S : TensorRSSpace 0 (m + 1) I x₀,
      riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) x₀ S =
        ∑ K : Fin 0 → Fin (Module.finrank ℝ E), ∑ J : Fin (m + 1) → Fin (Module.finrank ℝ E),
          fiberNormSqSummand (I := I) (M := M) g x₀ 0 (m + 1) S (Module.finrank ℝ E) eC K J :=
    fun S => rfns_eq_sum_fiberNormSqSummand_of_orthoFrame (I := I) (M := M) g (m + 1) x₀ S eC hnC
      horthC
  have h := covGradBundleEquiv_symm_reading_rfns_le (I := I) (M := M) g m x₀ T eC K₀
    hreprS hreprSucc i
  rwa [heC_def] at h

/-- **The order-`0` layer of the frozen-frame curvature envelope, proved at the centre frame.** For a
closed smooth Riemannian manifold `(M, g)` there is a nonnegative rank-indexed family `kappa0 : ℕ → ℝ`,
**uniform over the centre `x₀`**, such that the order-`0` frozen-frame pure-Riemann curvature
endomorphism at the centre frame `smoothOrthoFrame g x₀`, evaluated at its own centre `x₀`, has
intrinsic squared fibre norm at most `kappa0 r` times that of `W`:
```
rfns(pureRFrozenDiffOp g (smoothOrthoFrame g x₀) … 0 r W)(x₀) ≤ kappa0 r · rfns(W)(x₀).
```

At rank `r = 0` the operator is the zero endomorphism and the bound is trivial; at rank `r = m + 1`
the endomorphism fibre `covGradBundleEquiv 0 m x₀ (∑ᵢ R(B_iˣ⁰, ·)(slot0_{B_iˣ⁰} W))` is read by the
slot-`0` Parseval frame-sum over a `g_{x₀}`-orthonormal frame `e`, each slice being the curvature
contraction `∑ᵢ R(B_iˣ⁰, e_a)(slot0_{B_iˣ⁰} W)`, fibre-bounded by the rank-`m` curvature sup
(`exists_uniform_riemannOp_tensorCov_proportional`) times the orthonormal Gram factors
`g(B_iˣ⁰, B_iˣ⁰) = g(e_a, e_a) = 1` (`smoothOrthoFrame_orthonormal_at_center`) and the slot-`0`
reading fibre norm `rfns((covGradBundleEquiv 0 m x₀).symm (W x₀) (B_iˣ⁰))(x₀) ≤ rfns(W)(x₀)`
(`covGradBundleEquiv_symm_reading_rfns_le`), giving `kappa0 (m + 1) = N³ · Csup m`. -/
theorem exists_proportional_pureRFrozenFrameDiffOp_orderZero
    (g : SmoothRiemannianMetric I M) :
    ∃ kappa0 : ℕ → ℝ, (∀ r, 0 ≤ kappa0 r) ∧
      ∀ (r : ℕ) (W : SmoothCcTensor g 0 r) (x₀ : M),
        riemannianFiberNormSq (I := I) (M := M) g 0 (r + 0) x₀
            ((pureRFrozenDiffOp (I := I) (M := M) g (smoothOrthoFrame (I := I) g x₀)
              (fun i => smoothOrthoFrame_smooth (I := I) g x₀ i) 0 r W).toSection x₀) ≤
          kappa0 r * riemannianFiberNormSq (I := I) (M := M) g 0 r x₀ (W.toSection x₀) := by
  classical
  set N : ℝ := (Module.finrank ℝ E : ℝ) with hN_def

  choose Csup hCsup_nonneg hCsup using fun m =>
    exists_uniform_riemannOp_tensorCov_proportional (I := I) (M := M) g m
  refine ⟨fun r => match r with | 0 => 0 | (m + 1) => N ^ 3 * Csup m,
    fun r => ?_, fun r W x₀ => ?_⟩
  · -- Nonnegativity of the constant family.
    cases r with
    | zero => exact le_refl 0
    | succ m => exact mul_nonneg (by positivity) (hCsup_nonneg m)

  rw [show (pureRFrozenDiffOp (I := I) (M := M) g (smoothOrthoFrame (I := I) g x₀)
        (fun i => smoothOrthoFrame_smooth (I := I) g x₀ i) 0 r W) =
      pureRFrozenEndo0 (I := I) (M := M) g (smoothOrthoFrame (I := I) g x₀)
        (fun i => smoothOrthoFrame_smooth (I := I) g x₀ i) r W from rfl]
  cases r with
  | zero =>

      rw [show ((pureRFrozenEndo0 (I := I) (M := M) g (smoothOrthoFrame (I := I) g x₀)
            (fun i => smoothOrthoFrame_smooth (I := I) g x₀ i) 0 W).toSection x₀ :
            TensorRSSpace 0 (0 + 0) I x₀) = (0 : TensorRSSpace 0 (0 + 0) I x₀) from rfl]
      rw [riemannianFiberNormSq_zero]
      have hrhs0 : (fun r => match r with
          | 0 => (0 : ℝ) | (m + 1) => N ^ 3 * Csup m) 0 = 0 := rfl
      rw [hrhs0, zero_mul]
  | succ m =>

      set B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b := smoothOrthoFrame (I := I) g x₀
        with hB_def
      have hBorth : ∀ i j : Fin (Module.finrank ℝ E),
          g.inner x₀ (B i x₀) (B j x₀) = if i = j then (1 : ℝ) else 0 := by
        intro i j; rw [hB_def]; exact smoothOrthoFrame_orthonormal_at_center (I := I) g x₀ i j

      obtain ⟨n, e, _bse, hn, _hbse_eq, horth, _hpars, _hexp, _hreprm1⟩ :=
        tangent_orthonormalBasisS_witness (I := I) (M := M) g (m + 1) x₀
      set K₀ : Fin 0 → Fin n := fun k => k.elim0 with hK₀

      have hreprS : ∀ S : TensorRSSpace 0 m I x₀,
          riemannianFiberNormSq (I := I) (M := M) g 0 m x₀ S =
            ∑ K : Fin 0 → Fin n, ∑ J : Fin m → Fin n,
              fiberNormSqSummand (I := I) (M := M) g x₀ 0 m S n e K J :=
        fun S => rfns_eq_sum_fiberNormSqSummand_of_orthoFrame (I := I) (M := M) g m x₀ S e
          (by rw [hn]) horth
      have hreprSucc : ∀ S : TensorRSSpace 0 (m + 1) I x₀,
          riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) x₀ S =
            ∑ K : Fin 0 → Fin n, ∑ J : Fin (m + 1) → Fin n,
              fiberNormSqSummand (I := I) (M := M) g x₀ 0 (m + 1) S n e K J :=
        fun S => rfns_eq_sum_fiberNormSqSummand_of_orthoFrame (I := I) (M := M) g (m + 1) x₀ S e
          (by rw [hn]) horth

      rw [show (pureRFrozenEndo0 (I := I) (M := M) g B
            (fun i => smoothOrthoFrame_smooth (I := I) g x₀ i) (m + 1) W).toSection x₀ =
          pureRFrozenEndoFib (I := I) (M := M) g m B W x₀ from rfl]

      rw [riemannianFiberNormSq_succ_eq_sum_slot0Curry_of_frame (I := I) (M := M) g m x₀ e K₀
        hreprS hreprSucc (pureRFrozenEndoFib (I := I) (M := M) g m B W x₀)]

      have hslice : ∀ a : Fin n,
          riemannianFiberNormSq (I := I) (M := M) g 0 m x₀
              (slot0Curry (I := I) (M := M) g x₀ m e K₀
                (pureRFrozenEndoFib (I := I) (M := M) g m B W x₀) a) =
            riemannianFiberNormSq (I := I) (M := M) g 0 m x₀
              (pureRFrozenDirCLM (I := I) (M := M) g m B (fun y : M => W.toSection y) x₀ (e a)) :=
        fun a => pureRFrozenEndoFib_slot0Curry_rfns_eq (I := I) (M := M) g m B W x₀ e K₀ hreprS a
      rw [Finset.sum_congr rfl (fun a (_ : a ∈ Finset.univ) => hslice a)]

      set Csm : ℝ := Csup m with hCsm_def
      have hper : ∀ a : Fin n,
          riemannianFiberNormSq (I := I) (M := M) g 0 m x₀
              (pureRFrozenDirCLM (I := I) (M := M) g m B (fun y : M => W.toSection y) x₀ (e a)) ≤
            (n : ℝ) * ((n : ℝ) * (Csm *
              riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) x₀ (W.toSection x₀))) := by
        intro a
        rw [pureRFrozenDirCLM_apply (I := I) (M := M) g m B (fun y : M => W.toSection y) x₀ (e a)]

        refine le_trans (riemannianFiberNormSq_sum_le_card_mul (I := I) (M := M) g 0 m x₀
          (Finset.univ : Finset (Fin (Module.finrank ℝ E))) _) ?_
        rw [Finset.card_univ, Fintype.card_fin]

        have hcard_le : (Module.finrank ℝ E : ℝ) = (n : ℝ) := by rw [hn]; rfl
        rw [hcard_le]
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg n)

        have hsummand : ∀ i : Fin (Module.finrank ℝ E),
            riemannianFiberNormSq (I := I) (M := M) g 0 m x₀
                (riemannOp (tensorCov (I := I) g 0 m) x₀ (B i x₀) (e a)
                  ((covGradBundleEquiv (I := I) (M := M) 0 m x₀).symm (W.toSection x₀) (B i x₀))) ≤
              Csm * riemannianFiberNormSq (I := I) (M := M) g 0 (m + 1) x₀ (W.toSection x₀) := by
          intro i
          have hgB : g.inner x₀ (B i x₀) (B i x₀) = 1 := by
            have := hBorth i i; rwa [if_pos rfl] at this
          have hge : g.inner x₀ (e a) (e a) = 1 := by
            have := horth a a; rwa [if_pos rfl] at this
          have hbound := hCsup m x₀ (B i x₀) (e a)
            ((covGradBundleEquiv (I := I) (M := M) 0 m x₀).symm (W.toSection x₀) (B i x₀))
          rw [hgB, hge, mul_one, mul_one, ← hCsm_def] at hbound
          refine le_trans hbound ?_
          refine mul_le_mul_of_nonneg_left ?_ (by rw [hCsm_def]; exact hCsup_nonneg m)

          exact covGradBundleEquiv_symm_reading_rfns_le_centreFrame (I := I) (M := M) g m x₀
            (W.toSection x₀) B hBorth i
        refine le_trans (Finset.sum_le_sum (fun i _ => hsummand i)) ?_
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hcard_le]

      refine le_trans (Finset.sum_le_sum (fun a _ => hper a)) ?_
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hn_eq : (n : ℝ) = N := by rw [hn, hN_def]; rfl
      have hrhs : (fun r => match r with
          | 0 => (0 : ℝ) | (m' + 1) => N ^ 3 * Csup m') (m + 1) = N ^ 3 * Csup m := rfl
      rw [hn_eq, hCsm_def, hrhs]
      exact le_of_eq (by ring)


/-! ## The frame-free pure-Riemann trace tower (the sound direct route)

The frozen-frame high-order tower above is unsound for `p ≥ 1`: its differentiated diagonal carries
the quadratic frame jet `(∇B)²` of the centre frame `B = smoothOrthoFrame g x₀`, which is
chart-selection-unbounded on a multi-chart manifold (no atlas-finiteness hypothesis). The replacement
below avoids the frame jet entirely by using, as the order-`0` base, the *moving-frame* pure-Riemann
endomorphism (the frame chosen at the evaluation point, orthonormal at its own centre), whose fibre
*value* is frame-independent (a genuine `g`-metric trace), hence frame-free; its differentiated tower
therefore differentiates only the frame-free curvature factor, never a frame jet. -/

/-- **The slot-`0` pure-Riemann curvature bilinear form at the curvature direction `v`.** For a fixed
direction `v ∈ T_y M`, the continuous bilinear form
```
(X, Y) ↦ riemannOp (tensorCov g 0 m) y X v ((covGradBundleEquiv 0 m y).symm (W y) Y),
```
i.e. `R(X, v)(slot0_Y W)`. The first slot `X` is the slot-`1` argument of the Riemann operator; the
second slot `Y` is the slot-`0` reading direction of `W`. This is the slot-`0`-reading analogue of
`pureRValuedBilinAt` (`MovingFrameCurvatureTraceSmooth`); its diagonal frame sum is the frozen-frame
pure-Riemann curvature direction CLM at `v`. -/
private noncomputable def pureRSlot0BilinAt
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    (W : Π b : M, TensorRSSpace 0 (m + 1) I b) (y : M) (v : TangentSpace I y) :
    TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] TensorRSSpace 0 m I y :=
  haveI : T2Space (TangentSpace I y) := inferInstanceAs (T2Space E)
  haveI : FiniteDimensional ℝ (TangentSpace I y) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun := fun X => (riemannOp (tensorCov (I := I) g 0 m) y X v).comp
        ((covGradBundleEquiv (I := I) (M := M) 0 m y).symm (W y))
      map_add' := fun X X' => by
        ext Y
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
          (riemannOp (tensorCov (I := I) g 0 m) y).map_add X X']
      map_smul' := fun c X => by
        ext Y
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
          RingHom.id_apply, (riemannOp (tensorCov (I := I) g 0 m) y).map_smul c X] }

/-- The defining apply formula for `pureRSlot0BilinAt`. -/
private lemma pureRSlot0BilinAt_apply
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    (W : Π b : M, TensorRSSpace 0 (m + 1) I b) (y : M) (v X Y : TangentSpace I y) :
    pureRSlot0BilinAt (I := I) (M := M) g m W y v X Y =
      riemannOp (tensorCov (I := I) g 0 m) y X v
        ((covGradBundleEquiv (I := I) (M := M) 0 m y).symm (W y) Y) := rfl

/-- **The slot-`i` frozen-frame summand is the diagonal of `pureRSlot0BilinAt`.** For a smooth frame
`B` and the smooth tensor section `W`, the slot-`i` summand of the frozen-frame pure-Riemann direction
CLM at `v` equals the diagonal `pureRSlot0BilinAt g m W y v (B i y) (B i y)`. True by `rfl` (both unfold
to `riemannOp y (B i y) v ((covGradBundleEquiv 0 m y).symm (W y) (B i y))`). -/
private lemma pureRSlot0BilinAt_frame_summand
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    (W : SmoothCcTensor g 0 (m + 1))
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (i : Fin (Module.finrank ℝ E)) (y : M) (v : TangentSpace I y) :
    riemannOp (tensorCov (I := I) g 0 m) y (B i y) v
        ((covGradBundleEquiv (I := I) (M := M) 0 m y).symm (W.toSection y) (B i y)) =
      pureRSlot0BilinAt (I := I) (M := M) g m (fun b : M => W.toSection b) y v (B i y) (B i y) := rfl

/-- **The frozen-frame pure-Riemann slot-`0` direction CLM is frame-independent among
`g_y`-orthonormal frames.** For two smooth tangent frames `B`, `C` both `g_y`-orthonormal at the
evaluation point `y`,
```
pureRFrozenDirCLM g m B (W.toSection) y = pureRFrozenDirCLM g m C (W.toSection) y.
```
For each curvature direction `v`, the value `∑ᵢ R(B_iʸ, v)(slot0_{B_iʸ} W)` is the diagonal frame
trace of the continuous bilinear form `pureRSlot0BilinAt g m W y v`, frame-independent by
`orthonormal_basis_bilin_trace` (after scalarising against the model). The slot-`0` reading is a
genuine `g`-metric trace (`B_i` contracted twice), exactly the shape that fixes the frame dependence to
the orthonormal Gram factor `1`. -/
private theorem pureRFrozenDirCLM_frame_independent
    (g : SmoothRiemannianMetric I M) (m : ℕ) (W : SmoothCcTensor g 0 (m + 1))
    {B C : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b} (y : M)
    (hB_orth : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner y (B i y) (B j y) = if i = j then (1 : ℝ) else 0)
    (hC_orth : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner y (C i y) (C j y) = if i = j then (1 : ℝ) else 0) :
    pureRFrozenDirCLM (I := I) (M := M) g m B (fun b : M => W.toSection b) y =
      pureRFrozenDirCLM (I := I) (M := M) g m C (fun b : M => W.toSection b) y := by
  classical
  haveI : T2Space (TangentSpace I y) := inferInstanceAs (T2Space E)
  haveI : FiniteDimensional ℝ (TangentSpace I y) := inferInstanceAs (FiniteDimensional ℝ E)
  refine ContinuousLinearMap.ext (fun v => ?_)
  refine ContinuousLinearMap.ext (fun D => ?_)
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro mtail
  haveI : T2Space (TensorRSSpace 0 m I y) :=
    inferInstanceAs (T2Space (Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace m I y))
  haveI : FiniteDimensional ℝ (TensorRSSpace 0 m I y) :=
    inferInstanceAs (FiniteDimensional ℝ (Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace m I y))

  set scalarize : TensorRSSpace 0 m I y →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap
      { toFun := fun T => Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace m I y from T) D) mtail
        map_add' := fun T T' => by
          change Tensor0SSpace.toModel ((T + T') D) mtail =
            Tensor0SSpace.toModel (T D) mtail + Tensor0SSpace.toModel (T' D) mtail
          rw [ContinuousLinearMap.add_apply, Tensor0SSpace.toModel_add,
            ContinuousMultilinearMap.add_apply]
        map_smul' := fun c T => by
          change Tensor0SSpace.toModel ((c • T) D) mtail = c • Tensor0SSpace.toModel (T D) mtail
          rw [ContinuousLinearMap.smul_apply, Tensor0SSpace.toModel_smul,
            ContinuousMultilinearMap.smul_apply] }
    with hscalarize_def
  have hscalarize_apply : ∀ T : TensorRSSpace 0 m I y,
      scalarize T = Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace m I y from T) D) mtail := by
    intro T
    rw [hscalarize_def, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk]

  set Hb : TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap
      { toFun := fun X => scalarize.comp
          (pureRSlot0BilinAt (I := I) (M := M) g m (fun b : M => W.toSection b) y v X)
        map_add' := fun X X' => by
          ext Y
          change scalarize (pureRSlot0BilinAt (I := I) (M := M) g m
              (fun b : M => W.toSection b) y v (X + X') Y) =
            scalarize (pureRSlot0BilinAt (I := I) (M := M) g m
                (fun b : M => W.toSection b) y v X Y) +
              scalarize (pureRSlot0BilinAt (I := I) (M := M) g m
                (fun b : M => W.toSection b) y v X' Y)
          rw [map_add (pureRSlot0BilinAt (I := I) (M := M) g m
            (fun b : M => W.toSection b) y v) X X',
            ContinuousLinearMap.add_apply, map_add scalarize]
        map_smul' := fun c X => by
          ext Y
          change scalarize (pureRSlot0BilinAt (I := I) (M := M) g m
              (fun b : M => W.toSection b) y v (c • X) Y) =
            c • scalarize (pureRSlot0BilinAt (I := I) (M := M) g m
              (fun b : M => W.toSection b) y v X Y)
          rw [map_smul (pureRSlot0BilinAt (I := I) (M := M) g m
            (fun b : M => W.toSection b) y v) c X,
            ContinuousLinearMap.smul_apply, map_smul scalarize] }
    with hHb_def
  have hHb_apply : ∀ X Y : TangentSpace I y,
      Hb X Y = Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace m I y from
          pureRSlot0BilinAt (I := I) (M := M) g m (fun b : M => W.toSection b) y v X Y) D) mtail := by
    intro X Y
    rw [hHb_def, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
      ContinuousLinearMap.comp_apply, hscalarize_apply]

  have hframe : ∀ (F : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b),
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace m I y from
          pureRFrozenDirCLM (I := I) (M := M) g m F (fun b : M => W.toSection b) y v) D) mtail =
      ∑ i : Fin (Module.finrank ℝ E), Hb (F i y) (F i y) := by
    intro F
    have hsum_apply :
        (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace m I y from
          pureRFrozenDirCLM (I := I) (M := M) g m F (fun b : M => W.toSection b) y v) D =
        ∑ i : Fin (Module.finrank ℝ E),
          (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace m I y from
            riemannOp (tensorCov (I := I) g 0 m) y (F i y) v
              ((covGradBundleEquiv (I := I) (M := M) 0 m y).symm (W.toSection y) (F i y))) D := by
      rw [pureRFrozenDirCLM_apply, ContinuousLinearMap.sum_apply]
    rw [hsum_apply, ← Tensor0SSpace.toModelL_apply, map_sum, ContinuousMultilinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Tensor0SSpace.toModelL_apply, hHb_apply (F i y) (F i y),
      pureRSlot0BilinAt_frame_summand (I := I) (M := M) g m W F i y v]
  rw [hframe B, hframe C]
  rw [orthonormal_basis_bilin_trace (I := I) (M := M) g (x := y) Hb (fun i => B i y) hB_orth,
    orthonormal_basis_bilin_trace (I := I) (M := M) g (x := y) Hb (fun i => C i y) hC_orth]

/-- **The moving-frame pure-Riemann slot-`0` curvature endomorphism fibre value (rank `m + 1`).** At
the base point `x`, the slot-`0` uncurry of the pure-Riemann direction CLM against the *moving*
`g_x`-orthonormal frame `smoothOrthoFrame g x` (orthonormal at its own centre `x`):
`pureRFrozenEndoFib g m (smoothOrthoFrame g x) W x`. Its *value* is frame-free (a genuine `g`-metric
trace), so the differentiated tower built from it never differentiates a frame jet — the sound
replacement for the frozen-frame endomorphism. -/
private noncomputable def pureRGenuineEndoFib
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    (W : SmoothCcTensor g 0 (m + 1)) (x : M) :
    TensorRSSpace 0 (m + 1) I x :=
  pureRFrozenEndoFib (I := I) (M := M) g m (smoothOrthoFrame (I := I) g x) W x

/-- **On `smoothOrthoFrameNbhd x₀`, the moving-frame slot-`0` endomorphism fibre equals the
frozen-frame fibre against `smoothOrthoFrame g x₀`.** Both are the slot-`0` uncurry of a pure-Riemann
direction CLM; the moving frame `smoothOrthoFrame g y` is `g_y`-orthonormal at its own centre `y`, and
`smoothOrthoFrame g x₀` is `g_y`-orthonormal at `y` for `y ∈ smoothOrthoFrameNbhd x₀`; frame
independence (`pureRFrozenDirCLM_frame_independent`) identifies the two CLMs, hence the two endomorphism
fibres. -/
private lemma pureRGenuineEndoFib_eq_frozen_on_nbhd
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    (W : SmoothCcTensor g 0 (m + 1)) (x₀ : M) {y : M}
    (hy : y ∈ smoothOrthoFrameNbhd (I := I) (M := M) x₀) :
    pureRGenuineEndoFib (I := I) (M := M) g m W y =
      pureRFrozenEndoFib (I := I) (M := M) g m (smoothOrthoFrame (I := I) g x₀) W y := by
  rw [pureRGenuineEndoFib, pureRFrozenEndoFib, pureRFrozenEndoFib]
  refine congrArg (covGradBundleEquiv (I := I) (M := M) 0 m y) ?_
  exact pureRFrozenDirCLM_frame_independent (I := I) (M := M) g m W y
    (fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g y i j)
    (fun i j => smoothOrthoFrame_orthonormal (I := I) g x₀ hy i j)

/-- **Base-point smoothness of the moving-frame slot-`0` pure-Riemann endomorphism fibre field.** For a
closed smooth Riemannian manifold `(M, g)`, the `(0, m + 1)`-tensor fibre field
`x ↦ pureRGenuineEndoFib g m W x` is a smooth section. At each `x₀`, on `smoothOrthoFrameNbhd x₀` the
moving fibre equals the frozen fibre against `smoothOrthoFrame g x₀`
(`pureRGenuineEndoFib_eq_frozen_on_nbhd`), a smooth section (`pureRFrozenEndoFib_contMDiff`), and
`ContMDiffAt.congr_of_eventuallyEq` transfers smoothness. -/
private theorem pureRGenuineEndoFib_contMDiff
    (g : SmoothRiemannianMetric I M) (m : ℕ) (W : SmoothCcTensor g 0 (m + 1)) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 (m + 1) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 0 (m + 1) ℝ E)
        (E := fun z : M => TensorRSSpace 0 (m + 1) I z) x
        (pureRGenuineEndoFib (I := I) (M := M) g m W x)) := by
  classical
  intro x₀
  have h_fixed_at : ContMDiffAt I (I.prod 𝓘(ℝ, TensorRSModel 0 (m + 1) ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 (m + 1) ℝ E)
        (E := fun z : M => TensorRSSpace 0 (m + 1) I z) y
        (pureRFrozenEndoFib (I := I) (M := M) g m (smoothOrthoFrame (I := I) g x₀) W y)) x₀ :=
    pureRFrozenEndoFib_contMDiff (I := I) (M := M) g m
      (fun i => smoothOrthoFrame_smooth (I := I) g x₀ i) W x₀
  refine h_fixed_at.congr_of_eventuallyEq ?_
  filter_upwards [smoothOrthoFrameNbhd_mem_nhds (I := I) (M := M) x₀] with y hy
  exact congrArg (TotalSpace.mk' (TensorRSModel 0 (m + 1) ℝ E)
    (E := fun z : M => TensorRSSpace 0 (m + 1) I z) y)
    (pureRGenuineEndoFib_eq_frozen_on_nbhd (I := I) (M := M) g m W x₀ hy)

/-- **The order-`0` moving-frame pure-Riemann curvature endomorphism at rank `m + 1`**, a smooth
compactly-supported `(0, m + 1)`-tensor section: the moving-frame slot-`0` endomorphism
`pureRGenuineEndoFib`, frame-free in value, smooth (`pureRGenuineEndoFib_contMDiff`). -/
private noncomputable def pureRGenuineEndoSucc
    (g : SmoothRiemannianMetric I M) (m : ℕ) (W : SmoothCcTensor g 0 (m + 1)) :
    SmoothCcTensor g 0 (m + 1) where
  toSection :=
    { toFun := fun x : M => pureRGenuineEndoFib (I := I) (M := M) g m W x
      contMDiff_toFun := pureRGenuineEndoFib_contMDiff (I := I) (M := M) g m W }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

@[simp] private lemma pureRGenuineEndoSucc_toSection
    (g : SmoothRiemannianMetric I M) (m : ℕ) (W : SmoothCcTensor g 0 (m + 1)) (x : M) :
    (pureRGenuineEndoSucc (I := I) (M := M) g m W).toSection x =
      pureRGenuineEndoFib (I := I) (M := M) g m W x := rfl

/-- **The order-`0` moving-frame pure-Riemann curvature endomorphism at every rank** (totalised). For
rank `r = m + 1 ≥ 1` it is the genuine endomorphism `pureRGenuineEndoSucc`; for rank `0` (no slot-`0`
to read) it is the zero operator. The zero junk at rank `0` is never reached by the grid (the recursion
only increases the rank, starting from the base rank `s + 1`). -/
private noncomputable def pureRGenuineEndo0
    (g : SmoothRiemannianMetric I M) :
    ∀ (r : ℕ), SmoothCcTensor g 0 r → SmoothCcTensor g 0 r
  | 0 => fun _ => 0
  | (m + 1) => fun W => pureRGenuineEndoSucc (I := I) (M := M) g m W

/-- **The order-`p` differentiated moving-frame pure-Riemann curvature operator.** Acting on a smooth
compactly-supported `(0, r)`-tensor section `W`, the `p`-times covariantly-differentiated *frame-free*
pure-Riemann curvature endomorphism, defined recursively as the exact covariant-Leibniz remainder:

* `p = 0`: the order-`0` frame-free endomorphism `pureRGenuineEndo0 g r W`;
* `p + 1`: `∇(op p r W) − (rank-cast) op p (r + 1) (∇W)` — the differentiated curvature factor (the
  input section's derivative `∇W` cancels), rank-cast `(r + 1) + p = r + (p + 1)`.

By construction the single-step covariant Leibniz holds by `sub_add_cancel`. Since the order-`0` base is
frame-free in value, the differentiated tower differentiates only the curvature factor, never a frame
jet — the sound analogue of the unsound `pureRFrozenDiffOp`. -/
noncomputable def pureRGenuineDiffOp
    (g : SmoothRiemannianMetric I M) :
    ∀ (p r : ℕ), SmoothCcTensor g 0 r → SmoothCcTensor g 0 (r + p)
  | 0, r => fun W => pureRGenuineEndo0 (I := I) (M := M) g r W
  | (p + 1), r => fun W =>
      covGrad (I := I) (M := M) g 0 (r + p)
          (pureRGenuineDiffOp g p r W) -
        castRankCc_db g 0 (by omega : (r + 1) + p = r + (p + 1))
          (pureRGenuineDiffOp g p (r + 1) (covGrad (I := I) (M := M) g 0 r W))

/-- **The exact single-step covariant Leibniz of the differentiated moving-frame curvature tower.**
By the recursive definition, `∇(op p r W)` splits exactly into the higher-order remainder
`op (p + 1) r W` and the rank-cast lower-order term applied to `∇W`. Proved by `sub_add_cancel`. -/
private theorem covGrad_pureRGenuineDiffOp_eq
    (g : SmoothRiemannianMetric I M) (p r : ℕ) (W : SmoothCcTensor g 0 r) :
    covGrad (I := I) (M := M) g 0 (r + p) (pureRGenuineDiffOp (I := I) (M := M) g p r W) =
      pureRGenuineDiffOp (I := I) (M := M) g (p + 1) r W +
        castRankCc_db g 0 (by omega : (r + 1) + p = r + (p + 1))
          (pureRGenuineDiffOp (I := I) (M := M) g p (r + 1)
            (covGrad (I := I) (M := M) g 0 r W)) := by
  change _ = (covGrad (I := I) (M := M) g 0 (r + p)
      (pureRGenuineDiffOp (I := I) (M := M) g p r W) -
      castRankCc_db g 0 (by omega : (r + 1) + p = r + (p + 1))
        (pureRGenuineDiffOp (I := I) (M := M) g p (r + 1)
          (covGrad (I := I) (M := M) g 0 r W))) + _
  rw [sub_add_cancel]


/-- **The moving-frame pure-Riemann endomorphism fibre value depends `ℝ`-linearly on the section
value.** `pureRGenuineEndoFib g m (c₁ • W₁ + c₂ • W₂) x = c₁ • pureRGenuineEndoFib g m W₁ x +
c₂ • pureRGenuineEndoFib g m W₂ x`. The fibre reads its section only through the slot-`0` value
`(covGradBundleEquiv 0 m x).symm (W x) (B_iˣ)` (`pureRFrozenDirCLM_apply`), `ℝ`-linear in `W x`
(continuous-linear `.symm`, then the curvature CLM `riemannOp`), uncurried through the linear
`covGradBundleEquiv 0 m x`. -/
private lemma pureRGenuineEndoFib_linear
    (g : SmoothRiemannianMetric I M) (m : ℕ) (c₁ c₂ : ℝ)
    (W₁ W₂ : SmoothCcTensor g 0 (m + 1)) (x : M) :
    pureRGenuineEndoFib (I := I) (M := M) g m
        (c₁ • W₁ + c₂ • W₂) x =
      c₁ • pureRGenuineEndoFib (I := I) (M := M) g m W₁ x +
        c₂ • pureRGenuineEndoFib (I := I) (M := M) g m W₂ x := by
  classical
  rw [pureRGenuineEndoFib, pureRGenuineEndoFib, pureRGenuineEndoFib]
  rw [pureRFrozenEndoFib, pureRFrozenEndoFib, pureRFrozenEndoFib]
  rw [← map_smul (covGradBundleEquiv (I := I) (M := M) 0 m x) c₁,
    ← map_smul (covGradBundleEquiv (I := I) (M := M) 0 m x) c₂,
    ← map_add (covGradBundleEquiv (I := I) (M := M) 0 m x)]
  refine congrArg (covGradBundleEquiv (I := I) (M := M) 0 m x) ?_
  refine ContinuousLinearMap.ext (fun v => ?_)
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smul_apply,
    pureRFrozenDirCLM_apply, pureRFrozenDirCLM_apply, pureRFrozenDirCLM_apply,
    Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hval : (c₁ • W₁ + c₂ • W₂).toSection x =
      c₁ • W₁.toSection x + c₂ • W₂.toSection x := by
    rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply,
      SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply,
      SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply]
  rw [hval, map_add, map_smul, map_smul,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smul_apply, map_add, map_smul, map_smul]

/-- **The moving-frame pure-Riemann endomorphism fibre value is value-local.** If `W₁.toSection x =
W₂.toSection x` then `pureRGenuineEndoFib g m W₁ x = pureRGenuineEndoFib g m W₂ x`: the fibre reads its
section only through the slot-`0` value at `x`. -/
private lemma pureRGenuineEndoFib_local
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    (W₁ W₂ : SmoothCcTensor g 0 (m + 1)) (x : M)
    (hx : W₁.toSection x = W₂.toSection x) :
    pureRGenuineEndoFib (I := I) (M := M) g m W₁ x =
      pureRGenuineEndoFib (I := I) (M := M) g m W₂ x := by
  classical
  rw [pureRGenuineEndoFib, pureRGenuineEndoFib, pureRFrozenEndoFib, pureRFrozenEndoFib]
  refine congrArg (covGradBundleEquiv (I := I) (M := M) 0 m x) ?_
  refine ContinuousLinearMap.ext (fun v => ?_)
  rw [pureRFrozenDirCLM_apply, pureRFrozenDirCLM_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [hx]

/-- **The order-`0` moving-frame pure-Riemann curvature operator is a fibrewise curvature operator.**
The order-`0` base `pureRGenuineDiffOp 0 r = pureRGenuineEndo0 g r` is `ℝ`-linear in its section and
value-local: at rank `0` it is the zero operator; at rank `m + 1` its fibre value
`pureRGenuineEndoFib g m W x` reads its section only through the slot-`0` value at `x`
(`pureRGenuineEndoFib_linear`, `pureRGenuineEndoFib_local`) — the `IsOrderZeroCurvFactor` fingerprint
for the frame-free pure-Riemann tower. -/
private theorem pureRGenuineDiffOp_isOrderZeroCurvFactor (g : SmoothRiemannianMetric I M) :
    IsOrderZeroCurvFactor (I := I) (M := M) g (pureRGenuineDiffOp (I := I) (M := M) g) where
  linear := by
    intro r c₁ c₂ W₁ W₂ x
    cases r with
    | zero =>
        have h0 : ∀ W : SmoothCcTensor g 0 0,
            (pureRGenuineDiffOp (I := I) (M := M) g 0 0 W).toSection x =
              (0 : TensorRSSpace 0 (0 + 0) I x) := by
          intro W
          change (pureRGenuineEndo0 (I := I) (M := M) g 0 W).toSection x =
            (0 : TensorRSSpace 0 (0 + 0) I x)
          rw [show pureRGenuineEndo0 (I := I) (M := M) g 0 W = 0 from rfl,
            SmoothCcTensor.toSection_zero, ContMDiffSection.coe_zero]
          rfl
        rw [h0, h0, h0]
        simp
    | succ m =>
        rw [show (pureRGenuineDiffOp (I := I) (M := M) g 0 (m + 1) (c₁ • W₁ + c₂ • W₂)).toSection x =
              pureRGenuineEndoFib (I := I) (M := M) g m (c₁ • W₁ + c₂ • W₂) x from rfl,
          show (pureRGenuineDiffOp (I := I) (M := M) g 0 (m + 1) W₁).toSection x =
              pureRGenuineEndoFib (I := I) (M := M) g m W₁ x from rfl,
          show (pureRGenuineDiffOp (I := I) (M := M) g 0 (m + 1) W₂).toSection x =
              pureRGenuineEndoFib (I := I) (M := M) g m W₂ x from rfl,
          pureRGenuineEndoFib_linear (I := I) (M := M) g m c₁ c₂ W₁ W₂ x]
  local' := by
    intro r W₁ W₂ x hx
    cases r with
    | zero =>
        have h0 : ∀ W : SmoothCcTensor g 0 0,
            (pureRGenuineDiffOp (I := I) (M := M) g 0 0 W).toSection x =
              (0 : TensorRSSpace 0 (0 + 0) I x) := by
          intro W
          change (pureRGenuineEndo0 (I := I) (M := M) g 0 W).toSection x =
            (0 : TensorRSSpace 0 (0 + 0) I x)
          rw [show pureRGenuineEndo0 (I := I) (M := M) g 0 W = 0 from rfl,
            SmoothCcTensor.toSection_zero, ContMDiffSection.coe_zero]
          rfl
        rw [h0, h0]
    | succ m =>
        rw [show (pureRGenuineDiffOp (I := I) (M := M) g 0 (m + 1) W₁).toSection x =
              pureRGenuineEndoFib (I := I) (M := M) g m W₁ x from rfl,
          show (pureRGenuineDiffOp (I := I) (M := M) g 0 (m + 1) W₂).toSection x =
              pureRGenuineEndoFib (I := I) (M := M) g m W₂ x from rfl,
          pureRGenuineEndoFib_local (I := I) (M := M) g m W₁ W₂ x hx]

/-- **The fibre version of the pure-Riemann curvature direction CLM reading a single tensor.** Reads
the slot-`0` direction of a single `(0, m + 1)`-tensor `τ` along each frame vector `B_iˣ` and contracts
it through the curvature operator `R(B_iˣ, ·)`, exactly as `pureRFrozenDirCLM` reads the section value
`W x`; it is the section-free reading needed to factor the order-`0` endomorphism through a fixed fibre
operator. -/
private noncomputable def pureRDirCLMTensor
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (x : M) (τ : TensorRSSpace 0 (m + 1) I x) :
    TangentSpace I x →L[ℝ] TensorRSSpace 0 m I x :=
  ∑ i : Fin (Module.finrank ℝ E),
    (haveI : T2Space (TangentSpace I x) := inferInstanceAs (T2Space E)
     haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
     LinearMap.toContinuousLinearMap
      { toFun := fun v => riemannOp (tensorCov (I := I) g 0 m) x (B i x) v
          ((covGradBundleEquiv (I := I) (M := M) 0 m x).symm τ (B i x))
        map_add' := fun v v' => by
          rw [map_add (riemannOp (tensorCov (I := I) g 0 m) x (B i x)) v v']; rfl
        map_smul' := fun c v => by
          rw [map_smul (riemannOp (tensorCov (I := I) g 0 m) x (B i x)) c v]; rfl })

set_option linter.unusedSectionVars false in
/-- The defining apply formula for `pureRDirCLMTensor`. -/
private lemma pureRDirCLMTensor_apply
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (x : M) (τ : TensorRSSpace 0 (m + 1) I x) (v : TangentSpace I x) :
    pureRDirCLMTensor (I := I) (M := M) g m B x τ v =
      ∑ i : Fin (Module.finrank ℝ E),
        riemannOp (tensorCov (I := I) g 0 m) x (B i x) v
          ((covGradBundleEquiv (I := I) (M := M) 0 m x).symm τ (B i x)) := by
  classical
  rw [pureRDirCLMTensor, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk]

set_option linter.unusedSectionVars false in
/-- **The moving-frame pure-Riemann direction CLM is the single-tensor reading of the section value.**
`pureRFrozenDirCLM g m B (W.toSection) x = pureRDirCLMTensor g m B x (W.toSection x)`: both unfold to
the same frame sum of curvature contractions of the slot-`0` reading of `W x`. -/
private lemma pureRFrozenDirCLM_eq_pureRDirCLMTensor
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (W : SmoothCcTensor g 0 (m + 1)) (x : M) :
    pureRFrozenDirCLM (I := I) (M := M) g m B (fun y : M => W.toSection y) x =
      pureRDirCLMTensor (I := I) (M := M) g m B x (W.toSection x) := by
  refine ContinuousLinearMap.ext (fun v => ?_)
  rw [pureRFrozenDirCLM_apply, pureRDirCLMTensor_apply]

set_option linter.unusedSectionVars false in
/-- **Source-rank-`0` Hom-bundle curvature naturality (single fibre).** For the `(0, m)`-tensor
curvature operator `riemannOp (tensorCov g 0 m)` applied to a `(0, m)`-rank tensor `Ξ` (a CLM
`Tensor0S0 → Tensor0Sm`), reading the result at a `(0, 0)`-tensor `d` recovers the abstract
`(0, m)`-tensor curvature on `Ξ d`:
`(R^{(0,m)}_x(v, w) Ξ) d = riemannOp (tensor0SCov m) x v w (Ξ d)`. The scalar source-curvature
`R^{(0,0)}` vanishes (`riemannSec_tensor0SCov_zero_eq_zero`); the proof converts both bundled
curvatures to `riemannSec`s through smooth extensions (`riemannOp_apply_smooth`) and applies the generic
Hom curvature–Leibniz rule `riemannSec_homBundleGen_apply_eq` with vanishing source term. -/
private theorem riemannOp_tensorCov_homNatural
    (g : SmoothRiemannianMetric I M) (m : ℕ) (x : M) (v w : TangentSpace I x)
    (Ξ : TensorRSSpace 0 m I x) (d : Tensor0SSpace 0 I x) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace m I x from
        riemannOp (tensorCov (I := I) g 0 m) x v w Ξ) d =
      riemannOp (Tensor0SNabla.tensor0SCovariantDerivative I M m (LeviCivita (I := I) g)) x v w
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace m I x from Ξ) d) := by
  classical
  set X : Π y : M, TangentSpace I y := smoothExtensionTangent (I := I) x v with hX_def
  set Wfield : Π y : M, TangentSpace I y := smoothExtensionTangent (I := I) x w with hW_def
  have hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X) :=
    smoothExtensionTangent_contMDiff (I := I) x v
  have hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Wfield) :=
    smoothExtensionTangent_contMDiff (I := I) x w
  have hXx : X x = v := smoothExtensionTangent_eq (I := I) x v
  have hWx : Wfield x = w := smoothExtensionTangent_eq (I := I) x w
  obtain ⟨Ξsec, hΞx⟩ := ContMDiffSection.exists_eq_at (I := I)
    (F := TensorRSModel 0 m ℝ E) (V := fun y : M => TensorRSSpace 0 m I y) (n := (⊤ : ℕ∞)) x Ξ
  obtain ⟨dSec, hdSec⟩ := ContMDiffSection.exists_eq_at (I := I)
    (F := Tensor0SModel 0 ℝ E) (V := fun y : M => Tensor0SSpace 0 I y) (n := (⊤ : ℕ∞)) x d
  have hΞd_smooth : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel m ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel m ℝ E)
        (E := fun z : M => Tensor0SSpace m I z) y
        ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace m I y from Ξsec y) (dSec y))) :=
    ContMDiff.clm_bundle_apply (b := id) Ξsec.contMDiff dSec.contMDiff
  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace m I x from
        riemannOp (tensorCov (I := I) g 0 m) x v w Ξ) d =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace m I x from
        riemannSec (tensorCov (I := I) g 0 m) (fun b => X b) (fun b => Wfield b)
          (fun b => Ξsec b) x) (dSec x) from by
    rw [← hXx, ← hWx, ← hΞx,
      riemannOp_apply_smooth (cov := tensorCov (I := I) g 0 m) hX hW Ξsec.contMDiff]
    rw [show d = dSec x from hdSec.symm]]
  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace m I x from
        riemannSec (tensorCov (I := I) g 0 m) (fun b => X b) (fun b => Wfield b)
          (fun b => Ξsec b) x) (dSec x) =
      riemannSec (Tensor0SNabla.tensor0SCovariantDerivative I M m (LeviCivita (I := I) g))
          (fun b => X b) (fun b => Wfield b)
          (HomConnectionGen.pairedSection (M := M) (U := fun z : M => Tensor0SSpace 0 I z)
            (V := fun z : M => Tensor0SSpace m I z)
            (fun b => Ξsec b) (fun b => dSec b)) x -
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace m I x from Ξsec x)
          (riemannSec (Tensor0SNabla.tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g))
            (fun b => X b) (fun b => Wfield b) (fun b => dSec b) x) from
    HomConnectionGen.riemannSec_homBundleGen_apply_eq I M
      (Tensor0SModel 0 ℝ E) (fun z : M => Tensor0SSpace 0 I z)
      (Tensor0SModel m ℝ E) (fun z : M => Tensor0SSpace m I z)
      (Tensor0SNabla.tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g))
      (Tensor0SNabla.tensor0SCovariantDerivative I M m (LeviCivita (I := I) g))
      ⟨fun b => X b, hX⟩ ⟨fun b => Wfield b, hW⟩ Ξsec dSec x]
  rw [show riemannSec (Tensor0SNabla.tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g))
        (fun b => X b) (fun b => Wfield b) (fun b => dSec b) x = 0 from
    riemannSec_tensor0SCov_zero_eq_zero (I := I) (M := M) g ⟨fun b => X b, hX⟩
      ⟨fun b => Wfield b, hW⟩ (fun b => dSec b) dSec.contMDiff x]
  rw [map_zero, sub_zero]
  rw [show riemannOp (Tensor0SNabla.tensor0SCovariantDerivative I M m (LeviCivita (I := I) g)) x v w
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace m I x from Ξ) d) =
      riemannSec (Tensor0SNabla.tensor0SCovariantDerivative I M m (LeviCivita (I := I) g))
          (fun b => X b) (fun b => Wfield b)
          (HomConnectionGen.pairedSection (M := M) (U := fun z : M => Tensor0SSpace 0 I z)
            (V := fun z : M => Tensor0SSpace m I z)
            (fun b => Ξsec b) (fun b => dSec b)) x from by
    rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace m I x from Ξ) d =
        HomConnectionGen.pairedSection (M := M) (U := fun z : M => Tensor0SSpace 0 I z)
          (V := fun z : M => Tensor0SSpace m I z)
          (fun b => Ξsec b) (fun b => dSec b) x from by
      rw [HomConnectionGen.pairedSection_apply, show d = dSec x from hdSec.symm, hΞx]]
    rw [← hXx, ← hWx]
    exact riemannOp_apply_smooth
      (cov := Tensor0SNabla.tensor0SCovariantDerivative I M m (LeviCivita (I := I) g)) hX hW
      hΞd_smooth]

set_option linter.unusedSectionVars false in
/-- **The slot-reading bridge.** The slot-`0` reading of `(covGradBundleEquiv 0 m x).symm τ` along
`w`, applied to the `(0, 0)`-tensor `d`, equals the slot-`0` curry of `τ d` along `w`:
`((covGradBundleEquiv 0 m x).symm τ w) d = tensor0S_curry m x (τ d) w`. Both evaluate on `v'` to
`toModel (τ d) (cons w v')` (`covGradBundleEquiv_symm_apply_eval`, `tensor0S_curry_apply_eval`). -/
private lemma covGradBundleEquiv_symm_apply_eq_curry
    (m : ℕ) (x : M)
    (τ : TensorRSSpace 0 (m + 1) I x) (w : TangentSpace I x) (d : Tensor0SSpace 0 I x) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace m I x from
      ((covGradBundleEquiv (I := I) (M := M) 0 m x).symm τ) w) d =
      tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) m x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from τ) d) w := by
  apply tensor0SSpace_ext (𝕜 := ℝ) m x
  intro v'
  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace m I x from
        ((covGradBundleEquiv (I := I) (M := M) 0 m x).symm τ) w) d v' =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace m I x from
          ((covGradBundleEquiv (I := I) (M := M) 0 m x).symm τ) w) d) v' from rfl]
  rw [covGradBundleEquiv_symm_apply_eval (I := I) (M := M) 0 m x τ w d v']
  rw [show tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) m x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from τ) d) w v' =
      Tensor0SSpace.toModel
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) m x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from τ) d) w) v' from rfl]
  rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from τ) d) w v']

set_option linter.unusedSectionVars false in
/-- **The slot-`0` pure-Riemann endomorphism value reads its tensor only through the slot-`0` slice of
`τ d`.** Evaluated at the `(0, 0)`-tensor `d` on a tuple `v`, the uncurry of `pureRDirCLMTensor g m B x τ`
through `covGradBundleEquiv` is the frame sum of abstract `(0, m)`-tensor curvature values
`R^{(0,m)}(B_iˣ, v 0)(tensor0S_curry m x (τ d) (B_iˣ))`, read on `tail v` — depending on `τ` solely
through `τ d`. From `covGradBundleEquiv_apply_eval`, the single-fibre Hom naturality
`riemannOp_tensorCov_homNatural`, and the slot-reading bridge
`covGradBundleEquiv_symm_apply_eq_curry`. -/
private lemma pureRDirCLMTensor_covGradEquiv_eval
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (x : M) (τ : TensorRSSpace 0 (m + 1) I x) (d : Tensor0SSpace 0 I x)
    (v : Fin (m + 1) → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from
          covGradBundleEquiv (I := I) (M := M) 0 m x
            (pureRDirCLMTensor (I := I) (M := M) g m B x τ)) d) v =
      ∑ i : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel
          (riemannOp (Tensor0SNabla.tensor0SCovariantDerivative I M m (LeviCivita (I := I) g)) x
            (B i x) (v 0)
            (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) m x
              ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from τ) d) (B i x)))
          (Matrix.vecTail v) := by
  classical
  rw [covGradBundleEquiv_apply_eval (I := I) (M := M) 0 m x
    (pureRDirCLMTensor (I := I) (M := M) g m B x τ) d v]
  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace m I x from
        pureRDirCLMTensor (I := I) (M := M) g m B x τ (v 0)) d =
      (∑ i : Fin (Module.finrank ℝ E),
        riemannOp (tensorCov (I := I) g 0 m) x (B i x) (v 0)
          ((covGradBundleEquiv (I := I) (M := M) 0 m x).symm τ (B i x))) d from by
    rw [pureRDirCLMTensor_apply (I := I) (M := M) g m B x τ (v 0)]]
  rw [ContinuousLinearMap.sum_apply, ← Tensor0SSpace.toModelL_apply, map_sum,
    ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Tensor0SSpace.toModelL_apply]
  rw [riemannOp_tensorCov_homNatural (I := I) (M := M) g m x (B i x) (v 0)
    ((covGradBundleEquiv (I := I) (M := M) 0 m x).symm τ (B i x)) d]
  rw [covGradBundleEquiv_symm_apply_eq_curry (I := I) (M := M) m x τ (B i x) d]

set_option linter.unusedSectionVars false in
/-- **The slot-`0` pure-Riemann fibre value of a single tensor, read at the unit.** For a single
`(0, m + 1)`-tensor `S` and a tuple `v`, the unit-read uncurry of
`pureRDirCLMTensor g m B x (unitScalarRSLift x S)` is the frame sum of abstract `(0, m)`-tensor
curvature values `R^{(0,m)}(B_iˣ, v 0)(tensor0S_curry m x S (B_iˣ))` on `tail v`. Specialisation of
`pureRDirCLMTensor_covGradEquiv_eval` at `τ = unitScalarRSLift x S`, `d = unitZeroSec`, using the unit
round-trip `unitScalarRSLift_apply_unit`. -/
private lemma pureREndoOpFibVal_eval
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (x : M) (S : Tensor0SSpace (m + 1) I x) (v : Fin (m + 1) → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from
          covGradBundleEquiv (I := I) (M := M) 0 m x
            (pureRDirCLMTensor (I := I) (M := M) g m B x
              (unitScalarRSLift (I := I) (M := M) x S)))
          (unitZeroSec (I := I) (M := M) x)) v =
      ∑ i : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel
          (riemannOp (Tensor0SNabla.tensor0SCovariantDerivative I M m (LeviCivita (I := I) g)) x
            (B i x) (v 0)
            (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) m x S (B i x)))
          (Matrix.vecTail v) := by
  rw [pureRDirCLMTensor_covGradEquiv_eval (I := I) (M := M) g m B x
    (unitScalarRSLift (I := I) (M := M) x S) (unitZeroSec (I := I) (M := M) x) v]
  rw [unitScalarRSLift_apply_unit (I := I) (M := M) x S]

set_option linter.unusedSectionVars false in
/-- **The fibre pure-Riemann endomorphism operator at rank `m + 1`.** The fixed fibre operator
`Φ₀ (m + 1) x : T0S(m+1) →L T0S(m+1)` post-composed with a section value to recover the order-`0`
endomorphism: on a single `(0, m + 1)`-tensor `S`, `pureREndoOpFib g m x S` is the unit-read uncurry of
`pureRDirCLMTensor g m (smoothOrthoFrame g x) x (unitScalarRSLift x S)`. It is `ℝ`-linear in `S` (the
value formula `pureREndoOpFibVal_eval` is linear in `S` through the currying equivalence
`tensor0S_curry`), closed to a continuous-linear map on the finite-dimensional fibre. -/
private noncomputable def pureREndoOpFib
    (g : SmoothRiemannianMetric I M) (m : ℕ) (x : M) :
    Tensor0SSpace (m + 1) I x →L[ℝ] Tensor0SSpace (m + 1) I x :=
  haveI : FiniteDimensional ℝ (Tensor0SSpace (m + 1) I x) := inferInstance
  LinearMap.toContinuousLinearMap
    { toFun := fun S =>
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from
          covGradBundleEquiv (I := I) (M := M) 0 m x
            (pureRDirCLMTensor (I := I) (M := M) g m (smoothOrthoFrame (I := I) g x) x
              (unitScalarRSLift (I := I) (M := M) x S)))
          (unitZeroSec (I := I) (M := M) x)
      map_add' := fun S S' => by
        apply tensor0SSpace_ext (𝕜 := ℝ) (m + 1) x
        intro v
        rw [show (show Tensor0SSpace (m + 1) I x from
                (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from
                  covGradBundleEquiv (I := I) (M := M) 0 m x
                    (pureRDirCLMTensor (I := I) (M := M) g m (smoothOrthoFrame (I := I) g x) x
                      (unitScalarRSLift (I := I) (M := M) x (S + S'))))
                  (unitZeroSec (I := I) (M := M) x)) v =
              Tensor0SSpace.toModel
                ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from
                  covGradBundleEquiv (I := I) (M := M) 0 m x
                    (pureRDirCLMTensor (I := I) (M := M) g m (smoothOrthoFrame (I := I) g x) x
                      (unitScalarRSLift (I := I) (M := M) x (S + S'))))
                  (unitZeroSec (I := I) (M := M) x)) v from rfl,
          show (show Tensor0SSpace (m + 1) I x from
                (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from
                  covGradBundleEquiv (I := I) (M := M) 0 m x
                    (pureRDirCLMTensor (I := I) (M := M) g m (smoothOrthoFrame (I := I) g x) x
                      (unitScalarRSLift (I := I) (M := M) x S)))
                  (unitZeroSec (I := I) (M := M) x) +
                (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from
                  covGradBundleEquiv (I := I) (M := M) 0 m x
                    (pureRDirCLMTensor (I := I) (M := M) g m (smoothOrthoFrame (I := I) g x) x
                      (unitScalarRSLift (I := I) (M := M) x S')))
                  (unitZeroSec (I := I) (M := M) x)) v =
              Tensor0SSpace.toModel
                  ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from
                    covGradBundleEquiv (I := I) (M := M) 0 m x
                      (pureRDirCLMTensor (I := I) (M := M) g m (smoothOrthoFrame (I := I) g x) x
                        (unitScalarRSLift (I := I) (M := M) x S)))
                    (unitZeroSec (I := I) (M := M) x)) v +
                Tensor0SSpace.toModel
                  ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from
                    covGradBundleEquiv (I := I) (M := M) 0 m x
                      (pureRDirCLMTensor (I := I) (M := M) g m (smoothOrthoFrame (I := I) g x) x
                        (unitScalarRSLift (I := I) (M := M) x S')))
                    (unitZeroSec (I := I) (M := M) x)) v from rfl]
        rw [pureREndoOpFibVal_eval (I := I) (M := M) g m (smoothOrthoFrame (I := I) g x) x (S + S') v,
          pureREndoOpFibVal_eval (I := I) (M := M) g m (smoothOrthoFrame (I := I) g x) x S v,
          pureREndoOpFibVal_eval (I := I) (M := M) g m (smoothOrthoFrame (I := I) g x) x S' v,
          ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [show tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) m x (S + S')
                (smoothOrthoFrame (I := I) g x i x) =
              tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) m x S (smoothOrthoFrame (I := I) g x i x) +
                tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) m x S'
                  (smoothOrthoFrame (I := I) g x i x) from by
          rw [map_add (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) m x),
            ContinuousLinearMap.add_apply]]
        rw [map_add (riemannOp (Tensor0SNabla.tensor0SCovariantDerivative I M m (LeviCivita (I := I) g))
          x (smoothOrthoFrame (I := I) g x i x) (v 0)), Tensor0SSpace.toModel_add,
          ContinuousMultilinearMap.add_apply]
      map_smul' := fun c S => by
        apply tensor0SSpace_ext (𝕜 := ℝ) (m + 1) x
        intro v
        rw [show (show Tensor0SSpace (m + 1) I x from
                (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from
                  covGradBundleEquiv (I := I) (M := M) 0 m x
                    (pureRDirCLMTensor (I := I) (M := M) g m (smoothOrthoFrame (I := I) g x) x
                      (unitScalarRSLift (I := I) (M := M) x (c • S))))
                  (unitZeroSec (I := I) (M := M) x)) v =
              Tensor0SSpace.toModel
                ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from
                  covGradBundleEquiv (I := I) (M := M) 0 m x
                    (pureRDirCLMTensor (I := I) (M := M) g m (smoothOrthoFrame (I := I) g x) x
                      (unitScalarRSLift (I := I) (M := M) x (c • S))))
                  (unitZeroSec (I := I) (M := M) x)) v from rfl,
          show (show Tensor0SSpace (m + 1) I x from
                (RingHom.id ℝ) c • (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from
                  covGradBundleEquiv (I := I) (M := M) 0 m x
                    (pureRDirCLMTensor (I := I) (M := M) g m (smoothOrthoFrame (I := I) g x) x
                      (unitScalarRSLift (I := I) (M := M) x S)))
                  (unitZeroSec (I := I) (M := M) x)) v =
              c • Tensor0SSpace.toModel
                  ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from
                    covGradBundleEquiv (I := I) (M := M) 0 m x
                      (pureRDirCLMTensor (I := I) (M := M) g m (smoothOrthoFrame (I := I) g x) x
                        (unitScalarRSLift (I := I) (M := M) x S)))
                    (unitZeroSec (I := I) (M := M) x)) v from rfl]
        rw [pureREndoOpFibVal_eval (I := I) (M := M) g m (smoothOrthoFrame (I := I) g x) x (c • S) v,
          pureREndoOpFibVal_eval (I := I) (M := M) g m (smoothOrthoFrame (I := I) g x) x S v,
          Finset.smul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [show tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) m x (c • S)
                (smoothOrthoFrame (I := I) g x i x) =
              c • tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) m x S
                (smoothOrthoFrame (I := I) g x i x) from by
          rw [map_smul (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) m x),
            ContinuousLinearMap.smul_apply]]
        rw [map_smul (riemannOp (Tensor0SNabla.tensor0SCovariantDerivative I M m (LeviCivita (I := I) g))
          x (smoothOrthoFrame (I := I) g x i x) (v 0)), Tensor0SSpace.toModel_smul,
          ContinuousMultilinearMap.smul_apply] }

set_option linter.unusedSectionVars false in
/-- The defining apply formula for `pureREndoOpFib`. -/
private lemma pureREndoOpFib_apply
    (g : SmoothRiemannianMetric I M) (m : ℕ) (x : M) (S : Tensor0SSpace (m + 1) I x) :
    pureREndoOpFib (I := I) (M := M) g m x S =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from
        covGradBundleEquiv (I := I) (M := M) 0 m x
          (pureRDirCLMTensor (I := I) (M := M) g m (smoothOrthoFrame (I := I) g x) x
            (unitScalarRSLift (I := I) (M := M) x S)))
        (unitZeroSec (I := I) (M := M) x) := by
  rw [pureREndoOpFib, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk]

set_option linter.unusedSectionVars false in
/-- **The order-`0` endomorphism factors as post-composition by `pureREndoOpFib`.** For a smooth
section `W`, `pureRGenuineEndoFib g m W x = (pureREndoOpFib g m x).comp (W x)` (as `(0, m + 1)`-rank
tensors `T0S(0) →L T0S(m+1)`). Tested on a `(0, 0)`-tensor `d`, both sides have the same `toModel`
value: by `pureRDirCLMTensor_covGradEquiv_eval` (twice), each reads the slot-`0` curry of the same
`(0, m + 1)`-tensor `W x d` — the LHS through the moving section `W`, the RHS through the unit lift of
`W x d`. -/
private lemma pureRGenuineEndoFib_eq_comp
    (g : SmoothRiemannianMetric I M) (m : ℕ) (W : SmoothCcTensor g 0 (m + 1)) (x : M) :
    pureRGenuineEndoFib (I := I) (M := M) g m W x =
      TensorRSSpace.ofCLM
        ((pureREndoOpFib (I := I) (M := M) g m x).comp
          (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from W.toSection x)) := by
  apply tensorRSSpace_ext (𝕜 := ℝ) 0 (m + 1) x
  intro d
  apply tensor0SSpace_ext (𝕜 := ℝ) (m + 1) x
  intro v

  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from
        pureRGenuineEndoFib (I := I) (M := M) g m W x) d v =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from
          covGradBundleEquiv (I := I) (M := M) 0 m x
            (pureRDirCLMTensor (I := I) (M := M) g m (smoothOrthoFrame (I := I) g x) x
              (W.toSection x))) d) v from by
    rw [pureRGenuineEndoFib, pureRFrozenEndoFib,
      pureRFrozenDirCLM_eq_pureRDirCLMTensor (I := I) (M := M) g m
        (smoothOrthoFrame (I := I) g x) W x]
    rfl]
  rw [pureRDirCLMTensor_covGradEquiv_eval (I := I) (M := M) g m (smoothOrthoFrame (I := I) g x) x
    (W.toSection x) d v]

  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from
        TensorRSSpace.ofCLM
          ((pureREndoOpFib (I := I) (M := M) g m x).comp
            (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from W.toSection x))) d v =
      Tensor0SSpace.toModel
        (pureREndoOpFib (I := I) (M := M) g m x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from W.toSection x) d)) v from rfl]
  rw [pureREndoOpFib_apply (I := I) (M := M) g m x
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from W.toSection x) d)]
  rw [pureRDirCLMTensor_covGradEquiv_eval (I := I) (M := M) g m (smoothOrthoFrame (I := I) g x) x
    (unitScalarRSLift (I := I) (M := M) x
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from W.toSection x) d))
    (unitZeroSec (I := I) (M := M) x) v]
  rw [unitScalarRSLift_apply_unit (I := I) (M := M) x
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from W.toSection x) d)]

set_option linter.unusedSectionVars false in
/-- **The order-`0` moving-frame pure-Riemann operator trace value is the frame-summed bundle curvature
contraction of the slot-`0` slice (the frame-free `∑ᵢ R(Bᵢ, ·)`-trace value anatomy).** For a smooth
compactly-supported `(0, m + 1)`-tensor `W`, base point `x`, and tuple `v`, the unit-evaluated value of
the order-`0` pure-Riemann curvature operator `pureRGenuineDiffOp g 0 (m + 1) W` is the moving-frame sum
(over `Bᵢ := smoothOrthoFrame g x i`, orthonormal at `x`) of the `(0, m)`-tensor bundle curvature
`riemannOp (tensor0SCov m)` evaluated in the leading curvature direction `Bᵢ` and the gradient direction
`v 0`, contracted against the slot-`0` slice `slot0_{Bᵢ} W := tensor0S_curry m x (W(x) ⟨unit⟩) (Bᵢ)` of `W`
(the unit-read curry of `W` along `Bᵢ`), read on the trailing tuple:
```
(pureRGenuineDiffOp g 0 (m + 1) W)(x)(unit)(v)
  = ∑ᵢ toModel(R^{(0,m)}(Bᵢ, v 0)(slot0_{Bᵢ} W))(tail v).
```
This is the explicit `riemannOp`-trace value of the operator-field carrier `appCc (Φ₀ (m + 1)) W =
pureRGenuineDiffOp g 0 (m + 1) W` (the `Classical.choose` base spec defining `curvOpField`): it pins
*what* the choose-spec carries — the frame-summed bundle curvature trace `∑ᵢ R(Bᵢ, ·)` acting through the
slot-`0` reading of `W`, built from `g` and the Levi-Civita curvature alone (no
`smoothExtensionTangent` jet). It is frame-free in value (`pureRFrozenDirCLM_frame_independent`), the
sound order-`0` content whose covariant derivative is the differentiated trace `(∇R) W`.

**Proof.** The fibre value `(pureRGenuineDiffOp g 0 (m + 1) W)(x) = pureRGenuineEndoFib g m W x` (the
order-`0` base, `m + 1` branch) is the slot-`0` uncurry through `covGradBundleEquiv` of the moving-frame
pure-Riemann direction CLM (`pureRGenuineEndoFib`, `pureRFrozenEndoFib`,
`pureRFrozenDirCLM_eq_pureRDirCLMTensor`); the value formula `pureRDirCLMTensor_covGradEquiv_eval` reads
that uncurry as the frame sum of bundle curvature contractions of `tensor0S_curry m x (W x) (Bᵢ)`. -/
theorem pureRGenuineDiffOp_zero_succ_toSection_unit_eval
    (g : SmoothRiemannianMetric I M) (m : ℕ) (W : SmoothCcTensor g 0 (m + 1)) (x : M)
    (v : Fin (m + 1) → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from
          (pureRGenuineDiffOp (I := I) (M := M) g 0 (m + 1) W).toSection x)
          (unitZeroSec (I := I) (M := M) x)) v =
      ∑ i : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel
          (riemannOp (Tensor0SNabla.tensor0SCovariantDerivative I M m (LeviCivita (I := I) g)) x
            (smoothOrthoFrame (I := I) g x i x) (v 0)
            (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) m x
              ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from W.toSection x)
                (unitZeroSec (I := I) (M := M) x))
              (smoothOrthoFrame (I := I) g x i x)))
          (Matrix.vecTail v) := by
  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from
        (pureRGenuineDiffOp (I := I) (M := M) g 0 (m + 1) W).toSection x) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from
        covGradBundleEquiv (I := I) (M := M) 0 m x
          (pureRDirCLMTensor (I := I) (M := M) g m (smoothOrthoFrame (I := I) g x) x
            (W.toSection x))) from by
    change (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from
        pureRGenuineEndoFib (I := I) (M := M) g m W x) = _
    rw [pureRGenuineEndoFib, pureRFrozenEndoFib,
      pureRFrozenDirCLM_eq_pureRDirCLMTensor (I := I) (M := M) g m
        (smoothOrthoFrame (I := I) g x) W x]]
  rw [pureRDirCLMTensor_covGradEquiv_eval (I := I) (M := M) g m (smoothOrthoFrame (I := I) g x) x
    (W.toSection x) (unitZeroSec (I := I) (M := M) x) v]

set_option linter.unusedSectionVars false in
/-- **Base-point smoothness of the rank-`m + 1` pure-Riemann endomorphism operator field.** The
`(m + 1, m + 1)`-tensor fibre field `x ↦ pureREndoOpFib g m x` is a smooth section of the operator
bundle. By `contMDiff_clm_section_of_pointwise` it suffices to show, for every smooth
`(0, m + 1)`-tensor section `Z`, that `x ↦ pureREndoOpFib g m x (Z x)` is smooth; this equals
`x ↦ pureRGenuineEndoFib g m (lift Z) x (unit)` — the smooth order-`0` endomorphism field
(`pureRGenuineEndoFib_contMDiff`) of the unit-scalar lift `lift Z` evaluated at the smooth unit
`(0, 0)`-tensor (`ContMDiff.clm_bundle_apply`). -/
private theorem pureREndoOp_contMDiff (g : SmoothRiemannianMetric I M) (m : ℕ) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel (m + 1) (m + 1) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel (m + 1) (m + 1) ℝ E)
        (E := fun z : M => TensorRSSpace (m + 1) (m + 1) I z)
        x (TensorRSSpace.ofCLM (pureREndoOpFib (I := I) (M := M) g m x))) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SModel (m + 1) ℝ E) (V₁ := fun x : M => Tensor0SSpace (m + 1) I x)
    (F₂ := Tensor0SModel (m + 1) ℝ E) (V₂ := fun x : M => Tensor0SSpace (m + 1) I x)
    (φ := fun x => (show Tensor0SSpace (m + 1) I x →L[ℝ] Tensor0SSpace (m + 1) I x from
      pureREndoOpFib (I := I) (M := M) g m x))
  intro Z
  set Wσ : SmoothCcTensor g 0 (m + 1) :=
    ⟨unitScalarRSLiftCₛ (I := I) (M := M) Z, HasCompactSupport.of_compactSpace _⟩ with hWσ_def

  have hpt : ∀ x : M, pureREndoOpFib (I := I) (M := M) g m x (Z x) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from
        pureRGenuineEndoFib (I := I) (M := M) g m Wσ x) (unitZeroSec (I := I) (M := M) x) := by
    intro x
    rw [pureREndoOpFib_apply (I := I) (M := M) g m x (Z x)]
    rw [pureRGenuineEndoFib, pureRFrozenEndoFib,
      pureRFrozenDirCLM_eq_pureRDirCLMTensor (I := I) (M := M) g m
        (smoothOrthoFrame (I := I) g x) Wσ x]
    rfl
  have hWσ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 (m + 1) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 0 (m + 1) ℝ E)
        (E := fun z : M => TensorRSSpace 0 (m + 1) I z) x
        (pureRGenuineEndoFib (I := I) (M := M) g m Wσ x)) :=
    pureRGenuineEndoFib_contMDiff (I := I) (M := M) g m Wσ
  have heval : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel (m + 1) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel (m + 1) ℝ E)
        (E := fun z : M => Tensor0SSpace (m + 1) I z) x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from
          pureRGenuineEndoFib (I := I) (M := M) g m Wσ x)
          (unitZeroSec (I := I) (M := M) x))) :=
    ContMDiff.clm_bundle_apply (b := id) hWσ (unitZeroSec (I := I) (M := M)).contMDiff
  refine heval.congr ?_
  intro x
  exact (congrArg (TotalSpace.mk' (Tensor0SModel (m + 1) ℝ E)
    (E := fun z : M => Tensor0SSpace (m + 1) I z) x) (hpt x)).symm ▸ rfl

/-- **The order-`0` moving-frame pure-Riemann curvature operator is a fixed-operator-field action.** For
each covariant rank `r` there is a *fixed* smooth `(r, r)`-operator field `Φ₀ r` such that the order-`0`
frame-free endomorphism is its operator-field action on the section:
`pureRGenuineDiffOp 0 r W = appCc (Φ₀ r) W` for every `W`.

**Mathematical content (sound, not packaging, frame-free).** At rank `0` the order-`0` operator is the
zero operator (`pureRGenuineEndo0`, the `r = 0` branch), matched by `Φ₀ 0 = 0` (`appCc 0 W = 0`). At
rank `m + 1` the fibre value `pureRGenuineEndoFib g m W x` is the slot-`0` uncurry of the pure-Riemann
direction CLM against the moving frame `smoothOrthoFrame g x`; its *value* is frame-free (a genuine
`g`-metric trace, `pureRFrozenDirCLM_frame_independent`), `ℝ`-linear and value-local in the slot-`0`
reading of `W x` (`pureRGenuineEndoFib_linear`, `pureRGenuineEndoFib_local`), so it factors as a fixed
fibrewise operator `Φ₀ (m + 1) x : T0S(m+1) →L T0S(m+1)` post-composed with `W x` — exactly the
operator-field action `appCc (Φ₀ (m + 1)) W`.  Because the value is frame-free, `Φ₀` is a fixed smooth
curvature-coefficient field (built from `g, R` alone), never a chart-selection-unbounded frame jet.

This isolates the order-`0` curvature content — the single per-tower input the abstract operator-field
normal-form engine (`OperatorFieldDifferentiatedTowerNormalForm`) needs to deliver the high-order jet
envelope.  The genuinely-irreducible packaging here is the base-point smoothness of the frame-free
curvature endomorphism field `Φ₀ r`; it is the precise atomic node disclosed as a `sorry`. -/
theorem exists_pureRGenuineDiffOp_base_appCc (g : SmoothRiemannianMetric I M) :
    ∃ Φ₀ : ∀ r : ℕ, SmoothCcTensor g (r + 0) (r + 0),
      ∀ (r : ℕ) (W : SmoothCcTensor g 0 r),
        pureRGenuineDiffOp (I := I) (M := M) g 0 r W =
          appCc (I := I) (M := M) g (r + 0) (r + 0) (Φ₀ r) W := by
  classical

  refine ⟨fun r => match r with
    | 0 => 0
    | (m + 1) =>
        { toSection :=
            { toFun := fun x : M => TensorRSSpace.ofCLM (pureREndoOpFib (I := I) (M := M) g m x)
              contMDiff_toFun := pureREndoOp_contMDiff (I := I) (M := M) g m }
          hasCompactSupport := HasCompactSupport.of_compactSpace _ }, ?_⟩
  intro r W
  cases r with
  | zero =>

      apply SmoothCcTensor.ext
      apply ContMDiffSection.ext
      intro x
      rw [show (pureRGenuineDiffOp (I := I) (M := M) g 0 0 W).toSection x =
            (pureRGenuineEndo0 (I := I) (M := M) g 0 W).toSection x from rfl,
        show pureRGenuineEndo0 (I := I) (M := M) g 0 W = 0 from rfl,
        SmoothCcTensor.toSection_zero, ContMDiffSection.coe_zero]
      rw [appCc_toSection (I := I) (M := M) g 0 0 0 W]
      rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 0 I x from
            (0 : SmoothCcTensor g 0 0).toSection x) = 0 from by
        rw [SmoothCcTensor.toSection_zero, ContMDiffSection.coe_zero]; rfl]
      rw [ContinuousLinearMap.zero_comp]
      rfl
  | succ m =>

      apply SmoothCcTensor.ext
      apply ContMDiffSection.ext
      intro x
      rw [show (pureRGenuineDiffOp (I := I) (M := M) g 0 (m + 1) W).toSection x =
            pureRGenuineEndoFib (I := I) (M := M) g m W x from rfl]
      rw [appCc_toSection (I := I) (M := M) g (m + 1) (m + 1) _ W]
      rw [pureRGenuineEndoFib_eq_comp (I := I) (M := M) g m W x]
      rfl

/-- **The high-order (`p ≥ 1`) frame-free per-rank section-proportional fibre envelope for the
differentiated moving-frame pure-Riemann curvature tower, in JET form** (the single posited analytic
node). For a closed smooth Riemannian manifold `(M, g)` there is a nonnegative envelope family
`kappaHigh : ℕ → ℕ → ℝ` such that for every order `p`, covariant rank `r`, smooth compactly-supported
`(0, r)`-tensor `W`, and base point `x`, the order-`(p + 1)` differentiated *frame-free* pure-Riemann
curvature operator has intrinsic squared fibre norm at most `kappaHigh p r` times the order-`≤ (p + 1)`
covariant jet of `W`:

```
rfns(pureRGenuineDiffOp g (p + 1) r W)(x) ≤ kappaHigh p r · ∑_{q < p + 2} rfns(∇^q W)(x).
```

**Why the jet form, and not the single-value form `≤ kappaHigh p r · rfns(W)(x)`.** The single-value
form is **Lean-refuted FALSE** at the rank-`0`-degenerate base.  The order-`0` base `pureRGenuineEndo0`
reads the slot-`0` direction of its section, so at rank `0` (no slot-`0` to read) it is the zero
operator: `pureRGenuineDiffOp 0 0 = 0` (`pureRGenuineEndo0`, the `r = 0` branch).  The Leibniz remainder
then forces, at `(p, r) = (0, 0)`,
`pureRGenuineDiffOp 1 0 W = ∇(pureRGenuineDiffOp 0 0 W) − cast(pureRGenuineDiffOp 0 1 (∇W))
= −cast(pureRGenuineDiffOp 0 1 (∇W))`,
which reads the *gradient* `∇W (x)` — the rank-`1` pure-Riemann endomorphism applied to `∇W` — not the
value `W (x)`.  On a non-flat manifold there is a `W` with `W (x) = 0`, `∇W (x) ≠ 0` and
`pureRGenuineDiffOp 1 0 W (x) ≠ 0`, breaking `rfns(…) ≤ kappaHigh 0 0 · rfns(W)(x) = 0`.  Structurally,
the recursion subtracts the *full* rank-`(r + 1)` operator `op p (r + 1)` on `∇W`, while the genuine
covariant Leibniz spectator is the slot-extended rank-`r` operator `slotExtend(op p r)`; their
difference acts on the gradient slot — an irreducible one-jet term at every step.  The honest invariant
is therefore the jet bound: `op (p + 1) r W (x)` reads up to `∇^{p+1} W (x)`, controlled by
`∑_{q < p + 2} rfns(∇^q W)(x)`.

**Why this is TRUE in the jet form — and why it is FRAME-FREE (sound, unlike the deleted frozen posit).**
The order-`0` base `pureRGenuineEndo0` is the moving-frame pure-Riemann endomorphism whose fibre *value*
is a genuine `g`-metric trace (`pureRFrozenDirCLM_frame_independent`), built from the smooth metric `g`
and the smooth Levi-Civita curvature `R` *alone* — NOT from any frame jet.  Writing the order-`0`
operator as the action `op 0 r W = appCc Φ_r W` of a smooth frame-free operator-field section
`Φ_r = g^{-1}·R·(slot0-read)` (`OperatorFieldCovariantCalculus.appCc`), the operator-field covariant
product rule (`covGrad_appCc_eq`) gives
`∇(op p r W) = appCc(∇Φ_{p,r}) W + appCc(slotExtend Φ_{p,r}) (∇W)`, so the remainder
`op (p + 1) r W = appCc(∇Φ_{p,r}) W + appCc(slotExtend Φ_{p,r} − Φ_{p,r+1}) (∇W)` is the sum of a
*frame-free* operator-field action on `W` (the differentiated curvature coefficient `∇^{p+1} Φ`) and an
operator-field action of the *bounded* slot-mismatch on `∇W`.  Each operator factor is a fixed smooth
`(r, ·)`-tensor field, uniformly fibre-operator-bounded over the compact `M` by `‖∇^{≤ p + 1} R‖_∞`
(`exists_uniform_riemannianFiberNormSq_appCc_le` per order, finite by per-`p` compactness); the jet
window absorbs the surviving `∇W ⊆ ∇^{≤ p+1}W` term at every step.  Crucially, because `Φ` is
frame-free, `∇^{p+1} Φ` differentiates *only* the curvature factor, never the chart-selection-unbounded
frame jet `∇(smoothOrthoFrame g x)` that makes the deleted frozen-frame posit FALSE.  The
genuinely-irreducible analytic content is the uniform `‖∇^{≤ p + 1} R‖_∞`-control of the iterated
covariant derivative of the frame-free curvature endomorphism; it is posited here as the precise atomic
frame-free engine envelope, per order `p` and per rank `r` (the rank-`m` curvature derivation acts on
all `m` slots, so the constant grows with `r`).  Consumers transitively depend on `sorryAx` through this
single frame-free node.

**Why this is the honest per-tower posit (and not an abstract one).** This high-order boundedness
*cannot* be derived from an abstract order-`0` fingerprint plus the Leibniz remainder identity alone:
that abstract route (the deleted `op_perOrder_factorisation_continuous` in `OperatorFieldEvaluationLeibniz`)
is FALSE — the order-`0` fingerprint constrains the base only per-rank while the recursion mixes ranks,
so a value-local-at-order-`0` family can produce an order-`1` operator whose one-jet content is *not*
bounded by `kappaHigh` against any jet of `W` with a *uniform* (curvature-free) constant.  The bound is
TRUE *here* only because `pureRGenuineDiffOp` is the genuine differentiated tower of the *smooth*
frame-free curvature coefficient `Φ_r = g, R`, whose iterated covariant derivative `∇^{p+1} Φ_r` is
uniformly fibre-operator-bounded by `‖∇^{≤ p+1} R‖_∞`; that smooth-coefficient content is available only
to this concrete operator.  The posit is therefore stated *concretely* about `pureRGenuineDiffOp`, and
its proof is the uniform-curvature-derivative-norm control of this specific tower — the single
genuinely-irreducible analytic node, disclosed as a `sorry`.

**Non-vacuity / counterexample violation.** A degenerate witness `kappaHigh ≡ 0` is rejected on any
non-flat manifold: at `(p, r) = (0, 0)`, `pureRGenuineDiffOp 1 0 W = −cast(pureRGenuineDiffOp 0 1 (∇W))`
is genuinely nonzero for a `W` with `∇W (x) ≠ 0` whose slot-`0` reading carries a non-zero pure-Riemann
contraction (`R ≠ 0`), so `rfns(pureRGenuineDiffOp 1 0 W)(x) > 0` while the jet RHS
`0 · ∑_{q < 2} rfns(∇^q W)(x) = 0`.  The envelope must carry the genuine differentiated-curvature
magnitude; it genuinely *uses* `W` (the operator is applied to `W`, and the jet window genuinely reaches
`∇^{p+1} W`, not merely `W`). -/
theorem exists_proportional_pureRGenuineDiffOp_highOrder (g : SmoothRiemannianMetric I M) :
    ∃ kappaHigh : ℕ → ℕ → ℝ, (∀ p r, 0 ≤ kappaHigh p r) ∧
      ∀ (p r : ℕ) (W : SmoothCcTensor g 0 r) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g 0 (r + (p + 1)) x
            ((pureRGenuineDiffOp (I := I) (M := M) g (p + 1) r W).toSection x) ≤
          kappaHigh p r * ∑ q ∈ Finset.range (p + 2),
            riemannianFiberNormSq (I := I) (M := M) g 0 (r + q) x
              ((iteratedCovGrad g 0 r q W).toSection x) := by
  classical

  obtain ⟨Φ₀, hΦ₀⟩ := exists_pureRGenuineDiffOp_base_appCc (I := I) (M := M) g

  have hNF : ∀ (p r : ℕ),
      NormalForm (I := I) (M := M) g (pureRGenuineDiffOp (I := I) (M := M) g) p r :=
    fun p => normalForm_of_base (I := I) (M := M) g
      (pureRGenuineDiffOp (I := I) (M := M) g)
      (covGrad_pureRGenuineDiffOp_eq (I := I) (M := M) g) Φ₀ hΦ₀ p

  choose kap hkap_nn hkap using fun p r =>
    exists_jet_bound_of_normalForm (I := I) (M := M) g
      (pureRGenuineDiffOp (I := I) (M := M) g) p r (hNF p r)
  refine ⟨fun p r => kap (p + 1) r, fun p r => hkap_nn (p + 1) r, fun p r W x => ?_⟩

  have h := hkap (p + 1) r W x
  rw [show (p + 1) + 1 = p + 2 from rfl] at h
  exact h

/-- **The frame-free per-order, per-rank section-proportional fibre envelope for the differentiated
moving-frame pure-Riemann curvature tower, in JET form.** For a closed smooth Riemannian manifold
`(M, g)` there is a nonnegative envelope family `kappa : ℕ → ℕ → ℝ` such that for every order `p`,
covariant rank `r`, smooth compactly-supported `(0, r)`-tensor `W`, and base point `x`,

```
rfns(pureRGenuineDiffOp g p r W)(x) ≤ kappa p r · ∑_{q < p + 1} rfns(∇^q W)(x).
```

**Proof.** The order-`p = 0` layer is the *sound, fully-proven* moving-frame endomorphism bound: at the
base point `x` the frame-free operator `pureRGenuineEndo0 g r W` is, by definition, the frozen
endomorphism at the frame `smoothOrthoFrame g x` (orthonormal at its own centre `x`), so the proven
`exists_proportional_pureRFrozenFrameDiffOp_orderZero` (which holds for any frame orthonormal at the
evaluation point) bounds it by `kappa0 r · rfns(W)(x) = kappa0 r · ∑_{q < 1} rfns(∇^q W)(x)` — the
order-`0` operator is value-local, so its jet window `q < 1` carries only the value `∇^0 W = W`.  The
order-`p ≥ 1` layer is the single frame-free posited analytic node (now in jet form)
`exists_proportional_pureRGenuineDiffOp_highOrder` (window `q < (p' + 1) + 1 = p' + 2`).  The two combine
into one per-order jet family.  Consumers transitively depend on `sorryAx` only through the high-order
frame-free node.

**Non-vacuity.** `kappa ≡ 0` is rejected at `p = 0` on a non-flat manifold: the pure-Riemann contraction
`∑ᵢ R(B_iˣ, ·)(slot0_{B_iˣ} W)` is genuinely nonzero (`R ≠ 0`, nonzero slot-`0` reading), forcing
`rfns(pureRGenuineEndo0 g r W)(x) > 0` while the jet RHS `0 · ∑_{q < 1} rfns(∇^q W)(x) = 0`. -/
theorem exists_proportional_pureRGenuineDiffOp (g : SmoothRiemannianMetric I M) :
    ∃ kappa : ℕ → ℕ → ℝ, (∀ p r, 0 ≤ kappa p r) ∧
      ∀ (p r : ℕ) (W : SmoothCcTensor g 0 r) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g 0 (r + p) x
            ((pureRGenuineDiffOp (I := I) (M := M) g p r W).toSection x) ≤
          kappa p r * ∑ q ∈ Finset.range (p + 1),
            riemannianFiberNormSq (I := I) (M := M) g 0 (r + q) x
              ((iteratedCovGrad g 0 r q W).toSection x) := by
  classical

  obtain ⟨kappa0, hkappa0_nn, hkappa0⟩ :=
    exists_proportional_pureRFrozenFrameDiffOp_orderZero (I := I) (M := M) g
  obtain ⟨kappaHigh, hkappaHigh_nn, hkappaHigh⟩ :=
    exists_proportional_pureRGenuineDiffOp_highOrder (I := I) (M := M) g
  refine ⟨fun p r => match p with | 0 => kappa0 r | (p' + 1) => kappaHigh p' r,
    fun p r => ?_, fun p r W x => ?_⟩
  · cases p with
    | zero => exact hkappa0_nn r
    | succ p' => exact hkappaHigh_nn p' r
  · cases p with
    | zero =>

        have h := hkappa0 r W x
        rw [show (fun p r => match p with
            | 0 => kappa0 r | (p' + 1) => kappaHigh p' r) 0 r = kappa0 r from rfl]
        have hsec : (pureRGenuineDiffOp (I := I) (M := M) g 0 r W).toSection x =
            (pureRFrozenDiffOp (I := I) (M := M) g (smoothOrthoFrame (I := I) g x)
              (fun i => smoothOrthoFrame_smooth (I := I) g x i) 0 r W).toSection x := by
          cases r with
          | zero => rfl
          | succ m => rfl
        rw [hsec, Finset.sum_range_one]

        exact h
    | succ p' =>
        have h := hkappaHigh p' r W x
        rw [show (fun p r => match p with
            | 0 => kappa0 r | (p'' + 1) => kappaHigh p'' r) (p' + 1) r = kappaHigh p' r from rfl]

        rw [show (p' + 1) + 1 = p' + 2 from rfl]
        exact h

/-- **The slot-`0` reading of the differentiated section `∇S` along `B_i` is the directional covariant
derivative `∇_{B_iˣ} S`.** `(covGradBundleEquiv 0 s x).symm ((covGrad g 0 s S).toSection x) (B_iˣ) =
covApply (tensorCov g 0 s) (B i) (S.toSection) x`. The covariant gradient's fibre is, by definition
(`covGrad_toSection_apply`), the slot-`0` uncurry `covGradBundleEquiv 0 s x` of the directional
covariant derivative CLM `tensorRSCovariantDerivative … (S.toSection) x = tensorCov g 0 s …`; the
inverse equivalence round-trips it back to that CLM, and `covApply` is its evaluation at `B_iˣ`. -/
private lemma pureRFrozenSlot0_covGrad_eq
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b) (x : M)
    (i : Fin (Module.finrank ℝ E)) :
    (covGradBundleEquiv (I := I) (M := M) 0 s x).symm
        ((covGrad (I := I) (M := M) g 0 s S).toSection x) (B i x) =
      covApply (tensorCov (I := I) g 0 s) (B i) (fun y : M => S.toSection y) x := by
  rw [covGrad_toSection_apply (I := I) (M := M) g 0 s S x,
    ContinuousLinearEquiv.symm_apply_apply]
  rfl

/-- **The bridge: the order-`0` frozen-frame curvature operator on `∇S` is the frozen-frame
pure-Riemann section.** `pureRFrozenDiffOp g B hB 0 (s + 1) (covGrad g 0 s S) = fixedFramePureRSection
g s S B hB`. Both sides are the slot-`0` uncurry (`covGradBundleEquiv 0 s x`) of a frozen-frame
pure-Riemann curvature direction CLM; the two CLMs agree summand-by-summand because the slot-`0`
reading of `∇S` is the directional covariant derivative `∇_{B_iˣ} S`
(`pureRFrozenSlot0_covGrad_eq`), which is exactly the contracted section of `pureRDirCLMFixedFrame`. -/
private lemma pureRFrozenDiffOp0_eq_fixedFramePureRSection
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i))) :
    pureRFrozenDiffOp (I := I) (M := M) g B hB 0 (s + 1)
        (covGrad (I := I) (M := M) g 0 s S) =
      fixedFramePureRSection (I := I) (M := M) g s S B hB := by
  classical

  refine SmoothCcTensor.ext (DFunLike.ext _ _ (fun x => ?_))

  change pureRFrozenEndoFib (I := I) (M := M) g s B (covGrad (I := I) (M := M) g 0 s S) x =
    (fixedFramePureRSection (I := I) (M := M) g s S B hB).toSection x
  rw [fixedFramePureRSection_toSection, pureRFrozenEndoFib, genuineCurvPureRFibFixedFrame]

  refine congrArg (covGradBundleEquiv (I := I) (M := M) 0 s x) ?_
  refine ContinuousLinearMap.ext (fun v => ?_)
  rw [pureRFrozenDirCLM_apply, pureRDirCLMFixedFrame, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [pureRDirCLMSummandFixedFrame, LinearMap.coe_toContinuousLinearMap', pureRDirLMSummandFixedFrame,
    LinearMap.coe_mk, AddHom.coe_mk, pureRFrozenSlot0_covGrad_eq (I := I) (M := M) g s S B x i]

/-- **Heterogeneous rank-congruence for `covGrad`.** If `h : a = b`, then `covGrad g 0 a Y` and
`covGrad g 0 b Z` are heterogeneously equal whenever `Y, Z` are. -/
private theorem covGrad_heq_congr_tw (g : SmoothRiemannianMetric I M) {a b : ℕ}
    (h : a = b) {Y : SmoothCcTensor g 0 a} {Z : SmoothCcTensor g 0 b} (hYZ : HEq Y Z) :
    HEq (covGrad (I := I) (M := M) g 0 a Y) (covGrad (I := I) (M := M) g 0 b Z) := by
  subst h
  rw [eq_of_heq hYZ]

/-- **Heterogeneous commuting of one covariant gradient through the iterated gradient.** Applying `q`
covariant gradients to `covGrad g 0 s X` is heterogeneously equal to the `(q + 1)`-fold iterated
gradient of `X`; the two live in ranks `(s + 1) + q` and `s + (q + 1)`, which agree as naturals. -/
private theorem iteratedCovGrad_covGrad_comm_heq_tw (g : SmoothRiemannianMetric I M)
    (s q : ℕ) (X : SmoothCcTensor g 0 s) :
    HEq (iteratedCovGrad g 0 (s + 1) q (covGrad (I := I) (M := M) g 0 s X))
      (iteratedCovGrad g 0 s (q + 1) X) := by
  induction q with
  | zero =>
      rw [iteratedCovGrad_zero, iteratedCovGrad_succ, iteratedCovGrad_zero]
      exact HEq.rfl
  | succ k ih =>
      rw [iteratedCovGrad_succ (g := g) (r := 0) (s := s + 1) (j := k)
        (covGrad (I := I) (M := M) g 0 s X)]
      rw [iteratedCovGrad_succ (g := g) (r := 0) (s := s) (j := k + 1) X]
      exact covGrad_heq_congr_tw g (by omega : (s + 1) + k = s + (k + 1)) ih

/-- **The intrinsic fibre norm is invariant under a `SmoothCcTensor` rank-cast.** Heterogeneously
equal smooth compactly-supported tensors over agreeing ranks have equal section-value
`riemannianFiberNormSq` at every point. -/
private theorem rfns_toSection_heq_congr_tw (g : SmoothRiemannianMetric I M)
    {a b : ℕ} (h : a = b) {Y : SmoothCcTensor g 0 a} {Z : SmoothCcTensor g 0 b}
    (hYZ : HEq Y Z) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 0 a x (Y.toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g 0 b x (Z.toSection x) := by
  subst h
  rw [eq_of_heq hYZ]

/-- **Front-commuting one covariant gradient through the iterated gradient (rfns form).** The
intrinsic squared fibre norm of `∇^q(∇S)` at `x` equals that of `∇^{q + 1}S`. The rank reassociation
`(s + 1) + q = s + (q + 1)` is invisible to the intrinsic fibre norm. -/
private theorem rfns_iteratedCovGrad_covGrad_comm_tw (g : SmoothRiemannianMetric I M)
    (s q : ℕ) (S : SmoothCcTensor g 0 s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 0 ((s + 1) + q) x
        ((iteratedCovGrad g 0 (s + 1) q (covGrad (I := I) (M := M) g 0 s S)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g 0 (s + (q + 1)) x
        ((iteratedCovGrad g 0 s (q + 1) S).toSection x) :=
  rfns_toSection_heq_congr_tw g (by omega : (s + 1) + q = s + (q + 1))
    (iteratedCovGrad_covGrad_comm_heq_tw (I := I) (M := M) g s q S) x

/-- **The bridge: the order-`0` moving-frame curvature operator on `∇T` is the moving-centre
pure-Riemann section `GcurvSection`.** `pureRGenuineDiffOp g 0 (s + 1) (covGrad g 0 s T) =
GcurvSection g s T`. Fibrewise at `x`, the moving fibre `pureRGenuineEndoFib g s (∇T) x =
pureRFrozenEndoFib g s (smoothOrthoFrame g x) (∇T) x` equals the frozen-frame section fibre against
`smoothOrthoFrame g x` (`pureRFrozenDiffOp0_eq_fixedFramePureRSection`, read fibrewise — the slot-`0`
reading of `∇T` along `B_i` is the directional covariant derivative `∇_{B_i} T`), which equals the
moving-centre `GcurvSection` fibre at the centre `x` itself
(`GcurvSection_toSection_eventuallyEq_fixedFramePureRSection` at its own centre). -/
lemma pureRGenuineDiffOp0_eq_GcurvSection
    (g : SmoothRiemannianMetric I M) (s : ℕ) (T : SmoothCcTensor g 0 s) :
    pureRGenuineDiffOp (I := I) (M := M) g 0 (s + 1)
        (covGrad (I := I) (M := M) g 0 s T) =
      GcurvSection (I := I) (M := M) g s T := by
  classical
  refine SmoothCcTensor.ext (DFunLike.ext _ _ (fun x => ?_))

  change pureRGenuineEndoFib (I := I) (M := M) g s (covGrad (I := I) (M := M) g 0 s T) x =
    (GcurvSection (I := I) (M := M) g s T).toSection x
  rw [pureRGenuineEndoFib]
  set hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (smoothOrthoFrame (I := I) g x i)) :=
    fun i => smoothOrthoFrame_smooth (I := I) g x i with hB_def

  have hfrozen := pureRFrozenDiffOp0_eq_fixedFramePureRSection (I := I) (M := M) g s T
    (smoothOrthoFrame (I := I) g x) hB
  have hfib : pureRFrozenEndoFib (I := I) (M := M) g s (smoothOrthoFrame (I := I) g x)
        (covGrad (I := I) (M := M) g 0 s T) x =
      (fixedFramePureRSection (I := I) (M := M) g s T
        (smoothOrthoFrame (I := I) g x) hB).toSection x := by
    have := congrArg (fun (Z : SmoothCcTensor g 0 (s + 1)) => Z.toSection x) hfrozen
    simpa [pureRFrozenDiffOp, pureRFrozenEndo0, pureRFrozenEndoSucc_toSection] using this
  rw [hfib]

  exact ((GcurvSection_toSection_eventuallyEq_fixedFramePureRSection
    (I := I) (M := M) g s T x hB).self_of_nhds).symm

/-- **The moving-centre pure-Riemann curvature-jet grid bound (the `(p, w) = (1, 1)` headline, the
sound frame-free replacement).** For a closed smooth Riemannian manifold `(M, g)` there is a
*valence/order-dependent* nonnegative constant family `c : ℕ → ℕ → ℝ` such that at every covariant rank
`s`, smooth compactly-supported `(0, s)`-tensor `S`, gradient order `k`, and base point `x`, the
`k`-fold iterated covariant gradient of the moving-centre pure-Riemann section `GcurvSection g s S` is
fibre-bounded by

```
rfns(∇^k (GcurvSection g s S))(x) ≤ (c s k)² · ∑_{i < 1 + k} rfns(∇^{i + 1} S)(x).
```

This is the order-`1`/width-`1` graded curvature-jet bound the moving-centre curvature-jet induction
(`OrderSeparatedCurvatureJet.GcurvSection_gradedCurvJet`) consumes — *directly*, with NO frozen-frame
locality detour. It is **proved** by the at-point differentiated-bilinear-contraction single-sum grid
`DiffBilinOp.exists_rfns_iteratedCovGrad_singleSum_le_at` applied to the *frame-free* pure-Riemann tower
(`op := pureRGenuineDiffOp g …`, whose `covGrad_op` Leibniz is *proved* by
`covGrad_pureRGenuineDiffOp_eq`, whose frame-free envelope is the single posited node
`exists_proportional_pureRGenuineDiffOp`), the order-`0` bridge `pureRGenuineDiffOp0_eq_GcurvSection`
(the order-`0` operator on `∇S` is `GcurvSection`), and the rank-shift `∇^q(∇S) ≅ ∇^{q + 1}S`
(`rfns_iteratedCovGrad_covGrad_comm_tw`) collapsing the contracted-order range `0 … k` of `∇S` to
`1 … 1 + k` of `S`. The constant family is the engine's single-sum constant
`c s k := √(4^k · gridWindowSum kappa 0 (s + 1) k)`, frame-free because the posited per-rank envelope
`kappa` is.

**Non-vacuity.** With `c s 0 = 0` the bound forces `rfns(GcurvSection g s S)(x) = 0` at `k = 0`, i.e.
the pure-Riemann contraction `∑ᵢ R(B_iˣ, ·)(∇_{B_iˣ} S)` vanishes; false on a non-flat manifold
(`R ≠ 0`) for a non-parallel `S` (`∇S ≠ 0`). The constant family is genuinely positive. -/
theorem exists_GcurvSection_iteratedCovGrad_grid_bound (g : SmoothRiemannianMetric I M) :
    ∃ c : ℕ → ℕ → ℝ, (∀ s k, 0 ≤ c s k) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g 0 s) (k : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g 0 ((s + 1) + k) x
            ((iteratedCovGrad g 0 (s + 1) k
              (GcurvSection (I := I) (M := M) g s S)).toSection x) ≤
          (c s k) ^ 2 * ∑ i ∈ Finset.range (1 + k),
            riemannianFiberNormSq (I := I) (M := M) g 0 (s + (i + 1)) x
              ((iteratedCovGrad g 0 s (i + 1) S).toSection x) := by
  classical
  obtain ⟨kappa, hkappa_nn, hkappa⟩ := exists_proportional_pureRGenuineDiffOp (I := I) (M := M) g

  refine ⟨fun s' k => Real.sqrt ((4 : ℝ) ^ k * gridWindowSum kappa 0 (s' + 1) k),
    fun _ k => Real.sqrt_nonneg _, fun s S k x => ?_⟩
  have hcsq : (Real.sqrt ((4 : ℝ) ^ k * gridWindowSum kappa 0 (s + 1) k)) ^ 2 =
      (4 : ℝ) ^ k * gridWindowSum kappa 0 (s + 1) k := by
    rw [Real.sq_sqrt]
    exact mul_nonneg (by positivity) (gridWindowSum_nonneg hkappa_nn 0 (s + 1) k)
  rw [hcsq]

  have hgrid := DifferentialGeometry.Integral.Connection.DiffBilinOp.exists_rfns_iteratedCovGrad_singleSum_le_at
    (g := g)
    (op := fun p r W => pureRGenuineDiffOp (I := I) (M := M) g p r W)
    (fun p r W => covGrad_pureRGenuineDiffOp_eq (I := I) (M := M) g p r W)
    kappa hkappa_nn x
    (fun p r W => hkappa p r W x)
    (s + 1) (covGrad (I := I) (M := M) g 0 s S) k

  rw [pureRGenuineDiffOp0_eq_GcurvSection (I := I) (M := M) g s S] at hgrid
  refine hgrid.trans (le_of_eq ?_)

  refine congrArg (fun t => ((4 : ℝ) ^ k * gridWindowSum kappa 0 (s + 1) k) * t) ?_
  rw [Nat.add_comm 1 k]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  exact rfns_iteratedCovGrad_covGrad_comm_tw (I := I) (M := M) g s q S x

/-- **The frame-free curvature operator field `Φ₀ s`.** The fixed smooth `(s, s)`-operator field whose
operator-field action recovers the order-`0` moving-frame pure-Riemann curvature endomorphism
`pureRGenuineDiffOp g 0 s W = appCc (Φ₀ s) W` (`exists_pureRGenuineDiffOp_base_appCc`); its fibre value
is the genuine `g`-metric curvature trace `W ↦ ∑ᵢ R(Bᵢ, ·) W`, frame-free (built from `g, R` alone). It
is the curvature coefficient whose covariant derivative carries the differentiated-curvature `(∇R)`
content. It is a pure `Classical.choose` definition (no downstream dependency), homed at the most-upstream
curvature node so the curvature line shares it. -/
noncomputable def curvOpField (g : SmoothRiemannianMetric I M) (s : ℕ) :
    SmoothCcTensor g (s + 0) (s + 0) :=
  (Classical.choose (exists_pureRGenuineDiffOp_base_appCc (I := I) (M := M) g)) s

/-- **The order-`0` curvature operator base spec for `curvOpField`.** The defining `Classical.choose`
specification: the operator-field action of the frame-free curvature operator field `Φ₀ s := curvOpField
g s` on a smooth compactly-supported `(0, s)`-tensor `S` recovers the order-`0` moving-frame pure-Riemann
curvature trace `pureRGenuineDiffOp g 0 s S`. This is the identity through which the differentiated
operator field `covGrad (Φ₀ s)` and its passenger-slot extension `slotExtend (Φ₀ s)` are identified with
the curvature-derivative content. -/
theorem appCc_curvOpField_eq_pureRGenuineDiffOp
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    appCc (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s) S =
      pureRGenuineDiffOp (I := I) (M := M) g 0 s S :=
  (Classical.choose_spec (exists_pureRGenuineDiffOp_base_appCc (I := I) (M := M) g) s S).symm

/-- **The gauge-glued tensorial differentiated-curvature section `(∇R) S`.** For a smooth
compactly-supported `(0, s)`-tensor `S`, the operator-field action of the covariant derivative of the
frame-free curvature operator field `Φ₀ s` (`curvOpField`) on `S`:
```
genuineDiffCurvSection g s S := appCc (covGrad g s s (Φ₀ s)) S,
```
the differentiated-curvature contraction `∑ᵢ (∇R)(Bᵢ, ·) S` (the `(∇R) S` field), a smooth
compactly-supported `(0, s + 1)`-tensor. It is the covariant-derivative counterpart of the pure-Riemann
genuine section `GcurvSection g s S`: where the pure-Riemann trace is the action `appCc (Φ₀ s) S` of the
order-`0` curvature operator, the differentiated trace is the action `appCc (∇Φ₀ s) S` of its covariant
derivative (the operator-field product rule `covGrad_appCc_eq` separates the `(∇R) S` summand from the
`R(∇S)` spectator). It is constructed tensorially and smoothly through the operator-field calculus, never
extension-curried. -/
noncomputable def genuineDiffCurvSection
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    SmoothCcTensor g 0 (s + 1) :=
  appCc (I := I) (M := M) g (s + 0) (s + 0 + 1)
    (covGrad (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s)) S

/-- **The fibre value of `genuineDiffCurvSection` is the fibrewise composition `(∇Φ₀ s).comp S`.**
Definitional: the operator-field action `appCc` evaluates fibrewise as the composition of the
differentiated curvature operator with the section value (`appCc_toSection`). -/
@[simp] lemma genuineDiffCurvSection_toSection
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M) :
    (genuineDiffCurvSection (I := I) (M := M) g s S).toSection x =
      (show Tensor0SSpace (s + 0) I x →L[ℝ] Tensor0SSpace (s + 0 + 1) I x from
        (covGrad (I := I) (M := M) g (s + 0) (s + 0)
          (curvOpField (I := I) (M := M) g s)).toSection x).comp
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 0) I x from S.toSection x) := by
  rw [genuineDiffCurvSection,
    appCc_toSection (I := I) (M := M) g (s + 0) (s + 0 + 1)
      (covGrad (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s)) S x]
  rfl

/-- **The covariant-derivative spec of the frame-free curvature operator field (the section-level
B-rule inversion).** For a closed smooth Riemannian manifold `(M, g)`, covariant rank `s`, and smooth
compactly-supported `(0, s)`-tensor `S`, the gauge-glued tensorial differentiated-curvature section
`genuineDiffCurvSection g s S` (the operator-field action `appCc (covGrad (Φ₀ s)) S` of the covariant
derivative of the frame-free curvature operator field `Φ₀ s := curvOpField g s`) equals the covariant
gradient of the order-`0` pure-Riemann curvature trace minus the passenger-slot extension of `Φ₀ s`
acting on `∇S`:
```
genuineDiffCurvSection g s S
  = covGrad g 0 s (pureRGenuineDiffOp g 0 s S)
    − appCc (slotExtend (Φ₀ s)) (covGrad g 0 s S).
```
Both right-hand terms are concrete: `pureRGenuineDiffOp g 0 s S = appCc (Φ₀ s) S` is the order-`0`
moving-frame pure-Riemann curvature trace (the `Classical.choose` base spec defining `curvOpField`), and
`slotExtend (Φ₀ s)` is the passenger-slot extension of the frame-free curvature operator. This is the
covariant-derivative spec of `curvOpField`: it characterises the action of `covGrad (curvOpField g s)` as
the differentiated-curvature trace `(∇R) S`, the `(∇R)`-on-`S` summand isolated from the `R(∇S)`
spectator.

**Proof.** The operator-field covariant product rule `covGrad_appCc_eq` (the B-rule) at the square field
`Φ₀ s` and the tensor `S` reads `covGrad g 0 s (appCc (Φ₀ s) S) = appCc (covGrad (Φ₀ s)) S +
appCc (slotExtend (Φ₀ s)) (∇S)`, whose first summand is `genuineDiffCurvSection g s S` by definition.
Rearranging by `eq_sub_of_add_eq` isolates that summand, and rewriting `appCc (Φ₀ s) S =
pureRGenuineDiffOp g 0 s S` by the base spec `exists_pureRGenuineDiffOp_base_appCc` makes the first
right-hand term the concrete order-`0` curvature trace. -/
theorem genuineDiffCurvSection_eq_covGrad_sub_slotExtend
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    genuineDiffCurvSection (I := I) (M := M) g s S =
      covGrad (I := I) (M := M) g 0 (s + 0)
          (pureRGenuineDiffOp (I := I) (M := M) g 0 s S) -
        appCc (I := I) (M := M) g (s + 0 + 1) (s + 0 + 1)
          (slotExtend (I := I) (M := M) g (s + 0) (s + 0)
            (curvOpField (I := I) (M := M) g s))
          (covGrad (I := I) (M := M) g 0 (s + 0) S) := by
  classical
  have hbase : appCc (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s) S =
      pureRGenuineDiffOp (I := I) (M := M) g 0 s S :=
    (Classical.choose_spec (exists_pureRGenuineDiffOp_base_appCc (I := I) (M := M) g) s S).symm
  have hB := covGrad_appCc_eq (I := I) (M := M) g (s + 0) (s + 0)
    (curvOpField (I := I) (M := M) g s) S
  have hgds : appCc (I := I) (M := M) g (s + 0) (s + 0 + 1)
        (covGrad (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s)) S =
      genuineDiffCurvSection (I := I) (M := M) g s S := rfl
  rw [hgds] at hB
  have hB' := eq_sub_of_add_eq (hB.symm)
  rw [hB', hbase]

/-- **The passenger-slot action of the curvature operator field on `∇S` reads the gradient direction
first (the spectator-term unit-evaluation).** For a closed smooth Riemannian manifold `(M, g)`, covariant
rank `s`, smooth compactly-supported `(0, s)`-tensor `S`, point `x`, base `(0, 0)`-tensor `d`, gradient
direction `v0`, and trailing tuple `vs`, the passenger-slot operator-field action
`appCc (slotExtend (Φ₀ s)) (∇S)` evaluated on the tuple `Fin.cons v0 vs` reads the leading gradient
direction `v0` off the passenger slot and applies the frame-free curvature operator `Φ₀ s = curvOpField
g s` to the directional covariant derivative `∇_{v0} S`:
```
(appCc (slotExtend (Φ₀ s)) (∇S))(x)(d)(Fin.cons v0 vs)
  = (Φ₀ s)(x)((∇_{v0} S)(x)(d))(vs).
```
This is the spectator `R(∇S)` term of the differentiated curvature trace in unit-evaluated form: the
passenger slot carries the gradient direction, and the curvature endomorphism `Φ₀ s` acts on the
trailing slots of the directional derivative of `S` — never the next-rank curvature operator
`Φ₀ (s + 1)`.

**Proof.** Expand the operator-field action (`appCc_toSection`, the fibrewise composition) and the
slot-extended fibre operator (`slotExtend_toSection`), then read the leading slot by
`slotExtendFib_apply_eval` (the new slot is read first, the rest curried through `tensor0S_curry`), and
identify the curried gradient with the directional covariant derivative by
`tensor0S_curry_covGrad_appCc_eq`. -/
theorem appCc_slotExtend_curvOpField_covGrad_unit_eval
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    (d : Tensor0SSpace 0 I x) (v0 : E) (vs : Fin (s + 0) → E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 0 + 1) I x from
          (appCc (I := I) (M := M) g (s + 0 + 1) (s + 0 + 1)
            (slotExtend (I := I) (M := M) g (s + 0) (s + 0)
              (curvOpField (I := I) (M := M) g s))
            (covGrad (I := I) (M := M) g 0 (s + 0) S)).toSection x) d)
        (Fin.cons v0 vs) =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace (s + 0) I x →L[ℝ] Tensor0SSpace (s + 0) I x from
          (curvOpField (I := I) (M := M) g s).toSection x)
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 0) I x from
            tensorCovDerivAt (I := I) (M := M) g 0 (s + 0) S x v0) d))
        vs := by
  classical
  rw [appCc_toSection (I := I) (M := M) g (s + 0 + 1) (s + 0 + 1)
      (slotExtend (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s))
      (covGrad (I := I) (M := M) g 0 (s + 0) S) x,
    ContinuousLinearMap.comp_apply,
    slotExtend_toSection (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s) x]
  rw [slotExtendFib_apply_eval (I := I) (M := M) g (s + 0) (s + 0) x
    (show Tensor0SSpace (s + 0) I x →L[ℝ] Tensor0SSpace (s + 0) I x from
      (curvOpField (I := I) (M := M) g s).toSection x)
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 0 + 1) I x from
      (covGrad (I := I) (M := M) g 0 (s + 0) S).toSection x) d) v0 vs]
  rw [tensor0S_curry_covGrad_appCc_eq (I := I) (M := M) g (s + 0) S x d v0]

set_option maxHeartbeats 3200000 in
set_option backward.isDefEq.respectTransparency false in
/-- **The full unit-evaluated differentiated-curvature trace identity (the frame-free
`∇R`-trace pointwise characterization).** For a closed smooth Riemannian manifold `(M, g)`, covariant
rank `s`, smooth compactly-supported `(0, s)`-tensor `S`, point `x`, base `(0, 0)`-tensor `d`, gradient
direction `v0`, and trailing tuple `vs`, the directional covariant derivative of the order-`0`
pure-Riemann curvature trace decomposes, in unit-evaluated form, as the differentiated-curvature section
`genuineDiffCurvSection g s S` (the `(∇R) S` field) plus the passenger-slot curvature spectator
`(Φ₀ s)(∇_{v0} S)`:
```
(∇_{v0}(pureRGenuineDiffOp g 0 s S))(x)(d)(vs)
  = (genuineDiffCurvSection g s S)(x)(d)(Fin.cons v0 vs)
    + (Φ₀ s)(x)((∇_{v0} S)(x)(d))(vs).
```
Equivalently, `genuineDiffCurvSection = ∇(R-trace) − R(∇S)` pointwise: the differentiated-curvature
trace is the covariant derivative of the curvature trace with the spectator `R(∇S)` removed. This is the
frame-free unit-evaluated form of the `(∇R)`-trace, the foundation against which the
frame-summed-to-frame-free transfer compares the moving-frame frame sum.

**Proof.** The operator-field covariant product rule `covGrad_appCc_eq` (the B-rule) at the square field
`Φ₀ s` and `S`, rewritten by the base spec `exists_pureRGenuineDiffOp_base_appCc`
(`appCc (Φ₀ s) S = pureRGenuineDiffOp g 0 s S`), gives the section identity
`covGrad g 0 s (pureRGenuineDiffOp g 0 s S) = genuineDiffCurvSection g s S +
appCc (slotExtend (Φ₀ s)) (∇S)`. Reading it at `x`, applying to `d`, distributing the additive fibre
value (`ContinuousLinearMap.add_apply`, `Tensor0SSpace.toModel_add`), and unit-evaluating the left-hand
gradient by `covGrad_toSection_apply_eval` and the spectator by
`appCc_slotExtend_curvOpField_covGrad_unit_eval` gives the pointwise identity. -/
theorem covGrad_pureRGenuineDiffOp_unit_eval_eq_genuineDiffCurv_add_spectator
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    (d : Tensor0SSpace 0 I x) (v0 : E) (vs : Fin (s + 0) → E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 0) I x from
          tensorCovDerivAt (I := I) (M := M) g 0 (s + 0)
            (pureRGenuineDiffOp (I := I) (M := M) g 0 s S) x v0) d)
        vs =
      Tensor0SSpace.toModel
          ((genuineDiffCurvSection (I := I) (M := M) g s S).toSection x d)
          (Fin.cons v0 vs) +
        Tensor0SSpace.toModel
          ((show Tensor0SSpace (s + 0) I x →L[ℝ] Tensor0SSpace (s + 0) I x from
            (curvOpField (I := I) (M := M) g s).toSection x)
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 0) I x from
              tensorCovDerivAt (I := I) (M := M) g 0 (s + 0) S x v0) d))
          vs := by
  classical
  have hbase : appCc (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s) S =
      pureRGenuineDiffOp (I := I) (M := M) g 0 s S :=
    (Classical.choose_spec (exists_pureRGenuineDiffOp_base_appCc (I := I) (M := M) g) s S).symm
  have hB := covGrad_appCc_eq (I := I) (M := M) g (s + 0) (s + 0)
    (curvOpField (I := I) (M := M) g s) S
  rw [hbase] at hB
  have hsec := congrArg (fun T : SmoothCcTensor g 0 (s + 0 + 1) => T.toSection x) hB
  simp only at hsec
  rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply] at hsec
  have happ :
      (covGrad (I := I) (M := M) g 0 (s + 0)
          (pureRGenuineDiffOp (I := I) (M := M) g 0 s S)).toSection x d =
        (genuineDiffCurvSection (I := I) (M := M) g s S).toSection x d +
          (appCc (I := I) (M := M) g (s + 0 + 1) (s + 0 + 1)
            (slotExtend (I := I) (M := M) g (s + 0) (s + 0)
              (curvOpField (I := I) (M := M) g s))
            (covGrad (I := I) (M := M) g 0 (s + 0) S)).toSection x d := by
    rw [hsec, ContinuousLinearMap.add_apply]
    rfl
  have hlhs :
      Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 0) I x from
            tensorCovDerivAt (I := I) (M := M) g 0 (s + 0)
              (pureRGenuineDiffOp (I := I) (M := M) g 0 s S) x v0) d)
          vs =
        Tensor0SSpace.toModel
          ((covGrad (I := I) (M := M) g 0 (s + 0)
            (pureRGenuineDiffOp (I := I) (M := M) g 0 s S)).toSection x d)
          (Fin.cons v0 vs) := by
    have h := covGrad_toSection_apply_eval (I := I) (M := M) g 0 (s + 0)
      (pureRGenuineDiffOp (I := I) (M := M) g 0 s S) x d (Fin.cons v0 vs)
    refine Eq.symm (h.trans ?_)
    have htail : Matrix.vecTail (Fin.cons v0 vs : Fin (s + 0 + 1) → E) = vs := by
      funext j; simp [Matrix.vecTail, Fin.cons_succ]
    have hhead : (Fin.cons v0 vs : Fin (s + 0 + 1) → E) 0 = v0 := by simp [Fin.cons_zero]
    rw [htail, hhead]
  have hterm2 :
      Tensor0SSpace.toModel
          ((appCc (I := I) (M := M) g (s + 0 + 1) (s + 0 + 1)
            (slotExtend (I := I) (M := M) g (s + 0) (s + 0)
              (curvOpField (I := I) (M := M) g s))
            (covGrad (I := I) (M := M) g 0 (s + 0) S)).toSection x d)
          (Fin.cons v0 vs) =
        Tensor0SSpace.toModel
          ((show Tensor0SSpace (s + 0) I x →L[ℝ] Tensor0SSpace (s + 0) I x from
            (curvOpField (I := I) (M := M) g s).toSection x)
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 0) I x from
              tensorCovDerivAt (I := I) (M := M) g 0 (s + 0) S x v0) d))
          vs :=
    appCc_slotExtend_curvOpField_covGrad_unit_eval (I := I) (M := M) g s S x d v0 vs
  rw [hlhs, happ, Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply, hterm2]

/-- **The second covariant-derivative spec of the frame-free curvature operator field (the
twice-differentiated B-rule inversion).** For a closed smooth Riemannian manifold `(M, g)`, covariant
rank `s`, and smooth compactly-supported `(0, s)`-tensor `S`, the operator-field action of the second
covariant derivative `∇²Φ₀ = covGrad g r (r + 1)(covGrad g r r Φ₀)` (`r := s + 0`) of the frame-free
curvature operator field `Φ₀ s := curvOpField g s` on `S` — the differentiated-curvature carrier `T₁`
of the operator-field four-term Leibniz normal form — equals the covariant gradient of the once-
differentiated carrier `genuineDiffCurvSection g s S` minus the passenger-slot extension of the
once-differentiated operator field `∇Φ₀` acting on `∇S`:
```
appCc (∇²Φ₀) S
  = covGrad g 0 (s + 1) (genuineDiffCurvSection g s S)
    − appCc (slotExtend (∇Φ₀)) (∇S).
```
This is the once-differentiated spec `genuineDiffCurvSection_eq_covGrad_sub_slotExtend` applied one
covariant order higher: where the order-`1` inversion isolates `appCc (∇Φ₀) S = genuineDiffCurvSection`
from `covGrad (Φ₀-trace) − appCc (slotExtend Φ₀)(∇S)`, the order-`2` inversion isolates the curvature
carrier `appCc (∇²Φ₀) S = T₁` from `covGrad (genuineDiffCurvSection) − appCc (slotExtend (∇Φ₀))(∇S)`,
the differentiated-curvature term separated from the passenger cross term `T₃`.

**Proof.** The operator-field covariant product rule `covGrad_appCc_eq` (the B-rule) at the once-
differentiated square field `∇Φ₀ := covGrad g (s + 0) (s + 0) Φ₀` (rank `(s + 0, s + 0 + 1)`) and the
tensor `S` reads `covGrad g 0 (s + 0 + 1) (appCc (∇Φ₀) S) = appCc (covGrad (∇Φ₀)) S +
appCc (slotExtend (∇Φ₀)) (∇S)`; the contracted action `appCc (∇Φ₀) S` is `genuineDiffCurvSection g s S`
by definition, and the first summand `appCc (covGrad (∇Φ₀)) S` is `appCc (∇²Φ₀) S = T₁`. Rearranging by
`eq_sub_of_add_eq` isolates that summand. -/
theorem appCc_covGrad_covGrad_curvOpField_eq_covGrad_genuineDiffCurv_sub_slotExtend
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    appCc (I := I) (M := M) g (s + 0) (s + 0 + 1 + 1)
        (covGrad (I := I) (M := M) g (s + 0) (s + 0 + 1)
          (covGrad (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s))) S =
      covGrad (I := I) (M := M) g 0 (s + 0 + 1)
          (genuineDiffCurvSection (I := I) (M := M) g s S) -
        appCc (I := I) (M := M) g (s + 0 + 1) (s + 0 + 1 + 1)
          (slotExtend (I := I) (M := M) g (s + 0) (s + 0 + 1)
            (covGrad (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s)))
          (covGrad (I := I) (M := M) g 0 (s + 0) S) := by
  classical
  have hB := covGrad_appCc_eq (I := I) (M := M) g (s + 0) (s + 0 + 1)
    (covGrad (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s)) S
  have hgds : appCc (I := I) (M := M) g (s + 0) (s + 0 + 1)
        (covGrad (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s)) S =
      genuineDiffCurvSection (I := I) (M := M) g s S := rfl
  rw [hgds] at hB
  exact (eq_sub_of_add_eq hB.symm)

/-- **The passenger-slot action of the once-differentiated curvature operator field on `∇S` reads the
gradient direction first (the second-order spectator-term unit-evaluation).** For a closed smooth
Riemannian manifold `(M, g)`, covariant rank `s`, smooth compactly-supported `(0, s)`-tensor `S`, point
`x`, base `(0, 0)`-tensor `d`, gradient direction `v0`, and trailing tuple `vs`, the passenger-slot
operator-field action `appCc (slotExtend (∇Φ₀)) (∇S)` — the passenger cross term `T₃` of the second-
order normal form — evaluated on `Fin.cons v0 vs` reads the leading gradient direction `v0` off the
passenger slot and applies the once-differentiated curvature operator field `∇Φ₀ := covGrad Φ₀`
(`Φ₀ s = curvOpField g s`) to the directional covariant derivative `∇_{v0} S`:
```
(appCc (slotExtend (∇Φ₀)) (∇S))(x)(d)(Fin.cons v0 vs)
  = (∇Φ₀)(x)((∇_{v0} S)(x)(d))(vs).
```
This is the second-order spectator term in unit-evaluated form: the passenger slot carries the gradient
direction and the *differentiated* curvature endomorphism `∇Φ₀` acts on the trailing slots of the
directional derivative of `S`. It is `appCc_slotExtend_curvOpField_covGrad_unit_eval` one covariant
order higher (`Φ := ∇Φ₀` in place of `Φ₀`), proved by the identical operator-field calculus: expand the
action (`appCc_toSection`), the slot-extended fibre operator (`slotExtend_toSection`), read the leading
slot (`slotExtendFib_apply_eval`), and identify the curried gradient with the directional covariant
derivative (`tensor0S_curry_covGrad_appCc_eq`). -/
theorem appCc_slotExtend_covGrad_curvOpField_covGrad_unit_eval
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    (d : Tensor0SSpace 0 I x) (v0 : E) (vs : Fin (s + 0 + 1) → E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 0 + 1 + 1) I x from
          (appCc (I := I) (M := M) g (s + 0 + 1) (s + 0 + 1 + 1)
            (slotExtend (I := I) (M := M) g (s + 0) (s + 0 + 1)
              (covGrad (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s)))
            (covGrad (I := I) (M := M) g 0 (s + 0) S)).toSection x) d)
        (Fin.cons v0 vs) =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace (s + 0) I x →L[ℝ] Tensor0SSpace (s + 0 + 1) I x from
          (covGrad (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s)).toSection x)
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 0) I x from
            tensorCovDerivAt (I := I) (M := M) g 0 (s + 0) S x v0) d))
        vs := by
  classical
  rw [appCc_toSection (I := I) (M := M) g (s + 0 + 1) (s + 0 + 1 + 1)
      (slotExtend (I := I) (M := M) g (s + 0) (s + 0 + 1)
        (covGrad (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s)))
      (covGrad (I := I) (M := M) g 0 (s + 0) S) x,
    ContinuousLinearMap.comp_apply,
    slotExtend_toSection (I := I) (M := M) g (s + 0) (s + 0 + 1)
      (covGrad (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s)) x]
  rw [slotExtendFib_apply_eval (I := I) (M := M) g (s + 0) (s + 0 + 1) x
    (show Tensor0SSpace (s + 0) I x →L[ℝ] Tensor0SSpace (s + 0 + 1) I x from
      (covGrad (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s)).toSection x)
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 0 + 1) I x from
      (covGrad (I := I) (M := M) g 0 (s + 0) S).toSection x) d) v0 vs]
  rw [tensor0S_curry_covGrad_appCc_eq (I := I) (M := M) g (s + 0) S x d v0]

/-- **The full unit-evaluated second covariant-derivative frame-trace characterization of the `T₁`
curvature carrier (the doubly-differentiated frame-free `∇²R`-trace pointwise form).** For a closed
smooth Riemannian manifold `(M, g)`, covariant rank `s`, smooth compactly-supported `(0, s)`-tensor `S`,
point `x`, base `(0, 0)`-tensor `d`, leading covariant direction `v0`, and trailing tuple
`vs : Fin (s + 0 + 1) → E`, the unit-evaluated value of the differentiated-curvature carrier
`appCc (∇²Φ₀) S` (the `T₁` term of the operator-field four-term normal form
`covGrad_covGrad_appCc_curvOpField_eq_fourTerm`) decomposes as the directional covariant derivative of
the once-differentiated carrier `genuineDiffCurvSection g s S` (the `(∇R) S` field) minus the passenger-
slot spectator action of the once-differentiated curvature operator field `∇Φ₀` on `∇_{v0} S`:
```
(appCc (∇²Φ₀) S)(x)(d)(Fin.cons v0 vs)
  = (∇_{v0}(genuineDiffCurvSection g s S))(x)(d)(vs)
    − (∇Φ₀)(x)((∇_{v0} S)(x)(d))(vs).
```
The single leading direction `v0` is read by *both* the outer covariant derivative (term 1) and the
spectator passenger slot (term 2) — it is the outermost covariant slot of the second derivative; the
inner covariant direction and the curvature/gradient slots are carried by `vs`. This is the second-
order analogue of `covGrad_pureRGenuineDiffOp_unit_eval_eq_genuineDiffCurv_add_spectator`: where the
order-`1` form reads `∇` of the order-`0` pure-Riemann curvature trace as the carrier plus the order-`0`
curvature spectator `Φ₀(∇S)`, this order-`2` form reads `∇` of the *carrier* `genuineDiffCurvSection`
(itself `∇(R-trace) − Φ₀(∇S)`) as the `T₁` curvature carrier plus the once-differentiated curvature
spectator `(∇Φ₀)(∇S)`.

This is the frame-trace entry point the integrated covariant second-Bianchi emission consumes: composing
it with the once-differentiated unit-eval (which reads `genuineDiffCurvSection` through the frame-trace
value `pureRGenuineDiffOp_zero_succ_toSection_unit_eval`) exhibits the `T₁` carrier as the second
covariant derivative of the frame-summed moving-frame pure-Riemann curvature trace `∑ᵢ R(Bᵢ, ·)(slot0 S)`
— the doubly-differentiated moving-frame curvature carrier on which the cyclic differential Bianchi
`nablaTensor0SCurv_cyclic_eq_zero` and the orthonormal-frame skew form (frame-summed) act downstream. No
pointwise per-frame moving-frame curvature jet is transited; the decomposition is purely the section-
level operator-field product rule read at the unit.

**Proof.** The section-level second B-rule inversion
`appCc_covGrad_covGrad_curvOpField_eq_covGrad_genuineDiffCurv_sub_slotExtend`, read at `x`, applied to
`d`, distributing the subtraction over the fibre value (`SmoothCcTensor.toSection_sub`,
`ContMDiffSection.coe_sub`, `Tensor0SSpace.toModel_sub`, `ContinuousMultilinearMap.sub_apply`): the
outer covariant-gradient term reads `v0` off the leading slot (`covGrad_toSection_apply_eval`) leaving
the directional derivative of `genuineDiffCurvSection` on `vs`, and the spectator term unit-evaluates by
`appCc_slotExtend_covGrad_curvOpField_covGrad_unit_eval`. -/
theorem appCc_covGrad_covGrad_curvOpField_unit_eval
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    (d : Tensor0SSpace 0 I x) (v0 : E) (vs : Fin (s + 0 + 1) → E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 0 + 1 + 1) I x from
          (appCc (I := I) (M := M) g (s + 0) (s + 0 + 1 + 1)
            (covGrad (I := I) (M := M) g (s + 0) (s + 0 + 1)
              (covGrad (I := I) (M := M) g (s + 0) (s + 0)
                (curvOpField (I := I) (M := M) g s))) S).toSection x) d)
        (Fin.cons v0 vs) =
      Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 0 + 1) I x from
            tensorCovDerivAt (I := I) (M := M) g 0 (s + 0 + 1)
              (genuineDiffCurvSection (I := I) (M := M) g s S) x v0) d)
          vs -
        Tensor0SSpace.toModel
          ((show Tensor0SSpace (s + 0) I x →L[ℝ] Tensor0SSpace (s + 0 + 1) I x from
            (covGrad (I := I) (M := M) g (s + 0) (s + 0)
              (curvOpField (I := I) (M := M) g s)).toSection x)
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 0) I x from
              tensorCovDerivAt (I := I) (M := M) g 0 (s + 0) S x v0) d))
          vs := by
  classical
  have hsec := appCc_covGrad_covGrad_curvOpField_eq_covGrad_genuineDiffCurv_sub_slotExtend
    (I := I) (M := M) g s S
  have happ :
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 0 + 1 + 1) I x from
          (appCc (I := I) (M := M) g (s + 0) (s + 0 + 1 + 1)
            (covGrad (I := I) (M := M) g (s + 0) (s + 0 + 1)
              (covGrad (I := I) (M := M) g (s + 0) (s + 0)
                (curvOpField (I := I) (M := M) g s))) S).toSection x) d =
        (covGrad (I := I) (M := M) g 0 (s + 0 + 1)
            (genuineDiffCurvSection (I := I) (M := M) g s S)).toSection x d -
          (appCc (I := I) (M := M) g (s + 0 + 1) (s + 0 + 1 + 1)
            (slotExtend (I := I) (M := M) g (s + 0) (s + 0 + 1)
              (covGrad (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s)))
            (covGrad (I := I) (M := M) g 0 (s + 0) S)).toSection x d := by
    rw [hsec]
    rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
      ContinuousLinearMap.sub_apply]
  rw [happ, Tensor0SSpace.toModel_sub, ContinuousMultilinearMap.sub_apply]
  have hT1 :
      Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 0 + 1 + 1) I x from
            (covGrad (I := I) (M := M) g 0 (s + 0 + 1)
              (genuineDiffCurvSection (I := I) (M := M) g s S)).toSection x) d)
          (Fin.cons v0 vs) =
        Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 0 + 1) I x from
            tensorCovDerivAt (I := I) (M := M) g 0 (s + 0 + 1)
              (genuineDiffCurvSection (I := I) (M := M) g s S) x v0) d)
          vs := by
    rw [covGrad_toSection_apply_eval (I := I) (M := M) g 0 (s + 0 + 1)
      (genuineDiffCurvSection (I := I) (M := M) g s S) x d (Fin.cons v0 vs)]
    have hhead : (Fin.cons v0 vs : Fin (s + 0 + 1 + 1) → E) 0 = v0 := by
      simp [Fin.cons_zero]
    have htail : Matrix.vecTail (Fin.cons v0 vs : Fin (s + 0 + 1 + 1) → E) =
        (vs : Fin (s + 0 + 1) → E) := by
      funext j; simp [Matrix.vecTail, Fin.cons_succ]
    rw [hhead, htail]
  have hT2 := appCc_slotExtend_covGrad_curvOpField_covGrad_unit_eval
    (I := I) (M := M) g s S x d v0 vs
  rw [hT1, hT2]

end Connection
end Integral
end DifferentialGeometry

end
