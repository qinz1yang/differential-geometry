import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricCovDerivPullback
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricDerivNormRestrict
import DifferentialGeometry.Geometry.Curvature.RestrictOpenRm04
import DifferentialGeometry.Geometry.Curvature.Realized.MetricFamilyContinuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Basic.Core

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Restricting a Ricci-flow solution to an open subtype

For a Ricci-flow solution `S` on `M` and an open submanifold `U`, the fixed-`U`
restriction `t ↦ (S.metric t).restrictOpen U` is a Ricci-flow solution on `U`.
This is the missing transport link (Brick 1 of the P4 conv engine): it mirrors
`SolutionPullback.lean` field by field, using the germ-locality of curvature
(`metricRm04StdAt_restrictOpen`, `metricCov_restrictOpen_*`) and the seminorm
restriction bridges instead of the diffeomorphism-pullback lemmas.

## Curvature restriction lemmas (this section)

* `ricciTensor_restrictOpen` — Ricci is unchanged by restriction (trace of the
  banked `metricRm04StdAt_restrictOpen`).
* `metricRicci_restrictOpen_eval` — the bundled `(0,2)` Ricci section restricts.
* `metricScalarAt_restrictOpen` — scalar curvature is unchanged by restriction.
-/

noncomputable section

open Set Function Filter Bundle Manifold Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.RicciFlow (SolutionOn IsSolutionOn MetricVariationEquationOn
  ricciNorm SolutionFamily RicciAtFamily)

namespace DifferentialGeometry
namespace HCGCompactness

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M]
  [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]

/-- **Germ-locality of the Ricci tensor.**  Restricting a metric to an open
submanifold does not change its Ricci tensor at interior points.  Proved from the
orthonormal-basis trace form `ricciTensor_eq_orthonormal_trace`, the banked
`(0,4)` germ-locality `metricRm04StdAt_restrictOpen`, and the `Rm04 ↔ riemannOp`
bridge `metricRm04StdAt_eq_inner_riemannOp`.  Unlike the pullback case there is no
`mfderiv`: the tangent vectors are literally shared between `U` and `M`. -/
theorem ricciTensor_restrictOpen
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    [SigmaCompactSpace U] [T2Space U] [BoundarylessManifold I U]
    [IsManifold I 1 U] [IsManifold I ((∞ : WithTop ℕ∞) + 1) U]
    (x : U) (v w : TangentSpace I x) :
    ricciTensor (I := I) (M := U) (g.restrictOpen (I := I) U) x v w
      = ricciTensor (I := I) (M := M) g (x : M) v w := by
  classical
  obtain ⟨B, hB⟩ := exists_gOrthonormalBasis (I := I) (M := M) g (x : M)
  have hBU : ∀ i j,
      (g.restrictOpen (I := I) U).inner x (B i) (B j) = if i = j then (1 : ℝ) else 0 := by
    intro i j
    rw [SmoothRiemannianMetric.restrictOpen_inner]
    exact hB i j
  rw [ricciTensor_eq_orthonormal_trace (I := I) (M := U) (g.restrictOpen (I := I) U) x v w B hBU,
    ricciTensor_eq_orthonormal_trace (I := I) (M := M) g (x : M) v w B hB]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [(g.restrictOpen (I := I) U).symm x
        (riemannOp (LeviCivita (I := I) (g.restrictOpen (I := I) U)) x (B i) v w) (B i),
    ← metricRm04StdAt_eq_inner_riemannOp (I := I) (M := U) (g.restrictOpen (I := I) U)
        x (B i) v w (B i),
    metricRm04StdAt_restrictOpen (I := I) g U x (B i) v w (B i),
    metricRm04StdAt_eq_inner_riemannOp (I := I) (M := M) g (x : M) (B i) v w (B i),
    g.symm (x : M) (B i) (riemannOp (LeviCivita (I := I) g) (x : M) (B i) v w)]

/-- The bundled `(0,2)` Ricci section restricts: `metricRicci (g.restrictOpen U) x slots
= metricRicci g x slots` (shared slots).  Mirrors `metricRicci_pullback_eval`. -/
theorem metricRicci_restrictOpen_eval
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    [SigmaCompactSpace U] [T2Space U] [BoundarylessManifold I U]
    [IsManifold I 1 U] [IsManifold I ((∞ : WithTop ℕ∞) + 1) U]
    (x : U) (slots : Fin 2 → TangentSpace I x) :
    metricRicci (I := I) (M := U) (g.restrictOpen (I := I) U) x slots
      = metricRicci (I := I) (M := M) g (x : M) slots := by
  have hLHS : metricRicci (I := I) (M := U) (g.restrictOpen (I := I) U) x slots
      = ricciTensor (I := I) (M := U) (g.restrictOpen (I := I) U) x (slots 0) (slots 1) := by
    have hcmm : metricRicciAt (I := I) (M := U) (g.restrictOpen (I := I) U) x slots
        = metricRicciAt (I := I) (M := U) (g.restrictOpen (I := I) U) x (vec2 (slots 0) (slots 1)) :=
      congrArg _ (by funext i; fin_cases i <;> rfl)
    rw [metricRicci_apply, hcmm]
    exact metricRicciAt_apply_eq_ricciTensor (I := I) (g.restrictOpen (I := I) U) x (slots 0) (slots 1)
  have hRHS : metricRicci (I := I) (M := M) g (x : M) slots
      = ricciTensor (I := I) (M := M) g (x : M) (slots 0) (slots 1) := by
    have hcmm : metricRicciAt (I := I) (M := M) g (x : M) slots
        = metricRicciAt (I := I) (M := M) g (x : M) (vec2 (slots 0) (slots 1)) :=
      congrArg _ (by funext i; fin_cases i <;> rfl)
    rw [metricRicci_apply, hcmm]
    exact metricRicciAt_apply_eq_ricciTensor (I := I) g (x : M) (slots 0) (slots 1)
  rw [hLHS, hRHS]
  exact ricciTensor_restrictOpen (I := I) g U x (slots 0) (slots 1)

/-- **Germ-locality of scalar curvature.**  Scalar curvature is unchanged by
restricting the metric to an open submanifold.  Mirrors `metricScalarAt_pullback`
via the orthonormal-basis trace of Ricci and `ricciTensor_restrictOpen`. -/
theorem metricScalarAt_restrictOpen
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    [SigmaCompactSpace U] [T2Space U] [BoundarylessManifold I U]
    [IsManifold I 1 U] [IsManifold I ((∞ : WithTop ℕ∞) + 1) U]
    (x : U) :
    metricScalarAt (I := I) (M := U) (g.restrictOpen (I := I) U) x
      = metricScalarAt (I := I) (M := M) g (x : M) := by
  classical
  obtain ⟨basis, hON⟩ := exists_gOrthonormalBasis (I := I) (M := M) g (x : M)
  have hONU : ∀ i j,
      (g.restrictOpen (I := I) U).inner x (basis i) (basis j) = if i = j then (1 : ℝ) else 0 := by
    intro i j
    rw [SmoothRiemannianMetric.restrictOpen_inner]
    exact hON i j
  have hinvU : MetricInverseInBasis_gen (I := I) (M := U) (g.restrictOpen (I := I) U) x basis
      (identityInvMetric (Idx := Fin (Module.finrank ℝ (TangentSpace I x)))) := by
    simpa [identityInvMetric, diagonalInvMetric] using
      metricInverseInBasis_of_orthonormal (I := I) (M := U) (g.restrictOpen (I := I) U) basis hONU
  have hinvM : MetricInverseInBasis_gen (I := I) (M := M) g (x : M) basis
      (identityInvMetric (Idx := Fin (Module.finrank ℝ (TangentSpace I x)))) := by
    simpa [identityInvMetric, diagonalInvMetric] using
      metricInverseInBasis_of_orthonormal (I := I) (M := M) g basis hON
  rw [metricScalarAt_def, metricScalarAt_def,
    metricTracePair0SAt_eq_sum_basis (I := I) (M := U) (g.restrictOpen (I := I) U) basis
      (identityInvMetric (Idx := Fin (Module.finrank ℝ (TangentSpace I x)))) hinvU
      (metricRicciAt (I := I) (M := U) (g.restrictOpen (I := I) U) x),
    metricTracePair0SAt_eq_sum_basis (I := I) (M := M) g basis
      (identityInvMetric (Idx := Fin (Module.finrank ℝ (TangentSpace I x)))) hinvM
      (metricRicciAt (I := I) (M := M) g (x : M))]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  have e1 : metricRicciAt (I := I) (M := U) (g.restrictOpen (I := I) U) x (vec2 (basis i) (basis j))
      = ricciTensor (I := I) (M := U) (g.restrictOpen (I := I) U) x (basis i) (basis j) :=
    metricRicciAt_apply_eq_ricciTensor (I := I) (g.restrictOpen (I := I) U) x (basis i) (basis j)
  have e2 : metricRicciAt (I := I) (M := M) g (x : M) (vec2 (basis i) (basis j))
      = ricciTensor (I := I) (M := M) g (x : M) (basis i) (basis j) :=
    metricRicciAt_apply_eq_ricciTensor (I := I) g (x : M) (basis i) (basis j)
  have hric : metricRicciAt (I := I) (M := U) (g.restrictOpen (I := I) U) x
        (vec2 (basis i) (basis j))
      = metricRicciAt (I := I) (M := M) g (x : M) (vec2 (basis i) (basis j)) := by
    rw [e1, e2]
    exact ricciTensor_restrictOpen (I := I) g U x (basis i) (basis j)
  exact congrArg (fun r => identityInvMetric i j * r) hric

/-- The bundled lowered Riemann `(0,4)` section restricts (evaluated form):
`metricRm04 (g.restrictOpen U) x slots = metricRm04 g ↑x slots` (shared slots).  The `(0,4)`
analog of `metricRicci_restrictOpen_eval`, using the banked germ-locality
`metricRm04StdAt_restrictOpen` after the `metricRm04_apply`/`metricRm04StdAt_apply` bridge to
`metricRm04StdAt` on `vec4` slots. -/
theorem metricRm04_restrictOpen_eval
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    [SigmaCompactSpace U] [T2Space U] [BoundarylessManifold I U]
    [IsManifold I 1 U] [IsManifold I ((∞ : WithTop ℕ∞) + 1) U]
    (x : U) (slots : Fin 4 → TangentSpace I x) :
    metricRm04 (I := I) (M := U) (g.restrictOpen (I := I) U) x slots
      = metricRm04 (I := I) (M := M) g (x : M) slots := by
  have hLHS : metricRm04 (I := I) (M := U) (g.restrictOpen (I := I) U) x slots
      = metricRm04StdAt (I := I) (M := U) (g.restrictOpen (I := I) U) x
          (slots 0) (slots 1) (slots 2) (slots 3) := by
    have hcmm : metricRm04 (I := I) (M := U) (g.restrictOpen (I := I) U) x slots
        = metricRm04 (I := I) (M := U) (g.restrictOpen (I := I) U) x
            (vec4 (slots 0) (slots 1) (slots 2) (slots 3)) :=
      congrArg _ (by funext i; fin_cases i <;> rfl)
    rw [hcmm, metricRm04_apply]
    exact (metricRm04StdAt_apply (I := I) (M := U) (g.restrictOpen (I := I) U) x
      (slots 0) (slots 1) (slots 2) (slots 3)).symm
  have hRHS : metricRm04 (I := I) (M := M) g (x : M) slots
      = metricRm04StdAt (I := I) (M := M) g (x : M)
          (slots 0) (slots 1) (slots 2) (slots 3) := by
    have hcmm : metricRm04 (I := I) (M := M) g (x : M) slots
        = metricRm04 (I := I) (M := M) g (x : M)
            (vec4 (slots 0) (slots 1) (slots 2) (slots 3)) :=
      congrArg _ (by funext i; fin_cases i <;> rfl)
    rw [hcmm, metricRm04_apply]
    exact (metricRm04StdAt_apply (I := I) (M := M) g (x : M)
      (slots 0) (slots 1) (slots 2) (slots 3)).symm
  rw [hLHS, hRHS]
  exact metricRm04StdAt_restrictOpen (I := I) g U x (slots 0) (slots 1) (slots 2) (slots 3)

/-! ## The restricted Ricci-flow solution (9-field assembly)

`solutionOn_restrictOpen S U : SolutionOn (M := U) D` with
`base.metric t = (S.base.metric t).restrictOpen U`, together with the nine
`IsSolutionOn` fields.  Mirrors `SolutionPullback.isSolutionOn_pullback` along the
open inclusion `U ↪ M`. -/

variable {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}

/-- The restricted Ricci-flow solution data: `t ↦ (S.metric t).restrictOpen U`. -/
def solutionOn_restrictOpen
    (S : SolutionOn (I := I) (M := M) D) (U : TopologicalSpace.Opens M)
    [SigmaCompactSpace U] [T2Space U] :
    SolutionOn (I := I) (M := U) D where
  base := { metric := fun t => (S.base.metric t).restrictOpen (I := I) U }

open Classical in
/-- Smoothness of the inclusion-pushed frame section at a point of the image
`Subtype.val '' u`.  The section value is `tangentMap Subtype.val` on the `C∞` frame section on
`U`, reindexed by the `C∞` corestriction. -/
theorem restrictOpenPush_contMDiffWithinAt
    {Idx : Type} (U : TopologicalSpace.Opens M)
    [SigmaCompactSpace U] [T2Space U] [IsManifold I 1 U] [IsManifold I ((∞ : WithTop ℕ∞) + 1) U]
    {frame : Idx → (x : U) → TangentSpace I x} {u : Set U}
    (hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u) (i : Idx) (x : U) (hxu : x ∈ u) :
    ContMDiffWithinAt I (I.prod 𝓘(ℝ, E)) (∞ : WithTop ℕ∞)
      (fun y : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) y
        (if h : y ∈ U then frame i ⟨y, h⟩ else 0)) (Subtype.val '' u) (x : M) := by
  haveI : Inhabited U := ⟨x⟩
  -- Total corestriction `cor : M → U`, equal to `y ↦ ⟨y, ·⟩` on `U`.
  set cor : M → U := fun y => if h : y ∈ U then ⟨y, h⟩ else default with hcor_def
  -- `cor` is `C∞` at `↑x`: precomposed with `Subtype.val` it is the identity on `U`
  -- (`contMDiffAt_subtype_iff`).
  have hcorval : ∀ z : U, cor (z : M) = z := by
    intro z; rw [hcor_def]; simp only [dif_pos z.2, Subtype.coe_eta]
  have hcor : ContMDiffAt I I (∞ : WithTop ℕ∞) cor (x : M) := by
    rw [← contMDiffAt_subtype_iff (I := I) (I' := I) (U := U) (n := ∞) (x := x)]
    have hid : (fun z : U => cor (z : M)) = id := by funext z; simpa using hcorval z
    rw [hid]
    exact contMDiffAt_id
  -- The pushed frame section on `U` (`tangentMap Subtype.val ∘ (T% frame i)`), as a within-`u` fact.
  have hpush : ContMDiffWithinAt I (I.prod 𝓘(ℝ, E)) (∞ : WithTop ℕ∞)
      (fun z : U => tangentMap I I (Subtype.val : U → M)
        (TotalSpace.mk' E (E := fun w : U => TangentSpace I w) z (frame i z))) u x :=
    ((contMDiff_subtype_val (I := I) (U := U) (n := ∞)).contMDiff_tangentMap
      (by simp)).contMDiffAt.comp_contMDiffWithinAt x (hframe.contMDiffOn i x hxu)
  -- `cor` maps `Subtype.val '' u` into `u`.
  have hmaps : Set.MapsTo cor (Subtype.val '' u) u := by
    rintro y ⟨z, hz, rfl⟩
    rw [hcorval z]; exact hz
  -- `hpush` transported to the point `cor ↑x`.
  have hpush' : ContMDiffWithinAt I (I.prod 𝓘(ℝ, E)) (∞ : WithTop ℕ∞)
      (fun z : U => tangentMap I I (Subtype.val : U → M)
        (TotalSpace.mk' E (E := fun w : U => TangentSpace I w) z (frame i z))) u (cor (x : M)) := by
    rw [hcorval x]; exact hpush
  -- On `U`, `(g ∘ cor) z = ⟨z, frame i ⟨z, ·⟩⟩` (mfderiv Subtype.val = id), matching the target.
  have hgcor : ∀ z : M, (hz : z ∈ U) →
      (fun z : U => tangentMap I I (Subtype.val : U → M)
        (TotalSpace.mk' E (E := fun w : U => TangentSpace I w) z (frame i z))) (cor z)
        = TotalSpace.mk' E (E := fun w : M => TangentSpace I w) z
            (if h : z ∈ U then frame i ⟨z, h⟩ else 0) := by
    intro z hz
    have hcz : cor z = ⟨z, hz⟩ := by simp only [hcor_def, dif_pos hz]
    rw [dif_pos hz, hcz]
    show tangentMap I I (Subtype.val : U → M)
        (TotalSpace.mk' E (E := fun w : U => TangentSpace I w) (⟨z, hz⟩ : U) (frame i ⟨z, hz⟩))
      = TotalSpace.mk' E (E := fun w : M => TangentSpace I w) z (frame i ⟨z, hz⟩)
    show TotalSpace.mk' E (E := fun w : M => TangentSpace I w) ((⟨z, hz⟩ : U) : M)
        (mfderiv I I (Subtype.val : U → M) (⟨z, hz⟩ : U) (frame i ⟨z, hz⟩))
      = TotalSpace.mk' E (E := fun w : M => TangentSpace I w) z (frame i ⟨z, hz⟩)
    rw [mfderiv_subtype_val_apply]
  -- Compose: `s_M = (pushed section) ∘ cor` on `Subtype.val '' u`.
  refine (hpush'.comp (x : M) hcor.contMDiffWithinAt hmaps).congr_of_eventuallyEq ?_ ?_
  · filter_upwards [nhdsWithin_le_nhds ((U.isOpen).mem_nhds x.2)] with z hz
    exact (hgcor z hz).symm
  · exact (hgcor (x : M) x.2).symm

open Classical in
/-- **Pushforward of a `C∞` local frame under the open inclusion `U ↪ M`.**  For a `C∞` local
frame `frame` on `u ⊆ U`, the family `y ↦ frame · ⟨y, ·⟩` (padded with `0` off `U`) is a `C∞`
local frame on `Subtype.val '' u ⊆ M`.  Basis-ness transports because `frameM k ↑x = frame k x`
(the fibers `TangentSpace I x` / `TangentSpace I ↑x` are the shared model fiber `E`); smoothness is
`tangentMap Subtype.val` applied to the frame section, precomposed with the `C∞` corestriction
`y ↦ ⟨y, ·⟩` (`contMDiffAt_subtype_iff`). -/
theorem isLocalFrameOn_restrictOpenPush
    {Idx : Type} (U : TopologicalSpace.Opens M)
    [SigmaCompactSpace U] [T2Space U] [IsManifold I 1 U] [IsManifold I ((∞ : WithTop ℕ∞) + 1) U]
    {frame : Idx → (x : U) → TangentSpace I x} {u : Set U}
    (hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u) :
    IsLocalFrameOn (V := (TangentSpace I : M → Type _)) I E (∞ : WithTop ℕ∞)
      (fun i (y : M) => if h : y ∈ U then frame i ⟨y, h⟩ else 0) (Subtype.val '' u) where
  linearIndependent {y} hy := by
    obtain ⟨x, hxu, rfl⟩ := hy
    have hxU : (x : M) ∈ U := x.2
    have hval : (fun i => if h : (x : M) ∈ U then frame i ⟨(x : M), h⟩ else 0)
        = fun i => frame i x := by
      funext i; rw [dif_pos hxU]
    exact hval ▸ hframe.linearIndependent hxu
  generating {y} hy := by
    obtain ⟨x, hxu, rfl⟩ := hy
    have hxU : (x : M) ∈ U := x.2
    have hval : (fun i => if h : (x : M) ∈ U then frame i ⟨(x : M), h⟩ else 0)
        = fun i => frame i x := by
      funext i; rw [dif_pos hxU]
    exact hval ▸ hframe.generating hxu
  contMDiffOn i := by
    -- On `Subtype.val '' u`, the pushed section equals `tangentMap Subtype.val` applied to the
    -- `C∞` frame section on `U`, reindexed by the corestriction `cores y = ⟨y, ·⟩`.  `cores` is
    -- `C∞` on `Subtype.val '' u` (Mathlib `contMDiffAt_subtype_iff`).
    intro y hy
    obtain ⟨x, hxu, rfl⟩ := hy
    exact restrictOpenPush_contMDiffWithinAt (I := I) U hframe i x hxu

/-- **`frameCompSmooth` transport under the open inclusion.**  For a `C∞` frame `frame` on
`u ⊆ U`, the restricted metric coefficient `(t, x) ↦ ((S.metric t).restrictOpen U).inner x
(frame i x) (frame j x)` is jointly `C∞` on `D.regular ×ˢ u`.  Route: push `frame` to the `C∞`
frame `frameM` on `Subtype.val '' u ⊆ M` (`isLocalFrameOn_restrictOpenPush`); apply
`hS.smoothMetric.frameCompSmooth frameM`; precompose with the `C∞` spacetime inclusion
`(t, x) ↦ (t, ↑x)` and collapse `frameM ↑x = frame x` (`restrictOpen_inner`). -/
theorem frameCompSmooth_restrictOpen
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (U : TopologicalSpace.Opens M)
    [SigmaCompactSpace U] [T2Space U] [BoundarylessManifold I U]
    [IsManifold I 1 U] [IsManifold I ((∞ : WithTop ℕ∞) + 1) U]
    {Idx : Type} [Fintype Idx] (frame : Idx → (x : U) → TangentSpace I x) {u : Set U}
    (hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u) (i j : Idx) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × U =>
        ((solutionOn_restrictOpen (I := I) S U).family.metric p.1).inner p.2
          (frame i p.2) (frame j p.2))
      (D.regular ×ˢ u) := by
  classical
  -- The pushed frame on `Subtype.val '' u ⊆ M` and `M`'s frameCompSmooth against it.
  set frameM : Idx → (y : M) → TangentSpace I y :=
    fun k (y : M) => if h : y ∈ U then frame k ⟨y, h⟩ else 0 with hframeM_def
  have hframeM : IsLocalFrameOn (V := (TangentSpace I : M → Type _)) I E (∞ : WithTop ℕ∞)
      frameM (Subtype.val '' u) := isLocalFrameOn_restrictOpenPush (I := I) U hframe
  have hpf := hS.smoothMetric.frameCompSmooth frameM hframeM i j
  -- The `C∞` spacetime inclusion `ρ (t, x) = (t, ↑x)`.
  have hmap : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) (∞ : WithTop ℕ∞)
      (fun p : ℝ × U => (p.1, (p.2 : M))) :=
    contMDiff_fst.prodMk ((contMDiff_subtype_val (I := I) (U := U)).comp contMDiff_snd)
  have hmaps : Set.MapsTo (fun p : ℝ × U => (p.1, (p.2 : M)))
      (D.regular ×ˢ u) (D.regular ×ˢ (Subtype.val '' u)) :=
    fun p hp => ⟨hp.1, Set.mem_image_of_mem _ hp.2⟩
  have hcomp := hpf.comp hmap.contMDiffOn hmaps
  refine hcomp.congr ?_
  intro p hp
  have hxU : (p.2 : M) ∈ U := p.2.2
  have hval : ∀ k, frameM k (p.2 : M) = frame k p.2 := by
    intro k
    rw [hframeM_def]
    simp only [dif_pos hxU]
  simp only [Function.comp_apply, hval]
  rfl

/-- **Smoothness of the restricted metric family.**  The scalar coefficient fields
transport by the definitional rewrite `restrictOpen_inner` (the point/vectors are literally
shared with `↑x`); `metricTensor_cont` is `Tensor0SFamilyContinuousOnSet.restrictOpen`; and
`frameCompSmooth` transports the C∞ frame components along the open inclusion. -/
theorem metricFamilySmoothOn_restrictOpen
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (U : TopologicalSpace.Opens M)
    [SigmaCompactSpace U] [T2Space U] [BoundarylessManifold I U]
    [IsManifold I 1 U] [IsManifold I ((∞ : WithTop ℕ∞) + 1) U] :
    MetricFamilySmoothOn (I := I) D (solutionOn_restrictOpen (I := I) S U).family where
  coeff x X Y := hS.smoothMetric.coeff (x : M) X Y
  coeff_cont x X Y := hS.smoothMetric.coeff_cont (x : M) X Y
  metricTensor_cont := by
    apply Tensor0SFamilyContinuousOnSet.congr
      (Tensor0SFamilyContinuousOnSet.restrictOpen (I := I)
        (fun t x => Tensor0SBundle.metricTensorField (I := I) (S.family.metric t) x)
        hS.smoothMetric.metricTensor_cont U)
    intro t _ht x
    ext slots
    rfl
  frameCompSmooth := by
    intro Idx _ frame u hframe i j
    exact frameCompSmooth_restrictOpen (I := I) S hS U frame hframe i j

/-- **The restricted flow satisfies the Ricci-flow metric equation.**
`∂ₜ(g.restrictOpen U) = -2 Ric(g.restrictOpen U)`, from `S`'s equation via `restrictOpen_inner`
(coefficient) and `ricciTensor_restrictOpen` (Ricci germ-locality). -/
theorem metricVariationEquation_restrictOpen
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (U : TopologicalSpace.Opens M)
    [SigmaCompactSpace U] [T2Space U] [BoundarylessManifold I U]
    [IsManifold I 1 U] [IsManifold I ((∞ : WithTop ℕ∞) + 1) U] :
    MetricVariationEquationOn (I := I) (solutionOn_restrictOpen (I := I) S U) := by
  intro t x X Y
  have hric :
      RicciAtFamily.toTensorField (I := I)
          (solutionOn_restrictOpen (I := I) S U).ricciAt (t : ℝ) x X Y
        = RicciAtFamily.toTensorField (I := I) S.ricciAt (t : ℝ) (x : M) X Y := by
    simp only [RicciAtFamily.toTensorField_apply]
    change metricRicciAt (I := I)
          ((S.base.metric (t : ℝ)).restrictOpen (I := I) U) x (vec2 X Y)
        = metricRicciAt (I := I) (S.base.metric (t : ℝ)) (x : M) (vec2 X Y)
    rw [metricRicciAt_apply_eq_ricciTensor, metricRicciAt_apply_eq_ricciTensor]
    exact ricciTensor_restrictOpen (I := I) (S.base.metric (t : ℝ)) U x X Y
  rw [hric]
  exact hS.equation t (x : M) X Y

/-- The restricted scalar curvature equals the original at `↑x` (`metricScalarAt_restrictOpen`). -/
theorem scalar_restrictOpen
    (S : SolutionOn (I := I) (M := M) D) (U : TopologicalSpace.Opens M)
    [SigmaCompactSpace U] [T2Space U] [BoundarylessManifold I U]
    [IsManifold I 1 U] [IsManifold I ((∞ : WithTop ℕ∞) + 1) U]
    (t : ℝ) (x : U) :
    (solutionOn_restrictOpen (I := I) S U).scalar t x = S.scalar t (x : M) := by
  simp only [SolutionOn.scalar, SolutionFamily.scalar, solutionOn_restrictOpen]
  exact metricScalarAt_restrictOpen (I := I) (S.base.metric t) U x

/-- **Spacetime continuity of the restricted scalar curvature** (`scalarCont`): transport
`hS.scalarCont` along the continuous inclusion `(t, x) ↦ (t, ↑x)` via `scalar_restrictOpen`. -/
theorem scalarCont_restrictOpen
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (U : TopologicalSpace.Opens M)
    [SigmaCompactSpace U] [T2Space U] [BoundarylessManifold I U]
    [IsManifold I 1 U] [IsManifold I ((∞ : WithTop ℕ∞) + 1) U] :
    ContinuousOn (fun q : ℝ × U => (solutionOn_restrictOpen (I := I) S U).scalar q.1 q.2)
      (D.carrier ×ˢ (Set.univ : Set U)) := by
  have heq : (fun q : ℝ × U => (solutionOn_restrictOpen (I := I) S U).scalar q.1 q.2)
      = (fun p : ℝ × M => S.scalar p.1 p.2)
          ∘ (fun q : ℝ × U => ((q.1, (q.2 : M)) : ℝ × M)) := by
    funext q; exact scalar_restrictOpen (I := I) S U q.1 q.2
  rw [heq]
  exact hS.scalarCont.comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).continuousOn
    (fun q hq => ⟨hq.1, Set.mem_univ _⟩)

/-- **Within-time differentiability of the restricted scalar curvature** (`scalarTime`): for
fixed `x` only the time varies, so it transports from `hS.scalarTime` at `↑x` via
`scalar_restrictOpen`. -/
theorem scalarTime_restrictOpen
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (U : TopologicalSpace.Opens M)
    [SigmaCompactSpace U] [T2Space U] [BoundarylessManifold I U]
    [IsManifold I 1 U] [IsManifold I ((∞ : WithTop ℕ∞) + 1) U]
    {K : Set ℝ} {t : ℝ} (htK : t ∈ K) (hKsub : K ⊆ D.carrier) (x : U) :
    DifferentiableWithinAt ℝ
      (fun s : ℝ => (solutionOn_restrictOpen (I := I) S U).scalar s x) K t := by
  have heq : (fun s : ℝ => (solutionOn_restrictOpen (I := I) S U).scalar s x)
      = fun s : ℝ => S.scalar s (x : M) := by
    funext s; exact scalar_restrictOpen (I := I) S U s x
  rw [heq]
  exact hS.scalarTime htK hKsub (x : M)

/-- **Total-space continuity of the restricted Ricci tensor family** (`ricciCont`): transport
`hS.ricciCont` by `Tensor0SFamilyContinuousOnSet.restrictOpen`, then identify with
`(solutionOn_restrictOpen S U).ricci` via `metricRicci_restrictOpen_eval`. -/
theorem ricciCont_restrictOpen
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (U : TopologicalSpace.Opens M)
    [SigmaCompactSpace U] [T2Space U] [BoundarylessManifold I U]
    [IsManifold I 1 U] [IsManifold I ((∞ : WithTop ℕ∞) + 1) U] :
    Tensor0SFamilyContinuousOnSet (I := I) (M := U) 2 D.carrier
      (fun t x => (solutionOn_restrictOpen (I := I) S U).ricci t x) := by
  apply Tensor0SFamilyContinuousOnSet.congr
    (Tensor0SFamilyContinuousOnSet.restrictOpen (I := I)
      (fun t x => S.ricci t x) hS.ricciCont U)
  intro t _ht x
  ext slots
  exact (metricRicci_restrictOpen_eval (I := I) (S.base.metric t) U x slots).symm

/-- **Total-space continuity of the restricted lowered Riemann tensor family** (`rm04Cont`):
transport `hS.rm04Cont` by `Tensor0SFamilyContinuousOnSet.restrictOpen`, then identify with
`(solutionOn_restrictOpen S U).base.rm04` via `metricRm04_restrictOpen_eval`. -/
theorem rm04Cont_restrictOpen
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (U : TopologicalSpace.Opens M)
    [SigmaCompactSpace U] [T2Space U] [BoundarylessManifold I U]
    [IsManifold I 1 U] [IsManifold I ((∞ : WithTop ℕ∞) + 1) U] :
    Tensor0SFamilyContinuousOnSet (I := I) (M := U) 4 D.carrier
      (fun t x => (solutionOn_restrictOpen (I := I) S U).base.rm04 t x) := by
  apply Tensor0SFamilyContinuousOnSet.congr
    (Tensor0SFamilyContinuousOnSet.restrictOpen (I := I)
      (fun t x => S.base.rm04 t x) hS.rm04Cont U)
  intro t _ht x
  ext slots
  exact (metricRm04_restrictOpen_eval (I := I) (S.base.metric t) U x slots).symm

/-- The restricted Ricci norm `|Ric|²` equals the original at `↑x` (isometry/germ invariant): via
`normSq0S_restrictOpen_apply` (banked tensor-norm invariance) with `metricRicci_restrictOpen_eval`. -/
theorem ricciNorm_restrictOpen
    (S : SolutionOn (I := I) (M := M) D) (U : TopologicalSpace.Opens M)
    [SigmaCompactSpace U] [T2Space U] [BoundarylessManifold I U]
    [IsManifold I 1 U] [IsManifold I ((∞ : WithTop ℕ∞) + 1) U]
    (t : ℝ) (x : U) :
    ricciNorm (I := I) (solutionOn_restrictOpen (I := I) S U) t x
      = ricciNorm (I := I) S t (x : M) := by
  -- `ricciNorm` unfolds to `normSq0S` of the (restricted) Ricci section; the tensor-norm is
  -- unchanged by restriction (`normSq0S_restrictOpen_apply`), and the two Ricci sections agree
  -- slotwise (`metricRicci_restrictOpen_eval`).
  have hsec : metricRicci (I := I) (M := U) ((S.base.metric t).restrictOpen (I := I) U) x
      = metricRicci (I := I) (M := M) (S.base.metric t) (x : M) := by
    ext slots
    exact metricRicci_restrictOpen_eval (I := I) (S.base.metric t) U x slots
  have hnorm := normSq0S_restrictOpen_apply (I := I) (S.base.metric t) U 2 x
    (metricRicci (I := I) (M := U) ((S.base.metric t).restrictOpen (I := I) U) x)
  simp only [ricciNorm, SolutionOn.ricci, SolutionOn.family, SolutionFamily.ricci_apply,
    SolutionFamily.ricciAt, metricRicci_apply, solutionOn_restrictOpen] at *
  rw [hnorm, hsec]

/-- **Fixed-time spatial differentiability of the restricted Ricci norm** (`ricciNormSpace`):
`ricciNorm (restrictOpen S) t` is `C∞` on `U` (`normSq02_smooth`), hence `MDifferentiableAt`. -/
theorem ricciNormSpace_restrictOpen
    (S : SolutionOn (I := I) (M := M) D) (U : TopologicalSpace.Opens M)
    [SigmaCompactSpace U] [T2Space U] [BoundarylessManifold I U]
    [IsManifold I 1 U] [IsManifold I ((∞ : WithTop ℕ∞) + 1) U]
    (t : ℝ) (x : U) :
    MDifferentiableAt I 𝓘(ℝ, ℝ)
      (ricciNorm (I := I) (solutionOn_restrictOpen (I := I) S U) t) x := by
  have hsmooth : ContMDiff I 𝓘(ℝ, ℝ) (∞ : WithTop ℕ∞)
      (ricciNorm (I := I) (solutionOn_restrictOpen (I := I) S U) t) := by
    refine (DifferentialGeometry.Integral.Connection.normSq02_smooth (I := I) (M := U)
      ((solutionOn_restrictOpen (I := I) S U).family.metric t)
      (metricRicci (I := I) (M := U)
        ((solutionOn_restrictOpen (I := I) S U).family.metric t))).congr ?_
    intro y
    simp only [ricciNorm, SolutionOn.ricci, SolutionOn.family,
      SolutionFamily.ricci_apply, SolutionFamily.ricciAt, metricRicci_apply]
  exact hsmooth.contMDiffAt.mdifferentiableAt (by simp)

/-- **Smoothness of the restricted connection family** (`smoothConnection`): no transport needed —
the family connection is the Levi-Civita connection of `(S.metric t).restrictOpen U`, whose
smoothness is the general `leviCivitaConnectionOfMetric_contMDiffCovariantDerivative`. -/
theorem smoothConnection_restrictOpen
    (S : SolutionOn (I := I) (M := M) D) (U : TopologicalSpace.Opens M)
    [SigmaCompactSpace U] [T2Space U] [BoundarylessManifold I U]
    [IsManifold I 1 U] [IsManifold I ((∞ : WithTop ℕ∞) + 1) U] :
    ConnectionFamilySmoothOn (I := I) (solutionOn_restrictOpen (I := I) S U).family := by
  intro t
  exact leviCivitaConnectionOfMetric_contMDiffCovariantDerivative (I := I)
    ((solutionOn_restrictOpen (I := I) S U).base.metric (t : ℝ))

/-- **The restricted metric family is a Ricci-flow solution.**  For an open submanifold `U ↪ M`
and an `IsSolutionOn` candidate `S` on `M`, the fixed-`U` restriction
`t ↦ (S.metric t).restrictOpen U` satisfies all nine `IsSolutionOn` fields on `U`.  This is
Brick 1 of the P4 conv engine: the restriction-analog of `SolutionPullback.isSolutionOn_pullback`,
along the open inclusion instead of a diffeomorphism. -/
theorem isSolutionOn_restrictOpen
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (U : TopologicalSpace.Opens M)
    [SigmaCompactSpace U] [T2Space U] [BoundarylessManifold I U]
    [IsManifold I 1 U] [IsManifold I ((∞ : WithTop ℕ∞) + 1) U] :
    IsSolutionOn (I := I) (solutionOn_restrictOpen (I := I) S U) where
  smoothMetric := metricFamilySmoothOn_restrictOpen (I := I) S hS U
  smoothConnection := smoothConnection_restrictOpen (I := I) S U
  equation := metricVariationEquation_restrictOpen (I := I) S hS U
  scalarCont := scalarCont_restrictOpen (I := I) S hS U
  scalarTime := fun htK hKsub x => scalarTime_restrictOpen (I := I) S hS U htK hKsub x
  ricciCont := ricciCont_restrictOpen (I := I) S hS U
  rm04Cont := rm04Cont_restrictOpen (I := I) S hS U
  ricciNormSpace := fun t _ht x => ricciNormSpace_restrictOpen (I := I) S U t x
  ricciNormGrad := by
    intro t _ht x
    have hsmooth : ContMDiff I 𝓘(ℝ, ℝ) (∞ : WithTop ℕ∞)
        (ricciNorm (I := I) (solutionOn_restrictOpen (I := I) S U) t) := by
      refine (DifferentialGeometry.Integral.Connection.normSq02_smooth (I := I) (M := U)
        ((solutionOn_restrictOpen (I := I) S U).family.metric t)
        (metricRicci (I := I) (M := U)
          ((solutionOn_restrictOpen (I := I) S U).family.metric t))).congr ?_
      intro y
      simp only [ricciNorm, SolutionOn.ricci, SolutionOn.family,
        SolutionFamily.ricci_apply, SolutionFamily.ricciAt, metricRicci_apply]
    exact DifferentialGeometry.Integral.Connection.gradientFun_mdiffAt (I := I)
      ((solutionOn_restrictOpen (I := I) S U).family.metric t) hsmooth x

end HCGCompactness
end DifferentialGeometry
