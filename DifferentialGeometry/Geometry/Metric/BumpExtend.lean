import DifferentialGeometry.Geometry.Metric.SmoothMetricFromCoeff
import DifferentialGeometry.Geometry.Metric.OpenSubtype
import DifferentialGeometry.Geometry.Curvature.Riemann.Basic.Field

/-!
# Bump extension of a partial Riemannian metric to a total smooth metric

Given a smooth Riemannian metric `gU` defined only on an **open subtype**
`U : TopologicalSpace.Opens M`, a global fallback metric `R` on all of `M`, and a smooth bump
`χ : M → ℝ` valued in `[0,1]` with `tsupport χ ⊆ U`, the fiberwise form

`(R.bumpExtendOpen U gU χ).inner x = χ x • (gU extended by 0) x + (1 - χ x) • R.inner x`

is a genuine smooth Riemannian metric on all of `M`.  The extension-by-`0` of `gU` is the
fiberwise bilinear form `fun x => if hx : x ∈ U then gU.inner ⟨x,hx⟩ else 0`; the tangent fibers
over `(⟨x,hx⟩ : U)` and `(x : M)` are definitionally equal in this project (see
`OpenSubtype.lean`), so no transport is needed.

This is the **Step-D bump-extension** of the HCG compactness construction (MSM135 Ch4): a
comparison-pullback metric defined only on a coordinate ball / open subtype is turned into a
total metric so that Arzelà–Ascoli applies on all of `M`.

## Route

* `symm` is the pointwise convex-combination symmetry.
* `pos` is a boundary split: where `χ x = 0` the form is `R.inner x` (positive-definite by
  `R.pos`); where `χ x > 0`, then `x ∈ support χ ⊆ tsupport χ ⊆ U`, so the `dite` selects
  `gU.inner ⟨x,hx⟩` (positive-definite by `gU.pos`), and the convex combination of two
  positive-definite forms with weights in `(0,1]` is positive-definite.
* `isVonNBounded` is free (`posDef_isVonNBounded`), handled inside `smoothMetric_of_localCoeff`.
* `contMDiff` is the only real content, via the local frame-component route of
  `smoothMetric_of_localCoeff`.  Each frame coefficient
  `x ↦ χ x • extForm(gU)(frameᵢ)(frameⱼ) + (1-χ x) • R.inner(frameᵢ)(frameⱼ)` is smooth on the
  trivialization base set.  The `R`-summand is smooth by `metric_inner_contMDiffAt`.  The
  `χ • gU`-summand is smooth by an **extend-by-0 across the support** argument: it vanishes off
  `tsupport χ ⊆ U`, and on the open set `(U : Set M)` it equals `χ x • gU.inner ⟨x,_⟩(…)(…)`
  whose smoothness is pulled back from the subtype `U` through `contMDiffAt_subtype_iff`
  (scalar transport — no bundle mismatch).

## Main results

* `SmoothRiemannianMetric.bumpExtendOpen` : the bundled total metric.
* `bumpExtendOpen_inner_of_mem` : its inner product on `U` is the convex combination of `gU`
  and `R`.
* `bumpExtendOpen_eq_gU_on` : on a set `V ⊆ U` where `χ = 1` it agrees with the partial metric
  `gU` (the locality lemma).
-/

noncomputable section

open Bundle Manifold Set ContinuousLinearMap Bornology TopologicalSpace
open scoped Manifold Topology ContDiff Classical

namespace DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

namespace Geometry

/-- The fiberwise extension-by-`0` of the partial inner product `gU` (defined on `U`) to a
bilinear form on `T_xM` for every `x : M`: it is `gU.inner ⟨x,hx⟩` when `x ∈ U` and `0`
otherwise.  Well-typed because `TangentSpace I (⟨x,hx⟩ : U)` is defeq `TangentSpace I x`. -/
def extZeroForm (U : Opens M)
    [SigmaCompactSpace U] [T2Space U]
    (gU : SmoothRiemannianMetric I U) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  if hx : x ∈ U then gU.inner ⟨x, hx⟩ else 0

@[simp] lemma extZeroForm_of_mem (U : Opens M)
    [SigmaCompactSpace U] [T2Space U]
    (gU : SmoothRiemannianMetric I U) {x : M} (hx : x ∈ U)
    (v w : TangentSpace I x) :
    extZeroForm (I := I) U gU x v w = gU.inner ⟨x, hx⟩ v w := by
  have h : extZeroForm (I := I) U gU x = gU.inner ⟨x, hx⟩ := dif_pos hx
  exact DFunLike.congr_fun (DFunLike.congr_fun h v) w

lemma extZeroForm_of_not_mem (U : Opens M)
    [SigmaCompactSpace U] [T2Space U]
    (gU : SmoothRiemannianMetric I U) {x : M} (hx : x ∉ U)
    (v w : TangentSpace I x) :
    extZeroForm (I := I) U gU x v w = 0 := by
  simp only [extZeroForm]
  rw [dif_neg hx]
  simp

/-- The fiberwise bump-extension form `χ x • (gU extended by 0) x + (1 - χ x) • R.inner x`. -/
def bumpForm (R : SmoothRiemannianMetric I M) (U : Opens M)
    [SigmaCompactSpace U] [T2Space U]
    (gU : SmoothRiemannianMetric I U) (χ : M → ℝ) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  χ x • extZeroForm (I := I) U gU x + (1 - χ x) • R.inner x

lemma bumpForm_apply (R : SmoothRiemannianMetric I M) (U : Opens M)
    [SigmaCompactSpace U] [T2Space U]
    (gU : SmoothRiemannianMetric I U) (χ : M → ℝ) (x : M) (v w : TangentSpace I x) :
    bumpForm (I := I) R U gU χ x v w =
      χ x • extZeroForm (I := I) U gU x v w + (1 - χ x) • R.inner x v w := by
  simp [bumpForm, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]

/-- The bump-extension form is symmetric, from symmetry of `gU` and `R`. -/
lemma bumpForm_symm (R : SmoothRiemannianMetric I M) (U : Opens M)
    [SigmaCompactSpace U] [T2Space U]
    (gU : SmoothRiemannianMetric I U) (χ : M → ℝ) (x : M) (v w : TangentSpace I x) :
    bumpForm (I := I) R U gU χ x v w = bumpForm (I := I) R U gU χ x w v := by
  rw [bumpForm_apply, bumpForm_apply, R.symm x v w]
  by_cases hx : x ∈ U
  · rw [extZeroForm_of_mem (I := I) U gU hx v w, extZeroForm_of_mem (I := I) U gU hx w v,
      gU.symm ⟨x, hx⟩ v w]
  · rw [extZeroForm_of_not_mem (I := I) U gU hx v w, extZeroForm_of_not_mem (I := I) U gU hx w v]

/-- The bump-extension form is positive-definite, by a boundary split on `χ x`. -/
lemma bumpForm_pos (R : SmoothRiemannianMetric I M) (U : Opens M)
    [SigmaCompactSpace U] [T2Space U]
    (gU : SmoothRiemannianMetric I U) (χ : M → ℝ)
    (hχ01 : ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1)
    (hχsupp : tsupport χ ⊆ (U : Set M))
    (x : M) (v : TangentSpace I x) (hv : v ≠ 0) :
    0 < bumpForm (I := I) R U gU χ x v v := by
  rw [bumpForm_apply]
  have hR := R.pos x v hv
  have ha : 0 ≤ χ x := (hχ01 x).1
  have hb : 0 ≤ 1 - χ x := by linarith [(hχ01 x).2]
  rcases lt_or_eq_of_le ha with ha' | ha'
  · -- `χ x > 0` ⟹ `x ∈ U` ⟹ the dite selects `gU`, positive-definite.
    have hxU : x ∈ U := by
      apply hχsupp
      exact subset_tsupport χ (Function.mem_support.mpr (ne_of_gt ha'))
    rw [extZeroForm_of_mem (I := I) U gU hxU v v]
    have hgU := gU.pos ⟨x, hxU⟩ v hv
    have h1 : 0 < χ x • gU.inner ⟨x, hxU⟩ v v := by
      rw [smul_eq_mul]; exact mul_pos ha' hgU
    have h2 : 0 ≤ (1 - χ x) • R.inner x v v := by
      rw [smul_eq_mul]; exact mul_nonneg hb hR.le
    linarith
  · -- `χ x = 0` ⟹ the form is `R.inner x`, positive-definite.
    rw [← ha']
    simp only [zero_smul, zero_add, sub_zero, one_smul]
    exact hR

/-- The chart-local frame section `y ↦ frameVec x₀ i y` is smooth at any point of the
trivialization base set (local restatement of `ConvexCombination.frameVec_contMDiffAt`, which is
`private` there; reproved here so this file need not import that module). -/
lemma frameVec_cmdiffAt' (x₀ : M) (i : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => TotalSpace.mk' E y (frameVec (I := I) x₀ i y)) x := by
  set e := trivializationAt E (TangentSpace I) x₀ with he
  set b := Module.finBasis ℝ E with hb
  have hfr : frameVec (I := I) x₀ i =ᶠ[𝓝 x] e.localFrame b i := by
    filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
    rw [e.localFrame_apply_of_mem_baseSet b hy]
    change (e.symmL ℝ y) (b i) = e.basisAt b hy i
    rw [Bundle.Trivialization.basisAt, Module.Basis.map_apply,
      Bundle.Trivialization.symmL_apply, Bundle.Trivialization.linearEquivAt_symm_apply]
  refine (contMDiffAt_localFrame_of_mem (I := I) (n := (∞ : WithTop ℕ∞)) (e := e) (b := b)
    (i := i) hx).congr_of_eventuallyEq ?_
  exact hfr.mono (fun y hy => congrArg (TotalSpace.mk' E y) hy)

/-- The `U`-tangent frame section `z ↦ frameVec x₀ i ↑z` is a smooth section of the open-subtype
tangent bundle at `⟨x,_⟩`, whenever `x` lies in the trivialization base set.  Obtained as the
`mpullback` of the smooth `M`-frame by `Subtype.val` (whose `mfderiv` is the identity, hence
invertible). -/
lemma frameVec_sub_cmdiffAt (U : Opens M)
    [SigmaCompactSpace U] [T2Space U]
    (x₀ : M) (i : Fin (Module.finrank ℝ E)) {x : M}
    (hxb : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) (hxU : x ∈ U) :
    letI : TopologicalSpace U := inferInstance
    letI : ChartedSpace H U := TopologicalSpace.Opens.instChartedSpace (H := H) (M := M) (s := U)
    letI : IsManifold I ∞ U := { U.instHasGroupoid (contDiffGroupoid ∞ I) with }
    ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
      (fun z : U => TotalSpace.mk' E (E := fun z : U => TangentSpace I z) z
        (frameVec (I := I) x₀ i (z : M))) ⟨x, hxU⟩ := by
  letI : TopologicalSpace U := inferInstance
  letI : ChartedSpace H U := TopologicalSpace.Opens.instChartedSpace (H := H) (M := M) (s := U)
  letI : IsManifold I ∞ U := { U.instHasGroupoid (contDiffGroupoid ∞ I) with }
  have hf' : (mfderiv I I (Subtype.val : U → M) ⟨x, hxU⟩).IsInvertible := by
    rw [mfderiv_subtype_val (I := I) U ⟨x, hxU⟩]
    change (ContinuousLinearMap.id ℝ E).IsInvertible
    exact ContinuousLinearMap.isInvertible_equiv (f := ContinuousLinearEquiv.refl ℝ E)
  have hpull :
      ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
        (T% (VectorField.mpullback I I (Subtype.val : U → M) (frameVec (I := I) x₀ i)))
        (⟨x, hxU⟩ : U) :=
    ContMDiffAt.mpullback_vectorField_preimage
      (I := I) (I' := I) (f := (Subtype.val : U → M)) (V := frameVec (I := I) x₀ i)
      (x₀ := ⟨x, hxU⟩) (m := ∞) (n := ∞)
      (frameVec_cmdiffAt' (I := I) x₀ i hxb)
      (contMDiff_subtype_val (I := I) (U := U)).contMDiffAt
      hf' (by simp)
  refine hpull.congr_of_eventuallyEq ?_
  filter_upwards with z
  show TotalSpace.mk' E (E := fun z : U => TangentSpace I z) z _
    = TotalSpace.mk' E (E := fun z : U => TangentSpace I z) z _
  congr 1
  have hfz : (mfderiv I I (Subtype.val : U → M) z).IsInvertible := by
    rw [mfderiv_subtype_val (I := I) U z]
    change (ContinuousLinearMap.id ℝ E).IsInvertible
    exact ContinuousLinearMap.isInvertible_equiv (f := ContinuousLinearEquiv.refl ℝ E)
  rw [VectorField.mpullback_apply]
  refine ((ContinuousLinearMap.IsInvertible.inverse_apply_eq hfz).mpr ?_).symm
  rw [mfderiv_subtype_val (I := I) U z]
  rfl

/-- `ContMDiffAt` of the `χ • extZeroForm` frame coefficient at any `x ∈ baseSet ∩ U`: on `U` the
`dite` selects `gU.inner`, and the coefficient is the subtype pullback (via
`contMDiffAt_subtype_iff`) of `χ` times a smooth `gU` frame coefficient. -/
lemma chiGU_coeff_cmdiffAt (U : Opens M)
    [SigmaCompactSpace U] [T2Space U]
    (gU : SmoothRiemannianMetric I U) (χ : M → ℝ)
    (hχ : ContMDiff I 𝓘(ℝ, ℝ) ∞ χ) (x₀ : M) (i j : Fin (Module.finrank ℝ E))
    {x : M} (hxb : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) (hxU : x ∈ U) :
    ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun y : M => χ y • extZeroForm (I := I) U gU y
        (frameVec (I := I) x₀ i y) (frameVec (I := I) x₀ j y)) x := by
  letI : TopologicalSpace U := inferInstance
  letI : ChartedSpace H U := TopologicalSpace.Opens.instChartedSpace (H := H) (M := M) (s := U)
  letI : IsManifold I ∞ U := { U.instHasGroupoid (contDiffGroupoid ∞ I) with }
  rw [← contMDiffAt_subtype_iff (I := I) (I' := 𝓘(ℝ, ℝ)) (U := U) (n := ∞) (x := ⟨x, hxU⟩)]
  have heq : (fun z : U => χ (z : M) • extZeroForm (I := I) U gU (z : M)
        (frameVec (I := I) x₀ i (z : M)) (frameVec (I := I) x₀ j (z : M)))
      = (fun z : U => χ (z : M) • gU.inner z
        (frameVec (I := I) x₀ i (z : M)) (frameVec (I := I) x₀ j (z : M))) := by
    funext z
    rw [extZeroForm_of_mem (I := I) U gU z.2]
  rw [heq]
  have hχsub : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun z : U => χ (z : M)) ⟨x, hxU⟩ :=
    (hχ.comp (contMDiff_subtype_val (I := I) (U := U))).contMDiffAt
  have hgUinner : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun z : U => gU.inner z
        (frameVec (I := I) x₀ i (z : M)) (frameVec (I := I) x₀ j (z : M))) ⟨x, hxU⟩ :=
    DifferentialGeometry.Integral.Connection.CovariantDerivative.metric_inner_contMDiffAt
      (I := I) (M := U) gU
      (frameVec_sub_cmdiffAt (I := I) U x₀ i hxb hxU)
      (frameVec_sub_cmdiffAt (I := I) U x₀ j hxb hxU) le_rfl
  exact hχsub.smul hgUinner

/-- The `χ • extZeroForm` summand of the bump coefficient is `ContMDiffOn` on the trivialization
base set: at points of `U` by `chiGU_coeff_cmdiffAt`, off `tsupport χ ⊆ U` it vanishes. -/
lemma chiGU_coeff_cmdiffOn (U : Opens M)
    [SigmaCompactSpace U] [T2Space U]
    (gU : SmoothRiemannianMetric I U) (χ : M → ℝ)
    (hχ : ContMDiff I 𝓘(ℝ, ℝ) ∞ χ) (hχsupp : tsupport χ ⊆ (U : Set M))
    (x₀ : M) (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun y : M => χ y • extZeroForm (I := I) U gU y
        (frameVec (I := I) x₀ i y) (frameVec (I := I) x₀ j y))
      (trivializationAt E (TangentSpace I) x₀).baseSet := by
  intro x hxb
  by_cases hxU : x ∈ U
  · exact (chiGU_coeff_cmdiffAt (I := I) U gU χ hχ x₀ i j hxb hxU).contMDiffWithinAt
  · have hx_not_supp : x ∉ tsupport χ := fun h => hxU (hχsupp h)
    have hχ0 : (fun y : M => χ y • extZeroForm (I := I) U gU y
        (frameVec (I := I) x₀ i y) (frameVec (I := I) x₀ j y)) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
      have hopen : (tsupport χ)ᶜ ∈ 𝓝 x := (isClosed_tsupport χ).isOpen_compl.mem_nhds hx_not_supp
      filter_upwards [hopen] with y hy
      have : χ y = 0 := image_eq_zero_of_notMem_tsupport hy
      rw [this, zero_smul]
    refine ContMDiffWithinAt.congr_of_eventuallyEq ?_ (hχ0.filter_mono nhdsWithin_le_nhds)
      (by rw [hχ0.eq_of_nhds])
    exact contMDiffWithinAt_const

/-- The chart-frame coefficient of the bump-extension form is smooth on the trivialization base
set at `x₀`.  The `R`-summand is `metric_inner_contMDiffAt`; the `χ • gU`-summand vanishes off
`tsupport χ ⊆ U` and on `(U : Set M)` is the subtype pullback of a smooth `gU` coefficient. -/
lemma bumpForm_coeff_contMDiffOn (R : SmoothRiemannianMetric I M) (U : Opens M)
    [SigmaCompactSpace U] [T2Space U]
    (gU : SmoothRiemannianMetric I U) (χ : M → ℝ)
    (hχ : ContMDiff I 𝓘(ℝ, ℝ) ∞ χ) (hχsupp : tsupport χ ⊆ (U : Set M))
    (x₀ : M) (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun x => bumpForm (I := I) R U gU χ x
        (frameVec (I := I) x₀ i x) (frameVec (I := I) x₀ j x))
      (trivializationAt E (TangentSpace I) x₀).baseSet := by
  -- The whole coefficient is `(χ • gU-coeff) + (1-χ) • R-coeff`.
  have hrw : (fun x => bumpForm (I := I) R U gU χ x
        (frameVec (I := I) x₀ i x) (frameVec (I := I) x₀ j x))
      = (fun x => (χ x • extZeroForm (I := I) U gU x
            (frameVec (I := I) x₀ i x) (frameVec (I := I) x₀ j x))
          + (1 - χ x) * R.inner x (frameVec (I := I) x₀ i x) (frameVec (I := I) x₀ j x)) := by
    funext x
    rw [bumpForm_apply]
    simp [smul_eq_mul]
  rw [hrw]
  -- The `χ • gU` summand: smooth on the base set by extend-by-0 across `tsupport χ ⊆ U`.
  have hχgU := chiGU_coeff_cmdiffOn (I := I) U gU χ hχ hχsupp x₀ i j
  -- The `(1-χ) • R` summand: smooth via `metric_inner_contMDiffAt`.
  have hR : ContMDiffOn I 𝓘(ℝ) ∞
      (fun x => (1 - χ x) * R.inner x
        (frameVec (I := I) x₀ i x) (frameVec (I := I) x₀ j x))
      (trivializationAt E (TangentSpace I) x₀).baseSet := by
    intro x hx
    have hfri := frameVec_cmdiffAt' (I := I) x₀ i hx
    have hfrj := frameVec_cmdiffAt' (I := I) x₀ j hx
    have hg : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
        (fun y : M => R.inner y (frameVec (I := I) x₀ i y) (frameVec (I := I) x₀ j y)) x :=
      DifferentialGeometry.Integral.Connection.CovariantDerivative.metric_inner_contMDiffAt
        (I := I) R hfri hfrj le_rfl
    have hχ1x : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun y : M => 1 - χ y) x :=
      contMDiffAt_const.sub (hχ x)
    exact ((hχ1x.mul hg)).contMDiffWithinAt
  exact hχgU.add hR

end Geometry

open Geometry

/-- **Bump extension of a partial Riemannian metric to a total smooth metric.**  Given a smooth
metric `gU` on an open subtype `U`, a global fallback `R`, and a smooth bump `χ` valued in
`[0,1]` with `tsupport χ ⊆ U`, the fiberwise convex combination
`χ x • (gU extended by 0) x + (1 - χ x) • R.inner x` is a smooth Riemannian metric on `M`. -/
noncomputable def SmoothRiemannianMetric.bumpExtendOpen
    (R : SmoothRiemannianMetric I M) (U : Opens M)
    [SigmaCompactSpace U] [T2Space U]
    (gU : SmoothRiemannianMetric I U) (χ : M → ℝ)
    (hχ : ContMDiff I 𝓘(ℝ, ℝ) ∞ χ) (hχ01 : ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1)
    (hχsupp : tsupport χ ⊆ (U : Set M)) :
    SmoothRiemannianMetric I M :=
  (smoothMetric_of_localCoeff (I := I) (bumpForm (I := I) R U gU χ)
    (fun x v w => bumpForm_symm (I := I) R U gU χ x v w)
    (fun x v hv => bumpForm_pos (I := I) R U gU χ hχ01 hχsupp x v hv)
    (fun x₀ i j => bumpForm_coeff_contMDiffOn (I := I) R U gU χ hχ hχsupp x₀ i j)).choose

/-- The inner product of the bump extension on `U` is the convex combination of `gU` and `R`. -/
theorem bumpExtendOpen_inner_of_mem
    (R : SmoothRiemannianMetric I M) (U : Opens M)
    [SigmaCompactSpace U] [T2Space U]
    (gU : SmoothRiemannianMetric I U) (χ : M → ℝ)
    (hχ : ContMDiff I 𝓘(ℝ, ℝ) ∞ χ) (hχ01 : ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1)
    (hχsupp : tsupport χ ⊆ (U : Set M))
    (x : M) (hx : x ∈ U) (v w : TangentSpace I x) :
    (R.bumpExtendOpen U gU χ hχ hχ01 hχsupp).inner x v w =
      χ x • gU.inner ⟨x, hx⟩ v w + (1 - χ x) • R.inner x v w := by
  rw [show (R.bumpExtendOpen U gU χ hχ hχ01 hχsupp).inner x v w
        = bumpForm (I := I) R U gU χ x v w from
      (smoothMetric_of_localCoeff (I := I) (bumpForm (I := I) R U gU χ)
        (fun x v w => bumpForm_symm (I := I) R U gU χ x v w)
        (fun x v hv => bumpForm_pos (I := I) R U gU χ hχ01 hχsupp x v hv)
        (fun x₀ i j => bumpForm_coeff_contMDiffOn
          (I := I) R U gU χ hχ hχsupp x₀ i j)).choose_spec x v w]
  rw [bumpForm_apply, extZeroForm_of_mem (I := I) U gU hx v w]

/-- The inner product of the bump extension at ANY point is the fiberwise convex combination
`χ x • (gU extended by 0) x + (1 - χ x) • R.inner x`.  (On `U` this is
`bumpExtendOpen_inner_of_mem`; this variant keeps the `extZeroForm` so it also applies off `U`,
where `extZeroForm = 0`.) -/
theorem bumpExtendOpen_inner
    (R : SmoothRiemannianMetric I M) (U : Opens M)
    [SigmaCompactSpace U] [T2Space U]
    (gU : SmoothRiemannianMetric I U) (χ : M → ℝ)
    (hχ : ContMDiff I 𝓘(ℝ, ℝ) ∞ χ) (hχ01 : ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1)
    (hχsupp : tsupport χ ⊆ (U : Set M))
    (x : M) (v w : TangentSpace I x) :
    (R.bumpExtendOpen U gU χ hχ hχ01 hχsupp).inner x v w =
      χ x • Geometry.extZeroForm (I := I) U gU x v w + (1 - χ x) • R.inner x v w := by
  rw [show (R.bumpExtendOpen U gU χ hχ hχ01 hχsupp).inner x v w
        = Geometry.bumpForm (I := I) R U gU χ x v w from
      (smoothMetric_of_localCoeff (I := I) (Geometry.bumpForm (I := I) R U gU χ)
        (fun x v w => Geometry.bumpForm_symm (I := I) R U gU χ x v w)
        (fun x v hv => Geometry.bumpForm_pos (I := I) R U gU χ hχ01 hχsupp x v hv)
        (fun x₀ i j => Geometry.bumpForm_coeff_contMDiffOn
          (I := I) R U gU χ hχ hχsupp x₀ i j)).choose_spec x v w]
  rw [Geometry.bumpForm_apply]

/-- Off the topological support of `χ`, the bump extension coincides with the fallback metric
`R`. -/
theorem bumpExtendOpen_inner_of_notMem_tsupport
    (R : SmoothRiemannianMetric I M) (U : Opens M)
    [SigmaCompactSpace U] [T2Space U]
    (gU : SmoothRiemannianMetric I U) (χ : M → ℝ)
    (hχ : ContMDiff I 𝓘(ℝ, ℝ) ∞ χ) (hχ01 : ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1)
    (hχsupp : tsupport χ ⊆ (U : Set M))
    (x : M) (hx : x ∉ tsupport χ) (v w : TangentSpace I x) :
    (R.bumpExtendOpen U gU χ hχ hχ01 hχsupp).inner x v w = R.inner x v w := by
  have hχ0 : χ x = 0 := image_eq_zero_of_notMem_tsupport hx
  rw [bumpExtendOpen_inner (I := I) R U gU χ hχ hχ01 hχsupp x v w, hχ0]
  simp

/-- **Locality.**  On a set `V ⊆ U` where `χ = 1`, the bump extension agrees with the partial
metric `gU`. -/
theorem bumpExtendOpen_eq_gU_on
    (R : SmoothRiemannianMetric I M) (U : Opens M)
    [SigmaCompactSpace U] [T2Space U]
    (gU : SmoothRiemannianMetric I U) (χ : M → ℝ)
    (hχ : ContMDiff I 𝓘(ℝ, ℝ) ∞ χ) (hχ01 : ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1)
    (hχsupp : tsupport χ ⊆ (U : Set M))
    (V : Set M) (hV : ∀ x ∈ V, χ x = 1) (hVU : V ⊆ (U : Set M))
    (x : M) (hx : x ∈ V) (v w : TangentSpace I x) :
    (R.bumpExtendOpen U gU χ hχ hχ01 hχsupp).inner x v w = gU.inner ⟨x, hVU hx⟩ v w := by
  rw [bumpExtendOpen_inner_of_mem (I := I) R U gU χ hχ hχ01 hχsupp x (hVU hx), hV x hx]
  simp

end DifferentialGeometry
