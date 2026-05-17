import DifferentialGeometry.Geometry.Riemannian.Geodesic.VelocityChart

set_option linter.unusedSectionVars false
set_option linter.style.show false

/-!
# Chart transition formula on the tangent bundle of the tangent bundle

This file ships the explicit chart-α-vs-chart-β chart-transition formula on
`T(TM)` at points with coincident projection on `M`. Given two basepoints
`α, β : M` and a point `p : TangentBundle I M` lying in both chart sources,
the composite

```
(trivAt-on-T(TM) α).continuousLinearMapAt p ∘ (trivAt-on-T(TM) β).symmL p
```

is computed in terms of the base chart-transition `φ_αβ = extChartAt I α ∘
(extChartAt I β).symm` and its first and second derivatives:

```
(Q.1, Q.2) ↦ (fderiv φ_αβ y_β Q.1,
              fderiv φ_αβ y_β Q.2
                + fderiv (y ↦ fderiv φ_αβ y Q.1) y_β v_β)
```

where `y_β = extChartAt I β p.proj` and `v_β = chartFiberCoord β p`.

The proof proceeds in five steps:

1. Convert the composite of trivialisation maps on `T(TM)` to a coordinate
   change in `tangentBundleCore I.tangent (TangentBundle I M)` via
   `continuousLinearMapAt_trivializationAt_eq_core` and
   `symmL_trivializationAt_eq_core`, composed using `coordChange_comp`.
2. Express the resulting coordinate change as `fderivWithin 𝕜` of the
   tangent-bundle chart change at `extChartAt I.tangent ⟨β, 0⟩ p` via
   `tangentBundleCore_coordChange_achart`.
3. Drop `fderivWithin (range I.tangent)` to `fderiv` using
   `[I.Boundaryless]`.
4. Identify the tangent-bundle chart change with the explicit map
   `(y, w) ↦ (φ_αβ y, fderiv φ_αβ y w)` on a neighbourhood of
   `(y_β, v_β)`.
5. Compute the `fderiv` of this explicit map via the chain rule and
   `HasFDerivAt.clm_apply`, using Schwarz symmetry of the second
   derivative to match the headline formula.
-/

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## Auxiliary facts about the tangent-bundle extended chart -/

/-- Apply `extChartAt I.tangent ⟨α, 0⟩` to a point `q : TangentBundle I M` in
componentwise form. -/
lemma extChartAt_tangent_zeroSection_apply (α : M) (q : TangentBundle I M) :
    extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M) q =
      (extChartAt I α q.proj, chartFiberCoord (I := I) α q) := by
  classical
  -- Combine the first-coordinate and second-coordinate identities shipped
  -- in the velocity-chart file.
  ext
  · exact fst_extChartAt_tangent_zeroSection_apply (I := I) α q
  · exact snd_extChartAt_tangent_zeroSection_apply (I := I) α q

/-! ## The chart-transition function on `T(TM)`

We write `φ_αβ := extChartAt I α ∘ (extChartAt I β).symm : E → E` for the
chart transition on the base, and study the chart transition on `T(TM)`
at `(y_β, v_β) := extChartAt I.tangent ⟨β, 0⟩ p`. -/

/-- The chart transition `extChartAt I.tangent ⟨α, 0⟩ ∘
(extChartAt I.tangent ⟨β, 0⟩).symm : E × E → E × E`, evaluated pointwise on
the set where the base point lies in both chart sources, has the closed
form
```
(y, w) ↦ (extChartAt I α ((extChartAt I β).symm y),
          fderivWithin ℝ (extChartAt I α ∘ (extChartAt I β).symm) (range I) y w).
```
-/
lemma extChartAt_tangent_chart_change_apply
    (α β : M) {y : E} {w : E}
    (hy_target : y ∈ (extChartAt I β).target)
    (hy_source : (extChartAt I β).symm y ∈ (chartAt H α).source) :
    extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)
        ((extChartAt I.tangent (⟨β, (0 : E)⟩ : TangentBundle I M)).symm (y, w)) =
      (extChartAt I α ((extChartAt I β).symm y),
        fderivWithin ℝ (extChartAt I α ∘ (extChartAt I β).symm) (range I) y w) := by
  classical
  -- Let `b := (extChartAt I β).symm y ∈ M`.
  set b : M := (extChartAt I β).symm y with hb_def
  have hb_source_β : b ∈ (chartAt H β).source := by
    have : b ∈ (extChartAt I β).source := (extChartAt I β).map_target hy_target
    rwa [extChartAt_source] at this
  -- (1) Compute `(extChartAt I.tangent ⟨β, 0⟩).symm (y, w)`.
  -- By `FiberBundle.extChartAt`:
  --   `extChartAt I.tangent ⟨β, 0⟩ = (triv-β).toPartialEquiv ≫
  --                                  (extChartAt I β).prod (refl E)`.
  -- Its symm at `(y, w)` is
  --   `(triv-β).toPartialEquiv.symm ((extChartAt I β).symm y, w)`
  -- = `(triv-β).symm ((extChartAt I β).symm y) w`.
  -- We package this via the helper below, then apply `extChartAt I.tangent ⟨α, 0⟩`.
  have hsymm_value :
      (extChartAt I.tangent (⟨β, (0 : E)⟩ : TangentBundle I M)).symm (y, w) =
        (⟨b, (trivializationAt E (TangentSpace I) β).symm b w⟩ :
          TangentBundle I M) := by
    -- Use `FiberBundle.extChartAt` to unfold the extended chart on the tangent bundle.
    -- `extChartAt I.tangent ⟨β, 0⟩ = (triv-β).toPartialEquiv ≫
    --                                (extChartAt I β).prod (refl E)`.
    have hfb := FiberBundle.extChartAt (IB := I) (F := E) (E := TangentSpace I)
      (x := (⟨β, (0 : E)⟩ : TangentBundle I M))
    -- `hfb` says: `extChartAt I.tangent ⟨β, 0⟩ = (triv-β).toPartialEquiv ≫ (extChartAt I β).prod (refl E)`
    -- (using `⟨β, 0⟩.proj = β`).
    have heq : (extChartAt I.tangent (⟨β, (0 : E)⟩ : TangentBundle I M)).symm =
        ((trivializationAt E (TangentSpace I) β).toPartialEquiv ≫
          (extChartAt I β).prod (PartialEquiv.refl E)).symm := by
      rw [hfb]
    have hsymm_at_yw :
        (extChartAt I.tangent (⟨β, (0 : E)⟩ : TangentBundle I M)).symm (y, w) =
          ((trivializationAt E (TangentSpace I) β).toPartialEquiv ≫
            (extChartAt I β).prod (PartialEquiv.refl E)).symm (y, w) := by
      rw [heq]
    rw [hsymm_at_yw]
    -- Reduce the RHS via `coe_trans_symm`: `(P ≫ Q).symm = P.symm ∘ Q.symm`.
    -- So `(P ≫ Q).symm (y, w) = P.symm (Q.symm (y, w))`.
    -- Q := (extChartAt I β).prod (refl E). `Q.symm (y, w) = ((extChartAt I β).symm y, w) = (b, w)`.
    -- P := (triv-β).toPartialEquiv. `P.symm (b, w) = (triv-β).toPartialEquiv.symm (b, w)`.
    -- Use `mk_symm`: `⟨b, (triv-β).symm b w⟩ = (triv-β).toPartialEquiv.symm (b, w)` when `b ∈ baseSet`.
    have hb_baseβ : b ∈ (trivializationAt E (TangentSpace I) β).baseSet := by
      rw [TangentBundle.trivializationAt_baseSet]; exact hb_source_β
    have hmk := Pretrivialization.mk_symm
      (e := (trivializationAt E (TangentSpace I) β).toPretrivialization) hb_baseβ w
    -- `hmk : ⟨b, (triv-β).symm b w⟩ = (triv-β).toPartialEquiv.symm (b, w)`.
    -- Goal after rfl-unfolding both sides: equivalent to `hmk.symm`.
    show ((trivializationAt E (TangentSpace I) β).toPartialEquiv ≫
            (extChartAt I β).prod (PartialEquiv.refl E)).symm (y, w) =
        (⟨b, (trivializationAt E (TangentSpace I) β).symm b w⟩ :
            TangentBundle I M)
    -- The LHS reduces to `(triv-β).toPartialEquiv.symm (b, w)` (with `b = (extChartAt I β).symm y`).
    -- We claim the LHS equals `(triv-β).toPartialEquiv.symm ((extChartAt I β).symm y, w)`.
    have hLHS_eq :
        ((trivializationAt E (TangentSpace I) β).toPartialEquiv ≫
            (extChartAt I β).prod (PartialEquiv.refl E)).symm (y, w) =
          (trivializationAt E (TangentSpace I) β).toPartialEquiv.symm
            ((extChartAt I β).symm y, w) := rfl
    rw [hLHS_eq]
    -- Now `(triv-β).toPartialEquiv.symm ((extChartAt I β).symm y, w) = ⟨b, ...⟩` by `mk_symm.symm`.
    -- `hmk : ⟨b, (triv-β).symm b w⟩ = (triv-β).toPartialEquiv.symm (b, w)`.
    -- `b = (extChartAt I β).symm y`, so by `hb_def` substitution:
    exact hmk.symm
  -- (2) Apply `extChartAt I.tangent ⟨α, 0⟩` to the symm value.
  rw [hsymm_value]
  -- The resulting point in `TM` has base `b` and fibre `(triv-β).symm b w`.
  -- By the componentwise identity:
  have happ := extChartAt_tangent_zeroSection_apply (I := I) (α := α)
    (q := (⟨b, (trivializationAt E (TangentSpace I) β).symm b w⟩ :
      TangentBundle I M))
  rw [happ]
  -- The first component is `extChartAt I α b = extChartAt I α ((extChartAt I β).symm y)`.
  -- We need to identify the second component
  --   `chartFiberCoord α ⟨b, (triv-β).symm b w⟩`
  -- with `fderivWithin ℝ (extChartAt I α ∘ (extChartAt I β).symm) (range I) y w`.
  congr 1
  -- Unfold `chartFiberCoord α q = (triv-α q).2`.
  show ((trivializationAt E (TangentSpace I) α)
        (⟨b, (trivializationAt E (TangentSpace I) β).symm b w⟩ :
          TangentBundle I M)).2 = _
  -- Goal: `((triv-α) ⟨b, (triv-β).symm b w⟩).2 = fderivWithin ... y w`.
  -- Compute `(triv-α) ⟨b, (triv-β).symm b w⟩`:
  --   `(triv-α ⟨b, v⟩).2 = (triv-α).continuousLinearMapAt ℝ b v` when `b ∈ triv-α.baseSet`.
  -- And `triv-α.baseSet = (chartAt H α).source ∋ b`.
  -- Then `(triv-α).continuousLinearMapAt ℝ b ((triv-β).symm b w)`
  -- expands via `continuousLinearMapAt_trivializationAt_eq_core` and
  -- `symmL_trivializationAt_eq_core`, composed via `coordChange_comp`,
  -- to `coordChange (achart H β) (achart H α) b w =
  --     tangentCoordChange I β α b w =
  --     fderivWithin ℝ (extChartAt I α ∘ (extChartAt I β).symm) (range I) (extChartAt I β b) w
  --   = fderivWithin ℝ ... (range I) y w`.
  -- Step (a): convert `(triv-α ⟨b, _⟩).2` to `(triv-α).continuousLinearMapAt`.
  have hb_baseα : b ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact hy_source
  have hb_baseβ : b ∈ (trivializationAt E (TangentSpace I) β).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact hb_source_β
  -- `(triv-α ⟨b, v⟩).2 = (triv-α).continuousLinearMapAt ℝ b v` (because b ∈ baseSet).
  -- This uses `Trivialization.coe_linearMapAt_of_mem` for vector bundles.
  set v : TangentSpace I b := (trivializationAt E (TangentSpace I) β).symm b w
  -- `linearMapAt` on the base set gives the second component of the trivialization.
  have hαApply :
      (((trivializationAt E (TangentSpace I) α)
          (⟨b, v⟩ : TangentBundle I M)).2 : E) =
        (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b v := by
    -- By `coe_linearMapAt_of_mem`: `(triv).linearMapAt ℝ b y = (triv ⟨b, y⟩).2` when `b ∈ baseSet`.
    have hcoe := (trivializationAt E (TangentSpace I) α).coe_linearMapAt_of_mem
      (R := ℝ) hb_baseα
    -- `continuousLinearMapAt = linearMapAt` underlying coercion.
    have hcLM_eq_lm :
        ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b) v =
          ((trivializationAt E (TangentSpace I) α).linearMapAt ℝ b) v := rfl
    rw [hcLM_eq_lm, hcoe]
  rw [hαApply]
  -- Step (b): convert `(triv-α).continuousLinearMapAt ℝ b` to a coord-change in
  -- the tangent bundle core, via `continuousLinearMapAt_trivializationAt_eq_core`.
  have hα_eq_core :
      (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b =
        (tangentBundleCore I M).coordChange (achart H b) (achart H α) b :=
    TangentBundle.continuousLinearMapAt_trivializationAt_eq_core (I := I) (M := M)
      (b₀ := α) (b := b) hy_source
  -- Step (c): `v = (triv-β).symmL ℝ b w` (defequal up to `symm` vs `symmL` on the fibre).
  have hv_eq : v = (trivializationAt E (TangentSpace I) β).symmL ℝ b w := rfl
  -- Step (d): convert `(triv-β).symmL ℝ b` to a coord-change, via
  -- `symmL_trivializationAt_eq_core`.
  have hβ_symmL_eq_core :
      (trivializationAt E (TangentSpace I) β).symmL ℝ b =
        (tangentBundleCore I M).coordChange (achart H β) (achart H b) b :=
    TangentBundle.symmL_trivializationAt_eq_core (I := I) (M := M)
      (b₀ := β) (b := b) hb_source_β
  -- Put steps (b), (c), (d) together: apply the CLM and use `coordChange_comp`.
  rw [hα_eq_core, hv_eq, hβ_symmL_eq_core]
  -- Now goal is:
  --   coordChange (achart H b) (achart H α) b
  --     (coordChange (achart H β) (achart H b) b w) =
  --   fderivWithin ℝ (extChartAt I α ∘ (extChartAt I β).symm) (range I) y w.
  -- Apply `coordChange_comp` on the LHS:
  have hp_baseSet :
      b ∈ (tangentBundleCore I M).baseSet (achart H β) ∩
          (tangentBundleCore I M).baseSet (achart H b) ∩
          (tangentBundleCore I M).baseSet (achart H α) := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [tangentBundleCore_baseSet]; exact hb_source_β
    · rw [tangentBundleCore_baseSet]; exact mem_chart_source H b
    · rw [tangentBundleCore_baseSet]; exact hy_source
  have hcomp := (tangentBundleCore I M).coordChange_comp
    (i := achart H β) (j := achart H b) (k := achart H α) b hp_baseSet w
  -- `hcomp : coord(b)(α) b (coord(β)(b) b w) = coord(β)(α) b w`.
  -- We need to rewrite the LHS of the goal to the RHS of `hcomp`.
  -- Use `rw [show ...]` with explicit form to avoid unification issues.
  -- Final identification: `b := (extChartAt I β).symm y`, so `extChartAt I β b = y`.
  have hbase_y : extChartAt I β b = y := by
    show extChartAt I β ((extChartAt I β).symm y) = y
    exact (extChartAt I β).right_inv hy_target
  -- Now chain everything via `calc`.
  calc ((tangentBundleCore I M).coordChange (achart H b) (achart H α) b)
        (((tangentBundleCore I M).coordChange (achart H β) (achart H b) b) w)
      = ((tangentBundleCore I M).coordChange (achart H β) (achart H α) b) w := hcomp
    _ = (fderivWithin ℝ (extChartAt I α ∘ (extChartAt I β).symm) (range I)
            (extChartAt I β b)) w := by
        rw [tangentBundleCore_coordChange_achart (I := I) (M := M) β α b]
    _ = (fderivWithin ℝ (extChartAt I α ∘ (extChartAt I β).symm) (range I) y) w := by
        rw [hbase_y]

/-! ## EventuallyEq form

We now show that the explicit pointwise formula holds in a neighbourhood
of `(y_β, v_β)`. With `[I.Boundaryless]`, the underlying open sets are
neighbourhoods. -/

variable [I.Boundaryless]

/-- The chart change `extChartAt I.tangent ⟨α, 0⟩ ∘
(extChartAt I.tangent ⟨β, 0⟩).symm` agrees in a neighbourhood of
`extChartAt I.tangent ⟨β, 0⟩ p` with the explicit map
```
(y, w) ↦ (φ_αβ y, fderiv ℝ φ_αβ y w).
```
We use `[I.Boundaryless]` to convert `fderivWithin (range I) = fderiv`.
-/
lemma eventuallyEq_extChartAt_tangent_chart_change
    (α β : M) {p : TangentBundle I M}
    (hα : p.proj ∈ (chartAt H α).source)
    (hβ : p.proj ∈ (chartAt H β).source) :
    (fun yw : E × E => extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)
        ((extChartAt I.tangent (⟨β, (0 : E)⟩ : TangentBundle I M)).symm yw)) =ᶠ[𝓝
      (extChartAt I.tangent (⟨β, (0 : E)⟩ : TangentBundle I M) p)]
      (fun yw : E × E =>
        (extChartAt I α ((extChartAt I β).symm yw.1),
          fderiv ℝ (extChartAt I α ∘ (extChartAt I β).symm) yw.1 yw.2)) := by
  classical
  -- The neighbourhood is `U ×ˢ univ` where `U ⊆ E` is the open set
  -- `U = {y ∈ (extChartAt I β).target | (extChartAt I β).symm y ∈ (chartAt H α).source}`.
  -- Both conditions are satisfied at `y_β = extChartAt I β p.proj`.
  -- Step (a): `(extChartAt I β).target` is open (boundaryless), contains `y_β`.
  have hβ_target_open : IsOpen (extChartAt I β).target := isOpen_extChartAt_target β
  have hyβ_mem_target : extChartAt I β p.proj ∈ (extChartAt I β).target := by
    have hps : p.proj ∈ (extChartAt I β).source := by
      rw [extChartAt_source]; exact hβ
    exact (extChartAt I β).map_source hps
  -- Step (b): `U₁ := (extChartAt I β).symm ⁻¹' (chartAt H α).source` is open in `E`
  -- (continuous preimage of open).
  -- Use continuity of `(extChartAt I β).symm` on `(extChartAt I β).target`, but we'll
  -- restrict to `target` for openness.
  -- Easier: pick the open set
  --   `O := (extChartAt I β).target ∩ (extChartAt I β).symm ⁻¹' (chartAt H α).source`
  -- and verify it is a neighbourhood of `y_β`. Then `O ×ˢ univ` is a neighbourhood
  -- of `(y_β, v_β)`.
  have hSymmCts : ContinuousOn (extChartAt I β).symm (extChartAt I β).target :=
    continuousOn_extChartAt_symm β
  -- `(chartAt H α).source` is open in `M`.
  have hαsrc_open : IsOpen (chartAt H α).source := (chartAt H α).open_source
  -- `O := (extChartAt I β).target ∩ (extChartAt I β).symm ⁻¹' (chartAt H α).source`.
  -- `O` is open in `E` because:
  --   - On the open set `(extChartAt I β).target`, the function `(extChartAt I β).symm` is
  --     continuous, hence the preimage of `(chartAt H α).source` is open in
  --     `(extChartAt I β).target`, hence open in `E` (since target is open).
  have hO_open : IsOpen ((extChartAt I β).target ∩
      (extChartAt I β).symm ⁻¹' (chartAt H α).source) :=
    hSymmCts.isOpen_inter_preimage hβ_target_open hαsrc_open
  have hyβ_mem_O : extChartAt I β p.proj ∈ (extChartAt I β).target ∩
      (extChartAt I β).symm ⁻¹' (chartAt H α).source := by
    refine ⟨hyβ_mem_target, ?_⟩
    -- `(extChartAt I β).symm (extChartAt I β p.proj) = p.proj ∈ (chartAt H α).source`.
    have hps : p.proj ∈ (extChartAt I β).source := by
      rw [extChartAt_source]; exact hβ
    have hinv : (extChartAt I β).symm (extChartAt I β p.proj) = p.proj :=
      (extChartAt I β).left_inv hps
    rw [mem_preimage, hinv]; exact hα
  -- The neighbourhood condition: `O ×ˢ univ ∈ 𝓝 (y_β, v_β)`.
  -- By `IsOpen.mem_nhds` then `prod_mem_nhds_iff`.
  -- We first need to know what `extChartAt I.tangent ⟨β, 0⟩ p` evaluates to.
  -- By `extChartAt_tangent_zeroSection_apply`:
  --   `extChartAt I.tangent ⟨β, 0⟩ p = (extChartAt I β p.proj, chartFiberCoord β p)`.
  have hpβ_eval :
      extChartAt I.tangent (⟨β, (0 : E)⟩ : TangentBundle I M) p =
        (extChartAt I β p.proj, chartFiberCoord (I := I) β p) :=
    extChartAt_tangent_zeroSection_apply (I := I) (α := β) (q := p)
  rw [hpβ_eval]
  -- We want eventually equality on `𝓝 (y_β, v_β)`. We use the open neighbourhood
  -- `O ×ˢ univ` where `O` is as above.
  refine Filter.eventuallyEq_of_mem (s := ((extChartAt I β).target ∩
      (extChartAt I β).symm ⁻¹' (chartAt H α).source) ×ˢ (Set.univ : Set E)) ?_ ?_
  · -- Membership in 𝓝 (extChartAt I β p.proj, chartFiberCoord β p).
    rw [mem_nhds_iff]
    refine ⟨_, le_refl _, hO_open.prod isOpen_univ, ?_⟩
    exact ⟨hyβ_mem_O, mem_univ _⟩
  · -- Pointwise equality on the set.
    intro yw hyw
    rcases hyw with ⟨⟨hy_t, hy_s⟩, _⟩
    -- Apply the closed-form identity, then convert `fderivWithin (range I)` to `fderiv`
    -- via `[I.Boundaryless]`.
    have hclosed := extChartAt_tangent_chart_change_apply (I := I) (α := α) (β := β)
      (y := yw.1) (w := yw.2) hy_t hy_s
    -- Convert `fderivWithin (range I) ... = fderiv ...` using `range I = univ` and
    -- `fderivWithin_univ`.
    have hrange : (range I : Set E) = Set.univ := ModelWithCorners.range_eq_univ I
    have hfderiv_eq :
        fderivWithin ℝ (extChartAt I α ∘ (extChartAt I β).symm) (range I) yw.1 =
          fderiv ℝ (extChartAt I α ∘ (extChartAt I β).symm) yw.1 := by
      rw [hrange, fderivWithin_univ]
    -- Beta-reduce both lambda expressions then chain rewrites.
    show extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)
        ((extChartAt I.tangent (⟨β, (0 : E)⟩ : TangentBundle I M)).symm yw) =
      (extChartAt I α ((extChartAt I β).symm yw.1),
        fderiv ℝ (extChartAt I α ∘ (extChartAt I β).symm) yw.1 yw.2)
    -- `yw = (yw.1, yw.2)` definitionally.
    have hyw_eq : yw = (yw.1, yw.2) := rfl
    rw [hyw_eq, hclosed, hfderiv_eq]

/-! ## fderiv of the explicit chart-transition function

We now compute the `fderiv` at `(y_β, v_β)` of the explicit chart-transition
map `(y, w) ↦ (φ_αβ y, fderiv φ_αβ y w)`. The first coordinate is just the
chain-rule application; the second uses `HasFDerivAt.clm_apply`. -/

/-- Smoothness of the base chart change `φ_αβ = extChartAt I α ∘
(extChartAt I β).symm`, on a neighbourhood of `y_β = extChartAt I β p.proj`.

When `p.proj ∈ (chartAt H α).source ∩ (chartAt H β).source`, `φ_αβ` is
`C^∞` on the open set
`((extChartAt I β).symm ≫ extChartAt I α).source`, which is a neighbourhood
of `y_β` (using `[I.Boundaryless]`). -/
lemma contDiffOn_chartChange (α β : M) :
    ContDiffOn ℝ ∞ (extChartAt I α ∘ (extChartAt I β).symm)
      ((extChartAt I β).symm ≫ extChartAt I α).source := by
  exact contDiffOn_ext_coord_change (I := I) (M := M) (n := ∞) α β

/-- The source of the chart-change PartialEquiv contains `y_β`. -/
lemma yβ_mem_chartChange_source (α β : M)
    {p : TangentBundle I M}
    (hα : p.proj ∈ (chartAt H α).source)
    (hβ : p.proj ∈ (chartAt H β).source) :
    extChartAt I β p.proj ∈ ((extChartAt I β).symm ≫ extChartAt I α).source := by
  -- The source is `(extChartAt I β).target ∩
  --   (extChartAt I β).symm ⁻¹' (extChartAt I α).source`.
  rw [PartialEquiv.trans_source]
  refine ⟨?_, ?_⟩
  · -- `extChartAt I β p.proj ∈ (extChartAt I β).target`.
    have hps : p.proj ∈ (extChartAt I β).source := by
      rw [extChartAt_source]; exact hβ
    have : extChartAt I β p.proj ∈ (extChartAt I β).target :=
      (extChartAt I β).map_source hps
    -- `(extChartAt I β).symm.source = (extChartAt I β).target`.
    rw [PartialEquiv.symm_source]
    exact this
  · -- `(extChartAt I β).symm (extChartAt I β p.proj) = p.proj ∈ (extChartAt I α).source`.
    have hps : p.proj ∈ (extChartAt I β).source := by
      rw [extChartAt_source]; exact hβ
    have hinv : (extChartAt I β).symm (extChartAt I β p.proj) = p.proj :=
      (extChartAt I β).left_inv hps
    rw [mem_preimage, hinv, extChartAt_source]; exact hα

/-- The source of the chart-change PartialEquiv is open in `E`, hence a
neighbourhood of `y_β`. -/
lemma chartChange_source_mem_nhds (α β : M)
    {p : TangentBundle I M}
    (hα : p.proj ∈ (chartAt H α).source)
    (hβ : p.proj ∈ (chartAt H β).source) :
    ((extChartAt I β).symm ≫ extChartAt I α).source ∈
      𝓝 (extChartAt I β p.proj) := by
  classical
  -- The source is `(extChartAt I β).target ∩
  --   (extChartAt I β).symm ⁻¹' (extChartAt I α).source`. We show openness directly.
  rw [PartialEquiv.trans_source]
  -- `(extChartAt I β).symm.source = (extChartAt I β).target` is open (boundaryless).
  have hβ_target_open : IsOpen (extChartAt I β).target := isOpen_extChartAt_target β
  have hαsrc_open : IsOpen (extChartAt I α).source := by
    rw [extChartAt_source]; exact (chartAt H α).open_source
  -- Continuity of `(extChartAt I β).symm` on its source.
  have hSymmCts : ContinuousOn (extChartAt I β).symm (extChartAt I β).target :=
    continuousOn_extChartAt_symm β
  -- The intersection is open.
  have hopen :
      IsOpen ((extChartAt I β).target ∩
        (extChartAt I β).symm ⁻¹' (extChartAt I α).source) :=
    hSymmCts.isOpen_inter_preimage hβ_target_open hαsrc_open
  -- `(extChartAt I β).symm.source = (extChartAt I β).target`.
  have hsource : (extChartAt I β).symm.source = (extChartAt I β).target := rfl
  rw [hsource]
  refine hopen.mem_nhds ?_
  -- Membership: `extChartAt I β p.proj ∈ V ∩ target`.
  have hmem := yβ_mem_chartChange_source (I := I) (α := α) (β := β) (p := p) hα hβ
  rw [PartialEquiv.trans_source, hsource] at hmem
  exact hmem

/-- The base chart change `φ_αβ` is differentiable at `y_β`. -/
lemma differentiableAt_chartChange (α β : M)
    {p : TangentBundle I M}
    (hα : p.proj ∈ (chartAt H α).source)
    (hβ : p.proj ∈ (chartAt H β).source) :
    DifferentiableAt ℝ (extChartAt I α ∘ (extChartAt I β).symm)
      (extChartAt I β p.proj) := by
  classical
  have hsmooth := contDiffOn_chartChange (I := I) α β
  have hmem := yβ_mem_chartChange_source (I := I) (α := α) (β := β) (p := p) hα hβ
  have hnhd := chartChange_source_mem_nhds (I := I) (α := α) (β := β) hα hβ
  -- Use `ContDiffWithinAt.differentiableWithinAt` then `DifferentiableWithinAt.differentiableAt`.
  have hcdwa : ContDiffWithinAt ℝ ∞ (extChartAt I α ∘ (extChartAt I β).symm)
      ((extChartAt I β).symm ≫ extChartAt I α).source
      (extChartAt I β p.proj) := hsmooth _ hmem
  have hdwa : DifferentiableWithinAt ℝ (extChartAt I α ∘ (extChartAt I β).symm)
      ((extChartAt I β).symm ≫ extChartAt I α).source
      (extChartAt I β p.proj) :=
    hcdwa.differentiableWithinAt (by simp)
  exact hdwa.differentiableAt hnhd

/-- The base chart change `φ_αβ` is `C^∞` (in particular `C²`) on a
neighbourhood of `y_β`. We package this as an existence statement of an
open set on which `φ_αβ` is `C^∞`. -/
lemma exists_open_contDiffOn_chartChange (α β : M)
    {p : TangentBundle I M}
    (hα : p.proj ∈ (chartAt H α).source)
    (hβ : p.proj ∈ (chartAt H β).source) :
    ∃ U : Set E, IsOpen U ∧ extChartAt I β p.proj ∈ U ∧
      ContDiffOn ℝ ∞ (extChartAt I α ∘ (extChartAt I β).symm) U := by
  classical
  refine ⟨((extChartAt I β).symm ≫ extChartAt I α).source, ?_, ?_,
    contDiffOn_chartChange (I := I) α β⟩
  · -- Open source.
    have hβ_target_open : IsOpen (extChartAt I β).target := isOpen_extChartAt_target β
    have hαsrc_open : IsOpen (extChartAt I α).source := by
      rw [extChartAt_source]; exact (chartAt H α).open_source
    have hSymmCts : ContinuousOn (extChartAt I β).symm (extChartAt I β).target :=
      continuousOn_extChartAt_symm β
    have hsource : (extChartAt I β).symm.source = (extChartAt I β).target := rfl
    rw [PartialEquiv.trans_source, hsource]
    exact hSymmCts.isOpen_inter_preimage hβ_target_open hαsrc_open
  · exact yβ_mem_chartChange_source (I := I) (α := α) (β := β) (p := p) hα hβ

/-- The second-derivative function `y ↦ fderiv ℝ φ_αβ y` is differentiable at
`y_β`. We have `φ_αβ` is `C^∞` on an open neighbourhood of `y_β`, so
`fderiv φ_αβ` is `C^∞` (in particular differentiable) there. -/
lemma differentiableAt_fderiv_chartChange (α β : M)
    {p : TangentBundle I M}
    (hα : p.proj ∈ (chartAt H α).source)
    (hβ : p.proj ∈ (chartAt H β).source) :
    DifferentiableAt ℝ
      (fun y : E => fderiv ℝ (extChartAt I α ∘ (extChartAt I β).symm) y)
      (extChartAt I β p.proj) := by
  classical
  rcases exists_open_contDiffOn_chartChange (I := I) (α := α) (β := β) (p := p)
    hα hβ with ⟨U, hUopen, hyβU, hCdiff⟩
  -- On `U`, `fderiv φ_αβ` is differentiable. We use `ContDiffOn.fderiv_of_isOpen`.
  have hCdiff_pred :
      ContDiffOn ℝ 1
        (fderiv ℝ (extChartAt I α ∘ (extChartAt I β).symm)) U := by
    -- From `ContDiffOn ℝ ∞ φ_αβ U` and `1 + 1 ≤ ∞`, `fderiv φ_αβ` is `ContDiffOn ℝ 1`.
    have hcd : ContDiffOn ℝ ∞ (extChartAt I α ∘ (extChartAt I β).symm) U := hCdiff
    -- `1 + 1 = 2 ≤ ∞`; in `WithTop ℕ∞` (the ContDiff scale), `∞ = ((⊤ : ℕ∞) : WithTop ℕ∞)`,
    -- which is the supremum among `ℕ∞`-values, and `2 : WithTop ℕ∞` is the embedded `2 : ℕ∞`.
    -- So the inequality is `((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)`, which holds.
    have hmn : ((1 + 1 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
      exact_mod_cast (le_top : (1 + 1 : ℕ∞) ≤ ⊤)
    have hmn2 : (1 : WithTop ℕ∞) + 1 ≤ (∞ : WithTop ℕ∞) := by
      have : ((1 + 1 : ℕ∞) : WithTop ℕ∞) = (1 : WithTop ℕ∞) + 1 := by push_cast; rfl
      rw [← this]; exact hmn
    exact hcd.fderiv_of_isOpen hUopen hmn2
  -- Differentiability at `y_β` from `ContDiffOn ℝ 1`.
  have hdwa : DifferentiableWithinAt ℝ
      (fderiv ℝ (extChartAt I α ∘ (extChartAt I β).symm)) U
      (extChartAt I β p.proj) :=
    (hCdiff_pred _ hyβU).differentiableWithinAt one_ne_zero
  exact hdwa.differentiableAt (hUopen.mem_nhds hyβU)

/-- `HasFDerivAt` form of the previous lemma. -/
lemma hasFDerivAt_fderiv_chartChange (α β : M)
    {p : TangentBundle I M}
    (hα : p.proj ∈ (chartAt H α).source)
    (hβ : p.proj ∈ (chartAt H β).source) :
    HasFDerivAt
      (fun y : E => fderiv ℝ (extChartAt I α ∘ (extChartAt I β).symm) y)
      (fderiv ℝ
        (fun y : E => fderiv ℝ (extChartAt I α ∘ (extChartAt I β).symm) y)
        (extChartAt I β p.proj))
      (extChartAt I β p.proj) :=
  (differentiableAt_fderiv_chartChange (I := I) (α := α) (β := β) (p := p)
      hα hβ).hasFDerivAt

/-- `HasFDerivAt` form of `differentiableAt_chartChange`. -/
lemma hasFDerivAt_chartChange (α β : M)
    {p : TangentBundle I M}
    (hα : p.proj ∈ (chartAt H α).source)
    (hβ : p.proj ∈ (chartAt H β).source) :
    HasFDerivAt (extChartAt I α ∘ (extChartAt I β).symm)
      (fderiv ℝ (extChartAt I α ∘ (extChartAt I β).symm) (extChartAt I β p.proj))
      (extChartAt I β p.proj) :=
  (differentiableAt_chartChange (I := I) (α := α) (β := β) (p := p) hα hβ).hasFDerivAt

/-- The base chart change `φ_αβ` is `C²` on a neighbourhood of `y_β`. We
need this to apply Schwarz symmetry of the second derivative. -/
lemma eventually_hasFDerivAt_chartChange (α β : M)
    {p : TangentBundle I M}
    (hα : p.proj ∈ (chartAt H α).source)
    (hβ : p.proj ∈ (chartAt H β).source) :
    ∀ᶠ y in 𝓝 (extChartAt I β p.proj),
      HasFDerivAt (extChartAt I α ∘ (extChartAt I β).symm)
        (fderiv ℝ (extChartAt I α ∘ (extChartAt I β).symm) y) y := by
  classical
  rcases exists_open_contDiffOn_chartChange (I := I) (α := α) (β := β) (p := p)
    hα hβ with ⟨U, hUopen, hyβU, hCdiff⟩
  -- On `U`, `φ_αβ` is `C^∞` hence differentiable; HasFDerivAt holds at each point of `U`.
  refine Filter.eventually_of_mem (hUopen.mem_nhds hyβU) (fun y hyU => ?_)
  -- Differentiability at `y ∈ U` from `ContDiffOn ℝ 1 φ_αβ U` (or `∞`).
  have hcdwa : ContDiffWithinAt ℝ ∞
      (extChartAt I α ∘ (extChartAt I β).symm) U y := hCdiff _ hyU
  have hdwa : DifferentiableWithinAt ℝ
      (extChartAt I α ∘ (extChartAt I β).symm) U y :=
    hcdwa.differentiableWithinAt (by simp)
  exact (hdwa.differentiableAt (hUopen.mem_nhds hyU)).hasFDerivAt

/-! ## Schwarz symmetry of the second derivative -/

/-- The second derivative of `φ_αβ` at `y_β` is symmetric in its two
arguments. -/
lemma second_derivative_chartChange_symm (α β : M)
    {p : TangentBundle I M}
    (hα : p.proj ∈ (chartAt H α).source)
    (hβ : p.proj ∈ (chartAt H β).source)
    (v w : E) :
    fderiv ℝ (fun y : E => fderiv ℝ (extChartAt I α ∘ (extChartAt I β).symm) y)
      (extChartAt I β p.proj) v w =
    fderiv ℝ (fun y : E => fderiv ℝ (extChartAt I α ∘ (extChartAt I β).symm) y)
      (extChartAt I β p.proj) w v := by
  classical
  have hev := eventually_hasFDerivAt_chartChange (I := I) (α := α) (β := β) (p := p)
    hα hβ
  have hfd := hasFDerivAt_fderiv_chartChange (I := I) (α := α) (β := β) (p := p) hα hβ
  exact second_derivative_symmetric_of_eventually hev hfd v w

/-! ## Computing the fderiv of the explicit chart-transition map -/

/-- The fderiv of the explicit chart-transition map
`(y, w) ↦ (φ_αβ y, fderiv φ_αβ y w)` at `(y_β, v_β)`, applied to `Q : E × E`,
computed via the chain rule. The result is

```
(fderiv φ_αβ y_β Q.1,
 fderiv φ_αβ y_β Q.2 + fderiv (y ↦ fderiv φ_αβ y) y_β Q.1 v_β).
```

We will turn this into the headline form via Schwarz symmetry. -/
lemma hasFDerivAt_explicit_chart_change (α β : M) {p : TangentBundle I M}
    (hα : p.proj ∈ (chartAt H α).source)
    (hβ : p.proj ∈ (chartAt H β).source) :
    HasFDerivAt
      (fun yw : E × E =>
        (extChartAt I α ((extChartAt I β).symm yw.1),
          fderiv ℝ (extChartAt I α ∘ (extChartAt I β).symm) yw.1 yw.2))
      (let φ := extChartAt I α ∘ (extChartAt I β).symm
       let y_β := extChartAt I β p.proj
       let v_β := chartFiberCoord (I := I) β p
       ((fderiv ℝ φ y_β).comp (ContinuousLinearMap.fst ℝ E E)).prod
         ((fderiv ℝ φ y_β).comp (ContinuousLinearMap.snd ℝ E E) +
           ((fderiv ℝ (fun y => fderiv ℝ φ y) y_β).comp
             (ContinuousLinearMap.fst ℝ E E)).flip v_β))
      (extChartAt I β p.proj, chartFiberCoord (I := I) β p) := by
  classical
  -- Define convenient abbreviations.
  set φ : E → E := extChartAt I α ∘ (extChartAt I β).symm with hφ_def
  set y_β : E := extChartAt I β p.proj with hyβ_def
  set v_β : E := chartFiberCoord (I := I) β p with hvβ_def
  -- Step (a): the first coordinate `(y, w) ↦ φ y` has fderiv `(fderiv φ y_β).comp Prod.fst`.
  have hφ_diff : HasFDerivAt φ (fderiv ℝ φ y_β) y_β :=
    hasFDerivAt_chartChange (I := I) (α := α) (β := β) (p := p) hα hβ
  -- `(y, w) ↦ φ y = φ ∘ Prod.fst`.
  have hfst : HasFDerivAt (fun yw : E × E => φ yw.1)
      ((fderiv ℝ φ y_β).comp (ContinuousLinearMap.fst ℝ E E))
      (y_β, v_β) := by
    have hfst_hfd : HasFDerivAt (fun yw : E × E => yw.1)
        (ContinuousLinearMap.fst ℝ E E) (y_β, v_β) :=
      (ContinuousLinearMap.fst ℝ E E).hasFDerivAt
    -- The chain rule for `HasFDerivAt`: composition `φ ∘ (·.1)`.
    exact HasFDerivAt.comp (𝕜 := ℝ) (g := φ) (f := fun yw : E × E => yw.1)
      (x := (y_β, v_β)) hφ_diff hfst_hfd
  -- Step (b): the second coordinate `(y, w) ↦ fderiv φ y w`.
  -- Write `c yw := fderiv φ yw.1` (CLM `E →L[ℝ] E`) and `u yw := yw.2`.
  -- Then second coord is `(c yw) (u yw)` and we use `HasFDerivAt.clm_apply`.
  -- (b1) `c yw = fderiv φ yw.1 = (fderiv φ) ∘ Prod.fst`.
  have hDφ_diff : HasFDerivAt (fun y : E => fderiv ℝ φ y)
      (fderiv ℝ (fun y : E => fderiv ℝ φ y) y_β) y_β :=
    hasFDerivAt_fderiv_chartChange (I := I) (α := α) (β := β) (p := p) hα hβ
  have hc_hfd : HasFDerivAt (fun yw : E × E => fderiv ℝ φ yw.1)
      ((fderiv ℝ (fun y : E => fderiv ℝ φ y) y_β).comp
        (ContinuousLinearMap.fst ℝ E E))
      (y_β, v_β) := by
    have hfst_hfd : HasFDerivAt (fun yw : E × E => yw.1)
        (ContinuousLinearMap.fst ℝ E E) (y_β, v_β) :=
      (ContinuousLinearMap.fst ℝ E E).hasFDerivAt
    exact HasFDerivAt.comp (𝕜 := ℝ) (g := fun y : E => fderiv ℝ φ y)
      (f := fun yw : E × E => yw.1) (x := (y_β, v_β)) hDφ_diff hfst_hfd
  -- (b2) `u yw = yw.2`, with fderiv `Prod.snd`.
  have hu_hfd : HasFDerivAt (fun yw : E × E => yw.2)
      (ContinuousLinearMap.snd ℝ E E) (y_β, v_β) :=
    (ContinuousLinearMap.snd ℝ E E).hasFDerivAt
  -- (b3) Combine via `HasFDerivAt.clm_apply`.
  -- The fderiv of `yw ↦ (c yw) (u yw)` at `(y_β, v_β)` is
  --   `(c (y_β, v_β)).comp u' + c'.flip (u (y_β, v_β))`.
  -- Here:
  --   `c (y_β, v_β) = fderiv φ y_β`.
  --   `u' = Prod.snd`.
  --   `c' = (fderiv (y ↦ fderiv φ y) y_β).comp Prod.fst`.
  --   `u (y_β, v_β) = v_β`.
  have hsnd : HasFDerivAt
      (fun yw : E × E => (fderiv ℝ φ yw.1) yw.2)
      ((fderiv ℝ φ y_β).comp (ContinuousLinearMap.snd ℝ E E) +
        ((fderiv ℝ (fun y : E => fderiv ℝ φ y) y_β).comp
          (ContinuousLinearMap.fst ℝ E E)).flip v_β)
      (y_β, v_β) := hc_hfd.clm_apply hu_hfd
  -- (c) Combine first and second components into a product. We need to
  -- recognize the target function as the product of its components.
  -- The function we want to differentiate is `yw ↦ (φ yw.1, fderiv φ yw.1 yw.2)`.
  -- This is exactly the prod of the two components.
  -- Use `HasFDerivAt.prodMk`:
  exact hfst.prodMk hsnd

/-! ## Main theorem -/

/-- **The chart-α-vs-chart-β chart-transition formula on `T(TM)` at points
with coincident projection on `M`.**

Let `α β : M` and `p : TangentBundle I M` with `p.proj ∈ (chartAt H α).source`
and `p.proj ∈ (chartAt H β).source`. Write:

* `y_β := extChartAt I β p.proj` (the β-chart image of the base of `p`);
* `φ_αβ := extChartAt I α ∘ (extChartAt I β).symm` (the base chart change);
* `v_β := chartFiberCoord β p` (the β-fibre coordinate of `p`).

Then for every `Q : E × E`,
```
(trivAt-on-T(TM) α).continuousLinearMapAt p ((trivAt-on-T(TM) β).symmL p Q) =
  (fderiv φ_αβ y_β Q.1,
   fderiv φ_αβ y_β Q.2 + fderiv (y ↦ fderiv φ_αβ y Q.1) y_β v_β).
```
The first component is the base-chart Jacobian applied to `Q.1`. The
second is the base-chart Jacobian applied to `Q.2`, plus the
second-derivative correction `D²φ_αβ y_β (v_β, Q.1)`. The correction
appears because the fibre coordinate in the β-trivialisation must be
transported to the α-trivialisation, and that transport varies with the
base point. -/
theorem mfderiv_T_TM_chart_change_apply
    (α β : M) {p : TangentBundle I M}
    (hα : p.proj ∈ (chartAt H α).source)
    (hβ : p.proj ∈ (chartAt H β).source)
    (Q : E × E) :
    let y_β := extChartAt I β p.proj
    let φ_αβ := extChartAt I α ∘ (extChartAt I β).symm
    let v_β := chartFiberCoord (I := I) β p
    (trivializationAt (E × E) (TangentSpace I.tangent)
        (⟨α, (0 : E)⟩ : TangentBundle I M)).continuousLinearMapAt ℝ p
      ((trivializationAt (E × E) (TangentSpace I.tangent)
          (⟨β, (0 : E)⟩ : TangentBundle I M)).symmL ℝ p Q) =
      (fderiv ℝ φ_αβ y_β Q.1,
       fderiv ℝ φ_αβ y_β Q.2 +
         fderiv ℝ (fun y => fderiv ℝ φ_αβ y Q.1) y_β v_β) := by
  classical
  -- Introduce the let-bindings to match the body.
  simp only
  -- Abbreviations.
  set φ : E → E := extChartAt I α ∘ (extChartAt I β).symm with hφ_def
  set y_β : E := extChartAt I β p.proj with hyβ_def
  set v_β : E := chartFiberCoord (I := I) β p with hvβ_def
  -- Step (1): convert the LHS to the coord-change of `tangentBundleCore I.tangent (TM)` at `p`.
  -- (1a) `(triv-α-on-T(TM)).continuousLinearMapAt ℝ p = coordChange (achart p) (achart ⟨α,0⟩) p`.
  have hp_chart_α : p ∈ (chartAt (ModelProd H E)
      (⟨α, (0 : E)⟩ : TangentBundle I M)).source := by
    rw [TangentBundle.mem_chart_source_iff (I := I) (M := M) p
      (⟨α, (0 : E)⟩ : TangentBundle I M)]
    exact hα
  have hp_chart_β : p ∈ (chartAt (ModelProd H E)
      (⟨β, (0 : E)⟩ : TangentBundle I M)).source := by
    rw [TangentBundle.mem_chart_source_iff (I := I) (M := M) p
      (⟨β, (0 : E)⟩ : TangentBundle I M)]
    exact hβ
  -- (1b) Convert α trivialization CLM to coord-change in the tangent bundle of TM.
  have hα_eq_core :
      (trivializationAt (E × E) (TangentSpace I.tangent)
          (⟨α, (0 : E)⟩ : TangentBundle I M)).continuousLinearMapAt ℝ p =
        (tangentBundleCore I.tangent (TangentBundle I M)).coordChange
          (achart (ModelProd H E) p)
          (achart (ModelProd H E) (⟨α, (0 : E)⟩ : TangentBundle I M)) p :=
    TangentBundle.continuousLinearMapAt_trivializationAt_eq_core
      (I := I.tangent) (M := TangentBundle I M)
      (b₀ := (⟨α, (0 : E)⟩ : TangentBundle I M)) (b := p) hp_chart_α
  -- (1c) Convert β trivialization symmL to coord-change.
  have hβ_symmL_eq_core :
      (trivializationAt (E × E) (TangentSpace I.tangent)
          (⟨β, (0 : E)⟩ : TangentBundle I M)).symmL ℝ p =
        (tangentBundleCore I.tangent (TangentBundle I M)).coordChange
          (achart (ModelProd H E) (⟨β, (0 : E)⟩ : TangentBundle I M))
          (achart (ModelProd H E) p) p :=
    TangentBundle.symmL_trivializationAt_eq_core
      (I := I.tangent) (M := TangentBundle I M)
      (b₀ := (⟨β, (0 : E)⟩ : TangentBundle I M)) (b := p) hp_chart_β
  rw [hα_eq_core, hβ_symmL_eq_core]
  -- Step (2): compose via `coordChange_comp`.
  have hp_baseSet :
      p ∈ (tangentBundleCore I.tangent (TangentBundle I M)).baseSet
            (achart (ModelProd H E) (⟨β, (0 : E)⟩ : TangentBundle I M)) ∩
          (tangentBundleCore I.tangent (TangentBundle I M)).baseSet
            (achart (ModelProd H E) p) ∩
          (tangentBundleCore I.tangent (TangentBundle I M)).baseSet
            (achart (ModelProd H E)
              (⟨α, (0 : E)⟩ : TangentBundle I M)) := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [tangentBundleCore_baseSet]; exact hp_chart_β
    · rw [tangentBundleCore_baseSet]; exact mem_chart_source (ModelProd H E) p
    · rw [tangentBundleCore_baseSet]; exact hp_chart_α
  have hcomp :=
    (tangentBundleCore I.tangent (TangentBundle I M)).coordChange_comp
      (achart (ModelProd H E) (⟨β, (0 : E)⟩ : TangentBundle I M))
      (achart (ModelProd H E) p)
      (achart (ModelProd H E) (⟨α, (0 : E)⟩ : TangentBundle I M))
      p hp_baseSet Q
  -- `hcomp` has form: `coord(achart p)(achart ⟨α,0⟩) (coord(achart ⟨β,0⟩)(achart p) Q) =
  --                    coord(achart ⟨β,0⟩)(achart ⟨α,0⟩) Q`.
  -- The current goal's LHS matches the LHS of `hcomp`. Use `Eq.trans`.
  -- `rw [hcomp]` was failing due to subtle defeq issues — use `Eq.trans` directly.
  -- Step (3): identify the coord-change with `fderivWithin` of the tangent-bundle chart change.
  have hcoord_eq :=
    tangentBundleCore_coordChange_achart (I := I.tangent) (M := TangentBundle I M)
      (x := (⟨β, (0 : E)⟩ : TangentBundle I M))
      (x' := (⟨α, (0 : E)⟩ : TangentBundle I M))
      (z := p)
  -- We use `calc`:
  --   LHS = coord(β,0)(α,0) Q          (by hcomp)
  --       = (fderivWithin ...) Q       (by hcoord_eq)
  --       = (fderiv ...) Q             (by fderivWithin_univ, range I.tangent = univ)
  -- We delay these manipulations: rewrite RHS to canonical form, then finish via congr.
  refine hcomp.trans ?_
  rw [hcoord_eq]
  -- Goal:
  -- fderivWithin ℝ
  --   (extChartAt I.tangent ⟨α,0⟩ ∘ (extChartAt I.tangent ⟨β,0⟩).symm)
  --   (range I.tangent) (extChartAt I.tangent ⟨β,0⟩ p) Q =
  -- (fderiv ℝ φ y_β Q.1, fderiv ℝ φ y_β Q.2 + fderiv ℝ (fun y => fderiv ℝ φ y Q.1) y_β v_β)
  -- Step (4): convert `fderivWithin (range I.tangent) = fderiv` via boundarylessness.
  have hrange : (range I.tangent : Set (E × E)) = Set.univ :=
    ModelWithCorners.range_eq_univ I.tangent
  -- Step (5): use `EventuallyEq.fderiv_eq` to convert the chart change to
  -- the explicit form `(y, w) ↦ (φ y, fderiv φ y w)`.
  have hev := eventuallyEq_extChartAt_tangent_chart_change (I := I) (α := α) (β := β)
    (p := p) hα hβ
  -- `hev` lives in `𝓝 (extChartAt I.tangent ⟨β, 0⟩ p)`. We need to compute
  -- `fderiv` at that point.
  have hfderivWithin_eq :
      fderivWithin ℝ
          (fun yw : E × E => extChartAt I.tangent
              (⟨α, (0 : E)⟩ : TangentBundle I M)
              ((extChartAt I.tangent (⟨β, (0 : E)⟩ : TangentBundle I M)).symm yw))
          (range I.tangent)
          (extChartAt I.tangent (⟨β, (0 : E)⟩ : TangentBundle I M) p) =
        fderiv ℝ
          (fun yw : E × E => extChartAt I.tangent
              (⟨α, (0 : E)⟩ : TangentBundle I M)
              ((extChartAt I.tangent (⟨β, (0 : E)⟩ : TangentBundle I M)).symm yw))
          (extChartAt I.tangent (⟨β, (0 : E)⟩ : TangentBundle I M) p) := by
    rw [hrange, fderivWithin_univ]
  -- The composition `extChartAt I.tangent ⟨α,0⟩ ∘ (extChartAt I.tangent ⟨β,0⟩).symm`
  -- as a function rewrites as `fun yw => extChartAt I.tangent ⟨α,0⟩ ((...).symm yw)`.
  -- This is definitionally true.
  show fderivWithin ℝ
      (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M) ∘
        (extChartAt I.tangent (⟨β, (0 : E)⟩ : TangentBundle I M)).symm)
      (range I.tangent)
      (extChartAt I.tangent (⟨β, (0 : E)⟩ : TangentBundle I M) p) Q = _
  rw [show
      (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M) ∘
        (extChartAt I.tangent (⟨β, (0 : E)⟩ : TangentBundle I M)).symm) =
      (fun yw : E × E => extChartAt I.tangent
        (⟨α, (0 : E)⟩ : TangentBundle I M)
        ((extChartAt I.tangent (⟨β, (0 : E)⟩ : TangentBundle I M)).symm yw))
    from rfl]
  rw [hfderivWithin_eq]
  -- Now switch to the explicit chart change.
  have hfderiv_eq_explicit :
      fderiv ℝ
          (fun yw : E × E => extChartAt I.tangent
              (⟨α, (0 : E)⟩ : TangentBundle I M)
              ((extChartAt I.tangent (⟨β, (0 : E)⟩ : TangentBundle I M)).symm yw))
          (extChartAt I.tangent (⟨β, (0 : E)⟩ : TangentBundle I M) p) =
        fderiv ℝ
          (fun yw : E × E =>
            (extChartAt I α ((extChartAt I β).symm yw.1),
              fderiv ℝ φ yw.1 yw.2))
          (extChartAt I.tangent (⟨β, (0 : E)⟩ : TangentBundle I M) p) := by
    exact hev.fderiv_eq
  rw [hfderiv_eq_explicit]
  -- Step (6): compute the fderiv of the explicit map using `hasFDerivAt_explicit_chart_change`.
  -- First normalise the point `extChartAt I.tangent ⟨β, 0⟩ p` to `(y_β, v_β)`.
  have hp_β_eval :
      extChartAt I.tangent (⟨β, (0 : E)⟩ : TangentBundle I M) p = (y_β, v_β) :=
    extChartAt_tangent_zeroSection_apply (I := I) (α := β) (q := p)
  rw [hp_β_eval]
  -- Now the goal is
  -- fderiv ℝ (yw ↦ (extChartAt I α ((extChartAt I β).symm yw.1), fderiv φ yw.1 yw.2))
  --   (y_β, v_β) Q =
  -- (fderiv φ y_β Q.1, fderiv φ y_β Q.2 + fderiv (y ↦ fderiv φ y Q.1) y_β v_β)
  have hexp := hasFDerivAt_explicit_chart_change (I := I) (α := α) (β := β) (p := p)
    hα hβ
  -- `hexp.fderiv` rewrites the lhs to the explicit CLM.
  rw [hexp.fderiv]
  -- Now compute the CLM applied to Q. We unfold the let-bindings.
  -- The CLM is `((fderiv φ y_β) ∘L Prod.fst).prod (...)`.
  -- Applied to Q = (Q.1, Q.2):
  --   First component: `((fderiv φ y_β) ∘L Prod.fst) Q = fderiv φ y_β Q.1`.
  --   Second component: `((fderiv φ y_β) ∘L Prod.snd) Q + ((D²φ y_β) ∘L Prod.fst).flip v_β Q`
  --     = fderiv φ y_β Q.2 + (D²φ y_β Q.1) v_β.
  apply Prod.ext
  · -- First component: definitional.
    rfl
  · -- Second component.
    -- Goal: `(fderiv φ y_β).comp Prod.snd Q + ((D²φ y_β).comp Prod.fst).flip v_β Q
    --        = fderiv φ y_β Q.2 + fderiv (fun y => fderiv φ y Q.1) y_β v_β`.
    show (fderiv ℝ φ y_β).comp (ContinuousLinearMap.snd ℝ E E) Q +
          ((fderiv ℝ (fun y => fderiv ℝ φ y) y_β).comp
            (ContinuousLinearMap.fst ℝ E E)).flip v_β Q =
      (fderiv ℝ φ y_β) Q.2 + (fderiv ℝ (fun y => fderiv ℝ φ y Q.1) y_β) v_β
    -- First summand: `(A.comp Prod.snd) Q = A Q.2`, by `ContinuousLinearMap.comp_apply`.
    -- Second summand: `B.flip v_β Q = B Q v_β`, by `ContinuousLinearMap.flip_apply`.
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_snd',
      ContinuousLinearMap.flip_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_fst']
    -- Goal: `fderiv φ y_β Q.2 + fderiv (fun y => fderiv φ y) y_β Q.1 v_β =
    --       fderiv φ y_β Q.2 + fderiv (fun y => fderiv φ y Q.1) y_β v_β`.
    -- Cancel the common first summand.
    congr 1
    -- Goal: `fderiv (fun y => fderiv φ y) y_β Q.1 v_β = fderiv (fun y => fderiv φ y Q.1) y_β v_β`.
    -- We use Schwarz to swap arguments in the LHS, and the linear-evaluation chain rule on the RHS.
    -- Set f := fun y => fderiv ℝ φ y.
    set f : E → E →L[ℝ] E := fun y => fderiv ℝ φ y with hf_def
    -- Step (i): apply Schwarz to swap the two arguments on the LHS.
    have hswap : fderiv ℝ f y_β Q.1 v_β = fderiv ℝ f y_β v_β Q.1 :=
      second_derivative_chartChange_symm (I := I) (α := α) (β := β) (p := p) hα hβ Q.1 v_β
    rw [hswap]
    -- Step (ii): identify `fderiv (y ↦ fderiv φ y Q.1) y_β v_β` with `fderiv f y_β v_β Q.1`.
    -- Define `apply_at_Q.1 : (E →L[ℝ] E) →L[ℝ] E` by `L ↦ L Q.1`.
    let appQ1 : (E →L[ℝ] E) →L[ℝ] E := ContinuousLinearMap.apply ℝ E Q.1
    have happQ1_def : ∀ L : E →L[ℝ] E, appQ1 L = L Q.1 := fun _ => rfl
    -- `y ↦ fderiv φ y Q.1 = appQ1 ∘ f`.
    have hg_eq : (fun y : E => fderiv ℝ φ y Q.1) = appQ1 ∘ f := by
      funext y; simp [happQ1_def, f, appQ1]
    -- HasFDerivAt witness for f.
    have hf_hfd : HasFDerivAt f (fderiv ℝ f y_β) y_β :=
      hasFDerivAt_fderiv_chartChange (I := I) (α := α) (β := β) (p := p) hα hβ
    -- HasFDerivAt witness for appQ1.
    have happQ1_hfd : HasFDerivAt (⇑appQ1) appQ1 (f y_β) := appQ1.hasFDerivAt
    -- Composition.
    have hcomp_hfd : HasFDerivAt (⇑appQ1 ∘ f) (appQ1.comp (fderiv ℝ f y_β)) y_β :=
      HasFDerivAt.comp (𝕜 := ℝ) (g := ⇑appQ1) (f := f) (x := y_β)
        happQ1_hfd hf_hfd
    -- Rewrite back to `y ↦ fderiv φ y Q.1`.
    rw [← hg_eq] at hcomp_hfd
    -- The fderiv equals the unique HasFDerivAt witness.
    have hfderiv_eq_app :
        fderiv ℝ (fun y : E => fderiv ℝ φ y Q.1) y_β = appQ1.comp (fderiv ℝ f y_β) :=
      hcomp_hfd.fderiv
    rw [hfderiv_eq_app]
    -- Apply both sides to v_β.
    -- `(appQ1.comp (fderiv f y_β)) v_β = appQ1 (fderiv f y_β v_β) = fderiv f y_β v_β Q.1`.
    rw [ContinuousLinearMap.comp_apply, happQ1_def]

end Geodesic
end Riemannian
end Geometry
end DifferentialGeometry

end
