import DifferentialGeometry.Geometry.Riemannian.Geodesic.ChartTransitionTTM
import DifferentialGeometry.Geometry.Riemannian.Geodesic.Equation
import DifferentialGeometry.Integral.Connection.LeviCivita

set_option linter.unusedSectionVars false
set_option linter.style.show false

/-!
# The classical Christoffel transformation law in chart coordinates

For a smooth Riemannian metric `g` on a boundaryless smooth manifold `M` and a
point `x : M` lying in the chart sources at two basepoints `α, β : M`, the
chart-coordinate Christoffel contraction transforms under a coordinate change
as
```
Γ_α(J v_β, J v_β)(φ_α x)
  = J (Γ_β(v_β, v_β)(φ_β x)) − D²φ_αβ(v_β, v_β)
```
where
* `φ_α := extChartAt I α`, `φ_β := extChartAt I β` are the extended charts,
* `φ_αβ := φ_α ∘ φ_β.symm` is the chart-change map on the base,
* `J := fderiv φ_αβ (φ_β x)` is its Jacobian,
* `D²φ_αβ(v_β, v_β) := fderiv (y ↦ fderiv φ_αβ y v_β) (φ_β x) v_β` is the
  second derivative diagonally evaluated on `v_β`.

This file ships the headline
`chartChristoffelContraction_chart_transform` as a consequence of the
chart-overlap consistency of the chart-local Levi-Civita derivative.

## Mathematical content

The Levi-Civita derivative `∇_v σ` is intrinsic, so its presentations in the
α-chart and β-chart agree at any point `x` in both chart sources. The α-chart
presentation of `∇_v σ` at `x` is
```
trivFromE α x (fderiv (σ̃_α ∘ φ_α.symm) (φ_α x) (trivToE α x v)
              + Γ_α(σ̃_α x, ·) (v))
```
where `σ̃_α y := trivToE α y (σ y)` is the α-trivialised representation of `σ`.
The α-chart and β-chart representations are related at the fibre level by
`σ̃_α y = J(y) · σ̃_β y`, where `J(y) := tangentCoordChange β α y`. Applied at
`y = x`, this gives `σ̃_α x = J v_β` (when `σ̃_β x = v_β`).

Plugging both presentations into the chart-overlap equation
`∇_{σ(x)}σ |_α = ∇_{σ(x)}σ |_β` (evaluated as elements of `T_x M` and converted
to `E` via `trivToE α x`), expanding the chain rule for `fderiv (σ̃_α ∘
φ_α.symm)`, and using bilinearity of the trivialisation chart change, the
section-derivative terms cancel and the residual second-derivative correction
appears in the form `D²φ_αβ(v_β, v_β)`.

## Hypotheses

* `[I.Boundaryless]` — needed to convert `tangentCoordChange β α` (defined via
  `fderivWithin (range I)`) to ordinary `fderiv`, and to discharge the chart-
  source / chart-target memberships required by the goodset constructions.
* `[SigmaCompactSpace M]`, `[T2Space M]` — propagated from the chart-overlap
  consistency theorem in `Integral/Connection/LeviCivita.lean`, which uses
  `ContMDiffSection.exists_eq_at` and the Koszul local-uniqueness argument.

## Output

* `chartChristoffelContraction_chart_transform` — the headline equation in
  the form stated above.
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
variable [SigmaCompactSpace M] [T2Space M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection

/-! ## Bridge between `christoffelCorrection` and `chartChristoffelContraction`

`christoffelCorrection g α x Y v` is the CLM-valued Christoffel-correction in
the chart-local Levi-Civita formula, with `Y : E` the section's α-trivialised
value and `v : TangentSpace I x` the tangent-vector argument. The pointwise
formula matches `chartChristoffelContraction g α (trivToE α x v) Y (φ_α x)`
modulo a Finset.sum reorder. -/

/-- Reordering the triple sum: `∑ i ∑ j ∑ k = ∑ k ∑ i ∑ j`. -/
private lemma sum_reorder_ijk_to_kij {n : ℕ} (f : Fin n → Fin n → Fin n → E) :
    ∑ i, ∑ j, ∑ k, f i j k = ∑ k, ∑ i, ∑ j, f i j k := by
  classical
  -- Swap j-k inside, then i-k outside.
  -- ∑ i ∑ j ∑ k f = ∑ i ∑ k ∑ j f  (Finset.sum_comm on each i)
  --             = ∑ k ∑ i ∑ j f  (Finset.sum_comm outermost).
  conv_lhs =>
    rw [show (fun i : Fin n => ∑ j, ∑ k, f i j k) =
        fun i : Fin n => ∑ k, ∑ j, f i j k from by
      funext i; exact Finset.sum_comm]
  exact Finset.sum_comm

/-- Bridge: `christoffelCorrection g α x Y v` equals
`chartChristoffelContraction g α (trivToE α x v) Y (φ_α x)`. -/
private lemma christoffelCorrection_eq_chartChristoffelContraction
    (g : SmoothRiemannianMetric I M) (α : M) (x : M) (Y : E)
    (v : TangentSpace I x) :
    christoffelCorrection (I := I) g α x Y v =
      chartChristoffelContraction (I := I) g α
        (trivToE (I := I) α x v) Y (extChartAt I α x) := by
  classical
  rw [christoffelCorrection_apply]
  -- Reorder ∑ i ∑ j ∑ k → ∑ k ∑ i ∑ j and apply factor-rearrangement.
  rw [sum_reorder_ijk_to_kij]
  -- Unfold `chartChristoffelContraction`.
  unfold chartChristoffelContraction
  refine Finset.sum_congr rfl ?_
  intro k _
  -- Goal: ∑ i, ∑ j, (repr (trivToE v) i * repr Y j * Γ^k_{ij}(φ_α x)) • e_k =
  --       (∑ i ∑ j, Γ^k_{ij}(φ_α x) * chartCoord i (trivToE v) * chartCoord j Y) • e_k
  -- Pull the • e_k inside the sums; turn the RHS into a double sum of smuls.
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl ?_
  intro j _
  -- Both sides are now `(coefficient) • e_k`; equality of coefficients by ring.
  congr 1
  -- `chartCoord = repr_at_index`, by `chartCoord_def`.
  simp only [chartCoord_def]
  ring

/-! ## The base-level chart-change identity

`trivToE α x ∘L trivFromE β x = tangentCoordChange β α x`, which under
`[I.Boundaryless]` equals `fderiv (extChartAt I α ∘ (extChartAt I β).symm)
(extChartAt I β x)`. -/

section TrivChartChange

variable [I.Boundaryless]

/-- The composite `trivToE α x ∘ trivFromE β x` equals the tangent-bundle
core chart change `tangentCoordChange β α x`, evaluated at `x`. -/
private lemma trivToE_trivFromE_eq_coordChange
    (α β : M) {x : M}
    (hα : x ∈ (chartAt H α).source)
    (hβ : x ∈ (chartAt H β).source)
    (w : E) :
    trivToE (I := I) α x (trivFromE (I := I) β x w) =
      (tangentBundleCore I M).coordChange (achart H β) (achart H α) x w := by
  classical
  -- Step (a): `trivToE α x = coordChange (achart x) (achart α) x`.
  have hα_eq_core :
      (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ x =
        (tangentBundleCore I M).coordChange (achart H x) (achart H α) x :=
    TangentBundle.continuousLinearMapAt_trivializationAt_eq_core
      (I := I) (M := M) (b₀ := α) (b := x) hα
  -- Step (b): `trivFromE β x = coordChange (achart β) (achart x) x`.
  have hβ_symmL_eq_core :
      (trivializationAt E (TangentSpace I) β).symmL ℝ x =
        (tangentBundleCore I M).coordChange (achart H β) (achart H x) x :=
    TangentBundle.symmL_trivializationAt_eq_core
      (I := I) (M := M) (b₀ := β) (b := x) hβ
  -- Apply both rewrites and compose via `coordChange_comp`.
  show ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ x)
      ((trivializationAt E (TangentSpace I) β).symmL ℝ x w) = _
  rw [hα_eq_core, hβ_symmL_eq_core]
  have hbaseSet :
      x ∈ (tangentBundleCore I M).baseSet (achart H β) ∩
          (tangentBundleCore I M).baseSet (achart H x) ∩
          (tangentBundleCore I M).baseSet (achart H α) := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [tangentBundleCore_baseSet]; exact hβ
    · rw [tangentBundleCore_baseSet]; exact mem_chart_source H x
    · rw [tangentBundleCore_baseSet]; exact hα
  exact (tangentBundleCore I M).coordChange_comp
    (i := achart H β) (j := achart H x) (k := achart H α) x hbaseSet w

/-- The composite `trivToE α x ∘ trivFromE β x` equals
`fderiv (extChartAt I α ∘ (extChartAt I β).symm) (extChartAt I β x)`,
under `[I.Boundaryless]`. -/
private lemma trivToE_trivFromE_eq_fderiv_chartChange
    (α β : M) {x : M}
    (hα : x ∈ (chartAt H α).source)
    (hβ : x ∈ (chartAt H β).source)
    (w : E) :
    trivToE (I := I) α x (trivFromE (I := I) β x w) =
      fderiv ℝ (extChartAt I α ∘ (extChartAt I β).symm)
        (extChartAt I β x) w := by
  classical
  -- Combine the `coordChange` identification with `tangentBundleCore_coordChange_achart`.
  rw [trivToE_trivFromE_eq_coordChange (I := I) α β hα hβ w]
  -- `coordChange (achart β) (achart α) x = fderivWithin (range I) φ_αβ (φ_β x)`.
  rw [tangentBundleCore_coordChange_achart (I := I) (M := M) β α x]
  -- Convert `fderivWithin (range I)` to `fderiv` using `[I.Boundaryless]`.
  have hrange : (range I : Set E) = Set.univ :=
    ModelWithCorners.range_eq_univ I
  rw [hrange, fderivWithin_univ]

end TrivChartChange

/-! ## The main proof

We expand `chartLeviCivita_chart_overlap` applied to a smooth global section
`Y` with `Y x = trivFromE β x v_β`, convert to `E` via `trivToE α x`, and
match terms. -/

section ChartChristoffelTransform

variable [I.Boundaryless]

/-- A smooth global tangent-bundle section with prescribed fibre value at `x`. -/
private def globalY (β : M) (x : M) (v_β : E) :
    Cₛ^(⊤ : ℕ∞)⟮I; E, (TangentSpace I : M → Type _)⟯ :=
  (ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
    (F := E) (V := (TangentSpace I : M → Type _)) x
    (trivFromE (I := I) β x v_β)).choose

private lemma globalY_apply (β : M) (x : M) (v_β : E) :
    (globalY (I := I) β x v_β : Π y : M, TangentSpace I y) x =
      trivFromE (I := I) β x v_β :=
  (ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
    (F := E) (V := (TangentSpace I : M → Type _)) x
    (trivFromE (I := I) β x v_β)).choose_spec

private lemma globalY_mdiffAt (β : M) (x : M) (v_β : E) (y : M) :
    MDiffAt (T% (globalY (I := I) β x v_β : Π y : M, TangentSpace I y)) y :=
  (globalY (I := I) β x v_β).mdifferentiableAt

/-- Chart-α-representation of `Y` is the result of applying the bundle chart
change `trivToE α y ∘ trivFromE β y` to the chart-β-representation of `Y`,
as long as `y` is in both chart sources. -/
private lemma chartE_section_repr_α_eq_chartChange_β
    (α β : M) {y : M}
    (_hα : y ∈ (chartAt H α).source)
    (hβ : y ∈ (chartAt H β).source)
    (Y : Π y : M, TangentSpace I y) :
    chartE_section_repr (I := I) α Y y =
      trivToE (I := I) α y
        (trivFromE (I := I) β y (chartE_section_repr (I := I) β Y y)) := by
  classical
  -- `chartE_section_repr α Y y = trivToE α y (Y y)`.
  rw [chartE_section_repr_eq_trivToE]
  rw [chartE_section_repr_eq_trivToE]
  -- `trivFromE β y (trivToE β y (Y y)) = Y y` on the β baseSet (= chart source at β).
  have hβ_base : y ∈ (trivializationAt E (TangentSpace I) β).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact hβ
  rw [trivFromE_trivToE (I := I) β hβ_base]

/-- Pointwise on a neighbourhood of `x` in both chart sources, the chart-α
representation of `Y` equals `fderiv φ_αβ (φ_β y) · chartE_section_repr β Y y`. -/
private lemma chartE_section_repr_α_eq_J_chartE_β_pointwise
    (α β : M) {y : M}
    (hα : y ∈ (chartAt H α).source)
    (hβ : y ∈ (chartAt H β).source)
    (Y : Π y : M, TangentSpace I y) :
    chartE_section_repr (I := I) α Y y =
      fderiv ℝ (extChartAt I α ∘ (extChartAt I β).symm)
        (extChartAt I β y) (chartE_section_repr (I := I) β Y y) := by
  classical
  rw [chartE_section_repr_α_eq_chartChange_β (I := I) α β hα hβ Y]
  exact trivToE_trivFromE_eq_fderiv_chartChange (I := I) α β hα hβ _

end ChartChristoffelTransform

/-! ## Chain-rule analysis of `(Y_α ∘ φ_α.symm)` near `φ_α x`

Express `chartE_section_repr α Y ∘ (extChartAt I α).symm` as a composition
involving `fderiv φ_αβ` and the inverse chart change `extChartAt I β ∘
(extChartAt I α).symm`, then apply the chain rule. -/

section ChainRule

variable [I.Boundaryless]

/-- The α-side chart-pulled-back representation of `Y` agrees with the
"chart-change-conjugated" form on a neighbourhood of `extChartAt I α x`. -/
private lemma eventuallyEq_chartE_repr_α_chartChange_form
    (α β : M) {x : M}
    (hα : x ∈ (chartAt H α).source)
    (hβ : x ∈ (chartAt H β).source)
    (Y : Π y : M, TangentSpace I y) :
    (fun z : E => chartE_section_repr (I := I) α Y ((extChartAt I α).symm z)) =ᶠ[𝓝
      (extChartAt I α x)]
      (fun z : E =>
        fderiv ℝ (extChartAt I α ∘ (extChartAt I β).symm)
          (extChartAt I β ((extChartAt I α).symm z))
          (chartE_section_repr (I := I) β Y ((extChartAt I α).symm z))) := by
  classical
  -- The two functions agree on the open set
  --   `U := (extChartAt I α).target ∩
  --        (extChartAt I α).symm ⁻¹' ((chartAt H α).source ∩ (chartAt H β).source)`,
  -- which is a neighbourhood of `extChartAt I α x`.
  -- Step (a): target open (boundaryless).
  have hα_target_open : IsOpen (extChartAt I α).target := isOpen_extChartAt_target α
  have hα_src_open : IsOpen (chartAt H α).source := (chartAt H α).open_source
  have hβ_src_open : IsOpen (chartAt H β).source := (chartAt H β).open_source
  have hinter_open : IsOpen ((chartAt H α).source ∩ (chartAt H β).source) :=
    hα_src_open.inter hβ_src_open
  -- Step (b): `(extChartAt I α).symm` is continuous on its target.
  have hSymmCts : ContinuousOn (extChartAt I α).symm (extChartAt I α).target :=
    continuousOn_extChartAt_symm α
  -- Step (c): The intersection is open.
  set U : Set E :=
    (extChartAt I α).target ∩
      (extChartAt I α).symm ⁻¹'
        ((chartAt H α).source ∩ (chartAt H β).source)
  have hU_open : IsOpen U :=
    hSymmCts.isOpen_inter_preimage hα_target_open hinter_open
  -- Step (d): `extChartAt I α x ∈ U`.
  have hxα_src : x ∈ (extChartAt I α).source := by
    rw [extChartAt_source]; exact hα
  have hxα_target : extChartAt I α x ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source hxα_src
  have hxα_symm : (extChartAt I α).symm (extChartAt I α x) = x :=
    (extChartAt I α).left_inv hxα_src
  have hxα_inU : extChartAt I α x ∈ U := by
    refine ⟨hxα_target, ?_⟩
    rw [mem_preimage, hxα_symm]
    exact ⟨hα, hβ⟩
  -- Step (e): Pointwise equality on U.
  refine Filter.eventuallyEq_of_mem (s := U) (hU_open.mem_nhds hxα_inU) ?_
  intro z hz
  rcases hz with ⟨_, hsrc⟩
  rw [mem_preimage] at hsrc
  rcases hsrc with ⟨hαsrc, hβsrc⟩
  exact chartE_section_repr_α_eq_J_chartE_β_pointwise (I := I) α β hαsrc hβsrc Y

end ChainRule

/-! ## The headline -/

section Headline

variable [I.Boundaryless]

/-- The chart-β chart source is a neighbourhood of `x` (when `x` is in it). -/
private lemma chartβ_source_mem_nhds (β : M) {x : M}
    (hβ : x ∈ (chartAt H β).source) :
    (chartAt H β).source ∈ 𝓝 x :=
  (chartAt H β).open_source.mem_nhds hβ

/-- The chart-β extended chart target is open at `extChartAt I β x` under
`[I.Boundaryless]`. -/
private lemma extChartAt_β_target_mem_nhds (β : M) {x : M}
    (hβ : x ∈ (chartAt H β).source) :
    (extChartAt I β).target ∈ 𝓝 (extChartAt I β x) := by
  classical
  have hβ_target_open : IsOpen (extChartAt I β).target := isOpen_extChartAt_target β
  have hxβ_src : x ∈ (extChartAt I β).source := by
    rw [extChartAt_source]; exact hβ
  have hxβ_target : extChartAt I β x ∈ (extChartAt I β).target :=
    (extChartAt I β).map_source hxβ_src
  exact hβ_target_open.mem_nhds hxβ_target

/-- `extChartAt I β ∘ (extChartAt I α).symm`, the inverse chart change, has
`fderiv` equal to `(fderiv (extChartAt I α ∘ (extChartAt I β).symm)
(extChartAt I β x))⁻¹` at `extChartAt I α x`. The simpler statement we need:
it has `fderiv` applied to `J v_β` equal to `v_β`. -/
private lemma fderiv_inverse_chartChange_apply
    (α β : M) {x : M}
    (hα : x ∈ (chartAt H α).source)
    (hβ : x ∈ (chartAt H β).source) (v_β : E) :
    fderiv ℝ (extChartAt I β ∘ (extChartAt I α).symm)
        (extChartAt I α x)
        (fderiv ℝ (extChartAt I α ∘ (extChartAt I β).symm)
            (extChartAt I β x) v_β) = v_β := by
  classical
  -- Use the chain rule on `(extChartAt I β ∘ (extChartAt I α).symm) ∘
  --   (extChartAt I α ∘ (extChartAt I β).symm) = id` near `extChartAt I β x`.
  -- For this, we exhibit a neighbourhood of `extChartAt I β x` on which this
  -- composition equals identity, and use `Filter.EventuallyEq.fderiv_eq`.
  -- Apply this to deduce `fderiv (g ∘ f) (φ_β x) = id`, then by chain rule
  -- `fderiv g (f (φ_β x)) ∘ fderiv f (φ_β x) = id`.
  set f : E → E := extChartAt I α ∘ (extChartAt I β).symm with hf_def
  set g : E → E := extChartAt I β ∘ (extChartAt I α).symm with hg_def
  set y_β : E := extChartAt I β x with hyβ_def
  set y_α : E := extChartAt I α x with hyα_def
  -- f(y_β) = y_α.
  have hxβ_src : x ∈ (extChartAt I β).source := by
    rw [extChartAt_source]; exact hβ
  have hxα_src : x ∈ (extChartAt I α).source := by
    rw [extChartAt_source]; exact hα
  have hsymm_β : (extChartAt I β).symm y_β = x :=
    (extChartAt I β).left_inv hxβ_src
  have hsymm_α : (extChartAt I α).symm y_α = x :=
    (extChartAt I α).left_inv hxα_src
  have hfyβ : f y_β = y_α := by
    change extChartAt I α ((extChartAt I β).symm y_β) = y_α
    rw [hsymm_β]
  -- (1) g ∘ f = id on a neighbourhood of y_β.
  -- The neighbourhood is the open set
  --   V := (extChartAt I β).target ∩ (extChartAt I β).symm ⁻¹'
  --        ((chartAt H α).source ∩ (chartAt H β).source).
  have hβ_target_open : IsOpen (extChartAt I β).target := isOpen_extChartAt_target β
  have hα_src_open : IsOpen (chartAt H α).source := (chartAt H α).open_source
  have hβ_src_open : IsOpen (chartAt H β).source := (chartAt H β).open_source
  have hinter_open : IsOpen ((chartAt H α).source ∩ (chartAt H β).source) :=
    hα_src_open.inter hβ_src_open
  have hSymmCts : ContinuousOn (extChartAt I β).symm (extChartAt I β).target :=
    continuousOn_extChartAt_symm β
  set V : Set E :=
    (extChartAt I β).target ∩
      (extChartAt I β).symm ⁻¹'
        ((chartAt H α).source ∩ (chartAt H β).source) with hV_def
  have hV_open : IsOpen V :=
    hSymmCts.isOpen_inter_preimage hβ_target_open hinter_open
  -- y_β ∈ V:
  have hyβ_target : y_β ∈ (extChartAt I β).target :=
    (extChartAt I β).map_source hxβ_src
  have hyβ_inV : y_β ∈ V := by
    refine ⟨hyβ_target, ?_⟩
    rw [mem_preimage, hsymm_β]
    exact ⟨hα, hβ⟩
  -- (2) On V, `g ∘ f` = id.
  have hcomp_id : ∀ z ∈ V, (g ∘ f) z = z := by
    intro z hz
    rcases hz with ⟨hz_t, hz_pre⟩
    rw [mem_preimage] at hz_pre
    rcases hz_pre with ⟨hα_src_z, hβ_src_z⟩
    change extChartAt I β ((extChartAt I α).symm
      (extChartAt I α ((extChartAt I β).symm z))) = z
    have hzβ_src : (extChartAt I β).symm z ∈ (extChartAt I β).source :=
      (extChartAt I β).map_target hz_t
    have hzβ_inv : extChartAt I β ((extChartAt I β).symm z) = z :=
      (extChartAt I β).right_inv hz_t
    -- ((extChartAt I β).symm z) ∈ (extChartAt I α).source via hα_src_z.
    have hzα_src : (extChartAt I β).symm z ∈ (extChartAt I α).source := by
      rw [extChartAt_source]; exact hα_src_z
    rw [(extChartAt I α).left_inv hzα_src, hzβ_inv]
  -- (3) EventuallyEq form.
  have hEv : (g ∘ f) =ᶠ[𝓝 y_β] id := by
    refine Filter.eventuallyEq_of_mem (s := V) (hV_open.mem_nhds hyβ_inV) ?_
    intro z hz
    show (g ∘ f) z = id z
    rw [id_eq]
    exact hcomp_id z hz
  -- (4) Differentiability of f, g at the relevant points.
  -- f differentiable at y_β:
  have hf_diff : DifferentiableAt ℝ f y_β := by
    -- Wrap p with `p.proj = x`.
    let p : TangentBundle I M := (⟨x, (0 : E)⟩ : TangentBundle I M)
    have hpα : p.proj ∈ (chartAt H α).source := hα
    have hpβ : p.proj ∈ (chartAt H β).source := hβ
    have hd := differentiableAt_chartChange (I := I) (α := α) (β := β) (p := p) hpα hpβ
    -- `differentiableAt_chartChange` returns differentiability of
    -- `extChartAt I α ∘ (extChartAt I β).symm` at `extChartAt I β p.proj = y_β`.
    exact hd
  -- g differentiable at y_α:
  have hg_diff : DifferentiableAt ℝ g y_α := by
    let p : TangentBundle I M := (⟨x, (0 : E)⟩ : TangentBundle I M)
    have hpα : p.proj ∈ (chartAt H α).source := hα
    have hpβ : p.proj ∈ (chartAt H β).source := hβ
    have hd := differentiableAt_chartChange (I := I) (α := β) (β := α) (p := p) hpβ hpα
    -- Note: roles of α and β swapped.
    -- This gives differentiability of `extChartAt I β ∘ (extChartAt I α).symm` at
    -- `extChartAt I α p.proj = y_α`.
    exact hd
  -- (5) From the chain rule: `fderiv (g ∘ f) y_β = fderiv g (f y_β) ∘L fderiv f y_β`.
  have hg_diff' : DifferentiableAt ℝ g (f y_β) := by rw [hfyβ]; exact hg_diff
  have hchain : fderiv ℝ (g ∘ f) y_β =
      (fderiv ℝ g (f y_β)).comp (fderiv ℝ f y_β) := by
    rw [fderiv_comp y_β hg_diff' hf_diff]
  -- (6) From EventuallyEq, `fderiv (g ∘ f) y_β = fderiv id y_β = id`.
  have hfd_eq : fderiv ℝ (g ∘ f) y_β = fderiv ℝ (id : E → E) y_β :=
    hEv.fderiv_eq
  have hfd_id : fderiv ℝ (id : E → E) y_β = ContinuousLinearMap.id ℝ E :=
    fderiv_id (𝕜 := ℝ) (x := y_β)
  have hcomp_eq :
      (fderiv ℝ g (f y_β)).comp (fderiv ℝ f y_β) = ContinuousLinearMap.id ℝ E := by
    rw [← hchain, hfd_eq, hfd_id]
  -- (7) Apply to `v_β`.
  -- `((fderiv g (f y_β)).comp (fderiv f y_β)) v_β = v_β`.
  have happ :
      ((fderiv ℝ g (f y_β)).comp (fderiv ℝ f y_β)) v_β = v_β := by
    rw [hcomp_eq]
    rfl
  rw [ContinuousLinearMap.comp_apply] at happ
  rw [hfyβ] at happ
  -- happ : fderiv g y_α (fderiv f y_β v_β) = v_β.
  -- This matches our goal after unfolding f and g.
  show fderiv ℝ (extChartAt I β ∘ (extChartAt I α).symm) y_α
      (fderiv ℝ (extChartAt I α ∘ (extChartAt I β).symm) y_β v_β) = v_β
  exact happ

/- Auxiliary chain-rule lemma: the `fderiv` of the composition `fun z => fderiv
φ_αβ (ψ z) (h z)` at `z = φ_α x`, in direction `J v_β`, computed via the
product rule below. -/

/-- **Auxiliary**: differentiability of `Y_β ∘ φ_α.symm` near `φ_α x`. -/
private lemma differentiableAt_chartE_repr_β_α_pullback
    (α β : M) {x : M}
    (hα : x ∈ (chartAt H α).source)
    (hβ : x ∈ (chartAt H β).source)
    (Y : Π y : M, TangentSpace I y)
    (hY : MDiffAt (T% Y) x) :
    DifferentiableAt ℝ
      ((chartE_section_repr (I := I) β Y) ∘ (extChartAt I α).symm)
      (extChartAt I α x) := by
  classical
  -- `chartE_section_repr β Y : M → E` is MDifferentiable at `x` (transfer via β-trivialisation).
  have hYβ_at : MDiffAt (chartE_section_repr (I := I) β Y) x := by
    have hxβ_base : x ∈ (trivializationAt E (TangentSpace I) β).baseSet := by
      rw [TangentBundle.trivializationAt_baseSet]; exact hβ
    exact (mdifferentiableAt_section_iff_chartE (I := I) β Y hxβ_base).mp hY
  -- Bridge MDiff → DifferentiableAt of chart pullback at the interior point of α-target.
  -- Use `mdifferentiableAt_iff_source_of_mem_source` to get `MDiffWithinAt
  -- (range I)`, then drop to ordinary `DifferentiableAt` since `range I = univ`
  -- under boundarylessness.
  have hmdwa :
      MDiffAt[range I] ((chartE_section_repr (I := I) β Y) ∘
        (extChartAt I α).symm) (extChartAt I α x) :=
    (mdifferentiableAt_iff_source_of_mem_source
      (x := α) (x' := x) (f := chartE_section_repr (I := I) β Y) hα).mp hYβ_at
  -- `range I = univ` under boundarylessness.
  have hrange : (range I : Set E) = Set.univ := ModelWithCorners.range_eq_univ I
  rw [hrange] at hmdwa
  -- `MDiffWithinAt univ` = `MDiff` (model-with-corners with target a vector space).
  have hmd : MDiffAt ((chartE_section_repr (I := I) β Y) ∘ (extChartAt I α).symm)
      (extChartAt I α x) := by
    rw [← mdifferentiableWithinAt_univ]
    exact hmdwa
  -- Convert MDiff → DifferentiableAt (target is a vector space, source is a vector space).
  exact hmd.differentiableAt

/-- **Auxiliary**: differentiability of `extChartAt I β ∘ (extChartAt I α).symm` at `extChartAt I α x`. -/
private lemma differentiableAt_invChartChange
    (α β : M) {x : M}
    (hα : x ∈ (chartAt H α).source)
    (hβ : x ∈ (chartAt H β).source) :
    DifferentiableAt ℝ (extChartAt I β ∘ (extChartAt I α).symm)
      (extChartAt I α x) := by
  let p : TangentBundle I M := (⟨x, (0 : E)⟩ : TangentBundle I M)
  have hpα : p.proj ∈ (chartAt H α).source := hα
  have hpβ : p.proj ∈ (chartAt H β).source := hβ
  exact differentiableAt_chartChange (I := I) (α := β) (β := α) (p := p) hpβ hpα

/-- **Auxiliary**: differentiability of `extChartAt I α ∘ (extChartAt I β).symm` at `extChartAt I β x`. -/
private lemma differentiableAt_chartChange'
    (α β : M) {x : M}
    (hα : x ∈ (chartAt H α).source)
    (hβ : x ∈ (chartAt H β).source) :
    DifferentiableAt ℝ (extChartAt I α ∘ (extChartAt I β).symm)
      (extChartAt I β x) := by
  let p : TangentBundle I M := (⟨x, (0 : E)⟩ : TangentBundle I M)
  have hpα : p.proj ∈ (chartAt H α).source := hα
  have hpβ : p.proj ∈ (chartAt H β).source := hβ
  exact differentiableAt_chartChange (I := I) (α := α) (β := β) (p := p) hpα hpβ

/-- **Auxiliary**: differentiability of `y ↦ fderiv φ_αβ y` at `extChartAt I β x`. -/
private lemma differentiableAt_fderiv_chartChange'
    (α β : M) {x : M}
    (hα : x ∈ (chartAt H α).source)
    (hβ : x ∈ (chartAt H β).source) :
    DifferentiableAt ℝ
      (fun y : E => fderiv ℝ (extChartAt I α ∘ (extChartAt I β).symm) y)
      (extChartAt I β x) := by
  let p : TangentBundle I M := (⟨x, (0 : E)⟩ : TangentBundle I M)
  have hpα : p.proj ∈ (chartAt H α).source := hα
  have hpβ : p.proj ∈ (chartAt H β).source := hβ
  exact differentiableAt_fderiv_chartChange (I := I) (α := α) (β := β) (p := p) hpα hpβ

/-- **Auxiliary chain rule**: with
`F(z) := fderiv φ_αβ (ψ z) (h z)` where `ψ := extChartAt I β ∘
(extChartAt I α).symm` and `h := chartE_section_repr β Y ∘ (extChartAt I α).symm`,
the directional derivative `fderiv F (φ_α x) (J v_β)` decomposes as
```
  fderiv F (φ_α x) (J v_β)
    = fderiv (y ↦ fderiv φ_αβ y) (φ_β x) v_β (chartE_section_repr β Y x)
      + J · fderiv h (φ_α x) (J v_β).
```
The second derivative `fderiv (y ↦ fderiv φ_αβ y) (φ_β x) v_β
(chartE_section_repr β Y x)` reduces by Schwarz symmetry to `fderiv (y ↦ fderiv
φ_αβ y (chartE_section_repr β Y x)) (φ_β x) v_β`. -/
private lemma fderiv_Y_α_pullback_chain_rule
    (α β : M) {x : M}
    (hα : x ∈ (chartAt H α).source)
    (hβ : x ∈ (chartAt H β).source)
    (Y : Π y : M, TangentSpace I y)
    (hY : MDiffAt (T% Y) x) (v_β : E) :
    fderiv ℝ
        ((chartE_section_repr (I := I) α Y) ∘ (extChartAt I α).symm)
        (extChartAt I α x)
        (fderiv ℝ (extChartAt I α ∘ (extChartAt I β).symm)
          (extChartAt I β x) v_β) =
      fderiv ℝ
        (fun y : E => fderiv ℝ (extChartAt I α ∘ (extChartAt I β).symm) y
          (chartE_section_repr (I := I) β Y x))
        (extChartAt I β x) v_β +
      fderiv ℝ (extChartAt I α ∘ (extChartAt I β).symm)
        (extChartAt I β x)
        (fderiv ℝ
          ((chartE_section_repr (I := I) β Y) ∘ (extChartAt I α).symm)
          (extChartAt I α x)
          (fderiv ℝ (extChartAt I α ∘ (extChartAt I β).symm)
            (extChartAt I β x) v_β)) := by
  classical
  -- Use the EventuallyEq form of `Y_α ∘ φ_α.symm` to rewrite the LHS in terms
  -- of a clearer composition, then apply chain rule + product rule.
  -- Define abbreviations.
  set φ : E → E := extChartAt I α ∘ (extChartAt I β).symm with hφ_def
  set ψ : E → E := extChartAt I β ∘ (extChartAt I α).symm with hψ_def
  set y_β : E := extChartAt I β x with hyβ_def
  set y_α : E := extChartAt I α x with hyα_def
  set h : E → E := (chartE_section_repr (I := I) β Y) ∘ (extChartAt I α).symm with hh_def
  set Y_α : E → E := (chartE_section_repr (I := I) α Y) ∘ (extChartAt I α).symm with hY_α_def
  -- ψ(y_α) = y_β.
  have hxα_src : x ∈ (extChartAt I α).source := by
    rw [extChartAt_source]; exact hα
  have hsymm_α : (extChartAt I α).symm y_α = x :=
    (extChartAt I α).left_inv hxα_src
  have hψ_yα : ψ y_α = y_β := by
    change extChartAt I β ((extChartAt I α).symm y_α) = y_β
    rw [hsymm_α]
  -- h(y_α) = chartE_section_repr β Y x.
  have hh_yα : h y_α = chartE_section_repr (I := I) β Y x := by
    change chartE_section_repr (I := I) β Y ((extChartAt I α).symm y_α) =
      chartE_section_repr (I := I) β Y x
    rw [hsymm_α]
  -- Define `J := fderiv φ y_β`.
  set J : E →L[ℝ] E := fderiv ℝ φ y_β with hJ_def
  -- (1) `Y_α =ᶠ[𝓝 y_α] (fun z => fderiv φ (ψ z) (h z))`.
  have hEv : Y_α =ᶠ[𝓝 y_α]
      (fun z : E => fderiv ℝ φ (ψ z) (h z)) := by
    have := eventuallyEq_chartE_repr_α_chartChange_form (I := I) α β hα hβ Y
    -- The lemma's RHS pre-composes `chartE_section_repr β Y` with `(extChartAt I α).symm`,
    -- which is exactly our `h`.
    -- LHS of `this` is exactly `Y_α`.
    exact this
  -- (2) `fderiv Y_α y_α = fderiv (fun z => fderiv φ (ψ z) (h z)) y_α` (by hEv).
  have hLHS_eq :
      fderiv ℝ Y_α y_α =
        fderiv ℝ (fun z : E => fderiv ℝ φ (ψ z) (h z)) y_α :=
    hEv.fderiv_eq
  -- We need to compute the RHS via chain rule + product rule.
  -- Setup: F(z) := fderiv φ (ψ z) (h z) = clm_apply (fderiv φ ∘ ψ) h evaluated at z.
  -- Define u(z) := fderiv φ (ψ z) : E → (E →L[ℝ] E), and v(z) := h(z).
  -- Then F = u(z) v(z) (CLM application).
  -- By `HasFDerivAt.clm_apply`:
  --   F'(z₀)(w) = u'(z₀)(w)(v(z₀)) + u(z₀)(v'(z₀)(w)).
  -- We need to identify u'(y_α) and v'(y_α).
  set u : E → (E →L[ℝ] E) := fun z : E => fderiv ℝ φ (ψ z) with hu_def
  -- u(y_α) = fderiv φ y_β = J.
  have hu_yα : u y_α = J := by
    change fderiv ℝ φ (ψ y_α) = J
    rw [hψ_yα]
  -- u' at y_α = (fderiv (fun y => fderiv φ y) y_β) ∘L (fderiv ψ y_α).
  have hψ_diff : DifferentiableAt ℝ ψ y_α := differentiableAt_invChartChange (I := I) α β hα hβ
  have hfderiv_φ_diff : DifferentiableAt ℝ (fun y : E => fderiv ℝ φ y) y_β :=
    differentiableAt_fderiv_chartChange' (I := I) α β hα hβ
  have hu_hasFD : HasFDerivAt u
      ((fderiv ℝ (fun y : E => fderiv ℝ φ y) y_β).comp (fderiv ℝ ψ y_α)) y_α := by
    -- u(z) = (fun y => fderiv φ y) (ψ z). Apply chain rule.
    -- Outer at `ψ y_α = y_β`.
    have houter_at_ψyα :
        HasFDerivAt (fun y : E => fderiv ℝ φ y)
          (fderiv ℝ (fun y : E => fderiv ℝ φ y) y_β) (ψ y_α) := by
      rw [hψ_yα]; exact hfderiv_φ_diff.hasFDerivAt
    -- `HasFDerivAt.comp` has `x` as the explicit first argument.
    exact houter_at_ψyα.comp y_α hψ_diff.hasFDerivAt
  -- v_diff at y_α.
  have hv_hasFD : HasFDerivAt h (fderiv ℝ h y_α) y_α := by
    have hh_diff := differentiableAt_chartE_repr_β_α_pullback (I := I) α β hα hβ Y hY
    exact hh_diff.hasFDerivAt
  -- (3) Apply `HasFDerivAt.clm_apply`:
  --     F = (fun z => u(z) (h(z))).
  --     F.hasFDerivAt _ = u.hasFDerivAt.clm_apply h.hasFDerivAt.
  -- The output form is `((c x).comp u' + c'.flip (u x))`.
  have hF_hasFD : HasFDerivAt (fun z : E => fderiv ℝ φ (ψ z) (h z))
      ((u y_α).comp (fderiv ℝ h y_α) +
        (((fderiv ℝ (fun y : E => fderiv ℝ φ y) y_β).comp
            (fderiv ℝ ψ y_α)).flip (h y_α))) y_α :=
    hu_hasFD.clm_apply hv_hasFD
  -- (4) `fderiv (fun z => fderiv φ (ψ z) (h z)) y_α = (the CLM in hF_hasFD)`.
  rw [hLHS_eq]
  -- Apply this fderiv to `J v_β`.
  rw [hF_hasFD.fderiv]
  -- The goal after evaluating the CLM at `J v_β`:
  --   (u y_α).comp (fderiv h y_α) (J v_β)
  --   + ((fderiv (fun y => fderiv φ y) y_β).comp (fderiv ψ y_α)).flip (h y_α) (J v_β)
  -- = fderiv (fun y => fderiv φ y (chartE_section_repr β Y x)) y_β v_β
  --   + fderiv φ y_β (fderiv h y_α (J v_β))
  rw [ContinuousLinearMap.add_apply]
  rw [ContinuousLinearMap.flip_apply]
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  -- Goal:
  --   u y_α (fderiv h y_α (J v_β))
  --   + fderiv (fun y => fderiv φ y) y_β (fderiv ψ y_α (J v_β)) (h y_α)
  -- = fderiv (fun y => fderiv φ y (chartE_section_repr β Y x)) y_β v_β
  --   + fderiv φ y_β (fderiv h y_α (J v_β))
  rw [hh_yα, hu_yα]
  -- Now `u y_α = J = fderiv φ y_β`, and `h y_α = chartE_section_repr β Y x`.
  -- LHS = J (fderiv h y_α (J v_β))
  --     + fderiv (fun y => fderiv φ y) y_β (fderiv ψ y_α (J v_β)) (chartE_section_repr β Y x)
  -- RHS = fderiv (fun y => fderiv φ y (chartE_section_repr β Y x)) y_β v_β
  --     + J (fderiv h y_α (J v_β))   (since fderiv φ y_β = J definitionally via `set`)
  -- Commute the LHS sum to match RHS ordering.
  rw [add_comm]
  -- Goal:
  -- (fderiv (fun y => fderiv φ y) y_β (fderiv ψ y_α (J v_β)) (chartE_section_repr β Y x))
  -- + J (fderiv h y_α (J v_β))
  -- = fderiv (fun y => fderiv φ y (chartE_section_repr β Y x)) y_β v_β
  -- + J (fderiv h y_α (J v_β))
  congr 1
  -- (a) Simplify fderiv ψ y_α (J v_β) = v_β.
  have hψ_fderiv_J : fderiv ℝ ψ y_α (fderiv ℝ φ y_β v_β) = v_β := by
    show fderiv ℝ (extChartAt I β ∘ (extChartAt I α).symm) y_α
      (fderiv ℝ (extChartAt I α ∘ (extChartAt I β).symm) y_β v_β) = v_β
    exact fderiv_inverse_chartChange_apply (I := I) α β hα hβ v_β
  rw [show fderiv ℝ ψ y_α (J v_β) = v_β from hψ_fderiv_J]
  -- Now goal:
  -- fderiv (fun y => fderiv φ y) y_β v_β (chartE_section_repr β Y x)
  --   = fderiv (fun y => fderiv φ y (chartE_section_repr β Y x)) y_β v_β
  -- (b) Apply the `apply` commutation: `fderiv (fun y => f y) x` is a CLM, so
  --     for any fixed `w`, `(fderiv (fun y => f y) x).apply v w` ↔
  --     `fderiv (fun y => f y w) x v` (via the chain rule with the constant `w`).
  -- This is `ContinuousLinearMap.fderiv_apply_eq` or similar. We prove it inline.
  -- Specifically, `(fun y => fderiv φ y w) = (fun y => (fderiv φ y) w) = (apply_w) ∘ (fderiv φ)`,
  -- where `apply_w : (E →L[ℝ] E) →L[ℝ] E` is the evaluation-at-w CLM. By chain rule:
  -- `fderiv ((apply_w) ∘ (fderiv φ)) y_β = apply_w ∘ (fderiv (fderiv φ) y_β)`.
  -- Applied to v_β:
  -- `(apply_w ∘ (fderiv (fderiv φ) y_β)) v_β = apply_w ((fderiv (fderiv φ) y_β) v_β)`
  --                                         = (fderiv (fderiv φ) y_β v_β) w.
  -- That's exactly what we want.
  set w : E := chartE_section_repr (I := I) β Y x with hw_def
  -- `apply_w : (E →L[ℝ] E) →L[ℝ] E`.
  set apply_w : (E →L[ℝ] E) →L[ℝ] E :=
    (ContinuousLinearMap.apply ℝ E w) with happly_w_def
  -- `(fun y => fderiv φ y w) = apply_w ∘ (fun y => fderiv φ y)`.
  have hcomp_eq : (fun y : E => fderiv ℝ φ y w) =
      apply_w ∘ (fun y : E => fderiv ℝ φ y) := by
    funext y; rfl
  -- Compute the fderiv via the chain rule.
  rw [hcomp_eq]
  -- `fderiv (apply_w ∘ (fderiv φ)) y_β = apply_w.comp (fderiv (fderiv φ) y_β)`.
  rw [(apply_w.hasFDerivAt.comp y_β
    hfderiv_φ_diff.hasFDerivAt).fderiv]
  -- Apply to v_β.
  rw [ContinuousLinearMap.comp_apply]
  -- Goal: apply_w (fderiv (fun y => fderiv φ y) y_β v_β)
  --     = fderiv (fun y => fderiv φ y) y_β v_β w
  -- By def of apply_w.
  rfl

/-- **Headline**: the classical Christoffel transformation law in chart
coordinates.

For a smooth Riemannian metric `g` on a boundaryless smooth manifold `M`, the
chart-coordinate Christoffel contraction at two basepoints `α, β : M`
satisfies, at any point `x` in both chart sources:
```
Γ_α(J v_β, J v_β)(φ_α x)
  = J (Γ_β(v_β, v_β)(φ_β x))
    − fderiv (y ↦ fderiv φ_αβ y v_β) (φ_β x) v_β,
```
where `J := fderiv φ_αβ (φ_β x)` and `φ_αβ := φ_α ∘ φ_β.symm`. -/
theorem chartChristoffelContraction_chart_transform
    (g : SmoothRiemannianMetric I M) (α β : M) {x : M}
    (hα : x ∈ (chartAt H α).source) (hβ : x ∈ (chartAt H β).source)
    (v_β : E) :
    let J := fderiv ℝ (extChartAt I α ∘ (extChartAt I β).symm)
              (extChartAt I β x)
    chartChristoffelContraction (I := I) g α (J v_β) (J v_β)
        (extChartAt I α x) =
      J (chartChristoffelContraction (I := I) g β v_β v_β
            (extChartAt I β x))
        - fderiv ℝ
            (fun y => fderiv ℝ (extChartAt I α ∘ (extChartAt I β).symm) y v_β)
            (extChartAt I β x) v_β := by
  classical
  -- Introduce abbreviations.
  set φ_αβ : E → E := extChartAt I α ∘ (extChartAt I β).symm with hφ_def
  set y_β : E := extChartAt I β x with hyβ_def
  set y_α : E := extChartAt I α x with hyα_def
  set J : E →L[ℝ] E := fderiv ℝ φ_αβ y_β with hJ_def
  -- (1) Pick a smooth global section `Y` with `Y x = trivFromE β x v_β`.
  set Y : Π y : M, TangentSpace I y :=
    (globalY (I := I) β x v_β : Π y : M, TangentSpace I y) with hY_def
  have hY_x : Y x = trivFromE (I := I) β x v_β :=
    globalY_apply (I := I) β x v_β
  have hY_mdiff : ∀ y : M, MDiffAt (T% Y) y := fun y =>
    globalY_mdiffAt (I := I) β x v_β y
  -- (2) Both `x ∈ chartLeviCivitaGoodSet α` and `x ∈ chartLeviCivitaGoodSet β`.
  have hxα_src : x ∈ (extChartAt I α).source := by
    rw [extChartAt_source]; exact hα
  have hxβ_src : x ∈ (extChartAt I β).source := by
    rw [extChartAt_source]; exact hβ
  have hxα_base : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact hα
  have hxβ_base : x ∈ (trivializationAt E (TangentSpace I) β).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact hβ
  -- `extChartAt I α x ∈ interior ((extChartAt I α).target)` (boundarylessness).
  have hxα_int :
      extChartAt I α x ∈ interior ((extChartAt I α).target : Set E) := by
    have hβ_target_open : IsOpen (extChartAt I α).target := isOpen_extChartAt_target α
    have hxα_target : extChartAt I α x ∈ (extChartAt I α).target :=
      (extChartAt I α).map_source hxα_src
    rw [hβ_target_open.interior_eq]; exact hxα_target
  have hxβ_int :
      extChartAt I β x ∈ interior ((extChartAt I β).target : Set E) := by
    have hβ_target_open : IsOpen (extChartAt I β).target := isOpen_extChartAt_target β
    have hxβ_target : extChartAt I β x ∈ (extChartAt I β).target :=
      (extChartAt I β).map_source hxβ_src
    rw [hβ_target_open.interior_eq]; exact hxβ_target
  have hxα_good : x ∈ chartLeviCivitaGoodSet (I := I) α :=
    mem_chartLeviCivitaGoodSet_iff.mpr ⟨hxα_src, hxα_base, hxα_int⟩
  have hxβ_good : x ∈ chartLeviCivitaGoodSet (I := I) β :=
    mem_chartLeviCivitaGoodSet_iff.mpr ⟨hxβ_src, hxβ_base, hxβ_int⟩
  -- (3) Apply chart-overlap consistency.
  have hoverlap :
      chartLeviCivita (I := I) g α Y x (Y x) =
        chartLeviCivita (I := I) g β Y x (Y x) :=
    chartLeviCivita_chart_overlap (I := I) g α β hxα_good hxβ_good
      (hY_mdiff x) (Y x)
  -- (4) Apply `trivToE α x` to both sides.
  have htriv_eq :
      trivToE (I := I) α x (chartLeviCivita (I := I) g α Y x (Y x)) =
        trivToE (I := I) α x (chartLeviCivita (I := I) g β Y x (Y x)) :=
    congrArg _ hoverlap
  -- (5) Expand LHS via `chartLeviCivita_apply`.
  rw [chartLeviCivita_apply (I := I) g α Y hxα_good (Y x)] at htriv_eq
  rw [chartLeviCivita_apply (I := I) g β Y hxβ_good (Y x)] at htriv_eq
  -- After expansion, both sides are `trivToE α x (trivFromE _ x (inner _))`.
  -- LHS: `trivToE α x (trivFromE α x (inner_α))` = `inner_α` (round trip).
  -- RHS: `trivToE α x (trivFromE β x (inner_β))` = `J · inner_β` (chart change).
  -- For LHS: `inner_α := fderiv (Y^E_α ∘ φ_α.symm) (φ_α x) (trivToE α x (Y x)) +
  --              christoffelCorrection g α x (Y^E_α x) (Y x)`.
  -- Round-trip on LHS:
  have hLHS_round :
      trivToE (I := I) α x
          (trivFromE (I := I) α x
            (fderiv ℝ
                (chartE_section_repr (I := I) α Y ∘ (extChartAt I α).symm)
                (extChartAt I α x) (trivToE (I := I) α x (Y x)) +
              christoffelCorrection (I := I) g α x
                (chartE_section_repr (I := I) α Y x) (Y x))) =
        fderiv ℝ
            (chartE_section_repr (I := I) α Y ∘ (extChartAt I α).symm)
            (extChartAt I α x) (trivToE (I := I) α x (Y x)) +
          christoffelCorrection (I := I) g α x
            (chartE_section_repr (I := I) α Y x) (Y x) :=
    trivToE_trivFromE (I := I) α hxα_base _
  rw [hLHS_round] at htriv_eq
  -- For RHS: linearity of `trivToE α x` over `trivFromE β x`.
  -- `trivToE α x (trivFromE β x (A + B)) = trivToE α x (trivFromE β x A) +
  --   trivToE α x (trivFromE β x B)`.
  -- Use `map_add` twice.
  rw [map_add (trivFromE (I := I) β x)] at htriv_eq
  rw [map_add (trivToE (I := I) α x)] at htriv_eq
  -- Now RHS is:
  --   trivToE α x (trivFromE β x (fderiv (Y^E_β ∘ φ_β.symm) (φ_β x) (trivToE β x (Y x)))) +
  --   trivToE α x (trivFromE β x (christoffelCorrection g β x (Y^E_β x) (Y x))).
  -- Apply `trivToE_trivFromE_eq_fderiv_chartChange` to each.
  rw [trivToE_trivFromE_eq_fderiv_chartChange (I := I) α β hα hβ
        (fderiv ℝ (chartE_section_repr (I := I) β Y ∘ (extChartAt I β).symm)
          (extChartAt I β x) (trivToE (I := I) β x (Y x))),
      trivToE_trivFromE_eq_fderiv_chartChange (I := I) α β hα hβ
        (christoffelCorrection (I := I) g β x
          (chartE_section_repr (I := I) β Y x) (Y x))] at htriv_eq
  -- (6) Compute `trivToE β x (Y x)`.
  -- `Y x = trivFromE β x v_β` ⇒ `trivToE β x (Y x) = v_β` (round trip on β-baseSet).
  have htβx_Y : trivToE (I := I) β x (Y x) = v_β := by
    rw [hY_x]
    exact trivToE_trivFromE (I := I) β hxβ_base v_β
  -- (7) Compute `chartE_section_repr β Y x = trivToE β x (Y x) = v_β`.
  have hYE_β_x : chartE_section_repr (I := I) β Y x = v_β := by
    rw [chartE_section_repr_eq_trivToE]; exact htβx_Y
  -- (8) Compute `trivToE α x (Y x)`.
  -- This is `trivToE α x (trivFromE β x v_β) = J v_β`.
  have htαx_Y : trivToE (I := I) α x (Y x) = J v_β := by
    rw [hY_x]
    exact trivToE_trivFromE_eq_fderiv_chartChange (I := I) α β hα hβ v_β
  -- (9) Compute `chartE_section_repr α Y x = J v_β`.
  have hYE_α_x : chartE_section_repr (I := I) α Y x = J v_β := by
    rw [chartE_section_repr_eq_trivToE]; exact htαx_Y
  -- Substitute these into `htriv_eq`.
  rw [htαx_Y, hYE_α_x, hYE_β_x, htβx_Y] at htriv_eq
  -- (10) Convert `christoffelCorrection` to `chartChristoffelContraction`.
  -- Note: `christoffelCorrection g α x (J v_β) (Y x)` with `v := Y x` gives
  --   `chartChristoffelContraction g α (trivToE α x (Y x)) (J v_β) (φ_α x)`
  -- = `chartChristoffelContraction g α (J v_β) (J v_β) (φ_α x)` (since trivToE α x (Y x) = J v_β).
  rw [christoffelCorrection_eq_chartChristoffelContraction (I := I) g α x (J v_β) (Y x)] at htriv_eq
  -- Same for β.
  rw [christoffelCorrection_eq_chartChristoffelContraction (I := I) g β x v_β (Y x)] at htriv_eq
  -- The chartChristoffelContraction calls now have `trivToE α x (Y x) = J v_β` and `trivToE β x (Y x) = v_β`.
  rw [htαx_Y, htβx_Y] at htriv_eq
  -- (11) Apply chain rule on the LHS to expand `fderiv (Y_α ∘ φ_α.symm) (φ_α x) (J v_β)`.
  have hchain :=
    fderiv_Y_α_pullback_chain_rule (I := I) α β hα hβ Y (hY_mdiff x) v_β
  -- `hchain` rewrites the LHS derivative term; it reintroduces `chartE_section_repr β Y x`.
  rw [hchain] at htriv_eq
  -- Substitute back the literal value `chartE_section_repr β Y x = v_β`.
  rw [hYE_β_x] at htriv_eq
  -- Now htriv_eq reads:
  -- (fderiv (y ↦ fderiv φ_αβ y v_β) y_β v_β
  --   + J (fderiv (Y_β ∘ φ_α.symm) y_α (J v_β))) +
  -- chartChristoffelContraction g α (J v_β) (J v_β) (φ_α x) =
  -- J (fderiv (Y_β ∘ φ_β.symm) y_β v_β) +
  -- J (chartChristoffelContraction g β v_β v_β (φ_β x))
  -- But our LHS had `fderiv (y ↦ fderiv φ_αβ y) y_β v_β (chartE_section_repr β Y x)`.
  -- We rewrote with hYE_β_x to `fderiv (...) v_β` ... wait actually `v_β` appears inside the apply.
  -- Let me re-examine the hchain output carefully.
  -- hchain's RHS: `fderiv (fun y => fderiv φ_αβ y (chartE_section_repr β Y x)) y_β v_β +
  --   J (fderiv (Y_β ∘ φ_α.symm) y_α (J v_β))`.
  -- After hYE_β_x rewrite, this becomes:
  -- `fderiv (fun y => fderiv φ_αβ y v_β) y_β v_β +
  --   J (fderiv (Y_β ∘ φ_α.symm) y_α (J v_β))`.
  -- (12) Reduce `fderiv (Y_β ∘ φ_α.symm) y_α (J v_β) = fderiv (Y_β ∘ φ_β.symm) y_β v_β`.
  -- This is the inverse-chart-change reduction on the β-section pullback.
  have hβ_pullback_eq :
      fderiv ℝ ((chartE_section_repr (I := I) β Y) ∘ (extChartAt I α).symm)
          (extChartAt I α x) (J v_β) =
        fderiv ℝ ((chartE_section_repr (I := I) β Y) ∘ (extChartAt I β).symm)
          (extChartAt I β x) v_β := by
    -- `Y_β ∘ φ_α.symm = (Y_β ∘ φ_β.symm) ∘ (φ_β ∘ φ_α.symm)`.
    -- Apply chain rule: fderiv (Y_β ∘ φ_α.symm) y_α (J v_β) =
    --   fderiv (Y_β ∘ φ_β.symm) (φ_β y_α-side-image) (fderiv (φ_β ∘ φ_α.symm) y_α (J v_β)).
    -- (φ_β ∘ φ_α.symm) y_α = y_β. And fderiv (φ_β ∘ φ_α.symm) y_α (J v_β) = v_β.
    set ψ : E → E := extChartAt I β ∘ (extChartAt I α).symm with hψ_def
    set h_β : E → E := (chartE_section_repr (I := I) β Y) ∘ (extChartAt I β).symm with hh_β_def
    have hxα_src' : x ∈ (extChartAt I α).source := hxα_src
    have hsymm_α' : (extChartAt I α).symm y_α = x :=
      (extChartAt I α).left_inv hxα_src'
    have hψ_yα : ψ y_α = y_β := by
      change extChartAt I β ((extChartAt I α).symm y_α) = y_β
      rw [hsymm_α']
    -- We have eventually equality (Y_β ∘ φ_α.symm) =ᶠ[𝓝 y_α] (h_β ∘ ψ).
    -- On the open set V₁ := (extChartAt I α).target ∩
    --   (extChartAt I α).symm ⁻¹' (chartAt H β).source,
    -- both functions agree.
    have hα_target_open : IsOpen (extChartAt I α).target := isOpen_extChartAt_target α
    have hβ_src_open : IsOpen (chartAt H β).source := (chartAt H β).open_source
    have hSymmCts : ContinuousOn (extChartAt I α).symm (extChartAt I α).target :=
      continuousOn_extChartAt_symm α
    set V₁ : Set E :=
      (extChartAt I α).target ∩
        (extChartAt I α).symm ⁻¹' (chartAt H β).source with hV₁_def
    have hV₁_open : IsOpen V₁ :=
      hSymmCts.isOpen_inter_preimage hα_target_open hβ_src_open
    have hyα_inV₁ : y_α ∈ V₁ := by
      refine ⟨(extChartAt I α).map_source hxα_src', ?_⟩
      rw [mem_preimage, hsymm_α']
      exact hβ
    have hEv₁ :
        ((chartE_section_repr (I := I) β Y) ∘ (extChartAt I α).symm) =ᶠ[𝓝 y_α]
        (h_β ∘ ψ) := by
      refine Filter.eventuallyEq_of_mem (s := V₁) (hV₁_open.mem_nhds hyα_inV₁) ?_
      intro z hz
      rcases hz with ⟨hz_t, hz_pre⟩
      rw [mem_preimage] at hz_pre
      show chartE_section_repr (I := I) β Y ((extChartAt I α).symm z) =
        chartE_section_repr (I := I) β Y ((extChartAt I β).symm
          (extChartAt I β ((extChartAt I α).symm z)))
      have hzα_src : (extChartAt I α).symm z ∈ (extChartAt I α).source :=
        (extChartAt I α).map_target hz_t
      have hzβ_src : (extChartAt I α).symm z ∈ (extChartAt I β).source := by
        rw [extChartAt_source]; exact hz_pre
      rw [(extChartAt I β).left_inv hzβ_src]
    -- Apply `Filter.EventuallyEq.fderiv_eq`.
    have hEv₁_fderiv :
        fderiv ℝ ((chartE_section_repr (I := I) β Y) ∘ (extChartAt I α).symm) y_α =
          fderiv ℝ (h_β ∘ ψ) y_α :=
      hEv₁.fderiv_eq
    rw [hEv₁_fderiv]
    -- Now apply chain rule: fderiv (h_β ∘ ψ) y_α (J v_β) =
    --   fderiv h_β (ψ y_α) (fderiv ψ y_α (J v_β))
    -- = fderiv h_β y_β v_β.
    -- `h_β = chartE_section_repr β Y ∘ (extChartAt I β).symm` differentiable at `y_β`.
    have hh_β_diff : DifferentiableAt ℝ h_β y_β :=
      differentiableAt_chartE_repr_β_α_pullback (I := I) β β hβ hβ Y (hY_mdiff x)
    have hψ_diff : DifferentiableAt ℝ ψ y_α :=
      differentiableAt_invChartChange (I := I) α β hα hβ
    -- `fderiv (h_β ∘ ψ) y_α = fderiv h_β (ψ y_α) ∘L fderiv ψ y_α`.
    have hh_β_at_ψyα : HasFDerivAt h_β (fderiv ℝ h_β y_β) (ψ y_α) := by
      rw [hψ_yα]; exact hh_β_diff.hasFDerivAt
    have hcomp_fd : HasFDerivAt (h_β ∘ ψ)
        ((fderiv ℝ h_β y_β).comp (fderiv ℝ ψ y_α)) y_α :=
      hh_β_at_ψyα.comp y_α hψ_diff.hasFDerivAt
    rw [hcomp_fd.fderiv]
    -- Apply to J v_β.
    rw [ContinuousLinearMap.comp_apply]
    -- `fderiv ψ y_α (J v_β) = v_β` by `fderiv_inverse_chartChange_apply`.
    have hψ_fd_J : fderiv ℝ ψ y_α (J v_β) = v_β := by
      show fderiv ℝ (extChartAt I β ∘ (extChartAt I α).symm) y_α
        (fderiv ℝ (extChartAt I α ∘ (extChartAt I β).symm) y_β v_β) = v_β
      exact fderiv_inverse_chartChange_apply (I := I) α β hα hβ v_β
    rw [hψ_fd_J]
  rw [hβ_pullback_eq] at htriv_eq
  -- (13) Now htriv_eq reads:
  -- (fderiv (y ↦ fderiv φ_αβ y v_β) y_β v_β +
  --  J (fderiv (Y_β ∘ φ_β.symm) y_β v_β))
  -- + chartChristoffelContraction g α (J v_β) (J v_β) (φ_α x)
  -- = J (fderiv (Y_β ∘ φ_β.symm) y_β v_β)
  -- + J (chartChristoffelContraction g β v_β v_β (φ_β x))
  -- Subtract `J (fderiv (Y_β ∘ φ_β.symm) y_β v_β)` from both sides.
  -- This is straightforward algebra: rearrange.
  -- Goal:
  --   chartChristoffelContraction g α (J v_β) (J v_β) (φ_α x)
  --   = J (chartChristoffelContraction g β v_β v_β (φ_β x))
  --     - fderiv (y ↦ fderiv φ_αβ y v_β) y_β v_β.
  -- From htriv_eq, after subtracting `J · fderiv (Y_β ∘ φ_β.symm)`:
  -- fderiv (y ↦ fderiv φ_αβ y v_β) y_β v_β
  -- + chartChristoffelContraction g α (J v_β) (J v_β) (φ_α x)
  -- = J (chartChristoffelContraction g β v_β v_β (φ_β x)).
  -- Equivalently: chartChristoffelContraction g α (J v_β) (J v_β) (φ_α x)
  --             = J (...) - fderiv (...) v_β.
  -- Linear algebra: take the equation and isolate the goal term.
  -- Let A := fderiv (y ↦ fderiv φ_αβ y v_β) y_β v_β
  --     B := J (fderiv (Y_β ∘ φ_β.symm) y_β v_β)
  --     C := chartChristoffelContraction g α (J v_β) (J v_β) (φ_α x)
  --     D := J (chartChristoffelContraction g β v_β v_β (φ_β x))
  -- htriv_eq: (A + B) + C = B + D
  -- Goal: C = D - A.
  -- Subtract B from both sides: A + C = D. So C = D - A.
  -- Use AddCommGroup algebra to rearrange.
  -- The goal has form `C = D - A`; the hypothesis `htriv_eq` has form
  -- `(A + B) + C = B + D` (modulo definitional unfolding of `φ_αβ`, `y_β`, etc.).
  -- We solve by an `abel`-style argument that doesn't depend on the variable names.
  have hgoal : ∀ A B C D : E, A + B + C = B + D → C = D - A := by
    intro A B C D h
    -- A + B + C = B + D ⇒ A + C = D ⇒ C = D - A.
    have h1 : A + C = D := by
      have h3 : A + B + C = B + (A + C) := by abel
      exact add_left_cancel (h3.symm.trans h)
    have h2 : C = -A + D := by
      have : -A + (A + C) = -A + D := by rw [h1]
      simpa [← add_assoc] using this
    rw [h2]; abel
  exact hgoal _ _ _ _ htriv_eq

end Headline

end Geodesic
end Riemannian
end Geometry
end DifferentialGeometry

end
