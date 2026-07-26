import DifferentialGeometry.Geometry.Connection.Realization.SmoothSections
import DifferentialGeometry.Bundle.PartialMfderiv.FixedBase
import Mathlib.Geometry.Manifold.BumpFunction

/-!
# Local (`ContMDiffOn`/`ContMDiffAt`) smoothness of directional derivatives

`SmoothSections.lean` proves the *global* facts: for `h ∈ C^∞(M)` the exterior
derivative `extDerivFun h` is a smooth cotangent section, and a smooth cotangent
section paired with a smooth vector field is a smooth scalar.  Component towers
(`iterCovComp`/`iterCovCompU`) live on a local-frame domain `u`, so they need the
*local* versions:

* `contMDiffOn_dual_apply` — a global smooth dual section paired with a vector
  field that is only `ContMDiffOn u` is `ContMDiffOn u`.
* `contMDiffAt_extDerivFun_apply` — for `f` smooth *on an open `u`* and a vector
  field `V` smooth on `u`, the directional derivative `y ↦ (df)_y(V y)` is smooth
  at every point of `u`.  Proved by a `SmoothBumpFunction` localization of `f`
  (the bump-multiplied function is globally smooth and agrees with `f` near the
  point; `extDerivFun` only depends on the germ).

This is the analytic input for the differentiability of covariant-derivative
component towers (each tower level is `extDerivFun` of the previous level along a
frame field, minus Christoffel corrections).
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology
open Bundle

section SmoothSectionsLocal

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- A global smooth dual section paired with a vector field that is `ContMDiffOn u`
is `ContMDiffOn u`.  Local version of `contMDiff_dual_apply_section`. -/
theorem contMDiffOn_dual_apply
    (α : Cₛ^∞⟮I; E →L[ℝ] ℝ, (Bundle.dual ℝ (TangentSpace I : M → Type _))⟯)
    {V : (y : M) → TangentSpace I y} {u : Set M}
    (hV : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (V y)) u) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => α y (V y)) u := by
  have hα : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ)
        (E := fun x : M => (TangentSpace I x →L[ℝ] (Bundle.Trivial M ℝ) x))
        y (α y)) u := α.contMDiff.contMDiffOn
  have hap : ContMDiffOn I (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun y => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) y (α y (V y))) u :=
    ContMDiffOn.clm_bundle_apply (b := id) hα hV
  intro y hy
  exact (contMDiffWithinAt_section (F := ℝ) (E := Bundle.Trivial M ℝ)).mp (hap y hy)

/-- `extDerivFun` respects eventual equality of the differentiated function
(`mfderiv` only depends on the germ). -/
private theorem extDerivFun_congr_nhds
    {f g : M → ℝ} {x : M} (V : TangentSpace I x) (h : f =ᶠ[𝓝 x] g) :
    extDerivFun (I := I) f x V = extDerivFun (I := I) g x V := by
  rw [DifferentialGeometry.extDerivFun_real_eq_mfderiv I f x V,
    DifferentialGeometry.extDerivFun_real_eq_mfderiv I g x V,
    Filter.EventuallyEq.mfderiv_eq (I := I) (I' := 𝓘(ℝ, ℝ)) h]
  rfl

/-- **Local smoothness of the directional derivative.**  For `f` smooth on an open
`u` and a vector field `V` smooth on `u`, the scalar `y ↦ (df)_y(V y)` is
`ContMDiffAt` every `x ∈ u`.  Localizes `f` by a smooth bump supported in `u`
(`f̃ = χ·f` is globally smooth and agrees with `f` near `x`), applies the global
`contMDiff_extDerivFun_section`, pairs by `contMDiffOn_dual_apply`, and transfers
back along the germ equality. -/
theorem contMDiffAt_extDerivFun_apply
    {u : Set M} (hu : IsOpen u) {x : M} (hx : x ∈ u)
    {f : M → ℝ} (hf : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f u)
    {V : (y : M) → TangentSpace I y}
    (hV : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (V y)) u) :
    ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun y => extDerivFun (I := I) f y (V y)) x := by
  classical
  -- A bump at `x` with support inside `u`.
  obtain ⟨b, -, hb_supp⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := I) x).mem_iff.mp (hu.mem_nhds hx)
  -- The bump-localized function is globally smooth.
  set ftil : M → ℝ := fun y => b y * f y with hftil_def
  have hftil : ContMDiff I 𝓘(ℝ, ℝ) ∞ ftil := by
    apply contMDiff_of_locally_contMDiffOn
    intro z
    by_cases hz : z ∈ u
    · exact ⟨u, hu, hz, (b.contMDiff.contMDiffOn).mul hf⟩
    · refine ⟨(tsupport (b : M → ℝ))ᶜ, (isClosed_tsupport _).isOpen_compl,
        fun hmem => hz (hb_supp hmem), ?_⟩
      refine (contMDiffOn_const (c := (0 : ℝ))).congr ?_
      intro y hy
      have hb0 : b y = 0 := by
        by_contra hne
        exact hy (subset_tsupport _ hne)
      simp [hftil_def, hb0]
  -- The exterior derivative of the localization is a global smooth dual section.
  let dα : Cₛ^∞⟮I; E →L[ℝ] ℝ, (Bundle.dual ℝ (TangentSpace I : M → Type _))⟯ :=
    ⟨fun y => extDerivFun (I := I) ftil y,
      contMDiff_extDerivFun_section (I := I) (M := M) ⟨ftil, hftil⟩⟩
  have hpair : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun y => extDerivFun (I := I) ftil y (V y)) u :=
    contMDiffOn_dual_apply (I := I) dα hV
  have hAt : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun y => extDerivFun (I := I) ftil y (V y)) x :=
    hpair.contMDiffAt (hu.mem_nhds hx)
  -- Transfer along the germ equality `f = ftil` near `x` (where the bump is 1).
  refine hAt.congr_of_eventuallyEq ?_
  obtain ⟨w, hw_one, hw_open, hxw⟩ := eventually_nhds_iff.mp b.eventuallyEq_one
  refine eventually_nhds_iff.mpr ⟨w, ?_, hw_open, hxw⟩
  intro y hyw
  refine extDerivFun_congr_nhds (I := I) (V y) ?_
  refine eventually_nhds_iff.mpr ⟨w, ?_, hw_open, hyw⟩
  intro z hzw
  simp [hftil_def, hw_one z hzw]

end SmoothSectionsLocal
