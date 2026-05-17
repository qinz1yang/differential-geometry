import DifferentialGeometry.Geometry.Riemannian.Geodesic.Velocity
import Mathlib.Geometry.Manifold.IntegralCurve.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable

set_option linter.unusedSectionVars false

/-!
# Chart-coordinate rosetta stone for the velocity

This file is the chart-coordinate companion of
`DifferentialGeometry/Geometry/Riemannian/Geodesic/Velocity.lean`. It
ships the chart-form of the integral-curve / velocity bridge:

* `fst_mfderiv_extChartAt_tangent_at_zero_section`: the differential of
  the tangent-bundle extended chart at the zero section `⟨α, 0⟩`,
  followed by `Prod.fst`, equals the composition of the differential of
  the base extended chart at `α` with the differential of the bundle
  projection. This is the chart-coordinate translation of "the first
  factor of the tangent space of the tangent bundle is the tangent
  space of the base".

* `hasDerivAt_extChartAt_comp_of_isMIntegralCurveAt`: along an integral
  curve `f : ℝ → TM` of the chart-fixed geodesic vector field with
  base path `γ : ℝ → M`, the chart-base curve `s ↦ extChartAt I α (γ s)`
  has derivative `chartFiberCoord α (f t)` at `t`, i.e., the
  α-trivialised fibre coordinate of `f t`.

* `velocity_eq_snd_of_isMIntegralCurveAt`: the intrinsic identification
  of the velocity with the fibre part of the lift. Whenever the base
  path lies in the chart at the basepoint, the intrinsic
  `velocity γ t : TangentSpace I (γ t)` equals `(f t).2`, transported
  along `(f t).proj = γ t`.

The chart-coordinate identifications use only Mathlib's
`TangentBundle.continuousLinearMapAt_trivializationAt`, which converts
the manifold derivative of an extended chart into the trivialisation's
fibre map. Off the chart at the basepoint the third headline
genuinely fails: the geodesic vector field vanishes off the chart, so
the integral-curve identity forces the velocity to vanish while the
intrinsic fibre `(f t).2` need not.
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

open DifferentialGeometry.Integral.Measure

/-! ## Function-level identity for the tangent-bundle extended chart -/

/-- On the source of the tangent-bundle chart at `⟨α, 0⟩`, the
extended chart at `⟨α, 0⟩` agrees, in its first coordinate, with the
composition of the base extended chart at `α` with the bundle
projection.

This is a pointwise function-level identity, derived directly from
`FiberBundle.extChartAt` and `TangentBundle.trivializationAt_fst`. The
identity holds for every `q` since both sides reduce to applying the
base extended chart to `q.proj`; the chart-source hypothesis is not
needed at this level. -/
lemma fst_extChartAt_tangent_zeroSection_apply (α : M) (q : TangentBundle I M) :
    (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M) q).1 =
      extChartAt I α q.proj := by
  classical
  -- Decompose the bundle-level extended chart via `FiberBundle.extChartAt`.
  have hfb : extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M) q =
      ((extChartAt I α).prod (PartialEquiv.refl E))
        ((trivializationAt E (TangentSpace I) α).toPartialEquiv q) := by
    have := FiberBundle.extChartAt (IB := I) (F := E) (E := TangentSpace I)
      (x := (⟨α, (0 : E)⟩ : TangentBundle I M))
    -- `⟨α, 0⟩.proj = α`.
    change extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M) q = _
    rw [this]
    rfl
  rw [hfb]
  -- First coordinate of the prod-extension is `extChartAt I α` applied to the
  -- first coordinate of the trivialisation, which is `q.proj`.
  change extChartAt I α
      ((trivializationAt E (TangentSpace I) α).toPartialEquiv q).1 = _
  have hfstTriv : ((trivializationAt E (TangentSpace I) α).toPartialEquiv q).1 =
      q.proj := TangentBundle.trivializationAt_fst (I := I) α q
  rw [hfstTriv]

/-- Pointwise function-level identity restated as `EventuallyEq` on
`𝓝 p`. Since the underlying equality is unconditional, the
neighbourhood predicate is `Filter.univ_mem`. -/
lemma eventuallyEq_fst_extChartAt_tangent_zeroSection (α : M)
    (p : TangentBundle I M) :
    (fun q : TangentBundle I M =>
        (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M) q).1) =ᶠ[𝓝 p]
      (fun q : TangentBundle I M => extChartAt I α q.proj) :=
  Filter.Eventually.of_forall
    (fun q => fst_extChartAt_tangent_zeroSection_apply (I := I) α q)

/-! ## Mfderiv chain rule for the tangent-bundle extended chart -/

/-- **Chart-coordinate rosetta stone, mfderiv form.** The differential
of the tangent-bundle extended chart at `⟨α, 0⟩`, followed by the
first-component projection, factors as `mfderiv (extChartAt I α) p.proj`
composed with `mfderiv proj p`. Concretely, applied to a tangent
vector `X ∈ T_p(TM)`,

```
((mfderiv (extChartAt I.tangent ⟨α, 0⟩) p) X).1 =
  (mfderiv (extChartAt I α) p.proj) (mfderiv proj p X).
```
-/
theorem fst_mfderiv_extChartAt_tangent_at_zero_section
    {α : M} {p : TangentBundle I M}
    (hp : p.proj ∈ (chartAt H α).source)
    (X : TangentSpace I.tangent p) :
    ((mfderiv I.tangent 𝓘(ℝ, E × E)
       (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)) p) X).1 =
    (mfderiv I 𝓘(ℝ, E) (extChartAt I α) p.proj)
      ((mfderiv I.tangent I
          (Bundle.TotalSpace.proj : TangentBundle I M → M) p) X) := by
  classical
  -- (1) The two functions `Prod.fst ∘ extChartAt I.tangent ⟨α,0⟩` and
  -- `extChartAt I α ∘ proj` agree in a neighbourhood of `p`.
  have hev : (fun q : TangentBundle I M =>
        (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M) q).1) =ᶠ[𝓝 p]
      (fun q : TangentBundle I M => extChartAt I α q.proj) :=
    eventuallyEq_fst_extChartAt_tangent_zeroSection (I := I) α p
  -- (2) Both sides are mfderiv-able at `p`. We compute mfderiv of the LHS using
  -- the eventually-equal RHS.
  -- LHS, via Prod.fst CLM:
  have hLHS_eq :
      mfderiv I.tangent 𝓘(ℝ, E)
        (fun q : TangentBundle I M =>
          (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M) q).1) p =
      (ContinuousLinearMap.fst ℝ E E) ∘L
        (mfderiv I.tangent 𝓘(ℝ, E × E)
          (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)) p) := by
    -- mfderiv of `(Prod.fst ∘ ·)` factors via composition with a CLM.
    -- Use `mfderiv_comp_of_eq` with `g = Prod.fst : E × E → E` (a CLM, hence
    -- mdifferentiable everywhere in normed-space target).
    -- Smoothness of the first-projection CLM (manifold form).
    have hfst_contMDiff : ContMDiff 𝓘(ℝ, E × E) 𝓘(ℝ, E) ∞
        (fun y : E × E => y.1) := (ContinuousLinearMap.fst ℝ E E).contMDiff
    have hfst : MDifferentiableAt 𝓘(ℝ, E × E) 𝓘(ℝ, E)
        (fun y : E × E => y.1)
        (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M) p) :=
      hfst_contMDiff.mdifferentiableAt (by decide)
    have hchart : MDifferentiableAt I.tangent 𝓘(ℝ, E × E)
        (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)) p := by
      -- Source of the chart at `⟨α,0⟩` is `proj ⁻¹' (chartAt H α).source`.
      have hp' : p ∈ (chartAt (ModelProd H E)
          (⟨α, (0 : E)⟩ : TangentBundle I M)).source := by
        rw [TangentBundle.mem_chart_source_iff (I := I) (M := M) p
          (⟨α, (0 : E)⟩ : TangentBundle I M)]
        exact hp
      exact mdifferentiableAt_extChartAt (I := I.tangent) hp'
    have hcomp_mf := mfderiv_comp (I := I.tangent) (I' := 𝓘(ℝ, E × E)) (I'' := 𝓘(ℝ, E))
      (f := extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M))
      (g := fun y : E × E => y.1) (x := p) hfst hchart
    -- The mfderiv of a CLM in a normed-space target is the CLM itself.
    have hfst_mfderiv :
        mfderiv 𝓘(ℝ, E × E) 𝓘(ℝ, E) (fun y : E × E => y.1)
          (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M) p) =
        ContinuousLinearMap.fst ℝ E E := by
      -- Bridge via `HasFDerivAt` of the CLM.
      have h : HasFDerivAt (fun y : E × E => y.1)
          (ContinuousLinearMap.fst ℝ E E)
          (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M) p) :=
        (ContinuousLinearMap.fst ℝ E E).hasFDerivAt
      exact h.hasMFDerivAt.mfderiv
    -- `hcomp_mf` says: mfderiv (Prod.fst ∘ chart) = (mfderiv_fst) ∘L (mfderiv_chart).
    -- We need: mfderiv (fun q => (chart q).1) = (Prod.fst CLM) ∘L (mfderiv_chart).
    -- The two `fun` expressions are definitionally equal.
    change mfderiv I.tangent 𝓘(ℝ, E)
      ((fun y : E × E => y.1) ∘
        (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M))) p = _
    rw [hcomp_mf, hfst_mfderiv]
    rfl
  -- RHS, via the chain rule for `extChartAt I α ∘ proj`:
  have hRHS_eq :
      mfderiv I.tangent 𝓘(ℝ, E)
        (fun q : TangentBundle I M => extChartAt I α q.proj) p =
      (mfderiv I 𝓘(ℝ, E) (extChartAt I α) p.proj) ∘L
        (mfderiv I.tangent I
          (Bundle.TotalSpace.proj : TangentBundle I M → M) p) := by
    have hproj_mdiff : MDifferentiableAt I.tangent I
        (Bundle.TotalSpace.proj : TangentBundle I M → M) p :=
      Bundle.mdifferentiableAt_proj _
    have hchart_mdiff : MDifferentiableAt I 𝓘(ℝ, E)
        (extChartAt I α) ((Bundle.TotalSpace.proj : TangentBundle I M → M) p) :=
      mdifferentiableAt_extChartAt (I := I) hp
    have := mfderiv_comp (I := I.tangent) (I' := I) (I'' := 𝓘(ℝ, E))
      (f := (Bundle.TotalSpace.proj : TangentBundle I M → M))
      (g := extChartAt I α) (x := p) hchart_mdiff hproj_mdiff
    -- The composition is `fun q => extChartAt I α q.proj`.
    exact this
  -- (3) Use `EventuallyEq.mfderiv_eq` to equate the two mfderivs at `p`.
  have hmfd : mfderiv I.tangent 𝓘(ℝ, E)
      (fun q : TangentBundle I M =>
        (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M) q).1) p =
      mfderiv I.tangent 𝓘(ℝ, E)
        (fun q : TangentBundle I M => extChartAt I α q.proj) p :=
    Filter.EventuallyEq.mfderiv_eq hev
  rw [hLHS_eq, hRHS_eq] at hmfd
  -- Apply both sides to `X`.
  have happ := congrArg (fun L : TangentSpace I.tangent p →L[ℝ] E => L X) hmfd
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.coe_fst'] at happ
  exact happ

/-! ## Second-component identity for the tangent-bundle extended chart -/

/-- On the tangent-bundle chart at `⟨α, 0⟩`, the second coordinate of the
extended chart at `⟨α, 0⟩` agrees with the α-trivialised fibre coordinate
`chartFiberCoord α`.

Like the `fst` analogue, the identity holds for every `q` since both
sides reduce to the second component of the trivialisation at `α`; the
chart-source hypothesis is not needed at this pointwise level. -/
lemma snd_extChartAt_tangent_zeroSection_apply (α : M) (q : TangentBundle I M) :
    (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M) q).2 =
      chartFiberCoord (I := I) α q := by
  classical
  -- Decompose the bundle-level extended chart via `FiberBundle.extChartAt`.
  have hfb : extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M) q =
      ((extChartAt I α).prod (PartialEquiv.refl E))
        ((trivializationAt E (TangentSpace I) α).toPartialEquiv q) := by
    have := FiberBundle.extChartAt (IB := I) (F := E) (E := TangentSpace I)
      (x := (⟨α, (0 : E)⟩ : TangentBundle I M))
    change extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M) q = _
    rw [this]
    rfl
  rw [hfb]
  -- Second coordinate of the prod-extension is the identity (`refl E`) applied to
  -- the trivialisation's second component, which is `chartFiberCoord α q` by def.
  rfl

/-- Pointwise function-level identity restated as `EventuallyEq` on
`𝓝 p`. Since the underlying equality is unconditional, the
neighbourhood predicate is trivially true. -/
lemma eventuallyEq_snd_extChartAt_tangent_zeroSection (α : M)
    (p : TangentBundle I M) :
    (fun q : TangentBundle I M =>
        (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M) q).2) =ᶠ[𝓝 p]
      (fun q : TangentBundle I M => chartFiberCoord (I := I) α q) :=
  Filter.Eventually.of_forall
    (fun q => snd_extChartAt_tangent_zeroSection_apply (I := I) α q)

/-- **Chart-coordinate rosetta stone, mfderiv form, second component.**
The differential of the tangent-bundle extended chart at `⟨α, 0⟩`,
followed by the second-component projection, equals the differential of
`chartFiberCoord α : TangentBundle I M → E` at `p`.

Both sides are intrinsic: the RHS uses `mfderiv` of `chartFiberCoord α`
on the tangent bundle. -/
theorem snd_mfderiv_extChartAt_tangent_at_zero_section
    {α : M} {p : TangentBundle I M}
    (hp : p.proj ∈ (chartAt H α).source)
    (X : TangentSpace I.tangent p) :
    ((mfderiv I.tangent 𝓘(ℝ, E × E)
       (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)) p) X).2 =
    (mfderiv I.tangent 𝓘(ℝ, E)
       (fun q : TangentBundle I M => chartFiberCoord (I := I) α q) p) X := by
  classical
  -- (1) Eventually equal in a neighbourhood of `p`.
  have hev : (fun q : TangentBundle I M =>
        (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M) q).2) =ᶠ[𝓝 p]
      (fun q : TangentBundle I M => chartFiberCoord (I := I) α q) :=
    eventuallyEq_snd_extChartAt_tangent_zeroSection (I := I) α p
  -- (2) LHS mfderiv: factors as `Prod.snd CLM ∘L mfderiv (chart) p`.
  have hLHS_eq :
      mfderiv I.tangent 𝓘(ℝ, E)
        (fun q : TangentBundle I M =>
          (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M) q).2) p =
      (ContinuousLinearMap.snd ℝ E E) ∘L
        (mfderiv I.tangent 𝓘(ℝ, E × E)
          (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)) p) := by
    have hsnd_contMDiff : ContMDiff 𝓘(ℝ, E × E) 𝓘(ℝ, E) ∞
        (fun y : E × E => y.2) := (ContinuousLinearMap.snd ℝ E E).contMDiff
    have hsnd : MDifferentiableAt 𝓘(ℝ, E × E) 𝓘(ℝ, E)
        (fun y : E × E => y.2)
        (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M) p) :=
      hsnd_contMDiff.mdifferentiableAt (by decide)
    have hchart : MDifferentiableAt I.tangent 𝓘(ℝ, E × E)
        (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)) p := by
      have hp' : p ∈ (chartAt (ModelProd H E)
          (⟨α, (0 : E)⟩ : TangentBundle I M)).source := by
        rw [TangentBundle.mem_chart_source_iff (I := I) (M := M) p
          (⟨α, (0 : E)⟩ : TangentBundle I M)]
        exact hp
      exact mdifferentiableAt_extChartAt (I := I.tangent) hp'
    have hcomp_mf := mfderiv_comp (I := I.tangent) (I' := 𝓘(ℝ, E × E)) (I'' := 𝓘(ℝ, E))
      (f := extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M))
      (g := fun y : E × E => y.2) (x := p) hsnd hchart
    have hsnd_mfderiv :
        mfderiv 𝓘(ℝ, E × E) 𝓘(ℝ, E) (fun y : E × E => y.2)
          (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M) p) =
        ContinuousLinearMap.snd ℝ E E := by
      have h : HasFDerivAt (fun y : E × E => y.2)
          (ContinuousLinearMap.snd ℝ E E)
          (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M) p) :=
        (ContinuousLinearMap.snd ℝ E E).hasFDerivAt
      exact h.hasMFDerivAt.mfderiv
    change mfderiv I.tangent 𝓘(ℝ, E)
      ((fun y : E × E => y.2) ∘
        (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M))) p = _
    rw [hcomp_mf, hsnd_mfderiv]
    rfl
  -- (3) Use `EventuallyEq.mfderiv_eq` to equate the two mfderivs at `p`.
  have hmfd : mfderiv I.tangent 𝓘(ℝ, E)
      (fun q : TangentBundle I M =>
        (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M) q).2) p =
      mfderiv I.tangent 𝓘(ℝ, E)
        (fun q : TangentBundle I M => chartFiberCoord (I := I) α q) p :=
    Filter.EventuallyEq.mfderiv_eq hev
  rw [hLHS_eq] at hmfd
  -- (4) Apply both sides to `X`.
  have happ := congrArg (fun L : TangentSpace I.tangent p →L[ℝ] E => L X) hmfd
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.coe_snd'] at happ
  exact happ

/-! ## Trivialisation identity for the geodesic vector field -/

/-- The mfderiv of the tangent-bundle extended chart, applied to the
chart-fixed geodesic vector field, reproduces the chart-fibre data of
the geodesic vector field.

This is a direct consequence of
`TangentBundle.continuousLinearMapAt_trivializationAt` together with
`Trivialization.continuousLinearMapAt_symmL`. -/
lemma mfderiv_extChartAt_tangent_geodesicVectorFieldChart
    (g : SmoothRiemannianMetric I M) (α : M)
    {p : TangentBundle I M} (hp : p.proj ∈ (chartAt H α).source) :
    (mfderiv I.tangent 𝓘(ℝ, E × E)
       (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)) p)
      (geodesicVectorFieldChart (I := I) g α p) =
    geodesicVectorFieldChartFiber (I := I) g α p := by
  classical
  -- (a) `mfderiv (extChartAt I.tangent ⟨α,0⟩) p` equals the bundle trivialisation's
  -- continuousLinearMapAt at `p`, by `TangentBundle.continuousLinearMapAt_trivializationAt`.
  -- Source membership for the tangent-bundle chart at `⟨α,0⟩`:
  have hp' : p ∈ (chartAt (ModelProd H E)
      (⟨α, (0 : E)⟩ : TangentBundle I M)).source := by
    rw [TangentBundle.mem_chart_source_iff (I := I) (M := M) p
      (⟨α, (0 : E)⟩ : TangentBundle I M)]
    exact hp
  -- (b) `p` lies in the base set of the `T(TM)` trivialisation at `⟨α,0⟩`.
  have hp_baseSet : p ∈ (trivializationAt (E × E) (TangentSpace I.tangent)
      (⟨α, (0 : E)⟩ : TangentBundle I M)).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet (I := I.tangent)
        (M := TangentBundle I M) (⟨α, (0 : E)⟩ : TangentBundle I M)]
    exact hp'
  -- (c) Identify the mfderiv with the trivialisation's CLM at `p`.
  have hmfd_eq := TangentBundle.continuousLinearMapAt_trivializationAt
    (I := I.tangent) (M := TangentBundle I M)
    (x₀ := (⟨α, (0 : E)⟩ : TangentBundle I M)) (x := p) hp'
  -- `hmfd_eq` reads: `(trivAt _ _ ⟨α,0⟩).continuousLinearMapAt ℝ p = mfderiv extChartAt _ p`.
  rw [← hmfd_eq]
  -- (d) Apply the trivialisation CLM to the geodesic vector field, which is by
  -- definition `(triv).symmL p (chartFiberData)`. Then
  -- `continuousLinearMapAt_symmL` collapses the composition.
  unfold geodesicVectorFieldChart
  -- The definition uses `.symm` rather than `.symmL`; they are equal by `coe_symmₗ`.
  set e := trivializationAt (E × E) (TangentSpace I.tangent)
    (⟨α, (0 : E)⟩ : TangentBundle I M)
  -- `e.symm p (...) = e.symmL ℝ p (...)` by definition (`@[simps] symmL`).
  -- Use `continuousLinearMapAt_symmL` directly.
  have hsymm : e.symm p (geodesicVectorFieldChartFiber (I := I) g α p) =
      e.symmL ℝ p (geodesicVectorFieldChartFiber (I := I) g α p) := rfl
  rw [hsymm]
  exact e.continuousLinearMapAt_symmL hp_baseSet _

/-! ## Chart-form of the rosetta stone for integral curves -/

/-- **Chart-coordinate rosetta stone for integral curves of the
chart-fixed geodesic vector field.** Let `f : ℝ → TangentBundle I M`
be a local integral curve at `t` of `geodesicVectorFieldChart g α`,
projecting to `γ` (i.e. `(f s).proj = γ s` for all `s`). Whenever
`γ t` lies in the chart at the basepoint `α`, the chart-base curve
`s ↦ extChartAt I α (γ s)` has derivative equal to the α-trivialised
fibre coordinate `chartFiberCoord α (f t)` at `t`. -/
theorem hasDerivAt_extChartAt_comp_of_isMIntegralCurveAt
    (g : SmoothRiemannianMetric I M) (α : M) {γ : ℝ → M}
    {f : ℝ → TangentBundle I M} {t : ℝ}
    (hproj : ∀ s, (f s).proj = γ s)
    (hpath : IsMIntegralCurveAt f (geodesicVectorFieldChart (I := I) g α) t)
    (hbase : γ t ∈ (chartAt H α).source) :
    HasDerivAt (fun s => extChartAt I α (γ s))
      (chartFiberCoord (I := I) α (f t)) t := by
  classical
  -- (1) `f` has manifold derivative `(1).smulRight (V (f t))` at `t`.
  set V : (p : TangentBundle I M) → TangentSpace I.tangent p :=
    geodesicVectorFieldChart (I := I) g α with hV_def
  have hf_mf : HasMFDerivAt 𝓘(ℝ, ℝ) I.tangent f t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (V (f t))) := hpath.hasMFDerivAt
  -- (2) `(f t).proj = γ t`, so `proj ∘ f = γ`.
  have hf_proj : (f t).proj = γ t := hproj t
  -- (3) `extChartAt I α ∘ proj` is mdifferentiable at `f t` (since
  -- `(f t).proj = γ t ∈ chartAt source`).
  have hf_proj_chart : (f t).proj ∈ (chartAt H α).source := hf_proj ▸ hbase
  have hproj_mdiff : MDifferentiableAt I.tangent I
      (Bundle.TotalSpace.proj : TangentBundle I M → M) (f t) :=
    Bundle.mdifferentiableAt_proj _
  have hchart_mdiff : MDifferentiableAt I 𝓘(ℝ, E)
      (extChartAt I α)
      ((Bundle.TotalSpace.proj : TangentBundle I M → M) (f t)) :=
    mdifferentiableAt_extChartAt (I := I) hf_proj_chart
  -- (4) Chain rule: `extChartAt I α ∘ proj ∘ f` has mfderiv at `t`.
  have hcomp_mf : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E)
      ((fun q : TangentBundle I M => extChartAt I α q.proj) ∘ f) t
      (((mfderiv I 𝓘(ℝ, E) (extChartAt I α) (f t).proj).comp
          (mfderiv I.tangent I
            (Bundle.TotalSpace.proj : TangentBundle I M → M) (f t))).comp
        ((1 : ℝ →L[ℝ] ℝ).smulRight (V (f t)))) := by
    have hcomp_inner : HasMFDerivAt I.tangent 𝓘(ℝ, E)
        ((extChartAt I α) ∘ (Bundle.TotalSpace.proj : TangentBundle I M → M))
        (f t)
        ((mfderiv I 𝓘(ℝ, E) (extChartAt I α) (f t).proj).comp
          (mfderiv I.tangent I
            (Bundle.TotalSpace.proj : TangentBundle I M → M) (f t))) :=
      hchart_mdiff.hasMFDerivAt.comp _ hproj_mdiff.hasMFDerivAt
    -- Rewrite the outer composition.
    have : (fun q : TangentBundle I M => extChartAt I α q.proj) =
        ((extChartAt I α) ∘ (Bundle.TotalSpace.proj : TangentBundle I M → M)) :=
      rfl
    rw [this]
    exact hcomp_inner.comp t hf_mf
  -- (5) The function `(extChartAt I α ∘ proj) ∘ f` equals `s ↦ extChartAt I α (γ s)`.
  have hfun_eq :
      (fun q : TangentBundle I M => extChartAt I α q.proj) ∘ f =
        (fun s => extChartAt I α (γ s)) := by
    funext s
    simp [hproj s]
  rw [hfun_eq] at hcomp_mf
  -- (6) Translate `HasMFDerivAt` (target = 𝓘(ℝ, E)) to `HasDerivAt`.
  have hcomp_fd : HasFDerivAt (fun s => extChartAt I α (γ s))
      (((mfderiv I 𝓘(ℝ, E) (extChartAt I α) (f t).proj).comp
          (mfderiv I.tangent I
            (Bundle.TotalSpace.proj : TangentBundle I M → M) (f t))).comp
        ((1 : ℝ →L[ℝ] ℝ).smulRight (V (f t)))) t :=
    hcomp_mf.hasFDerivAt
  have hcomp_da : HasDerivAt (fun s => extChartAt I α (γ s))
      ((((mfderiv I 𝓘(ℝ, E) (extChartAt I α) (f t).proj).comp
          (mfderiv I.tangent I
            (Bundle.TotalSpace.proj : TangentBundle I M → M) (f t))).comp
        ((1 : ℝ →L[ℝ] ℝ).smulRight (V (f t)))) 1) t :=
    hcomp_fd.hasDerivAt
  -- (7) Simplify the derivative value:
  -- `((Q.comp ((1).smulRight v)) 1) = Q (((1).smulRight v) 1) = Q v` for any CLM Q.
  have hval :
      ((((mfderiv I 𝓘(ℝ, E) (extChartAt I α) (f t).proj).comp
          (mfderiv I.tangent I
            (Bundle.TotalSpace.proj : TangentBundle I M → M) (f t))).comp
        ((1 : ℝ →L[ℝ] ℝ).smulRight (V (f t)))) (1 : ℝ)) =
      (mfderiv I 𝓘(ℝ, E) (extChartAt I α) (f t).proj)
        ((mfderiv I.tangent I
            (Bundle.TotalSpace.proj : TangentBundle I M → M) (f t)) (V (f t))) := by
    -- `(Q.comp R) 1 = Q (R 1)` and `((1).smulRight v) 1 = (1 1) • v = v`.
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply, one_smul]
  rw [hval] at hcomp_da
  -- (8) Identify the value via (a) and the trivialisation identity.
  -- By (a) applied to `X = V (f t)`:
  --   ((mfderiv (extChartAt I.tangent ⟨α,0⟩) (f t)) (V (f t))).1 =
  --     (mfderiv (extChartAt I α) (γ t)) (mfderiv proj (f t) (V (f t)))
  have hfst := fst_mfderiv_extChartAt_tangent_at_zero_section (I := I)
    (α := α) (p := f t) hf_proj_chart (V (f t))
  -- By the trivialisation lemma, the LHS of `hfst` equals `(geodesicVectorFieldChartFiber g α (f t)).1`.
  have hfiber := mfderiv_extChartAt_tangent_geodesicVectorFieldChart (I := I) g α
    (p := f t) hf_proj_chart
  -- Convert via `congrArg .1`:
  have hfiber_fst :
      ((mfderiv I.tangent 𝓘(ℝ, E × E)
         (extChartAt I.tangent (⟨α, (0 : E)⟩ : TangentBundle I M)) (f t))
        (V (f t))).1 =
      (geodesicVectorFieldChartFiber (I := I) g α (f t)).1 := by
    rw [hfiber]
  -- The first component of `geodesicVectorFieldChartFiber g α (f t)` is `chartFiberCoord α (f t)`.
  have hfiber_fst' :
      (geodesicVectorFieldChartFiber (I := I) g α (f t)).1 =
      chartFiberCoord (I := I) α (f t) := rfl
  -- Combine:
  have hkey :
      (mfderiv I 𝓘(ℝ, E) (extChartAt I α) (f t).proj)
        ((mfderiv I.tangent I
            (Bundle.TotalSpace.proj : TangentBundle I M → M) (f t)) (V (f t))) =
      chartFiberCoord (I := I) α (f t) := by
    rw [← hfst, hfiber_fst, hfiber_fst']
  -- (9) Rewrite `(f t).proj` to `γ t` via `hf_proj`.
  rw [hkey] at hcomp_da
  exact hcomp_da

/-! ## Intrinsic identification of velocity with the fibre part of the lift -/

/-- **Intrinsic fibre identification of the velocity.** Under the
hypothesis that the base path `γ t` lies in the chart at the
basepoint `α`, the intrinsic `velocity γ t` equals the fibre
component `(f t).2` of the lift, transported via the projection
identity `(f t).proj = γ t`.

The chart hypothesis is mathematically necessary: off the chart at
`α`, the geodesic vector field vanishes, hence `f` is locally
constant and `velocity γ t = 0` while `(f t).2` need not vanish. -/
theorem velocity_eq_snd_of_isMIntegralCurveAt
    (g : SmoothRiemannianMetric I M) (α : M) {γ : ℝ → M}
    {f : ℝ → TangentBundle I M} {t : ℝ}
    (hproj : ∀ s, (f s).proj = γ s)
    (hpath : IsMIntegralCurveAt f (geodesicVectorFieldChart (I := I) g α) t)
    (hbase : γ t ∈ (chartAt H α).source) :
    velocity (I := I) γ t = (hproj t ▸ (f t).2 : TangentSpace I (γ t)) := by
  classical
  -- (A) From the chart-form rosetta (b), the chart-base curve has derivative
  -- `chartFiberCoord α (f t)`.
  have hderiv := hasDerivAt_extChartAt_comp_of_isMIntegralCurveAt (I := I)
    g α hproj hpath hbase
  -- (B) The intrinsic `velocity γ t` is `mfderiv γ t 1`. Its image under
  -- `mfderiv (extChartAt I α) (γ t)` is the derivative of `extChartAt I α ∘ γ`
  -- at `t`, applied to `1`, by the chain rule.
  have hf_proj : (f t).proj = γ t := hproj t
  have hf_proj_chart : (f t).proj ∈ (chartAt H α).source := hf_proj ▸ hbase
  -- `extChartAt I α` mdifferentiable at `γ t`.
  have hchart_mdiff_γ : MDifferentiableAt I 𝓘(ℝ, E)
      (extChartAt I α) (γ t) := mdifferentiableAt_extChartAt (I := I) hbase
  -- Bundle the derivative as a `HasMFDerivAt` claim about `velocity`:
  -- We need `mfderiv (extChartAt I α) (γ t) (velocity γ t) = chartFiberCoord α (f t)`.
  -- This will follow from the eventual differentiability and chain rule, but the cleanest
  -- way is to recognize that `HasDerivAt (extChartAt I α ∘ γ) c t` implies
  -- `HasMFDerivAt (extChartAt I α ∘ γ) t ((1).smulRight c)`, which in turn equals
  -- the composition `mfderiv (extChartAt I α) (γ t) ∘L (mfderiv γ t)`.
  -- We use only that the chart-base derivative gives the chart-fibre coordinate.
  -- Define the intrinsic vector to be compared with `velocity γ t`.
  set u : TangentSpace I (γ t) := (hproj t ▸ (f t).2 : TangentSpace I (γ t))
  -- (C) Apply `mfderiv (extChartAt I α) (γ t)` to `u`. By
  -- `TangentBundle.continuousLinearMapAt_trivializationAt`, this equals
  -- `(trivAt E (TangentSpace I) α).continuousLinearMapAt ℝ (γ t) u`.
  have hCLM_eq := TangentBundle.continuousLinearMapAt_trivializationAt
    (I := I) (M := M) (x₀ := α) (x := γ t) hbase
  -- `hCLM_eq : (trivAt _).continuousLinearMapAt ℝ (γ t) = mfderiv (extChartAt I α) (γ t)`.
  -- Step (D): compute `(trivAt _).continuousLinearMapAt ℝ (γ t) u`.
  -- Using `coe_linearMapAt_of_mem`: `(triv).continuousLinearMapAt ℝ b y = (triv ⟨b, y⟩).2`
  -- when `b ∈ baseSet`. With `b = γ t` (in chart source = baseSet) and
  -- `y = u : TangentSpace I (γ t) = E`, we get `(triv ⟨γ t, u⟩).2`.
  -- Since `u = hproj t ▸ (f t).2`, transporting via `hproj t` we have
  -- `⟨γ t, u⟩ = ⟨(f t).proj, (f t).2⟩ = f t` (after transport).
  have hbase_set : γ t ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet (I := I) (M := M) α]
    exact hbase
  -- `((triv).continuousLinearMapAt ℝ (γ t)) u = (triv ⟨γ t, u⟩).2`.
  have hlmAt_val :
      (((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ
            (γ t)) u : E) =
      (((trivializationAt E (TangentSpace I) α)
          (⟨γ t, u⟩ : TangentBundle I M)).2 : E) := by
    have hcoe := (trivializationAt E (TangentSpace I) α).coe_linearMapAt_of_mem
      (R := ℝ) hbase_set
    -- `hcoe : ⇑((triv).linearMapAt ℝ (γ t)) = fun y => (triv ⟨γ t, y⟩).2`
    -- `(triv).continuousLinearMapAt ℝ (γ t) y = ((triv).linearMapAt ℝ (γ t)) y`.
    have hcLM_eq_lm :
        ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ
            (γ t)) u =
          ((trivializationAt E (TangentSpace I) α).linearMapAt ℝ (γ t)) u := rfl
    rw [hcLM_eq_lm, hcoe]
  -- Now identify `⟨γ t, u⟩` with `f t` (after `hproj t` transport).
  have hpt_eq : (⟨γ t, u⟩ : TangentBundle I M) = f t := by
    -- `f t = ⟨(f t).proj, (f t).2⟩`, with `(f t).proj = γ t`. After transport via `hproj t`,
    -- `u = hproj t ▸ (f t).2 = (f t).2` (since TangentSpace I _ = E definitionally).
    -- Use `Bundle.TotalSpace.mk_proj`-style identification.
    change (⟨γ t, u⟩ : TangentBundle I M) = ⟨(f t).proj, (f t).2⟩
    -- `u : TangentSpace I (γ t)` and we want to identify with `(f t).2`.
    refine Bundle.TotalSpace.ext hf_proj.symm ?_
    -- After projecting both sides to `γ t`, the snd components must match.
    -- `hf_proj : (f t).proj = γ t`. So `u = hproj t ▸ (f t).2`.
    -- We need `cast _ u = (f t).2` modulo HEq.
    change HEq u (f t).2
    -- `TangentSpace I x = E` for all `x`, so HEq reduces to value equality.
    have hu : u = (hproj t ▸ (f t).2 : TangentSpace I (γ t)) := rfl
    -- Use `subst hf_proj` after rewriting.
    -- We need: HEq ((hproj t) ▸ (f t).2 : TangentSpace I (γ t)) (f t).2.
    -- `hproj t : (f t).proj = γ t`. Transport along this gives an HEq.
    rw [hu]
    exact (eqRec_heq (hproj t) ((f t).2))
  rw [hpt_eq] at hlmAt_val
  -- (E) `(triv ⟨α, ...⟩) (f t)).2 = chartFiberCoord α (f t)` by definition.
  have hfiberCoord :
      (((trivializationAt E (TangentSpace I) α) (f t)).2 : E) =
        chartFiberCoord (I := I) α (f t) := rfl
  rw [hfiberCoord] at hlmAt_val
  -- So `mfderiv (extChartAt I α) (γ t) u = chartFiberCoord α (f t)`.
  have hRHS_chart :
      (mfderiv I 𝓘(ℝ, E) (extChartAt I α) (γ t)) u =
        chartFiberCoord (I := I) α (f t) := by
    rw [← hCLM_eq]; exact hlmAt_val
  -- (F) Now compute `(mfderiv (extChartAt I α) (γ t)) (velocity γ t)`. By chain rule
  -- on `extChartAt I α ∘ γ`, this equals the derivative of `extChartAt I α ∘ γ` at `t`
  -- applied to `1 : ℝ`, which is `chartFiberCoord α (f t)` by (b).
  -- First, `velocity γ t = mfderiv γ t 1`.
  -- Mdifferentiability of `γ` at `t`: follows from `(proj ∘ f) = γ` and `f` mdiff at `t`.
  have hf_mdiff : MDifferentiableAt 𝓘(ℝ, ℝ) I.tangent f t :=
    hpath.hasMFDerivAt.mdifferentiableAt
  have hproj_mdiff : MDifferentiableAt I.tangent I
      (Bundle.TotalSpace.proj : TangentBundle I M → M) (f t) :=
    Bundle.mdifferentiableAt_proj _
  have hγ_eq_proj_f : γ = ((Bundle.TotalSpace.proj : TangentBundle I M → M) ∘ f) := by
    funext s; exact (hproj s).symm
  have hγ_mdiff : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t := by
    rw [hγ_eq_proj_f]
    exact hproj_mdiff.comp _ hf_mdiff
  have hchart_γ_mf : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E)
      ((extChartAt I α) ∘ γ) t
      ((mfderiv I 𝓘(ℝ, E) (extChartAt I α) (γ t)).comp
        (mfderiv 𝓘(ℝ, ℝ) I γ t)) :=
    hchart_mdiff_γ.hasMFDerivAt.comp _ hγ_mdiff.hasMFDerivAt
  -- Convert to `HasDerivAt`:
  have hchart_γ_fd : HasFDerivAt ((extChartAt I α) ∘ γ)
      ((mfderiv I 𝓘(ℝ, E) (extChartAt I α) (γ t)).comp
        (mfderiv 𝓘(ℝ, ℝ) I γ t)) t :=
    hchart_γ_mf.hasFDerivAt
  have hchart_γ_da : HasDerivAt ((extChartAt I α) ∘ γ)
      (((mfderiv I 𝓘(ℝ, E) (extChartAt I α) (γ t)).comp
        (mfderiv 𝓘(ℝ, ℝ) I γ t)) (1 : ℝ)) t :=
    hchart_γ_fd.hasDerivAt
  -- Simplify value:
  have hval_γ :
      (((mfderiv I 𝓘(ℝ, E) (extChartAt I α) (γ t)).comp
          (mfderiv 𝓘(ℝ, ℝ) I γ t)) (1 : ℝ)) =
        (mfderiv I 𝓘(ℝ, E) (extChartAt I α) (γ t))
          (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)) := by
    rw [ContinuousLinearMap.comp_apply]
  rw [hval_γ] at hchart_γ_da
  -- `velocity γ t = mfderiv γ t 1`.
  have hvel_def : velocity (I := I) γ t = mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ) := rfl
  -- Also `(extChartAt I α ∘ γ) = (fun s => extChartAt I α (γ s))`.
  have hcomp_eq :
      ((extChartAt I α) ∘ γ) = (fun s => extChartAt I α (γ s)) := rfl
  rw [hcomp_eq] at hchart_γ_da
  -- Now: `hchart_γ_da : HasDerivAt (fun s => extChartAt I α (γ s)) (mfderiv ... (velocity γ t)) t`.
  -- And `hderiv : HasDerivAt (fun s => extChartAt I α (γ s)) (chartFiberCoord α (f t)) t`.
  -- By uniqueness of `HasDerivAt`:
  have hLHS_chart : (mfderiv I 𝓘(ℝ, E) (extChartAt I α) (γ t))
      (velocity (I := I) γ t) = chartFiberCoord (I := I) α (f t) := by
    have h1 := hchart_γ_da
    have h2 := hderiv
    -- HasDerivAt determines the derivative uniquely.
    have heq : (mfderiv I 𝓘(ℝ, E) (extChartAt I α) (γ t))
        (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)) =
      chartFiberCoord (I := I) α (f t) := h1.unique h2
    rw [hvel_def]
    exact heq
  -- (G) Both `velocity γ t` and `u` get mapped by the invertible CLM
  -- `mfderiv (extChartAt I α) (γ t)` to `chartFiberCoord α (f t)`. Hence they are equal.
  have hinv : (mfderiv I 𝓘(ℝ, E) (extChartAt I α) (γ t)).IsInvertible := by
    -- Reduce to `isInvertible_mfderiv_extChartAt`.
    have hext : γ t ∈ (extChartAt I α).source := by
      rw [extChartAt_source]; exact hbase
    exact isInvertible_mfderiv_extChartAt (I := I) hext
  have hinj : Function.Injective (mfderiv I 𝓘(ℝ, E) (extChartAt I α) (γ t)) :=
    hinv.bijective.injective
  apply hinj
  rw [hLHS_chart, hRHS_chart]

end Geodesic
end Riemannian
end Geometry
end DifferentialGeometry

end
