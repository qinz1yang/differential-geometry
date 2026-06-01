import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.SmoothInSpace.VariationalLiftManifoldFlowOrbitODE
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.SmoothInSpace.VariationalODE
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.SmoothInSpace.VariationalLift
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.SmoothInSpace.VariationalLiftConventionBridge
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Producers for the two linearized-flow factor derivatives `hT` and `hP`

The orbit-ODE assembly `chartCloseDop_hasDerivAt_clm_comp`
(`SmoothInSpace/VariationalLiftManifoldFlowOrbitODE.lean`) and the flat per-slot identity
`rawVariationalIdentityFlat_of_orbitODE_factors`
(`SmoothInSpace/VariationalLiftFlatIdentity.lean`) both consume, for a diffeomorphism family
`Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M)`, the two factor `HasDerivAt` data

* `hP : HasDerivAt (chartCloseFderiv Φ_fam α x) P' t` — the orbit-derivative of the
  chart-coordinate spatial Fréchet derivative of the chart-`α`-conjugated flow; and
* `hT : HasDerivAt (chartCloseTriv Φ_fam α x) T' t` — the orbit-derivative of the moving
  inverse target trivialisation.

This file builds `hP` from the genuine Euclidean linearized-flow ODE, taking as inputs exactly
the chart-conjugation data that a concrete chart-local flow makes available.

## `hP` from the Euclidean variational ODE

`chartCloseFderiv Φ_fam α x s = mfderiv I 𝓘(ℝ, E) (extChartAt I α ∘ Φ_fam s) x`.  For a
chart-`α`-conjugated flow — i.e. when, near `x`, `extChartAt I α ∘ Φ_fam s` agrees with the
Euclidean flow `Φ_eucl(·, s)` post-composed with the *fixed* source chart `extChartAt I α`,
`extChartAt I α (Φ_fam s y) = Φ_eucl (extChartAt I α y) s` — the chain rule
(`mfderiv_comp`, `mfderiv_eq_fderiv` on the model side) factors the manifold pushforward as

  `chartCloseFderiv Φ_fam α x s
     = (fderiv ℝ (fun z => Φ_eucl z s) (extChartAt I α x)).comp (trivToE α x)`,

a *fixed* continuous-linear post-composition `· ∘L trivToE α x` of the Euclidean
chart-flow spatial Fréchet derivative `s ↦ fderiv ℝ (fun z => Φ_eucl z s) (extChartAt I α x)`.
The Euclidean operator-valued variational ODE `IsLocalFlow.hasDerivAt_partial_spatial_fderiv`
(`SmoothInSpace/VariationalODE.lean`) supplies the `HasDerivAt` of that Euclidean factor; the
fixed post-composition then transfers it (`HasFDerivAt.comp_hasDerivAt` with the fixed CLM
`compL · |>.flip (trivToE α x)`) to `chartCloseFderiv`.

This is the genuine producer for `hP`: no metric `g`, no `HasLocallyConstantChartAt`, no
joint-`C^∞`-on-`ℝ × M` predicate.  The only smoothness input is the Euclidean operator-valued
ODE on the model space `E`; the chart-conjugation agreement is a per-flow chart fact (an
eventual equality of `E`-valued maps), and the source-chart differential is the fixed
trivialisation `trivToE α x`.  No hypothesis-packaging: the inputs are the Euclidean
`HasDerivAt`, a chart-agreement eventual equality, and a manifold-differentiability datum,
none of which is — or trivially destructures to — the operator-valued `HasDerivAt` conclusion.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.ODE

open Set Function Bundle Filter
open scoped Manifold Topology ContDiff
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.ODE.Flow

section FactorProducers

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M]
  [BoundarylessManifold I M] in
/-- **Operator-valued `HasDerivAt` through a fixed continuous-linear post-composition on the
right.**

If `s ↦ A s : E →L[ℝ] E` has `HasDerivAt` at `t` with derivative `A'`, then for any fixed
`R : E →L[ℝ] E`, the path `s ↦ (A s).comp R` has `HasDerivAt` at `t` with derivative
`A'.comp R`.

This is the mechanical transport used to push the Euclidean operator-valued variational ODE
through the (time-independent) source-chart differential `R := trivToE α x`. -/
theorem hasDerivAt_clm_comp_right
    {A : ℝ → (E →L[ℝ] E)} {A' : E →L[ℝ] E} {t : ℝ}
    (hA : HasDerivAt A A' t) (R : E →L[ℝ] E) :
    HasDerivAt (fun s : ℝ => (A s).comp R) (A'.comp R) t := by
  have hcompR : HasFDerivAt (fun L : E →L[ℝ] E => L.comp R)
      ((ContinuousLinearMap.compL ℝ E E E).flip R) (A t) :=
    ((ContinuousLinearMap.compL ℝ E E E).flip R).hasFDerivAt
  have := hcompR.comp_hasDerivAt t hA
  simpa using this

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M]
  [BoundarylessManifold I M] in
/-- **Chart-conjugation decomposition of the chart-coordinate spatial Fréchet derivative.**

Let `Φ_eucl : E → ℝ → E` be the Euclidean chart-coordinate flow, and suppose that, near `x`,
the chart-`α`-conjugated manifold flow agrees with `Φ_eucl` post-composed with the *fixed*
source chart `extChartAt I α`:

  `extChartAt I α (Φ_fam s y) = Φ_eucl (extChartAt I α y) s`   for `y` near `x`.

Then the chart-coordinate spatial Fréchet derivative factor `chartCloseFderiv Φ_fam α x s`
(the second factor of `chartCloseDop`) decomposes, by the manifold chain rule
(`mfderiv_comp`, `mfderiv_eq_fderiv` on the model-space factor,
`continuousLinearMapAt_trivializationAt` for the source-chart differential), as the Euclidean
chart-flow spatial Fréchet derivative post-composed on the right with the *fixed* source-chart
trivialisation `trivToE α x`:

  `chartCloseFderiv Φ_fam α x s
     = (fderiv ℝ (fun z => Φ_eucl z s) (extChartAt I α x)).comp (trivToE α x)`.

Genuine content: the manifold chain rule applied to `(fun z => Φ_eucl z s) ∘ extChartAt I α`,
read through the eventual chart-conjugation agreement.  No metric, no hypothesis-packaging:
the conclusion is an `E →L E`-equation, not the variational `HasDerivAt` target. -/
theorem chartCloseFderiv_eq_eucl_comp_trivToE
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M) (α x : M) (s : ℝ)
    (Φ_eucl : E → ℝ → E)
    (hx_src : x ∈ (chartAt H α).source)
    (heucl_diff : DifferentiableAt ℝ (fun z => Φ_eucl z s) (extChartAt I α x))
    (hagree : (fun y => extChartAt I α ((Φ_fam s : M → M) y))
      =ᶠ[𝓝 x] (fun y => Φ_eucl (extChartAt I α y) s)) :
    chartCloseFderiv (I := I) Φ_fam α x s
      = (fderiv ℝ (fun z => Φ_eucl z s) (extChartAt I α x)).comp
          (trivToE (I := I) α x) := by
  unfold chartCloseFderiv
  have hmfeq : mfderiv I 𝓘(ℝ, E) (fun y => extChartAt I α ((Φ_fam s : M → M) y)) x
      = mfderiv I 𝓘(ℝ, E) (fun y => Φ_eucl (extChartAt I α y) s) x :=
    Filter.EventuallyEq.mfderiv_eq hagree
  rw [hmfeq]
  have hsrc_eq : mfderiv I 𝓘(ℝ, E) (extChartAt I α) x = trivToE (I := I) α x :=
    (TangentBundle.continuousLinearMapAt_trivializationAt (I := I) hx_src).symm
  have hext_diff : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I α) x :=
    mdifferentiableAt_extChartAt (I := I) hx_src
  have heucl_mdiff : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (fun z => Φ_eucl z s)
      (extChartAt I α x) :=
    heucl_diff.mdifferentiableAt
  have hchain :
      mfderiv I 𝓘(ℝ, E) ((fun z => Φ_eucl z s) ∘ (extChartAt I α)) x
        = (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun z => Φ_eucl z s) (extChartAt I α x)).comp
            (mfderiv I 𝓘(ℝ, E) (extChartAt I α) x) :=
    mfderiv_comp x heucl_mdiff hext_diff
  have hcompfun : (fun y => Φ_eucl (extChartAt I α y) s)
      = (fun z => Φ_eucl z s) ∘ (extChartAt I α) := rfl
  rw [hcompfun, hchain, hsrc_eq]
  rw [mfderiv_eq_fderiv]
  rfl

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M]
  [BoundarylessManifold I M] in
/-- **Producer for the chart spatial-variational factor `hP`.**

For a diffeomorphism family `Φ_fam` whose chart-`α`-conjugated flow agrees, near `x` and for
`s` near `t`, with a Euclidean chart-coordinate flow `Φ_eucl` post-composed with the *fixed*
source chart `extChartAt I α`, the chart-coordinate spatial Fréchet derivative factor
`chartCloseFderiv Φ_fam α x` satisfies the orbit-derivative ODE

  `HasDerivAt (chartCloseFderiv Φ_fam α x) (D'_eucl.comp (trivToE α x)) t`,

where `D'_eucl` is the derivative value of the *Euclidean* operator-valued variational ODE
`s ↦ fderiv ℝ (fun z => Φ_eucl z s) (extChartAt I α x)` at `t` (supplied by
`IsLocalFlow.hasDerivAt_partial_spatial_fderiv`).

The inputs are exactly the chart-coordinate flow data:

* `heucl` — the Euclidean operator-valued variational `HasDerivAt` on the model space `E`;
* `hx_src` — `x` lies in the chart source of `α` (where the conjugation is valid);
* `heucl_diff` — differentiability of the Euclidean spatial slice near `t` (so the chart
  decomposition `chartCloseFderiv_eq_eucl_comp_trivToE` applies eventually);
* `hagree` — the eventual (`=ᶠ[𝓝 t]` of `=ᶠ[𝓝 x]`) chart-conjugation agreement.

This is precisely the `hP : HasDerivAt (chartCloseFderiv Φ_fam α x) P' t` consumed by
`chartCloseDop_hasDerivAt_clm_comp` and `rawVariationalIdentityFlat_of_orbitODE_factors`, with
`P' := D'_eucl.comp (trivToE α x)`.  No metric `g`, no `HasLocallyConstantChartAt`, no
joint-`C^∞`-on-`ℝ × M`.  No hypothesis-packaging: the inputs are a Euclidean `HasDerivAt`, a
chart-membership datum, a per-time differentiability datum, and a chart-agreement eventual
equality, none of which is the operator-valued `HasDerivAt` conclusion. -/
theorem chartCloseFderiv_hasDerivAt_of_eucl
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M) (α x : M) (t : ℝ)
    (Φ_eucl : E → ℝ → E) {D'_eucl : E →L[ℝ] E}
    (hx_src : x ∈ (chartAt H α).source)
    (heucl : HasDerivAt (fun s : ℝ => fderiv ℝ (fun z => Φ_eucl z s) (extChartAt I α x))
      D'_eucl t)
    (heucl_diff : ∀ᶠ s : ℝ in 𝓝 t,
      DifferentiableAt ℝ (fun z => Φ_eucl z s) (extChartAt I α x))
    (hagree : ∀ᶠ s : ℝ in 𝓝 t,
      (fun y => extChartAt I α ((Φ_fam s : M → M) y))
        =ᶠ[𝓝 x] (fun y => Φ_eucl (extChartAt I α y) s)) :
    HasDerivAt (chartCloseFderiv (I := I) Φ_fam α x)
      (D'_eucl.comp (trivToE (I := I) α x)) t := by
  letI : InnerProductSpace ℝ (TangentSpace I x) := (inferInstance : InnerProductSpace ℝ E)
  have hpost : HasDerivAt
      (fun s : ℝ => (fderiv ℝ (fun z => Φ_eucl z s) (extChartAt I α x)).comp (trivToE (I := I) α x))
      (D'_eucl.comp (trivToE (I := I) α x)) t :=
    hasDerivAt_clm_comp_right heucl (trivToE (I := I) α x)
  have hev : (fun s : ℝ => chartCloseFderiv (I := I) Φ_fam α x s)
      =ᶠ[𝓝 t] (fun s : ℝ =>
        (fderiv ℝ (fun z => Φ_eucl z s) (extChartAt I α x)).comp (trivToE (I := I) α x)) := by
    filter_upwards [heucl_diff, hagree] with s hsd hsa
    exact chartCloseFderiv_eq_eucl_comp_trivToE (I := I) Φ_fam α x s Φ_eucl hx_src hsd hsa
  exact hpost.congr_of_eventuallyEq hev

section MovingTrivInverse

variable [CompleteSpace E]

omit [CompleteSpace E] in
/-- At the basepoint image `φ α`, the forward moving trivialisation is the identity
(`chartMovingTriv_basepoint`), hence a unit of the endomorphism ring `E →L[ℝ] E`. -/
theorem chartMovingTriv_basepoint_isUnit (α : M) :
    IsUnit (chartMovingTriv (I := I) α (extChartAt I α α)) := by
  have h1 : chartMovingTriv (I := I) α (extChartAt I α α) = (1 : E →L[ℝ] E) := by
    ext v
    simpa using chartMovingTriv_basepoint (I := I) α v
  rw [h1]
  exact isUnit_one

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M]
  [BoundarylessManifold I M] in
/-- **The chart-close inverse trivialisation IS the ring inverse of the moving trivialisation.**

For an orbit point `b := Φ_fam s x` in the chart source of `α`, the canonical chart-close
inverse trivialisation factor `chartCloseTriv Φ_fam α x s = trivFromE α b` (an honest `E →L[ℝ] E`
by the `chartCloseTriv` definition) is the *ring inverse* of the forward moving trivialisation
`chartMovingTriv α (extChartAt I α b)`:

  `chartCloseTriv Φ_fam α x s = Ring.inverse (chartMovingTriv α (extChartAt I α (Φ_fam s x)))`.

Both sides are genuine `E →L[ℝ] E`; the moving trivialisation, with the `chartCloseTriv` value as
its two-sided (vector-level) inverse, is a unit, and the ring inverse is read off by
`Ring.inverse_mul_cancel`.  No metric, no hypothesis-packaging: an `E →L E`-equation. -/
theorem chartCloseTriv_eq_ringInverse_chartMovingTriv
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M) (α x : M) (s : ℝ)
    (hsrc : (Φ_fam s : M → M) x ∈ (chartAt H α).source) :
    chartCloseTriv (I := I) Φ_fam α x s
      = Ring.inverse (chartMovingTriv (I := I) α (extChartAt I α ((Φ_fam s : M → M) x))) := by
  set b : M := (Φ_fam s : M → M) x with hb_def
  have hbase : b ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact hsrc
  have hbsymm : (extChartAt I α).symm (extChartAt I α b) = b :=
    (extChartAt I α).left_inv (by simpa [extChartAt_source] using hsrc)
  have hmul : chartMovingTriv (I := I) α (extChartAt I α b)
      * chartCloseTriv (I := I) Φ_fam α x s = 1 := by
    rw [ContinuousLinearMap.mul_def]; ext w
    change chartMovingTriv (I := I) α (extChartAt I α b)
        (chartCloseTriv (I := I) Φ_fam α x s w) = w
    unfold chartCloseTriv chartMovingTriv
    rw [hbsymm]
    exact trivToE_trivFromE (I := I) α hbase w
  have hmul' : chartCloseTriv (I := I) Φ_fam α x s
      * chartMovingTriv (I := I) α (extChartAt I α b) = 1 := by
    rw [ContinuousLinearMap.mul_def]; ext w
    change chartCloseTriv (I := I) Φ_fam α x s
        (chartMovingTriv (I := I) α (extChartAt I α b) w) = w
    unfold chartCloseTriv chartMovingTriv
    rw [hbsymm]
    exact trivFromE_trivToE (I := I) α hbase w
  have hunit : IsUnit (chartMovingTriv (I := I) α (extChartAt I α b)) :=
    isUnit_iff_exists_and_exists.mpr
      ⟨⟨chartCloseTriv (I := I) Φ_fam α x s, hmul⟩, ⟨chartCloseTriv (I := I) Φ_fam α x s, hmul'⟩⟩
  symm
  calc Ring.inverse (chartMovingTriv (I := I) α (extChartAt I α b))
      = Ring.inverse (chartMovingTriv (I := I) α (extChartAt I α b))
          * (chartMovingTriv (I := I) α (extChartAt I α b)
              * chartCloseTriv (I := I) Φ_fam α x s) := by rw [hmul, mul_one]
    _ = (Ring.inverse (chartMovingTriv (I := I) α (extChartAt I α b))
          * chartMovingTriv (I := I) α (extChartAt I α b))
          * chartCloseTriv (I := I) Φ_fam α x s := by rw [mul_assoc]
    _ = chartCloseTriv (I := I) Φ_fam α x s := by
          rw [Ring.inverse_mul_cancel _ hunit, one_mul]

/-- **Producer for the moving inverse-trivialisation factor `hT`.**

For a diffeomorphism family `Φ_fam` with `α := Φ_fam t x` the time-`t` orbit point, the moving
inverse target trivialisation factor `chartCloseTriv Φ_fam α x` (the first factor of
`chartCloseDop`) satisfies the orbit-derivative ODE

  `HasDerivAt (chartCloseTriv Φ_fam α x)
      ((-ContinuousLinearMap.mulLeftRight ℝ (E →L[ℝ] E) 1 1) g') t`,

where `g'` is the derivative value of the *forward* moving trivialisation along the orbit
`s ↦ chartMovingTriv α (extChartAt I α (Φ_fam s x))` at `t` (a pure smooth-structure jet).

The inputs are exactly the chart-coordinate flow data:

* `hg` — the `HasDerivAt` of the forward moving trivialisation along the orbit (the genuine
  smooth-structure chart-transition jet; metric-free, the orbit-derivative of the moving
  trivialisation, decomposed by the convention bridge `chartTrivRepr_fderiv_eq` into the `D²φ`
  content the project documents);
* `hcontAt` — continuity of the orbit `s ↦ Φ_fam s x` at `t` (so the orbit stays in the chart
  source of `α` near `t`, where the ring-inverse identification holds).

The derivative value uses the operator-inverse Fréchet derivative `hasFDerivAt_ringInverse` at
the basepoint unit `chartMovingTriv α (φ α) = 1` (`chartMovingTriv_basepoint_isUnit`), so
`(g t)⁻¹ = 1` and the value reduces to `-mulLeftRight ℝ (E →L E) 1 1` applied to `g'`.

This is precisely the `hT : HasDerivAt (chartCloseTriv Φ_fam α x) T' t` consumed by
`chartCloseDop_hasDerivAt_clm_comp` and `rawVariationalIdentityFlat_of_orbitODE_factors`, with
`T' := (-mulLeftRight ℝ (E →L E) 1 1) g'`.  No metric `g`, no `HasLocallyConstantChartAt`, no
joint-`C^∞`-on-`ℝ × M`.  No hypothesis-packaging: the inputs are the moving-trivialisation
`HasDerivAt` and an orbit-continuity datum, neither of which is the operator-valued `HasDerivAt`
conclusion. -/
theorem chartCloseTriv_hasDerivAt_of_movingTriv
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M) (t : ℝ) (x : M) {g' : E →L[ℝ] E}
    (hg : HasDerivAt
      (fun s : ℝ => chartMovingTriv (I := I) (Φ_fam t x)
        (extChartAt I (Φ_fam t x) ((Φ_fam s : M → M) x))) g' t)
    (hcontAt : ContinuousAt (fun s : ℝ => (Φ_fam s : M → M) x) t) :
    HasDerivAt (chartCloseTriv (I := I) Φ_fam (Φ_fam t x) x)
      ((-ContinuousLinearMap.mulLeftRight ℝ (E →L[ℝ] E)
          (1 : E →L[ℝ] E) (1 : E →L[ℝ] E)) g') t := by
  classical
  set α : M := Φ_fam t x with hα
  have ht_self : (Φ_fam t : M → M) x = α := rfl
  have hbase_eq : (fun s : ℝ => chartMovingTriv (I := I) α
        (extChartAt I α ((Φ_fam s : M → M) x))) t
      = chartMovingTriv (I := I) α (extChartAt I α α) := by
    simp only [ht_self]
  have hunit1 : chartMovingTriv (I := I) α (extChartAt I α α) = (1 : E →L[ℝ] E) := by
    ext v; simpa using chartMovingTriv_basepoint (I := I) α v
  have hinv_fderiv : HasFDerivAt (Ring.inverse : (E →L[ℝ] E) → (E →L[ℝ] E))
      (-ContinuousLinearMap.mulLeftRight ℝ (E →L[ℝ] E) (1 : E →L[ℝ] E) (1 : E →L[ℝ] E))
      (chartMovingTriv (I := I) α (extChartAt I α α)) := by
    have hu : (chartMovingTriv (I := I) α (extChartAt I α α)) = ((1 : (E →L[ℝ] E)ˣ) : E →L[ℝ] E) :=
      by rw [hunit1]; rfl
    rw [hu]
    have := hasFDerivAt_ringInverse (𝕜 := ℝ) (R := E →L[ℝ] E) (1 : (E →L[ℝ] E)ˣ)
    simpa using this
  have hgt_eq : (fun s : ℝ => chartMovingTriv (I := I) α
        (extChartAt I α ((Φ_fam s : M → M) x))) t
      = chartMovingTriv (I := I) α (extChartAt I α α) := hbase_eq
  have hchain : HasDerivAt
      (fun s : ℝ => Ring.inverse (chartMovingTriv (I := I) α
        (extChartAt I α ((Φ_fam s : M → M) x))))
      ((-ContinuousLinearMap.mulLeftRight ℝ (E →L[ℝ] E)
          (1 : E →L[ℝ] E) (1 : E →L[ℝ] E)) g') t := by
    have := (hgt_eq ▸ hinv_fderiv).comp_hasDerivAt t hg
    simpa using this
  have hmem : ∀ᶠ s : ℝ in 𝓝 t,
      (Φ_fam s : M → M) x ∈ (chartAt H α).source :=
    flow_orbit_eventually_mem_chartAt_source (I := I) Φ_fam t x hcontAt
  have hev : (chartCloseTriv (I := I) Φ_fam α x)
      =ᶠ[𝓝 t] (fun s : ℝ => Ring.inverse (chartMovingTriv (I := I) α
        (extChartAt I α ((Φ_fam s : M → M) x)))) := by
    filter_upwards [hmem] with s hs
    exact chartCloseTriv_eq_ringInverse_chartMovingTriv (I := I) Φ_fam α x s hs
  exact hchain.congr_of_eventuallyEq hev

end MovingTrivInverse

end FactorProducers

end DifferentialGeometry.PDE.RicciFlow.ODE
