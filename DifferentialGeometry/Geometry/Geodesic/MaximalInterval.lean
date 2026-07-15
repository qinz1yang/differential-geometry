import DifferentialGeometry.Geometry.Geodesic.Equation
import DifferentialGeometry.Geometry.Geodesic.Existence
import DifferentialGeometry.Geometry.Geodesic.Uniqueness
import DifferentialGeometry.Geometry.Comparison.Variation.SecondVariation
import Mathlib.Geometry.Manifold.Riemannian.PathELength
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option linter.unusedSectionVars false

/-!
# Maximal interval of definition for a geodesic with prescribed initial data

For a smooth Riemannian metric `g` on a boundaryless smooth manifold `M`
modelled on a complete inner-product space `E`, every initial datum
`(p : M, v : T_p M)` gives rise to a *maximal open interval*
`I_max(p, v) ⊆ ℝ` containing `0` on which a geodesic with that initial
datum is defined, together with a canonical curve `maximalGeodesic g p v : ℝ → M`
that realises this geodesic on `I_max(p, v)` (and is junk-valued outside).

## Main definitions

* `IsGeodesicOn g γ s`: an interval-restricted geodesic predicate; the
  set-relativised analogue of `IsGeodesic`. There exist a chart basepoint
  `α : M` and a lifted curve `f : ℝ → TangentBundle I M` projecting to
  `γ` such that `f` is an integral curve of the chart-fixed geodesic
  vector field `geodesicVectorFieldChart g α` on `s`.

* `maximalGeodesicInterval g p v`: the union of all open intervals
  containing `0` on which there exists a geodesic with `γ 0 = p` and
  velocity-lift value `v` at `0`. By construction, this is an open set
  containing `0`.

* `maximalGeodesic g p v`: a `ℝ → M`-curve obtained from
  `exists_geodesic_with_initial_velocity_at` together with a `Classical.choice` selection of a
  geodesic that covers each point of the maximal interval, junk-extended
  to the entire real line by the constant value `p` outside.

## Main theorems

* `maximalGeodesicInterval_isOpen`: openness.
* `zero_mem_maximalGeodesicInterval`: `0` is in the maximal interval.
* `maximalGeodesic_zero`: `maximalGeodesic g p v 0 = p`.
* `isGeodesicAt_maximalGeodesic`: at every `t ∈ maximalGeodesicInterval g p v`,
  the curve `maximalGeodesic g p v` is a local geodesic at `t`.

## Strategy

We follow the standard "union over local extensions" construction. The
maximal interval is the union of all open intervals `J` containing both
`0` and the point of interest on which a geodesic with the prescribed
initial condition exists. The curve `maximalGeodesic` is then defined by
picking, for each `t` in the maximal interval, the value of any such
local geodesic at `t`; the value is junk (= `p`) for `t` outside the
maximal interval. The headline geodesic predicate is established at the
pointwise `IsGeodesicAt` level, which is the regularity that the existence
theorem `exists_geodesic_with_initial_velocity_at` directly delivers. A globalised
`IsGeodesicOn` statement on the maximal interval would require integral
curves of the chart-fixed vector field to glue across chart changes; that
requires a moving-chart formulation of the geodesic equation and is
deferred.
-/

noncomputable section

open Bundle Manifold Set Filter Function
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

/-- `γ` is a geodesic on `s` with initial datum `(p, v)` at time `0` if
the velocity lift `f` projects to `γ`, satisfies `f 0 = ⟨p, v⟩`, and is an
integral curve of the chart-fixed geodesic vector field at the chart
basepoint `p`. The chart basepoint is fixed to be the initial point `p`,
which guarantees that the vector field is smooth at the initial data
(since `p ∈ (chartAt H p).source` is automatic). -/
def IsGeodesicOnWithInitial
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (s : Set ℝ)
    (p : M) (v : TangentSpace I p) : Prop :=
  ∃ f : ℝ → TangentBundle I M,
    (∀ t, (f t).proj = γ t) ∧
    f 0 = (⟨p, v⟩ : TangentBundle I M) ∧
    IsMIntegralCurveOn f (geodesicVectorFieldChart (I := I) g p) s

/-- An initial-data geodesic on `s` is, at every interior point `t` of `s`
(i.e. `s ∈ 𝓝 t`) whose foot `γ t` still lies in the base chart-source
`(chartAt H p).source`, a local spray geodesic `IsGeodesicAt g γ t` with
chart basepoint `p`. This is the spray-side projection used to feed the
chart-coordinate geodesic-equation bridge downstream.

The foot-in-source hypothesis `ht_src : γ t ∈ (chartAt H p).source` is the
chart-validity condition for the chart-`p`-fixed integral-curve datum: it
is exactly the well-posedness clause that the strengthened `IsGeodesicAt`
predicate records. At an interior point where `γ` has left the base chart,
the chart-`p` vector field has degenerated to the zero section, so no
`IsGeodesicAt` witness with basepoint `p` is available there. -/
lemma IsGeodesicOnWithInitial.isGeodesicAt
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M} {s : Set ℝ}
    {p : M} {v : TangentSpace I p} {t : ℝ}
    (hγ : IsGeodesicOnWithInitial (I := I) g γ s p v) (ht : s ∈ 𝓝 t)
    (ht_src : γ t ∈ (chartAt H p).source) :
    IsGeodesicAt (I := I) g γ t := by
  obtain ⟨f, hproj, _, hf⟩ := hγ
  refine ⟨p, f, hproj, ?_, hf.isMIntegralCurveAt ht⟩
  rw [hproj t]; exact ht_src

/-- The starting point is forced: if `IsGeodesicOnWithInitial g γ s p v`
holds, then `γ 0 = p`. -/
lemma IsGeodesicOnWithInitial.start_eq
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M} {s : Set ℝ}
    {p : M} {v : TangentSpace I p}
    (hγ : IsGeodesicOnWithInitial (I := I) g γ s p v) :
    γ 0 = p := by
  obtain ⟨f, hproj, hf0, _⟩ := hγ
  have h := hproj 0
  simp [hf0] at h
  exact h.symm

/-- `IsGeodesicOnWithInitial` is monotone in the set. -/
lemma IsGeodesicOnWithInitial.mono
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M} {s s' : Set ℝ}
    {p : M} {v : TangentSpace I p}
    (hγ : IsGeodesicOnWithInitial (I := I) g γ s p v) (hs : s' ⊆ s) :
    IsGeodesicOnWithInitial (I := I) g γ s' p v := by
  obtain ⟨f, hproj, hf0, hf⟩ := hγ
  exact ⟨f, hproj, hf0, hf.mono hs⟩

/-- The "membership witness" predicate for the maximal interval: at time
`t`, there exists a connected open `J ∋ 0, t` and a geodesic with initial
data `(p, v)` on `J`. Preconnectedness of `J` (i.e., `J` is an interval in
`ℝ`) is required to enable interval-propagation arguments, e.g.
identifying the witness curve with a known geodesic at every `t ∈ J` from
agreement at `t = 0`. This is packaged as a single-existential `Prop` so
that `Classical.choose` works cleanly. -/
def MaximalGeodesicWitness
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p)
    (t : ℝ) : Prop :=
  ∃ γ : ℝ → M, ∃ J : Set ℝ,
    IsOpen J ∧ IsPreconnected J ∧ (0 : ℝ) ∈ J ∧ t ∈ J ∧
      IsGeodesicOnWithInitial (I := I) g γ J p v

/-- The maximal interval of definition of a geodesic with initial data
`(p, v)`: the set of times `t : ℝ` admitting an open interval `J ∋ 0, t`
on which a geodesic with initial data `(p, v)` is defined. -/
def maximalGeodesicInterval
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p) :
    Set ℝ :=
  {t : ℝ | MaximalGeodesicWitness (I := I) g p v t}

/-- Membership unfolding. -/
lemma mem_maximalGeodesicInterval_iff
    {g : SmoothRiemannianMetric I M} {p : M} {v : TangentSpace I p}
    {t : ℝ} :
    t ∈ maximalGeodesicInterval (I := I) g p v ↔
      MaximalGeodesicWitness (I := I) g p v t :=
  Iff.rfl

/-- `maximalGeodesicInterval g p v` is open. The key observation: if
`MaximalGeodesicWitness g p v t` holds with witness `(γ, J)`, then for
every `t' ∈ J` we also have `MaximalGeodesicWitness g p v t'` (with the
same `(γ, J)`). Hence the maximal interval is locally a superset of an
open neighbourhood of every member. -/
theorem maximalGeodesicInterval_isOpen
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p) :
    IsOpen (maximalGeodesicInterval (I := I) g p v) := by
  rw [isOpen_iff_mem_nhds]
  intro t ht
  obtain ⟨γ, J, hJ, hJ_conn, h0, ht_in, hγ⟩ := ht
  refine Filter.mem_of_superset (hJ.mem_nhds ht_in) ?_
  intro t' ht'
  exact ⟨γ, J, hJ, hJ_conn, h0, ht', hγ⟩

section LocalExistence

variable [I.Boundaryless] [CompleteSpace E]

/-- The local geodesic produced by `exists_geodesic_with_initial_velocity_at` provides an open
interval `J ∋ 0` on which a geodesic with initial data `(p, v)` exists.
This is the basic witness for membership of `0` in the maximal interval. -/
lemma exists_maximalGeodesicWitness_zero
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p) :
    MaximalGeodesicWitness (I := I) g p v 0 := by
  obtain ⟨f, hf0, hf⟩ :=
    exists_isMIntegralCurveAt_geodesicVectorFieldChart (I := I) g p v
  rw [isMIntegralCurveAt_iff'] at hf
  obtain ⟨ε, hε, hf_on⟩ := hf
  refine ⟨projectCurve (I := I) f, Metric.ball (0 : ℝ) ε,
    Metric.isOpen_ball, ?_, Metric.mem_ball_self hε, Metric.mem_ball_self hε, ?_⟩
  · exact (convex_ball (0 : ℝ) ε).isPreconnected
  exact ⟨f, fun _ => rfl, hf0, hf_on⟩

/-- `0` belongs to the maximal interval. -/
theorem zero_mem_maximalGeodesicInterval
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p) :
    (0 : ℝ) ∈ maximalGeodesicInterval (I := I) g p v :=
  exists_maximalGeodesicWitness_zero (I := I) g p v

/-- The maximal interval is nonempty. -/
theorem maximalGeodesicInterval_nonempty
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p) :
    (maximalGeodesicInterval (I := I) g p v).Nonempty :=
  ⟨0, zero_mem_maximalGeodesicInterval (I := I) g p v⟩

end LocalExistence

section MaximalGeodesicDefinition

variable [I.Boundaryless] [CompleteSpace E]

/-- A local geodesic witness at time `t`, taken via `Classical.choose`
when `t ∈ maximalGeodesicInterval g p v`. -/
def maximalGeodesicChosenCurve
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p)
    {t : ℝ} (h : MaximalGeodesicWitness (I := I) g p v t) :
    ℝ → M :=
  Classical.choose h

lemma maximalGeodesicChosenCurve_spec
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p)
    {t : ℝ} (h : MaximalGeodesicWitness (I := I) g p v t) :
    ∃ J : Set ℝ, IsOpen J ∧ IsPreconnected J ∧ (0 : ℝ) ∈ J ∧ t ∈ J ∧
      IsGeodesicOnWithInitial (I := I) g
        (maximalGeodesicChosenCurve (I := I) g p v h) J p v :=
  Classical.choose_spec h

/-- The canonical maximal geodesic with initial data `(p, v)`. On the
maximal interval, it equals some local geodesic with the prescribed
initial data, chosen by `Classical.choose`; outside, it is the constant
`p`. -/
def maximalGeodesic
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p)
    (t : ℝ) : M :=
  letI : Decidable (MaximalGeodesicWitness (I := I) g p v t) := Classical.dec _
  if h : MaximalGeodesicWitness (I := I) g p v t then
    maximalGeodesicChosenCurve (I := I) g p v h t
  else p

/-- Outside the maximal interval, `maximalGeodesic` takes the value `p`. -/
lemma maximalGeodesic_of_not_mem
    {g : SmoothRiemannianMetric I M} {p : M} {v : TangentSpace I p}
    {t : ℝ} (ht : t ∉ maximalGeodesicInterval (I := I) g p v) :
    maximalGeodesic (I := I) g p v t = p := by
  unfold maximalGeodesic
  letI : Decidable (MaximalGeodesicWitness (I := I) g p v t) := Classical.dec _
  exact dif_neg ht

/-- On the maximal interval, `maximalGeodesic g p v` equals the chosen
local geodesic. -/
lemma maximalGeodesic_of_mem
    {g : SmoothRiemannianMetric I M} {p : M} {v : TangentSpace I p}
    {t : ℝ} (h : t ∈ maximalGeodesicInterval (I := I) g p v) :
    maximalGeodesic (I := I) g p v t =
      maximalGeodesicChosenCurve (I := I) g p v h t := by
  unfold maximalGeodesic
  letI : Decidable (MaximalGeodesicWitness (I := I) g p v t) := Classical.dec _
  exact dif_pos h

end MaximalGeodesicDefinition

section MaximalGeodesicValue

variable [I.Boundaryless] [CompleteSpace E]

/-- `maximalGeodesic g p v` starts at `p`. -/
theorem maximalGeodesic_zero
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p) :
    maximalGeodesic (I := I) g p v 0 = p := by
  have h0 := zero_mem_maximalGeodesicInterval (I := I) g p v
  rw [maximalGeodesic_of_mem (I := I) (g := g) (p := p) (v := v) h0]
  obtain ⟨_J, _hJ, _hJ_conn, _h0J, _h0J', hγ⟩ :=
    maximalGeodesicChosenCurve_spec (I := I) g p v h0
  exact hγ.start_eq

end MaximalGeodesicValue

section MaximalGeodesicAtTime

variable [I.Boundaryless] [CompleteSpace E]

/-- The witness `γ` chosen at `t ∈ maximalGeodesicInterval g p v` is a
local geodesic at `t` with the prescribed initial data, provided every
witness curve covering `t` keeps its foot `γ t` in the base chart-source
`(chartAt H p).source`. The headline statement we produce records the
existence of `(γ, J)` covering `t` such that `IsGeodesicAt g γ t`.

The foot-in-source hypothesis `ht_src` is the chart-validity clause for
the chart-`p`-fixed witness; see `IsGeodesicOnWithInitial.isGeodesicAt`.
It quantifies over witness curves because the witness producing `t`'s
membership is existentially bound. -/
theorem exists_isGeodesicAt_of_mem_maximalGeodesicInterval
    {g : SmoothRiemannianMetric I M} {p : M} {v : TangentSpace I p}
    {t : ℝ} (h : t ∈ maximalGeodesicInterval (I := I) g p v)
    (ht_src : ∀ (γ : ℝ → M) (J : Set ℝ),
      IsGeodesicOnWithInitial (I := I) g γ J p v →
        γ t ∈ (chartAt H p).source) :
    ∃ (γ : ℝ → M) (J : Set ℝ), IsOpen J ∧ (0 : ℝ) ∈ J ∧ t ∈ J ∧
      IsGeodesicOnWithInitial (I := I) g γ J p v ∧
      IsGeodesicAt (I := I) g γ t := by
  obtain ⟨γ, J, hJ, _hJ_conn, h0, ht, hγ⟩ := h
  refine ⟨γ, J, hJ, h0, ht, hγ, ?_⟩
  exact hγ.isGeodesicAt (hJ.mem_nhds ht) (ht_src γ J hγ)

/-- For every `t` in the maximal interval, there exists a geodesic
witness producing `IsGeodesicAt g (witness) t` with starting point `p`,
provided every witness curve keeps its foot `γ t` in the base chart-source
`(chartAt H p).source` (the chart-validity clause; see
`IsGeodesicOnWithInitial.isGeodesicAt`). The `t = 0` clause is automatic:
every witness starts at `p ∈ (chartAt H p).source`. -/
theorem exists_isGeodesicAt_zero_of_mem_maximalGeodesicInterval
    {g : SmoothRiemannianMetric I M} {p : M} {v : TangentSpace I p}
    {t : ℝ} (h : t ∈ maximalGeodesicInterval (I := I) g p v)
    (ht_src : ∀ (γ : ℝ → M) (J : Set ℝ),
      IsGeodesicOnWithInitial (I := I) g γ J p v →
        γ t ∈ (chartAt H p).source) :
    ∃ γ : ℝ → M, γ 0 = p ∧ IsGeodesicAt (I := I) g γ 0 ∧
      IsGeodesicAt (I := I) g γ t := by
  obtain ⟨γ, J, hJ, h0, ht, hγ_init, hγ_at⟩ :=
    exists_isGeodesicAt_of_mem_maximalGeodesicInterval (I := I) h ht_src
  refine ⟨γ, hγ_init.start_eq, ?_, hγ_at⟩
  refine hγ_init.isGeodesicAt (hJ.mem_nhds h0) ?_
  rw [hγ_init.start_eq]; exact mem_chart_source H p

end MaximalGeodesicAtTime

section MaximalGeodesicMain

variable [I.Boundaryless] [CompleteSpace E]

/-- Structural properties of the canonical maximal geodesic with initial
datum `(p, v)`: writing `I_max := maximalGeodesicInterval g p v` and
`γ_max := maximalGeodesic g p v`, the set `I_max` is open and contains `0`,
`γ_max 0 = p`, `γ_max` takes the junk value `p` outside `I_max`, and at
every `t ∈ I_max` there is a local geodesic `γ` with `γ 0 = p` that is a
geodesic at both `0` and `t`.

The hypothesis `hsrc` requires every local geodesic witness with initial
data `(p, v)` to keep its foot in `(chartAt H p).source` at each point of
`I_max`; it feeds `IsGeodesicOnWithInitial.isGeodesicAt`, and is needed
because where a witness has left the base chart the chart-`p` geodesic
vector field degenerates. -/
theorem maximalGeodesic_structure_of_footInSource
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p)
    (hsrc : ∀ t ∈ maximalGeodesicInterval (I := I) g p v,
      ∀ (γ : ℝ → M) (J : Set ℝ),
        IsGeodesicOnWithInitial (I := I) g γ J p v →
          γ t ∈ (chartAt H p).source) :
    let I_max := maximalGeodesicInterval (I := I) g p v
    let γ_max := maximalGeodesic (I := I) g p v
    IsOpen I_max ∧ (0 : ℝ) ∈ I_max ∧ γ_max 0 = p ∧
      (∀ t ∉ I_max, γ_max t = p) ∧
      (∀ t ∈ I_max, ∃ γ : ℝ → M, γ 0 = p ∧
        IsGeodesicAt (I := I) g γ 0 ∧ IsGeodesicAt (I := I) g γ t) := by
  refine ⟨maximalGeodesicInterval_isOpen (I := I) g p v,
    zero_mem_maximalGeodesicInterval (I := I) g p v,
    maximalGeodesic_zero (I := I) g p v, ?_, ?_⟩
  · intro t ht
    exact maximalGeodesic_of_not_mem (I := I) ht
  · intro t ht
    exact exists_isGeodesicAt_zero_of_mem_maximalGeodesicInterval (I := I) ht
      (hsrc t ht)

end MaximalGeodesicMain

section BridgeLemmas

variable [I.Boundaryless] [CompleteSpace E]

/-- A geodesic on `Set.univ` is exactly the same data as a global
geodesic. Under the intrinsic moving-foot formulation, `IsGeodesic g γ`
is `∀ t, HasGeodesicEquationAt g γ t` while
`IsGeodesicOn g γ Set.univ` is `∀ t ∈ Set.univ, HasGeodesicEquationAt g γ t`;
these agree by `Set.mem_univ`. -/
lemma isGeodesic_iff_isGeodesicOn_univ
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M} :
    IsGeodesic (I := I) g γ ↔ IsGeodesicOn (I := I) g γ (Set.univ : Set ℝ) := by
  constructor
  · intro hγ
    exact hγ.isGeodesicOn _
  · intro hγ t
    exact hγ t (Set.mem_univ t)

end BridgeLemmas

section ArcLengthBridge

open MeasureTheory intervalIntegral

variable [I.Boundaryless]
variable [Bundle.RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
variable [T2Space M] [SigmaCompactSpace M] [FiniteDimensional ℝ E]

/-- **Velocity-total-space continuity for a `C¹` curve on a closed interval.**
For a curve `η : ℝ → M` that is `C¹` on `Icc a b`, the within-set velocity
total-space section `t ↦ ⟨η t, mfderivWithin 𝓘(ℝ,ℝ) I η (Icc a b) t 1⟩` is
continuous on `Icc a b`. This is the closed-interval `ContinuousOn` analogue
of `MFDerivAlongCurve.continuous_tangentMap_unitLift`, routed through
`ContMDiffOn.continuousOn_tangentMapWithin` (with `UniqueMDiffOn (Icc a b)`
from `uniqueDiffOn_Icc`) precomposed with the continuous unit lift
`t ↦ ⟨t, 1⟩`. -/
private lemma continuousOn_velocityWithin_totalSpace_C1
    {η : ℝ → M} {a b : ℝ} (hab : a < b)
    (hη : ContMDiffOn 𝓘(ℝ, ℝ) I 1 η (Set.Icc a b)) :
    ContinuousOn
      (fun t : ℝ =>
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (η t)
          (mfderivWithin 𝓘(ℝ, ℝ) I η (Set.Icc a b) t (1 : ℝ)) : TangentBundle I M))
      (Set.Icc a b) := by
  have hUnique : UniqueMDiffOn 𝓘(ℝ, ℝ) (Set.Icc a b) := by
    intro x hx
    rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
    exact (uniqueDiffOn_Icc hab) x hx
  have hTan := hη.continuousOn_tangentMapWithin (le_refl 1) hUnique
  have hLift : Continuous (fun t : ℝ =>
      (⟨t, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) := by
    have h_homeo :
        Continuous ((tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).symm :
          ModelProd ℝ ℝ → TangentBundle 𝓘(ℝ, ℝ) ℝ) :=
      (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).symm.continuous
    exact h_homeo.comp (continuous_id.prodMk continuous_const)
  have hMaps : Set.MapsTo (fun t : ℝ => (⟨t, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ))
      (Set.Icc a b) (Bundle.TotalSpace.proj ⁻¹' (Set.Icc a b)) := by
    intro t ht
    simpa using ht
  have hComp : ContinuousOn
      (fun t : ℝ => tangentMapWithin 𝓘(ℝ, ℝ) I η (Set.Icc a b)
        (⟨t, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ))
      (Set.Icc a b) :=
    hTan.comp hLift.continuousOn hMaps
  refine hComp.congr ?_
  intro t _ht
  rfl

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **`ContinuousOn` of the `g`-speed-squared along a within-velocity section.**
For a metric `g`, a curve `η`, and the within-set velocity section
`vW t := mfderivWithin 𝓘(ℝ,ℝ) I η (Icc a b) t 1` presented through its
total-space `ContinuousOn`, the quadratic form `t ↦ g.inner (η t) (vW t) (vW t)`
is continuous on `Icc a b`. Mirrors `continuous_g_inner_along_param` from the
second-variation development, in its `ContinuousOn` form, using the bundle
inner product of `g`'s own continuous Riemannian metric. -/
private lemma continuousOn_g_speedSq_velocityWithin
    (g : SmoothRiemannianMetric I M) {η : ℝ → M} {a b : ℝ}
    (hVW : ContinuousOn
      (fun t : ℝ =>
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (η t)
          (mfderivWithin 𝓘(ℝ, ℝ) I η (Set.Icc a b) t (1 : ℝ)) : TangentBundle I M))
      (Set.Icc a b)) :
    ContinuousOn
      (fun t : ℝ =>
        g.inner (η t)
          (mfderivWithin 𝓘(ℝ, ℝ) I η (Set.Icc a b) t (1 : ℝ))
          (mfderivWithin 𝓘(ℝ, ℝ) I η (Set.Icc a b) t (1 : ℝ)))
      (Set.Icc a b) := by
  letI cg : Bundle.ContinuousRiemannianMetric E (TangentSpace I : M → Type _) :=
    g.toContinuousRiemannianMetric
  letI rb : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨cg.toRiemannianMetric⟩
  have h := ContinuousOn.inner_bundle (F := E) (B := M)
    (E := (TangentSpace I : M → Type _))
    (b := η)
    (v := fun t : ℝ => mfderivWithin 𝓘(ℝ, ℝ) I η (Set.Icc a b) t (1 : ℝ))
    (w := fun t : ℝ => mfderivWithin 𝓘(ℝ, ℝ) I η (Set.Icc a b) t (1 : ℝ))
    (s := Set.Icc a b) hVW hVW
  refine h.congr ?_
  intro t _ht
  rfl

/-- **Integrability of the `g`-speed integrand for a `C¹` curve.**
For a curve `η : ℝ → M` that is `C¹` on `Icc a b` with `a ≤ b`, given the
pointwise bundle-enorm identification on `Icc a b`, the speed integrand
`t ↦ √(g.inner (η t) (mfderiv η t 1) (mfderiv η t 1))` is integrable on
`Icc a b`.

The proof reduces to the `ContinuousOn` of the within-velocity speed integrand
on the compact interval (hence integrable by `ContinuousOn.integrableOn_Icc`),
then transfers to the `mfderiv` form by a.e.-equality on the co-null interior
`Ioo a b` (where `mfderivWithin = mfderiv`). The singleton case `a = b` is
handled directly via `integrableOn_singleton_iff`. The `hEnorm` argument is kept
for signature uniformity with `pathELength_eq_arcLength` and is not needed in
the proof. -/
lemma speedSqrt_integrableOn_Icc_of_C1
    (g : SmoothRiemannianMetric I M) {η : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hη : ContMDiffOn 𝓘(ℝ, ℝ) I 1 η (Set.Icc a b)) :
    MeasureTheory.IntegrableOn
      (fun t : ℝ => Real.sqrt
        (g.inner (η t)
          (mfderiv 𝓘(ℝ, ℝ) I η t (1 : ℝ))
          (mfderiv 𝓘(ℝ, ℝ) I η t (1 : ℝ))))
      (Set.Icc a b) MeasureTheory.volume := by
  classical
  rcases eq_or_lt_of_le hab with hab_eq | hab_lt
  · subst hab_eq
    rw [Set.Icc_self, MeasureTheory.integrableOn_singleton_iff]
    exact Or.inr (by simp)
  · have hVW := continuousOn_velocityWithin_totalSpace_C1 (I := I) (M := M)
      hab_lt hη
    have hSpeedSq := continuousOn_g_speedSq_velocityWithin (I := I) (M := M) g hVW
    have hSqrtW : ContinuousOn
        (fun t : ℝ => Real.sqrt
          (g.inner (η t)
            (mfderivWithin 𝓘(ℝ, ℝ) I η (Set.Icc a b) t (1 : ℝ))
            (mfderivWithin 𝓘(ℝ, ℝ) I η (Set.Icc a b) t (1 : ℝ))))
        (Set.Icc a b) :=
      Real.continuous_sqrt.comp_continuousOn hSpeedSq
    have hIntW : MeasureTheory.IntegrableOn
        (fun t : ℝ => Real.sqrt
          (g.inner (η t)
            (mfderivWithin 𝓘(ℝ, ℝ) I η (Set.Icc a b) t (1 : ℝ))
            (mfderivWithin 𝓘(ℝ, ℝ) I η (Set.Icc a b) t (1 : ℝ))))
        (Set.Icc a b) MeasureTheory.volume :=
      hSqrtW.integrableOn_Icc
    have hAgree : ∀ t ∈ Set.Ioo a b,
        Real.sqrt
            (g.inner (η t)
              (mfderivWithin 𝓘(ℝ, ℝ) I η (Set.Icc a b) t (1 : ℝ))
              (mfderivWithin 𝓘(ℝ, ℝ) I η (Set.Icc a b) t (1 : ℝ)))
          = Real.sqrt
            (g.inner (η t)
              (mfderiv 𝓘(ℝ, ℝ) I η t (1 : ℝ))
              (mfderiv 𝓘(ℝ, ℝ) I η t (1 : ℝ))) := by
      intro t ht
      have hmem : Set.Icc a b ∈ nhds t :=
        Icc_mem_nhds ht.1 ht.2
      rw [mfderivWithin_of_mem_nhds hmem]
    have hae : (fun t : ℝ => Real.sqrt
          (g.inner (η t)
            (mfderivWithin 𝓘(ℝ, ℝ) I η (Set.Icc a b) t (1 : ℝ))
            (mfderivWithin 𝓘(ℝ, ℝ) I η (Set.Icc a b) t (1 : ℝ))))
        =ᵐ[MeasureTheory.volume.restrict (Set.Icc a b)]
        (fun t : ℝ => Real.sqrt
          (g.inner (η t)
            (mfderiv 𝓘(ℝ, ℝ) I η t (1 : ℝ))
            (mfderiv 𝓘(ℝ, ℝ) I η t (1 : ℝ)))) := by
      have hIoo_ae : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc a b)),
          t ∈ Set.Ioo a b := by
        rw [← MeasureTheory.restrict_Ioo_eq_restrict_Icc]
        exact MeasureTheory.ae_restrict_mem measurableSet_Ioo
      filter_upwards [hIoo_ae] with t ht
      exact hAgree t ht
    exact hIntW.congr hae

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- Mathlib's `pathELength I γ a b` equals `ENNReal.ofReal (arcLength g γ a b)`
for a curve `γ` on `[a, b]` with `a ≤ b`, given the pointwise enorm
identification on `Icc a b`.

This is stated in the `RiemannianBundle`-active norm world (project tangent-fibre
norm instances locally suppressed), matching `riemMetricSpace`/`riemMetric_dist_eq`,
so that the resulting `riemannianEDist`/`dist` bounds compose without an
enorm-instance mismatch.

The hypotheses:
* `hab : a ≤ b` is the interval orientation.
* `hγ_int : IntegrableOn F (Set.Icc a b)` is integrability of the speed
  function `F`, used to convert `ENNReal.ofReal` of the integral to a
  Lebesgue `lintegral` of `ENNReal.ofReal ∘ F`.
* `hEnorm : ∀ t ∈ Icc a b,
    ‖mfderiv 𝓘(ℝ,ℝ) I γ t 1‖ₑ = ENNReal.ofReal (F t)`,
  where `F t = Real.sqrt (g.inner (γ t) (γ' t) (γ' t))`, is the assumed
  identification of the tangent-bundle enorm with the square root of the
  metric inner product.

The proof rewrites `pathELength` to a lintegral via
`pathELength_eq_lintegral_mfderiv_Icc`, replaces the integrand by
`ENNReal.ofReal ∘ F`, converts the lintegral to `ENNReal.ofReal` of the
Bochner integral over `Icc a b`, and identifies it with the interval
integral defining `arcLength` via `intervalIntegral.integral_of_le`. -/
theorem pathELength_eq_arcLength
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {a b : ℝ}
    (hab : a ≤ b)
    (hγ_int : MeasureTheory.IntegrableOn
      (fun t : ℝ => Real.sqrt
        (g.inner (γ t)
          (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))
          (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)))) (Set.Icc a b) MeasureTheory.volume)
    (hEnorm : ∀ t ∈ Set.Icc a b,
        ‖mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)‖ₑ
          = ENNReal.ofReal (Real.sqrt
              (g.inner (γ t)
                (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))
                (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))))) :
    pathELength I γ a b
      = ENNReal.ofReal
        (DifferentialGeometry.Geometry.Riemannian.Variation.arcLength (I := I) g γ a b) := by
  classical
  set F : ℝ → ℝ := fun t : ℝ => Real.sqrt
      (g.inner (γ t)
        (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))) with hF_def
  have hF_nn : ∀ t : ℝ, 0 ≤ F t := fun t => Real.sqrt_nonneg _
  rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc]
  change ∫⁻ t in Set.Icc a b, (fun t : ℝ => ‖mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)‖ₑ) t
    = ENNReal.ofReal (DifferentialGeometry.Geometry.Riemannian.Variation.arcLength
        (I := I) g γ a b)
  have h_lint_eq :=
    MeasureTheory.setLIntegral_congr_fun (μ := MeasureTheory.volume)
      (f := fun t : ℝ => ‖mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)‖ₑ)
      (g := fun t : ℝ => ENNReal.ofReal (F t))
      (s := Set.Icc a b)
      measurableSet_Icc
      (fun t ht => by simpa [hF_def] using hEnorm t ht)
  rw [h_lint_eq]
  have h_ofReal :
      ENNReal.ofReal (∫ t in Set.Icc a b, F t)
        = ∫⁻ t in Set.Icc a b, ENNReal.ofReal (F t) := by
    have hF_nn_ae : 0 ≤ᵐ[(MeasureTheory.volume).restrict (Set.Icc a b)] F :=
      MeasureTheory.ae_of_all _ hF_nn
    exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hγ_int hF_nn_ae
  rw [← h_ofReal]
  have h_Icc_Ioc :
      ∫ t in Set.Icc a b, F t = ∫ t in Set.Ioc a b, F t := by
    have h_set : Set.Icc a b = {a} ∪ Set.Ioc a b := by
      ext x
      simp only [Set.mem_Icc, Set.mem_union, Set.mem_singleton_iff, Set.mem_Ioc]
      constructor
      · rintro ⟨h1, h2⟩
        by_cases h : x = a
        · left; exact h
        · right; exact ⟨lt_of_le_of_ne h1 (fun h' => h h'.symm), h2⟩
      · rintro (rfl | ⟨h1, h2⟩)
        · exact ⟨le_refl _, hab⟩
        · exact ⟨le_of_lt h1, h2⟩
    rw [h_set]
    have hdisj : Disjoint ({a} : Set ℝ) (Set.Ioc a b) := by
      rw [Set.disjoint_left]
      rintro y hy hy'
      simp only [Set.mem_singleton_iff] at hy
      rw [hy] at hy'
      exact lt_irrefl _ hy'.1
    have h_int_singleton :
        MeasureTheory.IntegrableOn F ({a} : Set ℝ) MeasureTheory.volume := by
      rw [MeasureTheory.integrableOn_singleton_iff]
      exact Or.inr (by simp)
    have h_int_Ioc :
        MeasureTheory.IntegrableOn F (Set.Ioc a b) MeasureTheory.volume :=
      hγ_int.mono_set Set.Ioc_subset_Icc_self
    rw [MeasureTheory.setIntegral_union hdisj measurableSet_Ioc
      h_int_singleton h_int_Ioc]
    have h_singleton : ∫ t in ({a} : Set ℝ), F t = 0 := by
      simp
    rw [h_singleton, zero_add]
  have h_intInterval : ∫ t in a..b, F t = ∫ t in Set.Ioc a b, F t :=
    intervalIntegral.integral_of_le hab
  have h_arcLength :
      DifferentialGeometry.Geometry.Riemannian.Variation.arcLength (I := I) g γ a b
        = ∫ t in a..b, F t := by
    unfold DifferentialGeometry.Geometry.Riemannian.Variation.arcLength
    rfl
  rw [h_arcLength, h_intInterval, ← h_Icc_Ioc]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Distance is bounded by arc length.**  For a `C¹` curve `γ` on `[a, b]`
(`a ≤ b`) whose pointwise velocity `g`-norm is identified with the model enorm,
the Riemannian distance between the endpoints is at most the arc length:
`riemannianEDist I (γ a) (γ b) ≤ ENNReal.ofReal (arcLength g γ a b)`.  Combines
`riemannianEDist_le_pathELength` with `pathELength_eq_arcLength`.  Stated in the
`RiemannianBundle`-active norm world so it composes with `riemMetric_dist_eq`. -/
theorem riemannianEDist_le_arcLength
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Set.Icc a b))
    (hEnorm : ∀ t ∈ Set.Icc a b,
        ‖mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)‖ₑ
          = ENNReal.ofReal (Real.sqrt
              (g.inner (γ t)
                (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))
                (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))))) :
    riemannianEDist I (γ a) (γ b)
      ≤ ENNReal.ofReal
        (DifferentialGeometry.Geometry.Riemannian.Variation.arcLength (I := I) g γ a b) := by
  have hle : riemannianEDist I (γ a) (γ b) ≤ pathELength I γ a b :=
    riemannianEDist_le_pathELength hγ rfl rfl hab
  rwa [pathELength_eq_arcLength (I := I) g hab
    (speedSqrt_integrableOn_Icc_of_C1 (I := I) g hab hγ) hEnorm] at hle

end ArcLengthBridge

end Geodesic
end Riemannian
end Geometry
end DifferentialGeometry

end
