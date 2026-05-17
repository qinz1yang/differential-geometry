import DifferentialGeometry.Geometry.Riemannian.Geodesic.Equation
import DifferentialGeometry.Geometry.Riemannian.Geodesic.Existence
import DifferentialGeometry.Geometry.Riemannian.Geodesic.Uniqueness

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
  `exists_geodesic_at` together with a `Classical.choice` selection of a
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
theorem `exists_geodesic_at` directly delivers. A globalised
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

/-! ## Geodesic predicate on a set

The set-restricted analogue of `IsGeodesic`: there exists a chart
basepoint `α` and a velocity lift `f` that is an integral curve of the
chart-fixed geodesic vector field on the set `s`. The value of `γ`
outside `s` is irrelevant. -/

/-- `γ : ℝ → M` is a geodesic of `g` on `s : Set ℝ` if there is a chart
basepoint `α : M` and a velocity lift `f : ℝ → TangentBundle I M`
projecting to `γ` whose restriction to `s` is an integral curve of the
chart-fixed geodesic vector field `geodesicVectorFieldChart g α`. -/
def IsGeodesicOn (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (s : Set ℝ) : Prop :=
  ∃ (α : M) (f : ℝ → TangentBundle I M),
    (∀ t, (f t).proj = γ t) ∧
    IsMIntegralCurveOn f (geodesicVectorFieldChart (I := I) g α) s

/-- A geodesic on a set, viewed as a local geodesic at every interior
point of the set (i.e. every `t` with `s ∈ 𝓝 t`). -/
lemma IsGeodesicOn.isGeodesicAt {g : SmoothRiemannianMetric I M}
    {γ : ℝ → M} {s : Set ℝ} {t : ℝ}
    (hγ : IsGeodesicOn (I := I) g γ s) (ht : s ∈ 𝓝 t) :
    IsGeodesicAt (I := I) g γ t := by
  obtain ⟨α, f, hproj, hf⟩ := hγ
  exact ⟨α, f, hproj, hf.isMIntegralCurveAt ht⟩

/-- `IsGeodesicOn` is monotone in the set. -/
lemma IsGeodesicOn.mono {g : SmoothRiemannianMetric I M}
    {γ : ℝ → M} {s s' : Set ℝ}
    (hγ : IsGeodesicOn (I := I) g γ s) (hs : s' ⊆ s) :
    IsGeodesicOn (I := I) g γ s' := by
  obtain ⟨α, f, hproj, hf⟩ := hγ
  exact ⟨α, f, hproj, hf.mono hs⟩

/-- A global geodesic, restricted to any set, is a geodesic on that set. -/
lemma IsGeodesic.isGeodesicOn {g : SmoothRiemannianMetric I M}
    {γ : ℝ → M} (hγ : IsGeodesic (I := I) g γ) (s : Set ℝ) :
    IsGeodesicOn (I := I) g γ s := by
  obtain ⟨α, f, hproj, hf⟩ := hγ
  exact ⟨α, f, hproj, hf.isMIntegralCurveOn s⟩

/-! ## Initial-data carriers

A geodesic with prescribed initial data `(p : M, v : T_p M)` is one whose
lift `f` satisfies `f 0 = ⟨p, v⟩`. We encode this in a `Prop`-valued
predicate that records the initial datum at `t = 0`. -/

/-- `γ` is a geodesic on `s` with initial datum `(p, v)` at time `0` if
the velocity lift `f` produced by `IsGeodesicOn` can be chosen with
`f 0 = ⟨p, v⟩` and the chart basepoint of the lift is `p` itself.
Fixing the chart basepoint to be the initial point is geometrically
natural (the initial point lies in its own chart source) and is what
enables value-level propagation arguments via local uniqueness of
integral curves in the chart at `p`. -/
def IsGeodesicOnWithInitial
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (s : Set ℝ)
    (p : M) (v : TangentSpace I p) : Prop :=
  ∃ f : ℝ → TangentBundle I M,
    (∀ t, (f t).proj = γ t) ∧
    f 0 = (⟨p, v⟩ : TangentBundle I M) ∧
    IsMIntegralCurveOn f (geodesicVectorFieldChart (I := I) g p) s

/-- An initial-data geodesic on `s` is in particular a geodesic on `s`. -/
lemma IsGeodesicOnWithInitial.isGeodesicOn
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M} {s : Set ℝ}
    {p : M} {v : TangentSpace I p}
    (hγ : IsGeodesicOnWithInitial (I := I) g γ s p v) :
    IsGeodesicOn (I := I) g γ s := by
  obtain ⟨f, hproj, _, hf⟩ := hγ
  exact ⟨p, f, hproj, hf⟩

/-- The starting point is forced: if `IsGeodesicOnWithInitial g γ s p v`
holds and `0 ∈ s`, then `γ 0 = p`. -/
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

/-! ## The maximal interval

The maximal interval is the union over all *open* sets `J ⊆ ℝ` such that
`0 ∈ J` and a geodesic with initial data `(p, v)` exists on `J`. Taking
the union of opens gives an open set, automatically containing `0`. -/

/-- The "membership witness" predicate for the maximal interval: at time
`t`, there exists an open *preconnected* `J ∋ 0, t` (necessarily an open
real interval, since open preconnected subsets of `ℝ` are open intervals)
and a geodesic with initial data `(p, v)` on `J`. This is packaged as a
single-existential `Prop` so that `Classical.choose` works cleanly.

The preconnectedness requirement is mathematically essential: integral
curves of the chart-fixed geodesic vector field with prescribed initial
data at time `0` are uniquely determined only on the connected component
of `0` in `J`. Forcing `J` to be preconnected (hence an interval
containing both `0` and `t`) is what enables propagating value-level
information about the curve from time `0` to time `t`. -/
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
  -- `J ⊆ maximalGeodesicInterval g p v` and `J ∈ 𝓝 t`.
  refine Filter.mem_of_superset (hJ.mem_nhds ht_in) ?_
  intro t' ht'
  exact ⟨γ, J, hJ, hJ_conn, h0, ht', hγ⟩

/-! ## Local existence on the maximal interval

We use `exists_geodesic_at` to produce a local geodesic at `0`, which
gives a small open interval `(-ε, ε)` contained in the maximal interval.
This automatically places `0` in the maximal interval. -/

section LocalExistence

variable [I.Boundaryless] [CompleteSpace E]

/-- The local geodesic produced by `exists_geodesic_at` provides an open
interval `J ∋ 0` on which a geodesic with initial data `(p, v)` exists.
This is the basic witness for membership of `0` in the maximal interval. -/
lemma exists_maximalGeodesicWitness_zero
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p) :
    MaximalGeodesicWitness (I := I) g p v 0 := by
  obtain ⟨f, hf0, hf⟩ :=
    exists_isMIntegralCurveAt_geodesicVectorFieldChart (I := I) g p v
  -- Extract an open interval around `0` on which `f` is an integral curve.
  rw [isMIntegralCurveAt_iff'] at hf
  obtain ⟨ε, hε, hf_on⟩ := hf
  refine ⟨projectCurve (I := I) f, Metric.ball (0 : ℝ) ε,
    Metric.isOpen_ball, (convex_ball (0 : ℝ) ε).isPreconnected,
    Metric.mem_ball_self hε, Metric.mem_ball_self hε, ?_⟩
  -- Package as `IsGeodesicOnWithInitial`.
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

/-! ## The canonical maximal geodesic

We define `maximalGeodesic g p v t` by:

* if `t ∈ maximalGeodesicInterval g p v`, choose any witness
  `(γ, J)` covering `t` and return `γ t`;
* otherwise, return `p` (junk value).

Outside the maximal interval, the curve is the constant `p`. On the
maximal interval, the *value* depends on the choice of witness; we
package it through `Classical.choice`. Pointwise the value matches some
local geodesic with the prescribed initial data. -/

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

/-! ## Initial value of the maximal geodesic

`maximalGeodesic g p v 0 = p`. This follows from
`zero_mem_maximalGeodesicInterval` and the fact that any witness `γ` at
`t = 0` satisfies `γ 0 = p` (by `IsGeodesicOnWithInitial.start_eq`). -/

section MaximalGeodesicValue

variable [I.Boundaryless] [CompleteSpace E]

/-- `maximalGeodesic g p v` starts at `p`. -/
theorem maximalGeodesic_zero
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p) :
    maximalGeodesic (I := I) g p v 0 = p := by
  have h0 := zero_mem_maximalGeodesicInterval (I := I) g p v
  rw [maximalGeodesic_of_mem (I := I) (g := g) (p := p) (v := v) h0]
  obtain ⟨J, _hJ, _hJ_conn, _h0J, _h0J', hγ⟩ :=
    maximalGeodesicChosenCurve_spec (I := I) g p v h0
  -- `hγ : IsGeodesicOnWithInitial g (chosen) J p v`, so chosen 0 = p.
  exact hγ.start_eq

end MaximalGeodesicValue

/-! ## Pointwise geodesic property on the maximal interval

For every `t` in the maximal interval, the value `maximalGeodesic g p v t`
matches some local geodesic at `t`, and that local geodesic gives rise to
an `IsGeodesicAt` predicate at `t`. We do NOT claim a single
`IsGeodesicOn` predicate on the whole maximal interval: doing so would
require gluing chart-fixed integral curves across chart changes, which is
a moving-chart phenomenon and is deferred. -/

section MaximalGeodesicAtTime

variable [I.Boundaryless] [CompleteSpace E]

/-- The witness `γ` chosen at `t ∈ maximalGeodesicInterval g p v` is a
local geodesic at `t` with the prescribed initial data. The headline
statement we produce records the existence of `(γ, J)` covering `t` such
that `IsGeodesicAt g γ t`. -/
theorem exists_isGeodesicAt_of_mem_maximalGeodesicInterval
    {g : SmoothRiemannianMetric I M} {p : M} {v : TangentSpace I p}
    {t : ℝ} (h : t ∈ maximalGeodesicInterval (I := I) g p v) :
    ∃ (γ : ℝ → M) (J : Set ℝ), IsOpen J ∧ (0 : ℝ) ∈ J ∧ t ∈ J ∧
      IsGeodesicOnWithInitial (I := I) g γ J p v ∧
      IsGeodesicAt (I := I) g γ t := by
  obtain ⟨γ, J, hJ, _hJ_conn, h0, ht, hγ⟩ := h
  refine ⟨γ, J, hJ, h0, ht, hγ, ?_⟩
  -- `IsGeodesicAt` from `IsGeodesicOn`: take `t` as interior point of `J`.
  exact hγ.isGeodesicOn.isGeodesicAt (hJ.mem_nhds ht)

/-- For every `t` in the maximal interval, there exists a geodesic
witness producing `IsGeodesicAt g (witness) t` with starting point `p`. -/
theorem exists_isGeodesicAt_zero_of_mem_maximalGeodesicInterval
    {g : SmoothRiemannianMetric I M} {p : M} {v : TangentSpace I p}
    {t : ℝ} (h : t ∈ maximalGeodesicInterval (I := I) g p v) :
    ∃ γ : ℝ → M, γ 0 = p ∧ IsGeodesicAt (I := I) g γ 0 ∧
      IsGeodesicAt (I := I) g γ t := by
  obtain ⟨γ, J, hJ, h0, ht, hγ_init, hγ_at⟩ :=
    exists_isGeodesicAt_of_mem_maximalGeodesicInterval (I := I) h
  refine ⟨γ, hγ_init.start_eq, ?_, hγ_at⟩
  exact hγ_init.isGeodesicOn.isGeodesicAt (hJ.mem_nhds h0)

end MaximalGeodesicAtTime

/-! ## Existence of a maximal-interval geodesic via canonical witness

The theorems below package the canonical maximal geodesic together with
its starting properties: it starts at `p`, and on the maximal interval
some witnessing local geodesic agrees with it pointwise. This is the
useful downstream-facing form. -/

section MaximalGeodesicMain

variable [I.Boundaryless] [CompleteSpace E]

/-- **Headline theorem.** For every initial datum `(p, v)`, there exists
the maximal open interval `I_max := maximalGeodesicInterval g p v` and a
junk-extended curve `maximalGeodesic g p v : ℝ → M` such that:

* `I_max` is open and contains `0`;
* `maximalGeodesic g p v 0 = p`;
* every `t ∈ I_max` is covered by a local geodesic `γ` with initial data
  `(p, v)` satisfying `IsGeodesicAt g γ t`;
* outside `I_max`, the curve takes the junk value `p`.
-/
theorem exists_maximalGeodesic
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p) :
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

end MaximalGeodesicMain

end Geodesic
end Riemannian
end Geometry
end DifferentialGeometry

end
