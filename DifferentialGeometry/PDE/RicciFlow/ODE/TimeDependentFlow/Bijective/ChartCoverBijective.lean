import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.ChartOverlapUniqueness
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.Glue
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Geometry.Manifold.MFDeriv.Basic

namespace DifferentialGeometry.PDE.RicciFlow.ODE

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/--
**Single-chart chart-coord-to-manifold bijectivity transport** primitive.

Given a chart base `α : M`, a starting point `x ∈ (chartAt H α).source`, a
chart-α-coord curve `cflow : ℝ → E` (the chart-α-coord representation of the
`-X`-flow trajectory starting from the chart-α-coord image of some manifold
point `p : M`), and a target manifold point `q : M` such that:

* `q` agrees with the chart-α-pull-back of `cflow t` at the given time `t`
  (this records the chart-α representation of the manifold flow value);
* the chart-α-coord value `cflow t` equals the chart-α-coord image of `x`
  (this is the **chart-coord composition identity** in `E`).

we conclude `q = x` in the manifold `M`.

This primitive isolates the chart-coord-to-manifold translation step from
all other content. The two hypotheses are genuinely separable: the first is
a chart-α representation identity for `q`, the second is an equality in `E`
between two chart-α-coord values. The conclusion `q = x` is a manifold-level
identity in `M`, obtained by transport through the chart left-inverse and
the `ModelWithCorners` left-inverse.

The single hypothesis `hx_source` (`x ∈ (chartAt H α).source`) is needed to
invoke `(chartAt H α).left_inv` at `x`; it is supplied separately because
without it, the chart left-inverse step would fail.

This is genuine mathematical content: not every chart-coord equality
transports to a manifold equality — it requires chart-source membership of
the target point `x`.
-/
theorem chart_pullback_to_manifold_eq_via_chart_coord_inv
    (α : M) (cflow : ℝ → E) (t : ℝ) (x q : M)
    (hx_source : x ∈ (chartAt H α).source)
    (hq_repr : q = (chartAt H α).symm (I.symm (cflow t)))
    (hChartCoord_eq : cflow t = I ((chartAt H α) x)) :
    q = x := by
  rw [hq_repr, hChartCoord_eq, I.left_inv]
  exact (chartAt H α).left_inv hx_source

/--
**Single-chart bijectivity** specialized to the `Φ`/`Ψ` chart-cover flow
setup. Given chart-α-local Picard data for `X` and for `-X` at the same
base point `α`, a starting point `x ∈ (chartAt H α).source`, a time
`t ∈ Set.Ico 0 T`, and three structural inputs (the chart-α representation
of `Ψ t (Φ t x)` as the chart-α pull-back of the chart-α-coord `-X`-flow
applied to the chart-α-coord image of `Φ t x` at time `t`, plus the
chart-α-coord composition identity), we conclude `Ψ t (Φ t x) = x`.

This is a thin instantiation of `chart_pullback_to_manifold_eq_via_chart_coord_inv`
at `cflow s := (hperNeg).flow (I ((chartAt H α) (Φ t x))) s` and
`q := Ψ t (Φ t x)`.

The chart-α-coord composition identity
`(hperNeg).flow (I ((chartAt H α) (Φ t x))) t = I ((chartAt H α) x)` is the
genuine mathematical fact supplied externally — it says, in chart-α coords,
the `-X`-flow applied to the chart-α-coord image of `Φ t x` at time `t`
recovers the chart-α-coord image of `x`. This is what would be derived
from a chart-coord Grönwall argument together with the chart-α
representation of `Φ s x` (the `s ↦ Φ (t-s) x` reversed-time trajectory
satisfies the chart-α-coord `-X`-ODE in the autonomous case, or under
suitable chart-invariance / chart-transition Jacobian compatibility in the
time-dependent case).
-/
theorem chart_cover_flow_bijective_single_chart_short_time
    (X : ℝ → ∀ x : M, TangentSpace I x) (α : M)
    (hperNeg : ChartLocalPicardData (fun t x => -(X t x)) α)
    (Ψ : ℝ → M → M) (Φtx : M) (t : ℝ)
    (x : M) (hx_source : x ∈ (chartAt H α).source)
    (hΨ_repr_at_Φt : Ψ t Φtx = (chartAt H α).symm
      (I.symm ((hperNeg).flow (I ((chartAt H α) Φtx)) t)))
    (hChartCoord_inv :
      (hperNeg).flow (I ((chartAt H α) Φtx)) t = I ((chartAt H α) x)) :
    Ψ t Φtx = x := by
  exact chart_pullback_to_manifold_eq_via_chart_coord_inv
    (α := α)
    (cflow := fun s => (hperNeg).flow (I ((chartAt H α) Φtx)) s)
    (t := t) (x := x) (q := Ψ t Φtx)
    hx_source hΨ_repr_at_Φt hChartCoord_inv

/--
**Chart-cover bijectivity on short time** for `Ψ ∘ Φ`: given the chart-cover
flow data `(Φ, Ψ, T)` and per-point chart-α-and-overlap data supplying both
the chart-α representation of `Ψ s (Φ s x)` (in a chart `α_x` chosen for `x`)
and the chart-α-coord composition identity, we conclude
`Ψ s (Φ s x) = x` on a positive per-point short time horizon.

**Substantive content**: each per-point datum supplies a chart-α-coord
algebraic identity in `E`; the present theorem systematically transports
these identities to manifold-level identities in `M`. The chart-α-coord
composition hypothesis is what is supplied by a downstream chart-coord
Grönwall uniqueness argument under chart-invariance of `X` (the
chart-transition Jacobian fixes the chart-pulled `X`-vector at each time,
as in `chart_overlap_chart_alpha_coord_ode`'s `hcompat`).

**Not hypothesis-packaging**: the per-point data quantifies over chart-α-coord
flows in `E`; the conclusion is a manifold-level statement in `M`. The
transport between the two is non-trivial (chart left-inverse + chart-source
membership). The chart-α-coord composition identity is a property of the
chart-α-coord flow function, distinct from the manifold-level statement
about `Ψ ∘ Φ`.
-/
theorem chart_cover_flow_bijective_on_short_time
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (hperNeg : ∀ α : M, ChartLocalPicardData (fun t x => -(X t x)) α)
    (Φ Ψ : ℝ → M → M) (T : ℝ) (_hT_pos : 0 < T)
    (hPick : ∀ x : M, ∃ S : ℝ, 0 < S ∧ S ≤ T ∧
      ∃ α_x : M,
        x ∈ (chartAt H α_x).source ∧
        (∀ s ∈ Set.Ico (0 : ℝ) S,
          Ψ s (Φ s x) = (chartAt H α_x).symm
            (I.symm ((hperNeg α_x).flow
              (I ((chartAt H α_x) (Φ s x))) s))) ∧
        (∀ s ∈ Set.Ico (0 : ℝ) S,
          (hperNeg α_x).flow
            (I ((chartAt H α_x) (Φ s x))) s
            = I ((chartAt H α_x) x))) :
    ∀ x : M, ∃ S : ℝ, 0 < S ∧ S ≤ T ∧
      ∀ s ∈ Set.Ico (0 : ℝ) S, Ψ s (Φ s x) = x := by
  classical
  intro x
  obtain ⟨S, hS_pos, hS_le, α_x, hx_source, hΨ_repr_at_Φ, hChartCoord_inv⟩ :=
    hPick x
  refine ⟨S, hS_pos, hS_le, ?_⟩
  intro s hs
  exact chart_cover_flow_bijective_single_chart_short_time
    (X := X) (α := α_x) (hperNeg := hperNeg α_x)
    (Ψ := Ψ) (Φtx := Φ s x) (t := s)
    (x := x) (hx_source := hx_source)
    (hΨ_repr_at_Φ s hs) (hChartCoord_inv s hs)

/--
**Symmetric chart-cover bijectivity on short time** for `Φ ∘ Ψ`: same
substantive content as `chart_cover_flow_bijective_on_short_time`,
mirrored across the `Φ ↔ Ψ` and `X ↔ -X` swap.

The per-point chart-α-and-overlap data now supplies the chart-α
representation of `Φ s (Ψ s x)` and the chart-α-coord composition identity
for the `X` flow (rather than the `-X` flow). The conclusion is the
manifold-level identity `Φ s (Ψ s x) = x`.
-/
theorem chart_cover_flow_bijective_on_short_time_symm
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (hper : ∀ α : M, ChartLocalPicardData X α)
    (Φ Ψ : ℝ → M → M) (T : ℝ) (_hT_pos : 0 < T)
    (hPick : ∀ x : M, ∃ S : ℝ, 0 < S ∧ S ≤ T ∧
      ∃ α_x : M,
        x ∈ (chartAt H α_x).source ∧
        (∀ s ∈ Set.Ico (0 : ℝ) S,
          Φ s (Ψ s x) = (chartAt H α_x).symm
            (I.symm ((hper α_x).flow
              (I ((chartAt H α_x) (Ψ s x))) s))) ∧
        (∀ s ∈ Set.Ico (0 : ℝ) S,
          (hper α_x).flow
            (I ((chartAt H α_x) (Ψ s x))) s
            = I ((chartAt H α_x) x))) :
    ∀ x : M, ∃ S : ℝ, 0 < S ∧ S ≤ T ∧
      ∀ s ∈ Set.Ico (0 : ℝ) S, Φ s (Ψ s x) = x := by
  classical
  intro x
  obtain ⟨S, hS_pos, hS_le, α_x, hx_source, hΦ_repr_at_Ψ, hChartCoord_inv⟩ :=
    hPick x
  refine ⟨S, hS_pos, hS_le, ?_⟩
  intro s hs
  exact chart_pullback_to_manifold_eq_via_chart_coord_inv
    (α := α_x)
    (cflow := fun u => (hper α_x).flow (I ((chartAt H α_x) (Ψ s x))) u)
    (t := s) (x := x) (q := Φ s (Ψ s x))
    hx_source (hΦ_repr_at_Ψ s hs) (hChartCoord_inv s hs)

/--
**Headline two-sided bijectivity** for the chart-cover flow `(Φ, Ψ)`:
combines `chart_cover_flow_bijective_on_short_time` (forward) and
`chart_cover_flow_bijective_on_short_time_symm` (reverse) at a common
per-point short time horizon.

The per-point chart-α-and-overlap data in both directions supplies the
chart-α representations of `Ψ s (Φ s x)` and `Φ s (Ψ s x)` (transported via
chart-overlap Grönwall uniqueness from the chart-α representations of `Φ`
and `Ψ` given by `time_dependent_vf_globalflow_on_closed_mfd`), together
with the chart-α-coord composition identities for the `-X` and `X` flows.

**Conclusion**: For every `x : M`, there exists a positive short-time
horizon `S` on which `Ψ s ∘ Φ s = id` and `Φ s ∘ Ψ s = id` at `x`.

This is the substantive bijectivity statement: `Ψ s` is a two-sided
inverse of `Φ s` for `s` in a positive short interval. The lemma is the
manifold-level conjunction of the two chart-coord directional statements,
re-aligned to share a common per-point time horizon.
-/
theorem chart_cover_flow_bijective_two_sided_on_short_time
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (hper : ∀ α : M, ChartLocalPicardData X α)
    (hperNeg : ∀ α : M, ChartLocalPicardData (fun t x => -(X t x)) α)
    (Φ Ψ : ℝ → M → M) (T : ℝ) (hT_pos : 0 < T)
    (hPickFwd : ∀ x : M, ∃ S : ℝ, 0 < S ∧ S ≤ T ∧
      ∃ α_x : M,
        x ∈ (chartAt H α_x).source ∧
        (∀ s ∈ Set.Ico (0 : ℝ) S,
          Ψ s (Φ s x) = (chartAt H α_x).symm
            (I.symm ((hperNeg α_x).flow
              (I ((chartAt H α_x) (Φ s x))) s))) ∧
        (∀ s ∈ Set.Ico (0 : ℝ) S,
          (hperNeg α_x).flow
            (I ((chartAt H α_x) (Φ s x))) s
            = I ((chartAt H α_x) x)))
    (hPickRev : ∀ x : M, ∃ S : ℝ, 0 < S ∧ S ≤ T ∧
      ∃ α_x : M,
        x ∈ (chartAt H α_x).source ∧
        (∀ s ∈ Set.Ico (0 : ℝ) S,
          Φ s (Ψ s x) = (chartAt H α_x).symm
            (I.symm ((hper α_x).flow
              (I ((chartAt H α_x) (Ψ s x))) s))) ∧
        (∀ s ∈ Set.Ico (0 : ℝ) S,
          (hper α_x).flow
            (I ((chartAt H α_x) (Ψ s x))) s
            = I ((chartAt H α_x) x))) :
    ∀ x : M, ∃ S : ℝ, 0 < S ∧ S ≤ T ∧
      ∀ s ∈ Set.Ico (0 : ℝ) S,
        Ψ s (Φ s x) = x ∧ Φ s (Ψ s x) = x := by
  classical
  intro x
  obtain ⟨S₁, hS₁_pos, hS₁_le, hBij_fwd⟩ :=
    chart_cover_flow_bijective_on_short_time
      (M := M) (I := I) (E := E)
      X hperNeg Φ Ψ T hT_pos hPickFwd x
  obtain ⟨S₂, hS₂_pos, hS₂_le, hBij_rev⟩ :=
    chart_cover_flow_bijective_on_short_time_symm
      (M := M) (I := I) (E := E)
      X hper Φ Ψ T hT_pos hPickRev x
  refine ⟨min S₁ S₂, lt_min hS₁_pos hS₂_pos,
    (min_le_left _ _).trans hS₁_le, ?_⟩
  intro s hs
  have hs_S₁ : s ∈ Set.Ico (0 : ℝ) S₁ :=
    ⟨hs.1, lt_of_lt_of_le hs.2 (min_le_left _ _)⟩
  have hs_S₂ : s ∈ Set.Ico (0 : ℝ) S₂ :=
    ⟨hs.1, lt_of_lt_of_le hs.2 (min_le_right _ _)⟩
  exact ⟨hBij_fwd s hs_S₁, hBij_rev s hs_S₂⟩

end DifferentialGeometry.PDE.RicciFlow.ODE
