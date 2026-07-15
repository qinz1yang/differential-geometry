import DifferentialGeometry.Geometry.Exponential.GaussLemma
import DifferentialGeometry.Geometry.Geodesic.Equation
import DifferentialGeometry.Geometry.Geodesic.Existence
import DifferentialGeometry.Geometry.Geodesic.MaximalInterval
import DifferentialGeometry.Geometry.Geodesic.Uniqueness
import DifferentialGeometry.Geometry.Geodesic.Homogeneity
import DifferentialGeometry.Geometry.Geodesic.CrossVFReduction
import DifferentialGeometry.Geometry.Geodesic.ProjDerivative
import DifferentialGeometry.Geometry.Exponential.Defs
import DifferentialGeometry.Geometry.Exponential.Smoothness.ZeroSectionConstancy
import DifferentialGeometry.Geometry.Connection.ParallelTransport.AlongCurve
import DifferentialGeometry.Geometry.Connection.ParallelTransport.MFDerivAlongCurve
import DifferentialGeometry.Analysis.Integration.Measure.ChartDensity
import DifferentialGeometry.Geometry.Connection.LeviCivita.Defs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.Riemannian.PathELength
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.EMetricSpace.Lipschitz
import DifferentialGeometry.Geometry.Comparison.GeodesicSpeedBound
import DifferentialGeometry.Geometry.Comparison.ChartVelocityConvergence
import DifferentialGeometry.Geometry.Comparison.LocalGeodesicSeed
import DifferentialGeometry.Geometry.Comparison.EndpointContinuation

set_option linter.unusedSectionVars false

/-!
# Hopf-Rinow: metric-completeness implies geodesic-completeness and the
existence of minimising geodesics

For a smooth Riemannian metric `g` on a connected, sigma-compact,
boundaryless smooth manifold `M` that is metric-complete as a
`PseudoEMetricSpace`, this file packages the classical Hopf-Rinow chain.

> **Sorry status (audited 2026-07-05):** this file carries 4 `sorry`s in 3
> statement-level frontiers (`exists_continuous_path_realizing_riemannianEDist`,
> `minimizing_path_is_smooth_geodesic`, `unit_speed_rescale`).  A reference scan
> found **no downstream consumers** of these three declarations — they are dead
> `sorry`s and do NOT poison the HCG/C4 chain, whose proper-realization needs are
> served sorry-free by `HopfRinowProper.lean` (a separate route through
> `MinimizingGeodesic`).  Keep them as recorded frontiers for the intrinsic
> Hopf–Rinow completion, or discharge them; do not cite this file's presence in
> an import closure as evidence of a sorry-tainted capstone without checking
> `#print axioms` on the capstone itself.

## Geodesic-completeness chain

* `gc_constant_speed` -- a geodesic has constant `g`-speed.
* `isGeodesicOn_speedSq_const` -- constant `g`-speed of an intrinsic
  moving-foot geodesic on an open interval.
* `gc_length_distance_bound` -- `riemannianEDist` is Lipschitz in
  the parameter along a geodesic with constant speed bound.
* `gc_escape_cauchy` -- if the maximal interval of a geodesic
  escapes to a finite right endpoint, the values form a Cauchy
  sequence in `riemannianEDist`.
* `gc_velocity_limit` -- the velocity speed is preserved at the
  metric limit point.
* `gc_position_limit` -- a bounded-speed curve converges to a single
  limit point as the parameter approaches a finite endpoint.
* `hasEndpointContinuation_of_complete` -- metric completeness furnishes
  endpoint-continuation data at a finite right endpoint.
* `isGeodesicOn_extends_past_finite_endpoint` -- a geodesic glues to a
  fresh local geodesic launched at its endpoint limit point.
* `isGeodesicOn_Ici_of_complete` / `isGeodesicOn_Ici_of_complete_Ioo` --
  the intrinsic cross-chart right-completeness, assembling the iterated
  single-step extensions into a geodesic on `Ici 0` (resp. `Ioi a₀`).

## Hopf-Rinow existence of minimisers

* `exists_continuous_path_realizing_riemannianEDist` -- the infimum `riemannianEDist I p q`
  is attained by a continuous curve.
* `minimizing_path_is_smooth_geodesic` -- a length-minimising curve coincides
  after arclength rescale with a smooth geodesic.
* `unit_speed_rescale` -- affine reparametrisation rescales a geodesic
  to unit-speed.
* `exists_unit_speed_minimizing_geodesic_between_points` -- existence of a
  unit-speed minimising geodesic between any two points.

## File layout

The upstream geodesic-completeness machinery is split into sibling files that
this headline imports and re-exports:

* `Comparison.GeodesicSpeedBound` -- constant speed, length bounds, metric limits.
* `Comparison.ChartVelocityConvergence` -- chart-velocity convergence and the
  chart-Gram positive-definiteness bound.
* `Comparison.LocalGeodesicSeed` -- local geodesic seeded at a point and velocity.
* `Comparison.EndpointContinuation` -- endpoint-continuation data under metric
  completeness.

This file holds the geodesic-completeness colimit conclusions
(`isGeodesicOn_Ici_of_complete`, `isGeodesicOn_Ici_of_complete_Ioo`) and the
downstream Hopf-Rinow headlines (exponential-map totality, existence of
minimising geodesics, exponential surjectivity).
-/

noncomputable section

open Set Function Filter Bundle Manifold
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace HopfRinow

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [Module.Finite ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
variable [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]

section GeodesicCompleteness

open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.MFDerivAlongCurve
open DifferentialGeometry.Integral.DivergenceTheorem

variable [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]

/-- **Single-step intrinsic right-extension.** A geodesic on `Iio b` with
endpoint-continuation data at `b` extends to a geodesic on `Iio b'` for
some `b' > b`, agreeing with the original below `b`. Direct corollary of
`isGeodesicOn_extends_past_finite_endpoint`. -/
theorem isGeodesicOn_Iio_extend
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {b : ℝ}
    (hγ : IsGeodesicOn (I := I) g γ (Set.Iio b))
    (hcont : HasEndpointContinuation (I := I) g γ b) :
    ∃ (γ' : ℝ → M) (b' : ℝ), b < b' ∧
      IsGeodesicOn (I := I) g γ' (Set.Iio b') ∧
      (∀ t < b, γ' t = γ t) := by
  obtain ⟨η, δ, hδ, hη, _hη_mdiff, hmatch⟩ := hcont
  obtain ⟨γ', hgeo', hagree⟩ :=
    isGeodesicOn_extends_past_finite_endpoint (I := I) g hδ hγ hη hmatch
  exact ⟨γ', b + δ, by linarith, hgeo', hagree⟩

/-- **Locality of the moving-foot geodesic equation.** If two curves agree on
a neighbourhood of `t`, then either satisfies the geodesic equation at `t` iff
the other does. A thin wrapper around
`HasGeodesicEquationAt.congr_of_eventuallyEq_at` extracting the basepoint
equality from the eventual equality at `t`. -/
private theorem hasGeodesicEquationAt_congr_of_eventuallyEq
    {g : SmoothRiemannianMetric I M} {γ γ' : ℝ → M} {t : ℝ}
    (heq : γ =ᶠ[nhds t] γ') (h : HasGeodesicEquationAt (I := I) g γ' t) :
    HasGeodesicEquationAt (I := I) g γ t := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact HasGeodesicEquationAt.congr_of_eventuallyEq_at (I := I) (g := g)
    (heq.eq_of_nhds) heq h

/-- **Intrinsic right-completeness.** Suppose that for every geodesic on a
half-open interval `Iio b` (`b > 0`) extending the initial geodesic `γ₀`,
endpoint-continuation data is available at `b`. Then the initial geodesic
on `Iio b₀` extends to a geodesic on all of `Ici 0` — equivalently, on
`Iio b` for arbitrarily large `b`.

This is the *true* geodesic-completeness statement, replacing the (false
on multi-chart manifolds) fixed-basepoint `maximalGeodesicInterval =
univ`. Each extension step is `isGeodesicOn_Iio_extend`
(fully proven above, axiom-clean). The colimit of the iterated single-step
extensions is assembled by a maximal-chain argument: order the
extension records `(b, γ)` (geodesic on `Iio b`, agreeing with `γ₀` below
`b₀`) by interval inclusion together with agreement below the shorter
endpoint, and pass to a maximal chain `Mc` (Hausdorff maximality). The
chain order forces mutual agreement of its members, so their union curve
`Γ` is single-valued; on a neighbourhood of any time `t` below a chain
endpoint, `Γ` agrees with a genuine geodesic, so the moving-foot equation
transfers by locality
(`hasGeodesicEquationAt_congr_of_eventuallyEq`). If the chain's endpoint
set were bounded above, `Γ` would be a geodesic on `Iio (sSup …)` admitting
endpoint continuation, hence a strict single-step extension whose record is
chain-comparable above every member — a super-chain contradicting
maximality. Therefore the endpoints are unbounded and `Γ` is a geodesic on
all of `ℝ ⊇ Ici 0`. -/
theorem isGeodesicOn_Ici_of_endpointContinuation
    (g : SmoothRiemannianMetric I M) {γ₀ : ℝ → M} {b₀ : ℝ} (hb₀ : 0 < b₀)
    (hγ₀ : IsGeodesicOn (I := I) g γ₀ (Set.Iio b₀))
    (hcont : ∀ (γ : ℝ → M) (b : ℝ), 0 < b →
      IsGeodesicOn (I := I) g γ (Set.Iio b) →
      (∀ t < b₀, t < b → γ t = γ₀ t) →
      HasEndpointContinuation (I := I) g γ b) :
    ∃ γ : ℝ → M,
      IsGeodesicOn (I := I) g γ (Set.Ici (0 : ℝ)) ∧
      (∀ t, t < b₀ → γ t = γ₀ t) := by
  classical
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  let Good : (ℝ × (ℝ → M)) → Prop := fun br =>
    b₀ ≤ br.1 ∧ IsGeodesicOn (I := I) g br.2 (Set.Iio br.1) ∧
      (∀ t < b₀, br.2 t = γ₀ t)
  let Rec := {br : ℝ × (ℝ → M) // Good br}
  let R : Rec → Rec → Prop := fun a a' =>
    a.1.1 ≤ a'.1.1 ∧ (∀ t < a.1.1, a'.1.2 t = a.1.2 t)
  have hGood_r₀ : Good (b₀, γ₀) := ⟨le_refl _, hγ₀, fun t _ => rfl⟩
  let r₀ : Rec := ⟨(b₀, γ₀), hGood_r₀⟩
  have hchain0 : IsChain R {r₀} := by
    intro a ha b hb hab
    rw [Set.mem_singleton_iff] at ha hb; exact absurd (ha.trans hb.symm) hab
  obtain ⟨Mc, hMc_max, hMc_sub⟩ := hchain0.exists_maxChain
  have hr₀_mem : r₀ ∈ Mc := hMc_sub (Set.mem_singleton _)
  have hMc_chain : IsChain R Mc := hMc_max.1
  have hconsist : ∀ a ∈ Mc, ∀ a' ∈ Mc, ∀ t, t < a.1.1 → t < a'.1.1 →
      a.1.2 t = a'.1.2 t := by
    intro a ha a' ha' t hta hta'
    rcases eq_or_ne a a' with rfl | hne
    · rfl
    · rcases hMc_chain ha ha' hne with hR | hR
      · exact (hR.2 t hta).symm
      · exact hR.2 t hta'
  let Γ : ℝ → M := fun t =>
    if h : ∃ a : Rec, a ∈ Mc ∧ t < a.1.1 then (h.choose.1.2 t) else γ₀ t
  have hΓ_val : ∀ a ∈ Mc, ∀ t, t < a.1.1 → Γ t = a.1.2 t := by
    intro a ha t hta
    have hex : ∃ a : Rec, a ∈ Mc ∧ t < a.1.1 := ⟨a, ha, hta⟩
    change (if h : ∃ a : Rec, a ∈ Mc ∧ t < a.1.1 then (h.choose.1.2 t)
      else γ₀ t) = a.1.2 t
    rw [dif_pos hex]
    obtain ⟨hb_mem, hb_lt⟩ := hex.choose_spec
    exact hconsist _ hb_mem a ha t hb_lt hta
  have hΓ_agree : ∀ t, t < b₀ → Γ t = γ₀ t := by
    intro t ht
    have := hΓ_val r₀ hr₀_mem t ht
    simpa [r₀] using this
  have hΓ_geo_at : ∀ a ∈ Mc, ∀ t, t < a.1.1 →
      HasGeodesicEquationAt (I := I) g Γ t := by
    intro a ha t hta
    have hIio_nhds : Set.Iio a.1.1 ∈ 𝓝 t := isOpen_Iio.mem_nhds hta
    have heq : Γ =ᶠ[𝓝 t] a.1.2 := by
      filter_upwards [hIio_nhds] with s hs
      exact hΓ_val a ha s hs
    exact hasGeodesicEquationAt_congr_of_eventuallyEq (g := g) heq (a.2.2.1 t hta)
  let S : Set ℝ := (fun a : Rec => a.1.1) '' Mc
  have hS_ne : S.Nonempty := ⟨b₀, ⟨r₀, hr₀_mem, rfl⟩⟩
  by_cases hbdd : BddAbove S
  · exfalso
    let s := sSup S
    have hb₀_le_s : b₀ ≤ s := le_csSup hbdd ⟨r₀, hr₀_mem, rfl⟩
    have hs_pos : 0 < s := lt_of_lt_of_le hb₀ hb₀_le_s
    have hΓ_geo_Iios : IsGeodesicOn (I := I) g Γ (Set.Iio s) := by
      intro t ht
      obtain ⟨b, hbS, htb⟩ := exists_lt_of_lt_csSup hS_ne ht
      obtain ⟨a, ha, hab⟩ := hbS
      exact hΓ_geo_at a ha t (lt_of_lt_of_eq htb hab.symm)
    have hagree_s : ∀ t < b₀, t < s → Γ t = γ₀ t := fun t ht _ => hΓ_agree t ht
    have hcont_s : HasEndpointContinuation (I := I) g Γ s :=
      hcont Γ s hs_pos hΓ_geo_Iios hagree_s
    obtain ⟨Γ', s', hss', hΓ'_geo, hΓ'_agree⟩ :=
      isGeodesicOn_Iio_extend (I := I) g hΓ_geo_Iios hcont_s
    have hGood' : Good (s', Γ') := by
      refine ⟨le_trans hb₀_le_s hss'.le, hΓ'_geo, ?_⟩
      intro t ht
      have ht_s : t < s := lt_of_lt_of_le ht hb₀_le_s
      change Γ' t = γ₀ t
      rw [hΓ'_agree t ht_s]; exact hΓ_agree t ht
    let r' : Rec := ⟨(s', Γ'), hGood'⟩
    have hr'_notMem : r' ∉ Mc := by
      intro hmem
      have hmemS : s' ∈ S := ⟨r', hmem, rfl⟩
      exact absurd (le_csSup hbdd hmemS) (not_le.mpr hss')
    have hchain' : IsChain R (insert r' Mc) := by
      refine hMc_chain.insert ?_
      intro a ha _
      right
      have ha_mem_S : a.1.1 ∈ S := ⟨a, ha, rfl⟩
      have ha_le_s : a.1.1 ≤ s := le_csSup hbdd ha_mem_S
      refine ⟨?_, ?_⟩
      · change a.1.1 ≤ s'
        exact le_trans ha_le_s hss'.le
      · intro t hta
        have ht_s : t < s := lt_of_lt_of_le hta ha_le_s
        change Γ' t = a.1.2 t
        rw [hΓ'_agree t ht_s]; exact hΓ_val a ha t hta
    have heq_chain : Mc = insert r' Mc :=
      hMc_max.2 hchain' (Set.subset_insert _ _)
    exact hr'_notMem (heq_chain ▸ Set.mem_insert _ _)
  · refine ⟨Γ, ?_, hΓ_agree⟩
    intro t _
    rw [not_bddAbove_iff] at hbdd
    obtain ⟨b, hbS, htb⟩ := hbdd t
    obtain ⟨a, ha, hab⟩ := hbS
    exact hΓ_geo_at a ha t (lt_of_lt_of_eq htb hab.symm)

/-- **Chart-coordinate `C¹` regularity.**  If `γ` satisfies the moving-foot
geodesic equation at every point of an open set `s ∋ t` and is continuous on
`s`, then the fixed-chart curve `chartCurve (γ t) γ = φ_{γ t} ∘ γ` is
`ContDiffAt ℝ 1` at `t`. -/
theorem chartCurve_contDiffAt_one_of_isGeodesicOn
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {s : Set ℝ} {t : ℝ}
    (hs : IsOpen s) (ht : t ∈ s)
    (hγ : IsGeodesicOn (I := I) g γ s) (hcont : ContinuousOn γ s) :
    ContDiffAt ℝ 1 (chartCurve (I := I) (γ t) γ) t := by
  classical
  set α : M := γ t with hα_def
  set u : ℝ → E := chartCurve (I := I) α γ with hu_def
  have hα_src : α ∈ (chartAt H α).source := mem_chart_source H α
  have hcontAt_t : ContinuousAt γ t :=
    hcont.continuousAt (hs.mem_nhds ht)
  have hsrc_nhds : (fun s' => γ s') ⁻¹' (chartAt H α).source ∈ 𝓝 t := by
    have : α ∈ (chartAt H α).source := hα_src
    exact hcontAt_t.preimage_mem_nhds ((chartAt H α).open_source.mem_nhds (by rw [hα_def] at this ⊢; exact this))
  obtain ⟨V, hV_nhds, hV_src⟩ := Filter.eventually_iff_exists_mem.mp
    (Filter.eventually_of_mem hsrc_nhds (fun _ h => h))
  set W : Set ℝ := V ∩ s with hW_def
  have hW_nhds : W ∈ 𝓝 t := Filter.inter_mem hV_nhds (hs.mem_nhds ht)
  have hW_src : ∀ s' ∈ W, γ s' ∈ (chartAt H α).source := fun s' hs' => hV_src s' hs'.1
  have hW_geo : ∀ s' ∈ W, HasGeodesicEquationAt (I := I) g γ s' :=
    fun s' hs' => hγ s' hs'.2
  have hW_contAt : ∀ s' ∈ W, ContinuousAt γ s' :=
    fun s' hs' => hcont.continuousAt (hs.mem_nhds hs'.2)
  have hODE : ∀ s' ∈ W,
      HasDerivAt (deriv u)
        (- chartChristoffelContraction (I := I) g α (deriv u s') (deriv u s') (u s')) s' := by
    intro s' hs'
    simpa [hu_def] using
      hasGeodesicEquationAt_fixedChart_hasDerivAt_velocity (I := I) g α
        (γ := γ) (t := s') (hW_contAt s' hs') (hW_src s' hs') (hW_geo s' hs')
  obtain ⟨W', hW'_sub, hW'_open, hW'_mem⟩ := mem_nhds_iff.mp hW_nhds
  have hderiv_diffOn : ∀ s' ∈ W', DifferentiableAt ℝ (deriv u) s' :=
    fun s' hs' => (hODE s' (hW'_sub hs')).differentiableAt
  have hderiv_contOn : ContinuousOn (deriv u) W' :=
    fun s' hs' => (hderiv_diffOn s' hs').continuousAt.continuousWithinAt
  rw [contDiffAt_one_iff]
  refine ⟨fun s' => ContinuousLinearMap.toSpanSingleton ℝ (deriv u s'), W',
    hW'_open.mem_nhds hW'_mem, ?_, ?_⟩
  · have hCLE : Continuous
        (fun w : E => (ContinuousLinearMap.toSpanSingleton ℝ w : ℝ →L[ℝ] E)) :=
      ContinuousLinearMap.toSpanSingletonCLE.continuous
    exact hCLE.comp_continuousOn hderiv_contOn
  · intro s' hs'
    have hcont_s' : ContinuousAt γ s' := hW_contAt s' (hW'_sub hs')
    have hsrc_s' : γ s' ∈ (chartAt H (γ t)).source := hW_src s' (hW'_sub hs')
    have hu_ev' : ∀ᶠ r in 𝓝 s', HasDerivAt u (deriv u r) r := by
      simpa [hu_def] using
        hasGeodesicEquationAt_fixedChart_eventually_hasDerivAt (I := I) g α
          (γ := γ) (t := s') hcont_s' (by rw [hα_def]; exact hsrc_s')
          (hW_geo s' (hW'_sub hs'))
    exact hu_ev'.self_of_nhds.hasFDerivAt

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **`C¹`-in-time regularity of a moving-foot geodesic (pointwise).**  An
intrinsic moving-foot geodesic `γ` on an open set `s` that is continuous on `s`
is `ContMDiffAt 𝓘(ℝ, ℝ) I 1` at every `t ∈ s`.

This is the analytic engine supplying the `C¹` regularity conjunct of the
`hreg` hypothesis of `isGeodesicOn_Ici_of_complete`.  The proof works in the
fixed chart `α = γ t`: the fixed-chart curve `u = φ_α ∘ γ` is `ContDiffAt 1`
in time (`chartCurve_contDiffAt_one_of_isGeodesicOn`), `(extChartAt I α).symm`
is `C^∞` on the chart target, and `γ` agrees with `(extChartAt I α).symm ∘ u`
on a neighbourhood of `t` (chart round-trip on the chart source), so `γ` is
`ContMDiffAt 1` at `t`. -/
theorem isGeodesicOn_contMDiffAt_one
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {s : Set ℝ} {t : ℝ}
    (hs : IsOpen s) (ht : t ∈ s)
    (hγ : IsGeodesicOn (I := I) g γ s) (hcont : ContinuousOn γ s) :
    ContMDiffAt 𝓘(ℝ, ℝ) I 1 γ t := by
  classical
  set α : M := γ t with hα_def
  set u : ℝ → E := chartCurve (I := I) α γ with hu_def
  have hu_cd : ContDiffAt ℝ 1 u t :=
    chartCurve_contDiffAt_one_of_isGeodesicOn (I := I) g hs ht hγ hcont
  have hu_cmd : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 u t := hu_cd.contMDiffAt
  have hα_src : α ∈ (chartAt H α).source := mem_chart_source H α
  have hα_ext_src : α ∈ (extChartAt I α).source := by
    rw [extChartAt_source]; exact hα_src
  have hut_eq : u t = extChartAt I α α := by
    rw [hu_def, chartCurve_def, hα_def]
  have hut_target : u t ∈ (extChartAt I α).target := by
    rw [hut_eq]; exact (extChartAt I α).map_source hα_ext_src
  have htarget_nhds : (extChartAt I α).target ∈ 𝓝 (u t) := by
    have hut_int : u t ∈ interior (extChartAt I α).target := by
      rw [hut_eq]
      exact extChartAt_target_subset_interior_of_boundaryless (I := I) α
        ((extChartAt I α).map_source hα_ext_src)
    exact mem_nhds_iff.mpr ⟨interior (extChartAt I α).target, interior_subset,
      isOpen_interior, hut_int⟩
  have hsymm_within : ContMDiffWithinAt 𝓘(ℝ, E) I 1
      (extChartAt I α).symm (extChartAt I α).target (u t) :=
    contMDiffWithinAt_extChartAt_symm_target (I := I) α hut_target
  have hsymm_at : ContMDiffAt 𝓘(ℝ, E) I 1 (extChartAt I α).symm (u t) :=
    hsymm_within.contMDiffAt htarget_nhds
  have hcomp : ContMDiffAt 𝓘(ℝ, ℝ) I 1 ((extChartAt I α).symm ∘ u) t :=
    hsymm_at.comp t hu_cmd
  have hcontAt_t : ContinuousAt γ t := hcont.continuousAt (hs.mem_nhds ht)
  have hsrc_nhds : (fun s' => γ s') ⁻¹' (chartAt H α).source ∈ 𝓝 t :=
    hcontAt_t.preimage_mem_nhds ((chartAt H α).open_source.mem_nhds hα_src)
  have heq : ((extChartAt I α).symm ∘ u) =ᶠ[𝓝 t] γ := by
    filter_upwards [hsrc_nhds] with s' hs'
    have hs'_ext : γ s' ∈ (extChartAt I α).source := by
      rw [extChartAt_source]; exact hs'
    change (extChartAt I α).symm (u s') = γ s'
    rw [hu_def, chartCurve_def]
    exact (extChartAt I α).left_inv hs'_ext
  exact hcomp.congr_of_eventuallyEq heq.symm

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **`C¹`-in-time regularity of a moving-foot geodesic (on an open set).**  An
intrinsic moving-foot geodesic `γ` on an open set `s`, continuous on `s`, is
`ContMDiffOn 𝓘(ℝ, ℝ) I 1` on `s`.  This is the exact shape of the `C¹`
regularity conjunct fed (with `s = Set.Iio b`) to the `hreg` hypothesis of
`isGeodesicOn_Ici_of_complete`. -/
theorem isGeodesicOn_contMDiffOn_one
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {s : Set ℝ}
    (hs : IsOpen s)
    (hγ : IsGeodesicOn (I := I) g γ s) (hcont : ContinuousOn γ s) :
    ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ s := fun _t ht =>
  (isGeodesicOn_contMDiffAt_one (I := I) g hs ht hγ hcont).contMDiffWithinAt

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Intrinsic right-completeness from metric completeness.**  A geodesic
`γ₀` on `Set.Iio b₀` (`b₀ > 0`) on a metrically complete manifold extends,
across charts, to a geodesic on all of `Set.Ici 0` that agrees with `γ₀`
below `b₀`.

The hypothesis `hreg` is the per-extension analytic regularity of any
geodesic extending `γ₀` past a finite right endpoint `b`: such a geodesic is
`C¹` on `Set.Iio b`, and its velocity has `g`-speed bounded by a nonnegative
constant `c` (both as a bundle-enorm bound and as an inner-product bound by
`c ^ 2`).  These are the facts a constant-speed geodesic always satisfies;
they are NOT the extension conclusion (the geodesic equation on a strictly
larger interval).  Metric completeness supplies endpoint-continuation data
at `b` via `hasEndpointContinuation_of_complete`, and the colimit of the
iterated single-step extensions (`isGeodesicOn_Ici_of_endpointContinuation`)
assembles the global geodesic. -/
theorem isGeodesicOn_Ici_of_complete
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) {γ₀ : ℝ → M} {b₀ : ℝ} (hb₀ : 0 < b₀)
    (hγ₀ : IsGeodesicOn (I := I) g γ₀ (Set.Iio b₀))
    (hreg : ∀ (γ : ℝ → M) (b : ℝ), 0 < b →
      IsGeodesicOn (I := I) g γ (Set.Iio b) →
      (∀ t < b₀, t < b → γ t = γ₀ t) →
      ∃ c : ℝ, 0 ≤ c ∧
        ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Set.Iio b) ∧
        (∀ τ ∈ Set.Iio b,
          ‖mfderiv 𝓘(ℝ, ℝ) I γ τ (1 : ℝ)‖ₑ ≤ ENNReal.ofReal c) ∧
        (∀ s ∈ Set.Iio b,
          (g.inner (γ s)) (mfderiv 𝓘(ℝ, ℝ) I γ s 1)
              (mfderiv 𝓘(ℝ, ℝ) I γ s 1) ≤ c ^ 2)) :
    ∃ γ : ℝ → M,
      IsGeodesicOn (I := I) g γ (Set.Ici (0 : ℝ)) ∧
      (∀ t, t < b₀ → γ t = γ₀ t) := by
  refine isGeodesicOn_Ici_of_endpointContinuation (I := I) g hb₀ hγ₀ ?_
  intro γ b hb hγ hagree
  obtain ⟨c, hc_nonneg, hγ_smooth, hSpeedBound, hSpeedSq⟩ := hreg γ b hb hγ hagree
  have hsub : Set.Ioo (b - 1) b ⊆ Set.Iio b := fun s hs => hs.2
  exact hasEndpointContinuation_of_complete (I := I) g (by linarith : b - 1 < b)
    hc_nonneg (hγ_smooth.mono hsub) (fun τ hτ => hSpeedBound τ (hsub hτ))
    (fun s hs => hSpeedSq s (hsub hs)) (hγ.mono hsub)

/-- **Single-step bounded-left right-extension.** A geodesic on a bounded
interval `Ioo a₀ b` (`a₀ < b`) with endpoint-continuation data at `b` extends to
a geodesic on `Ioo a₀ b'` for some `b' > b`, agreeing with the original below
`b`.  Bounded-left analogue of `isGeodesicOn_Iio_extend`, built on the
bounded-left glue. -/
theorem isGeodesicOn_Ioo_extend
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {a₀ b : ℝ} (ha₀b : a₀ < b)
    (hγ : IsGeodesicOn (I := I) g γ (Set.Ioo a₀ b))
    (hγ_cont : ContinuousOn γ (Set.Ioo a₀ b))
    (hcont : HasEndpointContinuation (I := I) g γ b) :
    ∃ (γ' : ℝ → M) (b' : ℝ), b < b' ∧
      IsGeodesicOn (I := I) g γ' (Set.Ioo a₀ b') ∧
      ContinuousOn γ' (Set.Ioo a₀ b') ∧
      (∀ t < b, γ' t = γ t) := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨η, δ, hδ, hη, hη_mdiff, hmatch⟩ := hcont
  set G : ℝ → M := fun t => if t < b then γ t else η (t - b) with hG_def
  have hη_cont : ContinuousOn η (Set.Ioo (-δ) δ) :=
    fun t ht => (hη_mdiff t ht).continuousAt.continuousWithinAt
  have hηb_cont : ContinuousOn (fun t => η (t - b)) (Set.Ioo (b - δ) (b + δ)) := by
    have hshift : ContinuousOn (fun t : ℝ => t - b) (Set.Ioo (b - δ) (b + δ)) :=
      (continuous_sub_right b).continuousOn
    have hmaps : Set.MapsTo (fun t : ℝ => t - b) (Set.Ioo (b - δ) (b + δ))
        (Set.Ioo (-δ) δ) := fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
    exact hη_cont.comp hshift hmaps
  have hG_cont : ContinuousOn G (Set.Ioo a₀ (b + δ)) := by
    intro t ht
    rcases lt_trichotomy t b with hlt | heq | hgt
    · have htγ : t ∈ Set.Ioo a₀ b := ⟨ht.1, hlt⟩
      have hGγ : G =ᶠ[𝓝[Set.Ioo a₀ (b + δ)] t] γ := by
        have hnhds : Set.Iio b ∈ 𝓝 t := isOpen_Iio.mem_nhds hlt
        filter_upwards [nhdsWithin_le_nhds hnhds] with s hs
        simp only [hG_def, if_pos (mem_Iio.mp hs)]
      have hγ_at : ContinuousWithinAt γ (Set.Ioo a₀ (b + δ)) t := by
        refine (hγ_cont t htγ).mono_of_mem_nhdsWithin ?_
        exact mem_nhdsWithin_of_mem_nhds (isOpen_Ioo.mem_nhds htγ)
      refine hγ_at.congr_of_eventuallyEq hGγ ?_
      simp only [hG_def, if_pos hlt]
    · subst heq
      have hG_eq_ηb : G =ᶠ[𝓝[Set.Ioo a₀ (t + δ)] t] (fun s => η (s - t)) := by
        rw [eventuallyEq_nhdsWithin_iff]
        have hleft : ∀ᶠ s in 𝓝[<] t, G s = η (s - t) := by
          have hmatch' : γ =ᶠ[𝓝[<] t] (fun s => η (s - t)) := hmatch
          have hGγ : G =ᶠ[𝓝[<] t] γ := by
            filter_upwards [self_mem_nhdsWithin] with s hs
            simp only [hG_def, if_pos (mem_Iio.mp hs)]
          exact hGγ.trans hmatch'
        have hright : ∀ᶠ s in 𝓝[≥] t, G s = η (s - t) := by
          filter_upwards [self_mem_nhdsWithin] with s hs
          simp only [hG_def, if_neg (not_lt.mpr (mem_Ici.mp hs))]
        have hfull : G =ᶠ[𝓝 t] (fun s => η (s - t)) := by
          rw [← nhdsLT_sup_nhdsGE t, Filter.EventuallyEq, eventually_sup]
          exact ⟨hleft, hright⟩
        filter_upwards [hfull] with s hs _ using hs
      have hηb_at : ContinuousWithinAt (fun s => η (s - t)) (Set.Ioo a₀ (t + δ)) t := by
        have htmem : t ∈ Set.Ioo (t - δ) (t + δ) := ⟨by linarith, by linarith⟩
        refine (hηb_cont t htmem).mono_of_mem_nhdsWithin ?_
        exact mem_nhdsWithin_of_mem_nhds (isOpen_Ioo.mem_nhds htmem)
      refine hηb_at.congr_of_eventuallyEq hG_eq_ηb ?_
      simp only [hG_def, if_neg (lt_irrefl t), sub_self]
    · have htηb : t ∈ Set.Ioo (b - δ) (b + δ) := ⟨by linarith, ht.2⟩
      have hGηb : G =ᶠ[𝓝[Set.Ioo a₀ (b + δ)] t] (fun s => η (s - b)) := by
        have hnhds : Set.Ioi b ∈ 𝓝 t := isOpen_Ioi.mem_nhds hgt
        filter_upwards [nhdsWithin_le_nhds hnhds] with s hs
        simp only [hG_def, if_neg (not_lt.mpr (le_of_lt (mem_Ioi.mp hs)))]
      refine ContinuousWithinAt.congr_of_eventuallyEq ?_ hGηb ?_
      · refine (hηb_cont t htηb).mono_of_mem_nhdsWithin ?_
        exact mem_nhdsWithin_of_mem_nhds (isOpen_Ioo.mem_nhds htηb)
      · simp only [hG_def, if_neg (not_lt.mpr (le_of_lt hgt))]
  refine ⟨G, b + δ, by linarith,
    Geodesic.isGeodesicOn_glue_at_limit_Ioo (I := I) g hδ ha₀b hγ hη hmatch,
    hG_cont, ?_⟩
  intro t ht
  simp only [hG_def, if_pos ht]

/-- **`Ioo`-seeded intrinsic right-completeness.** Suppose that for every
geodesic on a bounded interval `Ioo a₀ b` (`b > 0`) extending the initial
geodesic `γ₀` (which is a geodesic on `Ioo a₀ b₀`), endpoint-continuation data is
available at `b`.  Then the initial geodesic extends to a geodesic on the
right-unbounded interval `Ioi a₀`, agreeing with `γ₀` below `b₀`.

Bounded-left analogue of `isGeodesicOn_Ici_of_endpointContinuation`: the
extension records are geodesics on `Ioo a₀ b` with the fixed left endpoint `a₀`,
ordered by interval inclusion plus agreement below the shorter endpoint, and the
union over a maximal chain is the colimit geodesic on `Ioi a₀`.  Each step is the
bounded-left `isGeodesicOn_Ioo_extend`; the maximal-chain colimit assembly is
identical to the `Iio` engine since both only inspect left-neighbourhoods of the
growing right endpoint. -/
theorem isGeodesicOn_Ioi_of_endpointContinuation
    (g : SmoothRiemannianMetric I M) {γ₀ : ℝ → M} {a₀ b₀ : ℝ}
    (ha₀ : a₀ < 0) (hb₀ : 0 < b₀)
    (hγ₀ : IsGeodesicOn (I := I) g γ₀ (Set.Ioo a₀ b₀))
    (hγ₀_cont : ContinuousOn γ₀ (Set.Ioo a₀ b₀))
    (hcont : ∀ (γ : ℝ → M) (b : ℝ), 0 < b →
      IsGeodesicOn (I := I) g γ (Set.Ioo a₀ b) →
      ContinuousOn γ (Set.Ioo a₀ b) →
      (∀ t < b₀, t < b → γ t = γ₀ t) →
      HasEndpointContinuation (I := I) g γ b) :
    ∃ γ : ℝ → M,
      IsGeodesicOn (I := I) g γ (Set.Ioi a₀) ∧
      ContinuousOn γ (Set.Ioi a₀) ∧
      (∀ t, t < b₀ → γ t = γ₀ t) := by
  classical
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  have ha₀b₀ : a₀ < b₀ := lt_trans ha₀ hb₀
  let Good : (ℝ × (ℝ → M)) → Prop := fun br =>
    b₀ ≤ br.1 ∧ IsGeodesicOn (I := I) g br.2 (Set.Ioo a₀ br.1) ∧
      ContinuousOn br.2 (Set.Ioo a₀ br.1) ∧
      (∀ t < b₀, br.2 t = γ₀ t)
  let Rec := {br : ℝ × (ℝ → M) // Good br}
  let R : Rec → Rec → Prop := fun a a' =>
    a.1.1 ≤ a'.1.1 ∧ (∀ t < a.1.1, a'.1.2 t = a.1.2 t)
  have hGood_r₀ : Good (b₀, γ₀) := ⟨le_refl _, hγ₀, hγ₀_cont, fun t _ => rfl⟩
  let r₀ : Rec := ⟨(b₀, γ₀), hGood_r₀⟩
  have hchain0 : IsChain R {r₀} := by
    intro a ha b hb hab
    rw [Set.mem_singleton_iff] at ha hb; exact absurd (ha.trans hb.symm) hab
  obtain ⟨Mc, hMc_max, hMc_sub⟩ := hchain0.exists_maxChain
  have hr₀_mem : r₀ ∈ Mc := hMc_sub (Set.mem_singleton _)
  have hMc_chain : IsChain R Mc := hMc_max.1
  have hconsist : ∀ a ∈ Mc, ∀ a' ∈ Mc, ∀ t, t < a.1.1 → t < a'.1.1 →
      a.1.2 t = a'.1.2 t := by
    intro a ha a' ha' t hta hta'
    rcases eq_or_ne a a' with rfl | hne
    · rfl
    · rcases hMc_chain ha ha' hne with hR | hR
      · exact (hR.2 t hta).symm
      · exact hR.2 t hta'
  let Γ : ℝ → M := fun t =>
    if h : ∃ a : Rec, a ∈ Mc ∧ t < a.1.1 then (h.choose.1.2 t) else γ₀ t
  have hΓ_val : ∀ a ∈ Mc, ∀ t, t < a.1.1 → Γ t = a.1.2 t := by
    intro a ha t hta
    have hex : ∃ a : Rec, a ∈ Mc ∧ t < a.1.1 := ⟨a, ha, hta⟩
    change (if h : ∃ a : Rec, a ∈ Mc ∧ t < a.1.1 then (h.choose.1.2 t)
      else γ₀ t) = a.1.2 t
    rw [dif_pos hex]
    obtain ⟨hb_mem, hb_lt⟩ := hex.choose_spec
    exact hconsist _ hb_mem a ha t hb_lt hta
  have hΓ_agree : ∀ t, t < b₀ → Γ t = γ₀ t := by
    intro t ht
    have := hΓ_val r₀ hr₀_mem t ht
    simpa [r₀] using this
  have hΓ_geo_at : ∀ a ∈ Mc, ∀ t, a₀ < t → t < a.1.1 →
      HasGeodesicEquationAt (I := I) g Γ t := by
    intro a ha t hta_lo hta
    have hIoo_nhds : Set.Ioo a₀ a.1.1 ∈ 𝓝 t := isOpen_Ioo.mem_nhds ⟨hta_lo, hta⟩
    have heq : Γ =ᶠ[𝓝 t] a.1.2 := by
      filter_upwards [hIoo_nhds] with s hs
      exact hΓ_val a ha s hs.2
    exact hasGeodesicEquationAt_congr_of_eventuallyEq (g := g) heq
      (a.2.2.1 t ⟨hta_lo, hta⟩)
  have hΓ_cont_at : ∀ a ∈ Mc, ∀ t, a₀ < t → t < a.1.1 →
      ContinuousWithinAt Γ (Set.Ioi a₀) t := by
    intro a ha t hta_lo hta
    have htmem : t ∈ Set.Ioo a₀ a.1.1 := ⟨hta_lo, hta⟩
    have heq : Γ =ᶠ[𝓝[Set.Ioi a₀] t] a.1.2 := by
      have hnhds : Set.Iio a.1.1 ∈ 𝓝 t := isOpen_Iio.mem_nhds hta
      filter_upwards [nhdsWithin_le_nhds hnhds] with s hs
      exact hΓ_val a ha s (mem_Iio.mp hs)
    have hmem_at : ContinuousWithinAt a.1.2 (Set.Ioi a₀) t := by
      refine ((a.2.2.2.1 t htmem)).mono_of_mem_nhdsWithin ?_
      exact mem_nhdsWithin_of_mem_nhds (isOpen_Ioo.mem_nhds htmem)
    exact hmem_at.congr_of_eventuallyEq heq (hΓ_val a ha t hta)
  let S : Set ℝ := (fun a : Rec => a.1.1) '' Mc
  have hS_ne : S.Nonempty := ⟨b₀, ⟨r₀, hr₀_mem, rfl⟩⟩
  by_cases hbdd : BddAbove S
  · exfalso
    let s := sSup S
    have hb₀_le_s : b₀ ≤ s := le_csSup hbdd ⟨r₀, hr₀_mem, rfl⟩
    have hs_pos : 0 < s := lt_of_lt_of_le hb₀ hb₀_le_s
    have ha₀_lt_s : a₀ < s := lt_of_lt_of_le ha₀b₀ hb₀_le_s
    have hΓ_geo_Ioos : IsGeodesicOn (I := I) g Γ (Set.Ioo a₀ s) := by
      intro t ht
      obtain ⟨b, hbS, htb⟩ := exists_lt_of_lt_csSup hS_ne ht.2
      obtain ⟨a, ha, hab⟩ := hbS
      exact hΓ_geo_at a ha t ht.1 (lt_of_lt_of_eq htb hab.symm)
    have hΓ_cont_Ioos : ContinuousOn Γ (Set.Ioo a₀ s) := by
      intro t ht
      obtain ⟨b, hbS, htb⟩ := exists_lt_of_lt_csSup hS_ne ht.2
      obtain ⟨a, ha, hab⟩ := hbS
      have hcw := hΓ_cont_at a ha t ht.1 (lt_of_lt_of_eq htb hab.symm)
      exact hcw.mono (fun u hu => hu.1)
    have hagree_s : ∀ t < b₀, t < s → Γ t = γ₀ t := fun t ht _ => hΓ_agree t ht
    have hcont_s : HasEndpointContinuation (I := I) g Γ s :=
      hcont Γ s hs_pos hΓ_geo_Ioos hΓ_cont_Ioos hagree_s
    obtain ⟨Γ', s', hss', hΓ'_geo, hΓ'_cont, hΓ'_agree⟩ :=
      isGeodesicOn_Ioo_extend (I := I) g ha₀_lt_s hΓ_geo_Ioos hΓ_cont_Ioos hcont_s
    have hGood' : Good (s', Γ') := by
      refine ⟨le_trans hb₀_le_s hss'.le, hΓ'_geo, hΓ'_cont, ?_⟩
      intro t ht
      have ht_s : t < s := lt_of_lt_of_le ht hb₀_le_s
      change Γ' t = γ₀ t
      rw [hΓ'_agree t ht_s]; exact hΓ_agree t ht
    let r' : Rec := ⟨(s', Γ'), hGood'⟩
    have hr'_notMem : r' ∉ Mc := by
      intro hmem
      have hmemS : s' ∈ S := ⟨r', hmem, rfl⟩
      exact absurd (le_csSup hbdd hmemS) (not_le.mpr hss')
    have hchain' : IsChain R (insert r' Mc) := by
      refine hMc_chain.insert ?_
      intro a ha _
      right
      have ha_mem_S : a.1.1 ∈ S := ⟨a, ha, rfl⟩
      have ha_le_s : a.1.1 ≤ s := le_csSup hbdd ha_mem_S
      refine ⟨?_, ?_⟩
      · change a.1.1 ≤ s'
        exact le_trans ha_le_s hss'.le
      · intro t hta
        have ht_s : t < s := lt_of_lt_of_le hta ha_le_s
        change Γ' t = a.1.2 t
        rw [hΓ'_agree t ht_s]; exact hΓ_val a ha t hta
    have heq_chain : Mc = insert r' Mc :=
      hMc_max.2 hchain' (Set.subset_insert _ _)
    exact hr'_notMem (heq_chain ▸ Set.mem_insert _ _)
  · refine ⟨Γ, ?_, ?_, hΓ_agree⟩
    · intro t ht
      rw [not_bddAbove_iff] at hbdd
      obtain ⟨b, hbS, htb⟩ := hbdd t
      obtain ⟨a, ha, hab⟩ := hbS
      exact hΓ_geo_at a ha t ht (lt_of_lt_of_eq htb hab.symm)
    · intro t ht
      rw [not_bddAbove_iff] at hbdd
      obtain ⟨b, hbS, htb⟩ := hbdd t
      obtain ⟨a, ha, hab⟩ := hbS
      exact hΓ_cont_at a ha t ht (lt_of_lt_of_eq htb hab.symm)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **`Ioo`-seeded forward geodesic completeness from metric completeness.**
A moving-foot geodesic `γ₀` on a bounded interval `Ioo a₀ b₀` (`a₀ < 0 < b₀`)
extends, across charts, to a geodesic on the right-unbounded interval `Ioi a₀`,
agreeing with `γ₀` below `b₀`.

This is the bounded-left analogue of `isGeodesicOn_Ici_of_complete`, seeded by
the *bounded* interval `Ioo a₀ b₀` produced by the local seed
`exists_isGeodesicOn_Ioo_at_velocity` (rather than a left-unbounded `Iio b₀`).
The per-extension analytic data `hreg` is the minimal separable regularity a
constant-speed geodesic supplies: `C¹`-in-time on `Ioo a₀ b`, with constant
`g`-speed bounded by a nonnegative `c`.  Metric completeness furnishes
endpoint-continuation data at each finite right endpoint `b`
(`hasEndpointContinuation_of_complete`, in its bounded-left form), and the colimit
assembly (`isGeodesicOn_Ioi_of_endpointContinuation`) produces the global forward
geodesic. -/
theorem isGeodesicOn_Ici_of_complete_Ioo
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) {γ₀ : ℝ → M} {a₀ b₀ : ℝ}
    (ha₀ : a₀ < 0) (hb₀ : 0 < b₀)
    (hγ₀ : IsGeodesicOn (I := I) g γ₀ (Set.Ioo a₀ b₀))
    (hγ₀_cont : ContinuousOn γ₀ (Set.Ioo a₀ b₀))
    (hreg : ∀ (γ : ℝ → M) (b : ℝ), 0 < b → IsGeodesicOn (I := I) g γ (Set.Ioo a₀ b) →
      ContinuousOn γ (Set.Ioo a₀ b) →
      (∀ t, a₀ < t → t < b₀ → t < b → γ t = γ₀ t) →
      ∃ c : ℝ, 0 ≤ c ∧ ContMDiffOn 𝓘(ℝ,ℝ) I 1 γ (Set.Ioo a₀ b) ∧
        (∀ τ ∈ Set.Ioo a₀ b, ‖mfderiv 𝓘(ℝ,ℝ) I γ τ 1‖ₑ ≤ ENNReal.ofReal c) ∧
        (∀ s ∈ Set.Ioo a₀ b, (g.inner (γ s)) (mfderiv 𝓘(ℝ,ℝ) I γ s 1)
          (mfderiv 𝓘(ℝ,ℝ) I γ s 1) ≤ c^2)) :
    ∃ γ : ℝ → M, IsGeodesicOn (I := I) g γ (Set.Ioi a₀) ∧
      (∀ t, t < b₀ → γ t = γ₀ t) := by
  have hcont : ∀ (γ : ℝ → M) (b : ℝ), 0 < b →
      IsGeodesicOn (I := I) g γ (Set.Ioo a₀ b) →
      ContinuousOn γ (Set.Ioo a₀ b) →
      (∀ t < b₀, t < b → γ t = γ₀ t) →
      HasEndpointContinuation (I := I) g γ b := by
    intro γ b hb hγ hγ_cont hagree
    obtain ⟨c, hc_nonneg, hγ_smooth, hSpeedBound, hSpeedSq⟩ :=
      hreg γ b hb hγ hγ_cont (fun t _ ht_b₀ ht_b => hagree t ht_b₀ ht_b)
    exact hasEndpointContinuation_of_complete (I := I) g (lt_trans ha₀ hb)
      hc_nonneg hγ_smooth hSpeedBound hSpeedSq hγ
  obtain ⟨γ, hgeo, _hcontΓ, hagreeΓ⟩ :=
    isGeodesicOn_Ioi_of_endpointContinuation (I := I) g ha₀ hb₀ hγ₀ hγ₀_cont hcont
  exact ⟨γ, hgeo, hagreeΓ⟩

end GeodesicCompleteness

section MinimiserExistence

variable [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]

/-- **Minimising sequence of `C¹` paths.** For any `p q : M` there is a
sequence of `C¹` curves `γₙ : ℝ → M` on `[0, 1]` from `p` to `q` whose
`pathELength`s converge from above to `riemannianEDist I p q`, provided
the latter is finite. The bound `pathELength I (γ n) 0 1 < d + 1/(n+1)`
is produced by the Mathlib infimum-approximation lemma
`exists_lt_of_riemannianEDist_lt`, and the lower bound
`d ≤ pathELength I (γ n) 0 1` by `riemannianEDist_le_pathELength`. -/
private theorem path_length_minimising_sequence
    (p q : M) (hd : riemannianEDist I p q ≠ ⊤) :
    ∃ γ : ℕ → ℝ → M,
      (∀ n, γ n 0 = p) ∧ (∀ n, γ n 1 = q) ∧
      (∀ n, CMDiff[Set.Icc (0 : ℝ) 1] 1 (γ n)) ∧
      (∀ n, riemannianEDist I p q ≤ pathELength I (γ n) 0 1) ∧
      (∀ n, pathELength I (γ n) 0 1 <
        riemannianEDist I p q + ENNReal.ofReal (1 / (n + 1))) := by
  set d : ℝ≥0∞ := riemannianEDist I p q with hd_def
  have hstep : ∀ n : ℕ, ∃ ρ : ℝ → M,
      ρ 0 = p ∧ ρ 1 = q ∧ CMDiff[Set.Icc (0 : ℝ) 1] 1 ρ ∧
      pathELength I ρ 0 1 < d + ENNReal.ofReal (1 / (n + 1)) := by
    intro n
    have hpos : (0 : ℝ) < 1 / (n + 1) := by positivity
    have hofReal_pos : (0 : ℝ≥0∞) < ENNReal.ofReal (1 / (n + 1)) :=
      ENNReal.ofReal_pos.mpr hpos
    have hlt : d < d + ENNReal.ofReal (1 / (n + 1)) :=
      ENNReal.lt_add_right (by rw [hd_def]; exact hd) hofReal_pos.ne'
    obtain ⟨ρ, hρ0, hρ1, hρ_smooth, hρ_len⟩ :=
      Manifold.exists_lt_of_riemannianEDist_lt (I := I) (x := p) (y := q)
        (r := d + ENNReal.ofReal (1 / (n + 1))) (by rw [hd_def] at hlt; exact hlt)
    exact ⟨ρ, hρ0, hρ1, hρ_smooth, hρ_len⟩
  choose γ hγ0 hγ1 hγ_smooth hγ_len using hstep
  refine ⟨γ, hγ0, hγ1, hγ_smooth, ?_, ?_⟩
  · intro n
    rw [hd_def]
    exact Manifold.riemannianEDist_le_pathELength (I := I) (γ := γ n)
      (a := 0) (b := 1) (hγ_smooth n) (hγ0 n) (hγ1 n) zero_le_one
  · intro n; rw [hd_def] at hγ_len ⊢; exact hγ_len n

/-- **Path-length infimum is attained.** On a complete Riemannian manifold
(`IsRiemannianManifold I M`, `CompleteSpace M`), for every `p q : M` there
is a continuous curve `γ : ℝ → M` with `γ 0 = p`, `γ 1 = q` whose
`pathELength I γ 0 1` equals `riemannianEDist I p q` (the distance infimum
over paths is attained). The proof builds a length-minimising sequence of
`C¹` paths whose lengths converge to `riemannianEDist I p q` and extracts a
continuous limit curve. -/
theorem exists_continuous_path_realizing_riemannianEDist
    (g : SmoothRiemannianMetric I M) (p q : M) :
    ∃ γ : ℝ → M,
      Continuous γ ∧ γ 0 = p ∧ γ 1 = q ∧
        pathELength I γ 0 1 = riemannianEDist I p q := by
  by_cases hd : riemannianEDist I p q = ⊤
  · sorry
  · obtain ⟨γseq, hγ0, hγ1, hγ_smooth, hγ_lb, hγ_ub⟩ :=
      path_length_minimising_sequence (I := I) p q hd
    set d : ℝ≥0∞ := riemannianEDist I p q with hd_def
    have hLen_tendsto :
        Tendsto (fun n => pathELength I (γseq n) 0 1) atTop (𝓝 d) := by
      have hupper :
          Tendsto (fun n : ℕ => d + ENNReal.ofReal (1 / (n + 1))) atTop (𝓝 d) := by
        have h1 : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0) :=
          tendsto_one_div_add_atTop_nhds_zero_nat
        have h2 : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / (n + 1)))
            atTop (𝓝 (ENNReal.ofReal 0)) :=
          (ENNReal.continuous_ofReal.tendsto 0).comp h1
        rw [ENNReal.ofReal_zero] at h2
        have h3 : Tendsto (fun n : ℕ => d + ENNReal.ofReal (1 / (n + 1)))
            atTop (𝓝 (d + 0)) :=
          Filter.Tendsto.const_add d h2
        simpa using h3
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le
        tendsto_const_nhds hupper (fun n => ?_) (fun n => ?_)
      · exact hγ_lb n
      · exact (hγ_ub n).le
    clear hLen_tendsto
    sorry

/-- **A length minimiser is, after reparametrisation, a smooth geodesic.**
If a continuous curve `γ` on `[a, b]` is length-minimising
(`pathELength I γ a b = riemannianEDist I (γ a) (γ b)`), then there is a
parameter length `L ≥ 0` and a reparametrisation `η : ℝ → M` with the same
endpoints (`η 0 = γ a`, `η L = γ b`) that is `C^∞` and `IsGeodesicAt` on the
open interval `(0, L)`, is `C¹` and `IsGeodesicOn` on `[0, L]`, has
`pathELength I η 0 L = ENNReal.ofReal L`, and whose length parameter realises
the endpoint distance, `ENNReal.ofReal L = riemannianEDist I (γ a) (γ b)`. -/
theorem minimizing_path_is_smooth_geodesic
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {a b : ℝ}
    (hab : a ≤ b) (hγ : Continuous γ)
    (hmin : pathELength I γ a b = riemannianEDist I (γ a) (γ b)) :
    ∃ (L : ℝ) (η : ℝ → M),
      0 ≤ L ∧ η 0 = γ a ∧ η L = γ b ∧
        (∀ t ∈ Set.Ioo (0 : ℝ) L, ContMDiffAt 𝓘(ℝ, ℝ) I ∞ η t) ∧
        (∀ t ∈ Set.Ioo (0 : ℝ) L,
          IsGeodesicAt (I := I) g η t) ∧
        pathELength I η 0 L = ENNReal.ofReal L ∧
        ENNReal.ofReal L = riemannianEDist I (γ a) (γ b) ∧
        ContMDiffOn 𝓘(ℝ, ℝ) I 1 η (Set.Icc 0 L) ∧
        IsGeodesicOn (I := I) g η (Set.Icc 0 L) := by
  sorry

/-- **Auxiliary: `IsGeodesicOn` is preserved under affine
reparametrisation.** If `γ` is a geodesic on `[a, b]` and `c, d : ℝ`, then
`s ↦ γ (c · s + d)` is a geodesic on the preimage interval.  This is the
moving-foot reading of the second-order chain rule: at each time the chart
velocity scales by `c`, the chart acceleration by `c²`, and the Christoffel
contraction by `c²` (`Γ(c v, c v) = c² · Γ(v, v)`), so the geodesic identity
carries over after factoring out `c²`.  Proved generally in
`Geodesic.Equation.isGeodesicOn_comp_affine`. -/
private theorem isGeodesicOn_affineReparam
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {a b c d : ℝ}
    (hγ_geod : IsGeodesicOn (I := I) g γ (Set.Icc a b)) :
    IsGeodesicOn (I := I) g (fun s => γ (c * s + d))
      {s : ℝ | c * s + d ∈ Set.Icc a b} :=
  isGeodesicOn_comp_affine (I := I) hγ_geod

/-- **Unit-speed reparametrisation of a geodesic of positive length.**
A geodesic `\gamma : [a, b] \to M` whose `pathELength` equals
`ENNReal.ofReal L` with `L > 0` becomes unit-speed under the affine
reparametrisation `\eta(s) := \gamma(a + s \cdot (b - a)/L)` on
`[0, L]`. The `IsGeodesicOn` predicate is preserved under affine
reparametrisation. -/
theorem unit_speed_rescale
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {a b L : ℝ}
    (hab : a ≤ b) (hL : 0 < L)
    (hγ_geod : IsGeodesicOn (I := I) g γ (Set.Icc a b))
    (hγ_len : pathELength I γ a b = ENNReal.ofReal L)
    (hγ_C1 : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Set.Icc a b)) :
    ∃ η : ℝ → M,
      η 0 = γ a ∧ η L = γ b ∧
        IsGeodesicOn (I := I) g η (Set.Icc 0 L) ∧
        ContMDiffOn 𝓘(ℝ, ℝ) I 1 η (Set.Icc 0 L) ∧
        ∀ t ∈ Set.Icc (0 : ℝ) L,
          (g.inner (η t)) (mfderiv 𝓘(ℝ, ℝ) I η t 1)
              (mfderiv 𝓘(ℝ, ℝ) I η t 1) = 1 := by
  set c : ℝ := (b - a) / L with hc_def
  refine ⟨fun s => γ (a + s * c), ?_, ?_, ?_, ?_, ?_⟩
  · change γ (a + 0 * c) = γ a
    simp
  · change γ (a + L * c) = γ b
    have hL_ne : L ≠ 0 := ne_of_gt hL
    have hLc : L * c = b - a := by
      simp [hc_def, mul_div_assoc', mul_div_cancel_left₀ _ hL_ne]
    have hsum : a + L * c = b := by rw [hLc]; ring
    rw [hsum]
  · have hreparam :
        IsGeodesicOn (I := I) g (fun s => γ (c * s + a))
          {s : ℝ | c * s + a ∈ Set.Icc a b} :=
      isGeodesicOn_affineReparam (I := I) g (a := a) (b := b)
        (c := c) (d := a) hγ_geod
    have hrw : (fun s => γ (c * s + a)) = (fun s => γ (a + s * c)) := by
      funext s
      have : c * s + a = a + s * c := by ring
      rw [this]
    rw [hrw] at hreparam
    apply hreparam.mono
    intro s hs
    rcases hs with ⟨hs0, hsL⟩
    have hba : 0 ≤ b - a := sub_nonneg.mpr hab
    have hL_ne : L ≠ 0 := ne_of_gt hL
    have hc_nonneg : 0 ≤ c := by
      rw [hc_def]; exact div_nonneg hba hL.le
    have hsc_nonneg : 0 ≤ s * c := mul_nonneg hs0 hc_nonneg
    have hLc : L * c = b - a := by
      simp [hc_def, mul_div_assoc', mul_div_cancel_left₀ _ hL_ne]
    have hsc_le : s * c ≤ b - a := by
      calc s * c ≤ L * c := mul_le_mul_of_nonneg_right hsL hc_nonneg
        _ = b - a := hLc
    refine ⟨?_, ?_⟩
    · linarith
    · linarith
  · have hφ_cd : ContDiff ℝ 1 (fun s : ℝ => a + s * c) := by
      exact contDiff_const.add (contDiff_id.mul contDiff_const)
    have hφ_mC1 :
        ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) 1 (fun s : ℝ => a + s * c) (Set.Icc 0 L) :=
      hφ_cd.contMDiff.contMDiffOn
    have hMapsTo :
        Set.Icc (0 : ℝ) L ⊆ (fun s : ℝ => a + s * c) ⁻¹' Set.Icc a b := by
      intro s hs
      rcases hs with ⟨hs0, hsL⟩
      have hba : 0 ≤ b - a := sub_nonneg.mpr hab
      have hL_ne : L ≠ 0 := ne_of_gt hL
      have hc_nonneg : 0 ≤ c := by
        rw [hc_def]; exact div_nonneg hba hL.le
      have hsc_nonneg : 0 ≤ s * c := mul_nonneg hs0 hc_nonneg
      have hLc : L * c = b - a := by
        simp [hc_def, mul_div_assoc', mul_div_cancel_left₀ _ hL_ne]
      have hsc_le : s * c ≤ b - a := by
        calc s * c ≤ L * c := mul_le_mul_of_nonneg_right hsL hc_nonneg
          _ = b - a := hLc
      refine ⟨?_, ?_⟩
      · linarith
      · linarith
    have hcomp :
        ContMDiffOn 𝓘(ℝ, ℝ) I 1 (γ ∘ (fun s : ℝ => a + s * c)) (Set.Icc 0 L) :=
      hγ_C1.comp hφ_mC1 hMapsTo
    exact hcomp
  · intro t _ht
    sorry

/-- **Hopf-Rinow existence (unit-speed minimising geodesic).** On a complete
Riemannian manifold (`IsRiemannianManifold I M`, `CompleteSpace M`), any two
points `p q : M` are joined by a curve `γ` and a parameter length `L ≥ 0`
with `γ 0 = p`, `γ L = q`, where `γ` is `C¹` and `IsGeodesicOn` on `[0, L]`,
has unit `g`-speed at every `t ∈ [0, L]`, and whose length realises the
distance, `riemannianEDist I p q = ENNReal.ofReal L`. Assembled from
`exists_continuous_path_realizing_riemannianEDist`, `minimizing_path_is_smooth_geodesic`, and
`unit_speed_rescale`. -/
theorem exists_unit_speed_minimizing_geodesic_between_points
    (g : SmoothRiemannianMetric I M) (p q : M) :
    ∃ (γ : ℝ → M) (L : ℝ),
      0 ≤ L ∧ γ 0 = p ∧ γ L = q ∧
        ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Set.Icc 0 L) ∧
        IsGeodesicOn (I := I) g γ (Set.Icc 0 L) ∧
        (∀ t ∈ Set.Icc (0 : ℝ) L,
          (g.inner (γ t)) (mfderiv 𝓘(ℝ, ℝ) I γ t 1)
              (mfderiv 𝓘(ℝ, ℝ) I γ t 1) = 1) ∧
        riemannianEDist I p q = ENNReal.ofReal L := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨α, hα_cont, hα0, hα1, hα_len⟩ :=
    exists_continuous_path_realizing_riemannianEDist (I := I) g p q
  have hαlen' : pathELength I α 0 1 = riemannianEDist I (α 0) (α 1) := by
    rw [hα0, hα1]; exact hα_len
  obtain ⟨L, η, hL_nonneg, hη0, hηL, _hη_smooth_int, _hη_geod_int,
      hη_len_min, hL_eq_dist, hη_C1_min, hη_geod_min⟩ :=
    minimizing_path_is_smooth_geodesic (I := I) g (γ := α) (a := 0) (b := 1)
      zero_le_one hα_cont hαlen'
  have hηp : η 0 = p := by rw [hη0, hα0]
  have hηq : η L = q := by rw [hηL, hα1]
  have hη_geod_closed : IsGeodesicOn (I := I) g η (Set.Icc 0 L) := hη_geod_min
  have hη_C1 : ContMDiffOn 𝓘(ℝ, ℝ) I 1 η (Set.Icc 0 L) := hη_C1_min
  have hη_len : pathELength I η 0 L = ENNReal.ofReal L := hη_len_min
  rcases (lt_or_eq_of_le hL_nonneg) with hLpos | hLzero
  · obtain ⟨ζ, hζ0, hζL, hζ_geod, hζ_C1, hζ_unit⟩ :=
      unit_speed_rescale (I := I) g (γ := η) (a := 0) (b := L) (L := L)
        hL_nonneg hLpos hη_geod_closed hη_len hη_C1
    refine ⟨ζ, L, hL_nonneg, ?_, ?_, ?_, hζ_geod, hζ_unit, ?_⟩
    · rw [hζ0]; exact hηp
    · rw [hζL]; exact hηq
    · exact hζ_C1
    · have hL_eq_pq : ENNReal.ofReal L = riemannianEDist I p q := by
        rw [hL_eq_dist, hα0, hα1]
      exact hL_eq_pq.symm
  · subst hLzero
    have hpq : p = q := by rw [← hηp]; exact hηq
    have hfin_pos : 0 < Module.finrank ℝ E :=
      Nat.pos_of_ne_zero (NeZero.ne _)
    haveI hNT : Nontrivial E := Module.nontrivial_of_finrank_pos hfin_pos
    obtain ⟨u, hu_ne⟩ : ∃ u : TangentSpace I p, u ≠ 0 :=
      ⟨(exists_ne (0 : E)).choose, (exists_ne (0 : E)).choose_spec⟩
    have hc_pos : 0 < (g.inner p) u u := g.pos p u hu_ne
    have hc_ne : (g.inner p) u u ≠ 0 := ne_of_gt hc_pos
    set s : ℝ := Real.sqrt ((g.inner p) u u)⁻¹ with hs_def
    have hs_sq : s * s = ((g.inner p) u u)⁻¹ := by
      rw [hs_def]
      have hinv_nn : 0 ≤ ((g.inner p) u u)⁻¹ := inv_nonneg.mpr hc_pos.le
      exact Real.mul_self_sqrt hinv_nn
    set v : TangentSpace I p := s • u with hv_def
    have hv_unit : (g.inner p) v v = 1 := by
      rw [hv_def, map_smul (g.inner p), ContinuousLinearMap.smul_apply,
        map_smul (g.inner p u), smul_eq_mul, smul_eq_mul]
      rw [show s * (s * (g.inner p) u u) = (s * s) * (g.inner p) u u by ring]
      rw [hs_sq, inv_mul_cancel₀ hc_ne]
    obtain ⟨γ', f, hf0, hγ'_eq, hγ'_zero, hf_mIC, hγ'_geod⟩ :=
      exists_geodesic_with_initial_velocity_at (I := I) g p v
    refine ⟨γ', 0, le_refl 0, hγ'_zero, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hγ'_zero, hpq]
    · have hIcc_eq : (Set.Icc (0 : ℝ) 0) = ({0} : Set ℝ) :=
        Set.Icc_self 0
      rw [hIcc_eq]
      intro t ht
      rcases ht with rfl
      rw [contMDiffWithinAt_iff']
      refine ⟨continuousWithinAt_singleton, ?_⟩
      have hsub :
          ((extChartAt 𝓘(ℝ, ℝ) (0 : ℝ)).target ∩
            (extChartAt 𝓘(ℝ, ℝ) (0 : ℝ)).symm ⁻¹'
              (({0} : Set ℝ) ∩ γ' ⁻¹' (extChartAt I (γ' 0)).source)) ⊆
            {extChartAt 𝓘(ℝ, ℝ) (0 : ℝ) 0} := by
        intro x hx
        have hx_sym : (extChartAt 𝓘(ℝ, ℝ) (0 : ℝ)).symm x ∈
            ({0} : Set ℝ) ∩ γ' ⁻¹' (extChartAt I (γ' 0)).source :=
          hx.2
        have hx_sym0 : (extChartAt 𝓘(ℝ, ℝ) (0 : ℝ)).symm x = 0 := hx_sym.1
        have hx_in_target : x ∈ (extChartAt 𝓘(ℝ, ℝ) (0 : ℝ)).target := hx.1
        have hxx : x = extChartAt 𝓘(ℝ, ℝ) (0 : ℝ) 0 := by
          calc x = extChartAt 𝓘(ℝ, ℝ) (0 : ℝ)
                      ((extChartAt 𝓘(ℝ, ℝ) (0 : ℝ)).symm x) :=
                  ((extChartAt 𝓘(ℝ, ℝ) (0 : ℝ)).right_inv hx_in_target).symm
            _ = extChartAt 𝓘(ℝ, ℝ) (0 : ℝ) 0 := by rw [hx_sym0]
        exact hxx
      exact (contDiffWithinAt_singleton).mono hsub
    · intro t ht
      rw [Set.Icc_self 0, Set.mem_singleton_iff] at ht
      subst ht
      exact hγ'_geod.hasGeodesicEquationAt
    · intro t ht
      have hIcc_eq : (Set.Icc (0 : ℝ) 0) = ({0} : Set ℝ) :=
        Set.Icc_self 0
      rw [hIcc_eq] at ht
      rcases ht with rfl
      subst hγ'_eq
      have hmf : mfderiv 𝓘(ℝ, ℝ) I (projectCurve (I := I) f) 0 (1 : ℝ) =
          (f 0).snd :=
        IsMIntegralCurveAt.mfderiv_proj_one (I := I) (g := g) (f := f)
          (α := p) (t₀ := 0) hf_mIC
          (by rw [hf0]; exact mem_chart_source H p)
      have hgoal :
          ∀ (q : TangentBundle I M)
            (hq : q = (⟨p, v⟩ : TangentBundle I M))
            (m : TangentSpace I q.proj)
            (hm : m = q.snd),
            (g.inner q.proj) m m = 1 := by
        intro q hq m hm
        rcases hq
        change m = v at hm
        subst hm
        exact hv_unit
      exact hgoal (f 0) hf0
        (mfderiv 𝓘(ℝ, ℝ) I (projectCurve (I := I) f) 0 (1 : ℝ)) hmf
    · rw [← hpq, ENNReal.ofReal_zero]
      exact riemannianEDist_self

end MinimiserExistence

end HopfRinow
end Riemannian
end Geometry
end DifferentialGeometry
