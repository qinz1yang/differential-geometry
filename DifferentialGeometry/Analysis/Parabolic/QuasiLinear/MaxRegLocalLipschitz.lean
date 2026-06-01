import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.MaxRegSmallTime
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.BallRetraction

/-!
# Small-time strong existence for a locally Lipschitz nonlinearity

The small-time engine `quasilinear_strong_existence_smallTime`
(`MaxRegSmallTime`) produces, for **any** global Lipschitz constant `L`, a
positive horizon `T_L` and a strong solution of `∂_t u = Δ_∇ u + N(u)` on
`(0, T_L]`.  It requires `N : H^{a+1} → Hᵃ` to be *globally* `LipschitzWith L`.

Genuinely interesting nonlinearities (e.g. the Ricci–DeTurck right-hand side) are
only **locally** Lipschitz: Lipschitz on each ball around the initial datum, with
a constant that depends on the radius and may blow up as the radius grows.  This
file bridges the gap by the standard **truncation** device.

## The truncation device

Fix a radius `R > 0` and the centre `u₀' = ι(u₀)`, the inclusion of the initial
datum into `H^{a+1}`.  The **recentred radial retraction**

  `ρ(v) := u₀' + ballRetraction R (v − u₀')`

is the metric projection onto the closed `H^{a+1}`-ball `closedBall u₀' R`:

* it is globally `1`-Lipschitz (`recenteredBallRetraction_lipschitzWith`,
  composition of the nonexpansive `ballRetraction` with two isometric shifts);
* it maps every point into `closedBall u₀' R`
  (`recenteredBallRetraction_mapsTo`);
* it fixes every point of `closedBall u₀' R`
  (`recenteredBallRetraction_eq_self_of_mem`).

The **truncated nonlinearity** `Ñ_R := N ∘ ρ` is therefore *globally*
`LipschitzWith (L_R · 1)` whenever `N` is `LipschitzOnWith L_R` on
`closedBall u₀' R` (`truncatedNonlin_lipschitzWith`), and it agrees with `N` on
the ball (`truncatedNonlin_eq_of_mem`).

## Main results

* `truncatedNonlin_lipschitzWith` — `Ñ_R` is globally Lipschitz.
* `quasilinear_strong_existence_truncated_smallTime_ofCompact` — the small-time
  engine applied to `Ñ_R`: a horizon `T > 0` and a strong solution of the
  **truncated** equation `∂_t u = Δ_∇ u + Ñ_R(u)`.  This is *unconditional*
  (no stays-in-ball hypothesis); it is the honest globally-Lipschitz output for
  the truncated map.
* `nemytskiiHa1_truncated_eqOn_ball` — the reduction lemma: on the event that the
  `H^{a+1}`-view solution field stays a.e. in `closedBall u₀' R`, the truncated
  Nemytskii forcing `t ↦ Ñ_R(field t)` agrees a.e. with the genuine nonlinear
  forcing `t ↦ N(field t)`.
* `de_simon_quasilinear_tensor_heat_short_time_existence_locally_lipschitz_of_compact_resolvent` — **the
  headline cutoff**: for a locally-Lipschitz `N` and a radius `R` on whose ball
  the constructed `H^{a+1}` field stays (a.e. in time), there is a horizon `T > 0`
  and a strong solution of the genuine equation `∂_t u = Δ_∇ u + N(u)`, with the
  forcing `gforce` represented a.e. by `t ↦ N(field_{a+1} t)`.

## The remaining analytic input (`stays-in-ball`)

The headline theorem still carries one genuine analytic hypothesis: that the
constructed `H^{a+1}`-view solution field
`maxRegDuhamelSolFieldHa1 … u₀ gStar` lies, for a.e. `t`, in
`closedBall u₀' R`.  This is **not** a restatement of the conclusion: it is a
quantitative smallness statement about the explicit fixed-point field, and it is
the only piece not produced by the engine.

It is the standard "the mild solution starts at `u₀'` and varies continuously, so
it stays near `u₀'` on a short enough interval" fact.  Proving it
*unconditionally* (thereby removing the hypothesis and choosing `R, T` internally)
requires a **time-continuity estimate of the `H^{a+1}`-view field at `t = 0`**
that the current spectral-synthesis API does not expose: the field
`maxRegDuhamelSolFieldHa1` is built by `timeL2OfModes` as a pure
`L²([0,T]; H^{a+1})` element, with no continuous-in-time `H^{a+1}`-valued
representative.  The carrier `timeH1` does carry a continuous `Hᵃ`-valued
representative (`TimeSobolev.timeH1.continuousOn_toFun`, `toFun_zero`), but at the
*lower* scale `a`, not at the scale `a + 1` where `N` is evaluated.

The precise missing lemma is a **uniform-in-time `H^{a+1}` modulus of continuity
at `0`** for the subcritical Duhamel field:

  `∀ ε > 0, ∃ T' ∈ (0, T], ∀ᵐ t ≤ T',`
    `‖maxRegDuhamelSolFieldHa1 … u₀ gforce t − ι(u₀)‖_{H^{a+1}} ≤ ε`,

with the modulus controlled in terms of `‖gforce‖_{L²([0,T];Hᵃ)}` and the
`H^{a+2}`-norm of `u₀` (the homogeneous part contributes `‖e^{tΔ}u₀ − u₀‖ → 0` by
spectral dominated convergence; the Duhamel part is `O(√T)` by the `√T`-decay
`maximalRegularitySolFieldHa1_norm_le`).  With that lemma one chooses
`R := ‖∇²-bound‖`-type radius, then shrinks the horizon to `T'` so the field stays
in `closedBall u₀' R`, discharging the hypothesis and yielding the fully
unconditional cutoff.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace QuasiLinear

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable {g : SmoothRiemannianMetric I M} {r s : ℕ}
variable {a : ℝ} {T : ℝ}

section Recentre

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- **The recentred radial retraction** onto the closed ball of radius `R`
centred at `c`: points inside are fixed, points outside are pulled radially onto
the boundary sphere of `closedBall c R`. -/
noncomputable def recenteredBallRetraction (c : X) (R : ℝ) (v : X) : X :=
  c + ballRetraction R (v - c)

/-- The recentred retraction is globally `1`-Lipschitz: it is the nonexpansive
`ballRetraction` conjugated by the isometric shift `v ↦ v − c`. -/
theorem recenteredBallRetraction_lipschitzWith {R : ℝ} (hR : 0 ≤ R) (c : X) :
    LipschitzWith 1 (recenteredBallRetraction c R) := by
  have hshift : LipschitzWith 1 (fun v : X => v - c) :=
    LipschitzWith.of_dist_le_mul fun x y => by
      rw [NNReal.coe_one, one_mul, dist_sub_right]
  have hadd : LipschitzWith 1 (fun w : X => c + w) :=
    LipschitzWith.of_dist_le_mul fun x y => by
      rw [NNReal.coe_one, one_mul, dist_add_left]
  have hcomp :
      LipschitzWith (1 * (1 * 1))
        (fun v : X => c + ballRetraction R (v - c)) :=
    hadd.comp ((lipschitzWith_ballRetraction (X := X) hR).comp hshift)
  simpa [recenteredBallRetraction] using hcomp

/-- The recentred retraction maps every point into the closed ball
`closedBall c R`. -/
theorem recenteredBallRetraction_mapsTo {R : ℝ} (hR : 0 ≤ R) (c : X) :
    Set.MapsTo (recenteredBallRetraction c R) Set.univ (Metric.closedBall c R) := by
  intro v _
  rw [Metric.mem_closedBall, dist_eq_norm, recenteredBallRetraction,
    add_comm c _, add_sub_cancel_right]
  exact ballRetraction_mem_closedBall hR (v - c)

/-- The recentred retraction fixes every point of the closed ball
`closedBall c R`. -/
theorem recenteredBallRetraction_eq_self_of_mem {R : ℝ} {c v : X}
    (hv : v ∈ Metric.closedBall c R) :
    recenteredBallRetraction c R v = v := by
  rw [Metric.mem_closedBall, dist_eq_norm] at hv
  rw [recenteredBallRetraction, ballRetraction_eq_self_of_mem hv, add_sub_cancel]

end Recentre

section Truncation

variable {N : tensorHs (I := I) (M := M) g r s (a + 1) →
    tensorHs (I := I) (M := M) g r s a}

/-- **The truncated nonlinearity** `Ñ_R(v) := N (ρ(v))`, the composition of `N`
with the recentred radial retraction `ρ` onto the closed ball of radius `R`
about the centre `u₀'`.  It coincides with `N` on `closedBall u₀' R` and is
globally Lipschitz. -/
def truncatedNonlin (N : tensorHs (I := I) (M := M) g r s (a + 1) →
      tensorHs (I := I) (M := M) g r s a)
    (u₀' : tensorHs (I := I) (M := M) g r s (a + 1)) (R : ℝ) :
    tensorHs (I := I) (M := M) g r s (a + 1) →
      tensorHs (I := I) (M := M) g r s a :=
  fun v => N (recenteredBallRetraction u₀' R v)

/-- The truncated nonlinearity agrees with `N` on the closed ball
`closedBall u₀' R`: there the recentred retraction is the identity. -/
theorem truncatedNonlin_eq_of_mem
    {u₀' : tensorHs (I := I) (M := M) g r s (a + 1)} {R : ℝ}
    {v : tensorHs (I := I) (M := M) g r s (a + 1)}
    (hv : v ∈ Metric.closedBall u₀' R) :
    truncatedNonlin (I := I) (M := M) N u₀' R v = N v := by
  rw [truncatedNonlin, recenteredBallRetraction_eq_self_of_mem hv]

/-- **The truncated nonlinearity is globally Lipschitz** with the *local*
Lipschitz constant `L_R` of `N` on `closedBall u₀' R`: it is the composition of
the `L_R`-Lipschitz-on-the-ball map `N` with the globally `1`-Lipschitz
recentred retraction, which lands inside the ball. -/
theorem truncatedNonlin_lipschitzWith {L_R : ℝ≥0}
    {u₀' : tensorHs (I := I) (M := M) g r s (a + 1)} {R : ℝ} (hR : 0 ≤ R)
    (hN : LipschitzOnWith L_R N (Metric.closedBall u₀' R)) :
    LipschitzWith L_R (truncatedNonlin (I := I) (M := M) N u₀' R) := by
  have hρ : LipschitzOnWith 1 (recenteredBallRetraction u₀' R) Set.univ :=
    lipschitzOnWith_univ.mpr
      (recenteredBallRetraction_lipschitzWith (X := _) hR u₀')
  have hmaps := recenteredBallRetraction_mapsTo (X := _) hR u₀'
  have hcomp : LipschitzOnWith (L_R * 1)
      (N ∘ recenteredBallRetraction u₀' R) Set.univ :=
    hN.comp hρ hmaps
  rw [mul_one] at hcomp
  have : LipschitzWith L_R (N ∘ recenteredBallRetraction u₀' R) :=
    lipschitzOnWith_univ.mp hcomp
  exact this

end Truncation

/-- **Truncated small-time strong existence.**  For a locally-Lipschitz
nonlinearity `N` — specifically, `LipschitzOnWith L_R N (closedBall u₀' R)` where
`u₀' = ι(u₀)` is the inclusion of the initial datum into `H^{a+1}` — the
small-time engine applied to the globally-Lipschitz truncated nonlinearity
`Ñ_R := truncatedNonlin N u₀' R` yields a positive horizon and, for every short
time, a strong solution of the **truncated** equation `∂_t u = Δ_∇ u + Ñ_R(u)`,
`u(0) = u₀`.  No stays-in-ball hypothesis is needed for the truncated equation. -/
theorem quasilinear_strong_existence_truncated_smallTime_ofCompact
    {N : tensorHs (I := I) (M := M) g r s (a + 1) →
      tensorHs (I := I) (M := M) g r s a}
    {L_R : ℝ≥0} {R : ℝ} (hR : 0 ≤ R)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    (hN : LipschitzOnWith L_R N (Metric.closedBall
      (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        (show (a + 1) ≤ a + 2 by linarith) u₀) R)) :
    ∃ T_R : ℝ, 0 < T_R ∧ ∀ {T : ℝ} (hT : 0 < T) (_hTR : T ≤ T_R) (hT1 : T ≤ 1),
      ∃ (u : MaxRegSolutionSpace (I := I) (M := M) a T)
        (gforce : timeL2 (tensorHs (I := I) (M := M) g r s a) T),
        u = maxRegDuhamelMap (I := I) (M := M) a hT hT1 u₀ gforce ∧
          gforce = nemytskiiHa1 (I := I) (M := M)
              (truncatedNonlin_lipschitzWith (I := I) (M := M) hR hN)
              (maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 u₀ gforce) ∧
          TimeSobolev.timeH1.trace0 _ T u =
              tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
                (show a ≤ a + 2 by linarith) u₀ ∧
          TimeSobolev.timeH1.timeDeriv _ T u =
            timeScaleLaplacian (I := I) (M := M) a
                (maxRegDuhamelSolField (I := I) (M := M) a hT hT1 u₀ gforce) +
              nemytskiiHa1 (I := I) (M := M)
                (truncatedNonlin_lipschitzWith (I := I) (M := M) hR hN)
                (maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 u₀
                  gforce) :=
  quasilinear_strong_existence_smallTime (I := I) (M := M)
    (h_compact := h_compact) u₀
    (truncatedNonlin_lipschitzWith (I := I) (M := M) hR hN)

/-- **The truncated forcing agrees a.e. with the genuine nonlinear forcing on the
stays-in-ball event.**  If the `H^{a+1}`-view field `field` lies, for a.e. `t`,
in `closedBall u₀' R`, then the truncated Nemytskii image
`nemytskiiHa1 (truncated) field` is represented a.e. by `t ↦ N(field t)`: on the
ball `Ñ_R(field t) = N(field t)`. -/
theorem nemytskiiHa1_truncated_eqOn_ball
    {N : tensorHs (I := I) (M := M) g r s (a + 1) →
      tensorHs (I := I) (M := M) g r s a}
    {L_R : ℝ≥0} {R : ℝ} (hR : 0 ≤ R)
    {u₀' : tensorHs (I := I) (M := M) g r s (a + 1)}
    (hN : LipschitzOnWith L_R N (Metric.closedBall u₀' R))
    (field : timeL2 (tensorHs (I := I) (M := M) g r s (a + 1)) T)
    (hball : ∀ᵐ t ∂(timeMeasure T), field t ∈ Metric.closedBall u₀' R) :
    nemytskiiHa1 (I := I) (M := M)
        (truncatedNonlin_lipschitzWith (I := I) (M := M) hR hN) field =ᵐ[timeMeasure T]
      fun t => N (field t) := by
  have hcoe := nemytskiiHa1_coeFn (I := I) (M := M)
    (truncatedNonlin_lipschitzWith (I := I) (M := M) hR hN) field
  filter_upwards [hcoe, hball] with t ht htmem
  rw [ht, truncatedNonlin_eq_of_mem (I := I) (M := M) htmem]

/-- **Small-time strong existence for a locally Lipschitz nonlinearity — the
cutoff.**

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, a real Sobolev
exponent `a`, an initial datum `u₀ ∈ H^{a+2}`, a radius `R ≥ 0`, and a
nonlinearity `N : H^{a+1} → Hᵃ` that is **only locally Lipschitz** —
`LipschitzOnWith L_R N` on the closed `H^{a+1}`-ball `closedBall (ι u₀) R` around
the included initial datum (no global Lipschitz constant assumed) — there is a
positive horizon `T_R` such that, on every short interval `(0, T]` on which the
constructed `H^{a+1}`-view solution field **stays a.e. in that ball**, there is a
strong solution `u ∈ H¹([0,T]; Hᵃ)` of the genuine quasi-linear tensor heat
equation

  `∂_t u = Δ_∇ u + N(u)`,  `u(0) = u₀`,

with the forcing `gforce` represented a.e. by `t ↦ N(field_{a+1} t)`, i.e. the
pointwise-in-time nonlinearity along the `H^{a+1}`-view solution field.

The construction truncates `N` to the globally-Lipschitz
`Ñ_R := truncatedNonlin N (ι u₀) R`, runs the any-global-`L` small-time engine
on `Ñ_R` to obtain the strong solution of `∂_t u = Δ_∇ u + Ñ_R(u)`, and then —
on the stays-in-ball event — replaces `Ñ_R` by `N` along the field via
`nemytskiiHa1_truncated_eqOn_ball` (they agree on the ball).

The stays-in-ball hypothesis `hstay` is the **only** non-engine analytic input;
it is a smallness statement about the explicit fixed-point field, **not** a
restatement of the conclusion (see the module docstring for the precise
time-continuity lemma that would discharge it unconditionally). -/
theorem de_simon_quasilinear_tensor_heat_short_time_existence_locally_lipschitz_of_compact_resolvent
    {N : tensorHs (I := I) (M := M) g r s (a + 1) →
      tensorHs (I := I) (M := M) g r s a}
    {L_R : ℝ≥0} {R : ℝ} (hR : 0 ≤ R)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    (hN : LipschitzOnWith L_R N (Metric.closedBall
      (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        (show (a + 1) ≤ a + 2 by linarith) u₀) R)) :
    ∃ T_R : ℝ, 0 < T_R ∧ ∀ {T : ℝ} (hT : 0 < T) (_hTR : T ≤ T_R) (hT1 : T ≤ 1)
        (gforce : timeL2 (tensorHs (I := I) (M := M) g r s a) T)
        (_hfix : gforce = nemytskiiHa1 (I := I) (M := M)
            (truncatedNonlin_lipschitzWith (I := I) (M := M) hR hN)
            (maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 u₀ gforce))
        (_hstay : ∀ᵐ t ∂(timeMeasure T),
            maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 u₀ gforce t ∈
              Metric.closedBall
                (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
                  (show (a + 1) ≤ a + 2 by linarith) u₀) R),
      ∃ u : MaxRegSolutionSpace (I := I) (M := M) a T,
        u = maxRegDuhamelMap (I := I) (M := M) a hT hT1 u₀ gforce ∧
          gforce =ᵐ[timeMeasure T]
            (fun t => N (maxRegDuhamelSolFieldHa1 (I := I) (M := M)
              a hT hT1 u₀ gforce t)) ∧
          TimeSobolev.timeH1.trace0 _ T u =
              tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
                (show a ≤ a + 2 by linarith) u₀ ∧
          TimeSobolev.timeH1.timeDeriv _ T u =
            timeScaleLaplacian (I := I) (M := M) a
                (maxRegDuhamelSolField (I := I) (M := M) a hT hT1 u₀ gforce) +
              nemytskiiHa1 (I := I) (M := M)
                (truncatedNonlin_lipschitzWith (I := I) (M := M) hR hN)
                (maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 u₀
                  gforce) := by
  refine ⟨smallTimeHorizon L_R, smallTimeHorizon_pos L_R, ?_⟩
  intro T hT hTR hT1 gforce hfix hstay
  refine ⟨maxRegDuhamelMap (I := I) (M := M) a hT hT1 u₀ gforce, rfl, ?_, ?_, ?_⟩
  · conv_lhs => rw [hfix]
    exact nemytskiiHa1_truncated_eqOn_ball (I := I) (M := M) hR hN
      (maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 u₀ gforce) hstay
  · exact maxRegDuhamelMap_trace0 (I := I) (M := M) (a := a) (T := T)
      hT hT1 u₀ gforce
  · rw [maxRegDuhamelMap_timeDeriv_eq (I := I) (M := M)
      (h_compact := h_compact) (a := a) (T := T) hT hT1 u₀ gforce]
    exact congrArg₂ (· + ·) rfl hfix

end QuasiLinear
end Parabolic
end Analysis
end DifferentialGeometry

end
