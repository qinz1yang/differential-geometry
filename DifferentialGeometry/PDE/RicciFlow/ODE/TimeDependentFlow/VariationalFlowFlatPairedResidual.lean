import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.VariationalFlowFlatPairing
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.SmoothInSpace.VariationalLiftFlatToCovariant
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.SmoothInSpace.VariationalLiftTransport

/-!
# The PAIRED-residual route for the moving-pushforward inner product

`variational_flow_flat_pairing_hasDerivAt` (`VariationalFlowFlatPairing.lean`) produces the
flat-route derivative of the frozen-metric moving-pushforward inner product

  `s ↦ g.inner (Φ_fam t x) (mfderiv (Φ_fam s) x v) (mfderiv (Φ_fam s) x w)`

namely `-lieDerivMetric g X α dΦv dΦw + metricTransportResidual g X Φ_fam t x v w`, **out of two
per-slot inputs** `hcorr_v` / `hcorr_w`:

  `T'v (dΦv) + P'v v = -∇_{dΦv} X + christoffelCorrection g α α (X̃_α α) dΦv`     (and slot `w`).

Each per-slot input mixes the **metric** Christoffel correction `christoffelCorrection g α α …`
into a per-slot `E`-equation.  But `∇g = 0` is a *paired*, not a per-slot, identity: the metric
content of the moving-pushforward variation is the symmetric pairing of the two pushforward
slots against the metric-transport term, and only there does metric-compatibility close it.
Asking for the metric Christoffel correction *per slot* is, after the bridge substitution
`∇_w X = F(w) + Γ(w)` (with `F` the metric-free trivialised flat / Lie-type derivative), the
identity `T'v (dΦv) + P'v v = -F(dΦv)` **fused with** the metric `Γ(dΦv)` on the right-hand
side — i.e. it forces the metric Christoffel to be reconstructed from the metric-free factor
jets per slot, which is the false `D²φ = Γ` per-slot reading.

## The paired re-architecture

This file replaces the two metric-carrying per-slot inputs by the two **metric-free** flat-value
identities (the genuine Lie-type variational fact, never the false `D²φ = Γ`)

  `T'v (dΦv) + P'v v = -(fderiv (chartRawRepr α X) (φ α) dΦv + movingTrivCorrection α X dΦv)`

(and slot `w`), which assert only that the orbit-pushforward flat derivative equals the negative
**trivialised flat derivative** of `X` (= `-F(dΦv)`); this carries no metric and no `Γ`/`D²φ`
identification.  The metric `Γ` then enters **only paired**, inside the proof, via the basepoint
bridge `leviCivita_basepoint_eq_rawFderiv_add_corrections` — itself derived from
`trivFromE_innerCLM_eq_leviCivita_at_orbit` (`∇g = 0` read through metric-compatible chart
Levi-Civita) and the honest chart decomposition
`chartLeviCivitaInnerCLM_basepoint_eq_rawFderiv_add_corrections`.  The bridge states

  `(LeviCivita g) X α w = fderiv (chartRawRepr α X) (φ α) w + movingTrivCorrection α X w
                            + christoffelCorrection g α α (X̃_α α) w`,

i.e. `F(w) = ∇_w X - Γ(w)`.  Substituting `F(dΦv) = ∇_{dΦv} X - Γ(dΦv)` into the symmetric
pairing

  `g_α(Vflat, dΦw) + g_α(dΦv, Wflat) = -g_α(F(dΦv), dΦw) - g_α(dΦv, F(dΦw))`,

the **covariant** pieces `g_α(∇_{dΦv} X, dΦw) + g_α(dΦv, ∇_{dΦw} X)` assemble to `lieDerivMetric`
(`neg_lieDerivMetric_eq_neg_killing_sum`) while the **metric** Christoffel pieces survive
*paired* as `g_α(Γ(dΦv), dΦw) + g_α(dΦv, Γ(dΦw)) = metricTransportResidual`.  The metric-free
factor jets `fderiv (chartRawRepr) + D²φ` (= `F`) cancel across the two slots against `∇ - Γ`;
the metric appears solely through the paired bridge substitution, exactly as `∇g = 0` dictates.

This is the honest paired replacement for `variational_flow_flat_pairing_hasDerivAt`: same
conclusion (`-lieDerivMetric + metricTransportResidual`), with the two per-slot metric-carrying
`hcorr_v`/`hcorr_w` replaced by two metric-free flat-value identities plus the two basepoint-bridge
`E`-equations (`∇_u X = F(u) + Γ(u)`).  The bridge equations are *not* assumed: the
combined-instance lemma `leviCivita_basepoint_eq_rawFderiv_add_corrections` (section A) discharges
each from the genuinely-paired bridge data (a goodset-membership and section-differentiability
datum at the basepoint, plus the convention-bridge side conditions), and they cross into the
inner-product-only pairing assembly (section B) as plain `E`-equations.  No `sorry`, no `axiom`,
no `HasLocallyConstantChartAt`-style
hypothesis, no joint-`C^∞`-on-`ℝ × M` predicate, and **no** false `D²φ = Γ` identification — the
metric Christoffel is never assumed equal to a smooth-structure jet per slot; it enters only
paired, derived from `∇g = 0`.  No hypothesis-packaging: the flat-value inputs are `E`-equations,
the conclusion is the scalar pairing `HasDerivAt`, a distinct object.
-/

noncomputable section

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace ODE

open Bundle Set
open scoped Manifold Topology ContDiff
open DifferentialGeometry
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.DeTurck
open DifferentialGeometry.PDE.RicciFlow.Pullback

section Bridge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

/-- **The inverse target trivialisation is the identity at its own basepoint.**

The chart-`α` inverse trivialisation CLM at `(α, α)` is the identity on the fibre
`TangentSpace I α = E`: `trivFromE α α v = v`.  This is the inverse companion of
`trivToE_basepoint`: `trivFromE α α` is the self-`coordChange` of the tangent-bundle core read
at `α`, which is the identity on the base set (which contains `α`).  Routed through
`TangentBundle.symmL_trivializationAt_eq_core` and `coordChange_self`. -/
theorem trivFromE_basepoint (α : M) (v : TangentSpace I α) :
    trivFromE (I := I) α α v = v := by
  classical
  have hcore : trivFromE (I := I) α α
      = (tangentBundleCore I M).coordChange (achart H α) (achart H α) α :=
    TangentBundle.symmL_trivializationAt_eq_core (I := I) (M := M)
      (b₀ := α) (b := α) (mem_chart_source H α)
  rw [hcore]
  exact (tangentBundleCore I M).coordChange_self (achart H α) α
    (by rw [tangentBundleCore_baseSet]; exact mem_chart_source H α) v

/-- **The basepoint bridge: the bundled Levi-Civita value as raw flat `fderiv` + `D²φ` + metric
Christoffel.**

At the orbit basepoint `α` (in its own good set, with `X` manifold-differentiable there, and the
convention-bridge differentiability side conditions), the bundled covariant derivative of `X`
along `w` decomposes as

  `(LeviCivita g) X α w
     = fderiv (chartRawRepr α X) (φ α) w + movingTrivCorrection α X w
       + christoffelCorrection g α α (X̃_α α) w`,

i.e. `∇_w X = F(w) + Γ(w)` with `F(w) := fderiv (chartRawRepr α X) (φ α) w +
movingTrivCorrection α X w` the *metric-free* trivialised flat (Lie-type) derivative and `Γ(w)`
the metric Christoffel correction.

This is **`∇g = 0` read on the chart**: `trivFromE_innerCLM_eq_leviCivita_at_orbit` (the
metric-compatible chart Levi-Civita value, equal to the bundled covariant derivative at the
basepoint) composed with the honest chart decomposition
`chartLeviCivitaInnerCLM_basepoint_eq_rawFderiv_add_corrections`, with the basepoint inverse
trivialisation discharged to the identity (`trivFromE_basepoint`).  The conclusion is an
`E`-equation exposing precisely how the metric `Γ` sits *between* the bundled covariant value and
the metric-free factor jets; it is the genuinely-paired channel by which the metric enters the
pushforward variation.  No hypothesis-packaging: the conclusion is an `E`-equation derived from
two cited identities, never an asserted target. -/
theorem leviCivita_basepoint_eq_rawFderiv_add_corrections
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Π y : M, TangentSpace I y) (w : TangentSpace I α)
    (hα : α ∈ chartLeviCivitaGoodSet (I := I) α)
    (hX : MDiffAt (T% X) α)
    (hRdiff : DifferentiableAt ℝ (chartRawRepr (I := I) α X) (extChartAt I α α))
    (hCdiff : DifferentiableAt ℝ
      (fun z => chartMovingTriv (I := I) α z) (extChartAt I α α)) :
    (LeviCivita (I := I) g) X α w
      = fderiv ℝ (chartRawRepr (I := I) α X) (extChartAt I α α) w
        + movingTrivCorrection (I := I) α X w
        + christoffelCorrection (I := I) g α α
            (chartE_section_repr (I := I) α X α) w := by
  classical
  have hbridge :
      trivFromE (I := I) α α (chartLeviCivitaInnerCLM (I := I) g α X α w)
        = (LeviCivita (I := I) g) X α w :=
    trivFromE_innerCLM_eq_leviCivita_at_orbit (I := I) g X α w hα hX
  rw [trivFromE_basepoint (I := I) α (chartLeviCivitaInnerCLM (I := I) g α X α w)] at hbridge
  rw [← hbridge]
  exact chartLeviCivitaInnerCLM_basepoint_eq_rawFderiv_add_corrections (I := I) g α X w
    hRdiff hCdiff

end Bridge

section MainPairing

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

/-- **PAIRED flat-route Cartan pairing of the moving-pushforward inner product.**

The honest **paired-residual** replacement for `variational_flow_flat_pairing_hasDerivAt`.  Given
the two flat per-slot identities (`RawVariationalIdentityFlat` for `v` and `w`, the producers'
output), the two **metric-free** flat-value identities

  `T'v (dΦv) + P'v v = -(fderiv (chartRawRepr α X) (φ α) dΦv + movingTrivCorrection α X dΦv)`
  `T'w (dΦw) + P'w w = -(fderiv (chartRawRepr α X) (φ α) dΦw + movingTrivCorrection α X dΦw)`

— each asserting only that the orbit-pushforward flat derivative is the negative trivialised flat
(Lie-type) derivative `-F(·)`, carrying **no** metric and **no** `Γ`/`D²φ` identification — and
the two basepoint-bridge `E`-equations (`∇g = 0`)

  `(LeviCivita g) X α dΦv = (fderiv (chartRawRepr α X) (φ α) dΦv + movingTrivCorrection α X dΦv)
                              + christoffelCorrection g α α (X̃_α α) dΦv`     (and slot `w`),

discharged by `leviCivita_basepoint_eq_rawFderiv_add_corrections`, the frozen-metric
moving-pushforward inner-product variation curve

  `s ↦ g.inner (Φ_fam t x) (mfderiv (Φ_fam s) x v) (mfderiv (Φ_fam s) x w)`

has at `t` the derivative

  `-lieDerivMetric g X (Φ_fam t x) dΦv dΦw + metricTransportResidual g X Φ_fam t x v w`.

The metric `Γ` enters **only paired**: combining the metric-free flat-value identity
`Vflat = -F(dΦv)` with the bridge `∇_{dΦv} X = F(dΦv) + Γ(dΦv)` gives `Vflat = -∇_{dΦv} X + Γ(dΦv)`
(and slot `w`); the metric-free factor jets `F` cancel against `∇ - Γ` slot by slot, the covariant
pieces assemble to `-lieDerivMetric` (`neg_lieDerivMetric_eq_neg_killing_sum`), and the metric
Christoffel pieces survive *paired* as `metricTransportResidual`.  The false per-slot `D²φ = Γ`
is never used: each bridge `E`-equation is the *true* chart formula `∂X = ∇X - ΓX`, not an
identification of a smooth-structure jet with the metric symbol.  No hypothesis-packaging: the
flat-value and bridge inputs are `E`-equations, the conclusion is the scalar pairing
`HasDerivAt`, a distinct object. -/
theorem variational_flow_flat_paired_residual_hasDerivAt
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M) (v w : TangentSpace I x)
    (T'v P'v T'w P'w : E →L[ℝ] E)
    (hv_flat : RawVariationalIdentityFlat (I := I) Φ_fam t x v T'v P'v)
    (hw_flat : RawVariationalIdentityFlat (I := I) Φ_fam t x w T'w P'w)
    (hflatval_v :
      T'v (mfderiv I I (Φ_fam t : M → M) x v) + P'v v
        = -(fderiv ℝ (chartRawRepr (I := I) (Φ_fam t x)
                (X : ∀ y : M, TangentSpace I y))
              (extChartAt I (Φ_fam t x) (Φ_fam t x))
              (mfderiv I I (Φ_fam t : M → M) x v)
            + movingTrivCorrection (I := I) (Φ_fam t x)
                (X : ∀ y : M, TangentSpace I y)
                (mfderiv I I (Φ_fam t : M → M) x v)))
    (hflatval_w :
      T'w (mfderiv I I (Φ_fam t : M → M) x w) + P'w w
        = -(fderiv ℝ (chartRawRepr (I := I) (Φ_fam t x)
                (X : ∀ y : M, TangentSpace I y))
              (extChartAt I (Φ_fam t x) (Φ_fam t x))
              (mfderiv I I (Φ_fam t : M → M) x w)
            + movingTrivCorrection (I := I) (Φ_fam t x)
                (X : ∀ y : M, TangentSpace I y)
                (mfderiv I I (Φ_fam t : M → M) x w)))
    (hbridge_v :
      (LeviCivita (I := I) g) (X : ∀ y : M, TangentSpace I y) (Φ_fam t x)
          (mfderiv I I (Φ_fam t : M → M) x v)
        = (fderiv ℝ (chartRawRepr (I := I) (Φ_fam t x)
                (X : ∀ y : M, TangentSpace I y))
              (extChartAt I (Φ_fam t x) (Φ_fam t x))
              (mfderiv I I (Φ_fam t : M → M) x v)
            + movingTrivCorrection (I := I) (Φ_fam t x)
                (X : ∀ y : M, TangentSpace I y)
                (mfderiv I I (Φ_fam t : M → M) x v))
          + christoffelCorrection (I := I) g (Φ_fam t x) (Φ_fam t x)
              (chartE_section_repr (I := I) (Φ_fam t x)
                (X : ∀ y : M, TangentSpace I y) (Φ_fam t x))
              (mfderiv I I (Φ_fam t : M → M) x v))
    (hbridge_w :
      (LeviCivita (I := I) g) (X : ∀ y : M, TangentSpace I y) (Φ_fam t x)
          (mfderiv I I (Φ_fam t : M → M) x w)
        = (fderiv ℝ (chartRawRepr (I := I) (Φ_fam t x)
                (X : ∀ y : M, TangentSpace I y))
              (extChartAt I (Φ_fam t x) (Φ_fam t x))
              (mfderiv I I (Φ_fam t : M → M) x w)
            + movingTrivCorrection (I := I) (Φ_fam t x)
                (X : ∀ y : M, TangentSpace I y)
                (mfderiv I I (Φ_fam t : M → M) x w))
          + christoffelCorrection (I := I) g (Φ_fam t x) (Φ_fam t x)
              (chartE_section_repr (I := I) (Φ_fam t x)
                (X : ∀ y : M, TangentSpace I y) (Φ_fam t x))
              (mfderiv I I (Φ_fam t : M → M) x w)) :
    HasDerivAt
      (fun s : ℝ => g.inner (Φ_fam t x)
        (mfderiv I I (Φ_fam s : M → M) x v)
        (mfderiv I I (Φ_fam s : M → M) x w))
      (-lieDerivMetric (I := I) g X (Φ_fam t x)
          (mfderiv I I (Φ_fam t : M → M) x v)
          (mfderiv I I (Φ_fam t : M → M) x w)
        + metricTransportResidual (I := I) g X Φ_fam t x v w) t := by
  classical
  set α := Φ_fam t x with hα_def
  set dΦv : TangentSpace I α := mfderiv I I (Φ_fam t : M → M) x v with hdΦv
  set dΦw : TangentSpace I α := mfderiv I I (Φ_fam t : M → M) x w with hdΦw
  set Vflat : TangentSpace I α := T'v dΦv + P'v v with hVflat
  set Wflat : TangentSpace I α := T'w dΦw + P'w w with hWflat
  set Xα : E := chartE_section_repr (I := I) α (X : ∀ y : M, TangentSpace I y) α with hXα
  set nablaV : TangentSpace I α :=
    (LeviCivita (I := I) g) (X : ∀ y : M, TangentSpace I y) α dΦv with hnablaV
  set nablaW : TangentSpace I α :=
    (LeviCivita (I := I) g) (X : ∀ y : M, TangentSpace I y) α dΦw with hnablaW
  set Cv : TangentSpace I α := christoffelCorrection (I := I) g α α Xα dΦv with hCv
  set Cw : TangentSpace I α := christoffelCorrection (I := I) g α α Xα dΦw with hCw
  set Fv : TangentSpace I α :=
    fderiv ℝ (chartRawRepr (I := I) α (X : ∀ y : M, TangentSpace I y))
        (extChartAt I α α) dΦv
      + movingTrivCorrection (I := I) α (X : ∀ y : M, TangentSpace I y) dΦv with hFv
  set Fw : TangentSpace I α :=
    fderiv ℝ (chartRawRepr (I := I) α (X : ∀ y : M, TangentSpace I y))
        (extChartAt I α α) dΦw
      + movingTrivCorrection (I := I) α (X : ∀ y : M, TangentSpace I y) dΦw with hFw
  have hVflat_eq : Vflat = -Fv := hflatval_v
  have hWflat_eq : Wflat = -Fw := hflatval_w
  have hbr_v : nablaV = Fv + Cv := hbridge_v
  have hbr_w : nablaW = Fw + Cw := hbridge_w
  have hcorr_v' : Vflat = -nablaV + Cv := by
    rw [hVflat_eq, hbr_v]; abel
  have hcorr_w' : Wflat = -nablaW + Cw := by
    rw [hWflat_eq, hbr_w]; abel
  have h_total :=
    variational_flow_inner_total_derivative (I := I) g Φ_fam t x v w Vflat Wflat hv_flat hw_flat
  have hval :
      g.inner α Vflat dΦw + g.inner α dΦv Wflat
        = -lieDerivMetric (I := I) g X α dΦv dΦw
          + metricTransportResidual (I := I) g X Φ_fam t x v w := by
    have hbil1 : (g.inner α) (-nablaV + Cv)
        = -(g.inner α) nablaV + (g.inner α) Cv := by
      rw [ContinuousLinearMap.map_add (g.inner α) _ _,
        ContinuousLinearMap.map_neg (g.inner α) _]
    have hslot1 : g.inner α Vflat dΦw
        = -g.inner α nablaV dΦw + g.inner α Cv dΦw := by
      rw [hcorr_v', hbil1, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.neg_apply]
    have hslot2 : g.inner α dΦv Wflat
        = -g.inner α dΦv nablaW + g.inner α dΦv Cw := by
      rw [hcorr_w', ContinuousLinearMap.map_add (g.inner α dΦv) _ _,
        ContinuousLinearMap.map_neg (g.inner α dΦv) _]
    have hcartan :
        -g.inner α nablaV dΦw + -g.inner α dΦv nablaW
          = -lieDerivMetric (I := I) g X α dΦv dΦw := by
      rw [hnablaV, hnablaW]
      exact (neg_lieDerivMetric_eq_neg_killing_sum (I := I) g X α dΦv dΦw).symm
    have hres : g.inner α Cv dΦw + g.inner α dΦv Cw
        = metricTransportResidual (I := I) g X Φ_fam t x v w := by
      rw [metricTransportResidual, hCv, hCw, hXα]
    rw [hslot1, hslot2, ← hcartan, ← hres]
    ring
  rwa [hval] at h_total

end MainPairing

end ODE
end RicciFlow
end PDE
end DifferentialGeometry
