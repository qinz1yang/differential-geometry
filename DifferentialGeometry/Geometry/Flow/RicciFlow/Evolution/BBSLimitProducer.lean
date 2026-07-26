import DifferentialGeometry.Geometry.Flow.RicciFlow.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.CinftyLimitGlue
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.BBSAllMBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.EndpointMetricLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.EndpointRicciLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.ExtendShiInputs

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# BBSLimitProducer — Dispatch C: `cinftyLimitData_of_solution`

**STATUS (2026-07-14): ALTERNATE ROUTE; COMBINED CHECK PENDING.** `extends_of_rmBounded` currently
uses the interior-restart + forward-uniqueness route and does not consume `CinftyLimitData`. This
producer remains an independent endpoint-limit route. C1+C2, G3, and G4 are individually proved;
the C3 packaging source is assembled below and awaits combined verification.
The Shi-content successor is `shiCovBound_of_soln` (`ExtendShiInputs.lean`), whose discharge plan
(`ExtendShiInputs.md` §SHI DISCHARGE PLAN) unifies the citation with the HCG `MovingShiBoundOn`
interface. Kept for reference per the transitions rule.

Producer for the (now-deleted) `hLimit` sorry in `MaximalTime.lean` (the `extends_of_rmBounded`
BBS/long-time pillar of Hamilton 3D): from a **bounded-curvature** Ricci-flow solution on
`[α, ω)` in **dimension 3**, produce the smooth limit data `CinftyLimitData g_fam α ω hαω`
at the right endpoint `ω`.

The full plan, interface map, and standing-input ledger are in `BBSLimitProducer.md`.

## Architecture (completed producers, pending combined verification)

`cinftyLimitData_of_solution` is `cinftyLimitData_of_allMBounds ∘ bbsAllMBounds`. The original
route notes below are retained for context, but references to `bbsAllMBounds` as a `sorry` are
superseded: C1+C2 are complete, while G3 and G4 supply the two fields of C3.

* **`bbsAllMBounds`** (bricks C1+C2): the verified Bernstein–Bando–Shi
  all-order derivative estimate `‖∇ᵐRm‖² ≤ Cₘ` on slabs bounded away from the
  start.

* **`cinftyLimitData_of_allMBounds`** (brick C3): the limit-extraction **analysis** — from the
  all-`m` bounds, build the `C∞` limit metric and prove Ricci continuity across `ω`.  This is
  split into two dedicated producers. `exists_endMetric` supplies G3
  (`limitMetric`/`tendsto_left`), and `ricci_tendsto_left` supplies G4
  (`ricci_match`) by sequential two-jet compactness and `ricciConv_of_dnConv`.

The endpoint below only packages those two real producers; it introduces no
additional analysis assumption.

## Dimension and bound conventions

* `hdim : Module.finrank ℝ E = 3` — the whole residual stack is dim-3 (the Uhlenbeck KN identity
  `Rm04 = KN(Ric,S,g)` needs `Weyl = 0`).  This matches `extends_of_rmBounded`'s purpose
  (`ham3_main`).  The per-fibre `finrank (TangentSpace I x) = 3` is derived internally.
* The curvature bound is stated on the **intrinsic** squared norm `nablaKRm04NormSqIntrinsic S 0`
  ( `= normSq0S (g t) x 4 (∇⁰Rm)` , frame-independent), via the realizing `Rm04`.  The hypotheses
  `hRm`/`hbound` are the *unfolded* forms of `MaximalTime`'s `Rm04RealizesSolutionConnectionOn` /
  `Rm04NormSqBoundedAt` (defeq), so `extends_of_rmBounded` wires them with no translation and this
  file does not import `MaximalTime` (avoiding an import cycle).
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.Integral.Connection
open Bundle Tensor0SBundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [SigmaCompactSpace M] [T2Space M] [CompactSpace M] [BoundarylessManifold I M]

/-- **Brick C3 (the limit-extraction analysis).**  From the Bernstein–Bando–Shi all-`m` bounds
near `ω`, produce the smooth limit data `CinftyLimitData g_fam α ω`.

G3 is supplied by `exists_endMetric`; G4 is supplied by
`ricci_tendsto_left`. -/
def cinftyLimitData_of_allMBounds
    {alpha omega : ℝ} {hαω : alpha < omega}
    (S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega hαω))
    (hS : IsSolutionOn (I := I) S)
    (hdim : Module.finrank ℝ E = 3)
    (hbound : ∃ K : ℝ, ∀ (t : ℝ) (x : M),
        alpha ≤ t → t < omega →
          Tensor0SBundle.normSq0S (I := I) (S.base.metric t) x 4
            (S.base.rm04 t x) ≤ K)
    (hEquiv : ∃ Lambda : ℝ, 1 ≤ Lambda ∧
      ∃ t1 : ℝ, t1 ∈ Set.Ico alpha omega ∧
        ∀ s : ℝ, s ∈ Set.Ico t1 omega →
          ∀ x : M, ∀ v : TangentSpace I x,
            Lambda⁻¹ * (S.base.metric alpha).inner x v v ≤
                (S.base.metric s).inner x v v ∧
              (S.base.metric s).inner x v v ≤
                Lambda * (S.base.metric alpha).inner x v v)
    (hbounds : ∀ m : ℕ, ∃ C : ℝ, ∀ (t : ℝ) (x : M),
        (alpha + omega) / 2 ≤ t → t < omega →
          nablaKRm04NormSqIntrinsic (I := I) S m t x ≤ C) :
    CinftyLimitData (I := I) S.base.metric alpha omega hαω := by
  classical
  -- `exists_endMetric` is `Prop`-valued while the goal is data, so the endpoint
  -- metric is extracted with `Exists.choose` rather than destructured.
  have hex := exists_endMetric (I := I) S hdim hS hbound hEquiv
  refine
    { limitMetric := hex.choose
      tendsto_left := hex.choose_spec
      ricci_match := ?_ }
  intro x v w
  exact ricci_tendsto_left (I := I) S hdim hS hbound hEquiv hex.choose hex.choose_spec x v w

/-- **Dispatch C target — `CinftyLimitData` from a bounded-curvature dim-3 solution.**  This was
introduced for the former `hLimit` leaf of `extends_of_rmBounded` (`MaximalTime.lean`).  It is the
sorry-free composition `cinftyLimitData_of_allMBounds ∘ bbsAllMBounds`. The all-`m` estimate is
proved in `BBSAllMBounds.lean`; the endpoint route is retained as compactness infrastructure even
though the live extension proof now uses interior restart and forward uniqueness instead.

`hRm`/`hbound` are the unfolded forms of `MaximalTime.Rm04RealizesSolutionConnectionOn` /
`Rm04NormSqBoundedAt` (definitionally equal), so the call site wires them directly. -/
def cinftyLimitData_of_solution
    {alpha omega : ℝ} {hαω : alpha < omega}
    (S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega hαω))
    (hS : IsSolutionOn (I := I) S)
    (hdim : Module.finrank ℝ E = 3)
    (Rm04 : ℝ → Tensor04Section (I := I) (M := M))
    (hRm : ∀ t : RealTimeInterval.FlowTime (RealTimeInterval.closedOpen alpha omega hαω),
      Rm04RealizesConnection (I := I)
        (S.family.metric (t : ℝ)) (S.family.connection (t : ℝ)) (Rm04 (t : ℝ)))
    (hbound : ∃ K : ℝ, ∀ (t : ℝ) (x : M),
        alpha ≤ t → t < omega →
          Tensor0SBundle.normSq0S (I := I) (S.base.metric t) x 4 (Rm04 t x) ≤ K) :
    CinftyLimitData (I := I) S.base.metric alpha omega hαω := by
  have hRmRaw : ∀ t ∈ Set.Ico alpha omega,
      Rm04RealizesConnection (I := I) (S.base.metric t)
        (metricCov (I := I) (M := M) (S.base.metric t)) (Rm04 t) := by
    intro t ht
    simpa [SolutionOn.family, SolutionFamily.connection] using
      hRm (⟨t, ht⟩ : RealTimeInterval.FlowTime
        (RealTimeInterval.closedOpen alpha omega hαω))
  have hCan := rm04_bound_can (I := I) Rm04 hRmRaw hbound
  have hK := hbound.choose_spec
  have hRic := ric_quad_le_of_soln (I := I) hRmRaw hK
  have hRicConst :
      0 ≤ (Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt hbound.choose := by
    positivity
  have hEquiv := hell_of_soln (I := I) hS hRicConst hRic
  exact cinftyLimitData_of_allMBounds (I := I) S hS hdim hCan hEquiv
    (bbsAllMBounds (I := I) S hS hdim Rm04 hRm hbound)

end DifferentialGeometry.PDE.RicciFlow
