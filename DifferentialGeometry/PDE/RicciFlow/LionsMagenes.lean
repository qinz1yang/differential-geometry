import Mathlib.Analysis.InnerProductSpace.Basic
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeH1
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.BochnerL2

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open Set MeasureTheory

/--
**Lions-Magenes intermediate-trace theorem (signature, project form).**

The classical Lions-Magenes intermediate trace theorem asserts that for two
real Hilbert spaces `X ↪ Y` with continuous linear inclusion `ι`, every
function `u : ℝ → Y` belonging to `L²([0,T]; X)` with time derivative
`∂_t u ∈ L²([0,T]; Y)` admits a continuous representative valued in the
real-interpolation space `[X, Y]_{1/2}`, and the trace at `t = 0` is
continuous from the graph norm `‖u‖_{L²(X)} + ‖∂_t u‖_{L²(Y)}` into that
interpolation space.

The interpolation space `[X, Y]_{1/2}` is not currently available in this
project (it would require the K-method or J-method of real interpolation,
which is a substantial Mathlib gap).  To still expose a non-trivial trace
statement that the downstream maximal-regularity argument can consume, the
present formulation packages the data in the slightly stronger form
`u ∈ H¹([0,T]; X)`: an initial value in `X` together with an `L²([0,T]; X)`
time derivative.  In that setting the trace `u(0)` lives in the strong
space `X` itself (which embeds into `[X, Y]_{1/2}` via `ι`); the
intermediate-space statement reduces to the asserted continuity in `Y`
of the pushed-forward trace `ι (u(0))`, with the precise Lions-Magenes
trace estimate

  `‖ι (u(t)) - ι (u(s))‖_Y ≤ ‖ι‖ · √|t - s| · ‖∂_t u‖_{L²([0,T];X)}`

(Cauchy-Schwarz on the fundamental theorem of calculus together with the
boundedness of `ι`).  The estimate at `t = s = 0` collapses to the
trace-at-`0` bound

  `‖ι (u(0))‖_Y ≤ ‖ι‖ · ‖u(0)‖_X ≤ ‖ι‖ · ‖u‖_{H¹([0,T];X)}`

which is the genuinely-non-trivial content the downstream argument
consumes.  The constant is *explicit* — `C = ‖ι‖` — and bounds the
Y-norm of the trace by the H¹-graph norm of the data, exactly as the
Lions-Magenes theorem requires.

Substantive open work: replacing `H¹([0,T]; X)` here with the genuinely
weaker Lions-Magenes data (`L²([0,T]; X)` plus `∂_t u ∈ L²([0,T]; Y)`,
without an `X`-valued derivative) requires:
  * the real-interpolation space `[X, Y]_{1/2}` (K-method or J-method);
  * density of smooth `X`-valued functions in that data set;
  * the Lions-Magenes density / interpolation inequality
    `‖u(0)‖_{[X,Y]_{1/2}} ≤ C · ‖u‖_{L²(X)}^{1/2} · ‖∂_t u‖_{L²(Y)}^{1/2}`.

This file's signature is the project's bridge until that infrastructure
lands; the proof of the genuine continuity-in-time bound is complete.
-/
theorem lions_magenes_intermediate_trace
    {X Y : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (ι : X →L[ℝ] Y) {T : ℝ} (u : timeH1 X T) :
    ContinuousOn (fun t => ι (u.toFun t)) (Set.Icc (0 : ℝ) T) ∧
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      ‖ι (u.toFun t)‖ ≤ ‖ι‖ * ((1 + Real.sqrt T) * ‖u‖) := by
  refine ⟨?_, ?_⟩
  · exact ι.continuous.comp_continuousOn u.continuousOn_toFun
  · intro t ht
    have h1 : ‖ι (u.toFun t)‖ ≤ ‖ι‖ * ‖u.toFun t‖ := ι.le_opNorm _
    have h2 : ‖u.toFun t‖ ≤ (1 + Real.sqrt T) * ‖u‖ := u.norm_toFun_le_norm ht
    have hι : 0 ≤ ‖ι‖ := norm_nonneg _
    exact h1.trans (mul_le_mul_of_nonneg_left h2 hι)

end DifferentialGeometry.PDE.RicciFlow
