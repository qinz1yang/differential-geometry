import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.SpectralSmoothRepresentativeRealize
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.TensorHsRealize
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.DeTurckChartRegularityFromJoint

/-!
# (Removed) Joint chart-Gram smoothness from L²-time-continuity

This module formerly held `jointChartGramSmooth_of_spectralSmooth_timeContinuous`, which
asserted that an `L²`-time-*continuous*, all-order-spatially-smooth realized family has a
jointly `C^∞`-up-to-`t = 0` chart-Gram matrix.  That statement is **false**: time
*continuity* of the `L²` class is too weak.  Counterexample: `T_rep t = ρ(t) • S₀` for a
fixed nonzero smooth `S₀` and a continuous `ρ` that equals `c · |t|` near `0` (bounded so
the global fibre bound `δ < 1` holds).  Both premises hold — `t ↦ (T_rep t).toL2` is
continuous and lands in `⋂_σ Hˢ` — yet the chart-Gram entry is affine in `T_rep t`, namely
`chartGram(g) + ρ(t) · ccTensorBilinSymm(S₀)(eᵢ, eⱼ)`, which inherits the `|t|`-kink at
`t = 0` and is therefore not `C^∞` in time.

The correct hypothesis is time *smoothness* of the eigen-coordinates with a summable
time-jet mode-mass; that statement is `jointChartGramSmooth_of_spectralSmooth_timeSmooth`
in `SpectralEigenSeriesJointGram.lean`, which is proved sorry-free (`#print axioms` is
`[propext, Classical.choice, Quot.sound]`).  The realize-side consumer
`realizedFamily_jointChartGramSmooth` cites that proved time-smooth form, and the false
time-continuous form had no consumers, so it is removed rather than proved.

This module is now empty; its import may be dropped from the aggregate (and from
`DeTurckRealizedSolutionFamily.lean`, where it is an unused import) at merge.
-/
