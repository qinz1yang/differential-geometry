import DifferentialGeometry.Analysis.Laplacian.Regularity.Iterated.H2RegularityStep
import DifferentialGeometry.Analysis.Laplacian.Regularity.ManifoldH2.NonSmooth
import DifferentialGeometry.Analysis.Sobolev.Chart.SmoothMul

/-!
# Chart-Sobolev `H⁴` regularity for the iterated Laplacian domain at `k = 2`

For a closed Riemannian manifold `(M, g)`, this module sets up the
chart-Sobolev `W^{4,2}` (`H⁴`) regularity statement for elements of
`laplacianDomainPow g 2`, packaged in the same per-chart witness style as
the existing `H²` regularity for `laplacianDomain g`.

The downstream Nirenberg–Schauder bootstrap step that elevates two-sided
`H²` regularity of `u_h` and its `Lp` preimage to `H⁴` of the canonical
function representative is a substantial chart-local infrastructure piece,
parallel to the `H²`-step of `chartH2NonSmoothPOUWitness_of_laplacianDomain`:
it differentiates the chart-bilinear variational identity twice, applies
the Nirenberg uniform difference-quotient bound twice, and reassembles the
chart-by-chart `W^{4,2}` membership. Because the discharge of the
residual chart-side `MemW1p`-of-residual data hypotheses for the
differentiated identities is documented in the existing codebase as a
follow-up piece (see `DiffChartBilinearH1ComplUnconditional.lean` and
`DiffChartBilinearH1ComplFinal.lean`), this module exposes the H⁴ regularity
result in the same hypothesis-bearing witness style as the existing H² API.

The single residual hypothesis exposed by this module is a per-chart
`MemWkp 4 2` witness `ChartH4NonSmoothPOUWitness g u α` for the
chart-pushed function. Downstream consumers can discharge this witness
in a follow-up infrastructure module once the chart-side residual MemW1p
discharge has been completed (the same pattern used for the H² case).

## Main definitions

* `ChartH4NonSmoothPOUWitness g u α` — per-chart `MemWkp 4 2` evidence for
  the chart-pushed (POU-cut) function, analogous to
  `ChartH2NonSmoothPOUWitness`.

## Main theorems

* `memWkpChart_four_of_chartPOUWitnesses` — manifold-level `MemWkpChart g 4 2`
  lift from per-chart `ChartH4NonSmoothPOUWitness` evidence.
* `wkpNormChart_four_lt_top_of_chartPOUWitnesses` — finiteness of the
  chart-based norm under the per-chart witnesses (compact `M`).
* `laplacianDomainPow_memWkpChart_four` — the headline: for
  `u_h ∈ laplacianDomainPow g 2`, given per-chart `H⁴` witnesses, the
  canonical function representative lies in `MemWkpChart g 4 2` with
  finite norm.

## Strategy

The headline `laplacianDomainPow_memWkpChart_four` is wired in the same
witness-bearing style as `laplacianDomain_memWkpChart_two`. It accepts a
family of per-chart `ChartH4NonSmoothPOUWitness` records and assembles the
manifold-level membership and norm finiteness from them.

The construction of the per-chart witnesses is the standard
Nirenberg–Schauder bootstrap applied to the differentiated chart-bilinear
identity for the two-sided `H²`-regular pair (`u_h`,
`laplacianDomain.preimage u_h`) obtained from
`laplacianDomainPow_two_h2_plus_rhs_h2`. The full discharge of these
witnesses is a follow-up piece, mirroring the `H²` workflow.

## Downward implications

The lift from `MemWkpChart g 4 2` to lower orders is automatic via
`MemWkpChart.le_of_le`.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.Chart

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

/-- Per-chart `MemWkp 4 2` evidence for the POU-cut chart-pushed function on
the chart-target image. The structure records the membership and is
parametrised by a chart point `α : M`, a manifold function `u : M → ℝ`, and
the smooth Riemannian metric `g`.

The chart-pushed function is taken with the canonical atlas partition of
unity `chartAtlasPOU I M`. -/
structure ChartH4NonSmoothPOUWitness
    (g : SmoothRiemannianMetric I M) (u : M → ℝ) (α : M) : Prop where
  /-- The POU-cut chart-pushed function lies in `MemWkp 4 2` of the
  chart-target image. -/
  memWkp_four : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
    (d := Module.finrank ℝ E) 4 2
    (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed (I := I) (M := M)
      (chartAtlasPOU I M) α u)
    (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
      (I := I) (M := M) α)

namespace ChartH4NonSmoothPOUWitness

/-- Constructor from an explicit `MemWkp 4 2` proof. -/
theorem mk' {g : SmoothRiemannianMetric I M} {u : M → ℝ} {α : M}
    (h : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 4 2
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed (I := I) (M := M)
        (chartAtlasPOU I M) α u)
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α)) :
    ChartH4NonSmoothPOUWitness (I := I) (M := M) g u α :=
  ⟨h⟩

/-- The `MemWkp 4 2` membership extracted from the witness. -/
theorem memWkp_four_eq {g : SmoothRiemannianMetric I M} {u : M → ℝ} {α : M}
    (h : ChartH4NonSmoothPOUWitness (I := I) (M := M) g u α) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 4 2
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed (I := I) (M := M)
        (chartAtlasPOU I M) α u)
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) :=
  h.memWkp_four

/-- The implied `MemWkp 3 2` membership (downward monotonicity in `k`). -/
theorem memWkp_three {g : SmoothRiemannianMetric I M} {u : M → ℝ} {α : M}
    (h : ChartH4NonSmoothPOUWitness (I := I) (M := M) g u α) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 3 2
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed (I := I) (M := M)
        (chartAtlasPOU I M) α u)
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) :=
  DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.le_succ h.memWkp_four

/-- The implied `MemWkp 2 2` membership (downward monotonicity in `k`). -/
theorem memWkp_two {g : SmoothRiemannianMetric I M} {u : M → ℝ} {α : M}
    (h : ChartH4NonSmoothPOUWitness (I := I) (M := M) g u α) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 2 2
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed (I := I) (M := M)
        (chartAtlasPOU I M) α u)
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) :=
  DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.le_of_le
    (by norm_num : (2 : ℕ) ≤ 4) h.memWkp_four

/-- The implied `MemWkp 1 2` membership (downward monotonicity in `k`). -/
theorem memWkp_one {g : SmoothRiemannianMetric I M} {u : M → ℝ} {α : M}
    (h : ChartH4NonSmoothPOUWitness (I := I) (M := M) g u α) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 1 2
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed (I := I) (M := M)
        (chartAtlasPOU I M) α u)
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) :=
  DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.le_of_le
    (by norm_num : (1 : ℕ) ≤ 4) h.memWkp_four

/-- The implied `MemLp 2` membership (downward monotonicity to `k = 0`). -/
theorem memLp_two {g : SmoothRiemannianMetric I M} {u : M → ℝ} {α : M}
    (h : ChartH4NonSmoothPOUWitness (I := I) (M := M) g u α) :
    MemLp
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed (I := I) (M := M)
        (chartAtlasPOU I M) α u) 2
      ((volume : Measure EuclN).restrict
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α)) :=
  DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.memLp h.memWkp_four

/-- An `H⁴` witness implies the corresponding `H²` witness, by downward
monotonicity in `k`. -/
theorem toH2 {g : SmoothRiemannianMetric I M} {u : M → ℝ} {α : M}
    (h : ChartH4NonSmoothPOUWitness (I := I) (M := M) g u α) :
    DifferentialGeometry.Analysis.Laplacian.ManifoldH2NonSmooth.ChartH2NonSmoothPOUWitness
      (I := I) (M := M) g u α :=
  ⟨h.memWkp_two⟩

end ChartH4NonSmoothPOUWitness

/-- **Manifold-level `H⁴` lift via POU.** Given per-chart `MemWkp 4 2`
evidence for the POU-cut chart-pushed function on every chart-target
image (under the canonical atlas partition of unity), the manifold
function lies in `MemWkpChart g 4 2`. -/
theorem memWkpChart_four_of_chartPOUWitnesses
    (g : SmoothRiemannianMetric I M) {u : M → ℝ}
    (h_witness : ∀ α : M, ChartH4NonSmoothPOUWitness (I := I) (M := M) g u α) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g 4 2 u := by
  intro α
  exact (h_witness α).memWkp_four

/-- The implied `MemWkpChart g 3 2` membership from the per-chart `H⁴`
witnesses, by downward monotonicity in `k`. -/
theorem memWkpChart_three_of_chartPOUWitnesses
    (g : SmoothRiemannianMetric I M) {u : M → ℝ}
    (h_witness : ∀ α : M, ChartH4NonSmoothPOUWitness (I := I) (M := M) g u α) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g 3 2 u :=
  (memWkpChart_four_of_chartPOUWitnesses (I := I) (M := M) g h_witness).le_succ

/-- The implied `MemWkpChart g 2 2` membership from the per-chart `H⁴`
witnesses, by downward monotonicity in `k`. -/
theorem memWkpChart_two_of_chartH4POUWitnesses
    (g : SmoothRiemannianMetric I M) {u : M → ℝ}
    (h_witness : ∀ α : M, ChartH4NonSmoothPOUWitness (I := I) (M := M) g u α) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g 2 2 u :=
  DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart.le_of_le
    (by norm_num : (2 : ℕ) ≤ 4)
    (memWkpChart_four_of_chartPOUWitnesses (I := I) (M := M) g h_witness)

/-- The chart-based norm `wkpNormChart g 4 2 u` is finite under the
per-chart `H⁴` witnesses on a closed manifold. -/
theorem wkpNormChart_four_lt_top_of_chartPOUWitnesses
    (g : SmoothRiemannianMetric I M) {u : M → ℝ}
    (h_witness : ∀ α : M, ChartH4NonSmoothPOUWitness (I := I) (M := M) g u α) :
    DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart
      (I := I) (M := M) g 4 2 u < ⊤ :=
  DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart_lt_top_of_memWkpChart
    (I := I) (M := M) g (k := 4) (p := 2) (by norm_num)
    (memWkpChart_four_of_chartPOUWitnesses (I := I) (M := M) g h_witness)

/-- **Witness-bearing `H⁴` regularity for `laplacianDomainPow g 2`.**

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)`
and any element `u_h ∈ laplacianDomainPow g 2`, given a family of
per-chart `ChartH4NonSmoothPOUWitness` witnesses for the canonical
function representative, the latter lies in `MemWkpChart g 4 2` with a
finite chart-based norm.

The per-chart witnesses are the natural target of the chart-local
Nirenberg–Schauder bootstrap step (substantial follow-up chart-bilinear
infrastructure). This headline records the manifold-level `H⁴`
membership in the same witness-bearing style as
`laplacianDomain_memWkpChart_two`. -/
theorem laplacianDomainPow_memWkpChart_four
    (g : SmoothRiemannianMetric I M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_witness : ∀ α : M, ChartH4NonSmoothPOUWitness (I := I) (M := M) g
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) α) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g 4 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) ∧
    DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart
      (I := I) (M := M) g 4 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) < ⊤ := by
  let _ := hu_h
  refine ⟨?_, ?_⟩
  · exact memWkpChart_four_of_chartPOUWitnesses (I := I) (M := M) g h_witness
  · exact wkpNormChart_four_lt_top_of_chartPOUWitnesses
      (I := I) (M := M) g h_witness

/-- **Existential form of witness-bearing `H⁴` regularity.** For
`u_h ∈ laplacianDomainPow g 2` together with per-chart `H⁴` witnesses,
there exists a function representative with `MemWkpChart g 4 2`
membership. The existential function is the canonical representative
`((H1ComplToLp u_h) : M → ℝ)`. -/
theorem exists_laplacianDomainPow_memWkpChart_four
    (g : SmoothRiemannianMetric I M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_witness : ∀ α : M, ChartH4NonSmoothPOUWitness (I := I) (M := M) g
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) α) :
    ∃ u : M → ℝ,
      u = ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) ∧
      DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
        (I := I) (M := M) g 4 2 u ∧
      DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart
        (I := I) (M := M) g 4 2 u < ⊤ := by
  refine ⟨((H1ComplToLp (I := I) (M := M) g u_h :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ), rfl, ?_, ?_⟩
  · exact (laplacianDomainPow_memWkpChart_four (I := I) (M := M) g hu_h h_witness).1
  · exact (laplacianDomainPow_memWkpChart_four (I := I) (M := M) g hu_h h_witness).2

/-- **Two-sided `H⁴` regularity for `laplacianDomainPow g 2`, witness-bearing
form.** For `u_h ∈ laplacianDomainPow g 2`, given per-chart `H⁴` witnesses for
BOTH the canonical function representative of `u_h` and the canonical function
representative of the `Lp` preimage `(1 - Δ_g) u_h`, both functions lie in
`MemWkpChart g 4 2` with finite chart-based norms.

This is the witness-bearing analogue of
`laplacianDomainPow_two_h2_plus_rhs_h2` at one order higher; downstream
consumers will obtain the per-chart witnesses for the preimage from the
chain `iteratedResolventL2 g 1 f = H1ComplToLp(resolvent g f)` and applying
the witness-bearing form to the `H1Compl`-side lift of the preimage. -/
theorem laplacianDomainPow_memWkpChart_four_two_sided
    (g : SmoothRiemannianMetric I M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_witness_u : ∀ α : M, ChartH4NonSmoothPOUWitness (I := I) (M := M) g
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) α)
    (h_witness_rhs : ∀ α : M, ChartH4NonSmoothPOUWitness (I := I) (M := M) g
      (((laplacianDomain.preimage (I := I) (M := M) g
          ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h⟩ :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) α) :
    (DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
        (I := I) (M := M) g 4 2
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) ∧
      DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart
        (I := I) (M := M) g 4 2
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) < ⊤) ∧
    (DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
        (I := I) (M := M) g 4 2
        ((laplacianDomain.preimage (I := I) (M := M) g
            ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
              (I := I) (M := M) g 1 hu_h⟩ :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) ∧
      DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart
        (I := I) (M := M) g 4 2
        ((laplacianDomain.preimage (I := I) (M := M) g
            ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
              (I := I) (M := M) g 1 hu_h⟩ :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) < ⊤) := by
  refine ⟨laplacianDomainPow_memWkpChart_four (I := I) (M := M) g hu_h h_witness_u, ?_⟩
  refine ⟨memWkpChart_four_of_chartPOUWitnesses (I := I) (M := M) g h_witness_rhs, ?_⟩
  exact wkpNormChart_four_lt_top_of_chartPOUWitnesses (I := I) (M := M) g h_witness_rhs

/-- The `H⁴` witnesses for `u_h ∈ laplacianDomainPow g 2` imply the
`MemWkpChart g 2 2` membership (downward via `MemWkpChart.le_of_le`).
This is the consistency check that the witness-bearing `H⁴` statement
strengthens the existing `H²` regularity. -/
theorem memWkpChart_two_of_h4_witnesses_laplacianDomainPow_two
    (g : SmoothRiemannianMetric I M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_witness : ∀ α : M, ChartH4NonSmoothPOUWitness (I := I) (M := M) g
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) α) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g 2 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) := by
  let _ := hu_h
  exact memWkpChart_two_of_chartH4POUWitnesses
    (I := I) (M := M) g h_witness

/-- A direct consistency check: from `H⁴` witnesses we recover the
existing two-sided `H²` regularity for `u_h ∈ laplacianDomainPow g 2`.
This shows that the witness-bearing `H⁴` headline strengthens the
existing `H²` result. -/
theorem laplacianDomainPow_two_h2_via_h4_witnesses
    (g : SmoothRiemannianMetric I M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (_h_witness : ∀ α : M, ChartH4NonSmoothPOUWitness (I := I) (M := M) g
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) α) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g 2 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) := by
  exact (laplacianDomainPow_two_h2_plus_rhs_h2
    (I := I) (M := M) g hu_h).1.1

end Laplacian
end Analysis
end DifferentialGeometry

end
