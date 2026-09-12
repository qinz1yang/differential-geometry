# Local homology and oriented chart compatibility

This separate `PoincareLean` project contains a dependency-closed checkpoint of
89 Poincare modules. It extends the recovered Chapter 35 source at commit
`b45bfa009368c8f5f531e10f4f5280e90079d6ad` and preserves its mathematical objects
and `Poincare` namespaces. `Poincare.lean` imports every included leaf.

The additions prove:

- composition, neighborhood naturality, restriction and germ laws for the
  actual local integral singular-homology maps;
- the actual chart/excision commuting square;
- invariance of induced positive-degree relative maps under homotopy of their
  subspace restrictions, when the relevant target absolute group vanishes;
- a punctured-ball homotopy from an invertible derivative to the given map,
  with a positive radius, continuous endpoints and the interpolation formula;
- equality of the corresponding relative-homology maps on one produced ball
  in every positive homological degree;
- equality of the original ambient relative maps with the invertible derivative
  in every natural homological degree, including degree zero;
- equality of relative H0 maps for pointwise joined continuous maps preserving
  the given subspaces;
- multiplication by the sign of the determinant for the actual top local
  integral homology map of any continuous linear equivalence of a finite-dimensional
  real normed space, including dimension zero;
- the actual local-homology map of a differentiable open partial homeomorphism
  with differentiable inverse equals its derivative determinant sign after
  translating source and target basepoints to zero, including dimension zero;
- composition and neighborhood restriction laws for actual open-partial-homeomorphism
  local maps in every natural degree;
- equality of the normalized local top-homology maps from the same manifold
  point under two charts whose actual tangent trivializations preserve the
  same orientation, for finite-dimensional real normed models including rank zero.

The eight new/changed modules and their exact baseline/current hashes are listed in
[provenance/SNAPSHOT.json](provenance/SNAPSHOT.json). The derivative homotopy
retains its [upstream attribution and modification record](provenance/README.md).

## Environment and validation

The portable package files preserve Lean `v4.33.1`, Mathlib commit
`0df444a360eaa60ab8c11dca51a86af692955474`, and the original DifferentialGeometry
`v0.1.2` dependency at `1b535dd102b94cc42b107cca27059687888f08b3`.
The selected source closure imports Mathlib only; no DifferentialGeometry source
is copied into this project. The toolchain file has only its extra trailing
blank line removed. Its original and normalized hashes are recorded.

The package root target is `lake build Poincare`, run from this directory.
On Della all sustained checks belong to the shared Slurm CPU worker. Use the
existing exact caches offline; local cache paths and any validation-only path
manifest stay outside the published package files.

The 74-module checkpoint passed its final affected-module/root build and
consumer/linter/axiom gate in Slurm 13781140, request
1789229647248153045-topology_checkpoint-a464ec28. The six additional leaves,
changed derivative-comparison source and root freshly compiled with zero
diagnostics; unchanged leaves retain their verified prior compilation. All 12
public exports, four nonidentity consumers, and a nonzero degree-zero class
consumer passed exact signatures and standard-only axiom guards, with stock
declaration linters over the entire
imported package and the consumers. The previous 68-module checkpoint was
published as `76917c5e2`.

The new 88-module snapshot retains those 74 sources unchanged and adds 13
unchanged baseline dependencies plus `LocalLinearMaps`. The latter passed its
fresh module and imported consumer gate in the original isolated project,
request `1789235551579974740-topology-d57a1cb3`. Its sole new public result uses
the given continuous linear equivalence directly; reflection, sphere and matrix
proof machinery remains private. Consumers checked nonidentity positive and
negative maps, an actual nonzero class moved by negation, and rank zero.

The final portable 88-module gate passed in Slurm 13781140, request
`1789236250289124336-topology_checkpoint-db7e7dbe`. All 14 added leaves and the
root freshly compiled with zero diagnostics in 5:55.36; the full request took
401.64 seconds. All 93 source/configuration/harness guards and 22 exact
signature/axiom pairs passed, including all 13 public exports. Stock declaration
linters and standard-only axiom checks covered the imported package and consumers.
The unchanged 74 leaves retain their earlier compilation evidence.
Source hashes and the separate validation records are recorded in
[provenance/SNAPSHOT.json](provenance/SNAPSHOT.json). No acceptance of the larger
topology suite is asserted.

The derivative-sign extension keeps the same 88 leaves and exposes one further
public result in the existing `LocalDerivativeComparison` module. The forward
and inverse differentiability hypotheses concern the actual local map; no
chosen derivative equivalence, point-fixing equation or global puncture
preservation is required. Four private helpers handle the produced small ball,
translations and neighborhood cancellation once. Both previous public derivative
proofs are preserved.

Final portable request `1789239376984243943-topology_checkpoint-ed89b504`
passed in Slurm 13781140 in 124.07 seconds. The changed leaf and `Poincare`
root freshly compiled without diagnostics in 1:16.87. All 99 guards and 25
signature/axiom pairs passed, covering all 14 public exports, the unchanged
prior consumers, an actual restricted nonidentity map with negative derivative,
and dimension zero. All-package and consumer declaration linters and
standard-only transitive axioms pass. The 87 unchanged leaves retain their
earlier compilation evidence; the previous 88-leaf checkpoint's evidence is
preserved in the snapshot record.

The oriented-chart extension adds `LocalOrientation`, bringing the checkpoint to
89 leaves and 17 public exports. Its primary theorem compares maps from the
same actual manifold local-homology group to the model's group at zero. The
hypothesis concerns one tangent orientation and the actual two trivializations;
no independent local generators or locally constant charts are supplied.
Two shared neighborhood/composition laws now live in `LocalCharts`. The old
55-line private neighborhood helper was moved there unchanged, and all three
retained public derivative-comparison proofs are unchanged.

Final portable request `1789242935902017893-topology_checkpoint-96e8ea73`
passed in Slurm 13781140 in 183.53 seconds. `LocalCharts`,
`LocalDerivativeComparison`, `LocalOrientation` and `Poincare` freshly compiled
without diagnostics in 2:14.67. All 99 guards and 32 signature/axiom pairs
passed, including all 17 public exports and every previous consumer readback.
The new consumers use actual translated manifold charts and a restricted
composition whose source is a proper intersection. All-package and consumer
stock declaration linters and standard-only transitive axioms pass. The 86
unchanged leaves retain their earlier compilation evidence. The original
full-source gate separately checks a rank-zero oriented chart transition.
These results establish pointwise chart compatibility; producing one coherent
class over a neighborhood remains the next step.

## Remaining topology work

This checkpoint supplies foundations for the orientation-to-local-homology
bridge. Coherent oriented local generators, fundamental classes, integral
duality, normalized homotopy and loop-family classes, and the canonical width
specializations remain open.

The separate frozen 87-declaration handoff, its registry and consumers, and
`handoff/CANONICAL_TOPOLOGY_READY.md` remain unavailable. This package does not
replace that contract or assert completion of T1--T9/C1--C5. It introduces no
deferred inputs. The recovered full Poincare project remains separate from this
selected source checkpoint.
