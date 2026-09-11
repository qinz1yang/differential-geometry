# STRUCTURE.md — mathematical file and folder placement

This file is the authority for the placement, granularity, and dependency structure of
`DifferentialGeometry`. `NAMING.md` governs declaration names. `AGENTS.md` governs workflow,
soundness, source discipline, and delivery.

## 1. Library architecture

Reusable mathematics is the product. Hamilton's theorem, Ricci flow, surgery, and Perelman's theorem
are thin capstones over reusable topology, geometry, and analysis.

The canonical top-level pillars are:

```text
DifferentialGeometry/
  Bundle/
  Tensor/
  Topology/
  Geometry/
  Analysis/
  External/
```

- `Bundle/` contains reusable smooth-bundle foundations and bundle operations.
- `Tensor/` contains metric-free multilinear, tensor, alternating, exterior, realization, and tensorial
  infrastructure. Metric-dependent results leave this pillar for `Geometry/`.
- `Topology/` contains general topology used by differential geometry and differential topology itself:
  adjunction spaces, cell and handle attachment, Morse theory, covering-space and manifold topology,
  and eventually reusable three-manifold topology.
- `Geometry/` contains metric and connection geometry, curvature, coordinates, geodesics, exponential
  maps, comparison geometry, boundary geometry, Hodge geometry, geometric operators, and geometric
  flows.
- `Analysis/` contains dry analytic infrastructure: calculus, integration and measure, ODE, Sobolev,
  Schauder, elliptic, spectral, parabolic, heat, and related functional analysis.
- `External/` is vendored third-party mathematics and is not edited or reorganized.

Do not create another top-level pillar until its first real reusable declaration exists and its
dependency direction is understood.

## 2. Topology is a peer pillar

`Topology/` is not a submodule of `Geometry/`. Topological constructions do not depend on a metric, and
differential topology is consumed by several geometric applications.

Use the following natural homes:

```text
Topology/
  Attachment/       adjunction spaces, cells, relative attachment, quotient and gluing API
  Morse/            critical points, Morse index and lemma, regular levels, cell attachment
  Covering/         covering spaces and universal-cover results when promoted
  Handle/           smooth handles, collars and manifold gluing once real theorems land
  ThreeManifold/    reusable 3-manifold topology once its first theorem lands
```

Do not create the last three folders speculatively. Existing reusable topology under
`Geometry/Topology/` is legacy placement and should move to `Topology/` when touched coherently.

Morse-specific use of smooth charts and ODE flow does not move Morse theory into `Geometry/`. General
ODE existence and flow infrastructure belongs in `Analysis/ODE/`; the theorem-specific assembly that
turns it into a Morse-theoretic conclusion belongs in `Topology/Morse/`.

Topological cell attachment and homotopy consequences belong in `Topology/Attachment/` and
`Topology/Morse/`. A smooth handle is stronger than an attached CW cell: reusable collars, embeddings,
manifolds with boundary or corners, and handle gluing belong in `Topology/Handle/`. Ricci-flow-specific
surgery glue belongs under `Geometry/Flow/RicciFlow/Surgery/`, consuming those reusable foundations.

## 3. Geometry and geometric flow

The canonical geometry tree includes subject homes such as:

```text
Geometry/
  Boundary/
  Comparison/
  Connection/
  Coordinates/
  Curvature/
  Exponential/
  Geodesic/
  Hodge/
  Metric/
  Operator/
  Flow/
    RicciFlow/
```

Only genuinely flow-specific definitions and glue belong under `Geometry/Flow/`. Promote reusable ODE,
PDE, integration, tensor, bundle, topology, and static geometry out to their natural pillars.

## 4. Analysis is a first-class pillar

The canonical analytic homes include:

```text
Analysis/
  Calculus/
  Integration/
  ODE/
  Sobolev/
  Schauder/
  Elliptic/
  Spectral/
  Parabolic/
  Heat/
```

The old top-level `Integration/` tree is legacy placement. New integration and measure mathematics goes
under `Analysis/Integration/`; migrate legacy files only in dependency-closed coherent changes.

PDE and geometric-analysis results are organized by their reasoning nature, not by their first Ricci
flow consumer. Geometry may state the geometric operator; Analysis proves dry estimates and existence;
the application imports both.

## 5. Files and concept folders

Placement is mathematical, not line-count driven.

- One coherent development, however long, is one file.
- A single definition with immediate constructors, simp lemmas, and elementary properties may remain in
  one file.
- A definition with a reusable API and several genuinely separable mathematical developments becomes a
  concept folder, normally with `Defs.lean`, `Basic.lean`, and mathematically named aspect files.
- Split only at real interfaces: definitions versus realization, local versus global theory, topology
  versus smooth structure, model theorem versus manifold transport, or construction versus application.
- Never split a proof or create files merely to satisfy a line-count target or reduce visible file size.
- Private lemmas used by only one coherent proof remain with that proof.
- Promote reusable helpers to their natural home; otherwise keep them private. Do not leave generic
  subtype, equivalence, finite-set, or continuity utilities public inside an application namespace.

Files use UpperCamelCase mathematical names. `Defs.lean` and `Basic.lean` are reserved for genuine
concept-folder roles, not generic dumping grounds.

## 6. Imports and dependency direction

Lean's acyclic module graph is the hard constraint. Maintain these semantic directions:

- `Bundle/`, metric-free `Tensor/`, and foundational `Topology/` stay low-level.
- Foundational `Geometry/Metric`, `Geometry/Connection`, and `Geometry/Curvature` do not import
  high-level `Analysis/` back.
- `Analysis/` may consume the geometric definitions needed to state analytic operators and estimates.
- High-level `Geometry/` and `Topology/Morse/` may consume `Analysis/` when a genuine ODE, integration,
  or PDE theorem is required.
- `Geometry/Flow/` is an application layer and may consume all reusable lower layers.
- `External/` is imported as vendored mathematics but never edited to repair local architecture.

Use precise leaf imports. Do not import the flat root aggregate from library source.

## 7. Aggregation and namespaces

`DifferentialGeometry.lean` is the single flat root aggregate and imports every public leaf module.
There are no per-folder aggregator modules.

Folders are for mathematical navigation and dependency boundaries. Namespaces follow mathematical
objects and subjects and need not mirror the entire path. Moving a file does not by itself justify
namespace churn.

Every new public leaf is registered in `DifferentialGeometry.lean` and verified by the root build even
when it has no current consumers.

## 8. Variants and theorem direction

Organize variants by their conclusions:

- Different conclusions are coequal siblings over shared foundations.
- The same conclusion with stronger assumptions or a special object is a corollary of the natural
  general theorem.
- Model-space results and conditional transport lemmas are foundations for the manifold theorem, not
  substitutes carrying its classical name.
- Local and global results remain separate when globalization requires compactness, completeness,
  partitions of unity, flow existence, or gluing.
- Topological equivalence, homeomorphism, diffeomorphism, isotopy, deformation retract, and relative
  equivalence are distinct interfaces and must not be silently weakened.

## 9. Hamilton and Perelman placement

Create Hamilton-, Perelman-, surgery-, or three-manifold-specific homes only when the first real theorem
lands.

- Reusable Ricci flow equations, evolution identities, compactness inputs, and surgery-independent flow
  mathematics belong under `Geometry/Flow/RicciFlow/` or a lower natural pillar.
- Reusable differential topology, Morse theory, handle attachment, covering theory, and 3-manifold
  topology belong under `Topology/`.
- Surgery-specific assembly belongs under `Geometry/Flow/RicciFlow/Surgery/`.
- Hamilton's and Perelman's final application theorems remain thin and must not become homes for reusable
  PDE, geometry, or topology.

## 10. Placement review

Before accepting a new or moved module, verify:

- the declarations have one canonical mathematical home;
- generic helpers are private or promoted;
- the chosen split reflects a real interface rather than file length;
- imports are precise and acyclic;
- foundational geometry does not import Analysis back;
- conditional/model results are separated from global classical headlines;
- legacy placement is not copied into new work;
- the leaf is registered in the flat root aggregate.
