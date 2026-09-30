# Current proof and source update — September 30, 2026

The scalar shifted area contradiction and least-exterior-area continuity from local disk comparisons are proved. Smooth disk-boundary reparametrization, preservation of the exterior spanning-disk conditions, and area invariance under bi-Lipschitz disk reparametrization have proved adapters. The unnecessary manifold hypothesis on the composition lemma was removed following the requested `unusedArguments` check.

`hyperbolicGeometricStructure` replaces the old finite-volume name and has a model simp lemma; the local atlas admission drops unneeded T2/SigmaCompact binders. Mostow–Prasad, cusp curvature, and the local hyperbolic-atlas theorem remain prepared admissions. Concrete finite-volume models and cusp truncations are now definitions used by the separated flow interfaces; their producer remains admitted.

The primitive meridian, fixed-curve minimizer, same-flow comparisons and post-event upper barrier are separated in the flow modules. Meeks–Yau1982 MathZ Theorems1–2 were visually read on PDF4–9 (printed153–158); Hamilton1999 sections11–12 were read on PDF22–34 (printed716–728). The latter is a normalized free-boundary route. These sources do not silently discharge the fixed-boundary, exact exterior, physical normalization or surgery adapters.

See the current improvement report, public axiom/linter logs, and source JSON. The original review below is historical and its admission counts and implementation gaps may be superseded.

---
# Hyperbolic geometry and cusp-area skeleton review

Reviewed against the current mathematical body of master207A.tex. These are
honest skeleton declarations: four mathematical leaf proofs deliberately use
`sorry`, as requested by the user. The downstream compositions are actual Lean
proofs, but their axiom closures inherit those placeholders. This is not a
formal proof of hyperbolic persistence, Meeks–Yau, or ambient incompressibility
for an arbitrary surgery tower.

## Mathematical scope

- `Geometry/Hyperbolic/Rigidity.lean`: HG04/MPR79, uniqueness of a smooth
  Riemannian isometry in the specified homotopy class. Both manifolds are
  connected, complete, smooth, boundaryless, dimension three, and finite volume.
  They have the same strictly negative constant sectional curvature. No
  orientability or compactness premise was added. Sectional curvature is tested
  only on linearly independent pairs; evaluating it on dependent pairs would
  make a negative constant-curvature hypothesis inconsistent. The conclusion
  compares an actual continuous homotopy equivalence to the actual isometry,
  without asserting equality of arbitrary based fundamental-group maps.
- `Geometry/Hyperbolic/ModelAtlas.lean`: local curvature −1 supplies the existing
  hyperbolic Thurston atlas. The genuinely assembled
  `finiteVolumeGeometricStructure` starts with curvature −1/4, scales the metric
  by 1/4, and uses the inherited curvature, completeness, and volume scaling
  lemmas. It produces the existing complete finite-volume geometric structure
  on the same carrier. Transport along a full-interior diffeomorphism uses the
  existing `GC.Geometry.GeometricStructure.pullback`. Restriction to a finite
  cusp core is not claimed complete; core embedding and interior-opening map
  remain different maps. The local-atlas leaf is an unproved space-form input,
  not an assertion that this inherited mathematical foundation was absent.
- `Analysis/ODE/AreaUpperBarrier.lean`: HG14 with a real nonnegative continuous
  function on one entire late half-line. At every contact, including a surgery
  contact when the hypothesis is used, an open neighborhood supports a smooth
  upper barrier with equality and the strict derivative inequality. The
  minimizing function itself is not assumed differentiable. The reusable leaf
  allows a shift c with T+c>0. Its integrating-factor proof is exactly HG14's
  argument with s=t+c. The normalized c=1/4 theorem and D=π specializations are
  actual proofs from that leaf. The general shift is a mathematical
  generalization of the elementary ODE argument, not a newly proved Ricci-flow
  scalar estimate.
- `Geometry/MinimalSurface/ExteriorDiskArea.lean`: IMS03's actual infimum is over
  smooth embedded immersed closed disks with prescribed parametrized boundary
  in the exterior frontier and interior in the exterior interior. Area is the
  inherited `riemannianDiskArea`, not an arbitrary assigned number. The infimum
  is nonnegative even when the class is empty, but every use in the geometric
  consumer separately requires attainment by an admissible disk. No existence,
  positivity, stability, or Meeks–Yau assertion is smuggled into this definition.
  The IMS08 comparison theorem requires actual minimizers and two-direction
  area comparisons of minimizers at every nearby time in the half-line. It
  does not require all competitors to lie in the surgery-avoiding carrier;
  IMS07 supplies that carrier for minimizers. It does not require a continuous
  choice of minimizer or a diffeomorphism of whole pre-/post-surgery slices.
- `Geometry/Flow/RicciFlow/LongTime/CuspIncompressibility.lean`: actual conditional
  HG15/IMS10 consumers. The finite cusp family uses actual continuous maps into
  the actual time-dependent ambient carrier and injectivity at every source
  basepoint. A failed inclusion must supply the whole-half-line area function
  and barriers. One consumer retains the concrete exterior-disk infimum; the
  endpoint adapters take the explicitly displayed numerical obstruction and
  apply it to `SmoothAssembly.torusInPrime` for the supplied reconstruction.
  These adapters are named `...of_...` and are not geometric producer theorems.
  Product-collar transport is proved using the existing torus homotopy and its
  basepoint track, so the selected cusp slice has the reference slice's kernel.

## Double-checks and repaired corner cases

1. The current selected route is prescribed-boundary IMS01–IMS11/IAU01–IAU03.
   Historical HG10/HG12 free-boundary contracts are not claimed implemented.
2. No nonzero-kernel claim is deduced from model peripheral injection. The
   ambient target of every injected map is explicit. The selected exterior
   meridian may lie at a different port from the initially failing seam.
3. The local comparison hypothesis was narrowed to actual minimizers, matching
   IMS07–IMS08. Requiring transport for every competitor would have silently
   strengthened the source construction.
4. Cusp maps and prescribed loops are defined only after their own thresholds.
   The numerical area function is extended by zero before its starting time.
   Thus empty earlier carriers do not force nonexistent earlier loops. The
   function is required continuous only on the late half-line; this extension
   claims no continuity across its starting endpoint from the left.
5. Zero cusp labels are permitted. Empty or closed hyperbolic families require
   no disk argument. The model rigidity statement itself requires a connected
   nonempty manifold, as the natural statement does.
6. Contact neighborhoods are open in real time, with upper domination on their
   intersection with the half-line. A local barrier can therefore be two-sided
   at surgery without requiring the area function before its initial domain.
7. The slope bound is strict and contains −π in the D=π case. T+c>0 prevents a
   zero or negative integrating-factor denominator. No positive margin on the
   size of the contact neighborhood is imposed uniformly over all surgeries.
8. No derivative, completeness, finite volume, or based-map evidence follows
   from a geometry tag alone. The finite-volume metric output has all actual
   existing GeometricStructure fields.
9. All new files are in the mathematical subject homes in DifferentialGeometry.
   Generic real analysis is outside RicciFlow. The hyperbolic cusp metric file
   was factored into Geometry/Hyperbolic/Cusp by the collapse agent; that file's
   source review belongs to the collapse record.

## Sources actually inspected or reused

Fresh reads in this task:

- master207A.tex HG01–HG04 (10647–10705, 12496–12515), MPR79
  (15392–15424), HPI08 (17980–18030), HG10–HG17 and selected
  IMS/IAU statements and proof passages (18059–18916, with targeted proof expansion around
  18251–18338 and 18475–18850).
- Archived MSM206.tex `MosTowSection`, lines 17115–17163, statement and
  homotopy-equivalence corollary. Its unbased group-map shorthand is not copied
  as an exact based-map equation.
- Archived GrishaPerelman2.tex §7.3, lines 1105–1135, persistence and ambient
  incompressibility through surgery. This short primary assertion is not
  substituted for the written IMS proof.
- `reference_checks_revision118.md`, `reference_checks_revision167.md`,
  `reference_checks_revision168.md`, and the exact retained source identities
  and reopened passages in `source_checks_revision168.json`.

Unchanged source checks reused at their recorded scope:

- Kleiner–Lott, February 20, 2013: §91 pp.2818–2823/PDF232–237; §68
  pp.2746–2748/PDF160–162; §73 pp.2758–2762/PDF172–176; scalar bound
  §79.11 p.2780/PDF194; profile conventions §85–86.9.
- Meeks–Yau Math. Z.179 (1982), Theorems1–2/Assertion2,
  pp.153,155–157/PDF4,6–8. Nullhomotopy must be supplied; the printed theorem
  suppresses it. No claim of a newly checked Lean Meeks–Yau implementation.
- Meeks–Pérez–Ros (2008) Lemma2.1/Theorem2.8 and the stability conventions,
  with IAU01's compact intrinsic ball correction. This radius leaf is not
  included in the present Lean skeleton.
- Full finite-volume Mostow proof/dependency audit revision118; Schwartz's
  compact theorem is not imported as if it already proved the finite-volume
  extension. Archived versions and hashes remain distinct from moving sources.

The author publications page for Schwartz was refreshed on this task and its
Mostow entry had no separately linked correction. An attempted old Lott URL
returned HTTP404. The revision168 bounded author/publisher correction review
is retained for the unchanged surgery/minimal-surface claims; no exhaustive
absence-of-errata claim is made.

## Deliberate remaining decomposition

This is not one declaration per Chapter8 node. QRG global core/end comparison,
quantitative compactness, HPI actual persistent smooth embeddings and coverage,
Meeks–Yau existence, surgery-neck avoidance, kernel transport, and actual
upper-barrier production are not separately formalized here. The root
selected-flow existence leaf combines those remaining producers at a coarse
interface. Its `sorry` must be split into these developments during proof work;
the conditional consumers here are not evidence that those producers exist.
The root selected-flow interface now pins its obstruction to the actual
`exteriorDiskArea` and requires actual minimizer attainment on the same F;
it no longer takes an unrelated numerical A. Its future refinement still
needs the prescribed-meridian/kernel and exterior-family geometry.

The added `LongTime/ExteriorDiskFlow.lean` uses the actual last stage and
physical metric of `ObservationTower.observe` at every post-event time. At
positive regular times, proved equality/HEq lemmas identify them with the
existing RegularSlice stage and metric. Its area function is the actual
exterior disk infimum on this same tower, not an arbitrary number. Only its
negative-time extension uses clipping to zero; the producer requires the
area half-line to start after the selected positive slice. No new `sorry`
is used by this helper.

The independent root integration review is recorded in
`long_time_independent_review.md`. It found and required correction of the
initial draft's A/flow/tolerance quantifier reversal, and separation of closed
nonnegative components before the sequence-based collapse step.

## Verification

All six owned leaves compile with Lean4.33.1 and LEAN_NUM_THREADS=2, using the
existing warm dependency cache. Four direct `sorry` leaves remain: generalized
HG14, finite-volume Mostow–Prasad, curvature-to-local-hyperbolic atlas, and
continuity from two-direction minimizing-disk comparisons. No existing proved
file was modified by this subtask. The build log is
`.lake/gc/hyperbolic-skeleton-build.log`, with the same-flow helper checked in
`.lake/gc/exterior-disk-flow-build.log`. Compilation checks the exact stated
interfaces; it does not verify the four leaf proofs or their source adequacy.
