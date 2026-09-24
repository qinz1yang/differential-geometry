# Section 32 descent: implementation draft after route review

Review date: 2026-09-24 UTC. Lane b, token claude-agent-b-20260919.
Checkout: D:/differential-geometry-moise-int, branch codex/moise-integration.
Latest read-only HEAD observed: 0c5a656d7c15628d4113fe5aaaadf87ec6dabfe3.
The checkout is shared and the lead may advance HEAD independently.
All PL-relative paths below refer to DifferentialGeometry/Topology/PiecewiseLinear/.

## Verdict and limits

There is a coherent mathematical route from the existing tower, initial separator, and allowed
inputs. No counterexample or need for a new named input was found in this review. However, the
current public state and capping interfaces do NOT yet justify the remaining classification and
bridge-existence claims. The three substantial new proof gates are:

1. Boundary-marked capping transport, followed by classification through a reference subsurface
   of the original odd torus.
2. A genuine initial component meeting both essential seam colors, and its survival under capping.
3. Deleting a connected open patch of a closed PL surface whose bounded filling misses both vertices.

These are proposed internal theorems to prove, not hypotheses to add to the frozen leaf. This
review does not certify their Lean elaboration or transitive axiom closures. Do not replace any
of them by a transition oracle or by an assumption packaging the intended conclusion.

The Euler-characteristic component ledger remains useful, but a chi increment alone does not
classify a component or identify its marked boundary circles. The reference-subsurface route is
preferable to building a general genus-and-boundary classification solely for this task.

No downstream annular-chain open-cell, pseudo-cell, or reduced-disk leaf is used in this route.
The generic limit lemmas in the probe may be copied and revalidated in plain namespaces.

## Exact current verification state and first action after switching back

- Modules 1--61: jointly audited and logged. Baseline manifest:
  Codex13CarrierNonseparationManifest.json.
  Audit: AuditCodex13CarrierNonseparation.receipt.json; exitCode=0, diagnosticLines=0,
  sourceStable=true, sharedArtifactsModified=false. Allowed axioms and all 13 linters passed.
- Modules 62--70: individually compiled with zero diagnostics; every receipt was re-read and its
  source SHA-256 matched during this review. Their joint axiom/linter audit is still pending.
- Module 71, CanonicalSurfaceClosedDeletion: the proof now elaborates (compiler exitCode=0),
  but the checker rejects an unused-tactic warning, so it is NOT an accepted clean module.
  Its receipt has diagnosticLines=2 (warning plus associated diagnostic text).
- No module 72 has been created. This review did not start a compiler or edit a Lean source.

The next exact source repair is to remove the redundant line in module 71:

    change Nat.card (ConnectedComponents (Y i).space) + 1 = _

Keep the following rewrite and proof:

    rw [show Y i = R from Function.update_self i R X]
    exact hcount

Then prepare/check module 71 using the host guard and lease. Extend the 61-module external audit
with modules 62--71, run it serially, archive its receipt/log, and append accepted receipts/hashes
through RecordCodex13Checkpoint.ps1. Do not mistake the current warning-bearing receipt for that
future clean checkpoint.

Modules 62--71, in order:
BallInteriorContractible; TubePairSimplyConnected; EmptyBoundaryManifold;
CanonicalSurfaceClosedNonseparation; CollaredTraceRemoval; CanonicalSurfaceClosedTraces;
CanonicalTowerSurfaceClosed; TowerSurfaceComponentDeletion;
CanonicalSurfaceComponentComplement; CanonicalSurfaceClosedDeletion.

## Notation and the state already available

Write E_i = T''(2*i), Theta_i = T''(2*i+1), and O_j = phi '' S(j).
The actual odd row is L_i = (X i).space and its closed carrier is
K_i = (O_(2*i) union O_(2*i+1)) union O_(2*i+2).
The full-even-tori surface is

    Mfull(X) = union_i (E_i union L_i) union {P'}.

IsCanonicalSurface records finite oriented WB2 rows, pairwise disjoint rows,
L_i subset interior K_i, exact intrinsic boundary on E_i union E_(i+1), finite collared traces,
original seam provenance, exclusion of P', and the actual separator property.

CanonicalSurfaceNullNormalization already performs real finite-window disk splits and strict
finite null-rank descent. A row i can be classified only AFTER BOTH seam indices i and i+1 have
been normalized. A window's outermost half-processed row must not be called completed.

CanonicalSurfaceClosedTraces proves that a boundaryless row component avoids every E_k.
CanonicalSurfaceClosedDeletion supplies the actual Type 1 deletion, using the new compact
filling and relative exterior machinery, subject only to the compiler warning above.
Type 1 does not require a sphere-versus-torus classification of the closed component.

## Gate A: preserve the actual marked maps

CollaredTraceSplit.exists_split_reducing_nullTraceCount_with_cap already produces the SAME
actual PL cap map f together with

    EqOn f id ((L minus O) union ((L inter T) minus G)).

SeparatingSurfacePairSplit and IsCanonicalNullSplit.capping currently discard this certificate.
Expose it through those outputs and through the component correspondence. For the opposite end
of a row, the other even torus misses the active outer-even support, so its entire boundary is
fixed by the outside-O clause. The uncapped component maps need the same surviving-boundary
certificate. Do not choose an unrelated existential PL equivalence and call it marked.

Minimum useful consequence: every surviving boundary circle is mapped onto itself, preferably
pointwise. Preserve the component equivalence and the actual circle labels, not just a count.
This is information already in the constructed proof, not a new geometric assumption.

## Gate B: classify by a reference subsurface of the fixed odd torus

For each current component C of row i that has at least one boundary circle essential in
Theta_i, maintain a finite connected WB2 reference complex R and a PL map f such that

    R.space subset Theta_i,
    boundary R = boundary C,
    f : R.space -> C is a PL homeomorphism,
    f is the identity on boundary R.

Initially use the actual corresponding component of canonicalOddPiece and the identity map.
Components without any essential boundary do not need to be embedded back into Theta_i.
After both endpoint null ranks vanish, such components have empty boundary and are Type 1.

Reference update under a cap along G:
- G is an original null seam. CanonicalTowerNullSeamDisks transfers nullity to Theta_i using
  h314; choose the actual PL disk D in Theta_i with boundary G.
- If the new component still has an essential boundary H, then H is a surviving old boundary,
  H is disjoint from G, and H cannot be contained in D.
- The connected intrinsic interior of R avoids G and lies on one side of D. It cannot lie
  inside D, because its closure contains R and hence H. Thus R.space inter D = G.
- Glue R and D, extend the identity boundary correspondence between D and the actual cap disk,
  and compose with the SAME actual cap map. This yields the next marked reference.
- Obtain the new reference manifold and boundary by transport through that PL equivalence;
  do not introduce an extra reference-collar hypothesis if it can be obtained this way.

Useful existing APIs, to inspect again with precise scopes before implementation:
- PLDiskCircleComplement: IsPLHomeomorphOn.exists_disk_complement_of_circle.
- SurfaceDiskSeparation: IsPLTorus.disjoint_disk_of_essential_circle.
- ManifoldInteriorConnected: isConnected_sdiff_boundaryComplex_space.
- ManifoldInteriorDensity: space_subset_closure_sdiff_boundaryComplex_space.
- ManifoldSubcomplexBoundary: inter_closure_sdiff_eq_image_stdSimplexBoundary.
- BallReplacement: exists_isPLHomeomorphOn_extension_of_stdSimplexBoundary.
- PLHomeomorphGluing: exists_isPLHomeomorphOn_union.

Terminal classification of a reference component:
- Zero boundary circles: Type 1.
- Exactly one essential boundary circle: impossible. The reference is a proper subsurface of
  Theta_i, whose relative frontier is that circle. Its connected interior and nonempty outside
  force the circle to separate Theta_i. SeparatingPolygonDisk then supplies a disk, contradicting
  essentiality. Never call h286 with n=1.
- At least two: identify R.space as the closure of one connected component of Theta_i minus
  its boundary-circle family. Use the relative-frontier theorem and dense connected intrinsic
  interior, then apply h286 legally. Transport the annulus with its two EXACT ends by the marked f.

The two ends can both be on E_i, both on E_(i+1), or one on each. Classify these as returning or
bridging only after obtaining their actual labelled circles. Do not infer opposite ends merely
from Euler characteristic or from being an annulus.

## Gate C: every row has a real bridge witness

Do NOT infer existence from h314 alone: it gives a universal generator-or-disk alternative.
Do NOT infer it from reducing a finite bridge count to at most one. Do NOT use an unproved
nonseparation assertion for the two infinite tower tails.

A bounded construction from the original canonical configuration is available:

1. Produce a PL carrying circle Klo in Theta_i inter interior(S''(2*i)) using
   PolygonCarrierOfSpine.exists_polygon_carrier_of_spine.
   Its shared core is phi '' J(2*i+1); the other core phi '' J(2*i) lies inside the lower even
   torus and is disjoint from the odd solid, using the previous outer torus and apart.
   The spine data come from the planar cell interior/revolution model and embedding transport.
   The inner-solid generator follows from
   fundamentalGroup_map_inclusion_bijective_of_isSpine_of_isTopologicalSolidTorus.
   The symmetric construction gives Khi inside the upper even torus, using shared core
   phi '' J(2*i+2) and other core phi '' J(2*i+3).

2. Let Wlo = Theta_i inter S''(2*i). It carries H1 of the odd solid because it contains Klo.
   Khi is an essential PL circle in Theta_i disjoint from Wlo. The relative frontier of Wlo
   is contained in the finite lower trace circles. Apply
   TorusSubsurfaceCarrier.IsPLTorus.carriesFirstHomologyOnto_or_subsingleton_of_disjoint
   with the identity map on Theta_i. Exclude the trivial target using nontrivial H1 of a solid
   torus. This gives an essential lower trace circle. Exchange lower and upper to get both colors.
   The generator/nonseparation implications use TorusCircleHomology, not a claim that any
   zero image in a solid torus must bound a disk on its boundary.

3. Finite disjoint essential circles on Theta_i cut it into a cyclic family of annuli.
   Both colors occur, so there is a mixed adjacent pair Glo,Ghi. Prove the bounded adjacency
   statement using h286 plus connectedness of the finite cut-incidence graph, or a cut-open
   annulus model. The required hypothesis n>=2 is supplied by the two disjoint colors.

4. Do not claim the whole mixed annulus is initially in canonicalOddPiece. Null trace circles
   may make holes. Their disks avoid every essential circle and lie in the open band. Take a
   maximal disjoint disk subfamily and remove its interiors. The resulting punctured annulus
   has connected intrinsic interior U, misses ALL original trace circles, and its closure
   contains both Glo and Ghi. For connectedness, map the annulus to a prism lateral boundary,
   add its two cap disks, and reuse sphere-minus-finitely-many-disjoint-disks connectedness.
   Sources include DisjointRimDiskFamily and
   TubeOfGraphDualCells.IsPLSphere.isConnected_sdiff_iUnion_of_isPLBall_two;
   TorusSubsurfaceCarrier already contains the null-disk nesting/maximal-family pattern.

5. U has constant inside/outside membership for each even solid. It cannot lie inside the
   lower solid, since its closure meets Ghi in the disjoint upper solid; symmetrically for the
   upper solid. Thus closure U is contained in the actual initial oddPiece. This provides ONE
   actual initial component containing BOTH essential marked circles.

6. Propagate just that witness through the actual component equivalences from Gate A. Null
   capping does not merge components and fixes both surviving essential circles. Type 1 cannot
   delete this component because its boundary is nonempty. Returning-component deletion cannot
   delete it because its two end colors differ. Once Gate B classifies it, it is a bridge.

This avoids maintaining a global covering of all reference bands. Per-component reference maps
ALONE do not provide the initial mixed witness; that existence theorem is a separate gate.

## Gate D: one general connected-patch deletion theorem

Work in the actual open pair interior U. The proposed theorem has these local geometric data:

- M and R are relatively closed in U; R subset M; M separates a,b in U.
- C = M minus R is nonempty and connected.
- Q is a finite, connected, closed PL two-manifold with C subset Q subset M.
- V is a compact regular closed region contained in U, frontier V = Q, and a,b are outside V.

Conclusion: R still separates a,b.
These are certificates to PRODUCE in each application, not new inputs to exists_descentSequence.
Notice C = Q minus R, so C is open in the locally path connected manifold Q and is path connected.

Proof draft: if R does not separate, take a path in U minus R from a to b. If it meets V, take
its first and last contact with V; both contact points lie in Q minus R = C. Join them by a path
in C. The latter has compact image, so restrict a bicollar of Q to a sufficiently thin neighborhood
of that image missing R, and push the middle path to the exterior side of V. Near the contact
points, connect the original exterior path segments to this pushed path in the local exterior
half-ball. Replace the entire first-to-last segment once. The resulting path avoids both R and C,
contradicting separation by M. This handles potentially infinitely many excursions into V.

An alternative is a component proof: in the connected component W of U minus R meeting C,
Q inter W = C. The unique local exterior-component label is locally constant along connected C.
Every component of W minus V meets that exterior collar, so W minus V is connected. The two
vertices then lie in one component of U minus M.

Important API traps:
- SurfaceRelativeExterior cannot directly be applied to the noncompact open patch C.
- Separates.of_frontier_replacement cannot directly be applied with N=V: its frontier condition
  asks for frontier V minus R subset complement M, while that set is exactly C subset M.
- Use the existing first/last-path argument only as a proof template, or construct a genuine
  outward buffer with the required frontier condition. Do not silently reverse that condition.

Applications (all supporting geometry is finite):

Type 2: let A be a returning annulus and J0,J1 its two essential ends on one E_k.
Use h286 with n=2 to obtain an annulus B on E_k with these ends. Glue A and B along their FULL
boundary to a finite closed connected PL surface Q. It lies in interior K_i. The already proved
SurfaceRegionInSolidTorus filling theorem puts V inside interior K_i; havoid puts both vertices
outside. Remove A's intrinsic interior globally, or equivalently delete A's entire row component
while retaining its boundary in the full even torus. Apply Gate D.

Type 3: choose Bkeep and Bdiscard between E_i and E_(i+1). Use h286 n=2 to connect their lower
ends by Alo and their upper ends by Ahi. The two bridges are disjoint; the two endpoint annuli are
disjoint. Use ManifoldDisjointUnion.exists_space_disjoint_union for these two pairs, then
BoundaryGluing.exists_isCombinatorialManifold_space_union along the same four-circle boundary.
The four-annulus cycle is connected. No genus calculation or separate orientation hypothesis is
needed. Q lies in interior K_i, so the same filling and Gate D delete Bdiscard. Keep at least
one bridge using Gate C; only excess bridge count is decremented.

Half choice: once row i-1 and row i each have exactly one bridge, E_i meets the rows in exactly
two different essential circles Jhi(i-1), Jlo(i). Produce BOTH complementary closed annuli and
their exact union/intersection on E_i, not just the one annulus existential returned by h286.
Either one can be retained. Take Q=E_i and delete the other annulus's intrinsic interior.
Its patch meets no remaining odd row, and both vertices are outside its solid torus/filling.
Gate D preserves separation. There is no extra global binary-choice equation: compatibility is
specified by these exact end labels. Independent choices are valid after the local deletion proof.

This route does not need h267 to select a prescribed pair of three surfaces. The frozen leaf must
still retain h267 byte-for-byte. Do not edit its signature merely because a stronger reusable
native topological theorem makes that particular input unused.

## Finite measures and preservation certificates

Use finite component labels supplied by the actual finite complexes. Suitable phase measures:

1. Existing finite windowNullRank.
2. Number of closed components in the active rows (or total components while deleting a closed one).
3. Number of returning components in those rows.
4. Sum of bridgeCount(i)-1 over active rows, AFTER proving bridgeCount(i)>=1.
5. Number of pending half choices at the active completed seams.

Every transition must provide the actual remainder complex, its finite manifold/orientability
proofs, exact boundary/trace deletion, component correspondence, unchanged rows, protected-set
equality, and separator certificate. ManifoldComponentComplement already handles deleting an
arbitrary component; adapt the trace proof to losing its boundary circles rather than assuming
the component is disjoint from all even tori (that special assumption is only valid for Type 1).
Later phases only delete circles/components, hence preserve null-freeness. Half deletion does not
change the underlying full-even-tori state at all.

## A compatible recursion that reuses the existing full-torus state

Do not force IsCanonicalSurface itself to represent partially deleted even tori.
Keep two layers of data:

- X_n, an actual underlying full-even-tori IsCanonicalSurface;
- a finite set of completed even indices and the permanently chosen H_i there.

Define the displayed separator M_n by finitely deleting the complementary halves from Mfull(X_n).
Each deletion is justified by Gate D. Reconstruct it from the underlying full surface at each
stage; M_n need not be the literal starting surface of the next surgery. The frozen conclusion
requires closed separators and local eventual equality, not a step equation between M_n and
M_(n+1). Thus no extra partial-torus variant of every existing null-split theorem is required.

A concrete guard schedule:
- Completed rows [a,b] each have exactly one bridge. Only interior even indices a+1,...,b have
  selected halves. Guard tori E_a and E_(b+1) remain full in the displayed surface.
- Both seam indices of every completed row have already been null-normalized.
- To expand, normalize new seam indices a-1 and b+2, then normalize rows a-1 and b+1 through
  classification, closed deletion, returning deletion, and excess-bridge deletion.
- The new null operations change only rows a-2,a-1 or b+1,b+2. Their even outer supports are
  disjoint from old completed rows/halves by apart and the exact unchanged-row clauses.
- Select halves at the old guard indices a and b+1 using the new bridges. They become permanent;
  the new guards are a-1 and b+2.

Start by normalizing seams 0 and 1 and row 0. There are no interior halves yet. Expand to [-n,n],
or use larger padded intervals containing all carrier indices meeting the next compact exhaustion
set of U minus {P'}. The latter follows the prescribed compact-window workflow exactly; the
integer-interval version explains why only a one-row guard is needed.

Set M_0 exactly equal to initialSurface. Let the first normalized checkpoint be M_1; subsequent
checkpoints use the finite-half construction above. All intermediates retain P', since no carrier
contains P'. The old bridge geometries, labelled endpoints, and chosen H_i are literally fixed.

## Limit and frozen endpoint assembly

For every fixed row/half index there is a stage after which its set is literally constant.
For each x in U minus {P'}, the tower's locallyFinite field gives a neighborhood meeting finitely
many OUTER carrier indices. Triple carriers still have finite local support by the three affine
index preimages, exactly as in CanonicalTowerSurfaceClosed. Take the maximum stabilization stage
of this finite set. This proves the required neighborhood equality, not merely pointwise equality.

Copy and revalidate the probe's generic locally_eventually_eq_iUnion_of_finite_support and
isClosed_of_locally_eventually_eq_off_point under unique plain names when needed. Include P' in
every M_n and in the limit. Relative closedness follows from eventual local equality off P'.
Do not use the downstream annular-chain open-cell theorem to prove any deletion or stabilization.

Every IsAnnularChain field must be discharged explicitly:

- half / bridge: the marked annulus certificates, with half endpoints Jhi(i-1),Jlo(i).
- halfSubset / halfSubsetTorus: chosen H_i lies on E_i, hence in its fixed outer torus.
- bridgeSubset: the state's actual triple-carrier containment.
- loSubset / hiSubset: the saved original seam labels on E_i and E_(i+1).
- loGenerator / hiGenerator: CanonicalSurfaceEssentialSeams, original trace provenance, h314,
  and zero null counts; preserve the universal inclusion-proof/basepoint form in the frozen field.
- halfInterBridge / bridgeInterHalf: full row boundary meets and exact annulus ends, not just subsets.
- halfDisjoint: distinct even tori lie in disjoint outer carriers.
- bridgeDisjoint: the state already gives pairwise disjoint rows.
- halfBridgeDisjoint: CanonicalSurfaceClosedTraces.inter_even_subset_boundary plus the two
  exact end labels. This is essential for rows two indices apart whose triple carriers overlap.
- centerNotMem: the state and outer-torus center avoidance.

Restate the leaf and its variable block byte-identically only at final closure. The frozen target
is in Skeleton/Section32PseudoCell.lean:260--291; no Skeleton module may be imported.

## Implementation order after the outstanding clean checkpoint

1. Expose the real marked cap/uncapped-component maps; recompile all changed own consumers.
2. Prove reference-disk attachment and terminal annulus classification.
3. Prove the initial mixed-color component witness and marked-history preservation. This is the
   nonemptiness gate; settle it before writing a redundant-bridge normalization wrapper.
4. Prove the general connected-patch deletion theorem and its Type 2 / Type 3 / half applications.
5. Assemble actual finite-rank normalizers with preservation certificates.
6. Implement guarded compact-window recursion with an underlying full state and displayed M_n.
7. Prove all limit fields, close the unchanged leaf, and run the full tree-external audit.

Search names and statement shapes before every new declaration. Candidate APIs mentioned above
are source-verified guidance, not fresh compiler/axiom certification. Revalidate newly introduced
dependencies through the private-root checker and the final axiom audit. Keep the lease at one
Lean process and host at no more than four. No git writes, no frozen edits, no new named inputs.

## Final API notes from the independent review

The original mixed-witness construction uses the finite range 2*i-1 through 2*i+3, including
both far endpoint cores; it is not restricted to the central triple. PolygonCarrierOfSpine's
H1-isomorphic-to-Z helper is private. To rule out a trivial H1 target, use the public
SolidTorusHurewiczOne injectivity theorem together with the existing nontrivial fundamental-group
result, or prove the natural standalone H1 result; do not refer to the private helper by accident.
For the disjoint null-disk subfamily theorem, its condition that two disks do not cover the torus
is witnessed by any point of an essential circle, since every such disk avoids that circle.
