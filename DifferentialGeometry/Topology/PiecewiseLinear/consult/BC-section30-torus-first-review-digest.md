# Toroidal-shell interpolation: first review and lead due diligence

Date: 2026-09-22. Owner-supplied answer to [AT](AT-section30-torus-review-request.md),
against mirror `f3a1e6ba2f153cc1df42b50c9da4d8ec95def22d`.

**All seven statements OK and frozen; all seven proofs OPEN.** The lead checked the complete
current source, actual suppliers, assemblies and paper fixtures. No new endpoint assumption,
duplicate leaf, complete counterexample or substantive disagreement was found.

| Leaf | Verdict | Checked obligation |
|---|---|---|
| `IsCombinatorialManifold.nonempty_homeomorph_torus_of_isOrientable_of_eulerChar_eq_zero` | OK | Finite connected closed orientable genus-one recognition; orientability excludes the Klein bottle. |
| `IsPLTorus.exists_combinatorial_triangulation` | OK | Finite polyhedral triangulation and two-dimensional link recognition, independently of three-dimensional approximation. |
| `subset_interior_of_nested_tori` | OK | Identify the actual bounded region using its frontier, regular-closedness and connected interior/exterior, then obtain both strict inclusions. |
| `IsPLTorus.exists_nontrivial_fundamentalGroup_kernel_in_solidTorus` | OK | A map from the torus group to the group of the ambient interior of a solid torus has nontrivial kernel. |
| `not_nullhomotopic_inclusion_of_nested_tori` | OK | The shell product retracts onto its inner end and glues to the identity on the inner solid torus; the actual inclusion is not nullhomotopic. |
| `exists_isPLBall_superset_of_exterior_compression` | OK | Construct one compact regular neighborhood inside the prescribed open set and identify that very neighborhood as a ball enclosing the original region. |
| `exists_ball_pair_of_interior_essential_disk` | OK | A relative disk neighborhood and its cut remainder give two balls with precisely two disjoint common boundary disks. |

## Source and assembly checks

`ToroidalShellHomology.lean:55` supplies the finite connected orientable separator and Euler
characteristic zero used in 30.6. The first leaf consumes these actual fields; it does not
silently remove orientability. The second leaf starts from the actual definition of
`IsPLTorus`, a polyhedron with a topological torus homeomorphism. Its finite surface link
identification remains to prove and does not require the three-dimensional Moise producer.

`SurfaceFilling.lean:77` jointly returns the region complex `R`, its intrinsic boundary,
ambient frontier, regular-closed certificate, connected interior and connected exterior.
The nesting leaf consumes these certificates for that same `R`. The kernel leaf must still
identify the topological solid torus's intrinsic interior with its ambient interior before
using the groups `Z²` and `Z`. The shell retraction fixes the full common boundary so that
it glues to the identity; neither argument consumes 30.8.

`SurfaceEssentialDisk.lean:69` consumes `Moise252` and the actual fundamental-group kernel,
and returns an essential PL disk **inside the same prescribed open set**. The assembly uses
`U=interior S₂`, the exact disk-boundary image and connectedness of its interior to choose
the interior or exterior branch. It does not add unrestricted `Moise264` as a hypothesis.

In the exterior branch, the ball output retains `B ⊆ interior S₂`. The maps
`S₁ → B → S₂` therefore give the actual nested inclusion; contractibility of `B` contradicts
the separate shell-inclusion leaf. In the interior branch,
`exists_cylindricalDiagram_of_ball_pair` consumes the precise two-ball intersection, with
ambient frontiers converted to intrinsic boundaries in dimension three. The three existing
assembly signatures remain `Moise252 → Moise306`,
`Moise306 → Moise252 → Moise307`, and `Moise252 → Moise307`.

## The support obligation in exterior compression

For arbitrary open `U` containing the compact union `R.space ∪ D`, choose a sufficiently
small compatible regular neighborhood **inside `U` first**. Essential compression of the
torus gives its boundary sphere. The proof must identify the bounded side with that same
neighborhood and hence show it is a PL ball. A sphere inside `U` need not bound a ball inside
`U`; applying Schoenflies to an unrelated sphere without the side identification loses the
output `B ⊆ U`. This is an internal proof obligation, not a missing hypothesis or a verified
counterexample to the leaf.

Similarly, the interior leaf must build the relative disk product neighborhood and closed
cut remainder, prove both are balls and identify exactly the two end disks. It does not take
the cylindrical diagram as a renamed assumption. The lead visually checked printed
pp.217–218, including both compression cases and the subsequent separate 30.8 statement.

## Shared paper fixtures

Let `ρ=max(|x|,|y|)` and `C_a={4-a≤ρ≤4+a, |z|≤a}`. Use `S₁=C₁`, `R.space=C₂`,
`S₂=C₃`, and `T=∂C₂`, with common finite subdivisions of the rectangular blocks.
The regions are regular closed, have connected interiors and exteriors, and have connected
orientable torus boundaries of Euler characteristic zero. Both inclusions are strict.

For `p,q∈∂[-1,1]²` and `a∈[1,3]`, the shell map is

\[
(p,q,a)\longmapsto((4+a q_1)p_1,(4+a q_1)p_2,a q_2).
\]

Its inverse recovers `a=max(|ρ-4|,|z|)`, `q=((ρ-4)/a,z/a)` and `p=(x/ρ,y/ρ)`.
This is a topological homeomorphism, exactly what `IsToroidalShell` asks for; no PL claim is
made for the bilinear formula. The level `a=2` supplies the separator and shell inclusion.

The interior meridian disk is `D_in={y=0, 2≤x≤6, |z|≤2}`. It lies entirely in `interior C₃`,
meets `∂C₂` exactly along its boundary and represents a nonzero torus class killed in the
solid torus. The halves `C₂∩{y≥0}` and `C₂∩{y≤0}` are PL balls; their intersection consists
of the two disjoint rectangular disks with `x∈[2,6]` and `x∈[-6,-2]`.

For the **separate local exterior fixture**, take `D_out={z=0,ρ≤2}` and
`U={x:dist(x,C₂∪D_out)<1/4}`. Its interior is outside `C₂` and its boundary is essential on
the torus. This `U` is not `interior C₃`: the center of `D_out` is outside `C₃`. Thus the
fixture does not pretend to inhabit the impossible exterior branch of the full nesting
assembly. Both disks admit PL simplex parametrizations. These mathematical checks are not
joint Lean inhabitants; **both fixtures remain UNTESTED**.

## Verification boundary

The seven proofs and both fixtures remain OPEN/UNTESTED. Only module documentation changes;
mathematical declarations, scopes and assemblies are unchanged. The initial local torus
file uses CRLF while AT's Git blob uses LF; snapshot comparison normalizes that pre-existing
difference, and the edit preserves all local code bytes outside the module documentation.
The committed mathematical text is compared directly with the review blob.

The private lead evidence directory `claude-moise-agent-c/fill-interface-evidence-20260922`
contains `four-producer-review-snapshot-comparison.json`, `four-producer-frozen-review.json`
and the unchanged-source `Section30Torus-audit.json`. The final lease-c check passed with
Lean exit 0, a stable source hash and seven authorized leaf-sorry warnings only. The earlier axiom audit of the eight real suppliers is
retained; no unchanged real-module audit is repeated or new proof claimed. No full root
build is claimed. The sole progress entry is `FREE_INPUTS.md` B1.h.

Final check UTC: `2026-09-22T13:27:50.2793980Z`. Checked source SHA-256:
`1a136e007407fbbea5880f687b70331d8d302831e7b3df196c8252500920f41e`.
