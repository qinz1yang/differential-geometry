# Model comparison angles and the curvature-zero limit

The new leaf is `DifferentialGeometry/Geometry/Comparison/ModelAngle.lean`.
It implements AC35 on Lean 4.35.0-rc3 and the pinned mathlib commit
`c55e6e786f49471c72fbddbec5415808896aec1e`. It does not assert a
Riemannian or Alexandrov comparison theorem.

## Exact mathematical contracts

All public declarations use the existing namespace
`DifferentialGeometry.Geometry.Comparison.Toponogov`. The existing low-level
`Toponogov/ComparisonAngle.lean` supplies the Euclidean comparison-angle
definition, its cosine law, and its degenerate-triangle identities. That leaf
was built without modification. The legacy duplicate angle vocabulary is not
imported.

`comparisonAngleNegCurvature κ a b c` has central side lengths `a,b` and
opposite side length `c`. The intended domain has `κ ≥ 0`: the actual model
curvature is **minus κ**, and the lengths in the hyperbolic functions are
multiplied by **sqrt κ**. At `κ = 0`, the definition is exactly the existing
Euclidean `comparisonAngle a b c`. At nonzero κ, it is the arccosine of

```
[cosh(sqrt κ a) cosh(sqrt κ b) - cosh(sqrt κ c)]
/ [sinh(sqrt κ a) sinh(sqrt κ b)].
```

As a Lean real-valued function this definition is total. Values outside the
geometric side-length and nonnegative-κ domain are not asserted to represent
angles in any model space.

The public results are:

- `comparisonAngleNegCurvature_zero`: literal equality with the inherited
  Euclidean angle, for every triple of real arguments.
- `comparisonAngleNegCurvature_mem_Icc`: the total function takes values in
  `[0,π]`, because Mathlib's arccosine does.
- `cos_comparisonAngleNegCurvature_of_pos`: for κ>0, a>0, b>0,
  `|a-b| ≤ c ≤ a+b`, its cosine equals the displayed quotient. In particular,
  this is not relying on arccosine silently truncating an invalid cosine. The
  proof establishes the quotient belongs to `[-1,1]` from the two triangle
  inequalities, monotonicity of cosh in absolute value, and the hyperbolic
  addition and subtraction identities.
- `comparisonAngleNegCurvature_add` and
  `comparisonAngleNegCurvature_abs_sub`: for κ≥0 and a,b>0, the opposite
  sides a+b and |a−b| give the exact angles π and zero, respectively.
- `comparisonAngleNegCurvature_self`: the repeated-arm specialization
  gives `comparisonAngleNegCurvature κ a a 0 = 0` for κ≥0,a>0. This is used
  to pass from a four-distinct-points source comparison to comparison with
  repeated outer points permitted.
- `comparisonAngleNegCurvature_comm`: swapping the two central sides
  preserves the angle.
- `tendsto_comparisonAngleNegCurvature_zero`: for an arbitrary filter,
  κ tends to zero, a,b,c tend respectively to a₀,b₀,c₀, κ is eventually
  nonnegative, and a₀,b₀ are positive. The actual angles then tend to the
  Euclidean angle of a₀,b₀,c₀. The filter can include infinitely many κ=0
  indices; no strict positivity of κ is imposed.

The last theorem is analytically valid without triangle inequalities or
positivity of each approximating central side. AC35's valid model triples
are a special case. Positive limiting central sides imply their eventual
positivity. The theorem permits limiting opposite side length zero and
both degenerate triangle equalities. It does not assume the angles avoid
zero or π.

## Proof and source correspondence

Read the AC35 statement and full proof in `master207A.tex`, lines 3843–3890,
label `lem:alexandrov-angle-zero-limit`, and the relevant source comparison
in `reference_checks_revision69.md`. Blueprint source SHA256:
`277359ee147d25184d4b38b20a91ee44a394fd6ea316cfc368fab74e06bef79b`.

Reopened the retained AKP `model.tex`, branch `vol1`, commit
`ed6a16eb2a3c66c1f0f54b183bd1a4176e78b245`, SHA256
`db849cb9a051e0c3f8ec335942c954f14223c542eee1a40c4bca4ea2a63af9f8`.
Read the model/triangle conventions at lines 6–34, curvature scaling and
Euclidean/hyperbolic values at lines 71–95, and the cosine law at lines
192–207. Its side order is opposite side first; the Lean argument order is
the inherited convention of central sides first. The source curvature
parameter is replaced by `-κ`, which produces the numerator sign and the
sqrt κ length scale displayed above. The pinned source is distinct from
the published edition and moving author repository. The unchanged errata
comparison in revision 69 is reused; this leaf makes no new source-edition
or absence-of-errata claim.

The proof removes the singularity using private functions

```
S(u) = sinh(u)/u for u≠0, with S(0)=1,
Q(u) = S(u/2)^2 / 2.
```

Mathlib's actual derivative of sinh at zero proves continuity of S there.
The exact cosh double-angle identity proves
`cosh(u)=1+u²Q(u)`, so Q is continuous at zero with Q(0)=1/2. This gives
the same regularization as AC35 without importing a separate power-series
development. The hyperbolic quotient is identically

```
[a²Q(sa)+b²Q(sb)-c²Q(sc)+s²a²b²Q(sa)Q(sb)]/[abS(sa)S(sb)],
```

where s=sqrt κ. Its denominator tends to a₀b₀>0. Taking the joint limit
and applying globally continuous arccosine proves the theorem, including
its endpoints. The κ=0 branch agrees with this expression exactly.

The canonical Euclidean-angle leaf and its used cosine and endpoint
lemmas were checked with `#print axioms`; only `propext`,
`Classical.choice`, and `Quot.sound` occurred. All nine new public
declarations were likewise checked individually and have only those
three axioms. A scoped Lake build of the new leaf passed with 2191 jobs
and no warnings. Further combined
declaration/axiom verification is recorded by the shared checker receipt.

Explicit consumer examples were checked through Lean stdin for the
nonnegative-curvature-parameter filter approaching zero, with central
sides 1,1 and opposite side respectively 2 and 0. They recover the limits
π and zero. The parameter filter includes κ=0 and positive κ values, so
these applications exercise the branch joining and degenerate endpoints.
