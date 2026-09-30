# Hyperbolic geometry, exterior disk area, and the incompressibility consumers

This report translates the **actual Lean statements** at commit
`ea0fae60ee01ef8c8d9b57a51794c6538f679c5d`. It covers all **28 authored declarations
in six files**: nine definitions, four directly admitted theorems, and fifteen
theorems with written Lean proofs. A written proof can still depend on an
admitted theorem; that distinction is recorded below. The code has not been
changed in preparing this report.

The six reviewed source files are:

- [Analysis/ODE/AreaUpperBarrier.lean](/Users/bennettchow/Documents/Codex/Geometrization/Worktrees/wtgc1/GC_BASELINE_EXPORT/DifferentialGeometry/Analysis/ODE/AreaUpperBarrier.lean)
- [Geometry/Hyperbolic/Rigidity.lean](/Users/bennettchow/Documents/Codex/Geometrization/Worktrees/wtgc1/GC_BASELINE_EXPORT/DifferentialGeometry/Geometry/Hyperbolic/Rigidity.lean)
- [Geometry/Hyperbolic/ModelAtlas.lean](/Users/bennettchow/Documents/Codex/Geometrization/Worktrees/wtgc1/GC_BASELINE_EXPORT/DifferentialGeometry/Geometry/Hyperbolic/ModelAtlas.lean)
- [Geometry/MinimalSurface/ExteriorDiskArea.lean](/Users/bennettchow/Documents/Codex/Geometrization/Worktrees/wtgc1/GC_BASELINE_EXPORT/DifferentialGeometry/Geometry/MinimalSurface/ExteriorDiskArea.lean)
- [Geometry/Flow/RicciFlow/LongTime/CuspIncompressibility.lean](/Users/bennettchow/Documents/Codex/Geometrization/Worktrees/wtgc1/GC_BASELINE_EXPORT/DifferentialGeometry/Geometry/Flow/RicciFlow/LongTime/CuspIncompressibility.lean)
- [Geometry/Flow/RicciFlow/LongTime/ExteriorDiskFlow.lean](/Users/bennettchow/Documents/Codex/Geometrization/Worktrees/wtgc1/GC_BASELINE_EXPORT/DifferentialGeometry/Geometry/Flow/RicciFlow/LongTime/ExteriorDiskFlow.lean)


The central distinction for mathematical approval is this: **the area argument
is encoded as a correct conditional deduction, but the existence of the required
geometric area data is not established in these files.** The continuous
nonnegative area function and all-time upper barriers would be contradictory.
Producing them from a hypothetical compressing torus is the difficult geometric
work; that work remains inside the broader admitted flow producer reviewed
elsewhere.

<a id="ha-0"></a>

## HA-0. Conventions and status labels

- **Definition:** an explicit mathematical object or predicate, not a theorem
  asserting that the predicate holds.
- **Admitted:** the theorem body is `sorry`. Lean has checked its type, not its
  mathematical truth.
- **Written proof, admission-dependent:** a real Lean proof whose audited
  dependency closure contains `sorryAx`.
- **Written proof, no skeleton admission:** the recorded declaration audit
  found no `sorryAx` in its closure. This is about the code's proof dependencies,
  not an independent reproof of all inherited mathematics.

Unless a subsection says otherwise, a smooth 3-manifold here is modeled on
all of \(\mathbb R^3\), hence has no boundary as a manifold. Subsets \(W\) may
have boundary. The Mostow and model-atlas statements explicitly assume
Hausdorffness and sigma compactness. The generic disk-area definitions and
consumers do not add these assumptions. Their use on the actual compact flow
carriers supplies the customary manifold conditions.

The loop parameter is \(\mathbb R/\mathbb Z\). The closed parameter disk is
\(\overline{\mathbb D}\subset\mathbb C\), with boundary parametrization
\(\theta\mapsto e^{2\pi i\theta}\). An equality of boundary traces below is an
equality of **parametrized maps**, not merely of their images or homotopy
classes.

<a id="ha-1"></a>

## HA-1. Constant-curvature geometry and rigidity

<a id="ha-1-1"></a>

### HA-1.1. Constant sectional curvature

**Lean:** `DifferentialGeometry.Geometry.Hyperbolic.hasConstantSectionalCurvature`.
**Status:** definition. Source: `Geometry/Hyperbolic/Rigidity.lean`, line 20.

For a smooth Riemannian metric \(g\) on a smooth 3-manifold \(M\), the predicate
\(\operatorname{ConstSec}(g,K)\) means
\[
 \forall p\in M\ \forall v,w\in T_pM,
 \quad (v,w)\text{ linearly independent}
 \ \Longrightarrow\ \sec_g(p;v,w)=K.
\]
There is no assertion about the library's value of sectional curvature on
linearly dependent vectors. The definition itself does not require
connectedness, completeness, finite volume, Hausdorffness, or sigma compactness.
Its elaborated signature retains only the smooth manifold and metric data it
uses.

<a id="ha-1-2"></a>

### HA-1.2. Marked finite-volume Mostow–Prasad rigidity

**Lean:** `DifferentialGeometry.Geometry.Hyperbolic.mostow_prasad`.
**Status:** admitted. Source: `Geometry/Hyperbolic/Rigidity.lean`, line 24.

Let \(M,N\) be connected, nonempty, Hausdorff, sigma compact smooth
3-manifolds without boundary. Let \(g,h\) be smooth Riemannian metrics, and
let \(K<0\) be **the same constant for both metrics**. Assume:

1. \(\operatorname{ConstSec}(g,K)\) and
   \(\operatorname{ConstSec}(h,K)\).
2. Both Riemannian metrics are complete.
3. Both total Riemannian volumes are finite.
4. A specified continuous homotopy equivalence \(u:M\to N\) is given.

Then there is a unique smooth diffeomorphism \(f:M\to N\) satisfying both
\[
 h_{f(p)}(df_pv,df_pw)=g_p(v,w)
 \quad\text{for every }p,v,w,
 \qquad f\simeq u.
\]
Thus uniqueness is **within the specified unbased homotopy class**, among
smooth diffeomorphisms preserving the metric. It is not uniqueness among all
isometries. It is not an equation between arbitrarily chosen based
fundamental-group homomorphisms. The input homotopy equivalence includes a
continuous inverse up to homotopy; no smoothness of \(u\) is required.

“Complete” is implemented as completeness of the intrinsic Riemannian
extended distance. In the connected case here this is the customary metric
completeness notion. Finite volume is literally
\(\operatorname{vol}_g(M)<+\infty\), and similarly for \(h\).

No orientability or compactness assumption is imposed. Empty manifolds are
excluded by `ConnectedSpace`; noncompact finite-volume cusped manifolds are
included. This declaration contains no quantitative closeness conclusion,
control of cusp coordinates, or time-dependent family of isometries.

<a id="ha-1-3"></a>

### HA-1.3. Local curvature gives a hyperbolic model atlas

**Lean:**
`DifferentialGeometry.Geometry.Hyperbolic.has_hyperbolic_atlas_of_curvature_neg_one`.
**Status:** admitted. Source: `Geometry/Hyperbolic/ModelAtlas.lean`, line 17.

Let \(M\) be a Hausdorff, sigma compact smooth 3-manifold, with smooth metric
\(g\) and \(\operatorname{ConstSec}(g,-1)\). Then every point has a smooth
local isometry from an open set in the fixed hyperbolic coordinate model.
That model is \(\mathbb R^3\), with coordinates \((x,y,z)\) and metric
\[
 h_{\mathbb H}=e^{-2z}(dx^2+dy^2)+dz^2.
\]
More literally, for each \(x\in M\), there is a partial smooth
diffeomorphism \(e\) from this coordinate model into \(M\), with
\(x\) in its target, for which \(e^*g=h_{\mathbb H}\) everywhere in its
source. This is precisely the inherited predicate `HasThurstonAtlas g
.hyperbolic`.

No completeness, finite volume, connectedness, or nonemptiness is assumed.
On the empty manifold the pointwise assertion is vacuous. The output is local
model charts; it does not supply a global developing map, a deck group, an
explicit quotient presentation, or a selected cusp decomposition.

<a id="ha-1-4"></a>

### HA-1.4. Complete finite-volume geometric structure from curvature −1/4

**Lean:** `DifferentialGeometry.Geometry.Hyperbolic.finiteVolumeGeometricStructure`.
**Status:** explicit construction, admission-dependent through HA-1.3.
Source: `Geometry/Hyperbolic/ModelAtlas.lean`, line 23.

On a Hausdorff, sigma compact smooth 3-manifold \(M\), assume \(g\) is
smooth, complete, finite volume, and has constant sectional curvature
\(-1/4\). The construction returns a `GeometricStructure` on the **same
whole carrier \(M\)**, having:

- model label `hyperbolic`;
- metric \(\widehat g=\tfrac14g\);
- completeness of \(\widehat g\);
- a hyperbolic model atlas for \(\widehat g\);
- finite total volume for \(\widehat g\).

The scaling is deliberate: \(\sec_{\frac14g}=4\sec_g=-1\), and in
dimension three volumes scale by \((1/4)^{3/2}=1/8\). Completeness and volume
scaling use existing proved lemmas; the atlas uses HA-1.3. There is no
connectedness assumption. The returned metric is **not literally the input
metric**, and this construction does not assert that a truncated cusp core
with its restricted original metric is complete.

**Companion declaration:**
`DifferentialGeometry.Geometry.Hyperbolic.finiteVolumeGeometricStructure_model`,
line 42, says exactly that the model label of this construction is
`hyperbolic`. Its proof is `rfl`; the recorded full declaration closure still
contains the admitted atlas theorem through the construction. It adds no
new geometric content.

<a id="ha-2"></a>

## HA-2. The real-variable area contradiction

<a id="ha-2-1"></a>

### HA-2.1. A strict local smooth upper barrier

**Lean:** `DifferentialGeometry.Analysis.hasLocalSmoothUpperBarrier`.
**Status:** definition. Source: `Analysis/ODE/AreaUpperBarrier.lean`, line 13.

Given \(A:\mathbb R\to\mathbb R\), a set \(S\subseteq\mathbb R\), and real
numbers \(t,b\), this means that there are an open set \(U\subseteq\mathbb R\)
and a function \(F:\mathbb R\to\mathbb R\) such that:
\[
 t\in U,\qquad F\in C^\infty(U),\qquad F(t)=A(t),
 \qquad A(s)\le F(s)\ (s\in U\cap S),\qquad F'(t)<b.
\]
\(F\) is only required smooth on \(U\), despite being a function defined
on all of \(\mathbb R\). The bound on its derivative is **strict**, and is
required only at the contact time. The area function \(A\) is not assumed
differentiable. The definition alone does not even require \(t\in S\);
the consumers below impose it.

When \(S=[T,\infty)\), the neighborhood \(U\) is open in \(\mathbb R\).
Domination at \(t=T\) is required only to the right, whereas at any
\(t>T\), including a surgery time in an application, it is required on
both sides sufficiently near the contact.

<a id="ha-2-2"></a>

### HA-2.2. The general shifted contradiction

**Lean:** `DifferentialGeometry.Analysis.not_nonnegative_area_upper_barriers_shift`.
**Status:** admitted. Source: `Analysis/ODE/AreaUpperBarrier.lean`, line 18.

Let \(A:\mathbb R\to\mathbb R\), and let \(T,c,D\in\mathbb R\) satisfy
\[
 T+c>0,\qquad 0<D<2\pi.
\]
Assume \(A\) is continuous on \([T,\infty)\), is nonnegative there, and
at **every** \(t\ge T\) has a local smooth upper barrier with
\[
 F'(t)<\frac{3A(t)}{4(t+c)}-2\pi+D.
\]
Then these assumptions imply a contradiction. Neither \(T\) nor \(c\)
separately needs to be positive. The condition \(T+c>0\) makes every
denominator on the half-line positive. There is no boundedness assumption
on \(A\), no uniform contact-neighborhood radius, and no differentiability
assumption on \(A\).

The intended elementary argument uses \((t+c)^{-3/4}A(t)\) and the divergent
integral of \((t+c)^{-3/4}\). This is an explanation of the admitted
statement, **not a claim that this proof has been formalized**. A finite time
interval, barriers only at regular flow times, or continuity only between
surgeries would not satisfy the statement.

<a id="ha-2-3"></a>

### HA-2.3. The three written specializations

Each row is a separate authored declaration in the same file, proved from
HA-2.2 and therefore admission-dependent.

| Lean name after `DifferentialGeometry.Analysis.` | Exact specialization | Line |
|---|---|---:|
| `not_nonnegative_area_upper_barriers` | Set \(c=1/4\); require \(T>-1/4\), \(0<D<2\pi\), continuity and nonnegativity on the whole half-line, and the bound \(3A/[4(t+1/4)]-2\pi+D\). | 28 |
| `not_nonnegative_area_upper_barriers_pi_shift` | Set \(D=\pi\); require \(T+c>0\), continuity and nonnegativity on the half-line, and the bound \(3A/[4(t+c)]-\pi\). | 39 |
| `not_nonnegative_area_upper_barriers_pi` | Set \(c=1/4,D=\pi\); require the stronger endpoint condition \(T\ge0\), continuity and nonnegativity, and the bound \(3A/[4(t+1/4)]-\pi\). | 52 |

All three conclude `False`, meaning their complete collections of hypotheses
cannot occur. None is a theorem producing barriers for a Ricci flow.

<a id="ha-3"></a>

## HA-3. What the exterior disk area actually means

<a id="ha-3-1"></a>

### HA-3.1. The competitor class

**Lean:** `DifferentialGeometry.Geometry.MinimalSurface.isExteriorSpanningDisk`.
**Status:** definition. Source: `Geometry/MinimalSurface/ExteriorDiskArea.lean`,
line 15.

Fix a subset \(W\subseteq M\), a continuous loop
\(\gamma:\mathbb R/\mathbb Z\to M\), and a continuous map
\(u:\overline{\mathbb D}\to M\). It is an admissible exterior spanning disk
precisely when all the following hold:

1. \(u(e^{2\pi i\theta})=\gamma(\theta)\) for every \(\theta\).
2. \(\gamma(\mathbb R/\mathbb Z)\subseteq\operatorname{frontier}(W)\).
3. \(u\) is a topological embedding.
4. \(u(\overline{\mathbb D})\subseteq W\).
5. \(u(\mathbb D)\subseteq\operatorname{interior}(W)\).
6. There exists a function \(U:\mathbb C\to M\), equal to \(u\) on
   \(\overline{\mathbb D}\), that is smooth on an open neighborhood of the
   closed disk, and whose differential is injective at every point of the
   closed disk.

Thus the competitors are smoothly immersed up to and across their parameter
boundary, and topologically embedded. No branch point is allowed, including
at the boundary. The extension need not be smooth outside the specified
neighborhood or have image in \(W\) outside the closed disk.

There is **no metric in this predicate**. In particular it does not mean
minimal, stable, conformal, least area, or orthogonal to the frontier. It
does not require \(W\) to be closed, compact, connected, a submanifold, or
mean convex, nor identify \(W\) as the complement of any particular
hyperbolic core. The word “exterior” is a name for this precisely specified
side condition. For an open \(W\), the boundary requirement and
\(u(\overline{\mathbb D})\subseteq W\) usually make the class empty;
actual applications intend a compact exterior including its boundary.

The elaborated predicate requires just topology and charts on \(M\); it
does not retain the surrounding file's unused smooth-manifold instance.
Its use with the area below does require the smooth metric/manifold data.

<a id="ha-3-2"></a>

### HA-3.2. The infimum and the meaning of “area”

**Lean:** `DifferentialGeometry.Geometry.MinimalSurface.leastExteriorDiskArea`.
**Status:** definition. Source: `Geometry/MinimalSurface/ExteriorDiskArea.lean`,
line 22.

For a smooth metric \(g\), define
\[
 a(g,W,\gamma)=\inf\{\operatorname{Area}_g(u):
       u\text{ satisfies HA-3.1}\}\in\mathbb R.
\]
This is a **real-valued infimum**, not an extended-real infimum. The inherited
`riemannianDiskArea` is the integral over the Euclidean closed unit disk of
the ordinary two-dimensional metric Jacobian:
\[
 \int_{\overline{\mathbb D}}
 \sqrt{g(U_x,U_x)g(U_y,U_y)-g(U_x,U_y)^2}\,dx\,dy.
\]
Formally the library first extends a continuous disk map to \(\mathbb C\)
using the radial metric projection onto the closed disk. Its derivative at
the circle need not be the derivative of a smooth extension. This causes no
area discrepancy: the circle has measure zero, and the inherited theorem
`riemannianDiskArea_eq_of_extension` proves equality with the displayed
integral for any agreeing extension. For the admitted competitor class, the
smooth extension on a neighborhood of the compact disk gives an integrable
Jacobian by the inherited compact integrability theorem. Thus these
competitors have the ordinary finite Riemannian area; the integral's totalized
value on nonintegrable arbitrary maps is not being used to manufacture
competitor areas.

The real infimum of the empty set is **zero in Lean**. Therefore
\(a(g,W,\gamma)\ge0\) by itself does not assert that a disk exists. Attainment
must be supplied separately. No strict positivity theorem, minimality theorem,
stability theorem, or Meeks–Yau theorem is asserted by this definition.

Two authored helpers are proved with no skeleton admission:

- `leastExteriorDiskArea_nonneg` (line 27): for every \(g,W,\gamma\),
  \(0\le a(g,W,\gamma)\), including the empty-class case.
- `leastExteriorDiskArea_le` (line 33): if a specified \(u\) is admissible,
  \(a(g,W,\gamma)\le\operatorname{Area}_g(u)\). The proof explicitly
  bounds all competitor areas below by zero before applying the infimum rule.

<a id="ha-3-3"></a>

### HA-3.3. Time-varying carriers and late-only loops

**Lean:** `DifferentialGeometry.Geometry.MinimalSurface.exteriorDiskAreaOn`.
**Status:** definition. Source: `Geometry/MinimalSurface/ExteriorDiskArea.lean`,
line 43.

One may specify a different smooth 3-manifold \(M_t\) for each real \(t\),
a smooth metric \(g_t\) on each \(M_t\), a subset \(W_t\subseteq M_t\), a
real starting time \(T\), and a continuous loop \(\gamma_t\) **only for
\(t\ge T\)**. Set
\[
 A(t)=\begin{cases}
       a(g_t,W_t,\gamma_t),&t\ge T,\\
       0,&t<T.
      \end{cases}
\]
There is no topology on the total family \(\coprod_tM_t\), no continuity of
\(g_t,W_t,\gamma_t\), no Ricci equation, and no surgery assumption in this
definition. The manifolds are allowed to change their underlying types.
The loop parameter depending on a proof of \(T\le t\) is Lean bookkeeping;
proof irrelevance makes it a single loop for each permitted time.

**Companion theorem:** `exteriorDiskAreaOn_nonneg` (line 52), proved with no
skeleton admission, says \(A(t)\ge0\) for every real \(t\), including
\(t<T\). No continuity from the left at \(T\) is asserted. No loop is
required on an earlier empty carrier.

<a id="ha-3-4"></a>

### HA-3.4. Continuity from two-direction comparisons of minimizers

**Lean:**
`DifferentialGeometry.Geometry.MinimalSurface.continuousOn_leastExteriorDiskArea_of_local_disk_comparisons`.
**Status:** admitted. Source: `Geometry/MinimalSurface/ExteriorDiskArea.lean`,
line 65.

Use exactly the time-dependent data of HA-3.3. Assume:

1. **Attainment at every late time.** For every \(t\ge T\), an admissible
   \(u_t\) exists with \(\operatorname{Area}_{g_t}(u_t)=A(t)\).
2. **Local two-direction comparison.** For every \(t_0\ge T\) and every
   \(\epsilon>0\), there is \(\delta>0\) such that, whenever
   \(t\ge T\) and \(|t-t_0|<\delta\), both statements hold:
   - For **every** attaining admissible disk \(u\) at \(t_0\), an
     admissible disk \(v\) at \(t\) exists with
     \(\operatorname{Area}_{g_t}(v)\le e^\epsilon
       \operatorname{Area}_{g_{t_0}}(u)\).
   - For **every** attaining admissible disk \(v\) at \(t\), an
     admissible disk \(u\) at \(t_0\) exists with
     \(\operatorname{Area}_{g_{t_0}}(u)\le e^\epsilon
       \operatorname{Area}_{g_t}(v)\).

Then \(A\) is continuous on \([T,\infty)\).

The comparison disks need not themselves attain the infimum. The radius
\(\delta\) may depend on \(t_0,\epsilon\), but works for all nearby
times and all minimizing disks in the two quantifiers. The statement does
not require comparison maps between whole manifolds, or a continuously
chosen minimizer. It does not supply the two comparisons from surgery
geometry; it assumes them. The blueprint uses \(e^{2\epsilon}\), whereas
the Lean statement uses \(e^\epsilon\); universal quantification over
all positive \(\epsilon\) makes these formulations equivalent by
renaming \(\epsilon/2\). No uniformity is lost in that renaming.

The direct numerical consequence is
\(e^{-\epsilon}A(t_0)\le A(t)\le e^\epsilon A(t_0)\).
This handles \(A(t_0)=0\) as well, without taking a logarithm of zero.
The theorem's assertion is mathematically elementary once its strong
comparison premises are available; its Lean proof is still admitted.

<a id="ha-4"></a>

## HA-4. What is, and is not, proved about torus injectivity

<a id="ha-4-1"></a>

### HA-4.1. A finite time-dependent family of continuous torus maps

**Lean:**
`DifferentialGeometry.Geometry.RicciFlow.cusp_injective_of_exterior_area_barriers`.
**Status:** written proof, admission-dependent through HA-2.2.
Source: `Geometry/Flow/RicciFlow/LongTime/CuspIncompressibility.lean`, line 15.

Let \(M_t,g_t\) be any family as in HA-3.3, let \(n\in\mathbb N\), and
let \(T_0\in\mathbb R\). For each \(t\ge T_0\) and each
\(i\in\{0,\ldots,n-1\}\), suppose a continuous map
\(f_{t,i}:T^2\to M_t\) is given. Assume the following implication for
**each** \(t\ge T_0\), each \(i\), and each basepoint \(x\in T^2\):

> If \((f_{t,i})_*:\pi_1(T^2,x)\to\pi_1(M_t,f_{t,i}(x))\) is not
> injective, there exist \(T\ge0\) with \(T\ge t\), subsets \(W_s\),
> and loops \(\gamma_s\) for all \(s\ge T\), such that the associated
> actual disk-area function \(A\) of HA-3.3 has an admissible attaining
> disk at every \(s\ge T\), is continuous on \([T,\infty)\), and has
> at every \(s\ge T\) a strict local smooth upper barrier with derivative
> less than \(3A(s)/[4(s+1/4)]-\pi\).

Then all the displayed homomorphisms \((f_{t,i})_*\) are injective.

The proof takes a hypothetical noninjectivity, obtains the promised area
function, proves its nonnegativity from the definition, and applies HA-2.3.
It does not use the attainment conjunct; attainment is retained as a
geometric requirement of the premise. Nor does the contradiction need
\(t\le T\) once the premise has supplied a half-line with \(T\ge0\).

**Exact scope:** the maps \(f_{t,i}\) need not be smooth, embedded,
time-continuous, or actual cusp maps. No Ricci flow is assumed. There is no
condition in this theorem relating \(\gamma_s\) to a particular primitive
kernel element of \(f_{t,i}\), or \(W_s\) to its exterior. Such relations
must be used inside the proof that produces the displayed implication. If
\(n=0\), both that implication and the conclusion are vacuous.

<a id="ha-4-2"></a>

### HA-4.2. Moving the torus along a product collar

**Lean:** `DifferentialGeometry.Geometry.RicciFlow.cusp_slice_injective_iff`.
**Status:** written proof, no skeleton admission.
Source: `Geometry/Flow/RicciFlow/LongTime/CuspIncompressibility.lean`, line 43.

For any topological space \(M\), any continuous
\(c:T^2\times\mathbb R\to M\), any \(r,s\in\mathbb R\), and any
\(x\in T^2\), the map \(y\mapsto c(y,r)\) is injective on fundamental
groups at \(x\) if and only if \(y\mapsto c(y,s)\) is.

The proof uses the actual product homotopy and the existing theorem that
homotopic maps have equivalent injectivity properties, with the induced
basepoint track. No metric or smoothness is involved; \(c\) need not be
an embedding. It is not an inference from injection into an abstract
hyperbolic model to injection into a different ambient manifold.

<a id="ha-4-3"></a>

### HA-4.3. Injectivity for the actual reconstruction seams

**Lean:** `DifferentialGeometry.Geometry.RicciFlow.incompressible_of_area_barriers`.
**Status:** written proof, admission-dependent through HA-2.2.
Source: `Geometry/Flow/RicciFlow/LongTime/CuspIncompressibility.lean`, line 51.

Let \(C\) be the existing compact carrier, \(G\) its actual paired-torus
gluing data, \(S\) a smooth assembly of that gluing, and
\(r:S.\mathrm{assembled}\to P\) an orientation-preserving smooth
reconstruction onto a connected closed oriented 3-manifold \(P\).
Despite the code name `torusInPrime`, this type **does not assume that
\(P\) is prime**. For every gluing label \(i\), the relevant map is
the actual quotient seam followed by \(r\), denoted \(j_i:T^2\to P\).

Assume for every \(i\) and every basepoint \(x\), failure of injectivity
of \((j_i)_*\) produces real data \(T\ge0\) and
\(A:\mathbb R\to\mathbb R\) which are continuous and nonnegative
on \([T,\infty)\), with a strict smooth local upper barrier at each
\(t\ge T\) having derivative less than
\(3A(t)/[4(t+1/4)]-\pi\). Then `S.Incompressible r` holds: every
actual seam map is injective on fundamental groups at every basepoint.

This adapter does not itself require that \(A\) be an area, or that it
be attached to a flow. It is a numerical contradiction consumer whose
conclusion is precisely the existing reconstruction's injectivity predicate.

**Shifted companion:**
`DifferentialGeometry.Geometry.RicciFlow.incompressible_of_shifted_area_barriers`,
line 67, has exactly the same reconstruction data and conclusion. Its
noninjectivity premise produces \(T\ge0\), \(c>0\), and \(A\), with
the bound \(3A(t)/[4(t+c)]-\pi\). The proof derives \(T+c>0\) and
uses HA-2.3. The shift can depend on the failed seam and basepoint. This
theorem also has a written admission-dependent proof.

<a id="ha-4-4"></a>

### HA-4.4. Approval issue: the consumers do not expose the producer's substance

After granting the area contradiction, each “noninjectivity produces an
impossible area function” premise above is logically equivalent to the
corresponding injectivity conclusion: the forward implication is the written
proof, while if injectivity already holds, the premise follows vacuously.
This does **not** make the conditional proof false. It does mean these
consumers by themselves provide almost no independent check of the
geometric proof of incompressibility.

The broader selected-flow producer in `LateDecomposition.lean` uses the actual
same-flow disk area defined below. That rules out an unrelated numerical
function, but does not yet expose, as separately checked fields, the fixed
primitive meridian, its preservation through surgery, actual persistent cusp
embeddings, mean-convex exterior geometry, or the common unchanged carrier
and boundary-moving isotopy. Mathematicians should review that producer as a
large remaining theorem, not treat the short `...of_area_barriers` proofs as
having formalized Meeks–Yau or surgery avoidance.

<a id="ha-5"></a>

## HA-5. The same-flow physical area and the event-time convention

All seven declarations in this section are in
`Geometry/Flow/RicciFlow/LongTime/ExteriorDiskFlow.lean`. None has `sorryAx`
in its recorded dependency closure. They take an existing
`ObservationTower P g`, a compatible collection of actual finite surgery
histories with specified initial carrier \(P\) and initial metric \(g\).
This section does not construct such a tower or strengthen its analytic
control.

<a id="ha-5-1"></a>

### HA-5.1. The carrier at every real time

**Lean:** `GC.LongTime.postStage`. **Status:** definition. Line 18.

For \(t\in\mathbb R\), put \(\tau=\max\{t,0\}\), restrict the tower to
its observation through \(\tau\), and take that observation's last stage.
This defines \(M_t^{\mathrm{post}}\), including its existing orientation
and manifold structure. For \(t\ge0\), this is the actual carrier at time
\(t\). At an exact surgery time it is the **post-surgery** stage. For
\(t<0\), it is the time-zero stage; this is a totalization convention,
not a backward flow.

This event convention follows from the inherited restriction rule: the active
stage is the largest stage index whose start time is \(\le t\), not
\(<t\). The last stage of the observation is that active stage at the
observation horizon. A stage may be empty.

<a id="ha-5-2"></a>

### HA-5.2. The physical metric on that carrier

**Lean:** `GC.LongTime.postMetric`. **Status:** definition. Line 22.

On `postStage O t`, take the last stage's actual `stageMetric` evaluated at
the same \(\tau=\max\{t,0\}\). At a surgery time this is the post-surgery
output metric. This is the **physical metric**. It is neither
\(t^{-1}g(t)\) nor \((4t)^{-1}g(t)\). No value is divided by zero at
\(t=0\).

<a id="ha-5-3"></a>

### HA-5.3. Agreement with a regular slice

Two separate authored theorems have written proofs without skeleton admissions:

- `GC.LongTime.postStage_regularSlice` (line 26): for any `RegularSlice O`
  with time \(s.time>0\), the carrier `postStage O s.time` equals the
  stage stored by the regular slice.
- `GC.LongTime.postMetric_regularSlice` (line 37): the physical metric
  `postMetric O s.time` is the same metric as `s.metric`, after accounting
  for that equality of the carriers. The Lean conclusion is heterogeneous
  equality because the metric types mention their respective carriers.

These are exact identifications of two descriptions of the same observation,
not a diffeomorphism between different surgery slices or a metric-comparison
estimate across surgery.

<a id="ha-5-4"></a>

### HA-5.4. The actual same-flow area function

**Lean:** `GC.LongTime.exteriorDiskArea`. **Status:** definition. Line 57.

Choose, for every real time, a subset
\(W_t\subseteq M_t^{\mathrm{post}}\), a starting time \(T\in\mathbb R\),
and a loop \(\gamma_t\) in that carrier for every \(t\ge T\). Define
\[
 A_O(t)=\begin{cases}
 a(\mathrm{postMetric}(O,t),W_t,\gamma_t),&t\ge T,\\
 0,&t<T.
 \end{cases}
\]
This is HA-3.3 applied to the actual observation tower. The definition itself
still permits arbitrary \(W_t\) and \(\gamma_t\), imposes no continuity
or persistence on them, and does not require \(T\ge0\). Its intended root
application chooses \(T\) after a positive regular slice, so only actual
nonnegative flow times are used in the area contradiction.

Two authored written helpers, without skeleton admissions, are:

- `GC.LongTime.exteriorDiskArea_nonneg` (line 62): \(A_O(t)\ge0\) for all
  real \(t\).
- `GC.LongTime.exteriorDiskArea_eq` (line 68): if \(t\ge T\),
  \(A_O(t)=a(\mathrm{postMetric}(O,t),W_t,\gamma_t)\), exactly.

They provide no assertion of attainment, positive area, continuity, smooth
upper barriers, or identification of any \(W_t\) with a specified thin
complement. At a surgery contact, the future producer must use the actual
post-surgery infimum and prove the two-sided numerical barrier using a common
unchanged region. These helpers do not assert a global identification of
pre- and post-surgery manifolds.

<a id="ha-6"></a>

## HA-6. Mathematical review findings and decisions needed

This reading found **no concrete counterexample to the four admitted leaf
statements** in these six files. Their principal formulations are compatible
with the corresponding natural-language arguments, subject to the explicit
limitations above. That conclusion is a targeted mathematical review, not
proof verification of admitted claims.

The following distinctions should remain visible when approving the skeleton:

| Point for review | What the code actually does | What remains outside these six files |
|---|---|---|
| Mostow–Prasad | Admits the finite-volume, same-curvature, marked homotopy-class theorem in dimension three. | Its proof, quantitative rigidity, controlled persistent families, and cusp coverage. |
| Hyperbolic geometric metric | Uses \(g/4\) on the same whole carrier when \(\sec g=-1/4\). | A full-interior map from each actual cut piece to the complete hyperbolic carrier. |
| Fixed-boundary disks | Uses embedded, unbranched smooth disks with exactly parametrized boundary, on the specified side. | Actual existence in the chosen exterior; source-to-class comparison; minimality and stability. |
| Empty disk class | Gives real infimum zero, and proves nonnegativity. | Attainment must rule out emptiness wherever geometry is claimed. |
| Continuity through surgery | Admits continuity from explicit forward and backward minimizing-disk comparisons. | Common compact carrier, its two-sided smooth metric, and actual boundary-preserving transports. |
| Area barrier | Requires a strict smooth upper barrier at every time of one entire half-line. | Scalar bound, boundary estimates, first variation, Gauss–Bonnet, and surgery-neck avoidance in the actual flow. |
| Torus injection | Has genuine contradiction consumers for the actual maps supplied to them. | Producer premises currently encapsulate the essential geometric argument. |
| Empty families | Permits zero tori, with vacuous injection obligations; permits empty stages in the tower helpers. | No fictitious loop is required before its threshold; late loops themselves force nonempty carriers where used. |

In particular, there is no new standalone Lean theorem here saying “Meeks–Yau
holds for the actual exterior,” “every least-area disk avoids the surgery
necks,” or “the chosen meridian is preserved through every event.” Those
would be natural future statements when the large root producer is split
into independently assignable tasks. Approving the present statement layer
does not approve a completed proof of those facts.

<a id="ha-7"></a>

## HA-7. Evidence for this translation

Freshly inspected for this report:

- The complete six Lean source files, all 28 authored declarations, and their
  full elaborated signatures and recorded axiom closures in
  `evidence/declarations.json`.
- The inherited definitions `SmoothDiskExtension`, `freeLoop`, `closedDisk`,
  `diskTrace`, `riemannianDiskArea`, `riemannianAreaDensity`, and
  `tangentTwoJacobian`; the existing extension-invariance and compact
  integrability statements for disk area.
- `RiemannianMetricComplete`, `HasThurstonAtlas`, `CoordinateModelAtlas`,
  the hyperbolic `coordinateInner`, and `GeometricStructure`.
- `SmoothAssembly.Reconstruction`, `torusInPrime`, and `Incompressible`;
  `ObservationTower.observe`, `ObservedHistory.activeStage`, and the
  exact-event and observation-horizon rules.
- Blueprint `master207A.tex`, MPR79 lines 15392–15424; IMS02–IMS03 around
  lines 18251–18338; IMS08–IMS09 around lines 18533–18607; IAU02–IAU03
  around lines 18724–18855. These were used to compare the actual predicates,
  not to substitute prose for code.
- Archived `BooksPapers/MSM206.tex`, `MosTowSection`, lines 17115–17166,
  for the Mostow statement and its homotopy-equivalence formulation. Its
  shorthand based-group equation is not copied into the Lean theorem.

The prior source review is `hyperbolic_review.md`, with exact source identities
in `hyperbolic_crosswalk.json`. This report reuses unchanged source/errata
checks only at their documented scope; it does not claim a fresh literature
or errata search. It does not rerun the Lean build. Compilation and the axiom
classification above are read from the final recorded verification of the
pinned commit, supplemented by direct source inspection. The machine-readable
`hyperbolic_area_coverage.json` maps every declaration to the subsection that
translates it.
