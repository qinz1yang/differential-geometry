# Exact tangent nets and direction dimension upper bounds

Six public theorems in three new leaves give quantitative nets on the SAME actual tangent and a one-power covering/dimension upper bound for its actual completed directions. The original ambient and intrinsic geometric headlines retain q and allow every natural dimension upper bound, including the separately proved n0 case.

## Every ball in the same actual tangent

`Comparison.TangentPolynomialNets` takes the original complete metric source, global arbitrarily short continuous curves, open U with dimH(U)<=n, original local comparison parameter1 on U, and SAME q in U. Parameter1 is the curvature -1 convention. Set K(n)=4*pairedChartDistortion(n)^2*sqrt(n)*sinh2. For EVERY B>0 and delta in(0,1], it returns an internal strict delta-net of the closed B-ball of literal TangentCone(q), of cardinality at most

`(2+4*(K(n)*(B+1)))^n * delta^(-n)`.

The intrinsic theorem has the corresponding original local comparison on B(p,8R), R>0, and applies at EVERY q in that open ball. No half-ball condition, source properness, complete intrinsic open ball, assumed target model or target-covering premise is added.

At n>=1 the exact original normalized nets at radius t_i*(B+1), t_i=1/(i+1), and relative error (delta/4)/(B+1) transfer through the accepted actual full tangent blowup. In the rescaled source these are radius B+1, absolute delta/4 nets. The public CoveringLimit theorem transfers them to the SAME actual tangent with the displayed coefficient and strict internal coverage. At n0 the original local dimH bound and continuous paths force the source subsingleton, actual directions empty and tangent cone the singleton tip; the exact net has cardinality1.

## Generic annular packing

`Metric.ConeAngularCovering` takes any metric Y of diameter at most pi, n>=1, C>0 and uniform cone tip-ball5 epsilon-nets of cardinality at most C*epsilon^(-n), for every epsilon in(0,1]. Centers need not be internal. Its first theorem returns global strict angular delta-nets with bound

`3^n*C*delta^(-(n-1))`.

Its second theorem gives actual `dimH(Y)<=n-1`. No CBB, geodesic, completeness, properness, compactness, splitting or Nonempty premise is required. Empty bases are valid and no direction is chosen there.

The accepted separated Euclidean1 grid has norm<=1 and at least delta^(-1) points. Its attached grid subtype defines actual positive radii3+v(0) in[2,4]. The actual cone product family is injective and delta-separated: radial separation uses the cone radius inequality; angular separation uses4*distY<=pi*distCone at radius>=2 and pi<=4. The radius5 delta/3 cone net bounds this product cardinality. The finite packing-to-net theorem preserves the exact coefficient without a rounding factor; the accepted polynomial-net dimension theorem supplies the Hausdorff conclusion. The proof reuses the EuclideanFactorCovering grid argument, without falsely treating the cone as an exact product.

## Original direction-space upper bounds

`Comparison.DirectionDimension` combines these leaves on the SAME actual TangentCone(q), with B5 and the existing actual direction diameter bound. Both original ambient/intrinsic headlines return strict global nets in SpaceOfDirections(q) with exact coefficient

`3^n*(2+4*(K(n)*6))^n`

and power delta^(-(n-1)), together with actual dimH(SpaceOfDirections(q))<=n-1. Intrinsic q remains arbitrary in open B(p,8R). For n0 the proof separately establishes actual empty directions and an empty net. It does not apply the generic n>=1 theorem at zero or assert the invalid empty-direction dimension-plus-one formula.

## Sources and scope

KLP archived v1 July14 2026, SHA256 `3dc0a166ec88b1c7e50aeebd9924f747ece6fb1957c7b31dcbe17a90a9e61d67`: Definition1.2 printed20/PDF22; cone/tangent3.2-3.3 printed36-37/PDF38-39;3.4 semisolution129-130/PDF131-132;6.18 full proof and Exercise6.20(b) printed69/PDF71; complete6.20 semisolution138/PDF140. Actual readings and retained source checks are distinguished in the frozen author/peer records. The source's LINEAR-dimension equalities use6.18 and are stronger than these Hausdorff upper bounds. This quantitative transfer/annular argument is recorded as an alternative route for the stated upper bound, not an implementation of all those equalities.

The accepted factor-dimension source record is reused for its expanded AC45 packing proof and retained BBI correction/independent Mathlib Hausdorff facts. Source versions and errata qualifications remain; no new remote errata search or error-free-source claim is made. Mathlib stays pinned at `c55e6e786f49471c72fbddbec5415808896aec1e`.

A dimension upper bound does not produce a third direction, dimension equality, local dimension homogeneity, angular CBB1, nearby Euclidean tangents or automatic angular obstruction. Blueprint207 and migration interfaces remain unchanged; Chapters3-4 are not declared complete.

## Tests and acceptance scope

Nine new regressions retain exact quantitative outputs. Tangent-net applications cover real q14 outside the half-ball with at least two returned centers, unbounded original U with B37/delta1/100, and original singleton n0 with an exact singleton-tip net. Generic tests independently build finite-base radial cone nets for Empty, PUnit and actual {0,1} in the real line; they force empty, nonempty and at least two angular centers and prove actual dimension0. Source direction applications prove actual real-direction dimension0 with at least two centers at every delta<=1, actual empty singleton directions, and translated-plane direction dimension exactly1 with at least three centers at delta1/2. The plane lower bound uses a genuine nonconstant angular segment, not an assumed dimension formula.

Nine older real/plane fixture bodies appear once and are not counted as new tests. Fifteen explicit reports cover six production theorems and nine new tests. Temporary source elaboration, canonical leaf checks, independent full proof reads, the shared axiom gate and the separate blueprint audit remain distinct.

The 451-module shared gate checks 2,155 owned declarations in 3,289 jobs. Its observed increment is 14 owned declarations, comprising 6 declared public theorems and 8 compiler-generated declarations. Nine new concrete regressions and fifteen canonical-import standard-axiom reports pass, with silent selected lint. The separate blueprint static audit remains pending; no static pass is claimed. Its recorded status and latest completed failure are retained in the receipt. Generated increments are calculated from the actual gate relative to verified milestone127 minus six parsed public theorems. Static audit status may remain separately pending and is never relabeled as passed without completed success evidence. Earlier mathematical leaves remain unchanged.
