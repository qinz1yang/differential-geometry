# HeatKernelSup

## Proved source boundary

`HeatKernelSup.lean` adds the genuine endpoint estimates missing from the
finite-`p` file:

- pointwise convolution of an `L¹` scalar kernel with bounded continuous
  Banach-valued data;
- Bochner integrability of that convolution and Young's
  `L¹ * L∞ → L∞` estimate;
- exact linearity under subtraction, needed to estimate differences of
  Duhamel maps without changing representatives;
- positive-time Euclidean heat contraction in the spatial supremum norm;
- first- and second-spatial-derivative heat bounds with the precise
  `t^(-1/2)` and `t^(-1)` scaling already established in
  `HeatKernelLp.lean`.

The construction is pointwise on purpose.  An arbitrary bounded continuous
function on a noncompact Euclidean space need not be uniformly continuous,
so its translation orbit need not be continuous in the global supremum norm.
The file does not assume that false statement.

## Ricci--DeTurck use

This is the linear `C0` value brick for the regularizing-flow uniqueness route.
It does not close the rough nonlinear map.  The faithful Koch--Lamm space uses
local space-time `L²` and late `L^(n+4)` gradient arms; a stronger
`sqrt(t)‖∇h‖∞` carrier was rejected because the required second-derivative
heat singular integral is not bounded on arbitrary `L∞` data.  Treating the
nonlinearity as an abstract lower-order Lipschitz map would likewise not prove
the required Ricci--DeTurck result.

## Verification

The source contains no `sorry`, `admit`, axiom, opaque declaration, or
heartbeat override, and the complete file passes its focused Lean check
without local warnings.  The machinery stated here is 100% proved and
verified; `ricci_flow_forward_unique` remains 0% until the full rough
regularizing-flow and de-gauging chain is assembled.
