# Chart-local Picard integral identities

## Right-ray FTC adapter

`ode_right_ftc` is the minimal FTC normal form for ODE data whose derivative at
time `t` is recorded within `Ici t`.  It restricts that derivative to `Ioi t`
and applies the existing one-sided interval-integral theorem.  This avoids
strengthening a consumer to the incompatible `Ici 0` derivative hypothesis.

Focused verification passes without warnings or `sorry`.  The adapter and its
dedicated machinery are theorem-level 100%; it is a generic ODE producer and
does not itself prove any conjugate-heat or noncollapsing endpoint.
