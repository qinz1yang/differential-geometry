# ParametricAppCcJetBound

## Role

`app_jet_sq_le` gives the sharp squared one-jet action estimate.
`app_jet_of_bdd` turns a supplied pointwise coefficient-jet envelope into one
`L²` action window. `param_app_jet` obtains that envelope from
`joint_jet_bdd` on a compact parameter slab. Constants are independent of the
parameter, the input tensor, and its spectral or spatial support.

## Frontier

`app_jet_sq_le` was promoted from a private implementation lemma to the public
quantitative producer used by spectral smallness estimates; its statement and
proof body are unchanged.  After the upstream parametric-jet dependency was
repaired and refreshed, this file passed focused verification and the public
declaration was exported for downstream use.

Endpoint theorem: 0% (not stated in this module). Dedicated uniform action
machinery: 100%.
