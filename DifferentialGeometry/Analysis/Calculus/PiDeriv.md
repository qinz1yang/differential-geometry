# PiDeriv

## Status

`iteratedFDeriv_pi` is the canonical finite-Pi analogue of
`iteratedFDeriv_prodMk`. It was moved out of the final Step-B1 producer layer
so localized compactness and atom convergence can reuse the same generic
calculus theorem.

Focused verification and the targeted module refresh passed. The former
high-level duplicate was removed and all known callers now use this API.
