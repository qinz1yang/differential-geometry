# Locally Lipschitz maximal-regularity existence

## 2026-07-13 dependency split

The structural per-mode Duhamel coefficient identities were moved to the lower
`SolutionFieldLink.lean` module, which imports only `SolutionSpace`.  This file
now imports that module and retains the genuinely higher local-Lipschitz,
cross-scale, and recentered existence machinery.  No public theorem statement
changed.

Focused verification passes.  The split prevents the non-autonomous linear
consumer from importing the higher local-Lipschitz layer merely to identify its
Duhamel companion fields with `timeH1.toFun`.
