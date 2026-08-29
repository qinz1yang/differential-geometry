# TimeQuadraticRegular

## Scope

This generic time-Sobolev module is the post-weak-Euler momentum-regularity brick for the
Tonelli/direct-method chain.  It stays independent of manifolds and Ricci flow.

## Route

For a compactly supported smooth scalar test `φ` and a fixed vector `x`, realize `φ • x` as a
zero-endpoint `timeH1` variation.  The weak Euler identity then identifies the distributional
derivative of `2 A u'` with `F`.  The finite-dimensional weak fundamental theorem supplies a
constant-plus-primitive representative.

## Status

`mom_primitive` and its continuous-representative enhancement `mom_rep_cont` are implemented
without `sorry`.  They derive the distributional momentum equation from the actual zero-endpoint
`timeH1` Euler identity rather than taking that equation back as a premise.

## Project accounting

- `mom_primitive` / `mom_rep_cont`: 100%, focused verification passed.
- Generic post-weak-Euler regularity machinery: approximately 60% after this brick, because
  inversion of the momentum law and corner matching remain separate.
- Perelman `redVolume_anti`: 0%; this generic theorem is infrastructure only.
