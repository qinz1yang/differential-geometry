# Verification receipts

The linear THIRD focused check and named lint build succeeded on source SHA
`2B0C1C74D3F41EB094B5531DA5C0138A9B08E0CC20A2301BD01B1641481F70EB`.
The public endpoint has not received its separate axiom audit.
FIRST/SECOND logs preserve the prior failed versions; they do not describe the final source.

The historical `codex-late-three-*` receipts cover Homology and two other B-line
leaves together. Their Homology source SHA was
`4287489181806C2A17C49402B1C4DCCAC3CAC8ACE0BADD4E3A71FC55CAD6D998`.
Its historical inventory had 80 declarations: 67 standard-only, 13 with
recorded direct/transitive sorryAx. They are not a fresh audit of the entire snapshot.

`repl/001` is the actual pre-target environment request/response; setup took
30.780 seconds with no errors. It did not import Homology or include the target.
`repl/002` is the earlier candidate request/response, taking 5.968 seconds with
11 errors. The source-written final revision SHA `9DA2D099740896AACB9EDB57C32AEA2946ED9EF4C8B7472ADAC3207ABFB3C39F`
is separate and was NEVER checked. Do not apply the earlier error locations to
it mechanically or treat the failed response environment as reusable.
No final corrected-success test or intentional wrong-proof control was run.
The root host was closed normally at the user's stop request and released its elaboration lock.

Raw request text can be replayed only after checking imports, prefix, artifacts,
toolchain and ownership. Snapshot hashes do not make an old runtime environment valid.
No Lean/Lake/REPL process was started for this package.
