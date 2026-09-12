# TerminalRegularity

Claude's D3 definition, committed in ed1a6550a: TerminalJetContinuous is pointwise
left continuity of every evaluated spatial curvature jet at the terminal time;
IsAncientKappaSolutionTerminal pairs it with the existing ancient predicate.
It is not uniform convergence on space-time compact sets and does not itself
prove a terminal evolution equation.

The predicate and its public semantics are unchanged. TerminalCurvatureJets now
proves terminalJetContinuous_of_ancientFlow and
isAncientKappaSolutionTerminal_of_ancient from the existing native flow data.
Thus WindowedModelWitness.model_ancient and AncientExtension.ancient can supply
the terminal predicate directly without stronger model fields. The actual
TerminalBackwardSlab consumer uses the same proof, with no hjet argument.

The current source changes only the explanatory header: a nonregular endpoint
does not mean IsSolutionOn has no carrier regularity. Focused101 EMPTY (21.40s),
named101 passed (47.86s), and the fresh grouped helper audit101 passed (23.15s).
All three declarations here and all six actual producers in TerminalCurvatureJets
use standard axioms only. The four remaining slab interfaces are still open.
Current hashes/receipts: E:/lean-tools/chapter25-terminal-local-20260909/
curvature-jets-completion.json. Claims remain in WORKING_STATUS/script status.
