# Team Lean development

Read `docs/geometrization/README.md` and `TEAM_PLAN.md` before team work. Use the
task's agreed interface commit, source record and file claim. The human task
instruction determines the authorized scope; the schedule is not permission to
implement all future packets autonomously.

- Reuse the actual `DifferentialGeometry` foundation. Keep accepted PC sources
  and pins unchanged unless a task explicitly includes their migration.
- New code uses `autoImplicit false`, topic-specific modules and existing actual
  carrier/metric/history types. Preserve `GC.*` names when moving baseline code.
- Do not add output-valued assumptions to make a producer appear complete.
  Identify remaining hypotheses explicitly; a successful build does not certify
  that a statement matches the geometrization endpoint.
- Check exact source hypotheses, regularity, normalization, boundaries and
  uniformity before changing mathematical contracts. Record source versions and
  theorem/proof locators; reuse unchanged documented source checks.
- Do not edit another task's claimed files or the frozen checkpoint. Request
  shared API/import/pin changes in the integration patch rather than silently
  modifying interfaces under other workers.
- No placeholders, custom mathematical axioms, unsafe proof declarations or
  skipped kernel checking in DifferentialGeometry. Keep experiments outside it.
- Build the changed module first; before integration run
  `python3 tools/gc/check.py`. Include a real downstream consumer and distinguish
  source review, Lean elaboration, axiom checks and mathematical completeness.
- Do not push private sources or caches to public destinations. Ziyang's private
  development repository is the agreed destination; feature branches precede
  integration. Do not merge or contact teammates without task authorization.
