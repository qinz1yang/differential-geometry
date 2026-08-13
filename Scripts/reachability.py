#!/usr/bin/env python3
import re, sys

files = [
 "DifferentialGeometry/Tensor/Auxiliary/Perm.lean",
 "DifferentialGeometry/Tensor/Auxiliary/Shuffle/Placement.lean",
 "DifferentialGeometry/Tensor/Auxiliary/Shuffle/Decomposition.lean",
 "DifferentialGeometry/Tensor/Alternating/Wedge.lean",
 "DifferentialGeometry/Tensor/Exterior/Defs.lean",
 "DifferentialGeometry/Tensor/Exterior/Basic.lean",
 "DifferentialGeometry/Tensor/Exterior/Pullback.lean",
 "DifferentialGeometry/Tensor/Exterior/Cochain.lean",
 "DifferentialGeometry/Tensor/Exterior/Leibniz.lean",
 "DifferentialGeometry/Tensor/Exterior/ModelDifferentialForm.lean",
 "DifferentialGeometry/Analysis/Calculus/AnalyticTransfer.lean",
 "DifferentialGeometry/Tensor/Alternating/Comp.lean",
]
decl_pat = re.compile(r'^(private\s+)?(?:noncomputable\s+)?(?:def|theorem|lemma|structure|class|abbrev|instance)\s+([A-Za-z_][A-Za-z0-9_\']*)')
problems = []
for f in files:
    src = open(f).read()
    lines = src.splitlines()
    decls = []
    for i, line in enumerate(lines):
        s = line.strip()
        m = decl_pat.match(s)
        if m:
            if decls: decls[-1][3] = i
            decls.append([m.group(2), (m.group(1) or '').strip() == 'private', i, i + 1])
    if decls: decls[-1][3] = len(lines)
    # transitive reachability: public declarations are roots; a private declaration is
    # reachable if its name appears in a public block or in a reachable private block.
    reachable = set()
    changed = True
    while changed:
        changed = False
        for name, is_private, start, end in decls:
            if is_private and name in reachable:
                continue
            if is_private and name in reachable:
                continue
            if not is_private:
                if name not in reachable:
                    reachable.add(name)
                    changed = True
                continue
            # private: reachable if any reachable declaration's block mentions it
            for name2, is_private2, s2, e2 in decls:
                if name2 == name:
                    continue
                if is_private2 and name2 not in reachable:
                    continue
                if not is_private2 and name2 not in reachable:
                    continue
                block = "\n".join(lines[s2:e2])
                if name in block:
                    if name not in reachable:
                        reachable.add(name)
                        changed = True
                    break
    for name, is_private, start, end in decls:
        if is_private and name not in reachable:
            problems.append((f, name, start + 1))
if problems:
    for f, n, ln in problems:
        print(f"UNREACHABLE PRIVATE: {f}:{ln}: {n}")
    print(f"FAIL: {len(problems)} unreachable private declarations")
    sys.exit(1)
print("private reachability OK (source-based)")
