# AkMFold.lean — the Claim-1 m-fold engine (component route i)

SIGN CONVENTION (2026-06-10, authoritative for the wiring phase, see
`Claim1Wiring.md` §1b): `A_k := connectionDifferenceTensorAt (LC g_k) (LC gRef)
= ∇_k − ∇_ref` (POSITIVE two-term expansion; lowered-Koszul coefficients
`(+½,+½,−½)`).  Older notes here and in `RicBoundProof.md` write `A_k = ∇−∇_k`
(the flipped orientation) — `claim1` is sign-agnostic (free coefficients), but
new geometric lemmas must use the `∇_k − ∇_ref` orientation.

Spec/route: `RicBoundProof.md` (PROGRESS 9–10).  Status: **all content sorry-free, in oleans.**

## Contents

1. `iterCovCompU` — field-level UPPER tower (`covDerivStepCompU` analogue of `iterCovComp`;
   per-level `ext` = `frameExtData` of the running field; the `+1` upper slot kept LAST so
   ranks `(r+a)+1` stay defeq across the recursion). `_zero`/`_succ` simp lemmas (rfl).
2. `frameExtData_contrTail` — frameExtData product rule for the natural contraction
   (`∂(A∗B) = Σ_c (∂A·B + A·∂B)`), via `extDerivFun_finset_sum_mul_at`
   (`Bundle/PartialMfderiv/Basic.lean:416` — exact shape match). Hypotheses: component-wise
   `MDifferentiableAt` of both fields.
3. `covDerivStepComp_frameExtData_contrTail` — the field-level single-step Leibniz
   `∇(A∗B) = (∇_U A)∗B + A∗(∇B)` = `covDerivStepCompU_contrTail_leibniz` with `hext` := (2).
4. Tower differentiability: `iterCovComp_contMDiffOn`, `iterCovCompU_contMDiffOn`
   (every level `C^∞` on the open frame domain `u`; induction — each step is
   `extDerivFun(prev)` along the frame minus Γ-sums, and `∞` loses nothing per derivative),
   plus `iterCovComp_mdiffAt` / `iterCovCompU_mdiffAt` (the `hA`/`hB` inputs of (3) at every
   level) and private `contMDiffOn_finsetSum`.
   Analytic input: `contMDiffAt_extDerivFun_apply` from
   `Geometry/Connection/Realization/SmoothSectionsLocal.lean` (NEW; see that file — bump
   localization of the scalar only, vector field stays local via `contMDiffOn_dual_apply`).

## Lessons / gotchas

- Tower-level induction with multi-index `n`: keep `∀ n` INSIDE the induction motive —
  `n`'s type `Fin (r+a) → Idx` depends on the level `a`.
- The step unfolds to the explicit `extDerivFun − Γ-sums` form by `rw [iterCovComp_succ]; rfl`
  (`covDerivStepComp`/`covDerivStepCompU`/`frameExtData` are plain defs).
- `Fin ((r+(a+1))+1) = Fin ((r+a)+2)` is definitional (Nat-add recursion on the right) —
  no casts anywhere in the towers.
- Hypothesis style: frame smoothness as `ContMDiffOn … (fun y => TotalSpace.mk' E y (frame d y)) u`
  (what `IsLocalFrameOn` supplies), chr/base as per-component scalar `ContMDiffOn`.

## Piece 4 — the field single-step + `P(m)` binomial norm bound — DONE (2026-06-09, sorry-free)

Added (all sorry-free, in oleans):
- `slotId1`/`slotId2` — the two slot identities for the single-step's A/B terms
  (`[d,a,b]` regrouped: A-term = rank-cast `finCongr`; B-term = rotation `rotEquiv p q`).
- `rotEquiv p q : Fin (p+(q+1)) ≃ Fin (p+q+1)` — `[d,a,b]↦[a,d,b]` via `finCongr.trans (cycleRange ⟨p,_⟩)`.
- `covStep_contrTail_field` — **the field single-step in compReindex form**:
  `∇(A∗B) = (∇_U A∗B)∘e₁ + (A∗∇B)∘e₂` (general index `n`), `e₁=finCongr`, `e₂=rotEquiv`.
  Proof: `iterCovComp_succ`/`_zero` → reconstruct `n=cons (n 0)(append aPart bPart)` → Piece-3
  single-step → slotId1/slotId2 → fold back; finish `simp only [finCongr_apply]` (eta + finCongr↔Fin.cast).
- 3 wrappers: `compL2_iterCovComp_compReindex` (reindex norm-invariance through the tower),
  `iterCovComp_congr_on` (germ-congruence of the tower on open `u`), `contMDiffOn_contrTail`.
- **`compL2_iterCovComp_contrTail_le` = `P(m)`**: `|∇^m(A∗B)| ≤ ∑_c C(m,c)|∇_U^c A||∇^{m-c}B|`,
  the full binomial `compL2` bound, bottom-pull, universally quantified over the two fields.

### `P(m)` proof gotchas (durable)
- **Term-size blowup, NOT logic**: the calc with inlined branch fields timed out even at 4M
  heartbeats. FIX = `set HL/HR/LF/RF` so every calc step is small-term. (No `set_option`
  bump needed afterwards.)  Lesson: large geometric calc steps must use `set`-opaque fields.
- `set`-defined fields are defeq to their bodies → `rw [covStep_contrTail_field …]` auto-closes
  `hsplit` (no trailing `simp` — it errors "no goals").
- `covStep_contrTail_field`'s reindex must be `finCongr` (an EQUIV) so `iterCovComp_compReindex`
  applies; `Fin.cast` (a function) does not. `finCongr_apply` bridges the proof.
- Pascal step gives `C*(a*b)` (grouped); the `succ` target is left-assoc `C*a*b` → one extra
  `Finset.sum_congr … (mul_assoc _ _ _).symm` step (mirrors the bundled `iterCov_product`).
- `pascal_sum` MOVED to the shared ancestor `Evolution/CovDerivStepCompContrNorm.lean`
  (namespace `HCGCompactness`), used by both this file and bundled `ProductMFoldNorm`.

## ROUTE CORRECTION (2026-06-09) — INVERT FIRST, no ISO/isolation

**I went down a needlessly complex path (ISO: differentiate `∇g=A∗g` m times, then isolate the
top word `(∇_U^m A)∗g` via a reindex-tracked subtraction). That subtraction-through-reindex was
the complexity blow-up. ABANDON it.** The spec's "invert `∇g_k=A_k∗g_k`" means solve for `A_k`
FIRST, before differentiating:

    A_k = ∇g_k ∗ g_k⁻¹     (contract both sides of ∇g_k = A_k∗g_k with g_k⁻¹; g_k∗g_k⁻¹ = δ)

Then `∇^m A_k = ∇^m(∇g_k ∗ g_k⁻¹)` and **P(m) applies DIRECTLY** (the two fields are `∇g_k` and
`g_k⁻¹`):

    |∇^m A_k| ≤ ∑_c C(m,c) |∇^{c+1} g_k| |∇^{m-c} g_k⁻¹|.

`c=m` term = `|∇^{m+1}g_k|·|g_k⁻¹| ≤ C|∇^{m+1}g_k|` (the linear top term); `c<m` terms are lower
order ⇒ `C_m`. **NO isolation, NO subtraction, NO `iterCovComp_contrTail_succ`, NO reindex
matching.** `compL2_sub_le`/`compL2_neg` (added to CovDerivStepCompContrNorm) are now unused for
this — keep them (harmless, generic).

### SUPERSEDED: the "invert-first" detour was wrong too — final route = the spec's
isolate-and-invert, made tractable by the **recursive `isoTop`** (2026-06-10). The spec
(RicBoundProof.md 102–106) deliberately never differentiates `g⁻¹`. The reindex bookkeeping I
feared was dissolved by DEFINING the isolated top `isoTop` recursively WITH the bottom-pull
L-reindex built in — the ISO recursion then needs no reindex matching at all; the U-shift
enters once, at norm level, via `contrTail_extendLast` + a block equiv.

## ABSTRACT CLAIM 1 DONE (2026-06-10, all sorry-free, in oleans)

The complete chain (file order):
- `iterCovComp_contrTail_succ` — the bottom-pull ARRAY identity (P(m)'s calc as an `=`):
  `∇^{m+1}(A∗B) = ∇^m((∇_U A)∗B)∘ψ_L + ∇^m(A∗∇B)∘ψ_R`, ψ = `frontExtendIterC … ▸ shiftEquivC`.
- `isoReindex` (= ψ_L) + **`isoTop`** (recursive isolated top, `isoTop_{m+1}[A] = isoTop_m[∇_U A]∘ψ_L`).
- **`compL2_isoResidual_le` = `ISO(m)`**: `|∇^m(A∗g) − isoTop_m[A]| ≤ Σ_{c<m} C(m,c)|∇_U^c A||∇^{m-c}g|`
  (NO top term). Induction: hdec (array decomposition; `(∇_U^{m+1}A)`-terms cancel by isoTop's defn),
  triangle + comp_equiv, IH + P(m), `pascal_sum_notop` (new, shared CovDerivStepCompContrNorm).
- `blockLeftEquiv` + `contrTail_extendLast` + **`compL2_isoTop_eq`**: `|isoTop_m[A]| = |(∇_U^m A)∗g|`.
- **`compL2_contrTail_topU_le`**: `|(∇_U^m A)∗g| ≤ |∇^m(A∗g)| + (no-top binomial)`.
- **`contrTail_contrTail_inv`**: `(T∗G)∗Ginv = T` (pointwise inverse property only — `∇g⁻¹` never
  appears) + **`compL2_le_contrTail_inv`**: `|T| ≤ |T∗G|·|Ginv|`.
- **`claim1_abstract`**: `|∇_U^m A| ≤ C(m,C0,KR,K)·(1+|∇^{m+1}g|)` by strong induction, from
  `hinv` (pointwise inverse array), `hrelB` (`|∇^{m'}(A∗g)| ≤ KR·|∇^{m'+1}g|`, m'≤m — the Koszul
  norm input), `|Ginv|≤C0`, `|∇^j g|≤K (1≤j≤m)`. Constant `C = max C0 0·(max KR 0 + S)` explicit.

KEY MATH CORRECTION caught en route: the single contraction `A∗g = ∇g` as an EQUALITY is
geometrically FALSE (the true relation has A hitting BOTH lower slots of g: two terms). The
honest input is the KOSZUL form: `Ǎ = A∗g = ½(three slot-permutations of ∇g)` ⇒ the NORM bound
`hrelB` with `KR = 3/2`. claim1_abstract takes hrelB as hypothesis (rank-general in A again).

## CLAIM 1 (component form) STATED + PROVEN sorry-free (2026-06-10, `claim1`)

`claim1` (AkMFold.lean, end) — the textbook Claim-1 estimate in component-tower form:
`|∇_U^m A| ≤ C·(1 + |∇^{m+1}g|)` (`compL2 (iterCovCompU … A m)` and `compL2 (iterCovComp … g …)`),
from the hypotheses:
- `hkoszul` — the lowered-Koszul relation `contrTail(A y)(g y) = c₁·(∇g∘P₁)+c₂·(∇g∘P₂)+c₃·(∇g∘P₃)`
  on `u` (the eq-3.7/`connDiffCompEq` content in THIS frame; Koszul gives `c=(½,½,−½)`, KR=3/2),
- `hinv` (pointwise inverse array of g/Ginv), `hGinv` (`|Ginv|≤C0`), `hK` (`|∇^j g|≤K, 1≤j≤m`).
PROOF: discharge `claim1_abstract`'s `hrelB` from `hkoszul` via `iterCovComp_smul`+`_add`
(tower linearity), `compL2_iterCovComp_compReindex` (reindex norm-inv), `compL2_iterCovComp_shift`,
`compL2_smul`/`compL2_add_le` (new). Tools built: `frameExtData_smul`, `iterCovComp_smul`,
`compL2_smul`. **So the analytic + algebraic content of Claim 1 is fully closed.**

### Remaining = pure GEOMETRIC instantiation of `claim1`'s hypotheses (next session)
The three hyps `hkoszul`, `hinv`, `hK`/`hGinv` are now precisely the geometric inputs:
1. **hkoszul**: the lowered-Koszul FIELD identity `contrTail(A_k-comp)(g_k-comp) = ½(P₁+P₂−P₃)(∇g_k-comp)`
   on `u` in a FIXED frame. Only the g_k-ON pointwise `connDiffCompEq` exists — needs the
   frame-general (gRef-ON) tensor/component version (derive, or re-prove in the fixed frame).
2. **hinv**: from `InverseMetricComponentsInFrame` (exists, used by `metricGammaEquiv`).
3. **hGinv/hK**: `|g_k⁻¹|≤C` from eq-3.3 metric equivalence; `|∇^j g_k|≤K` from the (A_N) context.
4. **Identify the component fields**: `A := frameCompRS(connectionDifferenceTensorAt)`,
   `g := frameComp0S(metric)`, in a gRef-ON frame; and the norm bridge `compL2(iterCovCompU…) =
   √normSqRS(∇^m A_k)` (the UPPER tower realization, upper analogue of `iterCovComp_eq_iterCov`)
   so the component conclusion reads as the textbook geometric `|∇^m A_k|`. The (0,s)-side g-tower
   bridge already exists (`iterCovComp_eq_iterCov`).
DESIGN: use gRef-ON fixed frame (compL2 = gRef-norm; Claim-1's `C(1+·)` is immune to gRef↔g_k via
`|g⁻¹|≤C`). This is the geometric frontier; `claim1` is the clean target to instantiate into.
