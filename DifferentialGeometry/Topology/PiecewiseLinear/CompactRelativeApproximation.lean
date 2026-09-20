/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LocallyFiniteApproximation
import DifferentialGeometry.Topology.PiecewiseLinear.CompactEmbeddingApproximation

/-!
# Relative piecewise linear approximation on the compact stages of a piece tower

`Moise352` asks for a piecewise linear approximation of a topological embedding of a locally
finite polyhedral manifold with boundary, within a prescribed continuous positive error.
`LocallyFiniteApproximation` carries out the passage from the compact stages of a
`LocallyFinitePieceTower` to the whole set, and packages the remaining obligation as
`Moise352Stages`.  This file supplies the *stagewise recursion*: it builds the family of
stagewise maps out of a single one-step relative statement, and it isolates that one-step
statement as the only remaining mathematical obligation.

## The tolerance defect in `Moise352Stages`

`Moise352Stages` quantifies over a sequence of tolerances `ε : ℕ → ℝ` **before** the family
of maps, while also demanding that `f (i + 1)` agree with `f i` on `T.coreSpace i`.  Since the
stages increase, a point `x` of `T.coreSpace j` lies in every later stage, and the agreement
clause forces `f i x = f j x` for all `i ≥ j`; the error clause then reads
`dist (f j x) (h x) < ε i` for every `i ≥ j` at once.  Choosing a null sequence of tolerances
therefore pins `f j` to `h` on the whole stage.

`Moise352Stages.exists_isPLHomeomorphInto_eqOn` proves exactly this: the hypothesis implies
that the topological embedding `h` *coincides* with a piecewise linear embedding on every
compact stage of every tower.  That is a statement about `h`, not an approximation statement,
and it fails already for a non-piecewise-linear self-embedding of the real line; so
`Moise352Stages n` is not available as an input for `n ≥ 1`, and neither is the hypothesis
`hstages` of `LocallyFinitePieceTower.exists_isPLHomeomorphInto_dist_lt_of_stages`, which has
the same shape.  No counterexample tower is constructed here, so the falsity itself is a
mathematical remark rather than a formalised result; the implication above is formalised.

The repair is to let the tolerance depend on the *point* rather than on the stage index.  The
assembly theorem `LocallyFinitePieceTower.exists_isPLHomeomorphInto_of_stages` already takes a
pointwise error `φ : M₁ → ℝ`, and with a pointwise error the agreement clause costs nothing:
the bound inherited on the previous stage is the very bound that is demanded there.

## Main results

* `LocallyFinitePieceTower.eqOn_coreSpace_of_le`: a family of maps agreeing with its
  predecessors agrees with every earlier member on that member's stage.
* `Moise352Stages.exists_isPLHomeomorphInto_eqOn`: the tolerance defect described above.
* `Moise352StageStep`: the remaining obligation, in two clauses — an absolute piecewise
  linear approximation, injective on the first stage, and a relative one extending a given
  piecewise linear embedding of a stage over the next stage.
* `moise352_of_stageStep`: `Moise352` follows from `Moise352StageStep`.  Everything between
  the two — the recursion over the stages, the choice of tolerances, the separation estimates
  and the passage to the limit — is carried out here.
* `LocallyFinitePieceTower.coreSpace_ofPiece` and
  `LocallyFinitePieceTower.exists_isPLOn_injOn_eqOn_dist_lt_of_coreSpace_succ_subset`: the
  hypotheses of the step clause are satisfiable with a nonempty stage, and the conclusion is
  then met by the given map itself.

## What is not proved here

`Moise352StageStep` is not proved.  Its piecewise linear half is available in the model space:
`exists_isPLOn_dist_lt_eqOn` produces a piecewise linear map on a polyhedron agreeing with a
given piecewise linear map on a subpolyhedron and approximating a continuous map.  What is
missing is that the approximation can be chosen *injective*, relatively to the previous stage;
by `IsPLOn.isPLHomeomorphInto` injectivity on a compact set is all that separates a piecewise
linear map from a piecewise linear embedding, which is why the clauses of `Moise352StageStep`
ask only for `IsPLOn` together with `InjOn`.  The absolute case of that injectivity statement
is Moise 34.1; the relative case is what the stage recursion consumes.
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

section Chain

variable {n : ℕ} {M₁ : Type*} [TopologicalSpace M₁]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₁] {U : Set M₁}

/-- A family of maps each of which agrees with its predecessor on the predecessor's stage
agrees with every earlier member of the family on that member's stage.  The stages increase,
so the agreement propagates along the tower. -/
theorem LocallyFinitePieceTower.eqOn_coreSpace_of_le {Y : Type*}
    (T : LocallyFinitePieceTower n M₁ U) {f : ℕ → M₁ → Y}
    (hf : ∀ i, EqOn (f (i + 1)) (f i) (T.coreSpace i)) {i j : ℕ} (hij : i ≤ j) :
    EqOn (f j) (f i) (T.coreSpace i) := by
  induction j, hij using Nat.le_induction with
  | base => exact fun _ _ => rfl
  | succ k hik ih => exact fun x hx => (hf k (T.core_space_monotone hik hx)).trans (ih hx)

end Chain

section Defect

/-- The stagewise input `Moise352Stages` forces the map it approximates to be piecewise
linear already.

Because the agreement clause makes `f i` restrict to `f j` on the earlier stage
`T.coreSpace j`, and because the error clause is imposed at every later index `i` with the
tolerance `ε i` fixed in advance, a null sequence of tolerances leaves no room: the stage map
must equal `h` on the whole stage.  Consequently `Moise352Stages n` asserts that every
topological embedding of a locally finite polyhedral manifold with boundary agrees with a
piecewise linear embedding on each compact stage, which is false for `n ≥ 1`.

This is a defect in the quantifier order of `Moise352Stages`, not in the assembly it feeds:
`LocallyFinitePieceTower.exists_isPLHomeomorphInto_of_stages` asks for a *pointwise* error
function and is unaffected.  `Moise352StageStep` below is the repaired obligation. -/
theorem Moise352Stages.exists_isPLHomeomorphInto_eqOn {n : ℕ} (H : Moise352Stages.{u} n)
    {M₁ M₂ : Type u} [TopologicalSpace M₁] [T2Space M₁] [SecondCountableTopology M₁]
    [MetricSpace M₂] [SecondCountableTopology M₂]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₁]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₂]
    [HasGroupoid M₁ (plGroupoid n)] [HasGroupoid M₂ (plGroupoid n)]
    {K : Set M₁} (T : LocallyFinitePieceTower n M₁ K)
    (hT : ∀ i, IsCombinatorialManifoldWithBoundary n (T.piece i).piece.complex)
    {h : M₁ → M₂} (hh : Topology.IsEmbedding (K.domRestrict h)) (j : ℕ) :
    ∃ f : M₁ → M₂, IsPLHomeomorphInto n f (T.coreSpace j) ∧ EqOn f h (T.coreSpace j) := by
  obtain ⟨f, hstep, hstage, hclose⟩ :=
    H T hT hh (fun i : ℕ => 1 / ((i : ℝ) + 1)) fun _ => div_pos one_pos (by positivity)
  refine ⟨f j, hstage j, fun x hx => ?_⟩
  have hd : dist (f j x) (h x) ≤ 0 := by
    by_contra hcon
    rw [not_le] at hcon
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hcon
    obtain ⟨k, hjk, hmk⟩ : ∃ k : ℕ, j ≤ k ∧ m ≤ k :=
      ⟨max j m, le_max_left j m, le_max_right j m⟩
    have hxi : x ∈ T.coreSpace k := T.core_space_monotone hjk hx
    have heq : f k x = f j x := T.eqOn_coreSpace_of_le hstep hjk hx
    have hlt : dist (f j x) (h x) < 1 / ((k : ℝ) + 1) := by
      rw [← heq]
      exact hclose k x hxi
    have hcast : ((m : ℝ) + 1) ≤ ((k : ℝ) + 1) := by
      have hc : (m : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr hmk
      linarith
    have hle : 1 / ((k : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) hcast
    linarith
  exact dist_le_zero.mp hd

end Defect

/-- A quarter of the running minimum of a sequence of reals.  Auxiliary to
`exists_antitone_pos_four_mul_le_of_forall_pos`. -/
private noncomputable def quarterRunningMin (d : ℕ → ℝ) : ℕ → ℝ
  | 0 => d 0 / 4
  | i + 1 => min (quarterRunningMin d i) (d (i + 1) / 4)

/-- Any sequence of positive reals dominates, term by term and after multiplication by four,
some antitone sequence of positive reals.  This lets a single tolerance be chosen that is
simultaneously admissible at every earlier stage. -/
private theorem exists_antitone_pos_four_mul_le_of_forall_pos {d : ℕ → ℝ} (hd : ∀ i, 0 < d i) :
    ∃ ε : ℕ → ℝ, (∀ i, 0 < ε i) ∧ Antitone ε ∧ ∀ i, 4 * ε i ≤ d i := by
  refine ⟨quarterRunningMin d, ?_, antitone_nat_of_succ_le fun i => min_le_left _ _, ?_⟩
  · intro i
    induction i with
    | zero => exact div_pos (hd 0) (by norm_num)
    | succ k ih => exact lt_min ih (div_pos (hd (k + 1)) (by norm_num))
  · intro i
    cases i with
    | zero =>
      have h0 : quarterRunningMin d 0 = d 0 / 4 := rfl
      rw [h0]
      linarith
    | succ k =>
      have h1 : quarterRunningMin d (k + 1) ≤ d (k + 1) / 4 := min_le_right _ _
      linarith

section Obligation

/-- The remaining obligation behind `Moise352`, on one compact stage at a time.

Fix a locally finite piece tower `T` presenting `K`, a topological embedding `h` of `K`, and
an error function `φ` which on every compact stage is bounded below by a positive constant.
Two clauses are asked for.

* The *absolute* clause: some map is piecewise linear and injective on the first stage
  `T.coreSpace 0` and approximates `h` there within `φ`.
* The *relative* clause: given a piecewise linear embedding `g` of the stage `T.coreSpace i`
  which approximates `h` within `φ` there, some map is piecewise linear and injective on the
  next stage `T.coreSpace (i + 1)`, agrees with `g` on `T.coreSpace i`, and approximates `h`
  within `φ` on the whole of `T.coreSpace (i + 1)`.

The absolute clause is the relative one with the previous stage taken empty, and both are
compact statements: every set named is compact and the bound `φ` is bounded below there, so a
constant tolerance would do on the part of the stage that is not pinned by `g`.  The pointwise
form of the bound is what makes the two clauses compose: on `T.coreSpace i` the conclusion of
the relative clause is exactly its own hypothesis, transported along `EqOn`, and no tolerance
is ever asked to shrink on a region where a map has already been fixed.  This is precisely
what `Moise352Stages` gets wrong; see `Moise352Stages.exists_isPLHomeomorphInto_eqOn`.

Only `InjOn` is genuinely open.  The piecewise linear half of both clauses, including the
agreement clause, is the content of `exists_isPLOn_dist_lt_eqOn`, which is proved: it
approximates a continuous map on a polyhedron by a piecewise linear one agreeing with a given
piecewise linear map on a subpolyhedron.  And injectivity is all that is missing for an
embedding, by `IsPLOn.isPLHomeomorphInto`, which upgrades a piecewise linear injection of a
compact set to a piecewise linear embedding; that upgrade is performed inside
`moise352_of_stageStep`, which is why the clauses below stop at `IsPLOn` and `InjOn`.

The absolute clause is Moise 34.1 — approximation of a topological embedding of a compact
polyhedral manifold pair by a piecewise linear embedding — transported to a stage of a tower;
the relative clause is its relative form.  Both are unproved in this development.  `Moise341`
in `MoiseChain` is a strictly weaker statement: it is the case of a piecewise linear *ball* in
`EuclideanSpace ℝ (Fin 3)`, with a constant tolerance, no agreement clause, and no ambient
manifolds.  Nothing below restricts `n`; the dimension restriction under which these clauses
are expected to hold belongs to the clauses themselves. -/
def Moise352StageStep (n : ℕ) : Prop :=
  ∀ {M₁ M₂ : Type u} [TopologicalSpace M₁] [T2Space M₁] [SecondCountableTopology M₁]
    [MetricSpace M₂] [SecondCountableTopology M₂]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₁]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₂]
    [HasGroupoid M₁ (plGroupoid n)] [HasGroupoid M₂ (plGroupoid n)]
    {K : Set M₁} (T : LocallyFinitePieceTower n M₁ K),
    (∀ i, IsCombinatorialManifoldWithBoundary n (T.piece i).piece.complex) →
    ∀ {h : M₁ → M₂}, Topology.IsEmbedding (K.domRestrict h) →
    ∀ {φ : M₁ → ℝ}, (∀ i, ∃ c : ℝ, 0 < c ∧ ∀ x ∈ T.coreSpace i, c ≤ φ x) →
      (∃ f : M₁ → M₂, IsPLOn n n f (T.coreSpace 0) ∧ InjOn f (T.coreSpace 0) ∧
          ∀ x ∈ T.coreSpace 0, dist (f x) (h x) < φ x) ∧
        ∀ (i : ℕ) (g : M₁ → M₂), IsPLHomeomorphInto n g (T.coreSpace i) →
          (∀ x ∈ T.coreSpace i, dist (g x) (h x) < φ x) →
          ∃ f : M₁ → M₂, IsPLOn n n f (T.coreSpace (i + 1)) ∧
            InjOn f (T.coreSpace (i + 1)) ∧ EqOn f g (T.coreSpace i) ∧
            ∀ x ∈ T.coreSpace (i + 1), dist (f x) (h x) < φ x

end Obligation

section Reduction

/-- `Moise352` follows from the one-step relative statement `Moise352StageStep`.

The tolerances are chosen first, after the separation constants of
`LocallyFinitePieceTower.exists_pos_le_dist_coreSpace` and the minima of `φ` on the stages,
and are assembled into the single error function `x ↦ ε (least stage containing x)`.  That
function is bounded below on each compact stage by the tolerance of that stage, which is the
hypothesis `Moise352StageStep` requires; the stage maps are then produced by recursion, the
absolute clause supplying the first and the relative clause each successor, with the
approximation bound carried along unchanged on the part of the stage already fixed.  The
resulting family is fed to `LocallyFinitePieceTower.exists_isPLHomeomorphInto_of_stages`. -/
theorem moise352_of_stageStep {n : ℕ} (H : Moise352StageStep.{u} n) : Moise352.{u} n := by
  classical
  intro M₁ M₂ _ _ _ _ _ _ _ _ _ K hK h hh φ hφ hpos
  obtain ⟨T, hT⟩ := hK
  choose ρ hρpos hρsep using fun i => T.exists_pos_le_dist_coreSpace hh i
  have hcex : ∀ i, ∃ c : ℝ, 0 < c ∧ ∀ x ∈ T.coreSpace i, c ≤ φ x := by
    intro i
    rcases (T.coreSpace i).eq_empty_or_nonempty with he | hne
    · refine ⟨1, one_pos, fun x hx => ?_⟩
      rw [he] at hx
      exact absurd hx (notMem_empty x)
    · obtain ⟨x₀, hx₀, hle⟩ := (T.isCompact_core_space i).exists_isMinOn hne
        (hφ.mono (T.core_space_subset_union i))
      exact ⟨φ x₀, hpos x₀ (T.core_space_subset_union i hx₀),
        fun x hx => isMinOn_iff.mp hle x hx⟩
  choose c hcpos hcle using hcex
  obtain ⟨ε, hεpos, hεanti, hεd⟩ := exists_antitone_pos_four_mul_le_of_forall_pos
    (d := fun i => min (ρ i) (c i)) fun i => lt_min (hρpos i) (hcpos i)
  obtain ⟨β, hβ⟩ : ∃ β : M₁ → ℝ, ∀ x ∈ K, ∃ i, x ∈ T.coreSpace i ∧ β x = ε i ∧
      ∀ j, x ∈ T.coreSpace j → i ≤ j := by
    refine ⟨fun x => if hx : ∃ i, x ∈ T.coreSpace i then ε (Nat.find hx) else 1, ?_⟩
    intro x hx
    have hex : ∃ i, x ∈ T.coreSpace i := T.exists_mem_core_space hx
    exact ⟨Nat.find hex, Nat.find_spec hex, dif_pos hex, fun j hj => Nat.find_min' hex hj⟩
  have hβstage : ∀ i, ∃ b : ℝ, 0 < b ∧ ∀ x ∈ T.coreSpace i, b ≤ β x := by
    refine fun i => ⟨ε i, hεpos i, fun x hx => ?_⟩
    obtain ⟨j, -, hβx, hmin⟩ := hβ x (T.core_space_subset_union i hx)
    rw [hβx]
    exact hεanti (hmin i hx)
  obtain ⟨Hbase, Hstep⟩ := H T hT hh (φ := β) hβstage
  obtain ⟨u₀, hu₀pl, hu₀inj, hu₀d⟩ := Hbase
  have hu₀ : IsPLHomeomorphInto n u₀ (T.coreSpace 0) :=
    hu₀pl.isPLHomeomorphInto (T.isCompact_core_space 0) hu₀inj
  have hnext : ∀ (i : ℕ) (g : M₁ → M₂), ∃ v : M₁ → M₂,
      IsPLHomeomorphInto n g (T.coreSpace i) →
        (∀ x ∈ T.coreSpace i, dist (g x) (h x) < β x) →
        IsPLHomeomorphInto n v (T.coreSpace (i + 1)) ∧ EqOn v g (T.coreSpace i) ∧
          ∀ x ∈ T.coreSpace (i + 1), dist (v x) (h x) < β x := by
    intro i g
    by_cases hg : IsPLHomeomorphInto n g (T.coreSpace i) ∧
        ∀ x ∈ T.coreSpace i, dist (g x) (h x) < β x
    · obtain ⟨v, hvpl, hvinj, hveq, hvd⟩ := Hstep i g hg.1 hg.2
      exact ⟨v, fun _ _ => ⟨hvpl.isPLHomeomorphInto (T.isCompact_core_space (i + 1)) hvinj,
        hveq, hvd⟩⟩
    · exact ⟨h, fun h1 h2 => absurd ⟨h1, h2⟩ hg⟩
  choose G hG using hnext
  obtain ⟨f, hf0, hfsucc⟩ : ∃ f : ℕ → M₁ → M₂, f 0 = u₀ ∧ ∀ i, f (i + 1) = G i (f i) :=
    ⟨fun i => Nat.rec (motive := fun _ => M₁ → M₂) u₀ (fun k v => G k v) i, rfl, fun _ => rfl⟩
  have hinv : ∀ i, IsPLHomeomorphInto n (f i) (T.coreSpace i) ∧
      ∀ x ∈ T.coreSpace i, dist (f i x) (h x) < β x := by
    intro i
    induction i with
    | zero =>
      rw [hf0]
      exact ⟨hu₀, hu₀d⟩
    | succ k ih =>
      have hk := hG k (f k) ih.1 ih.2
      rw [hfsucc k]
      exact ⟨hk.1, hk.2.2⟩
  have hstepEq : ∀ i, EqOn (f (i + 1)) (f i) (T.coreSpace i) := by
    intro i
    rw [hfsucc i]
    exact (hG i (f i) (hinv i).1 (hinv i).2).2.1
  have hunif : ∀ x ∈ K, ∃ i, x ∈ T.coreSpace i ∧ ∃ r : ℝ, 3 * β x < r ∧
      ∀ z ∈ K \ T.coreSpace i, r ≤ dist (h z) (h x) ∧ 3 * β z < r := by
    intro x hx
    obtain ⟨i, hxi, hβx, -⟩ := hβ x hx
    refine ⟨i + 2, T.core_space_monotone (by omega) hxi, ρ i, ?_, fun z hz => ⟨?_, ?_⟩⟩
    · have h1 : 4 * ε i ≤ min (ρ i) (c i) := hεd i
      have h2 : min (ρ i) (c i) ≤ ρ i := min_le_left _ _
      have h3 : 0 < ε i := hεpos i
      rw [hβx]
      linarith
    · exact hρsep i x hxi z hz
    · obtain ⟨k, hzk, hβz, -⟩ := hβ z hz.1
      have hik : i ≤ k := by
        by_contra hcon
        exact hz.2 (T.core_space_monotone (by omega) hzk)
      have h1 : 4 * ε i ≤ min (ρ i) (c i) := hεd i
      have h2 : min (ρ i) (c i) ≤ ρ i := min_le_left _ _
      have h3 : ε k ≤ ε i := hεanti hik
      have h4 : 0 < ε k := hεpos k
      rw [hβz]
      linarith
  obtain ⟨g, hg, hgd⟩ := T.exists_isPLHomeomorphInto_of_stages hstepEq (fun i => (hinv i).1)
    (fun i => (hinv i).2) hunif
  refine ⟨g, hg, fun x hx => (hgd x hx).trans ?_⟩
  obtain ⟨i, hxi, hβx, -⟩ := hβ x hx
  have h1 : 4 * ε i ≤ min (ρ i) (c i) := hεd i
  have h2 : min (ρ i) (c i) ≤ c i := min_le_right _ _
  have h3 : c i ≤ φ x := hcle i x hxi
  have h4 : 0 < ε i := hεpos i
  rw [hβx]
  linarith

end Reduction

section NonVacuity

/-- Every stage of the tower attached to a single piecewise linear piece is the whole set.
Together with
`LocallyFinitePieceTower.exists_isPLOn_injOn_eqOn_dist_lt_of_coreSpace_succ_subset` this
exhibits the hypotheses of the step clause of `Moise352StageStep` as satisfiable with a
nonempty stage. -/
theorem LocallyFinitePieceTower.coreSpace_ofPiece {n : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] {Y : Set X} (P : PLPiece n X Y) (i : ℕ) :
    (LocallyFinitePieceTower.ofPiece P).coreSpace i = Y :=
  P.piece.bijOn.image_eq

/-- The step clause of `Moise352StageStep` is consistent with its hypotheses: on a tower whose
stage does not grow, the given piecewise linear embedding is itself a witness.  This applies
in particular to `LocallyFinitePieceTower.ofPiece`, all of whose stages agree with the
underlying, possibly nonempty, set; so the clause is neither vacuous nor self-contradictory,
and what remains open in `Moise352StageStep` is the genuine growth of a stage. -/
theorem LocallyFinitePieceTower.exists_isPLOn_injOn_eqOn_dist_lt_of_coreSpace_succ_subset
    {n : ℕ} {M₁ M₂ : Type*} [TopologicalSpace M₁] [MetricSpace M₂]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₁]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₂] {K : Set M₁}
    (T : LocallyFinitePieceTower n M₁ K) {i : ℕ}
    (hsub : T.coreSpace (i + 1) ⊆ T.coreSpace i) {g h : M₁ → M₂} {φ : M₁ → ℝ}
    (hg : IsPLHomeomorphInto n g (T.coreSpace i))
    (hd : ∀ x ∈ T.coreSpace i, dist (g x) (h x) < φ x) :
    ∃ f : M₁ → M₂, IsPLOn n n f (T.coreSpace (i + 1)) ∧ InjOn f (T.coreSpace (i + 1)) ∧
      EqOn f g (T.coreSpace i) ∧ ∀ x ∈ T.coreSpace (i + 1), dist (f x) (h x) < φ x := by
  have heq : T.coreSpace (i + 1) = T.coreSpace i :=
    Subset.antisymm hsub (T.core_space_monotone (Nat.le_succ i))
  refine ⟨g, ?_, ?_, fun _ _ => rfl, fun x hx => hd x (hsub hx)⟩
  · rw [heq]
    exact hg.isPLOn
  · rw [heq]
    exact hg.injOn

end NonVacuity

end DifferentialGeometry.Topology.PiecewiseLinear
