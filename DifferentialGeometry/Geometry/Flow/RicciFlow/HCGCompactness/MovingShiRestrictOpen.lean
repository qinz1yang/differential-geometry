import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.RicBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.SolutionRestrictOpen

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Restriction transport of the moving-metric Shi bound (`MovingShiBoundOn`)

The restriction-analog of `MovingShiPullback.lean`: it transports the
`MovingShiBoundOn` bound from a metric sequence `gSeq` on `M` to its open
restriction `t ↦ (gSeq i t).restrictOpen U` on an open submanifold `U`.

Unlike the pullback case, restriction *shares* tangent vectors: for `x : U` the
fibre `TangentSpace I x` is literally the model fibre `TangentSpace I ↑x`, so
there is no `mfderiv` in any statement.  The covariant-derivative tower is
therefore germ-local under restriction:

* `covDerivOfField_restrictOpen` — general base tower naturality
  (`covDerivOfField (restrictOpen g) A0U a x slots = covDerivOfField g A0M a ↑x slots`).
* `ricciSection_restrictOpen` — Ricci base case (both sides via
  `ricciSection_eq_ricciTensor` + `ricciTensor_restrictOpen`).
* `ricCovTower_restrictOpen` — the all-orders Ricci tower, reindexed to the
  `iterCov`/`ricCovTower` `(2+s)` indexing.
* `ricCovTower_normSq0S_restrictOpen` — the tower `normSq0S` is unchanged
  (banked `normSq0S_restrictOpen_apply`).
* `movingShiBoundOn_restrictOpen` — the endpoint Shi-bound transport.

This is the frontier deferred by Brick 2 of the P4 conv engine; it composes with
`movingShiBoundOn_pullback` (`MovingShiPullback.lean`) to land the moving-Shi
bound on the recentered source flows.
-/

noncomputable section

open Set Function Filter Bundle Manifold
open scoped Manifold Topology ContDiff ENNReal
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Connection.CovariantDerivative

namespace DifferentialGeometry
namespace HCGCompactness

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M]
  [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]

/-- General single-`covStep` recursion of `covDerivOfField` on an arbitrary
rank-2 base (public re-derivation of the recursion used by the pullback engine).
The leading slot gives the scalar directional derivative of the previous tower
level; the remaining terms are the Levi-Civita corrections in the non-leading
slots. -/
private theorem covDerivOfField_succ_eval
    (gRef : SmoothRiemannianMetric I M)
    (A0 : Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (a : Nat)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (V : Fin (a + 2) → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (x : M) :
    covDerivOfField (I := I) gRef A0 (a + 1) x
        (Fin.cons (X x) (fun q : Fin (a + 2) => V q x)) =
      extDerivFun (I := I)
          (fun y : M => covDerivOfField (I := I) gRef A0 a y
            (fun q : Fin (a + 2) => V q y)) x (X x) -
        ∑ p : Fin (a + 2),
          covDerivOfField (I := I) gRef A0 a x
            (Function.update (fun q : Fin (a + 2) => V q x) p
              (((leviCivitaConnectionOfMetric (I := I) gRef)
                  (fun y : M => V p y) x) (X x))) := by
  rw [covDerivOfField_succ, metricCovDerivStep_apply,
    Tensor0SBundle.totalNabla0SFun_apply_section]
  exact Tensor0SBundle.nabla0SFun_eval_smooth_slots
    (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
    (leviCivitaConnectionOfMetric (I := I) gRef) X V
    (covDerivOfField (I := I) gRef A0 a) x

/-- **Germ-locality of the `covDerivOfField` tower under restriction.**  For a
rank-2 base field `A0U` on `U` and `A0M` on `M` whose values agree at shared
points/vectors (`hA0`), the full `gRef`-covariant-derivative tower of `A0U`
under the restricted background metric agrees with the tower of `A0M` under the
ambient metric.  There is no `mfderiv`: the tangent vectors `slots q` are shared
between `x : U` and `↑x : M`.  The successor step reduces the leading-slot term
via `extDerivFun_restrictOpen` and the connection corrections via
`metricCov_restrictOpen_globalSection`. -/
theorem covDerivOfField_restrictOpen
    (gRef : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    [SigmaCompactSpace U] [T2Space U] [BoundarylessManifold I U]
    [IsManifold I 1 U] [IsManifold I 2 U] [IsManifold I ((∞ : WithTop ℕ∞) + 1) U]
    (A0U : Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H)
      (I := I) (M := U) (n := (∞ : WithTop ℕ∞)) 2)
    (A0M : Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (hA0 : ∀ (x : U) (slots : Fin 2 → TangentSpace I x),
      A0U x slots = A0M (x : M) slots) :
    ∀ a : Nat, ∀ x : U, ∀ slots : Fin (a + 2) → TangentSpace I x,
      covDerivOfField (I := I) (gRef.restrictOpen (I := I) U) A0U a x slots =
        covDerivOfField (I := I) gRef A0M a (x : M) slots := by
  classical
  intro a
  induction a with
  | zero =>
      intro x slots
      exact hA0 x slots
  | succ a ih =>
      intro x slots
      -- Ambient (`M`) witness sections for the slots at `↑x`.
      obtain ⟨X, hX⟩ :=
        ContMDiffSection.exists_eq_at_gen (I := I) (F := E) (V := TangentSpace I)
          (n := (⊤ : ℕ∞)) (x : M) (slots 0)
      let V : Fin (a + 2) →
          ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
        fun q =>
          (ContMDiffSection.exists_eq_at_gen (I := I) (F := E) (V := TangentSpace I)
            (n := (⊤ : ℕ∞)) (x : M) (slots q.succ)).choose
      have hV : ∀ q : Fin (a + 2), V q (x : M) = slots q.succ := by
        intro q
        exact
          (ContMDiffSection.exists_eq_at_gen (I := I) (F := E) (V := TangentSpace I)
            (n := (⊤ : ℕ∞)) (x : M) (slots q.succ)).choose_spec
      -- Their `U`-restrictions witness the same slots at `x : U`.
      let XU : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : U → Type _) :=
        restrictOpenTangentSection (I := I) U X
      let VU : Fin (a + 2) →
          ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : U → Type _) :=
        fun q => restrictOpenTangentSection (I := I) U (V q)
      have hsmooth :
          covDerivOfField (I := I) (gRef.restrictOpen (I := I) U) A0U (a + 1) x
              (Fin.cons (XU x) (fun q : Fin (a + 2) => VU q x)) =
            covDerivOfField (I := I) gRef A0M (a + 1) (x : M)
              (Fin.cons (X (x : M)) (fun q : Fin (a + 2) => V q (x : M))) := by
        have hleft :=
          covDerivOfField_succ_eval (I := I) (gRef.restrictOpen (I := I) U) A0U a XU VU x
        have hright :=
          covDerivOfField_succ_eval (I := I) gRef A0M a X V (x : M)
        rw [hleft, hright]
        -- Leading-slot directional-derivative term.
        have hderiv :
            extDerivFun (I := I)
                (fun y : U => covDerivOfField (I := I) (gRef.restrictOpen (I := I) U) A0U a y
                  (fun q : Fin (a + 2) => VU q y)) x (XU x) =
              extDerivFun (I := I)
                (fun z : M => covDerivOfField (I := I) gRef A0M a z
                  (fun q : Fin (a + 2) => V q z)) (x : M) (X (x : M)) := by
          have hscalar :
              (fun y : U => covDerivOfField (I := I) (gRef.restrictOpen (I := I) U) A0U a y
                (fun q : Fin (a + 2) => VU q y)) =
                fun y : U => (fun z : M => covDerivOfField (I := I) gRef A0M a z
                  (fun q : Fin (a + 2) => V q z)) (y : M) := by
            funext y
            simpa [VU, restrictOpenTangentSection_apply] using
              ih y (fun q : Fin (a + 2) => VU q y)
          have hf : MDifferentiableAt I 𝓘(ℝ, ℝ)
              (fun z : M => covDerivOfField (I := I) gRef A0M a z
                (fun q : Fin (a + 2) => V q z)) (x : M) :=
            (Tensor0SBundle.tensor0SField_eval_smooth_slots_contMDiffAt
              (I := I) (covDerivOfField (I := I) gRef A0M a)
              (fun q : Fin (a + 2) => V q) (x : M)).mdifferentiableAt (by simp)
          rw [hscalar]
          have hXU : XU x = X (x : M) := restrictOpenTangentSection_apply (I := I) U X x
          rw [hXU]
          exact extDerivFun_restrictOpen (I := I) U
            (fun z : M => covDerivOfField (I := I) gRef A0M a z
              (fun q : Fin (a + 2) => V q z)) x (X (x : M)) hf
        -- Connection-correction sum.
        have hsum :
            (∑ p : Fin (a + 2),
              covDerivOfField (I := I) (gRef.restrictOpen (I := I) U) A0U a x
                (Function.update (fun q : Fin (a + 2) => VU q x) p
                  (((leviCivitaConnectionOfMetric (I := I) (gRef.restrictOpen (I := I) U))
                      (fun y : U => VU p y) x) (XU x)))) =
              ∑ p : Fin (a + 2),
                covDerivOfField (I := I) gRef A0M a (x : M)
                  (Function.update (fun q : Fin (a + 2) => V q (x : M)) p
                    (((leviCivitaConnectionOfMetric (I := I) gRef)
                        (fun z : M => V p z) (x : M)) (X (x : M)))) := by
          apply Finset.sum_congr rfl
          intro p _
          -- The connection correction is germ-local (shared vector, no `mfderiv`).
          set covL : TangentSpace I x :=
            ((leviCivitaConnectionOfMetric (I := I) (gRef.restrictOpen (I := I) U))
              (fun y : U => VU p y) x) (XU x) with hcovL_def
          set covR : TangentSpace I (x : M) :=
            ((leviCivitaConnectionOfMetric (I := I) gRef)
              (fun z : M => V p z) (x : M)) (X (x : M)) with hcovR_def
          -- `covL = covR` from `metricCov_restrictOpen_globalSection` (shared vector).
          have hcov : covL = covR := by
            have hcov' := metricCov_restrictOpen_globalSection (I := I) gRef U (V p) x (X (x : M))
            -- `covL` is the LHS of `hcov'` (defeq: `VU p y = restrictOpenTangentField …`,
            -- `XU x = X ↑x`, `leviCivitaConnectionOfMetric = metricCov`).
            rw [hcovL_def, hcovR_def]
            have hXU : XU x = X (x : M) := restrictOpenTangentSection_apply (I := I) U X x
            rw [hXU]
            exact hcov'
          -- Slot vectors agree after the update (shared, via `hcov`).
          have hslots : (fun q : Fin (a + 2) =>
              Function.update (fun q : Fin (a + 2) => VU q x) p covL q) =
              (fun q : Fin (a + 2) =>
                Function.update (fun q : Fin (a + 2) => V q (x : M)) p covR q) := by
            funext q
            by_cases hqp : q = p
            · subst q
              simp only [Function.update_self]
              exact hcov
            · rw [Function.update_of_ne hqp, Function.update_of_ne hqp]
              simp only [VU, restrictOpenTangentSection_apply]
          -- Transport the tower level from `U` to `M` at the updated slots.
          have hih := ih x (Function.update (fun q : Fin (a + 2) => VU q x) p covL)
          calc
            covDerivOfField (I := I) (gRef.restrictOpen (I := I) U) A0U a x
                (Function.update (fun q : Fin (a + 2) => VU q x) p covL)
                = covDerivOfField (I := I) gRef A0M a (x : M)
                    (Function.update (fun q : Fin (a + 2) => VU q x) p covL) := hih
            _ = covDerivOfField (I := I) gRef A0M a (x : M)
                    (Function.update (fun q : Fin (a + 2) => V q (x : M)) p covR) :=
                  congrArg _ hslots
        rw [hderiv, hsum]
      -- Reassemble both sides from their `Fin.cons` split.
      have hslotsU :
          slots = Fin.cons (slots 0) (fun q : Fin (a + 2) => slots q.succ) := by
        funext q
        refine Fin.cases ?_ (fun p => ?_) q
        · rw [Fin.cons_zero]
        · rw [Fin.cons_succ]
      have hXUx : XU x = slots 0 := by
        rw [restrictOpenTangentSection_apply]; exact hX
      have hVUx : ∀ q : Fin (a + 2), VU q x = slots q.succ := by
        intro q; rw [restrictOpenTangentSection_apply]; exact hV q
      have hcons :
          (Fin.cons (XU x) (fun q : Fin (a + 2) => VU q x)
              : Fin (a + 1 + 2) → TangentSpace I x) = slots := by
        rw [hslotsU]
        funext q
        refine Fin.cases ?_ (fun p => ?_) q
        · rw [Fin.cons_zero, Fin.cons_zero, hXUx]
        · rw [Fin.cons_succ, Fin.cons_succ, hVUx]
      have hconsM :
          (Fin.cons (X (x : M)) (fun q : Fin (a + 2) => V q (x : M))
              : Fin (a + 1 + 2) → TangentSpace I (x : M)) = slots := by
        funext q
        refine Fin.cases ?_ (fun p => ?_) q
        · rw [Fin.cons_zero, hX]
        · rw [Fin.cons_succ, hV]
      rw [hcons, hconsM] at hsmooth
      exact hsmooth

/-- **Germ-locality of the Ricci section under restriction.**  The realized
Ricci section of the Levi-Civita connection of the restricted metric agrees with
the ambient Ricci section at shared points/vectors.  Both sides reduce to
`ricciTensor` (via `ricciSection_eq_ricciTensor`), which is germ-local
(`ricciTensor_restrictOpen`). -/
theorem ricciSection_restrictOpen
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    [SigmaCompactSpace U] [T2Space U] [BoundarylessManifold I U]
    [IsManifold I 1 U] [IsManifold I ((∞ : WithTop ℕ∞) + 1) U]
    (x : U) (slots : Fin 2 → TangentSpace I x) :
    CovariantDerivative.ricciSection (I := I)
        (leviCivitaConnectionOfMetric (I := I) (g.restrictOpen (I := I) U))
        (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally (I := I)
          (g.restrictOpen (I := I) U)) x slots
      = CovariantDerivative.ricciSection (I := I)
          (leviCivitaConnectionOfMetric (I := I) g)
          (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally (I := I) g)
          (x : M) slots := by
  -- Reshape `slots` to `vec2 (slots 0) (slots 1)` at each flavor separately (the
  -- `vec2` term's TangentSpace flavor is fixed by its expected argument type).
  have hLHS :
      CovariantDerivative.ricciSection (I := I)
          (leviCivitaConnectionOfMetric (I := I) (g.restrictOpen (I := I) U))
          (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally (I := I)
            (g.restrictOpen (I := I) U)) x slots
        = ricciTensor (I := I) (M := U) (g.restrictOpen (I := I) U) x (slots 0) (slots 1) := by
    have hvecU : slots = vec2 (I := I) (slots 0) (slots 1) := by
      funext i; fin_cases i <;> rfl
    rw [hvecU]
    exact ricciSection_eq_ricciTensor (I := I) (g.restrictOpen (I := I) U) x (slots 0) (slots 1)
  have hRHS :
      CovariantDerivative.ricciSection (I := I)
          (leviCivitaConnectionOfMetric (I := I) g)
          (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally (I := I) g)
          (x : M) slots
        = ricciTensor (I := I) (M := M) g (x : M) (slots 0) (slots 1) := by
    have hvecM : slots = vec2 (I := I) (slots 0) (slots 1) := by
      funext i; fin_cases i <;> rfl
    rw [hvecM]
    exact ricciSection_eq_ricciTensor (I := I) g (x : M) (slots 0) (slots 1)
  rw [hLHS, hRHS]
  exact ricciTensor_restrictOpen (I := I) g U x (slots 0) (slots 1)

/-- Evaluated form of `covDerivOfField_eq_iterCov`: `covDerivOfField gRef A0 m` at
`x` on `slots` equals `iterCov gRef 2 A0 m` at `x` on the `acEquiv m`-reindexed
slots.  (Local copy of `MovingShiPullback.covDerivOfField_apply_eq_iterCov` to
avoid a cross-file import cycle.) -/
private theorem covDerivOfField_apply_eq_iterCov'
    (gRef : SmoothRiemannianMetric I M)
    (A0 : Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (m : ℕ) (x : M) (slots : Fin (m + 2) → TangentSpace I x) :
    covDerivOfField (I := I) gRef A0 m x slots
      = iterCov (I := I) gRef 2 A0 m x (slots ∘ ⇑(acEquiv m)) := by
  rw [covDerivOfField_eq_iterCov]
  rfl

/-- **Restriction naturality of the Ricci-derivative tower `ricCovTower`.**
`ricCovTower (g.restrictOpen U)(g.restrictOpen U) s` at `x` evaluated on `slots`
equals `ricCovTower g g s` at `↑x` evaluated on the *shared* `slots`.  Assembled
from `covDerivOfField_restrictOpen` (Ricci base via `ricciSection_restrictOpen`),
reindexed to the `iterCov` indexing of `ricCovTower` by
`covDerivOfField_apply_eq_iterCov'`. -/
theorem ricCovTower_restrictOpen
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    [SigmaCompactSpace U] [T2Space U] [BoundarylessManifold I U]
    [IsManifold I 1 U] [IsManifold I 2 U] [IsManifold I ((∞ : WithTop ℕ∞) + 1) U]
    (s : ℕ) (x : U) (slots : Fin (2 + s) → TangentSpace I x) :
    ricCovTower (I := I) (g.restrictOpen (I := I) U)
        (g.restrictOpen (I := I) U) s x slots
      = ricCovTower (I := I) g g s (x : M) slots := by
  have hrestrict := covDerivOfField_restrictOpen (I := I) g U
    (CovariantDerivative.ricciSection (I := I)
      (leviCivitaConnectionOfMetric (I := I) (g.restrictOpen (I := I) U))
      (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally (I := I)
        (g.restrictOpen (I := I) U)))
    (CovariantDerivative.ricciSection (I := I)
      (leviCivitaConnectionOfMetric (I := I) g)
      (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally (I := I) g))
    (ricciSection_restrictOpen (I := I) g U) s x (slots ∘ (acEquiv s).symm)
  rw [covDerivOfField_apply_eq_iterCov', covDerivOfField_apply_eq_iterCov'] at hrestrict
  -- `ricCovTower g gRef s = iterCov gRef 2 (ricciSection (leviCivita g)) s` (definitional),
  -- so `convert` reduces to cancelling the `acEquiv`-reindexing on the slots.
  convert hrestrict using 2 <;>
    · funext i
      simp only [Function.comp_apply, Equiv.symm_apply_apply]

/-- **The Ricci-tower `normSq0S` is unchanged by restriction.**  In the shared
fibre at `x`, `normSq0S (g.restrictOpen U) x (ricCovTower (g.restrictOpen U) …)`
equals `normSq0S g ↑x (ricCovTower g …)`.  Combines `ricCovTower_restrictOpen`
(as a tensor equality, via `tensor0SSpace_ext`) with the banked
`normSq0S_restrictOpen_apply`. -/
theorem ricCovTower_normSq0S_restrictOpen
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    [SigmaCompactSpace U] [T2Space U] [BoundarylessManifold I U]
    [IsManifold I 1 U] [IsManifold I 2 U] [IsManifold I ((∞ : WithTop ℕ∞) + 1) U]
    (s : ℕ) (x : U) :
    Tensor0SBundle.normSq0S (I := I) (g.restrictOpen (I := I) U) x (2 + s)
        (ricCovTower (I := I) (g.restrictOpen (I := I) U)
          (g.restrictOpen (I := I) U) s x)
      = Tensor0SBundle.normSq0S (I := I) g (x : M) (2 + s)
          (ricCovTower (I := I) g g s (x : M)) := by
  rw [normSq0S_restrictOpen_apply (I := I) g U (2 + s) x
    (ricCovTower (I := I) (g.restrictOpen (I := I) U) (g.restrictOpen (I := I) U) s x)]
  -- The two towers agree as tensors in the shared fibre at `↑x`.
  have htensor :
      ricCovTower (I := I) (g.restrictOpen (I := I) U) (g.restrictOpen (I := I) U) s x
        = ricCovTower (I := I) g g s (x : M) := by
    ext slots
    exact ricCovTower_restrictOpen (I := I) g U s x slots
  rw [htensor]

/-- **The moving-metric Shi bound transfers under restriction.**  If the Shi
bound `MovingShiBoundOn` holds for the metric sequence `gSeq` on a set `U₀ ⊆ M`,
then it holds for the restricted sequence `i t ↦ (gSeq i t).restrictOpen U` on any
set `V ⊆ U` whose image under the inclusion lies in `U₀`.  Per-point, the
Ricci-tower `√normSq0S` is preserved (`ricCovTower_normSq0S_restrictOpen`), so the
bound at `↑x` gives the bound at `x`. -/
theorem movingShiBoundOn_restrictOpen
    (gSeq : ℕ → ℝ → SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    [SigmaCompactSpace U] [T2Space U] [BoundarylessManifold I U]
    [IsManifold I 1 U] [IsManifold I 2 U] [IsManifold I ((∞ : WithTop ℕ∞) + 1) U]
    (U₀ : Set M) (β ψ : ℝ) (Nord : ℕ) (KShi : ℝ) (V : Set U)
    (hV : ∀ x ∈ V, (x : M) ∈ U₀)
    (hShi : MovingShiBoundOn (I := I) U₀ β ψ gSeq Nord KShi) :
    MovingShiBoundOn (I := I) V β ψ
      (fun i t => (gSeq i t).restrictOpen (I := I) U) Nord KShi := by
  intro s hs i t ht x hx
  rw [ricCovTower_normSq0S_restrictOpen (I := I) (gSeq i t) U s x]
  exact hShi s hs i t ht (x : M) (hV x hx)

end HCGCompactness
end DifferentialGeometry

end
