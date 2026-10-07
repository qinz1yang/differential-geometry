import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.CostDefs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.FiniteJointAction
import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

open Set Filter _root_.MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped _root_.Manifold ContDiff _root_.Topology BigOperators Interval

universe u uP

def interleavedPieceEquiv (N : ℕ) :
    (Fin (N + 1) ⊕ (Fin N ⊕ Fin 1)) ≃ Fin (2 * N + 2) := by
  let f : (Fin (N + 1) ⊕ (Fin N ⊕ Fin 1)) → Fin (2 * N + 2)
    | .inl k => ⟨2 * k.val, by omega⟩
    | .inr (.inl k) => ⟨2 * k.val + 1, by omega⟩
    | .inr (.inr _) => ⟨2 * N + 1, by omega⟩
  apply Equiv.ofBijective f
  constructor
  · intro x y h
    have hv := congrArg Fin.val h
    rcases x with k | (k | k) <;> rcases y with l | (l | l)
    all_goals simp only [f] at hv
    all_goals simp only [Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl]
    all_goals first | apply Fin.ext; omega | exact Subsingleton.elim _ _ | omega
  · intro i
    by_cases hi : i.val = 2 * N + 1
    · exact ⟨.inr (.inr 0), Fin.ext hi.symm⟩
    · rcases Nat.mod_two_eq_zero_or_one i.val with h | h
      · refine ⟨.inl ⟨i.val / 2, by omega⟩, ?_⟩
        apply Fin.ext
        dsimp only [f]
        omega
      · refine ⟨.inr (.inl ⟨i.val / 2, by omega⟩), ?_⟩
        apply Fin.ext
        dsimp only [f]
        omega

theorem interleavedPieceEquiv_values (N : ℕ) :
    (∀ k : Fin (N + 1), interleavedPieceEquiv N (.inl k) =
      ⟨2 * k.val, by omega⟩) ∧
    (∀ k : Fin N, interleavedPieceEquiv N (.inr (.inl k)) =
      ⟨2 * k.val + 1, by omega⟩) ∧
    interleavedPieceEquiv N (.inr (.inr 0)) = Fin.last (2 * N + 1) := by
  exact ⟨fun _ => rfl, fun _ => rfl, rfl⟩

section Carrier

variable (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) {N : ℕ}
variable (j : Fin (N + 1) ≃ H.StageInterval first last)
variable (e : Fin N ≃ {i : Fin H.eventCount // first ≤ i.castSucc ∧ i.succ ≤ last})
variable (W : (k : Fin N) → TopologicalSpace.Opens (H.event (e k).val).incoming.terminalRegularOpen)

abbrev ActualPieceCarrier : (Fin (N + 1) ⊕ (Fin N ⊕ Fin 1)) → Type u :=
  Sum.elim (fun k => (H.stage (j k).val).Carrier)
    (Sum.elim (fun k => W k) (fun _ => (H.stage first).Carrier))

instance actualPieceTop (k) : TopologicalSpace (ActualPieceCarrier H first last j e W k) := by
  rcases k with k | (k | k) <;> dsimp only [ActualPieceCarrier, Sum.elim] <;> infer_instance

instance actualPieceChart (k) : ChartedSpace ThreeSpace
    (ActualPieceCarrier H first last j e W k) := by
  rcases k with k | (k | k) <;> dsimp only [ActualPieceCarrier, actualPieceTop, Sum.elim] <;>
    infer_instance

instance actualPieceManifold (k) : IsManifold ThreeModel ∞
    (ActualPieceCarrier H first last j e W k) := by
  rcases k with k | (k | k) <;>
    dsimp only [ActualPieceCarrier, actualPieceTop, actualPieceChart, Sum.elim] <;> infer_instance

instance actualPieceT2 (k) : T2Space (ActualPieceCarrier H first last j e W k) := by
  rcases k with k | (k | k) <;> dsimp only [ActualPieceCarrier, actualPieceTop, Sum.elim] <;>
    infer_instance

end Carrier

/-- Reindex one joint family through the actual ordinary, survivor, and tail
flows. Only the actual tail upper clock varies; its action split holds for every
parameter and every terminal clock. -/
theorem interleaved_actual_flow_joint_families
    {P : Type uP} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) {N : ℕ}
    (j : Fin (N + 1) ≃ H.StageInterval first last)
    (e : Fin N ≃ {i : Fin H.eventCount // first ≤ i.castSucc ∧ i.succ ≤ last})
    (W : (k : Fin N) → TopologicalSpace.Opens (H.event (e k).val).incoming.terminalRegularOpen)
    (DO : Fin (N + 1) → RealTimeInterval) (DS : Fin N → RealTimeInterval)
    (DT : RealTimeInterval)
    (SO : (k : Fin (N + 1)) →
      SolutionOn (I := ThreeModel) (M := (H.stage (j k).val).Carrier) (DO k))
    (SS : (k : Fin N) → SolutionOn (I := ThreeModel) (M := W k) (DS k))
    (ST : SolutionOn (I := ThreeModel) (M := (H.stage first).Carrier) DT)
    (hSO : ∀ k, IsSolutionOn (SO k)) (hSS : ∀ k, IsSolutionOn (SS k)) (hST : IsSolutionOn ST)
    (alphaO : (k : Fin (N + 1)) → ℝ → (H.stage (j k).val).Carrier)
    (alphaS : (k : Fin N) → ℝ → W k) (alphaT : ℝ → (H.stage first).Carrier)
    (T : ℝ) (s : Fin (2 * N + 3) → ℝ) :
    let K := Fin (N + 1) ⊕ (Fin N ⊕ Fin 1);
    let M0 : K → Type u := ActualPieceCarrier H first last j e W;
    let D0 : K → RealTimeInterval := Sum.elim DO (Sum.elim DS (fun _ => DT));
    let S0 : (k : K) → SolutionOn (I := ThreeModel) (M := M0 k) (D0 k) :=
      Sum.rec (fun k => SO k) (Sum.rec (fun k => SS k) (fun _ => ST));
    let alpha0 : (k : K) → ℝ → M0 k :=
      Sum.rec (fun k => alphaO k) (Sum.rec (fun k => alphaS k) (fun _ => alphaT));
    let q := interleavedPieceEquiv N;
    let M : Fin (2 * N + 2) → Type u := fun i => M0 (q.symm i);
    let D : Fin (2 * N + 2) → RealTimeInterval := fun i => D0 (q.symm i);
    let S : (i : Fin (2 * N + 2)) → SolutionOn (I := ThreeModel) (M := M i) (D i) :=
      fun i => S0 (q.symm i);
    let alpha : (i : Fin (2 * N + 2)) → ℝ → M i := fun i => alpha0 (q.symm i);
    (∀ i, IsSolutionOn (S i)) ∧
    (∀ k, HEq (S (q (.inl k))) (SO k)) ∧
    (∀ k, HEq (S (q (.inr (.inl k)))) (SS k)) ∧
    HEq (S (Fin.last (2 * N + 1))) ST ∧
    ∀ f : (i : Fin (2 * N + 2)) → P × ℝ → M i,
      let g := (Equiv.piCongrLeft' (fun k => P × ℝ → M0 k) q).symm f;
      (∀ i z r, f i (z, r) = g (q.symm i) (z, r)) ∧
      ((∀ i, ContMDiff (𝓘(ℝ, P).prod 𝓘(ℝ, ℝ)) ThreeModel (8 : ℕ) (f i)) →
        (∀ k, ContMDiff (𝓘(ℝ, P).prod 𝓘(ℝ, ℝ)) ThreeModel (8 : ℕ) (g (.inl k))) ∧
        (∀ k, ContMDiff (𝓘(ℝ, P).prod 𝓘(ℝ, ℝ)) ThreeModel (8 : ℕ)
          (g (.inr (.inl k)))) ∧
        ContMDiff (𝓘(ℝ, P).prod 𝓘(ℝ, ℝ)) ThreeModel (8 : ℕ) (g (.inr (.inr 0)))) ∧
      ((∀ i r, r ∈ Icc (s i.castSucc) (s i.succ) →
          (fun t => f i (0, t)) =ᶠ[𝓝 r] alpha i) →
        (∀ k r, r ∈ Icc (s (q (.inl k)).castSucc) (s (q (.inl k)).succ) →
          (fun t => g (.inl k) (0, t)) =ᶠ[𝓝 r] alphaO k) ∧
        (∀ k r, r ∈ Icc (s (q (.inr (.inl k))).castSucc)
          (s (q (.inr (.inl k))).succ) →
            (fun t => g (.inr (.inl k)) (0, t)) =ᶠ[𝓝 r] alphaS k) ∧
        (∀ r ∈ Icc (s ⟨2 * N + 1, by omega⟩) (s (Fin.last (2 * N + 2))),
          (fun t => g (.inr (.inr 0)) (0, t)) =ᶠ[𝓝 r] alphaT)) ∧
      (∀ (z : P) (w : ℝ),
        finiteJointAction S T f (fun i => s i.castSucc) (fun i => s i.succ) (z, w) =
          (∑ k, lRegularizedAction (SO k) T (fun r => g (.inl k) (z, r))
            (s (q (.inl k)).castSucc) (s (q (.inl k)).succ)) +
          (∑ k, lRegularizedAction (SS k) T (fun r => g (.inr (.inl k)) (z, r))
            (s (q (.inr (.inl k))).castSucc) (s (q (.inr (.inl k))).succ)) +
          lRegularizedAction ST T (fun r => g (.inr (.inr 0)) (z, r))
            (s ⟨2 * N + 1, by omega⟩) w) := by
  intro K M0 D0 S0 alpha0 q M D S alpha
  have hS0 (k : K) : IsSolutionOn (S0 k) := by
    rcases k with k | (k | k)
    · exact hSO k
    · exact hSS k
    · exact hST
  have hflow (k : K) : HEq (S (q k)) (S0 k) :=
    congr_arg_heq S0 (q.symm_apply_apply k)
  have hlast : q (.inr (.inr 0)) = Fin.last (2 * N + 1) :=
    (interleavedPieceEquiv_values N).2.2
  have hlastLeft : (Fin.last (2 * N + 1)).castSucc =
      (⟨2 * N + 1, by omega⟩ : Fin (2 * N + 3)) := rfl
  have hlastRight : (Fin.last (2 * N + 1)).succ = Fin.last (2 * N + 2) := rfl
  refine ⟨fun i => hS0 _, fun k => hflow (.inl k),
    fun k => hflow (.inr (.inl k)), ?_, ?_⟩
  · exact (congr_arg_heq S hlast.symm).trans (hflow (.inr (.inr 0)))
  intro f g
  have hg (i : Fin (2 * N + 2)) : g (q.symm i) = f i :=
    Equiv.piCongrLeft'_symm_apply_apply _ _ _ _
  refine ⟨fun i z r => congrFun (hg i).symm (z, r), ?_, ?_, ?_⟩
  · intro hf
    have hgSmooth (k : K) :
        ContMDiff (𝓘(ℝ, P).prod 𝓘(ℝ, ℝ)) ThreeModel (8 : ℕ) (g k) := by
      obtain ⟨i, rfl⟩ := q.symm.surjective k
      rw [hg]
      exact hf i
    exact ⟨fun k => hgSmooth (.inl k), fun k => hgSmooth (.inr (.inl k)),
      hgSmooth (.inr (.inr 0))⟩
  · intro hf
    have hgCenter (k : K) (r : ℝ)
        (hr : r ∈ Icc (s (q k).castSucc) (s (q k).succ)) :
        (fun t => g k (0, t)) =ᶠ[𝓝 r] alpha0 k := by
      obtain ⟨i, rfl⟩ := q.symm.surjective k
      rw [hg]
      exact hf i r (by simpa only [q.apply_symm_apply] using hr)
    refine ⟨fun k r hr => hgCenter (.inl k) r hr,
      fun k r hr => hgCenter (.inr (.inl k)) r hr, ?_⟩
    intro r hr
    exact hgCenter (.inr (.inr 0)) r (by simpa only [hlast, hlastLeft, hlastRight] using hr)
  · intro z w
    classical
    let upperW (i : Fin (2 * N + 2)) : ℝ :=
      if i = Fin.last (2 * N + 1) then w else s i.succ
    have hupperCast (i : Fin (2 * N + 1)) : upperW i.castSucc = s i.castSucc.succ := by
      apply ite_eq_right
      intro he
      have hval := congrArg Fin.val he
      have hi := i.isLt
      dsimp only [Fin.val_castSucc, Fin.val_last] at hval
      omega
    have hupperLast : upperW (Fin.last (2 * N + 1)) = w := ite_eq_left rfl
    have hwhole : finiteJointAction S T f (fun i => s i.castSucc) (fun i => s i.succ) (z, w) =
        ∑ i : Fin (2 * N + 2), lRegularizedAction (S i) T (fun r => f i (z, r))
          (s i.castSucc) (upperW i) := by
      have hsum := Fin.sum_univ_castSucc (fun i : Fin (2 * N + 2) =>
        lRegularizedAction (S i) T (fun r => f i (z, r)) (s i.castSucc) (upperW i))
      simpa only [finiteJointAction, hupperCast, hupperLast] using hsum.symm
    let A : K → ℝ := fun k => lRegularizedAction (S0 k) T (fun r => g k (z, r))
      (s (q k).castSucc) (upperW (q k))
    have heq : (∑ i : Fin (2 * N + 2), lRegularizedAction (S i) T (fun r => f i (z, r))
        (s i.castSucc) (upperW i)) = ∑ k, A k := by
      rw [← q.symm.sum_comp A]
      apply Finset.sum_congr rfl
      intro i _
      simp only [A, q.apply_symm_apply, hg]
      rfl
    have hnotO (k : Fin (N + 1)) : q (.inl k) ≠ Fin.last (2 * N + 1) := by
      intro h
      have hh : (.inl k : K) = .inr (.inr 0) := q.injective (h.trans hlast.symm)
      cases hh
    have hnotS (k : Fin N) : q (.inr (.inl k)) ≠ Fin.last (2 * N + 1) := by
      intro h
      have hh : (.inr (.inl k) : K) = .inr (.inr 0) := q.injective (h.trans hlast.symm)
      cases hh
    have hupperO (k : Fin (N + 1)) : upperW (q (.inl k)) = s (q (.inl k)).succ :=
      ite_eq_right (hnotO k)
    have hupperS (k : Fin N) : upperW (q (.inr (.inl k))) = s (q (.inr (.inl k))).succ :=
      ite_eq_right (hnotS k)
    have hupperTail : upperW (q (.inr (.inr 0))) = w := by
      rw [hlast]
      exact hupperLast
    have hlowerTail : s (q (.inr (.inr 0))).castSucc =
        s (⟨2 * N + 1, by omega⟩ : Fin (2 * N + 3)) := by
      rw [hlast, hlastLeft]
    have hAO (k : Fin (N + 1)) : A (.inl k) =
        lRegularizedAction (SO k) T (fun r => g (.inl k) (z, r))
          (s (q (.inl k)).castSucc) (s (q (.inl k)).succ) := by
      dsimp only [A, S0, M0, D0, ActualPieceCarrier, actualPieceTop,
        actualPieceChart, actualPieceManifold]
      rw [hupperO]
      rfl
    have hAS (k : Fin N) : A (.inr (.inl k)) =
        lRegularizedAction (SS k) T (fun r => g (.inr (.inl k)) (z, r))
          (s (q (.inr (.inl k))).castSucc) (s (q (.inr (.inl k))).succ) := by
      dsimp only [A, S0, M0, D0, ActualPieceCarrier, actualPieceTop,
        actualPieceChart, actualPieceManifold]
      rw [hupperS]
      rfl
    have hAT : A (.inr (.inr 0)) =
        lRegularizedAction ST T (fun r => g (.inr (.inr 0)) (z, r))
          (s (⟨2 * N + 1, by omega⟩ : Fin (2 * N + 3))) w := by
      dsimp only [A, S0, M0, D0, ActualPieceCarrier, actualPieceTop,
        actualPieceChart, actualPieceManifold]
      rw [hupperTail, hlowerTail]
      rfl
    have hsplit := (hwhole.trans heq).trans (Fintype.sum_sum_type A)
    simpa only [Fintype.sum_sum_type, Fin.sum_univ_one, hAO, hAS, hAT,
      ← add_assoc] using hsplit

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
