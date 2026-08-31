import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.ChartPartition.AccelerationAtNodes

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter Set
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
variable {D : RealTimeInterval}

private theorem has_fin_seg
    {m : Nat} (hm : 0 < m) (t : Fin (m + 1) → Real)
    (ht : Monotone t) {a b s : Real} (ht0 : t 0 = a)
    (htlast : t (Fin.last m) = b) (hs : s ∈ Icc a b) :
    ∃ i : Fin m, s ∈ Icc (t i.castSucc) (t i.succ) := by
  let P : Nat → Prop := fun k ↦ ∃ hk : k < m + 1, s ≤ t ⟨k, hk⟩
  have hP : ∃ k, P k := by
    refine ⟨m, Nat.lt_succ_self m, ?_⟩
    have hlast : t ⟨m, Nat.lt_succ_self m⟩ = b := by
      simpa only [Fin.last] using htlast
    simpa only [hlast] using hs.2
  let k := Nat.find hP
  rcases Nat.find_spec hP with ⟨hklt, hks⟩
  by_cases hk0 : k = 0
  · let i : Fin m := ⟨0, hm⟩
    refine ⟨i, ?_⟩
    have hsa : s = a := by
      apply le_antisymm
      · have hidx : (⟨k, hklt⟩ : Fin (m + 1)) = 0 := by
          ext
          exact hk0
        rw [hidx, ht0] at hks
        exact hks
      · exact hs.1
    subst s
    constructor
    · have hidx : i.castSucc = (0 : Fin (m + 1)) := by ext; rfl
      rw [hidx, ht0]
    · rw [← ht0]
      exact ht (Fin.zero_le _)
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
    let i : Fin m := ⟨k - 1, by omega⟩
    have hprev : ¬ P (k - 1) := Nat.find_min hP (by omega)
    refine ⟨i, ?_⟩
    constructor
    · have hnot : ¬ s ≤ t ⟨k - 1, by omega⟩ := by
        intro hle
        exact hprev ⟨by omega, hle⟩
      exact le_of_lt (lt_of_not_ge hnot)
    · have hidx : i.succ = (⟨k, hklt⟩ : Fin (m + 1)) := by
        ext
        change k - 1 + 1 = k
        omega
      rw [hidx]
      exact hks

omit [CompactSpace M] in
theorem lRegAction_minimizer_differentiable_and_acceleration_eq_on_interior
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (T a b : Real) {m : Nat} (t : Fin (m + 1) → Real)
    (ht : StrictMono t) (ht0 : t 0 = a)
    (htlast : t (Fin.last m) = b)
    (p : Fin m → M) (gamma : Real → M) (hgamma : Continuous gamma)
    (u : (i : Fin m) → timeH1 E (partitionIntervalLength t i))
    (hsrc : ∀ i, MapsTo gamma
      (Icc (t i.castSucc) (t i.succ)) (chartAt H (p i)).source)
    (hrep : ∀ i, EqOn (u i).toFun
      (fun r ↦ extChartAt I (p i) (gamma (t i.castSucc + r)))
      (Icc (0 : Real) (partitionIntervalLength t i)))
    (hreg : ∀ s ∈ Icc a b, T - s ^ 2 ∈ D.regular)
    (hmin : ∀ delta : Real → M,
      ContMDiff (modelWithCornersSelf Real Real) I 1 delta →
      delta a = gamma a → delta b = gamma b →
      lRegAction S T gamma a b ≤ lRegAction S T delta a b) :
    ∀ s ∈ Ioo a b,
      MDifferentiableAt (modelWithCornersSelf Real Real) I gamma s ∧
      DifferentiableAt Real
        (chartRepAt (I := I) gamma
          (fun r ↦ lVelocity (I := I) gamma r) s) s ∧
      covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) gamma
          (fun r ↦ lVelocity (I := I) gamma r) s =
        lRegAccel S T s (gamma s) (lVelocity (I := I) gamma s) := by
  classical
  intro s hs
  cases m with
  | zero =>
      have hab : a = b := ht0.symm.trans
        ((congrArg t (Fin.ext (by simp))).trans htlast)
      exfalso
      rw [hab] at hs
      exact (hs.1.trans hs.2).false
  | succ n =>
      obtain ⟨i, hi⟩ := has_fin_seg (Nat.succ_pos n) t ht.monotone
        ht0 htlast ⟨hs.1.le, hs.2.le⟩
      by_cases hleft : s = t i.castSucc
      · have hi0 : i ≠ 0 := by
          intro hi0
          subst i
          have hzero : (0 : Fin (n + 1)).castSucc =
              (0 : Fin (n + 2)) := by ext; rfl
          rw [hzero, ht0] at hleft
          exact hs.1.ne hleft.symm
        obtain ⟨q, hq⟩ := Fin.exists_succ_eq.mpr hi0
        cases n with
        | zero => exact Fin.elim0 q
        | succ n =>
            have hsnode : s = t q.succ.castSucc := by
              rw [hleft, ← hq]
            rw [hsnode]
            exact lRegAction_minimizer_acceleration_eq_at_partition_nodes (I := I) S hS T a b t ht ht0 htlast p
              gamma hgamma u hsrc hrep hreg hmin q
      · by_cases hright : s = t i.succ
        · have hilast : i ≠ Fin.last n := by
            intro hilast
            subst i
            have hidx : (Fin.last n).succ = Fin.last (n + 1) := by ext; simp
            rw [hidx, htlast] at hright
            exact hs.2.ne hright
          obtain ⟨q, hq⟩ := Fin.exists_castSucc_eq.mpr hilast
          cases n with
          | zero => exact Fin.elim0 q
          | succ n =>
              have hsnode : s = t q.succ.castSucc := by
                rw [hright]
                congr 1
                apply Fin.ext
                have hv := congrArg Fin.val hq
                simp only [Fin.val_castSucc] at hv
                simp only [Fin.val_succ, Fin.val_castSucc]
                omega
              rw [hsnode]
              exact lRegAction_minimizer_acceleration_eq_at_partition_nodes (I := I) S hS T a b t ht ht0 htlast p
                gamma hgamma u hsrc hrep hreg hmin q
        · have hsopen : s ∈ Ioo (t i.castSucc) (t i.succ) :=
            ⟨lt_of_le_of_ne hi.1 (Ne.symm hleft),
              lt_of_le_of_ne hi.2 hright⟩
          have hgamma2 := lRegAction_minimizer_contMDiffAt_two_of_mem_chart_piece_interior (I := I) S hS T a b t ht ht0
            htlast p gamma hgamma u hsrc hrep hreg hmin i s hsopen
          exact ⟨hgamma2.mdifferentiableAt (by norm_num),
            DifferentialGeometry.Geometry.Riemannian.MFDerivAlongCurve.velocity_coord_diff
              (I := I) gamma s hgamma2,
            lRegAction_minimizer_acceleration_eq_on_chart_piece_interior (I := I) S hS T a b t ht ht0 htlast p
              gamma hgamma u hsrc hrep hreg hmin i s hsopen⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
