import DifferentialGeometry.Analysis.Parabolic.Bernstein.FirstOrder
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.Derivatives.Regularity.Norm
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.Derivatives.Evolution.SolutionHeatEquation

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Filter Set
open Geometry.Curvature Geometry.Operator Analysis.Parabolic
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [BoundarylessManifold I M]

theorem nablaRm_normSq_cutoff_le
    {D : RealTimeInterval} {S : SolutionOn (I := I) (M := M) D}
    (hS : IsSolutionOn S) {T ε K α : ℝ}
    (cut : ParabolicCutoff (flowG S) T ε)
    (hreg : Icc 0 T ⊆ D.regular)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hTK : T * K ≤ α) (hsmall : 34 * ε * T ≤ 1 / 2)
    (hRm : ∀ t ∈ Icc 0 T, ∀ x, 0 < cut.chi t x →
      nablaKRm04NormSqIntrinsic S 0 t x ≤ K ^ 2) :
    let c := max (rmTowerCost (Module.finrank ℝ E) 0) (rmTowerCost (Module.finrank ℝ E) 1)
    ∀ t ∈ Icc 0 T, ∀ x,
      t * cut.chi t x ^ 2 * nablaKRm04NormSqIntrinsic S 1 t x ≤
        (1 + 2 * c * α) * (1 + c * α) * K ^ 2 +
          9 * ε * (1 + 2 * c * α) * K ^ 2 * t := by
  by_cases hT : 0 < T
  · let : IsManifold I 1 M := IsManifold.of_le
      (I := I) (M := M) (n := ((⊤ : ℕ∞) : WithTop ℕ∞))
      (WithTop.coe_le_coe.2 (le_top : (1 : ℕ∞) ≤ (⊤ : ℕ∞)))
    let : IsManifold I 2 M := IsManifold.of_le
      (I := I) (M := M) (n := ((⊤ : ℕ∞) : WithTop ℕ∞))
      (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞)))
    let c := max (rmTowerCost (Module.finrank ℝ E) 0) (rmTowerCost (Module.finrank ℝ E) 1)
    have hc : 0 ≤ c := (rmTowerCost_nonneg _ 0).trans (le_max_left _ _)
    have hw_cont : ∀ k ≤ 1,
        ContinuousOn
          (fun p : ℝ × M => nablaKRm04NormSqIntrinsic S k p.1 p.2)
          (spacetimeSlab (M := M) T) := by
      intro k _ p hp
      obtain ⟨a, b, hab, hsub⟩ := D.exists_Icc_regular (hreg hp.1)
      let Dco := RealTimeInterval.closedOpen a b (hab.1.trans hab.2)
      let Sco : SolutionOn (I := I) (M := M) Dco := S.timeRestrict Dco
      have hSco : IsSolutionOn Sco := by
        apply isSolutionOn_timeRestrict hS
        · exact fun q hq => D.regular_subset (hsub ⟨hq.1, hq.2.le⟩)
        · exact fun q hq => hsub ⟨hq.1.le, hq.2.le⟩
      have hfun :
          (fun q : ℝ × M => nablaKRm04NormSqIntrinsic S k q.1 q.2) =
            (fun q : ℝ × M => nablaKRm04NormSqIntrinsic Sco k q.1 q.2) := by
        funext q
        unfold nablaKRm04NormSqIntrinsic
        rw [nablaKRm04Field_eq_of_metric_eq
          (S₁ := S) (S₂ := Sco) (t₁ := q.1) (t₂ := q.1) rfl k]
        rfl
      rw [hfun]
      exact ((towerNorm_joint hSco k).continuousOn.continuousAt
        ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨hab, mem_univ _⟩)).continuousWithinAt
    let w := nablaKRm04NormSqIntrinsic S
    have hheat (k : ℕ) (hk : k ≤ 1) :
        TowerHeatBoundOn (D := D) w (nablaKNormLap S) c k := by
      apply TowerHeatBoundOn.mono_cost (h := towerHeatBoundOn_of_solution S hS k)
      rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
      · exact le_max_left _ _
      · exact le_max_right _ _
    have hdata (k : ℕ) (hk : k ≤ 1) (t : ℝ) (ht : t ∈ Icc 0 T)
        (htpos : 0 < t) (x : M) :
        DifferentiableWithinAt ℝ (fun s => w k s x) (Icc 0 T) t ∧
        parabolicOperatorWithDrift (flowG S) T (fun _ y => (0 : TangentSpace I y))
          (w k) t x ≤ -2 * w (k + 1) t x + towerReactionSum w c k t x := by
      let tau : RealTimeInterval.RegularTime D := ⟨t, hreg ht⟩
      obtain ⟨d, hd, hle⟩ := hheat k hk tau x
      have hd' : HasDerivWithinAt (fun s : ℝ => w k s x) d (Icc 0 T) t :=
        hd.mono (fun s hs => D.regular_subset (hreg hs))
      refine ⟨hd'.differentiableWithinAt, ?_⟩
      have hLap : heatOperatorWithDrift (flowG S) t
          (fun y => (0 : TangentSpace I y)) (w k t) x = nablaKNormLap S k t x := by
        rw [heatOperatorWithDrift_zero_drift, heatOperator_eq_laplacianAt, laplacianAt_eq]
        rfl
      rw [parabolicOperatorWithDrift_eq, hd'.derivWithin
        ((uniqueDiffOn_Icc hT).uniqueDiffWithinAt ht), hLap]
      change d ≤ nablaKNormLap S k t x +
        (-2 * w (k + 1) t x + towerReactionSum w c k t x) at hle
      linarith
    have hn (k : ℕ) (t : ℝ) (x : M) : 0 ≤ w k t x :=
      nablaKRm04NormSqIntrinsic_nonneg S k t x
    have hP0 (t : ℝ) (ht : t ∈ Icc 0 T) (htpos : 0 < t) (x : M) :
        parabolicOperatorWithDrift (flowG S) T (fun _ y => (0 : TangentSpace I y)) (w 0) t x ≤
          -2 * w 1 t x + c * w 0 t x * Real.sqrt (w 0 t x) := by
      have h := (hdata 0 (by norm_num) t ht htpos x).2
      have heq : towerReactionSum w c 0 t x = c * w 0 t x * Real.sqrt (w 0 t x) := by
        simp only [towerReactionSum, Nat.zero_add, Finset.sum_range_one, Nat.sub_self]
        calc
          c * Real.sqrt (w 0 t x) * Real.sqrt (w 0 t x) * Real.sqrt (w 0 t x) =
              c * (Real.sqrt (w 0 t x) * Real.sqrt (w 0 t x)) * Real.sqrt (w 0 t x) := by ring
          _ = _ := by rw [Real.mul_self_sqrt (hn 0 t x)]
      simpa only [heq, Nat.zero_add] using h
    have hP1 (t : ℝ) (ht : t ∈ Icc 0 T) (htpos : 0 < t) (x : M) :
        parabolicOperatorWithDrift (flowG S) T (fun _ y => (0 : TangentSpace I y)) (w 1) t x ≤
          -2 * w 2 t x + 2 * c * Real.sqrt (w 0 t x) * w 1 t x := by
      have h := (hdata 1 le_rfl t ht htpos x).2
      have heq : towerReactionSum w c 1 t x = 2 * c * Real.sqrt (w 0 t x) * w 1 t x := by
        simp only [towerReactionSum, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
          Nat.sub_zero, Nat.sub_self]
        calc
          c * Real.sqrt (w 0 t x) * Real.sqrt (w 1 t x) * Real.sqrt (w 1 t x) +
              c * Real.sqrt (w 1 t x) * Real.sqrt (w 0 t x) * Real.sqrt (w 1 t x) =
              2 * c * Real.sqrt (w 0 t x) * (Real.sqrt (w 1 t x) * Real.sqrt (w 1 t x)) := by ring
          _ = _ := by rw [Real.mul_self_sqrt (hn 1 t x)]
      simpa only [heq, Nat.reduceAdd] using h
    exact ParabolicCutoff.bernstein_first_order_estimate cut (w 0) (w 1) (w 2) c K α
      hc hK hα hTK hsmall
      (fun t _ x => hn 0 t x) (fun t _ x => hn 1 t x) (fun t _ x => hn 2 t x) hRm
      ((hw_cont 0 (by omega)).mono (fun _ hp => ⟨hp.1, mem_univ _⟩))
      ((hw_cont 1 le_rfl).mono (fun _ hp => ⟨hp.1, mem_univ _⟩))
      (fun t ht htpos x => (hdata 0 (by omega) t ht htpos x).1)
      (fun t ht htpos x => (hdata 1 le_rfl t ht htpos x).1)
      (fun t _ _ x => (nablaKNorm_smooth S t 0).contMDiffAt.mdifferentiableAt (by simp))
      (fun t _ _ x => (nablaKNorm_smooth S t 1).contMDiffAt.mdifferentiableAt (by simp))
      (fun t _ _ x => gradientFun_mdiffAt (S.base.metric t) (nablaKNorm_smooth S t 0) x)
      (fun t _ _ x => gradientFun_mdiffAt (S.base.metric t) (nablaKNorm_smooth S t 1) x)
      hP0 hP1
      (fun t _ _ x => towerNorm_grad_le S 0 t x)
      (fun t _ _ x => towerNorm_grad_le S 1 t x)
  · dsimp only
    intro t ht x
    have ht0 : t = 0 := le_antisymm (ht.2.trans (le_of_not_gt hT)) ht.1
    rw [ht0]
    simp only [zero_mul, mul_zero, add_zero]
    have hc : 0 ≤ max (rmTowerCost (Module.finrank ℝ E) 0)
        (rmTowerCost (Module.finrank ℝ E) 1) :=
      (rmTowerCost_nonneg _ 0).trans (le_max_left _ _)
    positivity

end DifferentialGeometry.PDE.RicciFlow
