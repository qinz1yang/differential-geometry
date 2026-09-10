import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Logic.Function.Iterate

set_option autoImplicit false

open Filter Set
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

theorem exists_metric_separated_subsequence
    {X : Type*} [MetricSpace X] {x : ℕ → X} (p : X)
    (hescape : Tendsto (fun i => dist p (x i)) atTop atTop)
    (R : ℝ) (hR : 0 < R) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧
      ∀ i j : ℕ, i < j → R < dist (x (phi i)) (x (phi j)) := by
  classical
  have hstep (i : ℕ) : ∃ j : ℕ, i < j ∧ dist p (x i) + R < dist p (x j) := by
    have hevent : ∀ᶠ j in atTop, i < j ∧ dist p (x i) + R < dist p (x j) :=
      (eventually_gt_atTop i).and (hescape.eventually_gt_atTop (dist p (x i) + R))
    exact hevent.exists
  choose next hindex hradial using hstep
  let phi : ℕ → ℕ := fun n => (next^[n]) 0
  have hsucc (n : ℕ) : phi (n + 1) = next (phi n) := Function.iterate_succ_apply' next n 0
  have hphi : StrictMono phi := by
    apply strictMono_nat_of_lt_succ
    intro n
    rw [hsucc]
    exact hindex (phi n)
  have hrad (n : ℕ) : dist p (x (phi n)) + R < dist p (x (phi (n + 1))) := by
    rw [hsucc]
    exact hradial (phi n)
  have hmono : StrictMono (fun n => dist p (x (phi n))) := by
    apply strictMono_nat_of_lt_succ
    intro n
    have hh := hrad n
    linarith
  refine ⟨phi, hphi, ?_⟩
  intro i j hij
  have hle := hmono.monotone (Nat.succ_le_iff.mpr hij)
  have hi := hrad i
  have htriangle := dist_triangle p (x (phi i)) (x (phi j))
  linarith

theorem exists_disjoint_closedBall_subsequence
    {X : Type*} [MetricSpace X] {x : ℕ → X} (p : X)
    (hescape : Tendsto (fun i => dist p (x i)) atTop atTop)
    (r : ℝ) (hr : 0 < r) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧
      Pairwise (fun i j : ℕ => Disjoint (Metric.closedBall (x (phi i)) r)
        (Metric.closedBall (x (phi j)) r)) := by
  obtain ⟨phi, hphi, hsep⟩ := exists_metric_separated_subsequence p hescape (2 * r) (by positivity)
  refine ⟨phi, hphi, ?_⟩
  intro i j hij
  have hfar : 2 * r < dist (x (phi i)) (x (phi j)) := by
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact hsep i j hlt
    · simpa only [dist_comm] using hsep j i hgt
  apply Set.disjoint_left.mpr
  intro q hqi hqj
  have hqi' : dist (x (phi i)) q ≤ r := by
    simpa only [Metric.mem_closedBall, dist_comm] using hqi
  have hqj' : dist q (x (phi j)) ≤ r := hqj
  have htriangle := dist_triangle (x (phi i)) q (x (phi j))
  linarith

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
