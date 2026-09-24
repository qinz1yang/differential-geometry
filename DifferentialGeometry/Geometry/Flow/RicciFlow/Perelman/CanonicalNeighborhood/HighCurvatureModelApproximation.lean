import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.HighCurvatureModelBounds

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open Filter Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold ContDiff _root_.Topology

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
  [T2Space (TangentBundle I3 M)]

theorem exists_high_curvature_model_approximations
    {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (o : TangentOrientationSection M) :
    ∃ kappa : ℝ, 0 < kappa ∧ ∀ (x : ℕ → M) (t : ℕ → ℝ),
      (∀ i, t i ∈ Ico 0 T) →
      Tendsto (fun i => S.scalar (t i) (x i)) atTop atTop →
      ∀ epsilon : ℕ → ℝ, (∀ i, epsilon i ∈ Ioo (0 : ℝ) 1) →
        ∃ phi : ℕ → ℕ, StrictMono phi ∧
          ∀ i, OrientedWitness S o (epsilon i) kappa (x (phi i)) (t (phi i)) := by
  classical
  obtain ⟨kappa, hkappa, hmodels⟩ := closed_flow_models hT S hS o
  refine ⟨kappa, hkappa, ?_⟩
  intro x t ht hscalar epsilon hepsilon
  have heventually : ∀ n, ∃ N, ∀ i ≥ N,
      OrientedWitness S o (epsilon n) kappa (x i) (t i) := by
    intro n
    obtain ⟨Q, _hQ, hQmodels⟩ := hmodels (epsilon n) (hepsilon n).1 (hepsilon n).2
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hscalar.eventually_ge_atTop Q)
    exact ⟨N, fun i hi => hQmodels (x i) (t i) (ht i) (hN i hi)⟩
  choose N hN using heventually
  let phi : ℕ → ℕ := Nat.rec (N 0) (fun n j => max (j + 1) (N (n + 1)))
  have hphi : StrictMono phi := strictMono_nat_of_lt_succ fun n =>
    (Nat.lt_succ_self (phi n)).trans_le (le_max_left _ _)
  have hge : ∀ n, N n ≤ phi n := by
    intro n
    cases n with
    | zero => exact le_rfl
    | succ n => exact le_max_right _ _
  exact ⟨phi, hphi, fun n => hN n (phi n) (hge n)⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
