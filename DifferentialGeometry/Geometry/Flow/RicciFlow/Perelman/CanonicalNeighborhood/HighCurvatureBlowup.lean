import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.HighCurvatureModelApproximation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedModelLimit

set_option autoImplicit false
noncomputable section
open Filter Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]

theorem arbitrary_high_curvature_blowup [CompactSpace M] [ConnectedSpace M]
    [T2Space (TangentBundle I3 M)] {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (o : TangentOrientationSection M) :
    ∃ kappa : ℝ, 0 < kappa ∧ ∀ (x : ℕ → M) (t : ℕ → ℝ),
      (∀ i, t i ∈ Set.Ico 0 T) →
      Filter.Tendsto (fun i => S.scalar (t i) (x i)) Filter.atTop Filter.atTop →
        Nonempty (BlowupLimit S o kappa x t) := by
  classical
  obtain ⟨kappa, hkappa, hmodels⟩ := exists_high_curvature_model_approximations hT S hS o
  refine ⟨kappa, hkappa, ?_⟩
  intro x t ht hscalar
  let epsilon : ℕ → ℝ := fun n => ((n : ℝ) + 2)⁻¹
  have hepsilon : ∀ n, epsilon n ∈ Ioo (0 : ℝ) 1 := by
    intro n
    have hn : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    exact ⟨inv_pos.mpr hn, (inv_lt_one₀ hn).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])⟩
  have hepszero : Tendsto epsilon atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop)
  obtain ⟨phi, hphi, hW⟩ := hmodels x t ht hscalar epsilon hepsilon
  let W : ∀ i, WindowedModelWitness (epsilon i) kappa S (x (phi i)) (t (phi i)) :=
    fun i => (hW i).choose
  have hregular : interior (RealTimeInterval.closedOpen 0 T hT).carrier ⊆
      (RealTimeInterval.closedOpen 0 T hT).regular := by
    simp only [RealTimeInterval.closedOpen, interior_Ico]
    exact subset_rfl
  obtain ⟨L⟩ := WindowedModelWitness.exists_blowup_limit hS o W hepszero hregular
  exact ⟨L.ofSubsequence phi hphi⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
