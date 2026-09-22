import DifferentialGeometry.Analysis.ODE.QuadraticCrossing
import DifferentialGeometry.Topology.Order.IntermediateValue
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedGoodPointBounds

set_option autoImplicit false

open Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

universe u

theorem exists_scalar_crossing_time_lower_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
        {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D},
        IsSolutionOn S → ∀ {a b A B : ℝ}, a ≤ b → 0 < A → A < B →
        Icc a b ⊆ D.carrier → ∀ x : M,
        S.scalar a x ≤ A → B ≤ S.scalar b x →
        (∀ t ∈ Ioo a b, A < S.scalar t x →
          ∃ eps kappa : ℝ, eps ≤ 1 / 4 ∧
            Nonempty (WindowedModelWitness eps kappa S x t) ∧
            Ioo (t - (eps * S.scalar t x)⁻¹) t ⊆ D.regular) →
        (A⁻¹ - B⁻¹) / C ≤ b - a := by
  obtain ⟨C, hC, hbound⟩ := exists_windowedModelWitness_scalar_derivative_bounds.{u}
  refine ⟨C, hC, ?_⟩
  intro M _ _ _ _ _ D S hS a b A B hab hA hAB hslab x ha hb hcover
  apply (div_le_iff₀ hC).mpr
  rw [mul_comm (b - a) C]
  refine DifferentialGeometry.Analysis.ODE.inv_sub_inv_le_mul_sub_of_deriv_le_sq
    (f := fun t => S.scalar t x) hab hA hAB ?_ ha hb ?_
  · intro t ht
    exact (hS.scalarTime ht hslab x).continuousWithinAt
  · intro t ht hhigh
    have hd : DifferentiableAt ℝ (fun s => S.scalar s x) t :=
      (hS.scalarTime (K := Icc a b) ⟨ht.1.le, ht.2.le⟩ hslab x).differentiableAt
        (Icc_mem_nhds ht.1 ht.2)
    obtain ⟨eps, kappa, heps, ⟨W⟩, hwindow⟩ := hcover t ht hhigh
    have hleft := (hbound hS W heps hwindow).2
    rw [hd.hasDerivAt.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Iic t)] at hleft
    exact ⟨hd, (le_abs_self _).trans hleft⟩

theorem exists_scalar_first_crossing_time_lower_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] [CompactSpace M]
        {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D},
        IsSolutionOn S → ∀ {a b A B : ℝ}, a ≤ b → 0 < A → A < B →
        Icc a b ⊆ D.carrier →
        (∀ x : M, S.scalar a x ≤ A) → (∃ x : M, B ≤ S.scalar b x) →
        (∀ t ∈ Ioo a b, ∀ x : M, A < S.scalar t x →
          ∃ eps kappa : ℝ, eps ≤ 1 / 4 ∧
            Nonempty (WindowedModelWitness eps kappa S x t) ∧
            Ioo (t - (eps * S.scalar t x)⁻¹) t ⊆ D.regular) →
        ∃ t ∈ Ioc a b, ∃ x : M, S.scalar t x = B ∧
          (∀ s ∈ Ico a t, ∀ y : M, S.scalar s y < B) ∧
          (∀ y : M, S.scalar t y ≤ B) ∧
          (A⁻¹ - B⁻¹) / C ≤ t - a := by
  obtain ⟨C, hC, helapsed⟩ := exists_scalar_crossing_time_lower_bound.{u}
  refine ⟨C, hC, ?_⟩
  intro M _ _ _ _ _ D S hS a b A B hab hA hAB hslab hreset hhit hcover
  have hcont : ContinuousOn (fun p : ℝ × M => S.scalar p.1 p.2)
      (Icc a b ×ˢ univ) :=
    hS.scalarCont.mono (Set.prod_mono hslab subset_rfl)
  obtain ⟨t, ht, x, heq, hbefore, hlevel⟩ :=
    hcont.exists_first_level_of_compact hab (fun x => (hreset x).trans_lt hAB) hhit
  refine ⟨t, ht, x, heq, hbefore, hlevel, ?_⟩
  exact helapsed hS ht.1.le hA hAB ((Icc_subset_Icc le_rfl ht.2).trans hslab)
    x (hreset x) heq.symm.le
    (fun s hs hhigh => hcover s ⟨hs.1, hs.2.trans_le ht.2⟩ x hhigh)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
