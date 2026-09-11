import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornGeometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.BadPointSelection

set_option autoImplicit false
noncomputable section
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] {D : RealTimeInterval}

private theorem exists_bad_point_of_floor_weight
    (S : SolutionOn (I := I3) (M := M) D) (o : TangentOrientationSection M)
    {eps kappa T K depth : ℝ} (hdepth : 0 ≤ depth)
    (hK : ∀ y s, s ∈ Set.Icc (0 : ℝ) T → S.scalar s y ≤ K) :
    ∀ n : ℕ, ∀ y s, ⌊K / S.scalar s y⌋₊ = n →
      (¬ OrientedWitness S o eps kappa y s) →
      0 < S.scalar s y → s ≤ T → 0 ≤ s - 2 * depth / S.scalar s y →
      ∃ x t, (¬ OrientedWitness S o eps kappa x t) ∧ 0 < S.scalar t x ∧
        S.scalar s y ≤ S.scalar t x ∧ t ≤ s ∧
        s - 2 * depth / S.scalar s y ≤ t - depth / S.scalar t x ∧
        ∀ y' s', s' ∈ Set.Icc (t - depth / S.scalar t x) t →
          2 * S.scalar t x ≤ S.scalar s' y' → OrientedWitness S o eps kappa y' s' := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro y s hn hbad hR hsT hs0
    have hnn : 0 ≤ depth / S.scalar s y := div_nonneg hdepth hR.le
    have hdouble : 2 * depth / S.scalar s y = 2 * (depth / S.scalar s y) := by ring
    by_cases hex : ∃ y' s', s' ∈ Set.Icc (s - depth / S.scalar s y) s ∧
        2 * S.scalar s y ≤ S.scalar s' y' ∧ ¬ OrientedWitness S o eps kappa y' s'
    · obtain ⟨y', s', hs'mem, hR2, hbad'⟩ := hex
      have hR' : 0 < S.scalar s' y' := lt_of_lt_of_le (by linarith) hR2
      have hnn' : 0 ≤ 2 * depth / S.scalar s' y' := div_nonneg (by linarith) hR'.le
      have hhalf : 2 * depth / S.scalar s' y' ≤ depth / S.scalar s y := by
        have h1 : 2 * depth / S.scalar s' y' ≤ 2 * depth / (2 * S.scalar s y) :=
          div_le_div_of_nonneg_left (by linarith) (by linarith) hR2
        rwa [mul_div_mul_left depth (S.scalar s y) (by norm_num : (2 : ℝ) ≠ 0)] at h1
      have hchain : s - 2 * depth / S.scalar s y ≤ s' - 2 * depth / S.scalar s' y' := by
        have h1 := hs'mem.1
        linarith
      have hs'0 : 0 ≤ s' - 2 * depth / S.scalar s' y' := hs0.trans hchain
      have hs'T : s' ≤ T := hs'mem.2.trans hsT
      have hKbound : S.scalar s' y' ≤ K := hK y' s' ⟨by linarith, hs'T⟩
      have hlt : ⌊K / S.scalar s' y'⌋₊ < ⌊K / S.scalar s y⌋₊ :=
        floor_div_lt_floor_div_of_two_mul_le hR hR2 hKbound
      rw [hn] at hlt
      obtain ⟨x, t, hbadx, hRx, hRle, htle, hwin, hgood⟩ :=
        ih _ hlt y' s' rfl hbad' hR' hs'T hs'0
      exact ⟨x, t, hbadx, hRx, by linarith, htle.trans hs'mem.2, by linarith, hgood⟩
    · refine ⟨y, s, hbad, hR, le_rfl, le_rfl, by linarith, ?_⟩
      intro y' s' hs' hRy'
      by_contra hcon
      exact hex ⟨y', s', hs', hRy', hcon⟩

theorem exists_closed_window_bad_point
    (S : SolutionOn (I := I3) (M := M) D) (o : TangentOrientationSection M)
    {eps kappa T K depth : ℝ} (hdepth : 0 ≤ depth)
    (hwindow : Set.Icc 0 T ⊆ D.carrier)
    (hK : ∀ y s, s ∈ Set.Icc 0 T → S.scalar s y ≤ K)
    {xhat : M} {that : ℝ} (hthat : 1 ≤ that) (hthatT : that ≤ T)
    (hQhat : 0 < S.scalar that xhat) (hdepthQ : depth ≤ S.scalar that xhat / 4)
    (hbad : ¬ OrientedWitness S o eps kappa xhat that) :
    ∃ x t, ¬ OrientedWitness S o eps kappa x t ∧
      S.scalar that xhat ≤ S.scalar t x ∧ t ∈ Set.Icc (1 / 2) that ∧
      depth / S.scalar t x ≤ 1 / 4 ∧
      Set.Icc (t - depth / S.scalar t x) t ⊆ D.carrier ∧
      ∀ y s, s ∈ Set.Icc (t - depth / S.scalar t x) t →
        2 * S.scalar t x ≤ S.scalar s y → OrientedWitness S o eps kappa y s := by
  have hhalf : 2 * depth / S.scalar that xhat ≤ 1 / 2 := by
    rw [div_le_iff₀ hQhat]
    linarith
  have hs0 : 0 ≤ that - 2 * depth / S.scalar that xhat := by linarith
  obtain ⟨x, t, hbadx, hRx, hRle, htle, hwin, hgood⟩ :=
    exists_bad_point_of_floor_weight S o hdepth hK _ xhat that rfl hbad hQhat hthatT hs0
  have hdepthRx : 0 ≤ depth / S.scalar t x := div_nonneg hdepth hRx.le
  have hratio : depth / S.scalar t x ≤ 1 / 4 := by
    have h1 : depth / S.scalar t x ≤ depth / S.scalar that xhat :=
      div_le_div_of_nonneg_left hdepth hQhat hRle
    have h2 : depth / S.scalar that xhat ≤ 1 / 4 := by
      rw [div_le_iff₀ hQhat]
      linarith
    exact h1.trans h2
  refine ⟨x, t, hbadx, hRle, ⟨by linarith, htle⟩, hratio, ?_, hgood⟩
  exact (Set.Icc_subset_Icc (by linarith) (htle.trans hthatT)).trans hwindow

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
