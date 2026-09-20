import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.UniversalScalarDifferentialBounds

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Set
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.DifferentialGeometry.Manifold ContDiff

universe u uE uH

theorem le_one_of_time_zero_le_one_of_scale_comparison {R : ℝ → ℝ} {eta : ℝ} (heta : 0 < eta)
    (hpos : ∀ t ≤ 0, 0 < R t)
    (hstep : ∀ t ≤ 0, ∀ s ∈ Set.Icc (t - (2 * eta * R t)⁻¹) t, R s ≤ R t)
    (hzero : R 0 ≤ 1) :
    ∀ t ≤ 0, R t ≤ 1 := by
  have hc : 0 < (2 * eta)⁻¹ := inv_pos.mpr (by linarith)
  set c : ℝ := (2 * eta)⁻¹ with hcdef
  have hcpos : 0 < c := by rw [hcdef]; exact hc
  have key : ∀ k : ℕ, ∀ s ∈ Set.Icc (-((k : ℝ) * c)) 0, R s ≤ 1 := by
    intro k
    induction k with
    | zero =>
        intro s hs
        have hs0 : s = 0 := le_antisymm hs.2 (by simpa using hs.1)
        rw [hs0]
        exact hzero
    | succ k ih =>
        intro s hs
        have hs1 : -(((Nat.succ k : ℕ) : ℝ) * c) ≤ s := hs.1
        have hcast : (((Nat.succ k : ℕ) : ℝ)) = (k : ℝ) + 1 := by push_cast; ring
        rw [hcast] at hs1
        have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
        have ha : -((k : ℝ) * c) ≤ 0 := by nlinarith
        rcases le_total (-((k : ℝ) * c)) s with hsa | hsa
        · exact ih s ⟨hsa, hs.2⟩
        · have hlow : -((k : ℝ) * c) - c ≤ s := by nlinarith
          have hRa : R (-((k : ℝ) * c)) ≤ 1 := ih _ ⟨le_refl _, ha⟩
          have h2 : 2 * eta * R (-((k : ℝ) * c)) ≤ 2 * eta := by
            have hmul := mul_le_mul_of_nonneg_left hRa (by linarith : (0 : ℝ) ≤ 2 * eta)
            linarith
          have h3 : 0 < 2 * eta * R (-((k : ℝ) * c)) := by
            have hp := hpos _ ha
            positivity
          have hlep : c ≤ (2 * eta * R (-((k : ℝ) * c)))⁻¹ := by
            have h4 : (2 * eta)⁻¹ ≤ (2 * eta * R (-((k : ℝ) * c)))⁻¹ := by
              simpa only [one_div] using one_div_le_one_div_of_le h3 h2
            simpa only [hcdef] using h4
          have hmem : s ∈ Set.Icc (-((k : ℝ) * c) - (2 * eta * R (-((k : ℝ) * c)))⁻¹)
              (-((k : ℝ) * c)) := ⟨by linarith, hsa⟩
          exact le_trans (hstep _ ha s hmem) hRa
  intro t ht
  obtain ⟨k, hk⟩ := exists_nat_ge (-t / c)
  have hkt : -((k : ℝ) * c) ≤ t := by
    have h1 : -t ≤ (k : ℝ) * c := (div_le_iff₀ hcpos).mp hk
    linarith
  exact key k t ⟨hkt, ht⟩

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)

local instance backwardBoundTopology : TopologicalSpace F.M := F.topology
local instance backwardBoundCharted : ChartedSpace H F.M := F.charted
local instance backwardBoundSmooth : IsManifold I ∞ F.M := F.smooth
local instance backwardBoundC1 : IsManifold I 1 F.M :=
  IsManifold.of_le (I := I) (M := F.M) (n := ∞) (by decide : (1 : WithTop ℕ∞) ≤ ∞)
local instance backwardBoundSigmaCompact : SigmaCompactSpace F.M := F.sigmaCompact
local instance backwardBoundT2 : T2Space F.M := F.t2
local instance backwardBoundTangentT2 : T2Space (TangentBundle I F.M) := F.t2TangentBundle

theorem ancientKappa_scalar_bounded_of_time_zero_le_one {kappa : ℝ}
    (hanc : IsAncientKappaSolution (I := I) kappa F)
    {eta : ℝ} (heta : 0 < eta) (hb : ScalarDifferentialBounds F eta)
    (hzero : ∀ y : F.M, F.S.scalar 0 y ≤ 1) :
    PointedFlowScalarBounded (I := I) F 1 := by
  intro t ht x
  have ht0 : t ≤ 0 := by simpa only [hanc.carrier_eq, Set.mem_Iic] using ht
  refine ⟨ancientKappa_scalar_nonneg (I := I) F hanc ht0 x, ?_⟩
  refine le_one_of_time_zero_le_one_of_scale_comparison (R := fun s => F.S.scalar s x) heta
    (fun s hs => ancientKappa_scalar_pos (I := I) F hanc hs x)
    (fun s hs s' hs' =>
      (ancientKappa_temporal_scale_comparison (I := I) F hanc heta
        (fun s hs y => ancientKappa_scalar_pos (I := I) F hanc hs y) hb hs x s' hs').2)
    (hzero x) t ht0

theorem ancientKappa_scalar_bounded_of_universal_mixed_jet_bound {C0 C1 C2 : ℝ}
    (h00 : UniversalMixedJetBound.{u} 0 0 C0)
    (h10 : UniversalMixedJetBound.{u} 1 0 C1)
    (h20 : UniversalMixedJetBound.{u} 2 0 C2) :
    ∃ eta : ℝ, 0 < eta ∧ ∀ (kappa : ℝ) (F : PointedFlowData.{u, 0, 0} (I := I3)
        ancientTimeInterval),
      IsAncientKappaSolution (I := I3) kappa F →
        (∀ y : F.M, F.S.scalar 0 y ≤ 1) → PointedFlowScalarBounded (I := I3) F 1 := by
  obtain ⟨eta, heta1, hb⟩ := exists_universal_scalarDifferentialBounds.{u} h00 h10 h20
  refine ⟨eta, lt_of_lt_of_le zero_lt_one heta1, ?_⟩
  intro kappa F' hanc hzero
  exact ancientKappa_scalar_bounded_of_time_zero_le_one (F := F')
    hanc (lt_of_lt_of_le zero_lt_one heta1) (hb kappa F' hanc) hzero

theorem exists_scalar_function_pos_time_zero_le_one_not_le_one :
    ∃ R : ℝ → ℝ, (∀ t ≤ 0, 0 < R t) ∧ R 0 ≤ 1 ∧ ¬ (∀ t ≤ 0, R t ≤ 1) :=
  ⟨fun t => if t = 0 then 1 else 2, fun t _ => by by_cases h : t = 0 <;> simp [h],
    by simp, fun h => by
      have h1 := h (-1) (by norm_num)
      norm_num at h1⟩

theorem scale_comparison_hypotheses_satisfiable :
    (∀ t ≤ (0 : ℝ), 0 < (fun _ : ℝ => (1 : ℝ)) t) ∧
      (∀ t ≤ (0 : ℝ), ∀ s ∈ Set.Icc (t - (2 * (1 / 2 : ℝ) * (fun _ : ℝ => (1 : ℝ)) t)⁻¹) t,
        (fun _ : ℝ => (1 : ℝ)) s ≤ (fun _ : ℝ => (1 : ℝ)) t) ∧
      (fun _ : ℝ => (1 : ℝ)) 0 ≤ 1 ∧
      (∀ t ≤ (0 : ℝ), (fun _ : ℝ => (1 : ℝ)) t ≤ 1) :=
  ⟨fun _ _ => one_pos,
    fun _ _ _ _ => le_refl 1,
    le_refl 1,
    fun t ht => (le_one_of_time_zero_le_one_of_scale_comparison (R := fun _ : ℝ => (1 : ℝ))
      (eta := 1 / 2) (by norm_num) (fun _ _ => one_pos) (fun _ _ _ _ => le_refl 1)
      (le_refl 1)) t ht⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
