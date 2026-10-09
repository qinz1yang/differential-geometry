import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.AncientExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedTerminalComparison

set_option autoImplicit false
noncomputable section
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

namespace AncientExtensionAudit

universe u

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.DifferentialGeometry.Manifold ContDiff ENNReal

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem threshold_hypothesis_vacuous {A : ℝ} (hA : A < 0) {f : ℝ → ℝ}
    (hf : ∀ s : ℝ, 0 ≤ f s) : ∀ s : ℝ, f s ≤ A → False :=
  fun s hs => absurd (le_trans (hf s) hs) (not_le_of_gt hA)

theorem implication_vacuous_of_empty_hypothesis {P : ℝ → Prop} {G : ℝ → Prop}
    (hempty : ∀ x : ℝ, ¬ P x) : ∀ x : ℝ, P x → G x :=
  fun x hx => absurd hx (hempty x)

theorem threshold_bound_iff_nonnegative {f : ℝ → ℝ} (hf : ∀ s : ℝ, 0 ≤ f s) :
    (∀ A : ℝ, ∃ C : ℝ, ∀ s : ℝ, f s ≤ A → f s ≤ C) ↔
      (∀ A : ℝ, 0 ≤ A → ∃ C : ℝ, ∀ s : ℝ, f s ≤ A → f s ≤ C) := by
  constructor
  · intro h A _
    exact h A
  · intro h A
    by_cases hA : 0 ≤ A
    · exact h A hA
    · exact ⟨0, fun s hs =>
        absurd hs (threshold_hypothesis_vacuous (lt_of_not_ge hA) hf s)⟩

theorem scale_threshold_not_uniform :
    (∀ n : ℕ, ∃ k : ℝ, 0 < k ∧ k ≤ 1 / ((n : ℝ) + 1)) ∧
      ¬ (∃ k : ℝ, 0 < k ∧ ∀ n : ℕ, k ≤ 1 / ((n : ℝ) + 1)) := by
  constructor
  · intro n
    exact ⟨1 / ((n : ℝ) + 1), by positivity, le_rfl⟩
  · rintro ⟨k, hkpos, hk⟩
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / k)
    have hk1 : k * (1 / k) = 1 := by field_simp
    have hmono : k * (1 / k) < k * ((n : ℝ) + 1) := by
      have h1 : k * (1 / k) < k * (n : ℝ) := mul_lt_mul_of_pos_left hn hkpos
      have h2 : k * (n : ℝ) < k * ((n : ℝ) + 1) :=
        mul_lt_mul_of_pos_left (by linarith) hkpos
      linarith
    have hbig : 1 < k * ((n : ℝ) + 1) := by linarith
    have hle := hk n
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)] at hle
    linarith

theorem shrinking_scale_not_uniform :
    (∀ n : ℕ, ∃ d : ℝ, 0 < d ∧ d ≤ 1 / ((n : ℝ) + 1) ^ 2) ∧
      ¬ (∃ d : ℝ, 0 < d ∧ ∀ n : ℕ, d ≤ 1 / ((n : ℝ) + 1) ^ 2) := by
  constructor
  · intro n
    exact ⟨1 / ((n : ℝ) + 1) ^ 2, by positivity, le_rfl⟩
  · rintro ⟨d, hdpos, hd⟩
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / d)
    have hnpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hbig : 1 < d * ((n : ℝ) + 1) ^ 2 := by
      have h1 : 1 < d * (n : ℝ) := by
        have := mul_lt_mul_of_pos_left hn hdpos
        rwa [mul_one_div, div_self (ne_of_gt hdpos)] at this
      have h2 : d * (n : ℝ) < d * ((n : ℝ) + 1) ^ 2 := by
        have hnle : (n : ℝ) < ((n : ℝ) + 1) ^ 2 := by nlinarith
        exact mul_lt_mul_of_pos_left hnle hdpos
      linarith
    have hle := hd n
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < ((n : ℝ) + 1) ^ 2)] at hle
    linarith

theorem windowedTerminalComparison_inhabited {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    {X : NormalizedSequence.{u} eps kappa sigma Phi} {L : TerminalLimit X}
    {J : RealTimeInterval} (B : BackwardExtension L J) :
    WindowedTerminalComparison B J B.solution.base.metric :=
  terminalComparison_of_backwardExtension B

end AncientExtensionAudit

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
