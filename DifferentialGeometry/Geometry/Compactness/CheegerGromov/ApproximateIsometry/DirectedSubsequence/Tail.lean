import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.MetricApproximation.Defs
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Chain

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry.CheegerGromovCompactness

open scoped Manifold ContDiff
open Set (MapsTo)

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : ℕ → Type u} [∀ j, TopologicalSpace (M j)] [∀ j, ChartedSpace H (M j)]

variable [FiniteDimensional ℝ E]
variable [∀ j, T2Space (M j)] [∀ j, IsManifold I ∞ (M j)]

theorem nonempty_chain_metric_approximation_shift
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    (N j k : ℕ) {K : Set (M (N + j))} {eps : ℝ} {p : ℕ}
    (hD : Nonempty (PartialDiffeomorphMetricApproximation (I := I) K eps p
      (chainComp Ψ (N + j) k) (g (N + j)) (g ((N + j) + k)))) :
    Nonempty (PartialDiffeomorphMetricApproximation (I := I) K eps p
      (chainComp (Mf := fun n => M (N + n)) (fun n => Ψ (N + n)) j k)
      (g (N + j)) (g (N + (j + k)))) := by
  rw [chainComp_shift_eq]
  have hcast : ∀ {a b : ℕ} (h : a = b)
      (F : PartialDiffeomorph I I (M (N + j)) (M a) (∞ : WithTop ℕ∞)),
      Nonempty (PartialDiffeomorphMetricApproximation (I := I) K eps p
        F (g (N + j)) (g a)) →
      Nonempty (PartialDiffeomorphMetricApproximation (I := I) K eps p
        (h ▸ F) (g (N + j)) (g b)) := by
    intro a b h F hF
    cases h
    exact hF
  exact hcast (Nat.add_assoc N j k) (chainComp Ψ (N + j) k) hD

theorem exists_tail_chain_metric_approximations
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    (K U : ∀ j, Set (M j))
    (hUK : ∀ j, U j ⊆ K j)
    (hmap : ∀ j, MapsTo (Ψ j) (U j) (U (j + 1)))
    (hdata : ∀ p : ℕ, ∃ J : ℕ, ∀ j : ℕ, J ≤ j → ∀ k : ℕ,
      Nonempty (PartialDiffeomorphMetricApproximation (I := I) (K j) (1 / 2) p
        (chainComp Ψ j k) (g j) (g (j + k)))) :
    ∃ N : ℕ,
      let Ψ' : ∀ j, PartialDiffeomorph I I (M (N + j)) (M (N + (j + 1)))
          (∞ : WithTop ℕ∞) := fun j => Ψ (N + j)
      ∃ _ : ∀ j k : ℕ, PartialDiffeomorphMetricApproximation (I := I)
          (K (N + j)) (1 / 2) 0
          (chainComp (Mf := fun n => M (N + n)) Ψ' j k)
          (g (N + j)) (g (N + (j + k))),
        (∀ j k, U (N + j) ⊆
          (chainComp (Mf := fun n => M (N + n)) Ψ' j k).source) ∧
        (∀ j k, MapsTo (chainComp (Mf := fun n => M (N + n)) Ψ' j k)
          (U (N + j)) (U (N + (j + k)))) ∧
        ∀ j p : ℕ, ∃ a : ℕ,
          (chainComp (Mf := fun n => M (N + n)) Ψ' j a :
            M (N + j) → M (N + (j + a))) '' U (N + j) ⊆ K (N + (j + a)) ∧
          ∀ c : ℕ, Nonempty (PartialDiffeomorphMetricApproximation (I := I)
            (K (N + (j + a))) (1 / 2) p
            (chainComp (Mf := fun n => M (N + n)) Ψ' (j + a) c)
            (g (N + (j + a))) (g (N + ((j + a) + c)))) := by
  classical
  obtain ⟨N, hN⟩ := hdata 0
  refine ⟨N, ?_⟩
  let Ψ' : ∀ j, PartialDiffeomorph I I (M (N + j)) (M (N + (j + 1)))
      (∞ : WithTop ℕ∞) := fun j => Ψ (N + j)
  let D0 : ∀ j k : ℕ, PartialDiffeomorphMetricApproximation (I := I)
      (K (N + j)) (1 / 2) 0
      (chainComp (Mf := fun n => M (N + n)) Ψ' j k)
      (g (N + j)) (g (N + (j + k))) := fun j k =>
    Classical.choice (nonempty_chain_metric_approximation_shift Ψ g N j k
      (hN (N + j) (Nat.le_add_right N j) k))
  have hstep : ∀ j, MapsTo (Ψ' j) (U (N + j)) (U (N + (j + 1))) :=
    fun j => hmap (N + j)
  have hchain : ∀ j k, MapsTo (chainComp (Mf := fun n => M (N + n)) Ψ' j k)
      (U (N + j)) (U (N + (j + k))) :=
    chainComp_mapsTo Ψ' (fun j => U (N + j)) hstep
  refine ⟨D0, fun j k => (hUK (N + j)).trans (D0 j k).source_sub, hchain, ?_⟩
  intro j p
  obtain ⟨J, hJ⟩ := hdata p
  refine ⟨J, ?_, fun c => ?_⟩
  · exact ((hchain j J).image_subset).trans (hUK (N + (j + J)))
  · exact nonempty_chain_metric_approximation_shift Ψ g N (j + J) c
      (hJ (N + (j + J)) (by omega) c)

end DifferentialGeometry.CheegerGromovCompactness
