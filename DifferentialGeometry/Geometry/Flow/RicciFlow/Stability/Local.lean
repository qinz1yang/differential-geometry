import DifferentialGeometry.Geometry.Curvature.DimensionThree.TensorNorm
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Basic
import DifferentialGeometry.Geometry.Metric.Convergence.Defs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.OpenRestriction
import DifferentialGeometry.Analysis.TimeInterval

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology ENNReal
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry (SmoothRiemannianMetric)

universe u

abbrev ModelBall (L : ℝ) : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 3)) :=
  ⟨Metric.ball (0 : (EuclideanSpace ℝ (Fin 3))) L, Metric.isOpen_ball⟩

theorem modelBall_mono {L L' : ℝ} (h : L' ≤ L) : ModelBall L' ≤ ModelBall L :=
  Metric.ball_subset_ball h

def localStabilityInitialJetHypothesis
    (L : ℕ → ℝ) (v : ℕ → ℝ) (hv : ∀ i, 0 < v i)
    (γ : SmoothRiemannianMetric (𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) (EuclideanSpace ℝ (Fin 3)))
    (ℓ : (i : ℕ) → SolutionOn (I := (𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))) (M := ↥(ModelBall (L i)))
      (RealTimeInterval.closed (0 : ℝ) (v i) (le_of_lt (hv i)))) : Prop :=
  ∀ A : Set (EuclideanSpace ℝ (Fin 3)), IsCompact A → ∀ p : ℕ,
    Tendsto (fun i : ℕ => metricDerivNormSupOn (Subtype.val ⁻¹' A) p ((ℓ i).base.metric 0)
      (γ.restrictOpen (ModelBall (L i))) (γ.restrictOpen (ModelBall (L i)))) atTop (𝓝 0)

def localStabilityCauchyConclusion
    (L : ℕ → ℝ) (v : ℕ → ℝ) (hv : ∀ i, 0 < v i)
    (γ : SmoothRiemannianMetric (𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) (EuclideanSpace ℝ (Fin 3)))
    (ℓ : (i : ℕ) → SolutionOn (I := (𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))) (M := ↥(ModelBall (L i)))
      (RealTimeInterval.closed (0 : ℝ) (v i) (le_of_lt (hv i)))) : Prop :=
  ∀ A : Set (EuclideanSpace ℝ (Fin 3)), IsCompact A → ∀ m : ℕ, 4 ≤ m → ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ i j : ℕ, N ≤ i → N ≤ j → ∀ r : ℝ, ∀ hr : r ≤ min (L i) (L j),
      ∀ u ∈ Set.Icc (0 : ℝ) (min (v i) (v j)),
        metricDerivNormSupOn (I := (𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))) (M := ↥(ModelBall r))
          (Subtype.val ⁻¹' A) m
          (((ℓ i).base.metric u).restrictOpenOfSubset
            (modelBall_mono (le_trans hr (min_le_left (L i) (L j)))))
          (((ℓ j).base.metric u).restrictOpenOfSubset
            (modelBall_mono (le_trans hr (min_le_right (L i) (L j)))))
          ((γ.restrictOpen (ModelBall r)))
        ≤ ε

def localStabilityLimitFlowConclusion
    (L : ℕ → ℝ) (v : ℕ → ℝ) (hv : ∀ i, 0 < v i)
    (γ : SmoothRiemannianMetric (𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) (EuclideanSpace ℝ (Fin 3)))
    (ℓ : (i : ℕ) → SolutionOn (I := (𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))) (M := ↥(ModelBall (L i)))
      (RealTimeInterval.closed (0 : ℝ) (v i) (le_of_lt (hv i)))) : Prop :=
  ∃ γLim : ℝ → SmoothRiemannianMetric (𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) (EuclideanSpace ℝ (Fin 3)),
    γLim 0 = γ ∧
      ∀ A : Set (EuclideanSpace ℝ (Fin 3)), IsCompact A → ∀ m : ℕ, 4 ≤ m → ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, ∀ i j : ℕ, N ≤ i → N ≤ j → ∀ r : ℝ,
          ∀ hr : r ≤ min (L i) (L j),
          ∀ u ∈ Set.Icc (0 : ℝ) (min (v i) (v j)), ∀ a : ℕ, a ≤ m →
            ∀ x : ↥(ModelBall r), (x : (EuclideanSpace ℝ (Fin 3))) ∈ A →
              metricDerivNorm (I := (𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))) (M := ↥(ModelBall r)) a
                (((ℓ i).base.metric u).restrictOpenOfSubset
                  (modelBall_mono (le_trans hr (min_le_left (L i) (L j)))))
                ((γLim u).restrictOpen (ModelBall r))
                ((γ.restrictOpen (ModelBall r))) x ≤ ε

def isLocalStabilityInput : Prop :=
  ∀ θ : ℝ, 0 < θ → θ < 1 → ∀ K : ℝ, 0 < K →
    ∀ (L : ℕ → ℝ) (_hLpos : ∀ i, 0 < L i) (_hLtop : Tendsto L atTop atTop)
      (v : ℕ → ℝ) (hv : ∀ i, 0 < v i) (_hvθ : ∀ i, v i ≤ θ)
      (γ : SmoothRiemannianMetric (𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) (EuclideanSpace ℝ (Fin 3)))
      (ℓ : (i : ℕ) → SolutionOn (I := (𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))) (M := ↥(ModelBall (L i)))
        (RealTimeInterval.closed (0 : ℝ) (v i) (le_of_lt (hv i)))),
      (∀ i, DifferentialGeometry.PDE.RicciFlow.IsSolutionOn (ℓ i)) →
      (∀ i, ∀ x : ↥(ModelBall (L i)),
        curvatureNormSq ((ℓ i).base.metric (v i)) x
          (DifferentialGeometry.Geometry.Curvature.metricRm04At (I := (𝓘(ℝ, EuclideanSpace ℝ (Fin 3))))
            (M := ↥(ModelBall (L i))) ((ℓ i).base.metric (v i)) x) ≤ K ^ 2) →
      localStabilityInitialJetHypothesis L v hv γ ℓ →
      localStabilityCauchyConclusion L v hv γ ℓ

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
