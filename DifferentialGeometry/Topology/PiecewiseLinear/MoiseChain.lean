import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.LemmaThree
import DifferentialGeometry.Topology.PiecewiseLinear.ComponentComplex
import DifferentialGeometry.Topology.Connected.Separation
import DifferentialGeometry.Topology.Connected.TwoSided

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

def IsNullHomotopic {X : Type u} [TopologicalSpace X] (γ : freeLoop X) : Prop :=
  ∃ x : X, γ.Homotopic (ContinuousMap.const _ x)

def Moise251 : Prop :=
  ∀ {N : ℕ} (S : NormalSystem (EuclideanSpace ℝ (Fin N))),
    Nonempty (NormalSystem.NonsingularCell S)

open Classical in
def Moise252 : Prop :=
  ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) (_ : Finite K.faces),
    IsCombinatorialManifoldWithBoundary 3 K → IsOrientable 3 K →
    ∀ c : ConnectedComponents (boundaryComplex 3 K).space,
    ∀ hsub : (connectedComponentComplex (boundaryComplex 3 K) c).space ⊆ K.space,
    ∀ γ : freeLoop (connectedComponentComplex (boundaryComplex 3 K) c).space,
      IsNullHomotopic ((⟨Set.inclusion hsub, continuous_inclusion hsub⟩ :
        C((connectedComponentComplex (boundaryComplex 3 K) c).space, K.space)).comp γ) →
      ¬ IsNullHomotopic γ →
      ∃ (Δ : Set E) (r : (Fin 3 → ℝ) → E),
        IsPLHomeomorphOn r (stdSimplex ℝ (Fin 3)) Δ ∧
        Δ ⊆ K.space ∧
        r '' stdSimplexBoundary 2 ⊆
          (connectedComponentComplex (boundaryComplex 3 K) c).space ∧
        Δ ∩ (boundaryComplex 3 K).space = r '' stdSimplexBoundary 2

open Classical in
def Moise264 : Prop :=
  ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) (_ : Finite K.faces),
    IsCombinatorialManifoldWithBoundary 3 K →
    ∀ (L : Geometry.SimplicialComplex ℝ E) (_ : Finite L.faces),
      IsCombinatorialManifold 2 L →
      L.space ⊆ K.space \ (boundaryComplex 3 K).space → IsTwoSided L.space →
    let S := L.space
    ∀ (x : S) (g : FundamentalGroup S x),
      g ≠ 1 →
      (∀ hsub : S ⊆ K.space,
        FundamentalGroup.map (⟨Set.inclusion hsub, continuous_inclusion hsub⟩ :
          C(S, K.space)) x g = 1) →
      ∃ (Δ : Set E) (r : (Fin 3 → ℝ) → E),
        IsPLHomeomorphOn r (stdSimplex ℝ (Fin 3)) Δ ∧
        Δ ⊆ K.space \ (boundaryComplex 3 K).space ∧
        Δ ∩ S = r '' stdSimplexBoundary 2

def IsTopologicalCell (n : ℕ) {E : Type u} [TopologicalSpace E] (C : Set E) : Prop :=
  Nonempty (C ≃ₜ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)

def IsSphericalShell {E : Type u} [TopologicalSpace E] (X B₀ B₁ : Set E) : Prop :=
  ∃ φ : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × Set.Icc (0 : ℝ) 1) ≃ₜ X,
    B₀ = Subtype.val '' (φ '' {p | (p.2 : ℝ) = 0}) ∧
    B₁ = Subtype.val '' (φ '' {p | (p.2 : ℝ) = 1})

def Moise304 : Prop :=
  ∀ (X B₀ B₁ : Set (EuclideanSpace ℝ (Fin 3))),
    IsSphericalShell X B₀ B₁ →
    ∃ B : Set (EuclideanSpace ℝ (Fin 3)),
      IsPLSphere 2 B ∧ B ⊆ interior X ∧ Separates B B₀ B₁

def Moise305 : Prop :=
  ∀ (C₁ C₂ : Set (EuclideanSpace ℝ (Fin 3))),
    IsTopologicalCell 3 C₁ → IsTopologicalCell 3 C₂ → C₁ ⊆ interior C₂ →
    (∃ B₀ B₁, IsSphericalShell (closure (C₂ \ C₁)) B₀ B₁) →
    ∃ C : Set (EuclideanSpace ℝ (Fin 3)),
      IsPLBall 3 C ∧ C₁ ⊆ interior C ∧ C ⊆ interior C₂

def Moise341 : Prop :=
  ∀ (C : Set (EuclideanSpace ℝ (Fin 3))), IsPLBall 3 C →
    ∀ h : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3),
      ContinuousOn h C → InjOn h C →
    ∀ ε : ℝ, 0 < ε →
      ∃ f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3),
        IsPLHomeomorphOn f C (f '' C) ∧ ∀ x ∈ C, dist (f x) (h x) < ε

end DifferentialGeometry.Topology.PiecewiseLinear
