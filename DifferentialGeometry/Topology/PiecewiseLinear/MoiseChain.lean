import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.LemmaThree
import DifferentialGeometry.Topology.PiecewiseLinear.ComponentComplex
import DifferentialGeometry.Topology.Connected.Separation
import DifferentialGeometry.Topology.Connected.TwoSided
import DifferentialGeometry.Topology.PiecewiseLinear.CylindricalDiagram
import DifferentialGeometry.Topology.PiecewiseLinear.Transition361
import DifferentialGeometry.Topology.PiecewiseLinear.MapApproximation

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
    IsSphericalShell (closure (C₂ \ C₁)) (frontier C₁) (frontier C₂) →
    ∃ C : Set (EuclideanSpace ℝ (Fin 3)),
      IsPLBall 3 C ∧ C₁ ⊆ interior C ∧ C ⊆ interior C₂

def Moise341 : Prop :=
  ∀ (C : Set (EuclideanSpace ℝ (Fin 3))), IsPLBall 3 C →
    ∀ h : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3),
      ContinuousOn h C → InjOn h C →
    ∀ ε : ℝ, 0 < ε →
      ∃ f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3),
        IsPLHomeomorphOn f C (f '' C) ∧ ∀ x ∈ C, dist (f x) (h x) < ε

def IsPLTorus (T : Set (EuclideanSpace ℝ (Fin 3))) : Prop :=
  IsPolyhedron T ∧
    Nonempty (T ≃ₜ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ×
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1))

def IsToroidalShell {E : Type u} [TopologicalSpace E] (Y T₀ T₁ : Set E) : Prop :=
  ∃ φ : ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ×
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) × Set.Icc (0 : ℝ) 1) ≃ₜ Y,
    T₀ = Subtype.val '' (φ '' {p | (p.2 : ℝ) = 0}) ∧
    T₁ = Subtype.val '' (φ '' {p | (p.2 : ℝ) = 1})

def Moise306 : Prop :=
  ∀ (Y T₀ T₁ : Set (EuclideanSpace ℝ (Fin 3))),
    IsToroidalShell Y T₀ T₁ →
    ∃ T : Set (EuclideanSpace ℝ (Fin 3)),
      IsPLTorus T ∧ T ⊆ interior Y ∧ Separates T T₀ T₁

def IsTopologicalSolidTorus {E : Type u} [TopologicalSpace E] (S : Set E) : Prop :=
  Nonempty (S ≃ₜ (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ×
    Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1))

def HasCylindricalDiagram (S : Set (EuclideanSpace ℝ (Fin 3))) : Prop :=
  ∃ f : (Fin 3 → ℝ) × ℝ → EuclideanSpace ℝ (Fin 3),
    IsCylindricalDiagram f (stdSimplex ℝ (Fin 3)) S

def Moise307 : Prop :=
  ∀ (S₁ S₂ : Set (EuclideanSpace ℝ (Fin 3))),
    IsTopologicalSolidTorus S₁ → IsTopologicalSolidTorus S₂ → S₁ ⊆ interior S₂ →
    IsToroidalShell (closure (S₂ \ S₁)) (frontier S₁) (frontier S₂) →
    ∃ S : Set (EuclideanSpace ℝ (Fin 3)),
      HasCylindricalDiagram S ∧ S₁ ⊆ interior S ∧ S ⊆ interior S₂

open Classical in
def Moise331 : Prop :=
  ∀ (T : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
    (_ : Finite T.faces) (L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))),
    L.faces ⊆ T.faces → (∀ s ∈ L.faces, s.card ≤ 2) → IsConnected L.space →
    ∀ U : Set (EuclideanSpace ℝ (Fin 3)), IsOpen U → L.space ⊆ U →
    ∀ h : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3),
      ContinuousOn h U → InjOn h U →
    ∀ ε : ℝ, 0 < ε →
      ∃ f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3),
        (derivedNeighborhood T L).space ⊆ U ∧
        IsPLHomeomorphOn f (derivedNeighborhood T L).space
          (f '' (derivedNeighborhood T L).space) ∧
        f '' (derivedNeighborhood T L).space ∈ nhdsSet (h '' L.space) ∧
        ∀ x ∈ (derivedNeighborhood T L).space, dist (f x) (h x) < ε

open Classical in
def Moise351 (n : ℕ) : Prop :=
  ∀ {M₁ M₂ : Type u} [TopologicalSpace M₁] [T2Space M₁] [SecondCountableTopology M₁]
    [MetricSpace M₂] [SecondCountableTopology M₂]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₁]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₂]
    [HasGroupoid M₁ (plGroupoid n)] [HasGroupoid M₂ (plGroupoid n)]
    {U : Set M₁} (_ : IsOpen U) {K : Set M₁} (_ : K ⊆ U) (_ : IsClosed (((↑) : U → M₁) ⁻¹' K))
    {h : M₁ → M₂} (_ : Topology.IsEmbedding (U.domRestrict h))
    (φ : M₁ → ℝ) (_ : ContinuousOn φ U) (_ : ∀ x ∈ U, 0 < φ x),
    ∃ N : Set M₁,
      IsLocallyFinitePolyhedralManifoldWithBoundary (n := n) n N ∧
      K ⊆ interior N ∧ N ⊆ U ∧
      ∃ f : M₁ → M₂, IsPLHomeomorphInto n f N ∧
        f '' N ∈ nhdsSet (h '' K) ∧ ∀ x ∈ N, dist (f x) (h x) < φ x

def PLMapApproximation : Prop :=
  ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {P : Set E}, IsPolyhedron P → IsCompact P →
    ∀ {f : E → EuclideanSpace ℝ (Fin 3)}, ContinuousOn f P →
    ∀ ε : ℝ, 0 < ε →
      ∃ g : E → EuclideanSpace ℝ (Fin 3),
        IsPiecewiseAffineOn g P ∧ ∀ x ∈ P, dist (g x) (f x) < ε

theorem plMapApproximation : PLMapApproximation := by
  intro E _ _ _ P hP hPc f hf ε hε
  exact exists_isPiecewiseAffineOn_dist_lt hP hPc hf hε

def TopologicalCellComplementConnected : Prop :=
  ∀ C : Set (EuclideanSpace ℝ (Fin 3)), IsTopologicalCell 3 C → IsConnected Cᶜ

end DifferentialGeometry.Topology.PiecewiseLinear
