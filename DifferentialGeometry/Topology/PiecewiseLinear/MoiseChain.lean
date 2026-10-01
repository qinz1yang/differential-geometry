import DifferentialGeometry.Topology.SolidTorus.Spine
import DifferentialGeometry.Topology.SolidTorus.Shell
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.Induction
import DifferentialGeometry.Topology.PiecewiseLinear.ComponentComplex
import DifferentialGeometry.Topology.PiecewiseLinear.CombinatorialSolidTorus
import DifferentialGeometry.Topology.Connected.Separation
import DifferentialGeometry.Topology.Connected.TwoSided
import DifferentialGeometry.Topology.PiecewiseLinear.CylindricalDiagram
import DifferentialGeometry.Topology.PiecewiseLinear.SolidTorus
import DifferentialGeometry.Topology.PiecewiseLinear.Homeomorph.Basic
import DifferentialGeometry.Topology.PiecewiseLinear.MapApproximation
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldApproximation
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralGraph
import DifferentialGeometry.Topology.PiecewiseLinear.SimplicialApproximation

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

def IsNullHomotopic {X : Type u} [TopologicalSpace X] (γ : freeLoop X) : Prop :=
  ∃ x : X, γ.Homotopic (ContinuousMap.const _ x)

def IsTopologicalCell (n : ℕ) {E : Type u} [TopologicalSpace E] (C : Set E) : Prop :=
  Nonempty (C ≃ₜ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)

def IsSphericalShell {E : Type u} [TopologicalSpace E] (X B₀ B₁ : Set E) : Prop :=
  ∃ φ : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × Set.Icc (0 : ℝ) 1) ≃ₜ X,
    B₀ = Subtype.val '' (φ '' {p | (p.2 : ℝ) = 0}) ∧
    B₁ = Subtype.val '' (φ '' {p | (p.2 : ℝ) = 1})

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

def HasCylindricalDiagram (S : Set (EuclideanSpace ℝ (Fin 3))) : Prop :=
  ∃ f : (Fin 3 → ℝ) × ℝ → EuclideanSpace ℝ (Fin 3),
    IsCylindricalDiagram f (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) S

open Classical in
def Moise351 : Prop :=
  ∀ {M₁ M₂ : Type u} [TopologicalSpace M₁] [T2Space M₁] [SecondCountableTopology M₁]
    [MetricSpace M₂] [SecondCountableTopology M₂]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
    [HasGroupoid M₁ (plGroupoid 3)] [HasGroupoid M₂ (plGroupoid 3)]
    {U : Set M₁} (_ : IsOpen U) {K : Set M₁} (_ : K ⊆ U) (_ : IsClosed (((↑) : U → M₁) ⁻¹' K))
    (_ : IsLocallyFinitePolyhedralGraph (n := 3) K)
    {h : M₁ → M₂} (_ : Topology.IsEmbedding (U.domRestrict h))
    (φ : M₁ → ℝ) (_ : ContinuousOn φ U) (_ : ∀ x ∈ U, 0 < φ x),
    ∃ N : Set M₁,
      IsLocallyFiniteRegularNeighborhoodOf (n := 3) N K U ∧
      ∃ f : M₁ → M₂, IsPLHomeomorphInto 3 f N ∧
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

def PLPolyhedronMapApproximation : Prop :=
  ∀ {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (L : Geometry.SimplicialComplex ℝ F) [Finite L.faces]
    {f : E → F}, ContinuousOn f K.space → MapsTo f K.space L.space →
    ∀ ε : ℝ, 0 < ε →
      ∃ g : E → F, IsPiecewiseAffineOn g K.space ∧ MapsTo g K.space L.space ∧
        ∀ x ∈ K.space, dist (g x) (f x) < ε

theorem plPolyhedronMapApproximation : PLPolyhedronMapApproximation := by
  intro E F _ _ _ _ _ _ K _ L _ f hf hmap ε hε
  obtain ⟨g, hg, hgmap, hdist, -, -⟩ :=
    exists_isPiecewiseAffineOn_mapsTo_dist_lt K L hf hmap hε
  exact ⟨g, hg, hgmap, hdist⟩

def PLManifoldMapApproximation : Prop :=
  ∀ {n : ℕ} {M : Type} [MetricSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [HasGroupoid M (plGroupoid 3)]
    {P Q : Set (EuclideanSpace ℝ (Fin n))}, IsPolyhedron P → IsPolyhedron Q → Q ⊆ P →
    ∀ {f : EuclideanSpace ℝ (Fin n) → M}, ContinuousOn f P → IsPLOn n 3 f Q →
    ∀ ε : ℝ, 0 < ε →
      ∃ g : EuclideanSpace ℝ (Fin n) → M,
        IsPLOn n 3 g P ∧ EqOn g f Q ∧ ∀ x ∈ P, dist (g x) (f x) < ε

theorem plManifoldMapApproximation : PLManifoldMapApproximation := by
  intro n M _ _ _ P Q hP hQ hQP f hf hfQ ε hε
  exact exists_isPLOn_dist_lt_eqOn hP hQ hQP hf hfQ hε

def TopologicalCellComplementConnected : Prop :=
  ∀ C : Set (EuclideanSpace ℝ (Fin 3)), IsTopologicalCell 3 C → IsConnected Cᶜ

section AnnularSeparation

open _root_.Topology

local notation "E3" => EuclideanSpace ℝ (Fin 3)

def IsPLAnnulusWithEnds (X J₀ J₁ : Set E3) : Prop :=
  ∃ (J : Set E3) (ρ : E3 × ℝ → E3), IsPLSphere 1 J ∧
    IsPLHomeomorphOn ρ (J ×ˢ Icc (0 : ℝ) 1) X ∧
    J₀ = ρ '' (J ×ˢ {(0 : ℝ)}) ∧ J₁ = ρ '' (J ×ˢ {(1 : ℝ)})

end AnnularSeparation

end DifferentialGeometry.Topology.PiecewiseLinear
