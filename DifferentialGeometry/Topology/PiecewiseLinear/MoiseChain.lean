/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.LemmaThree
import DifferentialGeometry.Topology.PiecewiseLinear.ComponentComplex
import DifferentialGeometry.Topology.PiecewiseLinear.CombinatorialSolidTorus
import DifferentialGeometry.Topology.Connected.Separation
import DifferentialGeometry.Topology.Connected.TwoSided
import DifferentialGeometry.Topology.PiecewiseLinear.CylindricalDiagram
import DifferentialGeometry.Topology.PiecewiseLinear.SolidTorus
import DifferentialGeometry.Topology.PiecewiseLinear.Transition361
import DifferentialGeometry.Topology.PiecewiseLinear.MapApproximation
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldApproximation
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralGraph
import DifferentialGeometry.Topology.PiecewiseLinear.SimplicialApproximation

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
        IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Δ ∧
        Δ ⊆ K.space ∧
        Δ ∩ (boundaryComplex 3 K).space = r '' stdSimplexBoundary 2 ∧
        ∃ hboundary : r '' stdSimplexBoundary 2 ⊆
            (connectedComponentComplex (boundaryComplex 3 K) c).space,
          ¬ (⟨Set.inclusion hboundary, continuous_inclusion hboundary⟩ :
            C(r '' stdSimplexBoundary 2,
              (connectedComponentComplex (boundaryComplex 3 K) c).space)).Nullhomotopic

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
        IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Δ ∧
        Δ ⊆ K.space \ (boundaryComplex 3 K).space ∧
        Δ ∩ S = r '' stdSimplexBoundary 2 ∧
        ∃ hboundary : r '' stdSimplexBoundary 2 ⊆ S,
          ¬ (⟨Set.inclusion hboundary, continuous_inclusion hboundary⟩ :
            C(r '' stdSimplexBoundary 2, S)).Nullhomotopic

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

def HasCylindricalDiagram (S : Set (EuclideanSpace ℝ (Fin 3))) : Prop :=
  ∃ f : (Fin 3 → ℝ) × ℝ → EuclideanSpace ℝ (Fin 3),
    IsCylindricalDiagram f (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) S

def Moise307 : Prop :=
  ∀ (S₁ S₂ : Set (EuclideanSpace ℝ (Fin 3))),
    IsTopologicalSolidTorus S₁ → IsTopologicalSolidTorus S₂ → S₁ ⊆ interior S₂ →
    IsToroidalShell (closure (S₂ \ S₁)) (frontier S₁) (frontier S₂) →
    ∃ S : Set (EuclideanSpace ℝ (Fin 3)),
      HasCylindricalDiagram S ∧ S₁ ⊆ interior S ∧ S ⊆ interior S₂

open Classical in
def Moise331 : Prop :=
  ∀ (L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) (_ : Finite L.faces),
    (∀ s ∈ L.faces, s.card ≤ 2) →
    (∃ e ∈ L.faces, e.card = 2) →
    IsConnected L.space →
    (∀ v : L.vertices,
      ((SimplicialComplex.edgeGraph L).neighborSet v).ncard ≠ 1) →
    ∀ U : Set (EuclideanSpace ℝ (Fin 3)), IsOpen U → L.space ⊆ U →
    ∀ h : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3),
      Topology.IsEmbedding (U.domRestrict h) →
    ∀ ε : ℝ, 0 < ε →
      ∃ (T L' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))),
        T.faces.Finite ∧
        IsSubdivision L' L ∧
        L'.faces ⊆ T.faces ∧
        IsCombinatorialManifoldWithBoundary 3 T ∧
        T.space ∈ nhdsSet L.space ∧
        IsCombinatorialManifoldWithBoundary 3 (derivedNeighborhood T L') ∧
        (derivedNeighborhood T L').space ∈ nhdsSet L.space ∧
        (derivedNeighborhood T L').space ⊆ U ∧
        ∃ f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3),
          IsPLHomeomorphOn f (derivedNeighborhood T L').space
            (f '' (derivedNeighborhood T L').space) ∧
          f '' (derivedNeighborhood T L').space ∈ nhdsSet (h '' L.space) ∧
          ∀ x ∈ (derivedNeighborhood T L').space, dist (f x) (h x) < ε

open Classical in
theorem Moise331.applies_to_tetrahedron_oneSkeleton (h331 : Moise331) :
    ∃ L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)),
      L.faces.Finite ∧
      (∃ v : L.vertices,
        ((SimplicialComplex.edgeGraph L).neighborSet v).ncard = 3) ∧
      ∀ U : Set (EuclideanSpace ℝ (Fin 3)), IsOpen U → L.space ⊆ U →
      ∀ h : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3),
        Topology.IsEmbedding (U.domRestrict h) →
      ∀ ε : ℝ, 0 < ε →
        ∃ (T L' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))),
          T.faces.Finite ∧
          IsSubdivision L' L ∧
          L'.faces ⊆ T.faces ∧
          IsCombinatorialManifoldWithBoundary 3 T ∧
          T.space ∈ nhdsSet L.space ∧
          IsCombinatorialManifoldWithBoundary 3 (derivedNeighborhood T L') ∧
          (derivedNeighborhood T L').space ∈ nhdsSet L.space ∧
          (derivedNeighborhood T L').space ⊆ U ∧
          ∃ f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3),
            IsPLHomeomorphOn f (derivedNeighborhood T L').space
              (f '' (derivedNeighborhood T L').space) ∧
            f '' (derivedNeighborhood T L').space ∈ nhdsSet (h '' L.space) ∧
            ∀ x ∈ (derivedNeighborhood T L').space, dist (f x) (h x) < ε := by
  obtain ⟨L, hfin, hdim, hedge, hconn, hend, hbranch⟩ := exists_tetrahedron_oneSkeleton
  let _ : Finite L.faces := hfin.to_subtype
  exact ⟨L, hfin, hbranch, h331 L inferInstance hdim hedge hconn hend⟩

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

def IsSpine (S J : Set (EuclideanSpace ℝ (Fin 3))) : Prop :=
  ∃ (φ : (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ×
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) ≃ₜ S)
    (p : EuclideanSpace ℝ (Fin 2)),
    p ∈ interior (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) ∧
    J = Subtype.val '' (φ '' {q | (q.1 : EuclideanSpace ℝ (Fin 2)) = p})

def Moise308 : Prop :=
  ∀ (S J : Set (EuclideanSpace ℝ (Fin 3))),
    HasCylindricalDiagram S → IsSpine S J →
    ∀ hJS : J ⊆ S, ∀ x : J,
      Subgroup.closure (Set.range (FundamentalGroup.map
        (⟨Set.inclusion hJS, continuous_inclusion hJS⟩ : C(J, S)) x)) = ⊤

section AnnularSeparation

open _root_.Topology

local notation "E3" => EuclideanSpace ℝ (Fin 3)

def IsPLAnnulusWithEnds (X J₀ J₁ : Set E3) : Prop :=
  ∃ (J : Set E3) (ρ : E3 × ℝ → E3), IsPLSphere 1 J ∧
    IsPLHomeomorphOn ρ (J ×ˢ Icc (0 : ℝ) 1) X ∧
    J₀ = ρ '' (J ×ˢ {(0 : ℝ)}) ∧ J₁ = ρ '' (J ×ˢ {(1 : ℝ)})

def Moise303 : Prop :=
  ∀ (M H K C Δ D₁ D₂ Ω : Set E3) (r r₁ r₂ : (Fin 3 → ℝ) → E3),
    IsOpen M → IsConnected M → H ⊆ M → K ⊆ M → Disjoint H K →
    IsClosed (((↑) : M → E3) ⁻¹' H) → IsClosed (((↑) : M → E3) ⁻¹' K) →
    C ⊆ M → IsClosed (((↑) : M → E3) ⁻¹' C) →
    Separates (((↑) : M → E3) ⁻¹' C) (((↑) : M → E3) ⁻¹' H) (((↑) : M → E3) ⁻¹' K) →
    IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Δ → Δ ⊆ C →
    IsPLHomeomorphOn r₁ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₁ →
    IsPLHomeomorphOn r₂ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₂ →
    D₁ ∩ D₂ = Δ → D₁ ∪ D₂ ⊆ C → D₁ ∪ D₂ ∈ 𝓝ˢ[C] Δ →
    Δ ⊆ D₁ \ r₁ '' stdSimplexBoundary 2 → Δ ⊆ D₂ \ r₂ '' stdSimplexBoundary 2 →
    IsOpen Ω → Δ ⊆ Ω → Ω ⊆ M → Disjoint Ω (H ∪ K) →
    ∃ (C' A₁ Δ₁ J₁ : Set E3) (r' : (Fin 3 → ℝ) → E3),
      IsClosed (((↑) : M → E3) ⁻¹' C') ∧ C' ⊆ M ∧
      Separates (((↑) : M → E3) ⁻¹' C') (((↑) : M → E3) ⁻¹' H) (((↑) : M → E3) ⁻¹' K) ∧
      C' \ Ω = C \ Ω ∧ D₂ ⊆ C' ∧
      IsPLAnnulusWithEnds A₁ (r '' stdSimplexBoundary 2) J₁ ∧ A₁ ⊆ D₁ ∩ Ω ∧
      A₁ ∩ Δ = r '' stdSimplexBoundary 2 ∧
      IsPLHomeomorphOn r' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Δ₁ ∧ J₁ = r' '' stdSimplexBoundary 2 ∧
      Δ₁ ⊆ Ω ∧ Δ₁ ∩ C = J₁ ∧
      C' = (C \ (A₁ \ (r '' stdSimplexBoundary 2 ∪ J₁))) ∪ Δ₁

open Classical in
def Moise286 : Prop :=
  ∀ (S : Set E3), IsCombinatorialSolidTorus S → ∀ (n : ℕ) (G : Fin n → Set E3), 1 < n →
    (∀ i, IsPLSphere 1 (G i)) → (∀ i, G i ⊆ frontier S) →
    Pairwise (fun i j => Disjoint (G i) (G j)) →
    (∀ i, ¬ ∃ (Δ : Set E3) (r : (Fin 3 → ℝ) → E3),
      IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Δ ∧ Δ ⊆ frontier S ∧
        G i = r '' stdSimplexBoundary 2) →
    ∀ x ∈ frontier S \ (⋃ i, G i), ∃ i j : Fin n, i ≠ j ∧
      IsPLAnnulusWithEnds (closure (connectedComponentIn (frontier S \ ⋃ i, G i) x)) (G i) (G j)

open Classical in
def Moise267 : Prop :=
  ∀ M : Fin 3 → Geometry.SimplicialComplex ℝ E3, (∀ i, (M i).faces.Finite) →
    (∀ i, IsCombinatorialManifoldWithBoundary 2 (M i)) → (∀ i, IsConnected (M i).space) →
    (∀ i j, (boundaryComplex 2 (M i)).space = (boundaryComplex 2 (M j)).space) →
    (boundaryComplex 2 (M 0)).space.Nonempty →
    (∀ i j, i ≠ j → Disjoint ((M i).space \ (boundaryComplex 2 (M i)).space)
      ((M j).space \ (boundaryComplex 2 (M j)).space)) →
    ∀ x ∉ (⋃ i, (M i).space),
      ¬ Bornology.IsBounded (connectedComponentIn (⋃ i, (M i).space)ᶜ x) →
      ∃ i j k : Fin 3, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
        frontier (connectedComponentIn (⋃ i, (M i).space)ᶜ x) = (M i).space ∪ (M j).space ∧
        ∀ y ∈ (M k).space \ (boundaryComplex 2 (M k)).space,
          Bornology.IsBounded (connectedComponentIn ((M i).space ∪ (M j).space)ᶜ y)

end AnnularSeparation

end DifferentialGeometry.Topology.PiecewiseLinear
