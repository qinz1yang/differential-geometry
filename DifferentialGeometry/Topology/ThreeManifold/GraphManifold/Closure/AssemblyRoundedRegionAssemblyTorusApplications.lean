import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyRoundedRegionAssemblyTorus
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyNormMeasure

/-!
# Consumers of FC42 packet T4b

* `exists_rawGraphPresentation_of_pieceEmbeddings` (consumer of the builder
  `exists_regularCutData_of_pieceEmbeddings`): injective Raw pieces with the set-level cut data
  give a raw presentation of `W` (through B3);
* `DecompositionCertificate.nonempty_rawGraphPresentation_of_cycleUnions` (consumer of
  `exists_regularCutData_of_badVertexCount_eq_zero`): with `μ = 0` and the closed branches excluded,
  `W` is Raw as soon as every cycle union of every complete cycle partition is Raw;
* `DecompositionCertificate.nonempty_rawGraphPresentation_of_sphereMeasure_eq_zero_of_L1`
  (consumer of the torus assembly): the same statement in the induction measure `μ(D) = 0` of N4.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

/-- **Raw from injective Raw pieces with cut data.** -/
theorem exists_rawGraphPresentation_of_pieceEmbeddings {W : CompactCarrier.{u}} [Nonempty W.Carrier]
    {n : ℕ} (E : BoundaryTori W n) {ι σ : Type*} [Finite ι] [Finite σ]
    (Q : ι → PieceEmbedding W) (hcov : ⋃ j, range (Q j).map = univ)
    (S : σ → TorusSeam W)
    (hSdisj : Pairwise fun c d => Disjoint (S c).collar.target (S d).collar.target)
    (side : σ → Bool → ι)
    (hside : ∀ c b, range (Q (side c b)).map ∩ (S c).collar.target =
      (S c).collar '' {p | p ∈ signedCollarSource ∧ if b then p.2 ≤ 0 else 0 ≤ p.2})
    (own : Fin n → ι) (hown : ∀ i, (E.collar i).target ⊆ range (Q (own i)).map)
    (hbd : ∀ j (q : (Q j).Piece), (𝓡∂ 3).IsBoundaryPoint q →
      (∃ c b t, side c b = j ∧ (Q j).map q = (S c).collar (t, 0)) ∨
        (∃ i t, own i = j ∧ (Q j).map q = E.torusMap i t))
    (hover : ∀ j j', j ≠ j' → range (Q j).map ∩ range (Q j').map ⊆
      ⋃ c, range fun t => (S c).collar (t, 0))
    (hext : W.model.boundary W.Carrier = E.image)
    (hES : ∀ i c, Disjoint (E.collar i).target (S c).collar.target)
    (hraw : ∀ j, ∃ X : CompactCarrier.{u}, Nonempty (RawGraphPresentation X) ∧
      Nonempty (X.Carrier ≃ₘ⟮X.model, 𝓡∂ 3⟯ (Q j).Piece)) :
    Nonempty (RawGraphPresentation W) := by
  obtain ⟨R, hR⟩ := exists_regularCutData_of_pieceEmbeddings E Q hcov S hSdisj side hside own
    hown hbd hover hext hES
  refine exists_rawGraphPresentation_of_regularCutData R fun j => ?_
  obtain ⟨j', hj'⟩ := hR j
  rw [hj']
  exact hraw j'

namespace DecompositionCertificate

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} (D : DecompositionCertificate W E)

/-- **Raw from Raw cycle unions** (`μ = 0`, closed branches excluded). -/
theorem nonempty_rawGraphPresentation_of_cycleUnions [Nonempty W.Carrier]
    (hsph : D.sphereSeamCount = 0) (hbad : D.badVertexCount = 0)
    (hnz : ∀ k C, D.vertex k ≠ .closedZero C)
    (hslim : ¬ ∃ (k : Fin D.vertexCount) (P : PieceEmbedding W) (p : P.Piece → Circle)
      (hp : ContMDiff (𝓡∂ 3) (𝓡 1) ∞ p) (hsub : ∀ q, Surjective (mfderiv (𝓡∂ 3) (𝓡 1) p q))
      (fib : SlimFibre P p) (hcl : (𝓡∂ 3).boundary P.Piece = ∅),
      D.vertex k = .slim P (.overCircle p hp hsub fib hcl))
    (hcyc : ∀ (P : D.CyclePartition) (j : Fin P.cnt), ∃ X : CompactCarrier.{u},
      Nonempty (RawGraphPresentation X) ∧
        Nonempty (X.Carrier ≃ₘ⟮X.model, 𝓡∂ 3⟯ (P.roundedUnion j).Piece)) :
    Nonempty (RawGraphPresentation W) := by
  obtain ⟨δ, hδ, hδ1, P, R, hR⟩ :=
    D.exists_regularCutData_of_badVertexCount_eq_zero hsph hbad hnz hslim
  refine exists_rawGraphPresentation_of_regularCutData R fun j => ?_
  rcases hR j with ⟨j', hj'⟩ | h
  · rw [hj']
    exact hcyc P j'
  · exact h

/-- **The torus assembly in the induction measure** `μ(D) = 0` (L1 as one plain hypothesis). -/
theorem nonempty_rawGraphPresentation_of_sphereMeasure_eq_zero_of_L1 [Nonempty W.Carrier]
    (hμ : D.sphereMeasure = 0)
    (hnz : ∀ k C, D.vertex k ≠ .closedZero C)
    (hslim : ¬ ∃ (k : Fin D.vertexCount) (P : PieceEmbedding W) (p : P.Piece → Circle)
      (hp : ContMDiff (𝓡∂ 3) (𝓡 1) ∞ p) (hsub : ∀ q, Surjective (mfderiv (𝓡∂ 3) (𝓡 1) p q))
      (fib : SlimFibre P p) (hcl : (𝓡∂ 3).boundary P.Piece = ∅),
      D.vertex k = .slim P (.overCircle p hp hsub fib hcl))
    (hprodD : D.RimProduct)
    (hL1 : ∀ (C : BallHandleCycle W) (_hprod : C.RimProduct)
      (_hint : ∀ k, range (C.ball k).map ⊆ (W.interior : Set W.Carrier)),
      Nonempty (solidTorusCarrier.{u}.Carrier ≃ₘ⟮solidTorusCarrier.{u}.model, 𝓡∂ 3⟯
        C.union.Piece)) :
    Nonempty (RawGraphPresentation W) := by
  have hsph : D.sphereSeamCount = 0 := by
    unfold sphereMeasure at hμ
    omega
  have hbad : D.badVertexCount = 0 := by
    unfold sphereMeasure at hμ
    omega
  exact D.nonempty_rawGraphPresentation_of_badVertexCount_eq_zero_of_L1 hsph hbad hnz hslim
    hprodD hL1

end DecompositionCertificate

end GC.GraphManifold.Assembly
