import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC41RowSFR

/-!
# Consumers of the FC41 row `fc41_row_SFR`

Lane S-FC41 (suffix `_SFR`), group G1. Every conjunct of `fc41_row_SFR` (numbered 1–18 in its
docstring) is used by one of the theorems below, each obtained from the row by projection:

* `nonempty_rawGraphPresentation_of_fc41_row_SFR` — the μ-recursion of FC42 with the six step
  packets S5, N2, N3, A4, A3 and L1 (conjuncts 12–17) read off the row: a certificate without a
  closed zero vertex whose rim charts satisfy the rim-product clause gives a raw presentation;
* `exists_rawGraphPresentation_or_aux_nonneg_of_fc41_row_SFR` — **FC42, form (b), from the row**:
  the same six packets fed to
  `exists_rawGraphPresentation_or_aux_nonneg_of_certificate_of_rimProduct_of_steps`;
* `exists_rawGraphPresentation_or_closedGeometric_of_fc41_row_SFR` — FC42 in the form of the closed
  chapter-14 threshold (a raw presentation, or a closed carrier with a spherical, `S² × ℝ` or
  Euclidean geometric structure): conjunct 9 after the previous theorem; no admitted space-form
  recognition is used;
* `exists_rawGraphPresentation_of_circleBundle_of_fc41_row_SFR` — the slim circle-base branch of
  FC42 (torus or sphere fibre over `1`) from conjuncts 10, 11 and 6;
* `fc41_row_edgeCirclePiece_raw_SFR` — a circle-base edge piece is diffeomorphic to a carrier with a
  raw presentation (conjuncts 18 and 4), the `hpiece` shape of conjunct 2;
* `fc41_row_regularCut_solidTorus_or_twisted_SFR` and
  `fc41_row_torusPresentation_solidTorus_or_twisted_SFR` — the FC42 torus assembly: all pieces solid
  tori or twisted interval bundles over the Klein bottle (conjuncts 4, 5 with 2 respectively 1);
* `fc41_row_connectedSum_cyclic_SFR` and `fc41_row_connectedSum_projective_sphereTwoTimesCircle_SFR`
  — connected sums of cyclic spherical space forms, and `RP³ # (S² × S¹)` (conjuncts 3, 8 and 3, 6,
  7).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

/-- **The μ-recursion of FC42 from the row `fc41_row_SFR`**: no closed zero vertex and the
rim-product clause give a raw presentation. -/
theorem nonempty_rawGraphPresentation_of_fc41_row_SFR
    (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier] {n : ℕ} {E : BoundaryTori W n}
    (D : DecompositionCertificate W E) (hnz : ∀ k C, D.vertex k ≠ .closedZero C)
    (hprod : D.RimProduct) : Nonempty (RawGraphPresentation W) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hS5, hN2, hN3, hA4, hA3, hL1, -⟩ := fc41_row_SFR.{u}
  exact nonempty_rawGraphPresentation_of_rimProduct_of_steps hL1 hS5 hN2 hN3 hA4 hA3 W D hnz hprod

/-- **FC42, form (b), from the row `fc41_row_SFR`.** -/
theorem exists_rawGraphPresentation_or_aux_nonneg_of_fc41_row_SFR
    (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier] {n : ℕ} {E : BoundaryTori W n}
    (D : DecompositionCertificate W E) (hprod : D.RimProduct) :
    Nonempty (RawGraphPresentation W) ∨
      (W.model.boundary W.Carrier = ∅ ∧ ∃ g' : SmoothRiemannianMetric W.model W.Carrier,
        DifferentialGeometry.Geometry.Riemannian.SectionalBoundedBelow g' 0) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hS5, hN2, hN3, hA4, hA3, hL1, -⟩ := fc41_row_SFR.{u}
  exact exists_rawGraphPresentation_or_aux_nonneg_of_certificate_of_rimProduct_of_steps
    hL1 hS5 hN2 hN3 hA4 hA3 W D hprod

/-- **FC42 in the closed threshold form**: a raw presentation, or a closed carrier with a spherical,
`S² × ℝ` or Euclidean geometric structure. The closed zero vertex enters only through the
auxiliary `sec ≥ 0` disjunct of the previous theorem and the disjunctive conjunct 9 of the row. -/
theorem exists_rawGraphPresentation_or_closedGeometric_of_fc41_row_SFR
    (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier] {n : ℕ} {E : BoundaryTori W n}
    (D : DecompositionCertificate W E) (hprod : D.RimProduct) :
    Nonempty (RawGraphPresentation W) ∨
      (W.model.boundary W.Carrier = ∅ ∧
        ∃ G : GC.Geometry.GeometricStructure W.model W.Carrier,
          G.model = .spherical ∨ G.model = .sphericalProduct ∨ G.model = .euclidean) := by
  obtain ⟨-, -, -, -, -, -, -, -, h9, -⟩ := fc41_row_SFR.{u}
  exact h9 W (exists_rawGraphPresentation_or_aux_nonneg_of_fc41_row_SFR W D hprod)

/-- **The slim circle-base branch from the row**: a closed carrier fibred over the circle whose
fibre over `1` is an embedded torus or an embedded sphere has a raw presentation (torus: conjunct
10; sphere: conjunct 11 recognizes `S² × S¹`, conjunct 6 gives its presentation). -/
theorem exists_rawGraphPresentation_of_circleBundle_of_fc41_row_SFR (W : CompactCarrier.{u})
    [ConnectedSpace W.Carrier] (hW : W.model.boundary W.Carrier = ∅) (p : W.Carrier → Circle)
    (hp : ContMDiff W.model (𝓡 1) ∞ p) (hsub : ∀ x, Surjective (mfderiv W.model (𝓡 1) p x))
    (hfibre : (∃ f : Torus → W.Carrier, IsSmoothEmbedding torusModel W.model ∞ f ∧
        range f = p ⁻¹' {1}) ∨
      ∃ f : ClosureSphere.{u} → W.Carrier, IsSmoothEmbedding (𝓡 2) W.model ∞ f ∧
        range f = p ⁻¹' {1}) :
    Nonempty (RawGraphPresentation W) := by
  obtain ⟨-, -, -, -, -, h6, -, -, -, h10, h11, -⟩ := fc41_row_SFR.{u}
  rcases hfibre with ⟨f, hf, hr⟩ | ⟨f, hf, hr⟩
  · exact h10 W hW p hp hsub f hf hr
  · exact h6 W (h11 W hW p hp hsub f hf hr)

/-- **A circle-base edge piece is a solid torus with a raw presentation**: the `hpiece` shape of
conjunct 2 (conjunct 18 gives the diffeomorphism from the standard solid torus, conjunct 4 the
presentation of the standard solid torus). -/
theorem fc41_row_edgeCirclePiece_raw_SFR {W : CompactCarrier.{u}} (P : EdgeCirclePiece W) :
    ∃ X : CompactCarrier.{u}, Nonempty (RawGraphPresentation X) ∧
      Nonempty (X.Carrier ≃ₘ⟮X.model, 𝓡∂ 3⟯ P.piece.Piece) := by
  obtain ⟨-, -, -, h4, -, -, -, -, -, -, -, -, -, -, -, -, -, h18⟩ := fc41_row_SFR.{u}
  obtain ⟨G, -⟩ := h4 (W := solidTorusCarrier.{u})
    ⟨Diffeomorph.refl solidTorusCarrier.{u}.model solidTorusCarrier.{u}.Carrier ∞⟩
  exact ⟨solidTorusCarrier.{u}, ⟨G⟩, h18 P⟩

/-- **The FC42 torus assembly from regular cut data (conjunct 2), pieces solid tori or twisted
interval bundles over the Klein bottle (conjuncts 4 and 5).** -/
theorem fc41_row_regularCut_solidTorus_or_twisted_SFR {W : CompactCarrier.{u}} {n : ℕ}
    {E : BoundaryTori W n} (D : RegularCutData W E)
    (h : ∀ j,
      Nonempty (solidTorusCarrier.{u}.Carrier ≃ₘ⟮solidTorusCarrier.{u}.model, 𝓡∂ 3⟯
        (D.piece j).Piece) ∨
      Nonempty (mobiusBundleCarrier.{u}.Carrier ≃ₘ⟮mobiusBundleCarrier.{u}.model, 𝓡∂ 3⟯
        (D.piece j).Piece)) :
    Nonempty (RawGraphPresentation W) := by
  obtain ⟨-, h2, -, h4, h5, -⟩ := fc41_row_SFR.{u}
  refine h2 D fun j => ?_
  rcases h j with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · obtain ⟨G, -⟩ := h4 (W := solidTorusCarrier.{u})
      ⟨Diffeomorph.refl solidTorusCarrier.{u}.model solidTorusCarrier.{u}.Carrier ∞⟩
    exact ⟨solidTorusCarrier.{u}, ⟨G⟩, ⟨e⟩⟩
  · obtain ⟨G, -⟩ := h5 (W := mobiusBundleCarrier.{u})
      ⟨Diffeomorph.refl mobiusBundleCarrier.{u}.model mobiusBundleCarrier.{u}.Carrier ∞⟩
    exact ⟨mobiusBundleCarrier.{u}, ⟨G⟩, ⟨e⟩⟩

/-- **The torus assembly from a torus presentation (conjunct 1), components solid tori or twisted
interval bundles over the Klein bottle (conjuncts 4 and 5).** -/
theorem fc41_row_torusPresentation_solidTorus_or_twisted_SFR {W : CompactCarrier.{u}}
    (T : TorusPresentation W)
    (h : ∀ i,
      Nonempty (solidTorusCarrier.{u}.Carrier ≃ₘ⟮solidTorusCarrier.{u}.model,
        (T.Component i).model⟯ (T.Component i).Carrier) ∨
      Nonempty (mobiusBundleCarrier.{u}.Carrier ≃ₘ⟮mobiusBundleCarrier.{u}.model,
        (T.Component i).model⟯ (T.Component i).Carrier)) :
    Nonempty (RawGraphPresentation W) := by
  obtain ⟨h1, -, -, h4, h5, -⟩ := fc41_row_SFR.{u}
  refine h1 T fun i => ?_
  rcases h i with he | he
  · obtain ⟨G, -⟩ := h4 he
    exact ⟨G⟩
  · obtain ⟨G, -⟩ := h5 he
    exact ⟨G⟩

/-- **Connected sums of cyclic spherical space forms** (conjuncts 3 and 8). -/
theorem fc41_row_connectedSum_cyclic_SFR (G₁ G₂ : SphericalSpaceFormGroup)
    [IsCyclic G₁.group] [IsCyclic G₂.group] :
    Nonempty (RawGraphPresentation (NoCuts.carrier
      (connectedSum G₁.manifold.ulift.{0, u} G₂.manifold.ulift.{0, u}))) := by
  obtain ⟨-, -, h3, -, -, -, -, h8, -⟩ := fc41_row_SFR.{u}
  exact h3 _ _ (h8 G₁) (h8 G₂)

/-- **`RP³ # (S² × S¹)`** (conjuncts 3, 6 and 7). -/
theorem fc41_row_connectedSum_projective_sphereTwoTimesCircle_SFR :
    Nonempty (RawGraphPresentation (NoCuts.carrier
      (connectedSum projectiveThreeSpaceLift.{u} sphereTwoTimesCircleLift.ulift.{0, u}))) := by
  obtain ⟨-, -, h3, -, -, h6, h7, -⟩ := fc41_row_SFR.{u}
  refine h3 _ _ ?_ ?_
  · obtain ⟨G, -⟩ := h7 (W := NoCuts.carrier projectiveThreeSpaceLift.{u})
      ⟨Diffeomorph.refl _ _ ∞⟩
    exact ⟨G⟩
  · exact h6 (NoCuts.carrier sphereTwoTimesCircleLift.ulift.{0, u})
      ⟨sphereTwoTimesCircleUliftProduct.{u}.trans
        ((uliftDiffeomorph (𝓡 2) (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)).symm.prodCongr
          sphereOneDiffeomorphCircle.symm)⟩

end GC.GraphManifold.Assembly
