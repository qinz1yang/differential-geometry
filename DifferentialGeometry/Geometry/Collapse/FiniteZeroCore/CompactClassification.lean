import DifferentialGeometry.Geometry.Thurston.NonnegativeClassificationUnconditional
import DifferentialGeometry.Geometry.Thurston.ProjectiveSumDihedral
import DifferentialGeometry.Geometry.Thurston.SphericalProductCyclicQuotient
import DifferentialGeometry.Geometry.Thurston.SphericalProductUniversalCover
import DifferentialGeometry.Geometry.Thurston.SphericalStructureStandard
import DifferentialGeometry.Geometry.Thurston.FlatPrime
import DifferentialGeometry.Geometry.Metric.Approximation.NonnegativeSectional

/-!
# LFR53: compact finite three-model classification

Chapter 13, row LFR53 (`thm:collapse-compact-finite-classification`). A closed connected oriented
`3`-manifold with a `C^n` metric (`2 ≤ n`) of nonnegative finite-order sectional curvature has
smooth type

* a spherical space form `S³/Γ` (oriented diffeomorphism),
* `S² × S¹`,
* `RP³ # RP³`, or
* a compact orientable flat manifold: it carries a complete metric with a Euclidean Thurston atlas
  and is covered by `ℝ³` through a smooth covering local diffeomorphism.

Assembly, with no new analysis:
* LFR50 (`MetricSmoothing.exists_smooth_sectional_nonneg_of_finite_metric`) gives a smooth
  metric with `sec ≥ 0` on the SAME carrier;
* the chapter 5–7 classification U1
  (`GC.Geometry.exists_geometricStructure_of_boundaryless_unconditional`) gives a spherical,
  `S² × ℝ` or Euclidean geometric structure;
* the chapter 7 translations into smooth types: the space-form covering theorem
  (`exists_orientedDiffeomorph_sphericalSpaceForm_of_constantPositiveSectionalCurvature`), the
  `S² × ℝ` deck presentation (`SphericalProduct.exists_classified_presentation_of_universalCover`,
  `sphericalProductUniversalCover`) with its cyclic (`cyclicCylinderQuotientIsSphereTwoTimesCircle`)
  and dihedral (`dihedralCylinderQuotientIsProjectiveSum`) quotients, and the flat exponential
  covering (`GC.Endpoint.exists_isCoveringMap_of_euclidean`).

Not delivered: the Bieberbach rewriting of the flat case as `T³/Γ` with a finite group `Γ` (no
Bieberbach theorem in the tree); the row states it as an equivalent form.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Collapse

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The four smooth types of LFR53 for a closed connected oriented `3`-manifold `P`: a spherical
space form, `S² × S¹`, `RP³ # RP³`, or a compact orientable flat manifold (a complete Euclidean
geometric structure, covered by `ℝ³`). -/
def IsCompactNonnegativeType (P : ConnectedClosedOrientedManifold.{u} 3) : Prop :=
  (∃ Γ : SphericalSpaceFormGroup, Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      P.toClosedOrientedManifold Γ.manifold.toClosedOrientedManifold)) ∨
    Nonempty (P.Carrier ≃ₘ⟮𝓡 3, (𝓡 2).prod (𝓡 1)⟯ SphereTwoTimesCircle) ∨
    Nonempty (P.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
      (connectedSum projectiveThreeSpaceLift.{u} projectiveThreeSpaceLift.{u}).Carrier) ∨
    ((∃ G : GC.Geometry.GeometricStructure (𝓡 3) P.Carrier, G.model = .euclidean) ∧
      ∃ p : E3 → P.Carrier, IsCoveringMap p ∧ Function.Surjective p ∧
        IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ p)

/-- A spherical geometric structure gives a spherical space form. -/
theorem isCompactNonnegativeType_of_spherical (P : ConnectedClosedOrientedManifold.{u} 3)
    (G : GC.Geometry.GeometricStructure (𝓡 3) P.Carrier) (hG : G.model = .spherical) :
    IsCompactNonnegativeType P := by
  have hA : GC.Geometry.HasThurstonAtlas G.metric .spherical := hG ▸ G.atlas
  exact Or.inl
    (exists_orientedDiffeomorph_sphericalSpaceForm_of_constantPositiveSectionalCurvature P G.metric
      (GC.Geometry.constantPositiveSectionalCurvatureMetric_of_hasThurstonAtlas_spherical hA))

/-- An `S² × ℝ` geometric structure gives `S² × S¹` (cyclic deck group) or `RP³ # RP³`
(dihedral deck group). -/
theorem isCompactNonnegativeType_of_sphericalProduct (P : ConnectedClosedOrientedManifold.{u} 3)
    (G : GC.Geometry.GeometricStructure (𝓡 3) P.Carrier) (hG : G.model = .sphericalProduct) :
    IsCompactNonnegativeType P := by
  obtain ⟨Γ, ⟨pr⟩, hcls⟩ :=
    GC.Geometry.SphericalProduct.exists_classified_presentation_of_universalCover
      GC.Geometry.SphericalProduct.sphericalProductUniversalCover P G hG
  rcases hcls with ⟨A, c, hA, hc, rfl⟩ | ⟨c₁, c₂, hne, rfl⟩
  · exact Or.inr (Or.inl
      (GC.Geometry.SphericalProduct.cyclicCylinderQuotientIsSphereTwoTimesCircle P.Carrier A c hA
        hc pr))
  · exact Or.inr (Or.inr (Or.inl
      (GC.Geometry.SphericalProduct.dihedralCylinderQuotientIsProjectiveSum P.Carrier c₁ c₂ hne
        pr)))

/-- A Euclidean geometric structure gives a compact orientable flat manifold covered by `ℝ³`. -/
theorem isCompactNonnegativeType_of_euclidean (P : ConnectedClosedOrientedManifold.{u} 3)
    (G : GC.Geometry.GeometricStructure (𝓡 3) P.Carrier) (hG : G.model = .euclidean) :
    IsCompactNonnegativeType P :=
  Or.inr (Or.inr (Or.inr ⟨⟨G, hG⟩, GC.Endpoint.exists_isCoveringMap_of_euclidean P G hG⟩))

/-- **LFR53, smooth-metric kernel.** A closed connected oriented `3`-manifold with a smooth metric
of nonnegative sectional curvature has one of the four smooth types. -/
theorem isCompactNonnegativeType_of_sectional_nonneg (P : ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) P.Carrier) (hsec : Riemannian.SectionalBoundedBelow g 0) :
    IsCompactNonnegativeType P := by
  obtain ⟨G, hG | hG | hG⟩ :=
    GC.Geometry.exists_geometricStructure_of_boundaryless_unconditional g hsec
  · exact isCompactNonnegativeType_of_spherical P G hG
  · exact isCompactNonnegativeType_of_sphericalProduct P G hG
  · exact isCompactNonnegativeType_of_euclidean P G hG

private instance finrankThreeNeZero : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩

/-- **LFR53 (the row).** A closed connected oriented `3`-manifold with a `C^n` Riemannian metric,
`2 ≤ n`, of nonnegative finite-order sectional curvature has one of the four smooth types: a
spherical space form, `S² × S¹`, `RP³ # RP³`, or a compact orientable flat manifold. The
classification uses LFR50's auxiliary smooth metric on the same carrier; the original metric is
not compared with it. -/
theorem isCompactNonnegativeType_of_finite_metric (P : ConnectedClosedOrientedManifold.{u} 3)
    {n : ℕ∞ω} (hn : (2 : ℕ∞ω) ≤ n)
    (g : Bundle.ContMDiffRiemannianMetric (𝓡 3) n E3 (TangentSpace (𝓡 3) : P.Carrier → Type _))
    (hsec : ∀ x (v w : TangentSpace (𝓡 3) x), 0 ≤ g.sectionalCurvature x v w) :
    IsCompactNonnegativeType P := by
  obtain ⟨h, hh⟩ :=
    MetricSmoothing.exists_smooth_sectional_nonneg_of_finite_metric (by simp) hn g hsec
  exact isCompactNonnegativeType_of_sectional_nonneg P h hh

end DifferentialGeometry.Geometry.Collapse
