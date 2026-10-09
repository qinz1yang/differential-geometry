import DifferentialGeometry.Topology.Engulfing.Obstacle.Approximation.ObstacleExpansionApproximation

namespace DifferentialGeometry.Topology.Engulfing

open Set _root_.Geometry _root_.Topology

noncomputable section

variable {E : Type*} [DecidableEq E]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {n d p : ℕ}

structure RelativeGeneralPositionApproximation
    (K L : SimplicialComplex ℝ E) (T : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)))
    (f : C(K.space, EuclideanSpace ℝ (Fin n))) (d p : ℕ) (ε : ℝ) where
  augmentation : ObstacleAugmentation K L T f d p
  expansions : augmentation.preservesSourceExpansions
  vertices : EuclideanSpace ℝ (Fin augmentation.ambientDimension) → EuclideanSpace ℝ (Fin n)
  correction : EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n)
  approximation : C(K.space, EuclideanSpace ℝ (Fin n))
  generalPosition : ∀ s : Finset (EuclideanSpace ℝ (Fin augmentation.ambientDimension)),
    (s : Set (EuclideanSpace ℝ (Fin augmentation.ambientDimension))) ⊆ augmentation.joint.vertices →
      s.card ≤ n + 1 → AffineIndependent ℝ (fun x : s => vertices x.val)
  fixed_exact : ∀ x : augmentation.joint.space, x.val ∈ augmentation.fixedImage.space →
    correctedInterpolant augmentation.joint augmentation.joint_finite vertices correction x =
      augmentation.oldMap x
  source_exact : ∀ x, approximation x =
    correctedInterpolant augmentation.joint augmentation.joint_finite vertices correction
      (augmentation.sourceMap x)
  relative : ∀ x : K.space, x.val ∈ L.space → approximation x = f x
  near : ∀ x, ‖approximation x - f x‖ < ε
  correction_near : ∀ y, ‖correction y - y‖ < ε
  inverse_near : ∀ y, ‖correction.symm y - y‖ < ε
  obstacle_image : T.space = ⋃ s ∈ augmentation.obstacleImage.faces,
    correction '' convexHull ℝ (vertices ''
      (s : Set (EuclideanSpace ℝ (Fin augmentation.ambientDimension))))
  raw_oscillation : ∀ s ∈ augmentation.joint.faces, ∀ x y : augmentation.joint.space,
    x.val ∈ convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin augmentation.ambientDimension))) →
    y.val ∈ convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin augmentation.ambientDimension))) →
    ‖interpolateVertices augmentation.joint augmentation.joint_finite vertices x -
      interpolateVertices augmentation.joint augmentation.joint_finite vertices y‖ < 5 * ε

theorem ObstacleAugmentation.exists_relativeGeneralPositionApproximation
    {K L : SimplicialComplex ℝ E} {T : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n))}
    {f : C(K.space, EuclideanSpace ℝ (Fin n))}
    (a : ObstacleAugmentation K L T f d p) (ha : a.preservesSourceExpansions)
    {ε : ℝ} (hε : 0 < ε) : Nonempty (RelativeGeneralPositionApproximation K L T f d p ε) := by
  obtain ⟨b, hb, w, H, g, hgp, hfix, hg, hrel, hnear, hH, hHinv, hT, hosc⟩ :=
    a.exists_compatible_generalPosition ha hε
  exact ⟨⟨b, hb, w, H, g, hgp, hfix, hg, hrel, hnear, hH, hHinv, hT, hosc⟩⟩

theorem exists_relativeGeneralPositionApproximation
    (K L : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hLK : L.faces ⊆ K.faces)
    (T : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n))) (hT : T.faces.Finite)
    (hKd : ∀ s ∈ K.faces, s.card ≤ d + 1)
    (hTp : ∀ s ∈ T.faces, s.card ≤ p + 1) (hpd : p ≤ d)
    (f : C(K.space, EuclideanSpace ℝ (Fin n)))
    (hPL : ∀ s ∈ L.faces, ∃ A : E →ᵃ[ℝ] EuclideanSpace ℝ (Fin n),
      ∀ x : K.space, x.val ∈ convexHull ℝ (s : Set E) → f x = A x.val)
    (hinj : InjOn f (Subtype.val ⁻¹' L.space)) {ε : ℝ} (hε : 0 < ε) :
    Nonempty (RelativeGeneralPositionApproximation K L T f d p ε) := by
  obtain ⟨a⟩ := exists_obstacleAugmentation K L hK hLK T hT hKd hTp hpd f hPL hinj
  obtain ⟨b, hb⟩ := a.exists_preserving_source_expansions hK hKd
  exact b.exists_relativeGeneralPositionApproximation hb hε

end

end DifferentialGeometry.Topology.Engulfing
