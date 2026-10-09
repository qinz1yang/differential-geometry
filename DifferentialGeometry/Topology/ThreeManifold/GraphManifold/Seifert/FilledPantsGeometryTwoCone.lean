import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.FilledPantsGeometryBound

/-!
# The `H² × ℝ` geometry of a two-cone filled pants block

Lane A5 (design `docs/geometrization/handoffs/20261004-design-a5-filled-pants-assembly.md`, §0 route
D and §6 tier T4, with review 21). The two-cone fold restricted to its open domain,
`foldRestrict`, is a surjective local diffeomorphism onto the interior of the block; its
same-image pairs are `FoldRel`-related (`foldRel_of_foldMap_eq`), which is the pair condition of
`metricFiberCompatible_of_foldPairs`, and the proper exhaustion `twoConeExhaust` has a uniformly
bounded differential along the fold (`exists_gradient_bound`), so `GeometricStructure.ofFold`
gives an interior geometry of model `.hyperbolicProduct` (`twoConeGeometryOfFold`).
-/

set_option autoImplicit false

noncomputable section
open Set Complex Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Geometry
open scoped Topology ComplexConjugate ContDiff Manifold

universe u

namespace GC.Seifert

namespace TwoConeFold

namespace Fold

open ConeShape

section Geometry

variable {W : CompactCarrier.{u}} {d : SeifertData} (C : SeifertBlockCharts W d)
  (m₁ m₂ : Fin d.fillingCount) (hk : d.k = 3)
  (hj : ∀ m : Fin d.fillingCount, (C.port (.inr m)).val ≠ 0)
  (hp : ∀ m : Fin d.fillingCount, 0 < (d.fillingSlope m).1)
  {σ : ConeShape} (D : σ.FoldData)
  (hθ₁ : σ.θ₁ * (chartNumbers C m₁ m₂).p₁ = Real.pi)
  (hθ₂ : σ.θ₂ * (chartNumbers C m₁ m₂).p₂ = Real.pi)
  (hc₁ : C.tubeCentre m₁ = ((3 / 2 : ℝ) : ℂ)) (hc₂ : C.tubeCentre m₂ = ((-(3 / 2) : ℝ) : ℂ))
  (hall : ∀ m, m = m₁ ∨ m = m₂)

def foldRestrict (y : foldDomain C m₁ m₂ D hθ₁ hθ₂) : W.pieceInterior ⊤ :=
  foldMap C m₁ m₂ hk D hθ₁ hθ₂ y

include hj hp hc₁ hc₂ in
theorem isLocalDiffeomorph_foldRestrict :
    letI := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior ⊤)
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (foldRestrict C m₁ m₂ hk D hθ₁ hθ₂) := by
  let _ := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior ⊤)
  intro y
  exact IsLocalDiffeomorphAt.comp
    (hg := isLocalDiffeomorphAt_foldMap C m₁ m₂ hk hj hp D hθ₁ hθ₂ hc₁ hc₂ y.2)
    (hf := isLocalDiffeomorph_subtype_val (foldDomain C m₁ m₂ D hθ₁ hθ₂) y)

include hj hp hc₁ hc₂ hall in
theorem surjective_foldRestrict : Function.Surjective (foldRestrict C m₁ m₂ hk D hθ₁ hθ₂) := by
  intro x
  obtain ⟨y, hy, hyx⟩ := surjective_foldMap C m₁ m₂ hk hj hp D hθ₁ hθ₂ hc₁ hc₂ hall x
  exact ⟨⟨y, hy⟩, hyx⟩

include hj hp hc₁ hc₂ in
theorem foldRestrict_pairs (y y' : foldDomain C m₁ m₂ D hθ₁ hθ₂)
    (h : foldRestrict C m₁ m₂ hk D hθ₁ hθ₂ y = foldRestrict C m₁ m₂ hk D hθ₁ hθ₂ y') :
    ∃ γ : ModelCoordinates ≃ₘ⟮𝓡 3, 𝓡 3⟯ ModelCoordinates,
      Diffeomorph.pullbackMetric (coordinateModelMetric .hyperbolicProduct) γ =
        coordinateModelMetric .hyperbolicProduct ∧ γ (y : ModelCoordinates) = y' ∧
        ∃ U : TopologicalSpace.Opens ModelCoordinates, (y : ModelCoordinates) ∈ U ∧
          ∃ hUN : (U : Set ModelCoordinates) ⊆ foldDomain C m₁ m₂ D hθ₁ hθ₂,
            ∃ hmaps : MapsTo γ (U : Set ModelCoordinates) (foldDomain C m₁ m₂ D hθ₁ hθ₂),
              ∀ z : U, foldRestrict C m₁ m₂ hk D hθ₁ hθ₂ ⟨γ (z : ModelCoordinates),
                hmaps z.property⟩ = foldRestrict C m₁ m₂ hk D hθ₁ hθ₂
                  ⟨(z : ModelCoordinates), hUN z.property⟩ := by
  obtain ⟨γ, hγ, hyy, U, hyU, hUN, hmaps, hF⟩ :=
    foldRel_of_foldMap_eq C m₁ m₂ hk hj hp D hθ₁ hθ₂ hc₁ hc₂ y.2 y'.2 h
  exact ⟨γ, hγ, hyy, U, hyU, hUN, hmaps, fun z => hF z z.property⟩

include hj hp hc₁ hc₂ in
theorem exists_gradient_bound :
    letI := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior ⊤)
    ∃ K : NNReal, 0 < K ∧ ∀ y : foldDomain C m₁ m₂ D hθ₁ hθ₂, ∀ v : TangentSpace (𝓡 3) y,
      ‖mfderiv (𝓡 3) 𝓘(ℝ) (twoConeExhaust C hk D ∘ foldRestrict C m₁ m₂ hk D hθ₁ hθ₂) y v‖ ≤
        K * Real.sqrt
          (((coordinateModelMetric .hyperbolicProduct).restrictOpen
            (foldDomain C m₁ m₂ D hθ₁ hθ₂)).inner y v v) := by
  let _ := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior ⊤)
  obtain ⟨K, hK1, hK⟩ := exists_bound_fderiv_exhaustFn C m₁ m₂ hk hj hp D hθ₁ hθ₂ hc₁ hc₂
  refine ⟨⟨K, by linarith⟩, by
    change (0 : ℝ) < K
    linarith, fun y v => ?_⟩
  have heq : twoConeExhaust C hk D ∘ foldRestrict C m₁ m₂ hk D hθ₁ hθ₂ =
      exhaustFn C m₁ m₂ hk D hθ₁ hθ₂ ∘
        (Subtype.val : foldDomain C m₁ m₂ D hθ₁ hθ₂ → ModelCoordinates) := rfl
  have hd1 : MDifferentiableAt (𝓡 3) 𝓘(ℝ) (exhaustFn C m₁ m₂ hk D hθ₁ hθ₂)
      (y : ModelCoordinates) :=
    (((contDiffOn_exhaustFn C m₁ m₂ hk hj hp D hθ₁ hθ₂ hc₁ hc₂).contDiffAt
      ((foldDomain C m₁ m₂ D hθ₁ hθ₂).isOpen.mem_nhds y.2)).differentiableAt
        (by simp)).mdifferentiableAt
  have hd2 : MDifferentiableAt (𝓡 3) (𝓡 3)
      (Subtype.val : foldDomain C m₁ m₂ D hθ₁ hθ₂ → ModelCoordinates) y :=
    (contMDiff_subtype_val (I := 𝓡 3) (n := ∞)).mdifferentiableAt (by simp)
  have key := hK y y.2 v
  have e1 : mfderiv (𝓡 3) 𝓘(ℝ) (exhaustFn C m₁ m₂ hk D hθ₁ hθ₂) (y : ModelCoordinates) v =
      fderiv ℝ (exhaustFn C m₁ m₂ hk D hθ₁ hθ₂) y v := by
    rw [mfderiv_eq_fderiv]
    rfl
  have e2 : ((coordinateModelMetric .hyperbolicProduct).restrictOpen
      (foldDomain C m₁ m₂ D hθ₁ hθ₂)).inner y v v =
        coordinateInner .hyperbolicProduct y v v :=
    (SmoothRiemannianMetric.restrictOpen_inner _ _ _ _ _).trans
      (coordinateModelMetric_inner _ _ _ _)
  rw [heq, mfderiv_comp y hd1 hd2, ContinuousLinearMap.comp_apply]
  erw [mfderiv_subtype_val_apply, e1, e2, Real.norm_eq_abs]
  exact key

def twoConeGeometryOfFold : W.InteriorGeometry ⊤ := by
  letI := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior ⊤)
  letI := Manifold.interiorIsManifold W.model ∞ (M := W.pieceInterior ⊤)
  have hF := isLocalDiffeomorph_foldRestrict C m₁ m₂ hk hj hp D hθ₁ hθ₂ hc₁ hc₂
  have hsurj := surjective_foldRestrict C m₁ m₂ hk hj hp D hθ₁ hθ₂ hc₁ hc₂ hall
  have hcompat := metricFiberCompatible_of_foldPairs (coordinateModelMetric .hyperbolicProduct)
    (foldDomain C m₁ m₂ D hθ₁ hθ₂) (foldRestrict C m₁ m₂ hk D hθ₁ hθ₂) hF
    (foldRestrict_pairs C m₁ m₂ hk hj hp D hθ₁ hθ₂ hc₁ hc₂)
  have hcomplete : RiemannianMetricComplete
      (foldMetric ((coordinateModelMetric .hyperbolicProduct).restrictOpen
        (foldDomain C m₁ m₂ D hθ₁ hθ₂)) (foldRestrict C m₁ m₂ hk D hθ₁ hθ₂) hF hsurj
          hcompat) := by
    obtain ⟨K, hK, hb⟩ := exists_gradient_bound C m₁ m₂ hk hj hp D hθ₁ hθ₂ hc₁ hc₂
    exact foldMetric_complete_of_proper _ _ hF hsurj hcompat
      ((contMDiff_twoConeExhaust C m₁ m₂ hk hj hp D hθ₁ hθ₂ hc₁ hc₂ hall).of_le (by simp))
      (isProperMap_twoConeExhaust C m₁ m₂ hk hj hp D hθ₁ hθ₂ hc₁ hc₂ hall) hK hb
  exact GeometricStructure.ofFold
    ((coordinateModelMetric .hyperbolicProduct).restrictOpen (foldDomain C m₁ m₂ D hθ₁ hθ₂))
    ((coordinateModelMetric_hasThurstonAtlas .hyperbolicProduct).foldRestrictOpen
      (foldDomain C m₁ m₂ D hθ₁ hθ₂)) (by decide) (foldRestrict C m₁ m₂ hk D hθ₁ hθ₂) hF hsurj
    hcompat hcomplete

theorem twoConeGeometryOfFold_model :
    letI := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior ⊤)
    letI := Manifold.interiorIsManifold W.model ∞ (M := W.pieceInterior ⊤)
    (twoConeGeometryOfFold C m₁ m₂ hk hj hp D hθ₁ hθ₂ hc₁ hc₂ hall).model =
      ThurstonModel.hyperbolicProduct :=
  rfl

end Geometry

end Fold

end TwoConeFold

end GC.Seifert
