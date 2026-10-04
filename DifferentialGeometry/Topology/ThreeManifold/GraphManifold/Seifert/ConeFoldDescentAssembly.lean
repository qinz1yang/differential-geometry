import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ConeFoldDescentBound
import DifferentialGeometry.Geometry.Thurston.FoldDescent
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.FilledPantsGeometryNormalise

/-!
# Assembly: the `H² × ℝ` geometry of the one-cone block from a cone fold

Route D (`TH/FoldDescent.lean`). For a shape `σ` with `θ₁ p = π`, `θ₂ = 0` and a two-dimensional
fold `D : σ.FoldData`, the fold `foldMap : descentDomain → (descentCarrier c).pieceInterior ⊤` is a
surjective local diffeomorphism whose same-image pairs are related by isometries of the
`.hyperbolicProduct` coordinate metric preserving the fold near the first point
(`foldMap_pairs`), so the restricted coordinate metric descends
(`metricFiberCompatible_of_foldPairs`); the descended metric is complete by the proper exhaustion
`carrierExhaust` with the uniform gradient bound of `exists_bound_fderiv_exhaustFn`
(`foldMetric_complete_of_proper`). `GeometricStructure.ofFold` then gives an interior geometry
of model `.hyperbolicProduct` (`descentGeometry`). For `c = coneFillingOf p q` the carrier is
the standard one-cone carrier, which yields `oneConeBlock_interiorGeometry_of_foldData`, the
input of the filled-pants assembly (`exists_oneConeInteriorGeometry_of_standard`).
-/

set_option autoImplicit false
noncomputable section
open Complex Set Filter Topology
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Geometry
open scoped ContDiff ComplexConjugate Manifold

universe u

namespace GC.Seifert

namespace ConeShape.FoldData

variable {σ : ConeShape} (D : σ.FoldData) (c : ConeFilling) (hθ : σ.θ₁ * c.p = Real.pi)

theorem exists_gradient_bound (hσ : σ.θ₂ = 0) :
    letI := Manifold.interiorChartedSpace (descentCarrier.{u} c).model ∞
      (M := (descentCarrier.{u} c).pieceInterior ⊤)
    ∃ C : NNReal, 0 < C ∧ ∀ y : D.descentDomain c hθ, ∀ v : TangentSpace (𝓡 3) y,
      ‖mfderiv (𝓡 3) 𝓘(ℝ) (D.carrierExhaust.{u} c ∘ D.foldMap c hθ hσ) y v‖ ≤
        C * Real.sqrt
          (((coordinateModelMetric .hyperbolicProduct).restrictOpen (D.descentDomain c hθ)).inner
            y v v) := by
  let _ := Manifold.interiorChartedSpace (descentCarrier.{u} c).model ∞
      (M := (descentCarrier.{u} c).pieceInterior ⊤)
  obtain ⟨C, hC1, hC⟩ := D.exists_bound_fderiv_exhaustFn.{u} c hθ hσ
  refine ⟨⟨C, by linarith⟩, by
    change (0 : ℝ) < C
    linarith, fun y v => ?_⟩
  have heq : D.carrierExhaust.{u} c ∘ D.foldMap c hθ hσ =
      D.exhaustFn.{u} c ∘ (Subtype.val : D.descentDomain c hθ → ModelCoordinates) := rfl
  have hd1 : MDifferentiableAt (𝓡 3) 𝓘(ℝ) (D.exhaustFn.{u} c) (y : ModelCoordinates) :=
    (((D.contDiffOn_exhaustFn.{u} c hθ hσ).contDiffAt
      ((D.descentDomain c hθ).isOpen.mem_nhds y.2)).differentiableAt (by simp)).mdifferentiableAt
  have hd2 : MDifferentiableAt (𝓡 3) (𝓡 3) (Subtype.val : D.descentDomain c hθ → ModelCoordinates)
      y := (contMDiff_subtype_val (I := 𝓡 3) (n := ∞)).mdifferentiableAt (by simp)
  have key := hC y y.2 v
  have e1 : mfderiv (𝓡 3) 𝓘(ℝ) (D.exhaustFn.{u} c) (y : ModelCoordinates) v =
      fderiv ℝ (D.exhaustFn.{u} c) y v := by
    rw [mfderiv_eq_fderiv]
    rfl
  have e2 : ((coordinateModelMetric .hyperbolicProduct).restrictOpen (D.descentDomain c hθ)).inner
      y v v = coordinateInner .hyperbolicProduct y v v :=
    (SmoothRiemannianMetric.restrictOpen_inner _ _ _ _ _).trans
      (coordinateModelMetric_inner _ _ _ _)
  rw [heq, mfderiv_comp y hd1 hd2, ContinuousLinearMap.comp_apply]
  erw [mfderiv_subtype_val_apply, e1, e2, Real.norm_eq_abs]
  exact key

def descentGeometry (hσ : σ.θ₂ = 0) : (descentCarrier.{u} c).InteriorGeometry ⊤ := by
  letI := Manifold.interiorChartedSpace (descentCarrier.{u} c).model ∞
    (M := (descentCarrier.{u} c).pieceInterior ⊤)
  letI := Manifold.interiorIsManifold (descentCarrier.{u} c).model ∞
    (M := (descentCarrier.{u} c).pieceInterior ⊤)
  have hF := D.isLocalDiffeomorph_foldMap.{u} c hθ hσ
  have hsurj := D.foldMap_surjective.{u} c hθ hσ
  have hcompat := metricFiberCompatible_of_foldPairs (coordinateModelMetric .hyperbolicProduct)
    (D.descentDomain c hθ) (D.foldMap.{u} c hθ hσ) hF (D.foldMap_pairs.{u} c hθ hσ)
  have hcomplete : RiemannianMetricComplete
      (foldMetric ((coordinateModelMetric .hyperbolicProduct).restrictOpen (D.descentDomain c hθ))
        (D.foldMap.{u} c hθ hσ) hF hsurj hcompat) := by
    obtain ⟨C, hC, hb⟩ := D.exists_gradient_bound.{u} c hθ hσ
    exact foldMetric_complete_of_proper _ _ hF hsurj hcompat (D.contMDiff_carrierExhaust c)
      (D.isProperMap_carrierExhaust c) hC hb
  exact GeometricStructure.ofFold
    ((coordinateModelMetric .hyperbolicProduct).restrictOpen (D.descentDomain c hθ))
    ((coordinateModelMetric_hasThurstonAtlas .hyperbolicProduct).foldRestrictOpen
      (D.descentDomain c hθ)) (by decide) (D.foldMap.{u} c hθ hσ) hF hsurj hcompat hcomplete

theorem descentGeometry_model (hσ : σ.θ₂ = 0) :
    letI := Manifold.interiorChartedSpace (descentCarrier.{u} c).model ∞
      (M := (descentCarrier.{u} c).pieceInterior ⊤)
    letI := Manifold.interiorIsManifold (descentCarrier.{u} c).model ∞
      (M := (descentCarrier.{u} c).pieceInterior ⊤)
    (D.descentGeometry.{u} c hθ hσ).model = ThurstonModel.hyperbolicProduct :=
  rfl

end ConeShape.FoldData

theorem oneConeBlock_interiorGeometry_of_foldData {p : ℕ} {q : ℤ} (hp : 2 ≤ p)
    (hpq : Int.gcd (p : ℤ) q = 1) {σ : ConeShape} (hθ₁ : σ.θ₁ * p = Real.pi) (hθ₂ : σ.θ₂ = 0)
    (hF : σ.FoldData) :
    ∃ G : (oneConeStandardCarrier.{u} p q hp hpq).InteriorGeometry ⊤,
      letI := Manifold.interiorChartedSpace (oneConeStandardCarrier.{u} p q hp hpq).model ∞
        (M := (oneConeStandardCarrier.{u} p q hp hpq).pieceInterior ⊤)
      letI := Manifold.interiorIsManifold (oneConeStandardCarrier.{u} p q hp hpq).model ∞
        (M := (oneConeStandardCarrier.{u} p q hp hpq).pieceInterior ⊤)
      G.model = ThurstonModel.hyperbolicProduct :=
  ⟨hF.descentGeometry (coneFillingOf p q hp hpq) hθ₁ hθ₂,
    hF.descentGeometry_model (coneFillingOf p q hp hpq) hθ₁ hθ₂⟩

end GC.Seifert
