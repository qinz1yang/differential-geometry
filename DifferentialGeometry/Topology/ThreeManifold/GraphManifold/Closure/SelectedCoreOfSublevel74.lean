import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SelectedCoreOfDiscCore74
import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.LPA05SublevelTypeClause

/-!
# Draft 74, G32: the four non-closed LFR54 branches are selected smooth cores

Lane C14-REG-CHAIN (by S-REG-CHAIN3), G32. On the actual selected sublevel `A` of the original
source `X`, each of LPA05's non-closed sublevel predicates (`PointSoulCoreSublevel`,
`CircleSoulCoreSublevel`, `ProjectiveSoulCoreSublevel`, `KleinSoulCoreSublevel`, with a model `Nc`
that is only a charted space) gives a `SelectedSmoothCore74 A` of the matching branch (ball,
solid torus, punctured `ℝP³`, twisted interval bundle): the solid parametrization is
`SolidParam74.ofDiscCore74` and the model identification is the diffeomorphism of the clause after
the model change `morseModelWithCornersHalfSpace 2 ↔ 𝓡∂ 3`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Bundle Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly

open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.Topology.VectorBundle
open DifferentialGeometry.Topology.Morse
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Manifold (morseHalfSpaceHomeomorphism morseHalfSpaceHomeomorphism_model
  morseEuclideanCoordinates morseHalfSpaceEuclideanChartedSpace morseHalfSpaceEuclidean_isManifold
  contMDiff_chartedSpaceTransHomeomorph_source_iff contMDiff_chartedSpaceTransHomeomorph_iff
  isSmoothEmbedding_chartedSpaceTransHomeomorph_source_iff)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] ballCharts_ASMCERT ballSmooth_ASMCERT

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "I3" => 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))

variable {X : Type} [TopologicalSpace X] [ChartedSpace E3 X] [IsManifold I3 ∞ X]
  {Nc : Type} [TopologicalSpace Nc] [T2Space Nc] [ChartedSpace E3 Nc] {A : Set X}

/-- **`D³`: the point-soul branch is a selected ball core.** -/
theorem nonempty_selectedCore74_ofPointSoul (h : PointSoulCoreSublevel Nc A) :
    Nonempty (SelectedSmoothCore74.{0, 0} A) := by
  obtain ⟨F, i1, i2, i3, V, j1, j2, j3, j4, j5, j6, j7, D, hd, T₀, hT₀, Ψ, hAs, hΨA, Φ, -, -⟩ :=
    h
  let := discCoreChartedSpace D hd T₀ hT₀
  let := DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 2
  let S := SolidParam74.ofDiscCore74 D hd T₀ hT₀ Ψ hAs hΨA
  have e : S.Piece ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ClosedCell 3 :=
    Diffeomorph.ofMorseSource74 (M := {x : Nc // ‖(D.symm x).2‖ ≤ T₀}) Φ
  exact ⟨.ball S e⟩

/-- **`S¹ × D²`: the circle-soul branch is a selected solid-torus core.** -/
theorem nonempty_selectedCore74_ofCircleSoul (h : CircleSoulCoreSublevel Nc A) :
    Nonempty (SelectedSmoothCore74.{0, 0} A) := by
  obtain ⟨F, i1, i2, i3, V, j1, j2, j3, j4, j5, j6, j7, D, hd, T₀, hT₀, Ψ, hAs, hΨA, Φ, -⟩ := h
  let := discCoreChartedSpace D hd T₀ hT₀
  let S := SolidParam74.ofDiscCore74 D hd T₀ hT₀ Ψ hAs hΨA
  have e : GC.GraphManifold.solidTorusCarrier.{0}.Carrier ≃ₘ⟮
      GC.GraphManifold.solidTorusCarrier.{0}.model, 𝓡∂ 3⟯ S.Piece :=
    Diffeomorph.ofMorseTarget74 (M := {x : Nc // ‖(D.symm x).2‖ ≤ T₀}) Φ
  exact ⟨.solidTorus S e⟩

/-- **`ℝP³ ∖ int D³`: the surface-soul branch with a projective core.** -/
theorem nonempty_selectedCore74_ofProjectiveSoul
    (h : ProjectiveSoulCoreSublevel Nc A) : Nonempty (SelectedSmoothCore74.{0, 0} A) := by
  obtain ⟨B, k1, k2, k3, k4, k5, k6, F, i1, i2, i3, V, j1, j2, j3, j4, j5, j6, j7, D, hd, T₀,
    hT₀, Ψ, hAs, hΨA, cb, f, hf, hrange, -⟩ := h
  let := discCoreChartedSpace D hd T₀ hT₀
  let S := SolidParam74.ofDiscCore74 D hd T₀ hT₀ Ψ hAs hΨA
  have key := (isSmoothEmbedding_chartedSpaceTransHomeomorph_source_iff
      (morseModelWithCornersHalfSpace 2) (𝓡∂ 3)
      (morseHalfSpaceHomeomorphism 2)
      (morseEuclideanCoordinates 2)
      (morseHalfSpaceHomeomorphism_model 2) (𝓡 3)
      (f := f)).mpr hf
  let f' : S.Piece → projectiveThreeSpaceLift.{0}.Carrier := f
  have hf' : IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ f' := key
  exact ⟨.puncturedRP3 S cb f' hf' hrange⟩

/-- **`D(o(K))`: the surface-soul branch with a twisted interval bundle core.** -/
theorem nonempty_selectedCore74_ofKleinSoul (h : KleinSoulCoreSublevel Nc A) :
    Nonempty (SelectedSmoothCore74.{0, 0} A) := by
  obtain ⟨B, k1, k2, k3, k4, k5, k6, F, i1, i2, i3, V, j1, j2, j3, j4, j5, j6, j7, D, hd, T₀,
    hT₀, Ψ, hAs, hΨA, Φ, -⟩ := h
  let := discCoreChartedSpace D hd T₀ hT₀
  let S := SolidParam74.ofDiscCore74 D hd T₀ hT₀ Ψ hAs hΨA
  have e0 : S.Piece ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ GC.Seifert.mobiusBundleSet.{0} :=
    Diffeomorph.ofMorseSource74 (M := {x : Nc // ‖(D.symm x).2‖ ≤ T₀}) Φ
  have e : GC.Seifert.mobiusBundleCarrier.{0}.Carrier ≃ₘ⟮
      GC.Seifert.mobiusBundleCarrier.{0}.model, 𝓡∂ 3⟯ S.Piece :=
    e0.symm
  exact ⟨.twistedIBundle S e⟩

end GC.GraphManifold.Assembly
