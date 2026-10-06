import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SelectedSmoothCore74
import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.LPA05DiscCoreEmbedding74
import DifferentialGeometry.Topology.VectorBundle.DiscCoreConnected74
import DifferentialGeometry.Topology.Manifold.MorseHalfSpaceSmooth

/-!
# Draft 74, G32: the solid parametrization of a LFR54 disc core

Lane C14-REG-CHAIN (by S-REG-CHAIN3), G32. A sublevel `A` of the original source `X` carried by
an ambient partial diffeomorphism `Ψ : X ⇀ Nc` onto the disc core
`D_T = {y | ‖(D.symm y).2‖ ≤ T}` of a disc bundle `D : E ≃ Nc` over a compact connected base
(the data of LPA05's sublevel clauses) is a `SolidParam74`:

* `SolidParam74.ofDiscCore74`: the piece is the core with the boundary charts of
  `discCoreChartedSpace`, re-expressed in the model `𝓡∂ 3` (`morseHalfSpaceEuclideanChartedSpace`);
  the map is `y ↦ Ψ⁻¹ y`; its smooth embedding is `discCore_comp_isSmoothEmbedding_R74` after the
  source model change; compact (`isCompact_discCore`), connected (`connectedSpace_discCore_R74`),
  second countable (σ-compact charted space).
* `Diffeomorph.ofMorseSource74` / `ofMorseTarget74`: the model change of the diffeomorphisms of
  LPA05's clauses (`morseModelWithCornersHalfSpace 2` ↔ `𝓡∂ 3`).
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

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "I3" => 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))

section ModelChange

variable {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℝ E'] {H' : Type}
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {M : Type} [TopologicalSpace M] [ChartedSpace (MorseHalfSpace 2) M]
  {Y : Type} [TopologicalSpace Y] [ChartedSpace H' Y]

/-- **Source model change.** A diffeomorphism out of a manifold with the Morse boundary charts is a
diffeomorphism out of the same space with the charts in the model `𝓡∂ 3`. -/
def Diffeomorph.ofMorseSource74 (Φ : Diffeomorph (morseModelWithCornersHalfSpace 2) J M Y ∞) :
    letI := morseHalfSpaceEuclideanChartedSpace 2 M
    Diffeomorph (𝓡∂ 3) J M Y ∞ :=
  letI := morseHalfSpaceEuclideanChartedSpace 2 M
  { toEquiv := Φ.toEquiv
    contMDiff_toFun :=
      (contMDiff_chartedSpaceTransHomeomorph_source_iff
        (morseModelWithCornersHalfSpace 2) (𝓡∂ 3) (morseHalfSpaceHomeomorphism 2)
        (morseEuclideanCoordinates 2)
        (morseHalfSpaceHomeomorphism_model 2) J).mpr Φ.contMDiff
    contMDiff_invFun :=
      (contMDiff_chartedSpaceTransHomeomorph_iff
        (morseModelWithCornersHalfSpace 2) (𝓡∂ 3) (morseHalfSpaceHomeomorphism 2)
        (morseEuclideanCoordinates 2)
        (morseHalfSpaceHomeomorphism_model 2) J).mpr Φ.symm.contMDiff }

/-- **Target model change.** A diffeomorphism into a manifold with the Morse boundary charts is a
diffeomorphism into the same space with the charts in the model `𝓡∂ 3`. -/
def Diffeomorph.ofMorseTarget74 (Φ : Diffeomorph J (morseModelWithCornersHalfSpace 2) Y M ∞) :
    letI := morseHalfSpaceEuclideanChartedSpace 2 M
    Diffeomorph J (𝓡∂ 3) Y M ∞ :=
  letI := morseHalfSpaceEuclideanChartedSpace 2 M
  { toEquiv := Φ.toEquiv
    contMDiff_toFun :=
      (contMDiff_chartedSpaceTransHomeomorph_iff
        (morseModelWithCornersHalfSpace 2) (𝓡∂ 3) (morseHalfSpaceHomeomorphism 2)
        (morseEuclideanCoordinates 2)
        (morseHalfSpaceHomeomorphism_model 2) J).mpr Φ.contMDiff
    contMDiff_invFun :=
      (contMDiff_chartedSpaceTransHomeomorph_source_iff
        (morseModelWithCornersHalfSpace 2) (𝓡∂ 3) (morseHalfSpaceHomeomorphism 2)
        (morseEuclideanCoordinates 2)
        (morseHalfSpaceHomeomorphism_model 2) J).mpr
        Φ.symm.contMDiff }

end ModelChange

section DiscCore

variable {EB F : Type} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [FiniteDimensional ℝ EB] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {HB : Type} [TopologicalSpace HB]
  {IB : ModelWithCorners ℝ EB HB} [IB.Boundaryless]
  {B : Type} [TopologicalSpace B] [ChartedSpace HB B] [IsManifold IB ∞ B]
  [CompactSpace B] [ConnectedSpace B]
  {V : B → Type} [TopologicalSpace (TotalSpace F V)]
  [∀ b, NormedAddCommGroup (V b)] [∀ b, InnerProductSpace ℝ (V b)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V IB]
  [IsContMDiffRiemannianBundle IB ∞ F V]
  {X : Type} [TopologicalSpace X] [ChartedSpace E3 X] [IsManifold I3 ∞ X]
  {N : Type} [TopologicalSpace N] [T2Space N] [ChartedSpace E3 N]

omit [CompactSpace B] [ConnectedSpace B] [T2Space N] in
/-- The disc core is a manifold for its Morse boundary charts. -/
theorem discCore_isManifold_R74
    (D : Diffeomorph (IB.prod 𝓘(ℝ, F)) I3 (TotalSpace F V) N ∞)
    (hd : Module.finrank ℝ (EB × F) = 2 + 1) (T : ℝ) (hT : 0 < T) :
    let := discCoreChartedSpace D hd T hT
    IsManifold (morseModelWithCornersHalfSpace 2) ∞ {x : N // ‖(D.symm x).2‖ ≤ T} := by
  let := normClosedDiscBundleChartedSpace (IB := IB) (V := V) hd T hT
  let := closedDiscBundleChartedSpace (IB := IB) (V := V) hd T hT
  let := closedDiscBundle_isManifold (IB := IB) (V := V) hd T hT
  let := normClosedDiscBundle_isManifold (IB := IB) (V := V) hd T hT
  let := discCoreChartedSpace D hd T hT
  exact DifferentialGeometry.Manifold.Homeomorph.instIsManifoldPullback
    (I := morseModelWithCornersHalfSpace 2) (n := ∞) (discCoreHomeomorph D T).symm

/-- **The solid parametrization of a LFR54 disc core** (D74-8): the core with its boundary charts
in the model `𝓡∂ 3`, mapped to `X` by `Ψ⁻¹`. -/
def SolidParam74.ofDiscCore74 {A : Set X}
    (D : Diffeomorph (IB.prod 𝓘(ℝ, F)) I3 (TotalSpace F V) N ∞)
    (hd : Module.finrank ℝ (EB × F) = 2 + 1) (T : ℝ) (hT : 0 < T)
    (Ψ : PartialDiffeomorph I3 I3 X N ∞) (hAs : A ⊆ Ψ.source)
    (hA : Ψ '' A = {y | ‖(D.symm y).2‖ ≤ T}) : SolidParam74.{0, 0} A :=
  letI := discCoreChartedSpace D hd T hT
  haveI := discCore_isManifold_R74 D hd T hT
  letI := morseHalfSpaceEuclideanChartedSpace 2
    {x : N // ‖(D.symm x).2‖ ≤ T}
  haveI : IsManifold (𝓡∂ 3) ∞ {x : N // ‖(D.symm x).2‖ ≤ T} :=
    morseHalfSpaceEuclidean_isManifold 2 _
  haveI : CompactSpace {x : N // ‖(D.symm x).2‖ ≤ T} :=
    isCompact_iff_compactSpace.mp (isCompact_discCore D T)
  haveI : SecondCountableTopology (EuclideanHalfSpace 3) :=
    inferInstanceAs (SecondCountableTopology {x : E3 // 0 ≤ x 0})
  haveI : SecondCountableTopology {x : N // ‖(D.symm x).2‖ ≤ T} :=
    ChartedSpace.secondCountable_of_sigmaCompact (EuclideanHalfSpace 3)
      {x : N // ‖(D.symm x).2‖ ≤ T}
  haveI : ConnectedSpace {x : N // ‖(D.symm x).2‖ ≤ T} :=
    connectedSpace_discCore_R74 D hT.le
  { Piece := {x : N // ‖(D.symm x).2‖ ≤ T}
    param := fun y => Ψ.symm y.1
    embedding :=
      (isSmoothEmbedding_chartedSpaceTransHomeomorph_source_iff
        (morseModelWithCornersHalfSpace 2) (𝓡∂ 3)
        (morseHalfSpaceHomeomorphism 2)
        (morseEuclideanCoordinates 2)
        (morseHalfSpaceHomeomorphism_model 2) I3).mpr
        (discCore_comp_isSmoothEmbedding_R74 D hd T hT Ψ (by
          intro y hy
          obtain ⟨a, ha, rfl⟩ : y ∈ Ψ '' A := by rw [hA]; exact hy
          exact Ψ.map_source (hAs ha)))
    range_eq := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        obtain ⟨a, ha, hay⟩ : y.1 ∈ Ψ '' A := by rw [hA]; exact y.2
        change Ψ.symm y.1 ∈ A
        rw [← hay]
        have hl : Ψ.symm (Ψ a) = a := Ψ.left_inv (hAs ha)
        rw [hl]
        exact ha
      · intro hx
        refine ⟨⟨Ψ x, ?_⟩, Ψ.left_inv (hAs hx)⟩
        have : Ψ x ∈ Ψ '' A := ⟨x, hx, rfl⟩
        rw [hA] at this
        exact this }

end DiscCore

end GC.GraphManifold.Assembly
