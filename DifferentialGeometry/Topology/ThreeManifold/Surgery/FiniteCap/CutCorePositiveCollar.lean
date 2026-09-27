import DifferentialGeometry.Topology.Manifold.HalfClosedIntervalSmoothMaps
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.CutCoreCollarSmooth
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.PositiveCuttingCoordinates
import DifferentialGeometry.Topology.Manifold.InverseFunction.ContDiffOn

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry.Metric DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev PosE3 := EuclideanSpace ℝ (Fin 3)
private abbrev PosS2 := Metric.sphere (0 : PosE3) 1
private abbrev PosIC := (𝓡 2).prod 𝓘(ℝ)
private abbrev PosIR := (𝓡 2).prod (𝓡∂ 1)
private local instance : Fact (Module.finrank ℝ PosE3 = 2 + 1) := ⟨by simp⟩

def positiveCuttingCollarInclusion (B : ℝ) : positiveCuttingCylinder B → PosS2 × Ico (0 : ℝ) B :=
  fun q => (q.val.1, ⟨q.val.2, q.property.1.le, q.property.2⟩)

theorem positiveCuttingCollarInclusion_contMDiff {B : ℝ} (hB : 0 < B) :
    let : ChartedSpace (EuclideanHalfSpace 1) (Ico (0 : ℝ) B) := halfClosedIntervalChartedSpace hB
    ContMDiff PosIC PosIR ∞ (positiveCuttingCollarInclusion B) := by
  let : ChartedSpace (EuclideanHalfSpace 1) (Ico (0 : ℝ) B) := halfClosedIntervalChartedSpace hB
  have hf : ContMDiff PosIC (𝓡 2) ∞ (fun q : positiveCuttingCylinder B => q.val.1) :=
    contMDiff_fst.comp (contMDiff_subtype_val (I := PosIC) (U := positiveCuttingCylinder B))
  have ht : ContMDiff PosIC 𝓘(ℝ) ∞ (fun q : positiveCuttingCylinder B => q.val.2) :=
    contMDiff_snd.comp (contMDiff_subtype_val (I := PosIC) (U := positiveCuttingCylinder B))
  exact hf.prodMk (contMDiff_halfClosedInterval_of_val PosIC hB
    (fun q : positiveCuttingCylinder B => ⟨q.val.2, q.property.1.le, q.property.2⟩) ht)

def cuttingPositiveCylinderMap {δ : ℝ} (hδ : 0 < δ) (b : Bool) :
    positiveCuttingCylinder (cuttingCollarWidth δ) → bufferedCylinder δ :=
  cuttingCollarCylinderMap hδ b ∘ positiveCuttingCollarInclusion (cuttingCollarWidth δ)

theorem cuttingPositiveCylinderMap_contMDiff {δ : ℝ} (hδ : 0 < δ) (b : Bool) :
    ContMDiff PosIC PosIC ∞ (cuttingPositiveCylinderMap hδ b) := by
  let : ChartedSpace (EuclideanHalfSpace 1) (Ico (0 : ℝ) (cuttingCollarWidth δ)) :=
    halfClosedIntervalChartedSpace (cuttingCollarWidth_pos hδ)
  exact (cuttingCollarCylinderMap_contMDiff hδ b).comp
    (positiveCuttingCollarInclusion_contMDiff (cuttingCollarWidth_pos hδ))

theorem cuttingPositiveCylinderMap_injective {δ : ℝ} (hδ : 0 < δ) (b : Bool) :
    Injective (cuttingPositiveCylinderMap hδ b) := by
  intro q r he
  have hα := (isEmbedding_cuttingCollarCylinderMap hδ b).injective he
  have h₁ : q.val.1 = r.val.1 := congrArg
    (fun z : PosS2 × Ico (0 : ℝ) (cuttingCollarWidth δ) => z.1) hα
  have h₂ : q.val.2 = r.val.2 := congrArg
    (fun z : PosS2 × Ico (0 : ℝ) (cuttingCollarWidth δ) => z.2.val) hα
  exact Subtype.ext (Prod.ext h₁ h₂)

theorem cuttingPositiveCylinderMap_mfderiv {δ : ℝ} (hδ : 0 < δ) (b : Bool)
    (q : positiveCuttingCylinder (cuttingCollarWidth δ)) :
    mfderiv PosIC PosIC (cuttingPositiveCylinderMap hδ b) q =
      mfderiv PosIC PosIC (cylinderAxialDiffeomorph (I := 𝓡 2) (M := PosS2)
        (cuttingSign b) (cuttingSign b) (cuttingSign_sq b)) q.val := by
  let D := cylinderAxialDiffeomorph (I := 𝓡 2) (M := PosS2)
    (cuttingSign b) (cuttingSign b) (cuttingSign_sq b)
  have hκ := cuttingPositiveCylinderMap_contMDiff hδ b
  have hl := mfderiv_comp q
    ((contMDiff_subtype_val (I := PosIC) (U := bufferedCylinder δ) (n := ∞)).mdifferentiableAt (by simp))
    (hκ.mdifferentiableAt (by simp))
  have hr := mfderiv_comp q (D.contMDiff.mdifferentiableAt (by simp))
    ((contMDiff_subtype_val (I := PosIC) (U := positiveCuttingCylinder (cuttingCollarWidth δ)) (n := ∞)).mdifferentiableAt (by simp))
  rw [mfderiv_subtype_val] at hl hr
  dsimp only [TangentSpace] at hl hr ⊢
  have hraw : (Subtype.val : bufferedCylinder δ → PosS2 × ℝ) ∘ cuttingPositiveCylinderMap hδ b =
      D ∘ (Subtype.val : positiveCuttingCylinder (cuttingCollarWidth δ) → PosS2 × ℝ) := rfl
  rw [hraw] at hl
  apply ContinuousLinearMap.ext
  intro v
  have hlv : mfderiv PosIC PosIC (D ∘ (Subtype.val : positiveCuttingCylinder (cuttingCollarWidth δ) → PosS2 × ℝ)) q v =
      mfderiv PosIC PosIC (cuttingPositiveCylinderMap hδ b) q v :=
    congrArg (fun L : (EuclideanSpace ℝ (Fin 2) × ℝ) →L[ℝ] (EuclideanSpace ℝ (Fin 2) × ℝ) => L v) hl
  have hrv : mfderiv PosIC PosIC (D ∘ (Subtype.val : positiveCuttingCylinder (cuttingCollarWidth δ) → PosS2 × ℝ)) q v =
      mfderiv PosIC PosIC D q.val v := congrArg (fun L : (EuclideanSpace ℝ (Fin 2) × ℝ) →L[ℝ] (EuclideanSpace ℝ (Fin 2) × ℝ) => L v) hr
  exact hlv.symm.trans hrv

theorem cuttingPositiveCylinderMap_isLocalDiffeomorph {δ : ℝ} (hδ : 0 < δ) (b : Bool) :
    IsLocalDiffeomorph PosIC PosIC ∞ (cuttingPositiveCylinderMap hδ b) := by
  apply isLocalDiffeomorph_of_injective_mfderiv _ (cuttingPositiveCylinderMap_contMDiff hδ b) _ rfl
  intro q
  rw [cuttingPositiveCylinderMap_mfderiv]
  exact ((cylinderAxialDiffeomorph (I := 𝓡 2) (M := PosS2)
    (cuttingSign b) (cuttingSign b) (cuttingSign_sq b)).isLocalDiffeomorph.mfderivToContinuousLinearEquiv (by simp) q.val).injective

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable [TopologicalSpace M] [ChartedSpace H M]
variable {ι : Type*} {precision : ι → ℝ}

theorem cuttingPositiveAmbient_isLocalDiffeomorph
    (hδ : ∀ i, 0 < precision i) (f : ∀ i : ι, bufferedCylinder (precision i) → M)
    (hs : ∀ i, IsLocalDiffeomorph PosIC I ∞ (f i)) (b : ι × Bool) :
    IsLocalDiffeomorph PosIC I ∞ (f b.1 ∘ cuttingPositiveCylinderMap (hδ b.1) b.2) :=
  fun q => ((cuttingPositiveCylinderMap_isLocalDiffeomorph (hδ b.1) b.2) q).comp I M
    (hs b.1 (cuttingPositiveCylinderMap (hδ b.1) b.2 q))
end DifferentialGeometry.Topology.ThreeManifold.Surgery
