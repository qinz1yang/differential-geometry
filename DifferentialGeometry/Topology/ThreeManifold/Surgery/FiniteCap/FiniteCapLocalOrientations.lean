import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapNeighborhoodSmooth
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCoreInteriorSmooth
import DifferentialGeometry.Topology.Manifold.SmoothOrientationComposition

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
variable {ι : Type*} [Finite ι] {precision : ι → ℝ} {L : ℝ}
variable (hdim : Module.finrank ℝ E = 3) (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
variable (hs : ∀ i, IsLocalDiffeomorph IC I ∞ (f i))
local notation "LocalOrientationQ" => FiniteCapQuotient hL hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj

def finiteCapRadialCoordinateMap (b : ι × Bool) :
    let : ChartedSpace E3 LocalOrientationQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    finiteCapNeighborhoodOpens hL hδ f hf hdisj b → E3 := by
  let : ChartedSpace E3 LocalOrientationQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  exact Subtype.val ∘ finiteCapNeighborhoodDiffeomorph I hdim hL hδ f hf hdisj hs b

theorem finiteCapRadialCoordinateMap_eq_openChart (b : ι × Bool)
    (p : finiteCapNeighborhoodOpens hL hδ f hf hdisj b) :
    let : ChartedSpace E3 LocalOrientationQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    finiteCapRadialCoordinateMap I hdim hL hδ f hf hdisj hs b p =
      finiteCapOpenChart hL hδ f hf hdisj b p.val := by
  let : ChartedSpace E3 LocalOrientationQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  exact (finiteCapOpenChart_apply hL hδ f hf hdisj b p).symm

theorem finiteCapRadialCoordinateMap_contMDiff (b : ι × Bool) :
    let : ChartedSpace E3 LocalOrientationQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    ContMDiff (𝓡 3) (𝓡 3) ∞ (finiteCapRadialCoordinateMap I hdim hL hδ f hf hdisj hs b) := by
  let : ChartedSpace E3 LocalOrientationQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  exact (contMDiff_subtype_val (I := 𝓡 3) (U := finiteCapRadialBall (L := L) (precision := precision) b)).comp
    (finiteCapNeighborhoodDiffeomorph I hdim hL hδ f hf hdisj hs b).contMDiff

theorem finiteCapRadialCoordinateMap_mfderiv_bijective (b : ι × Bool)
    (p : finiteCapNeighborhoodOpens hL hδ f hf hdisj b) :
    let : ChartedSpace E3 LocalOrientationQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    Bijective (mfderiv (𝓡 3) (𝓡 3) (finiteCapRadialCoordinateMap I hdim hL hδ f hf hdisj hs b) p) := by
  let : ChartedSpace E3 LocalOrientationQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  let V := finiteCapRadialBall (L := L) (precision := precision) b
  let D := finiteCapNeighborhoodDiffeomorph I hdim hL hδ f hf hdisj hs b
  exact bijective_mfderiv_comp (𝓡 3) (𝓡 3) (𝓡 3) D (Subtype.val : V → E3) D.contMDiff
    (contMDiff_subtype_val (I := 𝓡 3) (U := V))
    (fun q => (D.mfderivToContinuousLinearEquiv (by simp) q).bijective)
    (bijective_mfderiv_open_val (𝓡 3) V) p

def finiteCapNeighborhoodSmoothOrientation (b : ι × Bool)
    (o : Orientation ℝ E3 (Fin (Module.finrank ℝ E3))) :
    let : ChartedSpace E3 LocalOrientationQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ LocalOrientationQ := finiteCapQuotient_isManifold hdim hL hδ f hf hdisj hs
    SmoothOrientation (𝓡 3) (finiteCapNeighborhoodOpens hL hδ f hf hdisj b) := by
  let : ChartedSpace E3 LocalOrientationQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ LocalOrientationQ := finiteCapQuotient_isManifold hdim hL hδ f hf hdisj hs
  exact pullbackSmoothOrientation (𝓡 3) (𝓡 3) (finiteCapRadialCoordinateMap I hdim hL hδ f hf hdisj hs b)
    (finiteCapRadialCoordinateMap_contMDiff I hdim hL hδ f hf hdisj hs b)
    (finiteCapRadialCoordinateMap_mfderiv_bijective I hdim hL hδ f hf hdisj hs b)
    (euclideanSmoothOrientation E3 o)

theorem finiteCapNeighborhoodSmoothOrientation_pushforward (b : ι × Bool)
    (o : Orientation ℝ E3 (Fin (Module.finrank ℝ E3)))
    (p : finiteCapNeighborhoodOpens hL hδ f hf hdisj b) :
    let : ChartedSpace E3 LocalOrientationQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ LocalOrientationQ := finiteCapQuotient_isManifold hdim hL hδ f hf hdisj hs
    tangentOrientationEquiv (differentialEquivOfBijective (𝓡 3) (𝓡 3)
      (finiteCapRadialCoordinateMap I hdim hL hδ f hf hdisj hs b)
      (finiteCapRadialCoordinateMap_mfderiv_bijective I hdim hL hδ f hf hdisj hs b) p).toLinearEquiv
        ((finiteCapNeighborhoodSmoothOrientation I hdim hL hδ f hf hdisj hs b o).val p) = o := by
  let : ChartedSpace E3 LocalOrientationQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ LocalOrientationQ := finiteCapQuotient_isManifold hdim hL hδ f hf hdisj hs
  exact pullbackSmoothOrientation_pushforward (𝓡 3) (𝓡 3)
    (finiteCapRadialCoordinateMap I hdim hL hδ f hf hdisj hs b)
    (finiteCapRadialCoordinateMap_contMDiff I hdim hL hδ f hf hdisj hs b)
    (finiteCapRadialCoordinateMap_mfderiv_bijective I hdim hL hδ f hf hdisj hs b)
    (euclideanSmoothOrientation E3 o) p

def finiteOldAmbientCoordinateMap :
    let : ChartedSpace E3 LocalOrientationQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    finiteCoreInteriorOpens hL hδ f hf hdisj → M := by
  let : ChartedSpace E3 LocalOrientationQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  exact Subtype.val ∘ (finiteCoreInteriorDiffeomorph I hdim hL hδ f hf hdisj hs).symm

theorem finiteOldAmbientCoordinateMap_contMDiff :
    let : ChartedSpace E3 LocalOrientationQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    ContMDiff (𝓡 3) I ∞ (finiteOldAmbientCoordinateMap I hdim hL hδ f hf hdisj hs) := by
  let : ChartedSpace E3 LocalOrientationQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  exact (contMDiff_subtype_val (I := I) (U := coreInteriorDomain f)).comp
    (finiteCoreInteriorDiffeomorph I hdim hL hδ f hf hdisj hs).symm.contMDiff

theorem finiteOldAmbientCoordinateMap_mfderiv_bijective
    (p : finiteCoreInteriorOpens hL hδ f hf hdisj) :
    let : ChartedSpace E3 LocalOrientationQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    Bijective (mfderiv (𝓡 3) I (finiteOldAmbientCoordinateMap I hdim hL hδ f hf hdisj hs) p) := by
  let : ChartedSpace E3 LocalOrientationQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  let D := (finiteCoreInteriorDiffeomorph I hdim hL hδ f hf hdisj hs).symm
  exact bijective_mfderiv_comp (𝓡 3) I I D (Subtype.val : coreInteriorDomain f → M) D.contMDiff
    (contMDiff_subtype_val (I := I) (U := coreInteriorDomain f))
    (fun q => (D.mfderivToContinuousLinearEquiv (by simp) q).bijective)
    (bijective_mfderiv_open_val I (coreInteriorDomain f)) p

def finiteOldSmoothOrientation (o : SmoothOrientation I M) :
    let : ChartedSpace E3 LocalOrientationQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ LocalOrientationQ := finiteCapQuotient_isManifold hdim hL hδ f hf hdisj hs
    SmoothOrientation (𝓡 3) (finiteCoreInteriorOpens hL hδ f hf hdisj) := by
  let : ChartedSpace E3 LocalOrientationQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ LocalOrientationQ := finiteCapQuotient_isManifold hdim hL hδ f hf hdisj hs
  exact pullbackSmoothOrientation (𝓡 3) I (finiteOldAmbientCoordinateMap I hdim hL hδ f hf hdisj hs)
    (finiteOldAmbientCoordinateMap_contMDiff I hdim hL hδ f hf hdisj hs)
    (finiteOldAmbientCoordinateMap_mfderiv_bijective I hdim hL hδ f hf hdisj hs) o

theorem finiteOldSmoothOrientation_pushforward (o : SmoothOrientation I M)
    (p : finiteCoreInteriorOpens hL hδ f hf hdisj) :
    let : ChartedSpace E3 LocalOrientationQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ LocalOrientationQ := finiteCapQuotient_isManifold hdim hL hδ f hf hdisj hs
    tangentOrientationEquiv (differentialEquivOfBijective (𝓡 3) I
      (finiteOldAmbientCoordinateMap I hdim hL hδ f hf hdisj hs)
      (finiteOldAmbientCoordinateMap_mfderiv_bijective I hdim hL hδ f hf hdisj hs) p).toLinearEquiv
        ((finiteOldSmoothOrientation I hdim hL hδ f hf hdisj hs o).val p) =
          o.val (finiteOldAmbientCoordinateMap I hdim hL hδ f hf hdisj hs p) := by
  let : ChartedSpace E3 LocalOrientationQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ LocalOrientationQ := finiteCapQuotient_isManifold hdim hL hδ f hf hdisj hs
  exact pullbackSmoothOrientation_pushforward (𝓡 3) I
    (finiteOldAmbientCoordinateMap I hdim hL hδ f hf hdisj hs)
    (finiteOldAmbientCoordinateMap_contMDiff I hdim hL hδ f hf hdisj hs)
    (finiteOldAmbientCoordinateMap_mfderiv_bijective I hdim hL hδ f hf hdisj hs) o p
end DifferentialGeometry.Topology.ThreeManifold.Surgery
