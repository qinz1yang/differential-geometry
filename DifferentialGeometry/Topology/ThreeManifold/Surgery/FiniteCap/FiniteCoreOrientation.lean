import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapGlobalOrientation
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCoreOrientationCoordinates

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Topology.Manifold DifferentialGeometry.Topology.Manifold.Attachment
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev E2 := EuclideanSpace ℝ (Fin 2)
private abbrev ER := E2 × EuclideanSpace ℝ (Fin 1)
private abbrev IR := (𝓡 2).prod (𝓡∂ 1)
private abbrev IH := ModelProd E2 (EuclideanHalfSpace 1)
private abbrev S2 := Metric.sphere (0 : E3) 1
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)
private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
variable {ι : Type*} [Finite ι] {precision : ι → ℝ} {L : ℝ}
variable (hdim : Module.finrank ℝ E = 3) (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
variable (hs : ∀ i, IsLocalDiffeomorph IC I ∞ (f i))
local notation "OrientedQ" => FiniteCapQuotient hL hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj

theorem exists_finiteCapSmoothOrientation_preserving_core (o : SmoothOrientation I M) :
    let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
    let : ChartedSpace E3 OrientedQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ OrientedQ := finiteCapQuotient_isManifold hdim hL hδ f hf hdisj hs
    ∃ oE : (ι × Bool) → Orientation ℝ E3 (Fin (Module.finrank ℝ E3)),
      ∃ oQ : SmoothOrientation (𝓡 3) OrientedQ,
        (∀ b, oE b = (Module.finBasis ℝ E3).orientation ∨ oE b = -(Module.finBasis ℝ E3).orientation) ∧
        (∀ b : ι × Bool,
          letI := halfClosedIntervalChartedSpace (cuttingCollarWidth_pos (hδ b.1))
          letI := halfClosedInterval_isManifold (cuttingCollarWidth_pos (hδ b.1))
          ∀ q : S2 × Ico (0 : ℝ) (cuttingCollarWidth (precision b.1)),
            (radialCollarSmoothOrientation hL (cuttingCollarWidth_pos (hδ b.1)) (oE b)).val q =
              (cuttingCollarSmoothOrientation I hdim hδ f hf hdisj hs b o).val q) ∧
        (∀ p : finiteCoreInteriorOpens hL hδ f hf hdisj,
          oQ.val p.val = (finiteOldSmoothOrientation I hdim hL hδ f hf hdisj hs o).val p) ∧
        (∀ (b : ι × Bool) (p : finiteCapNeighborhoodOpens hL hδ f hf hdisj b),
          oQ.val p.val = (finiteCapNeighborhoodSmoothOrientation I hdim hL hδ f hf hdisj hs b (oE b)).val p) ∧
        ∀ p : cutCore f,
          tangentOrientationEquiv (differentialEquivOfBijective IR (𝓡 3)
            (finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj)
            (finiteCoreInclusion_mfderiv_bijective I hdim hL hδ f hf hdisj hs) p).toLinearEquiv
              ((cutCoreSmoothOrientation I hdim hδ f hf hdisj hs o).val p) =
                oQ.val (finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj p) := by
  let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  let : ChartedSpace E3 OrientedQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ OrientedQ := finiteCapQuotient_isManifold hdim hL hδ f hf hdisj hs
  obtain ⟨oE, oQ, hsign, hcollar, hOld, hCap⟩ := exists_finiteCapSmoothOrientation I hdim hL hδ f hf hdisj hs o
  refine ⟨oE, oQ, hsign, hcollar, hOld, hCap, ?_⟩
  let j := finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj
  let hbj := finiteCoreInclusion_mfderiv_bijective I hdim hL hδ f hf hdisj hs
  let OCore := cutCoreSmoothOrientation I hdim hδ f hf hdisj hs o
  have hPresCollar : ∀ (b : ι × Bool) (q : S2 × Ico (0 : ℝ) (cuttingCollarWidth (precision b.1))),
      tangentOrientationEquiv (differentialEquivOfBijective IR (𝓡 3) j hbj
        (cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b q)).toLinearEquiv
          (OCore.val (cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b q)) =
            oQ.val (j (cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b q)) := by
    intro b q
    let := halfClosedIntervalChartedSpace (cuttingCollarWidth_pos (hδ b.1))
    let := halfClosedInterval_isManifold (cuttingCollarWidth_pos (hδ b.1))
    let κ := cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b
    let ρ := radialCollarOrientationMap L (cuttingCollarWidth (precision b.1))
    let pN := finiteCoreCollarLift hL hδ f hf hdisj b q
    let C := finiteCapRadialCoordinateMap I hdim hL hδ f hf hdisj hs b
    let eK : ER ≃L[ℝ] ER := differentialEquivOfBijective IR IR κ
      (cuttingCollarMap_mfderiv_bijective I hdim hδ f hf hdisj hs b) q
    let eJ : ER ≃L[ℝ] E3 := differentialEquivOfBijective IR (𝓡 3) j hbj (κ q)
    let eC : E3 ≃L[ℝ] E3 := differentialEquivOfBijective (𝓡 3) (𝓡 3) C
      (finiteCapRadialCoordinateMap_mfderiv_bijective I hdim hL hδ f hf hdisj hs b) pN
    let eR : ER ≃L[ℝ] E3 := differentialEquivOfBijective IR (𝓡 3) ρ
      (radialCollarOrientationMap_mfderiv_bijective hL (cuttingCollarWidth_pos (hδ b.1))) q
    let OK := (cuttingCollarSmoothOrientation I hdim hδ f hf hdisj hs b o).val q
    let OR := (radialCollarSmoothOrientation hL (cuttingCollarWidth_pos (hδ b.1)) (oE b)).val q
    have hD : eR = (eK.trans eJ).trans eC := by
      apply ContinuousLinearEquiv.ext
      funext v
      exact congrArg (fun D : ER →L[ℝ] E3 => D v)
        (finiteCoreCollarLift_radial_mfderiv I hdim hL hδ f hf hdisj hs b q)
    have hK : tangentOrientationEquiv eK.toLinearEquiv OK = OCore.val (κ q) :=
      pullbackSmoothOrientation_pushforward IR IR κ
        (cuttingCollarMap_isLocalDiffeomorph I hdim hδ f hf hdisj hs b).contMDiff
        (cuttingCollarMap_mfderiv_bijective I hdim hδ f hf hdisj hs b) OCore q
    have hR : tangentOrientationEquiv eR.toLinearEquiv OR = oE b :=
      pullbackSmoothOrientation_pushforward IR (𝓡 3) ρ
        (radialCollarOrientationMap_isSmoothEmbedding hL (cuttingCollarWidth_pos (hδ b.1))).contMDiff
        (radialCollarOrientationMap_mfderiv_bijective hL (cuttingCollarWidth_pos (hδ b.1)))
        (euclideanSmoothOrientation E3 (oE b)) q
    have hQ : tangentOrientationEquiv eC.toLinearEquiv (oQ.val (j (κ q))) = oE b :=
      (congrArg (tangentOrientationEquiv eC.toLinearEquiv) (hCap b pN)).trans
        (finiteCapNeighborhoodSmoothOrientation_pushforward I hdim hL hδ f hf hdisj hs b (oE b) pN)
    have hT : tangentOrientationEquiv eR.toLinearEquiv OK =
        tangentOrientationEquiv eC.toLinearEquiv
          (tangentOrientationEquiv eJ.toLinearEquiv (tangentOrientationEquiv eK.toLinearEquiv OK)) := by
      rw [hD]
      exact (tangentOrientationEquiv_trans (eK.trans eJ).toLinearEquiv eC.toLinearEquiv OK).trans
        (congrArg (tangentOrientationEquiv eC.toLinearEquiv)
          (tangentOrientationEquiv_trans eK.toLinearEquiv eJ.toLinearEquiv OK))
    apply (tangentOrientationEquiv eC.toLinearEquiv).injective
    calc
      tangentOrientationEquiv eC.toLinearEquiv (tangentOrientationEquiv eJ.toLinearEquiv (OCore.val (κ q))) =
          tangentOrientationEquiv eC.toLinearEquiv
            (tangentOrientationEquiv eJ.toLinearEquiv (tangentOrientationEquiv eK.toLinearEquiv OK)) :=
        congrArg (fun z => tangentOrientationEquiv eC.toLinearEquiv (tangentOrientationEquiv eJ.toLinearEquiv z)) hK.symm
      _ = tangentOrientationEquiv eR.toLinearEquiv OK := hT.symm
      _ = tangentOrientationEquiv eR.toLinearEquiv OR :=
        congrArg (tangentOrientationEquiv eR.toLinearEquiv) (hcollar b q).symm
      _ = oE b := hR
      _ = tangentOrientationEquiv eC.toLinearEquiv (oQ.val (j (κ q))) := hQ.symm
  intro p
  rcases eq_univ_iff_forall.mp (finiteCapNeighborhood_cover hL hδ f hf hdisj) (j p) with hpOld | hpCap
  · have hpK : p.val ∈ interior (cutCore f) := by
      have hp' : p ∈ finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj ⁻¹'
          finiteCoreInterior hL hδ f (fun i => (hf i).injective) hdisj := hpOld
      rw [finiteCoreInterior_core_preimage] at hp'
      exact hp'
    let pK : finiteCoreOldDomainOpens f := ⟨p, hpK⟩
    let qO := finiteCoreOldLift hL hδ f hf hdisj pK
    let σ := finiteOldAmbientCoordinateMap I hdim hL hδ f hf hdisj hs
    let eJ : ER ≃L[ℝ] E3 := differentialEquivOfBijective IR (𝓡 3) j hbj p
    let eA : ER ≃L[ℝ] E := differentialEquivOfBijective IR I (Subtype.val : cutCore f → M)
      (cutCore_ambientInclusion_mfderiv_bijective I hdim hδ f hf hdisj hs) p
    let eO : E3 ≃L[ℝ] E := differentialEquivOfBijective (𝓡 3) I σ
      (finiteOldAmbientCoordinateMap_mfderiv_bijective I hdim hL hδ f hf hdisj hs) qO
    have hD : eA = eJ.trans eO := by
      apply ContinuousLinearEquiv.ext
      funext v
      exact congrArg (fun D : ER →L[ℝ] E => D v)
        (finiteCoreOldLift_ambient_mfderiv I hdim hL hδ f hf hdisj hs pK)
    have hPoint : σ qO = p.val :=
      congrFun (finiteCoreOldLift_ambient_coordinate I hdim hL hδ f hf hdisj hs) pK
    have hQ : tangentOrientationEquiv eO.toLinearEquiv (oQ.val (j p)) = o.val p.val :=
      (congrArg (tangentOrientationEquiv eO.toLinearEquiv) (hOld qO)).trans
        ((finiteOldSmoothOrientation_pushforward I hdim hL hδ f hf hdisj hs o qO).trans (congrArg o.val hPoint))
    apply (tangentOrientationEquiv eO.toLinearEquiv).injective
    calc
      tangentOrientationEquiv eO.toLinearEquiv (tangentOrientationEquiv eJ.toLinearEquiv (OCore.val p)) =
          tangentOrientationEquiv eA.toLinearEquiv (OCore.val p) := by
        rw [hD]
        exact (tangentOrientationEquiv_trans eJ.toLinearEquiv eO.toLinearEquiv (OCore.val p)).symm
      _ = o.val p.val := cutCoreSmoothOrientation_pushforward I hdim hδ f hf hdisj hs o p
      _ = tangentOrientationEquiv eO.toLinearEquiv (oQ.val (j p)) := hQ.symm
  · obtain ⟨b, hb⟩ := mem_iUnion.mp hpCap
    have hp : p ∈ range (cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b) := by
      rw [← finiteCapNeighborhood_core_preimage hL hδ f (fun i => (hf i).injective) hdisj b]
      exact hb
    obtain ⟨q, hq⟩ := hp
    exact hq ▸ hPresCollar b q

end DifferentialGeometry.Topology.ThreeManifold.Surgery
