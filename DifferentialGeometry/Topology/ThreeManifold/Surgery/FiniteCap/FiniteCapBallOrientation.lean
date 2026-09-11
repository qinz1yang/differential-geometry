import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCoreOrientation
import DifferentialGeometry.Topology.Manifold.ClosedBallOrientation

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Topology.Manifold DifferentialGeometry.Topology.Manifold.Attachment
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev Ball (L : ℝ) := {x : E3 // ‖x‖ ≤ L}
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

private theorem cap_radial_mfderiv (b : ι × Bool) (x : Ball L) :
    letI := closedBallChartedSpace hL
    let : ChartedSpace E3 OrientedQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    mfderiv (𝓡∂ 3) (𝓡 3) (Subtype.val : Ball L → E3) x =
      (mfderiv (𝓡 3) (𝓡 3) (finiteCapRadialCoordinateMap I hdim hL hδ f hf hdisj hs b)
        (⟨finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj ⟨b, x⟩, Or.inl ⟨x, rfl⟩⟩ :
          finiteCapNeighborhoodOpens hL hδ f hf hdisj b)).comp
      (mfderiv (𝓡∂ 3) (𝓡 3)
        (fun y : Ball L => finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj ⟨b, y⟩) x) := by
  let := closedBallChartedSpace hL
  let : ChartedSpace E3 OrientedQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  let N := finiteCapNeighborhoodOpens hL hδ f hf hdisj b
  let j : Ball L → OrientedQ := fun y => finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj ⟨b, y⟩
  let r : Ball L → N := fun y => ⟨j y, Or.inl ⟨y, rfl⟩⟩
  let C := finiteCapRadialCoordinateMap I hdim hL hδ f hf hdisj hs b
  have hr : ContMDiff (𝓡∂ 3) (𝓡 3) ∞ r :=
    (ContMDiff.subtypeVal_comp_iff N r).mp
      (finiteCapInclusion_ball_isSmoothEmbedding I hdim hL hδ f hf hdisj hs b).contMDiff
  have hC := finiteCapRadialCoordinateMap_contMDiff I hdim hL hδ f hf hdisj hs b
  have hmap : C ∘ r = (Subtype.val : Ball L → E3) := by
    funext y
    exact finiteCapNeighborhoodHomeomorph_cap hL hδ f hf hdisj b y
  let D : (Ball L → E3) → (E3 →L[ℝ] E3) := fun g => mfderiv (𝓡∂ 3) (𝓡 3) g x
  have hd : (mfderiv (𝓡∂ 3) (𝓡 3) (C ∘ r) x : E3 →L[ℝ] E3) =
      mfderiv (𝓡∂ 3) (𝓡 3) (Subtype.val : Ball L → E3) x := congrArg D hmap
  have hc : (mfderiv (𝓡∂ 3) (𝓡 3) (C ∘ r) x : E3 →L[ℝ] E3) =
      (mfderiv (𝓡 3) (𝓡 3) C (r x)).comp (mfderiv (𝓡∂ 3) (𝓡 3) r x) :=
    mfderiv_comp (f := r) (g := C) x (hC.mdifferentiableAt (by simp)) (hr.mdifferentiableAt (by simp))
  have hj : (mfderiv (𝓡∂ 3) (𝓡 3) r x : E3 →L[ℝ] E3) = mfderiv (𝓡∂ 3) (𝓡 3) j x :=
    (mfderiv_comp_open_val (𝓡∂ 3) (𝓡 3) N r hr x).symm
  exact hd.symm.trans (hc.trans
    (congrArg (fun A : E3 →L[ℝ] E3 => (mfderiv (𝓡 3) (𝓡 3) C (r x)).comp A) hj))

theorem exists_finiteCapSmoothOrientation_preserving_core_and_caps (o : SmoothOrientation I M) :
    letI := closedBallChartedSpace hL
    letI := closedBall_isManifold hL
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
        (∀ p : cutCore f,
          tangentOrientationEquiv (differentialEquivOfBijective IR (𝓡 3)
            (finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj)
            (finiteCoreInclusion_mfderiv_bijective I hdim hL hδ f hf hdisj hs) p).toLinearEquiv
              ((cutCoreSmoothOrientation I hdim hδ f hf hdisj hs o).val p) =
                oQ.val (finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj p) ) ∧
        ∀ (b : ι × Bool) (x : Ball L),
          tangentOrientationEquiv (differentialEquivOfBijective (𝓡∂ 3) (𝓡 3)
            (fun y : Ball L => finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj ⟨b, y⟩)
            (finiteCapInclusion_ball_mfderiv_bijective I hdim hL hδ f hf hdisj hs b) x).toLinearEquiv
              ((closedBallSmoothOrientation hL (oE b)).val x) =
                oQ.val (finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj ⟨b, x⟩) := by
  let := closedBallChartedSpace hL
  let := closedBall_isManifold hL
  let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  let : ChartedSpace E3 OrientedQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ OrientedQ := finiteCapQuotient_isManifold hdim hL hδ f hf hdisj hs
  obtain ⟨oE, oQ, hsign, hcollar, hOld, hCap, hCore⟩ :=
    exists_finiteCapSmoothOrientation_preserving_core I hdim hL hδ f hf hdisj hs o
  refine ⟨oE, oQ, hsign, hcollar, hOld, hCap, hCore, ?_⟩
  intro b x
  let j : Ball L → OrientedQ := fun y => finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj ⟨b, y⟩
  let pN : finiteCapNeighborhoodOpens hL hδ f hf hdisj b := ⟨j x, Or.inl ⟨x, rfl⟩⟩
  let C := finiteCapRadialCoordinateMap I hdim hL hδ f hf hdisj hs b
  let eJ : E3 ≃L[ℝ] E3 := differentialEquivOfBijective (𝓡∂ 3) (𝓡 3) j
    (finiteCapInclusion_ball_mfderiv_bijective I hdim hL hδ f hf hdisj hs b) x
  let eC : E3 ≃L[ℝ] E3 := differentialEquivOfBijective (𝓡 3) (𝓡 3) C
    (finiteCapRadialCoordinateMap_mfderiv_bijective I hdim hL hδ f hf hdisj hs b) pN
  let eA : E3 ≃L[ℝ] E3 := differentialEquivOfBijective (𝓡∂ 3) (𝓡 3) (Subtype.val : Ball L → E3)
    (closedBall_inclusion_mfderiv_bijective hL) x
  let OB := (closedBallSmoothOrientation hL (oE b)).val x
  have hD : eA = eJ.trans eC := by
    apply ContinuousLinearEquiv.ext
    funext v
    exact congrArg (fun D : E3 →L[ℝ] E3 => D v) (cap_radial_mfderiv I hdim hL hδ f hf hdisj hs b x)
  have hA : tangentOrientationEquiv eA.toLinearEquiv OB = oE b :=
    closedBallSmoothOrientation_pushforward hL (oE b) x
  have hQ : tangentOrientationEquiv eC.toLinearEquiv (oQ.val (j x)) = oE b :=
    (congrArg (tangentOrientationEquiv eC.toLinearEquiv) (hCap b pN)).trans
      (finiteCapNeighborhoodSmoothOrientation_pushforward I hdim hL hδ f hf hdisj hs b (oE b) pN)
  apply (tangentOrientationEquiv eC.toLinearEquiv).injective
  calc
    tangentOrientationEquiv eC.toLinearEquiv (tangentOrientationEquiv eJ.toLinearEquiv OB) =
        tangentOrientationEquiv eA.toLinearEquiv OB := by
      rw [hD]
      exact (tangentOrientationEquiv_trans eJ.toLinearEquiv eC.toLinearEquiv OB).symm
    _ = oE b := hA
    _ = tangentOrientationEquiv eC.toLinearEquiv (oQ.val (j x)) := hQ.symm

end DifferentialGeometry.Topology.ThreeManifold.Surgery
