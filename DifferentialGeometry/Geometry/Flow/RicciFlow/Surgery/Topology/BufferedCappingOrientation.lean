import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CappingReparametrization
import DifferentialGeometry.Topology.Manifold.ClosedBallLinearIsometry
import DifferentialGeometry.Tensor.LinearAlgebra.Orientation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SphericalTransitionBridge
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BufferedFiniteCappingSmooth
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.WorldBridges
import DifferentialGeometry.Topology.Manifold.OrientationTransport
import DifferentialGeometry.Topology.Manifold.ClosedBallOrientation
import DifferentialGeometry.Topology.Manifold.BallChartAffine
import DifferentialGeometry.Topology.Manifold.SmoothModelTransportSource
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.CutCoreOrientation

section

set_option autoImplicit false
noncomputable section

open Set Manifold
open DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

private local instance : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) := ⟨by simp⟩
attribute [local instance] threeBallChartedSpace threeBall_isManifold

theorem exists_cap_reparametrization_map_orientation
    (o : Orientation ℝ ThreeSpace (Fin 3)) (b : Bool) :
    ∃ (A : ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace)
      (B : ThreeBall ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ThreeBall)
      (a : Sphere 2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ Sphere 2),
      (A = LinearIsometryEquiv.refl ℝ ThreeSpace ∨ A = LinearIsometryEquiv.neg ℝ) ∧
      (∀ x : ThreeBall, (B x : ThreeSpace) = A x) ∧
      (∀ y : Sphere 2, (a y : ThreeSpace) = A y) ∧
      (∀ y : Sphere 2, B (sphereToThreeBall y) = sphereToThreeBall (a y)) ∧
      Orientation.map (Fin 3) A.toLinearEquiv
        ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation) =
          (if b then (1 : ℝˣ) else -1) • o := by
  classical
  let o₀ := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation
  let o₁ : Orientation ℝ ThreeSpace (Fin 3) := (if b then (1 : ℝˣ) else -1) • o
  rcases Orientation.eq_or_eq_neg o₀ o₁ (by simp) with heq | heq
  · refine ⟨LinearIsometryEquiv.refl ℝ ThreeSpace, Diffeomorph.refl (𝓡∂ 3) ThreeBall ∞,
      Diffeomorph.refl (𝓡 2) (Sphere 2) ∞, Or.inl rfl,
      (fun _ => rfl), (fun _ => rfl), (fun _ => rfl), ?_⟩
    exact heq
  · let B := closedBallLinearIsometryDiffeomorph (𝓡∂ 3) 1
      isSmoothEmbedding_threeBall_inclusion.isImmersion (LinearIsometryEquiv.neg ℝ : ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace)
    refine ⟨LinearIsometryEquiv.neg ℝ, B, sphereAntipodalDiffeomorph (n := 2),
      Or.inr rfl, (fun _ => rfl), (fun _ => rfl), ?_, ?_⟩
    · intro y
      exact closedBallLinearIsometryDiffeomorph_neg_sphere (𝓡∂ 3)
        isSmoothEmbedding_threeBall_inclusion.isImmersion y
    · change Orientation.map (Fin 3) (LinearEquiv.neg ℝ) o₀ = o₁
      rw [Orientation.map_negLinearEquiv_of_odd o₀ (by simp) (by norm_num), heq, neg_neg]

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end

end

section

set_option autoImplicit false
noncomputable section

open Set Function Manifold
open DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Topology.Handle
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

attribute [local instance] threeBallChartedSpace threeBall_isManifold

variable {N : Type*} [TopologicalSpace N] [ChartedSpace ThreeSpace N]
  [IsManifold ThreeModel ∞ N]

private theorem orientation_map_bool_smul
    (A : ThreeSpace ≃ₗ[ℝ] ThreeSpace) (b : Bool) (o : Orientation ℝ ThreeSpace (Fin 3)) :
    Orientation.map (Fin 3) A ((if b then (1 : ℝˣ) else -1) • o) =
      (if b then (1 : ℝˣ) else -1) • Orientation.map (Fin 3) A o := by
  cases b <;> simp [Module.Ray.neg_units_smul]

theorem cap_positive_of_preserving_orientation
    {L : ℝ} (hL : 0 < L) :
    letI := closedBallChartedSpace hL
    letI := closedBall_isManifold hL
    ∀ (j : {x : ThreeSpace // ‖x‖ ≤ L} → N)
      (hj : IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞ j)
      (oE : Orientation ℝ ThreeSpace (Fin (Module.finrank ℝ ThreeSpace)))
      (oN : SmoothOrientation ThreeModel N)
      (A : ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace)
      (B : ThreeBall ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ThreeBall) (b : Bool),
      (∀ x : ThreeBall, (B x : ThreeSpace) = A x) →
      Orientation.map (Fin 3) A.toLinearEquiv
        ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation) =
          (if b then (1 : ℝˣ) else -1) •
            Orientation.reindex ℝ ThreeSpace (finCongr finrank_threeSpace_eq_three) oE →
      (∀ y : {x : ThreeSpace // ‖x‖ ≤ L},
        tangentOrientationEquiv (differentialEquivOfBijective (𝓡∂ 3) ThreeModel j
          (fun p => bijective_mfderiv_of_isImmersionAt (𝓡∂ 3) ThreeModel j p
            (hj.isImmersion.isImmersionAt p) rfl) y).toLinearEquiv
          ((closedBallSmoothOrientation hL oE).val y) = oN.val (j y)) →
      ∀ x : ThreeBall,
        ∃ hi : Bijective (mfderiv (𝓡∂ 3) ThreeModel (Subtype.val : ThreeBall → ThreeSpace) x),
        ∃ hk : Bijective (mfderiv (𝓡∂ 3) ThreeModel (j ∘ threeBallScaleDiffeomorph hL ∘ B) x),
          Orientation.map (Fin 3)
            ((LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) ThreeModel
              (Subtype.val : ThreeBall → ThreeSpace) x).toLinearMap hi).symm.trans
              (LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) ThreeModel
                (j ∘ threeBallScaleDiffeomorph hL ∘ B) x).toLinearMap hk))
            ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation) =
              (if b then (1 : ℝˣ) else -1) •
                (TangentOrientationSection.ofSmoothOrientation oN).orientation
                  (j (threeBallScaleDiffeomorph hL (B x))) := by
  let := closedBallChartedSpace hL
  let := closedBall_isManifold hL
  intro j hj oE oN A B b hB hA hpres x
  let D := B.trans (threeBallScaleDiffeomorph hL)
  let hb := fun y => bijective_mfderiv_of_isImmersionAt (𝓡∂ 3) ThreeModel j y
    (hj.isImmersion.isImmersionAt y) rfl
  have hi := bijective_mfderiv_of_isImmersionAt (𝓡∂ 3) ThreeModel
    (Subtype.val : ThreeBall → ThreeSpace) x
    (isSmoothEmbedding_threeBall_inclusion.isImmersion.isImmersionAt x) rfl
  have hD := (D.mfderivToContinuousLinearEquiv (by simp) x).bijective
  have hk : Bijective (mfderiv (𝓡∂ 3) ThreeModel (j ∘ D) x) := by
    rw [mfderiv_comp x (hj.contMDiff.mdifferentiableAt (by simp))
      (D.contMDiff.mdifferentiableAt (by simp))]
    exact (hb (D x)).comp hD
  refine ⟨hi, hk, ?_⟩
  let I₀ : ThreeSpace ≃ₗ[ℝ] ThreeSpace :=
    LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) ThreeModel (Subtype.val : ThreeBall → ThreeSpace) x).toLinearMap hi
  let I₁ : ThreeSpace ≃ₗ[ℝ] ThreeSpace := (differentialEquivOfBijective (𝓡∂ 3) ThreeModel
    (Subtype.val : {x : ThreeSpace // ‖x‖ ≤ L} → ThreeSpace)
    (closedBall_inclusion_mfderiv_bijective hL) (D x)).toLinearEquiv
  let J : ThreeSpace ≃ₗ[ℝ] ThreeSpace := (differentialEquivOfBijective (𝓡∂ 3) ThreeModel j hb (D x)).toLinearEquiv
  let D' : ThreeSpace ≃ₗ[ℝ] ThreeSpace := (D.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv
  let K : ThreeSpace ≃ₗ[ℝ] ThreeSpace := LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) ThreeModel (j ∘ D) x).toLinearMap hk
  let C := LinearEquiv.smulOfNeZero ℝ ThreeSpace L hL.ne'
  have hK : K = D'.trans J := by
    apply LinearEquiv.ext
    intro v
    exact congrArg (fun T => T v)
      (mfderiv_comp x (hj.contMDiff.mdifferentiableAt (by simp))
        (D.contMDiff.mdifferentiableAt (by simp)))
  have hcoord (v : ThreeSpace) : I₁ (D' v) = C (A (I₀ v)) := by
    have hchain := mfderiv_comp x
      ((isSmoothEmbedding_closedBall_inclusion hL).contMDiff.mdifferentiableAt (by simp))
      (D.contMDiff.mdifferentiableAt (by simp))
    let F : ThreeSpace →L[ℝ] ThreeSpace := L • A.toContinuousLinearEquiv.toContinuousLinearMap
    have heq : (Subtype.val : {x : ThreeSpace // ‖x‖ ≤ L} → ThreeSpace) ∘ D =
        F ∘ (Subtype.val : ThreeBall → ThreeSpace) := by
      funext y
      change L • (B y : ThreeSpace) = L • A y
      rw [hB]
    rw [heq, mfderiv_comp x F.mdifferentiableAt
      (isSmoothEmbedding_threeBall_inclusion.contMDiff.mdifferentiableAt (by simp)),
      ContinuousLinearMap.mfderiv_eq] at hchain
    exact (congrArg (fun T => T v) hchain).symm
  have hlinear : I₀.symm.trans K = (A.toLinearEquiv.trans C).trans (I₁.symm.trans J) := by
    rw [hK]
    apply LinearEquiv.ext
    intro v
    apply congrArg J
    apply I₁.injective
    change I₁ (D' (I₀.symm v)) = I₁ (I₁.symm (C (A v)))
    rw [hcoord, I₀.apply_symm_apply, I₁.apply_symm_apply]
  have hraw := DifferentialGeometry.orientation_map_inverse_trans_of_tangentOrientationEquiv
    finrank_threeSpace_eq_three I₁ J ((closedBallSmoothOrientation hL oE).val (D x))
    (closedBallSmoothOrientation_pushforward hL oE (D x)) (hpres (D x))
  have hfinal : Orientation.map (Fin 3) (I₀.symm.trans K)
        ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation) =
      (if b then (1 : ℝˣ) else -1) •
        Orientation.reindex ℝ ThreeSpace (finCongr finrank_threeSpace_eq_three) (oN.val (j (D x))) := by
    rw [hlinear]
    erw [DifferentialGeometry.orientation_map_trans (A.toLinearEquiv.trans C) (I₁.symm.trans J),
      DifferentialGeometry.orientation_map_trans A.toLinearEquiv C]
    erw [DifferentialGeometry.Topology.OrientationAssembly.orientation_map_smulOfNeZero_tangent
      (M := ThreeSpace) (0 : ThreeSpace) L hL, hA, orientation_map_bool_smul, hraw]
  rw [TangentOrientationSection.ofSmoothOrientation_apply]
  exact hfinal

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end

end

section

noncomputable section

open Set Function Manifold
open DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.Topology.ThreeManifold.Surgery
open DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] {ι : Type} [Fintype ι] {δ : ι → ℝ} {L : ℝ}
  (hL : 0 < L) (hδ : ∀ i, 0 < δ i) (hδ1 : ∀ i, δ i < 1)
  (f : ∀ i : ι, bufferedCylinder (δ i) → M)
  (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
  (hdisj : Pairwise fun i j => Disjoint (range (f i)) (range (f j)))
  (hs : ∀ i, IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ)) ThreeModel ∞ (f i))

local notation "T" => TubeSystem.ofBufferedCharts hδ hδ1 f hf hdisj
local notation "Q" => FiniteCapQuotient hL hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj
local notation "ER" => EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 1)

theorem Capping.ofBufferedFiniteCaps_core_positive_of_preserving_orientation
    (o : SmoothOrientation ThreeModel M) :
    letI : ChartedSpace EuclideanHalfSpaceProdModel (cutCore f) :=
      cutCoreBoundaryChartedSpace ThreeModel finrank_threeSpace_eq_three hδ f hf hdisj
    letI : IsManifold ((𝓡 2).prod (𝓡∂ 1)) ∞ (cutCore f) :=
      cutCore_isManifold ThreeModel finrank_threeSpace_eq_three hδ f hf hdisj hs
    letI : ChartedSpace ThreeSpace Q :=
      finiteCapChartedSpace ThreeModel finrank_threeSpace_eq_three hL hδ f hf hdisj
    letI : IsManifold ThreeModel ∞ Q :=
      finiteCapQuotient_isManifold finrank_threeSpace_eq_three hL hδ f hf hdisj hs
    ∀ (oQ : SmoothOrientation ThreeModel Q),
      (∀ p : cutCore f,
        tangentOrientationEquiv (differentialEquivOfBijective ((𝓡 2).prod (𝓡∂ 1)) ThreeModel
          (finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj)
          (finiteCoreInclusion_mfderiv_bijective ThreeModel finrank_threeSpace_eq_three
            hL hδ f hf hdisj hs) p).toLinearEquiv
          ((cutCoreSmoothOrientation ThreeModel finrank_threeSpace_eq_three hδ f hf hdisj hs o).val p) =
            oQ.val (finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj p)) →
      letI := bufferedCutCoreChartedSpace hδ hδ1 f hf hdisj
      ∀ x : (T).core,
        ∃ hi : Bijective (mfderiv (𝓡∂ 3) ThreeModel (Subtype.val : (T).core → M) x),
        ∃ hj : Bijective (mfderiv (𝓡∂ 3) ThreeModel
            (Capping.ofBufferedFiniteCaps hL hδ hδ1 f hf hdisj).coreInclusion x),
          Orientation.map (Fin 3)
            ((LinearEquiv.ofBijective
              (mfderiv (𝓡∂ 3) ThreeModel (Subtype.val : (T).core → M) x).toLinearMap hi).symm.trans
              (LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) ThreeModel
                (Capping.ofBufferedFiniteCaps hL hδ hδ1 f hf hdisj).coreInclusion x).toLinearMap hj))
            ((TangentOrientationSection.ofSmoothOrientation o).orientation x.val) =
              (TangentOrientationSection.ofSmoothOrientation oQ).orientation
                ((Capping.ofBufferedFiniteCaps hL hδ hδ1 f hf hdisj).coreInclusion x) := by
  let : ChartedSpace EuclideanHalfSpaceProdModel (cutCore f) :=
    cutCoreBoundaryChartedSpace ThreeModel finrank_threeSpace_eq_three hδ f hf hdisj
  let : IsManifold ((𝓡 2).prod (𝓡∂ 1)) ∞ (cutCore f) :=
    cutCore_isManifold ThreeModel finrank_threeSpace_eq_three hδ f hf hdisj hs
  let : ChartedSpace ThreeSpace Q :=
    finiteCapChartedSpace ThreeModel finrank_threeSpace_eq_three hL hδ f hf hdisj
  let : IsManifold ThreeModel ∞ Q :=
    finiteCapQuotient_isManifold finrank_threeSpace_eq_three hL hδ f hf hdisj hs
  intro oQ hpres
  let := bufferedCutCoreChartedSpace hδ hδ1 f hf hdisj
  let : IsManifold (𝓡∂ 3) ∞ (T).core := bufferedCutCore_isManifold hδ hδ1 f hf hdisj hs
  let D : (T).core ≃ₘ⟮𝓡∂ 3, ((𝓡 2).prod (𝓡∂ 1))⟯ cutCore f := by
    let := euclideanHalfSpaceProdChartedSpace (cutCore f)
    let : IsManifold (𝓡∂ 3) ∞ (cutCore f) := euclideanHalfSpaceProd_isManifold (cutCore f)
    exact (bufferedCutCoreDiffeomorph hδ hδ1 f hf hdisj hs).trans
      (euclideanHalfSpaceProdDiffeomorph (cutCore f))
  let i : cutCore f → M := Subtype.val
  let j := finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj
  let a : (T).core → M := Subtype.val
  let b := (Capping.ofBufferedFiniteCaps hL hδ hδ1 f hf hdisj).coreInclusion
  have ha : i ∘ D = a := rfl
  have hb : j ∘ D = b := rfl
  have his : ContMDiff ((𝓡 2).prod (𝓡∂ 1)) ThreeModel ∞ i :=
    (cutCore_ambientInclusion_isSmoothEmbedding ThreeModel finrank_threeSpace_eq_three
      hδ f hf hdisj hs).contMDiff
  have hjs : ContMDiff ((𝓡 2).prod (𝓡∂ 1)) ThreeModel ∞ j :=
    (finiteCoreInclusion_isSmoothEmbedding ThreeModel finrank_threeSpace_eq_three
      hL hδ f hf hdisj hs).contMDiff
  let hbi := cutCore_ambientInclusion_mfderiv_bijective ThreeModel finrank_threeSpace_eq_three
    hδ f hf hdisj hs
  let hbj := finiteCoreInclusion_mfderiv_bijective ThreeModel finrank_threeSpace_eq_three
    hL hδ f hf hdisj hs
  intro x
  let d : ThreeSpace ≃L[ℝ] ER := D.mfderivToContinuousLinearEquiv (by simp) x
  let ai := differentialEquivOfBijective ((𝓡 2).prod (𝓡∂ 1)) ThreeModel i hbi (D x)
  let bj := differentialEquivOfBijective ((𝓡 2).prod (𝓡∂ 1)) ThreeModel j hbj (D x)
  let A := d.trans ai
  let B := d.trans bj
  have hda : (A : ThreeSpace →L[ℝ] ThreeSpace) = mfderiv (𝓡∂ 3) ThreeModel a x := by
    have hchain := mfderiv_comp x (his.mdifferentiableAt (by simp))
      (D.contMDiff.mdifferentiableAt (by simp))
    rw [ha] at hchain
    exact hchain.symm
  have hdb : (B : ThreeSpace →L[ℝ] ThreeSpace) = mfderiv (𝓡∂ 3) ThreeModel b x := by
    have hchain := mfderiv_comp x (hjs.mdifferentiableAt (by simp))
      (D.contMDiff.mdifferentiableAt (by simp))
    rw [hb] at hchain
    exact hchain.symm
  have hba : Bijective (mfderiv (𝓡∂ 3) ThreeModel a x) := by
    rw [← hda]
    exact A.bijective
  have hbb : Bijective (mfderiv (𝓡∂ 3) ThreeModel b x) := by
    rw [← hdb]
    exact B.bijective
  refine ⟨hba, hbb, ?_⟩
  have hea : LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) ThreeModel a x).toLinearMap hba =
      A.toLinearEquiv := by
    apply LinearEquiv.ext
    intro v
    exact (congrArg (fun L : ThreeSpace →L[ℝ] ThreeSpace => L v) hda).symm
  have heb : LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) ThreeModel b x).toLinearMap hbb =
      B.toLinearEquiv := by
    apply LinearEquiv.ext
    intro v
    exact (congrArg (fun L : ThreeSpace →L[ℝ] ThreeSpace => L v) hdb).symm
  let oc := (cutCoreSmoothOrientation ThreeModel finrank_threeSpace_eq_three hδ f hf hdisj hs o).val (D x)
  let ocNew := tangentOrientationEquiv d.symm.toLinearEquiv oc
  have hoi : tangentOrientationEquiv ai.toLinearEquiv oc = o.val x.val :=
    cutCoreSmoothOrientation_pushforward ThreeModel finrank_threeSpace_eq_three hδ f hf hdisj hs o (D x)
  have hoj : tangentOrientationEquiv bj.toLinearEquiv oc = oQ.val (b x) := hpres (D x)
  have hcancel : tangentOrientationEquiv d.toLinearEquiv
      (tangentOrientationEquiv d.symm.toLinearEquiv oc) = oc :=
    tangentOrientationEquiv_symm d.symm.toLinearEquiv oc
  have hA : tangentOrientationEquiv A.toLinearEquiv ocNew = o.val x.val := by
    change tangentOrientationEquiv (d.toLinearEquiv.trans ai.toLinearEquiv)
      (tangentOrientationEquiv d.symm.toLinearEquiv oc) = _
    rw [tangentOrientationEquiv_trans, hcancel]
    exact hoi
  have hB : tangentOrientationEquiv B.toLinearEquiv ocNew = oQ.val (b x) := by
    change tangentOrientationEquiv (d.toLinearEquiv.trans bj.toLinearEquiv)
      (tangentOrientationEquiv d.symm.toLinearEquiv oc) = _
    rw [tangentOrientationEquiv_trans, hcancel]
    exact hoj
  change Orientation.map (Fin 3)
    ((LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) ThreeModel a x).toLinearMap hba).symm.trans
      (LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) ThreeModel b x).toLinearMap hbb))
    ((TangentOrientationSection.ofSmoothOrientation o).orientation x.val) =
      (TangentOrientationSection.ofSmoothOrientation oQ).orientation (b x)
  rw [hea, heb, TangentOrientationSection.ofSmoothOrientation_apply,
    TangentOrientationSection.ofSmoothOrientation_apply]
  exact DifferentialGeometry.orientation_map_inverse_trans_of_tangentOrientationEquiv
    finrank_threeSpace_eq_three A.toLinearEquiv B.toLinearEquiv ocNew hA hB

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end

end
