/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Dynamics.FrameRotations
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Dynamics.MovingFrameTensor

noncomputable section

open Set Filter MeasureTheory
open DifferentialGeometry.ProjectiveOrthogonalGroup
open scoped Topology

namespace DifferentialGeometry.FrameTensorIsotropy

open HyperbolicBoundary Horospherical EuclideanBoundary GeodesicFlow
open BoundaryChartAction BoundaryChartConformal NormalizedDerivative
open MovingFrameTensor FrameRotations LorentzGenerators

variable {m : ℕ} [Nonempty (Fin m)]

local instance : MulAction (IsometryGroup m) (BoundaryH (m + 1)) :=
  poBoundaryMulAction (by omega)

theorem eq_id_of_quarterTurns (T : Horizontal m →L[ℝ] Horizontal m)
    (hsym : ∀ u v, inner ℝ (T u) v = inner ℝ (T v) u)
    (hpos : ∀ u, 0 ≤ inner ℝ (T u) u) (hnorm : ‖T‖ = 1)
    (hQ : ∀ (i j : Fin m), i ≠ j → ∀ u v,
      inner ℝ (T (quarterTurn i j u)) (quarterTurn i j v) = inner ℝ (T u) v) :
    T = ContinuousLinearMap.id ℝ (Horizontal m) := by
  classical
  let k : Fin m := Classical.choice inferInstance
  let c : ℝ := inner ℝ (T (basisVector k)) (basisVector k)
  have hd (i j : Fin m) :
      inner ℝ (T (basisVector i)) (basisVector i) =
        inner ℝ (T (basisVector j)) (basisVector j) := by
    by_cases hij : i = j
    · rw [hij]
    · have h := hQ i j hij (basisVector i) (basisVector i)
      rw [quarterTurn_first, map_neg, inner_neg_left, inner_neg_right, neg_neg] at h
      exact h.symm
  have ho (i j : Fin m) (hij : i ≠ j) :
      inner ℝ (T (basisVector i)) (basisVector j) = 0 := by
    have h := hQ i j hij (basisVector i) (basisVector j)
    rw [quarterTurn_first, quarterTurn_second hij, map_neg, inner_neg_left,
      hsym (basisVector j) (basisVector i)] at h
    linarith
  have hb (i : Fin m) : T (basisVector i) = c • basisVector i := by
    ext j
    have he : inner ℝ (T (basisVector i)) (basisVector j) = (T (basisVector i)) j := by
      simp only [basisVector, EuclideanSpace.inner_basisFun_real]
    rw [← he]
    by_cases hij : i = j
    · subst j
      have hc : (c • basisVector i) i = c := by
        simp [basisVector, EuclideanSpace.basisFun_apply]
      rw [hc]
      exact hd i k
    · rw [ho i j hij]
      simp [basisVector, EuclideanSpace.basisFun_apply, Ne.symm hij]
  have hT : T = c • ContinuousLinearMap.id ℝ (Horizontal m) := by
    rw [← sum_basis_differential T,
      ← sum_basis_differential (c • ContinuousLinearMap.id ℝ (Horizontal m))]
    apply Finset.sum_congr rfl
    intro i _
    change (EuclideanSpace.proj i).smulRight (T (basisVector i)) =
      (EuclideanSpace.proj i).smulRight (c • basisVector i)
    rw [hb]
  have hc : 0 ≤ c := hpos (basisVector k)
  rw [hT, norm_smul, ContinuousLinearMap.norm_id, mul_one, Real.norm_of_nonneg hc] at hnorm
  rw [hT, hnorm, one_smul]

theorem ae_frameTensor_eq_id_of_horospherical
    (F : Horizontal m → Horizontal m)
    (hF : ∀ᵐ x ∂(volume : Measure (Horizontal m)), fderiv ℝ F x ≠ 0)
    (H : Subgroup (IsometryGroup m))
    (hT : ∀ b : Fin m → ℝ, translation b ∈ H)
    (hO : ∀ b : Fin m → ℝ, oppositeTranslation b ∈ H)
    (hInv : ∀ h ∈ H, (fun g : IsometryGroup m => frameTensor F (g * h))
      =ᵐ[volume] frameTensor F) :
    ∀ᵐ g ∂(volume : Measure (IsometryGroup m)),
      frameTensor F g = ContinuousLinearMap.id ℝ (Horizontal m) := by
  have hQ (i j : Fin m) : ∀ᵐ g ∂(volume : Measure (IsometryGroup m)), i ≠ j →
      ∀ u v, inner ℝ (frameTensor F g (quarterTurn i j u)) (quarterTurn i j v) =
        inner ℝ (frameTensor F g u) v := by
    by_cases hij : i = j
    · exact Eventually.of_forall fun _ hne => (hne hij).elim
    · filter_upwards [hInv _ (quarterTurn_mem H hT hO hij)] with g hg
      intro _ u v
      rw [frameTensor_right_isometry F _ _ (rotation_embed (quarterTurn i j)) g] at hg
      have he := congrArg (fun A : Horizontal m →L[ℝ] Horizontal m => inner ℝ (A u) v) hg
      simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left,
        ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv] using he
  filter_upwards [ae_norm_frameTensor F hF, ae_all_iff.mpr (fun i => ae_all_iff.mpr (hQ i))]
    with g hg hQ
  apply eq_id_of_quarterTurns (frameTensor F g) _ _ hg hQ
  · intro u v
    simp only [frameTensor]
    rw [inner_normalizedTensor, inner_normalizedTensor, real_inner_comm]
  · exact normalizedTensor_nonneg _

theorem conformal_of_frameTensor_eq_id (F : Horizontal m → Horizontal m)
    {g : IsometryGroup m} (hg : g ∈ finiteFrames)
    (hF : fderiv ℝ F (chartAction g 0) ≠ 0)
    (hT : frameTensor F g = ContinuousLinearMap.id ℝ (Horizontal m)) :
    IsConformalMap (fderiv ℝ F (chartAction g 0)) := by
  have hC := isConformalMap_fderiv_chartAction g hg
  have hnonzero : (fderiv ℝ F (chartAction g 0)).comp (fderiv ℝ (chartAction g) 0) ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [DerivativeEccentricity.norm_comp_conformal_right _ _ hC]
    exact mul_ne_zero (norm_ne_zero_iff.mpr hF) (norm_ne_zero_iff.mpr hC.ne_zero)
  rw [frameTensor_eq F hg] at hT
  have hconf := (normalizedTensor_eq_id_iff _ hnonzero).mp hT
  have hinv := isConformalMap_fderiv_chartAction g⁻¹ (chartAction_mem_inverseDomain g hg)
  have h := hconf.comp hinv
  rwa [ContinuousLinearMap.comp_assoc, fderiv_inverse_chartAction g hg,
    ContinuousLinearMap.comp_id] at h

theorem ae_chartTensor_eq_id_of_frameTensor (F : Horizontal m → Horizontal m)
    (hF : ∀ᵐ x ∂(volume : Measure (Horizontal m)), fderiv ℝ F x ≠ 0)
    (hT : ∀ᵐ g ∂(volume : Measure (IsometryGroup m)),
      frameTensor F g = ContinuousLinearMap.id ℝ (Horizontal m)) :
    ∀ᵐ x ∂(volume : Measure (Horizontal m)),
      chartTensor F x = ContinuousLinearMap.id ℝ (Horizontal m) := by
  have hg : ∀ᵐ g ∂(volume : Measure (IsometryGroup m)),
      chartTensor F (coords (g • embed (0 : Horizontal m))) =
        ContinuousLinearMap.id ℝ (Horizontal m) := by
    filter_upwards [hT, ae_finiteFrames, quasiMeasurePreserving_framePoint.ae hF]
      with g hg hfinite hnonzero
    exact (normalizedTensor_eq_id_iff _ hnonzero).mpr
      (conformal_of_frameTensor_eq_id F hfinite hnonzero hg)
  have hm : MeasurableSet {v : BoundaryH (m + 1) |
      chartTensor F (coords v) = ContinuousLinearMap.id ℝ (Horizontal m)} :=
    ((measurable_chartTensor F).comp measurable_coords) isClosed_singleton.measurableSet
  have hb := (BoundaryMeasure.haar_orbit_ae_iff (embed (0 : Horizontal m)) hm).mp hg
  have hx := measurePreserving_embed.quasiMeasurePreserving.ae hb
  simpa only [coords_embed] using hx

end DifferentialGeometry.FrameTensorIsotropy
