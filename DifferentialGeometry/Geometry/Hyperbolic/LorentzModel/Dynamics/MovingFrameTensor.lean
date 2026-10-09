/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Analysis.Integration.Measure.GroupQuotient.MeasurableDescent
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Boundary.NormalizedDerivative

noncomputable section

open Set Filter MeasureTheory
open DifferentialGeometry.ProjectiveOrthogonalGroup
open scoped Topology

namespace DifferentialGeometry.MovingFrameTensor

open HyperbolicBoundary Horospherical EuclideanBoundary GeodesicFlow
open BoundaryChartAction BoundaryChartConformal NormalizedDerivative

variable {m : ℕ}

local instance : MulAction (IsometryGroup m) (BoundaryH (m + 1)) :=
  poBoundaryMulAction (by omega)
local instance : ContinuousSMul (IsometryGroup m) (BoundaryH (m + 1)) :=
  ⟨continuous_po_boundary (by omega)⟩

def finiteFrames : Set (IsometryGroup m) :=
  {g | (0 : Horizontal m) ∈ chartDomain g}

theorem isOpen_finiteFrames : IsOpen (finiteFrames (m := m)) :=
  isClosed_singleton.isOpen_compl.preimage (continuous_id.smul continuous_const)

theorem measurable_chartAction_at (x : Horizontal m) :
    Measurable (fun g : IsometryGroup m => chartAction g x) :=
  measurable_coords.comp (continuous_id.smul continuous_const).measurable

open Classical in
def frameDifferential (g : IsometryGroup m) : Horizontal m →L[ℝ] Horizontal m :=
  if g ∈ finiteFrames then fderiv ℝ (chartAction g) 0 else 0

theorem frameDifferential_eq {g : IsometryGroup m} (hg : g ∈ finiteFrames) :
    frameDifferential g = fderiv ℝ (chartAction g) 0 := ite_eq_left hg

private def differenceMatrix (t : ℝ) (g : IsometryGroup m) :
    Horizontal m →L[ℝ] Horizontal m :=
  ∑ i : Fin m, (EuclideanSpace.proj i).smulRight
    (t⁻¹ • (chartAction g (t • EuclideanSpace.basisFun (Fin m) ℝ i) - chartAction g 0))

private theorem smulRightL_eq (l : Horizontal m →L[ℝ] ℝ) (v : Horizontal m) :
    ContinuousLinearMap.smulRightL ℝ (Horizontal m) (Horizontal m) l v = l.smulRight v := by
  ext x
  rfl

private theorem measurable_differenceMatrix (t : ℝ) :
    Measurable (differenceMatrix (m := m) t) := by
  apply Finset.measurable_sum
  intro i _
  simpa only [Function.comp_def, smulRightL_eq, Pi.smul_apply, Pi.sub_apply] using
    ((ContinuousLinearMap.smulRightL ℝ (Horizontal m) (Horizontal m)
    (EuclideanSpace.proj i)).continuous.measurable.comp
      (((measurable_chartAction_at (t • EuclideanSpace.basisFun (Fin m) ℝ i)).sub
          (measurable_chartAction_at 0)).const_smul t⁻¹))

theorem sum_basis_differential (A : Horizontal m →L[ℝ] Horizontal m) :
    (∑ i : Fin m, (EuclideanSpace.proj i).smulRight
      (A (EuclideanSpace.basisFun (Fin m) ℝ i))) = A := by
  ext1 x
  simp only [sum_apply, ContinuousLinearMap.smulRight_apply]
  change (∑ i : Fin m, x i • A (EuclideanSpace.basisFun (Fin m) ℝ i)) = A x
  simpa only [map_sum, map_smul, EuclideanSpace.basisFun_repr] using
    congrArg A (EuclideanSpace.basisFun (Fin m) ℝ |>.sum_repr x)

private theorem differenceMatrix_tendsto {g : IsometryGroup m}
    (hg : g ∈ finiteFrames) :
    Tendsto (fun k : ℕ => differenceMatrix (1 / ((k : ℝ) + 1)) g) atTop
      (𝓝 (fderiv ℝ (chartAction g) 0)) := by
  rw [← sum_basis_differential (fderiv ℝ (chartAction g) 0)]
  apply tendsto_finsetSum
  intro i _
  have ht : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall (fun k => show 0 < 1 / ((k : ℝ) + 1) by positivity)⟩
  have hd := ((differentiableAt_chartAction g hg).hasFDerivAt.hasLineDerivAt
    (EuclideanSpace.basisFun (Fin m) ℝ i)).tendsto_slope_zero_right.comp ht
  have he := (ContinuousLinearMap.smulRightL ℝ (Horizontal m) (Horizontal m)
    (EuclideanSpace.proj i)).continuous.tendsto
      (fderiv ℝ (chartAction g) 0 (EuclideanSpace.basisFun (Fin m) ℝ i))
  simpa only [Function.comp_def, zero_add, smulRightL_eq] using he.comp hd

theorem measurable_frameDifferential : Measurable (frameDifferential (m := m)) := by
  classical
  let J : ℕ → IsometryGroup m → (Horizontal m →L[ℝ] Horizontal m) :=
    fun k => finiteFrames.piecewise (differenceMatrix (1 / ((k : ℝ) + 1))) (fun _ => 0)
  apply measurable_of_tendsto_metrizable (f := J)
  · intro k
    exact (measurable_differenceMatrix _).piecewise isOpen_finiteFrames.measurableSet measurable_const
  · apply tendsto_pi_nhds.mpr
    intro g
    by_cases hg : g ∈ finiteFrames
    · simpa only [J, piecewise_eq_of_mem _ _ _ hg, frameDifferential, ite_eq_left hg] using
        differenceMatrix_tendsto hg
    · simpa only [J, piecewise_eq_of_notMem _ _ _ hg, frameDifferential, ite_eq_right hg] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : Horizontal m →L[ℝ] Horizontal m))
          atTop (𝓝 0))

def frameTensor (F : Horizontal m → Horizontal m) (g : IsometryGroup m) :
    Horizontal m →L[ℝ] Horizontal m :=
  normalizedTensor ((fderiv ℝ F (chartAction g 0)).comp (frameDifferential g))

theorem frameTensor_eq (F : Horizontal m → Horizontal m)
    {g : IsometryGroup m} (hg : g ∈ finiteFrames) :
    frameTensor F g =
      normalizedTensor ((fderiv ℝ F (chartAction g 0)).comp (fderiv ℝ (chartAction g) 0)) := by
  rw [frameTensor, frameDifferential_eq hg]

theorem measurable_frameTensor (F : Horizontal m → Horizontal m) :
    Measurable (frameTensor F) := by
  apply measurable_normalizedTensor.comp
  simpa only [Function.comp_def, Function.uncurry_apply_pair, ContinuousLinearMap.compL_apply] using
    ((ContinuousLinearMap.compL ℝ (Horizontal m) (Horizontal m) (Horizontal m)).continuous₂.measurable.comp
      (((measurable_fderiv ℝ F).comp (measurable_chartAction_at 0)).prodMk
        measurable_frameDifferential))

theorem fderiv_chartAction_mul (g h : IsometryGroup m) {x : Horizontal m}
    (hx : x ∈ chartDomain h) (hy : chartAction h x ∈ chartDomain g) :
    fderiv ℝ (chartAction (g * h)) x =
      (fderiv ℝ (chartAction g) (chartAction h x)).comp (fderiv ℝ (chartAction h) x) := by
  have he : chartAction (g * h) =ᶠ[𝓝 x] (fun y => chartAction g (chartAction h y)) := by
    filter_upwards [(isOpen_chartDomain h).mem_nhds hx] with y hy
    exact (chartAction_mul g h hy).symm
  exact ((differentiableAt_chartAction g hy).hasFDerivAt.comp x
    (differentiableAt_chartAction h hx).hasFDerivAt).congr_of_eventuallyEq he |>.fderiv

theorem mem_chartDomain_mul (g h : IsometryGroup m) {x : Horizontal m}
    (hx : x ∈ chartDomain h) (hy : chartAction h x ∈ chartDomain g) :
    x ∈ chartDomain (g * h) := by
  change (g * h) • embed x ≠ MobiusBoundary.ptInfty
  rw [mul_smul, ← embed_chartAction h hx]
  exact hy

variable [Nonempty (Fin m)]

theorem ae_finiteFrames :
    ∀ᵐ g ∂(volume : Measure (IsometryGroup m)), g ∈ finiteFrames := by
  have h := BoundaryMeasure.haar_orbit_infty_null (embed (0 : Horizontal m))
  simpa only [ae_iff, finiteFrames, chartDomain, mem_ofPred_eq, not_not] using h

theorem quasiMeasurePreserving_framePoint :
    Measure.QuasiMeasurePreserving (fun g : IsometryGroup m => chartAction g 0) volume volume :=
  measurePreserving_coords.quasiMeasurePreserving.comp
    (BoundaryMeasure.quasiMeasurePreserving_orbit _)

theorem ae_frameTensor_left (g h : IsometryGroup m)
    (ψ : BoundaryH (m + 1) → BoundaryH (m + 1)) (F : Horizontal m → Horizontal m)
    (hF : ∀ x, embed (F x) = ψ (embed x))
    (heq : ∀ v, ψ (g • v) = h • ψ v)
    (hdiff : ∀ᵐ x ∂(volume : Measure (Horizontal m)), DifferentiableAt ℝ F x) :
    (fun k : IsometryGroup m => frameTensor F (g * k)) =ᵐ[volume] frameTensor F := by
  filter_upwards [ae_finiteFrames, quasiMeasurePreserving_framePoint.ae
    (ae_fderiv_conjugacy g h ψ F hF heq hdiff)] with k hk hchain
  have hgk : g * k ∈ finiteFrames := mem_chartDomain_mul g k hk hchain.1
  rw [frameTensor_eq F hgk, frameTensor_eq F hk,
    ← chartAction_mul g k hk, fderiv_chartAction_mul g k hk hchain.1,
    ← ContinuousLinearMap.comp_assoc, hchain.2.2, ContinuousLinearMap.comp_assoc]
  exact normalizedTensor_conformal_left _ _ (isConformalMap_fderiv_chartAction h hchain.2.1)

omit [Nonempty (Fin m)] in
theorem frameTensor_right_linear (F : Horizontal m → Horizontal m)
    (r : IsometryGroup m) (L : Horizontal m →L[ℝ] Horizontal m)
    (hr : ∀ x, r • embed x = embed (L x)) (g : IsometryGroup m) :
    frameTensor F (g * r) =
      normalizedTensor (((fderiv ℝ F (chartAction g 0)).comp (frameDifferential g)).comp L) := by
  have hd : ∀ x, x ∈ chartDomain r := fun x => by
    change r • embed x ≠ MobiusBoundary.ptInfty
    rw [hr]
    exact embed_ne_infty _
  have he : chartAction r = L := funext fun x => by
    change coords (r • embed x) = L x
    rw [hr, coords_embed]
  have hz : chartAction r 0 = 0 := by rw [he, map_zero]
  have hf : fderiv ℝ (chartAction r) 0 = L := by rw [he]; exact L.fderiv
  have hfinite : g * r ∈ finiteFrames ↔ g ∈ finiteFrames := by
    change (g * r) • embed (0 : Horizontal m) ≠ MobiusBoundary.ptInfty ↔
      g • embed (0 : Horizontal m) ≠ MobiusBoundary.ptInfty
    rw [mul_smul, hr, map_zero]
  by_cases hg : g ∈ finiteFrames
  · have hc : chartAction r 0 ∈ chartDomain g := by rw [hz]; exact hg
    rw [frameTensor_eq F (hfinite.mpr hg), ← chartAction_mul g r (hd 0),
      fderiv_chartAction_mul g r (hd 0) hc, hz, hf, frameDifferential_eq hg,
      ContinuousLinearMap.comp_assoc]
  · simp only [frameTensor, frameDifferential, ite_eq_right hg, ite_eq_right (hfinite.not.mpr hg),
      ContinuousLinearMap.comp_zero, ContinuousLinearMap.zero_comp, normalizedTensor_zero]

theorem frameTensor_right_diagonal (F : Horizontal m → Horizontal m)
    (g : IsometryGroup m) (t : ℝ) :
    frameTensor F (g * GeodesicFlow.diagonal t) = frameTensor F g := by
  have hr (x : Horizontal m) : GeodesicFlow.diagonal t • embed x =
      embed ((Real.exp t • ContinuousLinearMap.id ℝ (Horizontal m)) x) :=
    LorentzGenerators.diagonal_horo t (fun i => x i)
  rw [frameTensor_right_linear F _ _ hr, ContinuousLinearMap.comp_smul,
    ContinuousLinearMap.comp_id, normalizedTensor_smul _ (Real.exp_ne_zero t)]
  rfl

theorem frameTensor_right_isometry (F : Horizontal m → Horizontal m)
    (r : IsometryGroup m) (R : Horizontal m ≃ₗᵢ[ℝ] Horizontal m)
    (hr : ∀ x, r • embed x = embed (R x)) (g : IsometryGroup m) :
    frameTensor F (g * r) =
      (ContinuousLinearMap.adjoint R.toContinuousLinearEquiv.toContinuousLinearMap).comp
        ((frameTensor F g).comp R.toContinuousLinearEquiv.toContinuousLinearMap) := by
  rw [frameTensor_right_linear F r R.toContinuousLinearEquiv.toContinuousLinearMap hr,
    normalizedTensor_isometric_right]
  rfl

theorem ae_norm_frameTensor (F : Horizontal m → Horizontal m)
    (hF : ∀ᵐ x ∂(volume : Measure (Horizontal m)), fderiv ℝ F x ≠ 0) :
    ∀ᵐ g ∂(volume : Measure (IsometryGroup m)), ‖frameTensor F g‖ = 1 := by
  filter_upwards [ae_finiteFrames, quasiMeasurePreserving_framePoint.ae hF] with g hg hnonzero
  rw [frameTensor_eq F hg]
  apply norm_normalizedTensor
  have hC := isConformalMap_fderiv_chartAction g hg
  apply norm_ne_zero_iff.mp
  rw [DerivativeEccentricity.norm_comp_conformal_right _ _ hC]
  exact mul_ne_zero (norm_ne_zero_iff.mpr hnonzero) (norm_ne_zero_iff.mpr hC.ne_zero)

omit [Nonempty (Fin m)] in
theorem exists_quotient_tensor (Γ : Subgroup (IsometryGroup m)) [Countable Γ]
    (F : Horizontal m → Horizontal m)
    (hInv : ∀ γ : Γ, (fun g => frameTensor F ((γ : IsometryGroup m) * g))
      =ᵐ[volume] frameTensor F) :
    ∃ Tq : DifferentialGeometry.HomogeneousSpaceMeasure.FrameQuotient Γ → (Horizontal m →L[ℝ] Horizontal m),
      Measurable Tq ∧
      (fun g => Tq (DifferentialGeometry.HomogeneousSpaceMeasure.projection Γ g)) =ᵐ[volume] frameTensor F :=
  MeasurableOrbitDescent.exists_measurable_descent volume
    (fun γ : Γ => (continuous_const_mul (γ : IsometryGroup m)).measurable)
    (frameTensor F) (measurable_frameTensor F) hInv 0

end DifferentialGeometry.MovingFrameTensor
