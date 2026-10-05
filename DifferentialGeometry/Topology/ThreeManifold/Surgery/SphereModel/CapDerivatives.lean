import DifferentialGeometry.Topology.ThreeManifold.Surgery.SphereModel.CapCoordinates
import Mathlib.Analysis.InnerProductSpace.Calculus

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Metric Module
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open private ChartE3 ChartE4 standardNeckCapDenAmbient_eq standardNeckCapAmbientS standardNeckCapAmbientT standardNeckCapAmbientLast standardNeckCapAmbientComponent standardNeckCapUAmbient_eq standardNeckCapCAmbient_eq
  from DifferentialGeometry.Topology.ThreeManifold.Surgery.SphereModel.CapCoordinates

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

open private standardNeckCapDenNe from DifferentialGeometry.Topology.ThreeManifold.Surgery.SphereModel.CapCoordinates

theorem hasFDerivAt_capDen (v : E3) :
    HasFDerivAt (fun w : E3 => 1 + standardNeckCapAmbientRadius ^ 2 * ‖w‖ ^ 2)
      ((2 * standardNeckCapAmbientRadius ^ 2) • innerSL ℝ v) v := by
  have h1 := ((hasStrictFDerivAt_norm_sq v).hasFDerivAt).const_mul (standardNeckCapAmbientRadius ^ 2)
  have h2 := h1.const_add (1 : ℝ)
  simpa only [two_nsmul, ← two_smul ℝ, smul_smul, mul_comm, mul_left_comm, mul_assoc] using h2

theorem hasFDerivAt_capDenInv (v : E3) :
    HasFDerivAt ((fun x : ℝ => x⁻¹) ∘ standardNeckCapDenAmbient)
      (ContinuousLinearMap.toSpanSingleton ℝ (-(standardNeckCapDenAmbient v ^ 2)⁻¹) ∘SL
        ((2 * standardNeckCapAmbientRadius ^ 2) • innerSL ℝ v)) v := by
  have hden : HasFDerivAt (fun w : E3 => standardNeckCapDenAmbient w)
      ((2 * standardNeckCapAmbientRadius ^ 2) • innerSL ℝ v) v := by
    simpa only [standardNeckCapDenAmbient_eq] using hasFDerivAt_capDen v
  have hne : standardNeckCapDenAmbient v ≠ 0 :=
    fun hzero => standardNeckCapDenNe v (by simpa only [standardNeckCapDenAmbient_eq] using hzero)
  exact (hasFDerivAt_inv hne).comp v hden

theorem hasFDerivAt_capNumT (v : E3) :
    HasFDerivAt (fun w : E3 => 1 - standardNeckCapAmbientRadius ^ 2 * ‖w‖ ^ 2)
      ((-(2 * standardNeckCapAmbientRadius ^ 2)) • innerSL ℝ v) v := by
  have h := ((hasStrictFDerivAt_norm_sq v).hasFDerivAt).const_mul (standardNeckCapAmbientRadius ^ 2)
  have h2 := h.const_sub (1 : ℝ)
  simpa only [two_nsmul, ← two_smul ℝ, neg_smul, smul_smul, mul_comm, mul_left_comm, mul_assoc] using h2

theorem hasFDerivAt_capSRaw (v : E3) :
    HasFDerivAt (fun w : E3 => (2 * standardNeckCapAmbientRadius) *
        ((fun x : ℝ => x⁻¹) ∘ standardNeckCapDenAmbient) w)
      ((2 * standardNeckCapAmbientRadius) •
        (ContinuousLinearMap.toSpanSingleton ℝ (-(standardNeckCapDenAmbient v ^ 2)⁻¹) ∘SL
          ((2 * standardNeckCapAmbientRadius ^ 2) • innerSL ℝ v))) v :=
  (hasFDerivAt_capDenInv v).const_mul (2 * standardNeckCapAmbientRadius)

theorem hasFDerivAt_capTRaw (v : E3) :
    HasFDerivAt ((fun w : E3 => 1 - standardNeckCapAmbientRadius ^ 2 * ‖w‖ ^ 2) *
        ((fun x : ℝ => x⁻¹) ∘ standardNeckCapDenAmbient))
      ((1 - standardNeckCapAmbientRadius ^ 2 * ‖v‖ ^ 2) •
          ContinuousLinearMap.toSpanSingleton ℝ (-(standardNeckCapDenAmbient v ^ 2)⁻¹) ∘SL
            ((2 * standardNeckCapAmbientRadius ^ 2) • (innerSL ℝ) v) +
        ((fun x : ℝ => x⁻¹) ∘ standardNeckCapDenAmbient) v • -(2 * standardNeckCapAmbientRadius ^ 2) • (innerSL ℝ) v)
      v :=
  (hasFDerivAt_capNumT v).mul (hasFDerivAt_capDenInv v)

theorem hasFDerivAt_capURaw (v : E3) :
    HasFDerivAt ((fun w : E3 => 2 * standardNeckCapAmbientRadius *
        ((fun x : ℝ => x⁻¹) ∘ standardNeckCapDenAmbient) w) • id)
      ((2 * standardNeckCapAmbientRadius *
            ((fun x : ℝ => x⁻¹) ∘ standardNeckCapDenAmbient) v) • ContinuousLinearMap.id ℝ E3 +
          ((2 * standardNeckCapAmbientRadius) •
                ContinuousLinearMap.toSpanSingleton ℝ (-(standardNeckCapDenAmbient v ^ 2)⁻¹) ∘SL
                  ((2 * standardNeckCapAmbientRadius ^ 2) • (innerSL ℝ) v)).smulRight
            (id v))
      v :=
  (hasFDerivAt_capSRaw v).smul (hasFDerivAt_id v)

attribute [local instance] threeBallChartedSpace threeBall_isManifold

private abbrev standardNeckCapInclProjection : (i : Fin 4) → ChartE3 →L[ℝ] ℝ :=
  fun i => Fin.lastCases 0
    (fun j => PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) j) i

private abbrev standardNeckCapFrameProj : Fin 4 → (ChartE3 →L[ℝ] ℝ) :=
  (2 * standardNeckCapAmbientRadius) •
    (standardNeckCapInclProjection : (i : Fin 4) → ChartE3 →L[ℝ] ℝ)

private abbrev standardNeckCapIncl : ChartE3 →L[ℝ] ChartE4 :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi standardNeckCapInclProjection)

abbrev standardNeckCapAmbientDeriv : ChartE3 →L[ℝ] ChartE4 :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi standardNeckCapFrameProj)

private theorem standardNeckCapInclProjection_frame (k : Fin 3) :
    (ContinuousLinearMap.pi standardNeckCapInclProjection) (EuclideanSpace.single k (1 : ℝ))
      = Pi.single (M := fun _ : Fin 4 => ℝ) (Fin.castSucc k) (1 : ℝ) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [ContinuousLinearMap.pi_apply, standardNeckCapInclProjection, Fin.lastCases_last,
      zero_apply, Pi.single_eq_of_ne (M := fun _ : Fin 4 => ℝ) (Fin.castSucc_ne_last k).symm]
  · simp only [ContinuousLinearMap.pi_apply, standardNeckCapInclProjection, Fin.lastCases_castSucc,
      PiLp.proj_apply, PiLp.ofLp_single]
    by_cases hjk : j = k
    · subst hjk
      simp only [Pi.single_eq_same]
    · have hne : j.castSucc ≠ k.castSucc := fun hc => hjk (Fin.castSucc_injective 3 hc)
      rw [Pi.single_eq_of_ne (M := fun _ : Fin 3 => ℝ) hjk,
        Pi.single_eq_of_ne (M := fun _ : Fin 4 => ℝ) hne]

private theorem standardNeckCapFrameProj_frame (k : Fin 3) :
    (ContinuousLinearMap.pi standardNeckCapFrameProj) (EuclideanSpace.single k (1 : ℝ))
      = (2 * standardNeckCapAmbientRadius) •
          Pi.single (M := fun _ : Fin 4 => ℝ) (Fin.castSucc k) (1 : ℝ) := by
  have h := standardNeckCapInclProjection_frame k
  funext i
  rw [ContinuousLinearMap.pi_apply]
  rw [show standardNeckCapFrameProj i =
      (2 * standardNeckCapAmbientRadius) • standardNeckCapInclProjection i from rfl, smul_apply]
  rw [show (standardNeckCapInclProjection i) (EuclideanSpace.single k (1 : ℝ))
      = ((ContinuousLinearMap.pi standardNeckCapInclProjection)
          (EuclideanSpace.single k (1 : ℝ))) i from
    (ContinuousLinearMap.pi_apply standardNeckCapInclProjection _ i).symm]
  rw [h, Pi.smul_apply]

theorem standardNeckCapAmbientDeriv_basis (k : Fin 3) :
    standardNeckCapAmbientDeriv (EuclideanSpace.single k (1 : ℝ)) =
      (2 * standardNeckCapAmbientRadius) •
        EuclideanSpace.single (Fin.castSucc k) (1 : ℝ) := by
  rw [standardNeckCapAmbientDeriv, ContinuousLinearMap.comp_apply,
    standardNeckCapFrameProj_frame k]
  rfl

theorem standardNeckCapAmbientDeriv_eq_smul_incl :
    standardNeckCapAmbientDeriv = (2 * standardNeckCapAmbientRadius) • standardNeckCapIncl := by
  apply ContinuousLinearMap.ext
  intro v
  rw [standardNeckCapAmbientDeriv, standardNeckCapIncl, ContinuousLinearMap.comp_apply,
    smul_apply, ContinuousLinearMap.comp_apply]
  have hpi : (ContinuousLinearMap.pi standardNeckCapFrameProj) v =
      (2 * standardNeckCapAmbientRadius) •
        (ContinuousLinearMap.pi standardNeckCapInclProjection) v := by
    funext i
    rw [ContinuousLinearMap.pi_apply, Pi.smul_apply, ContinuousLinearMap.pi_apply]
    rfl
  rw [hpi]
  exact map_smul _ _ _

private theorem hasFDerivAt_standardNeckCapAmbientS :
    HasFDerivAt (𝕜 := ℝ) standardNeckCapAmbientS 0 0 := by
  have hfun : standardNeckCapAmbientS =
      fun v : ChartE3 => (2 * standardNeckCapAmbientRadius) *
        (standardNeckCapDenAmbient v)⁻¹ := by
    funext v
    rw [standardNeckCapAmbientS, standardNeckCapDenAmbient_eq, div_eq_mul_inv]
  rw [hfun]
  simpa [Function.comp_def] using hasFDerivAt_capSRaw (0 : ChartE3)

private theorem hasFDerivAt_standardNeckCapAmbientT :
    HasFDerivAt (𝕜 := ℝ) standardNeckCapAmbientT 0 0 := by
  have hfun : standardNeckCapAmbientT = fun v : ChartE3 =>
      (1 - standardNeckCapAmbientRadius ^ 2 * ‖v‖ ^ 2) *
        (standardNeckCapDenAmbient v)⁻¹ := by
    funext v
    rw [standardNeckCapAmbientT, standardNeckCapDenAmbient_eq, div_eq_mul_inv]
  rw [hfun]
  convert! hasFDerivAt_capTRaw (0 : ChartE3) using 1
  simp

private theorem hasFDerivAt_standardNeckCapAmbientLast (side : Bool) :
    HasFDerivAt (𝕜 := ℝ) (standardNeckCapAmbientLast side) 0 0 := by
  cases side with
  | false =>
      have hfun : standardNeckCapAmbientLast false = standardNeckCapAmbientT := by
        funext v
        simp [standardNeckCapAmbientLast, standardNeckCapCAmbient_eq]
      rw [hfun]
      exact hasFDerivAt_standardNeckCapAmbientT
  | true =>
      have hfun : standardNeckCapAmbientLast true = -standardNeckCapAmbientT := by
        funext v
        simp [standardNeckCapAmbientLast, standardNeckCapCAmbient_eq]
      rw [hfun]
      simpa using hasFDerivAt_standardNeckCapAmbientT.neg

private theorem hasFDerivAt_standardNeckCapAmbientComponent (j : Fin 3) :
    HasFDerivAt (𝕜 := ℝ) (standardNeckCapAmbientComponent j)
      ((2 * standardNeckCapAmbientRadius) •
        PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) j) 0 := by
  have hproj : HasFDerivAt (𝕜 := ℝ) (fun v : ChartE3 => v.ofLp j)
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) j) 0 := by
    simpa using (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) j).hasFDerivAt
  have h := hasFDerivAt_standardNeckCapAmbientS.mul hproj
  have h0 : standardNeckCapAmbientS (0 : ChartE3) = 2 * standardNeckCapAmbientRadius := by
    rw [standardNeckCapAmbientS]
    norm_num
  have hz : (0 : ChartE3).ofLp j = 0 := rfl
  have hfun : (standardNeckCapAmbientS * fun v : ChartE3 => v.ofLp j) =
      standardNeckCapAmbientComponent j := by
    funext v
    rw [Pi.mul_apply, standardNeckCapAmbientComponent]
  rw [hfun] at h
  simpa [h0, hz] using h

private theorem hasFDerivAt_ofLp_standardNeckCapPointAmbient (side : Bool) :
    HasFDerivAt (𝕜 := ℝ)
      (fun v : ChartE3 => WithLp.ofLp (standardNeckCapPointAmbient side v))
      (ContinuousLinearMap.pi standardNeckCapFrameProj) 0 := by
  rw [hasFDerivAt_pi]
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · have hfun : (fun v : ChartE3 =>
        WithLp.ofLp (standardNeckCapPointAmbient side v) (Fin.last 3)) =
        standardNeckCapAmbientLast side := by
      funext v
      show (standardNeckCapPointAmbient side v).ofLp (Fin.last 3) =
        standardNeckCapAmbientLast side v
      rw [standardNeckCapPointAmbient, WithLp.ofLp_toLp, snocR_last, standardNeckCapAmbientLast]
    rw [hfun]
    rw [show standardNeckCapFrameProj (Fin.last 3) = 0 from by
      rw [standardNeckCapFrameProj, Pi.smul_apply,
        show standardNeckCapInclProjection (Fin.last 3) = 0 from by
          rw [standardNeckCapInclProjection]
          exact Fin.lastCases_last]
      simp]
    exact hasFDerivAt_standardNeckCapAmbientLast side
  · have hfun : (fun v : ChartE3 =>
        WithLp.ofLp (standardNeckCapPointAmbient side v) (Fin.castSucc j)) =
        standardNeckCapAmbientComponent j := by
      funext v
      show (standardNeckCapPointAmbient side v).ofLp (Fin.castSucc j) =
        standardNeckCapAmbientComponent j v
      rw [standardNeckCapPointAmbient, WithLp.ofLp_toLp, snocR_castSucc,
        standardNeckCapUAmbient_eq, standardNeckCapAmbientComponent]
      rfl
    rw [hfun]
    rw [show standardNeckCapFrameProj (Fin.castSucc j) =
        (2 * standardNeckCapAmbientRadius) •
          PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) j from by
      rw [standardNeckCapFrameProj, Pi.smul_apply,
        show standardNeckCapInclProjection (Fin.castSucc j) =
          PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) j from by
          rw [standardNeckCapInclProjection]
          exact Fin.lastCases_castSucc j]]
    exact hasFDerivAt_standardNeckCapAmbientComponent j

theorem hasFDerivAt_standardNeckCapPointAmbient (side : Bool) :
    HasFDerivAt (standardNeckCapPointAmbient side) standardNeckCapAmbientDeriv 0 := by
  have h := (PiLp.hasFDerivAt_toLp (𝕜 := ℝ) 2
      (WithLp.ofLp (standardNeckCapPointAmbient side (0 : ChartE3)))).comp (0 : ChartE3)
    (hasFDerivAt_ofLp_standardNeckCapPointAmbient side)
  have hfun : WithLp.toLp 2 ∘
      (fun v : ChartE3 => WithLp.ofLp (standardNeckCapPointAmbient side v)) =
      standardNeckCapPointAmbient side := by
    funext v
    rw [Function.comp_apply, WithLp.toLp_ofLp]
  rw [hfun] at h
  exact h

theorem mfderiv_standardNeckCapPointAmbient (side : Bool) :
    mfderiv 𝓘(ℝ, ChartE3) 𝓘(ℝ, ChartE4) (standardNeckCapPointAmbient side) 0 =
      standardNeckCapAmbientDeriv := by
  rw [mfderiv_eq_fderiv]
  exact (hasFDerivAt_standardNeckCapPointAmbient side).fderiv

theorem mdifferentiableAt_threeBall_val :
    MDifferentiableAt (𝓡∂ 3) (𝓘(ℝ, ChartE3)) (Subtype.val : ThreeBall → ChartE3) 0 :=
  isSmoothEmbedding_threeBall_inclusion.contMDiff.contMDiffAt.mdifferentiableAt (by norm_num)

theorem hasMFDerivAt_standardNeckCapPointAmbient_zero (side : Bool) :
    HasMFDerivAt 𝓘(ℝ, ChartE3) 𝓘(ℝ, ChartE4) (standardNeckCapPointAmbient side) 0
      standardNeckCapAmbientDeriv :=
  (hasFDerivAt_standardNeckCapPointAmbient side).hasMFDerivAt

theorem mfderiv_standardNeckCapAmbient (side : Bool) :
    mfderiv (𝓡∂ 3) (𝓘(ℝ, ChartE4)) (standardNeckCapAmbient side) 0 =
      standardNeckCapAmbientDeriv ∘L
        mfderiv (𝓡∂ 3) (𝓘(ℝ, ChartE3)) (Subtype.val : ThreeBall → ChartE3) 0 := by
  have h1 : HasMFDerivAt 𝓘(ℝ, ChartE3) 𝓘(ℝ, ChartE4) (standardNeckCapPointAmbient side)
      ((0 : ThreeBall) : ChartE3) standardNeckCapAmbientDeriv :=
    hasMFDerivAt_standardNeckCapPointAmbient_zero side
  have h2 : HasMFDerivAt (𝓡∂ 3) (𝓘(ℝ, ChartE3)) (Subtype.val : ThreeBall → ChartE3) 0
      (mfderiv (𝓡∂ 3) (𝓘(ℝ, ChartE3)) (Subtype.val : ThreeBall → ChartE3) 0) :=
    mdifferentiableAt_threeBall_val.hasMFDerivAt
  have hcomp := h1.comp (0 : ThreeBall) h2
  have hfun : standardNeckCapAmbient side =
      (standardNeckCapPointAmbient side) ∘ (Subtype.val : ThreeBall → ChartE3) := rfl
  rw [hfun]
  exact hcomp.mfderiv

theorem mdifferentiableAt_standardSphere_val (z : Sphere 3) :
    MDifferentiableAt (𝓡 3) (𝓡 4) (Subtype.val : Sphere 3 → ChartE4) z :=
  (contMDiff_coe_sphere (n := 3) (m := ∞)).mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0)

theorem mdifferentiableAt_sumInl (z : Sphere 3) :
    MDifferentiableAt (𝓡 3) ThreeModel (Sum.inl : Sphere 3 → Sphere 3 ⊕ Sphere 3) z :=
  (ContMDiff.inl (I := ThreeModel) (M := Sphere 3) (M' := Sphere 3)).mdifferentiableAt
    (by simp : (∞ : ℕ∞ω) ≠ 0)

theorem mdifferentiableAt_sumInr (z : Sphere 3) :
    MDifferentiableAt (𝓡 3) ThreeModel (Sum.inr : Sphere 3 → Sphere 3 ⊕ Sphere 3) z :=
  (ContMDiff.inr (I := ThreeModel) (M := Sphere 3) (M' := Sphere 3)).mdifferentiableAt
    (by simp : (∞ : ℕ∞ω) ≠ 0)

theorem mfderiv_standardNeckCapping_apply_false
    (v : TangentSpace (𝓡∂ 3) (0 : ThreeBall)) :
    (mfderiv (𝓡 3) (𝓡 4) (Subtype.val : Sphere 3 → ChartE4) (standardNeckCapFun false 0))
        ((mfderiv (𝓡∂ 3) ThreeModel (standardNeckCapping.cap standardNeckBoundaryFalse) 0) v)
      = (mfderiv (𝓡∂ 3) (𝓘(ℝ, ChartE4)) (standardNeckCapAmbient false) 0) v := by
  have hcap : (mfderiv (𝓡∂ 3) ThreeModel
        (standardNeckCapping.cap standardNeckBoundaryFalse) 0) v
      = (mfderiv (𝓡∂ 3) (𝓡 3) (standardNeckCapFun false) 0) v := by
    rw [standardNeckCapping_cap_false,
      mfderiv_comp_apply (0 : ThreeBall)
        (mdifferentiableAt_sumInl (standardNeckCapFun false 0))
        (mdifferentiableAt_standardNeckCapFun false) v]
    exact congrFun (congrArg DFunLike.coe (mfderiv_sumInl (M := Sphere 3) (M' := Sphere 3)
      (I := ThreeModel) (p := (Sum.inl (standardNeckCapFun false 0) : Sphere 3 ⊕ Sphere 3))
      (q := standardNeckCapFun false 0)))
      ((mfderiv (𝓡∂ 3) (𝓡 3) (standardNeckCapFun false) 0) v)
  rw [hcap]
  exact (mfderiv_comp_apply (0 : ThreeBall)
    (mdifferentiableAt_standardSphere_val (standardNeckCapFun false 0))
    (mdifferentiableAt_standardNeckCapFun false) v).symm

theorem mfderiv_standardNeckCapping_apply_true
    (v : TangentSpace (𝓡∂ 3) (0 : ThreeBall)) :
    (mfderiv (𝓡 3) (𝓡 4) (Subtype.val : Sphere 3 → ChartE4) (standardNeckCapFun true 0))
        ((mfderiv (𝓡∂ 3) ThreeModel (standardNeckCapping.cap (PUnit.unit, true)) 0) v)
      = (mfderiv (𝓡∂ 3) (𝓘(ℝ, ChartE4)) (standardNeckCapAmbient true) 0) v := by
  have hcap : (mfderiv (𝓡∂ 3) ThreeModel (standardNeckCapping.cap (PUnit.unit, true)) 0) v
      = (mfderiv (𝓡∂ 3) (𝓡 3) (standardNeckCapFun true) 0) v := by
    rw [standardNeckCapping_cap_true,
      mfderiv_comp_apply (0 : ThreeBall)
        (mdifferentiableAt_sumInr (standardNeckCapFun true 0))
        (mdifferentiableAt_standardNeckCapFun true) v]
    exact congrFun (congrArg DFunLike.coe (mfderiv_sumInr (M := Sphere 3) (M' := Sphere 3)
      (I := ThreeModel) (q' := standardNeckCapFun true 0)))
      ((mfderiv (𝓡∂ 3) (𝓡 3) (standardNeckCapFun true) 0) v)
  rw [hcap]
  exact (mfderiv_comp_apply (0 : ThreeBall)
    (mdifferentiableAt_standardSphere_val (standardNeckCapFun true 0))
    (mdifferentiableAt_standardNeckCapFun true) v).symm

abbrev standardNeckCapChartVector (k : Fin 3) : TangentSpace (𝓘(ℝ, ChartE3)) (0 : ChartE3) :=
  (EuclideanSpace.single k (1 : ℝ) : TangentSpace (𝓘(ℝ, ChartE3)) (0 : ChartE3))

theorem standardNeckCapChartVector_eq_single (k : Fin 3) :
    standardNeckCapChartVector k = EuclideanSpace.single k (1 : ℝ) := rfl

theorem standardNeckCapping_frame_dictionary_false
    (hi : Function.Bijective (mfderiv (𝓡∂ 3) ThreeModel
      (Subtype.val : ThreeBall → ThreeSpace) 0))
    (hj : Function.Bijective (mfderiv (𝓡∂ 3) ThreeModel
      (standardNeckCapping.cap standardNeckBoundaryFalse) 0)) (k : Fin 3) :
    (mfderiv (𝓡 3) (𝓡 4) (Subtype.val : Sphere 3 → ChartE4) (standardNeckCapFun false 0))
        (((LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) ThreeModel
              (Subtype.val : ThreeBall → ThreeSpace) 0).toLinearMap hi).symm.trans
          (LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) ThreeModel
              (standardNeckCapping.cap standardNeckBoundaryFalse) 0).toLinearMap hj))
          (standardNeckCapChartVector k))
      = (2 * standardNeckCapAmbientRadius) •
          EuclideanSpace.single (Fin.castSucc k) (1 : ℝ) := by
  have hLE : (((LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) ThreeModel
        (Subtype.val : ThreeBall → ThreeSpace) 0).toLinearMap hi).symm.trans
        (LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) ThreeModel
          (standardNeckCapping.cap standardNeckBoundaryFalse) 0).toLinearMap hj))
        (standardNeckCapChartVector k))
      = (mfderiv (𝓡∂ 3) ThreeModel (standardNeckCapping.cap standardNeckBoundaryFalse) 0)
          (((LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) ThreeModel
            (Subtype.val : ThreeBall → ThreeSpace) 0).toLinearMap hi).symm)
            (standardNeckCapChartVector k)) := by
    simp only [LinearEquiv.trans_apply, LinearEquiv.ofBijective_apply]
    rfl
  rw [hLE, mfderiv_standardNeckCapping_apply_false]
  have hstep : (mfderiv (𝓡∂ 3) (𝓘(ℝ, ChartE4)) (standardNeckCapAmbient false) 0)
      (((LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) ThreeModel
        (Subtype.val : ThreeBall → ThreeSpace) 0).toLinearMap hi).symm)
        (standardNeckCapChartVector k))
      = standardNeckCapAmbientDeriv (standardNeckCapChartVector k) := by
    rw [mfderiv_standardNeckCapAmbient]
    change standardNeckCapAmbientDeriv
        ((mfderiv (𝓡∂ 3) (𝓘(ℝ, ChartE3)) (Subtype.val : ThreeBall → ChartE3) 0)
          ((LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) ThreeModel
              (Subtype.val : ThreeBall → ThreeSpace) 0).toLinearMap hi).symm
            (standardNeckCapChartVector k)))
      = standardNeckCapAmbientDeriv (standardNeckCapChartVector k)
    congr 1
    exact show (LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) ThreeModel
          (Subtype.val : ThreeBall → ThreeSpace) 0).toLinearMap hi)
        ((LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) ThreeModel
            (Subtype.val : ThreeBall → ThreeSpace) 0).toLinearMap hi).symm
          (standardNeckCapChartVector k)) = standardNeckCapChartVector k from
      LinearEquiv.apply_symm_apply _ _
  rw [hstep]
  rw [standardNeckCapChartVector_eq_single]
  exact standardNeckCapAmbientDeriv_basis k

private def standardNeckCapFourCycle : Equiv.Perm (Fin 4) :=
  Equiv.swap 2 3 * Equiv.swap 1 2 * Equiv.swap 0 1

private theorem standardNeckCapFourCycle_sign : Equiv.Perm.sign standardNeckCapFourCycle = -1 := by
  rw [standardNeckCapFourCycle, map_mul, map_mul, Equiv.Perm.sign_swap (by decide),
    Equiv.Perm.sign_swap (by decide), Equiv.Perm.sign_swap (by decide)]
  decide

private theorem standardNeckCapFourCycle_zero : standardNeckCapFourCycle 0 = Fin.last 3 := by
  decide

private theorem standardNeckCapFourCycle_one : standardNeckCapFourCycle 1 = 0 := by decide

private theorem standardNeckCapFourCycle_two : standardNeckCapFourCycle 2 = 1 := by decide

private theorem standardNeckCapFourCycle_three : standardNeckCapFourCycle 3 = 2 := by decide

private theorem standardNeckCapAmbientBaseFrame :
    (fun j : Fin 4 => EuclideanSpace.basisFun (Fin 4) ℝ (standardNeckCapFourCycle j)) =
      Fin.cons (EuclideanSpace.single (Fin.last 3) (1 : ℝ))
        (Fin.cons (EuclideanSpace.single 0 (1 : ℝ))
          (Fin.cons (EuclideanSpace.single 1 (1 : ℝ))
            (Fin.cons (EuclideanSpace.single 2 (1 : ℝ)) ![]))) := by
  funext j
  fin_cases j <;>
    simp [standardNeckCapFourCycle_zero, standardNeckCapFourCycle_one, standardNeckCapFourCycle_two,
      standardNeckCapFourCycle_three]

theorem standardNeckCapFrame_det :
    (EuclideanSpace.basisFun (Fin 4) ℝ).toBasis.det
        (Fin.cons (EuclideanSpace.single (Fin.last 3) (1 : ℝ))
          (Fin.cons ((2 * standardNeckCapAmbientRadius) • EuclideanSpace.single 0 (1 : ℝ))
            (Fin.cons ((2 * standardNeckCapAmbientRadius) • EuclideanSpace.single 1 (1 : ℝ))
              (Fin.cons ((2 * standardNeckCapAmbientRadius) • EuclideanSpace.single 2 (1 : ℝ))
                ![])))) =
      -((2 * standardNeckCapAmbientRadius) ^ 3) := by
  have hframe : Fin.cons (EuclideanSpace.single (Fin.last 3) (1 : ℝ))
      (Fin.cons ((2 * standardNeckCapAmbientRadius) • EuclideanSpace.single 0 (1 : ℝ))
        (Fin.cons ((2 * standardNeckCapAmbientRadius) • EuclideanSpace.single 1 (1 : ℝ))
          (Fin.cons ((2 * standardNeckCapAmbientRadius) • EuclideanSpace.single 2 (1 : ℝ))
            ![]))) =
      (fun j : Fin 4 => (if j = 0 then (1 : ℝ) else 2 * standardNeckCapAmbientRadius) •
        EuclideanSpace.basisFun (Fin 4) ℝ (standardNeckCapFourCycle j)) := by
    funext j
    fin_cases j <;>
      simp [standardNeckCapFourCycle_zero, standardNeckCapFourCycle_one,
        standardNeckCapFourCycle_two, standardNeckCapFourCycle_three]
  rw [hframe]
  have h := AlternatingMap.map_smul_univ (EuclideanSpace.basisFun (Fin 4) ℝ).toBasis.det
    (fun j : Fin 4 => if j = 0 then (1 : ℝ) else 2 * standardNeckCapAmbientRadius)
    (fun j : Fin 4 => EuclideanSpace.basisFun (Fin 4) ℝ (standardNeckCapFourCycle j))
  rw [h]
  have hperm : (EuclideanSpace.basisFun (Fin 4) ℝ).toBasis.det
      (fun j : Fin 4 => EuclideanSpace.basisFun (Fin 4) ℝ (standardNeckCapFourCycle j)) = -1 := by
    change (EuclideanSpace.basisFun (Fin 4) ℝ).toBasis.det
      (⇑(EuclideanSpace.basisFun (Fin 4) ℝ).toBasis ∘ ⇑standardNeckCapFourCycle) = -1
    have h2 := AlternatingMap.map_perm (EuclideanSpace.basisFun (Fin 4) ℝ).toBasis.det
      (⇑(EuclideanSpace.basisFun (Fin 4) ℝ).toBasis) standardNeckCapFourCycle
    rw [Basis.det_self, standardNeckCapFourCycle_sign] at h2
    rw [h2]
    norm_num
  rw [hperm]
  have hprod : (∏ i : Fin 4, (if i = 0 then (1 : ℝ) else 2 * standardNeckCapAmbientRadius)) =
      (2 * standardNeckCapAmbientRadius) ^ 3 := by
    rw [Fin.prod_univ_succ]
    norm_num [Fin.prod_univ_succ]
  rw [hprod, smul_eq_mul, mul_neg, mul_one]

theorem standardNeckCapFrame_det_neg : -((2 * standardNeckCapAmbientRadius) ^ 3) < 0 := by
  have h : (0 : ℝ) < 2 * standardNeckCapAmbientRadius := by
    have := standardNeckCapRadius_pos
    linarith
  have h3 : (0 : ℝ) < (2 * standardNeckCapAmbientRadius) ^ 3 := pow_pos h 3
  linarith

theorem standardNeckCapFun_false_zero_val :
    (standardNeckCapFun false 0).1 = EuclideanSpace.single (Fin.last 3) (1 : ℝ) := by
  rw [standardNeckCapFun_val_eq_ambient,
    show ((0 : ThreeBall) : ChartE3) = (0 : ChartE3) from rfl,
    standardNeckCapPointAmbient_false_zero]

theorem standardNeckCapFrame_det_not_pos :
    ¬ (0 < (EuclideanSpace.basisFun (Fin 4) ℝ).toBasis.det
        (Fin.cons (EuclideanSpace.single (Fin.last 3) (1 : ℝ))
          (Fin.cons ((2 * standardNeckCapAmbientRadius) • EuclideanSpace.single 0 (1 : ℝ))
            (Fin.cons ((2 * standardNeckCapAmbientRadius) • EuclideanSpace.single 1 (1 : ℝ))
              (Fin.cons ((2 * standardNeckCapAmbientRadius) • EuclideanSpace.single 2 (1 : ℝ))
                ![]))))) := by
  rw [standardNeckCapFrame_det]
  exact not_lt.mpr standardNeckCapFrame_det_neg.le

theorem standardNeckCapDictionaryFrame_det
    (hi : Function.Bijective (mfderiv (𝓡∂ 3) ThreeModel
      (Subtype.val : ThreeBall → ThreeSpace) 0))
    (hj : Function.Bijective (mfderiv (𝓡∂ 3) ThreeModel
      (standardNeckCapping.cap standardNeckBoundaryFalse) 0)) :
    (EuclideanSpace.basisFun (Fin 4) ℝ).toBasis.det
        (Fin.cons (EuclideanSpace.single (Fin.last 3) (1 : ℝ))
          (Fin.cons ((mfderiv (𝓡 3) (𝓡 4) (Subtype.val : Sphere 3 → ChartE4)
              (standardNeckCapFun false 0))
              (((LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) ThreeModel
                    (Subtype.val : ThreeBall → ThreeSpace) 0).toLinearMap hi).symm.trans
                (LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) ThreeModel
                    (standardNeckCapping.cap standardNeckBoundaryFalse) 0).toLinearMap hj))
                (standardNeckCapChartVector 0)))
            (Fin.cons ((mfderiv (𝓡 3) (𝓡 4) (Subtype.val : Sphere 3 → ChartE4)
                (standardNeckCapFun false 0))
                (((LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) ThreeModel
                      (Subtype.val : ThreeBall → ThreeSpace) 0).toLinearMap hi).symm.trans
                  (LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) ThreeModel
                      (standardNeckCapping.cap standardNeckBoundaryFalse) 0).toLinearMap hj))
                  (standardNeckCapChartVector 1)))
              (Fin.cons ((mfderiv (𝓡 3) (𝓡 4) (Subtype.val : Sphere 3 → ChartE4)
                  (standardNeckCapFun false 0))
                  (((LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) ThreeModel
                        (Subtype.val : ThreeBall → ThreeSpace) 0).toLinearMap hi).symm.trans
                    (LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) ThreeModel
                        (standardNeckCapping.cap standardNeckBoundaryFalse) 0).toLinearMap hj))
                    (standardNeckCapChartVector 2)))
                ![])))) =
      -((2 * standardNeckCapAmbientRadius) ^ 3) := by
  rw [standardNeckCapping_frame_dictionary_false hi hj 0,
    standardNeckCapping_frame_dictionary_false hi hj 1,
    standardNeckCapping_frame_dictionary_false hi hj 2]
  exact standardNeckCapFrame_det

theorem standardNeckCapDictionaryFrame_det_not_pos
    (hi : Function.Bijective (mfderiv (𝓡∂ 3) ThreeModel
      (Subtype.val : ThreeBall → ThreeSpace) 0))
    (hj : Function.Bijective (mfderiv (𝓡∂ 3) ThreeModel
      (standardNeckCapping.cap standardNeckBoundaryFalse) 0)) :
    ¬ (0 < (EuclideanSpace.basisFun (Fin 4) ℝ).toBasis.det
        (Fin.cons (EuclideanSpace.single (Fin.last 3) (1 : ℝ))
          (Fin.cons ((mfderiv (𝓡 3) (𝓡 4) (Subtype.val : Sphere 3 → ChartE4)
              (standardNeckCapFun false 0))
              (((LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) ThreeModel
                    (Subtype.val : ThreeBall → ThreeSpace) 0).toLinearMap hi).symm.trans
                (LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) ThreeModel
                    (standardNeckCapping.cap standardNeckBoundaryFalse) 0).toLinearMap hj))
                (standardNeckCapChartVector 0)))
            (Fin.cons ((mfderiv (𝓡 3) (𝓡 4) (Subtype.val : Sphere 3 → ChartE4)
                (standardNeckCapFun false 0))
                (((LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) ThreeModel
                      (Subtype.val : ThreeBall → ThreeSpace) 0).toLinearMap hi).symm.trans
                  (LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) ThreeModel
                      (standardNeckCapping.cap standardNeckBoundaryFalse) 0).toLinearMap hj))
                  (standardNeckCapChartVector 1)))
              (Fin.cons ((mfderiv (𝓡 3) (𝓡 4) (Subtype.val : Sphere 3 → ChartE4)
                  (standardNeckCapFun false 0))
                  (((LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) ThreeModel
                        (Subtype.val : ThreeBall → ThreeSpace) 0).toLinearMap hi).symm.trans
                    (LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) ThreeModel
                        (standardNeckCapping.cap standardNeckBoundaryFalse) 0).toLinearMap hj))
                    (standardNeckCapChartVector 2)))
                ![]))))) := by
  rw [standardNeckCapDictionaryFrame_det hi hj]
  exact not_lt.mpr standardNeckCapFrame_det_neg.le

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
