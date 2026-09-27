import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StandardNeckCutCapInstance
import DifferentialGeometry.Topology.Manifold.SphereOutwardFrameDictionary

set_option autoImplicit false
noncomputable section
open Bundle Manifold Set Metric Module
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

local instance : Fact ((-2 : ℝ) < 2) := ⟨by norm_num⟩

private abbrev ChartE3 := EuclideanSpace ℝ (Fin 3)

private abbrev ChartE4 := EuclideanSpace ℝ (Fin 4)

def standardNeckCapAmbientRadius : ℝ := Real.sqrt (5 / 3)

def standardNeckCapWAmbient (v : ChartE3) : ChartE3 := standardNeckCapAmbientRadius • v

def standardNeckCapDenAmbient (v : ChartE3) : ℝ := 1 + ‖standardNeckCapWAmbient v‖ ^ 2

def standardNeckCapUAmbient (v : ChartE3) : ChartE3 :=
  (2 / standardNeckCapDenAmbient v) • standardNeckCapWAmbient v

def standardNeckCapCAmbient (v : ChartE3) : ℝ :=
  (1 - ‖standardNeckCapWAmbient v‖ ^ 2) / standardNeckCapDenAmbient v

def standardNeckCapPointAmbient (side : Bool) (v : ChartE3) : ChartE4 :=
  WithLp.toLp 2 (snocR (fun i : Fin 3 => (standardNeckCapUAmbient v).ofLp i)
    (if side then -standardNeckCapCAmbient v else standardNeckCapCAmbient v))

theorem standardNeckCapRadius_sq : standardNeckCapAmbientRadius ^ 2 = 5 / 3 := by
  rw [standardNeckCapAmbientRadius, Real.sq_sqrt (by norm_num)]

theorem standardNeckCapRadius_pos : 0 < standardNeckCapAmbientRadius :=
  Real.sqrt_pos.mpr (by norm_num)

theorem standardNeckCapFun_val_eq_ambient (side : Bool) (v : ThreeBall) :
    (standardNeckCapFun side v).1 = standardNeckCapPointAmbient side (v : ChartE3) := rfl

private theorem standardNeckCapWAmbient_zero : standardNeckCapWAmbient (0 : ChartE3) = 0 := by
  rw [standardNeckCapWAmbient]
  simp

private theorem standardNeckCapDenAmbient_zero : standardNeckCapDenAmbient (0 : ChartE3) = 1 := by
  rw [standardNeckCapDenAmbient, standardNeckCapWAmbient_zero, norm_zero]
  norm_num

private theorem standardNeckCapUAmbient_zero : standardNeckCapUAmbient (0 : ChartE3) = 0 := by
  rw [standardNeckCapUAmbient, standardNeckCapDenAmbient_zero, standardNeckCapWAmbient_zero,
    smul_zero]

private theorem standardNeckCapCAmbient_zero : standardNeckCapCAmbient (0 : ChartE3) = 1 := by
  rw [standardNeckCapCAmbient, standardNeckCapDenAmbient_zero, standardNeckCapWAmbient_zero,
    norm_zero]
  norm_num

theorem standardNeckCapPointAmbient_false_zero :
    standardNeckCapPointAmbient false (0 : ChartE3) =
      EuclideanSpace.single (Fin.last 3) (1 : ℝ) := by
  apply WithLp.ofLp_injective 2
  simp only [standardNeckCapPointAmbient, WithLp.ofLp_toLp, standardNeckCapUAmbient_zero,
    standardNeckCapCAmbient_zero, Bool.false_eq_true, if_false]
  funext i
  fin_cases i <;> simp [snocR, Fin.snoc, Fin.last]

theorem standardNeckCapPointAmbient_true_zero :
    standardNeckCapPointAmbient true (0 : ChartE3) =
      - EuclideanSpace.single (Fin.last 3) (1 : ℝ) := by
  apply WithLp.ofLp_injective 2
  simp only [standardNeckCapPointAmbient, WithLp.ofLp_toLp, standardNeckCapUAmbient_zero,
    standardNeckCapCAmbient_zero, if_true]
  funext i
  fin_cases i <;> simp [snocR, Fin.snoc, Fin.last]

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

private theorem hasFDerivAt_standardNeckCapAmbientNormSq :
    HasFDerivAt (𝕜 := ℝ) (fun v : ChartE3 => ‖v‖ ^ 2) 0 0 := by
  have h : HasFDerivAt (𝕜 := ℝ) (fun v : ChartE3 => ‖v‖ ^ 2)
      (2 • innerSL ℝ (0 : ChartE3)) 0 := (hasFDerivAt_id (0 : ChartE3)).norm_sq
  simpa using h

private theorem standardNeckCapDenAmbient_eq (v : ChartE3) :
    standardNeckCapDenAmbient v = 1 + standardNeckCapAmbientRadius ^ 2 * ‖v‖ ^ 2 := by
  rw [standardNeckCapDenAmbient, standardNeckCapWAmbient, norm_smul,
    show ‖standardNeckCapAmbientRadius‖ = standardNeckCapAmbientRadius from
      Real.norm_of_nonneg (Real.sqrt_nonneg (5 / 3)),
    mul_pow, standardNeckCapRadius_sq]

private def standardNeckCapAmbientS (v : ChartE3) : ℝ :=
  2 * standardNeckCapAmbientRadius / (1 + standardNeckCapAmbientRadius ^ 2 * ‖v‖ ^ 2)

private def standardNeckCapAmbientT (v : ChartE3) : ℝ :=
  (1 - standardNeckCapAmbientRadius ^ 2 * ‖v‖ ^ 2) /
    (1 + standardNeckCapAmbientRadius ^ 2 * ‖v‖ ^ 2)

private def standardNeckCapAmbientLast (side : Bool) (v : ChartE3) : ℝ :=
  if side then -standardNeckCapCAmbient v else standardNeckCapCAmbient v

private def standardNeckCapAmbientComponent (j : Fin 3) (v : ChartE3) : ℝ :=
  standardNeckCapAmbientS v * v.ofLp j

private theorem standardNeckCapUAmbient_eq (v : ChartE3) :
    standardNeckCapUAmbient v = standardNeckCapAmbientS v • v := by
  rw [standardNeckCapUAmbient, standardNeckCapAmbientS, standardNeckCapDenAmbient_eq,
    standardNeckCapWAmbient, smul_smul]
  congr 1
  ring

private theorem standardNeckCapCAmbient_eq (v : ChartE3) :
    standardNeckCapCAmbient v = standardNeckCapAmbientT v := by
  rw [standardNeckCapCAmbient, standardNeckCapAmbientT, standardNeckCapDenAmbient_eq,
    standardNeckCapWAmbient, norm_smul,
    show ‖standardNeckCapAmbientRadius‖ = standardNeckCapAmbientRadius from
      Real.norm_of_nonneg (Real.sqrt_nonneg (5 / 3)),
    mul_pow, standardNeckCapRadius_sq]

private theorem hasFDerivAt_standardNeckCapAmbientDen :
    HasFDerivAt (𝕜 := ℝ)
      (fun v : ChartE3 => 1 + standardNeckCapAmbientRadius ^ 2 * ‖v‖ ^ 2) 0 0 := by
  have h1 : HasFDerivAt (𝕜 := ℝ)
      (fun v : ChartE3 => standardNeckCapAmbientRadius ^ 2 * ‖v‖ ^ 2) 0 0 := by
    simpa using hasFDerivAt_standardNeckCapAmbientNormSq.const_mul
      (standardNeckCapAmbientRadius ^ 2)
  simpa using h1.const_add 1

private theorem hasFDerivAt_standardNeckCapAmbientDenInv :
    HasFDerivAt (𝕜 := ℝ) (fun v : ChartE3 => (standardNeckCapDenAmbient v)⁻¹) 0 0 := by
  have hden : HasFDerivAt (𝕜 := ℝ) standardNeckCapDenAmbient 0 0 := by
    have h := hasFDerivAt_standardNeckCapAmbientDen
    rw [show standardNeckCapDenAmbient =
        fun v : ChartE3 => 1 + standardNeckCapAmbientRadius ^ 2 * ‖v‖ ^ 2 from
      funext standardNeckCapDenAmbient_eq]
    exact h
  have h0 : standardNeckCapDenAmbient (0 : ChartE3) ≠ 0 := by
    rw [standardNeckCapDenAmbient_eq]
    norm_num
  have h := (hasFDerivAt_inv (𝕜 := ℝ) h0).comp (0 : ChartE3) hden
  simpa [Function.comp_def] using h

private theorem hasFDerivAt_standardNeckCapAmbientS :
    HasFDerivAt (𝕜 := ℝ) standardNeckCapAmbientS 0 0 := by
  have h := hasFDerivAt_standardNeckCapAmbientDenInv.const_mul
    (2 * standardNeckCapAmbientRadius)
  have hfun : standardNeckCapAmbientS =
      fun v : ChartE3 => (2 * standardNeckCapAmbientRadius) *
        (standardNeckCapDenAmbient v)⁻¹ := by
    funext v
    rw [standardNeckCapAmbientS, standardNeckCapDenAmbient_eq, div_eq_mul_inv]
  rw [hfun]
  simpa using h

private theorem hasFDerivAt_standardNeckCapAmbientT :
    HasFDerivAt (𝕜 := ℝ) standardNeckCapAmbientT 0 0 := by
  have hnum : HasFDerivAt (𝕜 := ℝ)
      (fun v : ChartE3 => 1 - standardNeckCapAmbientRadius ^ 2 * ‖v‖ ^ 2) 0 0 := by
    have h1 : HasFDerivAt (𝕜 := ℝ)
        (fun v : ChartE3 => standardNeckCapAmbientRadius ^ 2 * ‖v‖ ^ 2) 0 0 := by
      simpa using hasFDerivAt_standardNeckCapAmbientNormSq.const_mul
        (standardNeckCapAmbientRadius ^ 2)
    simpa using h1.const_sub 1
  have hprod := hnum.mul hasFDerivAt_standardNeckCapAmbientDenInv
  have hfun : standardNeckCapAmbientT = fun v : ChartE3 =>
      (1 - standardNeckCapAmbientRadius ^ 2 * ‖v‖ ^ 2) *
        (standardNeckCapDenAmbient v)⁻¹ := by
    funext v
    rw [standardNeckCapAmbientT, standardNeckCapDenAmbient_eq, div_eq_mul_inv]
  rw [show ((fun v : ChartE3 => 1 - standardNeckCapAmbientRadius ^ 2 * ‖v‖ ^ 2) *
      fun v : ChartE3 => (standardNeckCapDenAmbient v)⁻¹) =
      fun v : ChartE3 => (1 - standardNeckCapAmbientRadius ^ 2 * ‖v‖ ^ 2) *
        (standardNeckCapDenAmbient v)⁻¹ from by
    funext v
    rw [Pi.mul_apply]] at hprod
  rw [hfun]
  simpa using hprod

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

attribute [local instance] threeBallChartedSpace threeBall_isManifold

private theorem snocR_eq_lastCases {n : ℕ} (f : Fin n → ℝ) (a : ℝ) :
    snocR f a = Fin.lastCases a f := by
  funext i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · rw [snocR_last, Fin.lastCases_last]
  · rw [snocR_castSucc, Fin.lastCases_castSucc]

private theorem contDiff_standardNeckCapDenTerm :
    ContDiff ℝ ∞ (fun v : ChartE3 => standardNeckCapAmbientRadius ^ 2 * ‖v‖ ^ 2) :=
  contDiff_const.mul (contDiff_id.norm_sq (𝕜 := ℝ))

private theorem contDiff_standardNeckCapDen :
    ContDiff ℝ ∞ (fun v : ChartE3 => 1 + standardNeckCapAmbientRadius ^ 2 * ‖v‖ ^ 2) :=
  contDiff_const.add contDiff_standardNeckCapDenTerm

private theorem standardNeckCapDenNe (v : ChartE3) :
    1 + standardNeckCapAmbientRadius ^ 2 * ‖v‖ ^ 2 ≠ 0 := by positivity

private theorem contDiff_standardNeckCapAmbientS : ContDiff ℝ ∞ standardNeckCapAmbientS :=
  ContDiff.div contDiff_const contDiff_standardNeckCapDen standardNeckCapDenNe

private theorem contDiff_standardNeckCapAmbientT : ContDiff ℝ ∞ standardNeckCapAmbientT :=
  ContDiff.div (contDiff_const.sub contDiff_standardNeckCapDenTerm)
    contDiff_standardNeckCapDen standardNeckCapDenNe

private theorem contDiff_standardNeckCapUAmbient : ContDiff ℝ ∞ standardNeckCapUAmbient := by
  have h : ContDiff ℝ ∞ (standardNeckCapAmbientS • (id : ChartE3 → ChartE3)) :=
    contDiff_standardNeckCapAmbientS.smul contDiff_id
  rwa [show standardNeckCapUAmbient = standardNeckCapAmbientS • (id : ChartE3 → ChartE3) from
    funext fun v => standardNeckCapUAmbient_eq v]

private theorem contDiff_standardNeckCapCAmbient : ContDiff ℝ ∞ standardNeckCapCAmbient := by
  rw [show standardNeckCapCAmbient = standardNeckCapAmbientT from
    funext fun v => standardNeckCapCAmbient_eq v]
  exact contDiff_standardNeckCapAmbientT

private theorem contDiff_standardNeckCapAmbientLast (side : Bool) :
    ContDiff ℝ ∞ (standardNeckCapAmbientLast side) := by
  cases side with
  | false =>
      rw [show standardNeckCapAmbientLast false = standardNeckCapAmbientT from
        funext fun v => by rw [standardNeckCapAmbientLast, standardNeckCapCAmbient_eq]; rfl]
      exact contDiff_standardNeckCapAmbientT
  | true =>
      rw [show standardNeckCapAmbientLast true = -standardNeckCapAmbientT from
        funext fun v => by rw [standardNeckCapAmbientLast, standardNeckCapCAmbient_eq]; rfl]
      exact contDiff_standardNeckCapAmbientT.neg

private def standardNeckCapCoordFun (side : Bool) (v : ChartE3) : Fin 4 → ℝ :=
  snocR (fun i : Fin 3 => (standardNeckCapUAmbient v).ofLp i)
    (if side then -standardNeckCapCAmbient v else standardNeckCapCAmbient v)

private theorem contMDiff_standardNeckCapCoordFun (side : Bool) :
    ContMDiff 𝓘(ℝ, ChartE3) 𝓘(ℝ, (Fin 4 → ℝ)) ∞ (standardNeckCapCoordFun side) := by
  rw [contMDiff_pi_space]
  intro i
  refine Fin.lastCases ?_ ?_ i
  · simp only [standardNeckCapCoordFun, snocR_last]
    exact (contDiff_standardNeckCapAmbientLast side).contMDiff
  · intro j
    simp only [standardNeckCapCoordFun, snocR_castSucc]
    exact ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) j).contMDiff).comp
      contDiff_standardNeckCapUAmbient.contMDiff

theorem contMDiff_standardNeckCapPointAmbient (side : Bool) :
    ContMDiff 𝓘(ℝ, ChartE3) 𝓘(ℝ, ChartE4) ∞ (standardNeckCapPointAmbient side) := by
  have hE : ContMDiff 𝓘(ℝ, ChartE3) 𝓘(ℝ, ChartE4) ∞
      (fun v : ChartE3 => (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin 4)).symm
        (standardNeckCapCoordFun side v)) :=
    ((EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin 4)).symm :
      (Fin 4 → ℝ) →L[ℝ] ChartE4).contMDiff.comp (contMDiff_standardNeckCapCoordFun side)
  refine hE.congr ?_
  intro v
  simp only [EuclideanSpace.equiv, PiLp.continuousLinearEquiv_symm_apply, standardNeckCapCoordFun,
    standardNeckCapPointAmbient, snocR]

def standardNeckCapAmbient (side : Bool) (v : ThreeBall) : ChartE4 :=
  standardNeckCapPointAmbient side (v : ChartE3)

theorem standardNeckCapAmbient_eq (side : Bool) :
    standardNeckCapAmbient side =
      fun v : ThreeBall => ((standardNeckCapFun side v : Sphere 3) : ChartE4) := by
  funext v
  exact (standardNeckCapFun_val_eq_ambient side v).symm

theorem contMDiff_standardNeckCapAmbient (side : Bool) :
    ContMDiff (𝓡∂ 3) 𝓘(ℝ, ChartE4) ∞ (standardNeckCapAmbient side) :=
  (contMDiff_standardNeckCapPointAmbient side).comp
    isSmoothEmbedding_threeBall_inclusion.contMDiff

theorem contMDiff_standardNeckCapFun (side : Bool) :
    ContMDiff (𝓡∂ 3) (𝓡 3) ∞ (standardNeckCapFun side) := by
  have hmem : ∀ v : ThreeBall, standardNeckCapAmbient side v ∈ Sphere 3 := by
    intro v
    rw [standardNeckCapAmbient_eq side]
    exact (standardNeckCapFun side v).2
  have h := (contMDiff_standardNeckCapAmbient side).codRestrict_sphere (n := 3) hmem
  rwa [show Set.codRestrict (standardNeckCapAmbient side) (Sphere 3) hmem =
      standardNeckCapFun side from
    funext fun v => Subtype.ext (standardNeckCapFun_val_eq_ambient side v).symm] at h

theorem mdifferentiableAt_standardNeckCapFun (side : Bool) :
    MDifferentiableAt (𝓡∂ 3) (𝓡 3) (standardNeckCapFun side) 0 :=
  (contMDiff_standardNeckCapFun side).contMDiffAt.mdifferentiableAt (by norm_num)

open private standardNeckCapSum standardNeckCapSum_eq_inl_of standardNeckCapSum_eq_inr_of
  from DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StandardNeckCutCapInstance

abbrev standardNeckBoundaryFalse : standardNeckTubeSystem.Boundary := (PUnit.unit, false)

abbrev standardNeckBoundaryTrue : standardNeckTubeSystem.Boundary := (PUnit.unit, true)

theorem standardNeckCapping_cap_apply_false (v : ThreeBall) :
    standardNeckCapping.cap standardNeckBoundaryFalse v = Sum.inl (standardNeckCapFun false v) := by
  rw [show standardNeckCapping.cap standardNeckBoundaryFalse =
      standardNeckCapSum standardNeckBoundaryFalse from rfl, standardNeckCapSum_eq_inl_of (by simp)]
  rfl

theorem standardNeckCapping_cap_apply_true (v : ThreeBall) :
    standardNeckCapping.cap (PUnit.unit, true) v = Sum.inr (standardNeckCapFun true v) := by
  rw [show standardNeckCapping.cap (PUnit.unit, true) =
      standardNeckCapSum (PUnit.unit, true) from rfl, standardNeckCapSum_eq_inr_of (by simp)]
  rfl

theorem standardNeckCapping_cap_false :
    ⇑(standardNeckCapping.cap standardNeckBoundaryFalse) =
      (Sum.inl : Sphere 3 → Sphere 3 ⊕ Sphere 3) ∘ standardNeckCapFun false :=
  funext standardNeckCapping_cap_apply_false

theorem standardNeckCapping_cap_true :
    ⇑(standardNeckCapping.cap (PUnit.unit, true)) =
      (Sum.inr : Sphere 3 → Sphere 3 ⊕ Sphere 3) ∘ standardNeckCapFun true :=
  funext standardNeckCapping_cap_apply_true

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
