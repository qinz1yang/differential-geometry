import DifferentialGeometry.Topology.ThreeManifold.Surgery.SphereModel.Capping
import DifferentialGeometry.Topology.Manifold.ClosedBall.ThreeBall
import Mathlib.Geometry.Manifold.Instances.Real

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Metric Module
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

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
    standardNeckCapCAmbient_zero, Bool.false_eq_true, ite_false]
  funext i
  fin_cases i <;> simp [snocR, Fin.snoc, Fin.last]

theorem standardNeckCapPointAmbient_true_zero :
    standardNeckCapPointAmbient true (0 : ChartE3) =
      - EuclideanSpace.single (Fin.last 3) (1 : ℝ) := by
  apply WithLp.ofLp_injective 2
  simp only [standardNeckCapPointAmbient, WithLp.ofLp_toLp, standardNeckCapUAmbient_zero,
    standardNeckCapCAmbient_zero, ite_true]
  funext i
  fin_cases i <;> simp [snocR, Fin.snoc, Fin.last]

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

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
