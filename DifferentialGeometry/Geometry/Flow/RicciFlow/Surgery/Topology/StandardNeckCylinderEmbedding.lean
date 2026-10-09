import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StandardNeckCutCap
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorphImmersion
import DifferentialGeometry.Topology.Manifold.ParametrizationDerivative
import DifferentialGeometry.Topology.Manifold.SphereDirection
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingComposition
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingOpenTarget
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

set_option autoImplicit false
noncomputable section

open Bundle Set Function MeasureTheory Filter Manifold
open scoped Manifold ContDiff Topology Interval

open DifferentialGeometry.Topology.Manifold

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

private local instance : Fact ((-2 : ℝ) < 2) := ⟨by norm_num⟩


private abbrev satCylModel := (𝓡 2).prod 𝓘(ℝ)

private abbrev satCylSpace := Sphere 2 × ℝ

private local instance : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) := ⟨by simp⟩

private local instance : Fact (Module.finrank ℝ FourSpace = 3 + 1) := ⟨by simp⟩

private def satCylBase : Sphere 2 :=
  ⟨EuclideanSpace.single (0 : Fin 3) 1, by
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero, PiLp.norm_single]
    norm_num⟩

private def satInitCoord (z : Sphere 3) : ThreeSpace :=
  WithLp.toLp 2 fun i : Fin 3 => (z.1 : FourSpace).ofLp i.castSucc

private def satLastCoord (z : Sphere 3) : ℝ := (z.1 : FourSpace).ofLp (Fin.last 3)

private def satCylPoint (y : Sphere 2) (s : ℝ) : FourSpace :=
  WithLp.toLp 2 (snocR (fun i : Fin 3 => Real.sqrt (1 - s ^ 2) * (y : ThreeSpace).ofLp i) s)

private theorem satCylPoint_lastCoord (y : Sphere 2) (s : ℝ) :
    (satCylPoint y s).ofLp (Fin.last 3) = s := by
  rw [satCylPoint, WithLp.ofLp_toLp, snocR_last]

private theorem satCylPoint_initCoord (y : Sphere 2) (s : ℝ) :
    WithLp.toLp 2 (fun i : Fin 3 => (satCylPoint y s).ofLp i.castSucc) =
      Real.sqrt (1 - s ^ 2) • (y : ThreeSpace) := by
  rw [satCylPoint, WithLp.ofLp_toLp]
  ext i
  rw [WithLp.ofLp_toLp, snocR_castSucc, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]

private theorem satCylPoint_eq_neckPoint (y : Sphere 2) (s : ℝ) :
    satCylPoint y (s / 4) = neckPoint y s :=
  rfl

private theorem satCylPoint_mem_sphere (y : Sphere 2) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    satCylPoint y s ∈ Sphere 3 := by
  rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
  have hsqrt : Real.sqrt (1 - s ^ 2) ^ 2 = 1 - s ^ 2 := Real.sq_sqrt (by linarith)
  have hy : ‖(y : ThreeSpace)‖ = 1 := by
    have h := y.2
    rwa [Metric.mem_sphere, dist_eq_norm, sub_zero] at h
  have h2 : ‖satCylPoint y s‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [satCylPoint, WithLp.ofLp_toLp]
    rw [Fin.sum_univ_castSucc]
    have h1 : (∑ i : Fin 3,
        ‖snocR (fun i : Fin 3 => Real.sqrt (1 - s ^ 2) * (y : ThreeSpace).ofLp i)
          s i.castSucc‖ ^ 2)
        = (Real.sqrt (1 - s ^ 2)) ^ 2 * ∑ i : Fin 3, ‖(y : ThreeSpace).ofLp i‖ ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [snocR_castSucc, norm_mul, mul_pow, Real.norm_eq_abs, sq_abs]
    rw [h1, snocR_last, Real.norm_eq_abs, sq_abs,
      ← EuclideanSpace.norm_sq_eq (y : ThreeSpace), hy, hsqrt]
    ring
  nlinarith [norm_nonneg (satCylPoint y s), h2]

private theorem satLastCoord_val (z : Sphere 3) :
    satLastCoord z = (z.1 : FourSpace).ofLp (Fin.last 3) := rfl

private theorem satInitCoord_val (z : Sphere 3) :
    satInitCoord z = WithLp.toLp 2 (fun i : Fin 3 => (z.1 : FourSpace).ofLp i.castSucc) := rfl

private theorem norm_satInitCoord_sq (z : Sphere 3) :
    ‖satInitCoord z‖ ^ 2 = 1 - satLastCoord z ^ 2 := by
  have h1 : ‖(z.1 : FourSpace)‖ ^ 2 = ∑ i : Fin 4, ((z.1 : FourSpace).ofLp i) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [Real.norm_eq_abs, sq_abs]
  have hz : ∑ i : Fin 4, ((z.1 : FourSpace).ofLp i) ^ 2 = 1 := by
    have hz1 : ‖(z.1 : FourSpace)‖ = 1 := by
      have h := z.2
      rwa [Metric.mem_sphere, dist_eq_norm, sub_zero] at h
    rw [← h1, hz1]
    norm_num
  have h2 : ‖satInitCoord z‖ ^ 2 = ∑ i : Fin 3, ((z.1 : FourSpace).ofLp i.castSucc) ^ 2 := by
    rw [satInitCoord, EuclideanSpace.norm_sq_eq]
    simp [Real.norm_eq_abs, sq_abs]
  have h3 := Fin.sum_univ_castSucc (fun i : Fin 4 => ((z.1 : FourSpace).ofLp i) ^ 2)
  rw [h3] at hz
  rw [h2, satLastCoord_val]
  linarith

private theorem satLastCoord_sq_le_one (z : Sphere 3) : satLastCoord z ^ 2 ≤ 1 := by
  have h := norm_satInitCoord_sq z
  have hnn : (0 : ℝ) ≤ ‖satInitCoord z‖ ^ 2 := sq_nonneg _
  linarith

private def satBand : TopologicalSpace.Opens satCylSpace :=
  ⟨{q : satCylSpace | q.2 ∈ Ioo (-(1 : ℝ)) 1}, isOpen_Ioo.preimage continuous_snd⟩

private theorem satBand_mem_abs {q : ↥satBand} : |(q : satCylSpace).2| < 1 :=
  abs_lt.mpr (Set.mem_Ioo.mp q.property)

private def satCylMap : ↥satBand → Sphere 3 :=
  Set.codRestrict (fun q : ↥satBand => satCylPoint (q : satCylSpace).1 (q : satCylSpace).2) _
    (fun q => satCylPoint_mem_sphere (q : satCylSpace).1
      (by have h := satBand_mem_abs (q := q)
          nlinarith [abs_nonneg (q : satCylSpace).2, sq_abs (q : satCylSpace).2]))

private theorem satCylMap_lastCoord (q : ↥satBand) :
    satLastCoord (satCylMap q) = (q : satCylSpace).2 :=
  satCylPoint_lastCoord _ _

private theorem satCylMap_initCoord (q : ↥satBand) :
    satInitCoord (satCylMap q) =
      Real.sqrt (1 - (q : satCylSpace).2 ^ 2) • ((q : satCylSpace).1 : ThreeSpace) := by
  rw [satInitCoord_val]
  exact satCylPoint_initCoord _ _

private theorem contMDiff_satCylSnd :
    ContMDiff ((𝓡 2).prod 𝓘(ℝ)) 𝓘(ℝ) ∞
      (fun q : ↥satBand => (q : satCylSpace).2) :=
  (contMDiff_snd (I := 𝓡 2) (J := 𝓘(ℝ))).comp contMDiff_subtype_val

private theorem contMDiff_satCylSqrt :
    ContMDiff ((𝓡 2).prod 𝓘(ℝ)) 𝓘(ℝ) ∞
      (fun q : ↥satBand => Real.sqrt (1 - (q : satCylSpace).2 ^ 2)) := by
  intro q
  have hpos : 0 < 1 - (q : satCylSpace).2 ^ 2 := by
    have h := satBand_mem_abs (q := q)
    nlinarith [abs_nonneg (q : satCylSpace).2, sq_abs (q : satCylSpace).2,
      abs_lt.mp h |>.1, abs_lt.mp h |>.2, sq_nonneg (q : satCylSpace).2]
  have hsq : ContMDiffAt 𝓘(ℝ) 𝓘(ℝ) ∞
      (fun s : ℝ => Real.sqrt (1 - s ^ 2)) ((q : satCylSpace).2) :=
    ((contDiffAt_const.sub (contDiffAt_id.pow 2)).sqrt hpos.ne').contMDiffAt
  have hcomp : ContMDiffAt ((𝓡 2).prod 𝓘(ℝ)) 𝓘(ℝ) ∞
      ((fun s : ℝ => Real.sqrt (1 - s ^ 2)) ∘
        (fun q : ↥satBand => (q : satCylSpace).2)) q :=
    ContMDiffAt.comp q hsq (contMDiff_satCylSnd.contMDiffAt)
  exact hcomp

private theorem contMDiff_satCylFstCoord (i : Fin 3) :
    ContMDiff ((𝓡 2).prod 𝓘(ℝ)) 𝓘(ℝ) ∞
      (fun q : ↥satBand => (((q : satCylSpace).1 : ThreeSpace).ofLp i)) :=
  ((EuclideanSpace.proj i).contMDiff).comp <|
    (contMDiff_coe_sphere (n := 2) (E := ThreeSpace)).comp <|
      (contMDiff_fst (I := 𝓡 2) (J := 𝓘(ℝ))).comp contMDiff_subtype_val

private def satCylCoordFun (q : ↥satBand) : Fin 4 → ℝ :=
  snocR (fun i : Fin 3 =>
    Real.sqrt (1 - (q : satCylSpace).2 ^ 2) * (((q : satCylSpace).1 : ThreeSpace).ofLp i))
    ((q : satCylSpace).2)

private theorem contMDiff_satCylCoordFun :
    ContMDiff ((𝓡 2).prod 𝓘(ℝ)) 𝓘(ℝ, Fin 4 → ℝ) ∞ satCylCoordFun := by
  rw [contMDiff_pi_space]
  intro i
  refine Fin.lastCases ?_ ?_ i
  · simp only [satCylCoordFun, snocR_last]
    exact contMDiff_satCylSnd
  · intro j
    simp only [satCylCoordFun, snocR_castSucc]
    exact contMDiff_satCylSqrt.mul (contMDiff_satCylFstCoord j)

private theorem contMDiff_satCylAmbient :
    ContMDiff ((𝓡 2).prod 𝓘(ℝ)) 𝓘(ℝ, FourSpace) ∞
      (fun q : ↥satBand => satCylPoint (q : satCylSpace).1 (q : satCylSpace).2) := by
  have hE : ContMDiff ((𝓡 2).prod 𝓘(ℝ)) 𝓘(ℝ, FourSpace) ∞
      (fun q : ↥satBand => (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin 4)).symm
        (satCylCoordFun q)) :=
    ((EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin 4)).symm :
      (Fin 4 → ℝ) →L[ℝ] FourSpace).contMDiff.comp contMDiff_satCylCoordFun
  refine hE.congr ?_
  intro q
  simp only [EuclideanSpace.equiv, PiLp.continuousLinearEquiv_symm_apply, satCylCoordFun,
    satCylPoint, snocR]

private theorem contMDiff_satCylMap :
    ContMDiff ((𝓡 2).prod 𝓘(ℝ)) ThreeModel ∞ satCylMap := by
  refine (ContMDiff.codRestrict_sphere contMDiff_satCylAmbient
    (fun q => satCylPoint_mem_sphere (q : satCylSpace).1
      (by have h := satBand_mem_abs (q := q)
          nlinarith [abs_nonneg (q : satCylSpace).2, sq_abs (q : satCylSpace).2]))).congr ?_
  intro q
  exact Subtype.ext rfl

private def satBandImage : Set (Sphere 3) :=
  {z : Sphere 3 | satLastCoord z ∈ Ioo (-(1 : ℝ)) 1}

private def satCylDir (z : Sphere 3) : Sphere 2 :=
  sphereDirection satCylBase (satInitCoord z)

private def satCylInverseCore (z : Sphere 3) : satCylSpace :=
  (satCylDir z, satLastCoord z)

private def satCylInverse (z : Sphere 3) : ↥satBand :=
  if h : satLastCoord z ∈ Ioo (-(1 : ℝ)) 1 then
    ⟨satCylInverseCore z, h⟩
  else ⟨(satCylBase, 0), Set.mem_Ioo.mpr ⟨by norm_num, by norm_num⟩⟩

private theorem one_sub_sq_pos_of_mem_domain (q : ↥satBand) :
    0 < 1 - (q : satCylSpace).2 ^ 2 := by
  obtain ⟨h1, h2⟩ := abs_lt.mp (satBand_mem_abs (q := q))
  nlinarith [sq_nonneg ((q : satCylSpace).2)]

private theorem one_sub_sq_pos_of_mem_band {z : Sphere 3} (hz : z ∈ satBandImage) :
    0 < 1 - satLastCoord z ^ 2 := by
  obtain ⟨h1, h2⟩ := hz
  nlinarith [sq_nonneg (satLastCoord z)]

private theorem satInitCoord_ne_zero_of_mem_band {z : Sphere 3} (hz : z ∈ satBandImage) :
    satInitCoord z ≠ 0 := by
  intro h
  have h2 := norm_satInitCoord_sq z
  rw [h, norm_zero] at h2
  have hpos := one_sub_sq_pos_of_mem_band hz
  linarith

private theorem contMDiff_satInitCoord :
    ContMDiff ThreeModel 𝓘(ℝ, ThreeSpace) ∞ satInitCoord := by
  have hE : ContMDiff ThreeModel 𝓘(ℝ, ThreeSpace) ∞
      (fun z : Sphere 3 => (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin 3)).symm
        (fun i : Fin 3 => (z.1 : FourSpace).ofLp i.castSucc)) :=
    ((EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin 3)).symm :
      (Fin 3 → ℝ) →L[ℝ] ThreeSpace).contMDiff.comp <|
      contMDiff_pi_space.mpr fun i =>
        ((EuclideanSpace.proj i.castSucc).contMDiff).comp
          (contMDiff_coe_sphere (n := 3) (E := FourSpace))
  refine hE.congr ?_
  intro z
  simp only [EuclideanSpace.equiv, PiLp.continuousLinearEquiv_symm_apply, satInitCoord]

private theorem contMDiff_satLastCoord : ContMDiff ThreeModel 𝓘(ℝ) ∞ satLastCoord :=
  ((EuclideanSpace.proj (Fin.last 3)).contMDiff).comp
    (contMDiff_coe_sphere (n := 3) (E := FourSpace))

private theorem contMDiffOn_satCylInverseCore :
    ContMDiffOn ThreeModel ((𝓡 2).prod 𝓘(ℝ)) ∞ satCylInverseCore satBandImage := by
  have hdir : ContMDiffOn ThreeModel (𝓡 2) ∞ satCylDir satBandImage :=
    (contMDiffOn_sphereDirection satCylBase).comp contMDiff_satInitCoord.contMDiffOn
      (fun z hz => satInitCoord_ne_zero_of_mem_band hz)
  exact hdir.prodMk contMDiff_satLastCoord.contMDiffOn

private theorem satCylInverseCore_apply_of_mem_band {z : Sphere 3} (hz : z ∈ satBandImage) :
    satCylInverse z = ⟨satCylInverseCore z, hz⟩ := dite_eq_left hz

private theorem satCylDir_map (q : ↥satBand) :
    satCylDir (satCylMap q) = (q : satCylSpace).1 := by
  rw [satCylDir, satCylMap_initCoord]
  exact sphereDirection_pos_smul satCylBase (q : satCylSpace).1
    (Real.sqrt_pos.mpr (one_sub_sq_pos_of_mem_domain q))

private theorem satCylInverse_map (q : ↥satBand) :
    satCylInverse (satCylMap q) = q := by
  have hband : satCylMap q ∈ satBandImage := by
    change satLastCoord (satCylMap q) ∈ Ioo (-(1 : ℝ)) 1
    rw [satCylMap_lastCoord]
    exact q.property
  rw [satCylInverseCore_apply_of_mem_band hband]
  apply Subtype.ext
  exact Prod.ext (satCylDir_map q) (satCylMap_lastCoord q)

private def satCylPartialEquiv : PartialEquiv ↥satBand (Sphere 3) where
  toFun := satCylMap
  invFun := satCylInverse
  source := univ
  target := range satCylMap
  map_source' := fun x _ => mem_range_self x
  map_target' := fun _ _ => mem_univ _
  left_inv' := fun x _ => satCylInverse_map x
  right_inv' := fun z hz => by
    obtain ⟨x, rfl⟩ := hz
    rw [satCylInverse_map]

private theorem contMDiffOn_satCylInverse :
    ContMDiffOn ThreeModel ((𝓡 2).prod 𝓘(ℝ)) ∞ satCylInverse (range satCylMap) := by
  have hsub : range satCylMap ⊆ satBandImage := by
    rintro z ⟨x, rfl⟩
    change satLastCoord (satCylMap x) ∈ Ioo (-(1 : ℝ)) 1
    rw [satCylMap_lastCoord]
    exact x.property
  have hval : ContMDiffOn ThreeModel ((𝓡 2).prod 𝓘(ℝ)) ∞
      (fun z : Sphere 3 => (satCylInverse z : satCylSpace)) (range satCylMap) :=
    ((contMDiffOn_satCylInverseCore.mono hsub).congr fun z hz =>
      congrArg Subtype.val (satCylInverseCore_apply_of_mem_band (hsub hz)))
  intro z hz
  exact (ContMDiffWithinAt.subtypeVal_comp_iff satBand satCylInverse _ z).mp (hval z hz)

private theorem satCylMap_injective : Function.Injective satCylMap := by
  intro p q hpq
  have hlast : (p : satCylSpace).2 = (q : satCylSpace).2 := by
    rw [← satCylMap_lastCoord p, ← satCylMap_lastCoord q, hpq]
  have hinit : Real.sqrt (1 - (p : satCylSpace).2 ^ 2) • ((p : satCylSpace).1 : ThreeSpace) =
      Real.sqrt (1 - (q : satCylSpace).2 ^ 2) • ((q : satCylSpace).1 : ThreeSpace) := by
    rw [← satCylMap_initCoord p, ← satCylMap_initCoord q, hpq]
  have hfst : ((p : satCylSpace).1 : ThreeSpace) = ((q : satCylSpace).1 : ThreeSpace) := by
    have hpos := Real.sqrt_pos.mpr (one_sub_sq_pos_of_mem_domain p)
    have h2 : Real.sqrt (1 - (p : satCylSpace).2 ^ 2) • ((p : satCylSpace).1 : ThreeSpace) =
        Real.sqrt (1 - (p : satCylSpace).2 ^ 2) • ((q : satCylSpace).1 : ThreeSpace) := by
      rw [hinit, hlast]
    have h3 := congrArg (fun w : ThreeSpace =>
      (Real.sqrt (1 - (p : satCylSpace).2 ^ 2))⁻¹ • w) h2
    simpa [smul_smul, inv_mul_cancel₀ (ne_of_gt hpos)] using h3
  exact Subtype.ext (Prod.ext (Subtype.ext hfst) hlast)

private theorem isSmoothEmbedding_satCylMap :
    IsSmoothEmbedding ((𝓡 2).prod 𝓘(ℝ)) ThreeModel ∞ satCylMap := by
  obtain ⟨-, hinj⟩ := isEmbedding_and_injective_mfderiv_of_smooth_partialEquiv
    satCylPartialEquiv rfl contMDiff_satCylMap contMDiffOn_satCylInverse
  refine isSmoothEmbedding_of_injective_mfderiv contMDiff_satCylMap satCylMap_injective hinj ?_
  simp [Module.finrank_prod]

private def satRate (u : ℝ) : ℝ := (1 / 2) * Real.exp (-(8 * u * expNegInvGlue u))

private def satMass (s : ℝ) : ℝ := ∫ x in (0)..s, satRate x

private def satPrimitive (s : ℝ) : ℝ := ∫ x in (0)..s, (satRate x - 1 / 2)

private def satBound : ℝ := 1 / 2 + Real.exp (-2) / 4

private def cylinderHeight (t : ℝ) : ℝ :=
  t / 4 + (satPrimitive (t - 2) - satPrimitive (-t - 2)) / 2

private theorem contDiff_satRate : ContDiff ℝ ∞ satRate := by
  unfold satRate
  fun_prop

private theorem satRate_pos (u : ℝ) : 0 < satRate u := by
  unfold satRate
  positivity

private theorem satRate_nonneg (u : ℝ) : 0 ≤ satRate u := (satRate_pos u).le

private theorem satRate_le_half (u : ℝ) : satRate u ≤ 1 / 2 := by
  have h1 : (0 : ℝ) ≤ 8 * u * expNegInvGlue u := by
    rcases le_or_gt 0 u with hu | hu
    · have := expNegInvGlue.nonneg u; nlinarith
    · rw [expNegInvGlue.zero_of_nonpos hu.le]; norm_num
  have h2 : Real.exp (-(8 * u * expNegInvGlue u)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; linarith
  unfold satRate
  linarith

private theorem satRate_of_nonpos {u : ℝ} (hu : u ≤ 0) : satRate u = 1 / 2 := by
  unfold satRate
  rw [expNegInvGlue.zero_of_nonpos hu, mul_zero, neg_zero, Real.exp_zero, mul_one]

private theorem contDiff_satMass : ContDiff ℝ ∞ satMass := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨intervalIntegral.differentiable_integral_of_continuous
    contDiff_satRate.continuous, ?_⟩
  have h : deriv satMass = satRate := by
    funext s
    exact Continuous.deriv_integral satRate contDiff_satRate.continuous 0 s
  rw [h]
  exact contDiff_satRate

private theorem satMass_nonneg {s : ℝ} (hs : 0 ≤ s) : 0 ≤ satMass s :=
  intervalIntegral.integral_nonneg hs fun u _ => satRate_nonneg u

private theorem satMass_nonpos {s : ℝ} (hs : s ≤ 0) : satMass s ≤ 0 := by
  rw [satMass, intervalIntegral.integral_symm (μ := volume) (f := satRate) s 0]
  exact neg_nonpos.mpr (intervalIntegral.integral_nonneg hs fun u _ => satRate_nonneg u)

private theorem expNegInvGlue_ge_quarter {x : ℝ} (hx : 1 ≤ x) :
    (1 / 4 : ℝ) ≤ expNegInvGlue x := by
  have h1 : expNegInvGlue 1 ≤ expNegInvGlue x := expNegInvGlue.monotone hx
  have h2 : expNegInvGlue 1 = Real.exp (-1) := by
    rw [expNegInvGlue, ite_eq_right (by norm_num : ¬ (1 : ℝ) ≤ 0), inv_one]
  have h3 : (1 / 4 : ℝ) ≤ Real.exp (-1) := by
    have h4 : (1 / 4 : ℝ) = (4 : ℝ)⁻¹ := by norm_num
    rw [h4, Real.exp_neg]
    exact (inv_le_inv₀ (by norm_num : (0 : ℝ) < 4) (Real.exp_pos 1)).mpr
      (Real.exp_one_lt_three.trans (by norm_num : (3 : ℝ) < 4)).le
  rw [h2] at h1
  exact h3.trans h1

private theorem satRate_le_exp {x : ℝ} (hx : 1 ≤ x) :
    satRate x ≤ (1 / 2) * Real.exp (-2 * x) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hη : (1 / 4 : ℝ) ≤ expNegInvGlue x := expNegInvGlue_ge_quarter hx
  have hmono : Real.exp (-(8 * x * expNegInvGlue x)) ≤ Real.exp (-2 * x) := by
    apply Real.exp_le_exp.mpr
    have hxη : x * (1 / 4) ≤ x * expNegInvGlue x := mul_le_mul_of_nonneg_left hη hx0.le
    nlinarith
  unfold satRate
  linarith

private theorem integral_exp_neg_two (s : ℝ) :
    ∫ x in (1)..s, (1 / 2 : ℝ) * Real.exp (-2 * x) =
      (1 / 4) * (Real.exp (-2) - Real.exp (-2 * s)) := by
  rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_comp_mul_left (a := 1) (b := s) (c := (-2 : ℝ)) Real.exp
    (by norm_num : (-2 : ℝ) ≠ 0)]
  rw [integral_exp]
  norm_num
  ring

private theorem satMass_le_satBound (s : ℝ) : satMass s ≤ satBound := by
  have hb : (0 : ℝ) ≤ Real.exp (-2) := (Real.exp_pos (-2)).le
  rcases le_or_gt s 1 with hs | hs
  · rcases le_or_gt s 0 with hs0 | hs0
    · have h := satMass_nonpos hs0
      unfold satBound
      linarith
    · have h1 : satMass s ≤ ∫ x in (0)..s, (1 / 2 : ℝ) ∂volume :=
        intervalIntegral.integral_mono_on hs0.le
          (contDiff_satRate.continuous.intervalIntegrable 0 s)
          (intervalIntegrable_const (μ := volume) (c := (1 / 2 : ℝ)))
          fun x _ => satRate_le_half x
      have h2 : ∫ x in (0)..s, (1 / 2 : ℝ) ∂volume = s / 2 := by
        rw [intervalIntegral.integral_const]; simp [smul_eq_mul, div_eq_mul_inv]
      unfold satBound
      linarith
  · have hsplit : satMass s =
        ∫ x in (0)..1, satRate x ∂volume + ∫ x in (1)..s, satRate x ∂volume := by
      rw [satMass, ← intervalIntegral.integral_add_adjacent_intervals (μ := volume)
        (contDiff_satRate.continuous.intervalIntegrable 0 1)
        (contDiff_satRate.continuous.intervalIntegrable 1 s)]
    have h1 : ∫ x in (0)..1, satRate x ∂volume ≤ 1 / 2 := by
      have hmono := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
        (contDiff_satRate.continuous.intervalIntegrable 0 1)
        (intervalIntegrable_const (μ := volume) (c := (1 / 2 : ℝ)))
        (fun x _ => satRate_le_half x)
      have hconst : ∫ x in (0)..1, (1 / 2 : ℝ) ∂volume = 1 / 2 := by
        rw [intervalIntegral.integral_const]; simp
      linarith
    have hcont : Continuous fun x : ℝ => (1 / 2 : ℝ) * Real.exp (-2 * x) :=
      continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))
    have h2 : ∫ x in (1)..s, satRate x ∂volume ≤ Real.exp (-2) / 4 := by
      have hmono : ∫ x in (1)..s, satRate x ∂volume ≤
          ∫ x in (1)..s, (1 / 2 : ℝ) * Real.exp (-2 * x) ∂volume :=
        intervalIntegral.integral_mono_on hs.le
          (contDiff_satRate.continuous.intervalIntegrable 1 s) (hcont.intervalIntegrable 1 s)
          (fun x hx => satRate_le_exp hx.1)
      rw [integral_exp_neg_two s] at hmono
      have : (0 : ℝ) ≤ Real.exp (-2 * s) := (Real.exp_pos _).le
      linarith
    rw [hsplit]
    unfold satBound
    linarith

private theorem satBound_lt_one : satBound < 1 := by
  have h : Real.exp (-2) ≤ 1 := by rw [Real.exp_le_one_iff]; norm_num
  unfold satBound
  linarith

private theorem contDiff_satPrimitive : ContDiff ℝ ∞ satPrimitive := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨intervalIntegral.differentiable_integral_of_continuous ?_, ?_⟩
  · exact contDiff_satRate.continuous.sub continuous_const
  · have h : deriv satPrimitive = fun s => satRate s - 1 / 2 := by
      funext s
      exact Continuous.deriv_integral (fun x => satRate x - 1 / 2)
        (contDiff_satRate.continuous.sub continuous_const) 0 s
    rw [h]
    exact contDiff_satRate.sub contDiff_const

private theorem satPrimitive_zero_of_nonpos {s : ℝ} (hs : s ≤ 0) : satPrimitive s = 0 := by
  have hcongr : ∫ x in (0)..s, (satRate x - 1 / 2) = ∫ x in (0)..s, (0 : ℝ) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_ge hs] at hx
    change satRate x - 1 / 2 = 0
    rw [satRate_of_nonpos hx.2]
    ring
  rw [satPrimitive, hcongr, intervalIntegral.integral_zero]

private theorem satPrimitive_eq (s : ℝ) : satPrimitive s = satMass s - s / 2 := by
  rw [satPrimitive, satMass, intervalIntegral.integral_sub
    (contDiff_satRate.continuous.intervalIntegrable 0 s)
    (intervalIntegrable_const (μ := volume) (c := (1 / 2 : ℝ))),
    intervalIntegral.integral_const]
  simp [smul_eq_mul, div_eq_mul_inv]

private theorem contDiff_cylinderHeight : ContDiff ℝ ∞ cylinderHeight := by
  have h1 : ContDiff ℝ ∞ fun t : ℝ => satPrimitive (t - 2) :=
    contDiff_satPrimitive.comp (contDiff_id.sub contDiff_const)
  have h2 : ContDiff ℝ ∞ fun t : ℝ => satPrimitive (-t - 2) :=
    contDiff_satPrimitive.comp ((contDiff_id.neg.sub contDiff_const))
  have h3 : ContDiff ℝ ∞ fun t : ℝ => t / 4 :=
    (contDiff_id (𝕜 := ℝ) (n := ∞)).div_const 4
  have h4 : ContDiff ℝ ∞ fun t : ℝ =>
      (satPrimitive (t - 2) - satPrimitive (-t - 2)) / 2 := (h1.sub h2).div_const 2
  have h5 : cylinderHeight = fun t : ℝ =>
      t / 4 + (satPrimitive (t - 2) - satPrimitive (-t - 2)) / 2 := rfl
  rw [h5]
  exact h3.add h4

private theorem hasDerivAt_satPrimitive (s : ℝ) :
    HasDerivAt satPrimitive (satRate s - 1 / 2) s := by
  have h : HasDerivAt satPrimitive (deriv satPrimitive s) s :=
    (Differentiable.differentiableAt (contDiff_satPrimitive.differentiable (by simp))
      (x := s)).hasDerivAt
  rwa [show deriv satPrimitive s = satRate s - 1 / 2 from
    Continuous.deriv_integral (fun x => satRate x - 1 / 2)
      (contDiff_satRate.continuous.sub continuous_const) 0 s] at h

private theorem deriv_cylinderHeight (t : ℝ) :
    deriv cylinderHeight t = (satRate (t - 2) + satRate (-t - 2)) / 2 - 1 / 4 := by
  have h1 : HasDerivAt (fun s : ℝ => satPrimitive (s - 2)) (satRate (t - 2) - 1 / 2) t := by
    have h := (hasDerivAt_satPrimitive (t - 2)).comp t ((hasDerivAt_id t).sub_const 2)
    simpa only [Function.comp_def, id_eq, mul_one] using h
  have h2 : HasDerivAt (fun s : ℝ => satPrimitive (-s - 2))
      (-(satRate (-t - 2) - 1 / 2)) t := by
    have h := (hasDerivAt_satPrimitive (-t - 2)).comp t ((hasDerivAt_id t).neg.sub_const 2)
    simpa only [Function.comp_def, id_eq, Pi.neg_apply, mul_neg, mul_one] using h
  have h3 : HasDerivAt (fun s : ℝ =>
      s / 4 + (satPrimitive (s - 2) - satPrimitive (-s - 2)) / 2)
      (1 / 4 + ((satRate (t - 2) - 1 / 2) - (-(satRate (-t - 2) - 1 / 2))) / 2) t :=
    ((hasDerivAt_id t).div_const 4).add ((h1.sub h2).div_const 2)
  have h4 : cylinderHeight = fun s : ℝ =>
      s / 4 + (satPrimitive (s - 2) - satPrimitive (-s - 2)) / 2 := rfl
  rw [h4, h3.deriv]
  ring

private theorem deriv_cylinderHeight_pos (t : ℝ) : 0 < deriv cylinderHeight t := by
  rw [deriv_cylinderHeight]
  rcases le_or_gt 2 t with ht | ht
  · have h : satRate (-t - 2) = 1 / 2 := satRate_of_nonpos (by linarith)
    rw [h]
    have := satRate_pos (t - 2)
    linarith
  · rcases le_or_gt t (-2) with ht' | ht'
    · have h : satRate (t - 2) = 1 / 2 := satRate_of_nonpos (by linarith)
      rw [h]
      have := satRate_pos (-t - 2)
      linarith
    · have h1 : satRate (t - 2) = 1 / 2 := satRate_of_nonpos (by linarith)
      have h2 : satRate (-t - 2) = 1 / 2 := satRate_of_nonpos (by linarith)
      rw [h1, h2]
      norm_num

private theorem strictMono_cylinderHeight : StrictMono cylinderHeight :=
  strictMono_of_deriv_pos deriv_cylinderHeight_pos

private theorem cylinderHeight_of_le_neg_two {t : ℝ} (ht : t ≤ -2) :
    cylinderHeight t = -1 / 2 - satMass (-t - 2) / 2 := by
  rw [cylinderHeight, satPrimitive_zero_of_nonpos (by linarith : t - 2 ≤ 0),
    satPrimitive_eq (-t - 2)]
  ring

private theorem cylinderHeight_of_two_le {t : ℝ} (ht : 2 ≤ t) :
    cylinderHeight t = 1 / 2 + satMass (t - 2) / 2 := by
  rw [cylinderHeight, satPrimitive_eq (t - 2),
    satPrimitive_zero_of_nonpos (by linarith : -t - 2 ≤ 0)]
  ring

private theorem cylinderHeight_of_mem_Icc {t : ℝ} (ht : t ∈ Icc (-2 : ℝ) 2) :
    cylinderHeight t = t / 4 := by
  rw [cylinderHeight, satPrimitive_zero_of_nonpos (by linarith [ht.2] : t - 2 ≤ 0),
    satPrimitive_zero_of_nonpos (by linarith [ht.1] : -t - 2 ≤ 0)]
  ring

private theorem abs_cylinderHeight_lt_one (t : ℝ) : |cylinderHeight t| < 1 := by
  rcases le_or_gt 2 t with ht | ht
  · rw [cylinderHeight_of_two_le ht, abs_lt]
    have h1 : 0 ≤ satMass (t - 2) := satMass_nonneg (by linarith)
    have h2 : satMass (t - 2) ≤ satBound := satMass_le_satBound _
    have h3 : satBound < 1 := satBound_lt_one
    constructor <;> linarith
  · rcases le_or_gt t (-2) with ht' | ht'
    · rw [cylinderHeight_of_le_neg_two ht', abs_lt]
      have h1 : 0 ≤ satMass (-t - 2) := satMass_nonneg (by linarith)
      have h2 : satMass (-t - 2) ≤ satBound := satMass_le_satBound _
      have h3 : satBound < 1 := satBound_lt_one
      constructor <;> linarith
    · rw [cylinderHeight_of_mem_Icc ⟨ht'.le, ht.le⟩, abs_div,
        abs_of_pos (by norm_num : (0 : ℝ) < 4)]
      have : |t| < 2 := abs_lt.mpr ⟨ht', ht⟩
      linarith

private theorem isSmoothEmbedding_cylinderHeight :
    IsSmoothEmbedding 𝓘(ℝ) 𝓘(ℝ) ∞ cylinderHeight := by
  refine DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_of_injective_mfderiv
    contDiff_cylinderHeight.contMDiff strictMono_cylinderHeight.injective ?_ ?_
  · intro x
    rw [mfderiv_eq_fderiv]
    change Function.Injective (fderiv ℝ cylinderHeight x : ℝ →L[ℝ] ℝ)
    intro u v huv
    have h0 : (u - v) • deriv cylinderHeight x = 0 := by
      rw [← fderiv_eq_smul_deriv, map_sub, huv, sub_self]
    have h1 : (u - v) = 0 := by
      rcases smul_eq_zero.mp h0 with h | h
      · exact h
      · exact absurd h (ne_of_gt (deriv_cylinderHeight_pos x))
    linarith
  · simp


private theorem abs_satCylPoint_param (p : Sphere 2 × ℝ) : |cylinderHeight p.2| < 1 :=
  abs_cylinderHeight_lt_one p.2

private theorem sq_satCylPoint_param (p : Sphere 2 × ℝ) : cylinderHeight p.2 ^ 2 ≤ 1 := by
  have h := abs_cylinderHeight_lt_one p.2
  nlinarith [abs_nonneg (cylinderHeight p.2), sq_abs (cylinderHeight p.2)]

private def satBandPoint (p : Sphere 2 × ℝ) : ↥satBand :=
  ⟨(p.1, cylinderHeight p.2), by
    change cylinderHeight p.2 ∈ Ioo (-(1 : ℝ)) 1
    exact (abs_lt.mp (abs_cylinderHeight_lt_one p.2))⟩

private theorem isSmoothEmbedding_satBandPoint :
    IsSmoothEmbedding ((𝓡 2).prod 𝓘(ℝ)) ((𝓡 2).prod 𝓘(ℝ)) ∞ satBandPoint := by
  refine DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_intoOpen
    ((𝓡 2).prod 𝓘(ℝ)) ((𝓡 2).prod 𝓘(ℝ)) satBand satBandPoint ?_
  have hprod : IsSmoothEmbedding ((𝓡 2).prod 𝓘(ℝ)) ((𝓡 2).prod 𝓘(ℝ)) ∞
      (Prod.map (id : Sphere 2 → Sphere 2) cylinderHeight) :=
    IsSmoothEmbedding.prodMap IsSmoothEmbedding.id isSmoothEmbedding_cylinderHeight
  convert hprod using 1
  funext p
  rfl

private def cylinderExtensionMap (p : Sphere 2 × ℝ) : Sphere 3 :=
  satCylMap (satBandPoint p)

private theorem isSmoothEmbedding_cylinderExtensionMap :
    IsSmoothEmbedding ((𝓡 2).prod 𝓘(ℝ)) ThreeModel ∞ cylinderExtensionMap :=
  IsSmoothEmbedding.comp (I := (𝓡 2).prod 𝓘(ℝ)) (J := (𝓡 2).prod 𝓘(ℝ))
    (J' := ThreeModel) (f := satBandPoint) (g := satCylMap)
    isSmoothEmbedding_satCylMap isSmoothEmbedding_satBandPoint (by decide)

private theorem cylinderExtensionMap_apply_tube (z : TubeDomain) :
    cylinderExtensionMap (z.1, (z.2 : ℝ)) = standardNeckTubeFun z := by
  apply Subtype.ext
  change satCylPoint z.1 (cylinderHeight (z.2 : ℝ)) = neckPoint z.1 (z.2 : ℝ)
  rw [cylinderHeight_of_mem_Icc z.2.2]
  exact satCylPoint_eq_neckPoint z.1 (z.2 : ℝ)

theorem standardNeckCutCapInputs_cylinderEmbedding :
    ∃ g : Sphere 2 × ℝ → Sphere 3,
      IsSmoothEmbedding ((𝓡 2).prod 𝓘(ℝ)) ThreeModel ∞ g ∧
        ∀ z : TubeDomain, g (z.1, (z.2 : ℝ)) = standardNeckTubeFun z :=
  ⟨cylinderExtensionMap, isSmoothEmbedding_cylinderExtensionMap,
    fun z => cylinderExtensionMap_apply_tube z⟩


end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
