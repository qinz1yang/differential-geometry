import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StandardNeckRegularity
import DifferentialGeometry.Topology.Manifold.OpenSphereCylinder
import DifferentialGeometry.Topology.Manifold.ParametrizationDerivative
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorphImmersion
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingFromOpen

set_option autoImplicit false
noncomputable section

open Bundle Manifold Set Function
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Topology.Manifold

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

private abbrev NeckFour := EuclideanSpace ℝ (Fin 4)

private abbrev CylModel := (𝓡 2).prod 𝓘(ℝ)

private abbrev CylSpace := Sphere 2 × ℝ

private local instance : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) := ⟨by simp⟩

private local instance : Fact (Module.finrank ℝ NeckFour = 3 + 1) := ⟨by simp⟩

private def neckCylBase : Sphere 2 :=
  ⟨EuclideanSpace.single (0 : Fin 3) 1, by
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero, PiLp.norm_single]
    norm_num⟩

private def neckInitCoord (z : Sphere 3) : ThreeSpace :=
  WithLp.toLp 2 fun i : Fin 3 => (z.1 : NeckFour).ofLp i.castSucc

private def neckLastCoord (z : Sphere 3) : ℝ := (z.1 : NeckFour).ofLp (Fin.last 3)

private def neckCylPoint (y : Sphere 2) (s : ℝ) : NeckFour :=
  WithLp.toLp 2 (snocR (fun i : Fin 3 => Real.sqrt (1 - s ^ 2) * (y : ThreeSpace).ofLp i) s)

private theorem neckCylPoint_lastCoord (y : Sphere 2) (s : ℝ) :
    (neckCylPoint y s).ofLp (Fin.last 3) = s := by
  rw [neckCylPoint, WithLp.ofLp_toLp, snocR_last]

private theorem neckCylPoint_initCoord (y : Sphere 2) (s : ℝ) :
    WithLp.toLp 2 (fun i : Fin 3 => (neckCylPoint y s).ofLp i.castSucc) =
      Real.sqrt (1 - s ^ 2) • (y : ThreeSpace) := by
  rw [neckCylPoint, WithLp.ofLp_toLp]
  ext i
  rw [WithLp.ofLp_toLp, snocR_castSucc, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]

private theorem neckCylPoint_eq_neckPoint (y : Sphere 2) (s : ℝ) :
    neckCylPoint y (s / 4) = neckPoint y s :=
  rfl

private theorem neckCylPoint_mem_sphere (y : Sphere 2) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    neckCylPoint y s ∈ Sphere 3 := by
  rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
  have hsqrt : Real.sqrt (1 - s ^ 2) ^ 2 = 1 - s ^ 2 := Real.sq_sqrt (by linarith)
  have hy : ‖(y : ThreeSpace)‖ = 1 := by
    have h := y.2
    rwa [Metric.mem_sphere, dist_eq_norm, sub_zero] at h
  have h2 : ‖neckCylPoint y s‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [neckCylPoint, WithLp.ofLp_toLp]
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
  nlinarith [norm_nonneg (neckCylPoint y s), h2]

private theorem neckLastCoord_val (z : Sphere 3) :
    neckLastCoord z = (z.1 : NeckFour).ofLp (Fin.last 3) := rfl

private theorem neckInitCoord_val (z : Sphere 3) :
    neckInitCoord z = WithLp.toLp 2 (fun i : Fin 3 => (z.1 : NeckFour).ofLp i.castSucc) := rfl

private theorem norm_neckInitCoord_sq (z : Sphere 3) :
    ‖neckInitCoord z‖ ^ 2 = 1 - neckLastCoord z ^ 2 := by
  have h1 : ‖(z.1 : NeckFour)‖ ^ 2 = ∑ i : Fin 4, ((z.1 : NeckFour).ofLp i) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [Real.norm_eq_abs, sq_abs]
  have hz : ∑ i : Fin 4, ((z.1 : NeckFour).ofLp i) ^ 2 = 1 := by
    have hz1 : ‖(z.1 : NeckFour)‖ = 1 := by
      have h := z.2
      rwa [Metric.mem_sphere, dist_eq_norm, sub_zero] at h
    rw [← h1, hz1]
    norm_num
  have h2 : ‖neckInitCoord z‖ ^ 2 = ∑ i : Fin 3, ((z.1 : NeckFour).ofLp i.castSucc) ^ 2 := by
    rw [neckInitCoord, EuclideanSpace.norm_sq_eq]
    simp [Real.norm_eq_abs, sq_abs]
  have h3 := Fin.sum_univ_castSucc (fun i : Fin 4 => ((z.1 : NeckFour).ofLp i) ^ 2)
  rw [h3] at hz
  rw [h2, neckLastCoord_val]
  linarith

private theorem neckLastCoord_sq_le_one (z : Sphere 3) : neckLastCoord z ^ 2 ≤ 1 := by
  have h := norm_neckInitCoord_sq z
  have hnn : (0 : ℝ) ≤ ‖neckInitCoord z‖ ^ 2 := sq_nonneg _
  linarith

private def neckCylDomain : TopologicalSpace.Opens CylSpace :=
  ⟨{q : CylSpace | q.2 ∈ Ioo (-(1 : ℝ)) 1}, isOpen_Ioo.preimage continuous_snd⟩

private theorem neckCylDomain_mem_abs {q : ↥neckCylDomain} : |(q : CylSpace).2| < 1 :=
  abs_lt.mpr (Set.mem_Ioo.mp q.property)

private def neckCylMap : ↥neckCylDomain → Sphere 3 :=
  Set.codRestrict (fun q : ↥neckCylDomain => neckCylPoint (q : CylSpace).1 (q : CylSpace).2) _
    (fun q => neckCylPoint_mem_sphere (q : CylSpace).1
      (by have h := neckCylDomain_mem_abs (q := q)
          nlinarith [abs_nonneg (q : CylSpace).2, sq_abs (q : CylSpace).2]))

private theorem neckCylMap_lastCoord (q : ↥neckCylDomain) :
    neckLastCoord (neckCylMap q) = (q : CylSpace).2 :=
  neckCylPoint_lastCoord _ _

private theorem neckCylMap_initCoord (q : ↥neckCylDomain) :
    neckInitCoord (neckCylMap q) =
      Real.sqrt (1 - (q : CylSpace).2 ^ 2) • ((q : CylSpace).1 : ThreeSpace) := by
  rw [neckInitCoord_val]
  exact neckCylPoint_initCoord _ _

private theorem contMDiff_neckCylSnd :
    ContMDiff ((𝓡 2).prod 𝓘(ℝ)) 𝓘(ℝ) ∞
      (fun q : ↥neckCylDomain => (q : CylSpace).2) :=
  (contMDiff_snd (I := 𝓡 2) (J := 𝓘(ℝ))).comp contMDiff_subtype_val

private theorem contMDiff_neckCylSqrt :
    ContMDiff ((𝓡 2).prod 𝓘(ℝ)) 𝓘(ℝ) ∞
      (fun q : ↥neckCylDomain => Real.sqrt (1 - (q : CylSpace).2 ^ 2)) := by
  intro q
  have hpos : 0 < 1 - (q : CylSpace).2 ^ 2 := by
    have h := neckCylDomain_mem_abs (q := q)
    nlinarith [abs_nonneg (q : CylSpace).2, sq_abs (q : CylSpace).2,
      abs_lt.mp h |>.1, abs_lt.mp h |>.2, sq_nonneg (q : CylSpace).2]
  have hsq : ContMDiffAt 𝓘(ℝ) 𝓘(ℝ) ∞
      (fun s : ℝ => Real.sqrt (1 - s ^ 2)) ((q : CylSpace).2) :=
    ((contDiffAt_const.sub (contDiffAt_id.pow 2)).sqrt hpos.ne').contMDiffAt
  have hcomp : ContMDiffAt ((𝓡 2).prod 𝓘(ℝ)) 𝓘(ℝ) ∞
      ((fun s : ℝ => Real.sqrt (1 - s ^ 2)) ∘
        (fun q : ↥neckCylDomain => (q : CylSpace).2)) q :=
    ContMDiffAt.comp q hsq (contMDiff_neckCylSnd.contMDiffAt)
  exact hcomp

private theorem contMDiff_neckCylFstCoord (i : Fin 3) :
    ContMDiff ((𝓡 2).prod 𝓘(ℝ)) 𝓘(ℝ) ∞
      (fun q : ↥neckCylDomain => (((q : CylSpace).1 : ThreeSpace).ofLp i)) :=
  ((EuclideanSpace.proj i).contMDiff).comp <|
    (contMDiff_coe_sphere (n := 2) (E := ThreeSpace)).comp <|
      (contMDiff_fst (I := 𝓡 2) (J := 𝓘(ℝ))).comp contMDiff_subtype_val

private def neckCylCoordFun (q : ↥neckCylDomain) : Fin 4 → ℝ :=
  snocR (fun i : Fin 3 =>
    Real.sqrt (1 - (q : CylSpace).2 ^ 2) * (((q : CylSpace).1 : ThreeSpace).ofLp i))
    ((q : CylSpace).2)

private theorem contMDiff_neckCylCoordFun :
    ContMDiff ((𝓡 2).prod 𝓘(ℝ)) 𝓘(ℝ, Fin 4 → ℝ) ∞ neckCylCoordFun := by
  rw [contMDiff_pi_space]
  intro i
  refine Fin.lastCases ?_ ?_ i
  · simp only [neckCylCoordFun, snocR_last]
    exact contMDiff_neckCylSnd
  · intro j
    simp only [neckCylCoordFun, snocR_castSucc]
    exact contMDiff_neckCylSqrt.mul (contMDiff_neckCylFstCoord j)

private theorem contMDiff_neckCylAmbient :
    ContMDiff ((𝓡 2).prod 𝓘(ℝ)) 𝓘(ℝ, NeckFour) ∞
      (fun q : ↥neckCylDomain => neckCylPoint (q : CylSpace).1 (q : CylSpace).2) := by
  have hE : ContMDiff ((𝓡 2).prod 𝓘(ℝ)) 𝓘(ℝ, NeckFour) ∞
      (fun q : ↥neckCylDomain => (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin 4)).symm
        (neckCylCoordFun q)) :=
    ((EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin 4)).symm :
      (Fin 4 → ℝ) →L[ℝ] NeckFour).contMDiff.comp contMDiff_neckCylCoordFun
  refine hE.congr ?_
  intro q
  simp only [EuclideanSpace.equiv, PiLp.continuousLinearEquiv_symm_apply, neckCylCoordFun,
    neckCylPoint, snocR]

private theorem contMDiff_neckCylMap :
    ContMDiff ((𝓡 2).prod 𝓘(ℝ)) ThreeModel ∞ neckCylMap := by
  refine (ContMDiff.codRestrict_sphere contMDiff_neckCylAmbient
    (fun q => neckCylPoint_mem_sphere (q : CylSpace).1
      (by have h := neckCylDomain_mem_abs (q := q)
          nlinarith [abs_nonneg (q : CylSpace).2, sq_abs (q : CylSpace).2]))).congr ?_
  intro q
  exact Subtype.ext rfl

private def neckCylBand : Set (Sphere 3) :=
  {z : Sphere 3 | neckLastCoord z ∈ Ioo (-(1 : ℝ)) 1}

private def neckCylDir (z : Sphere 3) : Sphere 2 :=
  sphereDirection neckCylBase (neckInitCoord z)

private def neckCylInverseCore (z : Sphere 3) : CylSpace :=
  (neckCylDir z, neckLastCoord z)

private def neckCylInverse (z : Sphere 3) : ↥neckCylDomain :=
  if h : neckLastCoord z ∈ Ioo (-(1 : ℝ)) 1 then
    ⟨neckCylInverseCore z, h⟩
  else ⟨(neckCylBase, 0), Set.mem_Ioo.mpr ⟨by norm_num, by norm_num⟩⟩

private theorem one_sub_sq_pos_of_mem_domain (q : ↥neckCylDomain) :
    0 < 1 - (q : CylSpace).2 ^ 2 := by
  obtain ⟨h1, h2⟩ := abs_lt.mp (neckCylDomain_mem_abs (q := q))
  nlinarith [sq_nonneg ((q : CylSpace).2)]

private theorem one_sub_sq_pos_of_mem_band {z : Sphere 3} (hz : z ∈ neckCylBand) :
    0 < 1 - neckLastCoord z ^ 2 := by
  obtain ⟨h1, h2⟩ := hz
  nlinarith [sq_nonneg (neckLastCoord z)]

private theorem neckInitCoord_ne_zero_of_mem_band {z : Sphere 3} (hz : z ∈ neckCylBand) :
    neckInitCoord z ≠ 0 := by
  intro h
  have h2 := norm_neckInitCoord_sq z
  rw [h, norm_zero] at h2
  have hpos := one_sub_sq_pos_of_mem_band hz
  linarith

private theorem contMDiff_neckInitCoord :
    ContMDiff ThreeModel 𝓘(ℝ, ThreeSpace) ∞ neckInitCoord := by
  have hE : ContMDiff ThreeModel 𝓘(ℝ, ThreeSpace) ∞
      (fun z : Sphere 3 => (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin 3)).symm
        (fun i : Fin 3 => (z.1 : NeckFour).ofLp i.castSucc)) :=
    ((EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin 3)).symm :
      (Fin 3 → ℝ) →L[ℝ] ThreeSpace).contMDiff.comp <|
      contMDiff_pi_space.mpr fun i =>
        ((EuclideanSpace.proj i.castSucc).contMDiff).comp
          (contMDiff_coe_sphere (n := 3) (E := NeckFour))
  refine hE.congr ?_
  intro z
  simp only [EuclideanSpace.equiv, PiLp.continuousLinearEquiv_symm_apply, neckInitCoord]

private theorem contMDiff_neckLastCoord : ContMDiff ThreeModel 𝓘(ℝ) ∞ neckLastCoord :=
  ((EuclideanSpace.proj (Fin.last 3)).contMDiff).comp
    (contMDiff_coe_sphere (n := 3) (E := NeckFour))

private theorem contMDiffOn_neckCylInverseCore :
    ContMDiffOn ThreeModel ((𝓡 2).prod 𝓘(ℝ)) ∞ neckCylInverseCore neckCylBand := by
  have hdir : ContMDiffOn ThreeModel (𝓡 2) ∞ neckCylDir neckCylBand :=
    (contMDiffOn_sphereDirection neckCylBase).comp contMDiff_neckInitCoord.contMDiffOn
      (fun z hz => neckInitCoord_ne_zero_of_mem_band hz)
  exact hdir.prodMk contMDiff_neckLastCoord.contMDiffOn

private theorem neckCylInverseCore_apply_of_mem_band {z : Sphere 3} (hz : z ∈ neckCylBand) :
    neckCylInverse z = ⟨neckCylInverseCore z, hz⟩ := dif_pos hz

private theorem neckCylDir_map (q : ↥neckCylDomain) :
    neckCylDir (neckCylMap q) = (q : CylSpace).1 := by
  rw [neckCylDir, neckCylMap_initCoord]
  exact sphereDirection_pos_smul neckCylBase (q : CylSpace).1
    (Real.sqrt_pos.mpr (one_sub_sq_pos_of_mem_domain q))

private theorem neckCylInverse_map (q : ↥neckCylDomain) :
    neckCylInverse (neckCylMap q) = q := by
  have hband : neckCylMap q ∈ neckCylBand := by
    change neckLastCoord (neckCylMap q) ∈ Ioo (-(1 : ℝ)) 1
    rw [neckCylMap_lastCoord]
    exact q.property
  rw [neckCylInverseCore_apply_of_mem_band hband]
  apply Subtype.ext
  exact Prod.ext (neckCylDir_map q) (neckCylMap_lastCoord q)

private def neckCylPartialEquiv : PartialEquiv ↥neckCylDomain (Sphere 3) where
  toFun := neckCylMap
  invFun := neckCylInverse
  source := univ
  target := range neckCylMap
  map_source' := fun x _ => mem_range_self x
  map_target' := fun _ _ => mem_univ _
  left_inv' := fun x _ => neckCylInverse_map x
  right_inv' := fun z hz => by
    obtain ⟨x, rfl⟩ := hz
    rw [neckCylInverse_map]

private theorem contMDiffOn_neckCylInverse :
    ContMDiffOn ThreeModel ((𝓡 2).prod 𝓘(ℝ)) ∞ neckCylInverse (range neckCylMap) := by
  have hsub : range neckCylMap ⊆ neckCylBand := by
    rintro z ⟨x, rfl⟩
    change neckLastCoord (neckCylMap x) ∈ Ioo (-(1 : ℝ)) 1
    rw [neckCylMap_lastCoord]
    exact x.property
  have hval : ContMDiffOn ThreeModel ((𝓡 2).prod 𝓘(ℝ)) ∞
      (fun z : Sphere 3 => (neckCylInverse z : CylSpace)) (range neckCylMap) :=
    ((contMDiffOn_neckCylInverseCore.mono hsub).congr fun z hz =>
      congrArg Subtype.val (neckCylInverseCore_apply_of_mem_band (hsub hz)))
  intro z hz
  exact (ContMDiffWithinAt.subtypeVal_comp_iff neckCylDomain neckCylInverse _ z).mp (hval z hz)

private theorem neckCylMap_injective : Function.Injective neckCylMap := by
  intro p q hpq
  have hlast : (p : CylSpace).2 = (q : CylSpace).2 := by
    rw [← neckCylMap_lastCoord p, ← neckCylMap_lastCoord q, hpq]
  have hinit : Real.sqrt (1 - (p : CylSpace).2 ^ 2) • ((p : CylSpace).1 : ThreeSpace) =
      Real.sqrt (1 - (q : CylSpace).2 ^ 2) • ((q : CylSpace).1 : ThreeSpace) := by
    rw [← neckCylMap_initCoord p, ← neckCylMap_initCoord q, hpq]
  have hfst : ((p : CylSpace).1 : ThreeSpace) = ((q : CylSpace).1 : ThreeSpace) := by
    have hpos := Real.sqrt_pos.mpr (one_sub_sq_pos_of_mem_domain p)
    have h2 : Real.sqrt (1 - (p : CylSpace).2 ^ 2) • ((p : CylSpace).1 : ThreeSpace) =
        Real.sqrt (1 - (p : CylSpace).2 ^ 2) • ((q : CylSpace).1 : ThreeSpace) := by
      rw [hinit, hlast]
    have h3 := congrArg (fun w : ThreeSpace => (Real.sqrt (1 - (p : CylSpace).2 ^ 2))⁻¹ • w) h2
    simpa [smul_smul, inv_mul_cancel₀ (ne_of_gt hpos)] using h3
  exact Subtype.ext (Prod.ext (Subtype.ext hfst) hlast)

private theorem isSmoothEmbedding_neckCylMap :
    IsSmoothEmbedding ((𝓡 2).prod 𝓘(ℝ)) ThreeModel ∞ neckCylMap := by
  obtain ⟨-, hinj⟩ := isEmbedding_and_injective_mfderiv_of_smooth_partialEquiv
    neckCylPartialEquiv rfl contMDiff_neckCylMap contMDiffOn_neckCylInverse
  refine isSmoothEmbedding_of_injective_mfderiv contMDiff_neckCylMap neckCylMap_injective hinj ?_
  simp [Module.finrank_prod]

private local instance : Fact ((-2 : ℝ) < 2) := ⟨by norm_num⟩

private def neckTubeInclusion (z : TubeDomain) : ↥neckCylDomain :=
  ⟨(z.1, (z.2 : ℝ) / 4), by
    change (z.2 : ℝ) / 4 ∈ Ioo (-(1 : ℝ)) 1
    obtain ⟨h1, h2⟩ := Set.mem_Icc.mp z.2.property
    exact Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩⟩

private noncomputable def realQuarterDiffeomorph : Diffeomorph 𝓘(ℝ) 𝓘(ℝ) ℝ ℝ ∞ :=
  (LinearEquiv.smulOfNeZero ℝ ℝ (1 / 4 : ℝ) (by norm_num) :
      ℝ ≃ₗ[ℝ] ℝ).toContinuousLinearEquiv |>.toDiffeomorph

private theorem isSmoothEmbedding_scaleIcc :
    IsSmoothEmbedding (𝓡∂ 1) 𝓘(ℝ) ∞ (fun t : Icc (-2 : ℝ) 2 => (t : ℝ) / 4) := by
  have h := (isSmoothEmbedding_subtypeVal_Icc (x := (-2 : ℝ)) (y := 2)
    (n := ∞)).diffeomorph_comp realQuarterDiffeomorph
  convert h using 1
  funext t
  change (t : ℝ) / 4 = (1 / 4 : ℝ) • (t : ℝ)
  rw [smul_eq_mul]
  ring

private theorem isSmoothEmbedding_neckTubeInclusion :
    IsSmoothEmbedding ((𝓡 2).prod (𝓡∂ 1)) ((𝓡 2).prod 𝓘(ℝ)) ∞
      neckTubeInclusion := by
  refine isSmoothEmbedding_intoOpen ((𝓡 2).prod (𝓡∂ 1)) ((𝓡 2).prod 𝓘(ℝ))
    neckCylDomain neckTubeInclusion ?_
  have hprod : IsSmoothEmbedding ((𝓡 2).prod (𝓡∂ 1)) ((𝓡 2).prod 𝓘(ℝ)) ∞
      (Prod.map (id : Sphere 2 → Sphere 2) (fun t : Icc (-2 : ℝ) 2 => (t : ℝ) / 4)) :=
    IsSmoothEmbedding.prodMap IsSmoothEmbedding.id isSmoothEmbedding_scaleIcc
  convert hprod using 1
  funext z
  rfl

theorem standardNeckTubeFun_isSmoothEmbedding :
    IsSmoothEmbedding ((𝓡 2).prod (𝓡∂ 1)) ThreeModel ∞ standardNeckTubeFun := by
  have hfun : (neckCylMap ∘ neckTubeInclusion) = standardNeckTubeFun := by
    funext z
    apply Subtype.ext
    change neckCylPoint z.1 ((z.2 : ℝ) / 4) = neckPoint z.1 (z.2 : ℝ)
    exact neckCylPoint_eq_neckPoint z.1 (z.2 : ℝ)
  have hcomp := IsSmoothEmbedding.comp_of_smoothBoundary
    (I := (𝓡 2).prod (𝓡∂ 1)) (J := (𝓡 2).prod 𝓘(ℝ)) (J' := ThreeModel)
    (f := neckTubeInclusion) (g := neckCylMap)
    isSmoothEmbedding_neckCylMap isSmoothEmbedding_neckTubeInclusion
  rw [hfun] at hcomp
  exact hcomp

theorem standardNeckTubeIsSmoothEmbedding_holds : standardNeckTubeIsSmoothEmbedding :=
  standardNeckTubeFun_isSmoothEmbedding

theorem standardNeckTubeSystem_tube_isSmoothEmbedding :
    letI : Fact ((-2 : ℝ) < 2) := ⟨by norm_num⟩
    ∀ a : standardNeckTubeSystem.Index,
      IsSmoothEmbedding ((𝓡 2).prod (𝓡∂ 1)) ThreeModel ∞
        (standardNeckTubeSystem.tube a) :=
  standardNeckTubeSystem_tube_smooth standardNeckTubeIsSmoothEmbedding_holds

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
