import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutCapPresentation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StandardNeckRegularity
import DifferentialGeometry.Topology.Manifold.SmoothModelTransportSource

set_option autoImplicit false
noncomputable section
open Bundle Manifold Set Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private abbrev NeckE3 := EuclideanSpace ℝ (Fin 3)

private abbrev NeckE4 := EuclideanSpace ℝ (Fin 4)

private def neckLastCoord (z : Sphere 3) : ℝ := (z.1 : NeckE4).ofLp (Fin.last 3)

private def neckInitCoord (z : Sphere 3) : NeckE3 :=
  WithLp.toLp 2 fun i : Fin 3 => (z.1 : NeckE4).ofLp i.castSucc

private theorem toLp_snocR_ofLp_last {n : ℕ} (f : Fin n → ℝ) (a : ℝ) :
    (WithLp.toLp 2 (snocR f a)).ofLp (Fin.last n) = a := by
  rw [WithLp.ofLp_toLp, snocR_last]

private theorem toLp_snocR_ofLp_castSucc {n : ℕ} (f : Fin n → ℝ) (a : ℝ) (i : Fin n) :
    (WithLp.toLp 2 (snocR f a)).ofLp i.castSucc = f i := by
  rw [WithLp.ofLp_toLp, snocR_castSucc]

private theorem norm_neckLastCoord (z : Sphere 3) : ‖(z.1 : NeckE4)‖ = 1 := by
  have h := z.2
  rwa [Metric.mem_sphere, dist_eq_norm, sub_zero] at h

private theorem norm_sq_neckLastCoord_le (z : Sphere 3) : neckLastCoord z ^ 2 ≤ 1 := by
  have h1 : ‖(z.1 : NeckE4)‖ ^ 2 = ∑ i : Fin 4, ((z.1 : NeckE4).ofLp i) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [Real.norm_eq_abs, sq_abs]
  have h2 := Fin.sum_univ_castSucc (fun i : Fin 4 => ((z.1 : NeckE4).ofLp i) ^ 2)
  have hz : ∑ i : Fin 4, ((z.1 : NeckE4).ofLp i) ^ 2 = 1 := by
    rw [← h1, norm_neckLastCoord z]
    norm_num
  rw [h2] at hz
  have h3 : ((z.1 : NeckE4).ofLp (Fin.last 3)) ^ 2 ≤
      (∑ i : Fin 3, ((z.1 : NeckE4).ofLp i.castSucc) ^ 2) +
        ((z.1 : NeckE4).ofLp (Fin.last 3)) ^ 2 := by
    have : (0 : ℝ) ≤ ∑ i : Fin 3, ((z.1 : NeckE4).ofLp i.castSucc) ^ 2 := by positivity
    linarith
  rw [hz] at h3
  exact h3

private theorem norm_sq_neckInitCoord (z : Sphere 3) :
    ‖neckInitCoord z‖ ^ 2 = 1 - neckLastCoord z ^ 2 := by
  have h1 : ‖(z.1 : NeckE4)‖ ^ 2 = ∑ i : Fin 4, ((z.1 : NeckE4).ofLp i) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [Real.norm_eq_abs, sq_abs]
  have hz : ∑ i : Fin 4, ((z.1 : NeckE4).ofLp i) ^ 2 = 1 := by
    rw [← h1, norm_neckLastCoord z]
    norm_num
  have h2 : ‖neckInitCoord z‖ ^ 2 =
      ∑ i : Fin 3, ((z.1 : NeckE4).ofLp i.castSucc) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [neckInitCoord, WithLp.ofLp_toLp, Real.norm_eq_abs, sq_abs]
  have h3 := Fin.sum_univ_castSucc (fun i : Fin 4 => ((z.1 : NeckE4).ofLp i) ^ 2)
  rw [h3] at hz
  rw [h2]
  simp only [neckLastCoord]
  linarith

private theorem tubeMap_lastCoord (z : TubeDomain) :
    neckLastCoord (standardNeckTubeFun z) = (z.2 : ℝ) / 4 := by
  change (neckPoint z.1 z.2.1 : NeckE4).ofLp (Fin.last 3) = (z.2 : ℝ) / 4
  rw [neckPoint, toLp_snocR_ofLp_last]

private theorem one_four_le_abs_neckLastCoord_of_mem_core
    (z : standardNeckTubeSystem.core) : 1 / 4 ≤ |neckLastCoord z.1| := by
  by_contra h
  have hz4 : |neckLastCoord z.1| < 1 / 4 := not_le.mp h
  have hc : -(1 / 4) < neckLastCoord z.1 ∧ neckLastCoord z.1 < 1 / 4 := abs_lt.mp hz4
  have htmem : 4 * neckLastCoord z.1 ∈ Icc (-2 : ℝ) 2 :=
    ⟨by linarith [hc.1], by linarith [hc.2]⟩
  set t : ℝ := 4 * neckLastCoord z.1 with htdef
  have ht4 : t / 4 = neckLastCoord z.1 := by rw [htdef]; ring
  have hvnorm : ‖neckInitCoord z.1‖ ^ 2 = 1 - neckLastCoord z.1 ^ 2 := norm_sq_neckInitCoord z.1
  have hvpos : 0 < ‖neckInitCoord z.1‖ := by
    have h2 : 0 < ‖neckInitCoord z.1‖ ^ 2 := by rw [hvnorm]; nlinarith [hc.1, hc.2]
    nlinarith [norm_nonneg (neckInitCoord z.1)]
  set y : Sphere 2 :=
    ⟨(‖neckInitCoord z.1‖)⁻¹ • neckInitCoord z.1, by
      rw [Metric.mem_sphere, dist_eq_norm, sub_zero, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
      exact inv_mul_cancel₀ (ne_of_gt hvpos)⟩ with hydef
  have hsqrt : Real.sqrt (1 - (t / 4) ^ 2) = ‖neckInitCoord z.1‖ := by
    rw [ht4, ← hvnorm, Real.sqrt_sq (norm_nonneg _)]
  have htube : standardNeckTubeFun (y, ⟨t, htmem⟩) = z.1 := by
    apply Subtype.ext
    apply WithLp.ofLp_injective 2
    funext i
    refine Fin.lastCases ?_ ?_ i
    · change (neckPoint y t : NeckE4).ofLp (Fin.last 3) = (z.1 : NeckE4).ofLp (Fin.last 3)
      rw [neckPoint, toLp_snocR_ofLp_last, ht4]
      rfl
    · intro j
      change (neckPoint y t : NeckE4).ofLp j.castSucc = (z.1 : NeckE4).ofLp j.castSucc
      rw [neckPoint, toLp_snocR_ofLp_castSucc]
      rw [hsqrt]
      change ‖neckInitCoord z.1‖ * ((y : NeckE3).ofLp j) = (neckInitCoord z.1).ofLp j
      rw [show (y : NeckE3) = (‖neckInitCoord z.1‖)⁻¹ • neckInitCoord z.1 from rfl]
      rw [WithLp.ofLp_smul]
      simp only [Pi.smul_apply, smul_eq_mul]
      field_simp
  have htlt : (-1 : ℝ) < t ∧ t < 1 := by
    rw [htdef]
    constructor <;> linarith [hc.1, hc.2]
  have hmem : z.1 ∈ standardNeckTubeSystem.removedBand PUnit.unit :=
    ⟨(y, ⟨t, htmem⟩), htlt, htube⟩
  exact z.2 (Set.mem_iUnion.mpr ⟨PUnit.unit, hmem⟩)

private theorem mem_core_iff (z : Sphere 3) :
    z ∈ standardNeckTubeSystem.core ↔ 1 / 4 ≤ |neckLastCoord z| := by
  constructor
  · intro hz
    exact one_four_le_abs_neckLastCoord_of_mem_core ⟨z, hz⟩
  · intro h
    rw [TubeSystem.core, Set.mem_compl_iff, Set.mem_iUnion]
    rintro ⟨a, w, hw, hwe⟩
    have hwlast : neckLastCoord z = (w.2 : ℝ) / 4 := by
      rw [← hwe]
      exact tubeMap_lastCoord w
    have hlt : |neckLastCoord z| < 1 / 4 := by
      rw [hwlast, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
      have : |(w.2 : ℝ)| < 1 := abs_lt.mpr ⟨hw.1, hw.2⟩
      linarith
    linarith

private theorem continuous_neckLastCoord : Continuous fun z : Sphere 3 => neckLastCoord z := by
  have h : (fun z : Sphere 3 => neckLastCoord z) =
      fun z : Sphere 3 => EuclideanSpace.proj (Fin.last 3) (z.1 : NeckE4) := by
    funext z
    rfl
  rw [h]
  exact (EuclideanSpace.proj (Fin.last 3)).continuous.comp continuous_subtype_val

private theorem isClosed_core : IsClosed standardNeckTubeSystem.core := by
  have hset : standardNeckTubeSystem.core = {z : Sphere 3 | 1 / 4 ≤ |neckLastCoord z|} :=
    Set.ext fun z => mem_core_iff z
  rw [hset]
  exact isClosed_Ici.preimage (continuous_abs.comp continuous_neckLastCoord)

private def coreLower : Set standardNeckTubeSystem.core :=
  {x | neckLastCoord x.1 ≤ -(1 / 4)}

private def coreUpper : Set standardNeckTubeSystem.core :=
  {x | 1 / 4 ≤ neckLastCoord x.1}

private theorem coreLower_union_coreUpper : coreLower ∪ coreUpper = univ := by
  ext x
  simp only [coreLower, coreUpper, Set.mem_union, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  rcases le_total 0 (neckLastCoord x.1) with h | h
  · right
    have := one_four_le_abs_neckLastCoord_of_mem_core x
    rwa [abs_of_nonneg h] at this
  · left
    have := one_four_le_abs_neckLastCoord_of_mem_core x
    rw [abs_of_nonpos h] at this
    linarith

private theorem not_mem_coreUpper_of_mem_coreLower {x : standardNeckTubeSystem.core}
    (hx : x ∈ coreLower) : x ∉ coreUpper := by
  simp only [coreLower, Set.mem_ofPred_eq] at hx
  simp only [coreUpper, Set.mem_ofPred_eq]
  linarith

private theorem not_mem_coreLower_of_mem_coreUpper {x : standardNeckTubeSystem.core}
    (hx : x ∈ coreUpper) : x ∉ coreLower := by
  simp only [coreUpper, Set.mem_ofPred_eq] at hx
  simp only [coreLower, Set.mem_ofPred_eq]
  linarith

private theorem isClosed_coreLower : IsClosed coreLower :=
  isClosed_Iic.preimage (continuous_neckLastCoord.comp continuous_subtype_val)

private theorem isClosed_coreUpper : IsClosed coreUpper :=
  isClosed_Ici.preimage (continuous_neckLastCoord.comp continuous_subtype_val)

private theorem isOpen_coreLower : IsOpen coreLower := by
  have hcompl : coreLower = coreUpperᶜ := by
    ext x
    constructor
    · intro hx hy
      exact not_mem_coreUpper_of_mem_coreLower hx hy
    · intro hx
      have hx' : x ∈ coreLower ∪ coreUpper := by rw [coreLower_union_coreUpper]; trivial
      rcases hx' with h | h
      · exact h
      · exact absurd h hx
  rw [hcompl]
  exact isClosed_coreUpper.isOpen_compl

private theorem isOpen_coreUpper : IsOpen coreUpper := by
  have hcompl : coreUpper = coreLowerᶜ := by
    ext x
    constructor
    · intro hx hy
      exact not_mem_coreLower_of_mem_coreUpper hx hy
    · intro hx
      have hx' : x ∈ coreLower ∪ coreUpper := by rw [coreLower_union_coreUpper]; trivial
      rcases hx' with h | h
      · exact absurd h hx
      · exact h
  rw [hcompl]
  exact isClosed_coreLower.isOpen_compl

private def neckCoreInclusion (x : standardNeckTubeSystem.core) : Sphere 3 ⊕ Sphere 3 :=
  if neckLastCoord x.1 ≤ -(1 / 4) then Sum.inl x.1 else Sum.inr x.1

private theorem neckCoreInclusion_of_mem_lower {x : standardNeckTubeSystem.core}
    (hx : x ∈ coreLower) : neckCoreInclusion x = Sum.inl x.1 :=
  if_pos hx

private theorem neckCoreInclusion_of_not_mem_lower {x : standardNeckTubeSystem.core}
    (hx : x ∉ coreLower) : neckCoreInclusion x = Sum.inr x.1 :=
  if_neg hx

private theorem continuous_neckCoreInclusion : Continuous neckCoreInclusion := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases h : x ∈ coreLower
  · refine (continuous_inl.comp continuous_subtype_val).continuousAt.congr ?_
    filter_upwards [isOpen_coreLower.mem_nhds h] with w hw
    exact (neckCoreInclusion_of_mem_lower hw).symm
  · have hx : x ∈ coreUpper := by
      have hx' : x ∈ coreLower ∪ coreUpper := by rw [coreLower_union_coreUpper]; trivial
      rcases hx' with h' | h'
      · exact absurd h' h
      · exact h'
    refine (continuous_inr.comp continuous_subtype_val).continuousAt.congr ?_
    filter_upwards [isOpen_coreUpper.mem_nhds hx] with w hw
    refine (neckCoreInclusion_of_not_mem_lower fun hcon => ?_).symm
    simp only [coreUpper, Set.mem_ofPred_eq] at hw
    simp only [coreLower, Set.mem_ofPred_eq] at hcon
    linarith

private theorem injective_neckCoreInclusion : Function.Injective neckCoreInclusion := by
  intro x y hxy
  by_cases hx : x ∈ coreLower
  · rw [neckCoreInclusion_of_mem_lower hx] at hxy
    by_cases hy : y ∈ coreLower
    · rw [neckCoreInclusion_of_mem_lower hy] at hxy
      exact Subtype.ext (Sum.inl_injective hxy)
    · rw [neckCoreInclusion_of_not_mem_lower hy] at hxy
      exact absurd hxy Sum.inl_ne_inr
  · rw [neckCoreInclusion_of_not_mem_lower hx] at hxy
    by_cases hy : y ∈ coreLower
    · rw [neckCoreInclusion_of_mem_lower hy] at hxy
      exact absurd hxy Sum.inr_ne_inl
    · rw [neckCoreInclusion_of_not_mem_lower hy] at hxy
      exact Subtype.ext (Sum.inr_injective hxy)

private theorem isEmbedding_neckCoreInclusion : Topology.IsEmbedding neckCoreInclusion := by
  have hc : CompactSpace standardNeckTubeSystem.core :=
    isCompact_iff_compactSpace.mp isClosed_core.isCompact
  exact (continuous_neckCoreInclusion.isClosedEmbedding injective_neckCoreInclusion).isEmbedding

private theorem norm_le_one_of_mem_closedBall (v : ThreeBall) : ‖(v : ThreeSpace)‖ ≤ 1 := by
  have h := v.2
  rwa [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h

private theorem mem_threeBall_of_norm_le {v : ThreeSpace} (h : ‖v‖ ≤ 1) : v ∈ ThreeBall := by
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
  exact h

private def capRadius : ℝ := Real.sqrt (5 / 3)

private def capW (v : ThreeBall) : NeckE3 := capRadius • (v : ThreeSpace)

private def capDen (v : ThreeBall) : ℝ := 1 + ‖capW v‖ ^ 2

private def capU (v : ThreeBall) : NeckE3 := (2 / capDen v) • capW v

private def capC (v : ThreeBall) : ℝ := (1 - ‖capW v‖ ^ 2) / capDen v

private theorem capRadius_sq : capRadius ^ 2 = 5 / 3 := by
  rw [capRadius, Real.sq_sqrt (by norm_num)]

private theorem capRadius_pos : 0 < capRadius := Real.sqrt_pos.mpr (by norm_num)

private theorem norm_capW_sq (v : ThreeBall) :
    ‖capW v‖ ^ 2 = 5 / 3 * ‖(v : ThreeSpace)‖ ^ 2 := by
  rw [capW, norm_smul, mul_pow, capRadius, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (by norm_num)]

private theorem norm_capW_sq_le (v : ThreeBall) : ‖capW v‖ ^ 2 ≤ 5 / 3 := by
  rw [norm_capW_sq]
  nlinarith [norm_nonneg (v : ThreeSpace), norm_le_one_of_mem_closedBall v]

private theorem capDen_pos (v : ThreeBall) : 0 < capDen v := by
  rw [capDen]
  positivity

private theorem capDen_ne_zero (v : ThreeBall) : capDen v ≠ 0 := ne_of_gt (capDen_pos v)

private theorem norm_capU_sq (v : ThreeBall) :
    ‖capU v‖ ^ 2 = 4 * ‖capW v‖ ^ 2 / capDen v ^ 2 := by
  rw [capU, norm_smul, mul_pow,
    Real.norm_of_nonneg (le_of_lt (div_pos (by norm_num) (capDen_pos v)))]
  ring

private theorem norm_capU_sq_add_capC_sq (v : ThreeBall) :
    ‖capU v‖ ^ 2 + capC v ^ 2 = 1 := by
  rw [norm_capU_sq, capC, div_pow, capDen]
  field_simp
  ring

private theorem capC_lower (v : ThreeBall) : -(1 / 4) ≤ capC v := by
  rw [capC, le_div_iff₀ (capDen_pos v), capDen]
  nlinarith [norm_capW_sq_le v]

private theorem capC_le_one (v : ThreeBall) : capC v ≤ 1 := by
  rw [capC, div_le_iff₀ (capDen_pos v), capDen]
  nlinarith [sq_nonneg ‖capW v‖]

private theorem sum_ofLp_sq_eq_norm_sq (u : NeckE3) :
    (∑ i : Fin 3, (u.ofLp i) ^ 2) = ‖u‖ ^ 2 := by
  simpa [Real.norm_eq_abs, sq_abs] using (EuclideanSpace.norm_sq_eq u).symm

private def capPoint (side : Bool) (v : ThreeBall) : NeckE4 :=
  WithLp.toLp 2 (snocR (fun i : Fin 3 => (capU v).ofLp i)
    (if side then -capC v else capC v))

private theorem norm_capPoint (side : Bool) (v : ThreeBall) : ‖capPoint side v‖ = 1 := by
  have h2 : ‖capPoint side v‖ ^ 2 =
      ‖capU v‖ ^ 2 + (if side then -capC v else capC v) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [capPoint, WithLp.ofLp_toLp, Real.norm_eq_abs, sq_abs]
    rw [Fin.sum_univ_castSucc]
    have h1 : (∑ i : Fin 3, (snocR (fun i : Fin 3 => (capU v).ofLp i)
        (if side then -capC v else capC v) i.castSucc) ^ 2)
        = ∑ i : Fin 3, ((capU v).ofLp i) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [snocR_castSucc]
    rw [h1, snocR_last, sum_ofLp_sq_eq_norm_sq]
  have h3 : (if side then -capC v else capC v) ^ 2 = capC v ^ 2 := by
    cases side <;> simp
  rw [h3, norm_capU_sq_add_capC_sq v] at h2
  nlinarith [norm_nonneg (capPoint side v)]

def standardNeckCapFun (side : Bool) (v : ThreeBall) : Sphere 3 :=
  ⟨capPoint side v, by
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
    exact norm_capPoint side v⟩

private theorem continuous_capW : Continuous fun v : ThreeBall => capW v := by
  have h : (fun v : ThreeBall => capW v) = fun v : ThreeBall => capRadius • (v : ThreeSpace) := by
    funext v
    rw [capW]
  rw [h]
  exact (continuous_const : Continuous fun _ : ThreeBall => capRadius).smul continuous_subtype_val

private theorem continuous_capDen : Continuous fun v : ThreeBall => capDen v := by
  have h : (fun v : ThreeBall => capDen v) = fun v : ThreeBall => 1 + ‖capW v‖ ^ 2 := by
    funext v
    rw [capDen]
  rw [h]
  exact (continuous_const : Continuous fun _ : ThreeBall => (1 : ℝ)).add
    ((continuous_norm.comp continuous_capW).pow 2)

private theorem continuous_capU_coord (i : Fin 3) :
    Continuous fun v : ThreeBall => (capU v).ofLp i := by
  have h : (fun v : ThreeBall => (capU v).ofLp i) =
      fun v : ThreeBall => (2 / capDen v) * (capW v).ofLp i := by
    funext v
    rw [capU]
    rfl
  rw [h]
  have hw : Continuous fun v : ThreeBall => (capW v).ofLp i := by
    have h2 : (fun v : ThreeBall => (capW v).ofLp i) =
        fun v : ThreeBall => capRadius * ((v : ThreeSpace).ofLp i) := by
      funext v
      rw [capW]
      rfl
    rw [h2]
    fun_prop
  exact (continuous_const.div continuous_capDen (fun v => capDen_ne_zero v)).mul hw

private theorem continuous_capC : Continuous fun v : ThreeBall => capC v := by
  have h : (fun v : ThreeBall => capC v) =
      fun v : ThreeBall => (1 - ‖capW v‖ ^ 2) / capDen v := by
    funext v
    rw [capC]
  rw [h]
  exact ((continuous_const : Continuous fun _ : ThreeBall => (1 : ℝ)).sub
    ((continuous_norm.comp continuous_capW).pow 2)).div
    continuous_capDen (fun v => capDen_ne_zero v)

private theorem continuous_capPoint (side : Bool) : Continuous (capPoint side) := by
  have h : capPoint side = fun v : ThreeBall =>
      WithLp.toLp 2 (snocR (fun i : Fin 3 => (capU v).ofLp i)
        (if side then -capC v else capC v)) := by
    funext v
    rw [capPoint]
  rw [h]
  refine (PiLp.continuous_toLp 2 (fun _ : Fin 4 => ℝ)).comp ?_
  refine Continuous.finSnoc ?_ ?_
  · apply continuous_pi
    intro i
    exact continuous_capU_coord i
  · cases side
    · simp only [Bool.false_eq_true, if_false]
      exact continuous_capC
    · simp only [if_true]
      exact continuous_capC.neg

private def standardNeckCap (side : Bool) : C(ThreeBall, Sphere 3) :=
  ⟨standardNeckCapFun side, (continuous_capPoint side).subtype_mk _⟩

private theorem standardNeckCap_apply (side : Bool) (v : ThreeBall) :
    standardNeckCap side v = standardNeckCapFun side v := rfl

private def capSign (side : Bool) : ℝ := if side then -1 else 1

private theorem capPoint_lastCoord (side : Bool) (v : ThreeBall) :
    (capPoint side v).ofLp (Fin.last 3) = capSign side * capC v := by
  rw [capPoint, toLp_snocR_ofLp_last]
  cases side <;> simp [capSign]

private theorem neckLastCoord_standardNeckCapFun (side : Bool) (v : ThreeBall) :
    neckLastCoord (standardNeckCapFun side v) = capSign side * capC v := by
  change (capPoint side v).ofLp (Fin.last 3) = capSign side * capC v
  exact capPoint_lastCoord side v

private theorem capU_eq_of_capPoint_eq {side : Bool} {v w : ThreeBall}
    (h : capPoint side v = capPoint side w) : capU v = capU w := by
  apply WithLp.ofLp_injective 2
  funext i
  have h' := congrArg (fun p : NeckE4 => p.ofLp i.castSucc) h
  simpa only [capPoint, toLp_snocR_ofLp_castSucc] using h'

private theorem capC_eq_of_capPoint_eq {side : Bool} {v w : ThreeBall}
    (h : capPoint side v = capPoint side w) : capC v = capC w := by
  have h' := congrArg (fun p : NeckE4 => p.ofLp (Fin.last 3)) h
  rw [capPoint_lastCoord, capPoint_lastCoord] at h'
  exact mul_left_cancel₀ (by cases side <;> simp [capSign]) h'

private theorem norm_capW_sq_eq_of_capC_eq {v w : ThreeBall} (h : capC v = capC w) :
    ‖capW v‖ ^ 2 = ‖capW w‖ ^ 2 := by
  have h1 : (0 : ℝ) < 1 + ‖capW v‖ ^ 2 := by positivity
  have h2 : (0 : ℝ) < 1 + ‖capW w‖ ^ 2 := by positivity
  have hv := h
  simp only [capC, capDen] at hv
  rw [div_eq_div_iff h1.ne' h2.ne'] at hv
  linarith

private theorem injective_capPoint (side : Bool) : Function.Injective (capPoint side) := by
  intro v w h
  have hr : ‖capW v‖ ^ 2 = ‖capW w‖ ^ 2 :=
    norm_capW_sq_eq_of_capC_eq (capC_eq_of_capPoint_eq h)
  have hU : capU v = capU w := capU_eq_of_capPoint_eq h
  have hden : capDen v = capDen w := by rw [capDen, capDen, hr]
  have hW : capW v = capW w := by
    have h1 : (2 / capDen w) • capW v = (2 / capDen w) • capW w := by
      simpa only [capU, hden] using hU
    have h2 := congrArg (fun u : NeckE3 => (capDen w / 2) • u) h1
    have hc : capDen w / 2 * (2 / capDen w) = 1 := by
      field_simp
      exact div_self (capDen_ne_zero w)
    simpa [smul_smul, hc, one_smul] using h2
  have hv : (v : ThreeSpace) = (w : ThreeSpace) := by
    have h1 := congrArg (fun u : NeckE3 => capRadius⁻¹ • u) hW
    have hc : capRadius⁻¹ * capRadius = 1 :=
      inv_mul_cancel₀ (ne_of_gt capRadius_pos)
    simpa [capW, smul_smul, hc, one_smul] using h1
  exact Subtype.ext hv

private theorem injective_standardNeckCapFun (side : Bool) :
    Function.Injective (standardNeckCapFun side) :=
  fun _ _ h => injective_capPoint side (congrArg Subtype.val h)

private theorem isEmbedding_standardNeckCapFun (side : Bool) :
    Topology.IsEmbedding (standardNeckCapFun side) := by
  have hc : CompactSpace ThreeBall := isCompact_iff_compactSpace.mp (isCompact_closedBall 0 1)
  have hcont : Continuous (standardNeckCapFun side) :=
    show Continuous fun v : ThreeBall => (⟨capPoint side v, _⟩ : Sphere 3) from
      (continuous_capPoint side).subtype_mk _
  exact (hcont.isClosedEmbedding (injective_standardNeckCapFun side)).isEmbedding

private theorem capSign_mul_self (side : Bool) : capSign side * capSign side = 1 := by
  cases side <;> norm_num [capSign]

private theorem capSign_sq (side : Bool) : capSign side ^ 2 = 1 := by
  cases side <;> norm_num [capSign]

private theorem capSign_ne_zero (side : Bool) : capSign side ≠ 0 := by
  cases side <;> norm_num [capSign]

private theorem capSign_eq_lastCoord (side : Bool) (v : ThreeBall) :
    (if side then -capC v else capC v) = capSign side * capC v := by
  cases side <;> simp [capSign]

private theorem self_toLp_snocR (z : Sphere 3) :
    z.1 = WithLp.toLp 2 (snocR (fun i : Fin 3 => (z.1 : NeckE4).ofLp i.castSucc)
      ((z.1 : NeckE4).ofLp (Fin.last 3))) := by
  apply WithLp.ofLp_injective 2
  funext i
  refine Fin.lastCases ?_ ?_ i
  · rw [toLp_snocR_ofLp_last]
  · intro j
    rw [toLp_snocR_ofLp_castSucc]

private theorem exists_standardNeckCapFun_eq (side : Bool) {z : Sphere 3}
    (hz : -(1 / 4) ≤ capSign side * neckLastCoord z) :
    ∃ v : ThreeBall, standardNeckCapFun side v = z := by
  set s : ℝ := capSign side with hsdef
  set c : ℝ := neckLastCoord z with hcdef
  set t : ℝ := s * c with htdef
  have hs2 : s ^ 2 = 1 := by rw [hsdef]; exact capSign_sq side
  have hst : s * t = c := by
    rw [htdef, ← mul_assoc, ← pow_two, hs2, one_mul]
  have hct : c ^ 2 = t ^ 2 := by
    rw [htdef, mul_pow, hs2, one_mul]
  have ht_ge : -(1 / 4) ≤ t := hz
  have ht_le : t ≤ 1 := by
    have h1 : c ^ 2 ≤ 1 := by rw [hcdef]; exact norm_sq_neckLastCoord_le z
    have h2 : |c| ≤ 1 := abs_le.mpr ⟨by nlinarith [h1], by nlinarith [h1]⟩
    have h3 : |s| = 1 := by rw [hsdef]; cases side <;> norm_num [capSign]
    have h4 : |t| = |c| := by rw [htdef, abs_mul, h3, one_mul]
    exact (abs_le.mp (by rw [h4]; exact h2)).2
  have hden : 0 < 1 + t := by
    have : -1 < t := by linarith
    linarith
  set r : ℝ := (1 - t) / (1 + t) with hrdef
  have hr_nonneg : 0 ≤ r := by
    rw [hrdef]
    exact div_nonneg (by linarith) (le_of_lt hden)
  have hr_le : r ≤ 5 / 3 := by
    rw [hrdef, div_le_iff₀ hden]
    linarith
  have hr_pos : 0 < 1 + r := by
    have h : 1 + r = 2 / (1 + t) := by
      rw [hrdef]
      field_simp
      ring
    rw [h]
    exact div_pos (by norm_num) hden
  have hr_den : (1 + r) / 2 = 1 / (1 + t) := by
    rw [hrdef]
    field_simp
    ring
  have hr_val : (1 - r) / (1 + r) = t := by
    rw [hrdef]
    field_simp
    ring
  have hw_sq : ‖(((1 + r) / 2 : ℝ) • neckInitCoord z)‖ ^ 2 = r := by
    rw [norm_smul, mul_pow, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ (1 + r) / 2),
      norm_sq_neckInitCoord, ← hcdef, hr_den, hrdef]
    field_simp
    rw [hct]
    ring
  have hwnorm_le : ‖(((1 + r) / 2 : ℝ) • neckInitCoord z)‖ ≤ capRadius :=
    le_of_sq_le_sq (by rw [hw_sq, capRadius_sq]; exact hr_le) (le_of_lt capRadius_pos)
  have hcr : 1 ≤ capRadius := by
    rw [capRadius, Real.one_le_sqrt]
    norm_num
  set v : ThreeBall :=
    ⟨capRadius⁻¹ • (((1 + r) / 2 : ℝ) • neckInitCoord z),
      mem_threeBall_of_norm_le (by
        rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (le_of_lt capRadius_pos))]
        have hinv : capRadius⁻¹ * capRadius = 1 :=
          inv_mul_cancel₀ (ne_of_gt capRadius_pos)
        nlinarith [norm_nonneg (((1 + r) / 2 : ℝ) • neckInitCoord z),
          inv_pos_of_pos capRadius_pos])⟩ with hvdef
  have hcapW : capW v = ((1 + r) / 2 : ℝ) • neckInitCoord z := by
    rw [hvdef]
    change capRadius • (capRadius⁻¹ • (((1 + r) / 2 : ℝ) • neckInitCoord z)) = _
    rw [smul_smul, mul_inv_cancel₀ (ne_of_gt capRadius_pos), one_smul]
  have hcapDen : capDen v = 1 + r := by
    rw [capDen, hcapW, hw_sq]
  have hcoef : 2 / (1 + r) * ((1 + r) / 2) = 1 := by
    field_simp
  have hcapU : capU v = neckInitCoord z := by
    rw [capU, hcapW, hcapDen]
    rw [smul_smul, hcoef, one_smul]
  have hcapC : capC v = t := by
    rw [capC, hcapW, hcapDen, hw_sq, hr_val]
  refine ⟨v, Subtype.ext ?_⟩
  apply WithLp.ofLp_injective 2
  funext i
  refine Fin.lastCases ?_ ?_ i
  · change (capPoint side v).ofLp (Fin.last 3) = (z.1 : NeckE4).ofLp (Fin.last 3)
    rw [capPoint_lastCoord, hcapC, ← hsdef, hst, hcdef]
    rfl
  · intro j
    change (capPoint side v).ofLp j.castSucc = (z.1 : NeckE4).ofLp j.castSucc
    rw [capPoint, toLp_snocR_ofLp_castSucc, hcapU]
    rfl

private theorem range_standardNeckCapFun_false :
    Set.range (standardNeckCapFun false) =
      {z : Sphere 3 | -(1 / 4) ≤ neckLastCoord z} := by
  ext z
  constructor
  · rintro ⟨v, rfl⟩
    change -(1 / 4) ≤ neckLastCoord (standardNeckCapFun false v)
    rw [neckLastCoord_standardNeckCapFun]
    simpa [capSign] using capC_lower v
  · intro hz
    exact exists_standardNeckCapFun_eq false (by simpa [capSign] using hz)

private theorem range_standardNeckCapFun_true :
    Set.range (standardNeckCapFun true) =
      {z : Sphere 3 | neckLastCoord z ≤ 1 / 4} := by
  ext z
  constructor
  · rintro ⟨v, rfl⟩
    change neckLastCoord (standardNeckCapFun true v) ≤ 1 / 4
    rw [neckLastCoord_standardNeckCapFun, capSign]
    simp only [if_true, neg_mul, one_mul]
    have := capC_lower v
    linarith
  · intro hz
    exact exists_standardNeckCapFun_eq true (by simpa [capSign] using hz)

private theorem coe_coreBoundarySphere (b : standardNeckTubeSystem.Boundary) (y : Sphere 2) :
    ((standardNeckTubeSystem.coreBoundarySphere b y : standardNeckTubeSystem.core) : Sphere 3) =
      standardNeckTubeFun (y, TubeSystem.boundaryLevel b.2) := rfl

private theorem neckLastCoord_coreBoundarySphere (b : standardNeckTubeSystem.Boundary)
    (y : Sphere 2) :
    neckLastCoord ((standardNeckTubeSystem.coreBoundarySphere b y :
      standardNeckTubeSystem.core) : Sphere 3) = (TubeSystem.boundaryLevel b.2 : ℝ) / 4 := by
  rw [coe_coreBoundarySphere]
  exact tubeMap_lastCoord (y, TubeSystem.boundaryLevel b.2)

private theorem norm_sphereToThreeBall (y : Sphere 2) :
    ‖(sphereToThreeBall y : ThreeSpace)‖ = 1 := by
  have h := y.2
  rwa [Metric.mem_sphere, dist_eq_norm, sub_zero] at h

private theorem norm_coe_sphereTwo (y : Sphere 2) : ‖(y : ThreeSpace)‖ = 1 := by
  have h := y.2
  rwa [Metric.mem_sphere, dist_eq_norm, sub_zero] at h

private theorem ofLp_smul_apply (c : ℝ) (x : NeckE3) (j : Fin 3) :
    (c • x).ofLp j = c * x.ofLp j := rfl

private theorem capW_sphereToThreeBall (y : Sphere 2) :
    capW (sphereToThreeBall y) = capRadius • (y : ThreeSpace) := rfl

private theorem norm_capW_sphereToThreeBall (y : Sphere 2) :
    ‖capW (sphereToThreeBall y)‖ ^ 2 = 5 / 3 := by
  rw [capW_sphereToThreeBall, norm_smul, mul_pow,
    Real.norm_of_nonneg (le_of_lt capRadius_pos), capRadius_sq, norm_coe_sphereTwo]
  ring

private theorem capC_sphereToThreeBall (y : Sphere 2) :
    capC (sphereToThreeBall y) = -(1 / 4) := by
  rw [capC, capDen, norm_capW_sphereToThreeBall]
  norm_num

private theorem three_quarters_capRadius : (3 / 4) * capRadius = Real.sqrt (15 / 16) := by
  have hsq : ((3 / 4) * Real.sqrt (5 / 3)) ^ 2 = (15 : ℝ) / 16 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  rw [capRadius]
  rw [show (15 : ℝ) / 16 = ((3 / 4) * Real.sqrt (5 / 3)) ^ 2 from hsq.symm,
    Real.sqrt_sq (by positivity)]

private theorem capU_sphereToThreeBall (y : Sphere 2) :
    capU (sphereToThreeBall y) = Real.sqrt (15 / 16) • (y : ThreeSpace) := by
  have hcoef : 2 / (1 + 5 / 3 : ℝ) = 3 / 4 := by norm_num
  rw [capU, capW_sphereToThreeBall, capDen, norm_capW_sphereToThreeBall, hcoef,
    smul_smul, three_quarters_capRadius]

private theorem standardNeckCapFun_sphereToThreeBall (side : Bool) (y : Sphere 2) :
    standardNeckCapFun side (sphereToThreeBall y) =
      standardNeckTubeFun (y, TubeSystem.boundaryLevel side) := by
  apply Subtype.ext
  apply WithLp.ofLp_injective 2
  funext i
  refine Fin.lastCases ?_ ?_ i
  · change (capPoint side (sphereToThreeBall y)).ofLp (Fin.last 3) =
      (neckPoint y (TubeSystem.boundaryLevel side : ℝ)).ofLp (Fin.last 3)
    rw [capPoint_lastCoord, neckPoint, toLp_snocR_ofLp_last]
    have h4 : capSign side * capC (sphereToThreeBall y) =
        (TubeSystem.boundaryLevel side : ℝ) / 4 := by
      rw [capC_sphereToThreeBall]
      cases side <;> norm_num [capSign, TubeSystem.boundaryLevel]
    rw [h4]
  · intro j
    change (capPoint side (sphereToThreeBall y)).ofLp j.castSucc =
      (neckPoint y (TubeSystem.boundaryLevel side : ℝ)).ofLp j.castSucc
    rw [capPoint, toLp_snocR_ofLp_castSucc, neckPoint, toLp_snocR_ofLp_castSucc,
      capU_sphereToThreeBall]
    have hsqrt : Real.sqrt (1 - ((TubeSystem.boundaryLevel side : ℝ) / 4) ^ 2) =
        Real.sqrt (15 / 16) := by
      congr 1
      cases side <;> norm_num [TubeSystem.boundaryLevel]
    rw [hsqrt, ofLp_smul_apply]

private theorem coreBoundarySphere_false_lastCoord (a : standardNeckTubeSystem.Index)
    (y : Sphere 2) :
    neckLastCoord ((standardNeckTubeSystem.coreBoundarySphere (a, false) y :
      standardNeckTubeSystem.core) : Sphere 3) = -(1 / 4) := by
  rw [neckLastCoord_coreBoundarySphere]
  norm_num [TubeSystem.boundaryLevel]

private theorem coreBoundarySphere_true_lastCoord (a : standardNeckTubeSystem.Index)
    (y : Sphere 2) :
    neckLastCoord ((standardNeckTubeSystem.coreBoundarySphere (a, true) y :
      standardNeckTubeSystem.core) : Sphere 3) = 1 / 4 := by
  rw [neckLastCoord_coreBoundarySphere]
  norm_num [TubeSystem.boundaryLevel]

private theorem exists_coreBoundarySphere_eq_of_lastCoord_eq
    (a : standardNeckTubeSystem.Index) (side : Bool) {z : Sphere 3}
    (hz : neckLastCoord z = if side then (1 : ℝ) / 4 else -(1 / 4)) :
    ∃ y : Sphere 2, ((standardNeckTubeSystem.coreBoundarySphere (a, side) y :
      standardNeckTubeSystem.core) : Sphere 3) = z := by
  have hc : neckLastCoord z = (TubeSystem.boundaryLevel side : ℝ) / 4 := by
    rw [hz]
    cases side <;> norm_num [TubeSystem.boundaryLevel]
  have hinit : ‖neckInitCoord z‖ ^ 2 = 15 / 16 := by
    rw [norm_sq_neckInitCoord, hc]
    cases side <;> norm_num [TubeSystem.boundaryLevel]
  have hnorm : ‖neckInitCoord z‖ = Real.sqrt (15 / 16) := by
    rw [← hinit, Real.sqrt_sq (norm_nonneg _)]
  set y : Sphere 2 :=
    ⟨(Real.sqrt (15 / 16))⁻¹ • neckInitCoord z, by
      rw [Metric.mem_sphere, dist_eq_norm, sub_zero, norm_smul,
        Real.norm_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)), hnorm]
      exact inv_mul_cancel₀ (by positivity)⟩ with hydef
  refine ⟨y, ?_⟩
  rw [coe_coreBoundarySphere]
  apply Subtype.ext
  apply WithLp.ofLp_injective 2
  funext i
  refine Fin.lastCases ?_ ?_ i
  · change (neckPoint y (TubeSystem.boundaryLevel side : ℝ)).ofLp (Fin.last 3) =
      (z.1 : NeckE4).ofLp (Fin.last 3)
    rw [neckPoint, toLp_snocR_ofLp_last, ← hc]
    rfl
  · intro j
    change (neckPoint y (TubeSystem.boundaryLevel side : ℝ)).ofLp j.castSucc =
      (z.1 : NeckE4).ofLp j.castSucc
    rw [neckPoint, toLp_snocR_ofLp_castSucc]
    have hsqrt : Real.sqrt (1 - ((TubeSystem.boundaryLevel side : ℝ) / 4) ^ 2) =
        Real.sqrt (15 / 16) := by
      congr 1
      cases side <;> norm_num [TubeSystem.boundaryLevel]
    rw [hsqrt]
    have hy : (y : ThreeSpace) = (Real.sqrt (15 / 16))⁻¹ • neckInitCoord z := rfl
    rw [hy, ofLp_smul_apply]
    have hne : Real.sqrt (15 / 16) ≠ 0 := by positivity
    rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]
    rfl

private theorem mem_coreLower_coreBoundarySphere_false (a : standardNeckTubeSystem.Index)
    (y : Sphere 2) :
    standardNeckTubeSystem.coreBoundarySphere (a, false) y ∈ coreLower :=
  le_of_eq (coreBoundarySphere_false_lastCoord a y)

private theorem mem_coreUpper_coreBoundarySphere_true (a : standardNeckTubeSystem.Index)
    (y : Sphere 2) :
    standardNeckTubeSystem.coreBoundarySphere (a, true) y ∈ coreUpper :=
  le_of_eq (coreBoundarySphere_true_lastCoord a y)

private theorem range_neckCoreInclusion :
    Set.range neckCoreInclusion =
      (Sum.inl '' {z : Sphere 3 | neckLastCoord z ≤ -(1 / 4)}) ∪
        (Sum.inr '' {z : Sphere 3 | 1 / 4 ≤ neckLastCoord z}) := by
  ext x
  constructor
  · rintro ⟨x₀, rfl⟩
    by_cases hx : x₀ ∈ coreLower
    · refine Or.inl ⟨x₀.1, ?_, (neckCoreInclusion_of_mem_lower hx).symm⟩
      simpa only [coreLower, Set.mem_ofPred_eq] using hx
    · have hx' : x₀ ∈ coreUpper := by
        have hx'' : x₀ ∈ coreLower ∪ coreUpper := by rw [coreLower_union_coreUpper]; trivial
        rcases hx'' with h | h
        · exact absurd h hx
        · exact h
      refine Or.inr ⟨x₀.1, ?_, (neckCoreInclusion_of_not_mem_lower hx).symm⟩
      simpa only [coreUpper, Set.mem_ofPred_eq] using hx'
  · rintro (h | h)
    · obtain ⟨z, hz, hzx⟩ := h
      simp only [Set.mem_ofPred_eq] at hz
      have hzcore : z ∈ standardNeckTubeSystem.core := by
        rw [mem_core_iff]
        rw [abs_of_nonpos (by linarith [hz])]
        linarith
      refine ⟨⟨z, hzcore⟩, ?_⟩
      rw [neckCoreInclusion_of_mem_lower (show _ ∈ coreLower from hz), hzx]
    · obtain ⟨z, hz, hzx⟩ := h
      simp only [Set.mem_ofPred_eq] at hz
      have hzcore : z ∈ standardNeckTubeSystem.core := by
        rw [mem_core_iff, abs_of_nonneg (by linarith [hz])]
        exact hz
      refine ⟨⟨z, hzcore⟩, ?_⟩
      rw [neckCoreInclusion_of_not_mem_lower (show _ ∉ coreLower from by
        simp only [coreLower, Set.mem_ofPred_eq]
        linarith [hz]), hzx]

private def standardNeckCapInl : C(ThreeBall, Sphere 3 ⊕ Sphere 3) :=
  ⟨fun v => Sum.inl (standardNeckCapFun false v),
    continuous_inl.comp (standardNeckCap false).continuous⟩

private def standardNeckCapInr : C(ThreeBall, Sphere 3 ⊕ Sphere 3) :=
  ⟨fun v => Sum.inr (standardNeckCapFun true v),
    continuous_inr.comp (standardNeckCap true).continuous⟩

private def standardNeckCapSum (b : standardNeckTubeSystem.Boundary) :
    C(ThreeBall, Sphere 3 ⊕ Sphere 3) :=
  if b.2 then standardNeckCapInr else standardNeckCapInl

private theorem standardNeckCapSum_false :
    standardNeckCapSum (PUnit.unit, false) = standardNeckCapInl := by
  simp [standardNeckCapSum]

private theorem standardNeckCapSum_true :
    standardNeckCapSum (PUnit.unit, true) = standardNeckCapInr := by
  simp [standardNeckCapSum]

private theorem standardNeckCapSum_false_apply (v : ThreeBall) :
    standardNeckCapSum (PUnit.unit, false) v = Sum.inl (standardNeckCapFun false v) := by
  rw [standardNeckCapSum_false]
  rfl

private theorem standardNeckCapSum_true_apply (v : ThreeBall) :
    standardNeckCapSum (PUnit.unit, true) v = Sum.inr (standardNeckCapFun true v) := by
  rw [standardNeckCapSum_true]
  rfl

private theorem range_standardNeckCapInl :
    Set.range (standardNeckCapInl : ThreeBall → Sphere 3 ⊕ Sphere 3) =
      Sum.inl '' {z : Sphere 3 | -(1 / 4) ≤ neckLastCoord z} := by
  have h : (standardNeckCapInl : ThreeBall → Sphere 3 ⊕ Sphere 3) =
      Sum.inl ∘ standardNeckCapFun false := rfl
  rw [h, Set.range_comp, range_standardNeckCapFun_false]

private theorem range_standardNeckCapInr :
    Set.range (standardNeckCapInr : ThreeBall → Sphere 3 ⊕ Sphere 3) =
      Sum.inr '' {z : Sphere 3 | neckLastCoord z ≤ 1 / 4} := by
  have h : (standardNeckCapInr : ThreeBall → Sphere 3 ⊕ Sphere 3) =
      Sum.inr ∘ standardNeckCapFun true := rfl
  rw [h, Set.range_comp, range_standardNeckCapFun_true]

private theorem standardNeckCapSum_eq_inl_of {b : standardNeckTubeSystem.Boundary}
    (hb : b.2 = false) : standardNeckCapSum b = standardNeckCapInl := by
  simp [standardNeckCapSum, hb]

private theorem standardNeckCapSum_eq_inr_of {b : standardNeckTubeSystem.Boundary}
    (hb : b.2 = true) : standardNeckCapSum b = standardNeckCapInr := by
  simp [standardNeckCapSum, hb]

private theorem isEmbedding_standardNeckCapSum (b : standardNeckTubeSystem.Boundary) :
    Topology.IsEmbedding (standardNeckCapSum b) := by
  by_cases hb : b.2
  · rw [standardNeckCapSum_eq_inr_of (by simpa using hb)]
    exact Topology.IsEmbedding.inr.comp (isEmbedding_standardNeckCapFun true)
  · rw [standardNeckCapSum_eq_inl_of (by simpa using hb)]
    exact Topology.IsEmbedding.inl.comp (isEmbedding_standardNeckCapFun false)

def standardNeckCapping : Capping standardNeckTubeSystem (Sphere 3 ⊕ Sphere 3) where
  coreInclusion := ⟨neckCoreInclusion, continuous_neckCoreInclusion⟩
  coreEmbedding := isEmbedding_neckCoreInclusion
  cap := standardNeckCapSum
  capEmbedding := isEmbedding_standardNeckCapSum
  attaching := fun _ => Homeomorph.refl _
  boundary_eq := by
    rintro ⟨a, s⟩ y
    cases a
    cases s
    · change Sum.inl (standardNeckCapFun false (sphereToThreeBall y)) =
        neckCoreInclusion (standardNeckTubeSystem.coreBoundarySphere (PUnit.unit, false) y)
      rw [standardNeckCapFun_sphereToThreeBall,
        neckCoreInclusion_of_mem_lower (mem_coreLower_coreBoundarySphere_false PUnit.unit y),
        coe_coreBoundarySphere]
    · change Sum.inr (standardNeckCapFun true (sphereToThreeBall y)) =
        neckCoreInclusion (standardNeckTubeSystem.coreBoundarySphere (PUnit.unit, true) y)
      rw [standardNeckCapFun_sphereToThreeBall,
        neckCoreInclusion_of_not_mem_lower
          (not_mem_coreLower_of_mem_coreUpper
            (mem_coreUpper_coreBoundarySphere_true PUnit.unit y)),
        coe_coreBoundarySphere]
  exhaustive := by
    refine eq_univ_of_forall ?_
    rintro (z | z)
    · by_cases h : neckLastCoord z ≤ -(1 / 4)
      · refine Or.inl ⟨⟨z, (mem_core_iff z).mpr ?_⟩, ?_⟩
        · rw [abs_of_nonpos (by linarith)]
          linarith
        · change neckCoreInclusion _ = Sum.inl z
          rw [neckCoreInclusion_of_mem_lower (show _ ∈ coreLower from h)]
      · refine Or.inr (Set.mem_iUnion.mpr ⟨(PUnit.unit, false), ?_⟩)
        obtain ⟨v, hv⟩ := exists_standardNeckCapFun_eq false (by simpa [capSign] using (by linarith :
          -(1 / 4) ≤ neckLastCoord z))
        exact ⟨v, by rw [standardNeckCapSum_false_apply, hv]⟩
    · by_cases h : 1 / 4 ≤ neckLastCoord z
      · refine Or.inl ⟨⟨z, (mem_core_iff z).mpr ?_⟩, ?_⟩
        · rw [abs_of_nonneg (by linarith)]
          exact h
        · change neckCoreInclusion _ = Sum.inr z
          rw [neckCoreInclusion_of_not_mem_lower (show _ ∉ coreLower from by
            simp only [coreLower, Set.mem_ofPred_eq]
            linarith)]
      · refine Or.inr (Set.mem_iUnion.mpr ⟨(PUnit.unit, true), ?_⟩)
        obtain ⟨v, hv⟩ := exists_standardNeckCapFun_eq true (by simpa [capSign] using (by linarith :
          neckLastCoord z ≤ 1 / 4))
        exact ⟨v, by rw [standardNeckCapSum_true_apply, hv]⟩
  core_cap_intersection := by
    rintro ⟨a, s⟩
    cases a
    cases s
    · ext x
      constructor
      · rintro ⟨hcore, hcap⟩
        obtain ⟨x₀, rfl⟩ := hcore
        obtain ⟨v, hv⟩ := hcap
        rw [standardNeckCapSum_false_apply] at hv
        by_cases hx : x₀ ∈ coreLower
        · have hz : x₀.1 = standardNeckCapFun false v :=
            (Sum.inl_injective (hv.trans (neckCoreInclusion_of_mem_lower hx))).symm
          have hle : -(1 / 4) ≤ neckLastCoord x₀.1 := by
            rw [hz, neckLastCoord_standardNeckCapFun, capSign]
            simpa using capC_lower v
          have heq : neckLastCoord x₀.1 = -(1 / 4) := le_antisymm hx hle
          obtain ⟨y, hy⟩ :=
            exists_coreBoundarySphere_eq_of_lastCoord_eq PUnit.unit false (by simpa using heq)
          refine ⟨y, ?_⟩
          simp only [ContinuousMap.coe_mk, ContinuousMap.comp_apply]
          rw [Subtype.ext hy]
        · exact absurd (hv.trans (neckCoreInclusion_of_not_mem_lower hx)) Sum.inl_ne_inr
      · rintro ⟨y, rfl⟩
        refine ⟨⟨_, rfl⟩, ⟨sphereToThreeBall y, ?_⟩⟩
        simp only [ContinuousMap.coe_mk, ContinuousMap.comp_apply]
        rw [standardNeckCapSum_false_apply, standardNeckCapFun_sphereToThreeBall,
          neckCoreInclusion_of_mem_lower (mem_coreLower_coreBoundarySphere_false PUnit.unit y),
          coe_coreBoundarySphere]
    · ext x
      constructor
      · rintro ⟨hcore, hcap⟩
        obtain ⟨x₀, rfl⟩ := hcore
        obtain ⟨v, hv⟩ := hcap
        rw [standardNeckCapSum_true_apply] at hv
        by_cases hx : x₀ ∈ coreLower
        · exact absurd (hv.trans (neckCoreInclusion_of_mem_lower hx)) Sum.inr_ne_inl
        · have hz : x₀.1 = standardNeckCapFun true v :=
            (Sum.inr_injective (hv.trans (neckCoreInclusion_of_not_mem_lower hx))).symm
          have hle : neckLastCoord x₀.1 ≤ 1 / 4 := by
            rw [hz, neckLastCoord_standardNeckCapFun, capSign]
            simp only [if_true, neg_mul, one_mul]
            have := capC_lower v
            linarith
          have hcore' : 1 / 4 ≤ |neckLastCoord x₀.1| := (mem_core_iff x₀.1).mp x₀.2
          have hup : 1 / 4 ≤ neckLastCoord x₀.1 := by
            rcases le_total 0 (neckLastCoord x₀.1) with h | h
            · rwa [abs_of_nonneg h] at hcore'
            · exfalso
              rw [abs_of_nonpos h] at hcore'
              have hx' : neckLastCoord x₀.1 ≤ -(1 / 4) := by linarith
              exact hx hx'
          have heq : neckLastCoord x₀.1 = 1 / 4 := le_antisymm hle hup
          obtain ⟨y, hy⟩ :=
            exists_coreBoundarySphere_eq_of_lastCoord_eq PUnit.unit true (by simpa using heq)
          refine ⟨y, ?_⟩
          simp only [ContinuousMap.coe_mk, ContinuousMap.comp_apply]
          rw [Subtype.ext hy]
      · rintro ⟨y, rfl⟩
        refine ⟨⟨_, rfl⟩, ⟨sphereToThreeBall y, ?_⟩⟩
        simp only [ContinuousMap.coe_mk, ContinuousMap.comp_apply]
        rw [standardNeckCapSum_true_apply, standardNeckCapFun_sphereToThreeBall,
          neckCoreInclusion_of_not_mem_lower
            (not_mem_coreLower_of_mem_coreUpper
              (mem_coreUpper_coreBoundarySphere_true PUnit.unit y)),
          coe_coreBoundarySphere]
  cap_disjoint := by
    rintro ⟨a, s⟩ ⟨a', s'⟩ hne
    cases a
    cases a'
    cases s <;> cases s'
    · exact absurd rfl hne
    · rw [Set.disjoint_left]
      rintro x ⟨v, hv⟩ ⟨v', hv'⟩
      rw [standardNeckCapSum_false_apply] at hv
      rw [standardNeckCapSum_true_apply] at hv'
      exact Sum.inl_ne_inr (hv.trans hv'.symm)
    · rw [Set.disjoint_left]
      rintro x ⟨v, hv⟩ ⟨v', hv'⟩
      rw [standardNeckCapSum_true_apply] at hv
      rw [standardNeckCapSum_false_apply] at hv'
      exact Sum.inr_ne_inl (hv.trans hv'.symm)
    · exact absurd rfl hne

abbrev standardNeckCutCap :
    CutCapTopology (Sphere 3) (Sphere 3) (Sphere 3) (Sphere 3 ⊕ Sphere 3) where
  tubes := standardNeckTubeSystem
  capping := standardNeckCapping
  presentation := Homeomorph.refl _
  nontrivial := Or.inl standardNeckTubeSystem_index_nonempty

theorem standardNeckCutCap_cap_false_mem_range_inl :
    ∀ y : ThreeBall, standardNeckCutCap.presentation
      (standardNeckCutCap.capping.cap (PUnit.unit, false) y) ∈
        Set.range (Sum.inl : Sphere 3 → Sphere 3 ⊕ Sphere 3) := by
  intro y
  exact ⟨standardNeckCapFun false y, (standardNeckCapSum_false_apply y).symm⟩

theorem standardNeckCutCap_cap_true_mem_range_inr :
    ∀ y : ThreeBall, standardNeckCutCap.presentation
      (standardNeckCutCap.capping.cap (PUnit.unit, true) y) ∈
        Set.range (Sum.inr : Sphere 3 → Sphere 3 ⊕ Sphere 3) := by
  intro y
  exact ⟨standardNeckCapFun true y, (standardNeckCapSum_true_apply y).symm⟩

theorem standardNeckCutCap_coreBoundarySphere_false_mem_retainedCore (y : Sphere 2) :
    standardNeckCutCap.tubes.coreBoundarySphere (PUnit.unit, false) y ∈
      standardNeckCutCap.retainedCore := by
  refine ⟨((standardNeckTubeSystem.coreBoundarySphere (PUnit.unit, false) y :
    standardNeckTubeSystem.core) : Sphere 3), ?_⟩
  change neckCoreInclusion
    (standardNeckTubeSystem.coreBoundarySphere (PUnit.unit, false) y) = Sum.inl _
  exact neckCoreInclusion_of_mem_lower (mem_coreLower_coreBoundarySphere_false PUnit.unit y)

theorem standardNeckCutCap_coreBoundarySphere_true_not_mem_retainedCore
    (y : Sphere 2) :
    standardNeckCutCap.tubes.coreBoundarySphere (PUnit.unit, true) y ∉
      standardNeckCutCap.retainedCore := by
  rintro ⟨q, hq⟩
  change neckCoreInclusion
    (standardNeckTubeSystem.coreBoundarySphere (PUnit.unit, true) y) = Sum.inl q at hq
  rw [neckCoreInclusion_of_not_mem_lower
    (not_mem_coreLower_of_mem_coreUpper (mem_coreUpper_coreBoundarySphere_true PUnit.unit y))]
    at hq
  exact Sum.inr_ne_inl hq

theorem standardNeckCutCap_core_ne_univ : standardNeckCutCap.tubes.core ≠ Set.univ := by
  obtain ⟨x, hx⟩ := standardNeckTubeSystem_removedBand_nonempty
  have hxnot : x ∉ standardNeckCutCap.tubes.core := fun hmem => by
    rw [TubeSystem.core, Set.mem_compl_iff] at hmem
    exact hmem (Set.mem_iUnion.mpr ⟨PUnit.unit, hx⟩)
  intro hc
  exact hxnot (by rw [hc]; exact Set.mem_univ x)

theorem standardNeckCutCap_nondegenerate :
    Nonempty standardNeckCutCap.tubes.Index ∧ standardNeckCutCap.tubes.core ≠ Set.univ ∧
      (standardNeckTubeSystem.removedBand PUnit.unit).Nonempty ∧
      standardNeckCutCap.tubes.boundarySphere (PUnit.unit, false) ≠
        standardNeckCutCap.tubes.boundarySphere (PUnit.unit, true) :=
  ⟨standardNeckTubeSystem_index_nonempty, standardNeckCutCap_core_ne_univ,
    standardNeckTubeSystem_removedBand_nonempty,
    standardNeckTubeSystem_boundarySphere_ne⟩

structure StandardNeckCutCapInputs where
  cylinderEmbedding : ∃ g : Sphere 2 × ℝ → Sphere 3,
    IsSmoothEmbedding ((𝓡 2).prod 𝓘(ℝ)) ThreeModel ∞ g ∧
      ∀ z : TubeDomain, g (z.1, (z.2 : ℝ)) = standardNeckTubeFun z
  [coreChartsModel : ChartedSpace
    DifferentialGeometry.Manifold.EuclideanHalfSpaceProdModel standardNeckTubeSystem.core]
  [coreSmoothModel : IsManifold ((𝓡 2).prod (𝓡∂ 1)) ∞ standardNeckTubeSystem.core]
  core_induced_model : IsSmoothEmbedding ((𝓡 2).prod (𝓡∂ 1)) ThreeModel ∞
    (Subtype.val : standardNeckTubeSystem.core → Sphere 3)
  core_boundary_model : ((𝓡 2).prod (𝓡∂ 1)).boundary standardNeckTubeSystem.core =
    ⋃ b : standardNeckTubeSystem.Boundary, Set.range (standardNeckTubeSystem.coreBoundarySphere b)
  core_inclusion_model : IsSmoothEmbedding ((𝓡 2).prod (𝓡∂ 1)) ThreeModel ∞
    standardNeckCapping.coreInclusion
  cap_smooth :
    letI : ChartedSpace (EuclideanHalfSpace 3) ThreeBall := threeBallChartedSpace
    ∀ b, IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞ (standardNeckCapping.cap b)
  core_positive :
    letI : ChartedSpace (EuclideanHalfSpace 3) standardNeckTubeSystem.core :=
      DifferentialGeometry.Manifold.euclideanHalfSpaceProdChartedSpace standardNeckTubeSystem.core
    letI : IsManifold (𝓡∂ 3) ∞ standardNeckTubeSystem.core :=
      DifferentialGeometry.Manifold.euclideanHalfSpaceProd_isManifold standardNeckTubeSystem.core
    ∀ x : standardNeckTubeSystem.core, (𝓡∂ 3).IsInteriorPoint x →
      ∃ hi : Function.Bijective (mfderiv (𝓡∂ 3) ThreeModel
          (Subtype.val : standardNeckTubeSystem.core → Sphere 3) x),
      ∃ hj : Function.Bijective (mfderiv (𝓡∂ 3) ThreeModel
          standardNeckCapping.coreInclusion x),
        Orientation.map (Fin 3)
          ((LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) ThreeModel
            (Subtype.val : standardNeckTubeSystem.core → Sphere 3) x).toLinearMap hi).symm.trans
            (LinearEquiv.ofBijective
              (mfderiv (𝓡∂ 3) ThreeModel standardNeckCapping.coreInclusion x).toLinearMap hj))
          (sphereThreeStage.orientation.orientation x.1) =
            (sphereThreeStage.sum sphereThreeStage).orientation.orientation
              (standardNeckCapping.coreInclusion x)
  cap_positive :
    letI : ChartedSpace (EuclideanHalfSpace 3) ThreeBall := threeBallChartedSpace
    letI : IsManifold (𝓡∂ 3) ∞ ThreeBall := threeBall_isManifold
    ∀ b, ∀ x : ThreeBall, (𝓡∂ 3).IsInteriorPoint x →
    ∃ hi : Function.Bijective (mfderiv (𝓡∂ 3) ThreeModel
        (Subtype.val : ThreeBall → ThreeSpace) x),
    ∃ hj : Function.Bijective (mfderiv (𝓡∂ 3) ThreeModel (standardNeckCapping.cap b) x),
      Orientation.map (Fin 3)
        ((LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) ThreeModel
          (Subtype.val : ThreeBall → ThreeSpace) x).toLinearMap hi).symm.trans
          (LinearEquiv.ofBijective
            (mfderiv (𝓡∂ 3) ThreeModel (standardNeckCapping.cap b) x).toLinearMap hj))
        ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation) =
          (sphereThreeStage.sum sphereThreeStage).orientation.orientation
            (standardNeckCapping.cap b x)
  presentation_positive : ∀ x : Sphere 3 ⊕ Sphere 3,
    ∃ hf : Function.Bijective (mfderiv ThreeModel ThreeModel
        (Diffeomorph.refl ThreeModel (Sphere 3 ⊕ Sphere 3) ∞) x),
      Orientation.map (Fin 3)
        (LinearEquiv.ofBijective (mfderiv ThreeModel ThreeModel
          (Diffeomorph.refl ThreeModel (Sphere 3 ⊕ Sphere 3) ∞) x).toLinearMap hf)
        ((sphereThreeStage.sum sphereThreeStage).orientation.orientation x) =
          Sum.elim (fun q => sphereThreeStage.orientation.orientation q)
            (fun d => sphereThreeStage.orientation.orientation d) x :=
    fun x => presentation_positive_refl_sum sphereThreeStage sphereThreeStage x

private theorem standardNeckTubeIsSmoothEmbedding_of_inputs (h : StandardNeckCutCapInputs) :
    standardNeckTubeIsSmoothEmbedding := by
  obtain ⟨g, hg, hsub⟩ := h.cylinderEmbedding
  exact standardNeckTubeIsSmoothEmbedding_of_cylinder_isSmoothEmbedding g hg hsub

def standardNeckCutCapTransition (h : StandardNeckCutCapInputs) :
    CutCapTransitionData sphereThreeStage sphereThreeStage sphereThreeStage
      (sphereThreeStage.sum sphereThreeStage) := by
  letI : Fact ((-2 : ℝ) < 2) := ⟨by norm_num⟩
  letI : ChartedSpace (EuclideanHalfSpace 3) ThreeBall := threeBallChartedSpace
  letI : IsManifold (𝓡∂ 3) ∞ ThreeBall := threeBall_isManifold
  letI : ChartedSpace DifferentialGeometry.Manifold.EuclideanHalfSpaceProdModel
      standardNeckCutCap.tubes.core := h.coreChartsModel
  letI : IsManifold ((𝓡 2).prod (𝓡∂ 1)) ∞ standardNeckCutCap.tubes.core := h.coreSmoothModel
  let coreCharts3 : ChartedSpace (EuclideanHalfSpace 3) standardNeckCutCap.tubes.core :=
    @DifferentialGeometry.Manifold.euclideanHalfSpaceProdChartedSpace
      standardNeckCutCap.tubes.core _ h.coreChartsModel
  letI : ChartedSpace (EuclideanHalfSpace 3) standardNeckCutCap.tubes.core := coreCharts3
  let coreSmooth3 : IsManifold (𝓡∂ 3) ∞ standardNeckCutCap.tubes.core :=
    @DifferentialGeometry.Manifold.euclideanHalfSpaceProd_isManifold
      standardNeckCutCap.tubes.core _ h.coreChartsModel h.coreSmoothModel
  letI : IsManifold (𝓡∂ 3) ∞ standardNeckCutCap.tubes.core := coreSmooth3
  exact CutCapTransitionData.mk
    (trace := standardNeckCutCap)
    (source_nonempty := sphereThreeStage_nonempty)
    (tube_smooth := standardNeckTubeSystem_tube_smooth
      (standardNeckTubeIsSmoothEmbedding_of_inputs h))
    (coreCharts := coreCharts3)
    (coreSmooth := coreSmooth3)
    (core_induced :=
      @DifferentialGeometry.Manifold.isSmoothEmbedding_coreSubtype_of_euclideanHalfSpaceProd
        (Sphere 3) _ _ (standardNeckCutCap.tubes.core) h.coreChartsModel h.coreSmoothModel
        h.core_induced_model)
    (core_boundary :=
      (@DifferentialGeometry.Manifold.euclideanHalfSpaceProd_boundary
        standardNeckCutCap.tubes.core _ h.coreChartsModel).trans h.core_boundary_model)
    (core_inclusion_smooth :=
      @DifferentialGeometry.Manifold.isSmoothEmbedding_coreInclusion_of_euclideanHalfSpaceProd
        (standardNeckCutCap.tubes.core) (Sphere 3 ⊕ Sphere 3) _ h.coreChartsModel
        h.coreSmoothModel _ _
        standardNeckCapping.coreInclusion h.core_inclusion_model)
    (cap_smooth := h.cap_smooth)
    (attaching := fun _ => Diffeomorph.refl (𝓡 2) (Sphere 2) ∞)
    (attaching_eq := fun _ => rfl)
    (core_positive := h.core_positive)
    (cap_positive := h.cap_positive)
    (presentation := Diffeomorph.refl ThreeModel (Sphere 3 ⊕ Sphere 3) ∞)
    (presentation_eq := rfl)
    (presentation_positive := fun x => by
      obtain ⟨hf, hfx⟩ := h.presentation_positive x
      refine ⟨hf, ?_⟩
      convert hfx using 2
      all_goals cases x <;> rfl)

theorem nonempty_cutCapTransitionData_of_standardNeckInputs (h : StandardNeckCutCapInputs) :
    Nonempty (CutCapTransitionData sphereThreeStage sphereThreeStage sphereThreeStage
      (sphereThreeStage.sum sphereThreeStage)) :=
  ⟨standardNeckCutCapTransition h⟩

theorem nonempty_smoothCutCapTransition_of_standardNeckInputs
    (h : StandardNeckCutCapInputs) :
    Nonempty (SmoothCutCapTransition sphereThreeStage sphereThreeStage sphereThreeStage
      (sphereThreeStage.sum sphereThreeStage)) := by
  obtain ⟨S⟩ := nonempty_cutCapTransitionData_of_standardNeckInputs h
  exact ⟨S.toSmoothCutCapTransition⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
