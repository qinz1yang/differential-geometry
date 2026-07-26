import DifferentialGeometry.Geometry.Metric.Sphere.PolarBij
import DifferentialGeometry.Geometry.Metric.Sphere.RoundIntrinsic
import DifferentialGeometry.Geometry.Exponential.DiagExpDerivative
import DifferentialGeometry.Geometry.Exponential.DiagInvFixed

/-!
# Radial logarithms on the round sphere

This file converts the ambient polar inverse into the intrinsic tangent vector
whose round exponential returns the original non-polar point.
-/

noncomputable section

open Bundle Filter Manifold Metric Module Set
open scoped Bundle Manifold Topology ContDiff InnerProductSpace
  RealInnerProductSpace

namespace DifferentialGeometry
namespace Geometry

open Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The ambient radial logarithm based at a unit vector. -/
def radialLog (p x : E) : E :=
  (spherePolarInv p x).1 • (spherePolarInv p x).2

/-- The ambient radial logarithm is smooth away from the two polar levels. -/
theorem radialLog_smooth (p : E) :
    ContDiffOn ℝ ∞ (radialLog p) {x : E | |⟪p, x⟫_ℝ| < 1} := by
  simpa only [radialLog] using
    (polarInv_smooth p).fst.smul (polarInv_smooth p).snd

/-- For a unit base point, the ambient radial logarithm is orthogonal to the
base radius. -/
theorem radialLog_orth {p : E} (hp : ‖p‖ = 1) (x : E) :
    ⟪p, radialLog p x⟫_ℝ = 0 := by
  have hpp : ⟪p, p⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_sq, hp, one_pow]
  simp only [radialLog, spherePolarInv, real_inner_smul_right,
    inner_sub_right, real_inner_smul_right, hpp]
  ring

/-- Away from the poles, the ambient radial logarithm has length equal to the
polar angle. -/
theorem radialLog_norm
    {p x : E} (hp : ‖p‖ = 1) (hx : ‖x‖ = 1)
    (hxp : x ≠ p) (hxnp : x ≠ -p) :
    ‖radialLog p x‖ = Real.arccos ⟪p, x⟫_ℝ := by
  obtain ⟨hr, _hpw, hwn, _hpolar⟩ := polar_decomp hp hx hxp hxnp
  simp only [radialLog, spherePolarInv, norm_smul, hwn, mul_one]
  rw [Real.norm_eq_abs, abs_of_pos hr.1]

/-- Away from the poles, polar reconstruction is a right inverse to the
ambient polar inverse. -/
theorem polar_right_inv
    {p x : E} (hp : ‖p‖ = 1) (hx : ‖x‖ = 1)
    (hxp : x ≠ p) (hxnp : x ≠ -p) :
    spherePolar p (spherePolarInv p x) = x := by
  obtain ⟨_hr, _hpw, _hwn, hpolar⟩ := polar_decomp hp hx hxp hxnp
  simpa only [spherePolarInv] using hpolar

variable [FiniteDimensional ℝ E]
variable {n : ℕ} [Fact (finrank ℝ E = n + 1)] [NeZero n]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

private instance sphereModel_neZero :
    NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) := by
  rw [finrank_euclideanSpace_fin]
  infer_instance

/-- The intrinsic round-sphere logarithm, totalized at the two poles. -/
def roundLog
    (p x : sphere (0 : E) 1) : EuclideanSpace ℝ (Fin n) :=
  (dInclEquiv (n := n) p).symm
    (((ℝ ∙ (p : E))ᗮ).orthogonalProjection (radialLog (p : E) (x : E)))

omit [FiniteDimensional ℝ E] [NeZero n] in
/-- The inclusion differential realizes the intrinsic logarithm as the
ambient radial logarithm. -/
theorem roundLog_val
    (p x : sphere (0 : E) 1) :
    dIncl (n := n) p (roundLog (n := n) p x) =
      radialLog (p : E) (x : E) := by
  let K : Submodule ℝ E := (ℝ ∙ (p : E))ᗮ
  have hmem : radialLog (p : E) (x : E) ∈ K := by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
    exact radialLog_orth (norm_eq_of_mem_sphere p) (x : E)
  rw [← dInclEquiv_coe (n := n) p]
  change
    (((dInclEquiv (n := n) p)
      ((dInclEquiv (n := n) p).symm
        (K.orthogonalProjection (radialLog (p : E) (x : E))))) : K) =
      radialLog (p : E) (x : E)
  rw [(dInclEquiv (n := n) p).apply_symm_apply]
  exact congrArg Subtype.val
    (K.orthogonalProjection_mem_subspace_eq_self
      ⟨radialLog (p : E) (x : E), hmem⟩)

omit [FiniteDimensional ℝ E] [NeZero n] in
/-- The round logarithm sends its base point to the zero tangent vector. -/
@[simp] theorem roundLog_self (p : sphere (0 : E) 1) :
    roundLog (n := n) p p = 0 := by
  apply mfderiv_coe_sphere_injective p
  change dIncl (n := n) p (roundLog (n := n) p p) =
    dIncl (n := n) p 0
  rw [roundLog_val, map_zero]
  have hpp : ⟪(p : E), (p : E)⟫_ℝ = 1 :=
    inner_self_eq_one_of_norm_eq_one (norm_eq_of_mem_sphere p)
  simp only [radialLog, spherePolarInv, hpp, Real.arccos_one, zero_smul]

omit [FiniteDimensional ℝ E] [NeZero n] in
/-- Away from both poles, the intrinsic round logarithm is smooth. -/
theorem roundLog_smooth_off (p : sphere (0 : E) 1) :
    ContMDiffOn (𝓡 n) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
      (roundLog (n := n) p) {x | x ≠ p ∧ x ≠ -p} := by
  intro x hx
  have hpNorm : ‖(p : E)‖ = 1 := norm_eq_of_mem_sphere p
  have hxNorm : ‖(x : E)‖ = 1 := norm_eq_of_mem_sphere x
  have habs : |⟪(p : E), (x : E)⟫_ℝ| < 1 := by
    rw [abs_lt]
    constructor
    · have hle :=
        neg_one_le_real_inner_of_norm_eq_one hpNorm hxNorm
      have hne : ⟪(p : E), (x : E)⟫_ℝ ≠ -1 := by
        intro heq
        have hpx :
            (p : E) = -(x : E) :=
          (inner_eq_neg_one_iff_of_norm_eq_one hpNorm hxNorm).mp heq
        have hxp : (x : E) = -(p : E) := by
          have hneg := congrArg Neg.neg hpx
          simpa only [neg_neg] using hneg.symm
        exact hx.2 (Subtype.ext hxp)
      exact lt_of_le_of_ne hle hne.symm
    · exact
        (inner_lt_one_iff_real_of_norm_eq_one hpNorm hxNorm).mpr
          (fun h => hx.1 (Subtype.ext h.symm))
  let A : Set E := {y : E | |⟪(p : E), y⟫_ℝ| < 1}
  have hAopen : IsOpen A := by
    exact isOpen_lt
      ((continuous_const.inner continuous_id).abs) continuous_const
  have hradAt :
      ContDiffAt ℝ ∞ (radialLog (p : E)) (x : E) :=
    (radialLog_smooth (p : E) (x : E) habs).contDiffAt
      (hAopen.mem_nhds habs)
  have hcoe :
      ContMDiffAt (𝓡 n) 𝓘(ℝ, E) ∞
        ((↑) : sphere (0 : E) 1 → E) x :=
    (contMDiff_coe_sphere (n := n)).contMDiffAt
  have hrad :
      ContMDiffAt (𝓡 n) 𝓘(ℝ, E) ∞
        (fun y : sphere (0 : E) 1 =>
          radialLog (p : E) (y : E)) x :=
    hradAt.contMDiffAt.comp x hcoe
  let L : E →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    (dInclEquiv (n := n) p).symm.toContinuousLinearMap.comp
      (((ℝ ∙ (p : E))ᗮ).orthogonalProjection)
  have hL :
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ L :=
    L.contDiff.contMDiff
  simpa only [roundLog, L] using (hL.contMDiffAt.comp x hrad).contMDiffWithinAt

omit [FiniteDimensional ℝ E] [NeZero n] in
/-- The round logarithm tends to zero at its base point. -/
theorem roundLog_tendsto (p : sphere (0 : E) 1) :
    Tendsto (roundLog (n := n) p) (𝓝 p) (𝓝 0) := by
  let a : sphere (0 : E) 1 → ℝ :=
    fun x => Real.arccos ⟪(p : E), (x : E)⟫_ℝ
  have hinner :
      Continuous (fun x : sphere (0 : E) 1 =>
        ⟪(p : E), (x : E)⟫_ℝ) :=
    continuous_const.inner
      (contMDiff_coe_sphere (m := ∞) (n := n)).continuous
  have ha : Tendsto a (𝓝 p) (𝓝 0) := by
    have h :=
      (Real.continuous_arccos.comp hinner).continuousAt (x := p)
    have hpp : ⟪(p : E), (p : E)⟫_ℝ = 1 :=
      inner_self_eq_one_of_norm_eq_one (norm_eq_of_mem_sphere p)
    simpa only [ContinuousAt, Function.comp_apply, a, hpp,
      Real.arccos_one] using h
  have hpneg : p ≠ -p := ne_neg_of_mem_unit_sphere ℝ p
  have hnotneg : ∀ᶠ x in 𝓝 p, x ≠ -p := by
    have hopen : IsOpen {x : sphere (0 : E) 1 | x ≠ -p} := by
      change IsOpen (({-p} : Set (sphere (0 : E) 1))ᶜ)
      exact isOpen_compl_singleton
    exact hopen.mem_nhds hpneg
  have hnorm :
      (fun x : sphere (0 : E) 1 =>
        ‖radialLog (p : E) (x : E)‖) =ᶠ[𝓝 p] a := by
    filter_upwards [hnotneg] with x hxneg
    by_cases hxp : x = p
    · subst x
      have hpp : ⟪(p : E), (p : E)⟫_ℝ = 1 :=
        inner_self_eq_one_of_norm_eq_one (norm_eq_of_mem_sphere p)
      simp only [radialLog, spherePolarInv, hpp, Real.arccos_one,
        zero_smul, norm_zero, a]
    · exact radialLog_norm
        (norm_eq_of_mem_sphere p) (norm_eq_of_mem_sphere x)
        (fun h => hxp (Subtype.ext h))
        (fun h => hxneg (Subtype.ext h))
  have hrad :
      Tendsto (fun x : sphere (0 : E) 1 =>
        radialLog (p : E) (x : E)) (𝓝 p) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact ha.congr' hnorm.symm
  let L : E →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    (dInclEquiv (n := n) p).symm.toContinuousLinearMap.comp
      (((ℝ ∙ (p : E))ᗮ).orthogonalProjection)
  have hL : Tendsto L (𝓝 0) (𝓝 0) := by
    have hLc : ContinuousAt L 0 := L.continuous.continuousAt
    simpa only [ContinuousAt, map_zero] using hLc
  simpa only [roundLog, L] using hL.comp hrad

variable
  [RiemannianBundle
    (fun p : sphere (0 : E) 1 => TangentSpace (𝓡 n) p)]
  [PseudoEMetricSpace (sphere (0 : E) 1)]
  [@CompleteSpace (sphere (0 : E) 1)
    (@PseudoEMetricSpace.toUniformSpace _ ‹PseudoEMetricSpace (sphere (0 : E) 1)›)]
  [IsRiemannianManifold (𝓡 n) (sphere (0 : E) 1)]
  [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
    (fun p : sphere (0 : E) 1 => TangentSpace (𝓡 n) p)]

/-- The intrinsic round exponential recovers every point other than the two
poles from its radial logarithm. -/
theorem round_exp_log
    (hEnorm : ∀ (y : sphere (0 : E) 1) (w : TangentSpace (𝓡 n) y),
      ‖w‖ₑ = ENNReal.ofReal
        (Real.sqrt ((roundMetric (E := E) (n := n)).inner y w w)))
    (p x : sphere (0 : E) 1) (hxp : x ≠ p) (hxnp : x ≠ -p) :
    expMapIntrinsic (I := 𝓡 n) (roundMetric (E := E) (n := n))
        hEnorm p (roundLog (n := n) p x) = x := by
  let r : ℝ := Real.arccos ⟪(p : E), (x : E)⟫_ℝ
  let w : E :=
    (Real.sin r)⁻¹ • ((x : E) - ⟪(p : E), (x : E)⟫_ℝ • (p : E))
  obtain ⟨hr, hpw, hwn, hpolar⟩ :=
    polar_decomp (norm_eq_of_mem_sphere p) (norm_eq_of_mem_sphere x)
      (fun h => hxp (Subtype.ext h)) (fun h => hxnp (Subtype.ext h))
  have hwmem : w ∈ (ℝ ∙ (p : E))ᗮ := by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
    exact hpw
  let v : TangentSpace (𝓡 n) p :=
    (dInclEquiv (n := n) p).symm ⟨w, hwmem⟩
  have hdv : dIncl (n := n) p v = w := by
    rw [← dInclEquiv_coe (n := n) p]
    exact congrArg Subtype.val
      ((dInclEquiv (n := n) p).apply_symm_apply ⟨w, hwmem⟩)
  have hv : ‖dIncl (n := n) p v‖ = 1 := by
    rw [hdv]
    exact hwn
  have hlog : roundLog (n := n) p x = r • v := by
    apply mfderiv_coe_sphere_injective p
    change dIncl (n := n) p (roundLog (n := n) p x) =
      dIncl (n := n) p (r • v)
    rw [roundLog_val, map_smul, hdv]
    rfl
  rw [hlog, round_exp_radial hEnorm p v hv r]
  apply Subtype.ext
  simpa only [greatCircle_val, hdv, spherePolar, r, w] using hpolar

/-- The intrinsic round exponential and logarithm cancel everywhere away from
the antipode, including at the base point. -/
theorem round_exp_log_ne
    (hEnorm : ∀ (y : sphere (0 : E) 1) (w : TangentSpace (𝓡 n) y),
      ‖w‖ₑ = ENNReal.ofReal
        (Real.sqrt ((roundMetric (E := E) (n := n)).inner y w w)))
    (p x : sphere (0 : E) 1) (hxnp : x ≠ -p) :
    expMapIntrinsic (I := 𝓡 n) (roundMetric (E := E) (n := n))
        hEnorm p (roundLog (n := n) p x) = x := by
  by_cases hxp : x = p
  · subst x
    rw [roundLog_self]
    change
      expMapIntrinsic (I := 𝓡 n) (roundMetric (E := E) (n := n))
        hEnorm p (0 : TangentSpace (𝓡 n) p) = p
    exact expMapIntrinsic_zero (roundMetric (E := E) (n := n)) hEnorm p
  · exact round_exp_log hEnorm p x hxp hxnp

private theorem log_eq_branch
    (hEnorm : ∀ (y : sphere (0 : E) 1) (w : TangentSpace (𝓡 n) y),
      ‖w‖ₑ = ENNReal.ofReal
        (Real.sqrt ((roundMetric (E := E) (n := n)).inner y w w)))
    (p : sphere (0 : E) 1) :
    roundLog (n := n) p =ᶠ[𝓝 p]
      (stdBranch (I := 𝓡 n) (roundMetric (E := E) (n := n))
        hEnorm p).fixedPD.symm := by
  let B :=
    stdBranch (I := 𝓡 n) (roundMetric (E := E) (n := n)) hEnorm p
  have hpneg : p ≠ -p := ne_neg_of_mem_unit_sphere ℝ p
  have hnotneg : ∀ᶠ x in 𝓝 p, x ≠ -p := by
    have hopen : IsOpen {x : sphere (0 : E) 1 | x ≠ -p} := by
      change IsOpen (({-p} : Set (sphere (0 : E) 1))ᶜ)
      exact isOpen_compl_singleton
    exact hopen.mem_nhds hpneg
  have hsource :
      ∀ᶠ x in 𝓝 p, roundLog (n := n) p x ∈ B.fixedPD.source :=
    roundLog_tendsto (n := n) p
      (B.fixedPD.open_source.mem_nhds B.fixedPD_zero_mem)
  filter_upwards [hnotneg, hsource] with x hxneg hxsrc
  by_cases hxp : x = p
  · subst x
    change roundLog (n := n) p p = B.fixedPD.symm p
    rw [roundLog_self]
    exact B.fixedPD_symm_center.symm
  · have hexp :=
      round_exp_log hEnorm p x hxp hxneg
    have hmap :
        B.fixedPD (roundLog (n := n) p x) = x := by
      simpa only [DiagInvBranch.fixedPD_apply] using hexp
    have hleft := B.fixedPD.left_inv hxsrc
    rw [hmap] at hleft
    exact hleft.symm

/-- The intrinsic round logarithm is smooth on the sphere with the antipode
removed. -/
theorem roundLog_smooth
    (hEnorm : ∀ (y : sphere (0 : E) 1) (w : TangentSpace (𝓡 n) y),
      ‖w‖ₑ = ENNReal.ofReal
        (Real.sqrt ((roundMetric (E := E) (n := n)).inner y w w)))
    (p : sphere (0 : E) 1) :
    ContMDiffOn (𝓡 n) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
      (roundLog (n := n) p) {x | x ≠ -p} := by
  let B :=
    stdBranch (I := 𝓡 n) (roundMetric (E := E) (n := n)) hEnorm p
  intro x hx
  by_cases hxp : x = p
  · subst x
    have hB :
        ContMDiffAt (𝓡 n) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
          B.fixedPD.symm p :=
      B.fixedPD.symm.contMDiffOn_toFun.contMDiffAt
        (B.fixedPD.open_target.mem_nhds B.fixedPD_center_mem)
    exact
      (hB.congr_of_eventuallyEq
        (log_eq_branch (n := n) hEnorm p)).contMDiffWithinAt
  · have hoff :
        ContMDiffWithinAt (𝓡 n) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
          (roundLog (n := n) p) {y | y ≠ p ∧ y ≠ -p} x :=
      roundLog_smooth_off (n := n) p x ⟨hxp, hx⟩
    have hopen : IsOpen {y : sphere (0 : E) 1 | y ≠ p ∧ y ≠ -p} := by
      change IsOpen
        (({p} : Set (sphere (0 : E) 1))ᶜ ∩
          (({-p} : Set (sphere (0 : E) 1))ᶜ))
      exact isOpen_compl_singleton.inter isOpen_compl_singleton
    exact (hoff.contMDiffAt (hopen.mem_nhds ⟨hxp, hx⟩)).contMDiffWithinAt

/-- At its base point, the differential of the intrinsic round logarithm is
the identity on the fixed round-sphere model space. -/
theorem roundLog_mfd_self
    (hEnorm : ∀ (y : sphere (0 : E) 1) (w : TangentSpace (𝓡 n) y),
      ‖w‖ₑ = ENNReal.ofReal
        (Real.sqrt ((roundMetric (E := E) (n := n)).inner y w w)))
    (p : sphere (0 : E) 1) :
    mfderiv (𝓡 n) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        (roundLog (n := n) p) p =
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by
  let logf : sphere (0 : E) 1 → EuclideanSpace ℝ (Fin n) :=
    roundLog (n := n) p
  let expf : EuclideanSpace ℝ (Fin n) → sphere (0 : E) 1 := fun u =>
    expMapIntrinsic (I := 𝓡 n) (roundMetric (E := E) (n := n))
      hEnorm p (show TangentSpace (𝓡 n) p from u)
  have hpneg : p ≠ -p := ne_neg_of_mem_unit_sphere ℝ p
  have hUopen : IsOpen {x : sphere (0 : E) 1 | x ≠ -p} := by
    change IsOpen (({-p} : Set (sphere (0 : E) 1))ᶜ)
    exact isOpen_compl_singleton
  have hlog :
      MDifferentiableAt (𝓡 n) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) logf p :=
    ((roundLog_smooth hEnorm p).contMDiffAt
      (hUopen.mem_nhds hpneg)).mdifferentiableAt (by simp)
  have hexp :
      MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡 n)
        expf (logf p) := by
    exact (intrinsicFiber_smooth (I := 𝓡 n)
      (roundMetric (E := E) (n := n)) hEnorm p).contMDiffAt.mdifferentiableAt
        (by simp)
  have hident : (expf ∘ logf) =ᶠ[𝓝 p] id := by
    refine eventuallyEq_of_mem (hUopen.mem_nhds hpneg) ?_
    intro x hx
    simpa only [expf, logf, Function.comp_apply, id_eq] using
      round_exp_log_ne hEnorm p x hx
  have hchain :=
    mfderiv_comp
      (I := 𝓡 n) (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (I'' := 𝓡 n) p hexp hlog
  have hp0 : logf p = 0 := by
    simp only [logf, roundLog_self]
  have hexp0 :
      mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡 n) expf 0 =
        ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by
    simpa only [expf] using
      mfderiv_expMapIntrinsic_at_zero (I := 𝓡 n)
        (roundMetric (E := E) (n := n)) hEnorm p
  rw [hident.mfderiv_eq, mfderiv_id, hp0, hexp0] at hchain
  ext v
  have hv := DFunLike.congr_fun hchain v
  simpa only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, logf] using hv.symm

end Geometry
end DifferentialGeometry
