import DifferentialGeometry.Geometry.Collapse.ZeroModel.SpaceFormDescend
import DifferentialGeometry.Topology.ThreeManifold.PoincareStandardDiscardedModels
import DifferentialGeometry.Topology.VectorBundle.RankOneQuotient.Descend

/-!
# The equatorial band of `ℝP³` and the antipodal parametrisation

Lane LFR54-QUOT (Q1, the closed `ℝP³` clause of LFR52, (LFR52.1)). On `P = projectiveThreeSpaceLift`
(the universe lift of `S³ / ±1`):
* `bandFn [w] = w₃²` is smooth (`contMDiff_bandFn`) with regular level `½`
  (`mfderiv_bandFn_ne_zero`), so the equatorial band `{w₃² ≤ ½}` is a regular sublevel;
* `projTheta (x, t) = [(x, t) / √(1 + t²)]` is a smooth map `S² × ℝ → P`, invariant under
  `(x, t) ↦ (-x, -t)` (`projTheta_neg`), with `w₃² ≤ ½ ↔ |t| ≤ 1`
  (`bandFn_projTheta_le_half_iff`);
* for an antipodally equivariant unit map `ν : S² → TotalSpace F V`, `projInvMap ν` inverts it:
  `[w] ↦ (w₃ / ‖w'‖) • ν (w' / ‖w'‖)` with `w' = (w₀, w₁, w₂)`, smooth off `{w' = 0}`
  (`contMDiffAt_projInvMap`).
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter Function Module Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse.ZeroModel.Projective

open DifferentialGeometry.Topology DifferentialGeometry.Geometry.Collapse.ZeroModel.SpaceForm
open DifferentialGeometry.Topology.VectorBundle.RankOneQuotient

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E4" => EuclideanSpace ℝ (Fin 4)
local notation "S2" => sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
local notation "S3" => sphere (0 : EuclideanSpace ℝ (Fin 4)) 1

/-- The antipodal group `±1` of `S³`. -/
abbrev rpGroup : SphericalSpaceFormGroup := SphericalSpaceFormGroup.antipodal

/-- `ℝ⁴` has dimension `3 + 1`. -/
local instance finrankFourFactProj_LFR54QUOT : Fact (finrank ℝ E4 = 3 + 1) := ⟨by simp⟩

/-! ### `ℝ⁴ = ℝ³ × ℝ` -/

/-- `(v, s) ∈ ℝ³ × ℝ` as a point of `ℝ⁴`. -/
def e4Join (v : E3) (s : ℝ) : E4 := !₂[v 0, v 1, v 2, s]

/-- The first three coordinates of a point of `ℝ⁴`. -/
def e4Head (w : E4) : E3 := !₂[w 0, w 1, w 2]

theorem norm_sq_e4Join (v : E3) (s : ℝ) : ‖e4Join v s‖ ^ 2 = ‖v‖ ^ 2 + s ^ 2 := by
  simp [e4Join, EuclideanSpace.norm_sq_eq, Fin.sum_univ_four, Fin.sum_univ_three]

theorem norm_sq_eq_head_last (w : E4) : ‖w‖ ^ 2 = ‖e4Head w‖ ^ 2 + w 3 ^ 2 := by
  simp [e4Head, EuclideanSpace.norm_sq_eq, Fin.sum_univ_four, Fin.sum_univ_three]

theorem e4Join_head_last (w : E4) : e4Join (e4Head w) (w 3) = w := by
  ext i
  fin_cases i <;> simp [e4Join, e4Head]

theorem e4Head_e4Join (v : E3) (s : ℝ) : e4Head (e4Join v s) = v := by
  ext i
  fin_cases i <;> simp [e4Join, e4Head]

theorem e4Join_last (v : E3) (s : ℝ) : (e4Join v s) 3 = s := by
  simp [e4Join]

theorem e4Head_smul (c : ℝ) (w : E4) : e4Head (c • w) = c • e4Head w := by
  ext i
  fin_cases i <;> simp [e4Head]

theorem smul_e4Join (c : ℝ) (v : E3) (s : ℝ) : c • e4Join v s = e4Join (c • v) (c * s) := by
  ext i
  fin_cases i <;> simp [e4Join]

theorem e4Head_neg (w : E4) : e4Head (-w) = -e4Head w := by
  ext i
  fin_cases i <;> simp [e4Head]

theorem e4Join_neg (v : E3) (s : ℝ) : e4Join (-v) (-s) = -e4Join v s := by
  ext i
  fin_cases i <;> simp [e4Join]

theorem contDiff_e4Join : ContDiff ℝ ∞ (fun q : E3 × ℝ => e4Join q.1 q.2) := by
  rw [contDiff_piLp]
  intro i
  fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue]
  · exact (EuclideanSpace.proj (0 : Fin 3) : E3 →L[ℝ] ℝ).contDiff.comp contDiff_fst
  · exact (EuclideanSpace.proj (1 : Fin 3) : E3 →L[ℝ] ℝ).contDiff.comp contDiff_fst
  · exact (EuclideanSpace.proj (2 : Fin 3) : E3 →L[ℝ] ℝ).contDiff.comp contDiff_fst
  · exact contDiff_snd

theorem contDiff_e4Head : ContDiff ℝ ∞ e4Head := by
  rw [contDiff_piLp]
  intro i
  fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue]
  · exact (EuclideanSpace.proj (0 : Fin 4) : E4 →L[ℝ] ℝ).contDiff
  · exact (EuclideanSpace.proj (1 : Fin 4) : E4 →L[ℝ] ℝ).contDiff
  · exact (EuclideanSpace.proj (2 : Fin 4) : E4 →L[ℝ] ℝ).contDiff

theorem norm_sq_e4Head_sphere (x : S3) : ‖e4Head (x : E4)‖ ^ 2 = 1 - (x : E4) 3 ^ 2 := by
  have h := norm_sq_eq_head_last (x : E4)
  rw [mem_sphere_zero_iff_norm.mp x.2, one_pow] at h
  linarith

theorem norm_sphere_two (x : S2) : ‖(x : E3)‖ = 1 := mem_sphere_zero_iff_norm.mp x.2

/-! ### The antipodal quotient and its universe lift -/

theorem antipodal_neg_mem : (LinearIsometryEquiv.neg ℝ : E4 ≃ₗᵢ[ℝ] E4) ∈ rpGroup.group :=
  Or.inr rfl

theorem rp_projection_neg (x : S3) : rpGroup.projection (-x) = rpGroup.projection x := by
  rw [SphericalSpaceFormGroup.projection_eq_iff]
  refine ⟨⟨LinearIsometryEquiv.neg ℝ, antipodal_neg_mem⟩, ?_⟩
  apply Subtype.ext
  simp [DifferentialGeometry.Geometry.sphereDiffeo_coe]

theorem eq_or_eq_neg_of_rp_projection_eq {x y : S3} (h : rpGroup.projection x = rpGroup.projection y) :
    y = x ∨ y = -x := by
  obtain ⟨γ, hγ⟩ := (rpGroup.projection_eq_iff x y).mp h
  rcases γ.2 with h1 | h1
  · left
    rw [← hγ]
    apply Subtype.ext
    rw [DifferentialGeometry.Geometry.sphereDiffeo_coe, h1]
    rfl
  · right
    rw [← hγ]
    apply Subtype.ext
    rw [DifferentialGeometry.Geometry.sphereDiffeo_coe, h1]
    rfl

/-- `S³ / ±1` into its universe lift `projectiveThreeSpaceLift`. -/
def rpUp (q : rpGroup.Orbit) : projectiveThreeSpaceLift.{u}.Carrier :=
  ClosedOrientedManifold.uliftDiffeomorph.{0, u} rpGroup.manifold.toClosedOrientedManifold q

/-- The inverse of `rpUp`. -/
def rpDown (y : projectiveThreeSpaceLift.{u}.Carrier) : rpGroup.Orbit :=
  (ClosedOrientedManifold.uliftDiffeomorph.{0, u} rpGroup.manifold.toClosedOrientedManifold).symm y

theorem rpDown_rpUp (q : rpGroup.Orbit) : rpDown.{u} (rpUp q) = q :=
  (ClosedOrientedManifold.uliftDiffeomorph.{0, u}
    rpGroup.manifold.toClosedOrientedManifold).symm_apply_apply q

theorem rpUp_rpDown (y : projectiveThreeSpaceLift.{u}.Carrier) : rpUp (rpDown y) = y :=
  (ClosedOrientedManifold.uliftDiffeomorph.{0, u}
    rpGroup.manifold.toClosedOrientedManifold).apply_symm_apply y

theorem contMDiff_rpUp : ContMDiff (𝓡 3) (𝓡 3) ∞ rpUp.{u} :=
  (ClosedOrientedManifold.uliftDiffeomorph.{0, u} rpGroup.manifold.toClosedOrientedManifold).contMDiff

theorem contMDiff_rpDown : ContMDiff (𝓡 3) (𝓡 3) ∞ rpDown.{u} :=
  (ClosedOrientedManifold.uliftDiffeomorph.{0, u}
    rpGroup.manifold.toClosedOrientedManifold).symm.contMDiff

theorem exists_rpUp (y : projectiveThreeSpaceLift.{u}.Carrier) :
    ∃ x : S3, y = rpUp (rpGroup.projection x) := by
  obtain ⟨x, hx⟩ := rpGroup.projection_surjective (rpDown y)
  exact ⟨x, by rw [hx, rpUp_rpDown]⟩

theorem contMDiff_rpUp_projection :
    ContMDiff (𝓡 3) (𝓡 3) ∞ (fun x : S3 => rpUp.{u} (rpGroup.projection x)) :=
  contMDiff_rpUp.comp rpGroup.projection_isLocalDiffeomorph.contMDiff

/-- Descent of a fibrewise constant map on `S³` to `P`, smooth where the original map is. -/
theorem contMDiffAt_orbitLift_rpDown {EN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
    {HN : Type*} [TopologicalSpace HN] {J : ModelWithCorners ℝ EN HN} {N : Type*}
    [TopologicalSpace N] [ChartedSpace HN N] (f : S3 → N)
    (hf : ∀ x y, rpGroup.projection x = rpGroup.projection y → f x = f y) (x : S3)
    (hx : ContMDiffAt (𝓡 3) J ∞ f x) :
    ContMDiffAt (𝓡 3) J ∞ (fun y => orbitLift rpGroup f hf (rpDown.{u} y))
      (rpUp (rpGroup.projection x)) := by
  have h := contMDiffAt_orbitLift rpGroup f hf x hx
  rw [← rpDown_rpUp.{u} (rpGroup.projection x)] at h
  exact h.comp _ (contMDiff_rpDown _)

/-! ### The band function -/

/-- `w₃²` on `S³`. -/
def bandSphere (x : S3) : ℝ := (x : E4) 3 ^ 2

theorem bandSphere_invariant (x y : S3) (h : rpGroup.projection x = rpGroup.projection y) :
    bandSphere x = bandSphere y := by
  rcases eq_or_eq_neg_of_rp_projection_eq h with rfl | rfl
  · rfl
  · simp [bandSphere]

/-- `[w] ↦ w₃²` on `P`. -/
def bandFn (y : projectiveThreeSpaceLift.{u}.Carrier) : ℝ :=
  orbitLift rpGroup bandSphere bandSphere_invariant (rpDown y)

theorem bandFn_rpUp (x : S3) : bandFn.{u} (rpUp (rpGroup.projection x)) = (x : E4) 3 ^ 2 := by
  rw [bandFn, rpDown_rpUp]
  rfl

theorem contMDiff_bandFn : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ bandFn.{u} := by
  intro y
  obtain ⟨x, rfl⟩ := exists_rpUp y
  have hs : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ bandSphere :=
    (((EuclideanSpace.proj (3 : Fin 4) : E4 →L[ℝ] ℝ).contDiff.pow 2).contMDiff).comp
      contMDiff_coe_sphere
  exact contMDiffAt_orbitLift_rpDown bandSphere bandSphere_invariant x (hs x)

theorem continuous_bandFn : Continuous bandFn.{u} := contMDiff_bandFn.continuous

/-- The level `½` of `bandFn` is regular (for any linear change of the model). -/
theorem mfderiv_bandFn_ne_zero {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    (e : E3 ≃L[ℝ] E') (y : projectiveThreeSpaceLift.{u}.Carrier) (hy : bandFn y = 1 / 2) :
    mfderiv ((𝓡 3).transContinuousLinearEquiv e) 𝓘(ℝ, ℝ) bandFn y ≠ 0 := by
  obtain ⟨x, rfl⟩ := exists_rpUp y
  rw [bandFn_rpUp] at hy
  set w : E4 := (x : E4)
  set w₃ : ℝ := w 3
  set h := e4Head w
  have hh : ‖h‖ ^ 2 = 1 / 2 := by
    have := norm_sq_e4Head_sphere x
    rw [hy] at this
    rw [this]
    norm_num
  have hhpos : 0 < ‖h‖ := by
    rcases (norm_nonneg h).lt_or_eq with h1 | h1
    · exact h1
    · rw [← h1] at hh
      norm_num at hh
  have hw₃ : w₃ ≠ 0 := by
    intro h0
    change w₃ ^ 2 = 1 / 2 at hy
    rw [h0] at hy
    norm_num at hy
  let c : ℝ → E4 := fun s =>
    e4Join ((Real.cos s - w₃ / ‖h‖ * Real.sin s) • h) (w₃ * Real.cos s + ‖h‖ * Real.sin s)
  have hc : ∀ s, c s ∈ S3 := by
    intro s
    rw [mem_sphere_zero_iff_norm]
    have h2 : ‖c s‖ ^ 2 = 1 := by
      simp only [c]
      rw [norm_sq_e4Join, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      have hs := Real.sin_sq_add_cos_sq s
      have hw := norm_sq_e4Head_sphere x
      change ‖h‖ ^ 2 = 1 - w₃ ^ 2 at hw
      field_simp
      nlinarith [hs, hw]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h2
  have hcs : ContDiff ℝ ∞ c := by
    refine contDiff_e4Join.comp (ContDiff.prodMk ?_ ?_)
    · exact (Real.contDiff_cos.sub (contDiff_const.mul Real.contDiff_sin)).smul contDiff_const
    · exact (contDiff_const.mul Real.contDiff_cos).add (contDiff_const.mul Real.contDiff_sin)
  let γ : ℝ → projectiveThreeSpaceLift.{u}.Carrier := fun s =>
    rpUp (rpGroup.projection (Set.codRestrict c _ hc s))
  have hγ : ContMDiff 𝓘(ℝ, ℝ) (𝓡 3) ∞ γ :=
    contMDiff_rpUp_projection.comp (hcs.contMDiff.codRestrict_sphere hc)
  have hγ0 : γ 0 = rpUp (rpGroup.projection x) := by
    change rpUp (rpGroup.projection ⟨c 0, hc 0⟩) = _
    congr 2
    apply Subtype.ext
    change e4Join ((Real.cos 0 - w₃ / ‖h‖ * Real.sin 0) • h)
      (w₃ * Real.cos 0 + ‖h‖ * Real.sin 0) = w
    rw [Real.cos_zero, Real.sin_zero, mul_zero, sub_zero, one_smul, mul_one, mul_zero, add_zero]
    exact e4Join_head_last w
  have hval : (fun s => bandFn (γ s)) = fun s => (w₃ * Real.cos s + ‖h‖ * Real.sin s) ^ 2 := by
    funext s
    change bandFn (rpUp (rpGroup.projection ⟨c s, hc s⟩)) = _
    rw [bandFn_rpUp]
    change (c s) 3 ^ 2 = _
    simp only [c, e4Join_last]
  have hD : HasDerivAt (fun s => bandFn (γ s)) (2 * w₃ * ‖h‖) 0 := by
    rw [hval]
    have h1 := (((Real.hasDerivAt_cos 0).const_mul w₃).add
      ((Real.hasDerivAt_sin 0).const_mul ‖h‖)).pow 2
    convert h1 using 1
    simp
  apply DifferentialGeometry.Geometry.Collapse.mfderiv_ne_zero_of_curve
    ((e.contMDiff_transContinuousLinearEquiv_left.mpr contMDiff_bandFn).mdifferentiableAt
      (by simp)) hγ0
    ((e.contMDiff_transContinuousLinearEquiv_right.mpr hγ).mdifferentiable (by simp) 0) hD
  exact mul_ne_zero (mul_ne_zero two_ne_zero hw₃) hhpos.ne'

/-! ### The antipodal parametrisation `S² × ℝ → P` -/

theorem projParam_mem (x : S2) (t : ℝ) : (√(1 + t ^ 2))⁻¹ • e4Join x t ∈ S3 := by
  rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  have h := norm_sq_e4Join (x : E3) t
  rw [norm_sphere_two x, one_pow] at h
  rw [← Real.sqrt_sq (norm_nonneg (e4Join (x : E3) t)), h]
  exact inv_mul_cancel₀ (Real.sqrt_pos.mpr (by positivity)).ne'

/-- The point `(x, t) / √(1 + t²)` of `S³`. -/
def projParamSphere (q : S2 × ℝ) : S3 := ⟨_, projParam_mem q.1 q.2⟩

/-- **The antipodal parametrisation** `(x, t) ↦ [(x, t) / √(1 + t²)]`. -/
def projTheta (q : S2 × ℝ) : projectiveThreeSpaceLift.{u}.Carrier :=
  rpUp (rpGroup.projection (projParamSphere q))

theorem contMDiff_projTheta : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ projTheta.{u} := by
  have hg : ContDiff ℝ ∞ (fun q : E3 × ℝ => (√(1 + q.2 ^ 2))⁻¹ • e4Join q.1 q.2) := by
    have hs : ContDiff ℝ ∞ (fun q : E3 × ℝ => (√(1 + q.2 ^ 2))⁻¹) := by
      refine ContDiff.inv ((contDiff_const.add (contDiff_snd.pow 2)).sqrt fun q => ?_) fun q => ?_
      · positivity
      · exact (Real.sqrt_pos.mpr (by positivity)).ne'
    exact hs.smul contDiff_e4Join
  have hin : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E3 × ℝ) ∞
      (fun q : S2 × ℝ => ((q.1 : E3), q.2)) :=
    (contMDiff_coe_sphere.comp contMDiff_fst).prodMk_space contMDiff_snd
  have hs : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ projParamSphere :=
    (hg.contMDiff.comp hin).codRestrict_sphere fun q => projParam_mem q.1 q.2
  exact contMDiff_rpUp_projection.comp hs

theorem projTheta_neg (x : S2) (t : ℝ) : projTheta.{u} (-x, -t) = projTheta.{u} (x, t) := by
  have hpt : projParamSphere (-x, -t) = -projParamSphere (x, t) := by
    apply Subtype.ext
    change (√(1 + (-t) ^ 2))⁻¹ • e4Join ((-x : S2) : E3) (-t) = -((√(1 + t ^ 2))⁻¹ • e4Join x t)
    rw [neg_sq, coe_neg_sphere, e4Join_neg, smul_neg]
  rw [projTheta, projTheta, hpt, rp_projection_neg]

theorem bandFn_projTheta (q : S2 × ℝ) : bandFn.{u} (projTheta q) = q.2 ^ 2 / (1 + q.2 ^ 2) := by
  rw [projTheta, bandFn_rpUp]
  change ((√(1 + q.2 ^ 2))⁻¹ • e4Join q.1 q.2) 3 ^ 2 = _
  rw [PiLp.smul_apply, e4Join_last, smul_eq_mul, mul_pow, inv_pow,
    Real.sq_sqrt (by positivity)]
  field_simp

theorem bandFn_projTheta_le_half_iff {q : S2 × ℝ} : bandFn.{u} (projTheta q) ≤ 1 / 2 ↔ |q.2| ≤ 1 := by
  rw [bandFn_projTheta, div_le_iff₀ (by positivity), ← sq_le_one_iff_abs_le_one]
  constructor <;> intro h <;> nlinarith

theorem bandFn_projTheta_lt_one (q : S2 × ℝ) : bandFn.{u} (projTheta q) < 1 := by
  rw [bandFn_projTheta, div_lt_one (by positivity)]
  linarith

/-! ### The unit vector of a nonzero vector of `ℝ³` -/

/-- `v / ‖v‖` (and a fixed point at `0`). -/
def unitS2 (v : E3) : S2 :=
  if hv : v = 0 then ⟨EuclideanSpace.single 0 1, by simp⟩ else
    ⟨‖v‖⁻¹ • v, by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]⟩

theorem coe_unitS2 {v : E3} (hv : v ≠ 0) : (unitS2 v : E3) = ‖v‖⁻¹ • v := by
  simp only [unitS2, hv, ↓reduceDIte]

theorem unitS2_neg {v : E3} (hv : v ≠ 0) : unitS2 (-v) = -unitS2 v := by
  apply Subtype.ext
  rw [coe_neg_sphere, coe_unitS2 hv, coe_unitS2 (neg_ne_zero.mpr hv), norm_neg, smul_neg]

theorem unitS2_smul {c : ℝ} (hc : 0 < c) {v : E3} (hv : v ≠ 0) : unitS2 (c • v) = unitS2 v := by
  apply Subtype.ext
  rw [coe_unitS2 hv, coe_unitS2 (smul_ne_zero hc.ne' hv), norm_smul, Real.norm_of_nonneg hc.le,
    smul_smul, mul_inv_rev, mul_assoc, inv_mul_cancel₀ hc.ne', mul_one]

theorem unitS2_coe (x : S2) : unitS2 (x : E3) = x := by
  have hx : (x : E3) ≠ 0 := ne_zero_of_mem_unit_sphere x
  apply Subtype.ext
  rw [coe_unitS2 hx, norm_sphere_two x, inv_one, one_smul]

theorem contMDiffAt_unitS2 {v : E3} (hv : v ≠ 0) :
    ContMDiffAt 𝓘(ℝ, E3) (𝓡 2) ∞ unitS2 v := by
  let U : TopologicalSpace.Opens E3 := ⟨{w | w ≠ 0}, isOpen_ne⟩
  have hmem : ∀ w : U, ‖(w : E3)‖⁻¹ • (w : E3) ∈ sphere (0 : E3) 1 := by
    intro w
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr w.2)]
  have hval : ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, E3) ∞ (fun w : U => ‖(w : E3)‖⁻¹ • (w : E3)) := by
    intro w
    have hn : ContDiffAt ℝ ∞ (fun z : E3 => ‖z‖⁻¹) w :=
      (contDiffAt_norm ℝ w.2).inv (norm_ne_zero_iff.mpr w.2)
    exact (contMDiffAt_subtype_iff (f := fun z : E3 => ‖z‖⁻¹ • z)).mpr
      (hn.smul contDiffAt_id).contMDiffAt
  have hc : ContMDiff 𝓘(ℝ, E3) (𝓡 2) ∞ (fun w : U => unitS2 (w : E3)) := by
    refine (hval.codRestrict_sphere hmem).congr fun w => ?_
    apply Subtype.ext
    rw [coe_unitS2 w.2]
    rfl
  exact contMDiffAt_subtype_iff.mp (hc ⟨v, hv⟩)

/-! ### The inverse map `P → TotalSpace F V` -/

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ b, NormedAddCommGroup (V b)] [∀ b, InnerProductSpace ℝ (V b)]
  [FiberBundle F V] [VectorBundle ℝ F V]

/-- On `S³`: `(w₃ / ‖w'‖) • ν (w' / ‖w'‖)`, `w' = (w₀, w₁, w₂)` (a constant at `w' = 0`). -/
def projSphereMap (ν : S2 → TotalSpace F V) (x : S3) : TotalSpace F V :=
  if e4Head (x : E4) = 0 then ν (unitS2 0)
  else rankOneParam ν (unitS2 (e4Head (x : E4)), (x : E4) 3 / ‖e4Head (x : E4)‖)

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace B]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V] in
theorem projSphereMap_of_ne (ν : S2 → TotalSpace F V) {x : S3} (hx : e4Head (x : E4) ≠ 0) :
    projSphereMap ν x =
      rankOneParam ν (unitS2 (e4Head (x : E4)), (x : E4) 3 / ‖e4Head (x : E4)‖) := by
  rw [projSphereMap, ite_eq_right hx]

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace B]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V] in
theorem projSphereMap_invariant (ν : S2 → TotalSpace F V)
    (hνneg : ∀ x, ν (-x) = ⟨(ν x).proj, -(ν x).2⟩) (x y : S3)
    (h : rpGroup.projection x = rpGroup.projection y) : projSphereMap ν x = projSphereMap ν y := by
  rcases eq_or_eq_neg_of_rp_projection_eq h with rfl | rfl
  · rfl
  by_cases hx : e4Head (x : E4) = 0
  · have hy : e4Head ((-x : S3) : E4) = 0 := by rw [coe_neg_sphere, e4Head_neg, hx, neg_zero]
    rw [projSphereMap, projSphereMap, ite_eq_left hx, ite_eq_left hy]
  · have hy : e4Head ((-x : S3) : E4) ≠ 0 := by
      rw [coe_neg_sphere, e4Head_neg]
      exact neg_ne_zero.mpr hx
    rw [projSphereMap_of_ne ν hx, projSphereMap_of_ne ν hy]
    have h1 : unitS2 (e4Head ((-x : S3) : E4)) = -unitS2 (e4Head (x : E4)) := by
      rw [coe_neg_sphere, e4Head_neg, unitS2_neg hx]
    have h2 : ((-x : S3) : E4) 3 / ‖e4Head ((-x : S3) : E4)‖ =
        -((x : E4) 3 / ‖e4Head (x : E4)‖) := by
      rw [coe_neg_sphere, e4Head_neg, norm_neg, PiLp.neg_apply, neg_div]
    rw [h1, h2]
    exact (rankOneParam_deck ν (fun p => -p) hνneg _ _).symm

/-- **The inverse map** `P → TotalSpace F V`. -/
def projInvMap (ν : S2 → TotalSpace F V) (hνneg : ∀ x, ν (-x) = ⟨(ν x).proj, -(ν x).2⟩)
    (y : projectiveThreeSpaceLift.{u}.Carrier) : TotalSpace F V :=
  orbitLift rpGroup (projSphereMap ν) (projSphereMap_invariant ν hνneg) (rpDown y)

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace B]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V] in
theorem projInvMap_rpUp (ν : S2 → TotalSpace F V)
    (hνneg : ∀ x, ν (-x) = ⟨(ν x).proj, -(ν x).2⟩) (x : S3) :
    projInvMap.{u} ν hνneg (rpUp (rpGroup.projection x)) = projSphereMap ν x := by
  rw [projInvMap, rpDown_rpUp]
  rfl

theorem contMDiffAt_projInvMap (ν : S2 → TotalSpace F V)
    (hν : ContMDiff (𝓡 2) (IB.prod 𝓘(ℝ, F)) ∞ ν)
    (hνneg : ∀ x, ν (-x) = ⟨(ν x).proj, -(ν x).2⟩) {x : S3} (hx : e4Head (x : E4) ≠ 0) :
    ContMDiffAt (𝓡 3) (IB.prod 𝓘(ℝ, F)) ∞ (projInvMap.{u} ν hνneg)
      (rpUp (rpGroup.projection x)) := by
  have hhead : ContMDiff (𝓡 3) 𝓘(ℝ, E3) ∞ (fun x : S3 => e4Head (x : E4)) :=
    contDiff_e4Head.contMDiff.comp contMDiff_coe_sphere
  have hu : ContMDiffAt (𝓡 3) (𝓡 2) ∞ (fun x : S3 => unitS2 (e4Head (x : E4))) x :=
    (contMDiffAt_unitS2 hx).comp x (hhead x)
  have ht : ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) ∞
      (fun x : S3 => (x : E4) 3 / ‖e4Head (x : E4)‖) x := by
    have h1 : ContDiffAt ℝ ∞ (fun w : E4 => w 3 / ‖e4Head w‖) (x : E4) :=
      (EuclideanSpace.proj (3 : Fin 4) : E4 →L[ℝ] ℝ).contDiff.contDiffAt.div
        ((contDiffAt_norm ℝ hx).comp _ contDiff_e4Head.contDiffAt) (norm_ne_zero_iff.mpr hx)
    exact h1.contMDiffAt.comp x (contMDiff_coe_sphere x)
  have hm : ContMDiffAt (𝓡 3) (IB.prod 𝓘(ℝ, F)) ∞
      (fun x : S3 => rankOneParam ν (unitS2 (e4Head (x : E4)), (x : E4) 3 / ‖e4Head (x : E4)‖))
      x :=
    (DifferentialGeometry.Geometry.Collapse.contMDiff_totalSpace_smul _).comp x
      (ht.prodMk ((hν _).comp x hu))
  have hcont : Continuous fun x : S3 => e4Head (x : E4) := hhead.continuous
  have hs : ContMDiffAt (𝓡 3) (IB.prod 𝓘(ℝ, F)) ∞ (projSphereMap ν) x := by
    apply hm.congr_of_eventuallyEq
    filter_upwards [hcont.continuousAt.eventually_ne hx] with x' hx'
    exact projSphereMap_of_ne ν hx'
  exact contMDiffAt_orbitLift_rpDown (projSphereMap ν) (projSphereMap_invariant ν hνneg) x hs

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace B]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V] in
/-- `projInvMap ∘ projTheta = Φ`. -/
theorem projInvMap_projTheta (ν : S2 → TotalSpace F V)
    (hνneg : ∀ x, ν (-x) = ⟨(ν x).proj, -(ν x).2⟩) (q : S2 × ℝ) :
    projInvMap.{u} ν hνneg (projTheta q) = rankOneParam ν q := by
  have hc : 0 < (√(1 + q.2 ^ 2))⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr (by positivity))
  have hx : (q.1 : E3) ≠ 0 := ne_zero_of_mem_unit_sphere q.1
  have hhead : e4Head ((projParamSphere q : S3) : E4) = (√(1 + q.2 ^ 2))⁻¹ • (q.1 : E3) := by
    change e4Head ((√(1 + q.2 ^ 2))⁻¹ • e4Join q.1 q.2) = _
    rw [e4Head_smul, e4Head_e4Join]
  have hne : e4Head ((projParamSphere q : S3) : E4) ≠ 0 := by
    rw [hhead]
    exact smul_ne_zero hc.ne' hx
  rw [projTheta, projInvMap_rpUp, projSphereMap_of_ne ν hne, hhead, unitS2_smul hc hx,
    unitS2_coe]
  congr 2
  change ((√(1 + q.2 ^ 2))⁻¹ • e4Join q.1 q.2) 3 / ‖(√(1 + q.2 ^ 2))⁻¹ • (q.1 : E3)‖ = q.2
  rw [PiLp.smul_apply, e4Join_last, norm_smul, Real.norm_of_nonneg hc.le, norm_sphere_two,
    mul_one, smul_eq_mul]
  field_simp

/-- `projTheta` inverts `projInvMap` off `{w' = 0}`. -/
theorem projTheta_coords {x : S3} (hx : e4Head (x : E4) ≠ 0) :
    projTheta.{u} (unitS2 (e4Head (x : E4)), (x : E4) 3 / ‖e4Head (x : E4)‖) =
      rpUp (rpGroup.projection x) := by
  rw [projTheta]
  congr 2
  apply Subtype.ext
  change (√(1 + ((x : E4) 3 / ‖e4Head (x : E4)‖) ^ 2))⁻¹ •
    e4Join (unitS2 (e4Head (x : E4)) : E3) ((x : E4) 3 / ‖e4Head (x : E4)‖) = (x : E4)
  have hn : 0 < ‖e4Head (x : E4)‖ := norm_pos_iff.mpr hx
  have hsq : 1 + ((x : E4) 3 / ‖e4Head (x : E4)‖) ^ 2 = (‖e4Head (x : E4)‖⁻¹) ^ 2 := by
    have := norm_sq_e4Head_sphere x
    field_simp
    linarith
  rw [hsq, Real.sqrt_sq (inv_nonneg.mpr hn.le), inv_inv, coe_unitS2 hx, smul_e4Join, smul_smul,
    mul_inv_cancel₀ hn.ne', one_smul, mul_div_cancel₀ _ hn.ne']
  exact e4Join_head_last _

/-- Points of `{w₃² < 1}` have `w' ≠ 0`. -/
theorem e4Head_ne_zero_of_bandFn_lt {x : S3} (hx : bandFn.{u} (rpUp (rpGroup.projection x)) < 1) :
    e4Head (x : E4) ≠ 0 := by
  rw [bandFn_rpUp] at hx
  intro h0
  have := norm_sq_e4Head_sphere x
  rw [h0, norm_zero] at this
  linarith

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace B]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V] in
/-- On the band the radial coordinate has absolute value at most one. -/
theorem abs_coord_le_one_of_bandFn_le {x : S3}
    (hx : bandFn.{u} (rpUp (rpGroup.projection x)) ≤ 1 / 2) :
    |(x : E4) 3 / ‖e4Head (x : E4)‖| ≤ 1 := by
  have hne : e4Head (x : E4) ≠ 0 := e4Head_ne_zero_of_bandFn_lt (by linarith)
  have hn : 0 < ‖e4Head (x : E4)‖ := norm_pos_iff.mpr hne
  rw [bandFn_rpUp] at hx
  have h := norm_sq_e4Head_sphere x
  rw [abs_div, abs_of_pos hn, div_le_one hn, ← sq_le_sq₀ (abs_nonneg _) hn.le, sq_abs]
  linarith

end DifferentialGeometry.Geometry.Collapse.ZeroModel.Projective
