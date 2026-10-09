import DifferentialGeometry.Geometry.Thurston.ProjectiveSumDihedralProfile
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.OppositeSum
import DifferentialGeometry.Topology.Manifold.BallChartOrientation
import DifferentialGeometry.Topology.Manifold.StereographicAntipodal
import DifferentialGeometry.Topology.Manifold.SphereOrthogonalAction
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.PartialDiffeomorph
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Product
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Open
import DifferentialGeometry.Topology.Manifold.InverseFunction
import DifferentialGeometry.Geometry.Metric.PolarCoordinates

/-!
# Stereographic ball charts on an antipodal quotient of `S³`

Chapter 7, packet P8c. Let `p : S³ → Z` present `Z` as the antipodal quotient of `S³` and let
`σ⁻¹` be the inverse stereographic projection from a fixed pole, so that `-σ⁻¹ w = σ⁻¹ (-4 w/‖w‖²)`.
The map `w ↦ p (σ⁻¹ (κ w))` is a ball chart of `Z` (`AntipodalSpherePresentation.exists_ballChart`)
and, up to a linear isometry, an oriented one (`exists_orientedBallChart`). The core map
`(y, t) ↦ p (σ⁻¹ (μ t • R y))` built from the profile `μ` is a local diffeomorphism on
`S² × (-5/12, 5/12)`, is invariant under `(y, t) ↦ (-y, -t)`, is injective modulo that involution,
and fills the complement of the unit ball of the chart for `|t| ≤ 1/4`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology
open scoped Manifold ContDiff Topology

namespace GC.Geometry.SphericalProduct

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E4" => EuclideanSpace ℝ (Fin 4)
local notation "S2" => Metric.sphere (0 : E3) 1
local notation "S3" => Metric.sphere (0 : E4) 1

private local instance dihedralChartFinrankThree : Fact (Module.finrank ℝ E3 = 2 + 1) :=
  ⟨by simp⟩

private local instance dihedralChartFinrankFour : Fact (Module.finrank ℝ E4 = 3 + 1) :=
  ⟨by simp⟩

universe u

def dihedralPole : S3 := ⟨EuclideanSpace.single 3 1, by simp⟩

def dihedralStereoInv (w : E3) : S3 := (stereographic' 3 dihedralPole).symm w

theorem dihedralStereo_apply_inv (w : E3) :
    stereographic' 3 dihedralPole (dihedralStereoInv w) = w :=
  (stereographic' 3 dihedralPole).right_inv (by simp)

theorem dihedralStereoInv_injective : Injective dihedralStereoInv := by
  intro a b h
  rw [← dihedralStereo_apply_inv a, ← dihedralStereo_apply_inv b, h]

theorem dihedralStereoInv_ne_pole (w : E3) : dihedralStereoInv w ≠ dihedralPole := by
  have h := (stereographic' 3 dihedralPole).map_target (x := w) (by simp)
  rw [stereographic'_source] at h
  exact h

theorem dihedralStereoInv_zero : dihedralStereoInv 0 = -dihedralPole := by
  apply Subtype.ext
  change ((stereographic' 3 dihedralPole).symm 0 : E4) = -(dihedralPole : E4)
  rw [stereographic'_symm_apply]
  simp only [map_zero, Submodule.coe_zero, norm_zero, smul_zero, zero_add]
  norm_num
  rw [smul_smul]
  norm_num

theorem dihedralStereoInv_antipodal (w : E3) (hw : w ≠ 0) :
    dihedralStereoInv ((-4 / ‖w‖ ^ 2) • w) = -dihedralStereoInv w :=
  DifferentialGeometry.Topology.Manifold.stereographicInverse_antipodal dihedralPole w hw

theorem norm_antipodal_smul (b : E3) (hb : b ≠ 0) :
    ‖(-4 / ‖b‖ ^ 2) • b‖ = 4 / ‖b‖ := by
  have hb' : 0 < ‖b‖ := norm_pos_iff.mpr hb
  rw [norm_smul, Real.norm_eq_abs, abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 4),
    abs_of_pos (pow_pos hb' 2)]
  field_simp

theorem exists_dihedralStereoInv (y : S3) :
    ∃ w, dihedralStereoInv w = y ∨ dihedralStereoInv w = -y := by
  by_cases hy : y = dihedralPole
  · exact ⟨0, Or.inr (by rw [dihedralStereoInv_zero, hy])⟩
  · refine ⟨stereographic' 3 dihedralPole y, Or.inl ?_⟩
    exact (stereographic' 3 dihedralPole).left_inv (by simpa using hy)

theorem isLocalDiffeomorph_dihedralStereoInv :
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ dihedralStereoInv := by
  have he : chartAt E3 (-dihedralPole) = stereographic' 3 dihedralPole := by
    change stereographic' 3 (-(-dihedralPole)) = stereographic' 3 dihedralPole
    rw [neg_neg]
  let D : PartialDiffeomorph (𝓡 3) (𝓡 3) S3 E3 ∞ :=
    { toPartialEquiv := (chartAt E3 (-dihedralPole)).toPartialEquiv
      open_source := (chartAt E3 (-dihedralPole)).open_source
      open_target := (chartAt E3 (-dihedralPole)).open_target
      contMDiffOn_toFun := contMDiffOn_chart
      contMDiffOn_invFun := contMDiffOn_chart_symm }
  intro x
  have h := PartialDiffeomorph.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ D.symm
    (show x ∈ D.target from by
      change x ∈ (chartAt E3 (-dihedralPole)).target
      rw [he]
      simp)
  change IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ (chartAt E3 (-dihedralPole)).symm x at h
  have h' : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ (stereographic' 3 dihedralPole).symm x := by
    simpa only [he] using h
  exact h'

theorem isLocalDiffeomorphAt_real {f : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) {x d : ℝ} (hx : x ∈ U) (hd : d ≠ 0) (hD : HasDerivAt f d x) :
    IsLocalDiffeomorphAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ f x := by
  let L : ℝ ≃L[ℝ] ℝ := (LinearEquiv.smulOfNeZero ℝ ℝ d hd).toContinuousLinearEquiv
  have hL : (L : ℝ →L[ℝ] ℝ) = ContinuousLinearMap.toSpanSingleton ℝ d := by
    apply ContinuousLinearMap.ext
    intro v
    change d * v = v * d
    ring
  apply Manifold.isLocalDiffeomorphAt_of_contMDiffOn_of_hasMFDerivAt_equiv
    f hf.contMDiffOn hU x hx L
  rw [hL]
  exact hD.hasFDerivAt.hasMFDerivAt

theorem isLocalDiffeomorphAt_dihedralProfile {t : ℝ} (ht : t ∈ dihedralDomain) :
    IsLocalDiffeomorphAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ dihedralProfile t := by
  obtain ⟨d, hd, hD⟩ := exists_hasDerivAt_dihedralProfile ht
  exact isLocalDiffeomorphAt_real isOpen_dihedralDomain contDiffOn_dihedralProfile ht hd.ne hD

structure AntipodalSpherePresentation (Z : Type*) [TopologicalSpace Z] [ChartedSpace E3 Z] where
  proj : S3 → Z
  isLocalDiffeomorph : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ proj
  surjective : Surjective proj
  fibres : ∀ x y : S3, proj x = proj y ↔ x = y ∨ (x : E4) = -(y : E4)

namespace AntipodalSpherePresentation

variable {Z : Type*} [TopologicalSpace Z] [ChartedSpace E3 Z] (P : AntipodalSpherePresentation Z)

theorem proj_neg (x : S3) : P.proj (-x) = P.proj x :=
  (P.fibres _ _).mpr (Or.inr rfl)

theorem proj_stereo_eq {a b : E3}
    (h : P.proj (dihedralStereoInv a) = P.proj (dihedralStereoInv b)) :
    a = b ∨ (b ≠ 0 ∧ a = (-4 / ‖b‖ ^ 2) • b) := by
  rcases (P.fibres _ _).mp h with h | h
  · exact Or.inl (dihedralStereoInv_injective h)
  · right
    by_cases hb : b = 0
    · exfalso
      apply dihedralStereoInv_ne_pole a
      apply Subtype.ext
      rw [h, hb, dihedralStereoInv_zero]
      simp
    · refine ⟨hb, dihedralStereoInv_injective ?_⟩
      rw [dihedralStereoInv_antipodal b hb]
      exact Subtype.ext h

theorem norm_eq_of_proj_stereo_eq {a b : E3}
    (h : P.proj (dihedralStereoInv a) = P.proj (dihedralStereoInv b)) :
    ‖a‖ = ‖b‖ ∨ ‖a‖ * ‖b‖ = 4 := by
  rcases P.proj_stereo_eq h with rfl | ⟨hb, rfl⟩
  · exact Or.inl rfl
  · right
    have hb' : 0 < ‖b‖ := norm_pos_iff.mpr hb
    rw [norm_antipodal_smul b hb]
    field_simp

theorem proj_stereo_antipodal (w : E3) (hw : w ≠ 0) :
    P.proj (dihedralStereoInv ((-4 / ‖w‖ ^ 2) • w)) = P.proj (dihedralStereoInv w) := by
  rw [dihedralStereoInv_antipodal w hw, P.proj_neg]

def ballMap (w : E3) : Z := P.proj (dihedralStereoInv (dihedralNeck • w))

theorem isLocalDiffeomorph_ballMap : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ P.ballMap := by
  let S : E3 ≃ₘ⟮𝓡 3, 𝓡 3⟯ E3 :=
    (LinearEquiv.smulOfNeZero ℝ E3 dihedralNeck dihedralNeck_pos.ne').toContinuousLinearEquiv
      |>.toDiffeomorph
  have h := DifferentialGeometry.isLocalDiffeomorph_comp
    (DifferentialGeometry.isLocalDiffeomorph_comp P.isLocalDiffeomorph
      isLocalDiffeomorph_dihedralStereoInv) S.isLocalDiffeomorph
  exact h

theorem injOn_ballMap : InjOn P.ballMap (Metric.ball 0 (2 / dihedralNeck)) := by
  intro w hw w' hw' h
  have hk := dihedralNeck_pos
  rw [Metric.mem_ball, dist_zero_right] at hw hw'
  rcases P.proj_stereo_eq h with h | ⟨hb, h⟩
  · exact smul_right_injective E3 hk.ne' h
  · exfalso
    have hn := congrArg norm h
    have hb' : 0 < ‖dihedralNeck • w'‖ := norm_pos_iff.mpr hb
    have e1 : ‖dihedralNeck • w‖ = dihedralNeck * ‖w‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hk]
    have e2 : ‖dihedralNeck • w'‖ = dihedralNeck * ‖w'‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hk]
    rw [norm_antipodal_smul _ hb, e1, e2] at hn
    rw [e2] at hb'
    have h1 : dihedralNeck * ‖w‖ < 2 := by
      rw [lt_div_iff₀ hk] at hw
      linarith
    have h2 : dihedralNeck * ‖w'‖ < 2 := by
      rw [lt_div_iff₀ hk] at hw'
      linarith
    have h3 : dihedralNeck * ‖w‖ * (dihedralNeck * ‖w'‖) = 4 := by
      rw [hn, div_mul_cancel₀ _ hb'.ne']
    nlinarith [norm_nonneg w, norm_nonneg w']

theorem exists_ballChart : ∃ b : BallChart 3 (𝓡 3) Z, ∀ w, b.chart w = P.ballMap w := by
  have hk := dihedralNeck_pos
  obtain ⟨Φ, hs, -, hf⟩ :=
    DifferentialGeometry.IsLocalDiffeomorphOn.exists_partialDiffeomorph_of_injOn
      (fun x => P.isLocalDiffeomorph_ballMap x) Metric.isOpen_ball
      ⟨0, Metric.mem_ball_self (div_pos two_pos hk)⟩ P.injOn_ballMap
  refine ⟨⟨Φ, ?_⟩, fun w => congrFun hf w⟩
  intro w hw
  rw [hs, Metric.mem_ball]
  rw [Metric.mem_closedBall] at hw
  have : 2 < 2 / dihedralNeck := by
    rw [lt_div_iff₀ hk]
    linarith [dihedralNeck_lt_one]
  linarith

end AntipodalSpherePresentation

theorem exists_orientedBallChart (X : ConnectedClosedOrientedManifold.{u} 3)
    (P : AntipodalSpherePresentation X.Carrier) :
    ∃ (c : OrientedBallChart X.toClosedOrientedManifold) (R : E3 ≃ₗᵢ[ℝ] E3),
      ∀ w, c.chart w = P.ballMap (R w) := by
  obtain ⟨b, hb⟩ := P.exists_ballChart
  rcases BallChart.exists_oriented (M := X.toClosedOrientedManifold) b with ⟨c, hc⟩ | ⟨c, hc⟩
  · exact ⟨c, LinearIsometryEquiv.refl ℝ E3, fun w => (hc w).trans (hb w)⟩
  · let c' : OrientedBallChart X.toClosedOrientedManifold :=
      { toBallChart := c.reflect.toBallChart
        preserves_orientation := fun x hx => by
          have h := c.reflect.preserves_orientation x hx
          exact h.trans (neg_neg (X.orientation.orientation (c.toBallChart.chart (-x)))) }
    refine ⟨c', LinearIsometryEquiv.neg ℝ, fun w => ?_⟩
    change c.toBallChart.chart (-w) = _
    rw [hc, hb]
    rfl

structure DihedralChart (X : ConnectedClosedOrientedManifold.{u} 3) extends
    AntipodalSpherePresentation X.Carrier where
  chart : OrientedBallChart X.toClosedOrientedManifold
  rot : E3 ≃ₗᵢ[ℝ] E3
  chart_apply : ∀ w, chart.chart w = proj (dihedralStereoInv (dihedralNeck • rot w))

theorem nonempty_dihedralChart (X : ConnectedClosedOrientedManifold.{u} 3)
    (P : AntipodalSpherePresentation X.Carrier) : Nonempty (DihedralChart X) := by
  obtain ⟨c, R, hc⟩ := exists_orientedBallChart X P
  exact ⟨{ P with chart := c, rot := R, chart_apply := hc }⟩

namespace DihedralChart

variable {X : ConnectedClosedOrientedManifold.{u} 3} (D : DihedralChart X)

def core (y : S2) (t : ℝ) : X.Carrier :=
  D.proj (dihedralStereoInv (dihedralProfile t • D.rot (y : E3)))

theorem norm_profile_rot {y : S2} {t : ℝ} (ht : t ∈ dihedralDomain) :
    ‖dihedralProfile t • D.rot (y : E3)‖ = dihedralProfile t := by
  rw [norm_smul, LinearIsometryEquiv.norm_map, norm_eq_of_mem_sphere, mul_one, Real.norm_eq_abs,
    abs_of_pos (dihedralProfile_pos ht)]

theorem core_neg (y : S2) {t : ℝ} (ht : t ∈ dihedralDomain) : D.core (-y) (-t) = D.core y t := by
  have hp := dihedralProfile_pos ht
  have hne : dihedralProfile t • D.rot (y : E3) ≠ 0 := by
    rw [← norm_pos_iff, D.norm_profile_rot ht]
    exact hp
  have hm := dihedralProfile_mul_neg ht
  have hneg : dihedralProfile (-t) = 4 / dihedralProfile t := by
    field_simp
    linarith
  have hv : dihedralProfile (-t) • D.rot ((-y : S2) : E3) =
      (-4 / ‖dihedralProfile t • D.rot (y : E3)‖ ^ 2) • (dihedralProfile t • D.rot (y : E3)) := by
    rw [D.norm_profile_rot ht, coe_neg_sphere, map_neg, smul_neg, smul_smul, hneg, ← neg_smul]
    congr 1
    field_simp
  unfold core
  rw [hv, D.toAntipodalSpherePresentation.proj_stereo_antipodal _ hne]

theorem profile_rot_injective {y y' : S2} {t t' : ℝ} (ht : t ∈ dihedralDomain)
    (ht' : t' ∈ dihedralDomain)
    (h : dihedralProfile t • D.rot (y : E3) = dihedralProfile t' • D.rot (y' : E3)) :
    t = t' ∧ y = y' := by
  have hn := congrArg norm h
  rw [D.norm_profile_rot ht, D.norm_profile_rot ht'] at hn
  have htt : t = t' := strictAntiOn_dihedralProfile.injOn ht ht' hn
  refine ⟨htt, ?_⟩
  rw [hn] at h
  have h2 := smul_right_injective E3 (dihedralProfile_pos ht').ne' h
  exact Subtype.ext (D.rot.injective h2)

theorem core_eq_core {y y' : S2} {t t' : ℝ} (ht : t ∈ dihedralDomain)
    (ht' : t' ∈ dihedralDomain) (h : D.core y t = D.core y' t') :
    (y' = y ∧ t' = t) ∨ (y' = -y ∧ t' = -t) := by
  rcases D.toAntipodalSpherePresentation.proj_stereo_eq h with h | ⟨-, h⟩
  · obtain ⟨h1, h2⟩ := D.profile_rot_injective ht ht' h
    exact Or.inl ⟨h2.symm, h1.symm⟩
  · have hm := dihedralProfile_mul_neg ht'
    have hp := dihedralProfile_pos ht'
    have hneg : dihedralProfile (-t') = 4 / dihedralProfile t' := by
      field_simp
      linarith
    rw [D.norm_profile_rot ht', smul_smul] at h
    have h' : dihedralProfile t • D.rot (y : E3) =
        dihedralProfile (-t') • D.rot ((-y' : S2) : E3) := by
      rw [h, coe_neg_sphere, map_neg, smul_neg, ← neg_smul, hneg]
      congr 1
      field_simp
    obtain ⟨h1, h2⟩ := D.profile_rot_injective ht (neg_mem_dihedralDomain ht') h'
    right
    rw [h2, neg_neg, h1, neg_neg]
    exact ⟨rfl, rfl⟩

theorem chart_smul (r : ℝ) (y : S2) :
    D.chart.chart (r • (y : E3)) =
      D.proj (dihedralStereoInv ((dihedralNeck * r) • D.rot (y : E3))) := by
  rw [D.chart_apply, map_smul, smul_smul]

theorem core_eq_chart {y : S2} {t r : ℝ} (h : dihedralProfile t = dihedralNeck * r) :
    D.core y t = D.chart.chart (r • (y : E3)) := by
  rw [D.chart_smul, ← h]
  rfl

theorem core_quarter (y : S2) : D.core y (1 / 4) = D.chart.chart (y : E3) := by
  rw [← one_smul ℝ (y : E3)]
  exact D.core_eq_chart (by rw [dihedralProfile_quarter, mul_one])

theorem norm_of_core_eq_chart {y : S2} {t : ℝ} (ht : t ∈ dihedralDomain) {w : E3}
    (h : D.core y t = D.chart.chart w) :
    dihedralNeck * ‖w‖ = dihedralProfile t ∨ dihedralProfile t * (dihedralNeck * ‖w‖) = 4 := by
  rw [D.chart_apply] at h
  have hk := dihedralNeck_pos
  have hn : ‖dihedralNeck • D.rot w‖ = dihedralNeck * ‖w‖ := by
    rw [norm_smul, LinearIsometryEquiv.norm_map, Real.norm_eq_abs, abs_of_pos hk]
  rcases D.toAntipodalSpherePresentation.norm_eq_of_proj_stereo_eq h with h | h
  · left
    rw [D.norm_profile_rot ht, hn] at h
    exact h.symm
  · right
    rw [D.norm_profile_rot ht, hn] at h
    exact h

theorem core_not_mem_ball {y : S2} {t : ℝ} (ht : t ∈ Icc (-(1 / 4)) (1 / 4)) :
    D.core y t ∉ D.chart.chart '' Metric.ball 0 1 := by
  rintro ⟨w, hw, h⟩
  have htd := Icc_subset_dihedralDomain ht
  have hk := dihedralNeck_pos
  have hp := dihedralProfile_pos htd
  rw [Metric.mem_ball, dist_zero_right] at hw
  have hkw : dihedralNeck * ‖w‖ < dihedralNeck := by nlinarith
  rcases D.norm_of_core_eq_chart htd h.symm with h1 | h1
  · have := (dihedralProfile_lt_neck_iff htd).mp (by linarith)
    linarith [ht.2]
  · have h4 : 4 / dihedralNeck < dihedralProfile t := by
      rw [div_lt_iff₀ hk]
      nlinarith
    have := (lt_dihedralProfile_iff htd).mp h4
    linarith [ht.1]

theorem core_not_mem_closedBall {y : S2} {t : ℝ} (ht : t ∈ Ioo (-(1 / 4)) (1 / 4)) :
    D.core y t ∉ D.chart.chart '' Metric.closedBall 0 1 := by
  rintro ⟨w, hw, h⟩
  have htd := Icc_subset_dihedralDomain (Ioo_subset_Icc_self ht)
  have hk := dihedralNeck_pos
  have hp := dihedralProfile_pos htd
  rw [Metric.mem_closedBall, dist_zero_right] at hw
  have hkw : dihedralNeck * ‖w‖ ≤ dihedralNeck := by nlinarith
  rcases D.norm_of_core_eq_chart htd h.symm with h1 | h1
  · have := (dihedralProfile_le_neck_iff htd).mp (by linarith)
    linarith [ht.2]
  · have h4 : 4 / dihedralNeck ≤ dihedralProfile t := by
      rw [div_le_iff₀ hk]
      nlinarith
    have := (le_dihedralProfile_iff htd).mp h4
    linarith [ht.1]

theorem exists_core_eq (q : X.Carrier) (hq : q ∉ D.chart.chart '' Metric.ball 0 1) :
    ∃ (y : S2) (t : ℝ), t ∈ Icc 0 (1 / 4) ∧ D.core y t = q := by
  have hk := dihedralNeck_pos
  obtain ⟨z, rfl⟩ := D.surjective q
  obtain ⟨a, ha⟩ := exists_dihedralStereoInv z
  have hqa : D.proj (dihedralStereoInv a) = D.proj z := by
    rcases ha with ha | ha
    · rw [ha]
    · rw [ha, D.toAntipodalSpherePresentation.proj_neg]
  have hsmall : ∀ b : E3, ‖b‖ < dihedralNeck →
      D.proj (dihedralStereoInv b) ∈ D.chart.chart '' Metric.ball 0 1 := by
    intro b hb
    refine ⟨D.rot.symm (dihedralNeck⁻¹ • b), ?_, ?_⟩
    · rw [Metric.mem_ball, dist_zero_right, LinearIsometryEquiv.norm_map, norm_smul,
        Real.norm_eq_abs, abs_inv, abs_of_pos hk, inv_mul_lt_iff₀ hk, mul_one]
      exact hb
    · rw [D.chart_apply, LinearIsometryEquiv.apply_symm_apply, smul_smul,
        mul_inv_cancel₀ hk.ne', one_smul]
  by_cases ha0 : a = 0
  · exfalso
    apply hq
    rw [← hqa, ha0]
    exact hsmall 0 (by rw [norm_zero]; exact hk)
  have hna : 0 < ‖a‖ := norm_pos_iff.mpr ha0
  have hlo : dihedralNeck ≤ ‖a‖ := by
    by_contra hlt
    exact hq (hqa ▸ hsmall a (not_le.mp hlt))
  have hhi : ‖a‖ ≤ 4 / dihedralNeck := by
    by_contra hlt
    apply hq
    rw [← hqa, ← D.toAntipodalSpherePresentation.proj_stereo_antipodal a ha0]
    apply hsmall
    rw [norm_smul, Real.norm_eq_abs, abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 4),
      abs_of_pos (pow_pos hna 2)]
    have hlt' : 4 / dihedralNeck < ‖a‖ := not_le.mp hlt
    rw [div_lt_iff₀ hk] at hlt'
    rw [show 4 / ‖a‖ ^ 2 * ‖a‖ = 4 / ‖a‖ by field_simp, div_lt_iff₀ hna]
    linarith
  obtain ⟨t, ht, hta⟩ := exists_dihedralProfile_eq ⟨hlo, hhi⟩
  let y : S2 := ⟨D.rot.symm (‖a‖⁻¹ • a), by
    rw [mem_sphere_zero_iff_norm, LinearIsometryEquiv.norm_map, norm_smul, Real.norm_eq_abs,
      abs_inv, abs_norm, inv_mul_cancel₀ hna.ne']⟩
  have hcore : D.core y t = D.proj z := by
    rw [← hqa]
    unfold core
    congr 2
    change dihedralProfile t • D.rot (D.rot.symm (‖a‖⁻¹ • a)) = a
    rw [LinearIsometryEquiv.apply_symm_apply, smul_smul, hta, mul_inv_cancel₀ hna.ne', one_smul]
  rcases le_total 0 t with h0 | h0
  · exact ⟨y, t, ⟨h0, ht.2⟩, hcore⟩
  · refine ⟨-y, -t, ⟨by linarith, by linarith [ht.1]⟩, ?_⟩
    rw [D.core_neg y (Icc_subset_dihedralDomain ht), hcore]

theorem isLocalDiffeomorphAt_core {y : S2} {t : ℝ} (ht : t ∈ dihedralDomain) :
    IsLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ (fun p : S2 × ℝ => D.core p.1 p.2)
      (y, t) := by
  have h1 : IsLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
      (Prod.map (DifferentialGeometry.Geometry.sphereDiffeo (n := 2) D.rot) dihedralProfile)
      (y, t) :=
    ((DifferentialGeometry.Geometry.sphereDiffeo (n := 2) D.rot).isLocalDiffeomorph y).prodMap
      (isLocalDiffeomorphAt_dihedralProfile ht)
  have h2 : IsLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
      DifferentialGeometry.Geometry.Riemannian.euclideanPolarMap
      (DifferentialGeometry.Geometry.sphereDiffeo (n := 2) D.rot y, dihedralProfile t) :=
    PartialDiffeomorph.isLocalDiffeomorphAt _ _ _
      (DifferentialGeometry.Geometry.Riemannian.euclideanPolarDiffeomorph (E := E3) (n := 2))
      (show 0 < dihedralProfile t from dihedralProfile_pos ht)
  have h3 := (h1.comp (𝓡 3) E3 h2).comp (𝓡 3) S3
    (isLocalDiffeomorph_dihedralStereoInv _)
  have h4 := h3.comp (𝓡 3) X.Carrier (D.isLocalDiffeomorph _)
  exact h4

end DihedralChart

end GC.Geometry.SphericalProduct
