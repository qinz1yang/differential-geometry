import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.UnitFillingSmooth
import DifferentialGeometry.Topology.Manifold.StereographicChart
import DifferentialGeometry.Topology.Manifold.StereographicAntipodal

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff Topology InnerProductSpace
open Set Function Manifold

namespace DifferentialGeometry.Topology.SphereUnitFilling

abbrev E3 := EuclideanSpace ℝ (Fin 3)
abbrev E4 := EuclideanSpace ℝ (Fin 4)
abbrev S3 := Metric.sphere (0 : E4) 1
private local instance : Fact (Module.finrank ℝ E4 = 3 + 1) := ⟨by simp⟩

lemma starRingEnd_real (c : ℝ) : (starRingEnd ℝ) c = c := rfl

lemma norm_coe_sphere (x : S3) : ‖(x : E4)‖ = 1 := by
  simpa only [Metric.mem_sphere, dist_zero_right] using x.2

lemma inner_stereographic_symm_apply (P : S3) (v : E3) :
    ⟪((stereographic' 3 P).symm v : E4), (P : E4)⟫_ℝ = (‖v‖ ^ 2 - 4) / (‖v‖ ^ 2 + 4) := by
  rw [stereographic'_symm_apply]
  set U : (ℝ ∙ (P : E4))ᗮ ≃ₗᵢ[ℝ] E3 :=
    (OrthonormalBasis.fromOrthogonalSpanSingleton 3 (ne_zero_of_mem_unit_sphere P)).repr with hU
  have hnorm : ‖(U.symm v : E4)‖ = ‖v‖ := U.symm.norm_map v
  have horth : ⟪((U.symm v : (ℝ ∙ (P : E4))ᗮ) : E4), (P : E4)⟫_ℝ = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_left.mp (U.symm v).2
  have hP : ⟪(P : E4), (P : E4)⟫_ℝ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, norm_coe_sphere P]
    norm_num
  simp only [inner_add_left, inner_smul_left, horth, hP, hnorm, mul_zero, mul_one,
    starRingEnd_real]
  field_simp
  ring

def radialSigma (s : ℝ) : ℝ :=
  if (4 / 3 : ℝ) ≤ s then 2 / s - 2 else -(3 / 8) * s

def radialPhi (s : ℝ) : ℝ :=
  if (4 / 3 : ℝ) ≤ s then (2 - 2 * s) / s ^ 2 else -(3 / 8)

def nu (v : E3) : E3 := radialPhi ‖v‖ • v

lemma radialSigma_of_lt {s : ℝ} (h : s < 4 / 3) : radialSigma s = -(3 / 8) * s := by
  rw [radialSigma, if_neg (not_le.mpr h)]

lemma radialSigma_of_ge {s : ℝ} (h : 4 / 3 ≤ s) : radialSigma s = 2 / s - 2 := by
  rw [radialSigma, if_pos h]

lemma radialPhi_of_lt {s : ℝ} (h : s < 4 / 3) : radialPhi s = -(3 / 8) := by
  rw [radialPhi, if_neg (not_le.mpr h)]

lemma radialPhi_of_ge {s : ℝ} (h : 4 / 3 ≤ s) : radialPhi s = (2 - 2 * s) / s ^ 2 := by
  rw [radialPhi, if_pos h]

lemma radialPhi_continuous : Continuous radialPhi := by
  refine continuous_if_le continuous_const continuous_id ?_ ?_ ?_
  · exact (continuousOn_const.sub (continuousOn_id.const_mul 2)).div
      (continuousOn_id.pow 2) (fun x hx => by
        have hx' : (4:ℝ) / 3 ≤ x := hx
        positivity)
  · exact continuousOn_const
  · intro x hx
    rw [← hx]
    norm_num

lemma radialSigma_continuous : Continuous radialSigma := by
  refine continuous_if_le continuous_const continuous_id ?_ ?_ ?_
  · exact (continuousOn_const.div continuousOn_id (fun x hx => by
      have hx' : (4:ℝ) / 3 ≤ x := hx
      positivity)).sub continuousOn_const
  · exact (continuousOn_id : ContinuousOn (fun x : ℝ => x) {x : ℝ | x ≤ 4 / 3}).const_mul
      (-(3 / 8))
  · intro x hx
    rw [← hx]
    norm_num

lemma radialSigma_eq_phi_mul (s : ℝ) : radialPhi s * s = radialSigma s := by
  by_cases h : s < 4 / 3
  · rw [radialPhi_of_lt h, radialSigma_of_lt h]
  · have hs : 4 / 3 ≤ s := le_of_not_gt h
    have hs0 : s ≠ 0 := by positivity
    rw [radialPhi_of_ge hs, radialSigma_of_ge hs]
    field_simp

lemma radialSigma_zero : radialSigma 0 = 0 := by
  rw [radialSigma_of_lt (by norm_num)]; norm_num

lemma radialSigma_two : radialSigma 2 = -1 := by
  rw [radialSigma_of_ge (by norm_num)]; norm_num

lemma radialSigma_nonpos {s : ℝ} (h0 : 0 ≤ s) : radialSigma s ≤ 0 := by
  by_cases h : s < 4 / 3
  · rw [radialSigma_of_lt h]; nlinarith
  · have hs : 4 / 3 ≤ s := le_of_not_gt h
    have hs0 : (0:ℝ) < s := by linarith
    rw [radialSigma_of_ge hs, sub_nonpos, div_le_iff₀ hs0]
    linarith

lemma radialSigma_injOn : Set.InjOn radialSigma (Set.Icc 0 2) := by
  intro s hs s' hs' h
  obtain ⟨hs0, hs2⟩ := hs
  obtain ⟨hs0', hs2'⟩ := hs'
  have hmid : -(1 / 2 : ℝ) = radialSigma (4 / 3) := by
    rw [radialSigma_of_ge (le_refl (4 / 3 : ℝ))]; norm_num
  by_cases h1 : s < 4 / 3
  · have hlt : -(3 / 8) * s > -(1 / 2 : ℝ) := by nlinarith
    by_cases h2' : s' < 4 / 3
    · rw [radialSigma_of_lt h1, radialSigma_of_lt h2'] at h
      linarith
    · have hs'3 : 4 / 3 ≤ s' := le_of_not_gt h2'
      have hle : radialSigma s' ≤ -(1 / 2 : ℝ) := by
        rw [hmid, radialSigma_of_ge hs'3]
        have hs'0 : (0:ℝ) < s' := by linarith
        rw [sub_le_iff_le_add, div_le_iff₀ hs'0]
        nlinarith
      rw [radialSigma_of_lt h1] at h
      linarith
  · have hs3 : 4 / 3 ≤ s := le_of_not_gt h1
    have hle : radialSigma s ≤ -(1 / 2 : ℝ) := by
      rw [hmid, radialSigma_of_ge hs3]
      have hs0'' : (0:ℝ) < s := by linarith
      rw [sub_le_iff_le_add, div_le_iff₀ hs0'']
      nlinarith
    by_cases h2' : s' < 4 / 3
    · have hlt : -(3 / 8) * s' > -(1 / 2 : ℝ) := by nlinarith
      rw [radialSigma_of_lt h2'] at h
      linarith
    · have hs'3 : 4 / 3 ≤ s' := le_of_not_gt h2'
      rw [radialSigma_of_ge hs3, radialSigma_of_ge hs'3] at h
      have hs0'' : (0:ℝ) < s := by linarith
      have hs'0 : (0:ℝ) < s' := by linarith
      field_simp at h
      linarith

lemma radialSigma_injective_of_eq {s t : ℝ} (hs : s ∈ Set.Icc 0 2) (ht : t ∈ Set.Icc 0 2)
    (h : radialSigma s = radialSigma t) : s = t :=
  radialSigma_injOn hs ht h

lemma nu_continuous : Continuous nu :=
  (radialPhi_continuous.comp continuous_norm).smul continuous_id

lemma nu_smul {s : ℝ} (hs : 0 ≤ s) {z : E3} (hz : ‖z‖ = 1) :
    nu (s • z) = radialSigma s • z := by
  have hnorm : ‖s • z‖ = s := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs, hz, mul_one]
  rw [nu, hnorm, ← radialSigma_eq_phi_mul s, smul_smul]

lemma norm_nu_of_le {v : E3} (h0 : 0 ≤ ‖v‖) :
    ‖nu v‖ = -radialSigma ‖v‖ := by
  have h1 : ‖nu v‖ = |radialPhi ‖v‖ * ‖v‖| := by
    rw [nu, norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (norm_nonneg v)]
  rw [h1, radialSigma_eq_phi_mul, abs_of_nonpos (radialSigma_nonpos h0)]

lemma norm_nu_le_one {v : E3} (hv : ‖v‖ ≤ 2) : ‖nu v‖ ≤ 1 := by
  rw [norm_nu_of_le (norm_nonneg v)]
  by_cases h : ‖v‖ < 4 / 3
  · rw [radialSigma_of_lt h]; nlinarith [norm_nonneg v]
  · have hs : 4 / 3 ≤ ‖v‖ := le_of_not_gt h
    have hs0 : (0:ℝ) < ‖v‖ := by linarith
    rw [radialSigma_of_ge hs, neg_sub]
    have : (1:ℝ) ≤ 2 / ‖v‖ := by
      rw [one_le_div₀ hs0]
      exact hv
    linarith

lemma nu_injOn : Set.InjOn nu (Metric.closedBall (0 : E3) 2) := by
  intro v hv v' hv' heq
  have hv2 : ‖v‖ ≤ 2 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hv
  have hv2' : ‖v'‖ ≤ 2 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hv'
  have hnorm : ‖nu v‖ = ‖nu v'‖ := by rw [heq]
  rw [norm_nu_of_le (norm_nonneg v), norm_nu_of_le (norm_nonneg v')] at hnorm
  have hsig : radialSigma ‖v‖ = radialSigma ‖v'‖ := by linarith
  have hvv : ‖v‖ = ‖v'‖ := radialSigma_injective_of_eq
    ⟨norm_nonneg v, hv2⟩ ⟨norm_nonneg v', hv2'⟩ hsig
  by_cases h0 : v = 0
  · have h0' : v' = 0 := by
      have : ‖v'‖ = 0 := by rw [← hvv, h0, norm_zero]
      exact norm_eq_zero.mp this
    rw [h0, h0']
  · have hpos : (0:ℝ) < ‖v‖ := norm_pos_iff.mpr h0
    have hphi : radialPhi ‖v‖ ≠ 0 := by
      intro hz
      have hzero : radialSigma ‖v‖ = 0 := by rw [← radialSigma_eq_phi_mul, hz, zero_mul]
      have hsub := radialSigma_injective_of_eq ⟨norm_nonneg v, hv2⟩
        ⟨le_refl (0:ℝ), by norm_num⟩ (by rw [hzero, radialSigma_zero])
      linarith
    have hsmul : radialPhi ‖v‖ • v = radialPhi ‖v‖ • v' := by
      have h1 : radialPhi ‖v‖ • v = nu v := rfl
      have h2 : radialPhi ‖v'‖ • v' = radialPhi ‖v‖ • v' := by rw [hvv]
      rw [h1, ← h2]
      exact heq
    have := congrArg (fun y : E3 => (radialPhi ‖v‖)⁻¹ • y) hsmul
    simpa only [smul_smul, inv_mul_cancel₀ hphi, one_smul] using this

lemma nu_surjOn : ∀ w ∈ Metric.closedBall (0 : E3) 1,
    ∃ v ∈ Metric.closedBall (0 : E3) 2, nu v = w := by
  intro w hw
  have hwn : ‖w‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hw
  by_cases hw0 : w = 0
  · refine ⟨0, ?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right]; norm_num
    · rw [hw0, nu, norm_zero, radialPhi_of_lt (by norm_num)]
      simp
  · have hwt : (0:ℝ) < ‖w‖ := norm_pos_iff.mpr hw0
    have hmem : -(‖w‖) ∈ Set.Icc (radialSigma 2) (radialSigma 0) := by
      rw [radialSigma_two, radialSigma_zero]
      exact ⟨by linarith, by linarith⟩
    obtain ⟨s, hs, hsv⟩ := (intermediate_value_Icc' (by norm_num : (0:ℝ) ≤ 2)
      radialSigma_continuous.continuousOn) hmem
    have hs0 : s ≠ 0 := by
      intro h0
      rw [h0, radialSigma_zero] at hsv
      linarith
    have hz : ‖-((‖w‖)⁻¹) • w‖ = 1 := by
      rw [norm_smul, norm_neg, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hwt),
        inv_mul_cancel₀ (ne_of_gt hwt)]
    refine ⟨s • (-((‖w‖)⁻¹) • w), ?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg hs.1, hz, mul_one]
      exact hs.2
    · rw [nu_smul hs.1 hz, hsv, smul_smul, neg_mul_neg, mul_inv_cancel₀ (ne_of_gt hwt), one_smul]

lemma chartAt_eq_stereographic (P : S3) :
    (chartAt E3 P : OpenPartialHomeomorph S3 E3) = stereographic' 3 (-P) := rfl

lemma contMDiffOn_stereographic_symm (P : S3) :
    ContMDiffOn 𝓘(ℝ, E3) (𝓡 3) ∞ (fun u : E3 => (stereographic' 3 P).symm u) Set.univ := by
  have h := contMDiffOn_chart_symm (I := (𝓡 3 : ModelWithCorners ℝ E3 E3)) (n := ∞) (M := S3)
    (x := (-P : S3))
  rw [chartAt_eq_stereographic, neg_neg] at h
  rw [stereographic'_target] at h
  exact h

lemma contMDiffOn_stereographic (P : S3) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (fun x : S3 => (stereographic' 3 P) x) {(P : S3)}ᶜ := by
  have h := contMDiffOn_chart (I := (𝓡 3 : ModelWithCorners ℝ E3 E3)) (n := ∞) (M := S3)
    (x := (-P : S3))
  rw [chartAt_eq_stereographic, neg_neg] at h
  rwa [stereographic'_source] at h

lemma mem_target_stereographic (P : S3) (v : E3) :
    v ∈ (stereographic' 3 P).target := by
  rw [stereographic'_target]; exact Set.mem_univ v

lemma mem_source_stereographic (P : S3) {x : S3} (hx : x ≠ P) :
    x ∈ (stereographic' 3 P).source := by
  rw [stereographic'_source]; exact hx

def sphereChartPartial (P : S3) : PartialDiffeomorph 𝓘(ℝ, E3) (𝓡 3) E3 S3 ∞ where
  toFun := fun u => (stereographic' 3 P).symm (-((2 : ℝ) • u))
  invFun := fun x => -(((2 : ℝ)⁻¹) • (stereographic' 3 P) x)
  source := Set.univ
  target := {(P : S3)}ᶜ
  map_source' := by
    intro u _
    have hv := (stereographic' 3 P).symm.map_source (x := -((2 : ℝ) • u))
      (mem_target_stereographic P _)
    rwa [OpenPartialHomeomorph.symm_target, stereographic'_source] at hv
  map_target' := by intro x _; exact Set.mem_univ _
  left_inv' := by
    intro u _
    have h : (stereographic' 3 P) ((stereographic' 3 P).symm (-((2:ℝ) • u))) =
        -((2:ℝ) • u) :=
      (stereographic' 3 P).right_inv (mem_target_stereographic P _)
    rw [h]
    module
  right_inv' := by
    intro x hx
    have hx' : x ∈ (stereographic' 3 P).source := mem_source_stereographic P (by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hx)
    have h2 : -((2 : ℝ) • -(((2 : ℝ)⁻¹) • (stereographic' 3 P) x)) = (stereographic' 3 P) x := by
      module
    rw [h2]
    exact (stereographic' 3 P).left_inv hx'
  open_source := isOpen_univ
  open_target := isClosed_singleton.isOpen_compl
  contMDiffOn_toFun := by
    have hlin : ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, E3) ∞ (fun u : E3 => -((2 : ℝ) • u)) :=
      (contDiff_const_smul (2 : ℝ)).neg.contMDiff
    have h := ContMDiffOn.comp_contMDiff (contMDiffOn_stereographic_symm P) hlin
      (fun u => Set.mem_univ u)
    simpa only [Function.comp_def] using h.contMDiffOn
  contMDiffOn_invFun := by
    have hlin : ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, E3) ∞ (fun v : E3 => -(((2 : ℝ)⁻¹) • v)) :=
      (contDiff_const_smul (((2 : ℝ)⁻¹))).neg.contMDiff
    have h := ContMDiff.comp_contMDiffOn hlin (contMDiffOn_stereographic P)
    simpa only [Function.comp_def] using h

lemma sphereChartPartial_toFun (P : S3) (u : E3) :
    (sphereChartPartial P).toPartialEquiv u = (stereographic' 3 P).symm (-((2 : ℝ) • u)) := rfl

lemma sphereChartPartial_apply (P : S3) (u : E3) :
    sphereChartPartial P u = (stereographic' 3 P).symm (-((2 : ℝ) • u)) := rfl

def sphereBallChart (P : S3) : BallChart 3 (𝓡 3) S3 where
  chart := sphereChartPartial P
  closedBall_subset_source := fun x _ => Set.mem_univ x

lemma ballImage_sphereBallChart (P : S3) :
    (sphereBallChart P).chart '' Metric.ball (0 : E3) 1 = {x : S3 | ⟪(x : E4), (P : E4)⟫_ℝ < 0} := by
  have himg : (sphereBallChart P).chart '' Metric.ball (0 : E3) 1
      = (stereographic' 3 P).symm '' Metric.ball (0 : E3) 2 := by
    have hfun : (sphereBallChart P).chart '' Metric.ball (0 : E3) 1 =
        ((fun v : E3 => (stereographic' 3 P).symm v) ∘ (fun u : E3 => -((2:ℝ) • u))) ''
          Metric.ball (0 : E3) 1 := rfl
    rw [hfun, Set.image_comp]
    congr 1
    ext v
    constructor
    · rintro ⟨u, hu, rfl⟩
      rw [Metric.mem_ball, dist_zero_right] at hu ⊢
      rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ) < 2)]
      linarith
    · intro hv
      refine ⟨-(((2:ℝ)⁻¹) • v), ?_, ?_⟩
      · rw [Metric.mem_ball, dist_zero_right] at hv ⊢
        rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (by norm_num : (0:ℝ) < 2))]
        linarith
      · simp only [smul_neg, smul_smul, mul_inv_cancel₀ (by norm_num : (2:ℝ) ≠ 0),
          neg_neg, one_smul]
  rw [himg]
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    rw [Metric.mem_ball, dist_zero_right] at hv
    rw [Set.mem_ofPred_eq, inner_stereographic_symm_apply]
    have hnum : ‖v‖ ^ 2 - 4 < 0 := by nlinarith [norm_nonneg v, hv]
    exact div_neg_of_neg_of_pos hnum (by positivity)
  · intro hx
    have hxlt : ⟪(x : E4), (P : E4)⟫_ℝ < 0 := hx
    have hxP : x ≠ P := by
      intro h
      rw [h, inner_self_eq_norm_sq_to_K, norm_coe_sphere P] at hxlt
      norm_num at hxlt
    refine ⟨(stereographic' 3 P) x, ?_, ?_⟩
    · rw [Metric.mem_ball, dist_zero_right]
      have hval : ⟪(x : E4), (P : E4)⟫_ℝ =
          (‖(stereographic' 3 P) x‖ ^ 2 - 4) / (‖(stereographic' 3 P) x‖ ^ 2 + 4) := by
        conv_lhs => rw [← (stereographic' 3 P).left_inv (mem_source_stereographic P hxP)]
        exact inner_stereographic_symm_apply P _
      have hxlt' := hxlt
      rw [hval] at hxlt'
      have hpos : (0:ℝ) < ‖(stereographic' 3 P) x‖ ^ 2 + 4 := by
        nlinarith [sq_nonneg ‖(stereographic' 3 P) x‖]
      have hnum : ‖(stereographic' 3 P) x‖ ^ 2 - 4 < 0 := by
        rcases (div_neg_iff.mp hxlt') with ⟨_, h2⟩ | ⟨h1, _⟩
        · exact absurd h2 (not_lt_of_ge (le_of_lt hpos))
        · exact h1
      nlinarith [hnum, norm_nonneg ((stereographic' 3 P) x)]
    · exact (stereographic' 3 P).left_inv (mem_source_stereographic P hxP)

lemma not_mem_chart_ball_iff (P : S3) (x : S3) :
    x ∉ (sphereBallChart P).chart '' Metric.ball (0 : E3) 1 ↔ 0 ≤ ⟪(x : E4), (P : E4)⟫_ℝ := by
  rw [ballImage_sphereBallChart]
  exact not_lt (a := ⟪(x : E4), (P : E4)⟫_ℝ) (b := 0)

lemma norm_stereographic_neg_le_two {P : S3} {x : S3}
    (hx : x ∉ (sphereBallChart P).chart '' Metric.ball (0 : E3) 1) :
    ‖(stereographic' 3 P) (-x)‖ ≤ 2 := by
  have hcap : 0 ≤ ⟪(x : E4), (P : E4)⟫_ℝ := (not_mem_chart_ball_iff P x).mp hx
  have hyP : ⟪((-x : S3) : E4), (P : E4)⟫_ℝ ≤ 0 := by
    have hcoe : ((-x : S3) : E4) = -(x : E4) := by simp
    rw [hcoe, inner_neg_left]
    linarith
  have hne : (-x : S3) ≠ P := by
    intro h
    rw [h, inner_self_eq_norm_sq_to_K, norm_coe_sphere P] at hyP
    norm_num at hyP
  have hleft := (stereographic' 3 P).left_inv (mem_source_stereographic P hne)
  have hcoord : ⟪((-x : S3) : E4), (P : E4)⟫_ℝ =
      (‖(stereographic' 3 P) (-x)‖ ^ 2 - 4) / (‖(stereographic' 3 P) (-x)‖ ^ 2 + 4) := by
    conv_lhs => rw [← hleft]
    exact inner_stereographic_symm_apply P _
  rw [hcoord] at hyP
  have hpos : (0:ℝ) < ‖(stereographic' 3 P) (-x)‖ ^ 2 + 4 := by
    nlinarith [sq_nonneg ‖(stereographic' 3 P) (-x)‖]
  rcases (div_nonpos_iff.mp hyP) with ⟨_, h2⟩ | ⟨h1, _⟩
  · exact absurd h2 (not_le_of_gt hpos)
  · nlinarith [h1, norm_nonneg ((stereographic' 3 P) (-x))]

def capPoint (P : S3) (x : (sphereBallChart P).Punctured) : Metric.closedBall (0 : E3) 2 :=
  ⟨(stereographic' 3 P) (-(x : S3)), by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact norm_stereographic_neg_le_two x.2⟩

def capToBall (P : S3) :
    (sphereBallChart P).Punctured → Metric.closedBall (0 : E3) 1 :=
  fun x => ⟨nu (capPoint P x : E3), by
    rw [Metric.mem_closedBall, dist_zero_right]
    refine norm_nu_le_one ?_
    simpa only [Metric.mem_closedBall, dist_zero_right] using (capPoint P x).2⟩

lemma capPoint_apply (P : S3) (x : (sphereBallChart P).Punctured) :
    ((capPoint P x : Metric.closedBall (0 : E3) 2) : E3) = (stereographic' 3 P) (-(x : S3)) := rfl

lemma capToBall_apply (P : S3) (x : (sphereBallChart P).Punctured) :
    ((capToBall P x : Metric.closedBall (0 : E3) 1) : E3) = nu (capPoint P x : E3) := rfl

lemma continuous_capPoint (P : S3) : Continuous (capPoint P) := by
  have hmem : ∀ x : (sphereBallChart P).Punctured, (-(x : S3) : S3) ∈ ({P}ᶜ : Set S3) := by
    intro x hx
    have hcap : 0 ≤ ⟪((x : S3) : E4), (P : E4)⟫_ℝ := (not_mem_chart_ball_iff P (x : S3)).mp x.2
    have hneg : ⟪((-((x : S3)) : S3) : E4), (P : E4)⟫_ℝ ≤ 0 := by
      have hcoe : ((-((x : S3)) : S3) : E4) = -((x : S3) : E4) := by simp
      rw [hcoe, inner_neg_left]
      linarith
    rw [hx, inner_self_eq_norm_sq_to_K, norm_coe_sphere P] at hneg
    norm_num at hneg
  have h1 : Continuous fun x : (sphereBallChart P).Punctured => (stereographic' 3 P) (-(x : S3)) :=
    ContinuousOn.comp_continuous (contMDiffOn_stereographic P).continuousOn
      (continuous_subtype_val.neg) hmem
  exact Continuous.subtype_mk h1 (fun x => by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact norm_stereographic_neg_le_two x.2)

lemma continuous_capToBall (P : S3) : Continuous (capToBall P) := by
  have h1 : Continuous fun x : (sphereBallChart P).Punctured => nu (capPoint P x : E3) :=
    nu_continuous.comp ((continuous_subtype_val :
      Continuous fun y : Metric.closedBall (0 : E3) 2 => (y : E3)).comp (continuous_capPoint P))
  exact Continuous.subtype_mk h1 (fun x => by
    rw [Metric.mem_closedBall, dist_zero_right]
    refine norm_nu_le_one ?_
    simpa only [Metric.mem_closedBall, dist_zero_right] using (capPoint P x).2)

lemma capToBall_injective (P : S3) : Function.Injective (capToBall P) := by
  intro x y hxy
  have h1 : nu ((capPoint P x : Metric.closedBall (0:E3) 2) : E3) =
      nu ((capPoint P y : Metric.closedBall (0:E3) 2) : E3) := by
    have this := congrArg (fun z : Metric.closedBall (0 : E3) 1 => (z : E3)) hxy
    rw [capToBall_apply, capToBall_apply] at this
    exact this
  have h2 := nu_injOn (capPoint P x).2 (capPoint P y).2 h1
  have h3 : (stereographic' 3 P) (-(x : S3)) = (stereographic' 3 P) (-(y : S3)) := by
    rw [capPoint_apply, capPoint_apply] at h2
    exact h2
  have hmems : ∀ z : (sphereBallChart P).Punctured, (-(z : S3) : S3) ∈ ({P}ᶜ : Set S3) := by
    intro z hz
    have hcap : 0 ≤ ⟪((z : S3) : E4), (P : E4)⟫_ℝ := (not_mem_chart_ball_iff P (z : S3)).mp z.2
    have hneg : ⟪((-((z : S3)) : S3) : E4), (P : E4)⟫_ℝ ≤ 0 := by
      have hcoe : ((-((z : S3)) : S3) : E4) = -((z : S3) : E4) := by simp
      rw [hcoe, inner_neg_left]
      linarith
    rw [hz, inner_self_eq_norm_sq_to_K, norm_coe_sphere P] at hneg
    norm_num at hneg
  have h4 : (-(x : S3) : S3) = -(y : S3) := by
    rw [← (stereographic' 3 P).left_inv (mem_source_stereographic P (hmems x)),
      ← (stereographic' 3 P).left_inv (mem_source_stereographic P (hmems y)), h3]
  exact Subtype.ext (neg_injective h4)

lemma mem_chart_ball_of_norm_lt {P : S3} {w : E3} (hw : w ∈ Metric.ball (0 : E3) 2) :
    (stereographic' 3 P).symm w ∈ (sphereBallChart P).chart '' Metric.ball (0 : E3) 1 := by
  rw [ballImage_sphereBallChart]
  rw [Set.mem_ofPred_eq, inner_stereographic_symm_apply]
  have hwlt : ‖w‖ < 2 := by simpa only [Metric.mem_ball, dist_zero_right] using hw
  have hnum : ‖w‖ ^ 2 - 4 < 0 := by nlinarith [norm_nonneg w]
  have hden : (0:ℝ) < ‖w‖ ^ 2 + 4 := by nlinarith [sq_nonneg ‖w‖]
  exact div_neg_of_neg_of_pos hnum hden

lemma capToBall_surjective (P : S3) : Function.Surjective (capToBall P) := by
  intro w
  obtain ⟨v, hv, hvw⟩ := nu_surjOn (w : E3) w.2
  have hv2 : ‖v‖ ≤ 2 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hv
  have hmem : (-((stereographic' 3 P).symm v) : S3) ∉
      (sphereBallChart P).chart '' Metric.ball (0 : E3) 1 := by
    refine (not_mem_chart_ball_iff P _).mpr ?_
    have hcoe : ((-((stereographic' 3 P).symm v) : S3) : E4) =
        -(((stereographic' 3 P).symm v : S3) : E4) := by simp
    rw [hcoe, inner_neg_left, inner_stereographic_symm_apply]
    have hden : (0:ℝ) < ‖v‖ ^ 2 + 4 := by nlinarith [sq_nonneg ‖v‖]
    have hnum : ‖v‖ ^ 2 - 4 ≤ 0 := by nlinarith [norm_nonneg v]
    have hq := div_nonpos_of_nonpos_of_nonneg hnum (le_of_lt hden)
    linarith
  refine ⟨⟨-((stereographic' 3 P).symm v), hmem⟩, ?_⟩
  refine Subtype.ext ?_
  rw [capToBall_apply]
  have hpoint : ((capPoint P ⟨-((stereographic' 3 P).symm v), hmem⟩ :
      Metric.closedBall (0 : E3) 2) : E3) = v := by
    rw [capPoint_apply]
    have harg : (-(↑(⟨-((stereographic' 3 P).symm v), hmem⟩ :
        (sphereBallChart P).Punctured) : S3) : S3) = (stereographic' 3 P).symm v := by simp
    rw [harg]
    exact (stereographic' 3 P).right_inv (mem_target_stereographic P v)
  rw [hpoint, hvw]

private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

abbrev sphereAnti (z : Metric.sphere (0 : E3) 1) : Metric.sphere (0 : E3) 1 :=
  DifferentialGeometry.Topology.Manifold.sphereAntipodalDiffeomorph (n := 2) z

noncomputable def capHomeomorph (P : S3) :
    (sphereBallChart P).Punctured ≃ₜ Metric.closedBall (0 : E3) 1 :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (capToBall P) ⟨capToBall_injective P, capToBall_surjective P⟩)
    (continuous_capToBall P)

lemma sphereAnti_eq_neg (z : Metric.sphere (0 : E3) 1) : sphereAnti z = -z := rfl

lemma antipodal_apply {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
    [Fact (Module.finrank ℝ E = n + 1)] (z : Metric.sphere (0 : E) 1) :
    DifferentialGeometry.Topology.Manifold.sphereAntipodalDiffeomorph (n := n) z = -z := rfl

lemma capToBall_boundary (P : S3) (z : Metric.sphere (0 : E3) 1) :
    capToBall P ((sphereBallChart P).boundaryMap (sphereAnti z)) =
      ⟨z, Metric.sphere_subset_closedBall z.2⟩ := by
  have hz1 : ‖(z : E3)‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using z.2
  refine Subtype.ext ?_
  have hxin : (((sphereBallChart P).boundaryMap (sphereAnti z) : (sphereBallChart P).Punctured) : S3)
      = (stereographic' 3 P).symm (-((2 : ℝ) • (sphereAnti z : Metric.sphere (0 : E3) 1))) := rfl
  rw [capToBall_apply, capPoint_apply, hxin, sphereAnti_eq_neg]
  have hcoe : ((-z : Metric.sphere (0 : E3) 1) : E3) = -(z : E3) := by simp
  have harg : -((2 : ℝ) • (-z : Metric.sphere (0 : E3) 1)) = (2 : ℝ) • (z : E3) := by
    rw [hcoe, smul_neg, neg_neg]
  rw [harg]
  have hne : ((2 : ℝ) • (z : E3)) ≠ 0 := by
    intro h
    have hnorm := congrArg norm h
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ) < 2), hz1, mul_one,
      norm_zero] at hnorm
    norm_num at hnorm
  have hanti := DifferentialGeometry.Topology.Manifold.stereographicInverse_antipodal (n := 3)
    (north := P) (x := (2 : ℝ) • (z : E3)) hne
  rw [← hanti]
  have hnorm2 : ‖((2 : ℝ) • (z : E3))‖ = 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ) < 2), hz1, mul_one]
  have hcoef : (-4 / ‖(2 : ℝ) • (z : E3)‖ ^ 2) • ((2 : ℝ) • (z : E3)) =
      -((2 : ℝ) • (z : E3)) := by
    rw [hnorm2]; norm_num
  rw [hcoef]
  have hright : (stereographic' 3 P) ((stereographic' 3 P).symm (-((2 : ℝ) • (z : E3)))) =
      -((2 : ℝ) • (z : E3)) :=
    (stereographic' 3 P).right_inv (mem_target_stereographic P _)
  rw [hright]
  have hnu := nu_smul (s := (2 : ℝ)) (by norm_num) (z := (-z : Metric.sphere (0 : E3) 1)) (by
    rw [hcoe, norm_neg]; exact hz1)
  rw [← smul_neg, ← hcoe, hnu, radialSigma_two]
  simp

lemma capToBall_radial (P : S3) (z : Metric.sphere (0 : E3) 1) {ρ : ℝ}
    (h1 : 1 ≤ ρ) (h2 : ρ ≤ 3 / 2) (hρ : ρ ∈ Set.Icc 1 2) :
    capToBall P ((sphereBallChart P).radialMap (sphereAnti z) ρ hρ) =
      ⟨(2 - ρ) • (z : E3), by
        have hz1 : ‖(z : E3)‖ = 1 := by
          simpa only [Metric.mem_sphere, dist_zero_right] using z.2
        rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (by linarith), hz1, mul_one]
        linarith⟩ := by
  have hz1 : ‖(z : E3)‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using z.2
  have hρpos : (0:ℝ) < ρ := by linarith
  refine Subtype.ext ?_
  have hxin : (((sphereBallChart P).radialMap (sphereAnti z) ρ hρ :
        (sphereBallChart P).Punctured) : S3)
      = (stereographic' 3 P).symm
        (-((2 : ℝ) • (ρ • (sphereAnti z : Metric.sphere (0 : E3) 1)))) := rfl
  rw [capToBall_apply, capPoint_apply, hxin, sphereAnti_eq_neg]
  have hcoe : ((-z : Metric.sphere (0 : E3) 1) : E3) = -(z : E3) := by simp
  have harg : -((2 : ℝ) • (ρ • (-z : Metric.sphere (0 : E3) 1))) = (2 * ρ) • (z : E3) := by
    rw [hcoe, smul_neg, smul_neg, neg_neg]
    module
  rw [harg]
  have hne : ((2 * ρ) • (z : E3)) ≠ 0 := by
    intro h
    have hnorm := congrArg norm h
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith : (0:ℝ) < 2 * ρ), hz1, mul_one,
      norm_zero] at hnorm
    linarith
  have hanti := DifferentialGeometry.Topology.Manifold.stereographicInverse_antipodal (n := 3)
    (north := P) (x := (2 * ρ) • (z : E3)) hne
  rw [← hanti]
  have hcoef : (-4 / ‖(2 * ρ) • (z : E3)‖ ^ 2) • ((2 * ρ) • (z : E3)) =
      -((2 / ρ) • (z : E3)) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith : (0:ℝ) < 2 * ρ), hz1, mul_one,
      smul_smul]
    have hρ2 : ρ ≠ 0 := ne_of_gt hρpos
    field_simp
    module
  rw [hcoef, ← smul_neg]
  rw [(stereographic' 3 P).right_inv (mem_target_stereographic P _)]
  have hnu := nu_smul (s := 2 / ρ) (by positivity) (z := (-z : E3)) (by rw [norm_neg]; exact hz1)
  rw [hnu]
  have hsig : radialSigma (2 / ρ) = ρ - 2 := by
    rw [radialSigma_of_ge (by
      rw [le_div_iff₀ hρpos]
      linarith)]
    field_simp
  rw [hsig, smul_neg, ← neg_smul, neg_sub]

end DifferentialGeometry.Topology.SphereUnitFilling
