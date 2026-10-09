import DifferentialGeometry.Topology.Handle.SphereNormalization
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.IsotopyExtension

/-!
# Disk normalization on the 2-sphere away from a round cap

Chapter-14 assembly, item L1 (lane ASM-L1), group G2, first half. On the unit sphere
`S ⊆ ℝ³`, the closed round cap `{θ | a ≤ ⟪θ, p⟫}` around `p` is fixed while a smooth disk is moved
onto another one: `exists_sphere_isotopy_eqOn_disk_off_cap`. The two disks are given as charts
`α β : ℝ² ⇀ S` on a closed ball `closedBall 0 R`, both avoiding the cap, and of the same orientation
in the stereographic chart from `p`. The isotopy is the identity on an open neighbourhood of the cap.

Route: the stereographic projection from `p` (`stereoChart p`) maps the complement of the cap onto
the open ball of squared radius `4 (1 + a) / (1 - a)` (`inner_stereoChart_symm`,
`stereoChart_mem_ball_iff`), which is convex. The Euclidean disk isotopy of the tree
(`exists_isotopy_eqOn_closedBall_of_partialDiffeomorphs_of_subset_of_radius`, compactly supported
in that ball) is transported to the sphere through the chart
(`PartialDiffeomorph.exists_isotopy_extension_of_isCompact`).
-/

set_option autoImplicit false

noncomputable section

open Set Metric
open scoped ContDiff Manifold InnerProductSpace

namespace DifferentialGeometry.Topology.Handle

local instance fact_finrank_three_ASML1 :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

/-- The stereographic projection from `p`, as a smooth partial diffeomorphism of the unit sphere
of `ℝ³` onto `ℝ²` (source: the complement of `p`; target: everything). -/
def stereoChart (p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    PartialDiffeomorph (𝓡 2) (𝓡 2) (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
      (EuclideanSpace ℝ (Fin 2)) ∞ where
  toPartialEquiv := (stereographic' 2 p).toPartialEquiv
  open_source := (stereographic' 2 p).open_source
  open_target := (stereographic' 2 p).open_target
  contMDiffOn_toFun := by
    have hchart : chartAt (EuclideanSpace ℝ (Fin 2)) (-p) = stereographic' 2 p := by
      change stereographic' 2 (-(-p)) = stereographic' 2 p
      rw [neg_neg]
    have h : ContMDiffOn (𝓡 2) (𝓡 2) ∞ (stereographic' 2 p) (stereographic' 2 p).source := by
      rw [← hchart]
      exact contMDiffOn_chart
    exact h
  contMDiffOn_invFun := by
    have hchart : chartAt (EuclideanSpace ℝ (Fin 2)) (-p) = stereographic' 2 p := by
      change stereographic' 2 (-(-p)) = stereographic' 2 p
      rw [neg_neg]
    have h : ContMDiffOn (𝓡 2) (𝓡 2) ∞ (stereographic' 2 p).symm
        (stereographic' 2 p).target := by
      rw [← hchart]
      exact contMDiffOn_chart_symm
    exact h

theorem stereoChart_apply (p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (θ : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) : stereoChart p θ = stereographic' 2 p θ :=
  rfl

theorem stereoChart_symm_apply (p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (y : EuclideanSpace ℝ (Fin 2)) : (stereoChart p).symm y = (stereographic' 2 p).symm y :=
  rfl

theorem stereoChart_source (p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    (stereoChart p).source = {p}ᶜ :=
  stereographic'_source p

theorem stereoChart_target (p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    (stereoChart p).target = univ :=
  stereographic'_target p

/-- The height of the inverse stereographic projection: `⟪c⁻¹ y, p⟫ = (‖y‖² - 4) / (‖y‖² + 4)`. -/
theorem inner_stereoChart_symm (p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (y : EuclideanSpace ℝ (Fin 2)) :
    ⟪((stereoChart p).symm y : EuclideanSpace ℝ (Fin 3)), (p : EuclideanSpace ℝ (Fin 3))⟫_ℝ =
      (‖y‖ ^ 2 - 4) / (‖y‖ ^ 2 + 4) := by
  rw [stereoChart_symm_apply, stereographic'_symm_apply]
  set U : (ℝ ∙ (p : EuclideanSpace ℝ (Fin 3)))ᗮ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) :=
    (OrthonormalBasis.fromOrthogonalSpanSingleton 2 (ne_zero_of_mem_unit_sphere p)).repr
  have hperp : ⟪((U.symm y : (ℝ ∙ (p : EuclideanSpace ℝ (Fin 3)))ᗮ) :
      EuclideanSpace ℝ (Fin 3)), (p : EuclideanSpace ℝ (Fin 3))⟫_ℝ = 0 :=
    Submodule.inner_left_of_mem_orthogonal (Submodule.mem_span_singleton_self _)
      (U.symm y).2
  have hnorm : ‖((U.symm y : (ℝ ∙ (p : EuclideanSpace ℝ (Fin 3)))ᗮ) :
      EuclideanSpace ℝ (Fin 3))‖ = ‖y‖ := by
    rw [Submodule.norm_coe, LinearIsometryEquiv.norm_map]
  have hpp : ⟪(p : EuclideanSpace ℝ (Fin 3)), (p : EuclideanSpace ℝ (Fin 3))⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere p]
    norm_num
  simp only [hnorm, inner_add_left, inner_smul_left, hperp, hpp, RCLike.conj_to_real]
  have hpos : (0 : ℝ) < ‖y‖ ^ 2 + 4 := by positivity
  field_simp
  ring

/-- The complement of the closed cap `{a ≤ ⟪θ, p⟫}` corresponds, under the stereographic
projection from `p`, to the open ball of squared radius `4 (1 + a) / (1 - a)`. -/
theorem inner_stereoChart_symm_lt_iff (p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) {a : ℝ}
    (ha : a < 1) {y : EuclideanSpace ℝ (Fin 2)} :
    ⟪((stereoChart p).symm y : EuclideanSpace ℝ (Fin 3)), (p : EuclideanSpace ℝ (Fin 3))⟫_ℝ < a ↔
      ‖y‖ ^ 2 < 4 * (1 + a) / (1 - a) := by
  rw [inner_stereoChart_symm]
  have hpos : (0 : ℝ) < ‖y‖ ^ 2 + 4 := by positivity
  have h1a : (0 : ℝ) < 1 - a := by linarith
  rw [div_lt_iff₀ hpos, lt_div_iff₀ h1a]
  constructor <;> intro h <;> nlinarith

/-- The radius of the image ball of the cap complement. -/
def capComplementRadius (a : ℝ) : ℝ := Real.sqrt (4 * (1 + a) / (1 - a))

theorem mem_ball_capComplementRadius_iff {a : ℝ} (ha : -1 < a) (ha' : a < 1)
    {y : EuclideanSpace ℝ (Fin 2)} :
    y ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) (capComplementRadius a) ↔
      ‖y‖ ^ 2 < 4 * (1 + a) / (1 - a) := by
  have hq : 0 ≤ 4 * (1 + a) / (1 - a) := div_nonneg (by linarith) (by linarith)
  rw [mem_ball_zero_iff, capComplementRadius, Real.lt_sqrt (norm_nonneg y)]

/-- A sphere point off the closed cap is a point of the chart source, sent into the image ball. -/
theorem stereoChart_mem_ball_of_inner_lt (p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) {a : ℝ}
    (ha : -1 < a) (ha' : a < 1) {θ : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1}
    (hθ : ⟪(θ : EuclideanSpace ℝ (Fin 3)), (p : EuclideanSpace ℝ (Fin 3))⟫_ℝ < a) :
    θ ∈ (stereoChart p).source ∧ stereoChart p θ ∈ ball (0 : EuclideanSpace ℝ (Fin 2))
      (capComplementRadius a) := by
  have hθp : θ ≠ p := by
    rintro rfl
    have h1 : ⟪(θ : EuclideanSpace ℝ (Fin 3)), (θ : EuclideanSpace ℝ (Fin 3))⟫_ℝ = 1 := by
      rw [real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere θ]
      norm_num
    linarith
  have hsrc : θ ∈ (stereoChart p).source := by
    rw [stereoChart_source]
    exact hθp
  refine ⟨hsrc, ?_⟩
  rw [mem_ball_capComplementRadius_iff ha ha', ← inner_stereoChart_symm_lt_iff p ha',
    show (stereoChart p).symm.toPartialEquiv = (stereoChart p).toPartialEquiv.symm from rfl,
    (stereoChart p).toPartialEquiv.left_inv hsrc]
  exact hθ

theorem inner_lt_of_mem_ball (p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) {a : ℝ}
    (ha : -1 < a) (ha' : a < 1) {y : EuclideanSpace ℝ (Fin 2)}
    (hy : y ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) (capComplementRadius a)) :
    ⟪((stereoChart p).symm y : EuclideanSpace ℝ (Fin 3)), (p : EuclideanSpace ℝ (Fin 3))⟫_ℝ < a :=
  (inner_stereoChart_symm_lt_iff p ha').mpr ((mem_ball_capComplementRadius_iff ha ha').mp hy)

/-- **Disk normalization on the sphere off a round cap.** Two disk charts `α`, `β` of the unit
sphere of `ℝ³`, both avoiding the closed cap `{a ≤ ⟪θ, p⟫}` on `closedBall 0 R` and of the same
orientation in the stereographic chart from `p`, are related by the end map of a smooth isotopy of
the sphere which starts at the identity and is the identity on an open neighbourhood of the cap. -/
theorem exists_sphere_isotopy_eqOn_disk_off_cap (p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    {a : ℝ} (ha : -1 < a) (ha' : a < 1)
    (α β : PartialDiffeomorph (𝓡 2) (𝓡 2) (EuclideanSpace ℝ (Fin 2))
      (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞)
    {R : ℝ} (hR : 0 < R) (hα : closedBall 0 R ⊆ α.source) (hβ : closedBall 0 R ⊆ β.source)
    (hαcap : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) R,
      ⟪(α x : EuclideanSpace ℝ (Fin 3)), (p : EuclideanSpace ℝ (Fin 3))⟫_ℝ < a)
    (hβcap : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) R,
      ⟪(β x : EuclideanSpace ℝ (Fin 3)), (p : EuclideanSpace ℝ (Fin 3))⟫_ℝ < a)
    (hori : 0 < (fderiv ℝ (stereoChart p ∘ α) 0).det * (fderiv ℝ (stereoChart p ∘ β) 0).det) :
    ∃ h : ℝ → Diffeomorph (𝓡 2) (𝓡 2) (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
        (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞,
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2) ∞
        (fun z : ℝ × sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 => h z.1 z.2) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2) ∞
        (fun z : ℝ × sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 => (h z.1).symm z.2) ∧
      h 0 = Diffeomorph.refl (𝓡 2) (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞ ∧
      (∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) R, h 1 (α x) = β x) ∧
      ∃ U : Set (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1), IsOpen U ∧
        {θ : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 |
          a ≤ ⟪(θ : EuclideanSpace ℝ (Fin 3)), (p : EuclideanSpace ℝ (Fin 3))⟫_ℝ} ⊆ U ∧
        ∀ t θ, θ ∈ U → h t θ = θ ∧ (h t).symm θ = θ := by
  set c := stereoChart p with hc
  let φ₀ := α.trans c
  let φ₁ := β.trans c
  have hφ₀ (x : EuclideanSpace ℝ (Fin 2)) : φ₀ x = c (α x) := rfl
  have hφ₁ (x : EuclideanSpace ℝ (Fin 2)) : φ₁ x = c (β x) := rfl
  have hs₀ : closedBall (0 : EuclideanSpace ℝ (Fin 2)) R ⊆ φ₀.source := fun x hx =>
    ⟨hα hx, (stereoChart_mem_ball_of_inner_lt p ha ha' (hαcap x hx)).1⟩
  have hs₁ : closedBall (0 : EuclideanSpace ℝ (Fin 2)) R ⊆ φ₁.source := fun x hx =>
    ⟨hβ hx, (stereoChart_mem_ball_of_inner_lt p ha ha' (hβcap x hx)).1⟩
  have hV₀ : φ₀ '' closedBall (0 : EuclideanSpace ℝ (Fin 2)) R ⊆
      ball 0 (capComplementRadius a) := by
    rintro _ ⟨x, hx, rfl⟩
    exact (stereoChart_mem_ball_of_inner_lt p ha ha' (hαcap x hx)).2
  have hV₁ : φ₁ '' closedBall (0 : EuclideanSpace ℝ (Fin 2)) R ⊆
      ball 0 (capComplementRadius a) := by
    rintro _ ⟨x, hx, rfl⟩
    exact (stereoChart_mem_ball_of_inner_lt p ha ha' (hβcap x hx)).2
  have h0 : (0 : EuclideanSpace ℝ (Fin 2)) ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) R :=
    mem_closedBall_self hR.le
  have hseg : ∀ t ∈ Icc (0 : ℝ) 1, (1 - t) • φ₀ 0 + t • φ₁ 0 ∈
      ball (0 : EuclideanSpace ℝ (Fin 2)) (capComplementRadius a) := fun t ht =>
    (convex_ball _ _) (hV₀ ⟨0, h0, rfl⟩) (hV₁ ⟨0, h0, rfl⟩) (by linarith [ht.2]) ht.1
      (by ring)
  obtain ⟨J, hJ, hJi, hJ0, hJ1, K, hK, hKV, hfix⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_isotopy_eqOn_closedBall_of_partialDiffeomorphs_of_subset_of_radius
      φ₀ φ₁ hR hs₀ hs₁ isOpen_ball hV₀ hV₁ hseg hori
  have hD : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2) ∞
      (fun z : ℝ × EuclideanSpace ℝ (Fin 2) => J z.1 z.2) := by
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    exact hJ.contMDiff
  have hDi : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2) ∞
      (fun z : ℝ × EuclideanSpace ℝ (Fin 2) => (J z.1).symm z.2) := by
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    exact hJi.contMDiff
  have hKt : K ⊆ c.target := by
    rw [hc, stereoChart_target]
    exact subset_univ K
  obtain ⟨Φ, hΦ, hΦi, hΦsrc, -, hΦc, hΦrefl, hKc, -, hΦfix⟩ :=
    PartialDiffeomorph.exists_isotopy_extension_of_isCompact c J hD hDi hK hKt
      (fun t y hy => (hfix t y hy).1)
  refine ⟨Φ, hΦ, hΦi, hΦrefl 0 hJ0, ?_, (c.symm '' K)ᶜ, hKc.isClosed.isOpen_compl, ?_,
    fun t θ hθ => hΦfix t θ hθ⟩
  · intro x hx
    have hαs : α x ∈ c.source := (stereoChart_mem_ball_of_inner_lt p ha ha' (hαcap x hx)).1
    have hβs : β x ∈ c.source := (stereoChart_mem_ball_of_inner_lt p ha ha' (hβcap x hx)).1
    have himg : Φ 1 (α x) ∈ c.source := by
      rw [← hΦsrc 1]
      exact ⟨α x, hαs, rfl⟩
    apply c.toPartialEquiv.injOn himg hβs
    rw [hΦc 1 (α x) hαs, ← hφ₀, hJ1 x hx, hφ₁]
  · intro θ hθ hmem
    obtain ⟨y, hyK, rfl⟩ := hmem
    have hlt := inner_lt_of_mem_ball p ha ha' (hKV hyK)
    exact absurd hθ (not_le.mpr hlt)

end DifferentialGeometry.Topology.Handle
