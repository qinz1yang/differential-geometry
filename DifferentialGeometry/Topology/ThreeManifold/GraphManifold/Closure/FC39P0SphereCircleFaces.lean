import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0SphereCircleBase

/-!
# FC39 producer, packet P0 (gate 1): the S³ circle kind meets the edge kind

Consumer of `sphereCircleBundle` (part A of the circle kind) and check of the ONE S³
configuration (review 49, T49-1): the vertical faces of the S³ edge bundle (the rims of the two
handles, `height = 1` over `C₂`) are EXACTLY the two `ψ`-faces of the circle region, i.e. the
chart image `J({ψ ∈ {1, 4}, r ∈ [1, 4]} × Circle)` (`sphereEdgeBundle_vertical_eq`); in
particular they lie in `M₃` (`sphereEdgeBundle_vertical_subset_region`).

Tools (also for part B, the corner charts): the antipode in the stereographic chart,
`−stereo_p⁻¹ w = stereo_p⁻¹ (−(4 / ‖w‖²) • w)` (`stereoChart_symm_neg_CIRCA`), so the north cap
direction `−stereo_N⁻¹ (ψ • c)` is the chart direction with `ψ ↦ 4 / ψ`, `c ↦ −c`
(`sphereCircleChart_neg`), and both handle charts in circle coordinates
(`cycleHandleChart_false_eq_circle`, `cycleHandleChart_true_eq_circle`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open DifferentialGeometry.Topology.Manifold Manifold
open scoped Manifold ContDiff Topology InnerProductSpace

namespace GC.GraphManifold.Assembly.FC39P0

local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "E3" => EuclideanSpace ℝ (Fin 3)

local instance sphereCircleFacesDim_CIRCA : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

/-! ## The antipode in the stereographic chart -/

/-- The scalar identity behind the antipode formula. -/
theorem stereo_neg_combination_CIRCA (u P : E3) {a : ℝ} (ha : 0 < a) :
    ((-(4 / a)) ^ 2 * a + 4)⁻¹ • (4 : ℝ) • (-(4 / a)) • u +
        ((-(4 / a)) ^ 2 * a + 4)⁻¹ • ((-(4 / a)) ^ 2 * a - 4) • P =
      -((a + 4)⁻¹ • (4 : ℝ) • u + (a + 4)⁻¹ • (a - 4) • P) := by
  have ha' : a ≠ 0 := ha.ne'
  have h4 : a + 4 ≠ 0 := by positivity
  have h1 : ((-(4 / a)) ^ 2 * a + 4)⁻¹ * 4 * (-(4 / a)) = -((a + 4)⁻¹ * 4) := by
    field_simp
    ring
  have h2 : ((-(4 / a)) ^ 2 * a + 4)⁻¹ * ((-(4 / a)) ^ 2 * a - 4) = -((a + 4)⁻¹ * (a - 4)) := by
    field_simp
    ring
  rw [smul_smul, smul_smul, smul_smul, smul_smul, smul_smul, h2, h1, neg_add, neg_smul, neg_smul]

/-- **The antipode in the stereographic chart**: `−stereo_p⁻¹ w = stereo_p⁻¹ (−(4 / ‖w‖²) • w)`
for `w ≠ 0`. -/
theorem stereoChart_symm_neg_CIRCA (p : sphere (0 : E3) 1) {w : E2} (hw : w ≠ 0) :
    -((Handle.stereoChart p).symm w : E3) =
      ((Handle.stereoChart p).symm (-(4 / ‖w‖ ^ 2) • w) : E3) := by
  rw [Handle.stereoChart_symm_apply, Handle.stereoChart_symm_apply,
    stereographic'_symm_apply (E := E3) (n := 2) p w,
    stereographic'_symm_apply (E := E3) (n := 2) p (-(4 / ‖w‖ ^ 2) • w)]
  dsimp only
  set U := (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) 2
    (ne_zero_of_mem_unit_sphere p)).repr
  have hnorm : ‖((U.symm w : (ℝ ∙ (p : E3))ᗮ) : E3)‖ = ‖w‖ := by
    rw [Submodule.norm_coe, LinearIsometryEquiv.norm_map]
  rw [map_smul, Submodule.coe_smul, norm_smul, hnorm, Real.norm_eq_abs, mul_pow, sq_abs]
  have ha : 0 < ‖w‖ ^ 2 := by positivity
  rw [stereo_neg_combination_CIRCA _ _ ha]

/-! ## The antipode on the circle and the north cap in the circle chart -/

/-- The antipode `c ↦ −c` of the circle. -/
def circleAntipode_CIRCA (s : Circle) : Circle :=
  unitOf (-(s : ℂ))

theorem coe_circleAntipode_CIRCA (s : Circle) : (circleAntipode_CIRCA s : ℂ) = -(s : ℂ) := by
  rw [circleAntipode_CIRCA, coe_unitOf (neg_ne_zero.2 (Circle.coe_ne_zero s)), norm_neg,
    Circle.norm_coe, inv_one, one_smul]

theorem planeOfCircle_antipode_CIRCA (s : Circle) :
    planeOfCircle (circleAntipode_CIRCA s) = -planeOfCircle s := by
  rw [planeOfCircle, planeOfCircle, coe_circleAntipode_CIRCA, map_neg]

theorem circleAntipode_antipode_CIRCA (s : Circle) :
    circleAntipode_CIRCA (circleAntipode_CIRCA s) = s :=
  Circle.ext (by rw [coe_circleAntipode_CIRCA, coe_circleAntipode_CIRCA, neg_neg])

/-- **The north cap direction in the circle chart**: `r • (−stereo_N⁻¹ (ψ • c)) = J((4/ψ, r), −c)`
(so the north cap `ψ' ≤ 1` of `cycleS3Handle true` is the band side `ψ = 4 / ψ' ≥ 4`). -/
theorem sphereCircleChart_neg {ψ : ℝ} (hψ : 0 < ψ) (r : ℝ) (s : Circle) :
    cycleBallAmbient false
        (r • -((Handle.stereoChart northPole).symm (ψ • planeOfCircle s) : E3)) =
      sphereCircleChart (sphereCircleEquiv.symm (4 / ψ, r), circleAntipode_CIRCA s) := by
  have hw : ψ • planeOfCircle s ≠ 0 := by
    intro h
    have hn := norm_smul_planeOfCircle_CIRCA hψ s
    rw [h, norm_zero] at hn
    exact hψ.ne' hn.symm
  rw [sphereCircleChart_equiv_symm, stereoChart_symm_neg_CIRCA northPole hw,
    norm_smul_planeOfCircle_CIRCA hψ, planeOfCircle_antipode_CIRCA]
  have he : -(4 / ψ ^ 2) • ψ • planeOfCircle s = (4 / ψ) • -planeOfCircle s := by
    rw [smul_smul, smul_neg, ← neg_smul]
    congr 2
    field_simp
  rw [he]

/-! ## The two handle charts in circle coordinates -/

theorem planeOfCircle_unitOf_CIRCA (w : E2) :
    ‖w‖ • planeOfCircle (unitOf (Complex.orthonormalBasisOneI.repr.symm w)) = w := by
  have h := congrArg Complex.orthonormalBasisOneI.repr
    (norm_smul_unitOf (Complex.orthonormalBasisOneI.repr.symm w))
  simpa only [planeOfCircle, map_smul, LinearIsometryEquiv.norm_map,
    LinearIsometryEquiv.apply_symm_apply] using h

/-- The south handle chart in circle coordinates: `χ_false (w, t) = J((‖w‖, ρ t), w / ‖w‖)`. -/
theorem cycleHandleChart_false_eq_circle (w : E2) (t : ℝ) :
    cycleHandleChart false (w, t) = sphereCircleChart
      (sphereCircleEquiv.symm (‖w‖, cycleHandleRadius t),
        unitOf (Complex.orthonormalBasisOneI.repr.symm w)) := by
  rw [cycleHandleChart_eq_FC39P0, sphereCircleChart_equiv_symm, planeOfCircle_unitOf_CIRCA]
  rfl

/-- The north handle chart in circle coordinates:
`χ_true (w, t) = J((4 / ‖w‖, ρ (1 − t)), −w / ‖w‖)`. -/
theorem cycleHandleChart_true_eq_circle {w : E2} (hw : w ≠ 0) (t : ℝ) :
    cycleHandleChart true (w, t) = sphereCircleChart
      (sphereCircleEquiv.symm (4 / ‖w‖, cycleHandleRadius (1 - t)),
        circleAntipode_CIRCA (unitOf (Complex.orthonormalBasisOneI.repr.symm w))) := by
  rw [← sphereCircleChart_neg (norm_pos_iff.2 hw), planeOfCircle_unitOf_CIRCA,
    cycleHandleChart_eq_FC39P0]
  rfl

/-! ## The edge vertical faces are the `ψ`-faces of the circle region -/

theorem cycleHandleRadius_mem_Icc_CIRCA {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    cycleHandleRadius t ∈ Icc (1 : ℝ) 4 := by
  have h0 : cycleHandleRadius 0 = 1 := by
    rw [cycleHandleRadius_inner (by norm_num)]
    norm_num
  have h1 : cycleHandleRadius 1 = 4 := by
    rw [cycleHandleRadius_outer (by norm_num)]
    norm_num
  have hm := cycleHandleRadius_strictMono.monotoneOn
  constructor
  · rw [← h0]
    exact hm ⟨le_rfl, zero_le_one⟩ ht ht.1
  · rw [← h1]
    exact hm ht ⟨zero_le_one, le_rfl⟩ ht.2

/-- The two `ψ`-faces of the circle base: `ψ ∈ {1, 4}`, `r ∈ [1, 4]`. -/
def sphereCirclePsiFaceSet : Set E2 :=
  sphereCircleEquiv ⁻¹' (({1, 4} : Set ℝ) ×ˢ Icc 1 4)

theorem sphereCirclePsiFaceSet_subset : sphereCirclePsiFaceSet ⊆ sphereCircleCbaseSet := by
  intro c hc
  refine ⟨?_, hc.2⟩
  rcases hc.1 with h | h <;> rw [h] <;> constructor <;> norm_num

/-- The edge-side condition `proj ∈ C₂` on the side `b` is `t ∈ [0, 1]`. -/
theorem edgeCbase_side_iff (b : Bool) {t : ℝ} (ht : t ∈ Ioo (-1 / 2 : ℝ) (3 / 2)) :
    t + edgeShift b ∈ edgeCbaseReal ↔ t ∈ Icc (0 : ℝ) 1 := by
  cases b <;> simp only [edgeShift, edgeCbaseReal, Bool.false_eq_true, ite_false, ite_true,
    add_zero, mem_union, mem_Icc] <;> constructor
  · rintro (h | h)
    · exact h
    · exact absurd h.1 (by linarith [ht.2])
  · exact Or.inl
  · rintro (h | h)
    · exact absurd h.2 (by linarith [ht.1])
    · constructor <;> linarith [h.1, h.2]
  · intro h
    exact Or.inr ⟨by linarith [h.1], by linarith [h.2]⟩

/-- **The edge vertical faces are exactly the `ψ`-faces of the circle region** (ONE S³
configuration): `V = J({ψ ∈ {1, 4}, r ∈ [1, 4]} × Circle)`; the south handle rims are the face
`ψ = 1`, the north handle rims the face `ψ = 4`. -/
theorem sphereEdgeBundle_vertical_eq :
    sphereEdgeBundle.vertical = sphereCircleChart '' (sphereCirclePsiFaceSet ×ˢ univ) := by
  change Subtype.val '' {x : edgeSource | edgeLineEquiv.symm (edgeProjE x.val) ∈ edgeCbaseReal ∧
    edgeHeightR x.val = 1} = _
  rw [image_val_edgeSource (fun s => edgeLineEquiv.symm s ∈ edgeCbaseReal) (· = 1)]
  ext x
  constructor
  · intro hx
    obtain ⟨b, p, ⟨hbox, hQ, hR⟩, rfl⟩ := mem_iUnion.1 hx
    change edgeLineEquiv.symm (edgeLineEquiv (p.2 + edgeShift b)) ∈ edgeCbaseReal at hQ
    rw [ContinuousLinearEquiv.symm_apply_apply, edgeCbase_side_iff b hbox.2] at hQ
    have hn : ‖p.1‖ = 1 := by
      have h0 := norm_nonneg p.1
      change ‖p.1‖ ^ 2 = 1 at hR
      nlinarith
    have hp1 : p.1 ≠ 0 := norm_ne_zero_iff.1 (by rw [hn]; norm_num)
    rcases p with ⟨w, t⟩
    change ‖w‖ = 1 at hn
    change w ≠ 0 at hp1
    change t ∈ Icc (0 : ℝ) 1 at hQ
    cases b
    · refine ⟨(sphereCircleEquiv.symm (‖w‖, cycleHandleRadius t),
        unitOf (Complex.orthonormalBasisOneI.repr.symm w)), ⟨?_, mem_univ _⟩,
          (cycleHandleChart_false_eq_circle w t).symm⟩
      change sphereCircleEquiv (sphereCircleEquiv.symm (‖w‖, cycleHandleRadius t)) ∈
        ({1, 4} : Set ℝ) ×ˢ Icc 1 4
      rw [ContinuousLinearEquiv.apply_symm_apply, hn]
      exact ⟨Or.inl rfl, cycleHandleRadius_mem_Icc_CIRCA hQ⟩
    · refine ⟨(sphereCircleEquiv.symm (4 / ‖w‖, cycleHandleRadius (1 - t)),
        circleAntipode_CIRCA (unitOf (Complex.orthonormalBasisOneI.repr.symm w))),
          ⟨?_, mem_univ _⟩, (cycleHandleChart_true_eq_circle hp1 t).symm⟩
      change sphereCircleEquiv (sphereCircleEquiv.symm (4 / ‖w‖, cycleHandleRadius (1 - t))) ∈
        ({1, 4} : Set ℝ) ×ˢ Icc 1 4
      rw [ContinuousLinearEquiv.apply_symm_apply, hn]
      refine ⟨Or.inr (by norm_num), cycleHandleRadius_mem_Icc_CIRCA ?_⟩
      constructor <;> linarith [hQ.1, hQ.2]
  · rintro ⟨⟨c, s⟩, ⟨hc, -⟩, rfl⟩
    obtain ⟨hψ, hr⟩ := hc
    change (sphereCircleEquiv c).1 ∈ ({1, 4} : Set ℝ) at hψ
    change (sphereCircleEquiv c).2 ∈ Icc (1 : ℝ) 4 at hr
    obtain ⟨⟨t, ht⟩, htr, -⟩ := cycleHandleRadius_inverse hr
    have hc' : c = sphereCircleEquiv.symm ((sphereCircleEquiv c).1, (sphereCircleEquiv c).2) :=
      (sphereCircleEquiv.symm_apply_apply c).symm
    rw [hc']
    rcases hψ with h | h
    · refine mem_iUnion.2 ⟨false, (planeOfCircle s, t), ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
      · rw [mem_ball_zero_iff, planeOfCircle_norm_CIRCA]
        norm_num
      · constructor <;> linarith [ht.1, ht.2]
      · change edgeLineEquiv.symm (edgeLineEquiv (t + edgeShift false)) ∈ edgeCbaseReal
        rw [ContinuousLinearEquiv.symm_apply_apply,
          edgeCbase_side_iff false ⟨by linarith [ht.1], by linarith [ht.2]⟩]
        exact ht
      · change ‖planeOfCircle s‖ ^ 2 = 1
        rw [planeOfCircle_norm_CIRCA, one_pow]
      · rw [h, ← htr, sphereCircleChart_equiv_symm, cycleHandleChart_eq_FC39P0, one_smul]
        rfl
    · refine mem_iUnion.2 ⟨true, (planeOfCircle (circleAntipode_CIRCA s), 1 - t),
        ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
      · rw [mem_ball_zero_iff, planeOfCircle_norm_CIRCA]
        norm_num
      · constructor <;> linarith [ht.1, ht.2]
      · change edgeLineEquiv.symm (edgeLineEquiv (1 - t + edgeShift true)) ∈ edgeCbaseReal
        rw [ContinuousLinearEquiv.symm_apply_apply,
          edgeCbase_side_iff true ⟨by linarith [ht.2], by linarith [ht.1]⟩]
        constructor <;> linarith [ht.1, ht.2]
      · change ‖planeOfCircle (circleAntipode_CIRCA s)‖ ^ 2 = 1
        rw [planeOfCircle_norm_CIRCA, one_pow]
      · have hs := sphereCircleChart_neg (ψ := 1) one_pos (sphereCircleEquiv c).2
          (circleAntipode_CIRCA s)
        rw [one_smul, circleAntipode_antipode_CIRCA, div_one] at hs
        rw [h, hs.symm, cycleHandleChart_eq_FC39P0, ← htr]
        simp only [↓reduceIte, sub_sub_cancel]

/-- The edge vertical faces lie in the circle region `M₃`. -/
theorem sphereEdgeBundle_vertical_subset_region :
    sphereEdgeBundle.vertical ⊆ sphereCircleBundle.region := by
  rw [sphereEdgeBundle_vertical_eq, sphereCircleBundle_region]
  exact image_mono (prod_mono sphereCirclePsiFaceSet_subset subset_rfl)

end GC.GraphManifold.Assembly.FC39P0
