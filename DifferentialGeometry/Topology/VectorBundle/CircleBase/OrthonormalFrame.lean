import DifferentialGeometry.Topology.VectorBundle.CircleBase.ZeroSectionOrientation
import DifferentialGeometry.Topology.Manifold.AddCircle.ParameterDerivative
import DifferentialGeometry.Topology.Manifold.Quotient

/-!
# Oriented rank-two bundles over the circle have a smooth orthonormal frame (P1a)

F7-LFR51 item P1a (frozen statement in `build-logs/scratch/F7-LFR51/P1Inputs.lean`), on the path
LFR54 → `ZeroModel.solidTorus`: a smooth Riemannian rank-two bundle over `AddCircle 1` whose total
space carries a smooth orientation has a smooth global orthonormal frame
(`exists_orthonormal_frame_of_orientable_totalSpace_circle`).

Route: a frame along the covering line on `(-1, 3)` (`exists_orthonormal_along_Ioo`); its holonomy
over one period is a rotation by the orientation of the total space (`planeDet_frameShift_pos`);
rotating back through `smoothTransition t · α` makes the frame agree with its shift at `t = 1`,
where the two are blended (`exists_blend_along`); the resulting frame is periodic near a point and
descends to the circle (`exists_orthonormal_frame_of_periodic_along`).
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter
open scoped ContDiff Topology Manifold InnerProductSpace

namespace DifferentialGeometry.Topology.VectorBundle

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : AddCircle (1 : ℝ) → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ b, NormedAddCommGroup (V b)] [∀ b, InnerProductSpace ℝ (V b)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℝ)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, ℝ) ∞ F V]

omit [FiniteDimensional ℝ F] [∀ b, InnerProductSpace ℝ (V b)] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℝ)] [IsContMDiffRiemannianBundle 𝓘(ℝ, ℝ) ∞ F V] in
/-- Smoothness descends along the covering map at a point. -/
theorem contMDiffAt_of_comp_coe {g : AddCircle (1 : ℝ) → TotalSpace F V} {t : ℝ}
    (h : ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) ∞
      (fun s : ℝ => g ((s : ℝ) : AddCircle (1 : ℝ))) t) :
    ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) ∞ g ((t : ℝ) : AddCircle (1 : ℝ)) := by
  have hlocal := AddCircle.isLocalDiffeomorph_coe t
  have hleft : hlocal.localInverse ((t : ℝ) : AddCircle (1 : ℝ)) = t :=
    hlocal.localInverse_left_inv hlocal.localInverse_mem_target
  have hsmooth : ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) ∞
      ((fun s : ℝ => g ((s : ℝ) : AddCircle (1 : ℝ))) ∘ hlocal.localInverse)
      ((t : ℝ) : AddCircle (1 : ℝ)) := by
    refine ContMDiffAt.comp (g := fun s : ℝ => g ((s : ℝ) : AddCircle (1 : ℝ)))
      ((t : ℝ) : AddCircle (1 : ℝ)) ?_ hlocal.contMDiffAt_localInverse
    rw [hleft]
    exact h
  apply hsmooth.congr_of_eventuallyEq
  filter_upwards [hlocal.localInverse_open_source.mem_nhds hlocal.localInverse_mem_source]
    with b hb
  change g b = g ((hlocal.localInverse b : ℝ) : AddCircle (1 : ℝ))
  rw [hlocal.localInverse_right_inv hb]

omit [FiniteDimensional ℝ F] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℝ)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, ℝ) ∞ F V] in
/-- **Descent of a frame along the line.** A smooth orthonormal frame along the covering line on an
open set containing `[c₀, c₀ + 1]` that is one-periodic near `c₀` gives a smooth orthonormal frame
of the bundle over the circle. -/
theorem exists_orthonormal_frame_of_periodic_along {D : Set ℝ} (hD : IsOpen D) {c₀ : ℝ}
    (hIcc : Icc c₀ (c₀ + 1) ⊆ D) {w : Fin 2 → (t : ℝ) → V t}
    (hw : ∀ i, ContMDiffOn 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) ∞
      (fun t : ℝ => (⟨(t : AddCircle (1 : ℝ)), w i t⟩ : TotalSpace F V)) D)
    (hon : ∀ t ∈ D, Orthonormal ℝ (fun i => w i t))
    (hper : ∀ᶠ t in 𝓝 c₀, ∀ i, (⟨((t + 1 : ℝ) : AddCircle (1 : ℝ)), w i (t + 1)⟩ :
      TotalSpace F V) = ⟨((t : ℝ) : AddCircle (1 : ℝ)), w i t⟩) :
    ∃ s : Fin 2 → (b : AddCircle (1 : ℝ)) → V b,
      (∀ i, ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) ∞
        (fun b => (⟨b, s i b⟩ : TotalSpace F V))) ∧
      ∀ b, Orthonormal ℝ (fun i => s i b) := by
  have hfact_LFR54P1 : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  let rep : AddCircle (1 : ℝ) → ℝ := fun b => (AddCircle.equivIco 1 c₀ b : ℝ)
  have hrepmem : ∀ b, rep b ∈ Ico c₀ (c₀ + 1) := fun b => (AddCircle.equivIco 1 c₀ b).2
  have hrep : ∀ b, ((rep b : ℝ) : AddCircle (1 : ℝ)) = b := by
    intro b
    have h := (AddCircle.equivIco 1 c₀).symm_apply_apply b
    rw [AddCircle.equivIco, QuotientAddGroup.equivIcoMod_symm_apply] at h
    exact h
  have hrep_of : ∀ t ∈ Ico c₀ (c₀ + 1), rep ((t : ℝ) : AddCircle (1 : ℝ)) = t := by
    intro t ht
    simp only [rep]
    rw [AddCircle.equivIco_coe_eq ht]
  let s : Fin 2 → (b : AddCircle (1 : ℝ)) → V b := fun i b =>
    cast (congrArg V (hrep b)) (w i (rep b))
  have hs : ∀ i b, (⟨b, s i b⟩ : TotalSpace F V) = ⟨((rep b : ℝ) : AddCircle (1 : ℝ)), w i (rep b)⟩ :=
    fun i b => totalSpace_mk_cast (hrep b) (w i (rep b))
  have hDmem : ∀ b, rep b ∈ D := fun b => hIcc (Ico_subset_Icc_self (hrepmem b))
  refine ⟨s, fun i => ?_, fun b => ?_⟩
  · intro b
    rw [← hrep b]
    apply contMDiffAt_of_comp_coe
    have ht := hrepmem b
    set t := rep b with htdef
    have hsm : ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) ∞
        (fun t : ℝ => (⟨(t : AddCircle (1 : ℝ)), w i t⟩ : TotalSpace F V)) t :=
      (hw i).contMDiffAt (hD.mem_nhds (hDmem b))
    refine hsm.congr_of_eventuallyEq ?_
    have hev : ∀ᶠ t' in 𝓝 t, t' ∈ Ioo (c₀ - 1) (c₀ + 1) ∧
        (t' < c₀ → ∀ i, (⟨((t' + 1 : ℝ) : AddCircle (1 : ℝ)), w i (t' + 1)⟩ : TotalSpace F V) =
          ⟨((t' : ℝ) : AddCircle (1 : ℝ)), w i t'⟩) := by
      rcases eq_or_lt_of_le ht.1 with heq | hlt
      · rw [← heq]
        filter_upwards [isOpen_Ioo.mem_nhds (show c₀ ∈ Ioo (c₀ - 1) (c₀ + 1) from
          ⟨by linarith, by linarith⟩), hper] with t' h1 h2
        exact ⟨h1, fun _ => h2⟩
      · filter_upwards [isOpen_Ioo.mem_nhds (show t ∈ Ioo c₀ (c₀ + 1) from ⟨hlt, ht.2⟩)]
          with t' h1
        exact ⟨⟨by linarith [h1.1], h1.2⟩, fun h => absurd h1.1 (not_lt.mpr h.le)⟩
    filter_upwards [hev] with t' ht'
    obtain ⟨hmem, hper'⟩ := ht'
    rw [hs]
    by_cases hlt : t' < c₀
    · have hq : ((t' : ℝ) : AddCircle (1 : ℝ)) = ((t' + 1 : ℝ) : AddCircle (1 : ℝ)) := by
        rw [AddCircle.coe_add, AddCircle.coe_period, add_zero]
      have hr : rep ((t' : ℝ) : AddCircle (1 : ℝ)) = t' + 1 := by
        rw [hq]
        exact hrep_of (t' + 1) ⟨by linarith [hmem.1], by linarith⟩
      rw [hr]
      exact hper' hlt i
    · have hr : rep ((t' : ℝ) : AddCircle (1 : ℝ)) = t' :=
        hrep_of t' ⟨not_lt.mp hlt, hmem.2⟩
      rw [hr]
  · have h := hon (rep b) (hDmem b)
    refine orthonormal_of_inner ?_ ?_ ?_
    · exact (inner_cast_cast (hrep b) _ _).trans (inner_self_of_orthonormal h 0)
    · exact (inner_cast_cast (hrep b) _ _).trans (inner_self_of_orthonormal h 1)
    · exact (inner_cast_cast (hrep b) _ _).trans (inner_zero_one_of_orthonormal h)

/-- **P1a (oriented rank-two bundles over the circle).** A smooth Riemannian bundle of rank two over
`AddCircle 1` whose total space carries a smooth orientation has a smooth global orthonormal
frame. -/
theorem exists_orthonormal_frame_of_orientable_totalSpace_circle
    (hF : Module.finrank ℝ F = 2)
    (oV : DifferentialGeometry.Topology.Manifold.SmoothOrientation (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F))
      (TotalSpace F V)) :
    ∃ s : Fin 2 → (b : AddCircle (1 : ℝ)) → V b,
      (∀ i, ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) ∞
        (fun b => (⟨b, s i b⟩ : TotalSpace F V))) ∧
      ∀ b, Orthonormal ℝ (fun i => s i b) := by
  obtain ⟨u, hu, hon⟩ := exists_orthonormal_along_Ioo (V := V) hF (-1) 3
  have hhol := planeDet_frameShift_pos hF oV hu hon (t₁ := 0) (by norm_num) (by norm_num)
  rw [zero_add] at hhol
  have h1mem : (1 : ℝ) ∈ Ioo (-1) 3 := ⟨by norm_num, by norm_num⟩
  have h2 := finrank_fiber_eq_two (V := V) hF ((1 : ℝ) : AddCircle (1 : ℝ))
  have hfd_LFR54P1 := finiteDimensional_fiber_of_two (V := V) hF ((1 : ℝ) : AddCircle (1 : ℝ))
  set x : Fin 2 → V ((1 : ℝ) : AddCircle (1 : ℝ)) := fun i => frameShift V u i 1 with hxdef
  set y : Fin 2 → V ((1 : ℝ) : AddCircle (1 : ℝ)) := fun i => u i 1 with hydef
  have hy : Orthonormal ℝ y := hon 1 h1mem
  have hx : Orthonormal ℝ x :=
    (frameShift_smooth hu hon).2 1 (show (1 : ℝ) - 1 ∈ Ioo (-1) 3 by norm_num)
  have hpos : 0 < planeDet y x := by
    have hsym : planeDet y x = planeDet x y := by
      simp only [planeDet]
      rw [real_inner_comm (y 0) (x 0), real_inner_comm (y 1) (x 1), real_inner_comm (y 0) (x 1),
        real_inner_comm (y 1) (x 0)]
      ring
    rw [hsym]
    exact hhol
  obtain ⟨α, hα, hβ⟩ := exists_cos_sin_eq (inner_sq_add_inner_sq_eq_one h2 hy hx)
  have hrot : y = planeRot α x := eq_planeRot_of_planeDet_pos h2 hy hx hpos hα hβ
  -- rotate the frame back through `smoothTransition t · α`
  let u' : Fin 2 → (t : ℝ) → V t := fun i t =>
    planeRot (-(Real.smoothTransition t * α)) (fun j => u j t) i
  have hst : ContDiff ℝ ∞ (fun t : ℝ => -(Real.smoothTransition t * α)) :=
    (Real.smoothTransition.contDiff.mul contDiff_const).neg
  have hu' : ∀ i, ContMDiffOn 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) ∞
      (fun t : ℝ => (⟨(t : AddCircle (1 : ℝ)), u' i t⟩ : TotalSpace F V)) (Ioo (-1) 3) :=
    fun i t ht => (contMDiffAt_along_planeRot (fun j => (hu j).contMDiffAt
      (isOpen_Ioo.mem_nhds ht)) hst.contMDiff.contMDiffAt i).contMDiffWithinAt
  have hon' : ∀ t ∈ Ioo (-1 : ℝ) 3, Orthonormal ℝ (fun i => u' i t) :=
    fun t ht => orthonormal_planeRot (hon t ht) _
  have hu'1 : (fun i => u' i 1) = x := by
    change planeRot (-(Real.smoothTransition 1 * α)) y = x
    rw [Real.smoothTransition.one_of_one_le le_rfl, one_mul, hrot, planeRot_planeRot,
      add_neg_cancel, planeRot_zero_angle]
  have hsh : ∀ i, frameShift V u' i 1 = frameShift V u i 1 := by
    intro i
    simp only [frameShift]
    congr 1
    change planeRot (-(Real.smoothTransition (1 - 1) * α)) (fun j => u j (1 - 1)) i = u i (1 - 1)
    rw [Real.smoothTransition.zero_of_nonpos (by norm_num), zero_mul, neg_zero,
      planeRot_zero_angle]
  have heq : ∀ i, frameShift V u' i 1 = u' i 1 := fun i => by
    rw [hsh i]
    exact (congrFun hu'1 i).symm
  -- blend `u'` with its shift at `t = 1`
  let U' : Set ℝ := (fun t => t - 1) ⁻¹' Ioo (-1) 3 ∩ Ioo (3 / 4) (5 / 4)
  have hU' : IsOpen U' :=
    (isOpen_Ioo.preimage (continuous_id.sub continuous_const)).inter isOpen_Ioo
  have h1U' : (1 : ℝ) ∈ U' := ⟨by norm_num, by norm_num, by norm_num⟩
  have hsm := frameShift_smooth hu' hon'
  obtain ⟨r, hr, w, hw, honw, hleft, hright, hwin⟩ := exists_blend_along hF isOpen_Ioo hU' hu'
    hon' (fun i => (hsm.1 i).mono inter_subset_left) (fun t ht => hsm.2 t ht.1) h1mem h1U' heq
  have hr8 : r ≤ 1 / 8 := by
    by_contra hcon
    have hmem := hwin (show (5 / 4 : ℝ) ∈ Ioo (1 - 2 * r) (1 + 2 * r) from
      ⟨by linarith, by linarith [not_le.mp hcon]⟩)
    exact absurd hmem.2.2.2 (lt_irrefl _)
  let D : Set ℝ := Ioo (-1) 3 ∩ Iio (1 + r) ∪ U' ∩ Ioi (1 - r)
  have hD : IsOpen D := (isOpen_Ioo.inter isOpen_Iio).union (hU'.inter isOpen_Ioi)
  have hIcc : Icc (3 * r / 2) (3 * r / 2 + 1) ⊆ D := by
    intro t ht
    by_cases htr : t < 1 + r
    · exact Or.inl ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, htr⟩
    · refine Or.inr ⟨⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, by linarith [not_lt.mp htr],
        by linarith [ht.2]⟩, ?_⟩
      change 1 - r < t
      linarith [not_lt.mp htr]
  have hper : ∀ᶠ t in 𝓝 (3 * r / 2), ∀ i,
      (⟨((t + 1 : ℝ) : AddCircle (1 : ℝ)), w i (t + 1)⟩ : TotalSpace F V) =
        ⟨((t : ℝ) : AddCircle (1 : ℝ)), w i t⟩ := by
    filter_upwards [isOpen_Ioo.mem_nhds (show 3 * r / 2 ∈ Ioo r (2 * r) from
      ⟨by linarith, by linarith⟩)] with t ht i
    rw [hright (t + 1) (by linarith [ht.1]) i, hleft t (by linarith [ht.2]) i,
      totalSpace_frameShift, add_sub_cancel_right]
  exact exists_orthonormal_frame_of_periodic_along hD hIcc hw honw hper

end DifferentialGeometry.Topology.VectorBundle
