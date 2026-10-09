import DifferentialGeometry.Topology.ClosedBall.UnitDisk
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Order.ProjIcc

/-!
# A closed disk with a collar attached along its boundary is a closed disk

Let `h : Disk (m+1) → X` be a continuous injection and `c : S^m × [0,1] → X` a continuous injection
with `c (θ, 0) = h θ` on the boundary sphere and `range h ∩ range c = h(∂)`.  Then the radial gluing
`x ↦ h (2x)` for `‖x‖ ≤ 1/2`, `x ↦ c (x/‖x‖, 2‖x‖ - 1)` for `‖x‖ ≥ 1/2` is a continuous injection
`Disk (m+1) → X` onto `range h ∪ range c`, whose boundary sphere goes onto the far end `c(S^m × {1})`.

Used twice by lane SF-C: for FC40b (a disk with an annulus attached, then a second disk, is a sphere)
and for LFR24's smooth disk (a topological disk sublevel with a product collar).
-/

set_option autoImplicit false

open Set Metric Function

namespace DifferentialGeometry.Topology.Surface

open DifferentialGeometry.Topology

variable {m : ℕ}

/-- The base point `e₀` of the unit sphere, used as a junk value at the origin. -/
noncomputable def collarSpherePoint (m : ℕ) : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 :=
  ⟨EuclideanSpace.single 0 1, by simp⟩

/-- The inner radial piece `x ↦ 2x`, clamped into the unit disk. -/
noncomputable def collarInner (x : Disk (m + 1)) : Disk (m + 1) :=
  ⟨(2 / max 1 (2 * ‖(x : EuclideanSpace ℝ (Fin (m + 1)))‖)) • (x : EuclideanSpace ℝ (Fin (m + 1))), by
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs,
      abs_of_pos (div_pos two_pos (lt_of_lt_of_le one_pos (le_max_left _ _)))]
    have hpos : 0 < max 1 (2 * ‖(x : EuclideanSpace ℝ (Fin (m + 1)))‖) := lt_of_lt_of_le one_pos (le_max_left _ _)
    rw [div_mul_eq_mul_div, div_le_one hpos]
    linarith [le_max_right 1 (2 * ‖(x : EuclideanSpace ℝ (Fin (m + 1)))‖)]⟩

/-- The angular coordinate `x/‖x‖` (junk at the origin). -/
noncomputable def collarAngle (x : Disk (m + 1)) : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 := by
  classical
  exact if hx : (x : EuclideanSpace ℝ (Fin (m + 1))) = 0 then collarSpherePoint m else
    ⟨‖(x : EuclideanSpace ℝ (Fin (m + 1)))‖⁻¹ • (x : EuclideanSpace ℝ (Fin (m + 1))), by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]⟩

/-- The collar coordinate `2‖x‖ - 1`, projected to `[0,1]`. -/
noncomputable def collarHeight (x : Disk (m + 1)) : Icc (0 : ℝ) 1 :=
  projIcc 0 1 zero_le_one (2 * ‖(x : EuclideanSpace ℝ (Fin (m + 1)))‖ - 1)

/-- The radial gluing of a disk and a collar. -/
noncomputable def collarGlue {X : Type*} (h : Disk (m + 1) → X)
    (c : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 × Icc (0 : ℝ) 1 → X) (x : Disk (m + 1)) : X :=
  if ‖(x : EuclideanSpace ℝ (Fin (m + 1)))‖ ≤ 1 / 2 then h (collarInner x) else c (collarAngle x, collarHeight x)

theorem continuous_collarInner : Continuous (collarInner (m := m)) := by
  apply Continuous.subtype_mk
  have hd : Continuous fun x : Disk (m + 1) =>
      2 / max 1 (2 * ‖(x : EuclideanSpace ℝ (Fin (m + 1)))‖) :=
    continuous_const.div (continuous_const.max (continuous_const.mul
      continuous_subtype_val.norm)) fun x => (lt_of_lt_of_le one_pos (le_max_left _ _)).ne'
  exact hd.smul continuous_subtype_val

theorem collarInner_coe_of_le {x : Disk (m + 1)} (hx : ‖(x : EuclideanSpace ℝ (Fin (m + 1)))‖ ≤ 1 / 2) :
    (collarInner x : EuclideanSpace ℝ (Fin (m + 1))) = (2 : ℝ) • (x : EuclideanSpace ℝ (Fin (m + 1))) := by
  have hmax : max 1 (2 * ‖(x : EuclideanSpace ℝ (Fin (m + 1)))‖) = 1 := max_eq_left (by linarith)
  simp only [collarInner, hmax, div_one]

theorem collarAngle_coe_of_ne {x : Disk (m + 1)} (hx : (x : EuclideanSpace ℝ (Fin (m + 1))) ≠ 0) :
    (collarAngle x : EuclideanSpace ℝ (Fin (m + 1))) = ‖(x : EuclideanSpace ℝ (Fin (m + 1)))‖⁻¹ • (x : EuclideanSpace ℝ (Fin (m + 1))) := by
  simp [collarAngle, hx]

theorem continuousOn_collarAngle :
    ContinuousOn (collarAngle (m := m)) {x | (x : EuclideanSpace ℝ (Fin (m + 1))) ≠ 0} := by
  intro x hx
  have hev : (fun y : Disk (m + 1) => (collarAngle y : EuclideanSpace ℝ (Fin (m + 1)))) =ᶠ[nhds x]
      fun y => ‖(y : EuclideanSpace ℝ (Fin (m + 1)))‖⁻¹ • (y : EuclideanSpace ℝ (Fin (m + 1))) := by
    filter_upwards [(isOpen_ne_fun continuous_subtype_val continuous_const).mem_nhds hx]
      with y hy using collarAngle_coe_of_ne hy
  have hc : ContinuousAt (fun y : Disk (m + 1) => ‖(y : EuclideanSpace ℝ (Fin (m + 1)))‖⁻¹ • (y : EuclideanSpace ℝ (Fin (m + 1)))) x :=
    ((continuous_subtype_val.norm.continuousAt).inv₀ (norm_ne_zero_iff.mpr hx)).smul
      continuous_subtype_val.continuousAt
  exact (Topology.IsInducing.subtypeVal.continuousAt_iff.mpr
    (hc.congr hev.symm)).continuousWithinAt

theorem collarHeight_coe_of_mem {x : Disk (m + 1)} (hx : 1 / 2 ≤ ‖(x : EuclideanSpace ℝ (Fin (m + 1)))‖) :
    (collarHeight x : ℝ) = 2 * ‖(x : EuclideanSpace ℝ (Fin (m + 1)))‖ - 1 := by
  have h1 : ‖(x : EuclideanSpace ℝ (Fin (m + 1)))‖ ≤ 1 := mem_closedBall_zero_iff.mp x.2
  rw [collarHeight, projIcc_of_mem]
  constructor <;> linarith

theorem ne_zero_of_half_le {x : Disk (m + 1)} (hx : 1 / 2 ≤ ‖(x : EuclideanSpace ℝ (Fin (m + 1)))‖) : (x : EuclideanSpace ℝ (Fin (m + 1))) ≠ 0 := by
  intro h0
  rw [h0, norm_zero] at hx
  linarith

variable {X : Type*} {h : Disk (m + 1) → X}
  {c : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 × Icc (0 : ℝ) 1 → X}

theorem collarGlue_of_le {x : Disk (m + 1)} (hx : ‖(x : EuclideanSpace ℝ (Fin (m + 1)))‖ ≤ 1 / 2) :
    collarGlue h c x = h (collarInner x) := by
  unfold collarGlue
  split_ifs with h'
  · rfl
  · exact absurd hx h'

theorem collarGlue_of_lt {x : Disk (m + 1)} (hx : 1 / 2 < ‖(x : EuclideanSpace ℝ (Fin (m + 1)))‖) :
    collarGlue h c x = c (collarAngle x, collarHeight x) := by
  unfold collarGlue
  split_ifs with h'
  · exact absurd h' (not_le.mpr hx)
  · rfl

/-- Continuity of the radial gluing, given that `c` and `h` agree on the boundary sphere. -/
theorem continuous_collarGlue [TopologicalSpace X] (hh : Continuous h) (hc : Continuous c)
    (hmatch : ∀ (θ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) (t : Icc (0 : ℝ) 1) (z : Disk (m + 1)), (t : ℝ) = 0 →
      (z : EuclideanSpace ℝ (Fin (m + 1))) = θ → c (θ, t) = h z) :
    Continuous (collarGlue h c) := by
  classical
  unfold collarGlue
  refine continuous_if_le continuous_subtype_val.norm continuous_const
    (hh.comp continuous_collarInner).continuousOn ?_ ?_
  · refine hc.comp_continuousOn (ContinuousOn.prodMk ?_ ?_)
    · exact continuousOn_collarAngle.mono fun x hx => ne_zero_of_half_le hx
    · exact (continuous_projIcc.comp ((continuous_const.mul continuous_subtype_val.norm).sub
        continuous_const)).continuousOn
  · intro x hx
    have hx' : ‖(x : EuclideanSpace ℝ (Fin (m + 1)))‖ = 1 / 2 := hx
    have h0 := ne_zero_of_half_le hx'.ge
    symm
    apply hmatch
    · rw [collarHeight_coe_of_mem hx'.ge, hx']
      ring
    · rw [collarAngle_coe_of_ne h0, collarInner_coe_of_le hx'.le, hx']
      norm_num

/-- Injectivity of the radial gluing, when the disk meets the collar only at its `0`-end. -/
theorem injective_collarGlue (hh : Injective h) (hc : Injective c)
    (hinter : ∀ z w, h z = c w → (w.2 : ℝ) = 0) :
    Injective (collarGlue h c) := by
  have hmixed : ∀ x y : Disk (m + 1), ‖(x : EuclideanSpace ℝ (Fin (m + 1)))‖ ≤ 1 / 2 → 1 / 2 < ‖(y : EuclideanSpace ℝ (Fin (m + 1)))‖ →
      collarGlue h c x ≠ collarGlue h c y := by
    intro x y hx hy hxy
    rw [collarGlue_of_le hx, collarGlue_of_lt hy] at hxy
    have h0 := hinter _ _ hxy
    simp only at h0
    rw [collarHeight_coe_of_mem hy.le] at h0
    linarith
  intro x y hxy
  rcases le_or_gt ‖(x : EuclideanSpace ℝ (Fin (m + 1)))‖ (1 / 2) with hx | hx <;>
    rcases le_or_gt ‖(y : EuclideanSpace ℝ (Fin (m + 1)))‖ (1 / 2) with hy | hy
  · rw [collarGlue_of_le hx, collarGlue_of_le hy] at hxy
    have h2 := congrArg Subtype.val (hh hxy)
    rw [collarInner_coe_of_le hx, collarInner_coe_of_le hy] at h2
    exact Subtype.ext (smul_right_injective _ two_ne_zero h2)
  · exact absurd hxy (hmixed x y hx hy)
  · exact absurd hxy.symm (hmixed y x hy hx)
  · rw [collarGlue_of_lt hx, collarGlue_of_lt hy] at hxy
    have hp := hc hxy
    have ha := congrArg Subtype.val (congrArg Prod.fst hp)
    have ht := congrArg Subtype.val (congrArg Prod.snd hp)
    simp only at ha ht
    rw [collarHeight_coe_of_mem hx.le, collarHeight_coe_of_mem hy.le] at ht
    have hn : ‖(x : EuclideanSpace ℝ (Fin (m + 1)))‖ = ‖(y : EuclideanSpace ℝ (Fin (m + 1)))‖ := by linarith
    rw [collarAngle_coe_of_ne (ne_zero_of_half_le hx.le),
      collarAngle_coe_of_ne (ne_zero_of_half_le hy.le), hn] at ha
    have hpos : ‖(y : EuclideanSpace ℝ (Fin (m + 1)))‖⁻¹ ≠ 0 := inv_ne_zero (by linarith)
    exact Subtype.ext (smul_right_injective _ hpos ha)

/-- The range of the radial gluing is the union of the disk and the collar. -/
theorem range_collarGlue
    (hmatch : ∀ (θ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) (t : Icc (0 : ℝ) 1) (z : Disk (m + 1)), (t : ℝ) = 0 →
      (z : EuclideanSpace ℝ (Fin (m + 1))) = θ → c (θ, t) = h z) :
    range (collarGlue h c) = range h ∪ range c := by
  apply Subset.antisymm
  · rintro _ ⟨x, rfl⟩
    rcases le_or_gt ‖(x : EuclideanSpace ℝ (Fin (m + 1)))‖ (1 / 2) with hx | hx
    · exact Or.inl ⟨_, (collarGlue_of_le hx).symm⟩
    · exact Or.inr ⟨_, (collarGlue_of_lt hx).symm⟩
  · rintro _ (⟨z, rfl⟩ | ⟨⟨θ, t⟩, rfl⟩)
    · have hz : ‖(z : EuclideanSpace ℝ (Fin (m + 1)))‖ ≤ 1 := mem_closedBall_zero_iff.mp z.2
      let x : Disk (m + 1) := ⟨(1 / 2 : ℝ) • (z : EuclideanSpace ℝ (Fin (m + 1))), by
        rw [mem_closedBall_zero_iff, norm_smul]
        norm_num
        linarith⟩
      have hx : ‖(x : EuclideanSpace ℝ (Fin (m + 1)))‖ ≤ 1 / 2 := by
        change ‖(1 / 2 : ℝ) • (z : EuclideanSpace ℝ (Fin (m + 1)))‖ ≤ 1 / 2
        rw [norm_smul]
        norm_num
        linarith
      refine ⟨x, ?_⟩
      rw [collarGlue_of_le hx]
      congr 1
      apply Subtype.ext
      rw [collarInner_coe_of_le hx]
      change (2 : ℝ) • (1 / 2 : ℝ) • (z : EuclideanSpace ℝ (Fin (m + 1))) = z
      rw [smul_smul]
      norm_num
    · have hθ : ‖(θ : EuclideanSpace ℝ (Fin (m + 1)))‖ = 1 := mem_sphere_zero_iff_norm.mp θ.2
      have ht0 : (0 : ℝ) ≤ t := t.2.1
      have ht1 : (t : ℝ) ≤ 1 := t.2.2
      let x : Disk (m + 1) := ⟨((1 + t) / 2 : ℝ) • (θ : EuclideanSpace ℝ (Fin (m + 1))), by
        rw [mem_closedBall_zero_iff, norm_smul, hθ, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
        linarith⟩
      have hxn : ‖(x : EuclideanSpace ℝ (Fin (m + 1)))‖ = (1 + t) / 2 := by
        change ‖((1 + t) / 2 : ℝ) • (θ : EuclideanSpace ℝ (Fin (m + 1)))‖ = _
        rw [norm_smul, hθ, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
        ring
      refine ⟨x, ?_⟩
      rcases eq_or_lt_of_le ht0 with h0 | hpos
      · have hx : ‖(x : EuclideanSpace ℝ (Fin (m + 1)))‖ ≤ 1 / 2 := by rw [hxn, ← h0]; norm_num
        rw [collarGlue_of_le hx]
        symm
        apply hmatch θ t _ h0.symm
        rw [collarInner_coe_of_le hx]
        change (2 : ℝ) • ((1 + t) / 2 : ℝ) • (θ : EuclideanSpace ℝ (Fin (m + 1))) = θ
        rw [smul_smul, ← h0]
        norm_num
      · have hx : 1 / 2 < ‖(x : EuclideanSpace ℝ (Fin (m + 1)))‖ := by rw [hxn]; linarith
        rw [collarGlue_of_lt hx]
        congr 1
        refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
        · rw [collarAngle_coe_of_ne (ne_zero_of_half_le hx.le), hxn]
          change ((1 + t) / 2 : ℝ)⁻¹ • ((1 + t) / 2 : ℝ) • (θ : EuclideanSpace ℝ (Fin (m + 1))) = θ
          rw [smul_smul, inv_mul_cancel₀ (by linarith), one_smul]
        · rw [collarHeight_coe_of_mem hx.le, hxn]
          ring

/-- The boundary sphere of the glued disk is the far end of the collar. -/
theorem image_diskSphere_collarGlue :
    collarGlue h c '' diskSphere (m + 1) = c '' {w | (w.2 : ℝ) = 1} := by
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    have hx1 : ‖(x : EuclideanSpace ℝ (Fin (m + 1)))‖ = 1 := mem_diskSphere.mp hx
    have hlt : 1 / 2 < ‖(x : EuclideanSpace ℝ (Fin (m + 1)))‖ := by rw [hx1]; norm_num
    refine ⟨(collarAngle x, collarHeight x), ?_, (collarGlue_of_lt hlt).symm⟩
    change (collarHeight x : ℝ) = 1
    rw [collarHeight_coe_of_mem hlt.le, hx1]
    norm_num
  · rintro _ ⟨⟨θ, t⟩, ht, rfl⟩
    have ht1 : (t : ℝ) = 1 := ht
    have hθ : ‖(θ : EuclideanSpace ℝ (Fin (m + 1)))‖ = 1 := mem_sphere_zero_iff_norm.mp θ.2
    let x : Disk (m + 1) := ⟨θ, sphere_subset_closedBall θ.2⟩
    have hlt : 1 / 2 < ‖(x : EuclideanSpace ℝ (Fin (m + 1)))‖ := by
      change 1 / 2 < ‖(θ : EuclideanSpace ℝ (Fin (m + 1)))‖
      rw [hθ]
      norm_num
    refine ⟨x, mem_diskSphere.mpr hθ, ?_⟩
    rw [collarGlue_of_lt hlt]
    congr 1
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · rw [collarAngle_coe_of_ne (ne_zero_of_half_le hlt.le)]
      change ‖(θ : EuclideanSpace ℝ (Fin (m + 1)))‖⁻¹ • (θ : EuclideanSpace ℝ (Fin (m + 1))) = θ
      rw [hθ, inv_one, one_smul]
    · rw [collarHeight_coe_of_mem hlt.le, ht1]
      change 2 * ‖(θ : EuclideanSpace ℝ (Fin (m + 1)))‖ - 1 = 1
      rw [hθ]
      norm_num

/-- **A disk with a collar is a disk.** If `h` and the collar `c` are continuous injections that
agree on the boundary sphere and meet only there, the radial gluing is a continuous injection of the
disk onto `range h ∪ range c`, with boundary the far end of the collar. -/
theorem exists_disk_of_disk_union_collar [TopologicalSpace X] (hh : Continuous h) (hh' : Injective h)
    (hc : Continuous c) (hc' : Injective c)
    (hmatch : ∀ (θ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) (t : Icc (0 : ℝ) 1) (z : Disk (m + 1)), (t : ℝ) = 0 →
      (z : EuclideanSpace ℝ (Fin (m + 1))) = θ → c (θ, t) = h z)
    (hinter : ∀ z w, h z = c w → (w.2 : ℝ) = 0) :
    ∃ e : Disk (m + 1) → X, Continuous e ∧ Injective e ∧ range e = range h ∪ range c ∧
      e '' diskSphere (m + 1) = c '' {w | (w.2 : ℝ) = 1} :=
  ⟨collarGlue h c, continuous_collarGlue hh hc hmatch, injective_collarGlue hh' hc' hinter,
    range_collarGlue hmatch, image_diskSphere_collarGlue⟩

end DifferentialGeometry.Topology.Surface
