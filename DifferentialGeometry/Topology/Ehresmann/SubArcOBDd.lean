import DifferentialGeometry.Topology.Ehresmann.SurfaceIntervalProductEFE

/-!
# Sub-arcs of a smooth embedded base arc (lane S-BD2d, suffix `_OBDd`), group G10c

* `SmoothEmbeddedBaseArc_EFE.subArc_OBDd γ s e`: the arc `u ↦ γ (s + (e - s) u)` for
  `0 ≤ s < e ≤ 1` (smooth, injective, regular), with its image `γ '' [s, e]` and its end values.
-/

set_option autoImplicit false

noncomputable section

open Set Function Topology
open scoped ContDiff

namespace DifferentialGeometry.Topology.Ehresmann

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] {Bs : Set H}

/-- The sub-arc `u ↦ γ (s + (e - s) u)` of a base arc, `0 ≤ s < e ≤ 1`. -/
def subArc_OBDd (γ : SmoothEmbeddedBaseArc_EFE Bs) (s e : ℝ) (hs : 0 ≤ s) (hse : s < e)
    (he : e ≤ 1) : SmoothEmbeddedBaseArc_EFE Bs where
  toFun u := γ.toFun (s + (e - s) * u)
  smooth := by
    have hmaps : MapsTo (fun u : ℝ => s + (e - s) * u) (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1) :=
      fun u hu => ⟨by nlinarith [hu.1, hu.2], by nlinarith [hu.1, hu.2]⟩
    exact γ.smooth.comp (contDiff_const.add (contDiff_const.mul contDiff_id)).contDiffOn hmaps
  injOn := by
    intro u hu u' hu' h
    have hI : ∀ v ∈ Icc (0 : ℝ) 1, s + (e - s) * v ∈ Icc (0 : ℝ) 1 := fun v hv =>
      ⟨by nlinarith [hv.1, hv.2], by nlinarith [hv.1, hv.2]⟩
    have := γ.injOn (hI u hu) (hI u' hu') h
    exact mul_left_cancel₀ (sub_pos.2 hse).ne' (by linarith)
  deriv_ne := by
    intro u hu
    have hI : s + (e - s) * u ∈ Icc (0 : ℝ) 1 := ⟨by nlinarith [hu.1, hu.2],
      by nlinarith [hu.1, hu.2]⟩
    have hmaps : MapsTo (fun v : ℝ => s + (e - s) * v) (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1) :=
      fun v hv => ⟨by nlinarith [hv.1, hv.2], by nlinarith [hv.1, hv.2]⟩
    have h1 : HasDerivWithinAt (fun v : ℝ => s + (e - s) * v) (e - s) (Icc (0 : ℝ) 1) u := by
      simpa using (((hasDerivAt_id u).const_mul (e - s)).const_add s).hasDerivWithinAt
    have h2 : HasDerivWithinAt γ.toFun (derivWithin γ.toFun (Icc (0 : ℝ) 1)
        (s + (e - s) * u)) (Icc (0 : ℝ) 1) (s + (e - s) * u) :=
      ((γ.smooth.differentiableOn (by simp)) _ hI).hasDerivWithinAt
    have hd := h2.scomp u h1 hmaps
    have hd' : derivWithin (fun u => γ.toFun (s + (e - s) * u)) (Icc (0 : ℝ) 1) u =
        (e - s) • derivWithin γ.toFun (Icc (0 : ℝ) 1) (s + (e - s) * u) :=
      hd.derivWithin (uniqueDiffOn_Icc zero_lt_one u hu)
    rw [hd']
    exact smul_ne_zero (sub_pos.2 hse).ne' (γ.deriv_ne _ hI)
  mapsTo := fun u hu => γ.mapsTo (show s + (e - s) * u ∈ Icc (0 : ℝ) 1 from
    ⟨by nlinarith [hu.1, hu.2], by nlinarith [hu.1, hu.2]⟩)

theorem subArc_toFun_OBDd (γ : SmoothEmbeddedBaseArc_EFE Bs) {s e : ℝ} (hs : 0 ≤ s) (hse : s < e)
    (he : e ≤ 1) (u : ℝ) : (subArc_OBDd γ s e hs hse he).toFun u = γ.toFun (s + (e - s) * u) :=
  rfl

/-- The image of the sub-arc is the image of `[s, e]`. -/
theorem image_subArc_OBDd (γ : SmoothEmbeddedBaseArc_EFE Bs) {s e : ℝ} (hs : 0 ≤ s)
    (hse : s < e) (he : e ≤ 1) :
    (subArc_OBDd γ s e hs hse he).toFun '' Icc 0 1 = γ.toFun '' Icc s e := by
  ext y
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨s + (e - s) * u, ⟨by nlinarith [hu.1, hu.2], by nlinarith [hu.1, hu.2]⟩, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    refine ⟨(t - s) / (e - s), ⟨div_nonneg (by linarith [ht.1]) (sub_pos.2 hse).le, ?_⟩, ?_⟩
    · rw [div_le_one (sub_pos.2 hse)]; linarith [ht.2]
    · change γ.toFun (s + (e - s) * ((t - s) / (e - s))) = γ.toFun t
      rw [mul_div_cancel₀ _ (sub_pos.2 hse).ne']
      congr 1
      ring

/-- The end values of the sub-arc. -/
theorem subArc_zero_OBDd (γ : SmoothEmbeddedBaseArc_EFE Bs) {s e : ℝ} (hs : 0 ≤ s)
    (hse : s < e) (he : e ≤ 1) : (subArc_OBDd γ s e hs hse he).toFun 0 = γ.toFun s := by
  change γ.toFun (s + (e - s) * 0) = γ.toFun s
  rw [mul_zero, add_zero]

theorem subArc_one_OBDd (γ : SmoothEmbeddedBaseArc_EFE Bs) {s e : ℝ} (hs : 0 ≤ s)
    (hse : s < e) (he : e ≤ 1) : (subArc_OBDd γ s e hs hse he).toFun 1 = γ.toFun e := by
  change γ.toFun (s + (e - s) * 1) = γ.toFun e
  rw [mul_one]
  congr 1
  ring

end DifferentialGeometry.Topology.Ehresmann
