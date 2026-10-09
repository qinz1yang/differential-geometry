import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.ExtPortCircleXPI

/-!
# FC39 external-port regression instance: radial topology of the carrier

Radial scaling `scalePt_XPI x r` (the point of the ray of `x` at radius `r`, clamped to `[1/2, 3]`)
is continuous in `r` and equals `x` at `r = rad x`. Hence every neighbourhood of a carrier point
contains points of its ray slightly above (if `rad x < 3`) and slightly below (if `1/2 < rad x`).
Consequences used by the junctions:

* `interior_rad_le_XPI`, `interior_le_rad_XPI` — interiors of radial sublevels / superlevels;
* `not_mem_relInt_XPI`, `mem_relInt_of_isOpen_XPI` — the relative interior `relInt A S` (§5.7)
  for radial sets.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0.ExtPortXPI

/-- The radius clamped to `[1/2, 3]`. -/
def radClamp_XPI (r : ℝ) : ℝ := max (1 / 2) (min 3 r)

theorem radClamp_bounds_XPI (r : ℝ) : 1 / 2 ≤ radClamp_XPI r ∧ radClamp_XPI r ≤ 3 :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

theorem radClamp_of_mem_XPI {r : ℝ} (h1 : 1 / 2 ≤ r) (h2 : r ≤ 3) : radClamp_XPI r = r := by
  rw [radClamp_XPI, min_eq_right h2, max_eq_right h1]

theorem continuous_radClamp_XPI : Continuous radClamp_XPI :=
  continuous_const.max (continuous_const.min continuous_id)

theorem norm_scaled_XPI (x : carrierW_XPI.Carrier) (r : ℝ) :
    ‖(radClamp_XPI r / rad_XPI x) • x.val.1.down‖ = radClamp_XPI r := by
  have hx := rad_pos_XPI x
  rw [norm_smul, Real.norm_of_nonneg (div_nonneg (by linarith [(radClamp_bounds_XPI r).1])
    hx.le)]
  exact div_mul_cancel₀ _ hx.ne'

/-- The point of the ray of `x` at the (clamped) radius `r`. -/
def scalePt_XPI (x : carrierW_XPI.Carrier) (r : ℝ) : carrierW_XPI.Carrier :=
  ⟨(ULift.up ((radClamp_XPI r / rad_XPI x) • x.val.1.down), x.val.2), by
    apply (mem_planarSet_iff (Or.inl rfl) _).mpr
    apply (mem_planarModel_two _).mpr
    change ‖(radClamp_XPI r / rad_XPI x) • x.val.1.down‖ ≤ 3 ∧
      1 / 2 ≤ ‖(radClamp_XPI r / rad_XPI x) • x.val.1.down‖
    rw [norm_scaled_XPI]
    exact ⟨(radClamp_bounds_XPI r).2, (radClamp_bounds_XPI r).1⟩⟩

theorem rad_scalePt_XPI (x : carrierW_XPI.Carrier) (r : ℝ) :
    rad_XPI (scalePt_XPI x r) = radClamp_XPI r :=
  norm_scaled_XPI x r

theorem rad_scalePt_of_mem_XPI (x : carrierW_XPI.Carrier) {r : ℝ} (h1 : 1 / 2 ≤ r) (h2 : r ≤ 3) :
    rad_XPI (scalePt_XPI x r) = r := by
  rw [rad_scalePt_XPI, radClamp_of_mem_XPI h1 h2]

theorem scalePt_rad_XPI (x : carrierW_XPI.Carrier) : scalePt_XPI x (rad_XPI x) = x := by
  have hb := rad_bounds_XPI x
  have hx := rad_pos_XPI x
  apply Subtype.ext
  change ((ULift.up ((radClamp_XPI (rad_XPI x) / rad_XPI x) • x.val.1.down), x.val.2) :
    PlaneLift.{0} × Circle) = x.val
  rw [radClamp_of_mem_XPI hb.1 hb.2, div_self hx.ne', one_smul]

theorem scalePt_snd_XPI (x : carrierW_XPI.Carrier) (r : ℝ) :
    (scalePt_XPI x r).val.2 = x.val.2 :=
  rfl

theorem continuous_scalePt_XPI (x : carrierW_XPI.Carrier) : Continuous (scalePt_XPI x) := by
  apply Continuous.subtype_mk
  refine Continuous.prodMk ?_ continuous_const
  exact continuous_uliftUp.comp
    (((continuous_radClamp_XPI.div_const _).smul continuous_const))

theorem tendsto_scalePt_XPI (x : carrierW_XPI.Carrier) :
    Tendsto (scalePt_XPI x) (𝓝 (rad_XPI x)) (𝓝 x) := by
  have h := (continuous_scalePt_XPI x).tendsto (rad_XPI x)
  rwa [scalePt_rad_XPI] at h

/-- **Points of the ray slightly above** `x` in every neighbourhood. -/
theorem exists_scale_above_XPI (x : carrierW_XPI.Carrier) (hx : rad_XPI x < 3)
    {U : Set carrierW_XPI.Carrier} (hU : U ∈ 𝓝 x) {b : ℝ} (hb : rad_XPI x < b) :
    ∃ r, rad_XPI x < r ∧ r < b ∧ r ≤ 3 ∧ scalePt_XPI x r ∈ U := by
  have h1 : ∀ᶠ r in 𝓝[>] (rad_XPI x), scalePt_XPI x r ∈ U :=
    ((tendsto_scalePt_XPI x).mono_left nhdsWithin_le_nhds) hU
  have h2 : ∀ᶠ r in 𝓝[>] (rad_XPI x), r ∈ Ioo (rad_XPI x) (min b 3) :=
    Ioo_mem_nhdsGT (lt_min hb hx)
  obtain ⟨r, hr1, hr2⟩ := (h1.and h2).exists
  exact ⟨r, hr2.1, lt_of_lt_of_le hr2.2 (min_le_left _ _),
    (lt_of_lt_of_le hr2.2 (min_le_right _ _)).le, hr1⟩

/-- **Points of the ray slightly below** `x` in every neighbourhood. -/
theorem exists_scale_below_XPI (x : carrierW_XPI.Carrier) (hx : 1 / 2 < rad_XPI x)
    {U : Set carrierW_XPI.Carrier} (hU : U ∈ 𝓝 x) {a : ℝ} (ha : a < rad_XPI x) :
    ∃ r, a < r ∧ r < rad_XPI x ∧ 1 / 2 ≤ r ∧ scalePt_XPI x r ∈ U := by
  have h1 : ∀ᶠ r in 𝓝[<] (rad_XPI x), scalePt_XPI x r ∈ U :=
    ((tendsto_scalePt_XPI x).mono_left nhdsWithin_le_nhds) hU
  have h2 : ∀ᶠ r in 𝓝[<] (rad_XPI x), r ∈ Ioo (max a (1 / 2)) (rad_XPI x) :=
    Ioo_mem_nhdsLT (max_lt ha hx)
  obtain ⟨r, hr1, hr2⟩ := (h1.and h2).exists
  exact ⟨r, lt_of_le_of_lt (le_max_left _ _) hr2.1, hr2.2,
    (lt_of_le_of_lt (le_max_right _ _) hr2.1).le, hr1⟩

/-! ## Interiors of radial sets -/

theorem interior_rad_le_XPI {c : ℝ} (hc : c < 3) :
    interior {y : carrierW_XPI.Carrier | rad_XPI y ≤ c} ⊆ {y | rad_XPI y < c} := by
  intro x hx
  have hxc : rad_XPI x ≤ c :=
    (interior_subset hx : x ∈ {y : carrierW_XPI.Carrier | rad_XPI y ≤ c})
  rcases lt_or_eq_of_le hxc with h | h
  · exact h
  · exfalso
    obtain ⟨r, hr1, -, hr3, hr4⟩ :=
      exists_scale_above_XPI x (h ▸ hc) (isOpen_interior.mem_nhds hx) (lt_add_one (rad_XPI x))
    have hy := interior_subset hr4
    change rad_XPI (scalePt_XPI x r) ≤ c at hy
    rw [rad_scalePt_of_mem_XPI x (by linarith [(rad_bounds_XPI x).1]) hr3] at hy
    linarith

theorem interior_le_rad_XPI {c : ℝ} (hc : 1 / 2 < c) :
    interior {y : carrierW_XPI.Carrier | c ≤ rad_XPI y} ⊆ {y | c < rad_XPI y} := by
  intro x hx
  have hxc : c ≤ rad_XPI x :=
    (interior_subset hx : x ∈ {y : carrierW_XPI.Carrier | c ≤ rad_XPI y})
  rcases lt_or_eq_of_le hxc with h | h
  · exact h
  · exfalso
    obtain ⟨r, -, hr2, hr3, hr4⟩ :=
      exists_scale_below_XPI x (h ▸ hc) (isOpen_interior.mem_nhds hx) (sub_one_lt (rad_XPI x))
    have hy := interior_subset hr4
    change c ≤ rad_XPI (scalePt_XPI x r) at hy
    rw [rad_scalePt_of_mem_XPI x hr3 (by linarith [(rad_bounds_XPI x).2])] at hy
    linarith

/-! ## Relative interiors -/

/-- A point of `A` whose every neighbourhood meets `A \ S` is not in `relInt A S`. -/
theorem not_mem_relInt_XPI {A S : Set carrierW_XPI.Carrier} {x : carrierW_XPI.Carrier}
    (h : ∀ U ∈ 𝓝 x, ∃ y ∈ U, y ∈ A ∧ y ∉ S) : x ∉ relInt A S := by
  rintro ⟨x', hx', rfl⟩
  rw [mem_interior_iff_mem_nhds, mem_nhds_subtype] at hx'
  obtain ⟨u, hu, hus⟩ := hx'
  obtain ⟨y, hyu, hyA, hyS⟩ := h u hu
  exact hyS (hus (show (⟨y, hyA⟩ : A) ∈ Subtype.val ⁻¹' u from hyu))

/-- A point of `A` inside an open set `O` with `A ∩ O ⊆ S` is in `relInt A S`. -/
theorem mem_relInt_of_isOpen_XPI {A S O : Set carrierW_XPI.Carrier} (hO : IsOpen O)
    (hOS : A ∩ O ⊆ S) {x : carrierW_XPI.Carrier} (hxA : x ∈ A) (hxO : x ∈ O) :
    x ∈ relInt A S := by
  refine ⟨⟨x, hxA⟩, ?_, rfl⟩
  rw [mem_interior_iff_mem_nhds]
  refine Filter.mem_of_superset ((hO.preimage continuous_subtype_val).mem_nhds hxO) ?_
  intro y hy
  exact hOS ⟨y.2, hy⟩

theorem relInt_subset_XPI (A S : Set carrierW_XPI.Carrier) : relInt A S ⊆ A ∩ S := by
  rintro _ ⟨x', hx', rfl⟩
  exact ⟨x'.2, (interior_subset hx' : x' ∈ Subtype.val ⁻¹' S)⟩

theorem relInt_empty_XPI (A : Set carrierW_XPI.Carrier) : relInt A ∅ = ∅ :=
  Set.eq_empty_of_subset_empty ((relInt_subset_XPI A ∅).trans inter_subset_right)

end GC.GraphManifold.Assembly.FC39P0.ExtPortXPI
