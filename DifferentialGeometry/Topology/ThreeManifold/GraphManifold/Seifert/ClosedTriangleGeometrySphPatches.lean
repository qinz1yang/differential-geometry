import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTriangleGeometrySphDiscs

/-!
# The wall patches of a spherical closed triangle fold

Lane B3d2 (design `docs/geometrization/handoffs/20261004-design-b3d-spherical-row.md`, §5, with
review 32 §5.4 and §6.6; the spherical analogue of B3c's `ClosedTriangleGeometryHypPatches`).
For a spherical datum `K` with walls `wᵢ = σ.wallSide i` and reflections `rᵢ = σ.refl i`, the
patch of wall `i` is `{z ∈ V i | Gᵢ z ∧ Gᵢ (rᵢ z)}` where `Gᵢ` collects open conditions which hold
strictly on wall `i` minus its two vertices: the two other side functions are positive, both
gauges `1 + v̄ⱼ z` have positive real part (each gauge is used on its own branch only, review 32
§6.6), the wall image of `f` (`Re f < -3/2`, `> 3/2`, `|Re f| < 3/2` with `|f|² < 25/4`), and
the angular wedges in the vertex discs of the wall; patch 0 also keeps `|Im z| < μ/2`, away from
the mirror disc of `v₁`. Patch 2 is cut down further by the continuity window of the gauge defect
`ψ₁ z + ψ₁ (r₂ z) - ψ₂ z - ψ₂ (r₂ z)` around `2 arg (1 + v₂ v₁)` (`patchTwo_window`). Since
`rᵢ` is an involution on `V i` and the defect is symmetric, each patch is stable under its
reflection (`patchZero_spec`, …); all conditions are continuous at the points where they hold,
so the patches are open. The main set `openTriangle ∪ patches` avoids the vertices, lies in both
gauge branches, meets its mirror only in patch 0 and never meets the mirror disc of `v₁`.
-/

set_option autoImplicit false

noncomputable section

open Set Complex Filter
open scoped ComplexConjugate Topology

namespace GC.Seifert

namespace ClosedTriangle

namespace Sph

namespace Lay

open TwoConeFold

variable (K : SphDatum)

def goodZero (z : ℂ) : Prop :=
  0 < K.σ.wallSide 1 z ∧ 0 < K.σ.wallSide 2 z ∧ 0 < (1 + conj K.σ.vertexOne * z).re ∧
    0 < (1 + conj K.σ.vertexTwo * z).re ∧ (K.D.f z).re < -(3 / 2) ∧ |z.im| < sphMu K / 2 ∧
    (radTwo K < ‖K.σ.rotTwo z‖ ∨
      exp (-((K.σ.θ₂ : ℂ) * I)) * K.σ.rotTwo z ∈ wedgeSet (K.σ.θ₂ / 2)) ∧
    (radThree K < ‖z‖ ∨ z ∈ wedgeSet (K.σ.θ₃ / 2))

def goodOne (z : ℂ) : Prop :=
  0 < K.σ.wallSide 0 z ∧ 0 < K.σ.wallSide 2 z ∧ 0 < (1 + conj K.σ.vertexOne * z).re ∧
    0 < (1 + conj K.σ.vertexTwo * z).re ∧ 3 / 2 < (K.D.f z).re ∧
    (radOne K < ‖K.σ.rotOne z‖ ∨ K.σ.rotOne z ∈ wedgeSet (K.σ.θ₁ / 2)) ∧
    (radThree K < ‖z‖ ∨ exp (-((K.σ.θ₃ : ℂ) * I)) * z ∈ wedgeSet (K.σ.θ₃ / 2))

def goodTwo (z : ℂ) : Prop :=
  0 < K.σ.wallSide 0 z ∧ 0 < K.σ.wallSide 1 z ∧ 0 < (1 + conj K.σ.vertexOne * z).re ∧
    0 < (1 + conj K.σ.vertexTwo * z).re ∧ -(3 / 2) < (K.D.f z).re ∧ (K.D.f z).re < 3 / 2 ∧
    normSq (K.D.f z) < 25 / 4 ∧
    (radOne K < ‖K.σ.rotOne z‖ ∨
      exp (-((K.σ.θ₁ : ℂ) * I)) * K.σ.rotOne z ∈ wedgeSet (K.σ.θ₁ / 2)) ∧
    (radTwo K < ‖K.σ.rotTwo z‖ ∨ K.σ.rotTwo z ∈ wedgeSet (K.σ.θ₂ / 2))

def defect (z : ℂ) : ℝ :=
  psiS K.σ.vertexOne z + psiS K.σ.vertexOne (K.σ.refl 2 z) - psiS K.σ.vertexTwo z -
    psiS K.σ.vertexTwo (K.σ.refl 2 z)

def patchZero : Set ℂ := {z | z ∈ K.D.V 0 ∧ goodZero K z ∧ goodZero K (conj z)}

def patchOne : Set ℂ := {z | z ∈ K.D.V 1 ∧ goodOne K z ∧ goodOne K (K.σ.refl 1 z)}

def patchTwo : Set ℂ := {z | z ∈ K.D.V 2 ∧ goodTwo K z ∧ goodTwo K (K.σ.refl 2 z) ∧
  |defect K z - 2 * arg (1 + K.σ.vertexTwo * K.σ.vertexOne)| < Real.pi}

def mainSet : Set ℂ := K.σ.openTriangle ∪ patchZero K ∪ patchOne K ∪ patchTwo K

section Continuity

theorem ne_of_re_pos {w : ℂ} (h : 0 < w.re) : w ≠ 0 := fun h0 => by
  rw [h0, zero_re] at h
  exact lt_irrefl _ h

theorem continuousAt_rotOne {z : ℂ} (h : 1 + conj K.σ.vertexOne * z ≠ 0) :
    ContinuousAt K.σ.rotOne z := by
  have e : K.σ.rotOne = fun z => -exp (-((K.σ.θ₃ : ℂ) * I)) * discV K.σ.vertexOne z :=
    funext (rotOne_eq_of_sph K.hσ)
  rw [e]
  exact continuousAt_const.mul (hasDerivAt_discV _ h).continuousAt

theorem continuousAt_rotTwo {z : ℂ} (h : 1 + conj K.σ.vertexTwo * z ≠ 0) :
    ContinuousAt K.σ.rotTwo z := by
  have e : K.σ.rotTwo = fun z => -exp ((K.σ.θ₂ : ℂ) * I) * discV K.σ.vertexTwo z :=
    funext (rotTwo_eq_of_sph K.hσ)
  rw [e]
  exact continuousAt_const.mul (hasDerivAt_discV _ h).continuousAt

theorem continuousAt_f {z : ℂ} (hz : z ∈ K.D.U) : ContinuousAt K.D.f z :=
  K.D.contDiffOn_f.continuousOn.continuousAt (K.D.isOpen_U.mem_nhds hz)

theorem continuousAt_refl (i : Fin 3) {z : ℂ} (hz : z ∈ K.σ.reflChart i) :
    ContinuousAt (K.σ.refl i) z :=
  (CompactShape.continuousOn_refl_sph K.hσ i).continuousAt
    ((CompactShape.isOpen_reflChart_sph K.hσ i).mem_nhds hz)

theorem continuousAt_psiS (v : ℂ) {z : ℂ} (h : 0 < (1 + conj v * z).re) :
    ContinuousAt (psiS v) z := by
  have hs : 1 + conj v * z ∈ slitPlane := mem_slitPlane_iff.mpr (Or.inl h)
  have hc : ContinuousAt (fun y => 1 + conj v * y) z := by fun_prop
  have h2 : ContinuousAt (fun y => arg (1 + conj v * y)) z :=
    ContinuousAt.comp (g := arg) (f := fun y => 1 + conj v * y) (continuousAt_arg hs) hc
  change ContinuousAt (fun y => -arg (1 + conj v * y)) z
  exact h2.neg

theorem ev_lt {g : ℂ → ℝ} {z : ℂ} {a : ℝ} (hg : ContinuousAt g z) (h : a < g z) :
    ∀ᶠ y in 𝓝 z, a < g y := hg.tendsto.eventually (lt_mem_nhds h)

theorem ev_gt {g : ℂ → ℝ} {z : ℂ} {a : ℝ} (hg : ContinuousAt g z) (h : g z < a) :
    ∀ᶠ y in 𝓝 z, g y < a := hg.tendsto.eventually (gt_mem_nhds h)

theorem ev_wedge {g g' : ℂ → ℂ} {z : ℂ} {r a : ℝ} (ha : a ≤ Real.pi) (hg : ContinuousAt g z)
    (hg' : ContinuousAt g' z) (h : r < ‖g z‖ ∨ g' z ∈ wedgeSet a) :
    ∀ᶠ y in 𝓝 z, r < ‖g y‖ ∨ g' y ∈ wedgeSet a := by
  rcases h with h | h
  · filter_upwards [ev_lt hg.norm h] with y hy
    exact Or.inl hy
  · filter_upwards [hg'.tendsto.eventually ((isOpen_wedgeSet ha).mem_nhds h)] with y hy
    exact Or.inr hy

theorem half_le_pi {θ : ℝ} (h0 : 0 < θ) (h : θ ≤ Real.pi / 2) : θ / 2 ≤ Real.pi := by
  linarith [Real.pi_pos]

theorem continuousAt_reOne {z : ℂ} :
    ContinuousAt (fun y => (1 + conj K.σ.vertexOne * y).re) z := by fun_prop

theorem continuousAt_reTwo {z : ℂ} :
    ContinuousAt (fun y => (1 + conj K.σ.vertexTwo * y).re) z := by fun_prop

theorem continuousAt_wall (i : Fin 3) {z : ℂ} : ContinuousAt (K.σ.wallSide i) z :=
  (K.σ.continuous_wallSide i).continuousAt

theorem ev_goodZero {z : ℂ} (hU : z ∈ K.D.U) (hz : goodZero K z) :
    ∀ᶠ y in 𝓝 z, goodZero K y := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hz
  have hf : ContinuousAt (fun y => (K.D.f y).re) z :=
    continuous_re.continuousAt.comp (continuousAt_f K hU)
  have hi : ContinuousAt (fun y : ℂ => |y.im|) z := by fun_prop
  have hr := continuousAt_rotTwo K (ne_of_re_pos h4)
  filter_upwards [ev_lt (continuousAt_wall K 1) h1, ev_lt (continuousAt_wall K 2) h2,
    ev_lt (continuousAt_reOne K) h3, ev_lt (continuousAt_reTwo K) h4, ev_gt hf h5, ev_gt hi h6,
    ev_wedge (half_le_pi K.σ.θ₂_pos K.σ.θ₂_le) hr (continuousAt_const.mul hr) h7,
    ev_wedge (half_le_pi K.σ.θ₃_pos K.σ.θ₃_le) continuousAt_id continuousAt_id h8]
    with y e1 e2 e3 e4 e5 e6 e7 e8
  exact ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩

theorem ev_goodOne {z : ℂ} (hU : z ∈ K.D.U) (hz : goodOne K z) :
    ∀ᶠ y in 𝓝 z, goodOne K y := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hz
  have hf : ContinuousAt (fun y => (K.D.f y).re) z :=
    continuous_re.continuousAt.comp (continuousAt_f K hU)
  have hr := continuousAt_rotOne K (ne_of_re_pos h3)
  filter_upwards [ev_lt (continuousAt_wall K 0) h1, ev_lt (continuousAt_wall K 2) h2,
    ev_lt (continuousAt_reOne K) h3, ev_lt (continuousAt_reTwo K) h4, ev_lt hf h5,
    ev_wedge (half_le_pi K.σ.θ₁_pos K.σ.θ₁_le) hr hr h6,
    ev_wedge (half_le_pi K.σ.θ₃_pos K.σ.θ₃_le) continuousAt_id
      (continuousAt_const.mul continuousAt_id) h7]
    with y e1 e2 e3 e4 e5 e6 e7
  exact ⟨e1, e2, e3, e4, e5, e6, e7⟩

theorem ev_goodTwo {z : ℂ} (hU : z ∈ K.D.U) (hz : goodTwo K z) :
    ∀ᶠ y in 𝓝 z, goodTwo K y := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hz
  have hf : ContinuousAt (fun y => (K.D.f y).re) z :=
    continuous_re.continuousAt.comp (continuousAt_f K hU)
  have hn : ContinuousAt (fun y => normSq (K.D.f y)) z :=
    Complex.continuous_normSq.continuousAt.comp (continuousAt_f K hU)
  have hr1 := continuousAt_rotOne K (ne_of_re_pos h3)
  have hr2 := continuousAt_rotTwo K (ne_of_re_pos h4)
  filter_upwards [ev_lt (continuousAt_wall K 0) h1, ev_lt (continuousAt_wall K 1) h2,
    ev_lt (continuousAt_reOne K) h3, ev_lt (continuousAt_reTwo K) h4, ev_lt hf h5, ev_gt hf h6,
    ev_gt hn h7, ev_wedge (half_le_pi K.σ.θ₁_pos K.σ.θ₁_le) hr1 (continuousAt_const.mul hr1) h8,
    ev_wedge (half_le_pi K.σ.θ₂_pos K.σ.θ₂_le) hr2 hr2 h9]
    with y e1 e2 e3 e4 e5 e6 e7 e8 e9
  exact ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9⟩

theorem refl_zero_mem_V {z : ℂ} (hV : z ∈ K.D.V 0) : conj z ∈ K.D.V 0 := by
  have := K.D.refl_mapsTo_V 0 hV
  rwa [CompactShape.refl_zero_apply_sph] at this

theorem isOpen_patchZero : IsOpen (patchZero K) := by
  refine isOpen_iff_mem_nhds.2 fun z hz => ?_
  obtain ⟨hV, hg, hg'⟩ := hz
  have e1 := ev_goodZero K (K.D.V_subset_U 0 hV) hg
  have e2 : ∀ᶠ y in 𝓝 z, goodZero K (conj y) :=
    Complex.continuous_conj.continuousAt.tendsto.eventually
      (ev_goodZero K (K.D.V_subset_U 0 (refl_zero_mem_V K hV)) hg')
  filter_upwards [(K.D.isOpen_V 0).mem_nhds hV, e1, e2] with y a b c
  exact ⟨a, b, c⟩

theorem isOpen_patchOne : IsOpen (patchOne K) := by
  refine isOpen_iff_mem_nhds.2 fun z hz => ?_
  obtain ⟨hV, hg, hg'⟩ := hz
  have e1 := ev_goodOne K (K.D.V_subset_U 1 hV) hg
  have e2 : ∀ᶠ y in 𝓝 z, goodOne K (K.σ.refl 1 y) :=
    (continuousAt_refl K 1 (K.D.V_subset_reflChart 1 hV)).tendsto.eventually
      (ev_goodOne K (K.D.V_subset_U 1 (K.D.refl_mapsTo_V 1 hV)) hg')
  filter_upwards [(K.D.isOpen_V 1).mem_nhds hV, e1, e2] with y a b c
  exact ⟨a, b, c⟩

theorem continuousAt_defect {z : ℂ} (hc : z ∈ K.σ.reflChart 2) (hg : goodTwo K z)
    (hg' : goodTwo K (K.σ.refl 2 z)) : ContinuousAt (defect K) z := by
  have hr := continuousAt_refl K 2 hc
  have a1 := continuousAt_psiS K.σ.vertexOne hg.2.2.1
  have a2 := (continuousAt_psiS K.σ.vertexOne hg'.2.2.1).comp hr
  have a3 := continuousAt_psiS K.σ.vertexTwo hg.2.2.2.1
  have a4 := (continuousAt_psiS K.σ.vertexTwo hg'.2.2.2.1).comp hr
  exact ((a1.add a2).sub a3).sub a4

theorem isOpen_patchTwo : IsOpen (patchTwo K) := by
  refine isOpen_iff_mem_nhds.2 fun z hz => ?_
  obtain ⟨hV, hg, hg', hw⟩ := hz
  have hc := K.D.V_subset_reflChart 2 hV
  have e1 := ev_goodTwo K (K.D.V_subset_U 2 hV) hg
  have e2 : ∀ᶠ y in 𝓝 z, goodTwo K (K.σ.refl 2 y) :=
    (continuousAt_refl K 2 hc).tendsto.eventually
      (ev_goodTwo K (K.D.V_subset_U 2 (K.D.refl_mapsTo_V 2 hV)) hg')
  have hd : ContinuousAt (fun y => |defect K y - 2 * arg (1 + K.σ.vertexTwo * K.σ.vertexOne)|)
      z :=
    continuous_abs.continuousAt.comp ((continuousAt_defect K hc hg hg').sub continuousAt_const)
  filter_upwards [(K.D.isOpen_V 2).mem_nhds hV, e1, e2, ev_gt hd hw] with y a b c d
  exact ⟨a, b, c, d⟩

end Continuity

section Specs

theorem patchZero_spec : ∀ z ∈ patchZero K,
    z ∈ K.D.V 0 ∧ (K.D.f z).re < -(3 / 2) ∧ conj z ∈ patchZero K := by
  rintro z ⟨hV, hg, hg'⟩
  refine ⟨hV, hg.2.2.2.2.1, refl_zero_mem_V K hV, hg', ?_⟩
  rw [conj_conj]
  exact hg

theorem patchOne_spec : ∀ z ∈ patchOne K,
    z ∈ K.D.V 1 ∧ 3 / 2 < (K.D.f z).re ∧ K.σ.refl 1 z ∈ patchOne K := by
  rintro z ⟨hV, hg, hg'⟩
  refine ⟨hV, hg.2.2.2.2.1, K.D.refl_mapsTo_V 1 hV, hg', ?_⟩
  rw [CompactShape.refl_refl_one_sph]
  exact hg

theorem defect_refl {z : ℂ} (hc : z ∈ K.σ.reflChart 2) :
    defect K (K.σ.refl 2 z) = defect K z := by
  unfold defect
  rw [CompactShape.refl_refl_two_sph K.hσ hc]
  ring

theorem patchTwo_spec : ∀ z ∈ patchTwo K, z ∈ K.D.V 2 ∧ -(3 / 2) < (K.D.f z).re ∧
    (K.D.f z).re < 3 / 2 ∧ normSq (K.D.f z) < 25 / 4 ∧ K.σ.refl 2 z ∈ patchTwo K := by
  rintro z ⟨hV, hg, hg', hw⟩
  have hc := K.D.V_subset_reflChart 2 hV
  refine ⟨hV, hg.2.2.2.2.1, hg.2.2.2.2.2.1, hg.2.2.2.2.2.2.1, K.D.refl_mapsTo_V 2 hV, hg', ?_,
    ?_⟩
  · rw [CompactShape.refl_refl_two_sph K.hσ hc]
    exact hg
  · rw [defect_refl K hc]
    exact hw

theorem patchTwo_window : ∀ z ∈ patchTwo K,
    |psiS K.σ.vertexOne z + psiS K.σ.vertexOne (K.σ.refl 2 z) - psiS K.σ.vertexTwo z -
      psiS K.σ.vertexTwo (K.σ.refl 2 z) - 2 * arg (1 + K.σ.vertexTwo * K.σ.vertexOne)| <
        Real.pi := fun _ hz => hz.2.2.2

theorem openTriangle_of {z : ℂ} (h0 : 0 < K.σ.wallSide 0 z) (h1 : 0 < K.σ.wallSide 1 z)
    (h2 : 0 < K.σ.wallSide 2 z) : z ∈ K.σ.openTriangle := by
  refine ⟨by rw [CompactShape.plane_sph K.hσ]; exact mem_univ z, fun i => ?_⟩
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

theorem patchZero_out : ∀ z ∈ patchZero K, z ∉ K.σ.triangle → conj z ∈ K.σ.openTriangle := by
  rintro z ⟨-, hg, hg'⟩ hT
  have h0 : K.σ.wallSide 0 z < 0 := by
    by_contra h
    rw [not_lt] at h
    exact hT ((CompactShape.mem_triangle_iff_sph K.hσ).2 ⟨h, hg.1.le, hg.2.1.le⟩)
  refine openTriangle_of K ?_ hg'.1 hg'.2.1
  change 0 < (conj z).im
  rw [conj_im]
  exact neg_pos.mpr h0

theorem patchOne_out : ∀ z ∈ patchOne K, z ∉ K.σ.triangle →
    K.σ.refl 1 z ∈ K.σ.openTriangle := by
  rintro z ⟨-, hg, hg'⟩ hT
  have h1 : K.σ.wallSide 1 z < 0 := by
    by_contra h
    rw [not_lt] at h
    exact hT ((CompactShape.mem_triangle_iff_sph K.hσ).2 ⟨hg.1.le, h, hg.2.1.le⟩)
  refine openTriangle_of K hg'.1 ?_ hg'.2.1
  rw [CompactShape.wallSide_refl_one_sph]
  exact neg_pos.mpr h1

theorem patchTwo_out : ∀ z ∈ patchTwo K, z ∉ K.σ.triangle →
    K.σ.refl 2 z ∈ K.σ.openTriangle := by
  rintro z ⟨hV, hg, hg', -⟩ hT
  have hc := K.D.V_subset_reflChart 2 hV
  have h2 : K.σ.wallSide 2 z < 0 := by
    by_contra h
    rw [not_lt] at h
    exact hT ((CompactShape.mem_triangle_iff_sph K.hσ).2 ⟨hg.1.le, hg.2.1.le, h⟩)
  refine openTriangle_of K hg'.1 hg'.2.1 ?_
  have hd1 := (CompactShape.mem_reflChart_two_iff_sph K.hσ).1 hc
  have hp1 : 0 < normSq (1 + K.σ.vertexTwo * z) := normSq_pos.mpr hd1.1
  have hp2 : 0 < normSq (1 + K.σ.vertexTwo * K.σ.refl 2 z) :=
    normSq_pos.mpr (CompactShape.one_add_vertexTwo_mul_refl_two_sph K.hσ hc)
  rw [CompactShape.wallSide_refl_two_sph' K.hσ hc, neg_mul, neg_pos]
  exact mul_neg_of_pos_of_neg (div_pos hp2 hp1) h2

end Specs

section Main

theorem main_ne : ∀ z ∈ mainSet K, z ≠ 0 ∧ z ≠ K.σ.vertexOne ∧ z ≠ K.σ.vertexTwo := by
  rintro z (((h | h) | h) | h)
  · exact K.σ.ne_of_mem_openTriangle h
  · obtain ⟨-, ⟨h1, h2, -⟩, -⟩ := h
    refine ⟨fun e => ?_, fun e => ?_, fun e => ?_⟩
    · rw [e, CompactShape.wallSide_one_zero_sph] at h1; exact lt_irrefl _ h1
    · rw [e, CompactShape.wallSide_one_vertexOne_sph] at h1; exact lt_irrefl _ h1
    · rw [e, CompactShape.wallSide_two_vertexTwo_sph K.hσ] at h2; exact lt_irrefl _ h2
  · obtain ⟨-, ⟨h0, h2, -⟩, -⟩ := h
    refine ⟨fun e => ?_, fun e => ?_, fun e => ?_⟩
    · rw [e, CompactShape.wallSide_zero_zero_sph] at h0; exact lt_irrefl _ h0
    · rw [e, CompactShape.wallSide_two_vertexOne_sph K.hσ] at h2; exact lt_irrefl _ h2
    · rw [e, CompactShape.wallSide_zero_vertexTwo_sph] at h0; exact lt_irrefl _ h0
  · obtain ⟨-, ⟨h0, h1, -⟩, -⟩ := h
    refine ⟨fun e => ?_, fun e => ?_, fun e => ?_⟩
    · rw [e, CompactShape.wallSide_zero_zero_sph] at h0; exact lt_irrefl _ h0
    · rw [e, CompactShape.wallSide_one_vertexOne_sph] at h1; exact lt_irrefl _ h1
    · rw [e, CompactShape.wallSide_zero_vertexTwo_sph] at h0; exact lt_irrefl _ h0

theorem re_pos_of_triangle {z : ℂ} (hz : z ∈ K.σ.triangle) :
    0 < (1 + conj K.σ.vertexOne * z).re ∧ 0 < (1 + conj K.σ.vertexTwo * z).re := by
  have a := CompactShape.conj_vertexOne_mul_re_nonneg_sph K.hσ hz
  have b := CompactShape.vertexTwo_mul_re_nonneg_sph K.hσ hz
  rw [add_re, add_re, one_re]
  constructor <;> linarith

theorem main_re_pos : ∀ z ∈ mainSet K,
    0 < (1 + conj K.σ.vertexOne * z).re ∧ 0 < (1 + conj K.σ.vertexTwo * z).re := by
  rintro z (((h | h) | h) | h)
  · exact re_pos_of_triangle K (K.σ.openTriangle_subset h)
  · exact ⟨h.2.1.2.2.1, h.2.1.2.2.2.1⟩
  · exact ⟨h.2.1.2.2.1, h.2.1.2.2.2.1⟩
  · exact ⟨h.2.1.2.2.1, h.2.1.2.2.2.1⟩

theorem main_slit : ∀ z ∈ mainSet K,
    1 + conj K.σ.vertexOne * z ∈ slitPlane ∧ 1 + conj K.σ.vertexTwo * z ∈ slitPlane :=
  fun z hz => ⟨mem_slitPlane_iff.mpr (Or.inl (main_re_pos K z hz).1),
    mem_slitPlane_iff.mpr (Or.inl (main_re_pos K z hz).2)⟩

theorem im_pos_or_patchZero : ∀ z ∈ mainSet K, z ∈ patchZero K ∨ 0 < z.im := by
  rintro z (((h | h) | h) | h)
  · exact Or.inr (h.2 0)
  · exact Or.inl h
  · exact Or.inr h.2.1.1
  · exact Or.inr h.2.1.1

theorem main_conj : ∀ z ∈ mainSet K, conj z ∈ mainSet K → z ∈ patchZero K := by
  intro z hz hc
  rcases im_pos_or_patchZero K z hz with h | h
  · exact h
  rcases im_pos_or_patchZero K (conj z) hc with h' | h'
  · have := (patchZero_spec K (conj z) h').2.2
    rwa [conj_conj] at this
  · rw [conj_im] at h'
    linarith

theorem main_mirror : ∀ z ∈ mainSet K, conj z ∉ discOneR K (radOne K) := by
  intro z hz h1
  have hi := im_gt_of_mem_discOne K h1
  rw [conj_im] at hi
  have := sphMu_pos K
  rcases im_pos_or_patchZero K z hz with h | h
  · have := (abs_lt.mp h.2.1.2.2.2.2.2.1).1
    linarith
  · linarith

end Main

end Lay

end Sph

end ClosedTriangle

end GC.Seifert
