import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTriangleGeometrySphLayout

/-!
# Consequences of a spherical base layout

Lane B3d (design `docs/geometrization/handoffs/20261004-design-b3d-spherical-row.md`, §5). For a
layout `L : SphLayout K` the pieces are open (`isOpen_discOne`, ..., `isOpen_mainSet`); on the
vertex discs the fold datum is the apex germ resp. the outer germ (`f_of_mem_discOne`, ...), the
rotated coordinates are small (`norm_rotOne_pow_le`, ...), the apex values avoid the phase cuts
(`re_apexOne_gt`, `re_apexTwo_lt`) and the outer values have `|f|² ≥ 9`; the disc of `v₂` and the
disc of `0` are symmetric under `conj`, the disc of `v₁` under the wall-1 reflection. On the main
set `f` is smooth, lies in the three phase domains and in the domain of the closed chart
(`main_subset_U`, `main_phase`, `f_main_props`).
-/

set_option autoImplicit false

noncomputable section
open Set Complex
open DifferentialGeometry GC.Geometry
open scoped Topology ComplexConjugate

namespace GC.Seifert

namespace ClosedTriangle

namespace Sph

namespace SphLayout

variable {K : SphDatum} (L : SphLayout K)

theorem eps_eq : K.σ.eps = -1 := by
  unfold CompactShape.eps
  rw [K.hσ]
  rfl

theorem norm_rotOne (z : ℂ) : ‖K.σ.rotOne z‖ = ‖discV K.σ.vertexOne z‖ := by
  have h : ‖exp (-((K.σ.θ₃ : ℂ) * I))‖ = 1 := by
    rw [← neg_mul, ← ofReal_neg, norm_exp_ofReal_mul_I]
  rw [rotOne_eq_of_sph K.hσ, norm_mul, norm_neg, h, one_mul]

theorem norm_rotTwo (z : ℂ) : ‖K.σ.rotTwo z‖ = ‖discV K.σ.vertexTwo z‖ := by
  rw [rotTwo_eq_of_sph K.hσ, norm_mul, norm_neg, norm_exp_ofReal_mul_I, one_mul]

theorem continuousOn_discV (v : ℂ) :
    ContinuousOn (discV v) {z | 1 + conj v * z ≠ 0} :=
  (differentiableOn_discV v fun _ hz => hz).continuousOn

theorem isOpen_discOneR (r : ℝ) : IsOpen (discOneR K r) := by
  have ho : IsOpen {z : ℂ | 1 + conj K.σ.vertexOne * z ≠ 0} :=
    isOpen_ne_fun (by fun_prop) continuous_const
  have hc : ContinuousOn (fun z => ‖discV K.σ.vertexOne z‖) {z | 1 + conj K.σ.vertexOne * z ≠ 0} :=
    continuous_norm.comp_continuousOn (continuousOn_discV _)
  have := hc.isOpen_inter_preimage ho (isOpen_Iio (a := r))
  convert this using 1
  ext z
  simp only [discOneR, mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_Iio, norm_rotOne]

theorem isOpen_discTwoR (r : ℝ) : IsOpen (discTwoR K r) := by
  have ho : IsOpen {z : ℂ | 1 + conj K.σ.vertexTwo * z ≠ 0} :=
    isOpen_ne_fun (by fun_prop) continuous_const
  have hc : ContinuousOn (fun z => ‖discV K.σ.vertexTwo z‖) {z | 1 + conj K.σ.vertexTwo * z ≠ 0} :=
    continuous_norm.comp_continuousOn (continuousOn_discV _)
  have := hc.isOpen_inter_preimage ho (isOpen_Iio (a := r))
  convert this using 1
  ext z
  simp only [discTwoR, mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_Iio, norm_rotTwo]

theorem isOpen_discOne : IsOpen L.discOne := isOpen_discOneR L.radOne

theorem isOpen_discTwo : IsOpen L.discTwo := isOpen_discTwoR L.radTwo

theorem isOpen_discThree : IsOpen L.discThree := isOpen_lt continuous_norm continuous_const

theorem isOpen_discOneMirror : IsOpen L.discOneMirror :=
  L.isOpen_discOne.preimage continuous_conj

theorem isOpen_mainSet : IsOpen L.mainSet :=
  (((K.σ.isOpen_openTriangle.union L.isOpen_patchZero).union L.isOpen_patchOne).union
    L.isOpen_patchTwo)

theorem mem_apexDisc_one {z : ℂ} (hz : z ∈ L.discOne) :
    z ∈ K.σ.apexDisc K.σ.vertexOne (K.D.apexRadius 0) := by
  refine ⟨?_, ?_⟩
  · rw [eps_eq]
    have := hz.1
    simpa using this
  · rw [disc_of_sph K.hσ, ← norm_rotOne]
    exact lt_of_lt_of_le hz.2 L.radOne_le_apex

theorem mem_apexDisc_two {z : ℂ} (hz : z ∈ L.discTwo) :
    z ∈ K.σ.apexDisc K.σ.vertexTwo (K.D.apexRadius 1) := by
  refine ⟨?_, ?_⟩
  · rw [eps_eq]
    have := hz.1
    simpa using this
  · rw [disc_of_sph K.hσ, ← norm_rotTwo]
    exact lt_of_lt_of_le hz.2 L.radTwo_le_apex

theorem f_of_mem_discOne {z : ℂ} (hz : z ∈ L.discOne) :
    z ∈ K.D.U ∧ K.D.f z = apexOneS K.σ z :=
  K.D.f_apexOne z (L.mem_apexDisc_one hz)

theorem f_of_mem_discTwo {z : ℂ} (hz : z ∈ L.discTwo) :
    z ∈ K.D.U ∧ K.D.f z = apexTwoS K.σ z :=
  K.D.f_apexTwo z (L.mem_apexDisc_two hz)

theorem f_of_mem_discThree {z : ℂ} (hz : z ∈ L.discThree) (h0 : z ≠ 0) :
    z ∈ K.D.U ∧ K.D.f z = compactOuterGerm K.σ.p₃ z :=
  K.D.f_outer z (norm_pos_iff.2 h0) (lt_of_lt_of_le hz L.radThree_le_apex)

theorem norm_rotOne_lt {z : ℂ} (hz : z ∈ L.discOne) : ‖K.σ.rotOne z‖ < 1 / 2 :=
  lt_of_lt_of_le hz.2 L.radOne_le_half

theorem norm_rotTwo_lt {z : ℂ} (hz : z ∈ L.discTwo) : ‖K.σ.rotTwo z‖ < 1 / 2 :=
  lt_of_lt_of_le hz.2 L.radTwo_le_half

theorem norm_lt_of_discThree {z : ℂ} (hz : z ∈ L.discThree) : ‖z‖ < 1 / 2 :=
  lt_of_lt_of_le hz L.radThree_le_half

theorem pow_le_of_lt_half {w : ℂ} (hw : ‖w‖ < 1 / 2) (p : ℕ) (hp : 2 ≤ p) :
    ‖w‖ ^ p ≤ 1 / 4 := by
  have h0 := norm_nonneg w
  calc ‖w‖ ^ p ≤ ‖w‖ ^ 2 := pow_le_pow_of_le_one h0 (by linarith) hp
    _ ≤ (1 / 2) ^ 2 := by gcongr
    _ = 1 / 4 := by norm_num

theorem norm_rotOne_pow_le {z : ℂ} (hz : z ∈ L.discOne) : ‖K.σ.rotOne z‖ ^ K.σ.p₁ ≤ 1 :=
  (pow_le_of_lt_half (L.norm_rotOne_lt hz) _ K.σ.two_le_p₁).trans (by norm_num)

theorem norm_rotTwo_pow_le {z : ℂ} (hz : z ∈ L.discTwo) : ‖K.σ.rotTwo z‖ ^ K.σ.p₂ ≤ 1 :=
  (pow_le_of_lt_half (L.norm_rotTwo_lt hz) _ K.σ.two_le_p₂).trans (by norm_num)

theorem re_apexOne_gt {z : ℂ} (hz : z ∈ L.discOne) : -(3 / 2) < (apexOneS K.σ z).re := by
  have h := pow_le_of_lt_half (L.norm_rotOne_lt hz) _ K.σ.two_le_p₁
  have hre := abs_re_le_norm (K.σ.rotOne z ^ K.σ.p₁ / 2)
  rw [norm_div, norm_pow] at hre
  simp only [apexOneS, add_re, div_ofNat_re]
  norm_num at hre ⊢
  have := (abs_le.1 hre).1
  linarith

theorem re_apexTwo_lt {z : ℂ} (hz : z ∈ L.discTwo) : (apexTwoS K.σ z).re < 3 / 2 := by
  have h := pow_le_of_lt_half (L.norm_rotTwo_lt hz) _ K.σ.two_le_p₂
  have hre := abs_re_le_norm (K.σ.rotTwo z ^ K.σ.p₂ / 2)
  rw [norm_div, norm_pow] at hre
  simp only [apexTwoS, add_re, neg_re, div_ofNat_re]
  norm_num at hre ⊢
  have := (abs_le.1 hre).2
  linarith

theorem norm_f_of_discThree {z : ℂ} (hz : z ∈ L.discThree) (h0 : z ≠ 0) :
    3 ≤ ‖K.D.f z‖ := by
  rw [(L.f_of_mem_discThree hz h0).2, compactOuterGerm, norm_neg, norm_mul, Complex.norm_real,
    norm_pow, norm_div, Complex.norm_conj, Complex.norm_real, norm_norm,
    div_self (norm_ne_zero_iff.mpr h0), one_pow, mul_one]
  have hn : ‖z‖ ^ K.σ.p₃ ≤ 1 :=
    pow_le_one₀ (norm_nonneg _) ((le_of_lt hz).trans (by linarith [L.radThree_le_half]))
  rw [Real.norm_of_nonneg (by linarith)]
  linarith

theorem normSq_f_of_discThree {z : ℂ} (hz : z ∈ L.discThree) (h0 : z ≠ 0) :
    9 ≤ normSq (K.D.f z) := by
  have h := L.norm_f_of_discThree hz h0
  rw [normSq_eq_norm_sq]
  nlinarith

theorem norm_pow_lt_seven {z : ℂ} (hz : z ∈ L.discThree) : ‖z‖ ^ K.σ.p₃ < 7 := by
  have : ‖z‖ ^ K.σ.p₃ ≤ 1 :=
    pow_le_one₀ (norm_nonneg _) ((le_of_lt hz).trans (by linarith [L.radThree_le_half]))
  linarith

theorem conj_mem_discTwo {z : ℂ} (hz : z ∈ L.discTwo) : conj z ∈ L.discTwo := by
  have hv := conj_vertexTwo_sph K.σ
  refine ⟨?_, ?_⟩
  · have h : 1 + conj K.σ.vertexTwo * conj z = conj (1 + conj K.σ.vertexTwo * z) := by
      rw [map_add, map_one, map_mul, conj_conj, hv]
    rw [h]
    exact (map_ne_zero _).2 hz.1
  · rw [rotTwo_conj_sph K.hσ, norm_mul, norm_conj]
    have : ‖exp (2 * (K.σ.θ₂ : ℂ) * I)‖ = 1 := by
      rw [show 2 * (K.σ.θ₂ : ℂ) * I = ((2 * K.σ.θ₂ : ℝ) : ℂ) * I by push_cast; ring,
        norm_exp_ofReal_mul_I]
    rw [this, one_mul]
    exact hz.2

theorem conj_mem_discThree {z : ℂ} (hz : z ∈ L.discThree) : conj z ∈ L.discThree := by
  change ‖conj z‖ < L.radThree
  rw [norm_conj]
  exact hz

theorem refl_one_mem_discOne {z : ℂ} (hz : z ∈ L.discOne) : K.σ.refl 1 z ∈ L.discOne := by
  refine ⟨?_, ?_⟩
  · have h1 := hz.1
    intro h
    apply h1
    have hc : 1 + conj K.σ.vertexOne * K.σ.refl 1 z = conj (1 + conj K.σ.vertexOne * z) := by
      change 1 + conj K.σ.vertexOne * (exp (2 * (K.σ.θ₃ : ℂ) * I) * conj z) = _
      set E := exp ((K.σ.θ₃ : ℂ) * I) with hE
      have hcE : conj E * E = 1 := by
        rw [mul_comm, mul_conj, normSq_eq_norm_sq, hE, norm_exp_ofReal_mul_I]
        norm_num
      have h2 : exp (2 * (K.σ.θ₃ : ℂ) * I) = E * E := by rw [hE, ← exp_add]; ring_nf
      have hv : K.σ.vertexOne = (K.σ.sideTan K.σ.θ₁ K.σ.θ₃ K.σ.θ₂ : ℂ) * E := rfl
      rw [h2, hv]
      simp only [map_add, map_one, map_mul, conj_ofReal, conj_conj]
      linear_combination ((K.σ.sideTan K.σ.θ₁ K.σ.θ₃ K.σ.θ₂ : ℂ) * E * conj z) * hcE
    rw [hc] at h
    exact (map_eq_zero _).1 h
  · rw [rotOne_refl_one_sph K.hσ, norm_conj]
    exact hz.2

theorem mem_discOneMirror_iff {z : ℂ} : z ∈ L.discOneMirror ↔ conj z ∈ L.discOne := Iff.rfl

theorem main_subset_U : L.mainSet ⊆ K.D.U := by
  intro z hz
  rcases hz with ((h | h) | h) | h
  · exact K.D.triangle_diff_subset_U ⟨K.σ.openTriangle_subset h,
      (K.σ.ne_of_mem_openTriangle h).1⟩
  · exact K.D.V_subset_U 0 (L.patchZero_spec z h).1
  · exact K.D.V_subset_U 1 (L.patchOne_spec z h).1
  · exact K.D.V_subset_U 2 (L.patchTwo_spec z h).1

theorem im_f_pos_of_open {z : ℂ} (h : z ∈ K.σ.openTriangle) : 0 < (K.D.f z).im :=
  K.D.im_f_pos h.1 h.2

theorem main_phase {z : ℂ} (hm : z ∈ L.mainSet) :
    K.D.f z ∈ phaseDomain (3 / 2) ∧ K.D.f z ∈ phaseDomain (-(3 / 2)) ∧
      (K.D.f z ∈ phaseDomain 0 ∨ normSq (K.D.f z) < 121 / 16) := by
  rcases hm with ((h | h) | h) | h
  · have := im_f_pos_of_open h
    exact ⟨mem_phaseDomain_iff.2 (Or.inl this), mem_phaseDomain_iff.2 (Or.inl this),
      Or.inl (mem_phaseDomain_iff.2 (Or.inl this))⟩
  · have hre := (L.patchZero_spec z h).2.1
    exact ⟨mem_phaseDomain_of_re_ne (by linarith), mem_phaseDomain_of_re_ne (by linarith),
      Or.inl (mem_phaseDomain_of_re_ne (by linarith))⟩
  · have hre := (L.patchOne_spec z h).2.1
    exact ⟨mem_phaseDomain_of_re_ne (by linarith), mem_phaseDomain_of_re_ne (by linarith),
      Or.inl (mem_phaseDomain_of_re_ne (by linarith))⟩
  · obtain ⟨-, h1, h2, h3, -⟩ := L.patchTwo_spec z h
    exact ⟨mem_phaseDomain_of_re_ne (by linarith), mem_phaseDomain_of_re_ne (by linarith),
      Or.inr (by linarith)⟩

theorem norm_f_lt_of_triangle {z : ℂ} (hz : z ∈ K.σ.triangle) (h0 : z ≠ 0) :
    ‖K.D.f z‖ < 7 / 2 :=
  (K.D.bijOn_f.mapsTo ⟨hz, h0⟩).1

theorem f_main_props {z : ℂ} (hm : z ∈ L.mainSet) :
    ‖K.D.f z‖ < 7 / 2 ∧ K.D.f z ≠ 3 / 2 ∧ K.D.f z ≠ -(3 / 2) := by
  have hne : ∀ w : ℂ, w.im ≠ 0 → w ≠ 3 / 2 ∧ w ≠ -(3 / 2) := by
    intro w hw
    constructor <;> rintro rfl <;> simp at hw
  have hre : ∀ w : ℂ, (w.re < -(3 / 2) ∨ 3 / 2 < w.re ∨ (-(3 / 2) < w.re ∧ w.re < 3 / 2)) →
      w ≠ 3 / 2 ∧ w ≠ -(3 / 2) := by
    intro w hw
    constructor <;> rintro rfl <;> norm_num at hw
  have hnorm : ∀ i : Fin 3, z ∈ K.D.V i → z ≠ 0 →
      (z ∉ K.σ.triangle → K.σ.refl i z ∈ K.σ.openTriangle) → ‖K.D.f z‖ < 7 / 2 := by
    intro i hV h0 hr
    by_cases hT : z ∈ K.σ.triangle
    · exact norm_f_lt_of_triangle hT h0
    · have hT' := hr hT
      have := norm_f_lt_of_triangle (K.σ.openTriangle_subset hT')
        (K.σ.ne_of_mem_openTriangle hT').1
      rwa [K.D.f_refl i z hV, norm_conj] at this
  have h0 : z ≠ 0 := (L.main_ne z hm).1
  rcases hm with ((h | h) | h) | h
  · exact ⟨norm_f_lt_of_triangle (K.σ.openTriangle_subset h) h0,
      hne _ (im_f_pos_of_open h).ne'⟩
  · obtain ⟨hV, hr, -⟩ := L.patchZero_spec z h
    refine ⟨hnorm 0 hV h0 (L.patchZero_out z h), hre _ (Or.inl hr)⟩
  · obtain ⟨hV, hr, -⟩ := L.patchOne_spec z h
    exact ⟨hnorm 1 hV h0 (L.patchOne_out z h), hre _ (Or.inr (Or.inl hr))⟩
  · obtain ⟨hV, h1, h2, -, -⟩ := L.patchTwo_spec z h
    exact ⟨hnorm 2 hV h0 (L.patchTwo_out z h), hre _ (Or.inr (Or.inr ⟨h1, h2⟩))⟩

end SphLayout

end Sph

end ClosedTriangle

end GC.Seifert
