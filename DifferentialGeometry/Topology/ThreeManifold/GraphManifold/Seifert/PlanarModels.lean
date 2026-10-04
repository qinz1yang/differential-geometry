import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.Peripheral
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.Decomposition
import DifferentialGeometry.Topology.Manifold.SmoothBoundaryAtlas.Inclusion
import DifferentialGeometry.Topology.Manifold.ConnectedInterior

/-!
# Planar bases and the product block `T² × I`

Chapter 6, packet K06b: instances of the K06 vocabulary of `Seifert/Blocks.lean`.

The round-hole models `planarModel 2` (the annulus `1/2 ≤ ‖z‖ ≤ 3`) and `planarModel 3` (the disc
of radius `3` minus the open discs of radius `1/2` about `±3/2`) are the sublevel sets
`planarFunction k ≤ 0`, where `planarFunction k` is the product of the functions
`sqDist c ρ z = ‖z - c‖² - ρ²` of the boundary circles. At a zero of one factor the other factors do
not vanish and the differential of that factor is `2⟪z - c, ·⟫`, so `0` is a regular value
(`planarFunction_regular`). Every point of the model is joined to the outer circle by a vertical
segment along which the distance to each real centre grows, so the model is connected
(`isConnected_planarModel`).

The surface `planarSet k` is the sublevel set in `PlaneLift = ULift ℂ` (for universe
polymorphism), charted by `SmoothBoundaryAtlas.regularSublevel`, and `planarSurface k` is the
compact connected surface. Circle `j` has the collar `planarCollar k j`,
`(t, s) ↦ c_j + (r_j ∓ s/4) τ_j t` (inwards from the outer circle, outwards from the holes, `τ_j`
the identity on the outer circle and `conj` on the holes), whose inverse is read off the polar
coordinates about `c_j`; at height `0` it is `planarCircleMap k j`. The collar targets are disjoint
and the collars exhaust the boundary `planarFunction k = 0`. The embedding is the inclusion into
`ℂ`, a smooth embedding by `isSmoothEmbedding_subtype_val`. This gives `annulusSurface`,
`annulusPlanarBase : PlanarBase 2`, `pantsSurface` and `pantsPlanarBase : PlanarBase 3`.

`productSet k ⊆ PlaneLift × S¹` is the regular sublevel set of the same function in a
three-manifold, oriented by the product of an orientation of `ℂ` and `circleOrientation`;
`productCarrier k` is the compact carrier `Pₖ × S¹` and `productDiffeomorph k` identifies
`Pₖ × S¹` with it. Its boundary tori are the planar collars times the circle.
`productPresentation k` is the torus presentation with one piece, no seams and these `k` tori as
external tori, and `productFibredPiece k` exhibits the piece as product fibred over
`planarBase k`; the collar equality holds by definition. For `k = 2` this is the block
`annulusCircleBlock : T2Interval annulusCircleCarrier`, good by `t2Interval_isGoodBlock`.
-/

set_option autoImplicit false

noncomputable section
open Set Metric Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology ComplexConjugate

universe u

namespace GC.Seifert

abbrev PlaneLift : Type u := ULift.{u} ℂ

instance : ChartedSpace ℂ PlaneLift.{u} := uliftChartedSpace _ _

instance : IsManifold 𝓘(ℝ, ℂ) ∞ PlaneLift.{u} := isManifold_ulift _ _

instance : SecondCountableTopology PlaneLift.{u} :=
  (Homeomorph.ulift : PlaneLift.{u} ≃ₜ ℂ).secondCountableTopology

theorem contMDiff_planeLift_down :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (ULift.down : PlaneLift.{u} → ℂ) :=
  (uliftDiffeomorph 𝓘(ℝ, ℂ) ℂ).symm.contMDiff

theorem contMDiff_planeLift_up :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (ULift.up : ℂ → PlaneLift.{u}) :=
  (uliftDiffeomorph 𝓘(ℝ, ℂ) ℂ).contMDiff

theorem mfderiv_ne_zero_of_comp {E H M F G N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace G]
    {J : ModelWithCorners ℝ F G} [TopologicalSpace N] [ChartedSpace G N]
    {f : M → ℝ} {s : N → M} {y : N} (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f (s y))
    (hs : MDifferentiableAt J I s y) (h : mfderiv J 𝓘(ℝ, ℝ) (f ∘ s) y ≠ 0) :
    mfderiv I 𝓘(ℝ, ℝ) f (s y) ≠ 0 := by
  intro h0
  apply h
  rw [mfderiv_comp y hf hs, h0]
  exact ContinuousLinearMap.zero_comp _

def sqDist (c : ℂ) (ρ : ℝ) (z : ℂ) : ℝ := ‖z - c‖ ^ 2 - ρ ^ 2

theorem contDiff_sqDist (c : ℂ) (ρ : ℝ) : ContDiff ℝ ∞ (sqDist c ρ) :=
  ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)).sub contDiff_const

theorem fderiv_sqDist_mul_ne_zero {R : ℂ → ℝ} {c z : ℂ} {ρ : ℝ} (hR : DifferentiableAt ℝ R z)
    (hz : sqDist c ρ z = 0) (hRz : R z ≠ 0) (hρ : ρ ≠ 0) :
    fderiv ℝ (fun w => sqDist c ρ w * R w) z ≠ 0 := by
  have hq : HasFDerivAt (sqDist c ρ)
      (2 • (innerSL ℝ (z - c)).comp (ContinuousLinearMap.id ℝ ℂ)) z :=
    (((hasFDerivAt_id z).sub_const c).norm_sq).sub_const (ρ ^ 2)
  change fderiv ℝ (sqDist c ρ * R) z ≠ 0
  rw [(hq.mul hR.hasFDerivAt).fderiv]
  intro h
  have h1 := DFunLike.congr_fun h (z - c)
  have hn : ‖z - c‖ ^ 2 = ρ ^ 2 := sub_eq_zero.mp hz
  change sqDist c ρ z * fderiv ℝ R z (z - c) +
    R z * ((2 : ℕ) • inner ℝ (z - c) (z - c)) = 0 at h1
  rw [hz, zero_mul, zero_add, real_inner_self_eq_norm_sq, hn, nsmul_eq_mul, Nat.cast_ofNat] at h1
  exact mul_ne_zero hRz (mul_ne_zero two_ne_zero (pow_ne_zero 2 hρ)) h1


theorem norm_sub_eq_of_sqDist_eq_zero {c z : ℂ} {ρ : ℝ} (hρ : 0 ≤ ρ) (h : sqDist c ρ z = 0) :
    ‖z - c‖ = ρ :=
  (pow_left_inj₀ (norm_nonneg _) hρ two_ne_zero).mp (sub_eq_zero.mp h)

def planarFunction (k : ℕ) (z : ℂ) : ℝ :=
  if k = 2 then sqDist 0 3 z * sqDist 0 (1 / 2) z
  else sqDist 0 3 z * (sqDist ((3 / 2 : ℝ) : ℂ) (1 / 2) z * sqDist ((-(3 / 2) : ℝ) : ℂ) (1 / 2) z)

theorem contDiff_planarFunction (k : ℕ) : ContDiff ℝ ∞ (planarFunction k) := by
  unfold planarFunction
  split_ifs
  · exact (contDiff_sqDist _ _).mul (contDiff_sqDist _ _)
  · exact (contDiff_sqDist _ _).mul ((contDiff_sqDist _ _).mul (contDiff_sqDist _ _))

theorem norm_sub_real_bounds (z : ℂ) (c : ℝ) : ‖z‖ - |c| ≤ ‖z - c‖ ∧ ‖z - c‖ ≤ ‖z‖ + |c| := by
  have h1 := norm_sub_norm_le z (c : ℂ)
  have h2 := norm_sub_le z (c : ℂ)
  rw [Complex.norm_real, Real.norm_eq_abs] at h1 h2
  exact ⟨h1, h2⟩

theorem three_le_norm_sub_add_norm_sub (z : ℂ) :
    3 ≤ ‖z - ((3 / 2 : ℝ) : ℂ)‖ + ‖z - ((-(3 / 2) : ℝ) : ℂ)‖ := by
  have h := norm_sub_le (z - ((-(3 / 2) : ℝ) : ℂ)) (z - ((3 / 2 : ℝ) : ℂ))
  have he : (z - ((-(3 / 2) : ℝ) : ℂ)) - (z - ((3 / 2 : ℝ) : ℂ)) = ((3 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 3)] at h
  linarith

theorem mem_planarModel_two (z : ℂ) : z ∈ planarModel 2 ↔ ‖z‖ ≤ 3 ∧ 1 / 2 ≤ ‖z‖ := by
  simp [planarModel, Fin.forall_fin_two, planarCenter]

theorem mem_planarModel_three (z : ℂ) : z ∈ planarModel 3 ↔
    ‖z‖ ≤ 3 ∧ 1 / 2 ≤ ‖z - ((3 / 2 : ℝ) : ℂ)‖ ∧ 1 / 2 ≤ ‖z - ((-(3 / 2) : ℝ) : ℂ)‖ := by
  simp [planarModel, Fin.forall_fin_succ, planarCenter]


theorem planarFunction_two (z : ℂ) :
    planarFunction 2 z = (‖z‖ ^ 2 - 3 ^ 2) * (‖z‖ ^ 2 - (1 / 2) ^ 2) := by
  simp [planarFunction, sqDist]

theorem planarFunction_three (z : ℂ) : planarFunction 3 z = (‖z‖ ^ 2 - 3 ^ 2) *
    ((‖z - ((3 / 2 : ℝ) : ℂ)‖ ^ 2 - (1 / 2) ^ 2) *
      (‖z - ((-(3 / 2) : ℝ) : ℂ)‖ ^ 2 - (1 / 2) ^ 2)) := by
  simp only [planarFunction, sqDist, sub_zero]
  rfl

theorem planarFunction_nonpos_iff {k : ℕ} (hk : k = 2 ∨ k = 3) (z : ℂ) :
    planarFunction k z ≤ 0 ↔ z ∈ planarModel k := by
  have h0 := norm_nonneg z
  rcases hk with rfl | rfl
  · rw [mem_planarModel_two, planarFunction_two]
    constructor
    · intro h
      by_contra hc
      rw [not_and_or, not_le, not_le] at hc
      rcases hc with hc | hc
      · have : 0 < (‖z‖ ^ 2 - 3 ^ 2) * (‖z‖ ^ 2 - (1 / 2) ^ 2) :=
          mul_pos (by nlinarith) (by nlinarith)
        linarith
      · have : 0 < (‖z‖ ^ 2 - 3 ^ 2) * (‖z‖ ^ 2 - (1 / 2) ^ 2) :=
          mul_pos_of_neg_of_neg (by nlinarith) (by nlinarith)
        linarith
    · rintro ⟨h1, h2⟩
      exact mul_nonpos_iff.mpr (Or.inr ⟨by nlinarith, by nlinarith⟩)
  · rw [mem_planarModel_three, planarFunction_three]
    have hb := norm_sub_real_bounds z (3 / 2)
    have hc := norm_sub_real_bounds z (-(3 / 2))
    have h3 := three_le_norm_sub_add_norm_sub z
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)] at hb
    rw [abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)] at hc
    have hb0 := norm_nonneg (z - ((3 / 2 : ℝ) : ℂ))
    have hc0 := norm_nonneg (z - ((-(3 / 2) : ℝ) : ℂ))
    set a := ‖z‖
    set b := ‖z - ((3 / 2 : ℝ) : ℂ)‖
    set c := ‖z - ((-(3 / 2) : ℝ) : ℂ)‖
    constructor
    · intro h
      refine ⟨?_, ?_, ?_⟩
      · by_contra ha
        have : 0 < (a ^ 2 - 3 ^ 2) * ((b ^ 2 - (1 / 2) ^ 2) * (c ^ 2 - (1 / 2) ^ 2)) :=
          mul_pos (by nlinarith) (mul_pos (by nlinarith) (by nlinarith))
        linarith
      · by_contra hb'
        have : 0 < (a ^ 2 - 3 ^ 2) * ((b ^ 2 - (1 / 2) ^ 2) * (c ^ 2 - (1 / 2) ^ 2)) :=
          mul_pos_of_neg_of_neg (by nlinarith) (mul_neg_of_neg_of_pos (by nlinarith) (by nlinarith))
        linarith
      · by_contra hc'
        have : 0 < (a ^ 2 - 3 ^ 2) * ((b ^ 2 - (1 / 2) ^ 2) * (c ^ 2 - (1 / 2) ^ 2)) :=
          mul_pos_of_neg_of_neg (by nlinarith) (mul_neg_of_pos_of_neg (by nlinarith) (by nlinarith))
        linarith
    · rintro ⟨h1, h2, h3⟩
      exact mul_nonpos_iff.mpr (Or.inr ⟨by nlinarith, mul_nonneg (by nlinarith) (by nlinarith)⟩)

theorem sq_sub_sq_eq_zero_iff {a ρ : ℝ} (ha : 0 ≤ a) (hρ : 0 ≤ ρ) :
    a ^ 2 - ρ ^ 2 = 0 ↔ a = ρ := by
  rw [sub_eq_zero]
  exact pow_left_inj₀ ha hρ two_ne_zero

theorem planarFunction_eq_zero_iff {k : ℕ} (hk : k = 2 ∨ k = 3) (z : ℂ) :
    planarFunction k z = 0 ↔ ∃ j : Fin k, ‖z - planarCenter k j‖ = planarRadius j := by
  have h3 : (0 : ℝ) ≤ 3 := by norm_num
  have h12 : (0 : ℝ) ≤ 1 / 2 := by norm_num
  rcases hk with rfl | rfl
  · rw [planarFunction_two, mul_eq_zero, sq_sub_sq_eq_zero_iff (norm_nonneg _) h3,
      sq_sub_sq_eq_zero_iff (norm_nonneg _) h12, Fin.exists_fin_two]
    simp [planarCenter, planarRadius]
  · rw [planarFunction_three, mul_eq_zero, mul_eq_zero, sq_sub_sq_eq_zero_iff (norm_nonneg _) h3,
      sq_sub_sq_eq_zero_iff (norm_nonneg _) h12, sq_sub_sq_eq_zero_iff (norm_nonneg _) h12,
      Fin.exists_fin_succ, Fin.exists_fin_succ, Fin.exists_fin_one]
    simp [planarCenter, planarRadius]

theorem planarFunction_regular (k : ℕ) {z : ℂ} (hz : planarFunction k z = 0) :
    fderiv ℝ (planarFunction k) z ≠ 0 := by
  have hd (c : ℂ) (ρ : ℝ) : DifferentiableAt ℝ (sqDist c ρ) z :=
    (contDiff_sqDist c ρ).differentiable (by simp) z
  have h3 : (0 : ℝ) ≤ 3 := by norm_num
  have h12 : (0 : ℝ) ≤ 1 / 2 := by norm_num
  by_cases hk : k = 2
  · have he : planarFunction k = fun w => sqDist 0 3 w * sqDist 0 (1 / 2) w := by
      funext w
      simp [planarFunction, hk]
    rw [he] at hz ⊢
    rcases mul_eq_zero.mp hz with h | h
    · have hn := norm_sub_eq_of_sqDist_eq_zero h3 h
      refine fderiv_sqDist_mul_ne_zero (hd _ _) h ?_ (by norm_num)
      rw [sqDist, hn]
      norm_num
    · have hn := norm_sub_eq_of_sqDist_eq_zero h12 h
      rw [show (fun w => sqDist 0 3 w * sqDist 0 (1 / 2) w) =
        fun w => sqDist 0 (1 / 2) w * sqDist 0 3 w from funext fun w => mul_comm _ _]
      refine fderiv_sqDist_mul_ne_zero (hd _ _) h ?_ (by norm_num)
      rw [sqDist, hn]
      norm_num
  · have he : planarFunction k = fun w => sqDist 0 3 w *
        (sqDist ((3 / 2 : ℝ) : ℂ) (1 / 2) w * sqDist ((-(3 / 2) : ℝ) : ℂ) (1 / 2) w) := by
      funext w
      simp [planarFunction, hk]
    rw [he] at hz ⊢
    have hb := norm_sub_real_bounds z (3 / 2)
    have hc := norm_sub_real_bounds z (-(3 / 2))
    have h3' := three_le_norm_sub_add_norm_sub z
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)] at hb
    rw [abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)] at hc
    have hb0 := norm_nonneg (z - ((3 / 2 : ℝ) : ℂ))
    have hc0 := norm_nonneg (z - ((-(3 / 2) : ℝ) : ℂ))
    rcases mul_eq_zero.mp hz with h | h
    · have hn := norm_sub_eq_of_sqDist_eq_zero h3 h
      rw [sub_zero] at hn
      refine fderiv_sqDist_mul_ne_zero ((hd _ _).mul (hd _ _)) h ?_ (by norm_num)
      simp only [sqDist]
      exact mul_ne_zero (by nlinarith) (by nlinarith)
    · rcases mul_eq_zero.mp h with h | h
      · have hn := norm_sub_eq_of_sqDist_eq_zero h12 h
        rw [show (fun w => sqDist 0 3 w * (sqDist ((3 / 2 : ℝ) : ℂ) (1 / 2) w *
            sqDist ((-(3 / 2) : ℝ) : ℂ) (1 / 2) w)) = fun w => sqDist ((3 / 2 : ℝ) : ℂ) (1 / 2) w *
            (sqDist 0 3 w * sqDist ((-(3 / 2) : ℝ) : ℂ) (1 / 2) w) from
          funext fun w => by ring]
        refine fderiv_sqDist_mul_ne_zero ((hd _ _).mul (hd _ _)) h ?_ (by norm_num)
        simp only [sqDist, sub_zero]
        exact mul_ne_zero (by nlinarith) (by nlinarith)
      · have hn := norm_sub_eq_of_sqDist_eq_zero h12 h
        rw [show (fun w => sqDist 0 3 w * (sqDist ((3 / 2 : ℝ) : ℂ) (1 / 2) w *
            sqDist ((-(3 / 2) : ℝ) : ℂ) (1 / 2) w)) =
            fun w => sqDist ((-(3 / 2) : ℝ) : ℂ) (1 / 2) w *
            (sqDist 0 3 w * sqDist ((3 / 2 : ℝ) : ℂ) (1 / 2) w) from
          funext fun w => by ring]
        refine fderiv_sqDist_mul_ne_zero ((hd _ _).mul (hd _ _)) h ?_ (by norm_num)
        simp only [sqDist, sub_zero]
        exact mul_ne_zero (by nlinarith) (by nlinarith)


theorem abs_planarCenter_le (k : ℕ) (j : Fin k) : |planarCenter k j| ≤ 3 / 2 := by
  unfold planarCenter
  split_ifs <;> norm_num

theorem outer_mem_planarModel (k : ℕ) (t : Circle) : (3 : ℝ) • (t : ℂ) ∈ planarModel k := by
  have hn : ‖(3 : ℝ) • (t : ℂ)‖ = 3 := by
    rw [norm_smul, Circle.norm_coe, mul_one, Real.norm_of_nonneg (by norm_num)]
  refine ⟨hn.le, fun j _ => ?_⟩
  have h1 := (norm_sub_real_bounds ((3 : ℝ) • (t : ℂ)) (planarCenter k j)).1
  have := abs_planarCenter_le k j
  linarith

def verticalSign (z : ℂ) : ℝ := if 0 ≤ z.im then 1 else -1

def verticalPoint (z : ℂ) : ℂ := ⟨z.re, verticalSign z * √(9 - z.re ^ 2)⟩

theorem verticalSign_mul_im (z : ℂ) : verticalSign z * z.im = |z.im| := by
  unfold verticalSign
  split_ifs with h
  · rw [one_mul, abs_of_nonneg h]
  · rw [abs_of_neg (not_le.mp h)]
    ring

theorem verticalSign_sq (z : ℂ) : verticalSign z ^ 2 = 1 := by
  unfold verticalSign
  split_ifs <;> norm_num

theorem re_sq_le_of_norm_le {z : ℂ} (hz : ‖z‖ ≤ 3) : z.re ^ 2 + z.im ^ 2 ≤ 9 := by
  have h := Complex.sq_norm z
  rw [Complex.normSq_apply] at h
  nlinarith [norm_nonneg z]

theorem norm_verticalPoint {z : ℂ} (hz : ‖z‖ ≤ 3) : ‖verticalPoint z‖ = 3 := by
  have h := re_sq_le_of_norm_le hz
  have hs : √(9 - z.re ^ 2) ^ 2 = 9 - z.re ^ 2 := Real.sq_sqrt (by nlinarith)
  have hsq : ‖verticalPoint z‖ ^ 2 = 3 ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [verticalPoint]
    nlinarith [verticalSign_sq z]
  exact (pow_left_inj₀ (norm_nonneg _) (by norm_num) two_ne_zero).mp hsq

theorem verticalPoint_mem_range {z : ℂ} (hz : ‖z‖ ≤ 3) :
    verticalPoint z ∈ range fun t : Circle => (3 : ℝ) • (t : ℂ) := by
  refine ⟨unitOf (verticalPoint z), ?_⟩
  change (3 : ℝ) • (unitOf (verticalPoint z) : ℂ) = verticalPoint z
  rw [← norm_verticalPoint hz]
  exact norm_smul_unitOf _

theorem segment_verticalPoint_subset {k : ℕ} {z : ℂ} (hz : z ∈ planarModel k) :
    segment ℝ z (verticalPoint z) ⊆ planarModel k := by
  rintro w ⟨a, b, ha, hb, hab, rfl⟩
  have h9 := re_sq_le_of_norm_le hz.1
  have hm0 : 0 ≤ 9 - z.re ^ 2 := by nlinarith
  have hs : √(9 - z.re ^ 2) ^ 2 = 9 - z.re ^ 2 := Real.sq_sqrt hm0
  have hs0 := Real.sqrt_nonneg (9 - z.re ^ 2)
  have him : |z.im| ≤ √(9 - z.re ^ 2) := Real.abs_le_sqrt (by nlinarith)
  have hre : (a • z + b • verticalPoint z).re = z.re := by
    simp only [Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, verticalPoint]
    rw [← add_mul, hab, one_mul]
  have hsg := verticalSign_sq z
  have hsi := verticalSign_mul_im z
  have hσ : verticalSign z * (a • z + b • verticalPoint z).im =
      a * |z.im| + b * √(9 - z.re ^ 2) := by
    simp only [Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero, verticalPoint]
    rw [← hsi]
    linear_combination (b * √(9 - z.re ^ 2)) * hsg
  set w := a • z + b • verticalPoint z
  have habs := abs_nonneg z.im
  have hlow : |z.im| ≤ verticalSign z * w.im := by
    rw [hσ]
    nlinarith
  have hup : verticalSign z * w.im ≤ √(9 - z.re ^ 2) := by
    rw [hσ]
    nlinarith
  have hw2 : w.im ^ 2 = (verticalSign z * w.im) ^ 2 := by
    rw [mul_pow, hsg, one_mul]
  have hz2 : z.im ^ 2 = |z.im| ^ 2 := (sq_abs _).symm
  have hlo2 : z.im ^ 2 ≤ w.im ^ 2 := by
    rw [hw2, hz2]
    exact pow_le_pow_left₀ habs hlow 2
  have hup2 : w.im ^ 2 ≤ 9 - z.re ^ 2 := by
    rw [hw2, ← hs]
    exact pow_le_pow_left₀ (habs.trans hlow) hup 2
  refine ⟨?_, fun j hj => ?_⟩
  · have hn := Complex.sq_norm w
    rw [Complex.normSq_apply, hre] at hn
    nlinarith [norm_nonneg w]
  · have hzj := hz.2 j hj
    have hn := Complex.sq_norm (w - planarCenter k j)
    have hn' := Complex.sq_norm (z - planarCenter k j)
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, sub_zero, hre] at hn hn'
    nlinarith [norm_nonneg (w - planarCenter k j), norm_nonneg (z - planarCenter k j)]

theorem isConnected_planarModel (k : ℕ) : IsConnected (planarModel k) := by
  have hc : Continuous fun t : Circle => (3 : ℝ) • (t : ℂ) :=
    contMDiff_circle_coe.continuous.const_smul (3 : ℝ)
  refine ⟨⟨_, outer_mem_planarModel k 1⟩,
    isPreconnected_of_forall ((3 : ℝ) • ((1 : Circle) : ℂ)) fun y hy => ?_⟩
  refine ⟨(range fun t : Circle => (3 : ℝ) • (t : ℂ)) ∪ segment ℝ y (verticalPoint y),
    union_subset (range_subset_iff.mpr (outer_mem_planarModel k))
      (segment_verticalPoint_subset hy), Or.inl ⟨1, rfl⟩, Or.inr (left_mem_segment ℝ _ _), ?_⟩
  exact (isPreconnected_range hc).union (verticalPoint y) (verticalPoint_mem_range hy.1)
    (right_mem_segment ℝ _ _) (convex_segment _ _).isPreconnected

theorem isCompact_planarModel {k : ℕ} (hk : k = 2 ∨ k = 3) : IsCompact (planarModel k) := by
  have he : planarModel k = {z | planarFunction k z ≤ 0} := by
    ext z
    exact (planarFunction_nonpos_iff hk z).symm
  refine isCompact_of_isClosed_isBounded ?_ ?_
  · rw [he]
    exact isClosed_le (contDiff_planarFunction k).continuous continuous_const
  · exact (isBounded_closedBall (x := (0 : ℂ)) (r := 3)).subset fun z hz =>
      mem_closedBall_zero_iff.mpr hz.1


def planarSet (k : ℕ) : Set PlaneLift.{u} := {w | planarFunction k w.down ≤ 0}

theorem mem_planarSet_iff {k : ℕ} (hk : k = 2 ∨ k = 3) (w : PlaneLift.{u}) :
    w ∈ planarSet k ↔ w.down ∈ planarModel k :=
  planarFunction_nonpos_iff hk w.down

theorem contMDiff_planarFunction_down (k : ℕ) :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞ (fun w : PlaneLift.{u} => planarFunction k w.down) :=
  (contDiff_planarFunction k).contMDiff.comp contMDiff_planeLift_down

theorem planarFunction_down_regular (k : ℕ) (w : PlaneLift.{u})
    (hw : planarFunction k w.down = 0) :
    mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) (fun w : PlaneLift.{u} => planarFunction k w.down) w ≠ 0 := by
  refine mfderiv_ne_zero_of_comp (J := 𝓘(ℝ, ℂ)) (s := ULift.up) (y := w.down)
    ((contMDiff_planarFunction_down k).mdifferentiableAt (by simp))
    (contMDiff_planeLift_up.mdifferentiableAt (by simp)) ?_
  change mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) (planarFunction k) w.down ≠ 0
  rw [mfderiv_eq_fderiv]
  exact planarFunction_regular k hw

def planarAtlas (k : ℕ) : SmoothBoundaryAtlas 𝓘(ℝ, ℂ) 2 (planarSet.{u} k) :=
  SmoothBoundaryAtlas.regularSublevel 𝓘(ℝ, ℂ) (n := 1) Complex.finrank_real_complex
    (contMDiff_planarFunction_down.{u} k) 0 (planarFunction_down_regular k)

instance (k : ℕ) : ChartedSpace (EuclideanHalfSpace 2) (planarSet.{u} k) :=
  (planarAtlas k).toChartedSpace

instance (k : ℕ) : IsManifold (𝓡∂ 2) ∞ (planarSet.{u} k) := (planarAtlas k).isManifold

theorem planarSet_isBoundaryPoint_iff (k : ℕ) (x : planarSet.{u} k) :
    (𝓡∂ 2).IsBoundaryPoint x ↔ planarFunction k x.val.down = 0 :=
  SmoothBoundaryAtlas.regularSublevel_isBoundaryPoint_iff 𝓘(ℝ, ℂ) (n := 1)
    Complex.finrank_real_complex (contMDiff_planarFunction_down k) 0
    (planarFunction_down_regular k) x

theorem contMDiff_planarSet_down (k : ℕ) :
    ContMDiff (𝓡∂ 2) 𝓘(ℝ, ℂ) ∞ (fun x : planarSet.{u} k => x.val.down) :=
  contMDiff_planeLift_down.comp (planarAtlas k).contMDiff_subtype_val

theorem planarSet_eq_preimage {k : ℕ} (hk : k = 2 ∨ k = 3) :
    planarSet.{u} k = (Homeomorph.ulift : PlaneLift.{u} ≃ₜ ℂ) ⁻¹' planarModel k := by
  ext w
  exact mem_planarSet_iff hk w

def planarSurface (k : ℕ) (hk : k = 2 ∨ k = 3) : CompactSurface.{u} where
  kind := .withBoundary
  Carrier := planarSet.{u} k
  charts := (inferInstance : ChartedSpace (EuclideanHalfSpace 2) (planarSet.{u} k))
  smooth := (inferInstance : IsManifold (𝓡∂ 2) ∞ (planarSet.{u} k))
  compact := isCompact_iff_compactSpace.mp (by
    rw [planarSet_eq_preimage hk]
    exact Homeomorph.ulift.isCompact_preimage.mpr (isCompact_planarModel hk))
  connected := isConnected_iff_connectedSpace.mp (by
    rw [planarSet_eq_preimage hk]
    exact Homeomorph.ulift.isConnected_preimage.mpr (isConnected_planarModel k))


def planarTwist {k : ℕ} (j : Fin k) (w : ℂ) : ℂ := if j.val = 0 then w else conj w

def planarSign {k : ℕ} (j : Fin k) : ℝ := if j.val = 0 then -1 else 1

theorem planarTwist_planarTwist {k : ℕ} (j : Fin k) (w : ℂ) :
    planarTwist j (planarTwist j w) = w := by
  unfold planarTwist
  split_ifs <;> simp

theorem planarTwist_smul {k : ℕ} (j : Fin k) (a : ℝ) (w : ℂ) :
    planarTwist j (a • w) = a • planarTwist j w := by
  unfold planarTwist
  split_ifs <;> simp [Complex.real_smul]

theorem norm_planarTwist {k : ℕ} (j : Fin k) (w : ℂ) : ‖planarTwist j w‖ = ‖w‖ := by
  unfold planarTwist
  split_ifs <;> simp

theorem contDiff_planarTwist {k : ℕ} (j : Fin k) : ContDiff ℝ ∞ (planarTwist j) := by
  unfold planarTwist
  split_ifs
  · exact contDiff_id
  · exact Complex.conjCLE.contDiff

theorem planarSign_mul_self {k : ℕ} (j : Fin k) : planarSign j * planarSign j = 1 := by
  unfold planarSign
  split_ifs <;> norm_num

theorem planarRadius_gt {k : ℕ} (j : Fin k) : 1 / 4 < planarRadius j := by
  unfold planarRadius
  split_ifs <;> norm_num

theorem planarCenter_zero {k : ℕ} {j : Fin k} (hj : j.val = 0) : planarCenter k j = 0 := by
  simp [planarCenter, hj]

theorem planarSign_mul_nonneg {k : ℕ} (j : Fin k) {z : ℂ} (hz : z ∈ planarModel k) :
    0 ≤ planarSign j * (‖z - planarCenter k j‖ - planarRadius j) := by
  by_cases hj : j.val = 0
  · simp only [planarSign, planarRadius, hj, ↓reduceIte, planarCenter_zero hj, Complex.ofReal_zero,
      sub_zero]
    linarith [hz.1]
  · simp only [planarSign, planarRadius, hj, ↓reduceIte, one_mul]
    linarith [hz.2 j hj]

theorem planarCollar_ne {k : ℕ} (j : Fin k) {z : ℂ} (hz : z ∈ planarModel k)
    (ht : planarSign j * (‖z - planarCenter k j‖ - planarRadius j) < 1 / 4) :
    z - planarCenter k j ≠ 0 := by
  have h0 := planarSign_mul_nonneg j hz
  rw [← norm_pos_iff]
  by_cases hj : j.val = 0
  · simp only [planarSign, planarRadius, hj, ↓reduceIte] at ht
    linarith
  · simp only [planarSign, planarRadius, hj, ↓reduceIte, one_mul] at h0
    linarith

def planarCollarFormula (k : ℕ) (j : Fin k) (q : ℂ × ℝ) : ℂ :=
  planarCenter k j + (planarRadius j + planarSign j * q.2 / 4) • planarTwist j q.1

theorem contDiff_planarCollarFormula (k : ℕ) (j : Fin k) :
    ContDiff ℝ ∞ (planarCollarFormula k j) :=
  contDiff_const.add ((contDiff_const.add ((contDiff_const.mul contDiff_snd).div_const 4)).smul
    ((contDiff_planarTwist j).comp contDiff_fst))

theorem planarCollarFormula_sub (k : ℕ) (j : Fin k) (q : ℂ × ℝ) :
    planarCollarFormula k j q - planarCenter k j =
      (planarRadius j + planarSign j * q.2 / 4) • planarTwist j q.1 :=
  add_sub_cancel_left _ _

theorem planarCollarRadius_pos {k : ℕ} (j : Fin k) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    0 < planarRadius j + planarSign j * s / 4 := by
  have := planarRadius_gt j
  unfold planarSign
  split_ifs <;> linarith

theorem norm_planarCollarFormula_sub {k : ℕ} (j : Fin k) (t : Circle) {s : ℝ} (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1) : ‖planarCollarFormula k j ((t : ℂ), s) - planarCenter k j‖ =
      planarRadius j + planarSign j * s / 4 := by
  rw [planarCollarFormula_sub, norm_smul, norm_planarTwist, Circle.norm_coe, mul_one,
    Real.norm_of_nonneg (planarCollarRadius_pos j hs0 hs1).le]

theorem planarSign_mul_collar {k : ℕ} (j : Fin k) (t : Circle) {s : ℝ} (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1) : planarSign j *
      (‖planarCollarFormula k j ((t : ℂ), s) - planarCenter k j‖ - planarRadius j) = s / 4 := by
  rw [norm_planarCollarFormula_sub j t hs0 hs1]
  have := planarSign_mul_self j
  linear_combination (s / 4) * this

theorem two_le_abs_planarCenter_sub {k : ℕ} (hk : k = 2 ∨ k = 3) {j j' : Fin k}
    (hj : j.val ≠ 0) (hj' : j'.val ≠ 0) (hne : j ≠ j') :
    2 ≤ |planarCenter k j - planarCenter k j'| := by
  rcases hk with rfl | rfl
  · fin_cases j <;> fin_cases j' <;> simp_all
  · fin_cases j <;> fin_cases j' <;> simp_all [planarCenter] <;> norm_num

theorem le_norm_sub_planarCenter (z : ℂ) (c c' : ℝ) :
    |c - c'| - ‖z - c‖ ≤ ‖z - c'‖ := by
  have h := norm_sub_le (z - c') (z - c)
  rw [show z - (c' : ℂ) - (z - c) = ((c - c' : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
    Real.norm_eq_abs] at h
  linarith

theorem planarCollarFormula_mem {k : ℕ} (hk : k = 2 ∨ k = 3) (j : Fin k) (t : Circle) {s : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : planarCollarFormula k j ((t : ℂ), s) ∈ planarModel k := by
  set p := planarCollarFormula k j ((t : ℂ), s)
  have hn := norm_planarCollarFormula_sub j t hs0 hs1
  have hcj := abs_planarCenter_le k j
  have hb := norm_sub_real_bounds p (planarCenter k j)
  by_cases hj : j.val = 0
  · simp only [planarSign, planarRadius, hj, ↓reduceIte] at hn
    rw [planarCenter_zero hj, Complex.ofReal_zero, sub_zero] at hn
    refine ⟨by linarith, fun j' hj' => ?_⟩
    have := (norm_sub_real_bounds p (planarCenter k j')).1
    have := abs_planarCenter_le k j'
    linarith
  · simp only [planarSign, planarRadius, hj, ↓reduceIte, one_mul] at hn
    refine ⟨by linarith [hb.1, hb.2], fun j' hj' => ?_⟩
    by_cases hjj : j = j'
    · subst hjj
      linarith
    · have := two_le_abs_planarCenter_sub hk hj hj' hjj
      have := le_norm_sub_planarCenter p (planarCenter k j) (planarCenter k j')
      linarith

theorem halfSpaceOneLift_coord (h : EuclideanHalfSpace 1) :
    Manifold.halfSpaceOneLift (h.val 0) = h := by
  rw [← halfPoint_eq_halfSpaceOneLift _ h.2]
  exact halfPoint_coord_eq h

def planarCollarMap (k : ℕ) (hk : k = 2 ∨ k = 3) (j : Fin k)
    (p : Circle × EuclideanHalfSpace 1) : planarSet.{u} k :=
  ⟨ULift.up (planarCollarFormula k j ((p.1 : ℂ), min (p.2.val 0) 1)),
    (mem_planarSet_iff hk _).mpr
      (planarCollarFormula_mem hk j p.1 (le_min p.2.2 zero_le_one) (min_le_right _ _))⟩

def planarCollarInv (k : ℕ) (j : Fin k) (x : planarSet.{u} k) :
    Circle × EuclideanHalfSpace 1 :=
  (unitOf (planarTwist j (x.val.down - planarCenter k j)), Manifold.halfSpaceOneLift
    (4 * (planarSign j * (‖x.val.down - planarCenter k j‖ - planarRadius j))))

def planarCollarTarget (k : ℕ) (j : Fin k) : Set (planarSet.{u} k) :=
  {x | planarSign j * (‖x.val.down - planarCenter k j‖ - planarRadius j) < 1 / 4}

theorem isOpen_planarCollarTarget (k : ℕ) (j : Fin k) :
    IsOpen (planarCollarTarget.{u} k j) :=
  isOpen_lt (continuous_const.mul (((continuous_norm.comp
    ((contMDiff_planarSet_down k).continuous.sub continuous_const))).sub continuous_const))
    continuous_const

theorem planarCollarMap_val {k : ℕ} (hk : k = 2 ∨ k = 3) (j : Fin k)
    {p : Circle × EuclideanHalfSpace 1} (hp : p ∈ circleCollarSource) :
    (planarCollarMap.{u} k hk j p).val.down = planarCollarFormula k j ((p.1 : ℂ), p.2.val 0) := by
  have hp' : p.2.val 0 < 1 := hp
  change planarCollarFormula k j ((p.1 : ℂ), min (p.2.val 0) 1) = _
  rw [min_eq_left hp'.le]

def planarCollar (k : ℕ) (hk : k = 2 ∨ k = 3) (j : Fin k) :
    PartialDiffeomorph circleCollarModel (𝓡∂ 2) (Circle × EuclideanHalfSpace 1)
      (planarSet.{u} k) ∞ where
  toFun := planarCollarMap.{u} k hk j
  invFun := planarCollarInv.{u} k j
  source := circleCollarSource
  target := planarCollarTarget k j
  map_source' := by
    intro p hp
    have hp' : p.2.val 0 < 1 := hp
    change planarSign j * (‖(planarCollarMap.{u} k hk j p).val.down - planarCenter k j‖ -
      planarRadius j) < 1 / 4
    rw [planarCollarMap_val hk j hp, planarSign_mul_collar j p.1 p.2.2 hp'.le]
    linarith
  map_target' := by
    intro x hx
    have hx' : planarSign j * (‖x.val.down - planarCenter k j‖ - planarRadius j) < 1 / 4 := hx
    change max (4 * (planarSign j * (‖x.val.down - planarCenter k j‖ - planarRadius j))) 0 < 1
    exact max_lt (by linarith) one_pos
  left_inv' := by
    intro p hp
    have hp' : p.2.val 0 < 1 := hp
    have hs0 := p.2.2
    change planarCollarInv.{u} k j (planarCollarMap.{u} k hk j p) = p
    unfold planarCollarInv
    rw [planarCollarMap_val hk j hp, planarSign_mul_collar j p.1 hs0 hp'.le,
      planarCollarFormula_sub, planarTwist_smul, planarTwist_planarTwist,
      unitOf_smul (planarCollarRadius_pos j hs0 hp'.le),
      show 4 * (p.2.val 0 / 4) = p.2.val 0 by ring, halfSpaceOneLift_coord]
  right_inv' := by
    intro x hx
    have hx' : planarSign j * (‖x.val.down - planarCenter k j‖ - planarRadius j) < 1 / 4 := hx
    have hz := (mem_planarSet_iff hk x.val).mp x.2
    have h0 := planarSign_mul_nonneg j hz
    set v := 4 * (planarSign j * (‖x.val.down - planarCenter k j‖ - planarRadius j)) with hv
    have hv0 : 0 ≤ v := by rw [hv]; positivity
    have hv1 : v < 1 := by rw [hv]; linarith
    have hsrc : planarCollarInv.{u} k j x ∈ circleCollarSource := by
      change max v 0 < 1
      exact max_lt hv1 one_pos
    apply Subtype.ext
    apply ULift.ext
    rw [planarCollarMap_val hk j hsrc]
    change planarCollarFormula k j ((unitOf (planarTwist j (x.val.down - planarCenter k j)) : ℂ),
      max v 0) = x.val.down
    rw [max_eq_left hv0]
    unfold planarCollarFormula
    have hr : planarRadius j + planarSign j * v / 4 = ‖x.val.down - planarCenter k j‖ := by
      rw [hv]
      linear_combination (‖x.val.down - planarCenter k j‖ - planarRadius j) * planarSign_mul_self j
    simp only
    rw [hr, ← norm_planarTwist j, ← planarTwist_smul, norm_smul_unitOf, planarTwist_planarTwist,
      add_sub_cancel]
  open_source := isOpen_lt
    ((EuclideanSpace.proj 0).continuous.comp (continuous_subtype_val.comp continuous_snd))
    continuous_const
  open_target := isOpen_planarCollarTarget k j
  contMDiffOn_toFun := by
    refine ((planarAtlas k).contMDiffOn_iff_subtype_val _ _).mpr ?_
    have hpair : ContMDiff circleCollarModel 𝓘(ℝ, ℂ × ℝ) ∞
        (fun p : Circle × EuclideanHalfSpace 1 => ((p.1 : ℂ), p.2.val 0)) :=
      (contMDiff_circle_coe.comp contMDiff_fst).prodMk_space
        (Manifold.contMDiff_halfSpaceOneCoordinate.comp contMDiff_snd)
    have h := contMDiff_planeLift_up.{u}.comp
      ((contDiff_planarCollarFormula k j).contMDiff.comp hpair)
    refine h.contMDiffOn.congr fun p hp => ?_
    change ULift.up (planarCollarMap.{u} k hk j p).val.down = _
    rw [planarCollarMap_val hk j hp]
    rfl
  contMDiffOn_invFun := by
    have hD : ContMDiff (𝓡∂ 2) 𝓘(ℝ, ℂ) ∞
        (fun x : planarSet.{u} k => x.val.down - planarCenter k j) :=
      (contDiff_id.sub contDiff_const).contMDiff.comp (contMDiff_planarSet_down k)
    have hne : ∀ x ∈ planarCollarTarget.{u} k j, x.val.down - planarCenter k j ≠ 0 :=
      fun x hx => planarCollar_ne j ((mem_planarSet_iff hk x.val).mp x.2) hx
    have hfirst : ContMDiffOn (𝓡∂ 2) (𝓡 1) ∞
        (fun x : planarSet.{u} k => unitOf (planarTwist j (x.val.down - planarCenter k j)))
        (planarCollarTarget k j) :=
      contMDiffOn_unitOf.comp ((contDiff_planarTwist j).contMDiff.comp hD).contMDiffOn
        fun x hx => by
          change planarTwist j _ ≠ 0
          rw [← norm_pos_iff, norm_planarTwist, norm_pos_iff]
          exact hne x hx
    have hnorm : ContMDiffOn (𝓡∂ 2) 𝓘(ℝ, ℝ) ∞
        (fun x : planarSet.{u} k =>
          4 * (planarSign j * (‖x.val.down - planarCenter k j‖ - planarRadius j)))
        (planarCollarTarget k j) := by
      intro x hx
      have hn : ContMDiffAt (𝓡∂ 2) 𝓘(ℝ, ℝ) ∞
          (fun x : planarSet.{u} k => ‖x.val.down - planarCenter k j‖) x :=
        (contDiffAt_norm ℝ (hne x hx)).contMDiffAt.comp x (hD x)
      exact ((contDiff_const.mul (contDiff_const.mul (contDiff_id.sub contDiff_const))).contMDiff
        |>.contMDiffAt.comp x hn).contMDiffWithinAt
    have hsecond : ContMDiffOn (𝓡∂ 2) (𝓡∂ 1) ∞
        (fun x : planarSet.{u} k => Manifold.halfSpaceOneLift
          (4 * (planarSign j * (‖x.val.down - planarCenter k j‖ - planarRadius j))))
        (planarCollarTarget k j) :=
      Manifold.contMDiffOn_halfSpaceOneLift.comp hnorm fun x _ => by
        have := planarSign_mul_nonneg j ((mem_planarSet_iff hk x.val).mp x.2)
        change (0 : ℝ) ≤ _
        positivity
    exact hfirst.prodMk hsecond


theorem planarCollar_apply_val {k : ℕ} (hk : k = 2 ∨ k = 3) (j : Fin k)
    {p : Circle × EuclideanHalfSpace 1} (hp : p ∈ circleCollarSource) :
    (planarCollar.{u} k hk j p).val.down = planarCollarFormula k j ((p.1 : ℂ), p.2.val 0) :=
  planarCollarMap_val hk j hp

theorem halfZero_mem_circleCollarSource (t : Circle) : (t, halfZero) ∈ circleCollarSource := by
  change (0 : ℝ) < 1
  norm_num

theorem planarCollar_zero_val {k : ℕ} (hk : k = 2 ∨ k = 3) (j : Fin k) (t : Circle) :
    (planarCollar.{u} k hk j (t, halfZero)).val.down = planarCircleMap k j t := by
  rw [planarCollar_apply_val hk j (halfZero_mem_circleCollarSource t)]
  change planarCollarFormula k j ((t : ℂ), 0) = _
  simp [planarCollarFormula, planarCircleMap, planarTwist, Complex.real_smul]

theorem planarCollar_disjoint {k : ℕ} (hk : k = 2 ∨ k = 3) :
    Pairwise fun i j =>
      Disjoint (planarCollar.{u} k hk i).target (planarCollar.{u} k hk j).target := by
  intro i j hij
  rw [Set.disjoint_left]
  intro x hi hj
  change planarSign i * (‖x.val.down - planarCenter k i‖ - planarRadius i) < 1 / 4 at hi
  change planarSign j * (‖x.val.down - planarCenter k j‖ - planarRadius j) < 1 / 4 at hj
  have hz := (mem_planarSet_iff hk x.val).mp x.2
  have hi0 := planarSign_mul_nonneg i hz
  have hj0 := planarSign_mul_nonneg j hz
  set z := x.val.down
  have key : ∀ a b : Fin k, a.val = 0 → b.val ≠ 0 →
      planarSign a * (‖z - planarCenter k a‖ - planarRadius a) < 1 / 4 →
      planarSign b * (‖z - planarCenter k b‖ - planarRadius b) < 1 / 4 → False := by
    intro a b ha hb h1 h2
    simp only [planarSign, planarRadius, ha, hb, ↓reduceIte, planarCenter_zero ha,
      Complex.ofReal_zero, sub_zero, one_mul] at h1 h2
    have := (norm_sub_real_bounds z (planarCenter k b)).1
    have := abs_planarCenter_le k b
    linarith
  by_cases hi' : i.val = 0
  · by_cases hj' : j.val = 0
    · exact hij (Fin.ext (hi'.trans hj'.symm))
    · exact key i j hi' hj' hi hj
  · by_cases hj' : j.val = 0
    · exact key j i hj' hi' hj hi
    · simp only [planarSign, planarRadius, hi', hj', ↓reduceIte, one_mul] at hi hj
      have := two_le_abs_planarCenter_sub hk hi' hj' hij
      have := le_norm_sub_planarCenter z (planarCenter k i) (planarCenter k j)
      linarith

theorem planarSet_boundary_eq {k : ℕ} (hk : k = 2 ∨ k = 3) :
    (𝓡∂ 2).boundary (planarSet.{u} k) =
      ⋃ j, range fun t => planarCollar.{u} k hk j (t, halfZero) := by
  ext x
  change (𝓡∂ 2).IsBoundaryPoint x ↔ _
  rw [planarSet_isBoundaryPoint_iff,
    planarFunction_eq_zero_iff hk, mem_iUnion]
  constructor
  · rintro ⟨j, hj⟩
    refine ⟨j, unitOf (planarTwist j (x.val.down - planarCenter k j)), ?_⟩
    have hx : x ∈ (planarCollar.{u} k hk j).target := by
      change planarSign j * (‖x.val.down - planarCenter k j‖ - planarRadius j) < 1 / 4
      rw [hj, sub_self, mul_zero]
      norm_num
    have hinv := (planarCollar.{u} k hk j).right_inv' hx
    have h2 : (planarCollar.{u} k hk j).symm x =
        (unitOf (planarTwist j (x.val.down - planarCenter k j)), halfZero) := by
      change planarCollarInv k j x = _
      unfold planarCollarInv
      rw [hj, sub_self, mul_zero, mul_zero, ← halfPoint_eq_halfSpaceOneLift 0 le_rfl]
      rfl
    change (planarCollar.{u} k hk j) ((planarCollar.{u} k hk j).symm x) = x at hinv
    rw [h2] at hinv
    exact hinv
  · rintro ⟨j, t, rfl⟩
    refine ⟨j, ?_⟩
    rw [planarCollar_zero_val, norm_planarCircleMap_sub]

def planarBase (k : ℕ) (hk : k = 2 ∨ k = 3) : PlanarBase.{u} k where
  surface := planarSurface k hk
  collar := planarCollar k hk
  source_eq _ := rfl
  boundary_zero j t := by
    have h := (planarSet_boundary_eq.{u} hk).symm ▸
      (mem_iUnion.mpr ⟨j, t, rfl⟩ : planarCollar.{u} k hk j (t, halfZero) ∈
        ⋃ j, range fun t => planarCollar.{u} k hk j (t, halfZero))
    exact h
  disjoint := planarCollar_disjoint hk
  boundary_exhausted := planarSet_boundary_eq hk
  embedding x := x.val.down
  isSmoothEmbedding :=
    ⟨((planarAtlas.{u} k).isSmoothEmbedding_subtype_val.isImmersion.comp_diffeomorph
      (uliftDiffeomorph 𝓘(ℝ, ℂ) ℂ).symm),
    (Homeomorph.ulift : PlaneLift.{u} ≃ₜ ℂ).isEmbedding.comp
      _root_.Topology.IsEmbedding.subtypeVal⟩
  range_embedding := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact (mem_planarSet_iff hk x.val).mp x.2
    · intro hz
      exact ⟨⟨ULift.up z, (mem_planarSet_iff hk (ULift.up z)).mpr hz⟩, rfl⟩
  embedding_collar j t := planarCollar_zero_val.{u} hk j t

def annulusSurface : CompactSurface.{u} := planarSurface 2 (Or.inl rfl)

def annulusPlanarBase : PlanarBase.{u} 2 := planarBase 2 (Or.inl rfl)

def pantsSurface : CompactSurface.{u} := planarSurface 3 (Or.inr rfl)

def pantsPlanarBase : PlanarBase.{u} 3 := planarBase 3 (Or.inr rfl)


def planeOrientation : ManifoldOrientation 𝓘(ℝ, ℂ) ℂ 2 :=
  (Manifold.exists_manifoldOrientation_of_simply_connected (M := ℂ)
    Complex.finrank_real_complex).some

def planeCircleOrientation :
    ManifoldOrientation (𝓘(ℝ, ℂ).prod (𝓡 1)) (PlaneLift.{u} × Circle) 3 :=
  productOrientation 𝓘(ℝ, ℂ) (𝓡 1) (by norm_num) le_rfl
    (uliftOrientation 𝓘(ℝ, ℂ) ℂ planeOrientation) circleOrientation

def productSet (k : ℕ) : Set (PlaneLift.{u} × Circle) := {p | planarFunction k p.1.down ≤ 0}

theorem contMDiff_productFunction (k : ℕ) : ContMDiff (𝓘(ℝ, ℂ).prod (𝓡 1)) 𝓘(ℝ, ℝ) ∞
    (fun p : PlaneLift.{u} × Circle => planarFunction k p.1.down) :=
  (contMDiff_planarFunction_down k).comp contMDiff_fst

theorem productFunction_regular (k : ℕ) (p : PlaneLift.{u} × Circle)
    (hp : planarFunction k p.1.down = 0) :
    mfderiv (𝓘(ℝ, ℂ).prod (𝓡 1)) 𝓘(ℝ, ℝ)
      (fun p : PlaneLift.{u} × Circle => planarFunction k p.1.down) p ≠ 0 := by
  refine mfderiv_ne_zero_of_comp (J := 𝓘(ℝ, ℂ))
    (s := fun w : ℂ => ((ULift.up w : PlaneLift.{u}), p.2)) (y := p.1.down)
    ((contMDiff_productFunction k).mdifferentiableAt (by simp))
    ((contMDiff_planeLift_up.prodMk contMDiff_const).mdifferentiableAt (by simp)) ?_
  change mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) (planarFunction k) p.1.down ≠ 0
  rw [mfderiv_eq_fderiv]
  exact planarFunction_regular k hp

theorem finrank_planeCircleModel :
    Module.finrank ℝ (ℂ × EuclideanSpace ℝ (Fin 1)) = 2 + 1 := by
  rw [Module.finrank_prod, Complex.finrank_real_complex, finrank_euclideanSpace_fin]

def productAtlas (k : ℕ) : SmoothBoundaryAtlas (𝓘(ℝ, ℂ).prod (𝓡 1)) 3 (productSet.{u} k) :=
  SmoothBoundaryAtlas.regularSublevel (𝓘(ℝ, ℂ).prod (𝓡 1)) (n := 2) finrank_planeCircleModel
    (contMDiff_productFunction.{u} k) 0 (productFunction_regular k)

instance (k : ℕ) : ChartedSpace (EuclideanHalfSpace 3) (productSet.{u} k) :=
  (productAtlas k).toChartedSpace

instance (k : ℕ) : IsManifold (𝓡∂ 3) ∞ (productSet.{u} k) := (productAtlas k).isManifold

theorem productSet_isBoundaryPoint_iff (k : ℕ) (x : productSet.{u} k) :
    (𝓡∂ 3).IsBoundaryPoint x ↔ planarFunction k x.val.1.down = 0 :=
  SmoothBoundaryAtlas.regularSublevel_isBoundaryPoint_iff (𝓘(ℝ, ℂ).prod (𝓡 1)) (n := 2)
    finrank_planeCircleModel (contMDiff_productFunction k) 0 (productFunction_regular k) x

theorem productSet_eq_prod (k : ℕ) : productSet.{u} k = planarSet k ×ˢ univ := by
  ext p
  simp [productSet, planarSet]

theorem isCompact_planarSet {k : ℕ} (hk : k = 2 ∨ k = 3) : IsCompact (planarSet.{u} k) := by
  rw [planarSet_eq_preimage hk]
  exact Homeomorph.ulift.isCompact_preimage.mpr (isCompact_planarModel hk)

def productCarrier (k : ℕ) (hk : k = 2 ∨ k = 3) : CompactCarrier.{u} where
  kind := .withBoundary
  Carrier := productSet.{u} k
  charts := (inferInstance : ChartedSpace (EuclideanHalfSpace 3) (productSet.{u} k))
  smooth := (inferInstance : IsManifold (𝓡∂ 3) ∞ (productSet.{u} k))
  compact := isCompact_iff_compactSpace.mp (by
    rw [productSet_eq_prod]
    exact (isCompact_planarSet hk).prod isCompact_univ)
  orientation := (productAtlas k).orientation planeCircleOrientation

def productDiffeomorph (k : ℕ) :
    (planarSet.{u} k × Circle) ≃ₘ⟮(𝓡∂ 2).prod (𝓡 1), 𝓡∂ 3⟯ productSet.{u} k where
  toFun q := ⟨(q.1.val, q.2), q.1.2⟩
  invFun p := (⟨p.val.1, p.2⟩, p.val.2)
  left_inv _ := rfl
  right_inv _ := rfl
  contMDiff_toFun := ((productAtlas k).contMDiff_iff_subtype_val _).mpr
    (((planarAtlas k).contMDiff_subtype_val.comp contMDiff_fst).prodMk contMDiff_snd)
  contMDiff_invFun :=
    (((planarAtlas k).contMDiff_iff_subtype_val _).mpr
      (contMDiff_fst.comp (productAtlas k).contMDiff_subtype_val)).prodMk
      (contMDiff_snd.comp (productAtlas k).contMDiff_subtype_val)

theorem connectedSpace_planarSet {k : ℕ} (hk : k = 2 ∨ k = 3) :
    ConnectedSpace (planarSet.{u} k) :=
  (planarSurface.{u} k hk).connected

theorem connectedSpace_productSet {k : ℕ} (hk : k = 2 ∨ k = 3) :
    ConnectedSpace (productSet.{u} k) := by
  have := connectedSpace_planarSet.{u} hk
  exact (productDiffeomorph.{u} k).toHomeomorph.connectedSpace_iff.mp inferInstance

theorem connectedSpace_pieceInterior_top (C : CompactCarrier.{u}) [ConnectedSpace C.Carrier] :
    ConnectedSpace (C.pieceInterior ⊤) := by
  have h : ((C.pieceInterior ⊤ : TopologicalSpace.Opens C.Carrier) : Set C.Carrier) =
      C.model.interior C.Carrier := by
    ext x
    exact ⟨fun hx => hx.2, fun hx => ⟨trivial, hx⟩⟩
  refine isConnected_iff_connectedSpace.mp ?_
  rw [h]
  exact ⟨Manifold.dense_manifold_interior.nonempty, Manifold.isPreconnected_manifold_interior⟩


def productCollarMap (k : ℕ) (hk : k = 2 ∨ k = 3) (j : Fin k)
    (p : Torus × EuclideanHalfSpace 1) : productSet.{u} k :=
  productDiffeomorph k (planarCollar k hk j (p.1.1, p.2), p.1.2)

def productCollarInv (k : ℕ) (hk : k = 2 ∨ k = 3) (j : Fin k) (x : productSet.{u} k) :
    Torus × EuclideanHalfSpace 1 :=
  ((((planarCollar k hk j).symm ((productDiffeomorph k).symm x).1).1,
    ((productDiffeomorph k).symm x).2),
    ((planarCollar k hk j).symm ((productDiffeomorph k).symm x).1).2)

def productCollar (k : ℕ) (hk : k = 2 ∨ k = 3) (j : Fin k) :
    PartialDiffeomorph halfCollarModel (𝓡∂ 3) (Torus × EuclideanHalfSpace 1)
      (productSet.{u} k) ∞ where
  toFun := productCollarMap k hk j
  invFun := productCollarInv k hk j
  source := halfCollarSource
  target := {x | ((productDiffeomorph.{u} k).symm x).1 ∈ (planarCollar.{u} k hk j).target}
  map_source' p hp := (planarCollar.{u} k hk j).map_source' hp
  map_target' x hx := (planarCollar.{u} k hk j).map_target' hx
  left_inv' p hp := by
    have h : (planarCollar.{u} k hk j).symm (planarCollar.{u} k hk j (p.1.1, p.2)) =
        (p.1.1, p.2) := (planarCollar.{u} k hk j).left_inv hp
    change ((((planarCollar.{u} k hk j).symm (planarCollar.{u} k hk j (p.1.1, p.2))).1, p.1.2),
      ((planarCollar.{u} k hk j).symm (planarCollar.{u} k hk j (p.1.1, p.2))).2) = p
    rw [h]
  right_inv' x hx := by
    have h : planarCollar.{u} k hk j
        ((planarCollar.{u} k hk j).symm ((productDiffeomorph.{u} k).symm x).1) =
        ((productDiffeomorph.{u} k).symm x).1 := (planarCollar.{u} k hk j).right_inv hx
    change productDiffeomorph.{u} k (planarCollar.{u} k hk j
      ((planarCollar.{u} k hk j).symm ((productDiffeomorph.{u} k).symm x).1),
      ((productDiffeomorph.{u} k).symm x).2) = x
    rw [h]
    exact (productDiffeomorph.{u} k).apply_symm_apply x
  open_source := isOpen_lt
    ((EuclideanSpace.proj 0).continuous.comp (continuous_subtype_val.comp continuous_snd))
    continuous_const
  open_target := (planarCollar.{u} k hk j).open_target.preimage
    (continuous_fst.comp (productDiffeomorph.{u} k).symm.continuous)
  contMDiffOn_toFun := by
    have hr : ContMDiff halfCollarModel circleCollarModel ∞
        (fun p : Torus × EuclideanHalfSpace 1 => (p.1.1, p.2)) :=
      (contMDiff_fst.comp contMDiff_fst).prodMk contMDiff_snd
    exact (productDiffeomorph.{u} k).contMDiff.comp_contMDiffOn
      (((planarCollar.{u} k hk j).contMDiffOn.comp hr.contMDiffOn fun p hp => hp).prodMk
        (contMDiff_snd.comp contMDiff_fst).contMDiffOn)
  contMDiffOn_invFun := by
    have hg : ContMDiffOn (𝓡∂ 3) circleCollarModel ∞
        (fun x => (planarCollar.{u} k hk j).symm ((productDiffeomorph.{u} k).symm x).1)
        {x | ((productDiffeomorph.{u} k).symm x).1 ∈ (planarCollar.{u} k hk j).target} :=
      (planarCollar.{u} k hk j).contMDiffOn_invFun.comp
        (contMDiff_fst.comp (productDiffeomorph.{u} k).symm.contMDiff).contMDiffOn fun x hx => hx
    exact ((contMDiff_fst.comp_contMDiffOn hg).prodMk
      (contMDiff_snd.comp (productDiffeomorph.{u} k).symm.contMDiff).contMDiffOn).prodMk
      (contMDiff_snd.comp_contMDiffOn hg)

theorem productCollar_apply (k : ℕ) (hk : k = 2 ∨ k = 3) (j : Fin k)
    (p : Torus × EuclideanHalfSpace 1) :
    productCollar.{u} k hk j p = productDiffeomorph k (planarCollar k hk j (p.1.1, p.2), p.1.2) :=
  rfl

def productBoundaryTori (k : ℕ) (hk : k = 2 ∨ k = 3) :
    BoundaryTori (productCarrier.{u} k hk) k where
  collar := productCollar k hk
  source_eq _ := rfl
  boundary_zero j t := by
    change (𝓡∂ 3).IsBoundaryPoint (productCollar.{u} k hk j (t, halfZero))
    rw [productSet_isBoundaryPoint_iff]
    exact (planarSet_isBoundaryPoint_iff k _).mp ((planarBase.{u} k hk).boundary_zero j t.1)
  disjoint i j hij := Disjoint.preimage _ (planarCollar_disjoint hk hij)

theorem productBoundary_eq (k : ℕ) (hk : k = 2 ∨ k = 3) :
    (𝓡∂ 3).boundary (productSet.{u} k) = (productBoundaryTori.{u} k hk).image := by
  ext x
  change (𝓡∂ 3).IsBoundaryPoint x ↔ _
  rw [productSet_isBoundaryPoint_iff]
  constructor
  · intro hx
    have hb : ((productDiffeomorph.{u} k).symm x).1 ∈ (𝓡∂ 2).boundary (planarSet.{u} k) :=
      (planarSet_isBoundaryPoint_iff k _).mpr hx
    rw [planarSet_boundary_eq hk] at hb
    obtain ⟨j, t, ht⟩ := mem_iUnion.mp hb
    dsimp only at ht
    refine mem_iUnion.mpr ⟨j, (t, x.val.2), ?_⟩
    change productDiffeomorph.{u} k (planarCollar.{u} k hk j (t, halfZero), x.val.2) = x
    rw [ht]
    exact (productDiffeomorph.{u} k).apply_symm_apply x
  · intro hx
    obtain ⟨j, t, rfl⟩ := mem_iUnion.mp hx
    exact (productSet_isBoundaryPoint_iff k _).mp ((productBoundaryTori.{u} k hk).boundary_zero j t)


def productComponents (k : ℕ) (hk : k = 2 ∨ k = 3) : (productCarrier.{u} k hk).Components :=
  @singleComponents _ (connectedSpace_productSet hk)
    (@connectedSpace_pieceInterior_top _ (connectedSpace_productSet hk))

def productPresentation (k : ℕ) (hk : k = 2 ∨ k = 3) :
    TorusPresentation (productCarrier.{u} k hk) where
  cutCarrier := productCarrier k hk
  components := productComponents k hk
  pairing := emptyTorusPairing _
  externalCount := k
  external := productBoundaryTori k hk
  cutExternal := productBoundaryTori k hk
  external_exhausted := productBoundary_eq k hk
  cut_boundary_exhausted := by
    rw [iUnion_block_emptyTorusPairing, Set.empty_union]
    exact productBoundary_eq k hk
  external_disjoint := by
    rw [iUnion_block_emptyTorusPairing]
    exact Set.empty_disjoint _
  reconstruction := emptyTorusPairingHomeomorph _
  quotient_smooth := contMDiff_id
  quotient_oriented x := by
    refine ⟨LinearEquiv.refl ℝ _, fun v => ?_, ?_⟩
    · change v = mfderiv _ _ (id : (productCarrier.{u} k hk).Carrier → _) x v
      rw [mfderiv_id]
      rfl
    · change Orientation.map (Fin 3) (LinearEquiv.refl ℝ (TangentSpace _ x))
          ((productCarrier.{u} k hk).orientation.orientation x) =
        (productCarrier.{u} k hk).orientation.orientation x
      rw [Orientation.map_refl]
      rfl
  interiorImage := (productCarrier k hk).interior
  interiorDiffeomorph := Diffeomorph.refl _ _ _
  interior_map _ := rfl
  seam m := m.elim0
  seam_source m := m.elim0
  seam_zero m := m.elim0
  seam_positive m := m.elim0
  seam_negative m := m.elim0
  seam_interior m := m.elim0
  seam_disjoint m := m.elim0
  marked_collar _ _ _ := rfl
  external_seam_disjoint _ m := m.elim0
  leftPiece m := m.elim0
  rightPiece m := m.elim0
  left_owned m := m.elim0
  right_owned m := m.elim0
  externalPiece _ := ⟨0, Nat.one_pos⟩
  external_owned _ := Set.subset_univ _

def productPort (k : ℕ) (hk : k = 2 ∨ k = 3) :
    Fin k ≃ (productPresentation.{u} k hk).OwnedSide ⟨0, Nat.one_pos⟩ where
  toFun j := ⟨.inr (.inr j), rfl⟩
  invFun s := match s with
    | ⟨.inl m, _⟩ => m.elim0
    | ⟨.inr (.inl m), _⟩ => m.elim0
    | ⟨.inr (.inr j), _⟩ => j
  left_inv _ := rfl
  right_inv s := by
    rcases s with ⟨m | m | j, h⟩
    · exact m.elim0
    · exact m.elim0
    · rfl

def productTrivialization (k : ℕ) :
    (planarSet.{u} k × Circle) ≃ₘ⟮(𝓡∂ 2).prod (𝓡 1), 𝓡∂ 3⟯
      (⊤ : TopologicalSpace.Opens (productSet.{u} k)) :=
  (productDiffeomorph k).trans (topOpensDiffeomorph (I := 𝓡∂ 3) (productSet.{u} k)).symm

def productFibredPiece (k : ℕ) (hk : k = 2 ∨ k = 3) :
    ProductFibredPiece (productPresentation.{u} k hk) ⟨0, Nat.one_pos⟩ k where
  base := planarBase k hk
  port := productPort k hk
  trivialization := productTrivialization k
  collar_eq j p hp := by
    apply Subtype.ext
    rw [TorusPresentation.pieceCollar_apply _ _ _ hp]
    rfl

def annulusCircleCarrier : CompactCarrier.{u} := productCarrier 2 (Or.inl rfl)

def annulusCirclePresentation : TorusPresentation annulusCircleCarrier.{u} :=
  productPresentation 2 (Or.inl rfl)

def annulusCirclePiece :
    ProductFibredPiece annulusCirclePresentation.{u} ⟨0, Nat.one_pos⟩ 2 :=
  productFibredPiece 2 (Or.inl rfl)

def singlePieceEquiv : Option (Fin t2IntervalData.fillingCount) ≃ Fin 1 where
  toFun _ := ⟨0, Nat.one_pos⟩
  invFun _ := none
  left_inv o := by
    rcases o with _ | m
    · rfl
    · exact m.elim0
  right_inv _ := Subsingleton.elim _ _

def freePortEquiv : Fin t2IntervalData.ports ⊕ Fin t2IntervalData.fillingCount ≃ Fin 2 where
  toFun := Sum.elim id fun m => m.elim0
  invFun := Sum.inl
  left_inv o := by
    rcases o with r | m
    · rfl
    · exact m.elim0
  right_inv _ := rfl

def annulusCircleBlock : T2Interval annulusCircleCarrier.{u} where
  presentation := annulusCirclePresentation
  piece := singlePieceEquiv
  product := annulusCirclePiece
  solid m := m.elim0
  port := freePortEquiv
  seam := Equiv.refl _
  free := Equiv.refl _
  free_port _ := rfl
  filled_port m := m.elim0
  solid_port m := m.elim0
  slope m := m.elim0

theorem annulusCircleBlock_isGoodBlock : annulusCircleBlock.{u}.IsGoodBlock :=
  t2Interval_isGoodBlock _

end GC.Seifert
