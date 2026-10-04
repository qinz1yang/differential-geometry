import DifferentialGeometry.Geometry.Collapse.BoundaryScale.FirstScaleGeneral
import DifferentialGeometry.Geometry.Collapse.CutPieceBalls

/-!
# Boundary counterexamples give uniform small-scale data (BSA04, BSA05, BSA06.a, BCP04.a kernels)

Blueprint 207B, BSA04 (`B:7838`), the collar clause of BSA05 (`B:7915`), BSA06.a (`B:7979`) and
BCP04.a (`B:8443`). The objects are the ACTUAL curvature scale `R_p = curvatureRadius g p`, first
volume scale `r_p(w) = firstVolumeScale g p w` and boundary distance `distanceToBoundary W g p` of a
compact manifold, possibly with boundary. The near-boundary input of BSA04 is the output of BSA01
(`R_p ≥ 1` and `vol B(p, a) ≤ C₀ δ² a` for `a ≤ 1` where `d(p, ∂W) ≤ 10`), taken as a hypothesis;
its proof from the collar geometry is a separate row. Away from the boundary the tree's static
hypothesis `boundaryVolumeCollapsed` is used verbatim.
* BSA04.a: `2 n r_p(1/n) < R_p` at EVERY point, for `n ≥ 3`, `δ ≤ 1/(16 n⁴)`, `C₀ = 1000`.
* BSA04.c: the whole-ball derivative bounds on `B(p, C r_p(w))`, `C < n`, `1/n ≤ w`, with the
  constant `A'(C, w) = max_k A(D⁻³ w) D^{-k-2}`, `D = max 1 C` (`boundaryDerivativeConstant`).
  No attainment premise: a zero scale makes the ball empty, a positive one is attained from below.
* BSA05, collar clause: `vol B(p, a) ≤ c a` with `c < w' a²` gives `r_p(w') < a`.
* BSA06.a and BCP04.a: `n/2 < d/ρ` (for `d > 10`) and `n d/(d+3) < d/ρ`, and the resulting
  interior containment of the scaled balls.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry DifferentialGeometry.Geometry.Riemannian GC.Endpoint
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.Geometry.Collapse

universe u

section General

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

/-- BSA04.a away from the boundary: volume collapse at the curvature scale with `δ ≤ 1/(16 n⁴)`
gives `2 n r_p(1/n) < R_p` (also when `R_p = ∞`). -/
theorem ofReal_two_mul_firstVolumeScale_lt_of_collapsed (g : SmoothRiemannianMetric I M)
    (p : M) {n δ : ℝ} (hn : 1 ≤ n) (hδn : δ * (16 * n ^ 4) ≤ 1)
    (hcol : volumeCollapsedAtCurvatureScale g δ p) :
    ENNReal.ofReal (2 * n * firstVolumeScale g p n⁻¹) < curvatureRadius g p := by
  by_cases htop : curvatureRadius g p = ⊤
  · rw [htop]
    exact ENNReal.ofReal_lt_top
  have hnpos : 0 < n := zero_lt_one.trans_le hn
  set R := (curvatureRadius g p).toReal with hRdef
  have hRpos : 0 < R := ENNReal.toReal_pos (curvatureRadius_pos g p).ne' htop
  have hReq : curvatureRadius g p = ENNReal.ofReal R := (ENNReal.ofReal_toReal htop).symm
  have hvolR := hcol R hRpos hReq
  set s := 2 * R / (5 * n) with hsdef
  have hs : 0 < s := by positivity
  have hsR : s ≤ R := by
    rw [hsdef, div_le_iff₀ (by positivity)]
    nlinarith
  have hn4 : 0 < n ^ 4 := by positivity
  have hkey : δ * R ^ 3 ≤ n⁻¹ * s ^ 3 := by
    have hs3 : n⁻¹ * s ^ 3 = 8 / 125 * R ^ 3 * (n ^ 4)⁻¹ := by
      rw [hsdef]
      field_simp
      ring
    have hδ' : δ * n ^ 4 ≤ 1 / 16 := by linarith
    rw [hs3]
    calc δ * R ^ 3 = (δ * n ^ 4) * R ^ 3 * (n ^ 4)⁻¹ := by field_simp
      _ ≤ 1 / 16 * R ^ 3 * (n ^ 4)⁻¹ := by gcongr
      _ ≤ 8 / 125 * R ^ 3 * (n ^ 4)⁻¹ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by norm_num) (by positivity))
          (by positivity)
  have hvol_s : (ballVolume g p s).toReal ≤ n⁻¹ * s ^ 3 := by
    have h1 := ENNReal.toReal_mono ENNReal.ofReal_ne_top
      ((ballVolume_monotone g p hsR).trans hvolR)
    rw [ENNReal.toReal_ofReal'] at h1
    exact h1.trans (max_le hkey (by positivity))
  have hle := firstVolumeScale_le_of_ballVolume_toReal_le g p hs hvol_s
  rw [hReq]
  apply (ENNReal.ofReal_lt_ofReal_iff hRpos).mpr
  have h2s : 2 * n * s = 4 / 5 * R := by
    rw [hsdef]
    field_simp
    ring
  nlinarith

omit [CompleteSpace E] in
/-- BSA04.a near the boundary: `R_p ≥ 1` and `vol B(p, a) ≤ C₀ δ² a` for `a ≤ 1`, with
`16 C₀ δ² n³ ≤ 1`, give `2 n r_p(1/n) < R_p`. -/
theorem ofReal_two_mul_firstVolumeScale_lt_of_small_volume (g : SmoothRiemannianMetric I M)
    (p : M) {n δ C₀ : ℝ} (hn : 1 ≤ n) (hkey : 16 * C₀ * δ ^ 2 * n ^ 3 ≤ 1)
    (hR : 1 ≤ curvatureRadius g p)
    (hvol : ∀ a : ℝ, 0 < a → a ≤ 1 → ballVolume g p a ≤ ENNReal.ofReal (C₀ * δ ^ 2 * a)) :
    ENNReal.ofReal (2 * n * firstVolumeScale g p n⁻¹) < curvatureRadius g p := by
  have hnpos : 0 < n := zero_lt_one.trans_le hn
  set s := (4 * n)⁻¹ with hsdef
  have hs : 0 < s := by positivity
  have hs1 : s ≤ 1 := by
    rw [hsdef]
    exact inv_le_one_of_one_le₀ (by linarith)
  have hbound : C₀ * δ ^ 2 * s ≤ n⁻¹ * s ^ 3 := by
    have hn3 : 0 < n ^ 3 := by positivity
    have hC : C₀ * δ ^ 2 ≤ 1 / (16 * n ^ 3) := by
      rw [le_div_iff₀ (by positivity)]
      calc C₀ * δ ^ 2 * (16 * n ^ 3) = 16 * C₀ * δ ^ 2 * n ^ 3 := by ring
        _ ≤ 1 := hkey
    have hs3 : n⁻¹ * s ^ 3 = 1 / (16 * n ^ 3) * s := by
      rw [hsdef]
      field_simp
      ring
    rw [hs3]
    exact mul_le_mul_of_nonneg_right hC hs.le
  have hvol_s : (ballVolume g p s).toReal ≤ n⁻¹ * s ^ 3 := by
    have h1 := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hvol s hs hs1)
    rw [ENNReal.toReal_ofReal'] at h1
    exact h1.trans (max_le hbound (by positivity))
  have hle := firstVolumeScale_le_of_ballVolume_toReal_le g p hs hvol_s
  have h2 : 2 * n * firstVolumeScale g p n⁻¹ < 1 := by
    have h2s : 2 * n * s = 1 / 2 := by
      rw [hsdef]
      field_simp
      ring
    nlinarith
  calc ENNReal.ofReal (2 * n * firstVolumeScale g p n⁻¹) < ENNReal.ofReal 1 :=
        (ENNReal.ofReal_lt_ofReal_iff one_pos).mpr h2
    _ = 1 := ENNReal.ofReal_one
    _ ≤ curvatureRadius g p := hR

/-- The constant `A'(C, w) = max_{k ≤ K} A(D⁻³ w) D^{-k-2}`, `D = max 1 C`, of BSA04.b, defined
once. -/
def boundaryDerivativeConstant (A : ℝ → ℝ) (K : ℕ) (C w : ℝ) : ℝ :=
  (Finset.range (K + 1)).sup' Finset.nonempty_range_add_one
    fun k => A (((max 1 C) ^ 3)⁻¹ * w) * ((max 1 C) ^ (k + 2))⁻¹

/-- BSA04.c: along the standing inequality `2 n r_p(1/n) < R_p`, the static whole-ball derivative
hypothesis gives the derivative bounds on `B(p, C r_p(w))` for `C < n` and `1/n ≤ w`, with the
constant `A'(C, w)`. A nonpositive `C` or a zero scale give an empty ball. -/
theorem curvatureDerivativeNorm_le_on_firstVolumeScale_ball [CompactSpace M]
    (g : SmoothRiemannianMetric I M) {K : ℕ} {A : ℝ → ℝ} {δ n : ℝ}
    (hderiv : curvatureDerivativesControlled g K A δ) (hn : 1 < n) (hδn : δ * n ^ 4 ≤ 1)
    {p : M} (hstand : ENNReal.ofReal (2 * n * firstVolumeScale g p n⁻¹) < curvatureRadius g p)
    {C w : ℝ} (hCn : C < n) (hwn : n⁻¹ ≤ w) (hwc : w < euclideanThreeUnitBallVolume) :
    ∀ k ≤ K, ∀ q ∈ riemannianBallOf g p (C * firstVolumeScale g p w),
      curvatureDerivativeNorm g k q ≤
        boundaryDerivativeConstant A K C w * (firstVolumeScale g p w ^ (k + 2))⁻¹ := by
  intro k hk q hq
  set r := firstVolumeScale g p w with hrdef
  set D := max 1 C with hDdef
  have hnpos : 0 < n := zero_lt_one.trans hn
  rcases (firstVolumeScale_nonneg g p w).eq_or_lt with hr | hrpos
  · exfalso
    have hq' : riemannianEDistOf g p q < ENNReal.ofReal (C * r) := hq
    rw [← hrdef] at hr
    rw [← hr, mul_zero, ENNReal.ofReal_zero] at hq'
    exact ENNReal.not_lt_zero hq'
  have hD1 : 1 ≤ D := le_max_left _ _
  have hDn : D < n := max_lt hn hCn
  have hDpos : 0 < D := zero_lt_one.trans_le hD1
  have hw : 0 < w := (inv_pos.mpr hnpos).trans_le hwn
  have hrle : r ≤ firstVolumeScale g p n⁻¹ :=
    firstVolumeScale_anti_of_le g p (inv_pos.mpr hnpos) hwn
  have hDr : D * r < 2 * n * firstVolumeScale g p n⁻¹ := by nlinarith
  have hscale : ENNReal.ofReal (D * r) < curvatureRadius g p :=
    (ENNReal.ofReal_le_ofReal hDr.le).trans_lt hstand
  have hD3 : 0 < D ^ 3 := by positivity
  have hthr : δ ≤ (D ^ 3)⁻¹ * w := by
    have hn4 : 0 < n ^ 4 := by positivity
    have h1 : δ ≤ 1 / n ^ 4 := (le_div_iff₀ hn4).mpr hδn
    have h2 : 1 / n ^ 4 = (n ^ 3)⁻¹ * n⁻¹ := by field_simp
    rw [h2] at h1
    exact h1.trans (mul_le_mul (inv_anti₀ hD3 (pow_le_pow_left₀ hDpos.le hDn.le 3)) hwn
      (inv_pos.mpr hnpos).le (by positivity))
  have hwc' : (D ^ 3)⁻¹ * w < euclideanThreeUnitBallVolume :=
    (mul_le_of_le_one_left hw.le (inv_le_one_of_one_le₀ (one_le_pow₀ hD1))).trans_lt hwc
  have hvol : ENNReal.ofReal ((D ^ 3)⁻¹ * w * (D * r) ^ 3) ≤ ballVolume g p (D * r) := by
    have he : (D ^ 3)⁻¹ * w * (D * r) ^ 3 = w * r ^ 3 := by field_simp
    rw [he]
    calc ENNReal.ofReal (w * r ^ 3) ≤ ENNReal.ofReal (ballVolume g p r).toReal :=
          ENNReal.ofReal_le_ofReal (le_ballVolume_toReal_firstVolumeScale_of_pos g p hrpos)
      _ = ballVolume g p r := ENNReal.ofReal_toReal (ballVolume_ne_top g p r)
      _ ≤ ballVolume g p (D * r) := ballVolume_monotone g p (le_mul_of_one_le_left hrpos.le hD1)
  have hCD : C * r ≤ D * r := mul_le_mul_of_nonneg_right (le_max_right 1 C) hrpos.le
  have hb := hderiv p ((D ^ 3)⁻¹ * w) (D * r) hthr hwc' (by positivity) hscale hvol k hk q
    (riemannianBallOf_mono g p hCD hq)
  have hmem : k ∈ Finset.range (K + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hk)
  calc curvatureDerivativeNorm g k q ≤ A ((D ^ 3)⁻¹ * w) * ((D * r) ^ (k + 2))⁻¹ := hb
    _ = A ((D ^ 3)⁻¹ * w) * (D ^ (k + 2))⁻¹ * (r ^ (k + 2))⁻¹ := by
      rw [mul_pow, mul_inv]
      ring
    _ ≤ boundaryDerivativeConstant A K C w * (r ^ (k + 2))⁻¹ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact Finset.le_sup' (fun j => A (((max 1 C) ^ 3)⁻¹ * w) * ((max 1 C) ^ (j + 2))⁻¹) hmem

omit [CompleteSpace E] in
/-- BSA05, collar clause: `vol B(p, a) ≤ c a` with `c < w' a²` forces `r_p(w') < a`. -/
theorem firstVolumeScale_lt_of_ballVolume_le_linear [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (p : M) {a c w' : ℝ} (ha : 0 < a) (hw' : 0 < w')
    (hvol : ballVolume g p a ≤ ENNReal.ofReal (c * a)) (hc : c < w' * a ^ 2) :
    firstVolumeScale g p w' < a := by
  have hV : (ballVolume g p a).toReal < w' * a ^ 3 := by
    have h1 := ENNReal.toReal_mono ENNReal.ofReal_ne_top hvol
    rw [ENNReal.toReal_ofReal'] at h1
    refine h1.trans_lt (max_lt ?_ (by positivity))
    have : c * a < w' * a ^ 2 * a := mul_lt_mul_of_pos_right hc ha
    linarith [show w' * a ^ 2 * a = w' * a ^ 3 by ring]
  have hev : ∀ᶠ t in 𝓝 a, (ballVolume g p a).toReal < w' * t ^ 3 :=
    continuousAt_const.eventually_lt (by fun_prop) hV
  obtain ⟨t, hlt, ht⟩ :=
    ((hev.filter_mono nhdsWithin_le_nhds).and (Ioo_mem_nhdsLT ha)).exists
  have hvt : (ballVolume g p t).toReal ≤ w' * t ^ 3 :=
    ((ballVolume_toReal_monotone g p ht.2.le)).trans hlt.le
  exact (firstVolumeScale_le_of_ballVolume_toReal_le g p ht.1 hvt).trans_lt ht.2

end General

/-! ### Real-variable forms of BSA06.a and BCP04.a -/

/-- BSA06.a: `R ≤ d + 3`, `2 n u < R`, `0 < ρ ≤ 2 u` and `d > 10` give `n/2 < d/ρ`. -/
theorem half_lt_distance_div_scale {n u ρ R d : ℝ} (hd : 10 < d) (hR : R ≤ d + 3)
    (hstand : 2 * n * u < R) (hρ : 0 < ρ) (hρu : ρ ≤ 2 * u) : n / 2 < d / ρ := by
  rw [lt_div_iff₀ hρ]
  rcases le_or_gt 0 n with hn | hn
  · nlinarith
  · nlinarith

/-- BCP04.a: `R ≤ d + 3`, `2 n u < R`, `0 < ρ ≤ 2 u` and `d > 0` give `n d/(d + 3) < d/ρ`. -/
theorem mul_div_add_three_lt_distance_div_scale {n u ρ R d : ℝ} (hd : 0 < d)
    (hR : R ≤ d + 3) (hstand : 2 * n * u < R) (hρ : 0 < ρ) (hρu : ρ ≤ 2 * u) :
    n * d / (d + 3) < d / ρ := by
  have hnρ : n * ρ < d + 3 := by
    rcases le_or_gt 0 n with hn | hn
    · nlinarith
    · nlinarith
  rw [div_lt_div_iff₀ (by linarith) hρ]
  nlinarith

/-- BCP04.a for `d > 5`: the ratio exceeds `5n/8`. -/
theorem five_mul_div_eight_lt_distance_div_scale {n u ρ R d : ℝ} (hn : 0 ≤ n) (hd : 5 < d)
    (hR : R ≤ d + 3) (hstand : 2 * n * u < R) (hρ : 0 < ρ) (hρu : ρ ≤ 2 * u) :
    5 * n / 8 < d / ρ := by
  refine lt_of_le_of_lt ?_
    (mul_div_add_three_lt_distance_div_scale (by linarith) hR hstand hρ hρu)
  rw [div_le_div_iff₀ (by norm_num) (by linarith)]
  nlinarith

/-! ### The carrier forms -/

section Carrier

variable (W : CompactCarrier.{u}) (g : SmoothRiemannianMetric W.model W.Carrier)

/-- BSA04.a on a compact carrier with boundary: the static volume collapse beyond distance `10`
and BSA01's near-boundary output (`R_p ≥ 1`, `vol B(p, a) ≤ 1000 δ² a` for `a ≤ 1`) give
`2 n r_p(1/n) < R_p` at EVERY point, for `n ≥ 3` and `0 ≤ δ ≤ 1/(16 n⁴)`. -/
theorem ofReal_two_mul_firstVolumeScale_lt_curvatureRadius_of_boundary_data
    {n δ : ℝ} (hn : 3 ≤ n) (hδ : 0 ≤ δ) (hδn : δ * (16 * n ^ 4) ≤ 1)
    (hcoll : boundaryVolumeCollapsed W g δ)
    (hnear : ∀ p, distanceToBoundary W g p ≤ ENNReal.ofReal 10 →
      1 ≤ curvatureRadius g p ∧ ∀ a : ℝ, 0 < a → a ≤ 1 →
        ballVolume g p a ≤ ENNReal.ofReal (1000 * δ ^ 2 * a))
    (p : W.Carrier) :
    ENNReal.ofReal (2 * n * firstVolumeScale g p n⁻¹) < curvatureRadius g p := by
  rcases le_or_gt (distanceToBoundary W g p) (ENNReal.ofReal 10) with hd | hd
  · obtain ⟨hR, hvol⟩ := hnear p hd
    refine ofReal_two_mul_firstVolumeScale_lt_of_small_volume g p (by linarith) ?_ hR hvol
    have hδ' : δ * n ^ 4 ≤ 1 / 16 := by linarith
    have h1 : (δ * n ^ 4) ^ 2 ≤ (1 / 16) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hδ' 2
    have h2 : (243 : ℝ) ≤ n ^ 5 := by
      have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hn 5
      norm_num at h
      linarith
    have hX : 0 ≤ 16 * 1000 * δ ^ 2 * n ^ 3 := by positivity
    have hX5 : 16 * 1000 * δ ^ 2 * n ^ 3 * n ^ 5 = 16000 * (δ * n ^ 4) ^ 2 := by ring
    nlinarith
  · have hcol := hcoll p (by simpa only [boundaryBufferDistance] using hd)
    exact ofReal_two_mul_firstVolumeScale_lt_of_collapsed g p (by linarith) hδn hcol

/-- BSA06 interior exhaustion: at a center with `d(p, ∂W) > 10`, BSA01.c (`R_p ≤ d + 3`) and the
standing inequality `2 n u < R_p`, every scaled ball `B(p, B ρ)` with `0 < ρ ≤ 2u` and `B ≤ n/2`
lies in the manifold interior. -/
theorem riemannianBallOf_scaled_subset_interior {p : W.Carrier} {n u ρ B : ℝ}
    (hd : ENNReal.ofReal 10 < distanceToBoundary W g p)
    (hR : curvatureRadius g p ≤ distanceToBoundary W g p + ENNReal.ofReal 3)
    (hstand : ENNReal.ofReal (2 * n * u) < curvatureRadius g p)
    (hρ : 0 < ρ) (hρu : ρ ≤ 2 * u) (hB : B ≤ n / 2) :
    riemannianBallOf g p (B * ρ) ⊆ W.model.interior W.Carrier := by
  apply riemannianBallOf_subset_interior W g
  by_cases htop : distanceToBoundary W g p = ⊤
  · rw [htop]
    exact le_top
  set D := (distanceToBoundary W g p).toReal with hDdef
  have hDeq : distanceToBoundary W g p = ENNReal.ofReal D := (ENNReal.ofReal_toReal htop).symm
  rw [hDeq] at hd hR ⊢
  have hD : 10 < D := (ENNReal.ofReal_lt_ofReal_iff'.mp hd).1
  rw [← ENNReal.ofReal_add (by linarith) (by norm_num)] at hR
  have h2nu : 2 * n * u < D + 3 :=
    (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mp (hstand.trans_le hR)
  have hratio := half_lt_distance_div_scale hD le_rfl h2nu hρ hρu
  rw [lt_div_iff₀ hρ] at hratio
  apply ENNReal.ofReal_le_ofReal
  nlinarith

end Carrier

end DifferentialGeometry.Geometry.Collapse
