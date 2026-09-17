import DifferentialGeometry.Topology.Planar.PolygonRounding
import DifferentialGeometry.External.Schoenflies.PolygonBridge
import DifferentialGeometry.Analysis.Calculus.SmoothMax
import DifferentialGeometry.Topology.Diffeomorph.Convex
import DifferentialGeometry.External.Schoenflies.PrePolygonSep
import DifferentialGeometry.External.ClassificationOfSurfaces.Moise.LineSubdivision
import DifferentialGeometry.Analysis.Convex.AffineBasis
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
import Mathlib.Analysis.Normed.Affine.AddTorsorBases

open Set Metric
open scoped ContDiff Manifold
open Schoenflies (Plane)
open LeanEval.Topology.ClassificationOfSurfaces.Moise
  (affineBasisOfTriangle triangleAffineEquiv triangleAffineEquiv_apply
    affineIndependent_plane_triple_of_det_ne_zero)

namespace DifferentialGeometry.Topology.Planar

noncomputable def roundedTriangleFunction (b : AffineBasis (Fin 3) ℝ Schoenflies.Plane)
    (ε : ℝ) (x : Schoenflies.Plane) : ℝ :=
  Real.smoothMax ε (Real.smoothMax ε (-(b.coord 0 x)) (-(b.coord 1 x))) (-(b.coord 2 x))

theorem convexOn_roundedTriangleFunction (b : AffineBasis (Fin 3) ℝ Schoenflies.Plane)
    {ε : ℝ} (hε : 0 < ε) : ConvexOn ℝ univ (roundedTriangleFunction b ε) := by
  have hc (i : Fin 3) : ConvexOn ℝ univ (fun x => -(b.coord i x)) := by
    convert! (convexOn_id convex_univ).comp_affineMap (-b.coord i) using 1
  exact Real.smoothMax.comp_convexOn hε (Real.smoothMax.comp_convexOn hε (hc 0) (hc 1)) (hc 2)

theorem contDiff_roundedTriangleFunction (b : AffineBasis (Fin 3) ℝ Schoenflies.Plane) (ε : ℝ) :
    ContDiff ℝ ∞ (roundedTriangleFunction b ε) := by
  have hc (i : Fin 3) : ContDiff ℝ ∞ (fun x => -(b.coord i x)) :=
    (⟨b.coord i, (b.coord i).continuous_of_finiteDimensional⟩ :
      Schoenflies.Plane →ᴬ[ℝ] ℝ).contDiff.neg
  exact (Real.smoothMax.contDiff ε).comp
    (((Real.smoothMax.contDiff ε).comp ((hc 0).prodMk (hc 1))).prodMk (hc 2))

theorem sublevel_roundedTriangleFunction_subset (b : AffineBasis (Fin 3) ℝ Schoenflies.Plane)
    {ε : ℝ} (hε : 0 < ε) :
    {x | roundedTriangleFunction b ε x ≤ 0} ⊆ convexHull ℝ (range b) := by
  intro x hx
  rw [b.convexHull_eq_nonneg_coord]
  have h01 : Real.smoothMax ε (-b.coord 0 x) (-b.coord 1 x) ≤ 0 :=
    (le_max_left _ _).trans ((Real.smoothMax.max_le hε _ _).trans hx)
  have h2 : -b.coord 2 x ≤ 0 :=
    (le_max_right _ _).trans ((Real.smoothMax.max_le hε _ _).trans hx)
  have h0 : -b.coord 0 x ≤ 0 := (le_max_left _ _).trans ((Real.smoothMax.max_le hε _ _).trans h01)
  have h1 : -b.coord 1 x ≤ 0 := (le_max_right _ _).trans ((Real.smoothMax.max_le hε _ _).trans h01)
  intro i
  fin_cases i
  · exact neg_nonpos.mp h0
  · exact neg_nonpos.mp h1
  · exact neg_nonpos.mp h2

theorem exists_diffeomorph_rounded_triangle (b : AffineBasis (Fin 3) ℝ Schoenflies.Plane)
    {ε : ℝ} (hε : 0 < ε) (hsmall : ε < 1 / 6) :
    ∃ D : Schoenflies.Plane ≃ₘ[ℝ] Schoenflies.Plane,
      D '' closedBall 0 1 = {x | roundedTriangleFunction b ε x ≤ 0} ∧
      D '' ball 0 1 = {x | roundedTriangleFunction b ε x < 0} ∧
      D '' sphere 0 1 = {x | roundedTriangleFunction b ε x = 0} := by
  let c := Finset.univ.centroid ℝ b
  have hc (i : Fin 3) : b.coord i c = 1 / 3 := by
    change b.coord i (Finset.univ.centroid ℝ b) = _
    rw [b.coord_apply_centroid (Finset.mem_univ i)]
    norm_num
  have hneg : roundedTriangleFunction b ε c < 0 := by
    unfold roundedTriangleFunction
    rw [hc 0, hc 1, hc 2]
    have h01 := Real.smoothMax.le_max_add hε (-(1 / 3)) (-(1 / 3))
    rw [max_self] at h01
    have hb := Real.smoothMax.le_max_add hε (Real.smoothMax ε (-(1 / 3)) (-(1 / 3))) (-(1 / 3))
    have hm : max (Real.smoothMax ε (-(1 / 3)) (-(1 / 3))) (-(1 / 3)) ≤ -(1 / 3) + ε :=
      max_le h01 (by linarith)
    linarith
  have hbounded := ((finite_range b).isCompact_convexHull ℝ).isBounded.subset
    (sublevel_roundedTriangleFunction_subset b hε)
  obtain ⟨D, _, _, hclosed, hopen, hboundary⟩ := Diffeomorph.exists_diffeomorph_convex_sublevel
    (convexOn_roundedTriangleFunction b hε) (contDiff_roundedTriangleFunction b ε) hbounded hneg
  exact ⟨D, hclosed, hopen, hboundary⟩

private theorem smoothMax_eq_left_of_add_le {ε x y : ℝ} (hε : 0 < ε)
    (h : y + ε ≤ x) : Real.smoothMax ε x y = x := by
  rw [Real.smoothMax.eq_max_of_le hε ((by linarith : ε ≤ x - y).trans (le_abs_self _))]
  exact max_eq_left (by linarith)

private theorem smoothMax_eq_right_of_add_le {ε x y : ℝ} (hε : 0 < ε)
    (h : x + ε ≤ y) : Real.smoothMax ε x y = y := by
  rw [Real.smoothMax.comm hε.ne']
  exact smoothMax_eq_left_of_add_le hε h

theorem roundedTriangleFunction_eq_of_coord_gap
    (b : AffineBasis (Fin 3) ℝ Schoenflies.Plane) {ε : ℝ} (hε : 0 < ε)
    (i : Fin 3) (x : Schoenflies.Plane)
    (hgap : ∀ j : Fin 3, j ≠ i → b.coord j x + ε ≤ b.coord i x) :
    roundedTriangleFunction b ε x =
      Real.smoothMax ε (-(b.coord (i + 1) x)) (-(b.coord (i + 2) x)) := by
  fin_cases i
  · change roundedTriangleFunction b ε x = Real.smoothMax ε (-b.coord 1 x) (-b.coord 2 x)
    have h1 : b.coord 1 x + ε ≤ b.coord 0 x := hgap 1 (by decide)
    unfold roundedTriangleFunction
    rw [smoothMax_eq_right_of_add_le hε (by linarith : -b.coord 0 x + ε ≤ -b.coord 1 x)]
  · change roundedTriangleFunction b ε x = Real.smoothMax ε (-b.coord 2 x) (-b.coord 0 x)
    have h0 : b.coord 0 x + ε ≤ b.coord 1 x := hgap 0 (by decide)
    unfold roundedTriangleFunction
    rw [smoothMax_eq_left_of_add_le hε (by linarith : -b.coord 1 x + ε ≤ -b.coord 0 x)]
    exact Real.smoothMax.comm hε.ne' _ _
  · change roundedTriangleFunction b ε x = Real.smoothMax ε (-b.coord 0 x) (-b.coord 1 x)
    have h0 : b.coord 0 x + ε ≤ b.coord 2 x := hgap 0 (by decide)
    apply smoothMax_eq_left_of_add_le hε
    have hm := (le_max_left (-b.coord 0 x) (-b.coord 1 x)).trans (Real.smoothMax.max_le hε _ _)
    linarith

theorem exists_triangle_vertex_chart (b : AffineBasis (Fin 3) ℝ Plane) (i : Fin 3) :
    ∃ e : Plane ≃ᵃ[ℝ] Plane, ∀ x,
      e x = Plane.mk (b.coord (i + 1) x - b.coord (i + 2) x) (b.coord (i + 1) x) := by
  let p : Fin 3 → Plane := ![b i, b (i + 2), b (i + 1)]
  let q : Fin 3 → Plane := ![Plane.mk 0 0, Plane.mk (-1) 0, Plane.mk 1 1]
  let t : Fin 3 ↪ Fin 3 := ⟨![i, i + 2, i + 1], by fin_cases i <;> decide⟩
  have hp : AffineIndependent ℝ p := by
    convert! b.ind.comp_embedding t using 1
    funext j
    fin_cases j <;> rfl
  have hq : AffineIndependent ℝ q := by
    apply affineIndependent_plane_triple_of_det_ne_zero
    norm_num [q, Plane.mk, PiLp.sub_apply]
  let e := triangleAffineEquiv p q hp hq
  let b' := affineBasisOfTriangle p hp
  have hx : (EuclideanSpace.proj 0).toAffineMap.comp e.toAffineMap =
      b.coord (i + 1) - b.coord (i + 2) := by
    apply AffineMap.ext_on b'.tot
    rintro x ⟨j, rfl⟩
    change (e (p j)) 0 = b.coord (i + 1) (p j) - b.coord (i + 2) (p j)
    rw [show e (p j) = q j from triangleAffineEquiv_apply p q hp hq j]
    fin_cases j <;> fin_cases i <;> norm_num [p, q, b.coord_apply, Plane.mk, Fin.ext_iff]
  have hy : (EuclideanSpace.proj 1).toAffineMap.comp e.toAffineMap = b.coord (i + 1) := by
    apply AffineMap.ext_on b'.tot
    rintro x ⟨j, rfl⟩
    change (e (p j)) 1 = b.coord (i + 1) (p j)
    rw [show e (p j) = q j from triangleAffineEquiv_apply p q hp hq j]
    fin_cases j <;> fin_cases i <;> norm_num [p, q, b.coord_apply, Plane.mk, Fin.ext_iff]
  refine ⟨e, fun x => ?_⟩
  ext k
  fin_cases k
  · exact congrArg (fun f : Plane →ᵃ[ℝ] ℝ => f x) hx
  · exact congrArg (fun f : Plane →ᵃ[ℝ] ℝ => f x) hy

private theorem triangle_coord_sum (b : AffineBasis (Fin 3) ℝ Plane) (i : Fin 3) (x : Plane) :
    b.coord i x + b.coord (i + 1) x + b.coord (i + 2) x = 1 := by
  have hs : b.coord 0 x + b.coord 1 x + b.coord 2 x = 1 := by
    simpa only [Fin.sum_univ_three] using b.sum_coord_apply_eq_one x
  fin_cases i
  · exact hs
  · change b.coord 1 x + b.coord 2 x + b.coord 0 x = 1
    linarith
  · change b.coord 2 x + b.coord 0 x + b.coord 1 x = 1
    linarith

private theorem triangle_chart_small_coords (b : AffineBasis (Fin 3) ℝ Plane)
    (i : Fin 3) (e : Plane ≃ᵃ[ℝ] Plane)
    (he : ∀ x, e x = Plane.mk (b.coord (i + 1) x - b.coord (i + 2) x) (b.coord (i + 1) x))
    {x : Plane} (hx : ‖e x‖ < 1 / 10) :
    7 / 10 < b.coord i x ∧ ∀ j : Fin 3, j ≠ i → |b.coord j x| < 1 / 5 := by
  have hX : |b.coord (i + 1) x - b.coord (i + 2) x| < 1 / 10 := by
    have h := lt_of_le_of_lt (PiLp.norm_apply_le (e x) 0) hx
    simpa [he, Plane.mk, Real.norm_eq_abs] using h
  have hY : |b.coord (i + 1) x| < 1 / 10 := by
    have h := lt_of_le_of_lt (PiLp.norm_apply_le (e x) 1) hx
    simpa [he, Plane.mk, Real.norm_eq_abs] using h
  have hp : |b.coord (i + 2) x| < 1 / 5 := by
    apply abs_lt.mpr
    obtain ⟨hXl, hXu⟩ := abs_lt.mp hX
    obtain ⟨hYl, hYu⟩ := abs_lt.mp hY
    constructor <;> linarith
  refine ⟨?_, ?_⟩
  · have hs := triangle_coord_sum b i x
    have hY' := (abs_lt.mp hY).2
    have hp' := (abs_lt.mp hp).2
    linarith
  · intro j hj
    have hc : j = i + 1 ∨ j = i + 2 := by
      fin_cases i <;> fin_cases j <;> simp_all [Fin.ext_iff]
    rcases hc with rfl | rfl
    · linarith
    · exact hp

private theorem triangle_chart_hull_iff (b : AffineBasis (Fin 3) ℝ Plane)
    (i : Fin 3) (e : Plane ≃ᵃ[ℝ] Plane)
    (he : ∀ x, e x = Plane.mk (b.coord (i + 1) x - b.coord (i + 2) x) (b.coord (i + 1) x))
    {x : Plane} (hx : ‖e x‖ < 1 / 10) :
    x ∈ convexHull ℝ (range b) ↔ 0 ≤ (e x) 1 - max ((e x) 0) 0 := by
  rw [b.convexHull_eq_nonneg_coord, he]
  change (∀ j, 0 ≤ b.coord j x) ↔
    0 ≤ b.coord (i + 1) x - max (b.coord (i + 1) x - b.coord (i + 2) x) 0
  rw [sub_nonneg, max_le_iff]
  have hs := (triangle_chart_small_coords b i e he hx).1
  constructor
  · intro h
    exact ⟨sub_le_self _ (h _), h _⟩
  · intro h j
    by_cases hj : j = i
    · subst j
      linarith
    · have hc : j = i + 1 ∨ j = i + 2 := by
        fin_cases i <;> fin_cases j <;> simp_all [Fin.ext_iff]
      rcases hc with rfl | rfl
      · exact h.2
      · linarith [h.1]

private theorem triangle_function_eq_chart (b : AffineBasis (Fin 3) ℝ Plane)
    (i : Fin 3) (e : Plane ≃ᵃ[ℝ] Plane)
    (he : ∀ x, e x = Plane.mk (b.coord (i + 1) x - b.coord (i + 2) x) (b.coord (i + 1) x))
    {x : Plane} (hx : ‖e x‖ < 1 / 10) :
    roundedTriangleFunction b (1 / 1000) x =
      Real.smoothMax (1 / 1000) ((e x) 0) 0 - (e x) 1 := by
  have hb := triangle_chart_small_coords b i e he hx
  have hgap (j : Fin 3) (hj : j ≠ i) : b.coord j x + 1 / 1000 ≤ b.coord i x := by
    have h := (abs_lt.mp (hb.2 j hj)).2
    linarith [hb.1]
  rw [roundedTriangleFunction_eq_of_coord_gap b (by norm_num) i x hgap, he]
  change Real.smoothMax (1 / 1000) (-b.coord (i + 1) x) (-b.coord (i + 2) x) =
    Real.smoothMax (1 / 1000) (b.coord (i + 1) x - b.coord (i + 2) x) 0 - b.coord (i + 1) x
  rw [Real.smoothMax.comm (by norm_num : (1 / 1000 : ℝ) ≠ 0)]
  have ht := Real.smoothMax.add_right (1 / 1000)
    (b.coord (i + 1) x - b.coord (i + 2) x) 0 (-b.coord (i + 1) x)
  convert! ht using 1
  ring_nf

private theorem triangle_chart_small_of_two_small (b : AffineBasis (Fin 3) ℝ Plane)
    (i : Fin 3) (e : Plane ≃ᵃ[ℝ] Plane)
    (he : ∀ x, e x = Plane.mk (b.coord (i + 1) x - b.coord (i + 2) x) (b.coord (i + 1) x))
    {x : Plane} (h1 : b.coord (i + 1) x ∈ Ico 0 (3 / 1000))
    (h2 : b.coord (i + 2) x ∈ Ico 0 (3 / 1000)) : ‖e x‖ < 1 / 20 := by
  have hsq : ‖e x‖ ^ 2 = (b.coord (i + 1) x - b.coord (i + 2) x) ^ 2 +
      (b.coord (i + 1) x) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, he]
    rfl
  have hsq1 : (b.coord (i + 1) x) ^ 2 ≤ (3 / 1000 : ℝ) ^ 2 :=
    (sq_le_sq₀ h1.1 (by norm_num)).mpr h1.2.le
  have hsq2 : (b.coord (i + 2) x) ^ 2 ≤ (3 / 1000 : ℝ) ^ 2 :=
    (sq_le_sq₀ h2.1 (by norm_num)).mpr h2.2.le
  nlinarith [mul_nonneg h1.1 h2.1, norm_nonneg (e x)]

private theorem smoothMax_nested_nonpos_of_two_small {ε a b c : ℝ} (hε : 0 < ε)
    (ha : a ≤ 0) (hb : b ≤ 0) (hc : c ≤ 0)
    (hlarge : (a ≤ -3 * ε ∧ b ≤ -3 * ε) ∨
      (a ≤ -3 * ε ∧ c ≤ -3 * ε) ∨ (b ≤ -3 * ε ∧ c ≤ -3 * ε)) :
    Real.smoothMax ε (Real.smoothMax ε a b) c ≤ 0 := by
  have hz : Real.smoothMax ε (-3 * ε) 0 = 0 := by
    rw [Real.smoothMax.eq_max_of_le hε (by rw [sub_zero, abs_of_neg (by linarith)]; linarith)]
    exact max_eq_right (by linarith)
  have hzr : Real.smoothMax ε 0 (-3 * ε) = 0 := by rw [Real.smoothMax.comm hε.ne', hz]
  rcases hlarge with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · have hab : Real.smoothMax ε a b ≤ -2 * ε := by
      have h := Real.smoothMax.le_max_add hε a b
      have hm := max_le h₁ h₂
      linarith
    have h : Real.smoothMax ε (Real.smoothMax ε a b) c ≤ Real.smoothMax ε (-2 * ε) 0 :=
      ((Real.smoothMax.monotone_left ε c) hab).trans ((Real.smoothMax.monotone_right ε _) hc)
    have heq : Real.smoothMax ε (-2 * ε) 0 = 0 := by
      rw [Real.smoothMax.eq_max_of_le hε (by rw [sub_zero, abs_of_neg (by linarith)]; linarith)]
      exact max_eq_right (by linarith)
    exact heq ▸ h
  · have hab : Real.smoothMax ε a b ≤ 0 := by
      calc
        _ ≤ Real.smoothMax ε (-3 * ε) b := (Real.smoothMax.monotone_left ε b) h₁
        _ ≤ Real.smoothMax ε (-3 * ε) 0 := (Real.smoothMax.monotone_right ε _) hb
        _ = 0 := hz
    calc
      _ ≤ Real.smoothMax ε 0 c := (Real.smoothMax.monotone_left ε c) hab
      _ ≤ Real.smoothMax ε 0 (-3 * ε) := (Real.smoothMax.monotone_right ε _) h₂
      _ = 0 := hzr
  · have hab : Real.smoothMax ε a b ≤ 0 := by
      calc
        _ ≤ Real.smoothMax ε 0 b := (Real.smoothMax.monotone_left ε b) ha
        _ ≤ Real.smoothMax ε 0 (-3 * ε) := (Real.smoothMax.monotone_right ε _) h₁
        _ = 0 := hzr
    calc
      _ ≤ Real.smoothMax ε 0 c := (Real.smoothMax.monotone_left ε c) hab
      _ ≤ Real.smoothMax ε 0 (-3 * ε) := (Real.smoothMax.monotone_right ε _) h₂
      _ = 0 := hzr

private theorem triangle_sublevel_eq_corner_replacement
    (b : AffineBasis (Fin 3) ℝ Plane) (e : Fin 3 → Plane ≃ᵃ[ℝ] Plane)
    (he : ∀ i x, e i x = Plane.mk (b.coord (i + 1) x - b.coord (i + 2) x) (b.coord (i + 1) x)) :
    {x | roundedTriangleFunction b (1 / 1000) x ≤ 0} =
      (convexHull ℝ (range b) \ ⋃ i, e i ⁻¹' ball 0 (1 / 20)) ∪
        ⋃ i, (e i ⁻¹' closedBall 0 (1 / 20)) ∩
          {x | 0 ≤ (e i x) 1 - Real.smoothMax (1 / 1000) ((e i x) 0) 0} := by
  ext x
  constructor
  · intro hx
    have hD := sublevel_roundedTriangleFunction_subset b (by norm_num : (0 : ℝ) < 1 / 1000) hx
    by_cases hN : x ∈ ⋃ i, e i ⁻¹' ball 0 (1 / 20)
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hN
      have hn : ‖e i x‖ < 1 / 20 := mem_ball_zero_iff.mp hi
      have hf := triangle_function_eq_chart b i (e i) (he i) (by linarith : ‖e i x‖ < 1 / 10)
      exact Or.inr (mem_iUnion.mpr ⟨i, ⟨mem_closedBall_zero_iff.mpr hn.le, by
        change 0 ≤ (e i x) 1 - Real.smoothMax (1 / 1000) ((e i x) 0) 0
        change roundedTriangleFunction b (1 / 1000) x ≤ 0 at hx
        linarith⟩⟩)
    · exact Or.inl ⟨hD, hN⟩
  · rintro (⟨hD, hN⟩ | hlocal)
    · have hcoord : ∀ j, 0 ≤ b.coord j x := by rwa [b.convexHull_eq_nonneg_coord] at hD
      have hnot (i : Fin 3) (h1 : b.coord (i + 1) x < 3 / 1000)
          (h2 : b.coord (i + 2) x < 3 / 1000) : False := by
        apply hN
        exact mem_iUnion.mpr ⟨i, mem_ball_zero_iff.mpr
          (triangle_chart_small_of_two_small b i (e i) (he i) ⟨hcoord _, h1⟩ ⟨hcoord _, h2⟩)⟩
      have hlarge : (3 / 1000 ≤ b.coord 0 x ∧ 3 / 1000 ≤ b.coord 1 x) ∨
          (3 / 1000 ≤ b.coord 0 x ∧ 3 / 1000 ≤ b.coord 2 x) ∨
          (3 / 1000 ≤ b.coord 1 x ∧ 3 / 1000 ≤ b.coord 2 x) := by
        by_cases h0 : 3 / 1000 ≤ b.coord 0 x
        · by_cases h1 : 3 / 1000 ≤ b.coord 1 x
          · exact Or.inl ⟨h0, h1⟩
          · by_cases h2 : 3 / 1000 ≤ b.coord 2 x
            · exact Or.inr (Or.inl ⟨h0, h2⟩)
            · exact (hnot 0 (lt_of_not_ge h1) (lt_of_not_ge h2)).elim
        · by_cases h1 : 3 / 1000 ≤ b.coord 1 x
          · by_cases h2 : 3 / 1000 ≤ b.coord 2 x
            · exact Or.inr (Or.inr ⟨h1, h2⟩)
            · exact (hnot 1 (lt_of_not_ge h2) (lt_of_not_ge h0)).elim
          · exact (hnot 2 (lt_of_not_ge h0) (lt_of_not_ge h1)).elim
      apply smoothMax_nested_nonpos_of_two_small (by norm_num : (0 : ℝ) < 1 / 1000)
        (neg_nonpos.mpr (hcoord 0)) (neg_nonpos.mpr (hcoord 1)) (neg_nonpos.mpr (hcoord 2))
      rcases hlarge with ⟨h0, h1⟩ | ⟨h0, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨by linarith, by linarith⟩
      · exact Or.inr (Or.inl ⟨by linarith, by linarith⟩)
      · exact Or.inr (Or.inr ⟨by linarith, by linarith⟩)
    · obtain ⟨i, hi, hside⟩ := mem_iUnion.mp hlocal
      have hn : ‖e i x‖ ≤ 1 / 20 := mem_closedBall_zero_iff.mp hi
      have hf := triangle_function_eq_chart b i (e i) (he i) (by linarith : ‖e i x‖ < 1 / 10)
      change 0 ≤ (e i x) 1 - Real.smoothMax (1 / 1000) ((e i x) 0) 0 at hside
      change roundedTriangleFunction b (1 / 1000) x ≤ 0
      linarith

private theorem triangle_vertex_chart_normalization (b : AffineBasis (Fin 3) ℝ Plane)
    (e : Fin 3 → Plane ≃ᵃ[ℝ] Plane)
    (he : ∀ i x, e i x = Plane.mk (b.coord (i + 1) x - b.coord (i + 2) x) (b.coord (i + 1) x))
    (i : Fin 3) : e i (b i) = 0 ∧ e i (b (i + 2)) = Plane.mk (-1) 0 ∧
        e i (b (i + 1)) = Plane.mk 1 1 := by
  simp only [he]
  fin_cases i <;> norm_num [b.coord_apply, Plane.mk, Fin.ext_iff] <;> exact Subsingleton.elim _ _

theorem exists_diffeomorph_corner_rounding_triangle (b : AffineBasis (Fin 3) ℝ Plane) :
    ∃ (e : Fin 3 → Plane ≃ᵃ[ℝ] Plane) (U : Fin 3 → Set Plane) (ε R : ℝ)
        (Φ : Plane ≃ₘ[ℝ] Plane),
      (∀ i, e i (b i) = 0 ∧ e i (b (i + 2)) = Plane.mk (-1) 0 ∧
        e i (b (i + 1)) = Plane.mk 1 1) ∧
      (∀ i, IsOpen (U i) ∧ e i ⁻¹' closedBall 0 R ⊆ U i) ∧
      (Pairwise fun i j => Disjoint (U i) (U j)) ∧ 0 < ε ∧ 3 * ε < R ∧
      (∀ i x, x ∈ U i → (x ∈ convexHull ℝ (range b) ↔
        0 ≤ (e i x) 1 - max ((e i x) 0) 0)) ∧
      Φ '' closedBall 0 1 =
        (convexHull ℝ (range b) \ ⋃ i, e i ⁻¹' ball 0 R) ∪
          ⋃ i, (e i ⁻¹' closedBall 0 R) ∩
            {x | 0 ≤ (e i x) 1 - Real.smoothMax ε ((e i x) 0) 0} := by
  choose e he using exists_triangle_vertex_chart b
  let U := fun i => e i ⁻¹' ball 0 (1 / 10)
  obtain ⟨Φ, hΦ, _, _⟩ := exists_diffeomorph_rounded_triangle b
    (by norm_num : (0 : ℝ) < 1 / 1000) (by norm_num)
  refine ⟨e, U, 1 / 1000, 1 / 20, Φ, ?_, ?_, ?_, by norm_num, by norm_num, ?_, ?_⟩
  · exact triangle_vertex_chart_normalization b e he
  · intro i
    refine ⟨isOpen_ball.preimage (e i).toAffineMap.continuous_of_finiteDimensional, ?_⟩
    intro x hx
    change e i x ∈ ball (0 : Plane) (1 / 10)
    apply closedBall_subset_ball (by norm_num : (1 / 20 : ℝ) < 1 / 10)
    exact hx
  · intro i j hij
    apply disjoint_left.mpr
    intro x hi hj
    have hci := triangle_chart_small_coords b i (e i) (he i) (mem_ball_zero_iff.mp hi)
    have hcj := triangle_chart_small_coords b j (e j) (he j) (mem_ball_zero_iff.mp hj)
    have h := (abs_lt.mp (hci.2 j hij.symm)).2
    linarith [hcj.1]
  · intro i x hx
    exact triangle_chart_hull_iff b i (e i) (he i) (mem_ball_zero_iff.mp hx)
  · exact hΦ.trans (triangle_sublevel_eq_corner_replacement b e he)

private theorem frontier_triangle_convexHull (b : AffineBasis (Fin 3) ℝ Plane) :
    frontier (convexHull ℝ (range b)) = ⋃ i, segment ℝ (b i) (b (i + 1)) := by
  have hclosed := (finite_range b).isClosed_convexHull ℝ
  rw [hclosed.frontier_eq, b.interior_convexHull, b.convexHull_eq_nonneg_coord]
  ext x
  constructor
  · rintro ⟨h, hn⟩
    have hn' : ¬ ∀ i, 0 < b.coord i x := hn
    push Not at hn'
    obtain ⟨i, hi⟩ := hn'
    have hseg := b.mem_segment_of_coord_eq_zero h i (le_antisymm hi (h i))
    refine mem_iUnion.mpr ⟨i + 1, ?_⟩
    convert! hseg using 1
    congr 1
    fin_cases i <;> rfl
  · intro hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    have hmem : x ∈ convexHull ℝ (range b) := (convex_convexHull ℝ (range b)).segment_subset
      (subset_convexHull ℝ _ (mem_range_self i)) (subset_convexHull ℝ _ (mem_range_self (i + 1))) hi
    have hcoord : ∀ j, 0 ≤ b.coord j x := by rwa [b.convexHull_eq_nonneg_coord] at hmem
    refine ⟨hcoord, ?_⟩
    intro hpos
    have hzero : b.coord (i + 2) x = 0 := by
      have himg : b.coord (i + 2) x ∈ (b.coord (i + 2)) '' segment ℝ (b i) (b (i + 1)) :=
        ⟨x, hi, rfl⟩
      rw [image_segment] at himg
      have hleft : b.coord (i + 2) (b i) = 0 := b.coord_apply_ne (by fin_cases i <;> decide)
      have hright : b.coord (i + 2) (b (i + 1)) = 0 := b.coord_apply_ne (by fin_cases i <;> decide)
      simpa only [hleft, hright, segment_same, mem_singleton_iff] using himg
    exact (hpos (i + 2)).ne' hzero

end DifferentialGeometry.Topology.Planar

namespace Schoenflies.PrePolygon

private theorem triangle_affineIndependent (P : PrePolygon 0) :
    AffineIndependent ℝ (fun i : Fin 3 => P.vertex (i.val : ZMod 3)) := by
  have hd : Plane.det (P.vertex (-1 - 1) - P.vertex (-1))
      (P.vertex 0 - P.vertex (-1)) ≠ 0 := by
    intro hd
    apply P.not_collinear_triangle
    apply P.mem_openSegment_of_det_eq_zero (-1)
    simpa only [neg_add_cancel] using hd
  have hq : AffineIndependent ℝ ![P.vertex 2, P.vertex 1, P.vertex 0] :=
    affineIndependent_plane_triple_of_det_ne_zero hd
  let t : Fin 3 ↪ Fin 3 := ⟨![2, 1, 0], by decide⟩
  convert! hq.comp_embedding t using 1
  funext i
  fin_cases i <;> rfl

private theorem exists_affineBasis_closed_triangle (P : PrePolygon 0) :
    ∃ b : AffineBasis (Fin 3) ℝ Plane,
      (∀ i, b i = P.vertex (i.val : ZMod 3)) ∧
      closure (inside P.carrier) = convexHull ℝ (range b) := by
  let p := fun i : Fin 3 => P.vertex (i.val : ZMod 3)
  let b := affineBasisOfTriangle p P.triangle_affineIndependent
  let C := convexHull ℝ (range b)
  have hfr : frontier C = P.carrier := by
    rw [DifferentialGeometry.Topology.Planar.frontier_triangle_convexHull]
    ext x
    simp only [PrePolygon.carrier, mem_iUnion, PrePolygon.edge]
    constructor
    · rintro ⟨i, hi⟩
      fin_cases i
      · exact ⟨0, hi⟩
      · exact ⟨1, hi⟩
      · exact ⟨2, hi⟩
    · rintro ⟨i, hi⟩
      fin_cases i
      · exact ⟨0, hi⟩
      · exact ⟨1, hi⟩
      · exact ⟨2, hi⟩
  have hclosed : IsClosed C := (finite_range b).isClosed_convexHull ℝ
  have hconv : Convex ℝ C := convex_convexHull ℝ _
  have hint : (interior C).Nonempty :=
    ⟨Finset.univ.centroid ℝ b, b.centroid_mem_interior_convexHull⟩
  have hcl : closure (interior C) = C :=
    (hconv.closure_interior_eq_closure_of_nonempty_interior hint).trans hclosed.closure_eq
  have hfri : frontier (interior C) = P.carrier := by
    rw [frontier, hcl, interior_interior]
    exact hclosed.frontier_eq.symm.trans hfr
  obtain ⟨x, hx⟩ := hint
  have hsub : interior C ⊆ P.carrierᶜ := by
    intro z hz hzc
    have hh : z ∈ C \ interior C := by rw [← hclosed.frontier_eq, hfr]; exact hzc
    exact hh.2 hz
  have hcomponent : connectedComponentIn P.carrierᶜ x = interior C :=
    Plane.connectedComponentIn_eq_of_frontier_disjoint isOpen_interior hconv.interior.isPreconnected
      hsub (by rw [hfri, inter_compl_self]) hx
  have hbounded : Bornology.IsBounded (interior C) :=
    ((finite_range b).isCompact_convexHull ℝ).isBounded.subset interior_subset
  have hxinside : x ∈ inside P.carrier := ⟨hsub hx, hcomponent.symm ▸ hbounded⟩
  have hi : inside P.carrier = interior C :=
    (P.isSeparating_carrier.connectedComponentIn_eq_inside hxinside).symm.trans hcomponent
  exact ⟨b, fun _ => rfl, by rw [hi, hcl]⟩

theorem exists_diffeomorph_corner_rounding_triangle (P : PrePolygon 0) :
    ∃ (e : ZMod 3 → Plane ≃ᵃ[ℝ] Plane) (U : ZMod 3 → Set Plane) (ε R : ℝ)
        (Φ : Plane ≃ₘ[ℝ] Plane),
      (∀ i, e i (P.vertex i) = 0 ∧ e i (P.vertex (i - 1)) = Plane.mk (-1) 0 ∧
        e i (P.vertex (i + 1)) = Plane.mk 1 1) ∧
      (∀ i, IsOpen (U i) ∧ e i ⁻¹' closedBall 0 R ⊆ U i) ∧
      (Pairwise fun i j => Disjoint (U i) (U j)) ∧ 0 < ε ∧ 3 * ε < R ∧
      (∀ i x, x ∈ U i → (x ∈ closure (inside P.carrier) ↔
        0 ≤ (e i x) 1 - max ((e i x) 0) 0)) ∧
      Φ '' closedBall 0 1 =
        (closure (inside P.carrier) \ ⋃ i, e i ⁻¹' ball 0 R) ∪
          ⋃ i, (e i ⁻¹' closedBall 0 R) ∩
            {x | 0 ≤ (e i x) 1 - Real.smoothMax ε ((e i x) 0) 0} := by
  obtain ⟨b, hb, hregion⟩ := P.exists_affineBasis_closed_triangle
  obtain ⟨e, U, ε, R, Φ, hnorm, hU, hdisj, hε, hR, hside, hΦ⟩ :=
    DifferentialGeometry.Topology.Planar.exists_diffeomorph_corner_rounding_triangle b
  let k := (ZMod.finEquiv 3).symm
  have hpoint (i : ZMod 3) : b (k i) = P.vertex i := by
    rw [hb]
    exact congrArg P.vertex (ZMod.natCast_zmod_val i)
  have hprev (i : ZMod 3) : k (i - 1) = k i + 2 := by
    change (ZMod.finEquiv 3).symm (i - 1) = _
    rw [map_sub, map_one, sub_eq_add_neg]
    rfl
  have hnext (i : ZMod 3) : k (i + 1) = k i + 1 := by
    exact k.map_add i 1
  refine ⟨fun i => e (k i), fun i => U (k i), ε, R, Φ, ?_, fun i => hU (k i), ?_, hε, hR, ?_, ?_⟩
  · intro i
    rw [← hpoint i, ← hpoint (i - 1), ← hpoint (i + 1), hprev, hnext]
    exact hnorm (k i)
  · intro i j hij
    exact hdisj (fun h => hij (k.injective h))
  · intro i x hx
    rw [hregion]
    exact hside (k i) x hx
  · rw [hregion]
    have hN := k.surjective.iUnion_comp (fun j : Fin 3 => e j ⁻¹' ball (0 : Plane) R)
    have hK := k.surjective.iUnion_comp (fun j : Fin 3 =>
      (e j ⁻¹' closedBall (0 : Plane) R) ∩
        {x | 0 ≤ (e j x) 1 - Real.smoothMax ε ((e j x) 0) 0})
    rw [hN, hK]
    exact hΦ

end Schoenflies.PrePolygon

namespace Schoenflies.PrePolygon

private theorem exists_diffeomorph_corner_rounding_of_carrier_eq_triangle
    {m : ℕ} (P : PrePolygon m) (Q : PrePolygon 0) (hcar : P.carrier = Q.carrier) :
    let I := {i : ZMod (m + 3) //
      Plane.det (P.vertex (i - 1) - P.vertex i) (P.vertex (i + 1) - P.vertex i) ≠ 0}
    ∃ (e : I → Plane ≃ᵃ[ℝ] Plane) (U : I → Set Plane) (r ε R : I → ℝ)
        (Φ : Plane ≃ₘ[ℝ] Plane),
      (∀ i, 0 < r i ∧ e i (P.vertex i) = 0 ∧
        e i (P.vertex ((i : ZMod (m + 3)) - 1)) = Plane.mk (-1) 0 ∧
        e i (P.vertex ((i : ZMod (m + 3)) + 1)) = Plane.mk (r i) (r i)) ∧
      (∀ i, IsOpen (U i) ∧ e i ⁻¹' closedBall 0 (R i) ⊆ U i) ∧
      (Pairwise fun i j => Disjoint (U i) (U j)) ∧
      (∀ i, 0 < ε i ∧ 3 * ε i < R i) ∧
      (∀ i x, x ∈ U i → (x ∈ closure (inside P.carrier) ↔
        0 ≤ (e i x) 1 - max ((e i x) 0) 0)) ∧
      Φ '' closedBall 0 1 =
        (closure (inside P.carrier) \ ⋃ i, e i ⁻¹' ball 0 (R i)) ∪
          ⋃ i, (e i ⁻¹' closedBall 0 (R i)) ∩
            {x | 0 ≤ (e i x) 1 - Real.smoothMax (ε i) ((e i x) 0) 0} := by
  dsimp only
  classical
  let I := {i : ZMod (m + 3) //
    Plane.det (P.vertex (i - 1) - P.vertex i) (P.vertex (i + 1) - P.vertex i) ≠ 0}
  let I' := {i : ZMod (m + 3) // P.vertex i ∈ (univ : Set Plane) ∧
    Plane.det (P.vertex (i - 1) - P.vertex i) (P.vertex (i + 1) - P.vertex i) ≠ 0}
  let J := {j : ZMod 3 // Q.vertex j ∈ (univ : Set Plane)}
  let k : I → I' := fun i => ⟨i, mem_univ _, i.property⟩
  have hk : Function.Bijective k := by
    constructor
    · intro i j h
      exact Subtype.ext (congrArg (fun x : I' => x.val) h)
    · intro i
      exact ⟨⟨i, i.property.2⟩, rfl⟩
  obtain ⟨e, U, ε, R, A, hnorm, hU, hdisj, hε, hR, hside, hA⟩ :=
    Q.exists_diffeomorph_corner_rounding_triangle
  have hdet (i : ZMod 3) :
      Plane.det (Q.vertex (i - 1) - Q.vertex i) (Q.vertex (i + 1) - Q.vertex i) ≠ 0 := by
    intro hd
    have hmem : e i (Q.vertex i) ∈
        e i '' openSegment ℝ (Q.vertex (i - 1)) (Q.vertex (i + 1)) :=
      ⟨Q.vertex i, Q.mem_openSegment_of_det_eq_zero i hd, rfl⟩
    change (e i).toAffineMap (Q.vertex i) ∈
      (e i).toAffineMap '' openSegment ℝ (Q.vertex (i - 1)) (Q.vertex (i + 1)) at hmem
    rw [image_openSegment] at hmem
    change e i (Q.vertex i) ∈ openSegment ℝ (e i (Q.vertex (i - 1)))
      (e i (Q.vertex (i + 1))) at hmem
    rw [(hnorm i).1, (hnorm i).2.1, (hnorm i).2.2] at hmem
    obtain ⟨a, b, ha, hb, hab, heq⟩ := hmem
    have heq₁ := congrArg (fun x : Plane => x 1) heq
    change a * 0 + b * 1 = 0 at heq₁
    exact hb.ne' (by linarith only [heq₁])
  have hcenter (i : ZMod 3) : Q.vertex i ∈ U i := by
    apply (hU i).2
    change e i (Q.vertex i) ∈ closedBall (0 : Plane) R
    rw [(hnorm i).1]
    exact mem_closedBall_self (by linarith only [hε, hR])
  obtain ⟨j, f, ρ, ℓ, B, η, hj, hcover, hdata, hflow⟩ :=
    P.exists_isotopy_to_reanchored_replacement Q
      (S := univ) (U := univ) isOpen_univ subset_rfl
      (fun x _ => by rw [hcar]) (closure (inside P.carrier))
      (fun j : J => e j) (fun j : J => U j)
      (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => R) (fun _ => ε)
      (fun j => ⟨one_pos, (hnorm j).1, (hnorm j).2.1, by simpa using (hnorm j).2.2⟩)
      (fun _ => Or.inr rfl)
      (fun j => by simp only [one_ne_zero, false_iff]; exact hdet j)
      (fun _ => Or.inr rfl) (fun _ => ⟨hε, hR⟩)
      (fun j => ⟨(hU j).1, hcenter j⟩)
      (fun i j hij => hdisj (fun h => hij (Subtype.ext h))) (fun j => (hU j).2)
      (fun j p hp => by simpa only [hcar, one_mul] using hside j p hp)
  have hη (i : I') : 0 < η i := (hdata i).2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨hwidth, heq, _, _, H, K, hH, hHi, hH0, hK, hKU, hfix, himage, _, _⟩ :=
    hflow η (fun i => ⟨hη i, le_rfl⟩)
  refine ⟨fun i => f (k i), fun i => U (j (k i)), fun i => ρ (k i),
    fun i => ℓ (k i) * η (k i), fun i => B (k i), A.trans (H 1), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    obtain ⟨_, _, hr, _, he, ha, hb, _⟩ := hdata (k i)
    exact ⟨hr, he, ha, hb⟩
  · intro i
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hBU, _⟩ := hdata (k i)
    exact ⟨(hU (j (k i))).1, hBU⟩
  · intro i i' hii'
    exact hdisj (fun h => hii' (hk.1 (hj (Subtype.ext h))))
  · intro i
    obtain ⟨_, _, _, hℓ, _⟩ := hdata (k i)
    exact ⟨mul_pos hℓ (hη (k i)), (hwidth (k i)).2⟩
  · intro i x hx
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hs⟩ := hdata (k i)
    simpa only [one_mul] using hs x hx
  · have hJ : Function.Surjective (fun j : J => (j : ZMod 3)) := fun j => ⟨⟨j, mem_univ _⟩, rfl⟩
    change (fun x => H 1 (A x)) '' closedBall 0 1 = _
    rw [← image_image, hA]
    have hsource := hJ.iUnion_comp (fun j : ZMod 3 => e j ⁻¹' ball (0 : Plane) R)
    have hsource' := hJ.iUnion_comp (fun j : ZMod 3 =>
      (e j ⁻¹' closedBall (0 : Plane) R) ∩
        {x | 0 ≤ (e j x) 1 - Real.smoothMax ε ((e j x) 0) 0})
    have htgt := hk.2.iUnion_comp (fun i : I' => f i ⁻¹' ball (0 : Plane) (B i))
    have htgt' := hk.2.iUnion_comp (fun i : I' =>
      (f i ⁻¹' closedBall (0 : Plane) (B i)) ∩
        {x | 0 ≤ (f i x) 1 - Real.smoothMax (ℓ i * η i) ((f i x) 0) 0})
    dsimp only at hsource hsource' htgt htgt'
    simp only [one_mul] at himage
    rw [hsource, hsource', ← htgt, ← htgt'] at himage
    simpa only [hcar] using himage


private theorem exists_diffeomorph_corner_replacement_of_carrier_eq_triangle
    {m : ℕ} (P : PrePolygon m) (Q : PrePolygon 0) (hcar : P.carrier = Q.carrier)
    (e : {i : ZMod (m + 3) //
      Plane.det (P.vertex (i - 1) - P.vertex i) (P.vertex (i + 1) - P.vertex i) ≠ 0} →
        Plane ≃ᵃ[ℝ] Plane)
    (U : {i : ZMod (m + 3) //
      Plane.det (P.vertex (i - 1) - P.vertex i) (P.vertex (i + 1) - P.vertex i) ≠ 0} → Set Plane)
    (r σ ε R : {i : ZMod (m + 3) //
      Plane.det (P.vertex (i - 1) - P.vertex i) (P.vertex (i + 1) - P.vertex i) ≠ 0} → ℝ)
    (hnorm : ∀ i, 0 < r i ∧ e i (P.vertex i) = 0 ∧
      e i (P.vertex ((i : ZMod (m + 3)) - 1)) = Plane.mk (-1) 0 ∧
      e i (P.vertex ((i : ZMod (m + 3)) + 1)) = Plane.mk (r i) (r i))
    (hU : ∀ i, IsOpen (U i))
    (hσ : ∀ i, σ i = -1 ∨ σ i = 1)
    (hε : ∀ i, 0 < ε i) (hR : ∀ i, 3 * ε i < R i)
    (hKU : ∀ i, e i ⁻¹' closedBall (0 : Plane) (R i) ⊆ U i)
    (hdisj : Pairwise fun i j => Disjoint (U i) (U j))
    (hside : ∀ i, ∀ x ∈ U i, x ∈ closure (inside P.carrier) ↔
      0 ≤ σ i * ((e i x) 1 - max ((e i x) 0) 0)) :
    ∃ Φ : Plane ≃ₘ[ℝ] Plane, Φ '' closedBall 0 1 =
      (closure (inside P.carrier) \ ⋃ i, e i ⁻¹' ball 0 (R i)) ∪
        ⋃ i, (e i ⁻¹' closedBall 0 (R i)) ∩
          {x | 0 ≤ σ i * ((e i x) 1 - Real.smoothMax (ε i) ((e i x) 0) 0)} := by
  obtain ⟨e₀, U₀, r₀, ε₀, R₀, A, hnorm₀, hU₀, hdisj₀, hε₀, hside₀, hA⟩ :=
    P.exists_diffeomorph_corner_rounding_of_carrier_eq_triangle Q hcar
  obtain ⟨H, K, hH, hHi, hH0, hK, hKU', hfix, himage, _, _⟩ :=
    Schoenflies.exists_isotopy_between_normalized_corner_replacements ![e₀, e]
      (fun i => P.vertex ((i : ZMod (m + 3)) - 1))
      (fun i => P.vertex ((i : ZMod (m + 3)) + 1))
      (fun i => P.vertex i) ![U₀, U] ![r₀, r] (fun _ _ => 1)
      ![fun _ => 1, σ] ![ε₀, ε] ![R₀, R]
      (D := closure (inside P.carrier))
      (by
        intro k i
        fin_cases k
        · exact ⟨(hnorm₀ i).1, (hnorm₀ i).2.2.1,
            by
              change e₀ i (P.vertex ((i : ZMod (m + 3)) + 1)) = Plane.mk (r₀ i) (1 * r₀ i)
              simpa only [one_mul] using (hnorm₀ i).2.2.2, (hnorm₀ i).2.1⟩
        · exact ⟨(hnorm i).1, (hnorm i).2.2.1,
            by
              change e i (P.vertex ((i : ZMod (m + 3)) + 1)) = Plane.mk (r i) (1 * r i)
              simpa only [one_mul] using (hnorm i).2.2.2, (hnorm i).2.1⟩)
      (by intro k i; fin_cases k; exacts [(hU₀ i).1, hU i])
      (fun _ _ => Or.inr rfl)
      (by intro k i; fin_cases k; exacts [Or.inr rfl, hσ i])
      (by intro k i; fin_cases k; exacts [(hε₀ i).1, hε i])
      (by intro k i; fin_cases k; exacts [(hε₀ i).2, hR i])
      (by intro k i; fin_cases k; exacts [(hU₀ i).2, hKU i])
      (by intro k; fin_cases k; exacts [hdisj₀, hdisj])
      (by
        intro k i x hx
        fin_cases k
        · change x ∈ closure (inside P.carrier) ↔
            0 ≤ 1 * ((e₀ i x) 1 - 1 * max ((e₀ i x) 0) 0)
          simpa only [one_mul] using hside₀ i x hx
        · change x ∈ closure (inside P.carrier) ↔
            0 ≤ σ i * ((e i x) 1 - 1 * max ((e i x) 0) 0)
          simpa only [one_mul] using hside i x hx)
  refine ⟨A.trans (H 1), ?_⟩
  change (fun x => H 1 (A x)) '' closedBall 0 1 = _
  rw [← image_image, hA]
  simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, one_mul] using himage


private theorem exists_triangle_carrier_eq_of_closure_inside_eq_convexHull
    {m : ℕ} (P : PrePolygon m) (b : AffineBasis (Fin 3) ℝ Plane)
    (hregion : closure (inside P.carrier) = convexHull ℝ (range b)) :
    ∃ Q : PrePolygon 0, P.carrier = Q.carrier := by
  have hdet : Plane.det (b 1 - b 0) (b 2 - b 0) ≠ 0 := by
    intro hd
    have h10 : b 1 - b 0 ≠ 0 := sub_ne_zero.mpr (b.ind.injective.ne (by decide))
    obtain ⟨t, ht⟩ := (Plane.det_eq_zero_iff_smul _ _ h10).mp hd
    have hc := congrArg (b.coord 2).linear ht
    have hc₂ : (b.coord 2).linear (b 2 - b 0) = 1 := by
      calc
        _ = b.coord 2 (b 2) - b.coord 2 (b 0) := (b.coord 2).linearMap_vsub _ _
        _ = 1 := by norm_num [b.coord_apply, Fin.ext_iff]
    have hc₁ : (b.coord 2).linear (b 1 - b 0) = 0 := by
      calc
        _ = b.coord 2 (b 1) - b.coord 2 (b 0) := (b.coord 2).linearMap_vsub _ _
        _ = 0 := by norm_num [b.coord_apply, Fin.ext_iff]
    rw [map_smul, hc₂, hc₁, smul_zero] at hc
    exact one_ne_zero hc
  let T : ClosedPolygon 0 := Schoenflies.triangle hdet
  let Q : PrePolygon 0 := ⟨T.vertex, T.vertex_inj, T.edges_meet⟩
  have hfr : frontier (convexHull ℝ (range b)) = Q.carrier := by
    rw [DifferentialGeometry.Topology.Planar.frontier_triangle_convexHull]
    ext x
    simp only [PrePolygon.carrier, mem_iUnion, PrePolygon.edge]
    constructor
    · rintro ⟨i, hi⟩
      fin_cases i
      · exact ⟨0, hi⟩
      · exact ⟨1, hi⟩
      · exact ⟨2, hi⟩
    · rintro ⟨i, hi⟩
      fin_cases i
      · exact ⟨0, hi⟩
      · exact ⟨1, hi⟩
      · exact ⟨2, hi⟩
  have hP : frontier (closure (inside P.carrier)) = P.carrier := by
    rw [frontier, closure_closure, interior_closure_inside_of_separating P.isSeparating_carrier]
    simpa only [frontier, P.isSeparating_carrier.isOpen_inside.interior_eq] using
      P.isSeparating_carrier.frontier_inside
  exact ⟨Q, hP.symm.trans ((congrArg frontier hregion).trans hfr)⟩

theorem exists_diffeomorph_corner_replacement_of_triangle
    {m : ℕ} (P : PrePolygon m) (b : AffineBasis (Fin 3) ℝ Plane)
    (hregion : closure (inside P.carrier) = convexHull ℝ (range b))
    (e : {i : ZMod (m + 3) //
      Plane.det (P.vertex (i - 1) - P.vertex i) (P.vertex (i + 1) - P.vertex i) ≠ 0} →
        Plane ≃ᵃ[ℝ] Plane)
    (U : {i : ZMod (m + 3) //
      Plane.det (P.vertex (i - 1) - P.vertex i) (P.vertex (i + 1) - P.vertex i) ≠ 0} → Set Plane)
    (r σ ε R : {i : ZMod (m + 3) //
      Plane.det (P.vertex (i - 1) - P.vertex i) (P.vertex (i + 1) - P.vertex i) ≠ 0} → ℝ)
    (hnorm : ∀ i, 0 < r i ∧
      e i (P.vertex ((i : ZMod (m + 3)) - 1)) = Plane.mk (-1) 0 ∧
      e i (P.vertex ((i : ZMod (m + 3)) + 1)) = Plane.mk (r i) (r i) ∧
      e i (P.vertex i) = 0)
    (hU : ∀ i, IsOpen (U i))
    (hσ : ∀ i, σ i = -1 ∨ σ i = 1)
    (hε : ∀ i, 0 < ε i) (hR : ∀ i, 3 * ε i < R i)
    (hKU : ∀ i, e i ⁻¹' closedBall (0 : Plane) (R i) ⊆ U i)
    (hdisj : Pairwise fun i j => Disjoint (U i) (U j))
    (hside : ∀ i, ∀ x ∈ U i, x ∈ closure (inside P.carrier) ↔
      0 ≤ σ i * ((e i x) 1 - max ((e i x) 0) 0)) :
    ∃ Φ : Plane ≃ₘ[ℝ] Plane, Φ '' closedBall 0 1 =
      (closure (inside P.carrier) \ ⋃ i, e i ⁻¹' ball 0 (R i)) ∪
        ⋃ i, (e i ⁻¹' closedBall 0 (R i)) ∩
          {x | 0 ≤ σ i * ((e i x) 1 - Real.smoothMax (ε i) ((e i x) 0) 0)} := by
  obtain ⟨Q, hcar⟩ := P.exists_triangle_carrier_eq_of_closure_inside_eq_convexHull b hregion
  exact P.exists_diffeomorph_corner_replacement_of_carrier_eq_triangle Q hcar e U r σ ε R
    (fun i => ⟨(hnorm i).1, (hnorm i).2.2.2, (hnorm i).2.1, (hnorm i).2.2.1⟩)
    hU hσ hε hR hKU hdisj hside

end Schoenflies.PrePolygon
