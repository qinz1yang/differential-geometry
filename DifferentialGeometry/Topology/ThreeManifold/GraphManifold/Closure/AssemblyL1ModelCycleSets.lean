import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1ModelCycle

/-!
# Chapter-14 assembly, item L1, group G3a: the set-level fields of the model cycle

How the pieces of the model cycle meet in `S³`: a neck meets the balls exactly on its ball side
(`modelNeck_mem_range_ball_iff`) and the handles exactly on its handle side
(`modelNeck_mem_range_handle_iff`), meets no other piece (`modelNeck_pieces`); balls and handles
are pairwise disjoint, and a handle meets the balls exactly in its two end disks
(`modelHandle_ball_inter`). The comparisons are made on heights modulo the period (window
lemma) and, at equal heights, on radii (strict radial monotonicity).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold Manifold
open scoped ContDiff Topology Manifold

universe u

namespace GC.GraphManifold.Assembly

local instance diskChartsS_ASML1d : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

variable {len : ℕ} {ε : ℝ}

theorem eq_zero_of_shift {len : ℕ} (hlen : 0 < len) {x y : ℝ} {m : ℤ}
    (h : y = x + 4 * len * m) (hxy : |y - x| < 4) : m = 0 := by
  have hL : (1 : ℝ) ≤ len := Nat.one_le_cast.mpr hlen
  have h1 : |(4 * len : ℝ) * m| < 4 := by
    have : y - x = 4 * len * m := by linarith
    rw [← this]
    exact hxy
  have h2 : |(m : ℝ)| < 1 := by
    rw [abs_mul, abs_of_pos (by positivity)] at h1
    by_contra hc
    have := mul_le_mul (le_refl (4 * (len : ℝ))) (not_lt.mp hc) zero_le_one (by positivity)
    nlinarith
  exact Int.abs_lt_one_iff.mp (by exact_mod_cast h2)

/-- The ball `j` read from the zone `k` one step below. -/
theorem modelBall_finRotate {len : ℕ} (hlen : 0 < len)
    (k : Fin len) (x : ClosedCell 3) :
    modelBall.{u} len ε (finRotate len k) x = modelSphere.{u} len
      ((ballMap ε (modelBase k) (x : EuclideanSpace ℝ (Fin 3))).1,
        (ballMap ε (modelBase k) (x : EuclideanSpace ℝ (Fin 3))).2 + 4) := by
  unfold modelBall ballSphere
  rw [ballMap_apply, ballMap_apply]
  simp only
  rw [show modelBase k - (ballCoord (x : EuclideanSpace ℝ (Fin 3))).2 + 4 =
    modelBase k + 4 + -(ballCoord (x : EuclideanSpace ℝ (Fin 3))).2 by ring, sub_eq_add_neg]
  exact modelBase_finRotate hlen k _ _

/-! ## Necks and balls -/

/-- The sphere bound of a ball point at a height `|h| ≥ 1/4`. -/
theorem norm_ballMap_fst_le_sphere (hε : 0 < ε) (hε' : ε ≤ 1 / 8) (c : ℝ) (x : ClosedCell 3)
    (hh : 1 / 4 ≤ |(ballCoord (x : EuclideanSpace ℝ (Fin 3))).2|) :
    ∃ s₀, 0 ≤ s₀ ∧ capCos s₀ = |(ballCoord (x : EuclideanSpace ℝ (Fin 3))).2| ∧
      ‖(ballMap ε c (x : EuclideanSpace ℝ (Fin 3))).1‖ ≤ neckRadius ε s₀ 0 := by
  have hx : ‖(x : EuclideanSpace ℝ (Fin 3))‖ ≤ 1 := x.2
  have hh1 := (abs_ballCoord_snd_le (x : EuclideanSpace ℝ (Fin 3))).trans hx
  obtain ⟨hr, hc⟩ := ballRadius_sphere hε hε' hh hh1
  refine ⟨_, by positivity, hc, ?_⟩
  rw [← hr]
  exact norm_ballMap_fst_le hε hε' c hx

theorem modelNeck_mem_range_ball_iff (hlen : 0 < len) (hε : 0 < ε) (hε' : ε ≤ 1 / 8)
    (k : Fin len) (b : Bool) {q : ModelSpace} (hq : q ∈ neckDomain ε) :
    modelNeck.{u} hlen hε hε' k b q ∈ range (modelBall.{u} len ε (rimBall len k b)) ↔ q.2 ≤ 0 := by
  constructor
  · rintro ⟨x, hx⟩
    by_contra hpos
    rw [not_le] at hpos
    set P := zoneChartMap ε (modelBase k) (neckFlip b q)
    set B := ballMap ε (modelBase k) (x : EuclideanSpace ℝ (Fin 3))
    have hPr := zoneChartMap_range hε hε' (modelBase k) (neckFlip_mapsTo hε hε' b hq)
    have hBr := ballMap_range hε hε' (modelBase k) x
    have hu := neck_height_mem hε hε' hq
    have hcos := capCos_neck_bounds (s := ‖q.1‖) (norm_nonneg _) (by linarith [hq.1])
    -- the ball point read from the zone `k`
    have hxB : ∃ d : ℝ, modelSphere.{u} len (B.1, B.2 + d) = modelSphere.{u} len P ∧
        (b = false → d = 0) ∧ (b = true → d = 4) := by
      cases b
      · refine ⟨0, ?_, fun _ => rfl, fun h => absurd h (by simp)⟩
        rw [add_zero]
        rw [modelNeck_apply] at hx
        exact hx
      · refine ⟨4, ?_, fun h => absurd h (by simp), fun _ => rfl⟩
        rw [modelNeck_apply, rimBall_true, modelBall_finRotate hlen] at hx
        exact hx
    obtain ⟨d, hdP, hd0, hd4⟩ := hxB
    obtain ⟨hw, m, hm⟩ := modelSphere_eq_shift hlen (p := (B.1, B.2 + d))
      (by exact hBr.1.trans_lt (by norm_num)) hPr.1 hdP
    have hPv : P.2 = modelBase k + (if b then 4 - (1 + q.2) * capCos ‖q.1‖ else
        (1 + q.2) * capCos ‖q.1‖) := by
      change (zoneChartMap ε (modelBase k) (neckFlip b q)).2 = _
      rw [zoneChartMap_neckFlip hε hε' _ b hq]
      cases b <;> simp only [↓reduceIte, Bool.false_eq_true, add_sub_assoc]
    have hBv : B.2 = modelBase k - (ballCoord (x : EuclideanSpace ℝ (Fin 3))).2 := ballMap_snd _ _ _
    set h := (ballCoord (x : EuclideanSpace ℝ (Fin 3))).2
    have hh1 : |h| ≤ 1 := (abs_ballCoord_snd_le _).trans x.2
    have hh1' := abs_le.mp hh1
    -- the height of the ball point
    have hheight : |h| = (1 + q.2) * capCos ‖q.1‖ := by
      cases b
      · rw [hd0 rfl] at hm
        simp only [Bool.false_eq_true, ↓reduceIte] at hPv
        rw [hPv, hBv] at hm
        simp only at hm
        have hm0 := eq_zero_of_shift hlen hm (by
          rw [show modelBase k + (1 + q.2) * capCos ‖q.1‖ - (modelBase k - h + 0) =
            (1 + q.2) * capCos ‖q.1‖ + h by ring, abs_lt]
          constructor <;> linarith)
        rw [hm0] at hm
        push_cast at hm
        rw [abs_of_neg (by linarith)]
        linarith
      · rw [hd4 rfl] at hm
        simp only [↓reduceIte] at hPv
        rw [hPv, hBv] at hm
        simp only at hm
        have hm0 := eq_zero_of_shift hlen hm (by
          rw [show modelBase k + (4 - (1 + q.2) * capCos ‖q.1‖) - (modelBase k - h + 4) =
            h - (1 + q.2) * capCos ‖q.1‖ by ring, abs_lt]
          constructor <;> linarith)
        rw [hm0] at hm
        push_cast at hm
        rw [abs_of_pos (by linarith)]
        linarith
    obtain ⟨s₀, hs₀, hcs₀, hle⟩ := norm_ballMap_fst_le_sphere hε hε' (modelBase k) x
      (by rw [hheight]; nlinarith)
    have hlt : s₀ < ‖q.1‖ := by
      apply (capCos_lt_capCos_iff hs₀ (norm_nonneg _)).mp
      rw [hcs₀, hheight]
      nlinarith
    have hrad := neckRadius_lt_of_lt ε hlt hpos
    have hPn : ‖P.1‖ = neckRadius ε ‖q.1‖ q.2 := modelNeck_fst_norm hε hε' k b hq
    have : ‖B.1‖ = ‖P.1‖ := by rw [hw]
    linarith
  · intro hq0
    obtain ⟨x, hx, hxq⟩ := exists_capRegion_capMap_eq hε hε' b hq hq0
    exact ⟨x, by rw [modelBall_cap hlen hε hε' k b x hx, hxq]⟩

/-! ## Necks and handles -/

theorem modelNeck_mem_range_handle_iff (hlen : 0 < len) (hε : 0 < ε) (hε' : ε ≤ 1 / 8)
    (k : Fin len) (b : Bool) {q : ModelSpace} (hq : q ∈ neckDomain ε) :
    modelNeck.{u} hlen hε hε' k b q ∈ range (modelHandle.{u} len ε k) ↔
      (0 ≤ q.2 ∧ ‖q.1‖ ≤ 1) := by
  have hτ := abs_lt.mp hq.2
  constructor
  · rintro ⟨q', hq'⟩
    rw [modelNeck_apply] at hq'
    have h := zoneSphere_injOn hε hε' hlen (modelBase k) (handleInclusion_mem_zoneDomain q')
      (neckFlip_mapsTo hε hε' b hq) hq'
    have h1 : ‖(q'.1 : ModelPlane)‖ ≤ 1 := q'.1.2
    have h2 := q'.2.2
    cases b
    · rw [neckFlip_false] at h
      rw [← h]
      exact ⟨h2.1, h1⟩
    · rw [neckFlip_true] at h
      simp only [handleInclusion, Prod.mk.injEq] at h
      refine ⟨by linarith [h2.2, h.2], by rw [← h.1]; exact h1⟩
  · rintro ⟨h0, h1⟩
    cases b
    · refine ⟨(⟨q.1, by simpa using h1⟩, ⟨q.2, h0, by linarith⟩), ?_⟩
      rw [modelNeck_apply, neckFlip_false]
      rfl
    · refine ⟨(⟨q.1, by simpa using h1⟩, ⟨1 - q.2, by linarith, by linarith⟩), ?_⟩
      rw [modelNeck_apply, neckFlip_true]
      rfl

/-! ## Heights of the balls and handles -/

theorem modelHandle_height (hε : 0 < ε) (hε' : ε ≤ 1 / 8) (k : Fin len)
    (q : ClosedCell 2 × Icc (0 : ℝ) 1) :
    ‖(zoneChartMap ε (modelBase k) (handleInclusion q)).1‖ < 13 / 10 ∧
      (zoneChartMap ε (modelBase k) (handleInclusion q)).2 =
        modelBase k + zoneHeight ‖(q.1 : ModelPlane)‖ (q.2 : ℝ) ∧
      3 / 10 < zoneHeight ‖(q.1 : ModelPlane)‖ (q.2 : ℝ) ∧
        zoneHeight ‖(q.1 : ModelPlane)‖ (q.2 : ℝ) < 37 / 10 := by
  have hz := handleInclusion_mem_zoneDomain q
  have hU := zoneHeight_mem (norm_nonneg _) hz.1 hz.2.1 hz.2.2
  refine ⟨(zoneChartMap_range hε hε' _ hz).1, ?_, hU⟩
  rw [zoneChartMap_apply]
  rfl

/-- The pieces met by a neck target are the labelled ball and handle. -/
theorem modelNeck_pieces (hlen : 0 < len) (hε : 0 < ε) (hε' : ε ≤ 1 / 8) (k : Fin len)
    (b : Bool) :
    (modelNeck.{u} hlen hε hε' k b).target ∩
        ((⋃ j, range (modelBall.{u} len ε j)) ∪ ⋃ j, range (modelHandle.{u} len ε j)) ⊆
      range (modelBall.{u} len ε (rimBall len k b)) ∪ range (modelHandle.{u} len ε k) := by
  rintro p ⟨hpT, hp⟩
  rw [modelNeck_target] at hpT
  obtain ⟨q, hq, rfl⟩ := hpT
  have hPr := zoneChartMap_range hε hε' (modelBase k) (neckFlip_mapsTo hε hε' b hq)
  obtain ⟨xb, hxb, hxf, hxt⟩ := modelNeck_height hε hε' (modelBase k) b hq
  rcases hp with hp | hp
  · obtain ⟨j, x, hx⟩ := Set.mem_iUnion.mp hp
    left
    have hBr := ballMap_range hε hε' (modelBase j) x
    obtain ⟨-, m, hm⟩ := modelSphere_eq_shift hlen (lt_of_le_of_lt hBr.1 (by norm_num)) hPr.1 hx
    rw [hxb] at hm
    have hBv : (ballMap ε (modelBase j) (x : EuclideanSpace ℝ (Fin 3))).2 =
        modelBase j - (ballCoord (x : EuclideanSpace ℝ (Fin 3))).2 := ballMap_snd _ _ _
    have hh1 := abs_le.mp ((abs_ballCoord_snd_le (x : EuclideanSpace ℝ (Fin 3))).trans x.2)
    rw [hBv] at hm
    unfold modelBase at hm
    cases b
    · have hx' := hxf rfl
      have hwin := eq_of_window (len := len) (a := ((k : ℕ) : ℤ)) (b := ((j : ℕ) : ℤ)) (m := m)
        (x := xb) (y := -(ballCoord (x : EuclideanSpace ℝ (Fin 3))).2)
        (by push_cast; linarith) (by rw [abs_lt]; constructor <;> linarith)
      have : j = k := fin_eq_of_int_eq (m := -m) (by linarith)
      subst this
      exact ⟨x, by rw [rimBall_false]; exact hx⟩
    · have hx' := hxt rfl
      have hwin := eq_of_window (len := len) (a := ((k : ℕ) : ℤ) + 1) (b := ((j : ℕ) : ℤ))
        (m := m) (x := xb - 4) (y := -(ballCoord (x : EuclideanSpace ℝ (Fin 3))).2)
        (by push_cast; linarith) (by rw [abs_lt]; constructor <;> linarith)
      have : j = finRotate len k := eq_finRotate_of_int_eq (m := -m) (by linarith)
      subst this
      exact ⟨x, by rw [rimBall_true]; exact hx⟩
  · obtain ⟨j, q', hq'⟩ := Set.mem_iUnion.mp hp
    right
    obtain ⟨hz, hv, hU⟩ := modelHandle_height hε hε' j q'
    obtain ⟨-, m, hm⟩ := modelSphere_eq_shift hlen hz hPr.1 hq'
    rw [hxb, hv] at hm
    unfold modelBase at hm
    have hxr : 8 / 25 < xb ∧ xb < 92 / 25 := by
      cases b
      · have := hxf rfl; constructor <;> linarith
      · have := hxt rfl; constructor <;> linarith
    have hwin := eq_of_window (len := len) (a := ((k : ℕ) : ℤ)) (b := ((j : ℕ) : ℤ)) (m := m)
      (x := xb) (y := zoneHeight ‖(q'.1 : ModelPlane)‖ (q'.2 : ℝ))
      (by push_cast; linarith) (by rw [abs_lt]; constructor <;> linarith)
    have : j = k := fin_eq_of_int_eq (m := -m) (by linarith)
    subst this
    exact ⟨q', hq'⟩

/-! ## Disjoint balls and handles -/

theorem modelBall_disjoint (hlen : 0 < len) (hε : 0 < ε) (hε' : ε ≤ 1 / 8) :
    Pairwise fun j j' : Fin len => Disjoint (range (modelBall.{u} len ε j))
      (range (modelBall.{u} len ε j')) := by
  intro j j' hne
  rw [Set.disjoint_left]
  rintro p ⟨x, rfl⟩ ⟨x', hx'⟩
  apply hne
  have hBr := ballMap_range hε hε' (modelBase j) x
  have hBr' := ballMap_range hε hε' (modelBase j') x'
  obtain ⟨-, m, hm⟩ := modelSphere_eq_shift hlen (lt_of_le_of_lt hBr'.1 (by norm_num))
    (lt_of_le_of_lt hBr.1 (by norm_num)) hx'
  rw [ballMap_snd, ballMap_snd] at hm
  have hh1 := abs_le.mp ((abs_ballCoord_snd_le (x : EuclideanSpace ℝ (Fin 3))).trans x.2)
  have hh1' := abs_le.mp ((abs_ballCoord_snd_le (x' : EuclideanSpace ℝ (Fin 3))).trans x'.2)
  unfold modelBase at hm
  have hwin := eq_of_window (len := len) (a := ((j : ℕ) : ℤ)) (b := ((j' : ℕ) : ℤ)) (m := m)
    (x := -(ballCoord (x : EuclideanSpace ℝ (Fin 3))).2)
    (y := -(ballCoord (x' : EuclideanSpace ℝ (Fin 3))).2)
    (by push_cast; linarith) (by rw [abs_lt]; constructor <;> linarith)
  exact fin_eq_of_int_eq hwin

theorem modelHandle_disjoint (hlen : 0 < len) (hε : 0 < ε) (hε' : ε ≤ 1 / 8) :
    Pairwise fun j j' : Fin len => Disjoint (range (modelHandle.{u} len ε j))
      (range (modelHandle.{u} len ε j')) := by
  intro j j' hne
  rw [Set.disjoint_left]
  rintro p ⟨q, rfl⟩ ⟨q', hq'⟩
  apply hne
  obtain ⟨hz, hv, hU⟩ := modelHandle_height hε hε' j q
  obtain ⟨hz', hv', hU'⟩ := modelHandle_height hε hε' j' q'
  obtain ⟨-, m, hm⟩ := modelSphere_eq_shift hlen hz' hz hq'
  rw [hv, hv'] at hm
  unfold modelBase at hm
  have hwin := eq_of_window (len := len) (a := ((j : ℕ) : ℤ)) (b := ((j' : ℕ) : ℤ)) (m := m)
    (x := zoneHeight ‖(q.1 : ModelPlane)‖ (q.2 : ℝ))
    (y := zoneHeight ‖(q'.1 : ModelPlane)‖ (q'.2 : ℝ))
    (by push_cast; linarith) (by rw [abs_lt]; constructor <;> linarith)
  exact fin_eq_of_int_eq hwin

/-! ## Handles and balls -/

theorem handleEnd_mem_neckDomain_of_end (hε : 0 < ε) (b : Bool) {q : ClosedCell 2 × Icc (0 : ℝ) 1}
    (hq : q.2 = iccEnd b) : handleEnd b q ∈ neckDomain ε ∧ (handleEnd b q).2 = 0 := by
  have h1 : ‖(q.1 : ModelPlane)‖ ≤ 1 := q.1.2
  have hv : (q.2 : ℝ) = if b then 1 else 0 := by
    rw [hq]
    cases b <;> rfl
  have h0 : (handleEnd b q).2 = 0 := by
    simp only [handleEnd, endCoord]
    cases b <;> simp only [↓reduceIte, Bool.false_eq_true] at hv ⊢ <;> linarith
  refine ⟨⟨?_, ?_⟩, h0⟩
  · change ‖(q.1 : ModelPlane)‖ < 1 + 2 * ε
    linarith
  · rw [h0, abs_zero]
    linarith

theorem modelHandle_mem_range_ball_of_end (hlen : 0 < len) (hε : 0 < ε) (hε' : ε ≤ 1 / 8)
    (k : Fin len) (b : Bool) {q : ClosedCell 2 × Icc (0 : ℝ) 1} (hq : q.2 = iccEnd b) :
    modelHandle.{u} len ε k q ∈ range (modelBall.{u} len ε (rimBall len k b)) := by
  obtain ⟨hD, h0⟩ := handleEnd_mem_neckDomain_of_end hε b hq
  rw [modelHandle_end hlen hε hε' k b q]
  exact (modelNeck_mem_range_ball_iff hlen hε hε' k b hD).mpr h0.le

theorem modelHandle_ball_inter (hlen : 0 < len) (hε : 0 < ε) (hε' : ε ≤ 1 / 8) (k j : Fin len) :
    range (modelHandle.{u} len ε k) ∩ range (modelBall.{u} len ε j) =
      (if j = k then modelHandle.{u} len ε k '' {q | q.2 = iccEnd false} else ∅) ∪
        (if j = finRotate len k then modelHandle.{u} len ε k '' {q | q.2 = iccEnd true}
          else ∅) := by
  ext p
  constructor
  · rintro ⟨⟨q, rfl⟩, ⟨x, hx⟩⟩
    obtain ⟨hz, hv, hU⟩ := modelHandle_height hε hε' k q
    have hBr := ballMap_range hε hε' (modelBase j) x
    obtain ⟨hw, m, hm⟩ := modelSphere_eq_shift hlen (p := ballMap ε (modelBase j)
      (x : EuclideanSpace ℝ (Fin 3))) (lt_of_le_of_lt hBr.1 (by norm_num)) hz hx
    rw [hv, ballMap_snd] at hm
    set s := ‖(q.1 : ModelPlane)‖ with hs
    set t := (q.2 : ℝ) with ht
    set U := zoneHeight s t with hUdef
    set h := (ballCoord (x : EuclideanSpace ℝ (Fin 3))).2 with hh
    have hs1 : s ≤ 1 := q.1.2
    have hs0 : 0 ≤ s := norm_nonneg _
    have ht01 := q.2.2
    have habs : |s| < 2 := by rw [abs_of_nonneg hs0]; linarith
    have hq35 : 3 / 5 ≤ capCos s := by
      have := capCos_le_capCos hs0 hs1
      rw [capCos_one] at this
      exact this
    have hq1 := capCos_le_one s
    have hU0 : capCos s ≤ U := by
      have := (zoneHeight_strictMono habs).monotone ht01.1
      rw [zoneHeight_of_le (by norm_num), add_zero, one_mul] at this
      exact this
    have hU1 : U ≤ 4 - capCos s := by
      have := (zoneHeight_strictMono habs).monotone ht01.2
      rw [zoneHeight_of_ge (s := s) (t := 1) (by norm_num), sub_self, add_zero, one_mul] at this
      exact this
    have hh1 := abs_le.mp ((abs_ballCoord_snd_le (x : EuclideanSpace ℝ (Fin 3))).trans x.2)
    have hnormZ : ‖(zoneChartMap ε (modelBase k) (handleInclusion q)).1‖ = zoneRadius ε s U :=
      norm_zoneChartMap_fst hε hε' _ (handleInclusion_mem_zoneDomain q)
    have hnormB : ‖(ballMap ε (modelBase j) (x : EuclideanSpace ℝ (Fin 3))).1‖ =
        zoneRadius ε s U := by rw [hw, hnormZ]
    unfold modelBase at hm
    rcases le_or_gt U 2 with hU2 | hU2
    · have hwin := eq_of_window (len := len) (a := ((k : ℕ) : ℤ)) (b := ((j : ℕ) : ℤ)) (m := m)
        (x := U) (y := -h) (by push_cast; linarith) (by rw [abs_lt]; constructor <;> linarith)
      have hjk : j = k := fin_eq_of_int_eq (m := -m) (by linarith)
      subst hjk
      have hm0 : m = 0 := by
        have : ((len : ℤ) * m) = 0 := by linarith
        rcases mul_eq_zero.mp this with h0 | h0
        · omega
        · exact h0
      subst hm0
      have hUh : U = -h := by push_cast at hm; linarith
      rcases eq_or_lt_of_le ht01.1 with ht0 | ht0
      · left
        rw [ite_eq_left rfl]
        refine ⟨q, ?_, rfl⟩
        change q.2 = iccEnd false
        apply Subtype.ext
        rw [← ht0]
        rfl
      · exfalso
        have hUq : capCos s < U := by
          have := zoneHeight_lt habs ht0
          rw [zoneHeight_of_le (by norm_num), add_zero, one_mul] at this
          exact this
        obtain ⟨s₀, hs₀, hcs₀, hle⟩ := norm_ballMap_fst_le_sphere hε hε' (modelBase j) x
          (by rw [← hh, abs_of_neg (by linarith)]; linarith)
        rw [← hh, abs_of_neg (by linarith), ← hUh] at hcs₀
        have hlt : s₀ < s := by
          apply (capCos_lt_capCos_iff hs₀ hs0).mp
          rw [hcs₀]
          exact hUq
        have hz0 : zoneRadius ε s₀ U = neckRadius ε s₀ 0 := by
          rw [zoneRadius_eq_lower hε hε' hs₀ (by linarith) hU2 (by linarith), ← hcs₀,
            div_self (by linarith), sub_self]
        have := zoneRadius_lt (u := U) hε hε' hs₀ hlt (by linarith) (by linarith) (by linarith)
        linarith
    · have hwin := eq_of_window (len := len) (a := ((k : ℕ) : ℤ) + 1) (b := ((j : ℕ) : ℤ))
        (m := m) (x := U - 4) (y := -h) (by push_cast; linarith)
        (by rw [abs_lt]; constructor <;> linarith)
      have hjk : j = finRotate len k := eq_finRotate_of_int_eq (m := -m) (by linarith)
      have hUh : U - 4 = -h := by
        have h4 : (4 : ℝ) * ((k : ℕ) + 1) = 4 * (j : ℕ) + 4 * len * m := by
          have : (((k : ℕ) : ℤ) + 1 : ℤ) = (j : ℕ) + len * m := hwin
          have : ((k : ℕ) : ℝ) + 1 = (j : ℕ) + len * m := by exact_mod_cast this
          linarith
        linarith
      rcases eq_or_lt_of_le ht01.2 with ht1 | ht1
      · right
        rw [ite_eq_left hjk]
        refine ⟨q, ?_, rfl⟩
        change q.2 = iccEnd true
        apply Subtype.ext
        rw [ht1]
        rfl
      · exfalso
        have hUq : U < 4 - capCos s := by
          have := zoneHeight_lt habs ht1
          rw [zoneHeight_of_ge (s := s) (t := 1) (by norm_num), sub_self, add_zero, one_mul] at this
          exact this
        obtain ⟨s₀, hs₀, hcs₀, hle⟩ := norm_ballMap_fst_le_sphere hε hε' (modelBase j) x
          (by rw [← hh, abs_of_pos (by linarith)]; linarith)
        rw [← hh, abs_of_pos (by linarith)] at hcs₀
        have hlt : s₀ < s := by
          apply (capCos_lt_capCos_iff hs₀ hs0).mp
          rw [hcs₀]
          linarith
        have hz0 : zoneRadius ε s₀ U = neckRadius ε s₀ 0 := by
          rw [zoneRadius_eq_upper hε hε' hs₀ (by linarith) hU2.le (by linarith),
            show 4 - U = h by linarith, ← hcs₀, div_self (by linarith), sub_self]
        have := zoneRadius_lt (u := U) hε hε' hs₀ hlt (by linarith) (by linarith) (by linarith)
        linarith
  · rintro (hp | hp)
    · split_ifs at hp with hjk
      · obtain ⟨q, hq, rfl⟩ := hp
        refine ⟨⟨q, rfl⟩, ?_⟩
        have := modelHandle_mem_range_ball_of_end hlen hε hε' k false hq
        rw [rimBall_false] at this
        rw [hjk]
        exact this
      · exact hp.elim
    · split_ifs at hp with hjk
      · obtain ⟨q, hq, rfl⟩ := hp
        refine ⟨⟨q, rfl⟩, ?_⟩
        have := modelHandle_mem_range_ball_of_end hlen hε hε' k true hq
        rw [rimBall_true] at this
        rw [hjk]
        exact this
      · exact hp.elim

end GC.GraphManifold.Assembly
