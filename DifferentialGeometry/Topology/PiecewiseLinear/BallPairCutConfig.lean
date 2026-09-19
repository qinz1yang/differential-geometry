/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BallPairCutModel
import DifferentialGeometry.Topology.PiecewiseLinear.MidpointIndependence

/-!
# A cut model for gluing ball pairs
-/

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem linearIndependent_pair_of_det_ne_zero {u v : E} (φ ψ : E →ₗ[ℝ] ℝ)
    (h : φ u * ψ v - φ v * ψ u ≠ 0) : LinearIndependent ℝ ![u, v] := by
  rw [LinearIndependent.pair_iff]
  intro a b hab
  have h1 : a * φ u + b * φ v = 0 := by
    have hφ := congrArg φ hab
    simpa using hφ
  have h2 : a * ψ u + b * ψ v = 0 := by
    have hψ := congrArg ψ hab
    simpa using hψ
  have ha : a * (φ u * ψ v - φ v * ψ u) = 0 := by linear_combination ψ v * h1 - φ v * h2
  have hb : b * (φ u * ψ v - φ v * ψ u) = 0 := by linear_combination φ u * h2 - ψ u * h1
  exact ⟨(mul_eq_zero.mp ha).resolve_right h, (mul_eq_zero.mp hb).resolve_right h⟩

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem sum_triple_insert [DecidableEq E] {M : Type*} [AddCommMonoid M] {a b c : E}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (f : E → M) :
    ∑ v ∈ ({a, b, c} : Finset E), f v = f a + (f b + f c) := by
  rw [Finset.sum_insert (by simp [hab, hac]), Finset.sum_insert (by simp [hbc]),
    Finset.sum_singleton]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem sum_quadruple_insert [DecidableEq E] {M : Type*} [AddCommMonoid M] {a b c e : E}
    (hab : a ≠ b) (hac : a ≠ c) (hae : a ≠ e) (hbc : b ≠ c) (hbe : b ≠ e) (hce : c ≠ e)
    (f : E → M) :
    ∑ v ∈ ({a, b, c, e} : Finset E), f v = f a + (f b + (f c + f e)) := by
  rw [Finset.sum_insert (by simp [hab, hac, hae]), Finset.sum_insert (by simp [hbc, hbe]),
    Finset.sum_insert (by simp [hce]), Finset.sum_singleton]

theorem mem_openSimplex_triple [DecidableEq E] {a b c x : E} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) {w₁ w₂ w₃ : ℝ} (h₁ : 0 < w₁) (h₂ : 0 < w₂) (h₃ : 0 < w₃)
    (hsum : w₁ + w₂ + w₃ = 1) (hx : w₁ • a + w₂ • b + w₃ • c = x) :
    x ∈ openSimplex ({a, b, c} : Finset E) := by
  obtain ⟨w, wa, wb, wc⟩ : ∃ w : E → ℝ, w a = w₁ ∧ w b = w₂ ∧ w c = w₃ :=
    ⟨fun v => if v = a then w₁ else if v = b then w₂ else w₃, by simp,
      by simp [Ne.symm hab], by simp [Ne.symm hac, Ne.symm hbc]⟩
  refine ⟨w, ?_, ?_, ?_⟩
  · intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · rw [wa]; exact h₁
    · rw [wb]; exact h₂
    · rw [wc]; exact h₃
  · rw [sum_triple_insert hab hac hbc w, wa, wb, wc]
    linarith
  · rw [sum_triple_insert hab hac hbc (fun v => w v • v)]
    simp only [wa, wb, wc]
    rw [← hx]
    abel

theorem mem_openSimplex_quadruple [DecidableEq E] {a b c e x : E} (hab : a ≠ b) (hac : a ≠ c)
    (hae : a ≠ e) (hbc : b ≠ c) (hbe : b ≠ e) (hce : c ≠ e)
    {w₁ w₂ w₃ w₄ : ℝ} (h₁ : 0 < w₁) (h₂ : 0 < w₂) (h₃ : 0 < w₃) (h₄ : 0 < w₄)
    (hsum : w₁ + w₂ + w₃ + w₄ = 1) (hx : w₁ • a + w₂ • b + w₃ • c + w₄ • e = x) :
    x ∈ openSimplex ({a, b, c, e} : Finset E) := by
  obtain ⟨w, wa, wb, wc, we⟩ : ∃ w : E → ℝ, w a = w₁ ∧ w b = w₂ ∧ w c = w₃ ∧ w e = w₄ :=
    ⟨fun v => if v = a then w₁ else if v = b then w₂ else if v = c then w₃ else w₄, by simp,
      by simp [Ne.symm hab], by simp [Ne.symm hac, Ne.symm hbc],
      by simp [Ne.symm hae, Ne.symm hbe, Ne.symm hce]⟩
  refine ⟨w, ?_, ?_, ?_⟩
  · intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · rw [wa]; exact h₁
    · rw [wb]; exact h₂
    · rw [wc]; exact h₃
    · rw [we]; exact h₄
  · rw [sum_quadruple_insert hab hac hae hbc hbe hce w, wa, wb, wc, we]
    linarith
  · rw [sum_quadruple_insert hab hac hae hbc hbe hce (fun v => w v • v)]
    simp only [wa, wb, wc, we]
    rw [← hx]
    abel

theorem coneSet_simplexBoundary_space {T : Finset E}
    (hT : AffineIndependent ℝ ((↑) : T → E)) (hcard : 2 ≤ T.card) {p : E}
    (hp : p ∈ openSimplex T) :
    coneSet p (simplexBoundary T hT).space = convexHull ℝ (T : Set E) := by
  classical
  rw [← coneComplex_space_eq_coneSet (isConeBase_simplexBoundary hT hcard hp),
    coneComplex_simplexBoundary_space hT hcard hp]

theorem exists_cutModel_data [FiniteDimensional ℝ E] (hn : Module.finrank ℝ E = 3) :
    ∃ (p₁ p₂ z y₁ y₂ : E) (L₁ L₂ L₀ L : Geometry.SimplicialComplex ℝ E),
      L₁.faces.Finite ∧ L₂.faces.Finite ∧ L₀.faces.Finite ∧
      IsConeBase p₁ L₁ ∧ IsConeBase p₂ L₂ ∧ IsConeBase z L₀ ∧
      IsPLSphere 2 L₁.space ∧ IsPLSphere 2 L₂.space ∧ IsPLSphere 1 L₀.space ∧
      coneSet z L₀.space ⊆ L₁.space ∧ coneSet z L₀.space ⊆ L₂.space ∧
      y₁ ∈ L₁.space ∧ y₁ ∉ coneSet z L₀.space ∧
      y₂ ∈ L₂.space ∧ y₂ ∉ coneSet z L₀.space ∧
      coneSet p₁ L₁.space ∩ coneSet p₂ L₂.space = coneSet z L₀.space ∧
      coneSet p₁ L₁.space ∩ (coneSet p₁ ({z, y₁} : Set E) ∪ coneSet p₂ ({z, y₂} : Set E)) =
        coneSet p₁ ({z, y₁} : Set E) ∧
      coneSet p₂ L₂.space ∩ (coneSet p₁ ({z, y₁} : Set E) ∪ coneSet p₂ ({z, y₂} : Set E)) =
        coneSet p₂ ({z, y₂} : Set E) ∧
      coneSet z L₀.space ∩ (coneSet p₁ ({z, y₁} : Set E) ∪ coneSet p₂ ({z, y₂} : Set E)) = {z} ∧
      IsPLBallPair 2 1 (coneSet p₁ L₁.space) (coneSet p₁ ({z, y₁} : Set E)) ∧
      IsPLBallPair 2 1 (coneSet p₂ L₂.space) (coneSet p₂ ({z, y₂} : Set E)) ∧
      IsPLBallPair 1 0 (coneSet z L₀.space) {z} ∧
      IsPLBallPair 2 1 (coneSet p₁ L₁.space ∪ coneSet p₂ L₂.space)
        (coneSet p₁ ({z, y₁} : Set E) ∪ coneSet p₂ ({z, y₂} : Set E)) ∧
      L.faces.Finite ∧ IsConeBase p₁ L ∧ IsPLSphere 2 L.space ∧
      coneSet p₁ L.space = coneSet p₁ L₁.space ∪ coneSet p₂ L₂.space ∧
      coneSet p₁ ({y₁, y₂} : Set E) =
        coneSet p₁ ({z, y₁} : Set E) ∪ coneSet p₂ ({z, y₂} : Set E) ∧
      y₁ ∈ L.space ∧ y₂ ∈ L.space ∧
      L₂.space ⊆ L.space ∪ coneSet z L₀.space := by
  classical
  obtain ⟨T, hT, hTcard, -, -, -⟩ :=
    exists_affineIndependent_openSimplex_subset (E := E) (n := 2) (by rw [hn]) (0 : E)
      (U := Set.univ) Filter.univ_mem
  obtain ⟨c, m, A, B, hcm, hcA, hcB, hmA, hmB, hAB, hTeq⟩ :=
    Finset.card_eq_four.mp (by omega : T.card = 4)
  subst hTeq
  obtain ⟨d, hd⟩ : ∃ d : E, d = m + m - c := ⟨_, rfl⟩
  obtain ⟨z, hzdef⟩ : ∃ z : E, z = (3 : ℝ)⁻¹ • (m + A + B) := ⟨_, rfl⟩
  obtain ⟨p, hpdef⟩ : ∃ p : E,
      p = (10 : ℝ)⁻¹ • c + (6 : ℝ)⁻¹ • m + (11 / 30 : ℝ) • A + (11 / 30 : ℝ) • B := ⟨_, rfl⟩
  obtain ⟨q, hqdef⟩ : ∃ q : E, q = (2 : ℝ)⁻¹ • (z + d) := ⟨_, rfl⟩
  have hm : c + d = m + m := by rw [hd]; abel
  have hcS : c ∉ ({m, A, B} : Finset E) := by simp [hcm, hcA, hcB]
  obtain ⟨ℓ, r, hℓS, hℓc, hℓd⟩ :=
    exists_linearMap_separating_midpoint (S := ({m, A, B} : Finset E)) (c := c) (d := d)
      (m := m) hT hcS (by simp) hm
  obtain ⟨ν, s, hν⟩ :=
    exists_linearMap_eq_add_const hT (fun v => if v = A then (1 : ℝ) else 0)
  have hℓm : ℓ m = r := hℓS m (by simp)
  have hℓA : ℓ A = r := hℓS A (by simp)
  have hℓB : ℓ B = r := hℓS B (by simp)
  have hνc : ν c = s := by rw [hν c (by simp), if_neg hcA]; ring
  have hνm : ν m = s := by rw [hν m (by simp), if_neg hmA]; ring
  have hνA : ν A = s + 1 := by rw [hν A (by simp), if_pos rfl]
  have hνB : ν B = s := by rw [hν B (by simp), if_neg (Ne.symm hAB)]; ring
  have hνd : ν d = s := by rw [hd, map_sub, map_add, hνm, hνc]; ring
  have hℓz : ℓ z = r := by
    rw [hzdef]
    simp only [map_smul, map_add, smul_eq_mul, hℓm, hℓA, hℓB]
    ring
  have hνz : ν z = s + 1 / 3 := by
    rw [hzdef]
    simp only [map_smul, map_add, smul_eq_mul, hνm, hνA, hνB]
    ring
  have hℓp : ℓ p = r - 1 / 10 := by
    rw [hpdef]
    simp only [map_smul, map_add, smul_eq_mul, hℓc, hℓm, hℓA, hℓB]
    ring
  have hνp : ν p = s + 11 / 30 := by
    rw [hpdef]
    simp only [map_smul, map_add, smul_eq_mul, hνc, hνm, hνA, hνB]
    ring
  have hℓq : ℓ q = r + 1 / 2 := by
    rw [hqdef]
    simp only [map_smul, map_add, smul_eq_mul, hℓz, hℓd]
    ring
  have hne : ∀ {x y : E}, ℓ x ≠ ℓ y → x ≠ y := by
    intro x y h hxy
    exact h (by rw [hxy])
  have hcd : c ≠ d := hne (by rw [hℓc, hℓd]; intro h; linarith)
  have hdm : d ≠ m := hne (by rw [hℓd, hℓm]; intro h; linarith)
  have hdA : d ≠ A := hne (by rw [hℓd, hℓA]; intro h; linarith)
  have hdB : d ≠ B := hne (by rw [hℓd, hℓB]; intro h; linarith)
  have hpc : p ≠ c := hne (by rw [hℓp, hℓc]; intro h; linarith)
  have hpd : p ≠ d := hne (by rw [hℓp, hℓd]; intro h; linarith)
  have hpz : p ≠ z := hne (by rw [hℓp, hℓz]; intro h; linarith)
  have hcz : c ≠ z := hne (by rw [hℓc, hℓz]; intro h; linarith)
  have hzd : z ≠ d := hne (by rw [hℓz, hℓd]; intro h; linarith)
  have hqz : q ≠ z := hne (by rw [hℓq, hℓz]; intro h; linarith)
  have hqd : q ≠ d := hne (by rw [hℓq, hℓd]; intro h; linarith)
  have hFcard : ({A, B} : Finset E).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simp [hAB]), Finset.card_singleton]
  have hcdF : c ∉ ({d, A, B} : Finset E) := by simp [hcd, hcA, hcB]
  have hdF : d ∉ ({A, B} : Finset E) := by simp [hdA, hdB]
  have hcmF : c ∉ ({m, A, B} : Finset E) := hcS
  have hdmF : d ∉ ({m, A, B} : Finset E) := by simp [hdm, hdA, hdB]
  have hmF : m ∉ ({A, B} : Finset E) := by simp [hmA, hmB]
  have hmcF : m ∉ ({c, A, B} : Finset E) := by simp [Ne.symm hcm, hmA, hmB]
  have hdcF : d ∉ ({c, A, B} : Finset E) := by simp [Ne.symm hcd, hdA, hdB]
  have hTout : AffineIndependent ℝ ((↑) : ↥({c, d, A, B} : Finset E) → E) :=
    affineIndependent_insert_midpoint_outer hT hm hmcF hdcF
  have hTin : AffineIndependent ℝ ((↑) : ↥({d, m, A, B} : Finset E) → E) :=
    affineIndependent_insert_midpoint_inner hT hm hcmF hdmF
  have hFm : AffineIndependent ℝ ((↑) : ↥({m, A, B} : Finset E) → E) :=
    affineIndependent_of_subset hT (Finset.subset_insert c _)
  have hz : z ∈ openSimplex ({m, A, B} : Finset E) :=
    mem_openSimplex_triple hmA hmB hAB (w₁ := 1 / 3) (w₂ := 1 / 3) (w₃ := 1 / 3) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by rw [hzdef]; module)
  have hp₁ : p ∈ openSimplex ({c, m, A, B} : Finset E) :=
    mem_openSimplex_quadruple hcm hcA hcB hmA hmB hAB (w₁ := (10 : ℝ)⁻¹) (w₂ := (6 : ℝ)⁻¹)
      (w₃ := 11 / 30) (w₄ := 11 / 30) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by rw [hpdef])
  have hp : p ∈ openSimplex ({c, d, A, B} : Finset E) :=
    mem_openSimplex_quadruple hcd hcA hcB hdA hdB hAB (w₁ := 11 / 60) (w₂ := 1 / 12)
      (w₃ := 11 / 30) (w₄ := 11 / 30) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by rw [hd, hpdef]; module)
  have hq : q ∈ openSimplex ({d, m, A, B} : Finset E) :=
    mem_openSimplex_quadruple hdm hdA hdB hmA hmB hAB (w₁ := 1 / 2) (w₂ := 1 / 6)
      (w₃ := 1 / 6) (w₄ := 1 / 6) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by rw [hqdef, hzdef]; module)
  have hzs : z ∈ segment ℝ p d :=
    ⟨10 / 11, 1 / 11, by norm_num, by norm_num, by norm_num, by rw [hpdef, hd, hzdef]; module⟩
  have hqs : q ∈ segment ℝ z d :=
    ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, by rw [hqdef]; module⟩
  have hqopen : q ∈ openSegment ℝ z d :=
    ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, by rw [hqdef]; module⟩
  have hrad : IsRadiallyInjective p ({c, d} : Set E) := by
    refine isRadiallyInjective_pair_of_linearIndependent
      (linearIndependent_pair_of_det_ne_zero ℓ ν ?_)
    have hval : ℓ (c - p) * ν (d - p) - ℓ (d - p) * ν (c - p) = 11 / 15 := by
      simp only [map_sub, hℓc, hℓp, hℓd, hνc, hνp, hνd]
      ring
    rw [hval]
    norm_num
  have hrad₁ : IsRadiallyInjective p ({c, z} : Set E) := by
    refine isRadiallyInjective_pair_of_linearIndependent
      (linearIndependent_pair_of_det_ne_zero ℓ ν ?_)
    have hval : ℓ (c - p) * ν (z - p) - ℓ (z - p) * ν (c - p) = 1 / 15 := by
      simp only [map_sub, hℓc, hℓp, hℓz, hνc, hνp, hνz]
      ring
    rw [hval]
    norm_num
  have hrad₂ : IsRadiallyInjective q ({z, d} : Set E) :=
    isRadiallyInjective_pair_of_mem_openSegment hzd hqopen
  have hℓclt : ℓ c < r := by rw [hℓc]; linarith
  have hℓdgt : r < ℓ d := by rw [hℓd]; linarith
  have hℓplt : ℓ p < r := by rw [hℓp]; linarith
  have hleft := isPLBallPair_cut_left hFcard hcmF hmF hT hℓS hℓclt hℓdgt hz hzs hp₁ hcz hpc hpz
    hrad₁
  have hright := isPLBallPair_cut_right hFcard hdmF hmF hTin hℓS hℓclt hℓdgt hℓplt hz hzs hq hqs
    hzd hqz hqd hrad₂
  have hface := isPLBallPair_cut_face (c := c) (d := d) (p := p) hFcard hmF hℓS hℓclt hℓdgt hℓplt
    hz hzs hFm
  have hunion := isPLBallPair_cut_union hFcard hcdF hdF hTout hp hcd hpc hpd hrad
  have hcut : convexHull ℝ ((({c, m, A, B} : Finset E)) : Set E) ∪
      convexHull ℝ ((({d, m, A, B} : Finset E)) : Set E) =
      convexHull ℝ ((({c, d, A, B} : Finset E)) : Set E) :=
    convexHull_cut_union hcdF hdF hcmF hdmF hmF hm
  have hinter : convexHull ℝ ((({c, m, A, B} : Finset E)) : Set E) ∩
      convexHull ℝ ((({d, m, A, B} : Finset E)) : Set E) =
      convexHull ℝ ((({m, A, B} : Finset E)) : Set E) :=
    convexHull_cut_inter hℓS hℓclt hℓdgt
  have hcard₁ : ({c, m, A, B} : Finset E).card = 2 + 2 := by
    rw [Finset.card_insert_of_notMem hcmF, Finset.card_insert_of_notMem hmF, hFcard]
  have hcard₂ : ({d, m, A, B} : Finset E).card = 2 + 2 := by
    rw [Finset.card_insert_of_notMem hdmF, Finset.card_insert_of_notMem hmF, hFcard]
  have hcard₀ : ({m, A, B} : Finset E).card = 1 + 2 := by
    rw [Finset.card_insert_of_notMem hmF, hFcard]
  have hcard : ({c, d, A, B} : Finset E).card = 2 + 2 := by
    rw [Finset.card_insert_of_notMem hcdF, Finset.card_insert_of_notMem hdF, hFcard]
  have h2₁ : 2 ≤ ({c, m, A, B} : Finset E).card := by omega
  have h2₂ : 2 ≤ ({d, m, A, B} : Finset E).card := by omega
  have h2₀ : 2 ≤ ({m, A, B} : Finset E).card := by omega
  have h2 : 2 ≤ ({c, d, A, B} : Finset E).card := by omega
  have hcone₁ := coneSet_simplexBoundary_space hT h2₁ hp₁
  have hcone₂ := coneSet_simplexBoundary_space hTin h2₂ hq
  have hcone₀ := coneSet_simplexBoundary_space hFm h2₀ hz
  have hcone := coneSet_simplexBoundary_space hTout h2 hp
  have hA₁ : coneSet p ({z, c} : Set E) = segment ℝ p c ∪ segment ℝ p z := by
    rw [coneSet_pair_eq_union_segment, Set.union_comm]
  have hA₂ : coneSet q ({z, d} : Set E) = segment ℝ z d := by
    rw [coneSet_pair_eq_union_segment, segment_union_segment_of_mem_segment hqs]
  have harc : coneSet p ({z, c} : Set E) ∪ coneSet q ({z, d} : Set E) =
      segment ℝ p c ∪ segment ℝ p d := by
    rw [hA₁, hA₂, ← hleft.2, ← hright.2, ← Set.union_inter_distrib_right, hcut,
      Set.inter_eq_right.mpr hunion.subset]
  have hFmplane : convexHull ℝ ((({m, A, B} : Finset E)) : Set E) ⊆ {x : E | ℓ x = r} :=
    convexHull_min (fun v hv => hℓS v (Finset.mem_coe.mp hv)) (convex_hyperplane ℓ.isLinear r)
  have hcFm : c ∉ convexHull ℝ ((({m, A, B} : Finset E)) : Set E) := by
    intro hmem
    have hval : ℓ c = r := hFmplane hmem
    rw [hℓc] at hval
    linarith
  have hdFm : d ∉ convexHull ℝ ((({m, A, B} : Finset E)) : Set E) := by
    intro hmem
    have hval : ℓ d = r := hFmplane hmem
    rw [hℓd] at hval
    linarith
  have hFmsub₁ : convexHull ℝ ((({m, A, B} : Finset E)) : Set E) ⊆
      (simplexBoundary ({c, m, A, B} : Finset E) hT).space := fun x hx =>
    (simplexBoundary _ hT).convexHull_subset_space
      (mem_simplexBoundary_faces_iff.mpr ⟨Finset.subset_insert c _,
        ⟨m, Finset.mem_insert_self m _⟩, fun h => hcmF (h ▸ Finset.mem_insert_self c _)⟩) hx
  have hFmsub₂ : convexHull ℝ ((({m, A, B} : Finset E)) : Set E) ⊆
      (simplexBoundary ({d, m, A, B} : Finset E) hTin).space := fun x hx =>
    (simplexBoundary _ hTin).convexHull_subset_space
      (mem_simplexBoundary_faces_iff.mpr ⟨Finset.subset_insert d _,
        ⟨m, Finset.mem_insert_self m _⟩, fun h => hdmF (h ▸ Finset.mem_insert_self d _)⟩) hx
  have hmseg : m ∈ segment ℝ c d :=
    ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, by rw [hd]; module⟩
  have hfacetA :
      convexHull ℝ ((({d, m, A, B} : Finset E).erase A : Finset E) : Set E) ⊆
        convexHull ℝ ((({c, d, A, B} : Finset E).erase A : Finset E) : Set E) := by
    apply convexHull_min
    · intro v hv
      simp only [Finset.mem_coe, Finset.mem_erase, Finset.mem_insert,
        Finset.mem_singleton] at hv
      rcases hv.2 with hvd | hvm | hvA | hvB
      · subst v
        exact subset_convexHull ℝ _ (by simp [hdA])
      · subst v
        exact (convex_convexHull ℝ _).segment_subset
          (subset_convexHull ℝ _ (by simp [hcA]))
          (subset_convexHull ℝ _ (by simp [hdA])) hmseg
      · exact (hv.1 hvA).elim
      · subst v
        exact subset_convexHull ℝ _ (by simp [Ne.symm hAB])
    · exact convex_convexHull ℝ _
  have hfacetB :
      convexHull ℝ ((({d, m, A, B} : Finset E).erase B : Finset E) : Set E) ⊆
        convexHull ℝ ((({c, d, A, B} : Finset E).erase B : Finset E) : Set E) := by
    apply convexHull_min
    · intro v hv
      simp only [Finset.mem_coe, Finset.mem_erase, Finset.mem_insert,
        Finset.mem_singleton] at hv
      rcases hv.2 with hvd | hvm | hvA | hvB
      · subst v
        exact subset_convexHull ℝ _ (by simp [hdB])
      · subst v
        exact (convex_convexHull ℝ _).segment_subset
          (subset_convexHull ℝ _ (by simp [hcB]))
          (subset_convexHull ℝ _ (by simp [hdB])) hmseg
      · subst v
        exact subset_convexHull ℝ _ (by simp [hAB])
      · exact (hv.1 hvB).elim
    · exact convex_convexHull ℝ _
  have hL₂sub : (simplexBoundary ({d, m, A, B} : Finset E) hTin).space ⊆
      (simplexBoundary ({c, d, A, B} : Finset E) hTout).space ∪
        coneSet z (simplexBoundary ({m, A, B} : Finset E) hFm).space := by
    rw [simplexBoundary_space _ hTin h2₂, simplexBoundary_space _ hTout h2, hcone₀]
    intro x hx
    obtain ⟨v, hv, hxv⟩ := Set.mem_iUnion₂.mp hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with hvd | hvm | hvA | hvB
    · subst v
      exact Or.inr
        (by simpa [hcd, hcm, hcA, hcB, hdm, hdA, hdB, hmA, hmB, hAB] using hxv)
    · subst v
      refine Or.inl (Set.mem_iUnion₂.mpr ⟨c, by simp, ?_⟩)
      have herase : ({d, m, A, B} : Finset E).erase m =
          ({c, d, A, B} : Finset E).erase c := by
        calc
          ({d, m, A, B} : Finset E).erase m =
              insert d (({m, A, B} : Finset E).erase m) :=
            Finset.erase_insert_of_ne hdm
          _ = {d, A, B} := by rw [Finset.erase_insert hmF]
          _ = ({c, d, A, B} : Finset E).erase c := (Finset.erase_insert hcdF).symm
      rw [herase] at hxv
      exact hxv
    · subst v
      exact Or.inl (Set.mem_iUnion₂.mpr ⟨A, by simp, hfacetA hxv⟩)
    · subst v
      exact Or.inl (Set.mem_iUnion₂.mpr ⟨B, by simp, hfacetB hxv⟩)
  refine ⟨p, q, z, c, d, simplexBoundary ({c, m, A, B} : Finset E) hT,
    simplexBoundary ({d, m, A, B} : Finset E) hTin, simplexBoundary ({m, A, B} : Finset E) hFm,
    simplexBoundary ({c, d, A, B} : Finset E) hTout,
    simplexBoundary_faces_finite _ hT, simplexBoundary_faces_finite _ hTin,
    simplexBoundary_faces_finite _ hFm, isConeBase_simplexBoundary hT h2₁ hp₁,
    isConeBase_simplexBoundary hTin h2₂ hq, isConeBase_simplexBoundary hFm h2₀ hz, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  · rw [simplexBoundary_space _ hT h2₁]
    exact isPLSphere_biUnion_erase _ hT hcard₁
  · rw [simplexBoundary_space _ hTin h2₂]
    exact isPLSphere_biUnion_erase _ hTin hcard₂
  · rw [simplexBoundary_space _ hFm h2₀]
    exact isPLSphere_biUnion_erase _ hFm hcard₀
  · rw [hcone₀]
    exact hFmsub₁
  · rw [hcone₀]
    exact hFmsub₂
  · exact vertex_mem_simplexBoundary_space hT (by simp) h2₁
  · rw [hcone₀]
    exact hcFm
  · exact vertex_mem_simplexBoundary_space hTin (by simp) h2₂
  · rw [hcone₀]
    exact hdFm
  · rw [hcone₁, hcone₂, hcone₀]
    exact hinter
  · rw [hcone₁, harc, hA₁]
    exact hleft.2
  · rw [hcone₂, harc, hA₂]
    exact hright.2
  · rw [hcone₀, harc]
    exact hface.2
  · rw [hcone₁, hA₁]
    exact hleft.1
  · rw [hcone₂, hA₂]
    exact hright.1
  · rw [hcone₀]
    exact hface.1
  · rw [hcone₁, hcone₂, harc, hcut]
    exact hunion
  · exact simplexBoundary_faces_finite _ hTout
  · exact isConeBase_simplexBoundary hTout h2 hp
  · rw [simplexBoundary_space _ hTout h2]
    exact isPLSphere_biUnion_erase _ hTout hcard
  · rw [hcone, hcone₁, hcone₂]
    exact hcut.symm
  · rw [coneSet_pair_eq_union_segment, harc]
  · exact vertex_mem_simplexBoundary_space hTout (by simp) h2
  · exact vertex_mem_simplexBoundary_space hTout (by simp) h2
  · exact hL₂sub

theorem exists_isPLBallPair_cut_model [FiniteDimensional ℝ E] (hn : Module.finrank ℝ E = 3) :
    ∃ (C₁ C₂ arc : Set E) (z : E),
      IsPLBallPair 2 1 (C₁ ∪ C₂) arc ∧
      IsPLBallPair 2 1 C₁ (C₁ ∩ arc) ∧
      IsPLBallPair 2 1 C₂ (C₂ ∩ arc) ∧
      IsPLBallPair 1 0 (C₁ ∩ C₂) {z} ∧
      C₁ ∩ C₂ ∩ arc = {z} := by
  obtain ⟨p₁, p₂, z, y₁, y₂, L₁, L₂, L₀, L, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    hmeet, hI₁, hI₂, hI₀, hpair₁, hpair₂, hpair₀, hpair, -, -, -, -, -, -, -, -⟩ :=
    exists_cutModel_data hn
  refine ⟨coneSet p₁ L₁.space, coneSet p₂ L₂.space,
    coneSet p₁ ({z, y₁} : Set E) ∪ coneSet p₂ ({z, y₂} : Set E), z, hpair, ?_, ?_, ?_, ?_⟩
  · rw [hI₁]
    exact hpair₁
  · rw [hI₂]
    exact hpair₂
  · rw [hmeet]
    exact hpair₀
  · rw [hmeet]
    exact hI₀

end DifferentialGeometry.Topology.PiecewiseLinear
