import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTriangleGeometryOuterSeam

/-!
# The closed punctured chart of a closed triangle block

Lane B3 (design `docs/geometrization/handoffs/20261004-design-b3-closed-triangle-assembly.md`,
§1). For charts `C` of a block with an outer filling `m` (hole `0`), `C.outerSeamInv m` is the full
inverse of X13's outer seam model (`seamModel_eq_outerSeamDir`), and on
`outerCollarRadius m < |u| < 3` the tube composed with it is the product chart
(`tubeMap_outerSeamInv`). For a closed triangle block (no port, three cones, cone `j` at hole `j`)
the closed punctured chart `C.closedChart hc h3 : ℂ × S¹ → W.pieceInterior ⊤` is the product chart
on `planarOpen 3`, `tube ∘ seamInv` on the punctured inner collars about `± 3/2` and
`tube ∘ outerSeamInv` on the outer collar `outerCollarRadius < |u| < 7/2`
(`closedChart_of_innerCollar`, `closedChart_of_outerCollar`); on
`closedDomain = {|u| < 7/2, u ≠ ± 3/2} × S¹` it is a local diffeomorphism
(`isLocalDiffeomorphAt_closedChart`), injective (`closedChart_injOn`), never on a core circle
`tube m (0, w)` (`closedChart_ne_tubeMap_zero`), and every point of the block is in its image or on
a core circle (`exists_closedChart_eq`). The virtual annulus `3 ≤ |u| < 7/2` is reached only
through the outer tube.
-/

set_option autoImplicit false

noncomputable section
open Set
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Geometry
open scoped Manifold ContDiff Topology ComplexConjugate

universe u

namespace GC.Seifert

variable {W : CompactCarrier.{u}} {d : SeifertData}

def closedDomain : Set (ℂ × Circle) := {y | ‖y.1‖ < 7 / 2 ∧ y.1 ≠ 3 / 2 ∧ y.1 ≠ -(3 / 2)}

namespace SeifertBlockCharts

variable (C : SeifertBlockCharts W d)

section OuterCollar

def outerSeamInv (m : Fin d.fillingCount) : ℂ × Circle → ℂ × Circle :=
  outerBwd (d.fillingOrder m) (d.fillingSlope m).1 (d.fillingSlope m).2 (C.a m) (C.b m)

def outerSeamDir (m : Fin d.fillingCount) : ℂ × Circle → ℂ × Circle :=
  outerFwd (d.fillingOrder m) (d.fillingSlope m).1 (d.fillingSlope m).2 (C.a m) (C.b m)

def outerCollarRadius (m : Fin d.fillingCount) : ℝ :=
  max (7 / 2 - (1 + C.ε) ^ d.fillingOrder m / 2) (5 / 2)

variable {m : Fin d.fillingCount} (hj0 : (C.port (.inr m)).val = 0)
  (hp : 0 < (d.fillingSlope m).1)

include hj0 in
theorem seamModel_eq_outerSeamDir :
    seamModel d m (C.port (.inr m)) (C.matrix m) = C.outerSeamDir m := by
  funext y
  have hA := C.matrix_eq m
  have h00 : (C.matrix m : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = -(d.fillingSlope m).1 := by
    rw [hA]; rfl
  have h01 : (C.matrix m : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = C.a m := by rw [hA]; rfl
  have h10 : (C.matrix m : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = -(d.fillingSlope m).2 := by
    rw [hA]; rfl
  have h11 : (C.matrix m : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = C.b m := by rw [hA]; rfl
  have hrad : planarRadius (C.port (.inr m)) = 3 := by simp [planarRadius, hj0]
  have hcen : planarCenter d.k (C.port (.inr m)) = 0 := by
    simp [planarCenter, hj0]
  apply Prod.ext
  · simp only [seamModel, linearTorusMap, h00, h01, hrad, hcen, hj0, ite_true, outerSeamDir,
      outerFwd, SeifertData.fillingOrder]
    push_cast
    ring
  · simp only [seamModel, linearTorusMap, h10, h11, outerSeamDir, outerFwd]

include hp in
theorem outerSeamDir_outerSeamInv {y : ℂ × Circle} (hy : ‖y.1‖ < 7 / 2) :
    C.outerSeamDir m (C.outerSeamInv m y) = y :=
  outerFwd_outerBwd (fillingOrder_pos hp).ne' (C.bezout m) hy

include hp in
theorem outerSeamInv_outerSeamDir {y : ℂ × Circle} (hy : ‖y.1‖ ^ d.fillingOrder m < 7) :
    C.outerSeamInv m (C.outerSeamDir m y) = y :=
  outerBwd_outerFwd (fillingOrder_pos hp).ne' (C.bezout m) hy

theorem five_halves_le_outerCollarRadius : 5 / 2 ≤ C.outerCollarRadius m := le_max_right _ _

include hp in
theorem outerCollarRadius_lt_three : C.outerCollarRadius m < 3 := by
  unfold outerCollarRadius
  apply max_lt _ (by norm_num)
  have h1 : 1 < (1 + C.ε) ^ d.fillingOrder m :=
    one_lt_pow₀ (by linarith [C.ε_pos]) (fillingOrder_pos hp).ne'
  linarith

theorem norm_outerSeamInv_fst {y : ℂ × Circle} (hy : ‖y.1‖ < 7 / 2) :
    ‖(C.outerSeamInv m y).1‖ = (7 - 2 * ‖y.1‖) ^ ((d.fillingOrder m : ℝ)⁻¹) :=
  norm_outerBwd_fst hy

include hp in
theorem norm_outerSeamInv_lt_of_collar {y : ℂ × Circle} (h1 : C.outerCollarRadius m < ‖y.1‖)
    (h2 : ‖y.1‖ < 7 / 2) : ‖(C.outerSeamInv m y).1‖ < 1 + C.ε := by
  rw [C.norm_outerSeamInv_fst h2]
  have hP : (0 : ℝ) < d.fillingOrder m := by exact_mod_cast fillingOrder_pos hp
  have h0 : 0 ≤ 7 - 2 * ‖y.1‖ := by linarith
  rw [Real.rpow_inv_lt_iff_of_pos h0 (by linarith [C.ε_pos]) hP, Real.rpow_natCast]
  have := le_max_left (7 / 2 - (1 + C.ε) ^ d.fillingOrder m / 2) (5 / 2)
  change _ ≤ C.outerCollarRadius m at this
  linarith

include hp in
theorem one_lt_norm_outerSeamInv {y : ℂ × Circle} (h : ‖y.1‖ < 3) :
    1 < ‖(C.outerSeamInv m y).1‖ := by
  rw [C.norm_outerSeamInv_fst (by linarith)]
  have hP : (0 : ℝ) < d.fillingOrder m := by exact_mod_cast fillingOrder_pos hp
  have h0 : 0 ≤ 7 - 2 * ‖y.1‖ := by linarith
  rw [Real.lt_rpow_inv_iff_of_pos zero_le_one h0 hP, Real.one_rpow]
  linarith

include hj0 hp in
theorem tubeMap_outerSeamInv {y : ℂ × Circle} (h1 : C.outerCollarRadius m < ‖y.1‖)
    (h2 : ‖y.1‖ < 3) (hy : y.1 ∈ planarOpen d.k) :
    C.tubeMap m (C.outerSeamInv m y) = C.chartProductMap (⟨y.1, hy⟩, y.2) := by
  have hlt := C.norm_outerSeamInv_lt_of_collar hp h1 (by linarith)
  have htr : C.outerSeamInv m y ∈ C.transitionDomain := by
    rw [C.transitionDomain_eq]
    exact ⟨C.one_lt_norm_outerSeamInv hp h2, hlt⟩
  have key : seamModel d m (C.port (.inr m)) (C.matrix m) (C.outerSeamInv m y) = y := by
    rw [C.seamModel_eq_outerSeamDir hj0, C.outerSeamDir_outerSeamInv hp (by linarith)]
  apply Subtype.ext
  rw [C.tubeMap_val hlt, C.transition m _ htr, C.chartProductMap_val]
  have k1 : (seamModel d m (C.port (.inr m)) (C.matrix m) (C.outerSeamInv m y)).1 = y.1 :=
    congrArg Prod.fst key
  have k2 : (seamModel d m (C.port (.inr m)) (C.matrix m) (C.outerSeamInv m y)).2 = y.2 :=
    congrArg Prod.snd key
  exact congrArg (fun z => (C.product z : W.Carrier)) (Prod.ext (Subtype.ext k1) k2)

end OuterCollar

section Closed

variable (hc : d.ports = 0) (h3 : d.cones.length = 3)

theorem port_val_closedHoleEquiv (j : Fin 3) :
    (C.port (.inr (C.closedHoleEquiv hc h3 j))).val = j.val := by
  rw [C.port_closedHoleEquiv hc h3 j]
  rfl

theorem fillingSlope_closedHoleEquiv_pos (j : Fin 3) :
    0 < (d.fillingSlope (C.closedHoleEquiv hc h3 j)).1 :=
  d.fillingSlope_fst_pos _

theorem tubeCentre_closedHoleEquiv_one : C.tubeCentre (C.closedHoleEquiv hc h3 1) = 3 / 2 := by
  have hk := d.k_eq_three_of_closedTriangle hc h3
  have hv := C.port_val_closedHoleEquiv hc h3 1
  unfold tubeCentre planarCenter
  rw [ite_eq_right (by omega), ite_eq_left (by simpa using hv)]
  push_cast
  ring

theorem tubeCentre_closedHoleEquiv_two : C.tubeCentre (C.closedHoleEquiv hc h3 2) = -(3 / 2) := by
  have hk := d.k_eq_three_of_closedTriangle hc h3
  have hv := C.port_val_closedHoleEquiv hc h3 2
  unfold tubeCentre planarCenter
  rw [ite_eq_right (by omega), ite_eq_right (by simp [hv]), ite_eq_left (by simpa using hv)]
  push_cast
  ring

omit C in
theorem isOpen_closedDomain : IsOpen closedDomain :=
  (isOpen_lt (continuous_norm.comp continuous_fst) continuous_const).inter
    ((isOpen_ne.preimage continuous_fst).inter (isOpen_ne.preimage continuous_fst))

include hc h3 in
open Classical in
def closedChart (y : ℂ × Circle) : W.pieceInterior ⊤ :=
  if h : y.1 ∈ planarOpen d.k then C.chartProductMap (⟨y.1, h⟩, y.2)
  else if ‖y.1 - 3 / 2‖ < C.collarRadius (C.closedHoleEquiv hc h3 1) then
    C.tubeMap (C.closedHoleEquiv hc h3 1) (C.seamInv (C.closedHoleEquiv hc h3 1) y)
  else if ‖y.1 + 3 / 2‖ < C.collarRadius (C.closedHoleEquiv hc h3 2) then
    C.tubeMap (C.closedHoleEquiv hc h3 2) (C.seamInv (C.closedHoleEquiv hc h3 2) y)
  else C.tubeMap (C.closedHoleEquiv hc h3 0) (C.outerSeamInv (C.closedHoleEquiv hc h3 0) y)

omit C in
include hc h3 in
theorem mem_planarOpen_iff {u : ℂ} :
    u ∈ planarOpen d.k ↔ ‖u‖ < 3 ∧ 1 / 2 < ‖u - 3 / 2‖ ∧ 1 / 2 < ‖u + 3 / 2‖ := by
  have hk := d.k_eq_three_of_closedTriangle hc h3
  constructor
  · intro h
    exact (planarFunction_three_neg_iff u).1 (planarFunction_neg_of_mem_planarOpen hk h)
  · intro h
    exact mem_planarOpen_of_planarFunction_neg hk ((planarFunction_three_neg_iff u).2 h)

theorem closedChart_of_mem_planarOpen {y : ℂ × Circle} (h : y.1 ∈ planarOpen d.k) :
    C.closedChart hc h3 y = C.chartProductMap (⟨y.1, h⟩, y.2) :=
  dite_eq_left h

theorem norm_sub_three_halves_add (u : ℂ) : 3 ≤ ‖u - 3 / 2‖ + ‖u + 3 / 2‖ := by
  have := norm_sub_le (u + 3 / 2) (u - 3 / 2)
  have h3 : (u + 3 / 2) - (u - 3 / 2) = 3 := by ring
  rw [h3] at this
  have h4 : ‖(3 : ℂ)‖ = 3 := by norm_num
  linarith

theorem closedChart_of_innerCollar_one {y : ℂ × Circle}
    (hm : ‖y.1 - 3 / 2‖ < C.collarRadius (C.closedHoleEquiv hc h3 1)) :
    C.closedChart hc h3 y =
      C.tubeMap (C.closedHoleEquiv hc h3 1) (C.seamInv (C.closedHoleEquiv hc h3 1) y) := by
  have hj : (C.port (.inr (C.closedHoleEquiv hc h3 1))).val ≠ 0 := by
    rw [C.port_val_closedHoleEquiv hc h3]; decide
  have hcen := C.tubeCentre_closedHoleEquiv_one hc h3
  by_cases h : y.1 ∈ planarOpen d.k
  · rw [C.closedChart_of_mem_planarOpen hc h3 h]
    have h1 : 1 / 2 < ‖y.1 - C.tubeCentre (C.closedHoleEquiv hc h3 1)‖ := by
      rw [hcen]; exact ((mem_planarOpen_iff hc h3).1 h).2.1
    exact (C.tubeMap_seamInv hj (C.fillingSlope_closedHoleEquiv_pos hc h3 1) h1
      (by rw [hcen]; exact hm) h).symm
  · unfold closedChart
    rw [dite_eq_right h, ite_eq_left hm]

theorem closedChart_of_innerCollar_two {y : ℂ × Circle}
    (hm : ‖y.1 + 3 / 2‖ < C.collarRadius (C.closedHoleEquiv hc h3 2)) :
    C.closedChart hc h3 y =
      C.tubeMap (C.closedHoleEquiv hc h3 2) (C.seamInv (C.closedHoleEquiv hc h3 2) y) := by
  have hj : (C.port (.inr (C.closedHoleEquiv hc h3 2))).val ≠ 0 := by
    rw [C.port_val_closedHoleEquiv hc h3]; decide
  have hcen := C.tubeCentre_closedHoleEquiv_two hc h3
  have hsub : y.1 - C.tubeCentre (C.closedHoleEquiv hc h3 2) = y.1 + 3 / 2 := by
    rw [hcen]; ring
  by_cases h : y.1 ∈ planarOpen d.k
  · rw [C.closedChart_of_mem_planarOpen hc h3 h]
    have h1 : 1 / 2 < ‖y.1 - C.tubeCentre (C.closedHoleEquiv hc h3 2)‖ := by
      rw [hsub]; exact ((mem_planarOpen_iff hc h3).1 h).2.2
    exact (C.tubeMap_seamInv hj (C.fillingSlope_closedHoleEquiv_pos hc h3 2) h1
      (by rw [hsub]; exact hm) h).symm
  · have hn : ¬ ‖y.1 - 3 / 2‖ < C.collarRadius (C.closedHoleEquiv hc h3 1) := by
      have := norm_sub_three_halves_add y.1
      have h1 := C.collarRadius_le_three_halves (m := C.closedHoleEquiv hc h3 1)
      have h2 := C.collarRadius_le_three_halves (m := C.closedHoleEquiv hc h3 2)
      intro hlt
      linarith
    unfold closedChart
    rw [dite_eq_right h, ite_eq_right hn, ite_eq_left hm]

theorem norm_sub_gt_of_outer {u : ℂ} (hu : 5 / 2 < ‖u‖) :
    1 < ‖u - 3 / 2‖ ∧ 1 < ‖u + 3 / 2‖ := by
  have h1 := norm_sub_norm_le u (3 / 2)
  have h2 := norm_sub_norm_le u (-(3 / 2))
  have e : ‖(3 / 2 : ℂ)‖ = 3 / 2 := by norm_num
  have e' : ‖(-(3 / 2) : ℂ)‖ = 3 / 2 := by norm_num
  rw [e] at h1
  rw [e', sub_neg_eq_add] at h2
  constructor <;> linarith

theorem closedChart_of_outerCollar {y : ℂ × Circle}
    (h1 : C.outerCollarRadius (C.closedHoleEquiv hc h3 0) < ‖y.1‖) :
    C.closedChart hc h3 y =
      C.tubeMap (C.closedHoleEquiv hc h3 0) (C.outerSeamInv (C.closedHoleEquiv hc h3 0) y) := by
  have hj0 : (C.port (.inr (C.closedHoleEquiv hc h3 0))).val = 0 :=
    C.port_val_closedHoleEquiv hc h3 0
  have hp := C.fillingSlope_closedHoleEquiv_pos hc h3 0
  have h52 := C.five_halves_le_outerCollarRadius (m := C.closedHoleEquiv hc h3 0)
  by_cases h : y.1 ∈ planarOpen d.k
  · rw [C.closedChart_of_mem_planarOpen hc h3 h]
    exact (C.tubeMap_outerSeamInv hj0 hp h1 ((mem_planarOpen_iff hc h3).1 h).1 h).symm
  · have h3' : 3 ≤ ‖y.1‖ := by
      by_contra hlt
      apply h
      have := norm_sub_gt_of_outer (u := y.1) (by linarith)
      exact (mem_planarOpen_iff hc h3).2 ⟨lt_of_not_ge hlt, by linarith, by linarith⟩
    have hn1 : ¬ ‖y.1 - 3 / 2‖ < C.collarRadius (C.closedHoleEquiv hc h3 1) := by
      have := norm_sub_norm_le y.1 (3 / 2)
      have e : ‖(3 / 2 : ℂ)‖ = 3 / 2 := by norm_num
      rw [e] at this
      have := C.collarRadius_le_three_halves (m := C.closedHoleEquiv hc h3 1)
      intro hlt
      linarith
    have hn2 : ¬ ‖y.1 + 3 / 2‖ < C.collarRadius (C.closedHoleEquiv hc h3 2) := by
      have := norm_sub_norm_le y.1 (-(3 / 2))
      have e : ‖(-(3 / 2) : ℂ)‖ = 3 / 2 := by norm_num
      rw [e, sub_neg_eq_add] at this
      have := C.collarRadius_le_three_halves (m := C.closedHoleEquiv hc h3 2)
      intro hlt
      linarith
    unfold closedChart
    rw [dite_eq_right h, ite_eq_right hn1, ite_eq_right hn2]

def closedInv (j : Fin 3) : ℂ × Circle → ℂ × Circle :=
  if j.val = 0 then C.outerSeamInv (C.closedHoleEquiv hc h3 j)
  else C.seamInv (C.closedHoleEquiv hc h3 j)

def closedDir (j : Fin 3) : ℂ × Circle → ℂ × Circle :=
  if j.val = 0 then C.outerSeamDir (C.closedHoleEquiv hc h3 j)
  else C.seamDir (C.closedHoleEquiv hc h3 j)

theorem closedDomain_cases {y : ℂ × Circle} (hy : y ∈ closedDomain) :
    y.1 ∈ planarOpen d.k ∨
      (‖y.1 - 3 / 2‖ < C.collarRadius (C.closedHoleEquiv hc h3 1) ∧ y.1 ≠ 3 / 2) ∨
      (‖y.1 + 3 / 2‖ < C.collarRadius (C.closedHoleEquiv hc h3 2) ∧ y.1 ≠ -(3 / 2)) ∨
      (C.outerCollarRadius (C.closedHoleEquiv hc h3 0) < ‖y.1‖ ∧ ‖y.1‖ < 7 / 2) := by
  obtain ⟨h7, h1, h2⟩ := hy
  by_cases ho : C.outerCollarRadius (C.closedHoleEquiv hc h3 0) < ‖y.1‖
  · exact Or.inr (Or.inr (Or.inr ⟨ho, h7⟩))
  by_cases hi1 : ‖y.1 - 3 / 2‖ < C.collarRadius (C.closedHoleEquiv hc h3 1)
  · exact Or.inr (Or.inl ⟨hi1, h1⟩)
  by_cases hi2 : ‖y.1 + 3 / 2‖ < C.collarRadius (C.closedHoleEquiv hc h3 2)
  · exact Or.inr (Or.inr (Or.inl ⟨hi2, h2⟩))
  left
  have hR := C.outerCollarRadius_lt_three (C.fillingSlope_closedHoleEquiv_pos hc h3 0)
  have hc1 := C.half_lt_collarRadius (C.fillingSlope_closedHoleEquiv_pos hc h3 1)
  have hc2 := C.half_lt_collarRadius (C.fillingSlope_closedHoleEquiv_pos hc h3 2)
  exact (mem_planarOpen_iff hc h3).2 ⟨by linarith [le_of_not_gt ho], by linarith [le_of_not_gt hi1],
    by linarith [le_of_not_gt hi2]⟩

theorem closedChart_core {y : ℂ × Circle} (hy : y ∈ closedDomain) (h : y.1 ∉ planarOpen d.k) :
    ∃ j : Fin 3, C.closedChart hc h3 y =
        C.tubeMap (C.closedHoleEquiv hc h3 j) (C.closedInv hc h3 j y) ∧
      ‖(C.closedInv hc h3 j y).1‖ ≤ 1 ∧ (C.closedInv hc h3 j y).1 ≠ 0 ∧
      C.closedDir hc h3 j (C.closedInv hc h3 j y) = y := by
  rcases C.closedDomain_cases hc h3 hy with h0 | ⟨hm, hne⟩ | ⟨hm, hne⟩ | ⟨ho, h7⟩
  · exact absurd h0 h
  · have hcen := C.tubeCentre_closedHoleEquiv_one hc h3
    have hp := C.fillingSlope_closedHoleEquiv_pos hc h3 1
    have hne' : y.1 ≠ C.tubeCentre (C.closedHoleEquiv hc h3 1) := by rw [hcen]; exact hne
    refine ⟨1, C.closedChart_of_innerCollar_one hc h3 hm, ?_, seamBwd_fst_ne_zero hne',
      C.seamDir_seamInv hp hne'⟩
    have hle : ‖y.1 - C.tubeCentre (C.closedHoleEquiv hc h3 1)‖ ≤ 1 / 2 := by
      rw [hcen]
      by_contra hlt
      apply h
      have hR := C.collarRadius_le_three_halves (m := C.closedHoleEquiv hc h3 1)
      have := norm_sub_three_halves_add y.1
      refine (mem_planarOpen_iff hc h3).2 ⟨?_, lt_of_not_ge hlt, by linarith⟩
      have := norm_le_norm_add_norm_sub' y.1 (3 / 2)
      have e : ‖(3 / 2 : ℂ)‖ = 3 / 2 := by norm_num
      rw [e] at this
      linarith
    by_contra hgt
    have := (C.lt_norm_seamInv_fst_iff hp one_pos).1 (lt_of_not_ge hgt)
    rw [one_pow] at this
    linarith
  · have hcen := C.tubeCentre_closedHoleEquiv_two hc h3
    have hp := C.fillingSlope_closedHoleEquiv_pos hc h3 2
    have hsub : y.1 - C.tubeCentre (C.closedHoleEquiv hc h3 2) = y.1 + 3 / 2 := by
      rw [hcen]; ring
    have hne' : y.1 ≠ C.tubeCentre (C.closedHoleEquiv hc h3 2) := by rw [hcen]; exact hne
    refine ⟨2, C.closedChart_of_innerCollar_two hc h3 hm, ?_, seamBwd_fst_ne_zero hne',
      C.seamDir_seamInv hp hne'⟩
    have hle : ‖y.1 - C.tubeCentre (C.closedHoleEquiv hc h3 2)‖ ≤ 1 / 2 := by
      rw [hsub]
      by_contra hlt
      apply h
      have hR := C.collarRadius_le_three_halves (m := C.closedHoleEquiv hc h3 2)
      have := norm_sub_three_halves_add y.1
      refine (mem_planarOpen_iff hc h3).2 ⟨?_, by linarith, lt_of_not_ge hlt⟩
      have := norm_le_norm_add_norm_sub' y.1 (-(3 / 2))
      have e : ‖(-(3 / 2) : ℂ)‖ = 3 / 2 := by norm_num
      rw [e, sub_neg_eq_add] at this
      linarith
    by_contra hgt
    have := (C.lt_norm_seamInv_fst_iff hp one_pos).1 (lt_of_not_ge hgt)
    rw [one_pow] at this
    linarith
  · have hp := C.fillingSlope_closedHoleEquiv_pos hc h3 0
    have h3' : 3 ≤ ‖y.1‖ := by
      by_contra hlt
      apply h
      have h52 := C.five_halves_le_outerCollarRadius (m := C.closedHoleEquiv hc h3 0)
      have := norm_sub_gt_of_outer (u := y.1) (by linarith)
      exact (mem_planarOpen_iff hc h3).2 ⟨lt_of_not_ge hlt, by linarith, by linarith⟩
    have hy0 : y.1 ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at h3'
      norm_num at h3'
    refine ⟨0, C.closedChart_of_outerCollar hc h3 ho, ?_, ?_, ?_⟩
    · change ‖(C.outerSeamInv (C.closedHoleEquiv hc h3 0) y).1‖ ≤ 1
      rw [C.norm_outerSeamInv_fst h7]
      have hP : (0 : ℝ) < d.fillingOrder (C.closedHoleEquiv hc h3 0) := by
        exact_mod_cast fillingOrder_pos hp
      have h0 : 0 ≤ 7 - 2 * ‖y.1‖ := by linarith
      exact Real.rpow_le_one h0 (by linarith) (inv_nonneg.mpr hP.le)
    · exact outerBwd_fst_ne_zero h7
    · exact C.outerSeamDir_outerSeamInv hp h7

theorem closedChart_injOn : InjOn (C.closedChart hc h3) closedDomain := by
  intro y hy y' hy' heq
  by_cases h : y.1 ∈ planarOpen d.k <;> by_cases h' : y'.1 ∈ planarOpen d.k
  · rw [C.closedChart_of_mem_planarOpen hc h3 h, C.closedChart_of_mem_planarOpen hc h3 h'] at heq
    have := C.chartProductMap_injective heq
    have h1 : y.1 = y'.1 := congrArg (fun z : planarOpen d.k × Circle => (z.1 : ℂ)) this
    have h2 : y.2 = y'.2 := congrArg (fun z : planarOpen d.k × Circle => z.2) this
    exact Prod.ext h1 h2
  · obtain ⟨j', hm', hle', -⟩ := C.closedChart_core hc h3 hy' h'
    rw [C.closedChart_of_mem_planarOpen hc h3 h, hm'] at heq
    have hv := congrArg (fun x : W.pieceInterior ⊤ => (x : W.Carrier)) heq
    simp only [C.chartProductMap_val, C.tubeMap_val (by linarith [C.ε_pos] :
      ‖(C.closedInv hc h3 j' y').1‖ < 1 + C.ε)] at hv
    exact absurd (hv ▸ (C.product _).2) (C.tube_core_not_mem_productRegion hle')
  · obtain ⟨j, hm, hle, -⟩ := C.closedChart_core hc h3 hy h
    rw [C.closedChart_of_mem_planarOpen hc h3 h', hm] at heq
    have hv := congrArg (fun x : W.pieceInterior ⊤ => (x : W.Carrier)) heq
    simp only [C.chartProductMap_val, C.tubeMap_val (by linarith [C.ε_pos] :
      ‖(C.closedInv hc h3 j y).1‖ < 1 + C.ε)] at hv
    exact absurd (hv.symm ▸ (C.product _).2) (C.tube_core_not_mem_productRegion hle)
  · obtain ⟨j, hm, hle, -, hdir⟩ := C.closedChart_core hc h3 hy h
    obtain ⟨j', hm', hle', -, hdir'⟩ := C.closedChart_core hc h3 hy' h'
    rw [hm, hm'] at heq
    obtain ⟨hjj, hs⟩ := (C.tubeMap_eq_iff_of_core (by linarith [C.ε_pos])
      (by linarith [C.ε_pos])).1 heq
    obtain rfl : j = j' := (C.closedHoleEquiv hc h3).injective hjj
    rw [← hdir, hs, hdir']

theorem closedChart_ne_tubeMap_zero {y : ℂ × Circle} (hy : y ∈ closedDomain)
    (m : Fin d.fillingCount) (w : Circle) : C.closedChart hc h3 y ≠ C.tubeMap m (0, w) := by
  intro heq
  have h0 : ‖((0 : ℂ), w).1‖ < 1 + C.ε := by
    change ‖(0 : ℂ)‖ < 1 + C.ε
    rw [norm_zero]
    linarith [C.ε_pos]
  by_cases h : y.1 ∈ planarOpen d.k
  · rw [C.closedChart_of_mem_planarOpen hc h3 h] at heq
    have hv := congrArg (fun x : W.pieceInterior ⊤ => (x : W.Carrier)) heq
    simp only [C.chartProductMap_val, C.tubeMap_val h0] at hv
    exact C.tube_core_not_mem_productRegion (m := m) (y := ((0 : ℂ), w))
      (by change ‖(0 : ℂ)‖ ≤ 1; rw [norm_zero]; norm_num) (hv ▸ (C.product _).2)
  · obtain ⟨j, hm, hle, hne0, -⟩ := C.closedChart_core hc h3 hy h
    rw [hm] at heq
    obtain ⟨-, hs⟩ := (C.tubeMap_eq_iff_of_core (by linarith [C.ε_pos]) h0).1 heq
    exact hne0 (congrArg Prod.fst hs)

theorem exists_closedChart_eq (x : W.pieceInterior ⊤) :
    (∃ y ∈ closedDomain, C.closedChart hc h3 y = x) ∨ ∃ m w, x = C.tubeMap m (0, w) := by
  have hprod : (x : W.Carrier) ∈ C.productRegion →
      ∃ y ∈ closedDomain, C.closedChart hc h3 y = x := by
    intro hx
    obtain ⟨z, hz⟩ := C.exists_chartProductMap_eq hx
    have hz' := (mem_planarOpen_iff hc h3).1 z.1.2
    refine ⟨((z.1 : ℂ), z.2), ⟨by linarith [hz'.1], ?_, ?_⟩, ?_⟩
    · intro he
      have he' : (z.1 : ℂ) = 3 / 2 := he
      have := hz'.2.1
      rw [he', sub_self, norm_zero] at this
      norm_num at this
    · intro he
      have he' : (z.1 : ℂ) = -(3 / 2) := he
      have := hz'.2.2
      rw [he', neg_add_cancel, norm_zero] at this
      norm_num at this
    · rw [C.closedChart_of_mem_planarOpen hc h3 z.1.2]
      exact hz
  rcases C.covers x x.2.2 with hx | ⟨m, hm⟩
  · exact Or.inl (hprod hx)
  set v := (C.tube m).symm x with hv
  have hvs : v ∈ (C.tube m).source := (C.tube m).map_target hm
  have hvx : C.tube m v = x := (C.tube m).right_inv hm
  have hvn : ‖v.1‖ < 1 + C.ε := by rw [C.tube_source] at hvs; exact hvs
  have htm : C.tubeMap m v = x := Subtype.ext ((C.tubeMap_val hvn).trans hvx)
  by_cases h0 : v.1 = 0
  · right
    refine ⟨m, v.2, ?_⟩
    rw [← htm]
    congr 1
    exact Prod.ext h0 rfl
  by_cases h1 : 1 < ‖v.1‖
  · left
    apply hprod
    have htr : v ∈ C.transitionDomain := by rw [C.transitionDomain_eq]; exact ⟨h1, hvn⟩
    have hmem : (x : W.Carrier) ∈ C.tube m '' C.transitionDomain := ⟨v, htr, hvx⟩
    rw [← C.tube_product_overlap m] at hmem
    exact hmem.2
  left
  have hpos : 0 < ‖v.1‖ := norm_pos_iff.mpr h0
  have hle : ‖v.1‖ ≤ 1 := le_of_not_gt h1
  obtain ⟨j, rfl⟩ : ∃ j, C.closedHoleEquiv hc h3 j = m :=
    ⟨(C.closedHoleEquiv hc h3).symm m, Equiv.apply_symm_apply _ _⟩
  have hp := C.fillingSlope_closedHoleEquiv_pos hc h3 j
  have hPpos := fillingOrder_pos hp
  have hpow : ‖v.1‖ ^ d.fillingOrder (C.closedHoleEquiv hc h3 j) ≤ 1 :=
    pow_le_one₀ (norm_nonneg _) hle
  have hpow0 : 0 < ‖v.1‖ ^ d.fillingOrder (C.closedHoleEquiv hc h3 j) := pow_pos hpos _
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 by fin_cases j <;> simp) with rfl | rfl | rfl
  · set y := C.outerSeamDir (C.closedHoleEquiv hc h3 0) v with hy
    have hn : ‖y.1‖ = 7 / 2 - ‖v.1‖ ^ d.fillingOrder (C.closedHoleEquiv hc h3 0) / 2 :=
      norm_outerFwd_fst (by linarith)
    have h52 := C.outerCollarRadius_lt_three (C.fillingSlope_closedHoleEquiv_pos hc h3 0)
    refine ⟨y, ⟨by linarith, ?_, ?_⟩, ?_⟩
    · intro he
      rw [he] at hn
      norm_num at hn
      linarith
    · intro he
      rw [he] at hn
      norm_num at hn
      linarith
    · rw [C.closedChart_of_outerCollar hc h3 (by linarith),
        C.outerSeamInv_outerSeamDir hp (by linarith)]
      exact htm
  · have hcen := C.tubeCentre_closedHoleEquiv_one hc h3
    set y := C.seamDir (C.closedHoleEquiv hc h3 1) v with hy
    have hn : ‖y.1 - C.tubeCentre (C.closedHoleEquiv hc h3 1)‖ =
        ‖v.1‖ ^ d.fillingOrder (C.closedHoleEquiv hc h3 1) / 2 := norm_seamFwd_sub v
    rw [hcen] at hn
    have hne : y.1 ≠ 3 / 2 := by
      intro he
      rw [he, sub_self, norm_zero] at hn
      linarith
    have hR := C.half_lt_collarRadius hp
    have hmem : y ∈ closedDomain := by
      refine ⟨?_, hne, ?_⟩
      · have := norm_le_norm_add_norm_sub' y.1 (3 / 2)
        have e : ‖(3 / 2 : ℂ)‖ = 3 / 2 := by norm_num
        rw [e] at this
        linarith
      · intro he
        rw [he] at hn
        norm_num at hn
        linarith
    refine ⟨y, hmem, ?_⟩
    rw [C.closedChart_of_innerCollar_one hc h3 (by linarith),
      C.seamInv_seamDir hp h0]
    exact htm
  · have hcen := C.tubeCentre_closedHoleEquiv_two hc h3
    set y := C.seamDir (C.closedHoleEquiv hc h3 2) v with hy
    have hn : ‖y.1 - C.tubeCentre (C.closedHoleEquiv hc h3 2)‖ =
        ‖v.1‖ ^ d.fillingOrder (C.closedHoleEquiv hc h3 2) / 2 := norm_seamFwd_sub v
    rw [hcen, sub_neg_eq_add] at hn
    have hne : y.1 ≠ -(3 / 2) := by
      intro he
      rw [he, neg_add_cancel, norm_zero] at hn
      linarith
    have hR := C.half_lt_collarRadius hp
    have hmem : y ∈ closedDomain := by
      refine ⟨?_, ?_, hne⟩
      · have := norm_le_norm_add_norm_sub' y.1 (-(3 / 2))
        have e : ‖(-(3 / 2) : ℂ)‖ = 3 / 2 := by norm_num
        rw [e, sub_neg_eq_add] at this
        linarith
      · intro he
        rw [he] at hn
        norm_num at hn
        linarith
    refine ⟨y, hmem, ?_⟩
    rw [C.closedChart_of_innerCollar_two hc h3 (by linarith),
      C.seamInv_seamDir hp h0]
    exact htm

theorem isLocalDiffeomorphAt_closedChart {y : ℂ × Circle} (hy : y ∈ closedDomain) :
    letI := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior ⊤)
    IsLocalDiffeomorphAt PlaneCircleModel (𝓡 3) ∞ (C.closedChart hc h3) y := by
  let _ := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior ⊤)
  rcases C.closedDomain_cases hc h3 hy with h | ⟨hm, hne⟩ | ⟨hm, hne⟩ | ⟨ho, h7⟩
  · let e : planarOpen d.k × Circle → ℂ × Circle :=
      Prod.map (Subtype.val : planarOpen d.k → ℂ) (id : Circle → Circle)
    have he : IsLocalDiffeomorphAt PlaneCircleModel PlaneCircleModel ∞ e (⟨y.1, h⟩, y.2) :=
      (isLocalDiffeomorph_subtype_val (planarOpen d.k) _).prodMap
        ((Diffeomorph.refl (𝓡 1) Circle ∞).isLocalDiffeomorph _)
    have hcomp : C.closedChart hc h3 ∘ e = C.chartProductMap := by
      funext z
      exact C.closedChart_of_mem_planarOpen hc h3 z.1.2
    have hgf : IsLocalDiffeomorphAt PlaneCircleModel (𝓡 3) ∞ (C.closedChart hc h3 ∘ e)
        (⟨y.1, h⟩, y.2) := by
      rw [hcomp]
      exact C.isLocalDiffeomorph_chartProductMap _
    exact isLocalDiffeomorphAt_of_comp hgf he
  · set m := C.closedHoleEquiv hc h3 1 with hmdef
    have hcen := C.tubeCentre_closedHoleEquiv_one hc h3
    have hp := C.fillingSlope_closedHoleEquiv_pos hc h3 1
    have hopen : IsOpen {z : ℂ × Circle | ‖z.1 - 3 / 2‖ < C.collarRadius m} :=
      isOpen_lt (continuous_norm.comp (continuous_fst.sub continuous_const)) continuous_const
    have hne' : y.1 ≠ C.tubeCentre m := by rw [hcen]; exact hne
    have hs := isLocalDiffeomorphAt_seamBwd (c := C.tubeCentre m) (P := d.fillingOrder m)
      (p := (d.fillingSlope m).1) (q := (d.fillingSlope m).2) (a := C.a m) (b := C.b m)
      (fillingOrder_pos hp).ne' (C.bezout m) hne'
    have ht := C.isLocalDiffeomorphAt_tubeMap (m := m)
      (C.norm_seamInv_lt_of_collar hp (by rw [hcen]; exact hm))
    refine IsLocalDiffeomorphAt.of_eventuallyEq ?_ (IsLocalDiffeomorphAt.comp (hf := hs) (hg := ht))
    filter_upwards [hopen.mem_nhds hm] with z hz
    exact C.closedChart_of_innerCollar_one hc h3 hz
  · set m := C.closedHoleEquiv hc h3 2 with hmdef
    have hcen := C.tubeCentre_closedHoleEquiv_two hc h3
    have hp := C.fillingSlope_closedHoleEquiv_pos hc h3 2
    have hsub : ∀ u : ℂ, u - C.tubeCentre m = u + 3 / 2 := fun u => by rw [hcen]; ring
    have hopen : IsOpen {z : ℂ × Circle | ‖z.1 + 3 / 2‖ < C.collarRadius m} :=
      isOpen_lt (continuous_norm.comp (continuous_fst.add continuous_const)) continuous_const
    have hne' : y.1 ≠ C.tubeCentre m := by rw [hcen]; exact hne
    have hs := isLocalDiffeomorphAt_seamBwd (c := C.tubeCentre m) (P := d.fillingOrder m)
      (p := (d.fillingSlope m).1) (q := (d.fillingSlope m).2) (a := C.a m) (b := C.b m)
      (fillingOrder_pos hp).ne' (C.bezout m) hne'
    have ht := C.isLocalDiffeomorphAt_tubeMap (m := m)
      (C.norm_seamInv_lt_of_collar hp (by rw [hsub]; exact hm))
    refine IsLocalDiffeomorphAt.of_eventuallyEq ?_ (IsLocalDiffeomorphAt.comp (hf := hs) (hg := ht))
    filter_upwards [hopen.mem_nhds hm] with z hz
    exact C.closedChart_of_innerCollar_two hc h3 hz
  · set m := C.closedHoleEquiv hc h3 0 with hmdef
    have hp := C.fillingSlope_closedHoleEquiv_pos hc h3 0
    have h52 := C.five_halves_le_outerCollarRadius (m := m)
    have hy0 : y.1 ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at ho
      linarith
    have hopen : IsOpen {z : ℂ × Circle | C.outerCollarRadius m < ‖z.1‖} :=
      isOpen_lt continuous_const (continuous_norm.comp continuous_fst)
    have hs := isLocalDiffeomorphAt_outerBwd (P := d.fillingOrder m)
      (p := (d.fillingSlope m).1) (q := (d.fillingSlope m).2) (a := C.a m) (b := C.b m)
      (fillingOrder_pos hp).ne' (C.bezout m) hy0 h7
    have ht := C.isLocalDiffeomorphAt_tubeMap (m := m) (C.norm_outerSeamInv_lt_of_collar hp ho h7)
    refine IsLocalDiffeomorphAt.of_eventuallyEq ?_ (IsLocalDiffeomorphAt.comp (hf := hs) (hg := ht))
    filter_upwards [hopen.mem_nhds ho] with z hz
    exact C.closedChart_of_outerCollar hc h3 hz

end Closed

end SeifertBlockCharts

end GC.Seifert
