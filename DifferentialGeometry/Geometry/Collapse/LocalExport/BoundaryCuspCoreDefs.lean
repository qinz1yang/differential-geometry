import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAugmentedOriginalMap

/-!
# BCG06, G1: the global cusp core and front, marker division (lane BCG6-K)

Draft 61 §4.1–§4.2, disposition D61-9, blueprint BCG06 (master207B). KERNEL form: the chain map
`C.E` does not exist yet, so the core and the front are defined for ARBITRARY functions
`u v : W → ℝ` (bound later to `(u_b, v_b) := J_b ∘ C.E`), and BCG04 / BCG05 enter as explicit
numerical premises:

* (BI)  `|u x - (P.block b x).1| < εd ∧ |v x - (P.block b x).2| < εd` at the point in question;
* (BFM) `v = 1` on `Safe_b = P.safeBand_BAUGA b` (band membership AND `32 ≤ η_b ≤ 78`).

Definitions (GLOBAL subsets of `W`, no localisation):

* `cuspNbhd35_BCG6K`: the open intrinsic `35`-neighbourhood of `∂_b W`;
* `cuspCore_BCG6K`  = `N₃₅(∂_b W) ∪ {v ≥ .9 ∧ u ≤ 40 v}` (BCG06.a);
* `cuspFront_BCG6K` = `{v ≥ .9 ∧ u = 40 v}` (BCG06.b).

Results:

* `block_fst_eq_mul_BCG6K`: everywhere on `W`, `(P.block b x).1 = η_b x · (P.block b x).2`;
* marker division (BCG06.c, at EVERY point of `W`): `v ≥ .9` puts the point in the original
  collar band with original marker `> .9 - εd` (`mem_collarBand_of_marker_BCG6K`);
  `u ≤ 40 v` gives `η_b < 40 + 41 εd / (.9 - εd)` (`height_lt_of_marked_BCG6K`); `u = 40 v`
  gives `|η_b - 40| < 41 εd / (.9 - εd) < .001` (`abs_height_sub_forty_lt_BCG6K`);
* the `N₃₅` geometry: first exit (`exists_height_lt_of_mem_cuspNbhd35_BCG6K`) and the vertical
  path (`mem_cuspNbhd35_of_height_le_BCG6K`);
* the strict-marker equivalence (`cuspCore_eq_strict_BCG6K`, `cuspFront_eq_strict_BCG6K`) and
  the front localisation (`front_localization_BCG6K`).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open scoped Manifold ContDiff Topology ENNReal
open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint
  DifferentialGeometry.Analysis DifferentialGeometry.Geometry.Riemannian

namespace DifferentialGeometry.Geometry.Collapse

universe u

variable {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ}
  {A : ℝ → ℝ} {w₀ ε : ℝ}

namespace BoundaryCollarPacket

variable (P : BoundaryCollarPacket W g K A w₀ ε) (b : Fin P.cusp.count)

/-- The open intrinsic `35`-neighbourhood `N₃₅(∂_b W)` of the boundary component `b`. -/
def cuspNbhd35_BCG6K : Set W.Carrier :=
  {x | ∃ y ∈ P.cusp.component b, riemannianEDistOf g y x < ENNReal.ofReal 35}

/-- **The cusp core (BCG06.a)**, a GLOBAL subset of `W`:
`C_b = N₃₅(∂_b W) ∪ {v ≥ .9 ∧ u ≤ 40 v}` for the boundary pair `(u, v)`. -/
def cuspCore_BCG6K (u v : Fin P.cusp.count → W.Carrier → ℝ) : Set W.Carrier :=
  P.cuspNbhd35_BCG6K b ∪ {x | (9 / 10 : ℝ) ≤ v b x ∧ u b x ≤ 40 * v b x}

/-- **The cusp front (BCG06.b)**, a GLOBAL subset of `W`: `H_b = {v ≥ .9 ∧ u = 40 v}`. -/
def cuspFront_BCG6K (u v : Fin P.cusp.count → W.Carrier → ℝ) : Set W.Carrier :=
  {x | (9 / 10 : ℝ) ≤ v b x ∧ u b x = 40 * v b x}

/-- The first component of the actual collar block is the height times the marker, everywhere
on `W` (both vanish off the band). -/
theorem block_fst_eq_mul_BCG6K (x : W.Carrier) :
    (P.block b x).1 = P.height b x * (P.block b x).2 := by
  by_cases hx : x ∈ P.collarBand_BAUGA b
  · rw [P.block_eq_of_mem_collarBand_BAUGA b hx, boundaryBlock_fst, boundaryBlock_snd]
  · rw [P.block_eq_zero_of_notMem_collarBand_BAUGA b hx]
    simp

/-- Marker division, first step: `v ≥ .9` and the BCG04 error `< εd < .9` give the original
marker `> .9 - εd`, so the point lies in the original collar band with `20 < η_b < 90`. -/
theorem mem_collarBand_of_marker_BCG6K {v : W.Carrier → ℝ} {εd : ℝ} {x : W.Carrier}
    (hεd : εd < 9 / 10) (hv : |v x - (P.block b x).2| < εd) (h9 : (9 / 10 : ℝ) ≤ v x) :
    9 / 10 - εd < (P.block b x).2 ∧ x ∈ P.collarBand_BAUGA b ∧
      20 < P.height b x ∧ P.height b x < 90 := by
  have hlt : 9 / 10 - εd < (P.block b x).2 := by linarith [(abs_lt.mp hv).2]
  have hne : P.block b x ≠ 0 := by
    intro h
    rw [h] at hlt
    change 9 / 10 - εd < (0 : ℝ) at hlt
    linarith
  have hmem := mem_of_indicator_boundaryBlock_ne_zero (S := P.collarBand_BAUGA b)
    (η := P.height b) (x := x) hne
  exact ⟨hlt, hmem.1, hmem.2.1, hmem.2.2⟩

/-- Marker division, inequality case (BCG06.c): `v ≥ .9` and `u ≤ 40 v` give
`η_b < 40 + 41 εd / (.9 - εd)`. -/
theorem height_lt_of_marked_BCG6K {u v : W.Carrier → ℝ} {εd : ℝ} {x : W.Carrier}
    (hεd : εd < 9 / 10) (hu : |u x - (P.block b x).1| < εd) (hv : |v x - (P.block b x).2| < εd)
    (h9 : (9 / 10 : ℝ) ≤ v x) (hle : u x ≤ 40 * v x) :
    P.height b x < 40 + 41 * εd / (9 / 10 - εd) := by
  obtain ⟨hζ, -, -, -⟩ := P.mem_collarBand_of_marker_BCG6K b hεd hv h9
  have hpos : 0 < 9 / 10 - εd := by linarith
  have hε0 : 0 ≤ εd := (abs_nonneg _).trans hu.le
  have hfst := P.block_fst_eq_mul_BCG6K b x
  have h1 := abs_lt.mp hu
  have h2 := abs_lt.mp hv
  have hkey : (P.height b x - 40) * (P.block b x).2 < 41 * εd := by nlinarith
  rw [← sub_lt_iff_lt_add', lt_div_iff₀ hpos]
  rcases le_or_gt (P.height b x - 40) 0 with hneg | hposh
  · nlinarith
  · nlinarith

/-- Marker division, equality case (BCG06.c, (Loc)): `v ≥ .9` and `u = 40 v` give
`|η_b - 40| < 41 εd / (.9 - εd)`. -/
theorem abs_height_sub_forty_lt_BCG6K {u v : W.Carrier → ℝ} {εd : ℝ} {x : W.Carrier}
    (hεd : εd < 9 / 10) (hu : |u x - (P.block b x).1| < εd) (hv : |v x - (P.block b x).2| < εd)
    (h9 : (9 / 10 : ℝ) ≤ v x) (heq : u x = 40 * v x) :
    |P.height b x - 40| < 41 * εd / (9 / 10 - εd) := by
  obtain ⟨hζ, -, -, -⟩ := P.mem_collarBand_of_marker_BCG6K b hεd hv h9
  have hpos : 0 < 9 / 10 - εd := by linarith
  have hε0 : 0 ≤ εd := (abs_nonneg _).trans hu.le
  have hfst := P.block_fst_eq_mul_BCG6K b x
  have h1 := abs_lt.mp hu
  have h2 := abs_lt.mp hv
  have hkey1 : (P.height b x - 40) * (P.block b x).2 < 41 * εd := by nlinarith
  have hkey2 : -(41 * εd) < (P.height b x - 40) * (P.block b x).2 := by nlinarith
  rw [lt_div_iff₀ hpos]
  rcases abs_cases (P.height b x - 40) with ⟨h, hs⟩ | ⟨h, hs⟩ <;> rw [h] <;> nlinarith

/-- The numerical form of (Loc): for `εd < 10⁻⁶`, `41 εd / (.9 - εd) < 1/1000`. -/
theorem loc_constant_lt_BCG6K {εd : ℝ} (h : εd < 1 / 1000000) :
    41 * εd / (9 / 10 - εd) < 1 / 1000 := by
  rw [div_lt_iff₀ (by linarith)]
  nlinarith

/-- (Loc), numerical: on the front `|η_b - 40| < 1/1000` and the point is in the band. -/
theorem front_height_BCG6K {u v : Fin P.cusp.count → W.Carrier → ℝ} {εd : ℝ} {x : W.Carrier}
    (hεd : εd < 1 / 1000000) (hu : |u b x - (P.block b x).1| < εd)
    (hv : |v b x - (P.block b x).2| < εd) (hx : x ∈ P.cuspFront_BCG6K b u v) :
    x ∈ P.collarBand_BAUGA b ∧ |P.height b x - 40| < 1 / 1000 := by
  have hε0 : 0 ≤ εd := (abs_nonneg _).trans hu.le
  refine ⟨(P.mem_collarBand_of_marker_BCG6K b (by linarith) hv hx.1).2.1, ?_⟩
  exact (P.abs_height_sub_forty_lt_BCG6K b (by linarith) hu hv hx.1 hx.2).trans
    (loc_constant_lt_BCG6K hεd)

/-- First exit: a point of `N₃₅(∂_b W)` is a collar point of height `< 35.01`. -/
theorem exists_height_lt_of_mem_cuspNbhd35_BCG6K {x : W.Carrier}
    (hx : x ∈ P.cuspNbhd35_BCG6K b) :
    ∃ q ∈ cuspDomain, (P.cusp.collar b).toFun q = x ∧ q.2.val 0 < 3501 / 100 := by
  obtain ⟨y, hy, hxy⟩ := hx
  obtain ⟨t, rfl⟩ := (Set.ext_iff.mp (P.cusp.collar b).boundary_image y).mpr hy
  by_contra hnot
  have hnot' : x ∉ (P.cusp.collar b).toFun '' {q : CuspHalfSpace | q.2.val 0 < 3501 / 100} := by
    rintro ⟨q, hq, rfl⟩
    exact hnot ⟨q, cusp_mem_cuspDomain_of_le (b := 3501 / 100) (by norm_num [cuspDepth]) hq.le,
      rfl, hq⟩
  have h1 := (P.cusp.collar b).ofReal_le_riemannianEDistOf_of_not_mem_image_height_lt
    (h := 3501 / 100) (by norm_num [cuspDepth]) (p := (t, halfZero))
    (by rw [halfZero_val_zero]; norm_num) hnot'
  rw [halfZero_val_zero, sub_zero] at h1
  have hw := P.threshold
  have hw0 : 0 ≤ w₀ := (P.cusp.collar b).delta_nonneg
  have hs : (35 / (3501 / 100) : ℝ) ≤ Real.sqrt (1 - w₀) :=
    Real.le_sqrt_of_sq_le (by nlinarith)
  have h35 : (35 : ℝ) ≤ Real.sqrt (1 - w₀) * (3501 / 100) := by
    rw [div_le_iff₀ (by norm_num)] at hs
    linarith
  exact absurd hxy (not_lt.mpr ((ENNReal.ofReal_le_ofReal h35).trans h1))

/-- Vertical path: a collar point of height `≤ 33` lies in `N₃₅(∂_b W)`. -/
theorem mem_cuspNbhd35_of_height_le_BCG6K {p : CuspHalfSpace} (hp : p ∈ cuspDomain)
    (h33 : p.2.val 0 ≤ 33) : (P.cusp.collar b).toFun p ∈ P.cuspNbhd35_BCG6K b := by
  refine ⟨(P.cusp.collar b).toFun (p.1, halfZero), ?_, ?_⟩
  · exact (Set.ext_iff.mp (P.cusp.collar b).boundary_image _).mp ⟨p.1, rfl⟩
  · have h := (P.cusp.collar b).riemannianEDistOf_le_flat (mem_cuspDomain_halfZero p.1) hp
    rw [riemannianEDistOf_self, ENNReal.toReal_zero, halfZero_val_zero] at h
    have hz0 : 0 ≤ p.2.val 0 := p.2.2
    have hsq : Real.sqrt ((0 - p.2.val 0) ^ 2 + 0 ^ 2) = p.2.val 0 := by
      rw [show (0 - p.2.val 0) ^ 2 + (0 : ℝ) ^ 2 = (p.2.val 0) ^ 2 by ring, Real.sqrt_sq hz0]
    rw [hsq] at h
    refine h.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr ?_)
    have hw := P.threshold
    have hs : Real.sqrt (1 + w₀) < 35 / 33 :=
      (Real.sqrt_lt' (by norm_num)).mpr (by nlinarith)
    have hs0 := Real.sqrt_nonneg (1 + w₀)
    nlinarith

/-- A band point of height `η_b < 32` lies in `N₃₅(∂_b W)` (contract `|η_b - z| < ε ≤ 1`). -/
theorem mem_cuspNbhd35_of_mem_band_BCG6K {x : W.Carrier} (hx : x ∈ P.collarBand_BAUGA b)
    (h32 : P.height b x < 32) : x ∈ P.cuspNbhd35_BCG6K b := by
  obtain ⟨p, hp, rfl⟩ := hx
  have hpd : p ∈ cuspDomain :=
    cusp_mem_cuspDomain_of_le (b := 98) (by norm_num [cuspDepth]) hp.2.le
  have h := abs_lt.mp (P.height_contract b p hpd hp.1.le hp.2.le).1
  exact P.mem_cuspNbhd35_of_height_le_BCG6K b hpd (by linarith [P.tolerance_le_one])

variable {b}

/-- **Strict-marker equivalence for the core**: replacing `v ≥ .9` by `v > .9` does not change
`C_b` (BCG05 on `Safe_b`, (Loc), and `N₃₅` below height `32`). -/
theorem cuspCore_eq_strict_BCG6K {u v : Fin P.cusp.count → W.Carrier → ℝ} {εd : ℝ} (hεd : εd < 1 / 1000000)
    (hBI : ∀ x, |u b x - (P.block b x).1| < εd ∧ |v b x - (P.block b x).2| < εd)
    (hBFM : ∀ x ∈ P.safeBand_BAUGA b, v b x = 1) :
    P.cuspCore_BCG6K b u v =
      P.cuspNbhd35_BCG6K b ∪ {x | (9 / 10 : ℝ) < v b x ∧ u b x ≤ 40 * v b x} := by
  ext x
  constructor
  · rintro (hN | ⟨h9, hle⟩)
    · exact Or.inl hN
    rcases h9.lt_or_eq with hlt | heq
    · exact Or.inr ⟨hlt, hle⟩
    left
    obtain ⟨-, hband, -, -⟩ := P.mem_collarBand_of_marker_BCG6K b (by linarith) (hBI x).2 h9
    by_contra hN
    have h32 : 32 ≤ P.height b x := by
      by_contra h
      exact hN (P.mem_cuspNbhd35_of_mem_band_BCG6K b hband (not_le.mp h))
    have hlt0 := P.height_lt_of_marked_BCG6K b (by linarith) (hBI x).1 (hBI x).2 h9 hle
    have hlt : P.height b x < 40 + 1 / 1000 := by linarith [loc_constant_lt_BCG6K hεd]
    have h1 := hBFM x ⟨hband, h32, by linarith⟩
    rw [← heq] at h1
    norm_num at h1
  · rintro (hN | ⟨h9, hle⟩)
    · exact Or.inl hN
    · exact Or.inr ⟨h9.le, hle⟩

/-- **Strict-marker equivalence for the front**: replacing `v ≥ .9` by `v > .9` does not change
`H_b`. -/
theorem cuspFront_eq_strict_BCG6K {u v : Fin P.cusp.count → W.Carrier → ℝ} {εd : ℝ} (hεd : εd < 1 / 1000000)
    (hBI : ∀ x, |u b x - (P.block b x).1| < εd ∧ |v b x - (P.block b x).2| < εd)
    (hBFM : ∀ x ∈ P.safeBand_BAUGA b, v b x = 1) :
    P.cuspFront_BCG6K b u v = {x | (9 / 10 : ℝ) < v b x ∧ u b x = 40 * v b x} := by
  ext x
  constructor
  · rintro hx
    obtain ⟨hband, hloc⟩ := P.front_height_BCG6K b hεd (hBI x).1 (hBI x).2 hx
    have h1 := hBFM x ⟨hband, by linarith [(abs_lt.mp hloc).1], by linarith [(abs_lt.mp hloc).2]⟩
    exact ⟨by rw [h1]; norm_num, hx.2⟩
  · rintro ⟨h9, heq⟩
    exact ⟨h9.le, heq⟩

/-- **Front localisation**: every front point lies in `Safe_b` with `|η_b - 40| < .001`, where
`v = 1` and `u = 40`. -/
theorem front_localization_BCG6K {u v : Fin P.cusp.count → W.Carrier → ℝ} {εd : ℝ} (hεd : εd < 1 / 1000000)
    (hBI : ∀ x, |u b x - (P.block b x).1| < εd ∧ |v b x - (P.block b x).2| < εd)
    (hBFM : ∀ x ∈ P.safeBand_BAUGA b, v b x = 1) {x : W.Carrier}
    (hx : x ∈ P.cuspFront_BCG6K b u v) :
    x ∈ P.safeBand_BAUGA b ∧ |P.height b x - 40| < 1 / 1000 ∧ v b x = 1 ∧ u b x = 40 := by
  obtain ⟨hband, hloc⟩ := P.front_height_BCG6K b hεd (hBI x).1 (hBI x).2 hx
  have hsafe : x ∈ P.safeBand_BAUGA b :=
    ⟨hband, by linarith [(abs_lt.mp hloc).1], by linarith [(abs_lt.mp hloc).2]⟩
  have h1 := hBFM x hsafe
  refine ⟨hsafe, hloc, h1, ?_⟩
  rw [hx.2, h1]
  norm_num

end BoundaryCollarPacket

end DifferentialGeometry.Geometry.Collapse
