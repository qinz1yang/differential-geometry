import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.FilledPantsGeometrySeam
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.FilledPantsGeometryRegressions

/-!
# The punctured block chart

Lane A5 (design `docs/geometrization/handoffs/20261004-design-a5-filled-pants-assembly.md`, §1,
§3.1 and §3.3 step 1, with review 21 §1.3 and §4.1). Let `C` be charts of a block with `d.k = 3`
whose fillings all sit at inner holes, with positive first slope coordinate. For a filling `m` with
centre `c = C.tubeCentre m` (`± 3/2`), X13's seam model is `seamFwd` (`seamModel_eq_seamFwd`), so
on the collar `1/2 < |ζ - c| < C.collarRadius m` the tube composed with the seam inverse
`C.seamInv m = seamBwd` is the product chart (`tubeMap_seamInv`). The punctured chart
`C.puncturedChart hk : ℂ × S¹ → W.pieceInterior ⊤` is the product chart over `planarOpen d.k` and
`tube m ∘ seamInv m` over the punctured collar `0 < |ζ - c| < C.collarRadius m`
(`puncturedChart_of_mem_planarOpen`, `puncturedChart_of_collar`), a local diffeomorphism at every
point of `C.puncturedDomain` (`isLocalDiffeomorphAt_puncturedChart`), injective there
(`puncturedChart_injOn`), never on a central fibre `tube m (0, w)`
(`puncturedChart_ne_tubeMap_zero`),
and every point of the interior is in its image or on a central fibre (`exists_puncturedChart_eq`).
The collar radius is capped at `3/2`, so distinct collars are disjoint.
-/

set_option autoImplicit false

noncomputable section
open Set
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Geometry
open scoped Manifold ContDiff Topology ComplexConjugate

universe u

namespace GC.Seifert

variable {W : CompactCarrier.{u}} {d : SeifertData}

def SeifertData.fillingOrder (d : SeifertData) (m : Fin d.fillingCount) : ℕ :=
  (d.fillingSlope m).1.natAbs

namespace SeifertBlockCharts

variable (C : SeifertBlockCharts W d)

def tubeCentre (m : Fin d.fillingCount) : ℂ := (planarCenter d.k (C.port (.inr m)) : ℂ)

def collarRadius (m : Fin d.fillingCount) : ℝ := min ((1 + C.ε) ^ d.fillingOrder m / 2) (3 / 2)

def seamInv (m : Fin d.fillingCount) : ℂ × Circle → ℂ × Circle :=
  seamBwd (C.tubeCentre m) (d.fillingOrder m) (d.fillingSlope m).1 (d.fillingSlope m).2 (C.a m)
    (C.b m)

def seamDir (m : Fin d.fillingCount) : ℂ × Circle → ℂ × Circle :=
  seamFwd (C.tubeCentre m) (d.fillingOrder m) (d.fillingSlope m).1 (d.fillingSlope m).2 (C.a m)
    (C.b m)

def tubeClamp (y : ℂ × Circle) : ℂ × Circle :=
  if ‖y.1‖ < 1 + C.ε then y else (0, 1)

theorem tubeClamp_mem_source (m : Fin d.fillingCount) (y : ℂ × Circle) :
    C.tubeClamp y ∈ (C.tube m).source := by
  rw [C.tube_source]
  unfold tubeClamp
  split_ifs with h
  · exact h
  · change ‖(0 : ℂ)‖ < 1 + C.ε
    rw [norm_zero]
    linarith [C.ε_pos]

def tubeMap (m : Fin d.fillingCount) (y : ℂ × Circle) : W.pieceInterior ⊤ :=
  ⟨C.tube m (C.tubeClamp y),
    trivial, C.tube_interior m ((C.tube m).map_source (C.tubeClamp_mem_source m y))⟩

theorem tubeMap_val {m : Fin d.fillingCount} {y : ℂ × Circle} (hy : ‖y.1‖ < 1 + C.ε) :
    (C.tubeMap m y : W.Carrier) = C.tube m y := by
  change C.tube m (C.tubeClamp y) = _
  rw [tubeClamp, ite_eq_left hy]

theorem tubeMap_injOn (m : Fin d.fillingCount) :
    InjOn (C.tubeMap m) {y | ‖y.1‖ < 1 + C.ε} := by
  intro y hy y' hy' h
  have h' := congrArg (fun x : W.pieceInterior ⊤ => (x : W.Carrier)) h
  simp only [C.tubeMap_val hy, C.tubeMap_val hy'] at h'
  exact (C.tube m).injOn (by rw [C.tube_source]; exact hy) (by rw [C.tube_source]; exact hy') h'

theorem isLocalDiffeomorphAt_tubeMap {m : Fin d.fillingCount} {y : ℂ × Circle}
    (hy : ‖y.1‖ < 1 + C.ε) :
    letI := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior ⊤)
    IsLocalDiffeomorphAt PlaneCircleModel (𝓡 3) ∞ (C.tubeMap m) y := by
  let _ := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior ⊤)
  have hsrc : y ∈ (C.tube m).source := by rw [C.tube_source]; exact hy
  have hopen : IsOpen {y : ℂ × Circle | ‖y.1‖ < 1 + C.ε} :=
    isOpen_lt (continuous_norm.comp continuous_fst) continuous_const
  have hclamp : IsLocalDiffeomorphAt PlaneCircleModel W.model ∞
      (fun y => C.tube m (C.tubeClamp y)) y := by
    refine IsLocalDiffeomorphAt.of_eventuallyEq ?_
      ((C.tube m).isLocalDiffeomorphAt PlaneCircleModel W.model ∞ hsrc)
    filter_upwards [hopen.mem_nhds hy] with z hz
    rw [tubeClamp, ite_eq_left hz]
  have hcod := isLocalDiffeomorphAt_subtypeCodRestrict
    (V := W.pieceInterior ⊤) (fun z => (C.tubeMap m z).property) hclamp
  exact IsLocalDiffeomorphAt.comp (hf := hcod)
    (hg := (Manifold.interiorAtlasDiffeomorph W.model ∞ (M := W.pieceInterior ⊤)).isLocalDiffeomorph
      _)

theorem tubeMap_eq_iff_of_core {m m' : Fin d.fillingCount} {y y' : ℂ × Circle}
    (hy : ‖y.1‖ < 1 + C.ε) (hy' : ‖y'.1‖ < 1 + C.ε) :
    C.tubeMap m y = C.tubeMap m' y' ↔ m = m' ∧ y = y' := by
  constructor
  · intro h
    have h' := congrArg (fun x : W.pieceInterior ⊤ => (x : W.Carrier)) h
    simp only [C.tubeMap_val hy, C.tubeMap_val hy'] at h'
    have hm : m = m' := by
      by_contra hne
      have hd := C.disjoint hne
      exact Set.disjoint_left.mp hd ((C.tube m).map_source (by rw [C.tube_source]; exact hy))
        (h' ▸ (C.tube m').map_source (by rw [C.tube_source]; exact hy'))
    subst hm
    exact ⟨rfl, C.tubeMap_injOn m hy hy' h⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem tube_core_not_mem_productRegion {m : Fin d.fillingCount} {y : ℂ × Circle}
    (hy : ‖y.1‖ ≤ 1) : (C.tube m y : W.Carrier) ∉ C.productRegion := by
  intro hp
  have hsrc : y ∈ (C.tube m).source := by
    rw [C.tube_source]
    change ‖y.1‖ < 1 + C.ε
    linarith [C.ε_pos]
  have hmem : (C.tube m y : W.Carrier) ∈ (C.tube m).target ∩ C.productRegion :=
    ⟨(C.tube m).map_source hsrc, hp⟩
  rw [C.tube_product_overlap m] at hmem
  obtain ⟨y', hy', he⟩ := hmem
  rw [C.transitionDomain_eq] at hy'
  have hsrc' : y' ∈ (C.tube m).source := by rw [C.tube_source]; exact hy'.2
  have := (C.tube m).injOn hsrc' hsrc he
  rw [this] at hy'
  linarith [hy'.1]

section Inner

variable {m : Fin d.fillingCount} (hk : d.k = 3) (hj : (C.port (.inr m)).val ≠ 0)
  (hp : 0 < (d.fillingSlope m).1)

include hp in
theorem fillingOrder_pos : 0 < d.fillingOrder m := by
  unfold SeifertData.fillingOrder
  omega

include hp in
theorem fillingSlope_eq_fillingOrder : (d.fillingSlope m).1 = (d.fillingOrder m : ℤ) := by
  unfold SeifertData.fillingOrder
  omega

include hk hj in
theorem tubeCentre_cases : C.tubeCentre m = 3 / 2 ∨ C.tubeCentre m = -(3 / 2) := by
  have hlt : (C.port (.inr m)).val < 3 := hk ▸ (C.port (.inr m)).isLt
  unfold tubeCentre planarCenter
  have hk2 : d.k ≠ 2 := by omega
  rw [ite_eq_right hk2]
  rcases (show (C.port (.inr m)).val = 1 ∨ (C.port (.inr m)).val = 2 by omega) with h | h
  · left
    rw [ite_eq_left h]
    push_cast
    ring
  · right
    rw [ite_eq_right (by omega), ite_eq_left h]
    push_cast
    ring

include hk hj in
theorem norm_tubeCentre : ‖C.tubeCentre m‖ = 3 / 2 := by
  rcases C.tubeCentre_cases hk hj with h | h <;> rw [h] <;> norm_num [Complex.norm_real]

include hj in
theorem seamModel_eq_seamDir :
    seamModel d m (C.port (.inr m)) (C.matrix m) = C.seamDir m := by
  funext y
  have hA := C.matrix_eq m
  have h00 : (C.matrix m : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = -(d.fillingSlope m).1 := by
    rw [hA]; rfl
  have h01 : (C.matrix m : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = C.a m := by rw [hA]; rfl
  have h10 : (C.matrix m : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = -(d.fillingSlope m).2 := by
    rw [hA]; rfl
  have h11 : (C.matrix m : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = C.b m := by rw [hA]; rfl
  have hrad : planarRadius (C.port (.inr m)) = 1 / 2 := by simp [planarRadius, hj]
  apply Prod.ext
  · simp only [seamModel, linearTorusMap, h00, h01, hrad, hj, ite_false, seamDir, seamFwd,
      tubeCentre, SeifertData.fillingOrder]
    rw [← Circle.coe_inv_eq_conj]
    simp only [mul_inv, ← zpow_neg, neg_neg]
    push_cast
    ring
  · simp only [seamModel, linearTorusMap, h10, h11, seamDir, seamFwd]

include hp in
theorem seamDir_seamInv {y : ℂ × Circle} (hy : y.1 ≠ C.tubeCentre m) :
    C.seamDir m (C.seamInv m y) = y :=
  seamFwd_seamBwd (fillingOrder_pos hp).ne' (C.bezout m) hy

include hp in
theorem seamInv_seamDir {y : ℂ × Circle} (hy : y.1 ≠ 0) :
    C.seamInv m (C.seamDir m y) = y :=
  seamBwd_seamFwd (fillingOrder_pos hp).ne' (C.bezout m) hy

theorem norm_seamInv_fst (y : ℂ × Circle) :
    ‖(C.seamInv m y).1‖ = (2 * ‖y.1 - C.tubeCentre m‖) ^ ((d.fillingOrder m : ℝ)⁻¹) :=
  norm_seamBwd_fst y

include hp in
theorem norm_seamInv_fst_lt_iff {y : ℂ × Circle} {r : ℝ} (hr : 0 < r) :
    ‖(C.seamInv m y).1‖ < r ↔ ‖y.1 - C.tubeCentre m‖ < r ^ d.fillingOrder m / 2 := by
  rw [C.norm_seamInv_fst]
  have hP : (0 : ℝ) < d.fillingOrder m := by exact_mod_cast fillingOrder_pos hp
  have h0 : 0 ≤ 2 * ‖y.1 - C.tubeCentre m‖ := by positivity
  rw [Real.rpow_inv_lt_iff_of_pos h0 hr.le hP, Real.rpow_natCast]
  constructor <;> intro h <;> linarith

include hp in
theorem lt_norm_seamInv_fst_iff {y : ℂ × Circle} {r : ℝ} (hr : 0 < r) :
    r < ‖(C.seamInv m y).1‖ ↔ r ^ d.fillingOrder m / 2 < ‖y.1 - C.tubeCentre m‖ := by
  rw [C.norm_seamInv_fst]
  have hP : (0 : ℝ) < d.fillingOrder m := by exact_mod_cast fillingOrder_pos hp
  have h0 : 0 ≤ 2 * ‖y.1 - C.tubeCentre m‖ := by positivity
  rw [Real.lt_rpow_inv_iff_of_pos hr.le h0 hP, Real.rpow_natCast]
  constructor <;> intro h <;> linarith

theorem collarRadius_le : C.collarRadius m ≤ (1 + C.ε) ^ d.fillingOrder m / 2 := min_le_left _ _

theorem collarRadius_le_three_halves : C.collarRadius m ≤ 3 / 2 := min_le_right _ _

include hp in
theorem half_lt_collarRadius : 1 / 2 < C.collarRadius m := by
  unfold collarRadius
  apply lt_min _ (by norm_num)
  have h1 : 1 < (1 + C.ε) ^ d.fillingOrder m :=
    one_lt_pow₀ (by linarith [C.ε_pos]) (fillingOrder_pos hp).ne'
  linarith

include hp in
theorem norm_seamInv_lt_of_collar {y : ℂ × Circle}
    (hy : ‖y.1 - C.tubeCentre m‖ < C.collarRadius m) :
    ‖(C.seamInv m y).1‖ < 1 + C.ε :=
  (C.norm_seamInv_fst_lt_iff hp (by linarith [C.ε_pos])).2 (hy.trans_le C.collarRadius_le)

include hj hp in
theorem tubeMap_seamInv {y : ℂ × Circle} (h1 : 1 / 2 < ‖y.1 - C.tubeCentre m‖)
    (h2 : ‖y.1 - C.tubeCentre m‖ < C.collarRadius m) (hy : y.1 ∈ planarOpen d.k) :
    C.tubeMap m (C.seamInv m y) = C.chartProductMap (⟨y.1, hy⟩, y.2) := by
  have hne : y.1 ≠ C.tubeCentre m := by
    intro h
    rw [h, sub_self, norm_zero] at h1
    norm_num at h1
  have htr : C.seamInv m y ∈ C.transitionDomain := by
    rw [C.transitionDomain_eq]
    refine ⟨?_, C.norm_seamInv_lt_of_collar hp h2⟩
    exact (C.lt_norm_seamInv_fst_iff hp one_pos).2 (by rw [one_pow]; linarith)
  have key : seamModel d m (C.port (.inr m)) (C.matrix m) (C.seamInv m y) = y := by
    rw [C.seamModel_eq_seamDir hj, C.seamDir_seamInv hp hne]
  apply Subtype.ext
  rw [C.tubeMap_val (C.norm_seamInv_lt_of_collar hp h2), C.transition m _ htr,
    C.chartProductMap_val]
  have k1 : (seamModel d m (C.port (.inr m)) (C.matrix m) (C.seamInv m y)).1 = y.1 :=
    congrArg Prod.fst key
  have k2 : (seamModel d m (C.port (.inr m)) (C.matrix m) (C.seamInv m y)).2 = y.2 :=
    congrArg Prod.snd key
  exact congrArg (fun z => (C.product z : W.Carrier)) (Prod.ext (Subtype.ext k1) k2)

end Inner

section Punctured

variable (hk : d.k = 3) (hj : ∀ m : Fin d.fillingCount, (C.port (.inr m)).val ≠ 0)
  (hp : ∀ m : Fin d.fillingCount, 0 < (d.fillingSlope m).1)

include hk in
theorem zero_mem_planarOpen : (0 : ℂ) ∈ planarOpen d.k :=
  mem_planarOpen_of_planarFunction_neg hk ((planarFunction_three_neg_iff 0).2 (by norm_num))

include hk hj in
theorem port_val_eq_of_tubeCentre_eq {m m' : Fin d.fillingCount}
    (h : C.tubeCentre m = C.tubeCentre m') : (C.port (.inr m)).val = (C.port (.inr m')).val := by
  have hlt : (C.port (.inr m)).val < 3 := hk ▸ (C.port (.inr m)).isLt
  have hlt' : (C.port (.inr m')).val < 3 := hk ▸ (C.port (.inr m')).isLt
  have hj1 := hj m
  have hj2 := hj m'
  unfold tubeCentre planarCenter at h
  have hk2 : d.k ≠ 2 := by omega
  rw [ite_eq_right hk2, ite_eq_right hk2] at h
  rcases (show (C.port (.inr m)).val = 1 ∨ (C.port (.inr m)).val = 2 by omega) with h1 | h1 <;>
    rcases (show (C.port (.inr m')).val = 1 ∨ (C.port (.inr m')).val = 2 by omega) with h2 | h2
  · rw [h1, h2]
  · rw [ite_eq_left h1, ite_eq_right (by omega : ¬(C.port (.inr m')).val = 1),
      ite_eq_left h2] at h
    have := congrArg Complex.re h
    norm_num at this
  · rw [ite_eq_right (by omega : ¬(C.port (.inr m)).val = 1), ite_eq_left h1,
      ite_eq_left h2] at h
    have := congrArg Complex.re h
    norm_num at this
  · rw [h1, h2]

include hk hj in
theorem collar_unique {ζ : ℂ} {m m' : Fin d.fillingCount}
    (hm : ‖ζ - C.tubeCentre m‖ < C.collarRadius m)
    (hm' : ‖ζ - C.tubeCentre m'‖ < C.collarRadius m') : m = m' := by
  by_contra hne
  have hc : C.tubeCentre m ≠ C.tubeCentre m' := by
    intro h
    apply hne
    have hv := C.port_val_eq_of_tubeCentre_eq hk hj h
    have := C.port.injective (Fin.ext hv)
    exact Sum.inr_injective this
  have hsum : C.tubeCentre m' = -C.tubeCentre m := by
    rcases C.tubeCentre_cases hk (hj m) with h1 | h1 <;>
      rcases C.tubeCentre_cases hk (hj m') with h2 | h2 <;>
      simp_all
  have hdist : ‖C.tubeCentre m - C.tubeCentre m'‖ = 3 := by
    rw [hsum, sub_neg_eq_add, ← two_mul, norm_mul, C.norm_tubeCentre hk (hj m)]
    norm_num
  have htri := norm_sub_le_norm_sub_add_norm_sub (C.tubeCentre m) ζ (C.tubeCentre m')
  rw [norm_sub_rev (C.tubeCentre m) ζ] at htri
  linarith [C.collarRadius_le_three_halves (m := m), C.collarRadius_le_three_halves (m := m')]

include hk hj in
theorem mem_planarOpen_of_collar {ζ : ℂ} {m : Fin d.fillingCount}
    (h1 : 1 / 2 < ‖ζ - C.tubeCentre m‖) (h2 : ‖ζ - C.tubeCentre m‖ < C.collarRadius m) :
    ζ ∈ planarOpen d.k := by
  apply mem_planarOpen_of_planarFunction_neg hk
  rw [planarFunction_three_neg_iff]
  have hR := C.collarRadius_le_three_halves (m := m)
  have hn := norm_sub_norm_le ζ (C.tubeCentre m)
  rw [C.norm_tubeCentre hk (hj m)] at hn
  rcases C.tubeCentre_cases hk (hj m) with h | h <;> rw [h] at h1 h2 hn
  · refine ⟨by linarith, h1, ?_⟩
    have h3 : ‖(3 : ℂ)‖ = 3 := by norm_num
    have := norm_sub_le (ζ + 3 / 2) (ζ - 3 / 2)
    rw [show ζ + 3 / 2 - (ζ - 3 / 2) = (3 : ℂ) by ring, h3] at this
    linarith
  · refine ⟨by linarith, ?_, by rwa [sub_neg_eq_add] at h1⟩
    have h3 : ‖(3 : ℂ)‖ = 3 := by norm_num
    have := norm_sub_le (ζ + 3 / 2) (ζ - 3 / 2)
    rw [show ζ + 3 / 2 - (ζ - 3 / 2) = (3 : ℂ) by ring, h3] at this
    rw [sub_neg_eq_add] at h2
    linarith

open Classical in
def puncturedChart (y : ℂ × Circle) : W.pieceInterior ⊤ :=
  if h : y.1 ∈ planarOpen d.k then C.chartProductMap (⟨y.1, h⟩, y.2)
  else if h' : ∃ m, ‖y.1 - C.tubeCentre m‖ < C.collarRadius m then
    C.tubeMap h'.choose (C.seamInv h'.choose y)
  else C.chartProductMap (⟨0, zero_mem_planarOpen hk⟩, y.2)

def puncturedDomain : Set (ℂ × Circle) :=
  {y | y.1 ∈ planarOpen d.k} ∪
    ⋃ m, {y | ‖y.1 - C.tubeCentre m‖ < C.collarRadius m ∧ y.1 ≠ C.tubeCentre m}

theorem mem_puncturedDomain {y : ℂ × Circle} : y ∈ C.puncturedDomain ↔ y.1 ∈ planarOpen d.k ∨
    ∃ m, ‖y.1 - C.tubeCentre m‖ < C.collarRadius m ∧ y.1 ≠ C.tubeCentre m := by
  simp [puncturedDomain]

theorem isOpen_puncturedDomain : IsOpen C.puncturedDomain := by
  apply IsOpen.union ((planarOpen d.k).isOpen.preimage continuous_fst)
  refine isOpen_iUnion fun m => IsOpen.inter ?_ ?_
  · exact isOpen_lt (continuous_norm.comp (continuous_fst.sub continuous_const)) continuous_const
  · exact isOpen_ne.preimage continuous_fst

theorem puncturedChart_of_mem_planarOpen {y : ℂ × Circle} (h : y.1 ∈ planarOpen d.k) :
    C.puncturedChart hk y = C.chartProductMap (⟨y.1, h⟩, y.2) :=
  dite_eq_left h

include hj hp in
theorem puncturedChart_of_collar {y : ℂ × Circle} {m : Fin d.fillingCount}
    (hm : ‖y.1 - C.tubeCentre m‖ < C.collarRadius m) :
    C.puncturedChart hk y = C.tubeMap m (C.seamInv m y) := by
  by_cases h : y.1 ∈ planarOpen d.k
  · rw [C.puncturedChart_of_mem_planarOpen hk h]
    have h1 : 1 / 2 < ‖y.1 - C.tubeCentre m‖ := chartPlanarInterior_hole_lt h _ (hj m)
    exact (C.tubeMap_seamInv (hj m) (hp m) h1 hm h).symm
  · have h' : ∃ m, ‖y.1 - C.tubeCentre m‖ < C.collarRadius m := ⟨m, hm⟩
    have hc : h'.choose = m := C.collar_unique hk hj h'.choose_spec hm
    unfold puncturedChart
    rw [dite_eq_right h, dite_eq_left h', hc]

include hj hp in
theorem isLocalDiffeomorphAt_puncturedChart {y : ℂ × Circle} (hy : y ∈ C.puncturedDomain) :
    letI := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior ⊤)
    IsLocalDiffeomorphAt PlaneCircleModel (𝓡 3) ∞ (C.puncturedChart hk) y := by
  let _ := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior ⊤)
  rcases C.mem_puncturedDomain.1 hy with h | ⟨m, hm, hne⟩
  · let e : planarOpen d.k × Circle → ℂ × Circle :=
      Prod.map (Subtype.val : planarOpen d.k → ℂ) (id : Circle → Circle)
    have he : IsLocalDiffeomorphAt PlaneCircleModel PlaneCircleModel ∞ e (⟨y.1, h⟩, y.2) :=
      (isLocalDiffeomorph_subtype_val (planarOpen d.k) _).prodMap
        ((Diffeomorph.refl (𝓡 1) Circle ∞).isLocalDiffeomorph _)
    have hcomp : C.puncturedChart hk ∘ e = C.chartProductMap := by
      funext z
      exact C.puncturedChart_of_mem_planarOpen hk z.1.2
    have hgf : IsLocalDiffeomorphAt PlaneCircleModel (𝓡 3) ∞ (C.puncturedChart hk ∘ e)
        (⟨y.1, h⟩, y.2) := by
      rw [hcomp]
      exact C.isLocalDiffeomorph_chartProductMap _
    exact isLocalDiffeomorphAt_of_comp hgf he
  · have hopen : IsOpen {z : ℂ × Circle | ‖z.1 - C.tubeCentre m‖ < C.collarRadius m ∧
        z.1 ≠ C.tubeCentre m} :=
      (isOpen_lt (continuous_norm.comp (continuous_fst.sub continuous_const))
        continuous_const).inter (isOpen_ne.preimage continuous_fst)
    have hs := isLocalDiffeomorphAt_seamBwd (c := C.tubeCentre m) (P := d.fillingOrder m)
      (p := (d.fillingSlope m).1) (q := (d.fillingSlope m).2) (a := C.a m) (b := C.b m)
      (fillingOrder_pos (hp m)).ne' (C.bezout m) hne
    have ht := C.isLocalDiffeomorphAt_tubeMap (m := m) (C.norm_seamInv_lt_of_collar (hp m) hm)
    refine IsLocalDiffeomorphAt.of_eventuallyEq ?_ (IsLocalDiffeomorphAt.comp (hf := hs) (hg := ht))
    filter_upwards [hopen.mem_nhds ⟨hm, hne⟩] with z hz
    exact C.puncturedChart_of_collar hk hj hp hz.1

include hk hj hp in
theorem puncturedChart_core {y : ℂ × Circle} (hy : y ∈ C.puncturedDomain)
    (h : y.1 ∉ planarOpen d.k) : ∃ m, C.puncturedChart hk y = C.tubeMap m (C.seamInv m y) ∧
      ‖(C.seamInv m y).1‖ ≤ 1 ∧ (C.seamInv m y).1 ≠ 0 ∧ y.1 ≠ C.tubeCentre m := by
  rcases C.mem_puncturedDomain.1 hy with h' | ⟨m, hm, hne⟩
  · exact absurd h' h
  refine ⟨m, C.puncturedChart_of_collar hk hj hp hm, ?_, seamBwd_fst_ne_zero hne, hne⟩
  have hle : ‖y.1 - C.tubeCentre m‖ ≤ 1 / 2 := by
    by_contra hlt
    exact h (C.mem_planarOpen_of_collar hk hj (lt_of_not_ge hlt) hm)
  by_contra hgt
  have := (C.lt_norm_seamInv_fst_iff (hp m) one_pos).1 (lt_of_not_ge hgt)
  rw [one_pow] at this
  linarith

include hj hp in
theorem puncturedChart_injOn : InjOn (C.puncturedChart hk) C.puncturedDomain := by
  intro y hy y' hy' heq
  by_cases h : y.1 ∈ planarOpen d.k <;> by_cases h' : y'.1 ∈ planarOpen d.k
  · rw [C.puncturedChart_of_mem_planarOpen hk h, C.puncturedChart_of_mem_planarOpen hk h'] at heq
    have := C.chartProductMap_injective heq
    have h1 : y.1 = y'.1 := congrArg (fun z : planarOpen d.k × Circle => (z.1 : ℂ)) this
    have h2 : y.2 = y'.2 := congrArg (fun z : planarOpen d.k × Circle => z.2) this
    exact Prod.ext h1 h2
  · obtain ⟨m', hm', hle', -⟩ := C.puncturedChart_core hk hj hp hy' h'
    rw [C.puncturedChart_of_mem_planarOpen hk h, hm'] at heq
    have hv := congrArg (fun x : W.pieceInterior ⊤ => (x : W.Carrier)) heq
    simp only [C.chartProductMap_val, C.tubeMap_val (by linarith [C.ε_pos] :
      ‖(C.seamInv m' y').1‖ < 1 + C.ε)] at hv
    exact absurd (hv ▸ (C.product _).2) (C.tube_core_not_mem_productRegion hle')
  · obtain ⟨m, hm, hle, -⟩ := C.puncturedChart_core hk hj hp hy h
    rw [C.puncturedChart_of_mem_planarOpen hk h', hm] at heq
    have hv := congrArg (fun x : W.pieceInterior ⊤ => (x : W.Carrier)) heq
    simp only [C.chartProductMap_val, C.tubeMap_val (by linarith [C.ε_pos] :
      ‖(C.seamInv m y).1‖ < 1 + C.ε)] at hv
    exact absurd (hv.symm ▸ (C.product _).2) (C.tube_core_not_mem_productRegion hle)
  · obtain ⟨m, hm, hle, -, hne⟩ := C.puncturedChart_core hk hj hp hy h
    obtain ⟨m', hm', hle', -, hne'⟩ := C.puncturedChart_core hk hj hp hy' h'
    rw [hm, hm'] at heq
    obtain ⟨rfl, hs⟩ := (C.tubeMap_eq_iff_of_core (by linarith [C.ε_pos])
      (by linarith [C.ε_pos])).1 heq
    rw [← C.seamDir_seamInv (hp m) hne, hs, C.seamDir_seamInv (hp m) hne']

include hj hp in
theorem puncturedChart_ne_tubeMap_zero {y : ℂ × Circle} (hy : y ∈ C.puncturedDomain)
    (m : Fin d.fillingCount) (w : Circle) : C.puncturedChart hk y ≠ C.tubeMap m (0, w) := by
  intro heq
  have h0 : ‖((0 : ℂ), w).1‖ < 1 + C.ε := by
    change ‖(0 : ℂ)‖ < 1 + C.ε
    rw [norm_zero]
    linarith [C.ε_pos]
  by_cases h : y.1 ∈ planarOpen d.k
  · rw [C.puncturedChart_of_mem_planarOpen hk h] at heq
    have hv := congrArg (fun x : W.pieceInterior ⊤ => (x : W.Carrier)) heq
    simp only [C.chartProductMap_val, C.tubeMap_val h0] at hv
    exact C.tube_core_not_mem_productRegion (m := m) (y := ((0 : ℂ), w))
      (by change ‖(0 : ℂ)‖ ≤ 1; rw [norm_zero]; norm_num) (hv ▸ (C.product _).2)
  · obtain ⟨m', hm', hle', hne0, -⟩ := C.puncturedChart_core hk hj hp hy h
    rw [hm'] at heq
    obtain ⟨-, hs⟩ := (C.tubeMap_eq_iff_of_core (by linarith [C.ε_pos]) h0).1 heq
    exact hne0 (congrArg Prod.fst hs)

include hj hp in
theorem exists_puncturedChart_eq (x : W.pieceInterior ⊤) :
    (∃ y ∈ C.puncturedDomain, C.puncturedChart hk y = x) ∨
      ∃ m w, x = C.tubeMap m (0, w) := by
  have hprod : (x : W.Carrier) ∈ C.productRegion →
      ∃ y ∈ C.puncturedDomain, C.puncturedChart hk y = x := by
    intro hx
    obtain ⟨z, hz⟩ := C.exists_chartProductMap_eq hx
    refine ⟨((z.1 : ℂ), z.2), C.mem_puncturedDomain.2 (Or.inl z.1.2), ?_⟩
    rw [C.puncturedChart_of_mem_planarOpen hk z.1.2]
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
  · left
    have hne : (C.seamDir m v).1 ≠ C.tubeCentre m := seamFwd_fst_ne h0
    have hdist : ‖(C.seamDir m v).1 - C.tubeCentre m‖ < C.collarRadius m := by
      rw [seamDir, norm_seamFwd_sub]
      have : ‖v.1‖ ^ d.fillingOrder m ≤ 1 := pow_le_one₀ (norm_nonneg _) (le_of_not_gt h1)
      linarith [C.half_lt_collarRadius (hp m)]
    refine ⟨C.seamDir m v, C.mem_puncturedDomain.2 (Or.inr ⟨m, hdist, hne⟩), ?_⟩
    rw [C.puncturedChart_of_collar hk hj hp hdist, C.seamInv_seamDir (hp m) h0, htm]

end Punctured

end SeifertBlockCharts

end GC.Seifert
