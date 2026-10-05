import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.ExtPortBandXPI

/-!
# FC39 external-port regression instance: carrier, ports and the two cusp cores

The carrier `carrierW_XPI = annulusCircleCarrier` (`{1/2 ≤ |z| ≤ 3} × S¹`) with its two product
boundary tori `portsE_XPI = productBoundaryTori 2` — a NON-EMPTY external port family (port `0`:
the outer torus `|z| = 3`, collar target `|z| > 11/4`; port `1`: the inner torus `|z| = 1/2`,
conjugate twist, collar target `|z| < 3/4`).

* the radius `rad_XPI`, the interior `1/2 < rad < 3`, regularity of radial functions;
* the cusp core `b`: the band from the external radius `3` / `1/2` to the internal radius `2` / `1`
  with the twist of the port (`cuspRadii_XPI b`), cusp function `σ_b (rad² − ρ_b²)`;
* **`extportCuspCores_XPI : CuspCores carrierW_XPI portsE_XPI`** (two cusps, both ports owned).
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology ComplexConjugate

namespace GC.GraphManifold.Assembly.FC39P0.ExtPortXPI

/-- The carrier of the external-port instance: `T² × I` as the annulus carrier. -/
abbrev carrierW_XPI : CompactCarrier.{0} := annulusCircleCarrier.{0}

/-- The two external ports: the product boundary tori. -/
abbrev portsE_XPI : BoundaryTori carrierW_XPI 2 := productBoundaryTori.{0} 2 (Or.inl rfl)

local instance carrierCharts_XPI' :
    ChartedSpace (EuclideanHalfSpace 3) carrierW_XPI.Carrier := by
  change ChartedSpace (EuclideanHalfSpace 3) (productSet.{0} 2)
  exact inferInstance

local instance carrierSmooth_XPI' : IsManifold (𝓡∂ 3) ∞ carrierW_XPI.Carrier := by
  change IsManifold (𝓡∂ 3) ∞ (productSet.{0} 2)
  exact inferInstance

/-! ## The radius -/

/-- The radius `|z|` of a carrier point. -/
def rad_XPI (x : carrierW_XPI.Carrier) : ℝ := ‖x.val.1.down‖

theorem continuous_rad_XPI : Continuous rad_XPI :=
  continuous_norm.comp (contMDiff_planeLift_down.continuous.comp
    (continuous_fst.comp continuous_subtype_val))

theorem rad_bounds_XPI (x : carrierW_XPI.Carrier) : 1 / 2 ≤ rad_XPI x ∧ rad_XPI x ≤ 3 :=
  torusMonodromyNormBounds x

theorem rad_pos_XPI (x : carrierW_XPI.Carrier) : 0 < rad_XPI x := by
  linarith [(rad_bounds_XPI x).1]

theorem carrier_ne_zero_XPI (x : carrierW_XPI.Carrier) : x.val.1.down ≠ 0 :=
  norm_pos_iff.mp (rad_pos_XPI x)

theorem carrier_isBoundaryPoint_iff_XPI {x : carrierW_XPI.Carrier} :
    (𝓡∂ 3).IsBoundaryPoint x ↔ rad_XPI x = 1 / 2 ∨ rad_XPI x = 3 := by
  refine (productSet_isBoundaryPoint_iff.{0} 2 x).trans ?_
  rw [planarFunction_eq_zero_iff (Or.inl rfl), Fin.exists_fin_two]
  simp [planarCenter, planarRadius, rad_XPI, or_comm]

/-- The interior of the carrier: `1/2 < rad < 3`. -/
theorem mem_carrier_interior_XPI {x : carrierW_XPI.Carrier} (h1 : 1 / 2 < rad_XPI x)
    (h2 : rad_XPI x < 3) : x ∈ carrierW_XPI.interior := by
  change (𝓡∂ 3).IsInteriorPoint x
  rw [ModelWithCorners.isInteriorPoint_iff_not_isBoundaryPoint, carrier_isBoundaryPoint_iff_XPI]
  rintro (h | h) <;> linarith

/-! ## Radial functions and their regularity -/

/-- The ambient radial function `c + σ |z|²`. -/
def radialFn_XPI (c σ : ℝ) (p : PlaneLift.{0} × Circle) : ℝ := c + σ * ‖p.1.down‖ ^ 2

theorem contMDiff_radialFn_XPI (c σ : ℝ) :
    ContMDiff (𝓘(ℝ, ℂ).prod (𝓡 1)) 𝓘(ℝ, ℝ) ∞ (radialFn_XPI c σ) := by
  have h1 : ContDiff ℝ ∞ (fun w : ℂ => c + σ * ‖w‖ ^ 2) :=
    contDiff_const.add (contDiff_const.mul (contDiff_norm_sq ℝ))
  exact (h1.contMDiff.comp contMDiff_planeLift_down).comp contMDiff_fst

theorem radialFn_regular_XPI {c σ : ℝ} (hσ : σ ≠ 0) (p : PlaneLift.{0} × Circle)
    (hp : p.1.down ≠ 0) :
    mfderiv (𝓘(ℝ, ℂ).prod (𝓡 1)) 𝓘(ℝ, ℝ) (radialFn_XPI c σ) p ≠ 0 := by
  refine mfderiv_ne_zero_of_comp (J := 𝓘(ℝ, ℂ))
    (s := fun w : ℂ => ((ULift.up w : PlaneLift.{0}), p.2)) (y := p.1.down)
    ((contMDiff_radialFn_XPI c σ).mdifferentiableAt (by simp))
    ((contMDiff_planeLift_up.prodMk contMDiff_const).mdifferentiableAt (by simp)) ?_
  change mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) (fun w : ℂ => c + σ * ‖w‖ ^ 2) p.1.down ≠ 0
  rw [mfderiv_eq_fderiv]
  have hq : HasFDerivAt (fun w : ℂ => ‖w‖ ^ 2)
      (2 • (innerSL ℝ p.1.down).comp (ContinuousLinearMap.id ℝ ℂ)) p.1.down :=
    (hasFDerivAt_id p.1.down).norm_sq
  rw [((hq.const_mul σ).const_add c).fderiv]
  intro h
  have h1 := DFunLike.congr_fun h p.1.down
  change σ * ((2 : ℕ) • inner ℝ p.1.down p.1.down) = 0 at h1
  rw [real_inner_self_eq_norm_sq, nsmul_eq_mul, Nat.cast_ofNat] at h1
  have hn : ‖p.1.down‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hp)
  exact mul_ne_zero hσ (mul_ne_zero two_ne_zero hn) h1

theorem contMDiff_carrier_val_XPI :
    ContMDiff (𝓡∂ 3) (𝓘(ℝ, ℂ).prod (𝓡 1)) ∞
      (Subtype.val : carrierW_XPI.Carrier → PlaneLift.{0} × Circle) :=
  (productAtlas.{0} 2).contMDiff_subtype_val

/-- A carrier function pulled back from an ambient function with nonzero differential has
nonzero differential. -/
theorem carrier_regular_of_ambient_XPI {F : PlaneLift.{0} × Circle → ℝ}
    (hF : ContMDiff (𝓘(ℝ, ℂ).prod (𝓡 1)) 𝓘(ℝ, ℝ) ∞ F) (x : carrierW_XPI.Carrier)
    (hx : mfderiv (𝓘(ℝ, ℂ).prod (𝓡 1)) 𝓘(ℝ, ℝ) F x.val ≠ 0) :
    mfderiv (𝓡∂ 3) 𝓘(ℝ, ℝ) (fun y : carrierW_XPI.Carrier => F y.val) x ≠ 0 := by
  have hval := (productAtlas.{0} 2).mfderiv_subtypeVal_bijective x
  have hchain := mfderiv_comp x (hF.mdifferentiableAt (by simp))
    (contMDiff_carrier_val_XPI.mdifferentiableAt (by simp))
  intro hzero
  have hz : mfderiv (𝓡∂ 3) 𝓘(ℝ, ℝ)
      (F ∘ (Subtype.val : carrierW_XPI.Carrier → PlaneLift.{0} × Circle)) x = 0 := hzero
  have hc := hchain.symm.trans hz
  apply hx
  ext v
  obtain ⟨u, hu⟩ := hval.2 v
  have hv := DFunLike.congr_fun hc u
  change mfderiv (𝓘(ℝ, ℂ).prod (𝓡 1)) 𝓘(ℝ, ℝ) F x.val
    ((mfderiv (𝓡∂ 3) (𝓘(ℝ, ℂ).prod (𝓡 1))
      (Subtype.val : carrierW_XPI.Carrier → PlaneLift.{0} × Circle) x) u) = 0 at hv
  rw [hu] at hv
  exact hv

/-- The carrier radial function `c + σ rad²`. -/
def carrierRadialFn_XPI (c σ : ℝ) (x : carrierW_XPI.Carrier) : ℝ := c + σ * rad_XPI x ^ 2

theorem contMDiff_carrierRadialFn_XPI (c σ : ℝ) :
    ContMDiff (𝓡∂ 3) 𝓘(ℝ, ℝ) ∞ (carrierRadialFn_XPI c σ) :=
  (contMDiff_radialFn_XPI c σ).comp contMDiff_carrier_val_XPI

theorem carrierRadialFn_regular_XPI {c σ : ℝ} (hσ : σ ≠ 0) (x : carrierW_XPI.Carrier) :
    mfderiv (𝓡∂ 3) 𝓘(ℝ, ℝ) (carrierRadialFn_XPI c σ) x ≠ 0 :=
  carrier_regular_of_ambient_XPI (contMDiff_radialFn_XPI c σ) x
    (radialFn_regular_XPI hσ x.val (carrier_ne_zero_XPI x))

/-! ## The ports -/

theorem portsE_torusMap_val_XPI (b : Fin 2) (t : Torus) :
    (portsE_XPI.torusMap b t).val =
      (ULift.up (planarCircleMap 2 b t.1), t.2) := by
  change ((planarCollar.{0} 2 (Or.inl rfl) b (t.1, halfZero)).val, t.2) = _
  rw [Prod.ext_iff]
  refine ⟨?_, rfl⟩
  apply ULift.ext
  exact planarCollar_zero_val.{0} (Or.inl rfl) b t.1

theorem planarCircleMap_eq_XPI (b : Fin 2) (t : Circle) :
    planarCircleMap 2 b t = planarRadius b • planarTwist b (t : ℂ) := by
  simp [planarCircleMap, planarCenter, planarTwist, Complex.real_smul]

theorem mem_portsE_target_zero_XPI {x : carrierW_XPI.Carrier} :
    x ∈ (portsE_XPI.collar 0).target ↔ 11 / 4 < rad_XPI x := by
  change -1 * (‖x.val.1.down - ((0 : ℝ) : ℂ)‖ - 3) < 1 / 4 ↔ _
  simp only [Complex.ofReal_zero, sub_zero, rad_XPI]
  constructor <;> intro h <;> linarith

theorem mem_portsE_target_one_XPI {x : carrierW_XPI.Carrier} :
    x ∈ (portsE_XPI.collar 1).target ↔ rad_XPI x < 3 / 4 := by
  change 1 * (‖x.val.1.down - ((0 : ℝ) : ℂ)‖ - 1 / 2) < 1 / 4 ↔ _
  simp only [Complex.ofReal_zero, sub_zero, rad_XPI]
  constructor <;> intro h <;> linarith

theorem closure_portsE_target_zero_XPI :
    closure (portsE_XPI.collar 0).target ⊆ {x | 11 / 4 ≤ rad_XPI x} :=
  closure_minimal (fun _ hx => (mem_portsE_target_zero_XPI.mp hx).le)
    (isClosed_le continuous_const continuous_rad_XPI)

theorem closure_portsE_target_one_XPI :
    closure (portsE_XPI.collar 1).target ⊆ {x | rad_XPI x ≤ 3 / 4} :=
  closure_minimal (fun _ hx => (mem_portsE_target_one_XPI.mp hx).le)
    (isClosed_le continuous_rad_XPI continuous_const)

/-! ## The two cusp bands -/

/-- The internal radius of the cusp `b`: `2` (outer cusp `0`) or `1` (inner cusp `1`). -/
def cuspInternalRadius_XPI (b : Fin 2) : ℝ := if b.val = 0 then 2 else 1

/-- The band of the cusp `b`: from the port radius `planarRadius b` (`3` or `1/2`) to the
internal radius, with the twist of the port `b`. -/
def cuspRadii_XPI (b : Fin 2) : BandRadii_XPI where
  r0 := planarRadius b
  r1 := cuspInternalRadius_XPI b
  twist := b
  r0_ge := by unfold planarRadius; split_ifs <;> norm_num
  r0_le := by unfold planarRadius; split_ifs <;> norm_num
  r1_ge := by unfold cuspInternalRadius_XPI; split_ifs <;> norm_num
  r1_le := by unfold cuspInternalRadius_XPI; split_ifs <;> norm_num
  ne := by unfold planarRadius cuspInternalRadius_XPI; split_ifs <;> norm_num

/-- The cusp piece `b`. -/
def cuspPiece_XPI (b : Fin 2) : PieceEmbedding carrierW_XPI := bandPiece_XPI (cuspRadii_XPI b)

theorem range_cuspPiece_zero_XPI :
    range (cuspPiece_XPI 0).map = {x | 2 ≤ rad_XPI x} := by
  rw [cuspPiece_XPI, range_bandPiece_XPI]
  ext x
  have hb := rad_bounds_XPI x
  change (rad_XPI x - planarRadius (0 : Fin 2)) * (rad_XPI x - cuspInternalRadius_XPI 0) ≤ 0 ↔ _
  simp only [planarRadius, cuspInternalRadius_XPI, Fin.val_zero, ↓reduceIte]
  constructor
  · intro h
    change 2 ≤ rad_XPI x
    by_contra hlt
    rw [not_le] at hlt
    have : 0 < (rad_XPI x - 3) * (rad_XPI x - 2) :=
      mul_pos_of_neg_of_neg (by linarith) (by linarith)
    linarith
  · intro h
    have h' : 2 ≤ rad_XPI x := h
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith [hb.2]) (by linarith)

theorem range_cuspPiece_one_XPI :
    range (cuspPiece_XPI 1).map = {x | rad_XPI x ≤ 1} := by
  rw [cuspPiece_XPI, range_bandPiece_XPI]
  ext x
  have hb := rad_bounds_XPI x
  change (rad_XPI x - planarRadius (1 : Fin 2)) * (rad_XPI x - cuspInternalRadius_XPI 1) ≤ 0 ↔ _
  simp only [planarRadius, cuspInternalRadius_XPI, Fin.val_one, one_ne_zero, ↓reduceIte]
  constructor
  · intro h
    change rad_XPI x ≤ 1
    by_contra hlt
    rw [not_le] at hlt
    have : 0 < (rad_XPI x - 1 / 2) * (rad_XPI x - 1) :=
      mul_pos (by linarith) (by linarith)
    linarith
  · intro h
    have h' : rad_XPI x ≤ 1 := h
    exact mul_nonpos_of_nonneg_of_nonpos (by linarith [hb.1]) (by linarith)

theorem range_cuspInternal_XPI (b : Fin 2) :
    (range fun t => (cuspPiece_XPI b).map
        (bandProduct_XPI (cuspRadii_XPI b) (t, Assembly.iccEnd true))) =
      {x | rad_XPI x = cuspInternalRadius_XPI b} :=
  range_bandEnd_map_XPI (cuspRadii_XPI b) true

/-- The cusp function `σ_b (rad² − ρ_b²)` (`4 − rad²` outer, `rad² − 1` inner). -/
def cuspFn_XPI (b : Fin 2) : carrierW_XPI.Carrier → ℝ :=
  carrierRadialFn_XPI (-(planarSign b * cuspInternalRadius_XPI b ^ 2)) (planarSign b)

theorem planarSign_ne_zero_XPI (b : Fin 2) : planarSign b ≠ 0 := by
  unfold planarSign
  split_ifs <;> norm_num

/-- The face neighbourhood of the cusp `b`: `|rad − ρ_b| < 1/4`. -/
def cuspNear_XPI (b : Fin 2) : TopologicalSpace.Opens carrierW_XPI.Carrier :=
  ⟨{x | |rad_XPI x - cuspInternalRadius_XPI b| < 1 / 4},
    isOpen_lt (continuous_abs.comp (continuous_rad_XPI.sub continuous_const)) continuous_const⟩

theorem mem_cuspNear_XPI {b : Fin 2} {x : carrierW_XPI.Carrier} :
    x ∈ cuspNear_XPI b ↔ |rad_XPI x - cuspInternalRadius_XPI b| < 1 / 4 :=
  Iff.rfl

theorem cuspNear_interior_XPI (b : Fin 2) :
    (cuspNear_XPI b : Set carrierW_XPI.Carrier) ⊆ carrierW_XPI.interior := by
  intro x hx
  have hx' := abs_lt.mp (mem_cuspNear_XPI.mp hx)
  have hr : 1 ≤ cuspInternalRadius_XPI b ∧ cuspInternalRadius_XPI b ≤ 2 := by
    unfold cuspInternalRadius_XPI; split_ifs <;> norm_num
  exact mem_carrier_interior_XPI (by linarith [hx'.1, hr.1]) (by linarith [hx'.2, hr.2])

theorem cuspFn_eq_XPI (b : Fin 2) (x : carrierW_XPI.Carrier) :
    cuspFn_XPI b x = planarSign b * (rad_XPI x ^ 2 - cuspInternalRadius_XPI b ^ 2) := by
  rw [cuspFn_XPI, carrierRadialFn_XPI]
  ring

theorem cusp_internal_eq_XPI (b : Fin 2) :
    {x | rad_XPI x = cuspInternalRadius_XPI b} =
      {x | x ∈ cuspNear_XPI b ∧ cuspFn_XPI b x = 0} := by
  ext x
  have hσ := planarSign_ne_zero_XPI b
  have hr : 0 < cuspInternalRadius_XPI b := by
    unfold cuspInternalRadius_XPI; split_ifs <;> norm_num
  have hx := rad_pos_XPI x
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · change |rad_XPI x - cuspInternalRadius_XPI b| < 1 / 4
      rw [show rad_XPI x = cuspInternalRadius_XPI b from h, sub_self, abs_zero]
      norm_num
    · rw [cuspFn_eq_XPI, show rad_XPI x = cuspInternalRadius_XPI b from h, sub_self, mul_zero]
  · rintro ⟨-, h⟩
    rw [cuspFn_eq_XPI] at h
    have h2 : rad_XPI x ^ 2 - cuspInternalRadius_XPI b ^ 2 = 0 :=
      (mul_eq_zero.mp h).resolve_left hσ
    have h3 : (rad_XPI x - cuspInternalRadius_XPI b) *
        (rad_XPI x + cuspInternalRadius_XPI b) = 0 := by
      rw [← h2]; ring
    have h4 : rad_XPI x + cuspInternalRadius_XPI b ≠ 0 := by linarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_right h4)

theorem cusp_near_eq_XPI (b : Fin 2) :
    range (cuspPiece_XPI b).map ∩ cuspNear_XPI b =
      {x | x ∈ cuspNear_XPI b ∧ cuspFn_XPI b x ≤ 0} := by
  ext x
  have hx := rad_pos_XPI x
  fin_cases b
  · change x ∈ range (cuspPiece_XPI 0).map ∩ cuspNear_XPI 0 ↔
      x ∈ cuspNear_XPI 0 ∧ cuspFn_XPI 0 x ≤ 0
    rw [range_cuspPiece_zero_XPI, cuspFn_eq_XPI]
    simp only [mem_inter_iff, Set.mem_ofPred_eq, planarSign, cuspInternalRadius_XPI, Fin.val_zero,
      ↓reduceIte]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h2, by nlinarith⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by nlinarith, h1⟩
  · change x ∈ range (cuspPiece_XPI 1).map ∩ cuspNear_XPI 1 ↔
      x ∈ cuspNear_XPI 1 ∧ cuspFn_XPI 1 x ≤ 0
    rw [range_cuspPiece_one_XPI, cuspFn_eq_XPI]
    simp only [mem_inter_iff, Set.mem_ofPred_eq, planarSign, cuspInternalRadius_XPI, Fin.val_one,
      one_ne_zero, ↓reduceIte]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h2, by nlinarith⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by nlinarith, h1⟩

theorem cusp_external_end_XPI (b : Fin 2) (t : Torus) :
    (cuspPiece_XPI b).map (bandProduct_XPI (cuspRadii_XPI b) (t, Assembly.iccEnd false)) =
      portsE_XPI.torusMap b t := by
  apply Subtype.ext
  rw [portsE_torusMap_val_XPI, planarCircleMap_eq_XPI]
  change ((ULift.up ((bandRadius_XPI (cuspRadii_XPI b) (Assembly.iccEnd false)) •
    planarTwist b (t.1 : ℂ)), t.2) : PlaneLift.{0} × Circle) = _
  rw [bandRadius_iccEnd_XPI]
  rfl

theorem cusp_collar_owned_XPI (b : Fin 2) :
    (portsE_XPI.collar b).target ⊆ range (cuspPiece_XPI b).map := by
  intro x hx
  fin_cases b
  · change x ∈ range (cuspPiece_XPI 0).map
    rw [range_cuspPiece_zero_XPI]
    have h := mem_portsE_target_zero_XPI.mp hx
    change 2 ≤ rad_XPI x
    linarith
  · change x ∈ range (cuspPiece_XPI 1).map
    rw [range_cuspPiece_one_XPI]
    have h := mem_portsE_target_one_XPI.mp hx
    change rad_XPI x ≤ 1
    linarith

theorem cusp_collar_closure_off_XPI (b : Fin 2) :
    Disjoint (closure (portsE_XPI.collar b).target)
      (range fun t => (cuspPiece_XPI b).map
        (bandProduct_XPI (cuspRadii_XPI b) (t, Assembly.iccEnd true))) := by
  rw [range_cuspInternal_XPI]
  fin_cases b
  · refine Set.disjoint_left.mpr fun x hx hx' => ?_
    have h1 := closure_portsE_target_zero_XPI hx
    change 11 / 4 ≤ rad_XPI x at h1
    change rad_XPI x = cuspInternalRadius_XPI 0 at hx'
    simp only [cuspInternalRadius_XPI, Fin.val_zero, ↓reduceIte] at hx'
    linarith
  · refine Set.disjoint_left.mpr fun x hx hx' => ?_
    have h1 := closure_portsE_target_one_XPI hx
    change rad_XPI x ≤ 3 / 4 at h1
    change rad_XPI x = cuspInternalRadius_XPI 1 at hx'
    simp only [cuspInternalRadius_XPI, Fin.val_one, one_ne_zero, ↓reduceIte] at hx'
    linarith

theorem cusp_disjoint_XPI :
    Pairwise fun b b' : Fin 2 => Disjoint (range (cuspPiece_XPI b).map)
      (range (cuspPiece_XPI b').map) := by
  have h01 : Disjoint (range (cuspPiece_XPI 0).map) (range (cuspPiece_XPI 1).map) := by
    rw [range_cuspPiece_zero_XPI, range_cuspPiece_one_XPI]
    refine Set.disjoint_left.mpr fun x hx hx' => ?_
    change 2 ≤ rad_XPI x at hx
    change rad_XPI x ≤ 1 at hx'
    linarith
  intro b b' hne
  fin_cases b <;> fin_cases b'
  · exact (hne rfl).elim
  · exact h01
  · exact h01.symm
  · exact (hne rfl).elim

/-- **The two cusp cores of the external-port instance**: cusp `b` owns port `b`. -/
def extportCuspCores_XPI : CuspCores carrierW_XPI portsE_XPI where
  ports := productBoundary_eq.{0} 2 (Or.inl rfl)
  piece := cuspPiece_XPI
  product b := bandProduct_XPI (cuspRadii_XPI b)
  external_end := cusp_external_end_XPI
  collar_owned := cusp_collar_owned_XPI
  collar_closure_off := cusp_collar_closure_off_XPI
  disjoint := cusp_disjoint_XPI
  cuspFn := cuspFn_XPI
  near := cuspNear_XPI
  near_interior := cuspNear_interior_XPI
  fn_smooth _ := (contMDiff_carrierRadialFn_XPI _ _).contMDiffOn
  fn_regular b x _ _ := carrierRadialFn_regular_XPI (planarSign_ne_zero_XPI b) x
  internal_eq b := (range_cuspInternal_XPI b).trans (cusp_internal_eq_XPI b)
  near_eq := cusp_near_eq_XPI
  internalModelFace b := bandModelFace_XPI (cuspRadii_XPI b) true
  internalModelFace_eq _ := rfl
  externalModelFace b := bandModelFace_XPI (cuspRadii_XPI b) false
  externalModelFace_eq _ := rfl
  modelFace_cases b F := (bandModelFace_cases_XPI (cuspRadii_XPI b) F).elim Or.inr Or.inl

theorem extportCuspCores_piece_XPI (b : Fin 2) :
    extportCuspCores_XPI.piece b = cuspPiece_XPI b :=
  rfl

end GC.GraphManifold.Assembly.FC39P0.ExtPortXPI
