import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTerminalFiniteGeneration

/-!
# Actual generators of the compact pants surface

The left and right open halves of the compact planar pants retract radially onto the two
native hole circles. Their overlap is convex. The circle maps and their genuine bijective
fundamental-group maps provide the geometric input for actual boundary generation.
-/

set_option autoImplicit false
noncomputable section
open Set DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open DifferentialGeometry.Topology.VanKampen
open scoped Topology ContinuousMap unitInterval ComplexConjugate
universe u
namespace GC.Seifert

section Radial
variable (K : Set ℂ) (c : ℂ) (r : ℝ)

abbrev RadialAnnulus := ↥{z : ℂ | z ∈ K ∧ r ≤ ‖z - c‖}

def radialAnnulusCircle (hr : 0 < r) (hS : Metric.sphere c r ⊆ K) :
    C(Circle, RadialAnnulus K c r) :=
  { toFun := fun t => ⟨c + (r : ℂ) * conj (t : ℂ), by
    have hn : ‖c + (r : ℂ) * conj (t : ℂ) - c‖ = r := by
      rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.le,
        Complex.norm_conj, Circle.norm_coe, mul_one]
    exact ⟨hS (by rwa [Metric.mem_sphere, dist_eq_norm]), hn.ge⟩⟩
    continuous_toFun := by fun_prop }

theorem radialAnnulus_sub_ne_zero (hr : 0 < r) (x : RadialAnnulus K c r) : x.1 - c ≠ 0 := by
  have hn := x.2.2
  intro h
  rw [h, norm_zero] at hn
  exact (hr.trans_le hn).false

def radialAnnulusDirection (hr : 0 < r) : C(RadialAnnulus K c r, Circle) :=
  circleNormalize (fun x => conj (x.1 - c)) (by fun_prop)
    (fun x => (map_ne_zero conj).2 (radialAnnulus_sub_ne_zero K c r hr x))

theorem radialAnnulusDirection_circle (hr : 0 < r) (hS : Metric.sphere c r ⊆ K) :
    (radialAnnulusDirection K c r hr).comp (radialAnnulusCircle K c r hr hS) =
      ContinuousMap.id Circle := by
  apply ContinuousMap.ext
  intro t
  apply Circle.coe_injective
  change conj (c + (r : ℂ) * conj (t : ℂ) - c) /
    (‖conj (c + (r : ℂ) * conj (t : ℂ) - c)‖ : ℂ) = t
  rw [add_sub_cancel_left, map_mul, Complex.conj_ofReal, Complex.conj_conj]
  exact circleNormalize_real_mul hr (Circle.norm_coe t)

def radialAnnulusHomotopy (hr : 0 < r) (hS : Metric.sphere c r ⊆ K)
    (hK : Convex ℝ K) :
    ((radialAnnulusCircle K c r hr hS).comp (radialAnnulusDirection K c r hr)).Homotopy
      (ContinuousMap.id (RadialAnnulus K c r)) where
  toFun p := ⟨c + (((1 - (p.1 : ℝ)) * r + (p.1 : ℝ) * ‖p.2.1 - c‖) /
    ‖p.2.1 - c‖ : ℝ) • (p.2.1 - c), by
    have hn : 0 < ‖p.2.1 - c‖ := hr.trans_le p.2.2.2
    let a : ℂ := c + (r / ‖p.2.1 - c‖ : ℝ) • (p.2.1 - c)
    have ha : a ∈ Metric.sphere c r := by
      rw [Metric.mem_sphere, dist_eq_norm]
      dsimp [a]
      rw [add_sub_cancel_left, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (div_nonneg hr.le hn.le),
        div_mul_cancel₀ r hn.ne']
    have heq : c + (((1 - (p.1 : ℝ)) * r + (p.1 : ℝ) * ‖p.2.1 - c‖) /
        ‖p.2.1 - c‖ : ℝ) • (p.2.1 - c) = AffineMap.lineMap a p.2.1 (p.1 : ℝ) := by
      rw [AffineMap.lineMap_apply_module']
      dsimp [a]
      push_cast
      have hnC : (‖p.2.1 - c‖ : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
      field_simp [hnC]
      ring
    refine ⟨heq ▸ hK.lineMap_mem (hS ha) p.2.2.1 p.1.2, ?_⟩
    have hs : 0 ≤ (1 - (p.1 : ℝ)) * r + (p.1 : ℝ) * ‖p.2.1 - c‖ :=
      add_nonneg (mul_nonneg (sub_nonneg.2 p.1.2.2) hr.le)
        (mul_nonneg p.1.2.1 hn.le)
    rw [add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg (div_nonneg hs hn.le), div_mul_cancel₀ _ hn.ne']
    nlinarith [p.1.2.1, p.1.2.2, p.2.2.2]⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    have hn : ∀ p : I × RadialAnnulus K c r, ‖p.2.1 - c‖ ≠ 0 :=
      fun p => (hr.trans_le p.2.2.2).ne'
    fun_prop
  map_zero_left x := by
    apply Subtype.ext
    simp only [Set.Icc.coe_zero, sub_zero, one_mul, zero_mul, add_zero]
    change c + (r / ‖x.1 - c‖ : ℝ) • (x.1 - c) =
      c + (r : ℂ) * conj (conj (x.1 - c) / (‖conj (x.1 - c)‖ : ℂ))
    rw [map_div₀, Complex.conj_conj, Complex.conj_ofReal, Complex.norm_conj,
      Complex.real_smul]
    push_cast
    ring
  map_one_left x := by
    apply Subtype.ext
    have hn : ‖x.1 - c‖ ≠ 0 := (hr.trans_le x.2.2).ne'
    simp [hn]


def radialAnnulusHomotopyEquiv (hr : 0 < r) (hS : Metric.sphere c r ⊆ K)
    (hK : Convex ℝ K) : RadialAnnulus K c r ≃ₕ Circle where
  toFun := radialAnnulusDirection K c r hr
  invFun := radialAnnulusCircle K c r hr hS
  left_inv := ⟨radialAnnulusHomotopy K c r hr hS hK⟩
  right_inv := by rw [radialAnnulusDirection_circle]

theorem bijective_map_radialAnnulusCircle (hr : 0 < r)
    (hS : Metric.sphere c r ⊆ K) (hK : Convex ℝ K) (t : Circle) :
    Function.Bijective (FundamentalGroup.map (radialAnnulusCircle K c r hr hS) t) := by
  apply bijective_fundamentalGroup_map_of_homotopyEquiv_leftInverse
    (radialAnnulusHomotopyEquiv K c r hr hS hK)
  intro a
  exact DFunLike.congr_fun (radialAnnulusDirection_circle K c r hr hS) a

theorem pathConnectedSpace_radialAnnulus (hr : 0 < r)
    (hS : Metric.sphere c r ⊆ K) (hK : Convex ℝ K) :
    PathConnectedSpace (RadialAnnulus K c r) where
  nonempty := ⟨radialAnnulusCircle K c r hr hS 1⟩
  joined x y := ⟨((radialAnnulusHomotopy K c r hr hS hK).evalAt x).symm.trans
    (((PathConnectedSpace.somePath (radialAnnulusDirection K c r hr x)
      (radialAnnulusDirection K c r hr y)).map (radialAnnulusCircle K c r hr hS).continuous).trans
        ((radialAnnulusHomotopy K c r hr hS hK).evalAt y))⟩

end Radial

section CompactPants

abbrev ClosedPants := ↥(planarModel 3)

def closedPantsLeft : Set ClosedPants := {x | x.1.re < 1 / 2}

def closedPantsRight : Set ClosedPants := {x | -(1 / 2) < x.1.re}

theorem isOpen_closedPantsLeft : IsOpen closedPantsLeft :=
  isOpen_lt (Complex.continuous_re.comp continuous_subtype_val) continuous_const

theorem isOpen_closedPantsRight : IsOpen closedPantsRight :=
  isOpen_lt continuous_const (Complex.continuous_re.comp continuous_subtype_val)

theorem closedPantsLeft_union_closedPantsRight : closedPantsLeft ∪ closedPantsRight = univ := by
  apply eq_univ_of_forall
  intro x
  by_cases h : x.1.re < 1 / 2
  · exact Or.inl h
  · exact Or.inr (by change -(1 / 2) < x.1.re; linarith)

def closedPantsLeftConvex : Set ℂ := {z | ‖z‖ ≤ 3 ∧ z.re < 1 / 2}

theorem convex_closedPantsLeftConvex : Convex ℝ closedPantsLeftConvex := by
  convert (convex_closedBall (0 : ℂ) 3).inter
    (convex_halfSpace_lt Complex.reLm.isLinear (1 / 2)) using 1
  ext z
  simp only [closedPantsLeftConvex, mem_inter_iff, mem_ofPred_eq, Metric.mem_closedBall,
    dist_zero_right]
  rfl

theorem closedPantsLeftConvex_sphere :
    Metric.sphere (-(3 / 2) : ℂ) (1 / 2) ⊆ closedPantsLeftConvex := by
  intro z hz
  have hn : ‖z - (-(3 / 2) : ℂ)‖ = 1 / 2 := by
    rwa [Metric.mem_sphere, dist_eq_norm] at hz
  have hnorm := norm_add_le (z - (-(3 / 2) : ℂ)) (-(3 / 2) : ℂ)
  rw [sub_add_cancel, hn] at hnorm
  have hre := Complex.re_le_norm (z - (-(3 / 2) : ℂ))
  rw [hn] at hre
  simp only [Complex.sub_re] at hre
  norm_num at hnorm hre
  exact ⟨by linarith, by change z.re < 1 / 2; linarith⟩

theorem closedPantsLeft_radialSet :
    {z : ℂ | z ∈ closedPantsLeftConvex ∧ 1 / 2 ≤ ‖z - (-(3 / 2) : ℂ)‖} =
      {z : ℂ | z ∈ planarModel 3 ∧ z.re < 1 / 2} := by
  ext z
  constructor
  · rintro ⟨⟨hn, hre⟩, hd⟩
    refine ⟨⟨hn, fun j hj => ?_⟩, hre⟩
    fin_cases j
    · exact absurd rfl hj
    · have h := Complex.re_le_norm ((3 / 2 : ℂ) - z)
      rw [norm_sub_rev] at h
      simp only [Complex.sub_re] at h
      norm_num [planarCenter] at h ⊢
      linarith
    · simpa [planarCenter] using hd
  · rintro ⟨⟨hn, hd⟩, hre⟩
    exact ⟨⟨hn, hre⟩, by simpa [planarCenter] using hd 2 (by decide)⟩

def closedPantsLeftRadialHomeomorph :
    RadialAnnulus closedPantsLeftConvex (-(3 / 2)) (1 / 2) ≃ₜ ↥closedPantsLeft where
  toFun z := ⟨⟨z.1, ((Set.ext_iff.mp closedPantsLeft_radialSet) z.1).mp z.2 |>.1⟩,
    ((Set.ext_iff.mp closedPantsLeft_radialSet) z.1).mp z.2 |>.2⟩
  invFun z := ⟨z.1.1, ((Set.ext_iff.mp closedPantsLeft_radialSet) z.1.1).mpr
    ⟨z.1.2, z.2⟩⟩
  left_inv z := by change (⟨z.1, z.2⟩ : RadialAnnulus _ _ _) = z; rfl
  right_inv z := by change (⟨⟨z.1.1, z.1.2⟩, z.2⟩ : ↥closedPantsLeft) = z; rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

def closedPantsLeftCircle : C(Circle, ↥closedPantsLeft) :=
  (closedPantsLeftRadialHomeomorph : C(_, _)).comp
    (radialAnnulusCircle closedPantsLeftConvex (-(3 / 2)) (1 / 2)
      (by norm_num) closedPantsLeftConvex_sphere)

theorem closedPantsLeftCircle_val (t : Circle) :
    ((closedPantsLeftCircle t).1 : ℂ) = planarCircleMap 3 2 t := by
  dsimp [closedPantsLeftCircle, closedPantsLeftRadialHomeomorph, radialAnnulusCircle]
  norm_num [planarCircleMap, planarCenter, planarRadius]

theorem bijective_map_closedPantsLeftCircle (t : Circle) :
    Function.Bijective (FundamentalGroup.map closedPantsLeftCircle t) := by
  rw [closedPantsLeftCircle, GC.Topology.fundamentalGroup_map_comp]
  exact (bijective_map_homeomorph closedPantsLeftRadialHomeomorph _).comp
    (bijective_map_radialAnnulusCircle _ _ _ (by norm_num)
      closedPantsLeftConvex_sphere convex_closedPantsLeftConvex t)

instance pathConnectedSpace_closedPantsLeft : PathConnectedSpace ↥closedPantsLeft := by
  have := pathConnectedSpace_radialAnnulus _ _ _ (by norm_num)
    closedPantsLeftConvex_sphere convex_closedPantsLeftConvex
  exact closedPantsLeftRadialHomeomorph.pathConnectedSpace

def closedPantsRightConvex : Set ℂ := {z | ‖z‖ ≤ 3 ∧ -(1 / 2) < z.re}

theorem convex_closedPantsRightConvex : Convex ℝ closedPantsRightConvex := by
  convert (convex_closedBall (0 : ℂ) 3).inter
    (convex_halfSpace_gt Complex.reLm.isLinear (-(1 / 2))) using 1
  ext z
  simp only [closedPantsRightConvex, mem_inter_iff, mem_ofPred_eq, Metric.mem_closedBall,
    dist_zero_right]
  rfl

theorem closedPantsRightConvex_sphere :
    Metric.sphere (3 / 2 : ℂ) (1 / 2) ⊆ closedPantsRightConvex := by
  intro z hz
  have hn : ‖z - (3 / 2 : ℂ)‖ = 1 / 2 := by
    rwa [Metric.mem_sphere, dist_eq_norm] at hz
  have hnorm := norm_add_le (z - (3 / 2 : ℂ)) (3 / 2 : ℂ)
  rw [sub_add_cancel, hn] at hnorm
  have hre := Complex.re_le_norm ((3 / 2 : ℂ) - z)
  rw [norm_sub_rev, hn] at hre
  simp only [Complex.sub_re] at hre
  norm_num at hnorm hre
  exact ⟨by linarith, by change -(1 / 2) < z.re; linarith⟩

theorem closedPantsRight_radialSet :
    {z : ℂ | z ∈ closedPantsRightConvex ∧ 1 / 2 ≤ ‖z - (3 / 2 : ℂ)‖} =
      {z : ℂ | z ∈ planarModel 3 ∧ -(1 / 2) < z.re} := by
  ext z
  constructor
  · rintro ⟨⟨hn, hre⟩, hd⟩
    refine ⟨⟨hn, fun j hj => ?_⟩, hre⟩
    fin_cases j
    · exact absurd rfl hj
    · simpa [planarCenter] using hd
    · have h := Complex.re_le_norm (z - (-(3 / 2) : ℂ))
      simp only [Complex.sub_re, Complex.neg_re] at h
      norm_num [planarCenter] at h ⊢
      linarith
  · rintro ⟨⟨hn, hd⟩, hre⟩
    exact ⟨⟨hn, hre⟩, by simpa [planarCenter] using hd 1 (by decide)⟩

def closedPantsRightRadialHomeomorph :
    RadialAnnulus closedPantsRightConvex (3 / 2) (1 / 2) ≃ₜ ↥closedPantsRight where
  toFun z := ⟨⟨z.1, ((Set.ext_iff.mp closedPantsRight_radialSet) z.1).mp z.2 |>.1⟩,
    ((Set.ext_iff.mp closedPantsRight_radialSet) z.1).mp z.2 |>.2⟩
  invFun z := ⟨z.1.1, ((Set.ext_iff.mp closedPantsRight_radialSet) z.1.1).mpr
    ⟨z.1.2, z.2⟩⟩
  left_inv z := by change (⟨z.1, z.2⟩ : RadialAnnulus _ _ _) = z; rfl
  right_inv z := by change (⟨⟨z.1.1, z.1.2⟩, z.2⟩ : ↥closedPantsRight) = z; rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

def closedPantsRightCircle : C(Circle, ↥closedPantsRight) :=
  (closedPantsRightRadialHomeomorph : C(_, _)).comp
    (radialAnnulusCircle closedPantsRightConvex (3 / 2) (1 / 2)
      (by norm_num) closedPantsRightConvex_sphere)

theorem closedPantsRightCircle_val (t : Circle) :
    ((closedPantsRightCircle t).1 : ℂ) = planarCircleMap 3 1 t := by
  dsimp [closedPantsRightCircle, closedPantsRightRadialHomeomorph, radialAnnulusCircle]
  norm_num [planarCircleMap, planarCenter, planarRadius]

theorem bijective_map_closedPantsRightCircle (t : Circle) :
    Function.Bijective (FundamentalGroup.map closedPantsRightCircle t) := by
  rw [closedPantsRightCircle, GC.Topology.fundamentalGroup_map_comp]
  exact (bijective_map_homeomorph closedPantsRightRadialHomeomorph _).comp
    (bijective_map_radialAnnulusCircle _ _ _ (by norm_num)
      closedPantsRightConvex_sphere convex_closedPantsRightConvex t)

instance pathConnectedSpace_closedPantsRight : PathConnectedSpace ↥closedPantsRight := by
  have := pathConnectedSpace_radialAnnulus _ _ _ (by norm_num)
    closedPantsRightConvex_sphere convex_closedPantsRightConvex
  exact closedPantsRightRadialHomeomorph.pathConnectedSpace


def closedPantsStrip : Set ℂ :=
  {z | ‖z‖ ≤ 3 ∧ z.re < 1 / 2 ∧ -(1 / 2) < z.re}

theorem closedPantsStrip_subset : closedPantsStrip ⊆ planarModel 3 := by
  rintro z ⟨hn, hl, hr⟩
  refine ⟨hn, fun j hj => ?_⟩
  fin_cases j
  · exact absurd rfl hj
  · have h := Complex.re_le_norm ((3 / 2 : ℂ) - z)
    rw [norm_sub_rev] at h
    simp only [Complex.sub_re] at h
    norm_num [planarCenter] at h ⊢
    linarith
  · have h := Complex.re_le_norm (z - (-(3 / 2) : ℂ))
    simp only [Complex.sub_re, Complex.neg_re] at h
    norm_num [planarCenter] at h ⊢
    linarith

def closedPantsOverlapHomeomorph :
    ↥(closedPantsLeft ∩ closedPantsRight) ≃ₜ ↥closedPantsStrip where
  toFun x := ⟨x.1.1, x.1.2.1, x.2.1, x.2.2⟩
  invFun z := ⟨⟨z.1, closedPantsStrip_subset z.2⟩, z.2.2.1, z.2.2.2⟩
  left_inv z := by
    change (⟨⟨z.1.1, z.1.2⟩, z.2⟩ : ↥(closedPantsLeft ∩ closedPantsRight)) = z
    rfl
  right_inv z := by change (⟨z.1, z.2⟩ : ↥closedPantsStrip) = z; rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

instance contractibleSpace_closedPantsOverlap :
    ContractibleSpace ↥(closedPantsLeft ∩ closedPantsRight) := by
  have hc : Convex ℝ closedPantsStrip := by
    convert (convex_closedBall (0 : ℂ) 3).inter
      ((convex_halfSpace_lt Complex.reLm.isLinear (1 / 2)).inter
        (convex_halfSpace_gt Complex.reLm.isLinear (-(1 / 2)))) using 1
    ext z
    simp only [closedPantsStrip, mem_inter_iff, mem_ofPred_eq, Metric.mem_closedBall,
      dist_zero_right]
    rfl
  have : ContractibleSpace ↥closedPantsStrip :=
    hc.contractibleSpace ⟨0, by norm_num [closedPantsStrip]⟩
  exact closedPantsOverlapHomeomorph.contractibleSpace

def closedPantsCircle (j : Fin 3) : C(Circle, ClosedPants) :=
  ⟨fun t => ⟨planarCircleMap 3 j t, planarCircleMap_mem_planarModel le_rfl j t⟩,
    (continuous_planarCircleMap 3 j).subtype_mk _⟩

theorem closedPantsLeftCircle_toAmbient :
    (subsetToAmbient closedPantsLeft).comp closedPantsLeftCircle = closedPantsCircle 2 := by
  apply ContinuousMap.ext
  intro t
  exact Subtype.ext (closedPantsLeftCircle_val t)

theorem closedPantsRightCircle_toAmbient :
    (subsetToAmbient closedPantsRight).comp closedPantsRightCircle = closedPantsCircle 1 := by
  apply ContinuousMap.ext
  intro t
  exact Subtype.ext (closedPantsRightCircle_val t)

instance pathConnectedSpace_closedPants : PathConnectedSpace ClosedPants := by
  rw [pathConnectedSpace_iff_univ, ← closedPantsLeft_union_closedPantsRight]
  exact (isPathConnected_iff_pathConnectedSpace.mpr
    pathConnectedSpace_closedPantsLeft).union
      (isPathConnected_iff_pathConnectedSpace.mpr pathConnectedSpace_closedPantsRight)
      ⟨⟨0, by norm_num [planarModel, planarCenter]; intro j hj; fin_cases j <;> norm_num at *⟩,
        by norm_num [closedPantsLeft], by norm_num [closedPantsRight]⟩

end CompactPants
end GC.Seifert
