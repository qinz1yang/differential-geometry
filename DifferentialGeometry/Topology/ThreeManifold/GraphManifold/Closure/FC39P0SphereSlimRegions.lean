import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0SphereSlimSeam

/-!
# FC39 producer, packet P0 (gate 1): the regions `M₁`, `M₂` of the S³ data

The slim-and-zero clauses of `JunctionsV2` (§5.7) for the S³ data (zero kind
`FC39P0SphereZero.lean`, slim kind `FC39P0SphereSlim.lean`), stereographic height
`q₀ = (r² − 4)/(r² + 4)`:

* `sphere_regionM1`: `M₁ = W \ int(Z ∪ C) = {−15/17 ≤ q₀ ≤ 3/5}`;
* `sphere_relInt_slim`: `int_{M₁} S = {−15/17 ≤ q₀ < −3/5}` (the relative interior, §5.7);
* `sphere_regionM2`: `M₂ = M₁ \ int_{M₁} S = {−3/5 ≤ q₀ ≤ 3/5}`;
* `sphere_slim_M2` (`slim_M2`: `S ∩ M₂` = the new ends), `sphere_shared_removed` (`shared_removed`:
  the shared face lies in `int_{M₁} S`), `sphere_frontier_M2` (`frontier_M2`:
  `frontier M₂ = ∂M₂`);
* the derived interface of review 49 "the relative collar of a shared face is removed":
  `sphereSharedSeam_slimSide_removed` (the slim side `s ∈ [0, 1)` of the seam collar lies in
  `int_{M₁} S`) and `sphereSharedSeam_target_disjoint_M2` (the whole seam collar misses `M₂`).

Tool: a point with `|q₀| < 1` is a limit of points with `q₀` slightly above and slightly below
(radial path `t ↦ ambient(t y)` in the stereographic chart), `mem_closure_height_above` /
`mem_closure_height_below`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open DifferentialGeometry.Topology.Manifold Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## Points of a level are limits from both sides -/

theorem stereoHeight_lt_stereoHeight {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    (a - 4) / (a + 4) < (b - 4) / (b + 4) := by
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith

theorem continuous_ambient_false : Continuous (cycleBallAmbient false) := by
  rw [← continuousOn_univ, ← cycleBallAmbient_source]
  exact (cycleBallAmbient false).contMDiffOn_toFun.continuousOn

/-- The radial path through a point off the poles, with its height. -/
theorem exists_radial_path {x : sphereW.Carrier} (hx : |sphereHeight x| < 1) :
    ∃ y : E3, y ≠ 0 ∧ cycleBallAmbient false y = x ∧
      ∀ t : ℝ, 0 ≤ t → sphereHeight (cycleBallAmbient false (t • y)) =
        (t ^ 2 * ‖y‖ ^ 2 - 4) / (t ^ 2 * ‖y‖ ^ 2 + 4) := by
  obtain ⟨y, rfl, hy⟩ := exists_ambient_of_height_lt (abs_lt.1 hx).2
  refine ⟨y, ?_, rfl, fun t ht => ?_⟩
  · rintro rfl
    rw [hy] at hx
    norm_num at hx
  · rw [sphereHeight_ambient_false, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht, mul_pow]

/-- **A point with `|q₀| < 1` is a limit of points with `q₀` slightly above.** -/
theorem mem_closure_height_above {x : sphereW.Carrier} (hx : |sphereHeight x| < 1) {c : ℝ}
    (hc : sphereHeight x < c) :
    x ∈ closure {z | sphereHeight x < sphereHeight z ∧ sphereHeight z < c} := by
  obtain ⟨y, hy0, rfl, hpath⟩ := exists_radial_path hx
  let f : ℝ → sphereW.Carrier := fun t => cycleBallAmbient false (t • y)
  have hf : Continuous f := continuous_ambient_false.comp (continuous_id.smul continuous_const)
  have hf1 : f 1 = cycleBallAmbient false y := by
    change cycleBallAmbient false ((1 : ℝ) • y) = _
    rw [one_smul]
  have ht : Tendsto f (𝓝[>] 1) (𝓝 (cycleBallAmbient false y)) :=
    hf1 ▸ (hf.tendsto 1).mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto ht ?_
  have hev1 : ∀ᶠ t in 𝓝[>] (1 : ℝ), sphereHeight (cycleBallAmbient false y) <
      sphereHeight (f t) := by
    refine eventually_nhdsWithin_of_forall fun t (ht1 : 1 < t) => ?_
    have h0 := hpath 1 zero_le_one
    rw [one_smul, one_pow, one_mul] at h0
    change _ < sphereHeight (cycleBallAmbient false (t • y))
    rw [h0, hpath t (by linarith)]
    apply stereoHeight_lt_stereoHeight (sq_nonneg _)
    have hn : 0 < ‖y‖ ^ 2 := by positivity
    have ht2 : 1 < t ^ 2 := by nlinarith
    calc ‖y‖ ^ 2 = 1 * ‖y‖ ^ 2 := by ring
      _ < t ^ 2 * ‖y‖ ^ 2 := mul_lt_mul_of_pos_right ht2 hn
  have hev2 : ∀ᶠ t in 𝓝[>] (1 : ℝ), sphereHeight (f t) < c := by
    have hq : Tendsto (fun t => sphereHeight (f t)) (𝓝 1)
        (𝓝 (sphereHeight (cycleBallAmbient false y))) :=
      hf1 ▸ ((contMDiff_sphereHeight.continuous.comp hf).tendsto 1)
    exact (hq.eventually (gt_mem_nhds hc)).filter_mono nhdsWithin_le_nhds
  exact hev1.and hev2

/-- **A point with `|q₀| < 1` is a limit of points with `q₀` slightly below.** -/
theorem mem_closure_height_below {x : sphereW.Carrier} (hx : |sphereHeight x| < 1) {c : ℝ}
    (hc : c < sphereHeight x) :
    x ∈ closure {z | c < sphereHeight z ∧ sphereHeight z < sphereHeight x} := by
  obtain ⟨y, hy0, rfl, hpath⟩ := exists_radial_path hx
  let f : ℝ → sphereW.Carrier := fun t => cycleBallAmbient false (t • y)
  have hf : Continuous f := continuous_ambient_false.comp (continuous_id.smul continuous_const)
  have hf1 : f 1 = cycleBallAmbient false y := by
    change cycleBallAmbient false ((1 : ℝ) • y) = _
    rw [one_smul]
  have ht : Tendsto f (𝓝[Ioo 0 1] 1) (𝓝 (cycleBallAmbient false y)) :=
    hf1 ▸ (hf.tendsto 1).mono_left nhdsWithin_le_nhds
  have : (𝓝[Ioo (0 : ℝ) 1] 1).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioo zero_ne_one]
    exact ⟨zero_le_one, le_rfl⟩
  refine mem_closure_of_tendsto ht ?_
  have hev1 : ∀ᶠ t in 𝓝[Ioo 0 1] (1 : ℝ), sphereHeight (f t) <
      sphereHeight (cycleBallAmbient false y) := by
    refine eventually_nhdsWithin_of_forall fun t (ht1 : t ∈ Ioo (0 : ℝ) 1) => ?_
    have h0 := hpath 1 zero_le_one
    rw [one_smul, one_pow, one_mul] at h0
    change sphereHeight (cycleBallAmbient false (t • y)) < _
    rw [h0, hpath t ht1.1.le]
    apply stereoHeight_lt_stereoHeight (by positivity)
    have hn : 0 < ‖y‖ ^ 2 := by positivity
    have ht2 : t ^ 2 < 1 := by nlinarith [ht1.1, ht1.2]
    nlinarith
  have hev2 : ∀ᶠ t in 𝓝[Ioo 0 1] (1 : ℝ), c < sphereHeight (f t) := by
    have hq : Tendsto (fun t => sphereHeight (f t)) (𝓝 1)
        (𝓝 (sphereHeight (cycleBallAmbient false y))) :=
      hf1 ▸ ((contMDiff_sphereHeight.continuous.comp hf).tendsto 1)
    exact (hq.eventually (lt_mem_nhds hc)).filter_mono nhdsWithin_le_nhds
  exact hev2.and hev1

/-- A point of an open set that is a limit of points of `B` meets `B` inside it. -/
theorem not_mem_interior_of_mem_closure {X : Type*} [TopologicalSpace X] {A B : Set X} {x : X}
    (hx : x ∈ closure B) (hAB : Disjoint A B) : x ∉ interior A := by
  intro hint
  obtain ⟨z, hzA, hzB⟩ := mem_closure_iff.1 hx (interior A) isOpen_interior hint
  exact Set.disjoint_left.1 hAB (interior_subset hzA) hzB

/-! ## `M₁` -/

theorem sphere_zero_union :
    (⋃ i, range (sphereZeroDomains.piece i).map) ∪
        (⋃ b, range (sphereCuspCores.piece b).map) =
      {x | sphereHeight x ≤ -15 / 17} ∪ {x | 3 / 5 ≤ sphereHeight x} := by
  ext x
  simp only [mem_union, mem_iUnion, mem_ofPred_eq]
  constructor
  · rintro (⟨i, hi⟩ | ⟨b, -⟩)
    · rw [sphereZeroDomains.range_eq i] at hi
      change sphereZeroRatio i x ≤ 0 at hi
      fin_cases i
      · left
        change sphereHeight x + 15 / 17 ≤ 0 at hi
        linarith
      · right
        change 3 / 5 - sphereHeight x ≤ 0 at hi
        linarith
    · exact b.elim0
  · rintro (h | h)
    · refine Or.inl ⟨(0 : Fin 2), ?_⟩
      rw [sphereZeroDomains.range_eq (0 : Fin 2)]
      change sphereHeight x + 15 / 17 ≤ 0
      linarith
    · refine Or.inl ⟨(1 : Fin 2), ?_⟩
      rw [sphereZeroDomains.range_eq (1 : Fin 2)]
      change 3 / 5 - sphereHeight x ≤ 0
      linarith

theorem sphere_interior_zero :
    interior ({x : sphereW.Carrier | sphereHeight x ≤ -15 / 17} ∪ {x | 3 / 5 ≤ sphereHeight x}) =
      {x | sphereHeight x < -15 / 17} ∪ {x | 3 / 5 < sphereHeight x} := by
  have hc := contMDiff_sphereHeight.continuous
  apply Subset.antisymm
  · intro x hx
    rcases interior_subset hx with h | h
    · change sphereHeight x ≤ -15 / 17 at h
      rcases h.lt_or_eq with h' | h'
      · exact Or.inl h'
      · exfalso
        have hx1 : |sphereHeight x| < 1 := by rw [h', abs_lt]; constructor <;> norm_num
        refine not_mem_interior_of_mem_closure
          (mem_closure_height_above hx1 (c := 3 / 5) (by rw [h']; norm_num)) ?_ hx
        rw [Set.disjoint_left]
        rintro z (hz | hz) ⟨hz1, hz2⟩
        · change sphereHeight z ≤ -15 / 17 at hz
          linarith
        · change 3 / 5 ≤ sphereHeight z at hz
          linarith
    · change 3 / 5 ≤ sphereHeight x at h
      rcases h.lt_or_eq with h' | h'
      · exact Or.inr h'
      · exfalso
        have hx1 : |sphereHeight x| < 1 := by rw [← h', abs_lt]; constructor <;> norm_num
        refine not_mem_interior_of_mem_closure
          (mem_closure_height_below hx1 (c := -15 / 17) (by rw [← h']; norm_num)) ?_ hx
        rw [Set.disjoint_left]
        rintro z (hz | hz) ⟨hz1, hz2⟩
        · change sphereHeight z ≤ -15 / 17 at hz
          linarith
        · change 3 / 5 ≤ sphereHeight z at hz
          linarith
  · exact interior_maximal (union_subset_union
      (fun x hx => show sphereHeight x ≤ -15 / 17 from le_of_lt hx)
      (fun x hx => show 3 / 5 ≤ sphereHeight x from le_of_lt hx))
      ((isOpen_lt hc continuous_const).union (isOpen_lt continuous_const hc))

/-- **`M₁` of the S³ data** is the band `−15/17 ≤ q₀ ≤ 3/5`. -/
theorem sphere_regionM1 :
    regionM1 sphereZeroDomains sphereCuspCores =
      {x | -15 / 17 ≤ sphereHeight x ∧ sphereHeight x ≤ 3 / 5} := by
  rw [regionM1, sphere_zero_union, sphere_interior_zero]
  ext x
  simp only [mem_compl_iff, mem_union, mem_ofPred_eq, not_or, not_lt]

/-! ## The relative interior of `S` in `M₁` and `M₂` -/

theorem sphereSlimPieces_union :
    sphereSlimPieces.union = {x | -15 / 17 ≤ sphereHeight x ∧ sphereHeight x ≤ -3 / 5} := by
  rw [SlimPiecesV2.union, ← range_slimMap]
  ext x
  simp only [mem_iUnion]
  constructor
  · rintro ⟨_, h⟩
    exact h
  · intro h
    exact ⟨(0 : Fin 1), h⟩

/-- **`int_{M₁} S` of the S³ data** is `−15/17 ≤ q₀ < −3/5`. -/
theorem sphere_relInt_slim :
    relInt (regionM1 sphereZeroDomains sphereCuspCores) sphereSlimPieces.union =
      {x | -15 / 17 ≤ sphereHeight x ∧ sphereHeight x < -3 / 5} := by
  have hc := contMDiff_sphereHeight.continuous
  rw [sphere_regionM1, sphereSlimPieces_union]
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    have hpS := interior_subset hp
    change -15 / 17 ≤ sphereHeight p.1 ∧ sphereHeight p.1 ≤ -3 / 5 at hpS
    refine ⟨hpS.1, ?_⟩
    rcases hpS.2.lt_or_eq with h' | h'
    · exact h'
    · exfalso
      have hx1 : |sphereHeight p.1| < 1 := by rw [h', abs_lt]; constructor <;> norm_num
      obtain ⟨U, hU, hUS⟩ := (mem_nhds_subtype _ _ _).1 (mem_interior_iff_mem_nhds.1 hp)
      obtain ⟨z, hzU, hz1, hz2⟩ := mem_closure_iff_nhds.1
        (mem_closure_height_above hx1 (c := 3 / 5) (by rw [h']; norm_num)) U hU
      have hzM : -15 / 17 ≤ sphereHeight z ∧ sphereHeight z ≤ 3 / 5 :=
        ⟨by linarith, hz2.le⟩
      have hzS := hUS (show (⟨z, hzM⟩ : {x : sphereW.Carrier // -15 / 17 ≤ sphereHeight x ∧
        sphereHeight x ≤ 3 / 5}) ∈ Subtype.val ⁻¹' U from hzU)
      change -15 / 17 ≤ sphereHeight z ∧ sphereHeight z ≤ -3 / 5 at hzS
      linarith [hzS.2]
  · rintro ⟨h1, h2⟩
    refine ⟨⟨x, h1, by linarith⟩, ?_, rfl⟩
    rw [mem_interior_iff_mem_nhds]
    refine (mem_nhds_subtype _ _ _).2 ⟨{z | sphereHeight z < -3 / 5},
      (isOpen_lt hc continuous_const).mem_nhds h2, ?_⟩
    rintro ⟨z, hz⟩ (hz' : sphereHeight z < -3 / 5)
    exact ⟨hz.1, hz'.le⟩

/-- **`M₂` of the S³ data** is the band `−3/5 ≤ q₀ ≤ 3/5` (`1 ≤ r ≤ 4`). -/
theorem sphere_regionM2 :
    regionM2 sphereSlimPieces = {x | -3 / 5 ≤ sphereHeight x ∧ sphereHeight x ≤ 3 / 5} := by
  rw [regionM2, sphere_relInt_slim, sphere_regionM1]
  ext x
  simp only [Set.mem_sdiff, mem_ofPred_eq, not_and, not_lt]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h3 h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨by linarith, h2⟩, fun _ => h1⟩

/-! ## The `JunctionsV2` clauses of the slim and zero kinds -/

/-- **`slim_M2` for the S³ data**: `S ∩ M₂` is the new end. -/
theorem sphere_slim_M2 :
    sphereSlimPieces.union ∩ regionM2 sphereSlimPieces =
      ⋃ e : sphereSlimPieces.NewEnd, sphereSlimPieces.endSet e.1 := by
  rw [sphereSlimPieces_union, sphere_regionM2]
  ext x
  simp only [mem_inter_iff, mem_ofPred_eq, mem_iUnion]
  constructor
  · rintro ⟨⟨-, h2⟩, h3, -⟩
    refine ⟨sphereNewEnd, ?_⟩
    rw [sphereNewEnd_set]
    exact le_antisymm h2 h3
  · rintro ⟨e, he⟩
    rw [eq_sphereNewEnd e, sphereNewEnd_set] at he
    change sphereHeight x = -3 / 5 at he
    rw [he]
    norm_num

/-- **`shared_removed` for the S³ data**: the shared face lies in `int_{M₁} S`. -/
theorem sphere_shared_removed (σ : ActualSharedFace sphereSlimPieces) :
    sphereSlimPieces.endSet σ.1 ⊆
      relInt (regionM1 sphereZeroDomains sphereCuspCores) sphereSlimPieces.union := by
  rw [eq_sphereSharedFace σ, sphereSharedFace_set, sphere_relInt_slim]
  intro x hx
  change sphereHeight x = -15 / 17 at hx
  change -15 / 17 ≤ sphereHeight x ∧ sphereHeight x < -3 / 5
  rw [hx]
  norm_num

theorem sphere_interior_M2 :
    interior {x : sphereW.Carrier | -3 / 5 ≤ sphereHeight x ∧ sphereHeight x ≤ 3 / 5} =
      {x | -3 / 5 < sphereHeight x ∧ sphereHeight x < 3 / 5} := by
  have hc := contMDiff_sphereHeight.continuous
  apply Subset.antisymm
  · intro x hx
    obtain ⟨h1, h2⟩ := interior_subset hx
    refine ⟨?_, ?_⟩
    · rcases h1.lt_or_eq with h' | h'
      · exact h'
      · exfalso
        have hx1 : |sphereHeight x| < 1 := by rw [← h', abs_lt]; constructor <;> norm_num
        refine not_mem_interior_of_mem_closure
          (mem_closure_height_below hx1 (c := -1) (by rw [← h']; norm_num)) ?_ hx
        rw [Set.disjoint_left]
        rintro z ⟨hz1, -⟩ ⟨-, hz2⟩
        rw [← h'] at hz2
        linarith
    · rcases h2.lt_or_eq with h' | h'
      · exact h'
      · exfalso
        have hx1 : |sphereHeight x| < 1 := by rw [h', abs_lt]; constructor <;> norm_num
        refine not_mem_interior_of_mem_closure
          (mem_closure_height_above hx1 (c := 1) (by rw [h']; norm_num)) ?_ hx
        rw [Set.disjoint_left]
        rintro z ⟨-, hz1⟩ ⟨hz2, -⟩
        rw [h'] at hz2
        linarith
  · exact interior_maximal (fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩)
      ((isOpen_lt continuous_const hc).inter (isOpen_lt hc continuous_const))

/-- **`frontier_M2` for the S³ data**: `frontier M₂ = ∂M₂ = {q₀ = ±3/5}`. -/
theorem sphere_frontier_M2 :
    frontier (regionM2 sphereSlimPieces) = sphereSlimPieces.boundaryM2 := by
  have hc := contMDiff_sphereHeight.continuous
  have hcl : IsClosed {x : sphereW.Carrier | -3 / 5 ≤ sphereHeight x ∧ sphereHeight x ≤ 3 / 5} :=
    (isClosed_le continuous_const hc).inter (isClosed_le hc continuous_const)
  rw [sphere_regionM2, sphere_boundaryM2, frontier, sphere_interior_M2, hcl.closure_eq]
  ext x
  simp only [Set.mem_sdiff, mem_ofPred_eq, mem_union, not_and, not_lt]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    rcases h1.lt_or_eq with h' | h'
    · exact Or.inr (le_antisymm h2 (h3 h'))
    · exact Or.inl h'.symm
  · rintro (h | h) <;> rw [h] <;> norm_num

/-! ## The relative collar of the shared face is removed -/

/-- **The slim side of the seam collar lies in `int_{M₁} S`** (the relative inward collar of the
shared face is removed with it). -/
theorem sphereSharedSeam_slimSide_removed (z : ClosureSphere.{0}) {s : ℝ} (hs : 0 ≤ s)
    (hs' : s < 1) :
    sphereSharedSeam.collar (z, s) ∈
      relInt (regionM1 sphereZeroDomains sphereCuspCores) sphereSlimPieces.union := by
  have hS := sphereSharedSeam_pos_mem z hs hs'
  change _ ∈ range slimMap at hS
  rw [range_slimMap] at hS
  have hT : sphereSharedSeam.collar (z, s) ∈ sphereSharedSeam.collar.target :=
    sphereSharedSeam.collar.map_source (by
      rw [sphereSharedSeam.source_eq]
      exact ⟨mem_univ _, by linarith, hs'⟩)
  have h67 := sphereHeight_le_of_mem_sharedSeam hT
  rw [sphere_relInt_slim]
  exact ⟨hS.1, by linarith⟩

/-- **The whole seam collar misses `M₂`.** -/
theorem sphereSharedSeam_target_disjoint_M2 :
    Disjoint sphereSharedSeam.collar.target (regionM2 sphereSlimPieces) := by
  rw [sphere_regionM2, Set.disjoint_left]
  rintro x hx ⟨h1, -⟩
  have := sphereHeight_le_of_mem_sharedSeam hx
  linarith

end GC.GraphManifold.Assembly.FC39P0
