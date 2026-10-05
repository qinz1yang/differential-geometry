import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1Standard

/-!
# Chapter-14 assembly, item L1, group G3: facts about the standard local forms

* the cap chart `capMap b` maps `neckCapRegion ε b` bijectively onto the ball side
  `neckDomain ε ∩ {τ ≤ 0}` (`capMap_mem_neckDomain`, `exists_capRegion_capMap_eq`,
  `capMap_injOn`);
* the handle end `handleEnd b` maps the end strip `|t - b| < 2ε` bijectively onto the handle side
  `neckDomain ε ∩ {0 ≤ τ, ‖z‖ ≤ 1}` (`handleEnd_mem_neckDomain`, `exists_handleEnd_eq`,
  `handleEnd_injective`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint Manifold
open scoped Manifold ContDiff Topology InnerProductSpace

namespace GC.GraphManifold.Assembly

local instance diskCharts_ASML1F : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

local instance fact_finrank_three_ASML1F :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

theorem northPole_val : ((northPole : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    EuclideanSpace ℝ (Fin 3)) = EuclideanSpace.single 2 1 := rfl

theorem southPole_val : ((southPole : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    EuclideanSpace ℝ (Fin 3)) = -EuclideanSpace.single 2 1 := rfl

theorem reflectThree_north : reflectThree ((northPole : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    EuclideanSpace ℝ (Fin 3)) = (southPole : EuclideanSpace ℝ (Fin 3)) := by
  rw [northPole_val, southPole_val]
  exact Submodule.reflection_orthogonalComplement_singleton_eq_neg _

theorem reflectThree_reflectThree (x : EuclideanSpace ℝ (Fin 3)) :
    reflectThree (reflectThree x) = x :=
  Submodule.reflection_reflection _ x

theorem inner_reflectThree (x y : EuclideanSpace ℝ (Fin 3)) :
    ⟪reflectThree x, y⟫_ℝ = ⟪x, reflectThree y⟫_ℝ := by
  conv_lhs => rw [← reflectThree_reflectThree y]
  exact reflectThree.inner_map_map x (reflectThree y)

theorem norm_reflectThree (x : EuclideanSpace ℝ (Fin 3)) : ‖reflectThree x‖ = ‖x‖ :=
  reflectThree.norm_map x

theorem inner_north_south : ⟪((northPole : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    EuclideanSpace ℝ (Fin 3)), (southPole : EuclideanSpace ℝ (Fin 3))⟫_ℝ = -1 := by
  rw [northPole_val, southPole_val, inner_neg_right, real_inner_self_eq_norm_sq]
  simp

/-- The south cap chart in terms of the direction. -/
theorem southCapMap_apply (x : EuclideanSpace ℝ (Fin 3)) :
    southCapMap x = (DifferentialGeometry.Topology.Handle.stereoChart northPole
      (DifferentialGeometry.Topology.Manifold.sphereDirection southPole x), ‖x‖ - 1) := rfl

/-- The cap charts and regions of the north cap are the mirror images of the south ones. -/
theorem capMap_true (x : EuclideanSpace ℝ (Fin 3)) : capMap true x = southCapMap (reflectThree x) :=
  rfl

theorem capMap_false (x : EuclideanSpace ℝ (Fin 3)) : capMap false x = southCapMap x := rfl

/-- The south-cap conditions on a point of `ℝ³`. -/
def SouthCapCond (ε : ℝ) (x : EuclideanSpace ℝ (Fin 3)) : Prop :=
  1 - 2 * ε < ‖x‖ ∧ ‖x‖ ≤ 1 ∧
    0 < ⟪x, ((southPole : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) : EuclideanSpace ℝ (Fin 3))⟫_ℝ ∧
    ‖(southCapMap x).1‖ < 1 + 2 * ε

theorem southCapCond_of_mem_capRegion {ε : ℝ} {b : Bool} {x : ClosedCell 3}
    (hx : x ∈ neckCapRegion ε b) :
    SouthCapCond ε (if b then reflectThree (x : EuclideanSpace ℝ (Fin 3))
      else (x : EuclideanSpace ℝ (Fin 3))) := by
  obtain ⟨h1, h2, h3⟩ := hx
  have hn : ‖(x : EuclideanSpace ℝ (Fin 3))‖ ≤ 1 := x.2
  cases b
  · exact ⟨h1, hn, h2, h3⟩
  · change SouthCapCond ε (reflectThree (x : EuclideanSpace ℝ (Fin 3)))
    refine ⟨by rw [norm_reflectThree]; exact h1, by rw [norm_reflectThree]; exact hn, ?_, h3⟩
    have hsn : reflectThree ((southPole : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
        EuclideanSpace ℝ (Fin 3)) = (northPole : EuclideanSpace ℝ (Fin 3)) := by
      rw [← reflectThree_north, reflectThree_reflectThree]
    rw [inner_reflectThree, hsn]
    exact h2

theorem capMap_mem_neckDomain {ε : ℝ} {b : Bool} {x : ClosedCell 3}
    (hx : x ∈ neckCapRegion ε b) :
    capMap b (x : EuclideanSpace ℝ (Fin 3)) ∈ neckDomain ε ∧
      (capMap b (x : EuclideanSpace ℝ (Fin 3))).2 ≤ 0 := by
  have hc := southCapCond_of_mem_capRegion hx
  obtain ⟨h1, hn, -, h3⟩ := hc
  have hcap : capMap b (x : EuclideanSpace ℝ (Fin 3)) = southCapMap
      (if b then reflectThree (x : EuclideanSpace ℝ (Fin 3)) else (x : EuclideanSpace ℝ (Fin 3))) := by
    cases b <;> rfl
  rw [hcap]
  refine ⟨⟨h3, ?_⟩, ?_⟩
  · change |‖_‖ - 1| < 2 * ε
    rw [abs_lt]
    constructor <;> linarith
  · change ‖_‖ - 1 ≤ 0
    linarith

/-- Every ball-side point of the neck domain is the cap chart of a point of the cap region. -/
theorem exists_capRegion_capMap_eq {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 8) (b : Bool)
    {q : EuclideanSpace ℝ (Fin 2) × ℝ} (hq : q ∈ neckDomain ε) (hq0 : q.2 ≤ 0) :
    ∃ x ∈ neckCapRegion ε b, capMap b (x : EuclideanSpace ℝ (Fin 3)) = q := by
  obtain ⟨hq1, hq2⟩ := hq
  have hq2' := (abs_lt.mp hq2).1
  set θ := (DifferentialGeometry.Topology.Handle.stereoChart northPole).symm q.1 with hθ
  have hθs : θ ∈ (DifferentialGeometry.Topology.Handle.stereoChart northPole).source :=
    (DifferentialGeometry.Topology.Handle.stereoChart northPole).map_target
      (by rw [DifferentialGeometry.Topology.Handle.stereoChart_target]; exact mem_univ _)
  have hθq : DifferentialGeometry.Topology.Handle.stereoChart northPole θ = q.1 :=
    (DifferentialGeometry.Topology.Handle.stereoChart northPole).right_inv
      (by rw [DifferentialGeometry.Topology.Handle.stereoChart_target]; exact mem_univ _)
  have hinner : 0 < ⟪(θ : EuclideanSpace ℝ (Fin 3)),
      ((southPole : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) : EuclideanSpace ℝ (Fin 3))⟫_ℝ := by
    have h := DifferentialGeometry.Topology.Handle.inner_stereoChart_symm northPole q.1
    rw [southPole_val, inner_neg_right, ← northPole_val]
    rw [← hθ] at h
    rw [h]
    have hsq : ‖q.1‖ ^ 2 < 4 := by
      have h0 : 0 ≤ ‖q.1‖ := norm_nonneg _
      nlinarith
    have hpos : (0 : ℝ) < ‖q.1‖ ^ 2 + 4 := by positivity
    rw [neg_pos, div_neg_iff]
    right
    exact ⟨by linarith, hpos⟩
  set r : ℝ := 1 + q.2
  have hr : 0 < r := by simp only [r]; linarith
  set y : EuclideanSpace ℝ (Fin 3) := r • (θ : EuclideanSpace ℝ (Fin 3)) with hy
  have hθn : ‖(θ : EuclideanSpace ℝ (Fin 3))‖ = 1 := norm_eq_of_mem_sphere θ
  have hyn : ‖y‖ = r := by rw [hy, norm_smul, hθn, mul_one, Real.norm_eq_abs, abs_of_pos hr]
  have hy0 : y ≠ 0 := by
    intro h
    rw [h, norm_zero] at hyn
    linarith
  have hdir : DifferentialGeometry.Topology.Manifold.sphereDirection southPole y = θ := by
    apply Subtype.ext
    rw [DifferentialGeometry.Topology.Manifold.coe_sphereDirection _ hy0, hyn, hy, smul_smul,
      inv_mul_cancel₀ hr.ne', one_smul]
  have hcap : southCapMap y = q := by
    rw [southCapMap_apply, hdir, hθq, hyn]
    simp only [r, add_sub_cancel_left]
  have hyb : ‖y‖ ≤ 1 := by rw [hyn]; simp only [r]; linarith
  have hyinner : 0 < ⟪y, ((southPole : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
      EuclideanSpace ℝ (Fin 3))⟫_ℝ := by
    rw [hy, inner_smul_left]
    simp only [RCLike.conj_to_real]
    exact mul_pos hr hinner
  have hyr : 1 - 2 * ε < ‖y‖ := by rw [hyn]; simp only [r]; linarith
  cases b
  · refine ⟨⟨y, by simpa using hyb⟩, ⟨hyr, ?_, ?_⟩, hcap⟩
    · simpa [capPole] using hyinner
    · change ‖(southCapMap y).1‖ < 1 + 2 * ε
      rw [hcap]
      exact hq1
  · refine ⟨⟨reflectThree y, by simpa [norm_reflectThree] using hyb⟩, ⟨?_, ?_, ?_⟩, ?_⟩
    · change 1 - 2 * ε < ‖reflectThree y‖
      rw [norm_reflectThree]
      exact hyr
    · change 0 < ⟪reflectThree y, ((capPole true : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
        EuclideanSpace ℝ (Fin 3))⟫_ℝ
      rw [inner_reflectThree]
      simpa [capPole, reflectThree_north] using hyinner
    · change ‖(southCapMap (reflectThree (reflectThree y))).1‖ < 1 + 2 * ε
      rw [reflectThree_reflectThree, hcap]
      exact hq1
    · change southCapMap (reflectThree (reflectThree y)) = q
      rw [reflectThree_reflectThree, hcap]

theorem southCapMap_injOn {ε : ℝ} {x x' : EuclideanSpace ℝ (Fin 3)} (hx : SouthCapCond ε x)
    (hx' : SouthCapCond ε x') (h : southCapMap x = southCapMap x') : x = x' := by
  have hnorm : ‖x‖ = ‖x'‖ := by
    have h2 := congrArg Prod.snd h
    simp only [southCapMap_apply] at h2
    linarith
  have hsrc (z : EuclideanSpace ℝ (Fin 3)) (hz : SouthCapCond ε z) (hz0 : z ≠ 0) :
      DifferentialGeometry.Topology.Manifold.sphereDirection southPole z ∈
        (DifferentialGeometry.Topology.Handle.stereoChart northPole).source := by
    rw [DifferentialGeometry.Topology.Handle.stereoChart_source]
    intro hN
    have hin := hz.2.2.1
    have hd := congrArg (fun w : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 =>
      ⟪(w : EuclideanSpace ℝ (Fin 3)), ((southPole : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
        EuclideanSpace ℝ (Fin 3))⟫_ℝ) hN
    rw [DifferentialGeometry.Topology.Manifold.coe_sphereDirection _ hz0, inner_smul_left,
      inner_north_south] at hd
    simp only [RCLike.conj_to_real] at hd
    have hpos : 0 < ‖z‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hz0)
    nlinarith [mul_pos hpos hin]
  have hx0 : x ≠ 0 := fun h0 => by
    have := hx.1
    rw [h0, norm_zero] at this
    have := hx.2.2.1
    rw [h0, inner_zero_left] at this
    exact lt_irrefl 0 this
  have hx'0 : x' ≠ 0 := fun h0 => by
    have := hx'.2.2.1
    rw [h0, inner_zero_left] at this
    exact lt_irrefl 0 this
  have hdir : DifferentialGeometry.Topology.Manifold.sphereDirection southPole x =
      DifferentialGeometry.Topology.Manifold.sphereDirection southPole x' := by
    have h1 := congrArg Prod.fst h
    simp only [southCapMap_apply] at h1
    exact (DifferentialGeometry.Topology.Handle.stereoChart northPole).toPartialEquiv.injOn
      (hsrc x hx hx0) (hsrc x' hx' hx'0) h1
  have hxd := congrArg (fun w : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 =>
    ‖x‖ • (w : EuclideanSpace ℝ (Fin 3))) hdir
  rw [DifferentialGeometry.Topology.Manifold.coe_sphereDirection _ hx0,
    DifferentialGeometry.Topology.Manifold.coe_sphereDirection _ hx'0, smul_smul, smul_smul,
    mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx0), hnorm,
    mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx'0), one_smul, one_smul] at hxd
  exact hxd

theorem capMap_injOn {ε : ℝ} {b : Bool} {x x' : ClosedCell 3} (hx : x ∈ neckCapRegion ε b)
    (hx' : x' ∈ neckCapRegion ε b)
    (h : capMap b (x : EuclideanSpace ℝ (Fin 3)) = capMap b (x' : EuclideanSpace ℝ (Fin 3))) :
    x = x' := by
  have hc := southCapCond_of_mem_capRegion hx
  have hc' := southCapCond_of_mem_capRegion hx'
  apply Subtype.ext
  cases b
  · exact southCapMap_injOn hc hc' h
  · have h' := southCapMap_injOn hc hc' h
    have := congrArg reflectThree h'
    simpa only [ite_true, reflectThree_reflectThree] using this

/-- The handle end lands on the handle side of the neck. -/
theorem handleEnd_mem_neckDomain {ε : ℝ} (b : Bool)
    {q : ClosedCell 2 × Icc (0 : ℝ) 1} (hq : |(q.2 : ℝ) - (iccEnd b : ℝ)| < 2 * ε) :
    handleEnd b q ∈ neckDomain ε ∧ 0 ≤ (handleEnd b q).2 ∧ ‖(handleEnd b q).1‖ ≤ 1 := by
  have h1 : ‖((q.1 : ClosedCell 2) : EuclideanSpace ℝ (Fin 2))‖ ≤ 1 := q.1.2
  have ht := q.2.2
  have hε0 : 0 < ε := by
    have := abs_nonneg ((q.2 : ℝ) - (iccEnd b : ℝ))
    linarith
  cases b
  · have hb : ((iccEnd false : Icc (0 : ℝ) 1) : ℝ) = 0 := rfl
    rw [hb, sub_zero, abs_of_nonneg ht.1] at hq
    refine ⟨⟨by change ‖((q.1 : ClosedCell 2) : EuclideanSpace ℝ (Fin 2))‖ < 1 + 2 * ε; linarith,
      ?_⟩, ht.1, h1⟩
    change |(q.2 : ℝ)| < 2 * ε
    rw [abs_of_nonneg ht.1]
    exact hq
  · have hb : ((iccEnd true : Icc (0 : ℝ) 1) : ℝ) = 1 := rfl
    rw [hb, abs_sub_comm, abs_of_nonneg (by linarith [ht.2])] at hq
    refine ⟨⟨by change ‖((q.1 : ClosedCell 2) : EuclideanSpace ℝ (Fin 2))‖ < 1 + 2 * ε; linarith,
      ?_⟩, ?_, h1⟩
    · change |1 - (q.2 : ℝ)| < 2 * ε
      rw [abs_of_nonneg (by linarith [ht.2])]
      exact hq
    · change (0 : ℝ) ≤ 1 - (q.2 : ℝ)
      linarith [ht.2]

/-- Every handle-side point of the neck domain is a handle end point. -/
theorem exists_handleEnd_eq {ε : ℝ} (hε' : ε ≤ 1 / 8) (b : Bool)
    {q : EuclideanSpace ℝ (Fin 2) × ℝ} (hq : q ∈ neckDomain ε) (hq0 : 0 ≤ q.2)
    (hq1 : ‖q.1‖ ≤ 1) :
    ∃ q' : ClosedCell 2 × Icc (0 : ℝ) 1, |(q'.2 : ℝ) - (iccEnd b : ℝ)| < 2 * ε ∧
      handleEnd b q' = q := by
  have hq2 : q.2 < 2 * ε := (abs_lt.mp hq.2).2
  have hle : q.2 ≤ 1 := by linarith
  cases b
  · refine ⟨(⟨q.1, by simpa using hq1⟩, ⟨q.2, hq0, hle⟩), ?_, rfl⟩
    change |q.2 - 0| < 2 * ε
    rw [sub_zero, abs_of_nonneg hq0]
    exact hq2
  · refine ⟨(⟨q.1, by simpa using hq1⟩, ⟨1 - q.2, by linarith, by linarith⟩), ?_, ?_⟩
    · change |1 - q.2 - 1| < 2 * ε
      rw [show 1 - q.2 - 1 = -q.2 by ring, abs_neg, abs_of_nonneg hq0]
      exact hq2
    · change (q.1, 1 - (1 - q.2)) = q
      rw [sub_sub_cancel]

theorem handleEnd_injective (b : Bool) : Injective (handleEnd b) := by
  rintro ⟨z, t⟩ ⟨z', t'⟩ h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only [handleEnd] at h1 h2
  have hz : z = z' := Subtype.ext h1
  have ht : t = t' := by
    apply Subtype.ext
    cases b
    · exact h2
    · simp only [endCoord, ite_true] at h2
      linarith
  rw [hz, ht]

end GC.GraphManifold.Assembly
