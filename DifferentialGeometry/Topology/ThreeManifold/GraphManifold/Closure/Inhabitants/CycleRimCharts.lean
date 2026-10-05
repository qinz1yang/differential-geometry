import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.CycleNecks
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.CycleIncidence

/-!
The four full-circle ambient rim charts are the genuine compositions of the polar rim with
the separated stereographic necks, with the true inner and antipodal outer vertex inequalities.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Manifold DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.Topology.Manifold GC.Endpoint GC.GraphManifold.Assembly
open scoped Manifold ContDiff InnerProductSpace

namespace GC.GraphManifold.Assembly

attribute [local instance] Handle.closedCellChartedSpaceSucc Handle.closedCellIsManifold

private abbrev E2 := EuclideanSpace ℝ (Fin 2)
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

def cycleRimChart (b e : Bool) :
    PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ × ℝ)) (𝓡 3)
      (Circle × (ℝ × ℝ)) (NoCuts.carrier standardThreeSphereLift.{0}).Carrier ∞ :=
  standardCycleRim.trans (cycleNeck b e)

private theorem cycleRimChart_neck_mem (b e : Bool) {p : Circle × (ℝ × ℝ)}
    (hp : p ∈ standardCycleRim.source) : standardCycleRim p ∈ (cycleNeck b e).source := by
  rw [cycleNeck_source]
  have ht := standardCycleRim.map_source hp
  change ‖(standardCycleRim p).1‖ < 1 + 2 * (1 / 16) ∧
    |(standardCycleRim p).2| < 2 * (1 / 16)
  change 7 / 8 < ‖(standardCycleRim p).1‖ ∧ ‖(standardCycleRim p).1‖ < 9 / 8 ∧
    |(standardCycleRim p).2| < 1 / 8 at ht
  constructor <;> linarith [ht.2.1, ht.2.2]

theorem cycleRimChart_source (b e : Bool) :
    (cycleRimChart b e).source = univ ×ˢ rimBox 2 := by
  ext p
  change (p ∈ standardCycleRim.source ∧ standardCycleRim p ∈ (cycleNeck b e).source) ↔ _
  constructor
  · exact fun hp => hp.1
  · exact fun hp => ⟨hp, cycleRimChart_neck_mem b e hp⟩

theorem cycleRimChart_disjoint {b e b' e' : Bool} (h : (b, e) ≠ (b', e')) :
    Disjoint (cycleRimChart b e).target (cycleRimChart b' e').target :=
  (cycleNeck_disjoint h).mono
    (fun z hz => show z ∈ (cycleNeck b e).target from hz.1)
    (fun z hz => show z ∈ (cycleNeck b' e').target from hz.1)

private theorem cycleRimChart_apply (b e : Bool) (p : Circle × (ℝ × ℝ)) :
    cycleRimChart b e p = cycleBallAmbient false
      ((if Bool.xor b e then 4 / (1 + (1 / 16 : ℝ) * p.2.2) else
          1 + (1 / 16 : ℝ) * p.2.2) •
        ((if b then -(Handle.stereoChart northPole).symm
            ((1 + (1 / 16 : ℝ) * p.2.1) • planeOfCircle p.1) else
          (Handle.stereoChart northPole).symm
            ((1 + (1 / 16 : ℝ) * p.2.1) • planeOfCircle p.1)) : E3)) := by
  cases b <;> cases e <;> rfl

theorem cycleRimChart_ball {b e : Bool} {p : Circle × (ℝ × ℝ)}
    (hp : p ∈ (cycleRimChart b e).source) :
    cycleRimChart b e p ∈ range (cycleBallPiece (Bool.xor b e)).map ↔ p.2.2 ≤ 0 := by
  have hy : |p.2.2| < 2 := by
    rw [cycleRimChart_source] at hp
    exact hp.2.2
  have hden : 0 < 1 + (1 / 16 : ℝ) * p.2.2 := by
    have hl := (abs_lt.mp hy).1
    linarith
  have hun : ∀ θ : S2, ‖(θ : E3)‖ = 1 := by
    intro θ
    exact mem_sphere_zero_iff_norm.mp θ.property
  rw [cycleRimChart_apply]
  cases b <;> cases e <;>
    simp only [Bool.false_xor, Bool.true_xor, Bool.false_eq_true, Bool.not_false,
      Bool.not_true, ↓reduceIte]
  · change _ ∈ range (cycleBallPiece false).map ↔ p.2.2 ≤ 0
    rw [cycleBall_false_mem, norm_smul, hun, mul_one, Real.norm_of_nonneg hden.le]
    constructor <;> intro h <;> linarith
  · change _ ∈ range (cycleBallPiece true).map ↔ p.2.2 ≤ 0
    rw [cycleBall_true_mem, norm_smul, hun, mul_one,
      Real.norm_of_nonneg (div_pos (by norm_num) hden).le]
    rw [le_div_iff₀ hden]
    constructor <;> intro h <;> linarith
  · change _ ∈ range (cycleBallPiece true).map ↔ p.2.2 ≤ 0
    rw [cycleBall_true_mem, norm_smul, norm_neg, hun, mul_one,
      Real.norm_of_nonneg (div_pos (by norm_num) hden).le]
    rw [le_div_iff₀ hden]
    constructor <;> intro h <;> linarith
  · change _ ∈ range (cycleBallPiece false).map ↔ p.2.2 ≤ 0
    rw [cycleBall_false_mem, norm_smul, norm_neg, hun, mul_one, Real.norm_of_nonneg hden.le]
    constructor <;> intro h <;> linarith

private theorem cycleRimChart_eq_handle {b e : Bool} {p : Circle × (ℝ × ℝ)}
    (hp : p ∈ (cycleRimChart b e).source) :
    cycleRimChart b e p = cycleHandleChart b
      ((standardCycleRim p).1, endCoord e (standardCycleRim p).2) := by
  have hy : |p.2.2| < 2 := by rw [cycleRimChart_source] at hp; exact hp.2.2
  have hl := (abs_lt.mp hy).1
  have hu := (abs_lt.mp hy).2
  rw [cycleRimChart_apply, cycleHandleChart_apply]
  cases b <;> cases e
  · change cycleBallAmbient false ((1 + (1 / 16 : ℝ) * p.2.2) •
      ((Handle.stereoChart northPole).symm (standardCycleRim p).1 : E3)) =
        cycleBallAmbient false (cycleHandleRadius ((1 / 16 : ℝ) * p.2.2) •
          ((Handle.stereoChart northPole).symm (standardCycleRim p).1 : E3))
    rw [cycleHandleRadius_inner (by linarith)]
  · change cycleBallAmbient false ((4 / (1 + (1 / 16 : ℝ) * p.2.2)) •
      ((Handle.stereoChart northPole).symm (standardCycleRim p).1 : E3)) =
        cycleBallAmbient false (cycleHandleRadius (1 - (1 / 16 : ℝ) * p.2.2) •
          ((Handle.stereoChart northPole).symm (standardCycleRim p).1 : E3))
    rw [cycleHandleRadius_outer (by linarith)]
    congr 2
    congr 1
    ring
  · change cycleBallAmbient false ((4 / (1 + (1 / 16 : ℝ) * p.2.2)) •
      (-((Handle.stereoChart northPole).symm (standardCycleRim p).1 : E3))) =
        cycleBallAmbient false (cycleHandleRadius (1 - (1 / 16 : ℝ) * p.2.2) •
          (-((Handle.stereoChart northPole).symm (standardCycleRim p).1 : E3)))
    rw [cycleHandleRadius_outer (by linarith)]
    congr 2
    congr 1
    ring
  · change cycleBallAmbient false ((1 + (1 / 16 : ℝ) * p.2.2) •
      (-((Handle.stereoChart northPole).symm (standardCycleRim p).1 : E3))) =
        cycleBallAmbient false (cycleHandleRadius (1 -
          (1 - (1 / 16 : ℝ) * p.2.2)) •
            (-((Handle.stereoChart northPole).symm (standardCycleRim p).1 : E3)))
    have he : 1 - (1 - (1 / 16 : ℝ) * p.2.2) = (1 / 16 : ℝ) * p.2.2 := by ring
    rw [he, cycleHandleRadius_inner (by linarith)]

private theorem cycleRimHandle_source {b e : Bool} {p : Circle × (ℝ × ℝ)}
    (hp : p ∈ (cycleRimChart b e).source) :
    ((standardCycleRim p).1, endCoord e (standardCycleRim p).2) ∈
      (cycleHandleChart b).source := by
  rw [cycleHandleChart_source]
  have hy : |p.2.2| < 2 := by rw [cycleRimChart_source] at hp; exact hp.2.2
  have hl := (abs_lt.mp hy).1
  have hu := (abs_lt.mp hy).2
  cases e
  · change True ∧ -1 / 2 < (1 / 16 : ℝ) * p.2.2 ∧
      (1 / 16 : ℝ) * p.2.2 < 3 / 2
    exact ⟨trivial, by constructor <;> linarith⟩
  · change True ∧ -1 / 2 < 1 - (1 / 16 : ℝ) * p.2.2 ∧
      1 - (1 / 16 : ℝ) * p.2.2 < 3 / 2
    exact ⟨trivial, by constructor <;> linarith⟩

private theorem cycleRimPlane_norm {p : Circle × (ℝ × ℝ)}
    (hp : p ∈ standardCycleRim.source) :
    ‖(standardCycleRim p).1‖ = 1 + (1 / 16 : ℝ) * p.2.1 := by
  change ‖(1 + (1 / 16 : ℝ) * p.2.1) • planeOfCircle p.1‖ = _
  have hl := (abs_lt.mp hp.2.1).1
  rw [norm_smul, Real.norm_of_nonneg (by linarith), planeOfCircle,
    LinearIsometryEquiv.norm_map, Circle.norm_coe, mul_one]

theorem cycleRimChart_handle {b e : Bool} {p : Circle × (ℝ × ℝ)}
    (hp : p ∈ (cycleRimChart b e).source) :
    cycleRimChart b e p ∈ range (cycleS3Handle b).map ↔
      0 ≤ p.2.2 ∧ p.2.1 ≤ 0 := by
  have hpr : p ∈ standardCycleRim.source := by
    rw [cycleRimChart_source] at hp
    exact hp
  have ha := cycleRimPlane_norm hpr
  have hy := (abs_lt.mp hpr.2.2)
  constructor
  · rintro ⟨x, hx⟩
    change cycleHandleChart b (x.1.val, x.2.val) = cycleRimChart b e p at hx
    rw [cycleRimChart_eq_handle hp] at hx
    have he := (cycleHandleChart b).injOn
      (by rw [cycleHandleChart_source]; exact ⟨trivial, by
        constructor <;> linarith [x.2.property.1, x.2.property.2]⟩)
      (cycleRimHandle_source hp) hx
    have hx0 := congrArg Prod.fst he
    have ht0 := congrArg Prod.snd he
    have ha1 : ‖(standardCycleRim p).1‖ ≤ 1 := by
      rw [← hx0]
      exact x.1.property
    constructor
    · cases e
      · change x.2.val = (1 / 16 : ℝ) * p.2.2 at ht0
        linarith [x.2.property.1]
      · change x.2.val = 1 - (1 / 16 : ℝ) * p.2.2 at ht0
        linarith [x.2.property.2]
    · linarith [ha1, ha]
  · intro hh
    let x : ClosedCell 2 := ⟨(standardCycleRim p).1, by rw [ha]; linarith [hh.2]⟩
    have ht : endCoord e (standardCycleRim p).2 ∈ Icc (0 : ℝ) 1 := by
      cases e
      · change 0 ≤ (1 / 16 : ℝ) * p.2.2 ∧ (1 / 16 : ℝ) * p.2.2 ≤ 1
        constructor <;> linarith [hh.1, hy.1, hy.2]
      · change 0 ≤ 1 - (1 / 16 : ℝ) * p.2.2 ∧ 1 - (1 / 16 : ℝ) * p.2.2 ≤ 1
        constructor <;> linarith [hh.1, hy.1, hy.2]
    exact ⟨(x, ⟨endCoord e (standardCycleRim p).2, ht⟩),
      (cycleRimChart_eq_handle hp).symm⟩

theorem cycleRimChart_label (b e : Bool) :
    cycleRimChart b e '' {p | p.2 = (0, 0)} =
      (fun x : ClosedCell 2 => (cycleS3Handle b).map (x, iccEnd e)) '' diskRim := by
  have hplane : ∀ θ : Circle, ‖planeOfCircle θ‖ = 1 := by
    intro θ
    rw [planeOfCircle, LinearIsometryEquiv.norm_map, Circle.norm_coe]
  have heq : ∀ θ : Circle, cycleRimChart b e (θ, (0, 0)) =
      (cycleS3Handle b).map (⟨planeOfCircle θ, (hplane θ).le⟩, iccEnd e) := by
    intro θ
    have hp : (θ, ((0 : ℝ), (0 : ℝ))) ∈ (cycleRimChart b e).source := by
      rw [cycleRimChart_source]
      exact ⟨trivial, by constructor <;> norm_num⟩
    rw [cycleRimChart_eq_handle hp]
    change cycleHandleChart b
      ((standardCycleRim (θ, (0, 0))).1, endCoord e (standardCycleRim (θ, (0, 0))).2) =
        cycleHandleChart b (planeOfCircle θ, (iccEnd e).val)
    congr 1
    cases e <;> simp [standardCycleRim, neckRim, endCoord, iccEnd]
  ext z
  constructor
  · rintro ⟨⟨θ, v⟩, hv, rfl⟩
    change v = (0, 0) at hv
    subst v
    refine ⟨⟨planeOfCircle θ, (hplane θ).le⟩, ?_, (heq θ).symm⟩
    change (⟨planeOfCircle θ, (hplane θ).le⟩ : ClosedCell 2) ∈
      (𝓡∂ 2).boundary (ClosedCell 2)
    rw [closedCell_boundary_eq_sphere 1]
    exact hplane θ
  · rintro ⟨x, hx, rfl⟩
    have hnx : ‖x.val‖ = 1 := by
      change x ∈ (𝓡∂ 2).boundary (ClosedCell 2) at hx
      rw [closedCell_boundary_eq_sphere 1] at hx
      exact hx
    let w : ℂ := Complex.orthonormalBasisOneI.repr.symm x.val
    have hnw : ‖w‖ = 1 := by
      change ‖Complex.orthonormalBasisOneI.repr.symm x.val‖ = 1
      rw [LinearIsometryEquiv.norm_map, hnx]
    let θ : Circle := ⟨w, mem_sphere_zero_iff_norm.mpr hnw⟩
    have hθ : planeOfCircle θ = x.val := by
      change Complex.orthonormalBasisOneI.repr
        (Complex.orthonormalBasisOneI.repr.symm x.val) = x.val
      exact LinearIsometryEquiv.apply_symm_apply _ _
    refine ⟨(θ, (0, 0)), rfl, ?_⟩
    rw [heq]
    congr 2
    exact Subtype.ext hθ

private theorem cycleRimChart_other_handle {b e : Bool} {p : Circle × (ℝ × ℝ)}
    (hp : p ∈ (cycleRimChart b e).source) :
    cycleRimChart b e p ∉ range (cycleS3Handle (!b)).map := by
  have hpr : p ∈ standardCycleRim.source := by
    rw [cycleRimChart_source] at hp
    exact hp
  have hn := standardCycleRim.map_source hpr
  change 7 / 8 < ‖(standardCycleRim p).1‖ ∧
    ‖(standardCycleRim p).1‖ < 9 / 8 ∧ |(standardCycleRim p).2| < 1 / 8 at hn
  have hs : ∀ a : E2, ‖a‖ < 2 →
      ⟪((Handle.stereoChart northPole).symm a : E3), (northPole : E3)⟫_ℝ < 0 := by
    intro a ha
    rw [Handle.inner_stereoChart_symm]
    apply div_neg_of_neg_of_pos
    · nlinarith [norm_nonneg a]
    · positivity
  have hs0 := hs (standardCycleRim p).1 (by linarith [hn.2.1])
  change ⟪((Handle.stereoChart northPole).symm
    ((1 + (1 / 16 : ℝ) * p.2.1) • planeOfCircle p.1) : E3),
      (northPole : E3)⟫_ℝ < 0 at hs0
  have hy := abs_lt.mp hpr.2.2
  have hr : 0 < 1 + (1 / 16 : ℝ) * p.2.2 := by linarith [hy.1]
  rintro ⟨q, hq⟩
  have hqs := hs q.1.val (by linarith [q.1.property])
  have ht : (if !b then 1 - q.2.val else q.2.val) ∈ Icc (0 : ℝ) 1 := by
    cases b <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    · constructor <;> linarith [q.2.property.1, q.2.property.2]
    · exact q.2.property
  have hrad : 0 < cycleHandleRadius (if !b then 1 - q.2.val else q.2.val) := by
    have hh := cycleHandleRadius_strictMono.monotoneOn
      (show (0 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num) ht ht.1
    rw [cycleHandleRadius_inner (by norm_num)] at hh
    linarith
  change cycleHandleChart (!b) (q.1.val, q.2.val) = cycleRimChart b e p at hq
  rw [cycleHandleChart_apply, cycleRimChart_apply] at hq
  have he := (cycleBallAmbient false).injOn
    (by rw [cycleBallAmbient_source]; exact mem_univ _)
    (by rw [cycleBallAmbient_source]; exact mem_univ _) hq
  have hinner := congrArg (fun v : E3 => ⟪v, (northPole : E3)⟫_ℝ) he
  cases b <;> cases e <;>
    simp only [Bool.not_false, Bool.not_true, Bool.false_xor, Bool.true_xor,
      Bool.false_eq_true, ↓reduceIte] at hinner hrad
  · change ⟪cycleHandleRadius (1 - q.2.val) •
      (-((Handle.stereoChart northPole).symm q.1.val : E3)), (northPole : E3)⟫_ℝ =
        ⟪(1 + (1 / 16 : ℝ) * p.2.2) •
          ((Handle.stereoChart northPole).symm
            ((1 + (1 / 16 : ℝ) * p.2.1) • planeOfCircle p.1) : E3),
          (northPole : E3)⟫_ℝ at hinner
    simp only [inner_smul_left, inner_neg_left, starRingEnd_apply, star_trivial] at hinner
    nlinarith
  · change ⟪cycleHandleRadius (1 - q.2.val) •
      (-((Handle.stereoChart northPole).symm q.1.val : E3)), (northPole : E3)⟫_ℝ =
        ⟪(4 / (1 + (1 / 16 : ℝ) * p.2.2)) •
          ((Handle.stereoChart northPole).symm
            ((1 + (1 / 16 : ℝ) * p.2.1) • planeOfCircle p.1) : E3),
          (northPole : E3)⟫_ℝ at hinner
    simp only [inner_smul_left, inner_neg_left, starRingEnd_apply, star_trivial] at hinner
    have hdiv : 0 < 4 / (1 + (1 / 16 : ℝ) * p.2.2) := div_pos (by norm_num) hr
    nlinarith
  · change ⟪cycleHandleRadius q.2.val •
      ((Handle.stereoChart northPole).symm q.1.val : E3), (northPole : E3)⟫_ℝ =
        ⟪(4 / (1 + (1 / 16 : ℝ) * p.2.2)) •
          (-((Handle.stereoChart northPole).symm
            ((1 + (1 / 16 : ℝ) * p.2.1) • planeOfCircle p.1) : E3)),
          (northPole : E3)⟫_ℝ at hinner
    simp only [inner_smul_left, inner_neg_left, starRingEnd_apply, star_trivial] at hinner
    have hdiv : 0 < 4 / (1 + (1 / 16 : ℝ) * p.2.2) := div_pos (by norm_num) hr
    nlinarith
  · change ⟪cycleHandleRadius q.2.val •
      ((Handle.stereoChart northPole).symm q.1.val : E3), (northPole : E3)⟫_ℝ =
        ⟪(1 + (1 / 16 : ℝ) * p.2.2) •
          (-((Handle.stereoChart northPole).symm
            ((1 + (1 / 16 : ℝ) * p.2.1) • planeOfCircle p.1) : E3)),
          (northPole : E3)⟫_ℝ at hinner
    simp only [inner_smul_left, inner_neg_left, starRingEnd_apply, star_trivial] at hinner
    nlinarith

private theorem cycleRimChart_other_ball {b e : Bool} {p : Circle × (ℝ × ℝ)}
    (hp : p ∈ (cycleRimChart b e).source) :
    cycleRimChart b e p ∉ range (cycleBallPiece (!(Bool.xor b e))).map := by
  have hy : |p.2.2| < 2 := by rw [cycleRimChart_source] at hp; exact hp.2.2
  have hl := (abs_lt.mp hy).1
  have hu := (abs_lt.mp hy).2
  have hr : 0 < 1 + (1 / 16 : ℝ) * p.2.2 := by linarith
  have hun : ∀ θ : S2, ‖(θ : E3)‖ = 1 := by
    intro θ
    exact mem_sphere_zero_iff_norm.mp θ.property
  rw [cycleRimChart_apply]
  cases b <;> cases e <;> simp only [Bool.false_xor, Bool.true_xor, Bool.not_false,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  · change _ ∉ range (cycleBallPiece true).map
    rw [cycleBall_true_mem, norm_smul, hun, mul_one, Real.norm_of_nonneg hr.le]
    linarith
  · change _ ∉ range (cycleBallPiece false).map
    rw [cycleBall_false_mem, norm_smul, hun, mul_one,
      Real.norm_of_nonneg (div_pos (by norm_num) hr).le]
    intro h
    have hh := (div_le_iff₀ hr).mp h
    linarith
  · change _ ∉ range (cycleBallPiece false).map
    rw [cycleBall_false_mem, norm_smul, norm_neg, hun, mul_one,
      Real.norm_of_nonneg (div_pos (by norm_num) hr).le]
    intro h
    have hh := (div_le_iff₀ hr).mp h
    linarith
  · change _ ∉ range (cycleBallPiece true).map
    rw [cycleBall_true_mem, norm_smul, norm_neg, hun, mul_one, Real.norm_of_nonneg hr.le]
    linarith

theorem cycleRimChart_quadrant {b e : Bool} {p : Circle × (ℝ × ℝ)}
    (hp : p ∈ (cycleRimChart b e).source) (hx : 0 < p.2.1) (hy : 0 < p.2.2) :
    cycleRimChart b e p ∉
      (⋃ v : Bool, range (cycleBallPiece v).map) ∪
        ⋃ a : Bool, range (cycleS3Handle a).map := by
  rintro (hball | hhandle)
  · obtain ⟨v, hv⟩ := mem_iUnion.mp hball
    by_cases h : v = Bool.xor b e
    · subst v
      have hh := (cycleRimChart_ball hp).mp hv
      linarith
    · have he : v = !(Bool.xor b e) := by
        cases v <;> cases b <;> cases e <;> simp_all
      subst v
      exact cycleRimChart_other_ball hp hv
  · obtain ⟨a, ha⟩ := mem_iUnion.mp hhandle
    by_cases h : a = b
    · subst a
      have hh := (cycleRimChart_handle hp).mp ha
      linarith [hh.2]
    · have he : a = !b := by cases a <;> cases b <;> simp_all
      subst a
      exact cycleRimChart_other_handle hp ha

end GC.GraphManifold.Assembly
