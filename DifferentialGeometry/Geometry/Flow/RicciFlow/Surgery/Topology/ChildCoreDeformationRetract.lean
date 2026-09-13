import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildParent
import DifferentialGeometry.Topology.Manifold.InteriorImage
import DifferentialGeometry.Topology.VanKampen.HomotopyRetract
import Mathlib.Geometry.Manifold.SmoothEmbedding
import Mathlib.Topology.Homotopy.Equiv

set_option autoImplicit false

noncomputable section

open Set Topology Manifold
open scoped Manifold ContDiff ContinuousMap unitInterval

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace TubeSystem

variable {M : Type*} [TopologicalSpace M] (T : TubeSystem M)

def middleSphere (a : T.Index) : Set M :=
  T.tube a '' {z : TubeDomain | z.2.1 = 0}

def puncturedCore : Set M := (⋃ a, T.middleSphere a)ᶜ

def shortenTime (t : ℝ) : ℝ := if 0 < t then max t 1 else min t (-1)

def shrinkTime (s t : ℝ) : ℝ :=
  if 0 < t then max t ((1 - s) * t + s) else min t ((1 - s) * t - s)

theorem shrinkTime_zero (t : ℝ) : shrinkTime 0 t = t := by
  simp [shrinkTime]

theorem shrinkTime_one (t : ℝ) : shrinkTime 1 t = shortenTime t := by
  simp [shrinkTime, shortenTime]

theorem one_le_shrinkTime_one {t : ℝ} (h : 0 < t) : 1 ≤ shrinkTime 1 t := by
  rw [shrinkTime_one, shortenTime, if_pos h]
  exact le_max_right _ _

theorem shrinkTime_one_le_neg_one {t : ℝ} (h : t < 0) : shrinkTime 1 t ≤ -1 := by
  rw [shrinkTime_one, shortenTime, if_neg (not_lt.mpr h.le)]
  exact min_le_right _ _

theorem shrinkTime_of_pos {s t : ℝ} (h : 0 < t) :
    shrinkTime s t = max t ((1 - s) * t + s) := by
  rw [shrinkTime, if_pos h]

theorem shrinkTime_of_nonpos {s t : ℝ} (h : ¬ 0 < t) :
    shrinkTime s t = min t ((1 - s) * t - s) := by
  rw [shrinkTime, if_neg h]

theorem shrinkTime_pos {s t : ℝ} (h : 0 < t) : 0 < shrinkTime s t := by
  rw [shrinkTime_of_pos h]
  exact lt_of_lt_of_le h (le_max_left _ _)

theorem shrinkTime_neg {s t : ℝ} (h : t < 0) : shrinkTime s t < 0 := by
  rw [shrinkTime_of_nonpos (not_lt.mpr h.le)]
  exact lt_of_le_of_lt (min_le_left _ _) h

theorem shrinkTime_ne_zero {s t : ℝ} (h : t ≠ 0) : shrinkTime s t ≠ 0 := by
  rcases lt_or_gt_of_ne h with h' | h'
  · exact ne_of_lt (shrinkTime_neg h')
  · exact ne_of_gt (shrinkTime_pos h')

theorem shrinkTime_eq_self_of_one_le {s t : ℝ} (hs : 0 ≤ s) (h : 1 ≤ t) :
    shrinkTime s t = t := by
  rw [shrinkTime_of_pos (lt_of_lt_of_le one_pos h), max_eq_left]
  nlinarith

theorem shrinkTime_eq_self_of_le_neg_one {s t : ℝ} (hs : 0 ≤ s) (h : t ≤ -1) :
    shrinkTime s t = t := by
  rw [shrinkTime_of_nonpos (not_lt.mpr (by linarith)), min_eq_left]
  nlinarith

theorem shrinkTime_mem_Icc {s t : ℝ} (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (ht : t ∈ Icc (-2 : ℝ) 2) : shrinkTime s t ∈ Icc (-2 : ℝ) 2 := by
  have hs' : 0 ≤ 1 - s := by linarith
  rcases lt_trichotomy t 0 with ht₀ | ht₀ | ht₀
  · rw [shrinkTime_of_nonpos (not_lt.mpr ht₀.le)]
    refine ⟨le_min ht.1 ?_, le_trans (min_le_left _ _) ht.2⟩
    nlinarith [mul_le_mul_of_nonneg_left ht.1 hs']
  · subst ht₀
    rw [shrinkTime_of_nonpos (lt_irrefl 0)]
    refine ⟨le_min (by norm_num) ?_, le_trans (min_le_left _ _) (by norm_num)⟩
    nlinarith
  · rw [shrinkTime_of_pos ht₀]
    refine ⟨le_trans ht.1 (le_max_left _ _), max_le ht.2 ?_⟩
    nlinarith [mul_le_mul_of_nonneg_left ht.2 hs']

def shrinkCoord (s : I) (z : Icc (-2 : ℝ) 2) : Icc (-2 : ℝ) 2 :=
  ⟨shrinkTime (s : ℝ) z.1, shrinkTime_mem_Icc s.2.1 s.2.2 z.2⟩

def shrinkTube (s : I) (z : TubeDomain) : TubeDomain :=
  (z.1, shrinkCoord s z.2)

theorem shrinkTube_apply (s : I) (z : TubeDomain) :
    shrinkTube s z = (z.1, shrinkCoord s z.2) := rfl

theorem shrinkTube_fst (s : I) (z : TubeDomain) : (shrinkTube s z).1 = z.1 := rfl

theorem shrinkTube_snd_val (s : I) (z : TubeDomain) :
    (shrinkTube s z).2.1 = shrinkTime (s : ℝ) z.2.1 := rfl

theorem shrinkTube_zero (z : TubeDomain) : shrinkTube (0 : I) z = z := by
  refine Prod.ext rfl (Subtype.ext ?_)
  exact shrinkTime_zero z.2.1

def expandCoord (s : I) (z : Icc (-2 : ℝ) 2) : Icc (-2 : ℝ) 2 :=
  ⟨max z.1 ((1 - (s : ℝ)) * z.1 + s), by
    have hs : (0 : ℝ) ≤ s := s.2.1
    have hs' : (0 : ℝ) ≤ 1 - s := by linarith [s.2.2]
    have h₁ : (1 - (s : ℝ)) * z.1 ≤ (1 - (s : ℝ)) * 2 :=
      mul_le_mul_of_nonneg_left z.2.2 hs'
    refine ⟨le_trans z.2.1 (le_max_left _ _), max_le z.2.2 ?_⟩
    linarith⟩

def compressCoord (s : I) (z : Icc (-2 : ℝ) 2) : Icc (-2 : ℝ) 2 :=
  ⟨min z.1 ((1 - (s : ℝ)) * z.1 - s), by
    have hs : (0 : ℝ) ≤ s := s.2.1
    have hs' : (0 : ℝ) ≤ 1 - s := by linarith [s.2.2]
    have h₁ : (1 - (s : ℝ)) * (-2) ≤ (1 - (s : ℝ)) * z.1 :=
      mul_le_mul_of_nonneg_left z.2.1 hs'
    exact ⟨le_min z.2.1 (by linarith), le_trans (min_le_left _ _) z.2.2⟩⟩

theorem expandCoord_apply (s : I) (z : Icc (-2 : ℝ) 2) :
    (expandCoord s z).1 = max z.1 ((1 - (s : ℝ)) * z.1 + s) := rfl

theorem compressCoord_apply (s : I) (z : Icc (-2 : ℝ) 2) :
    (compressCoord s z).1 = min z.1 ((1 - (s : ℝ)) * z.1 - s) := rfl

theorem continuous_expandCoord (s : I) : Continuous (expandCoord s) := by
  refine Continuous.subtype_mk (Continuous.max continuous_subtype_val ?_) _
  exact ((continuous_const.sub continuous_const).mul continuous_subtype_val).add continuous_const

theorem continuous_compressCoord (s : I) : Continuous (compressCoord s) := by
  refine Continuous.subtype_mk (Continuous.min continuous_subtype_val ?_) _
  exact ((continuous_const.sub continuous_const).mul continuous_subtype_val).sub continuous_const

theorem continuous_expandCoord_joint :
    Continuous fun q : I × Icc (-2 : ℝ) 2 => expandCoord q.1 q.2 := by
  have h₁ : Continuous fun q : I × Icc (-2 : ℝ) 2 => (1 - (q.1 : ℝ)) :=
    continuous_const.sub (continuous_subtype_val.comp continuous_fst)
  have hv : Continuous fun t : Icc (-2 : ℝ) 2 => t.1 := continuous_subtype_val
  have h₂ : Continuous fun q : I × Icc (-2 : ℝ) 2 => q.2.1 :=
    hv.comp continuous_snd
  have h₃ : Continuous fun q : I × Icc (-2 : ℝ) 2 => (q.1 : ℝ) :=
    continuous_subtype_val.comp continuous_fst
  exact Continuous.subtype_mk
    (Continuous.max (continuous_subtype_val.comp continuous_snd) ((h₁.mul h₂).add h₃)) _

theorem continuous_compressCoord_joint :
    Continuous fun q : I × Icc (-2 : ℝ) 2 => compressCoord q.1 q.2 := by
  have h₁ : Continuous fun q : I × Icc (-2 : ℝ) 2 => (1 - (q.1 : ℝ)) :=
    continuous_const.sub (continuous_subtype_val.comp continuous_fst)
  have hv : Continuous fun t : Icc (-2 : ℝ) 2 => t.1 := continuous_subtype_val
  have h₂ : Continuous fun q : I × Icc (-2 : ℝ) 2 => q.2.1 :=
    hv.comp continuous_snd
  have h₃ : Continuous fun q : I × Icc (-2 : ℝ) 2 => (q.1 : ℝ) :=
    continuous_subtype_val.comp continuous_fst
  exact Continuous.subtype_mk
    (Continuous.min (continuous_subtype_val.comp continuous_snd) ((h₁.mul h₂).sub h₃)) _

theorem shrinkTube_eq_expandCoord_of_pos (s : I) {z : TubeDomain} (hz : 0 < z.2.1) :
    shrinkTube s z = (z.1, expandCoord s z.2) := by
  rw [shrinkTube, expandCoord]
  exact Prod.ext rfl (Subtype.ext (shrinkTime_of_pos hz))

theorem shrinkTube_eq_compressCoord_of_neg (s : I) {z : TubeDomain} (hz : z.2.1 < 0) :
    shrinkTube s z = (z.1, compressCoord s z.2) := by
  rw [shrinkTube, compressCoord]
  exact Prod.ext rfl (Subtype.ext (shrinkTime_of_nonpos (not_lt.mpr hz.le)))

theorem expandCoord_eq_self_of_one_le (s : I) {z : Icc (-2 : ℝ) 2} (hz : 1 ≤ z.1) :
    expandCoord s z = z := by
  refine Subtype.ext ?_
  rw [expandCoord_apply, max_eq_left]
  nlinarith [s.2.1, s.2.2, hz]

theorem compressCoord_eq_self_of_le_neg_one (s : I) {z : Icc (-2 : ℝ) 2} (hz : z.1 ≤ -1) :
    compressCoord s z = z := by
  refine Subtype.ext ?_
  rw [compressCoord_apply, min_eq_left]
  nlinarith [s.2.1, hz]

theorem one_le_expandCoord_one (z : Icc (-2 : ℝ) 2) : 1 ≤ (expandCoord 1 z).1 := by
  rw [expandCoord_apply]
  simp

theorem compressCoord_one_le_neg_one (z : Icc (-2 : ℝ) 2) :
    (compressCoord 1 z).1 ≤ -1 := by
  rw [compressCoord_apply]
  simp

theorem closure_Icc_pos :
    closure {t : Icc (-2 : ℝ) 2 | 0 < t.1} = {t : Icc (-2 : ℝ) 2 | 0 ≤ t.1} := by
  refine Subset.antisymm
    (closure_minimal (by intro t ht; exact le_of_lt (show (0 : ℝ) < t.1 from ht))
      (isClosed_le continuous_const continuous_subtype_val)) ?_
  intro t ht
  rcases lt_or_eq_of_le (show (0 : ℝ) ≤ t.1 from ht) with h | h
  · exact subset_closure (show (0 : ℝ) < t.1 from h)
  · refine mem_closure_iff.2 fun U hU hzU => ?_
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (hU.mem_nhds hzU)
    have hε' : (0 : ℝ) < ε / 2 := by linarith
    have hlt : (0 : ℝ) < min 1 (ε / 2) := lt_min one_pos hε'
    have hle : min 1 (ε / 2) ≤ ε / 2 := min_le_right _ _
    have hI : min 1 (ε / 2) ∈ Set.Icc (-2 : ℝ) 2 :=
      ⟨by linarith, by linarith [min_le_left (1 : ℝ) (ε / 2)]⟩
    refine ⟨⟨min 1 (ε / 2), hI⟩, ?_, ?_⟩
    · refine hball ?_
      rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq, ← h, sub_zero, abs_of_pos hlt]
      linarith
    · exact hlt

theorem closure_Icc_neg :
    closure {t : Icc (-2 : ℝ) 2 | t.1 < 0} = {t : Icc (-2 : ℝ) 2 | t.1 ≤ 0} := by
  refine Subset.antisymm
    (closure_minimal (by intro t ht; exact le_of_lt (show t.1 < 0 from ht))
      (isClosed_le continuous_subtype_val continuous_const)) ?_
  intro t ht
  rcases lt_or_eq_of_le (show t.1 ≤ 0 from ht) with h | h
  · exact subset_closure (show t.1 < 0 from h)
  · refine mem_closure_iff.2 fun U hU hzU => ?_
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (hU.mem_nhds hzU)
    have hε' : (0 : ℝ) < ε / 2 := by linarith
    have hlt : (0 : ℝ) < min 1 (ε / 2) := lt_min one_pos hε'
    have hle : min 1 (ε / 2) ≤ ε / 2 := min_le_right _ _
    have hI : -(min 1 (ε / 2)) ∈ Set.Icc (-2 : ℝ) 2 :=
      ⟨by linarith [min_le_left (1 : ℝ) (ε / 2)], by linarith⟩
    refine ⟨⟨-(min 1 (ε / 2)), hI⟩, ?_, ?_⟩
    · refine hball ?_
      rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq, h, sub_zero, abs_neg, abs_of_pos hlt]
      linarith
    · exact (show -(min 1 (ε / 2)) < 0 from by linarith)

theorem closure_tubeTime_pos :
    closure {z : TubeDomain | 0 < z.2.1} = {z : TubeDomain | 0 ≤ z.2.1} := by
  have hset : {z : TubeDomain | 0 < z.2.1} =
      (univ : Set (Sphere 2)) ×ˢ {t : Icc (-2 : ℝ) 2 | 0 < t.1} := by
    ext z
    simp
  have hset' : {z : TubeDomain | 0 ≤ z.2.1} =
      (univ : Set (Sphere 2)) ×ˢ {t : Icc (-2 : ℝ) 2 | 0 ≤ t.1} := by
    ext z
    simp
  rw [hset, hset', closure_prod_eq, closure_univ, closure_Icc_pos]

theorem closure_tubeTime_neg :
    closure {z : TubeDomain | z.2.1 < 0} = {z : TubeDomain | z.2.1 ≤ 0} := by
  have hset : {z : TubeDomain | z.2.1 < 0} =
      (univ : Set (Sphere 2)) ×ˢ {t : Icc (-2 : ℝ) 2 | t.1 < 0} := by
    ext z
    simp
  have hset' : {z : TubeDomain | z.2.1 ≤ 0} =
      (univ : Set (Sphere 2)) ×ˢ {t : Icc (-2 : ℝ) 2 | t.1 ≤ 0} := by
    ext z
    simp
  rw [hset, hset', closure_prod_eq, closure_univ, closure_Icc_neg]

section Basic

variable {M : Type*} [TopologicalSpace M] (T : TubeSystem M)

def positiveTube (a : T.Index) : Set M := T.tube a '' {z : TubeDomain | 0 < z.2.1}

def negativeTube (a : T.Index) : Set M := T.tube a '' {z : TubeDomain | z.2.1 < 0}

def tubeTop (a : T.Index) : Set M := T.tube a '' {z : TubeDomain | 0 ≤ z.2.1}

def tubeBot (a : T.Index) : Set M := T.tube a '' {z : TubeDomain | z.2.1 ≤ 0}

def tubeCoord (a : T.Index) (x : M) (hx : x ∈ range (T.tube a)) : TubeDomain :=
  (T.embedding a).toHomeomorph.symm ⟨x, hx⟩

def tubeCoordMap (a : T.Index) : C(↥(range (T.tube a)), TubeDomain) :=
  ⟨fun u => (T.embedding a).toHomeomorph.symm u,
    (T.embedding a).toHomeomorph.symm.continuous⟩

theorem tubeCoord_eq (a : T.Index) (x : M) (hx : x ∈ range (T.tube a)) :
    T.tubeCoord a x hx = T.tubeCoordMap a ⟨x, hx⟩ := rfl

theorem tubeCoord_congr (a : T.Index) (x : M) (hx hx' : x ∈ range (T.tube a)) :
    T.tubeCoord a x hx = T.tubeCoord a x hx' :=
  congrArg (T.tubeCoordMap a) (Subtype.ext rfl)

theorem tubeCoord_tube (a : T.Index) (z : TubeDomain) :
    T.tubeCoord a (T.tube a z) (mem_range_self z) = z := by
  change (T.embedding a).toHomeomorph.symm ((T.embedding a).toHomeomorph z) = z
  exact (T.embedding a).toHomeomorph.symm_apply_apply z

theorem tube_tubeCoord (a : T.Index) (x : M) (hx : x ∈ range (T.tube a)) :
    T.tube a (T.tubeCoord a x hx) = x := by
  change ((T.embedding a).toHomeomorph ((T.embedding a).toHomeomorph.symm ⟨x, hx⟩)).1 = x
  exact congrArg Subtype.val ((T.embedding a).toHomeomorph.apply_symm_apply ⟨x, hx⟩)

theorem mem_middleSphere_iff (a : T.Index) (x : M) :
    x ∈ T.middleSphere a ↔ ∃ hx : x ∈ range (T.tube a), (T.tubeCoord a x hx).2.1 = 0 := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨mem_range_self z, by rw [T.tubeCoord_tube]; exact hz⟩
  · rintro ⟨hx, hz⟩
    exact ⟨T.tubeCoord a x hx, hz, T.tube_tubeCoord a x hx⟩

theorem mem_puncturedCore_iff (x : M) :
    x ∈ T.puncturedCore ↔ ∀ a, x ∉ T.middleSphere a := by
  simp [puncturedCore]

theorem eq_index_of_mem_range {a a' : T.Index} {x : M}
    (ha : x ∈ range (T.tube a)) (ha' : x ∈ range (T.tube a')) : a = a' := by
  by_contra hne
  exact Set.disjoint_left.mp (T.disjoint hne) ha ha'

theorem removedBand_subset_range (a : T.Index) :
    T.removedBand a ⊆ range (T.tube a) := image_subset_range _ _

theorem middleSphere_subset_range (a : T.Index) :
    T.middleSphere a ⊆ range (T.tube a) := image_subset_range _ _

theorem tubeTop_subset_range (a : T.Index) : T.tubeTop a ⊆ range (T.tube a) :=
  image_subset_range _ _

theorem tubeBot_subset_range (a : T.Index) : T.tubeBot a ⊆ range (T.tube a) :=
  image_subset_range _ _

theorem positiveTube_subset_tubeTop (a : T.Index) : T.positiveTube a ⊆ T.tubeTop a :=
  image_mono (by intro z hz; exact le_of_lt (show (0 : ℝ) < z.2.1 from hz))

theorem negativeTube_subset_tubeBot (a : T.Index) : T.negativeTube a ⊆ T.tubeBot a :=
  image_mono (by intro z hz; exact le_of_lt (show z.2.1 < 0 from hz))

theorem tubeCoord_snd_ne_zero {a : T.Index} {x : M} (hx : x ∈ T.puncturedCore)
    (ha : x ∈ range (T.tube a)) : (T.tubeCoord a x ha).2.1 ≠ 0 := fun h =>
  (T.mem_puncturedCore_iff x).mp hx a ((T.mem_middleSphere_iff a x).mpr ⟨ha, h⟩)

theorem nonneg_tubeCoord_of_mem_tubeTop {a : T.Index} {x : M} (hx : x ∈ T.tubeTop a)
    (ha : x ∈ range (T.tube a)) : 0 ≤ (T.tubeCoord a x ha).2.1 := by
  obtain ⟨z, hz, rfl⟩ := hx
  rw [T.tubeCoord_congr a (T.tube a z) ha (mem_range_self z), T.tubeCoord_tube]
  exact (show (0 : ℝ) ≤ z.2.1 from hz)

theorem nonpos_tubeCoord_of_mem_tubeBot {a : T.Index} {x : M} (hx : x ∈ T.tubeBot a)
    (ha : x ∈ range (T.tube a)) : (T.tubeCoord a x ha).2.1 ≤ 0 := by
  obtain ⟨z, hz, rfl⟩ := hx
  rw [T.tubeCoord_congr a (T.tube a z) ha (mem_range_self z), T.tubeCoord_tube]
  exact (show z.2.1 ≤ 0 from hz)

theorem tubeCoord_eq_of_eq_tube {a : T.Index} {x : M} (ha : x ∈ range (T.tube a))
    {z : TubeDomain} (hz : T.tube a z = x) : T.tubeCoord a x ha = z := by
  subst hz
  rw [T.tubeCoord_congr a (T.tube a z) ha (mem_range_self z), T.tubeCoord_tube]

noncomputable def coreFun (T : TubeSystem M) (p : I × M) : M := by
  classical
  exact if h : ∃ a, p.2 ∈ T.removedBand a then
    T.tube (Classical.choose h)
      (shrinkTube p.1 (T.tubeCoord (Classical.choose h) p.2
        ((T.removedBand_subset_range (Classical.choose h)) (Classical.choose_spec h))))
  else p.2

theorem coreFun_eq_of_mem_removedBand {p : I × M} {a : T.Index}
    (h : p.2 ∈ T.removedBand a) :
    T.coreFun p = T.tube a
      (shrinkTube p.1 (T.tubeCoord a p.2 (T.removedBand_subset_range a h))) := by
  classical
  have hex : ∃ a', p.2 ∈ T.removedBand a' := ⟨a, h⟩
  have hchoose : Classical.choose hex = a :=
    T.eq_index_of_mem_range
      ((T.removedBand_subset_range (Classical.choose hex)) (Classical.choose_spec hex))
      ((T.removedBand_subset_range a) h)
  obtain rfl : a = Classical.choose hex := hchoose.symm
  rw [coreFun, dif_pos hex]

theorem coreFun_eq_self_of_not_mem {p : I × M} (h : ∀ a, p.2 ∉ T.removedBand a) :
    T.coreFun p = p.2 := by
  classical
  unfold coreFun
  rw [dif_neg (by rintro ⟨a, ha⟩; exact h a ha)]

theorem coreFun_eq_self_of_not_mem_iUnion {p : I × M}
    (h : p.2 ∉ ⋃ a, range (T.tube a)) : T.coreFun p = p.2 := by
  refine T.coreFun_eq_self_of_not_mem fun a ha => h (mem_iUnion.mpr ⟨a, T.removedBand_subset_range a ha⟩)

theorem continuous_tubeTime : Continuous fun z : TubeDomain => z.2.1 :=
  continuous_subtype_val.comp continuous_snd

theorem isCompact_tubeTop (a : T.Index) : IsCompact (T.tubeTop a) :=
  (isClosed_le continuous_const continuous_tubeTime).isCompact.image (T.tube a).continuous

theorem isCompact_tubeBot (a : T.Index) : IsCompact (T.tubeBot a) :=
  (isClosed_le continuous_tubeTime continuous_const).isCompact.image (T.tube a).continuous

theorem mem_tubeTop_or_mem_tubeBot {a : T.Index} {x : M} (ha : x ∈ range (T.tube a))
    (ht : (T.tubeCoord a x ha).2.1 ≠ 0) : x ∈ T.tubeTop a ∨ x ∈ T.tubeBot a := by
  rcases lt_or_gt_of_ne ht with h | h
  · exact Or.inr ⟨T.tubeCoord a x ha, le_of_lt h, T.tube_tubeCoord a x ha⟩
  · exact Or.inl ⟨T.tubeCoord a x ha, le_of_lt h, T.tube_tubeCoord a x ha⟩

def expandTubeFun (a : T.Index) (p : I × M) : M := by
  classical
  exact if hx : p.2 ∈ range (T.tube a) then
    T.tube a ((T.tubeCoord a p.2 hx).1, expandCoord p.1 (T.tubeCoord a p.2 hx).2)
  else p.2

theorem expandTubeFun_eq (a : T.Index) (p : I × M) (hx : p.2 ∈ range (T.tube a)) :
    T.expandTubeFun a p = T.tube a
      ((T.tubeCoord a p.2 hx).1, expandCoord p.1 (T.tubeCoord a p.2 hx).2) := by
  rw [expandTubeFun, dif_pos hx]

theorem continuous_expandTubeFun_aux (a : T.Index) :
    Continuous fun u : ↥(univ ×ˢ range (T.tube a)) =>
      T.tube a (((T.embedding a).toHomeomorph.symm ⟨u.1.2, u.2.2⟩).1,
        expandCoord u.1.1 ((T.embedding a).toHomeomorph.symm ⟨u.1.2, u.2.2⟩).2) := by
  have hval : Continuous fun u : ↥(univ ×ˢ range (T.tube a)) => u.1.2 :=
    (continuous_snd : Continuous fun q : I × M => q.2).comp continuous_subtype_val
  have hcoord : Continuous fun u : ↥(univ ×ˢ range (T.tube a)) =>
      (T.embedding a).toHomeomorph.symm ⟨u.1.2, u.2.2⟩ :=
    (T.embedding a).toHomeomorph.symm.continuous.comp (Continuous.subtype_mk hval _)
  refine (T.tube a).continuous.comp (Continuous.prodMk ?_ ?_)
  · exact continuous_fst.comp hcoord
  · have hpair : Continuous fun u : ↥(univ ×ˢ range (T.tube a)) =>
        (u.1.1, ((T.embedding a).toHomeomorph.symm ⟨u.1.2, u.2.2⟩).2) :=
      Continuous.prodMk
        ((continuous_fst : Continuous fun q : I × M => q.1).comp continuous_subtype_val)
        (continuous_snd.comp hcoord)
    exact continuous_expandCoord_joint.comp hpair

theorem continuousOn_expandTubeFun (a : T.Index) :
    ContinuousOn (fun p : I × M => T.expandTubeFun a p) (univ ×ˢ range (T.tube a)) := by
  rw [continuousOn_iff_continuous_domRestrict]
  refine (T.continuous_expandTubeFun_aux a).congr fun u => ?_
  rw [Set.domRestrict_apply, expandTubeFun, dif_pos u.2.2]
  simp only [tubeCoord]

def compressTubeFun (a : T.Index) (p : I × M) : M := by
  classical
  exact if hx : p.2 ∈ range (T.tube a) then
    T.tube a ((T.tubeCoord a p.2 hx).1, compressCoord p.1 (T.tubeCoord a p.2 hx).2)
  else p.2

theorem compressTubeFun_eq (a : T.Index) (p : I × M) (hx : p.2 ∈ range (T.tube a)) :
    T.compressTubeFun a p = T.tube a
      ((T.tubeCoord a p.2 hx).1, compressCoord p.1 (T.tubeCoord a p.2 hx).2) := by
  rw [compressTubeFun, dif_pos hx]

theorem continuous_compressTubeFun_aux (a : T.Index) :
    Continuous fun u : ↥(univ ×ˢ range (T.tube a)) =>
      T.tube a (((T.embedding a).toHomeomorph.symm ⟨u.1.2, u.2.2⟩).1,
        compressCoord u.1.1 ((T.embedding a).toHomeomorph.symm ⟨u.1.2, u.2.2⟩).2) := by
  have hval : Continuous fun u : ↥(univ ×ˢ range (T.tube a)) => u.1.2 :=
    (continuous_snd : Continuous fun q : I × M => q.2).comp continuous_subtype_val
  have hcoord : Continuous fun u : ↥(univ ×ˢ range (T.tube a)) =>
      (T.embedding a).toHomeomorph.symm ⟨u.1.2, u.2.2⟩ :=
    (T.embedding a).toHomeomorph.symm.continuous.comp (Continuous.subtype_mk hval _)
  refine (T.tube a).continuous.comp (Continuous.prodMk ?_ ?_)
  · exact continuous_fst.comp hcoord
  · have hpair : Continuous fun u : ↥(univ ×ˢ range (T.tube a)) =>
        (u.1.1, ((T.embedding a).toHomeomorph.symm ⟨u.1.2, u.2.2⟩).2) :=
      Continuous.prodMk
        ((continuous_fst : Continuous fun q : I × M => q.1).comp continuous_subtype_val)
        (continuous_snd.comp hcoord)
    exact continuous_compressCoord_joint.comp hpair

theorem continuousOn_compressTubeFun (a : T.Index) :
    ContinuousOn (fun p : I × M => T.compressTubeFun a p) (univ ×ˢ range (T.tube a)) := by
  rw [continuousOn_iff_continuous_domRestrict]
  refine (T.continuous_compressTubeFun_aux a).congr fun u => ?_
  rw [Set.domRestrict_apply, compressTubeFun, dif_pos u.2.2]
  simp only [tubeCoord]

end Basic

section Closed

variable {M : Type*} [TopologicalSpace M] [T2Space M] (T : TubeSystem M)

theorem closure_tube_image (a : T.Index) (S : Set TubeDomain) :
    closure (T.tube a '' S) = T.tube a '' closure S := by
  refine Subset.antisymm ?_ (image_closure_subset_closure_image (T.tube a).continuous)
  exact closure_minimal (image_mono subset_closure)
    ((isClosed_closure).isCompact.image (T.tube a).continuous).isClosed

theorem closure_positiveTube (a : T.Index) : closure (T.positiveTube a) = T.tubeTop a := by
  rw [positiveTube, tubeTop, T.closure_tube_image, closure_tubeTime_pos]

theorem closure_negativeTube (a : T.Index) : closure (T.negativeTube a) = T.tubeBot a := by
  rw [negativeTube, tubeBot, T.closure_tube_image, closure_tubeTime_neg]

theorem isClosed_iUnion_range : IsClosed (⋃ a, range (T.tube a)) := by
  have hfin : (univ : Set T.Index).Finite := Set.toFinite _
  have := hfin.isClosed_biUnion fun a _ => (isCompact_range (T.tube a).continuous).isClosed
  simpa using this

omit [T2Space M] in
theorem isCompact_middleSphere (a : T.Index) : IsCompact (T.middleSphere a) :=
  (isClosed_eq continuous_tubeTime continuous_const).isCompact.image (T.tube a).continuous

theorem isClosed_iUnion_middleSphere : IsClosed (⋃ a, T.middleSphere a) := by
  have hfin : (univ : Set T.Index).Finite := Set.toFinite _
  have := hfin.isClosed_biUnion fun a _ => (T.isCompact_middleSphere a).isClosed
  simpa using this

theorem isOpen_puncturedCore : IsOpen T.puncturedCore :=
  T.isClosed_iUnion_middleSphere.isOpen_compl

theorem frontier_iUnion_range_subset :
    frontier (⋃ a, range (T.tube a)) ⊆ ⋃ a, frontier (range (T.tube a)) := by
  intro x hx
  obtain ⟨a, ha⟩ := mem_iUnion.mp (T.isClosed_iUnion_range.closure_subset hx.1)
  refine mem_iUnion.mpr ⟨a, ⟨subset_closure ha, fun hint => hx.2 ?_⟩⟩
  exact interior_mono (subset_iUnion (fun a => range (T.tube a)) a) hint

theorem mem_interior_iUnion_range_of_mem_range {x : M} (hx : x ∈ ⋃ a, range (T.tube a))
    (hfr : x ∉ ⋃ a, frontier (range (T.tube a))) :
    x ∈ interior (⋃ a, range (T.tube a)) := by
  by_contra hxint
  exact hfr (T.frontier_iUnion_range_subset
    ((mem_frontier_iff_notMem_interior hx).mpr hxint))

end Closed

section Manifold

variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] (T : TubeSystem M)

local instance : Fact ((-2 : ℝ) < 2) := ⟨by norm_num⟩

theorem frontier_range_tube_subset {a : T.Index}
    (hsm : IsSmoothEmbedding ((𝓡 2).prod (𝓡∂ 1)) ThreeModel ∞ (T.tube a)) :
    frontier (range (T.tube a)) ⊆ T.tube a '' {z : TubeDomain | z.2.1 = 2 ∨ z.2.1 = -2} := by
  intro y hy
  obtain ⟨z, rfl⟩ := (isCompact_range (T.tube a).continuous).isClosed.closure_subset hy.1
  have hzint : z ∉ ((𝓡 2).prod (𝓡∂ 1)).interior TubeDomain := by
    intro hzi
    have hopen : IsOpen (T.tube a '' ((𝓡 2).prod (𝓡∂ 1)).interior TubeDomain) :=
      DifferentialGeometry.Topology.Manifold.isOpen_image_interior_of_isImmersion
        hsm.isImmersion (by simp [ThreeSpace, Module.finrank_prod])
    have hzmem : T.tube a z ∈ T.tube a '' ((𝓡 2).prod (𝓡∂ 1)).interior TubeDomain :=
      Set.mem_image_of_mem _ hzi
    exact hy.2 (interior_maximal (image_subset_range _ _) hopen hzmem)
  by_cases h : z.2.1 = 2 ∨ z.2.1 = -2
  · exact ⟨z, h, rfl⟩
  · exfalso
    apply hzint
    rw [ModelWithCorners.interior_prod]
    exact ⟨BoundarylessManifold.isInteriorPoint,
      Icc_isInteriorPoint_interior
        ⟨lt_of_le_of_ne z.2.2.1 (fun hc => h (Or.inr hc.symm)),
          lt_of_le_of_ne z.2.2.2 (fun hc => h (Or.inl hc))⟩⟩

omit [T2Space M] [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M] in
theorem coreFun_eq_expandTubeFun {a : T.Index} {p : I × M} (hp : p.2 ∈ T.puncturedCore)
    (ht : p.2 ∈ T.tubeTop a) : T.coreFun p = T.expandTubeFun a p := by
  classical
  have ha : p.2 ∈ range (T.tube a) := T.tubeTop_subset_range a ht
  have h0 : 0 ≤ (T.tubeCoord a p.2 ha).2.1 := T.nonneg_tubeCoord_of_mem_tubeTop ht ha
  have hne : (T.tubeCoord a p.2 ha).2.1 ≠ 0 := T.tubeCoord_snd_ne_zero hp ha
  have hpos : 0 < (T.tubeCoord a p.2 ha).2.1 := lt_of_le_of_ne h0 (Ne.symm hne)
  rcases lt_or_ge (T.tubeCoord a p.2 ha).2.1 1 with hlt | hge
  · have hmem : p.2 ∈ T.removedBand a :=
      ⟨T.tubeCoord a p.2 ha, ⟨by linarith, hlt⟩, T.tube_tubeCoord a p.2 ha⟩
    rw [T.coreFun_eq_of_mem_removedBand hmem, T.expandTubeFun_eq a p ha,
      T.tubeCoord_congr a p.2 (T.removedBand_subset_range a hmem) ha,
      shrinkTube_eq_expandCoord_of_pos p.1 hpos]
  · have h1 : 1 ≤ (T.tubeCoord a p.2 ha).2.1 := hge
    have hnotmem : ∀ a', p.2 ∉ T.removedBand a' := by
      intro a' ha'
      have heq : a' = a :=
        T.eq_index_of_mem_range (T.removedBand_subset_range a' ha') ha
      obtain ⟨z, hz, hzx⟩ := heq ▸ ha'
      have hzt : 1 ≤ z.2.1 := by
        rw [← T.tubeCoord_eq_of_eq_tube (T.removedBand_subset_range a (heq ▸ ha')) hzx,
          T.tubeCoord_congr a p.2 (T.removedBand_subset_range a (heq ▸ ha')) ha]
        exact h1
      exact absurd hz.2 (not_lt.2 hzt)
    rw [T.coreFun_eq_self_of_not_mem hnotmem, T.expandTubeFun_eq a p ha,
      expandCoord_eq_self_of_one_le p.1 h1]
    exact (T.tube_tubeCoord a p.2 ha).symm

omit [T2Space M] [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M] in
theorem coreFun_eq_compressTubeFun {a : T.Index} {p : I × M} (hp : p.2 ∈ T.puncturedCore)
    (ht : p.2 ∈ T.tubeBot a) : T.coreFun p = T.compressTubeFun a p := by
  classical
  have ha : p.2 ∈ range (T.tube a) := T.tubeBot_subset_range a ht
  have h0 : (T.tubeCoord a p.2 ha).2.1 ≤ 0 := T.nonpos_tubeCoord_of_mem_tubeBot ht ha
  have hne : (T.tubeCoord a p.2 ha).2.1 ≠ 0 := T.tubeCoord_snd_ne_zero hp ha
  have hneg : (T.tubeCoord a p.2 ha).2.1 < 0 := lt_of_le_of_ne h0 hne
  rcases lt_or_ge (-1 : ℝ) (T.tubeCoord a p.2 ha).2.1 with hlt | hge
  · have hmem : p.2 ∈ T.removedBand a :=
      ⟨T.tubeCoord a p.2 ha, ⟨hlt, by linarith⟩, T.tube_tubeCoord a p.2 ha⟩
    rw [T.coreFun_eq_of_mem_removedBand hmem, T.compressTubeFun_eq a p ha,
      T.tubeCoord_congr a p.2 (T.removedBand_subset_range a hmem) ha,
      shrinkTube_eq_compressCoord_of_neg p.1 hneg]
  · have h1 : (T.tubeCoord a p.2 ha).2.1 ≤ -1 := hge
    have hnotmem : ∀ a', p.2 ∉ T.removedBand a' := by
      intro a' ha'
      have heq : a' = a :=
        T.eq_index_of_mem_range (T.removedBand_subset_range a' ha') ha
      obtain ⟨z, hz, hzx⟩ := heq ▸ ha'
      have hzt : z.2.1 ≤ -1 := by
        rw [← T.tubeCoord_eq_of_eq_tube (T.removedBand_subset_range a (heq ▸ ha')) hzx,
          T.tubeCoord_congr a p.2 (T.removedBand_subset_range a (heq ▸ ha')) ha]
        exact h1
      exact absurd hz.1 (not_lt.2 hzt)
    rw [T.coreFun_eq_self_of_not_mem hnotmem, T.compressTubeFun_eq a p ha,
      compressCoord_eq_self_of_le_neg_one p.1 h1]
    exact (T.tube_tubeCoord a p.2 ha).symm

theorem coreFun_eq_self_of_mem_closure_compl
    (hsm : ∀ a : T.Index, IsSmoothEmbedding ((𝓡 2).prod (𝓡∂ 1)) ThreeModel ∞ (T.tube a))
    {p : I × M} (hp : p.2 ∈ closure {x : M | x ∉ ⋃ a, range (T.tube a)}) :
    T.coreFun p = p.2 := by
  classical
  by_cases hx : p.2 ∈ ⋃ a, range (T.tube a)
  · have hne_int : p.2 ∉ interior (⋃ a, range (T.tube a)) := by
      intro hint
      obtain ⟨y, hy, hyc⟩ := mem_closure_iff.1 hp _ isOpen_interior hint
      exact hyc (interior_subset hy)
    have hfr : p.2 ∈ ⋃ a, frontier (range (T.tube a)) := by
      by_contra hfr
      exact hne_int (T.mem_interior_iUnion_range_of_mem_range hx hfr)
    obtain ⟨a, ha⟩ := mem_iUnion.mp hfr
    obtain ⟨z, hz, hzx⟩ := T.frontier_range_tube_subset (hsm a) ha
    have hxa : p.2 ∈ range (T.tube a) :=
      (isCompact_range (T.tube a).continuous).isClosed.closure_subset ha.1
    have hnotmem : ∀ a', p.2 ∉ T.removedBand a' := by
      intro a' ha'
      by_cases heq : a' = a
      · obtain ⟨z', hz', hz'x⟩ := heq ▸ ha'
        have hz'z : z' = z := (T.embedding a).injective (hz'x.trans hzx.symm)
        have h1' : (-1 : ℝ) < z'.2.1 := (show -1 < z'.2.1 from hz'.1)
        have h2' : z'.2.1 < 1 := (show z'.2.1 < 1 from hz'.2)
        rw [hz'z] at h1' h2'
        rcases hz with h2 | h2 <;> rw [h2] at h1' h2' <;> linarith
      · exact Set.disjoint_left.mp (T.disjoint heq) (T.removedBand_subset_range a' ha') hxa
    exact T.coreFun_eq_self_of_not_mem hnotmem
  · exact T.coreFun_eq_self_of_not_mem_iUnion hx

omit [T2Space M] [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M] in
theorem mem_closure_compl_of_mem_closure_range_compl {u : ↥T.puncturedCore}
    (hu : u ∈ closure {v : ↥T.puncturedCore | (v : M) ∉ ⋃ a, range (T.tube a)}) :
    (u : M) ∈ closure {x : M | x ∉ ⋃ a, range (T.tube a)} := by
  rw [mem_closure_iff]
  intro O hO huO
  by_contra hcon
  have hsub : O ⊆ ⋃ a, range (T.tube a) := fun y hy =>
    not_not.mp fun hyc => hcon ⟨y, hy, hyc⟩
  obtain ⟨v, hvO, hvA⟩ := mem_closure_iff.1 hu
    (Subtype.val ⁻¹' O : Set ↥T.puncturedCore)
    (hO.preimage continuous_subtype_val) huO
  exact hcon ⟨(v : M), hvO, hvA⟩

theorem continuousOn_coreFun_closure_compl
    (hsm : ∀ a : T.Index, IsSmoothEmbedding ((𝓡 2).prod (𝓡∂ 1)) ThreeModel ∞ (T.tube a)) :
    ContinuousOn (fun p : I × ↥T.puncturedCore => T.coreFun (p.1, (p.2 : M)))
      (univ ×ˢ closure {u : ↥T.puncturedCore | (u : M) ∉ ⋃ a, range (T.tube a)}) := by
  refine ((continuous_subtype_val.comp continuous_snd).continuousOn).congr ?_
  rintro ⟨s, u⟩ ⟨-, hu⟩
  exact T.coreFun_eq_self_of_mem_closure_compl hsm
    (T.mem_closure_compl_of_mem_closure_range_compl hu)

omit [T2Space M] [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M] in
theorem continuousOn_coreFun_tubeTop (a : T.Index) :
    ContinuousOn (fun p : I × ↥T.puncturedCore => T.coreFun (p.1, (p.2 : M)))
      (univ ×ˢ {u : ↥T.puncturedCore | (u : M) ∈ T.tubeTop a}) := by
  have hφ : Continuous fun p : I × ↥T.puncturedCore => (p.1, (p.2 : M)) :=
    Continuous.prodMk continuous_fst (continuous_subtype_val.comp continuous_snd)
  have hmap : MapsTo (fun p : I × ↥T.puncturedCore => (p.1, (p.2 : M)))
      (univ ×ˢ {u : ↥T.puncturedCore | (u : M) ∈ T.tubeTop a}) (univ ×ˢ range (T.tube a)) :=
    fun _ hp => ⟨trivial, T.tubeTop_subset_range a hp.2⟩
  refine ((T.continuousOn_expandTubeFun a).comp hφ.continuousOn hmap).congr ?_
  rintro ⟨s, u⟩ ⟨-, hu⟩
  exact T.coreFun_eq_expandTubeFun u.2 hu

omit [T2Space M] [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M] in
theorem continuousOn_coreFun_tubeBot (a : T.Index) :
    ContinuousOn (fun p : I × ↥T.puncturedCore => T.coreFun (p.1, (p.2 : M)))
      (univ ×ˢ {u : ↥T.puncturedCore | (u : M) ∈ T.tubeBot a}) := by
  have hφ : Continuous fun p : I × ↥T.puncturedCore => (p.1, (p.2 : M)) :=
    Continuous.prodMk continuous_fst (continuous_subtype_val.comp continuous_snd)
  have hmap : MapsTo (fun p : I × ↥T.puncturedCore => (p.1, (p.2 : M)))
      (univ ×ˢ {u : ↥T.puncturedCore | (u : M) ∈ T.tubeBot a}) (univ ×ˢ range (T.tube a)) :=
    fun _ hp => ⟨trivial, T.tubeBot_subset_range a hp.2⟩
  refine ((T.continuousOn_compressTubeFun a).comp hφ.continuousOn hmap).congr ?_
  rintro ⟨s, u⟩ ⟨-, hu⟩
  exact T.coreFun_eq_compressTubeFun u.2 hu

omit [T2Space M] [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M] in
theorem iUnion_pieces_eq_univ :
    (⋃ a ∈ (Finset.univ : Finset T.Index),
        ((univ : Set I) ×ˢ (Subtype.val ⁻¹' T.tubeTop a : Set ↥T.puncturedCore) ∪
          (univ : Set I) ×ˢ (Subtype.val ⁻¹' T.tubeBot a : Set ↥T.puncturedCore))) ∪
      ((univ : Set I) ×ˢ
        closure {u : ↥T.puncturedCore | (u : M) ∉ ⋃ a, range (T.tube a)}) = univ := by
  refine eq_univ_of_forall fun p => ?_
  by_cases hx : (p.2 : M) ∈ ⋃ a, range (T.tube a)
  · obtain ⟨a, ha⟩ := mem_iUnion.mp hx
    rcases T.mem_tubeTop_or_mem_tubeBot ha (T.tubeCoord_snd_ne_zero p.2.2 ha) with h | h
    · exact Or.inl (mem_iUnion₂.mpr ⟨a, Finset.mem_univ a, Or.inl ⟨trivial, h⟩⟩)
    · exact Or.inl (mem_iUnion₂.mpr ⟨a, Finset.mem_univ a, Or.inr ⟨trivial, h⟩⟩)
  · refine Or.inr ⟨trivial, subset_closure ?_⟩
    exact hx

private theorem continuousOn_biUnion_isClosed_finset {ι X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (s : Finset ι) {t : ι → Set X} {f : X → Y}
    (ht : ∀ i ∈ s, IsClosed (t i)) (hf : ∀ i ∈ s, ContinuousOn f (t i)) :
    ContinuousOn f (⋃ i ∈ s, t i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      have hdecomp : (⋃ i ∈ insert a s, t i) = t a ∪ ⋃ i ∈ s, t i := by
        ext x
        simp only [mem_union, mem_iUnion, Finset.mem_insert]
        constructor
        · rintro ⟨i, rfl | hi, hx⟩
          · exact Or.inl hx
          · exact Or.inr ⟨i, hi, hx⟩
        · rintro (hx | ⟨i, hi, hx⟩)
          · exact ⟨a, Or.inl rfl, hx⟩
          · exact ⟨i, Or.inr hi, hx⟩
      rw [hdecomp]
      refine ContinuousOn.union_of_isClosed (hf a (Finset.mem_insert_self a s))
        (ih (fun i hi => ht i (Finset.mem_insert_of_mem hi))
          (fun i hi => hf i (Finset.mem_insert_of_mem hi)))
        (ht a (Finset.mem_insert_self a s)) ?_
      exact (s.finite_toSet).isClosed_biUnion fun i hi => ht i (Finset.mem_insert_of_mem hi)

theorem continuous_coreFun
    (hsm : ∀ a : T.Index, IsSmoothEmbedding ((𝓡 2).prod (𝓡∂ 1)) ThreeModel ∞ (T.tube a)) :
    Continuous fun p : I × ↥T.puncturedCore => T.coreFun (p.1, (p.2 : M)) := by
  classical
  have hclosed : ∀ a : T.Index, IsClosed
      ((univ : Set I) ×ˢ (Subtype.val ⁻¹' T.tubeTop a : Set ↥T.puncturedCore) ∪
        (univ : Set I) ×ˢ (Subtype.val ⁻¹' T.tubeBot a : Set ↥T.puncturedCore)) := by
    intro a
    exact ((isClosed_univ : IsClosed (univ : Set I)).prod
      (IsClosed.preimage continuous_subtype_val (T.isCompact_tubeTop a).isClosed)).union
      ((isClosed_univ : IsClosed (univ : Set I)).prod
        (IsClosed.preimage continuous_subtype_val (T.isCompact_tubeBot a).isClosed))
  have hcont : ∀ a : T.Index, ContinuousOn
      (fun p : I × ↥T.puncturedCore => T.coreFun (p.1, (p.2 : M)))
      ((univ : Set I) ×ˢ {u : ↥T.puncturedCore | (u : M) ∈ T.tubeTop a} ∪
        (univ : Set I) ×ˢ {u : ↥T.puncturedCore | (u : M) ∈ T.tubeBot a}) := by
    intro a
    exact (T.continuousOn_coreFun_tubeTop a).union_of_isClosed
      (T.continuousOn_coreFun_tubeBot a)
      ((isClosed_univ : IsClosed (univ : Set I)).prod
        (IsClosed.preimage continuous_subtype_val (T.isCompact_tubeTop a).isClosed))
      ((isClosed_univ : IsClosed (univ : Set I)).prod
        (IsClosed.preimage continuous_subtype_val (T.isCompact_tubeBot a).isClosed))
  have hpieces : ContinuousOn (fun p : I × ↥T.puncturedCore => T.coreFun (p.1, (p.2 : M)))
      (⋃ a ∈ (Finset.univ : Finset T.Index),
        ((univ : Set I) ×ˢ (Subtype.val ⁻¹' T.tubeTop a : Set ↥T.puncturedCore) ∪
          (univ : Set I) ×ˢ (Subtype.val ⁻¹' T.tubeBot a : Set ↥T.puncturedCore))) := by
    have h := continuousOn_biUnion_isClosed_finset (X := I × ↥T.puncturedCore)
      (t := fun a : T.Index =>
        (univ : Set I) ×ˢ {u : ↥T.puncturedCore | (u : M) ∈ T.tubeTop a} ∪
          (univ : Set I) ×ˢ {u : ↥T.puncturedCore | (u : M) ∈ T.tubeBot a})
      (f := fun p : I × ↥T.puncturedCore => T.coreFun (p.1, (p.2 : M)))
      (Finset.univ : Finset T.Index) (fun a _ => hclosed a) (fun a _ => hcont a)
    exact h
  have hpieces_closed : IsClosed (⋃ a ∈ (Finset.univ : Finset T.Index),
      ((univ : Set I) ×ˢ (Subtype.val ⁻¹' T.tubeTop a : Set ↥T.puncturedCore) ∪
        (univ : Set I) ×ˢ (Subtype.val ⁻¹' T.tubeBot a : Set ↥T.puncturedCore))) := by
    simpa using (Set.toFinite (univ : Set T.Index)).isClosed_biUnion fun a _ => hclosed a
  rw [← continuousOn_univ, ← T.iUnion_pieces_eq_univ]
  exact hpieces.union_of_isClosed (T.continuousOn_coreFun_closure_compl hsm) hpieces_closed
    ((isClosed_univ : IsClosed (univ : Set I)).prod isClosed_closure)

end Manifold

section Assembly

variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] (T : TubeSystem M)

local instance : Fact ((-2 : ℝ) < 2) := ⟨by norm_num⟩

omit [T2Space M] [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M] in
theorem core_subset_puncturedCore : T.core ⊆ T.puncturedCore := by
  intro x hx
  rw [T.mem_puncturedCore_iff]
  intro a ha
  obtain ⟨z, hz, hzx⟩ := ha
  have hz0 : z.2.1 = 0 := (show z.2.1 = 0 from hz)
  exact hx (mem_iUnion.mpr ⟨a, z, ⟨by linarith [hz0], by linarith [hz0]⟩, hzx⟩)

omit [T2Space M] [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M] in
theorem coreFun_mem_puncturedCore {p : I × M} (hp : p.2 ∈ T.puncturedCore) :
    T.coreFun p ∈ T.puncturedCore := by
  classical
  by_cases h : ∃ a, p.2 ∈ T.removedBand a
  · obtain ⟨a, ha⟩ := h
    set z := T.tubeCoord a p.2 (T.removedBand_subset_range a ha) with hzdef
    have hz0 : z.2.1 ≠ 0 := by
      rw [hzdef]
      exact T.tubeCoord_snd_ne_zero hp (T.removedBand_subset_range a ha)
    rw [T.coreFun_eq_of_mem_removedBand ha, ← hzdef]
    intro hmem
    obtain ⟨b, hb⟩ := mem_iUnion.mp hmem
    have hb_range : T.tube a (shrinkTube p.1 z) ∈ range (T.tube b) :=
      T.middleSphere_subset_range b hb
    obtain ⟨z', hz', hz'x⟩ := hb
    have hba : b = a := T.eq_index_of_mem_range hb_range
      (Set.mem_range_self (shrinkTube p.1 z))
    rw [hba] at hz'x
    have hz'eq : z' = shrinkTube p.1 z := (T.embedding a).injective hz'x
    have hz'1 : (shrinkTube p.1 z).2.1 = 0 := by
      rw [hz'eq] at hz'
      exact (show (shrinkTube p.1 z).2.1 = 0 from hz')
    rw [shrinkTube_snd_val] at hz'1
    exact shrinkTime_ne_zero hz0 hz'1
  · rw [T.coreFun_eq_self_of_not_mem fun a ha => h ⟨a, ha⟩]
    exact hp

omit [T2Space M] [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M] in
theorem coreFun_mem_core {p : I × M} (hp : p.2 ∈ T.puncturedCore) :
    T.coreFun ((1 : I), p.2) ∈ T.core := by
  classical
  by_cases h : ∃ a, p.2 ∈ T.removedBand a
  · obtain ⟨a, ha⟩ := h
    set z := T.tubeCoord a p.2 (T.removedBand_subset_range a ha) with hzdef
    have hz0 : z.2.1 ≠ 0 := by
      rw [hzdef]
      exact T.tubeCoord_snd_ne_zero hp (T.removedBand_subset_range a ha)
    rw [T.coreFun_eq_of_mem_removedBand (p := ((1 : I), p.2)) ha, ← hzdef]
    intro hcore
    obtain ⟨b, hb⟩ := mem_iUnion.mp hcore
    have hb_range : T.tube a (shrinkTube (1 : I) z) ∈ range (T.tube b) :=
      T.removedBand_subset_range b hb
    obtain ⟨z', hz', hz'x⟩ := hb
    have hba : b = a := T.eq_index_of_mem_range hb_range
      (Set.mem_range_self (shrinkTube (1 : I) z))
    rw [hba] at hz'x
    have hz'eq : z' = shrinkTube (1 : I) z := (T.embedding a).injective hz'x
    have hz'1 : (-1 : ℝ) < (shrinkTube (1 : I) z).2.1 := by
      rw [hz'eq] at hz'
      exact (show (-1 : ℝ) < (shrinkTube (1 : I) z).2.1 from hz'.1)
    have hz'2 : (shrinkTube (1 : I) z).2.1 < 1 := by
      rw [hz'eq] at hz'
      exact (show (shrinkTube (1 : I) z).2.1 < 1 from hz'.2)
    rw [shrinkTube_snd_val] at hz'1 hz'2
    rcases lt_or_gt_of_ne hz0 with hneg | hpos
    · exact absurd hz'1 (not_lt.2 (shrinkTime_one_le_neg_one hneg))
    · exact absurd hz'2 (not_lt.2 (one_le_shrinkTime_one hpos))
  · rw [T.coreFun_eq_self_of_not_mem (p := ((1 : I), p.2)) fun a ha => h ⟨a, ha⟩]
    intro hcore
    obtain ⟨a, ha⟩ := mem_iUnion.mp hcore
    exact h ⟨a, ha⟩

omit [T2Space M] [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M] in
theorem coreFun_eq_self_of_mem_core {x : M} (hx : x ∈ T.core) (s : I) :
    T.coreFun (s, x) = x :=
  T.coreFun_eq_self_of_not_mem fun a ha => hx (mem_iUnion.mpr ⟨a, ha⟩)

omit [T2Space M] [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M] in
theorem coreFun_zero (p : I × M) : T.coreFun ((0 : I), p.2) = p.2 := by
  classical
  by_cases h : ∃ a, p.2 ∈ T.removedBand a
  · obtain ⟨a, ha⟩ := h
    rw [T.coreFun_eq_of_mem_removedBand (p := ((0 : I), p.2)) ha, shrinkTube_zero]
    exact T.tube_tubeCoord a p.2 (T.removedBand_subset_range a ha)
  · exact T.coreFun_eq_self_of_not_mem (p := ((0 : I), p.2)) fun a ha => h ⟨a, ha⟩

end Assembly

end TubeSystem

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
