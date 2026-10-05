import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyRimRounding
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GRimCornerScale
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# FC39 GROUP G, RIMBOX G7: the common rounding relative to normalized corners (kernel)

Lane FC39-RIMBOX-ROUND, disposition D62-4 (external review 62 §5.2–5.3; suggested name
`exists_rounding_relative_normalizedCorners`). On a σ-compact Hausdorff surface `B` with finitely many
defining functions `f l` (smooth, regular at their zeros, compact cornered region
`C = {∀ l, f l ≤ 0}`, two simultaneous zeros only at corner centres) and normalized corner charts `κ k`
on `(-2, 2)²` which are the restrictions of LARGER charts `K k` on `(-3, 3)²` (pairwise disjoint
targets; the two active functions read `-(λ x)`, `-(λ y)`, the others are negative), there is ONE
smooth function `r` with the five rounding fields of `CircleRegion`:

* `r ∘ κ k = -(λ_k ψ_std)` on the WHOLE box `(-2, 2)²` (`rounding_chart`);
* `{r ≤ 0}` agrees with `C` off the unit-box images (`rounding_agree`) and the symmetric difference
  lies in the unit-box images;
* `0` is a regular value of `r`; `{r ≤ 0} ⊆ C` is compact.

Construction (review 62 §5.2): `r = Σ_α ρ_α g_α` for a smooth partition of unity `ρ` subordinate to
the targets `K k (rimBox 3)` (local function `g = -λ ψ_std ∘ K⁻¹`), the face sets
`{f l' < 0 for l' ≠ l} \ ⋃ K (closed box 2)` (`g = f l`), the inside `{∀ l, f l < 0}` (`g = -1`) and the
outside `{∃ l, f l > 0}` (`g = 1`), the last three off the closed boxes. The weight of corner `k` is `1`
on `K k [-2, 2]²` (all other supports avoid it), which gives `rounding_chart` exactly. Off the unit
boxes every local function has the sign of the cornered region (`ψ_std` outside the unit box is the
quadrant test), so the convex combination has it too; at a common zero off the boxes `(-2, 2)²` the
only active local functions coincide with the one vanishing face function near the point
(`ψ_std = x` near `(0, y)`, `y ≥ 2`), so `r` equals it near the point; inside a box the chart formula
and `dψ_std ≠ 0` give regularity.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry.Topology.Manifold.CornerRounding
open Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0

/-! ## The standard rim rounding off the unit box -/

/-- The closed square `[-r, r]²`. -/
def closedRimBox_GRND (r : ℝ) : Set (ℝ × ℝ) :=
  {v | |v.1| ≤ r ∧ |v.2| ≤ r}

theorem isCompact_closedRimBox_GRND (r : ℝ) : IsCompact (closedRimBox_GRND r) := by
  have h : closedRimBox_GRND r = Icc (-r) r ×ˢ Icc (-r) r := by
    ext v
    simp only [closedRimBox_GRND, mem_ofPred_eq, mem_prod, mem_Icc, abs_le]
  rw [h]
  exact isCompact_Icc.prod isCompact_Icc

theorem rimBox_subset_closedRimBox_GRND (r : ℝ) : rimBox r ⊆ closedRimBox_GRND r :=
  fun _ hv => ⟨hv.1.le, hv.2.le⟩

theorem closedRimBox_subset_rimBox_GRND {r s : ℝ} (h : r < s) : closedRimBox_GRND r ⊆ rimBox s :=
  fun _ hv => ⟨hv.1.trans_lt h, hv.2.trans_lt h⟩

theorem zero_mem_rimBox_GRND {r : ℝ} (hr : 0 < r) : ((0 : ℝ), (0 : ℝ)) ∈ rimBox r :=
  ⟨by simpa using hr, by simpa using hr⟩

/-- Outside the open unit box, `ψ_std > 0` is the open quadrant. -/
theorem standardRimRounding_pos_iff_GRND {v : ℝ × ℝ} (hv : v ∉ rimBox 1) :
    0 < standardRimRounding v ↔ (0 < v.1 ∧ 0 < v.2) := by
  constructor
  · intro h
    have hm := h.trans_le (standardRimRounding_le_min v)
    exact ⟨hm.trans_le (min_le_left _ _), hm.trans_le (min_le_right _ _)⟩
  · rintro ⟨h1, h2⟩
    by_contra hle
    rcases (standardRimRounding_nonpos_iff hv).1 (not_lt.1 hle) with h | h
    · exact absurd h (not_le.2 h2)
    · exact absurd h (not_le.2 h1)

/-- `ψ_std = x` where `y ≥ x + 1/4`. -/
theorem standardRimRounding_eq_fst_GRND {w : ℝ × ℝ} (h : w.1 + 1 / 4 ≤ w.2) :
    standardRimRounding w = w.1 := by
  have hab : rimRoundingWidth ≤ |w.1 - w.2| := by
    rw [abs_sub_comm, abs_of_nonneg (by linarith), rimRoundingWidth]
    linarith
  rw [standardRimRounding, roundedMin_eq_min rimRoundingWidth_pos hab, min_eq_left (by linarith)]

/-- `ψ_std = y` where `x ≥ y + 1/4`. -/
theorem standardRimRounding_eq_snd_GRND {w : ℝ × ℝ} (h : w.2 + 1 / 4 ≤ w.1) :
    standardRimRounding w = w.2 := by
  have hab : rimRoundingWidth ≤ |w.1 - w.2| := by
    rw [abs_of_nonneg (by linarith), rimRoundingWidth]
    linarith
  rw [standardRimRounding, roundedMin_eq_min rimRoundingWidth_pos hab, min_eq_right (by linarith)]

/-! ## The cover and the local functions -/

section Kernel

variable {B : Type*} [TopologicalSpace B] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) B]

/-- The open cover of the rounding construction: the larger corner targets, the face sets, the
outside and the inside (the last three off the closed boxes `K k [-2, 2]²`). -/
def roundCover_GRND {m c : ℕ} (f : Fin m → B → ℝ)
    (K : Fin c → PartialDiffeomorph 𝓘(ℝ, ℝ × ℝ) (𝓡 2) (ℝ × ℝ) B ∞) :
    Fin c ⊕ (Fin m ⊕ Bool) → Set B
  | .inl k => (K k).target
  | .inr (.inl l) => {b | ∀ l', l' ≠ l → f l' b < 0} \ ⋃ k, K k '' closedRimBox_GRND 2
  | .inr (.inr true) => {b | ∃ l, 0 < f l b} \ ⋃ k, K k '' closedRimBox_GRND 2
  | .inr (.inr false) => {b | ∀ l, f l b < 0} \ ⋃ k, K k '' closedRimBox_GRND 2

/-- The local functions of the rounding construction. -/
def roundLocal_GRND {m c : ℕ} (f : Fin m → B → ℝ)
    (K : Fin c → PartialDiffeomorph 𝓘(ℝ, ℝ × ℝ) (𝓡 2) (ℝ × ℝ) B ∞) (lam : Fin c → ℝ) :
    Fin c ⊕ (Fin m ⊕ Bool) → B → ℝ
  | .inl k => fun b => -(lam k * standardRimRounding ((K k).symm b))
  | .inr (.inl l) => f l
  | .inr (.inr true) => fun _ => 1
  | .inr (.inr false) => fun _ => -1

omit [TopologicalSpace B] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) B] in
/-- The sign of a corner local function off the unit box is the sign of the cornered region. -/
theorem corner_sign_GRND {m : ℕ} (f : Fin m → B → ℝ) {p : B} {first second : Fin m} {lam : ℝ}
    (hlam : 0 < lam) {v : ℝ × ℝ} (hv : v ∉ rimBox 1) (hfirst : f first p = -(lam * v.1))
    (hsecond : f second p = -(lam * v.2))
    (hother : ∀ l, l ≠ first → l ≠ second → f l p < 0) :
    (-(lam * standardRimRounding v) ≤ 0 ↔ ∀ l, f l p ≤ 0) ∧
      (-(lam * standardRimRounding v) < 0 ↔ ∀ l, f l p < 0) := by
  constructor
  · rw [neg_nonpos, mul_nonneg_iff_of_pos_left hlam, standardRimRounding_nonneg_iff hv]
    constructor
    · rintro ⟨h1, h2⟩ l
      by_cases hl1 : l = first
      · rw [hl1, hfirst, neg_nonpos]
        exact mul_nonneg hlam.le h1
      by_cases hl2 : l = second
      · rw [hl2, hsecond, neg_nonpos]
        exact mul_nonneg hlam.le h2
      exact (hother l hl1 hl2).le
    · intro h
      have h1 := h first
      have h2 := h second
      rw [hfirst, neg_nonpos] at h1
      rw [hsecond, neg_nonpos] at h2
      exact ⟨nonneg_of_mul_nonneg_right (by linarith) hlam,
        nonneg_of_mul_nonneg_right (by linarith) hlam⟩
  · rw [neg_lt_zero, mul_pos_iff_of_pos_left hlam, standardRimRounding_pos_iff_GRND hv]
    constructor
    · rintro ⟨h1, h2⟩ l
      by_cases hl1 : l = first
      · rw [hl1, hfirst, neg_lt_zero]
        exact mul_pos hlam h1
      by_cases hl2 : l = second
      · rw [hl2, hsecond, neg_lt_zero]
        exact mul_pos hlam h2
      exact hother l hl1 hl2
    · intro h
      have h1 := h first
      have h2 := h second
      rw [hfirst, neg_lt_zero] at h1
      rw [hsecond, neg_lt_zero] at h2
      exact ⟨pos_of_mul_pos_right h1 hlam.le, pos_of_mul_pos_right h2 hlam.le⟩

end Kernel

/-! ## The kernel -/

section Main

variable {B : Type*} [TopologicalSpace B] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) B]
  [IsManifold (𝓡 2) ∞ B] [T2Space B] [SigmaCompactSpace B]

/-- **G7 kernel (D62-4): relative rounding with normalized corners.** See the module docstring. The
corner charts `κ k` of the circle region are the restrictions of the larger charts `K k`; the output
is the five rounding fields of `CircleRegion` (`rounding_smooth`, `rounding_regular`,
`rounding_chart`, `rounding_agree`, `rounded_compact`) for `κ`, and the symmetric difference of
`{r ≤ 0}` and `C` inside the unit-box images. -/
theorem exists_rounding_relative_normalizedCorners_GRND
    {m c : ℕ} (f : Fin m → B → ℝ) (hf : ∀ l, ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (f l))
    (hreg : ∀ l b, f l b = 0 → mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (f l) b ≠ 0)
    {C : Set B} (hC : C = {b | ∀ l, f l b ≤ 0}) (hCc : IsCompact C)
    (κ K : Fin c → PartialDiffeomorph 𝓘(ℝ, ℝ × ℝ) (𝓡 2) (ℝ × ℝ) B ∞)
    (hK : ∀ k, (K k).source = rimBox 3)
    (hκK : ∀ k v, v ∈ rimBox 2 → κ k v = K k v)
    (hKdisj : Pairwise fun k k' => Disjoint (K k).target (K k').target)
    (first second : Fin c → Fin m) (lam : Fin c → ℝ) (hlam : ∀ k, 0 < lam k)
    (hfirst : ∀ k v, v ∈ rimBox 3 → f (first k) (K k v) = -(lam k * v.1))
    (hsecond : ∀ k v, v ∈ rimBox 3 → f (second k) (K k v) = -(lam k * v.2))
    (hother : ∀ k l v, l ≠ first k → l ≠ second k → v ∈ rimBox 3 → f l (K k v) < 0)
    (hcenter : ∀ b l l', l ≠ l' → f l b = 0 → f l' b = 0 → ∃ k, b = κ k (0, 0)) :
    ∃ r : B → ℝ, ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ r ∧
      (∀ b, r b = 0 → mfderiv (𝓡 2) 𝓘(ℝ, ℝ) r b ≠ 0) ∧
      (∀ k v, v ∈ rimBox 2 → r (κ k v) = -(lam k * standardRimRounding v)) ∧
      {b | r b ≤ 0} \ (⋃ k, κ k '' rimBox 1) = C \ ⋃ k, κ k '' rimBox 1 ∧
      IsCompact {b | r b ≤ 0} ∧
      symmDiff {b | r b ≤ 0} C ⊆ ⋃ k, κ k '' rimBox 1 := by
  classical
  subst hC
  -- chart bookkeeping
  have hleft : ∀ k v, v ∈ rimBox 3 → (K k).symm (K k v) = v := fun k v hv =>
    (K k).toPartialEquiv.left_inv (by rw [hK k]; exact hv)
  have hright : ∀ k b, b ∈ (K k).target → K k ((K k).symm b) = b := fun k b hb =>
    (K k).toPartialEquiv.right_inv hb
  have hmaps : ∀ k v, v ∈ rimBox 3 → K k v ∈ (K k).target := fun k v hv =>
    (K k).toPartialEquiv.map_source (by rw [hK k]; exact hv)
  have hmapt : ∀ k b, b ∈ (K k).target → (K k).symm b ∈ rimBox 3 := fun k b hb => by
    rw [← hK k]
    exact (K k).toPartialEquiv.map_target hb
  have h23 : rimBox 2 ⊆ rimBox 3 := rimBox_mono (by norm_num)
  have h12 : rimBox 1 ⊆ rimBox 2 := rimBox_mono (by norm_num)
  have hcb3 : closedRimBox_GRND 2 ⊆ rimBox 3 := closedRimBox_subset_rimBox_GRND (by norm_num)
  have hb12 : rimBox 1 ⊆ closedRimBox_GRND 2 :=
    (rimBox_subset_closedRimBox_GRND 1).trans fun w hw =>
      ⟨hw.1.trans (by norm_num), hw.2.trans (by norm_num)⟩
  have hκK1 : (⋃ k, κ k '' rimBox 1) = ⋃ k, K k '' rimBox 1 := by
    refine iUnion_congr fun k => image_congr fun v hv => hκK k v (h12 hv)
  rw [hκK1]
  -- the closed boxes
  have hKcomp : ∀ k, IsCompact (K k '' closedRimBox_GRND 2) := fun k =>
    (isCompact_closedRimBox_GRND 2).image_of_continuousOn
      ((K k).contMDiffOn.continuousOn.mono (by rw [hK k]; exact hcb3))
  have hKc_closed : IsClosed (⋃ k, K k '' closedRimBox_GRND 2) :=
    isClosed_iUnion_of_finite fun k => (hKcomp k).isClosed
  set U := roundCover_GRND f K with hU
  set g := roundLocal_GRND f K lam with hg
  -- openness of the cover
  have hopen : ∀ α, IsOpen (U α) := by
    rintro (k | l | _ | _)
    · exact (K k).open_target
    · refine IsOpen.sdiff ?_ hKc_closed
      simp only [ofPred_forall]
      exact isOpen_iInter_of_finite fun l' => isOpen_iInter_of_finite fun _ =>
        isOpen_lt (hf l').continuous continuous_const
    · refine IsOpen.sdiff ?_ hKc_closed
      simp only [ofPred_forall]
      exact isOpen_iInter_of_finite fun l => isOpen_lt (hf l).continuous continuous_const
    · refine IsOpen.sdiff ?_ hKc_closed
      simp only [ofPred_exists]
      exact isOpen_iUnion fun l => isOpen_lt continuous_const (hf l).continuous
  -- a centre of a corner lies in its unit box image
  have hcentre : ∀ b l l', l ≠ l' → f l b = 0 → f l' b = 0 → ∃ k, b ∈ K k '' rimBox 1 := by
    intro b l l' hll' hl hl'
    obtain ⟨k, rfl⟩ := hcenter b l l' hll' hl hl'
    exact ⟨k, (0, 0), zero_mem_rimBox_GRND one_pos,
      (hκK k (0, 0) (zero_mem_rimBox_GRND two_pos)).symm⟩
  -- the cover covers
  have hcover : univ ⊆ ⋃ α, U α := by
    intro b _
    rw [mem_iUnion]
    by_cases hb : b ∈ ⋃ k, K k '' closedRimBox_GRND 2
    · obtain ⟨k, v, hv, rfl⟩ := mem_iUnion.1 hb
      exact ⟨.inl k, hmaps k v (hcb3 hv)⟩
    by_cases hneg : ∀ l, f l b < 0
    · exact ⟨.inr (.inr false), hneg, hb⟩
    by_cases hpos : ∃ l, 0 < f l b
    · exact ⟨.inr (.inr true), hpos, hb⟩
    push Not at hneg hpos
    obtain ⟨l, hl⟩ := hneg
    have hl0 : f l b = 0 := le_antisymm (hpos l) hl
    refine ⟨.inr (.inl l), fun l' hl' => ?_, hb⟩
    rcases (hpos l').lt_or_eq with h | h
    · exact h
    · obtain ⟨k, hk⟩ := hcentre b l' l hl' h hl0
      have hin : b ∈ ⋃ k, K k '' closedRimBox_GRND 2 :=
        mem_iUnion.2 ⟨k, image_mono hb12 hk⟩
      exact absurd hin hb
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate (𝓡 2) isClosed_univ U hopen hcover
  set r : B → ℝ := fun b => ∑ᶠ α, ρ α b • g α b with hr
  -- active weights live in their sets
  have hact : ∀ α b, ρ α b ≠ 0 → b ∈ U α := fun α b hb =>
    hρ α (subset_tsupport _ (mem_support.2 hb))
  -- pointwise agreement
  have hpt : ∀ b (h : ℝ), (∀ α, ρ α b ≠ 0 → g α b = h) → r b = h := fun b h hα =>
    ρ.finsum_smul_mem_convex (mem_univ b) (t := {h}) (fun α hα' => hα α hα') (convex_singleton h)
  -- on a closed box only the corner survives
  have hbox : ∀ k v, v ∈ closedRimBox_GRND 2 → r (K k v) = -(lam k * standardRimRounding v) := by
    intro k v hv
    refine hpt _ _ fun α hα => ?_
    have hU := hact α _ hα
    have hin : K k v ∈ ⋃ k, K k '' closedRimBox_GRND 2 := mem_iUnion.2 ⟨k, v, hv, rfl⟩
    rcases α with k' | l | _ | _
    · by_cases hkk : k' = k
      · subst hkk
        change -(lam k' * standardRimRounding ((K k').symm (K k' v))) = _
        rw [hleft k' v (hcb3 hv)]
      · exact absurd hU (Set.disjoint_left.1 (hKdisj (Ne.symm hkk)) (hmaps k v (hcb3 hv)))
    · exact absurd hin hU.2
    · exact absurd hin hU.2
    · exact absurd hin hU.2
  have hchart : ∀ k v, v ∈ rimBox 2 → r (κ k v) = -(lam k * standardRimRounding v) :=
    fun k v hv => by rw [hκK k v hv]; exact hbox k v (rimBox_subset_closedRimBox_GRND 2 hv)
  -- the sign lemma for the local functions
  have hsign : ∀ α b, b ∈ U α → b ∉ ⋃ k, K k '' rimBox 1 →
      (g α b ≤ 0 ↔ ∀ l, f l b ≤ 0) ∧ (g α b < 0 ↔ ∀ l, f l b < 0) := by
    intro α b hU hb1
    rcases α with k | l | _ | _
    · have hv := hmapt k b hU
      have hv1 : (K k).symm b ∉ rimBox 1 := fun h =>
        hb1 (mem_iUnion.2 ⟨k, _, h, hright k b hU⟩)
      have hb := hright k b hU
      have h1 := hfirst k _ hv
      have h2 := hsecond k _ hv
      rw [hb] at h1 h2
      exact corner_sign_GRND f (hlam k) hv1 h1 h2 fun l hl1 hl2 => by
        have := hother k l _ hl1 hl2 hv
        rwa [hb] at this
    · have hU' : ∀ l', l' ≠ l → f l' b < 0 := hU.1
      change (f l b ≤ 0 ↔ _) ∧ (f l b < 0 ↔ _)
      constructor
      · refine ⟨fun h l' => ?_, fun h => h l⟩
        by_cases hl : l' = l
        · rw [hl]; exact h
        · exact (hU' l' hl).le
      · refine ⟨fun h l' => ?_, fun h => h l⟩
        by_cases hl : l' = l
        · rw [hl]; exact h
        · exact hU' l' hl
    · have hU' : ∀ l, f l b < 0 := hU.1
      change ((-1 : ℝ) ≤ 0 ↔ _) ∧ ((-1 : ℝ) < 0 ↔ _)
      exact ⟨⟨fun _ l => (hU' l).le, fun _ => by norm_num⟩, ⟨fun _ => hU', fun _ => by norm_num⟩⟩
    · obtain ⟨l, hl⟩ : ∃ l, 0 < f l b := hU.1
      change ((1 : ℝ) ≤ 0 ↔ _) ∧ ((1 : ℝ) < 0 ↔ _)
      exact ⟨⟨fun h => absurd h (by norm_num), fun h => absurd (h l) (not_le.2 hl)⟩,
        ⟨fun h => absurd h (by norm_num), fun h => absurd (h l) (not_lt.2 hl.le)⟩⟩
  -- the sign of `r` off the unit boxes
  have hrsign : ∀ b, b ∉ ⋃ k, K k '' rimBox 1 →
      (r b ≤ 0 ↔ ∀ l, f l b ≤ 0) ∧ (r b < 0 ↔ ∀ l, f l b < 0) := by
    intro b hb1
    constructor
    · constructor
      · intro hrb
        by_contra hne
        have hpos : r b ∈ Ioi 0 := ρ.finsum_smul_mem_convex (mem_univ b)
          (fun α hα => not_le.1 fun h =>
            hne ((hsign α b (hact α b hα) hb1).1.1 h)) (convex_Ioi (0 : ℝ))
        exact absurd hrb (not_le.2 hpos)
      · intro h
        exact ρ.finsum_smul_mem_convex (mem_univ b)
          (fun α hα => (hsign α b (hact α b hα) hb1).1.2 h) (convex_Iic (0 : ℝ))
    · constructor
      · intro hrb
        by_contra hne
        have hnn : r b ∈ Ici 0 := ρ.finsum_smul_mem_convex (mem_univ b)
          (fun α hα => not_lt.1 fun h =>
            hne ((hsign α b (hact α b hα) hb1).2.1 h)) (convex_Ici (0 : ℝ))
        exact absurd hrb (not_lt.2 hnn)
      · intro h
        exact ρ.finsum_smul_mem_convex (mem_univ b)
          (fun α hα => (hsign α b (hact α b hα) hb1).2.2 h) (convex_Iio (0 : ℝ))
  -- smoothness
  have hsmooth : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ r := by
    refine hρ.contMDiff_finsum_smul (n := ⊤) hopen fun α => ?_
    rcases α with k | l | _ | _
    · have h1 : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ∞ (K k).symm (K k).target :=
        (K k).symm.contMDiffOn
      exact ((contDiff_const.mul contDiff_standardRimRounding).neg.contMDiff).comp_contMDiffOn h1
    · exact (hf l).contMDiffOn
    · exact contMDiffOn_const
    · exact contMDiffOn_const
  -- agreement off the unit boxes
  have hagree : {b | r b ≤ 0} \ (⋃ k, K k '' rimBox 1) =
      {b | ∀ l, f l b ≤ 0} \ ⋃ k, K k '' rimBox 1 := by
    ext b
    simp only [Set.mem_sdiff, mem_ofPred_eq]
    constructor
    · rintro ⟨h, hb⟩
      exact ⟨(hrsign b hb).1.1 h, hb⟩
    · rintro ⟨h, hb⟩
      exact ⟨(hrsign b hb).1.2 h, hb⟩
  -- the rounded base lies in the cornered base
  have hsubC : {b | r b ≤ 0} ⊆ {b | ∀ l, f l b ≤ 0} := by
    intro b hrb
    by_cases hb1 : b ∈ ⋃ k, K k '' rimBox 1
    · obtain ⟨k, v, hv, rfl⟩ := mem_iUnion.1 hb1
      have hrv := hbox k v (hb12 hv)
      have hrb' : r (K k v) ≤ 0 := hrb
      rw [hrv, neg_nonpos, mul_nonneg_iff_of_pos_left (hlam k)] at hrb'
      obtain ⟨hx, hy⟩ := nonneg_of_standardRimRounding_nonneg v hrb'
      intro l
      by_cases hl1 : l = first k
      · rw [hl1, hfirst k v (h23 (h12 hv)), neg_nonpos]
        exact mul_nonneg (hlam k).le hx
      by_cases hl2 : l = second k
      · rw [hl2, hsecond k v (h23 (h12 hv)), neg_nonpos]
        exact mul_nonneg (hlam k).le hy
      exact (hother k l v hl1 hl2 (h23 (h12 hv))).le
    · exact (hrsign b hb1).1.1 hrb
  -- regularity
  have hregular : ∀ b, r b = 0 → mfderiv (𝓡 2) 𝓘(ℝ, ℝ) r b ≠ 0 := by
    intro b hrb
    by_cases hb2 : b ∈ ⋃ k, K k '' rimBox 2
    · obtain ⟨k, v, hv, rfl⟩ := mem_iUnion.1 hb2
      intro hzero
      have hvs : v ∈ (K k).source := by rw [hK k]; exact h23 hv
      have hKd : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) (𝓡 2) (K k) v :=
        (K k).mdifferentiableAt (by simp) hvs
      have hrd : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ) r (K k v) :=
        (hsmooth (K k v)).mdifferentiableAt (by simp)
      have hcomp := mfderiv_comp v hrd hKd
      rw [hzero, ContinuousLinearMap.zero_comp] at hcomp
      have hψ : HasFDerivAt standardRimRounding (fderiv ℝ standardRimRounding v) v :=
        ((contDiff_standardRimRounding.differentiable (by simp)) v).hasFDerivAt
      have hloc : (r ∘ K k) =ᶠ[𝓝 v] fun w => -(lam k * standardRimRounding w) := by
        filter_upwards [(isOpen_rimBox_GRIM 2).mem_nhds hv] with w hw
        exact hbox k w (rimBox_subset_closedRimBox_GRND 2 hw)
      have hder : HasMFDerivAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ) (r ∘ K k) v
          (-(lam k • fderiv ℝ standardRimRounding v)) :=
        ((hψ.const_mul (lam k)).neg.hasMFDerivAt).congr_of_eventuallyEq hloc
      rw [hder.mfderiv] at hcomp
      have h11 := congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L ((1 : ℝ), (1 : ℝ))) hcomp
      simp only [neg_apply, smul_apply, fderiv_standardRimRounding_diag, smul_eq_mul,
        mul_one] at h11
      have h0 : -lam k = 0 := h11
      exact (hlam k).ne' (neg_eq_zero.1 h0)
    · have hb1 : b ∉ ⋃ k, K k '' rimBox 1 := fun h => hb2 (by
        obtain ⟨k, v, hv, rfl⟩ := mem_iUnion.1 h
        exact mem_iUnion.2 ⟨k, v, h12 hv, rfl⟩)
      have hle := (hrsign b hb1).1.1 hrb.le
      have hnlt : ¬ ∀ l, f l b < 0 := fun h => absurd ((hrsign b hb1).2.2 h) hrb.not_lt
      push Not at hnlt
      obtain ⟨l, hl⟩ := hnlt
      have hl0 : f l b = 0 := le_antisymm (hle l) hl
      have hothers : ∀ l', l' ≠ l → f l' b < 0 := fun l' hl' =>
        (hle l').lt_of_ne fun h => hb1 (hcentre b l' l hl' h hl0 |> fun ⟨k, hk⟩ =>
          mem_iUnion.2 ⟨k, hk⟩)
      -- every local weight vanishes near `b` or its function is `f l` near `b`
      have hloc : ∀ α, ∀ᶠ q in 𝓝 b, ρ α q = 0 ∨ g α q = f l q := by
        intro α
        by_cases hbU : b ∈ U α
        · rcases α with k | l' | _ | _
          · have hv := hmapt k b hbU
            have hbK := hright k b hbU
            have hv2 : (K k).symm b ∉ rimBox 2 := fun h =>
              hb2 (mem_iUnion.2 ⟨k, _, h, hbK⟩)
            have hf1 := hfirst k _ hv
            have hf2 := hsecond k _ hv
            rw [hbK] at hf1 hf2
            have hl12 : l = first k ∨ l = second k := by
              by_contra hne
              push Not at hne
              have := hother k l _ hne.1 hne.2 hv
              rw [hbK, hl0] at this
              exact lt_irrefl 0 this
            have hopenT : IsOpen ((K k).target ∩ (K k).symm ⁻¹'
                {w : ℝ × ℝ | w.1 + 1 / 4 < w.2}) :=
              (K k).symm.contMDiffOn.continuousOn.isOpen_inter_preimage (K k).open_target
                (isOpen_lt (continuous_fst.add continuous_const) continuous_snd)
            have hopenT' : IsOpen ((K k).target ∩ (K k).symm ⁻¹'
                {w : ℝ × ℝ | w.2 + 1 / 4 < w.1}) :=
              (K k).symm.contMDiffOn.continuousOn.isOpen_inter_preimage (K k).open_target
                (isOpen_lt (continuous_snd.add continuous_const) continuous_fst)
            rcases hl12 with hlk | hlk
            · -- the vertical face: `x = 0`, `y ≥ 2`
              have hx : ((K k).symm b).1 = 0 := by
                rw [hlk, hf1, neg_eq_zero] at hl0
                exact (mul_eq_zero.1 hl0).resolve_left (hlam k).ne'
              have hy : 0 ≤ ((K k).symm b).2 := by
                have := hle (second k)
                rw [hf2, neg_nonpos] at this
                exact nonneg_of_mul_nonneg_right (by linarith) (hlam k)
              have hy2 : 2 ≤ ((K k).symm b).2 := by
                by_contra hlt
                refine hv2 ⟨by rw [hx, abs_zero]; norm_num, ?_⟩
                rw [abs_of_nonneg hy]
                linarith
              refine Filter.Eventually.mono (hopenT.mem_nhds ⟨hbU, ?_⟩) fun q hq => Or.inr ?_
              · change ((K k).symm b).1 + 1 / 4 < ((K k).symm b).2
                linarith
              · have hwq := hmapt k q hq.1
                change -(lam k * standardRimRounding ((K k).symm q)) = f l q
                rw [standardRimRounding_eq_fst_GRND (le_of_lt hq.2), hlk,
                  ← hfirst k _ hwq, hright k q hq.1]
            · -- the horizontal face: `y = 0`, `x ≥ 2`
              have hy : ((K k).symm b).2 = 0 := by
                rw [hlk, hf2, neg_eq_zero] at hl0
                exact (mul_eq_zero.1 hl0).resolve_left (hlam k).ne'
              have hx : 0 ≤ ((K k).symm b).1 := by
                have := hle (first k)
                rw [hf1, neg_nonpos] at this
                exact nonneg_of_mul_nonneg_right (by linarith) (hlam k)
              have hx2 : 2 ≤ ((K k).symm b).1 := by
                by_contra hlt
                refine hv2 ⟨?_, by rw [hy, abs_zero]; norm_num⟩
                rw [abs_of_nonneg hx]
                linarith
              refine Filter.Eventually.mono (hopenT'.mem_nhds ⟨hbU, ?_⟩) fun q hq => Or.inr ?_
              · change ((K k).symm b).2 + 1 / 4 < ((K k).symm b).1
                linarith
              · have hwq := hmapt k q hq.1
                change -(lam k * standardRimRounding ((K k).symm q)) = f l q
                rw [standardRimRounding_eq_snd_GRND (le_of_lt hq.2), hlk,
                  ← hsecond k _ hwq, hright k q hq.1]
          · by_cases hll : l' = l
            · subst hll
              exact Filter.Eventually.of_forall fun q => Or.inr rfl
            · have := hbU.1 l (Ne.symm hll)
              rw [hl0] at this
              exact absurd this (lt_irrefl 0)
          · have := (hbU.1 : ∀ l, f l b < 0) l
            rw [hl0] at this
            exact absurd this (lt_irrefl 0)
          · obtain ⟨l'', hl''⟩ : ∃ l'', 0 < f l'' b := hbU.1
            exact absurd (hle l'') (not_le.2 hl'')
        · have hts : b ∉ tsupport (ρ α) := fun h => hbU (hρ α h)
          rw [notMem_tsupport_iff_eventuallyEq] at hts
          exact hts.mono fun q hq => Or.inl hq
      have hall : ∀ᶠ q in 𝓝 b, ∀ α, ρ α q = 0 ∨ g α q = f l q :=
        Filter.eventually_all.2 hloc
      have heq : r =ᶠ[𝓝 b] f l := hall.mono fun q hq =>
        hpt q (f l q) fun α hα => (hq α).resolve_left hα
      rw [heq.mfderiv_eq]
      exact hreg l b hl0
  refine ⟨r, hsmooth, hregular, hchart, hagree, ?_, ?_⟩
  · exact hCc.of_isClosed_subset (isClosed_le hsmooth.continuous continuous_const) hsubC
  · intro b hb
    by_contra hb1
    have hiff := (hrsign b hb1).1
    rcases (mem_symmDiff.1 hb) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h2 (hiff.1 h1)
    · exact h2 (hiff.2 h1)

end Main

end GC.GraphManifold.Assembly.FC39P0
