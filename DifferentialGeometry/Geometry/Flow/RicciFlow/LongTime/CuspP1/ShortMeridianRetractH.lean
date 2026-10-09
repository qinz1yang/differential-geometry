import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.ShortGeodesicDeepMain

/-!
# CP1-A3 (G2, model level): the exterior of a truncation retracts onto the exterior of its
deepening

For a hyperbolic truncation `T` of a finite-volume model `H` and `b ≥ 2`, the exterior
`H ∖ ι(int core)` is the disjoint union of the cusp ranges `⋃_q range (cuspMap q)`, and
`rho_CPA3 T b` pushes every cusp point of height `< b` to height `b` (identity above).
-/

set_option autoImplicit false
noncomputable section
open Set Function Filter Manifold GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
  DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology
universe u
namespace GC.LongTime.CuspP1

/-- Raise the height of a cusp point to at least `b`. -/
def cutoff_CPA3 (b : ℝ) (q : CuspHalfSpace) : CuspHalfSpace :=
  (q.1, halfSpaceOneLift (max (q.2.val 0) b))

theorem continuous_cutoff_CPA3 (b : ℝ) : Continuous (cutoff_CPA3 b) := by
  refine continuous_fst.prodMk ?_
  have h1 : Continuous (fun q : CuspHalfSpace => max (q.2.val 0) b) :=
    ((EuclideanSpace.proj 0).continuous.comp (continuous_subtype_val.comp continuous_snd)).max
      continuous_const
  exact continuous_halfSpaceOneLift_CPA2.comp h1

theorem cutoff_height_CPA3 {b : ℝ} (hb : 0 ≤ b) (q : CuspHalfSpace) :
    (cutoff_CPA3 b q).2.val 0 = max (q.2.val 0) b :=
  halfSpaceOneLift_val_CPA2 (le_max_of_le_right hb)

theorem cutoff_eq_self_CPA3 {b : ℝ} (q : CuspHalfSpace) (h : b ≤ q.2.val 0) :
    cutoff_CPA3 b q = q := by
  refine Prod.ext rfl ?_
  change halfSpaceOneLift (max (q.2.val 0) b) = q.2
  rw [max_eq_left h]
  exact halfSpaceOneLift_coord_CPA2 q.2

variable {H : FiniteVolumeHyperbolicModel.{u}} (T : HyperbolicTruncation H)

theorem cuspMap_eq_CPA3 {q q' : Fin T.count} {c c' : CuspHalfSpace}
    (h : T.cuspMap q c = T.cuspMap q' c') : q = q' ∧ c = c' := by
  have hq : q = q' := by
    by_contra hne
    exact Set.disjoint_left.mp (T.cusp_disjoint hne) ⟨c, rfl⟩ ⟨c', h.symm⟩
  subst hq
  exact ⟨rfl, (T.cuspEmbedding q).isEmbedding.injective h⟩

/-- The exterior of the core: the union of the cusp ranges. -/
def extSet_CPA3 : Set H.Carrier := ⋃ q, range (T.cuspMap q)

/-- The retraction of the exterior onto the exterior of the `b`-deepening. -/
def rho_CPA3 (b : ℝ) (p : H.Carrier) : H.Carrier :=
  open Classical in
  if h : ∃ (q : Fin T.count) (c : CuspHalfSpace), T.cuspMap q c = p then
    T.cuspMap h.choose (cutoff_CPA3 b h.choose_spec.choose)
  else p

theorem rho_cuspMap_CPA3 (b : ℝ) (q : Fin T.count) (c : CuspHalfSpace) :
    rho_CPA3 T b (T.cuspMap q c) = T.cuspMap q (cutoff_CPA3 b c) := by
  classical
  have h : ∃ (q' : Fin T.count) (c' : CuspHalfSpace), T.cuspMap q' c' = T.cuspMap q c :=
    ⟨q, c, rfl⟩
  rw [rho_CPA3, dif_pos h]
  have key : ∀ (a : Fin T.count) (d : CuspHalfSpace), T.cuspMap a d = T.cuspMap q c →
      T.cuspMap a (cutoff_CPA3 b d) = T.cuspMap q (cutoff_CPA3 b c) := by
    intro a d hd
    obtain ⟨rfl, rfl⟩ := cuspMap_eq_CPA3 T hd
    rfl
  exact key _ _ h.choose_spec.choose_spec

theorem continuousOn_rho_range_CPA3 (b : ℝ) (q : Fin T.count) :
    ContinuousOn (rho_CPA3 T b) (range (T.cuspMap q)) := by
  have hemb := (T.cuspEmbedding q).isEmbedding
  let e := hemb.toHomeomorph
  rw [continuousOn_iff_continuous_domRestrict]
  have : (range (T.cuspMap q)).domRestrict (rho_CPA3 T b) =
      fun y => T.cuspMap q (cutoff_CPA3 b (e.symm y)) := by
    ext ⟨p, hp⟩
    obtain ⟨c, rfl⟩ := hp
    have : e.symm ⟨T.cuspMap q c, c, rfl⟩ = c := by
      have h2 := e.symm_apply_apply c
      exact h2
    simp only [domRestrict_apply, this]
    exact rho_cuspMap_CPA3 T b q c
  rw [this]
  exact (T.cuspEmbedding q).contMDiff.continuous.comp
    ((continuous_cutoff_CPA3 b).comp e.symm.continuous)

theorem continuousOn_rho_ext_CPA3 (b : ℝ) : ContinuousOn (rho_CPA3 T b) (extSet_CPA3 T) := by
  have hcl : ∀ q, IsClosed (range (T.cuspMap q)) := isClosed_range_cuspMap_CPA2 T
  exact LocallyFinite.continuousOn_iUnion (locallyFinite_of_finite _) hcl
    (continuousOn_rho_range_CPA3 T b)

/-- Points of height zero in the cusp are not in `cuspW`. -/
theorem cuspMap_not_mem_cuspW_of_height_zero_CPA3 (q : Fin T.count) {c : CuspHalfSpace}
    (hc : ¬ 0 < c.2.val 0) (j : Fin T.count) : T.cuspMap q c ∉ cuspW_CPA2 T j := by
  rintro ⟨c', hc', h⟩
  obtain ⟨-, rfl⟩ := cuspMap_eq_CPA3 T h
  exact hc hc'

theorem deepHeight_cuspMap_of_height_zero_CPA3 (b : ℝ) (q : Fin T.count) {c : CuspHalfSpace}
    (hc : ¬ 0 < c.2.val 0) : deepHeight_CPA2 T b (T.cuspMap q c) = -b :=
  deepHeight_of_forall_not_mem_CPA2 T b (cuspMap_not_mem_cuspW_of_height_zero_CPA3 T q hc)

theorem deepHeight_rho_nonneg_CPA3 {b : ℝ} (hb : 2 ≤ b) (q : Fin T.count) (c : CuspHalfSpace) :
    0 ≤ deepHeight_CPA2 T b (rho_CPA3 T b (T.cuspMap q c)) := by
  rw [rho_cuspMap_CPA3]
  have h0 : 0 < (cutoff_CPA3 b c).2.val 0 := by
    rw [cutoff_height_CPA3 (by linarith)]
    exact lt_of_lt_of_le (by linarith) (le_max_right _ _)
  rw [deepHeight_cuspMap_CPA2 T b q h0, cutoff_height_CPA3 (by linarith)]
  have h1 : (1 : ℝ) ≤ max (c.2.val 0) b := le_trans (by linarith) (le_max_right _ _)
  rw [lam_eq_CPA2 h1]
  linarith [le_max_right (c.2.val 0) b]

theorem height_ge_of_deepHeight_nonneg_CPA3 {b : ℝ} (hb : 2 ≤ b) (q : Fin T.count)
    (c : CuspHalfSpace) (h : 0 ≤ deepHeight_CPA2 T b (T.cuspMap q c)) : b ≤ c.2.val 0 := by
  by_cases hc : 0 < c.2.val 0
  · rw [deepHeight_cuspMap_CPA2 T b q hc] at h
    by_cases h1 : 1 ≤ c.2.val 0
    · rw [lam_eq_CPA2 h1] at h
      linarith
    · have := lam_lt_one_CPA2 (not_le.mp h1)
      linarith
  · rw [deepHeight_cuspMap_of_height_zero_CPA3 T b q hc] at h
    linarith

theorem rho_eq_self_of_deepHeight_nonneg_CPA3 {b : ℝ} (hb : 2 ≤ b) (q : Fin T.count)
    (c : CuspHalfSpace) (h : 0 ≤ deepHeight_CPA2 T b (T.cuspMap q c)) :
    rho_CPA3 T b (T.cuspMap q c) = T.cuspMap q c := by
  rw [rho_cuspMap_CPA3, cutoff_eq_self_CPA3 _ (height_ge_of_deepHeight_nonneg_CPA3 T hb q c h)]

/-- The retraction fixes the points of height `≥ b` and moves the others into the `b`-deepening. -/
theorem rho_eq_or_mem_deepSet_CPA3 {b : ℝ} (hb : 2 ≤ b) (q : Fin T.count) (c : CuspHalfSpace) :
    rho_CPA3 T b (T.cuspMap q c) = T.cuspMap q c ∨
      rho_CPA3 T b (T.cuspMap q c) ∈ deepSet_CPA2 T b := by
  by_cases h : b ≤ c.2.val 0
  · left
    rw [rho_cuspMap_CPA3, cutoff_eq_self_CPA3 _ h]
  · right
    rw [rho_cuspMap_CPA3]
    change deepHeight_CPA2 T b _ ≤ 0
    have h0 : 0 < (cutoff_CPA3 b c).2.val 0 := by
      rw [cutoff_height_CPA3 (by linarith)]
      exact lt_of_lt_of_le (by linarith) (le_max_right _ _)
    rw [deepHeight_cuspMap_CPA2 T b q h0, cutoff_height_CPA3 (by linarith),
      max_eq_right (not_le.mp h).le, lam_eq_CPA2 (by linarith)]
    linarith

/-- A point moved by the retraction lies in a collar of height `< b`. -/
theorem exists_collar_of_rho_ne_CPA3 {b : ℝ} (q : Fin T.count) (c : CuspHalfSpace)
    (h : rho_CPA3 T b (T.cuspMap q c) ≠ T.cuspMap q c) : c.2.val 0 < b := by
  by_contra hb
  apply h
  rw [rho_cuspMap_CPA3, cutoff_eq_self_CPA3 _ (not_lt.mp hb)]

/-- The exterior of the core is the union of the cusp ranges. -/
theorem not_mem_interior_image_iff_CPA3 (p : H.Carrier) :
    p ∉ T.inclusion '' (T.core.interior : Set T.core.Carrier) ↔ p ∈ extSet_CPA3 T := by
  constructor
  · intro hp
    have hex : p ∈ range T.inclusion ∪ ⋃ k, range (T.cuspMap k) := by rw [T.exhausts]; trivial
    rcases hex with ⟨c, rfl⟩ | hk
    · by_cases hc : T.core.model.IsInteriorPoint c
      · exact absurd ⟨c, hc, rfl⟩ hp
      · have hbd : T.core.model.IsBoundaryPoint c :=
          (T.core.model.isInteriorPoint_or_isBoundaryPoint c).resolve_left hc
        have hb : c ∈ T.boundary.image := by
          rw [← T.boundary_exhausted]; exact hbd
        obtain ⟨k, x, rfl⟩ := mem_iUnion.mp hb
        exact mem_iUnion.mpr ⟨k, (x, halfZero), (T.cusp_zero k x)⟩
    · exact hk
  · intro hp
    rintro ⟨c, hc, rfl⟩
    obtain ⟨k, hk⟩ := mem_iUnion.mp hp
    exact inclusion_not_mem_range_of_interior_CPA2 T k hc hk

theorem interior_image_subset_neg_CPA3 {b : ℝ} (hb : 0 < b) :
    T.inclusion '' (T.core.interior : Set T.core.Carrier) ⊆ {p | deepHeight_CPA2 T b p < 0} := by
  rintro _ ⟨c, hc, rfl⟩
  have : ∀ i, T.inclusion c ∉ cuspW_CPA2 T i := by
    intro i hi
    obtain ⟨q, -, hq⟩ := hi
    exact inclusion_not_mem_range_of_interior_CPA2 T i hc ⟨q, hq⟩
  change deepHeight_CPA2 T b _ < 0
  rw [deepHeight_of_forall_not_mem_CPA2 T b this]
  linarith

end GC.LongTime.CuspP1
