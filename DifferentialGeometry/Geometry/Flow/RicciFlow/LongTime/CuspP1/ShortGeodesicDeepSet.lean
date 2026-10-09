import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.ShortGeodesicDeepLevel
import DifferentialGeometry.Topology.Manifold.HalfLine

set_option autoImplicit false
noncomputable section
open Set Function Filter Manifold GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open scoped Manifold ContDiff Topology
universe u
namespace GC.LongTime.CuspP1

/-- The half-line points of height at most `b`. -/
def halfSegment_CPA2 (b : ℝ) : Set (EuclideanHalfSpace 1) := {u | u.val 0 ≤ b}

theorem halfSegment_eq_image_CPA2 (b : ℝ) :
    halfSegment_CPA2 b = DifferentialGeometry.Topology.Manifold.halfSpaceOneLift '' Icc 0 b := by
  ext u
  constructor
  · intro hu
    refine ⟨u.val 0, ⟨u.2, hu⟩, ?_⟩
    apply Subtype.ext
    ext i
    rw [Subsingleton.elim i 0]
    change max (u.val 0) 0 = u.val 0
    exact max_eq_left u.2
  · rintro ⟨t, ht, rfl⟩
    change (max t 0) ≤ b
    rw [max_eq_left ht.1]
    exact ht.2

theorem isCompact_halfSegment_CPA2 {b : ℝ} (hb : 0 ≤ b) : IsCompact (halfSegment_CPA2 b) := by
  rw [halfSegment_eq_image_CPA2 b]
  exact isCompact_Icc.image_of_continuousOn
    (DifferentialGeometry.Topology.Manifold.contMDiffOn_halfSpaceOneLift.continuousOn.mono
      Icc_subset_Ici_self)

theorem isConnected_halfSegment_CPA2 {b : ℝ} (hb : 0 ≤ b) : IsConnected (halfSegment_CPA2 b) := by
  rw [halfSegment_eq_image_CPA2 b]
  exact isConnected_Icc hb |>.image _
    (DifferentialGeometry.Topology.Manifold.contMDiffOn_halfSpaceOneLift.continuousOn.mono
      Icc_subset_Ici_self)

variable {H : FiniteVolumeHyperbolicModel.{u}} (T : HyperbolicTruncation H)

/-- The part of the `i`-th cusp of height at most `b` (including the boundary torus). -/
def cuspCollar_CPA2 (i : Fin T.count) (b : ℝ) : Set H.Carrier :=
  T.cuspMap i '' (univ ×ˢ halfSegment_CPA2 b)

/-- The deeper core: points of `H` off the tails `{height > b}` of the cusps. -/
def deepSet_CPA2 (b : ℝ) : Set H.Carrier := {p | deepHeight_CPA2 T b p ≤ 0}

theorem isCompact_cuspCollar_CPA2 (i : Fin T.count) {b : ℝ} (hb : 0 ≤ b) :
    IsCompact (cuspCollar_CPA2 T i b) :=
  (isCompact_univ.prod (isCompact_halfSegment_CPA2 hb)).image
    (T.cuspEmbedding i).contMDiff.continuous

theorem isConnected_cuspCollar_CPA2 (i : Fin T.count) {b : ℝ} (hb : 0 ≤ b) :
    IsConnected (cuspCollar_CPA2 T i b) :=
  (isConnected_univ.prod (isConnected_halfSegment_CPA2 hb)).image _
    (T.cuspEmbedding i).contMDiff.continuous.continuousOn

theorem deepSet_eq_CPA2 {b : ℝ} (hb : 1 ≤ b) :
    deepSet_CPA2 T b = range T.inclusion ∪ ⋃ i, cuspCollar_CPA2 T i b := by
  ext p
  constructor
  · intro hp
    have hp' := (deepHeight_le_zero_iff_CPA2 T hb p).mp hp
    have hex : p ∈ range T.inclusion ∪ ⋃ i, range (T.cuspMap i) := by
      rw [T.exhausts]; trivial
    rcases hex with hι | hc
    · exact Or.inl hι
    · right
      obtain ⟨i, q, rfl⟩ := mem_iUnion.mp hc
      refine mem_iUnion.mpr ⟨i, q, ⟨trivial, ?_⟩, rfl⟩
      change q.2.val 0 ≤ b
      rcases q.2.2.eq_or_lt with h0 | hpos
      · rw [← h0]; linarith
      · exact hp' i q hpos rfl
  · intro hp
    change deepHeight_CPA2 T b p ≤ 0
    rw [deepHeight_le_zero_iff_CPA2 T hb]
    intro j q hq hqp
    rcases hp with ⟨c, rfl⟩ | hc
    · exfalso
      have hmem : T.cuspMap j q ∈ range T.inclusion ∩ range (T.cuspMap j) := ⟨⟨c, hqp.symm⟩, ⟨q, rfl⟩⟩
      rw [T.intersection j] at hmem
      obtain ⟨x, hx⟩ := hmem
      have := (T.cuspEmbedding j).isEmbedding.injective hx
      rw [← this] at hq
      simp [halfZero, halfPoint] at hq
    · obtain ⟨i, q', hq', rfl⟩ := mem_iUnion.mp hc
      by_cases hij : i = j
      · subst hij
        have := (T.cuspEmbedding i).isEmbedding.injective hqp
        subst this
        exact hq'.2
      · exfalso
        exact Set.disjoint_left.mp (T.cusp_disjoint hij) ⟨q', rfl⟩ ⟨q, hqp⟩

theorem isCompact_deepSet_CPA2 {b : ℝ} (hb : 1 ≤ b) : IsCompact (deepSet_CPA2 T b) := by
  rw [deepSet_eq_CPA2 T hb]
  refine (isCompact_range T.inclusion.continuous).union ?_
  exact isCompact_iUnion fun i => isCompact_cuspCollar_CPA2 T i (by linarith)

theorem isConnected_deepSet_CPA2 {b : ℝ} (hb : 1 ≤ b) : IsConnected (deepSet_CPA2 T b) := by
  rw [deepSet_eq_CPA2 T hb]
  have hcore : IsConnected (range T.inclusion) := by
    have := T.connected
    exact isConnected_range T.inclusion.continuous
  have hpiece : ∀ i, IsConnected (range T.inclusion ∪ cuspCollar_CPA2 T i b) := by
    intro i
    refine IsConnected.union ?_ hcore (isConnected_cuspCollar_CPA2 T i (by linarith))
    obtain ⟨x⟩ : Nonempty Torus := ⟨((1 : Circle), (1 : Circle))⟩
    refine ⟨T.cuspMap i (x, halfZero), ?_, ?_⟩
    · rw [T.cusp_zero]; exact ⟨_, rfl⟩
    · exact ⟨(x, halfZero), ⟨trivial, by change (0 : ℝ) ≤ b; linarith⟩, rfl⟩
  have hU : range T.inclusion ∪ ⋃ i, cuspCollar_CPA2 T i b =
      ⋃₀ (insert (range T.inclusion) (range fun i => range T.inclusion ∪ cuspCollar_CPA2 T i b)) := by
    ext p
    simp only [mem_union, mem_iUnion, mem_sUnion, mem_insert_iff, mem_range, exists_eq_or_imp,
      exists_exists_eq_and]
    constructor
    · rintro (h | ⟨i, h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨i, Or.inr h⟩
    · rintro (h | ⟨i, h | h⟩)
      · exact Or.inl h
      · exact Or.inl h
      · exact Or.inr ⟨i, h⟩
  rw [hU]
  obtain ⟨x₀, hx₀⟩ := hcore.nonempty
  refine ⟨⟨x₀, ⟨_, mem_insert _ _, hx₀⟩⟩, ?_⟩
  refine isPreconnected_sUnion x₀ _ ?_ ?_
  · rintro s (rfl | ⟨i, rfl⟩)
    · exact hx₀
    · exact Or.inl hx₀
  · rintro s (rfl | ⟨i, rfl⟩)
    · exact hcore.isPreconnected
    · exact (hpiece i).isPreconnected

end GC.LongTime.CuspP1
