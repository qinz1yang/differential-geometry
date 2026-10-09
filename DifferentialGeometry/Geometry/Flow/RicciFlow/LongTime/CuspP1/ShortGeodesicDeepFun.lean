import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.ShortGeodesicDeepChart
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

set_option autoImplicit false
noncomputable section
open Set Function Filter Manifold GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open scoped Manifold ContDiff Topology
universe u
namespace GC.LongTime.CuspP1

/-- Smooth profile: `0` for `s ≤ 1/2`, the identity for `s ≥ 1`. -/
def lam_CPA2 (s : ℝ) : ℝ := s * Real.smoothTransition (2 * s - 1)

theorem contDiff_lam_CPA2 : ContDiff ℝ ∞ lam_CPA2 :=
  contDiff_id.mul (Real.smoothTransition.contDiff.comp
    ((contDiff_const.mul contDiff_id).sub contDiff_const))

theorem lam_zero_CPA2 {s : ℝ} (h : s ≤ 1 / 2) : lam_CPA2 s = 0 := by
  rw [lam_CPA2, Real.smoothTransition.zero_of_nonpos (by linarith), mul_zero]

theorem lam_eq_CPA2 {s : ℝ} (h : 1 ≤ s) : lam_CPA2 s = s := by
  rw [lam_CPA2, Real.smoothTransition.one_of_one_le (by linarith), mul_one]

theorem lam_lt_one_CPA2 {s : ℝ} (h : s < 1) : lam_CPA2 s < 1 := by
  by_cases h2 : s ≤ 1 / 2
  · rw [lam_zero_CPA2 h2]; norm_num
  · have h2 : 1 / 2 < s := not_le.mp h2
    calc lam_CPA2 s = s * Real.smoothTransition (2 * s - 1) := rfl
      _ ≤ s * 1 := mul_le_mul_of_nonneg_left (Real.smoothTransition.le_one _) (by linarith)
      _ < 1 := by linarith

variable {H : FiniteVolumeHyperbolicModel.{u}} (T : HyperbolicTruncation H)

instance : Nonempty CuspHalfSpace := ⟨((1 : Circle), (1 : Circle)), halfZero⟩

/-- The open set of points of positive height in the `i`-th cusp. -/
def cuspW_CPA2 (i : Fin T.count) : Set H.Carrier :=
  T.cuspMap i '' {q : CuspHalfSpace | 0 < q.2.val 0}

/-- Interior chart of the `i`-th cusp embedding (`HCOL`). -/
def cuspChart_CPA2 (i : Fin T.count) :
    PartialDiffeomorph halfCollarModel (𝓡 3) CuspHalfSpace H.Carrier ∞ :=
  Classical.choose (exists_interior_partialDiffeomorph_CPA2 (T.cuspEmbedding i))

theorem cuspChart_source_CPA2 (i : Fin T.count) :
    (cuspChart_CPA2 T i).source = {q : CuspHalfSpace | 0 < q.2.val 0} :=
  (Classical.choose_spec (exists_interior_partialDiffeomorph_CPA2 (T.cuspEmbedding i))).1

theorem cuspChart_target_CPA2 (i : Fin T.count) :
    (cuspChart_CPA2 T i).target = cuspW_CPA2 T i :=
  (Classical.choose_spec (exists_interior_partialDiffeomorph_CPA2 (T.cuspEmbedding i))).2.1

theorem cuspChart_apply_CPA2 (i : Fin T.count) (q : CuspHalfSpace) :
    (cuspChart_CPA2 T i) q = T.cuspMap i q := by
  have := (Classical.choose_spec (exists_interior_partialDiffeomorph_CPA2 (T.cuspEmbedding i))).2.2
  exact congrFun this q

theorem isOpen_cuspW_CPA2 (i : Fin T.count) : IsOpen (cuspW_CPA2 T i) := by
  rw [← cuspChart_target_CPA2]; exact (cuspChart_CPA2 T i).open_target

/-- The height coordinate of a point of the `i`-th cusp (junk elsewhere). -/
def cuspHeight_CPA2 (i : Fin T.count) (p : H.Carrier) : ℝ :=
  ((cuspChart_CPA2 T i).symm p).2.val 0

theorem cuspHeight_apply_CPA2 (i : Fin T.count) {q : CuspHalfSpace} (hq : 0 < q.2.val 0) :
    cuspHeight_CPA2 T i (T.cuspMap i q) = q.2.val 0 := by
  have hs : q ∈ (cuspChart_CPA2 T i).source := by rw [cuspChart_source_CPA2]; exact hq
  have := (cuspChart_CPA2 T i).left_inv hs
  rw [cuspChart_apply_CPA2] at this
  exact congrArg (fun x : CuspHalfSpace => x.2.val 0) this

theorem contMDiffOn_cuspHeight_CPA2 (i : Fin T.count) :
    ContMDiffOn (𝓡 3) 𝓘(ℝ, ℝ) ∞ (cuspHeight_CPA2 T i) (cuspW_CPA2 T i) := by
  rw [← cuspChart_target_CPA2]
  have h1 : ContMDiffOn (𝓡 3) halfCollarModel ∞ (cuspChart_CPA2 T i).symm
      (cuspChart_CPA2 T i).target := (cuspChart_CPA2 T i).symm.contMDiffOn
  exact (DifferentialGeometry.Topology.Manifold.contMDiff_halfSpaceOneCoordinate.comp contMDiff_snd).comp_contMDiffOn h1

/-- The bump contributed by the `i`-th cusp. -/
def cuspBump_CPA2 (i : Fin T.count) (p : H.Carrier) : ℝ :=
  open Classical in if p ∈ cuspW_CPA2 T i then lam_CPA2 (cuspHeight_CPA2 T i p) else 0

/-- The deepening height function. -/
def deepHeight_CPA2 (b : ℝ) (p : H.Carrier) : ℝ := (∑ i, cuspBump_CPA2 T i p) - b

theorem cuspBump_of_mem_CPA2 {i : Fin T.count} {p : H.Carrier} (hp : p ∈ cuspW_CPA2 T i) :
    cuspBump_CPA2 T i p = lam_CPA2 (cuspHeight_CPA2 T i p) := by
  classical
  simp [cuspBump_CPA2, hp]

theorem cuspBump_of_not_mem_CPA2 {i : Fin T.count} {p : H.Carrier} (hp : p ∉ cuspW_CPA2 T i) :
    cuspBump_CPA2 T i p = 0 := by
  classical
  simp [cuspBump_CPA2, hp]

theorem mem_cuspW_cuspMap_CPA2 (i : Fin T.count) {q : CuspHalfSpace} (hq : 0 < q.2.val 0) :
    T.cuspMap i q ∈ cuspW_CPA2 T i := ⟨q, hq, rfl⟩

theorem cuspBump_cuspMap_CPA2 (i : Fin T.count) {q : CuspHalfSpace} (hq : 0 < q.2.val 0) :
    cuspBump_CPA2 T i (T.cuspMap i q) = lam_CPA2 (q.2.val 0) := by
  rw [cuspBump_of_mem_CPA2 T (mem_cuspW_cuspMap_CPA2 T i hq), cuspHeight_apply_CPA2 T i hq]

theorem not_mem_cuspW_of_ne_CPA2 {i j : Fin T.count} (hij : i ≠ j) {q : CuspHalfSpace} :
    T.cuspMap i q ∉ cuspW_CPA2 T j := by
  rintro ⟨q', -, h⟩
  exact Set.disjoint_left.mp (T.cusp_disjoint hij.symm) ⟨q', h⟩ ⟨q, rfl⟩

theorem sum_cuspBump_cuspMap_CPA2 (i : Fin T.count) {q : CuspHalfSpace} (hq : 0 < q.2.val 0) :
    ∑ j, cuspBump_CPA2 T j (T.cuspMap i q) = lam_CPA2 (q.2.val 0) := by
  rw [Finset.sum_eq_single i]
  · exact cuspBump_cuspMap_CPA2 T i hq
  · intro j _ hji
    exact cuspBump_of_not_mem_CPA2 T (not_mem_cuspW_of_ne_CPA2 T hji.symm)
  · intro h; exact absurd (Finset.mem_univ i) h

theorem sum_cuspBump_of_forall_not_mem_CPA2 {p : H.Carrier} (hp : ∀ i, p ∉ cuspW_CPA2 T i) :
    ∑ j, cuspBump_CPA2 T j p = 0 :=
  Finset.sum_eq_zero fun j _ => cuspBump_of_not_mem_CPA2 T (hp j)

/-- Tails of closed cusp ranges are closed. -/
theorem isClosed_cuspTail_CPA2 (hclosed : ∀ i, IsClosed (range (T.cuspMap i))) (i : Fin T.count)
    (t : ℝ) : IsClosed (T.cuspMap i '' {q : CuspHalfSpace | t ≤ q.2.val 0}) := by
  have hce : Topology.IsClosedEmbedding (T.cuspMap i) :=
    ⟨(T.cuspEmbedding i).isEmbedding, hclosed i⟩
  exact hce.isClosedMap _ (isClosed_le continuous_const
    ((EuclideanSpace.proj 0).continuous.comp (continuous_subtype_val.comp continuous_snd)))

theorem contMDiff_cuspBump_CPA2 (hclosed : ∀ i, IsClosed (range (T.cuspMap i)))
    (i : Fin T.count) : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (cuspBump_CPA2 T i) := by
  intro p
  by_cases hp : p ∈ cuspW_CPA2 T i
  · have h1 : ContMDiffOn (𝓡 3) 𝓘(ℝ, ℝ) ∞ (fun p => lam_CPA2 (cuspHeight_CPA2 T i p))
        (cuspW_CPA2 T i) :=
      contDiff_lam_CPA2.contMDiff.comp_contMDiffOn (contMDiffOn_cuspHeight_CPA2 T i)
    refine (h1.contMDiffAt ((isOpen_cuspW_CPA2 T i).mem_nhds hp)).congr_of_eventuallyEq ?_
    filter_upwards [(isOpen_cuspW_CPA2 T i).mem_nhds hp] with p' hp'
    exact cuspBump_of_mem_CPA2 T hp'
  · have hK := isClosed_cuspTail_CPA2 T hclosed i (1 / 2)
    have hpK : p ∉ T.cuspMap i '' {q : CuspHalfSpace | 1 / 2 ≤ q.2.val 0} := by
      rintro ⟨q, hq, rfl⟩
      exact hp (mem_cuspW_cuspMap_CPA2 T i (lt_of_lt_of_le (by norm_num) hq))
    have hzero : cuspBump_CPA2 T i =ᶠ[𝓝 p] fun _ => (0 : ℝ) := by
      filter_upwards [hK.isOpen_compl.mem_nhds hpK] with p' hp'
      by_cases hw : p' ∈ cuspW_CPA2 T i
      · rw [cuspBump_of_mem_CPA2 T hw]
        obtain ⟨q, hq, rfl⟩ := hw
        rw [cuspHeight_apply_CPA2 T i hq]
        apply lam_zero_CPA2
        by_contra hlt
        exact hp' ⟨q, le_of_lt (not_le.mp hlt), rfl⟩
      · exact cuspBump_of_not_mem_CPA2 T hw
    exact (contMDiffAt_const).congr_of_eventuallyEq hzero

theorem contMDiff_deepHeight_CPA2 (hclosed : ∀ i, IsClosed (range (T.cuspMap i))) (b : ℝ) :
    ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (deepHeight_CPA2 T b) := by
  intro p
  have hs : ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) ∞ (fun p => ∑ i, cuspBump_CPA2 T i p) p :=
    contMDiffAt_finsetSum fun i _ => contMDiff_cuspBump_CPA2 T hclosed i p
  exact hs.sub contMDiffAt_const

end GC.LongTime.CuspP1
