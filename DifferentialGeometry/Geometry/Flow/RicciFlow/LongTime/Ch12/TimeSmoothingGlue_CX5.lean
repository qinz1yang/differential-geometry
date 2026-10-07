import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TimeSmoothingTheta_CX5
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

set_option autoImplicit false

/-! # H2 gluing in a common unscathed chart

`f j` is the static representative of the actual `f_j(t)` in a common
survivor carrier. Thus equality at the endpoint identifies the same static
curves. Choosing such a carrier and identifying it with the observation tower
are explicit history inputs, not consequences of small endpoint distances.
The source domain `U` is open and independent of any stepwise accuracy function.
-/

noncomputable section
open Set Filter Topology
open scoped Manifold ContDiff

namespace GC.LongTime.Ch12

variable {M N : Type*}

/-- In a fixed survivor chart the static map has no time dependence. -/
def smoothingPiece_CX5 (θ : ℝ → ℝ) (a : ℝ) (f : M → N)
    (E : ℝ × M → M) (q : ℝ × M) : N := f (E (θ (q.1 / a), q.2))

/-- The actual dyadic formula, with a fixed choice of the interval at a seam. -/
def dyadicSmoothing_CX5 (T : ℝ) (θ : ℝ → ℝ) (f : ℕ → M → N)
    (E : ℕ → ℝ × M → M) (q : ℝ × M) : N :=
  let j := dyadicIndex_CX5 T q.1
  smoothingPiece_CX5 θ (dyadicTime_CX5 T j) (f j) (E j) q

theorem dyadicSmoothing_eq_CX5 {T : ℝ} (hT : 0 < T) (θ : ℝ → ℝ)
    (f : ℕ → M → N) (E : ℕ → ℝ × M → M) {j : ℕ} {q : ℝ × M}
    (ht : q.1 ∈ Ico (dyadicTime_CX5 T j) (dyadicTime_CX5 T (j + 1))) :
    dyadicSmoothing_CX5 T θ f E q =
      smoothingPiece_CX5 θ (dyadicTime_CX5 T j) (f j) (E j) q := by
  simp only [dyadicSmoothing_CX5, dyadicIndex_eq_CX5 hT ht]

/-- The entire seam strip is the next static map, not merely a nearby map. -/
theorem dyadicSmoothing_eqOn_seam_CX5 {T : ℝ} (hT : 0 < T) (θ : ℝ → ℝ)
    (hθ0 : ∀ s, s ≤ 7 / 4 → θ s = 0)
    (hθ1 : ∀ s, 15 / 8 ≤ s → θ s = 1)
    (f : ℕ → M → N) (E : ℕ → ℝ × M → M) (U : Set M)
    (hE0 : ∀ j p, p ∈ U → E j (0, p) = p)
    (hjoin : ∀ j p, p ∈ U → f j (E j (1, p)) = f (j + 1) p) (j : ℕ) :
    EqOn (dyadicSmoothing_CX5 T θ f E) (fun q : ℝ × M => f (j + 1) q.2)
      (Ioo ((15 / 8) * dyadicTime_CX5 T j)
        ((7 / 4) * dyadicTime_CX5 T (j + 1)) ×ˢ U) := by
  intro q hq
  have ha := dyadicTime_pos_CX5 hT j
  have hb := dyadicTime_pos_CX5 hT (j + 1)
  by_cases ht : q.1 < dyadicTime_CX5 T (j + 1)
  · rw [dyadicSmoothing_eq_CX5 hT θ f E ⟨by linarith [hq.1.1], ht⟩]
    unfold smoothingPiece_CX5
    rw [hθ1 _ ((le_div_iff₀ ha).mpr (by linarith [hq.1.1]))]
    exact hjoin j q.2 hq.2
  · have ht' : q.1 < dyadicTime_CX5 T (j + 1 + 1) := by
      rw [dyadicTime_succ_CX5]
      linarith [hq.1.2]
    rw [dyadicSmoothing_eq_CX5 hT θ f E ⟨le_of_not_gt ht, ht'⟩]
    unfold smoothingPiece_CX5
    rw [hθ0 _ ((div_le_iff₀ hb).mpr (by linarith [hq.1.2])), hE0 _ _ hq.2]

/-- The entire seam strip is the next static map, not merely a nearby map. -/
theorem dyadicSmoothing_eqOn_seam_of_adjacent_CX5 {T : ℝ} (hT : 0 < T) (θ : ℝ → ℝ)
    (hθ0 : ∀ s, s ≤ 7 / 4 → θ s = 0)
    (hθ1 : ∀ s, 15 / 8 ≤ s → θ s = 1)
    (f : ℕ → M → N) (E : ℕ → ℝ × M → M) (U : Set M) (j : ℕ)
    (hE0 : ∀ p, p ∈ U → E (j + 1) (0, p) = p)
    (hjoin : ∀ p, p ∈ U → f j (E j (1, p)) = f (j + 1) p) :
    EqOn (dyadicSmoothing_CX5 T θ f E) (fun q : ℝ × M => f (j + 1) q.2)
      (Ioo ((15 / 8) * dyadicTime_CX5 T j)
        ((7 / 4) * dyadicTime_CX5 T (j + 1)) ×ˢ U) := by
  intro q hq
  have ha := dyadicTime_pos_CX5 hT j
  have hb := dyadicTime_pos_CX5 hT (j + 1)
  by_cases ht : q.1 < dyadicTime_CX5 T (j + 1)
  · rw [dyadicSmoothing_eq_CX5 hT θ f E ⟨by linarith [hq.1.1], ht⟩]
    unfold smoothingPiece_CX5
    rw [hθ1 _ ((le_div_iff₀ ha).mpr (by linarith [hq.1.1]))]
    exact hjoin q.2 hq.2
  · have ht' : q.1 < dyadicTime_CX5 T (j + 1 + 1) := by
      rw [dyadicTime_succ_CX5]
      linarith [hq.1.2]
    rw [dyadicSmoothing_eq_CX5 hT θ f E ⟨le_of_not_gt ht, ht'⟩]
    unfold smoothingPiece_CX5
    rw [hθ0 _ ((div_le_iff₀ hb).mpr (by linarith [hq.1.2])), hE0 _ hq.2]

/-- The two formulas themselves agree on a space-time neighbourhood of a seam. -/
theorem smoothingPieces_eqOn_seam_CX5 {T : ℝ} (hT : 0 < T) (θ : ℝ → ℝ)
    (hθ0 : ∀ s, s ≤ 7 / 4 → θ s = 0)
    (hθ1 : ∀ s, 15 / 8 ≤ s → θ s = 1)
    (f : ℕ → M → N) (E : ℕ → ℝ × M → M) (U : Set M)
    (hE0 : ∀ j p, p ∈ U → E j (0, p) = p)
    (hjoin : ∀ j p, p ∈ U → f j (E j (1, p)) = f (j + 1) p) (j : ℕ) :
    EqOn (smoothingPiece_CX5 θ (dyadicTime_CX5 T j) (f j) (E j))
      (smoothingPiece_CX5 θ (dyadicTime_CX5 T (j + 1)) (f (j + 1)) (E (j + 1)))
      (Ioo ((15 / 8) * dyadicTime_CX5 T j)
        ((7 / 4) * dyadicTime_CX5 T (j + 1)) ×ˢ U) := by
  intro q hq
  unfold smoothingPiece_CX5
  rw [hθ1 _ ((le_div_iff₀ (dyadicTime_pos_CX5 hT j)).mpr (by linarith [hq.1.1])),
    hθ0 _ ((div_le_iff₀ (dyadicTime_pos_CX5 hT (j + 1))).mpr (by linarith [hq.1.2])),
    hE0 _ _ hq.2, hjoin _ _ hq.2]

section Germ
variable [TopologicalSpace M]

/-- Even at a joining time, the glued map has the germ of its selected formula.
This permits differentiation in any fixed target stage of an actual history. -/
theorem dyadicSmoothing_eventuallyEq_piece_CX5 {T : ℝ} (hT : 0 < T) (θ : ℝ → ℝ)
    (hθ0 : ∀ s, s ≤ 7 / 4 → θ s = 0) (hθ1 : ∀ s, 15 / 8 ≤ s → θ s = 1)
    (f : ℕ → M → N) (E : ℕ → ℝ × M → M) {U : Set M} (hU : IsOpen U)
    (hE0 : ∀ j p, p ∈ U → E j (0, p) = p)
    (hjoin : ∀ j p, p ∈ U → f j (E j (1, p)) = f (j + 1) p)
    {q : ℝ × M} (hq : q ∈ Ioi T ×ˢ U) :
    dyadicSmoothing_CX5 T θ f E =ᶠ[𝓝 q]
      smoothingPiece_CX5 θ (dyadicTime_CX5 T (dyadicIndex_CX5 T q.1))
        (f (dyadicIndex_CX5 T q.1)) (E (dyadicIndex_CX5 T q.1)) := by
  let j := dyadicIndex_CX5 T q.1
  change _ =ᶠ[𝓝 q] smoothingPiece_CX5 θ (dyadicTime_CX5 T j) (f j) (E j)
  have ht := dyadicIndex_mem_CX5 hT hq.1.le
  change q.1 ∈ Ico (dyadicTime_CX5 T j) (dyadicTime_CX5 T (j + 1)) at ht
  by_cases hi : dyadicTime_CX5 T j < q.1
  · filter_upwards [(isOpen_Ioo.prod hU).mem_nhds ⟨⟨hi, ht.2⟩, hq.2⟩] with z hz
    exact dyadicSmoothing_eq_CX5 hT θ f E ⟨hz.1.1.le, hz.1.2⟩
  · have htime : q.1 = dyadicTime_CX5 T j := le_antisymm (le_of_not_gt hi) ht.1
    have hj0 : j ≠ 0 := by
      intro hj0
      simp only [hj0, dyadicTime_zero_CX5] at htime
      exact (ne_of_gt hq.1) htime
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hj0
    have htime' : q.1 = dyadicTime_CX5 T (k + 1) := by simpa only [hk] using htime
    have hb : q ∈ Ioo ((15 / 8) * dyadicTime_CX5 T k)
        ((7 / 4) * dyadicTime_CX5 T (k + 1)) ×ˢ U := by
      refine ⟨?_, hq.2⟩
      rw [htime', dyadicTime_succ_CX5]
      constructor <;> nlinarith [dyadicTime_pos_CX5 hT k]
    filter_upwards [(isOpen_Ioo.prod hU).mem_nhds hb] with z hz
    rw [dyadicSmoothing_eqOn_seam_CX5 hT θ hθ0 hθ1 f E U hE0 hjoin k hz, hk]
    unfold smoothingPiece_CX5
    rw [hθ0 _ ((div_le_iff₀ (dyadicTime_pos_CX5 hT (k + 1))).mpr
      (by linarith [hz.1.2])), hE0 _ _ hz.2]


/-- Local version requiring zero/end matching only for the finitely many
windows meeting the prescribed history box. -/
theorem dyadicSmoothing_eventuallyEq_localPiece_CX5 {T a b : ℝ} (hT : 0 < T)
    (ha : T ≤ a) (θ : ℝ → ℝ)
    (hθ0 : ∀ s, s ≤ 7 / 4 → θ s = 0) (hθ1 : ∀ s, 15 / 8 ≤ s → θ s = 1)
    (f : ℕ → M → N) (E : ℕ → ℝ × M → M) {U : Set M} (hU : IsOpen U)
    (hE0 : ∀ j, dyadicTime_CX5 T j < b → a < dyadicTime_CX5 T (j + 1) →
      ∀ p ∈ U, E j (0, p) = p)
    (hjoin : ∀ j, a < dyadicTime_CX5 T (j + 1) → dyadicTime_CX5 T (j + 1) < b →
      ∀ p ∈ U, f j (E j (1, p)) = f (j + 1) p)
    {q : ℝ × M} (hq : q ∈ Ioo a b ×ˢ U) :
    dyadicSmoothing_CX5 T θ f E =ᶠ[𝓝 q]
      smoothingPiece_CX5 θ (dyadicTime_CX5 T (dyadicIndex_CX5 T q.1))
        (f (dyadicIndex_CX5 T q.1)) (E (dyadicIndex_CX5 T q.1)) := by
  let j := dyadicIndex_CX5 T q.1
  change _ =ᶠ[𝓝 q] smoothingPiece_CX5 θ (dyadicTime_CX5 T j) (f j) (E j)
  have ht := dyadicIndex_mem_CX5 hT (ha.trans hq.1.1.le)
  change q.1 ∈ Ico (dyadicTime_CX5 T j) (dyadicTime_CX5 T (j + 1)) at ht
  by_cases hi : dyadicTime_CX5 T j < q.1
  · filter_upwards [(isOpen_Ioo.prod hU).mem_nhds ⟨⟨hi, ht.2⟩, hq.2⟩] with z hz
    exact dyadicSmoothing_eq_CX5 hT θ f E ⟨hz.1.1.le, hz.1.2⟩
  · have htime : q.1 = dyadicTime_CX5 T j := le_antisymm (le_of_not_gt hi) ht.1
    have hj0 : j ≠ 0 := by
      intro hj0
      simp only [hj0, dyadicTime_zero_CX5] at htime
      exact (not_lt_of_ge ha) (htime ▸ hq.1.1)
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hj0
    have htime' : q.1 = dyadicTime_CX5 T (k + 1) := by simpa only [hk] using htime
    have hleft : a < dyadicTime_CX5 T (k + 1) := hq.1.1.trans_eq htime'
    have hright : dyadicTime_CX5 T (k + 1) < b := htime'.symm.trans_lt hq.1.2
    have hnext : a < dyadicTime_CX5 T (k + 1 + 1) :=
      hleft.trans ((dyadicTime_strictMono_CX5 hT) (Nat.lt_succ_self _))
    have hz := hE0 (k + 1) hright hnext
    have hj := hjoin k hleft hright
    have hb : q ∈ Ioo ((15 / 8) * dyadicTime_CX5 T k)
        ((7 / 4) * dyadicTime_CX5 T (k + 1)) ×ˢ U := by
      refine ⟨?_, hq.2⟩
      rw [htime', dyadicTime_succ_CX5]
      constructor <;> nlinarith [dyadicTime_pos_CX5 hT k]
    filter_upwards [(isOpen_Ioo.prod hU).mem_nhds hb] with z hzbox
    rw [dyadicSmoothing_eqOn_seam_of_adjacent_CX5 hT θ hθ0 hθ1 f E U k hz hj hzbox, hk]
    unfold smoothingPiece_CX5
    rw [hθ0 _ ((div_le_iff₀ (dyadicTime_pos_CX5 hT (k + 1))).mpr
      (by linarith [hzbox.1.2])), hz _ hzbox.2]

end Germ

section Smooth
variable {V W HM HN : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [TopologicalSpace HM] [TopologicalSpace HN]
  {I : ModelWithCorners ℝ V HM} {J : ModelWithCorners ℝ W HN}
  [TopologicalSpace M] [ChartedSpace HM M] [TopologicalSpace N] [ChartedSpace HN N]

theorem contMDiffOn_smoothingPiece_CX5 {θ : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ)
    (hθrange : ∀ s, θ s ∈ Icc (0 : ℝ) 1) (a : ℝ)
    {f : M → N} {E : ℝ × M → M} {U A : Set M}
    (hf : ContMDiffOn I J ∞ f A) (hE : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ E)
    (himage : ∀ μ ∈ Icc (0 : ℝ) 1, ∀ p ∈ U, E (μ, p) ∈ A) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) J ∞ (smoothingPiece_CX5 θ a f E) (univ ×ˢ U) := by
  have hp : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × M => θ (q.1 / a)) :=
    (hθ.comp (contDiff_id.div_const a)).contMDiff.comp contMDiff_fst
  exact hf.comp (hE.comp (hp.prodMk contMDiff_snd)).contMDiffOn
    (fun q hq => himage _ (hθrange _) _ hq.2)

/-- H2's joint smoothness theorem. Only the static maps, the H1 isotopies, their
source-domain inclusion, and their exact endpoint relation are inputs. -/
theorem contMDiffOn_dyadicSmoothing_CX5 {T : ℝ} (hT : 0 < T)
    {θ : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ) (hθrange : ∀ s, θ s ∈ Icc (0 : ℝ) 1)
    (hθ0 : ∀ s, s ≤ 7 / 4 → θ s = 0) (hθ1 : ∀ s, 15 / 8 ≤ s → θ s = 1)
    (f : ℕ → M → N) (E : ℕ → ℝ × M → M) {U : Set M} (hU : IsOpen U)
    (A : ℕ → Set M) (hf : ∀ j, ContMDiffOn I J ∞ (f j) (A j))
    (hE : ∀ j, ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (E j))
    (himage : ∀ j μ, μ ∈ Icc (0 : ℝ) 1 → ∀ p ∈ U, E j (μ, p) ∈ A j)
    (hE0 : ∀ j p, p ∈ U → E j (0, p) = p)
    (hjoin : ∀ j p, p ∈ U → f j (E j (1, p)) = f (j + 1) p) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) J ∞ (dyadicSmoothing_CX5 T θ f E) (Ioi T ×ˢ U) := by
  have hpieces (j : ℕ) := contMDiffOn_smoothingPiece_CX5 hθ hθrange
    (dyadicTime_CX5 T j) (hf j) (hE j) (himage j)
  have hUV (j : ℕ) : U ⊆ A j := by
    intro p hp
    simpa only [hE0 j p hp] using himage j 0 ⟨le_rfl, zero_le_one⟩ p hp
  intro q hq
  let j := dyadicIndex_CX5 T q.1
  have ht := dyadicIndex_mem_CX5 hT hq.1.le
  change q.1 ∈ Ico (dyadicTime_CX5 T j) (dyadicTime_CX5 T (j + 1)) at ht
  by_cases hinside : dyadicTime_CX5 T j < q.1
  · have heq : dyadicSmoothing_CX5 T θ f E =ᶠ[𝓝 q]
        smoothingPiece_CX5 θ (dyadicTime_CX5 T j) (f j) (E j) := by
      filter_upwards [(isOpen_Ioo.prod hU).mem_nhds ⟨⟨hinside, ht.2⟩, hq.2⟩] with z hz
      exact dyadicSmoothing_eq_CX5 hT θ f E ⟨hz.1.1.le, hz.1.2⟩
    exact ((hpieces j).contMDiffAt ((isOpen_univ.prod hU).mem_nhds ⟨mem_univ _, hq.2⟩)
      |>.congr_of_eventuallyEq heq).contMDiffWithinAt
  · have htime : q.1 = dyadicTime_CX5 T j := le_antisymm (le_of_not_gt hinside) ht.1
    have hj0 : j ≠ 0 := by
      intro hj0
      simp only [hj0, dyadicTime_zero_CX5] at htime
      exact (ne_of_gt hq.1) htime
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hj0
    have htime' : q.1 = dyadicTime_CX5 T (k + 1) := by simpa only [hk] using htime
    have hbox : q ∈ Ioo ((15 / 8) * dyadicTime_CX5 T k)
        ((7 / 4) * dyadicTime_CX5 T (k + 1)) ×ˢ U := by
      refine ⟨?_, hq.2⟩
      rw [htime', dyadicTime_succ_CX5]
      constructor <;> nlinarith [dyadicTime_pos_CX5 hT k]
    have heq : dyadicSmoothing_CX5 T θ f E =ᶠ[𝓝 q]
        (fun z : ℝ × M => f (k + 1) z.2) := by
      filter_upwards [(isOpen_Ioo.prod hU).mem_nhds hbox] with z hz
      exact dyadicSmoothing_eqOn_seam_CX5 hT θ hθ0 hθ1 f E U hE0 hjoin k hz
    have hs : ContMDiffAt (𝓘(ℝ, ℝ).prod I) J ∞ (fun z : ℝ × M => f (k + 1) z.2) q :=
      ((hf (k + 1)).mono (hUV (k + 1))).contMDiffAt (hU.mem_nhds hq.2)
        |>.comp q contMDiffAt_snd
    exact (hs.congr_of_eventuallyEq heq).contMDiffWithinAt


/-- Joint smoothing on a finite history window. No smoothness or matching
conditions are imposed on discrete windows disjoint from `(a,b)`. -/
theorem contMDiffOn_windowSmoothing_CX5 {T a b : ℝ} (hT : 0 < T) (ha : T ≤ a)
    {θ : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ) (hθrange : ∀ s, θ s ∈ Icc (0 : ℝ) 1)
    (hθ0 : ∀ s, s ≤ 7 / 4 → θ s = 0) (hθ1 : ∀ s, 15 / 8 ≤ s → θ s = 1)
    (f : ℕ → M → N) (E : ℕ → ℝ × M → M) {U : Set M} (hU : IsOpen U)
    (A : ℕ → Set M)
    (hf : ∀ j, dyadicTime_CX5 T j < b → a < dyadicTime_CX5 T (j + 1) →
      ContMDiffOn I J ∞ (f j) (A j))
    (hE : ∀ j, ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (E j))
    (himage : ∀ j, dyadicTime_CX5 T j < b → a < dyadicTime_CX5 T (j + 1) →
      ∀ μ ∈ Icc (0 : ℝ) 1, ∀ p ∈ U, E j (μ, p) ∈ A j)
    (hE0 : ∀ j, dyadicTime_CX5 T j < b → a < dyadicTime_CX5 T (j + 1) →
      ∀ p ∈ U, E j (0, p) = p)
    (hjoin : ∀ j, a < dyadicTime_CX5 T (j + 1) → dyadicTime_CX5 T (j + 1) < b →
      ∀ p ∈ U, f j (E j (1, p)) = f (j + 1) p) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) J ∞ (dyadicSmoothing_CX5 T θ f E) (Ioo a b ×ˢ U) := by
  intro q hq
  let j := dyadicIndex_CX5 T q.1
  have ht := dyadicIndex_mem_CX5 hT (ha.trans hq.1.1.le)
  have hjb : dyadicTime_CX5 T j < b := ht.1.trans_lt hq.1.2
  have haj : a < dyadicTime_CX5 T (j + 1) := hq.1.1.trans ht.2
  have hpiece := contMDiffOn_smoothingPiece_CX5 hθ hθrange (dyadicTime_CX5 T j)
    (hf j hjb haj) (hE j) (himage j hjb haj)
  have heq := dyadicSmoothing_eventuallyEq_localPiece_CX5 hT ha θ hθ0 hθ1 f E hU hE0 hjoin hq
  exact ((hpiece.contMDiffAt ((isOpen_univ.prod hU).mem_nhds ⟨mem_univ _, hq.2⟩)).congr_of_eventuallyEq heq).contMDiffWithinAt

end Smooth

/-- All time jets match after any fixed coordinate map on the target. This is a
consequence of equality on an open seam interval; no limit of close maps is used. -/
theorem smoothingPieces_timeJets_CX5 {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {T : ℝ} (hT : 0 < T) (θ : ℝ → ℝ)
    (hθ0 : ∀ s, s ≤ 7 / 4 → θ s = 0) (hθ1 : ∀ s, 15 / 8 ≤ s → θ s = 1)
    (f : ℕ → M → N) (E : ℕ → ℝ × M → M) (U : Set M)
    (hE0 : ∀ j p, p ∈ U → E j (0, p) = p)
    (hjoin : ∀ j p, p ∈ U → f j (E j (1, p)) = f (j + 1) p)
    (j : ℕ) (p : M) (hp : p ∈ U) (χ : N → W) (n : ℕ) :
    iteratedDeriv n (fun t => χ (smoothingPiece_CX5 θ (dyadicTime_CX5 T j)
      (f j) (E j) (t, p))) (dyadicTime_CX5 T (j + 1)) =
    iteratedDeriv n (fun t => χ (smoothingPiece_CX5 θ (dyadicTime_CX5 T (j + 1))
      (f (j + 1)) (E (j + 1)) (t, p))) (dyadicTime_CX5 T (j + 1)) := by
  apply Filter.EventuallyEq.iteratedDeriv_eq
  have hleft : (15 / 8) * dyadicTime_CX5 T j < dyadicTime_CX5 T (j + 1) := by
    rw [dyadicTime_succ_CX5]
    nlinarith [dyadicTime_pos_CX5 hT j]
  have hright : dyadicTime_CX5 T (j + 1) < (7 / 4) * dyadicTime_CX5 T (j + 1) := by
    nlinarith [dyadicTime_pos_CX5 hT (j + 1)]
  filter_upwards [Ioo_mem_nhds hleft hright] with t ht
  exact congrArg χ (smoothingPieces_eqOn_seam_CX5 hT θ hθ0 hθ1 f E U hE0 hjoin j ⟨ht, hp⟩)

end GC.LongTime.Ch12
