import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.BufferedCoresEmpty
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TimeSmoothingTheta_CX5

set_option autoImplicit false

/-! # HPS04--05: finite-family choices and one decreasing accuracy

This implements the explicit correction following HPS04: take a maximum of
starting thresholds and a minimum of allowed errors. The harmless extra values
`0` and `1` make both choices valid for the empty family as well. The source
domains are inputs already obtained from an open space-time domain; the
accuracy diagonal does not redefine those domains as moving balls.
-/

noncomputable section
open Set Filter Topology DifferentialGeometry
open DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff

namespace GC.LongTime.Ch12

universe u v

def commonThreshold_CX5 {ι : Type*} [Fintype ι] (T : ι → ℝ) : ℝ := by
  classical
  exact (insert 0 (Finset.univ.image T)).max' (by simp)

def commonTolerance_CX5 {ι : Type*} [Fintype ι] (ε : ι → ℝ) : ℝ := by
  classical
  exact (insert 1 (Finset.univ.image ε)).min' (by simp)

theorem le_commonThreshold_CX5 {ι : Type*} [Fintype ι] (T : ι → ℝ) (i : ι) :
    T i ≤ commonThreshold_CX5 T := by
  classical
  exact Finset.le_max' _ _ (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, by simp, rfl⟩))

theorem commonTolerance_le_CX5 {ι : Type*} [Fintype ι] (ε : ι → ℝ) (i : ι) :
    commonTolerance_CX5 ε ≤ ε i := by
  classical
  exact Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, by simp, rfl⟩))

theorem commonTolerance_pos_CX5 {ι : Type*} [Fintype ι] {ε : ι → ℝ}
    (hε : ∀ i, 0 < ε i) : 0 < commonTolerance_CX5 ε := by
  classical
  have hm : commonTolerance_CX5 ε ∈ insert 1 (Finset.univ.image ε) :=
    Finset.min'_mem _ _
  rcases Finset.mem_insert.mp hm with h | h
  · rw [h]; norm_num
  · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
    rw [← hi]
    exact hε i

/-- Simultaneous finite-family admission, including a genuinely positive common
smallness tolerance. The common starting time is the maximum, not the minimum. -/
theorem finiteWindowChoice_CX5 {ι : Type*} [Fintype ι] (T ε : ι → ℝ)
    (hε : ∀ i, 0 < ε i) :
    0 < commonTolerance_CX5 ε ∧
      ∀ i (t δ : ℝ), commonThreshold_CX5 T ≤ t → δ ≤ commonTolerance_CX5 ε →
        T i ≤ t ∧ δ ≤ ε i :=
  ⟨commonTolerance_pos_CX5 hε, fun i _ _ ht hδ =>
    ⟨(le_commonThreshold_CX5 T i).trans ht, hδ.trans (commonTolerance_le_CX5 ε i)⟩⟩

/-- Direct common speed accuracy from the finitely many H1 isotopy-speed
sequences. The inputs are `η_i(j) → 0`, not a speed estimate with an already
chosen accuracy. Its start is strictly later than the dyadic base time. -/
theorem commonSpeedAccuracy_CX5 {ι : Type*} [Finite ι] {T : ℝ} (hT : 0 < T)
    (B : ℝ) (η : ι → ℕ → ℝ) (hη : ∀ i, Tendsto (η i) atTop (𝓝 0)) :
    ∃ (start : ℝ) (α : ℝ → ℝ), T < start ∧
      (∀ t, start ≤ t → 0 < α t ∧ α t < 1) ∧ AntitoneOn α (Ici start) ∧
      (∀ ε : ℝ, 0 < ε → ∃ S : ℝ, ∀ t : ℝ, S ≤ t → α t < ε) ∧
      ∀ i t, start ≤ t → 4 * B * η i (dyadicIndex_CX5 T t) < α t := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let limits (ε : ℝ) (i : ι) : ℝ :=
    if h : 0 < ε then
      (eventually_dyadic_speed_margin_CX5 hT B (η i) (hη i) (half_pos h)).choose
    else T + 1
  let S (ε : ℝ) := max (T + 1) (commonThreshold_CX5 (limits ε))
  obtain ⟨s, α, _, hpos, hmono, hdec, hpass⟩ := diagonal_accuracy_S11 S
  have hsT : T < s := by
    have hb := (le_max_left (T + 1) _).trans (hpass s le_rfl)
    linarith
  obtain ⟨s1, hs1⟩ := hdec 1 zero_lt_one
  refine ⟨max s s1, α, hsT.trans_le (le_max_left _ _), ?_, ?_, hdec, ?_⟩
  · intro t ht
    exact ⟨hpos t ((le_max_left _ _).trans ht), hs1 t ((le_max_right _ _).trans ht)⟩
  · intro t ht r hr htr
    exact hmono (show s ≤ t from (le_max_left s s1).trans ht)
      (show s ≤ r from (le_max_left s s1).trans hr) htr
  · intro i t ht
    have hst : s ≤ t := (le_max_left _ _).trans ht
    have ha := hpos t hst
    have hi : limits (α t) i ≤ t :=
      (le_commonThreshold_CX5 (limits (α t)) i).trans
        ((le_max_right (T + 1) _).trans (hpass t hst))
    have hb := (eventually_dyadic_speed_margin_CX5 hT B (η i) (hη i) (half_pos ha)).choose_spec.2 t
      (by simpa only [limits, dite_eq_left ha] using hi)
    exact hb.trans (half_lt_self ha)

/-- One positive, decreasing accuracy for a finite family of actual physical
maps and velocity vectors. `error` is the numerical metric-jet error obtained
from the HPS04 pullback calculation; all orders, balls, and tolerances are
explicit. The input is one eventual bound for each *fixed* requested accuracy.
No simultaneous infinite-order bound at one time is assumed. -/
theorem commonAccuracy_physical_CX5
    {P : OrientedThreeStage.{u}} {g : P.Metric} (F : GC.Interface.RawSurgery P g)
    {ι : Type v} [Finite ι] (H : ι → FiniteVolumeHyperbolicModel.{u}) (K : ℕ) (T₀ : ℝ)
    (domain : ∀ i, ℝ → Set (H i).Carrier)
    (f : ∀ i (t : ℝ), T₀ ≤ t → (H i).Carrier → (postStage F.observation t).Carrier)
    (velocity : ∀ i (t : ℝ) (ht : T₀ ≤ t) (p : (H i).Carrier),
      TangentSpace (𝓡 3) (f i t ht p))
    (error : ∀ i, ℝ → ℕ → (H i).Carrier → ℝ)
    (hfinite : ∀ i (ε : ℝ), 0 < ε → ∃ T : ℝ, ∀ (t : ℝ) (hbase : T₀ ≤ t), T ≤ t →
      riemannianBallOf (H i).metric (H i).basepoint (2 * ε⁻¹) ⊆ domain i t ∧
      (∀ k : ℕ, k ≤ max K ⌈ε⁻¹⌉₊ →
        ∀ p ∈ riemannianBallOf (H i).metric (H i).basepoint (2 * ε⁻¹),
          error i t k p < ε / 2) ∧
      (∀ p ∈ riemannianBallOf (H i).metric (H i).basepoint (2 * ε⁻¹),
        (postMetric F.observation t).inner (f i t hbase p) (velocity i t hbase p) (velocity i t hbase p) <
          (ε / 2) ^ 2 / t)) :
    ∃ (start : ℝ) (α : ℝ → ℝ), 0 < start ∧ ∃ hstart : T₀ ≤ start,
      (∀ t, start ≤ t → 0 < α t ∧ α t < 1) ∧ AntitoneOn α (Ici start) ∧
      (∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ t : ℝ, T ≤ t → α t < ε) ∧
      ∀ i t (ht : start ≤ t),
        riemannianBallOf (H i).metric (H i).basepoint (2 * (α t)⁻¹) ⊆ domain i t ∧
        (∀ k : ℕ, k ≤ max K ⌈(α t)⁻¹⌉₊ →
          ∀ p ∈ riemannianBallOf (H i).metric (H i).basepoint (2 * (α t)⁻¹),
            error i t k p < α t) ∧
        (∀ p ∈ riemannianBallOf (H i).metric (H i).basepoint (2 * (α t)⁻¹),
          (postMetric F.observation t).inner (f i t (hstart.trans ht) p)
            (velocity i t (hstart.trans ht) p) (velocity i t (hstart.trans ht) p) <
            α t ^ 2 / t) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let thresholds (ε : ℝ) (i : ι) : ℝ :=
    if h : 0 < ε then (hfinite i ε h).choose else 1
  let T (ε : ℝ) := max T₀ (max 1 (commonThreshold_CX5 (thresholds ε)))
  obtain ⟨s, α, hs, hαpos, hmono, hdec, hpass⟩ := diagonal_accuracy_S11 T
  obtain ⟨s1, hs1⟩ := hdec 1 zero_lt_one
  have hbase : T₀ ≤ max s s1 :=
    ((le_max_left T₀ _).trans (hpass s le_rfl)).trans (le_max_left _ _)
  refine ⟨max s s1, α, hs.trans_le (le_max_left _ _), hbase, ?_, ?_, hdec, ?_⟩
  · intro t ht
    exact ⟨hαpos t ((le_max_left _ _).trans ht), hs1 t ((le_max_right _ _).trans ht)⟩
  · intro t ht r hr htr
    exact hmono (show s ≤ t from (le_max_left s s1).trans ht)
      (show s ≤ r from (le_max_left s s1).trans hr) htr
  · intro i t ht
    have hst : s ≤ t := (le_max_left _ _).trans ht
    have ha := hαpos t hst
    have htpos : 0 < t := hs.trans_le hst
    have hi : thresholds (α t) i ≤ t :=
      (le_commonThreshold_CX5 (thresholds (α t)) i).trans
        ((le_max_right 1 _).trans ((le_max_right T₀ _).trans (hpass t hst)))
    have hbound := (hfinite i (α t) ha).choose_spec t (hbase.trans ht)
      (by simpa only [thresholds, dite_eq_left ha] using hi)
    refine ⟨hbound.1, ?_, ?_⟩
    · intro k hk p hp
      exact (hbound.2.1 k hk p hp).trans (half_lt_self ha)
    · intro p hp
      refine (hbound.2.2 p hp).trans (div_lt_div_of_pos_right ?_ htpos)
      nlinarith [sq_pos_of_pos ha]

end GC.LongTime.Ch12
