import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.BufferedCores

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set
open scoped Manifold ContDiff ENNReal
universe u
namespace GC.LongTime.Ch12

/-- Diagonal helper: from thresholds `T w` build a positive antitone-to-zero `acc` on `[S 0, ∞)`
with `T (acc t) ≤ t` for all `t ≥ S 0`, and `S 0 > 0`. -/
theorem diagonal_accuracy_S11 (T : ℝ → ℝ) :
    ∃ (start : ℝ) (acc : ℝ → ℝ), 0 < start ∧ (∀ t, start ≤ t → 0 < acc t) ∧
      AntitoneOn acc (Ici start) ∧ (∀ ε : ℝ, 0 < ε → ∃ T' : ℝ, ∀ t, T' ≤ t → acc t < ε) ∧
      ∀ t, start ≤ t → T (acc t) ≤ t := by
  classical
  let S : ℕ → ℝ := fun n => (n : ℝ) + 1 + ∑ k ∈ Finset.range (n + 1), |T (1 / ((k : ℝ) + 1))|
  have hSge : ∀ n : ℕ, (n : ℝ) + 1 ≤ S n := fun n => by
    have : 0 ≤ ∑ k ∈ Finset.range (n + 1), |T (1 / ((k : ℝ) + 1))| :=
      Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    simp only [S]; linarith
  have hSmono : Monotone S := by
    intro a b hab
    have h1 : (a : ℝ) ≤ b := by exact_mod_cast hab
    have h2 : ∑ k ∈ Finset.range (a + 1), |T (1 / ((k : ℝ) + 1))| ≤
        ∑ k ∈ Finset.range (b + 1), |T (1 / ((k : ℝ) + 1))| :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
        (fun _ _ _ => abs_nonneg _)
    simp only [S]; linarith
  have hST : ∀ n : ℕ, T (1 / ((n : ℝ) + 1)) ≤ S n := fun n => by
    have : |T (1 / ((n : ℝ) + 1))| ≤ ∑ k ∈ Finset.range (n + 1), |T (1 / ((k : ℝ) + 1))| :=
      Finset.single_le_sum (f := fun k : ℕ => |T (1 / ((k : ℝ) + 1))|)
        (fun _ _ => abs_nonneg _) (Finset.self_mem_range_succ n)
    have h2 := le_abs_self (T (1 / ((n : ℝ) + 1)))
    simp only [S]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  let N : ℝ → ℕ := fun t => Nat.findGreatest (fun n => S n ≤ t) ⌊t⌋₊
  have hN_le : ∀ t, S 0 ≤ t → S (N t) ≤ t := fun t ht =>
    Nat.findGreatest_spec (P := fun n => S n ≤ t) (Nat.zero_le _) ht
  have hN_ge : ∀ t m, S m ≤ t → m ≤ N t := fun t m hm => by
    refine Nat.le_findGreatest ?_ hm
    have : (m : ℝ) ≤ t := by have := hSge m; linarith
    exact Nat.le_floor this
  have hNmono : ∀ s t, s ≤ t → N s ≤ N t := fun s t hst => by
    by_cases h : S 0 ≤ s
    · exact hN_ge t _ ((hN_le s h).trans hst)
    · have : N s = 0 := by
        by_contra hne
        have h1 : S (N s) ≤ s := (Nat.findGreatest_eq_iff.mp rfl).2.1 hne
        exact h (le_trans (hSmono (Nat.zero_le _)) h1)
      omega
  refine ⟨S 0, fun t => 1 / ((N t : ℝ) + 1), ?_, ?_, ?_, ?_, ?_⟩
  · have := hSge 0; simp at this; linarith
  · intro t _; positivity
  · intro s _ t _ hst
    have : (N s : ℝ) ≤ N t := by exact_mod_cast hNmono s t hst
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  · intro ε hε
    obtain ⟨m, hm⟩ := exists_nat_gt (1 / ε)
    refine ⟨S m, fun t ht => ?_⟩
    have h1 : (m : ℝ) ≤ N t := by exact_mod_cast hN_ge t m ht
    have : 1 / ε < (N t : ℝ) + 1 := by linarith
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hε] at this
    linarith
  · intro t ht
    exact (hST (N t)).trans (hN_le t ht)

/-- CH12-R1 §1.1 / D-R1-1: the empty family is a *conditional* inhabitant.  If for every fixed
`w > 0` the `w`-thick part of the normalized slices is eventually empty (the exact negation of the
hypothesis of `thick_covered`), then there are buffered persistent cores with `count = 0`
(accuracy chosen by a diagonal argument). -/
def BufferedPersistentCores.ofEmpty_S11
    {P : OrientedThreeStage.{u}} {g : P.Metric} (F : GC.Interface.RawSurgery P g) (K : ℕ)
    (hempty : ∀ w : ℝ, 0 < w → ∃ T : ℝ, ∀ (t : ℝ) (ht : 0 < t), T ≤ t →
      ∀ (p : (postStage F.observation t).Carrier) (r : ℝ), 0 < r →
        curvatureRadius (scaleMetric t⁻¹ (inv_pos.mpr ht) (postMetric F.observation t)) p =
          ENNReal.ofReal r →
        ENNReal.ofReal (w * r ^ 3) ≤
          ballVolume (scaleMetric t⁻¹ (inv_pos.mpr ht) (postMetric F.observation t)) p r →
        False) :
    BufferedPersistentCores F K :=
  let T : ℝ → ℝ := fun w => if h : 0 < w then Classical.choose (hempty w h) else 0
  let hD := diagonal_accuracy_S11 T
  { count := 0
    model := fun i => i.elim0
    start := Classical.choose hD
    start_pos := (Classical.choose_spec (Classical.choose_spec hD)).1
    accuracy := Classical.choose (Classical.choose_spec hD)
    accuracy_pos := (Classical.choose_spec (Classical.choose_spec hD)).2.1
    accuracy_antitone := (Classical.choose_spec (Classical.choose_spec hD)).2.2.1
    accuracy_decay := (Classical.choose_spec (Classical.choose_spec hD)).2.2.2.1
    domain := fun i => i.elim0
    map := fun i => i.elim0
    smooth := fun i => i.elim0
    embedding := fun i => i.elim0
    advertised_ball := fun i => i.elim0
    exhausts := fun i => i.elim0
    disjoint := fun t ht i => i.elim0
    metric_error := fun i => i.elim0
    thick_covered := by
      intro t ht p r hr hcr hvol
      have hst := (Classical.choose_spec (Classical.choose_spec hD)).2.2.2.2 t ht
      have hpos := (Classical.choose_spec (Classical.choose_spec hD)).2.1 t ht
      have ht0 : 0 < t := (Classical.choose_spec (Classical.choose_spec hD)).1.trans_le ht
      have hT : T (Classical.choose (Classical.choose_spec hD) t) =
          Classical.choose (hempty _ hpos) := by simp [T, hpos]
      have := Classical.choose_spec (hempty _ hpos) t ht0 (hT ▸ hst) p r hr hcr hvol
      exact this.elim
    static_patches := fun i => i.elim0
    buffer_domain := fun i => i.elim0
    buffer_error := fun i => i.elim0 }

theorem BufferedPersistentCores.ofEmpty_count_S11
    {P : OrientedThreeStage.{u}} {g : P.Metric} (F : GC.Interface.RawSurgery P g) (K : ℕ)
    (hempty : ∀ w : ℝ, 0 < w → ∃ T : ℝ, ∀ (t : ℝ) (ht : 0 < t), T ≤ t →
      ∀ (p : (postStage F.observation t).Carrier) (r : ℝ), 0 < r →
        curvatureRadius (scaleMetric t⁻¹ (inv_pos.mpr ht) (postMetric F.observation t)) p =
          ENNReal.ofReal r →
        ENNReal.ofReal (w * r ^ 3) ≤
          ballVolume (scaleMetric t⁻¹ (inv_pos.mpr ht) (postMetric F.observation t)) p r →
        False) :
    (BufferedPersistentCores.ofEmpty_S11 F K hempty).count = 0 := rfl

end GC.LongTime.Ch12
