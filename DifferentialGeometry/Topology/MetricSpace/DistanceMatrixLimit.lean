import Mathlib.Topology.MetricSpace.Completion
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Sequences

set_option autoImplicit false
open Filter Set
open scoped Topology

namespace Metric

universe u v
variable {L : Type u} [Countable L]
variable {X : ℕ → Type v} [∀ n, PseudoMetricSpace (X n)]

theorem exists_pseudometric_subseq_tendsto_dist (x : ∀ n, L → X n)
    (B : L → L → ℝ) (hB : ∀ n a b, dist (x n a) (x n b) ≤ B a b) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ d : PseudoMetricSpace L,
      ∀ a b, Tendsto (fun n => dist (x (φ n) a) (x (φ n) b)) atTop
        (𝓝 (d.dist a b)) := by
  let I (ab : L × L) := Set.Icc (0 : ℝ) (B ab.1 ab.2)
  have : ∀ ab : L × L, CompactSpace (I ab) :=
    fun _ => isCompact_iff_compactSpace.mp isCompact_Icc
  let z : ℕ → (∀ ab : L × L, I ab) :=
    fun n ab => ⟨dist (x n ab.1) (x n ab.2), dist_nonneg, hB n ab.1 ab.2⟩
  obtain ⟨a, _, φ, hφ, ha⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set (∀ ab : L × L, I ab))).tendsto_subseq
      (x := z) (fun _ => Set.mem_univ _)
  let D : L → L → ℝ := fun p q => (a (p, q)).val
  have hD (p q : L) :
      Tendsto (fun n => dist (x (φ n) p) (x (φ n) q)) atTop (𝓝 (D p q)) := by
    exact (continuous_subtype_val.tendsto (a (p, q))).comp ((tendsto_pi_nhds.mp ha) (p, q))
  have hself (p : L) : D p p = 0 := by
    have h : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 (D p p)) := by
      simpa only [dist_self] using hD p p
    exact tendsto_nhds_unique h tendsto_const_nhds
  have hcomm (p q : L) : D p q = D q p := by
    exact tendsto_nhds_unique (hD p q) (by simpa only [dist_comm] using hD q p)
  have htriangle (p q r : L) : D p r ≤ D p q + D q r := by
    exact le_of_tendsto_of_tendsto (hD p r) ((hD p q).add (hD q r))
      (Eventually.of_forall (fun n => dist_triangle (x (φ n) p) (x (φ n) q) (x (φ n) r)))
  let d : PseudoMetricSpace L :=
    { dist := D, dist_self := hself, dist_comm := hcomm, dist_triangle := htriangle }
  exact ⟨φ, hφ, d, hD⟩

theorem exists_completion_subseq_tendsto_dist (x : ∀ n, L → X n)
    (B : L → L → ℝ) (hB : ∀ n a b, dist (x n a) (x n b) ≤ B a b) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ d : PseudoMetricSpace L,
      letI := d
      DenseRange (fun a : L => (a : UniformSpace.Completion L)) ∧
      ∀ a b, Tendsto (fun n => dist (x (φ n) a) (x (φ n) b)) atTop
        (𝓝 (dist (a : UniformSpace.Completion L) (b : UniformSpace.Completion L))) := by
  obtain ⟨φ, hφ, d, hd⟩ := exists_pseudometric_subseq_tendsto_dist x B hB
  refine ⟨φ, hφ, d, ?_⟩
  let := d
  refine ⟨UniformSpace.Completion.denseRange_coe, ?_⟩
  intro a b
  simpa only [UniformSpace.Completion.dist_eq] using hd a b

omit [Countable L] in
theorem exists_mem_finset_dist_le_of_tendsto {Y : Type*} [PseudoMetricSpace Y]
    (x : ∀ n, L → X n) (z : L → Y) (F : Finset L) (b : L) (η : ℝ)
    (hlim : ∀ a ∈ F, Tendsto (fun n => dist (x n b) (x n a)) atTop
      (𝓝 (dist (z b) (z a))))
    (hnet : ∀ᶠ n in atTop, ∃ a ∈ F, dist (x n b) (x n a) ≤ η) :
    ∃ a ∈ F, dist (z b) (z a) ≤ η := by
  obtain ⟨a, ha, hfreq⟩ :=
    (Filter.frequently_exists_finite F.finite_toSet).mp hnet.frequently
  exact ⟨a, ha, le_of_tendsto_of_frequently (hlim a ha) hfreq⟩

omit [Countable L] in
theorem exists_mem_finset_dist_le_of_denseRange {Y : Type*} [PseudoMetricSpace Y]
    (z : L → Y) (hz : DenseRange z) (F : Finset L) (q : Y) (R η : ℝ)
    (hnet : ∀ b : L, dist (z b) q < R → ∃ a ∈ F, dist (z b) (z a) ≤ η) :
    ∀ y : Y, dist y q < R → ∃ a ∈ F, dist y (z a) ≤ η := by
  have hclosed : IsClosed {y : Y | ∃ a ∈ F, dist y (z a) ≤ η} := by
    have h := isClosed_biUnion_finset
      (s := F) (f := fun a => Metric.closedBall (z a) η)
      (fun _ _ => isClosed_closedBall)
    convert h using 1
    ext y
    simp
  intro y
  exact hz.induction_on y (isClosed_imp isOpen_ball hclosed) hnet

omit [Countable L] in
theorem properSpace_of_finite_nets_at_basepoint {Y : Type*} [PseudoMetricSpace Y]
    [CompleteSpace Y] (z : L → Y) (q : Y)
    (hnet : ∀ R : ℝ, 0 < R → ∀ η : ℝ, 0 < η → ∃ F : Finset L,
      ∀ y : Y, dist y q < R → ∃ a ∈ F, dist y (z a) ≤ η) : ProperSpace Y := by
  refine ⟨fun p r => isCompact_iff_totallyBounded_isComplete.mpr ⟨?_, isClosed_closedBall.isComplete⟩⟩
  rw [Metric.totallyBounded_iff]
  intro ε hε
  obtain ⟨F, hF⟩ := hnet (max 0 (r + dist p q) + 1) (by positivity)
    (ε / 2) (half_pos hε)
  refine ⟨z '' (F : Set L), F.finite_toSet.image z, ?_⟩
  intro y hy
  have hyR : dist y q < max 0 (r + dist p q) + 1 := by
    have htri := dist_triangle y p q
    have hle := le_max_right 0 (r + dist p q)
    change dist y p ≤ r at hy
    linarith
  obtain ⟨a, ha, hya⟩ := hF y hyR
  exact Set.mem_iUnion.mpr ⟨z a, Set.mem_iUnion.mpr
    ⟨⟨a, ha, rfl⟩, by change dist y (z a) < ε; linarith⟩⟩

end Metric
