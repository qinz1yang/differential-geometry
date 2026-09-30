import DifferentialGeometry.Topology.Manifold.ChartDisk.Construction

namespace DifferentialGeometry.Topology

open scoped Manifold ContDiff
open Metric Set _root_.Topology

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

theorem exists_chartDisks_and_strip_supported [T2Space M] [IsManifold (𝓡 n) ∞ M]
    (hn : 1 ≤ n) {U : Set M} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ (e₀ e₁ : Disk n → M) (f : M → ℝ),
      isChartDisk e₀ ∧ isChartDisk e₁ ∧ Disjoint (range e₀) (range e₁) ∧
      ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f ∧
      f ⁻¹' Iic (-1/2) = range e₀ ∧ f ⁻¹' Ici (1/2) = range e₁ ∧
      f ⁻¹' Iio (-1/2) = e₀ '' diskInterior n ∧ f ⁻¹' Ioi (1/2) = e₁ '' diskInterior n ∧
      f ⁻¹' {-1/2} = e₀ '' diskSphere n ∧ f ⁻¹' {1/2} = e₁ '' diskSphere n ∧
      (∀ x, f x = -1/2 ∨ f x = 1/2 → ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt (𝓡 n) f x) ∧
      tsupport f ⊆ U ∧ (∀ x, -1 ≤ f x ∧ f x ≤ 1) := by
  obtain ⟨p, hpU⟩ := hne
  set φ := chartAt (EuclideanSpace ℝ (Fin n)) p with hφ_def
  have hφ : φ ∈ atlas (EuclideanSpace ℝ (Fin n)) M := chart_mem_atlas _ p
  obtain ⟨ρ, hρ, hball⟩ :=
    Metric.mem_nhds_iff.1 ((φ.isOpen_inter_preimage_symm hU).mem_nhds
      ⟨mem_chart_target (EuclideanSpace ℝ (Fin n)) p,
        by
          change φ.symm (φ p) ∈ U
          rw [φ.left_inv (mem_chart_source _ p)]
          exact hpU⟩)
  obtain ⟨v, hv⟩ : ∃ v : EuclideanSpace ℝ (Fin n), ‖v‖ = 1 :=
    ⟨EuclideanSpace.single (⟨0, hn⟩ : Fin n) (1 : ℝ), by simp⟩
  set R : ℝ := ρ / 8 with hR_def
  have hR : 0 < R := by positivity
  set c₀ : EuclideanSpace ℝ (Fin n) := φ p + (4 * R) • v with hc₀_def
  set c₁ : EuclideanSpace ℝ (Fin n) := φ p - (4 * R) • v with hc₁_def
  have hsep : ‖c₀ - c₁‖ = 8 * R := by
    have : c₀ - c₁ = (8 * R) • v := by
      rw [hc₀_def, hc₁_def]
      rw [show (8 * R) • v = (4 * R) • v + (4 * R) • v by rw [← add_smul]; ring_nf]
      abel
    rw [this, norm_smul, hv, mul_one, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hsep' : 3 * R ≤ ‖c₀ - c₁‖ := by rw [hsep]; linarith
  have hc₀p : ‖c₀ - φ p‖ = 4 * R := by
    rw [hc₀_def, add_sub_cancel_left, norm_smul, hv, mul_one, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
  have hc₁p : ‖c₁ - φ p‖ = 4 * R := by
    rw [hc₁_def, sub_sub_cancel_left, norm_neg, norm_smul, hv, mul_one, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
  have hlocal : closedBall c₀ (3 / 2 * R) ∪ closedBall c₁ (3 / 2 * R) ⊆
      φ.target ∩ φ.symm ⁻¹' U := by
    intro y hy
    apply hball
    rw [mem_ball_iff_norm]
    rcases hy with hy | hy
    · rw [mem_closedBall_iff_norm] at hy
      have := norm_sub_le_norm_sub_add_norm_sub y c₀ (φ p)
      linarith
    · rw [mem_closedBall_iff_norm] at hy
      have := norm_sub_le_norm_sub_add_norm_sub y c₁ (φ p)
      linarith
  have hsub : closedBall c₀ (3 / 2 * R) ∪ closedBall c₁ (3 / 2 * R) ⊆ φ.target :=
    hlocal.trans inter_subset_left
  have hsub₀ : closedBall c₀ R ⊆ φ.target :=
    (closedBall_subset_closedBall (by linarith)).trans (subset_union_left.trans hsub)
  have hsub₁ : closedBall c₁ R ⊆ φ.target :=
    (closedBall_subset_closedBall (by linarith)).trans (subset_union_right.trans hsub)
  set e₀ : Disk n → M := fun x => φ.symm (c₀ + R • (x : EuclideanSpace ℝ (Fin n))) with he₀_def
  set e₁ : Disk n → M := fun x => φ.symm (c₁ + R • (x : EuclideanSpace ℝ (Fin n))) with he₁_def
  have he₀ : ∀ x : Disk n, e₀ x = φ.symm (c₀ + R • (x : EuclideanSpace ℝ (Fin n))) := fun _ => rfl
  have he₁ : ∀ x : Disk n, e₁ x = φ.symm (c₁ + R • (x : EuclideanSpace ℝ (Fin n))) := fun _ => rfl
  set f := chartTwoBump φ c₀ c₁ R with hf_def
  have hsmooth : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f := chartTwoBump_contMDiff hφ hR hsub
  refine ⟨e₀, e₁, f, ⟨φ, c₀, R, hφ, hR, hsub₀, he₀⟩, ⟨φ, c₁, R, hφ, hR, hsub₁, he₁⟩, ?_,
    hsmooth, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Set.disjoint_left]
    intro x hx₀ hx₁
    rw [mem_range_chartDisk_iff hR hsub₀ he₀] at hx₀
    rw [mem_range_chartDisk_iff hR hsub₁ he₁] at hx₁
    have := norm_sub_le_norm_sub_add_norm_sub c₀ (φ x) c₁
    rw [norm_sub_rev c₀ (φ x), hsep] at this
    linarith [hx₀.2, hx₁.2]
  · ext x
    rw [mem_preimage, mem_Iic, mem_range_chartDisk_iff hR hsub₀ he₀, hf_def,
      chartTwoBump_pred_iff (P := fun t => t ≤ -1/2) (by norm_num),
      twoBump_le_neg_half_iff hR hsep']
  · ext x
    rw [mem_preimage, mem_Ici, mem_range_chartDisk_iff hR hsub₁ he₁, hf_def,
      chartTwoBump_pred_iff (P := fun t => 1/2 ≤ t) (by norm_num),
      half_le_twoBump_iff hR hsep']
  · ext x
    rw [mem_preimage, mem_Iio, mem_image_diskInterior_iff hR hsub₀ he₀, hf_def,
      chartTwoBump_pred_iff (P := fun t => t < -1/2) (by norm_num),
      twoBump_lt_neg_half_iff hR hsep']
  · ext x
    rw [mem_preimage, mem_Ioi, mem_image_diskInterior_iff hR hsub₁ he₁, hf_def,
      chartTwoBump_pred_iff (P := fun t => 1/2 < t) (by norm_num),
      half_lt_twoBump_iff hR hsep']
  · ext x
    rw [mem_preimage, mem_singleton_iff, mem_image_diskSphere_iff hR hsub₀ he₀, hf_def,
      chartTwoBump_pred_iff (P := fun t => t = -1/2) (by norm_num),
      twoBump_eq_neg_half_iff hR hsep']
  · ext x
    rw [mem_preimage, mem_singleton_iff, mem_image_diskSphere_iff hR hsub₁ he₁, hf_def,
      chartTwoBump_pred_iff (P := fun t => t = 1/2) (by norm_num),
      twoBump_eq_half_iff hR hsep']
  · intro x hx
    have hfg : ∀ y ∈ φ.target, f (φ.symm y) = twoBump c₀ c₁ R y := fun y hy =>
      chartTwoBump_symm_apply hy
    rcases hx with hx | hx
    · rw [hf_def, chartTwoBump_pred_iff (P := fun t => t = -1/2) (by norm_num),
        twoBump_eq_neg_half_iff hR hsep'] at hx
      exact not_isCriticalPointAt_of_chart hφ hsmooth hfg hx.1
        (twoBump_not_hasFDerivAt_zero hR hsep' hx.2)
    · rw [hf_def, chartTwoBump_pred_iff (P := fun t => t = 1/2) (by norm_num),
        twoBump_eq_half_iff hR hsep'] at hx
      refine not_isCriticalPointAt_of_chart hφ hsmooth hfg hx.1 ?_
      intro hg
      have hg' : HasFDerivAt (twoBump c₁ c₀ R) (0 : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) (φ x) := by
        have := hg.neg
        rw [neg_zero] at this
        refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
        exact twoBump_swap c₀ c₁ R y
      exact twoBump_not_hasFDerivAt_zero hR (by rwa [norm_sub_rev]) hx.2 hg'
  · apply (closure_minimal (chartTwoBump_support_subset hR)
      (((isCompact_closedBall _ _).union (isCompact_closedBall _ _)).image_of_continuousOn
        (φ.continuousOn_symm.mono hsub)).isClosed).trans
    rintro _ ⟨y, hy, rfl⟩
    exact (hlocal hy).2
  · intro x
    by_cases hx : x ∈ φ.source
    · rw [hf_def, chartTwoBump_apply_of_mem hx]
      have h₀ := diskProfile_nonneg R ‖φ x - c₀‖
      have h₁ := diskProfile_nonneg R ‖φ x - c₁‖
      have h₀' := diskProfile_le_one R ‖φ x - c₀‖
      have h₁' := diskProfile_le_one R ‖φ x - c₁‖
      dsimp [twoBump, radialBump]
      constructor <;> linarith
    · rw [hf_def, chartTwoBump_apply_of_notMem hx]
      norm_num

end DifferentialGeometry.Topology
