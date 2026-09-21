import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Completion
import Mathlib.Topology.UniformSpace.UniformEmbedding
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith

open Set

namespace DifferentialGeometry.Geometry

variable {M : Type*} [PseudoMetricSpace M]

theorem isometry_Icc_of_lipschitzOnWith_of_dist_eq
    {γ : ℝ → M} {a b : ℝ} (hγ : LipschitzOnWith 1 γ (Icc a b))
    (hend : dist (γ a) (γ b) = b - a) :
    Isometry (fun t : Icc a b ↦ γ t) := by
  apply Isometry.of_dist_eq
  intro s t
  suffices h : ∀ s t : Icc a b, (s : ℝ) ≤ t → dist (γ s) (γ t) = (t : ℝ) - s by
    rcases le_total (s : ℝ) t with hst | hts
    · simpa [Subtype.dist_eq, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hst)] using h s t hst
    · rw [dist_comm, h t s hts]
      simp [Subtype.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hts)]
  intro s t hst
  have hab : a ≤ b := s.2.1.trans s.2.2
  have hstUpper := hγ.dist_le_mul (s : ℝ) s.2 t t.2
  have haUpper := hγ.dist_le_mul a ⟨le_rfl, hab⟩ (s : ℝ) s.2
  have hbUpper := hγ.dist_le_mul (t : ℝ) t.2 b ⟨hab, le_rfl⟩
  simp only [NNReal.coe_one, one_mul, Real.dist_eq,
    abs_of_nonpos (sub_nonpos.mpr hst), abs_of_nonpos (sub_nonpos.mpr s.2.1),
    abs_of_nonpos (sub_nonpos.mpr t.2.2)] at hstUpper haUpper hbUpper
  have htri := dist_triangle4 (γ a) (γ s) (γ t) (γ b)
  rw [hend] at htri
  linarith

open Filter UniformSpace in
open scoped Topology in
theorem exists_completion_endpoint_of_isometry
    {a b : ℝ} (hab : a < b)
    {g : Ico a b → M} (hg : Isometry g) :
    ∃ q : Completion M,
      Tendsto (fun t => (g t : Completion M))
        (comap (Subtype.val : Ico a b → ℝ) (𝓝 b)) (𝓝 q) ∧
      ∀ t : Ico a b, dist q (g t : Completion M) = b - t := by
  let l : Filter (Ico a b) := comap Subtype.val (𝓝 b)
  have hmap : NeBot (map (Subtype.val : Ico a b → ℝ) l) := by
    rw [map_comap_setCoe_val]
    exact right_nhdsWithin_Ico_neBot hab
  let _ : NeBot l := hmap.of_map
  have hl : Cauchy l := cauchy_nhds.comap'
    (le_of_eq isUniformEmbedding_subtype_val.isUniformInducing.comap_uniformity) inferInstance
  let G : Ico a b → Completion M := fun t => (g t : Completion M)
  have hG : Isometry G := Completion.coe_isometry.comp hg
  obtain ⟨q, hq⟩ := CompleteSpace.complete (hl.map hG.uniformContinuous)
  have hqT : Tendsto G l (𝓝 q) := hq
  refine ⟨q, hqT, ?_⟩
  intro t
  have hdist := hqT.dist (tendsto_const_nhds (x := G t))
  have hparam : Tendsto (Subtype.val : Ico a b → ℝ) l (𝓝 b) := tendsto_comap
  have hdist' := hparam.dist (tendsto_const_nhds (x := (t : ℝ)))
  have hdist'' : Tendsto (fun s : Ico a b => dist (s : ℝ) (t : ℝ)) l (𝓝 (dist q (G t))) :=
    hdist.congr' (Eventually.of_forall fun s => hG.dist_eq s t)
  rw [tendsto_nhds_unique hdist'' hdist', Real.dist_eq,
    abs_of_nonneg (sub_nonneg.mpr t.property.2.le)]


end DifferentialGeometry.Geometry
