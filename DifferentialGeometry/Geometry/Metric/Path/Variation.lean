import DifferentialGeometry.Topology.MetricSpace.IntrinsicEDist
import Mathlib.Geometry.Manifold.Riemannian.Basic

set_option autoImplicit false

noncomputable section
open Set Bundle Manifold
open scoped ContDiff Manifold ENNReal

namespace Manifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [PseudoEMetricSpace M] [ChartedSpace H M]
  [RiemannianBundle (TangentSpace I : M → Type _)] [IsRiemannianManifold I M]

theorem eVariationOn_le_pathELength {γ : ℝ → M} {a b : ℝ}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc a b)) :
    eVariationOn γ (Icc a b) ≤ pathELength I γ a b := by
  unfold eVariationOn
  refine iSup_le fun ⟨n, ⟨u, hu, hs⟩⟩ => ?_
  have htele : ∀ k : ℕ, ∑ i ∈ Finset.range k, pathELength I γ (u i) (u (i + 1)) =
      pathELength I γ (u 0) (u k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ih,
        pathELength_add (hu (Nat.zero_le k)) (hu (Nat.le_succ k))]
  calc
    _ ≤ ∑ i ∈ Finset.range n, pathELength I γ (u i) (u (i + 1)) := by
      apply Finset.sum_le_sum
      intro i _
      rw [edist_comm, IsRiemannianManifold.out (I := I)]
      exact riemannianEDist_le_pathELength
        (hγ.mono (Icc_subset_Icc (hs i).1 (hs (i + 1)).2)) rfl rfl (hu (Nat.le_succ i))
    _ = pathELength I γ (u 0) (u n) := htele n
    _ ≤ pathELength I γ a b := pathELength_mono (hs 0).1 (hs n).2

theorem exists_path_eVariationOn_lt_of_riemannianEDist_lt
    {x y : M} {r : ℝ≥0∞} (hr : riemannianEDist I x y < r) :
    ∃ p : Path x y, eVariationOn p univ < r := by
  obtain ⟨γ, hγ0, hγ1, hγ, hlength⟩ := exists_lt_of_riemannianEDist_lt hr
  let p : Path x y := {
    toFun := fun t => γ t
    continuous_toFun := hγ.continuousOn.domRestrict
    source' := hγ0
    target' := hγ1 }
  refine ⟨p, ?_⟩
  have heq : EqOn p.extend γ (Icc (0 : ℝ) 1) := by
    intro t ht
    rw [p.extend_apply ht]
    rfl
  rw [← p.eVariationOn_extend, eVariationOn.congr heq]
  exact (eVariationOn_le_pathELength hγ).trans_lt hlength

theorem intrinsicEDist_eq_riemannianEDist (x y : M) :
    Metric.intrinsicEDist x y = riemannianEDist I x y := by
  apply le_antisymm
  · by_contra h
    obtain ⟨p, hp⟩ := exists_path_eVariationOn_lt_of_riemannianEDist_lt (lt_of_not_ge h)
    exact (not_lt_of_ge (Metric.intrinsicEDist_le_path_variation p)) hp
  · rw [← IsRiemannianManifold.out (I := I)]
    exact Metric.edist_le_intrinsicEDist x y

end Manifold
