import DifferentialGeometry.Topology.LoopSpace.Basic
import DifferentialGeometry.Topology.Manifold.AddCircle
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import DifferentialGeometry.Topology.Manifold.Coincidences

noncomputable section

open Set Manifold
open scoped Topology Manifold

namespace DifferentialGeometry.Topology

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ F H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M]

theorem finite_nonembedding_times_of_compact_transverse_double_points
    (hdim : Module.finrank ℝ F = 3) (γ : ℝ → freeLoop M) {J : Set ℝ}
    {K S : Set (ℝ × loopCircle × loopCircle)} (hK : IsCompact K) (hKS : K ⊆ S)
    (hleft : MDifferentiableOn (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))) I
      (fun p => γ p.1 p.2.1) S)
    (hright : MDifferentiableOn (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))) I
      (fun p => γ p.1 p.2.2) S)
    (hoff : ∀ p ∈ K, p.2.1 ≠ p.2.2)
    (hcover : ∀ t ∈ J, ∀ z w : loopCircle, z ≠ w → γ t z = γ t w →
      (t, z, w) ∈ K)
    (htrans : ∀ p ∈ K, p.2.1 ≠ p.2.2 →
      γ p.1 p.2.1 = γ p.1 p.2.2 →
      Function.Surjective
        ((show (ℝ × ℝ × ℝ) →L[ℝ] F from mfderivWithin (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))) I
          (fun q => γ q.1 q.2.1) S p) -
        (show (ℝ × ℝ × ℝ) →L[ℝ] F from mfderivWithin (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))) I
          (fun q => γ q.1 q.2.2) S p))) :
    {t | t ∈ J ∧ ¬ _root_.Topology.IsEmbedding (γ t)}.Finite := by
  have hdim' : Module.finrank ℝ (ℝ × ℝ × ℝ) = Module.finrank ℝ F := by
    simp [Module.finrank_prod, hdim]
  have hfinite : {p | p ∈ K ∧ γ p.1 p.2.1 =
      γ p.1 p.2.2}.Finite := by
    apply finite_coincidences_of_hasMFDerivWithinAt_sub_injective
      (I := 𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))) (J := I) hK
      (hleft.continuousOn.mono hKS) (hright.continuousOn.mono hKS)
    intro p hp heq
    refine ⟨_, _, ((hleft p (hKS hp)).hasMFDerivWithinAt.mono hKS),
      ((hright p (hKS hp)).hasMFDerivWithinAt.mono hKS), ?_⟩
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim').mpr
      (htrans p hp (hoff p hp) heq)
  apply (hfinite.image Prod.fst).subset
  intro t ht
  have hnotinj : ¬ Function.Injective (γ t) := by
    intro hinj
    exact ht.2 ((γ t).continuous.isClosedEmbedding hinj).isEmbedding
  simp only [Function.Injective, not_forall] at hnotinj
  obtain ⟨z, w, heq, hne⟩ := hnotinj
  exact ⟨(t, z, w), ⟨hcover t ht.1 z w hne heq, heq⟩, rfl⟩

theorem exists_finset_embedding_outside_of_compact_transverse_double_points
    (hdim : Module.finrank ℝ F = 3) (γ : ℝ → freeLoop M) {J : Set ℝ}
    {K S : Set (ℝ × loopCircle × loopCircle)} (hK : IsCompact K) (hKS : K ⊆ S)
    (hleft : MDifferentiableOn (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))) I
      (fun p => γ p.1 p.2.1) S)
    (hright : MDifferentiableOn (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))) I
      (fun p => γ p.1 p.2.2) S)
    (hoff : ∀ p ∈ K, p.2.1 ≠ p.2.2)
    (hcover : ∀ t ∈ J, ∀ z w : loopCircle, z ≠ w → γ t z = γ t w →
      (t, z, w) ∈ K)
    (htrans : ∀ p ∈ K, p.2.1 ≠ p.2.2 →
      γ p.1 p.2.1 = γ p.1 p.2.2 →
      Function.Surjective
        ((show (ℝ × ℝ × ℝ) →L[ℝ] F from mfderivWithin (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))) I
          (fun q => γ q.1 q.2.1) S p) -
        (show (ℝ × ℝ × ℝ) →L[ℝ] F from mfderivWithin (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))) I
          (fun q => γ q.1 q.2.2) S p))) :
    ∃ exceptional : Finset ℝ, ∀ t ∈ J, t ∉ exceptional →
      _root_.Topology.IsEmbedding (γ t) := by
  classical
  have hfinite := finite_nonembedding_times_of_compact_transverse_double_points
    hdim γ hK hKS hleft hright hoff hcover htrans
  refine ⟨hfinite.toFinset, fun t ht hnot => ?_⟩
  by_contra hne
  exact hnot (hfinite.mem_toFinset.mpr ⟨ht, hne⟩)

end DifferentialGeometry.Topology
end

noncomputable section

open Set Manifold
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.Topology

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ F H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M]

theorem exists_finset_embedding_outside_of_compact_transverse_double_points_of_contMDiff
    (hdim : Module.finrank ℝ F = 3) (γ : ℝ → freeLoop M) {J : Set ℝ}
    (hγ : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I 1
      (fun p : ℝ × loopCircle => γ p.1 p.2))
    {K : Set (ℝ × loopCircle × loopCircle)} (hK : IsCompact K)
    (hoff : ∀ p ∈ K, p.2.1 ≠ p.2.2)
    (hcover : ∀ t ∈ J, ∀ z w : loopCircle, z ≠ w → γ t z = γ t w →
      (t, z, w) ∈ K)
    (htrans : ∀ p ∈ K, p.2.1 ≠ p.2.2 → γ p.1 p.2.1 = γ p.1 p.2.2 →
      Function.Surjective
        ((show (ℝ × ℝ × ℝ) →L[ℝ] F from
          mfderiv (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))) I
            (fun q : ℝ × loopCircle × loopCircle => γ q.1 q.2.1) p) -
        (show (ℝ × ℝ × ℝ) →L[ℝ] F from
          mfderiv (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))) I
            (fun q : ℝ × loopCircle × loopCircle => γ q.1 q.2.2) p))) :
    ∃ exceptional : Finset ℝ, ∀ t ∈ J, t ∉ exceptional →
      _root_.Topology.IsEmbedding (γ t) := by
  have hleft : ContMDiff (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))) I 1
      (fun q : ℝ × loopCircle × loopCircle => γ q.1 q.2.1) :=
    hγ.comp (contMDiff_fst.prodMk contMDiff_snd.fst)
  have hright : ContMDiff (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))) I 1
      (fun q : ℝ × loopCircle × loopCircle => γ q.1 q.2.2) :=
    hγ.comp (contMDiff_fst.prodMk contMDiff_snd.snd)
  apply exists_finset_embedding_outside_of_compact_transverse_double_points
    hdim γ hK (subset_univ K)
    (hleft.mdifferentiable (by norm_num)).mdifferentiableOn
    (hright.mdifferentiable (by norm_num)).mdifferentiableOn hoff hcover
  intro p hp hne heq
  simpa only [mfderivWithin_univ] using htrans p hp hne heq

end DifferentialGeometry.Topology
end
