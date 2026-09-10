import DifferentialGeometry.Topology.Manifold.EmbeddedHypersurface.Coorientation
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

open Set DifferentialGeometry.Topology.Morse
open scoped Manifold ContDiff Topology
set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.Manifold.EmbeddedHypersurface

private theorem mvfderiv_finset_sum
    {E H M A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    (J : ModelWithCorners ℝ E H) (s : Finset A) {g : A → M → ℝ} {x : M}
    (hg : ∀ i ∈ s, MDifferentiableAt J 𝓘(ℝ, ℝ) (g i) x) :
    mvfderiv J (fun y => ∑ i ∈ s, g i y) x = ∑ i ∈ s, mvfderiv J (g i) x := by
  classical
  have hdiff (t : Finset A) (ht : ∀ i ∈ t, MDifferentiableAt J 𝓘(ℝ, ℝ) (g i) x) :
      MDifferentiableAt J 𝓘(ℝ, ℝ) (fun y => ∑ i ∈ t, g i y) x := by
    induction t using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using (mdifferentiableAt_const (I := J) (c := (0 : ℝ)))
    | @insert b t hb ih =>
      simp only [Finset.sum_insert hb]
      exact (ht b (Finset.mem_insert_self _ _)).add
        (ih (fun i hi => ht i (Finset.mem_insert_of_mem hi)))
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, mvfderiv_const]
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [mvfderiv_fun_add (hg a (Finset.mem_insert_self _ _))
      (hdiff s (fun i hi => hg i (Finset.mem_insert_of_mem hi))),
      ih (fun i hi => hg i (Finset.mem_insert_of_mem hi))]

variable {m : ℕ} {H G S M : Type*}
  [TopologicalSpace H] [TopologicalSpace G]
  [TopologicalSpace S] [ChartedSpace H S]
  [TopologicalSpace M] [ChartedSpace G M]
  (I : ModelWithCorners ℝ (MorseModel m) H)
  (J : ModelWithCorners ℝ (MorseModel (m + 1)) G)
  [I.Boundaryless] [J.Boundaryless] [IsManifold J ∞ M]
  [T2Space M] [SigmaCompactSpace M]

theorem exists_smooth_function_regular_on_compact_hypersurface {e : S → M}
    (he : Manifold.IsSmoothEmbedding I J ∞ e) (hK : IsCompact (range e))
    (V : ∀ s, TangentSpace J (e s))
    (hV : Continuous (fun s => (⟨e s, V s⟩ : TangentBundle J M)))
    (htrans : ∀ s, V s ∉ (mfderiv I J e s).range) :
    ∃ f : M → ℝ, ContMDiff J 𝓘(ℝ, ℝ) ∞ f ∧ IsCompact (tsupport f) ∧
      (∀ s, f (e s) = 0) ∧
      ∀ s, (0 : ℝ) < (mfderiv J 𝓘(ℝ, ℝ) f (e s)) (V s) := by
  classical
  have hlocal := fun s => exists_positive_local_definingFunction I J he V hV s (htrans s)
  choose U hU hxU f hf hz hr hpos using hlocal
  have hcover : range e ⊆ ⋃ s, U s := by
    rintro _ ⟨s, rfl⟩
    exact mem_iUnion.mpr ⟨s, hxU s⟩
  let _ : LocallyCompactSpace G := J.locallyCompactSpace
  let _ : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace G M
  obtain ⟨W, hW, hKW, hclW, hWc⟩ :=
    exists_open_between_and_isCompact_closure hK (isOpen_iUnion hU) hcover
  let D : S → Set M := fun s => U s ∩ W
  have hD : ∀ s, IsOpen (D s) := fun s => (hU s).inter hW
  have hcoverD : range e ⊆ ⋃ s, D s := by
    rintro _ ⟨s, rfl⟩
    exact mem_iUnion.mpr ⟨s, hxU s, hKW (mem_range_self s)⟩
  obtain ⟨a, ha⟩ := hK.elim_finite_subcover D hD hcoverD
  let A : Type _ := ↥a
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate (I := J)
    hK.isClosed (fun i : A => D i.1) (fun i => hD i.1) (by
      intro y hy
      obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.mp (ha hy)
      exact mem_iUnion.mpr ⟨⟨i, hi⟩, hyi⟩)
  let g : A → M → ℝ := fun i y => ρ i y * f i.1 y
  have hg : ∀ i, ContMDiff J 𝓘(ℝ, ℝ) ∞ (g i) := by
    intro i
    exact ρ.contMDiff_smul (fun y hy =>
      (hf i.1).contMDiffAt ((hU i.1).mem_nhds (hρ i hy).1))
  let F : M → ℝ := fun y => ∑ i : A, g i y
  have hF : ContMDiff J 𝓘(ℝ, ℝ) ∞ F := by
    have hh := ρ.contMDiff_finsum_smul (fun (i : A) y hy =>
      (hf i.1).contMDiffAt ((hU i.1).mem_nhds (hρ i hy).1))
    simpa only [finsum_eq_sum_of_fintype, smul_eq_mul] using hh
  have hzero (i : A) (y : M) (hy : y ∉ D i.1) : ρ i y = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hh => hy (hρ i hh))
  have hsupp : Function.support F ⊆ W := by
    intro y hy
    by_contra hn
    apply hy
    apply Finset.sum_eq_zero
    intro i _
    change ρ i y * f i.1 y = 0
    rw [hzero i y (fun hyD => hn hyD.2), zero_mul]
  refine ⟨F, hF, hWc.of_isClosed_subset (isClosed_tsupport F) (closure_mono hsupp), ?_, ?_⟩
  · intro s
    apply Finset.sum_eq_zero
    intro i _
    change ρ i (e s) * f i.1 (e s) = 0
    by_cases hi : e s ∈ D i.1
    · rw [(hz i.1 _ hi.1).mpr (mem_range_self s), mul_zero]
    · rw [hzero i _ hi, zero_mul]
  · intro s
    have hterm (i : A) : mvfderiv J (g i) (e s) (V s) =
        ρ i (e s) * mvfderiv J (f i.1) (e s) (V s) := by
      by_cases hi : e s ∈ tsupport (ρ i)
      · have hfi := (hf i.1).contMDiffAt ((hU i.1).mem_nhds (hρ i hi).1)
        have hfi0 := (hz i.1 _ (hρ i hi).1).mpr (mem_range_self s)
        have hh := mvfderiv_fun_mul
          (((ρ i).contMDiff (e s)).mdifferentiableAt (by simp)) (hfi.mdifferentiableAt (by simp))
        have hh' := congrArg (fun L : TangentSpace J (e s) →L[ℝ] ℝ => L (V s)) hh
        simpa only [hfi0, zero_smul, add_zero, smul_apply, smul_eq_mul]
          using hh'
      · have heq : g i =ᶠ[𝓝 (e s)] fun _ => 0 := by
          filter_upwards [(isClosed_tsupport (ρ i)).isOpen_compl.mem_nhds hi] with y hy
          change ρ i y * f i.1 y = 0
          rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]
        have hg0 : mvfderiv J (g i) (e s) = 0 := by
          unfold mvfderiv
          erw [heq.mfderiv_eq, mfderiv_const]
          exact ContinuousLinearMap.comp_zero _
        rw [hg0, image_eq_zero_of_notMem_tsupport hi, zero_mul]
        rfl
    have hsum := congrArg (fun L : TangentSpace J (e s) →L[ℝ] ℝ => L (V s))
      (mvfderiv_finset_sum J (Finset.univ : Finset A)
        (fun i _ => ((hg i) (e s)).mdifferentiableAt (by simp)))
    change (0 : ℝ) < mvfderiv J F (e s) (V s)
    change mvfderiv J F (e s) (V s) = (∑ i : A, mvfderiv J (g i) (e s)) (V s) at hsum
    rw [hsum, sum_apply]
    simp_rw [hterm]
    apply Finset.sum_pos'
    · intro i _
      by_cases hi : ρ i (e s) = 0
      · rw [hi, zero_mul]
      · apply mul_nonneg (ρ.nonneg _ _)
        exact (hpos i.1 s (hρ i (subset_tsupport _ hi)).1).le
    · obtain ⟨i, hi⟩ := ρ.exists_pos_of_mem (mem_range_self s)
      exact ⟨i, Finset.mem_univ _, mul_pos hi
        (hpos i.1 s (hρ i (subset_tsupport _ (ne_of_gt hi))).1)⟩

end DifferentialGeometry.Manifold.EmbeddedHypersurface
