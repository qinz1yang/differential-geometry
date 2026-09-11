import DifferentialGeometry.Topology.Manifold.BoundaryCollar.Conormal
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

open Set Function Topology
open scoped Manifold ContDiff
set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.Manifold.BoundaryCollar

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M]
  [T2Space M] [SigmaCompactSpace M]

theorem exists_smooth_boundary_definingFunction (hK : IsCompact ((𝓡∂ n).boundary M)) :
    ∃ U : TopologicalSpace.Opens M, (𝓡∂ n).boundary M ⊆ U ∧
      ∃ f : M → ℝ, ContMDiff (𝓡∂ n) 𝓘(ℝ, ℝ) ∞ f ∧
        (∀ y, 0 ≤ f y) ∧
        (∀ y ∈ U, f y = 0 ↔ (𝓡∂ n).IsBoundaryPoint y) ∧
        ∀ y, (𝓡∂ n).IsBoundaryPoint y →
          ∃ c : ℝ, 0 < c ∧ mfderiv (𝓡∂ n) 𝓘(ℝ, ℝ) f y =
            c • EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin n) := by
  classical
  let C : M → Set M := fun p => (chartAt (EuclideanHalfSpace n) p).source
  have hC (p : M) : IsOpen (C p) := (chartAt (EuclideanHalfSpace n) p).open_source
  have hcover : (𝓡∂ n).boundary M ⊆ ⋃ p, C p := by
    intro y _
    exact mem_iUnion.mpr ⟨y, mem_chart_source (EuclideanHalfSpace n) y⟩
  obtain ⟨a, ha⟩ := hK.elim_finite_subcover C hC hcover
  let e : Fin a.card ≃ ↥a := by
    simpa only [Fintype.card_coe] using (Fintype.equivFin ↥a).symm
  let p : Fin a.card → M := fun i => (e i).val
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate (I := 𝓡∂ n)
    hK.isClosed (fun i : Fin a.card => C (p i)) (fun i => hC (p i)) (by
      intro y hy
      obtain ⟨j, hj, hyj⟩ := mem_iUnion₂.mp (ha hy)
      exact mem_iUnion.mpr ⟨e.symm ⟨j, hj⟩, by simpa only [p, Equiv.apply_symm_apply] using hyj⟩)
  let g : Fin a.card → M → ℝ := fun i y => ρ i y * chartHeight (n := n) (p i) y
  have hg (i : Fin a.card) : ContMDiff (𝓡∂ n) 𝓘(ℝ, ℝ) ∞ (g i) := by
    exact ρ.contMDiff_smul (fun y hy =>
      (contMDiffOn_chartHeight (n := n) (k := ∞) (p i)).contMDiffAt
        ((hC (p i)).mem_nhds (hρ i hy)))
  let f : M → ℝ := fun y => ∑ i, g i y
  have hf : ContMDiff (𝓡∂ n) 𝓘(ℝ, ℝ) ∞ f := ContMDiff.sum (fun i _ => hg i)
  have hgn (i : Fin a.card) (y : M) : 0 ≤ g i y :=
    mul_nonneg (ρ.nonneg _ _) (chartHeight_nonneg (n := n) _ _)
  have hfn (y : M) : 0 ≤ f y := Finset.sum_nonneg (fun i _ => hgn i y)
  let U : TopologicalSpace.Opens M :=
    ⟨{y | 0 < ∑ i : Fin a.card, ρ i y}, isOpen_lt continuous_const
      (continuous_finsetSum _ (fun i _ => (ρ i).contMDiff.continuous))⟩
  have hKU : (𝓡∂ n).boundary M ⊆ U := by
    intro y hy
    change 0 < ∑ i : Fin a.card, ρ i y
    have hh := ρ.sum_eq_one hy
    rw [finsum_eq_sum_of_fintype] at hh
    rw [hh]
    exact zero_lt_one
  have hz (y : M) (hy : (𝓡∂ n).IsBoundaryPoint y) : f y = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    change ρ i y * chartHeight (n := n) (p i) y = 0
    by_cases hi : ρ i y = 0
    · rw [hi, zero_mul]
    · rw [(chartHeight_eq_zero_iff (n := n) (p i) (hρ i (subset_tsupport _ hi))).mpr hy,
        mul_zero]
  have hfzero (y : M) (hy : y ∈ U) : f y = 0 ↔ (𝓡∂ n).IsBoundaryPoint y := by
    refine ⟨fun hh => ?_, hz y⟩
    obtain ⟨i, _, hi⟩ := (Finset.sum_pos_iff_of_nonneg
      (fun (i : Fin a.card) _ => ρ.nonneg i y)).mp hy
    have hgi := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hgn i y)).mp hh i
      (Finset.mem_univ i)
    have hheight : chartHeight (n := n) (p i) y = 0 :=
      (mul_eq_zero.mp hgi).resolve_left (ne_of_gt hi)
    exact (chartHeight_eq_zero_iff (n := n) (p i) (hρ i (subset_tsupport _ (ne_of_gt hi)))).mp hheight
  refine ⟨U, hKU, f, hf, hfn, hfzero, ?_⟩
  intro y hy
  let u : TangentSpace (𝓡∂ n) y := EuclideanSpace.single (0 : Fin n) (1 : ℝ)
  have hterm (i : Fin a.card) : mvfderiv (𝓡∂ n) (g i) y u =
      ρ i y * mvfderiv (𝓡∂ n) (chartHeight (n := n) (p i)) y u := by
    by_cases hi : y ∈ tsupport (ρ i)
    · have hheight := (contMDiffOn_chartHeight (n := n) (k := ∞) (p i)).contMDiffAt
        ((hC (p i)).mem_nhds (hρ i hi))
      have hheight0 := (chartHeight_eq_zero_iff (n := n) (p i) (hρ i hi)).mpr hy
      have hh := congrArg (fun L : TangentSpace (𝓡∂ n) y →L[ℝ] ℝ => L u)
        (mvfderiv_fun_mul (((ρ i).contMDiff y).mdifferentiableAt (by simp))
          (hheight.mdifferentiableAt (by simp)))
      simpa only [hheight0, zero_smul, add_zero, smul_apply, smul_eq_mul] using! hh
    · have heq : g i =ᶠ[𝓝 y] fun _ => 0 := by
        filter_upwards [(isClosed_tsupport (ρ i)).isOpen_compl.mem_nhds hi] with z hz
        change ρ i z * chartHeight (n := n) (p i) z = 0
        rw [image_eq_zero_of_notMem_tsupport hz, zero_mul]
      have hg0 : mvfderiv (𝓡∂ n) (g i) y = 0 := by
        unfold mvfderiv
        erw [heq.mfderiv_eq, mfderiv_const]
        exact ContinuousLinearMap.comp_zero _
      rw [hg0, image_eq_zero_of_notMem_tsupport hi, zero_mul]
      rfl
  have hsum : mvfderiv (𝓡∂ n) f y =
      ∑ i : Fin a.card, mvfderiv (𝓡∂ n) (g i) y := by
    have hsumDeriv := HasMFDerivAt.sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin a.card))) =>
      ((hg i y).mdifferentiableAt (by simp)).hasMFDerivAt)
    have heq : (∑ i : Fin a.card, g i) = f := by
      funext z
      simp only [Finset.sum_apply, f]
    rw [heq] at hsumDeriv
    exact hsumDeriv.mfderiv
  have hsum' : mvfderiv (𝓡∂ n) f y u = ∑ i, mvfderiv (𝓡∂ n) (g i) y u := by
    rw [hsum, sum_apply]
  have hheightpos (i : Fin a.card) (hi : 0 < ρ i y) :
      0 < mvfderiv (𝓡∂ n) (chartHeight (n := n) (p i)) y u := by
    obtain ⟨c, hc, he⟩ := mfderiv_chartHeight_eq_pos_smul_proj (n := n) (p i)
      (hρ i (subset_tsupport _ (ne_of_gt hi))) hy
    change 0 < (show ℝ from mfderiv (𝓡∂ n) 𝓘(ℝ, ℝ) (chartHeight (n := n) (p i)) y u)
    erw [he]
    change 0 < c * (EuclideanSpace.single (0 : Fin n) (1 : ℝ)) 0
    simpa using hc
  have hdf : 0 < mvfderiv (𝓡∂ n) f y u := by
    rw [hsum']
    simp_rw [hterm]
    apply Finset.sum_pos'
    · intro i _
      by_cases hi : ρ i y = 0
      · rw [hi, zero_mul]
      · exact mul_nonneg (ρ.nonneg _ _) (hheightpos i (lt_of_le_of_ne (ρ.nonneg i y) (Ne.symm hi))).le
    · obtain ⟨i, hi⟩ := ρ.exists_pos_of_mem hy
      exact ⟨i, Finset.mem_univ _, mul_pos hi (hheightpos i hi)⟩
  apply mfderiv_eq_pos_smul_proj_of_nonneg ((hf y).mdifferentiableAt (by simp))
    hy (hz y hy) (Filter.Eventually.of_forall hfn)
  intro hzero
  change 0 < (show ℝ from mfderiv (𝓡∂ n) 𝓘(ℝ, ℝ) f y u) at hdf
  erw [hzero] at hdf
  exact lt_irrefl (0 : ℝ) hdf

end DifferentialGeometry.Manifold.BoundaryCollar
