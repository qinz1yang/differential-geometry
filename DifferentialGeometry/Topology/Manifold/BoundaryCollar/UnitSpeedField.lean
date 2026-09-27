import DifferentialGeometry.Topology.Manifold.BoundaryCollar.DefiningFunction
import DifferentialGeometry.Topology.Manifold.BoundaryCollar.InwardField
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

open Set Function Topology Bundle
open scoped Manifold ContDiff
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.Manifold.BoundaryCollar

private theorem contMDiff_mvfderiv_apply_section
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners ℝ E H) [IsManifold I ∞ M]
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    {V : (y : M) → TangentSpace I y}
    (hV : ContMDiff I I.tangent ∞ (fun y => (⟨y, V y⟩ : TangentBundle I M))) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y => mvfderiv I f y (V y)) := by
  have ht := (hf.contMDiff_tangentMap (m := ∞) (by simp)).comp hV
  exact (contMDiff_snd_tangentBundle_modelSpace ℝ 𝓘(ℝ, ℝ)).comp ht

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M]
  [T2Space M] [SigmaCompactSpace M]

theorem exists_smooth_unitSpeed_boundaryField (hK : IsCompact ((𝓡∂ n).boundary M)) :
    ∃ O : TopologicalSpace.Opens M, (𝓡∂ n).boundary M ⊆ O ∧
      ∃ f : M → ℝ, ContMDiff (𝓡∂ n) 𝓘(ℝ, ℝ) ∞ f ∧
        (∀ y, 0 ≤ f y) ∧ (∀ y ∈ O, f y = 0 ↔ (𝓡∂ n).IsBoundaryPoint y) ∧
        ∃ V : (y : M) → TangentSpace (𝓡∂ n) y,
          ContMDiff (𝓡∂ n) (𝓡∂ n).tangent ∞
            (fun y => (⟨y, V y⟩ : TangentBundle (𝓡∂ n) M)) ∧
          IsCompact (tsupport V) ∧
          (∀ y ∈ O, (mfderiv (𝓡∂ n) 𝓘(ℝ, ℝ) f y) (V y) = (1 : ℝ)) ∧
          ∀ y : BoundaryManifold (𝓡∂ n) M,
            0 < (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin n)) (V y) := by
  classical
  obtain ⟨U, hKU, f, hf, hfn, hfzero, hdf⟩ := exists_smooth_boundary_definingFunction hK
  obtain ⟨Y, hY, _, hYpos⟩ := exists_smooth_inwardField hK
  let a : M → ℝ := fun y => mvfderiv (𝓡∂ n) f y (Y y)
  have ha : ContMDiff (𝓡∂ n) 𝓘(ℝ, ℝ) ∞ a := contMDiff_mvfderiv_apply_section (𝓡∂ n) hf hY
  have haK (y : BoundaryManifold (𝓡∂ n) M) : 0 < a y := by
    obtain ⟨c, hc, he⟩ := hdf y y.2
    change 0 < (show ℝ from mfderiv (𝓡∂ n) 𝓘(ℝ, ℝ) f y (Y y))
    erw [he]
    change 0 < c * (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin n)) (Y y)
    exact mul_pos hc (hYpos y).1
  let A : Set M := U ∩ {y | 0 < a y}
  have hA : IsOpen A := U.isOpen.inter (isOpen_lt continuous_const ha.continuous)
  have hKA : (𝓡∂ n).boundary M ⊆ A := fun y hy => ⟨hKU hy, haK ⟨y, hy⟩⟩
  let _ : LocallyCompactSpace (EuclideanHalfSpace n) := (𝓡∂ n).locallyCompactSpace
  let _ : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace (EuclideanHalfSpace n) M
  obtain ⟨W, hW, hKW, hclW, hWc⟩ := exists_open_between_and_isCompact_closure hK hA hKA
  obtain ⟨Q, hQ, hKQ, hclQ, _⟩ := exists_open_between_and_isCompact_closure hK hW hKW
  have hWA : W ⊆ A := subset_closure.trans hclW
  have hQW : Q ⊆ W := subset_closure.trans hclQ
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate (I := 𝓡∂ n)
    (show IsClosed (closure Q) from isClosed_closure) (fun _ : Unit => W) (fun _ => hW) (by
      intro y hy
      exact mem_iUnion.mpr ⟨(), hclQ hy⟩)
  have hρone (y : M) (hy : y ∈ Q) : ρ () y = 1 := by
    simpa only [finsum_eq_sum_of_fintype, Fintype.sum_unique] using ρ.sum_eq_one (subset_closure hy)
  let Z : (y : M) → TangentSpace (𝓡∂ n) y := fun y => (a y)⁻¹ • Y y
  have hZ : ContMDiffOn (𝓡∂ n) (𝓡∂ n).tangent ∞
      (fun y => (⟨y, Z y⟩ : TangentBundle (𝓡∂ n) M)) W := by
    apply ContMDiffOn.smul_section
    · exact ha.contMDiffOn.inv₀ (fun y hy => ne_of_gt (hWA hy).2)
    · exact hY.contMDiffOn
  let V : (y : M) → TangentSpace (𝓡∂ n) y := fun y => ρ () y • Z y
  have hV : ContMDiff (𝓡∂ n) (𝓡∂ n).tangent ∞
      (fun y => (⟨y, V y⟩ : TangentBundle (𝓡∂ n) M)) :=
    ContMDiffOn.smul_section_of_tsupport (ρ ()).contMDiff.contMDiffOn hW (hρ ()) hZ
  have hsupp : Function.support V ⊆ W := by
    intro y hy
    by_contra hn
    apply hy
    change ρ () y • Z y = 0
    rw [image_eq_zero_of_notMem_tsupport (fun hh => hn (hρ () hh)), zero_smul]
  have hunit (y : M) (hy : y ∈ Q) :
      (mfderiv (𝓡∂ n) 𝓘(ℝ, ℝ) f y) (V y) = (1 : ℝ) := by
    let L := mvfderiv (𝓡∂ n) f y
    change L (ρ () y • ((a y)⁻¹ • Y y)) = 1
    rw [hρone y hy, one_smul, map_smul]
    change (a y)⁻¹ * a y = 1
    exact inv_mul_cancel₀ (ne_of_gt (hWA (hQW hy)).2)
  refine ⟨⟨Q, hQ⟩, hKQ, f, hf, hfn,
    (fun y hy => hfzero y (hWA (hQW hy)).1), V, hV,
    hWc.of_isClosed_subset (isClosed_tsupport V) (closure_mono hsupp), hunit, ?_⟩
  intro y
  obtain ⟨c, hc, he⟩ := hdf y y.2
  have hh := hunit y (hKQ y.2)
  erw [he] at hh
  change c * (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin n)) (V y) = 1 at hh
  apply (mul_pos_iff_of_pos_left hc).mp
  rw [hh]
  exact zero_lt_one

end DifferentialGeometry.Manifold.BoundaryCollar
