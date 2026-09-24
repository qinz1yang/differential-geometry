import DifferentialGeometry.Geometry.Comparison.Variation.Field.Smoothness


noncomputable section

namespace DifferentialGeometry.Geometry.Riemannian.Variation

open Bundle Manifold
open scoped ContDiff Manifold Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

theorem varField_contMDiff
    {m n : ℕ∞ω} (f : ℝ → ℝ → M)
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I n
      (fun p : ℝ × ℝ ↦ f p.1 p.2)) (hmn : m + 1 ≤ n) :
    ContMDiff 𝓘(ℝ, ℝ) I.tangent m
      (fun t ↦ (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
        (f 0 t) (mfderiv 𝓘(ℝ, ℝ) I (fun u ↦ f u t) 0 (1 : ℝ)) :
          TangentBundle I M)) := by
  have hf' : ContMDiff 𝓘(ℝ, ℝ × ℝ) I n (fun p : ℝ × ℝ ↦ f p.1 p.2) := by
    rwa [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  have hn : (1 : ℕ∞ω) ≤ n :=
    (le_add_of_nonneg_left (show (0 : ℕ∞ω) ≤ m from zero_le)).trans hmn
  have hn0 : n ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hn)
  have hunit : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ).tangent m
      (fun t : ℝ ↦ (TotalSpace.mk' (ℝ × ℝ)
        (E := (TangentSpace 𝓘(ℝ, ℝ × ℝ) : (ℝ × ℝ) → Type _))
        (0, t) (1, 0) : TangentBundle 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ))) := by
    intro t
    rw [Bundle.contMDiffAt_totalSpace]
    have hbase : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ) m
        (fun t : ℝ ↦ ((0 : ℝ), t)) :=
      (contDiff_const.prodMk contDiff_id).contMDiff
    refine ⟨hbase t, ?_⟩
    simpa only [trivializationAt_model_space_apply] using
      (contMDiffAt_const (c := ((1, 0) : ℝ × ℝ)))
  have hfield (t : ℝ) :
      (mfderiv 𝓘(ℝ, ℝ) I (fun u ↦ f u t) 0 (1 : ℝ) : E) =
        mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun p : ℝ × ℝ ↦ f p.1 p.2)
          (0, t) (1, 0) := by
    have hinc : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ) ∞
        (fun u : ℝ ↦ (u, t)) :=
      (contDiff_id.prodMk contDiff_const).contMDiff
    have hc := mfderiv_comp (0 : ℝ) (hf'.mdifferentiable hn0 (0, t))
      (hinc.mdifferentiable (by simp) 0)
    have hd : fderiv ℝ (fun u : ℝ ↦ (u, t)) 0 =
        ContinuousLinearMap.inl ℝ ℝ ℝ :=
      (hasFDerivAt_prodMk_left (0 : ℝ) t).fderiv
    rw [mfderiv_eq_fderiv, hd] at hc
    exact congrArg (fun A ↦ A (1 : ℝ)) hc
  have heq :
      (fun t ↦ (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
        (f 0 t) (mfderiv 𝓘(ℝ, ℝ) I (fun u ↦ f u t) 0 (1 : ℝ)) :
          TangentBundle I M)) =
      tangentMap 𝓘(ℝ, ℝ × ℝ) I (fun p : ℝ × ℝ ↦ f p.1 p.2) ∘
        (fun t : ℝ ↦ (TotalSpace.mk' (ℝ × ℝ)
          (E := (TangentSpace 𝓘(ℝ, ℝ × ℝ) : (ℝ × ℝ) → Type _))
          (0, t) (1, 0) : TangentBundle 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ))) := by
    funext t
    apply TotalSpace.ext
    · rfl
    · exact heq_of_eq (hfield t)
  rw [heq]
  exact (hf'.contMDiff_tangentMap hmn).comp hunit

theorem IsSmoothVariation.varField_contMDiff
    {f : ℝ → ℝ → M} (hf : IsSmoothVariation (I := I) f)
    {m : ℕ∞ω} (hm : m ≤ 7) :
    ContMDiff 𝓘(ℝ, ℝ) I.tangent m
      (fun t ↦ (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
        (f 0 t) (mfderiv 𝓘(ℝ, ℝ) I (fun u ↦ f u t) 0 (1 : ℝ)) :
          TangentBundle I M)) := by
  have hmn : m + 1 ≤ (8 : ℕ∞ω) := by
    calc
      m + 1 ≤ 7 + 1 := by
        simpa only [add_comm] using (_root_.add_le_add_right hm 1)
      _ = 8 := by norm_num
  exact DifferentialGeometry.Geometry.Riemannian.Variation.varField_contMDiff
    (n := 8) f hf hmn

end DifferentialGeometry.Geometry.Riemannian.Variation

end
