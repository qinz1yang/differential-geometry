import DifferentialGeometry.Topology.Manifold.LinearChartSubmanifold

/-!
# Subsets in chart form: every linear chart is in the maximal atlas, smooth maps into the subset

Lane S-EDP-FDC2, group G6 (kernel K0 for FDC03's circle bundle in the ABSTRACT base `W₁`). The
subset `W ⊆ H` of `LinearChartSubmanifold` (charts `κ i`, parametrizations `φ i`, pieces `O i`)
carries the charted space `linearChartedSpace_R74` (one linear chart per point, at a covering
piece chosen once). Here:

* `linearChart_mem_maximalAtlas_EFE`: the linear chart of EVERY index `i` (not only the chosen
  ones) lies in the maximal atlas, so it is a smooth chart (`κ i` read in `W`, inverse `φ i`);
* `contMDiffAt_of_val_EFE`: a map `F : M → W` which is continuous at `x` and whose composite with
  the inclusion `W → H` is smooth at `x` is smooth at `x` (the inclusion is an embedding);
* `contMDiff_of_val_EFE`: the global form;
* `surjective_mfderiv_of_chart_EFE`: if `F : M → W` is smooth, `F x` lies in the piece `O i`, and
  the chart composite `x ↦ κ i (F x)` has surjective differential at `x`, then so does `F`.
-/

set_option autoImplicit false

noncomputable section

open Set Metric
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Topology.Manifold

variable {H E : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedAddCommGroup E]
  [NormedSpace ℝ E] {ι : Type*}

/-- **Every linear chart of a subset in chart form is in the maximal atlas** (the transition maps
`κ j ∘ φ i`, `κ i ∘ φ j` are smooth on the ball). -/
theorem linearChart_mem_maximalAtlas_EFE (W : Set H) (κ : ι → H →L[ℝ] E) (φ : ι → E → H)
    (O : ι → Set H) (r : ℝ) (hO : ∀ i, IsOpen (O i)) (hφs : ∀ i, ContDiffOn ℝ ∞ (φ i) (ball 0 r))
    (hφ : ∀ i, ∀ b ∈ ball (0 : E) r, φ i b ∈ W ∩ O i ∧ κ i (φ i b) = b)
    (hκ : ∀ i, ∀ y ∈ W ∩ O i, κ i y ∈ ball (0 : E) r ∧ φ i (κ i y) = y)
    (hcov : W ⊆ ⋃ i, O i) (i : ι) (y₀ : W) :
    let _ := linearChartedSpace_R74 W κ φ O r hO hφs hφ hκ hcov
    linearChart_R74 W (κ i) (φ i) (O i) r (hO i) (hφs i).continuousOn (hφ i) (hκ i) y₀ ∈
      IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ W := by
  dsimp only
  let _ := linearChartedSpace_R74 W κ φ O r hO hφs hφ hκ hcov
  rw [IsManifold.mem_maximalAtlas_iff]
  intro e' he'
  change e' ∈ range (linearChartAt_R74 W κ φ O r hO hφs hφ hκ hcov) at he'
  obtain ⟨y, rfl⟩ := he'
  have aux : ∀ (j i' : ι) (z y₁ : W),
      ContDiffOn ℝ ∞ (⇑((linearChart_R74 W (κ j) (φ j) (O j) r (hO j) (hφs j).continuousOn
          (hφ j) (hκ j) z).symm ≫ₕ linearChart_R74 W (κ i') (φ i') (O i') r (hO i')
          (hφs i').continuousOn (hφ i') (hκ i') y₁))
        ((linearChart_R74 W (κ j) (φ j) (O j) r (hO j) (hφs j).continuousOn
          (hφ j) (hκ j) z).symm ≫ₕ linearChart_R74 W (κ i') (φ i') (O i') r (hO i')
          (hφs i').continuousOn (hφ i') (hκ i') y₁).source := by
    intro j i' z y₁
    refine ((κ i').contDiff.comp_contDiffOn
      ((hφs j).mono fun b hb => ?_)).congr fun b hb => ?_
    · exact hb.1
    · have hb' : b ∈ ball (0 : E) r := hb.1
      change κ i' (((linearChart_R74 W (κ j) (φ j) (O j) r (hO j) (hφs j).continuousOn
        (hφ j) (hκ j) z).symm b : W) : H) = κ i' (φ j b)
      rw [linearChart_R74_symm_val _ _ _ _ _ _ _ _ _ _ hb']
  have hprop : ∀ (f : OpenPartialHomeomorph E E),
      ContDiffOn ℝ ∞ (⇑f) f.source → (contDiffPregroupoid ∞ 𝓘(ℝ, E)).property f f.source := by
    intro f hf
    change ContDiffOn ℝ ∞ (𝓘(ℝ, E) ∘ f ∘ (𝓘(ℝ, E)).symm) _
    simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.comp_id,
      Function.id_comp, Set.preimage_id, Set.range_id, Set.inter_univ] using hf
  have hmem : ∀ (j i' : ι) (z y₁ : W),
      ((linearChart_R74 W (κ j) (φ j) (O j) r (hO j) (hφs j).continuousOn
          (hφ j) (hκ j) z).symm ≫ₕ linearChart_R74 W (κ i') (φ i') (O i') r (hO i')
          (hφs i').continuousOn (hφ i') (hκ i') y₁) ∈ contDiffGroupoid ∞ 𝓘(ℝ, E) := by
    intro j i' z y₁
    rw [contDiffGroupoid, mem_groupoid_of_pregroupoid]
    refine ⟨hprop _ (aux j i' z y₁), ?_⟩
    have hs : ((linearChart_R74 W (κ j) (φ j) (O j) r (hO j) (hφs j).continuousOn
          (hφ j) (hκ j) z).symm ≫ₕ linearChart_R74 W (κ i') (φ i') (O i') r (hO i')
          (hφs i').continuousOn (hφ i') (hκ i') y₁).symm =
        ((linearChart_R74 W (κ i') (φ i') (O i') r (hO i')
          (hφs i').continuousOn (hφ i') (hκ i') y₁).symm ≫ₕ linearChart_R74 W (κ j) (φ j) (O j)
          r (hO j) (hφs j).continuousOn (hφ j) (hκ j) z) := by
      rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.symm_symm]
    refine hprop _ ?_
    rw [hs]
    exact aux i' j y₁ z
  exact ⟨hmem i _ y₀ y, hmem _ i y y₀⟩

section Maps

variable {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] {HM : Type*}
  [TopologicalSpace HM] {I : ModelWithCorners ℝ EM HM} {M : Type*} [TopologicalSpace M]
  [ChartedSpace HM M]

/-- **A map into a subset in chart form is smooth at `x` when its composite with the inclusion
is** (the inclusion is an embedding; the chart at `F x` is a linear map of the ambient space). -/
theorem contMDiffAt_of_val_EFE (W : Set H) (κ : ι → H →L[ℝ] E) (φ : ι → E → H) (O : ι → Set H)
    (r : ℝ) (hO : ∀ i, IsOpen (O i)) (hφs : ∀ i, ContDiffOn ℝ ∞ (φ i) (ball 0 r))
    (hφ : ∀ i, ∀ b ∈ ball (0 : E) r, φ i b ∈ W ∩ O i ∧ κ i (φ i b) = b)
    (hκ : ∀ i, ∀ y ∈ W ∩ O i, κ i y ∈ ball (0 : E) r ∧ φ i (κ i y) = y)
    (hcov : W ⊆ ⋃ i, O i) (F : M → W) (x : M) (hc : ContinuousAt F x)
    (hF : ContMDiffAt I 𝓘(ℝ, H) ∞ (fun z => (F z : H)) x) :
    let _ := linearChartedSpace_R74 W κ φ O r hO hφs hφ hκ hcov
    ContMDiffAt I 𝓘(ℝ, E) ∞ F x := by
  dsimp only
  let _ := linearChartedSpace_R74 W κ φ O r hO hφs hφ hκ hcov
  rw [contMDiffAt_iff_target]
  refine ⟨hc, ?_⟩
  have h1 : ContMDiffAt I 𝓘(ℝ, E) ∞
      (fun z => κ (linearChartIdx_R74 W O hcov (F x)) (F z : H)) x :=
    ((κ (linearChartIdx_R74 W O hcov (F x))).contDiff.contMDiff.contMDiffAt).comp x hF
  exact h1

/-- **The global form of `contMDiffAt_of_val_EFE`.** -/
theorem contMDiff_of_val_EFE (W : Set H) (κ : ι → H →L[ℝ] E) (φ : ι → E → H) (O : ι → Set H)
    (r : ℝ) (hO : ∀ i, IsOpen (O i)) (hφs : ∀ i, ContDiffOn ℝ ∞ (φ i) (ball 0 r))
    (hφ : ∀ i, ∀ b ∈ ball (0 : E) r, φ i b ∈ W ∩ O i ∧ κ i (φ i b) = b)
    (hκ : ∀ i, ∀ y ∈ W ∩ O i, κ i y ∈ ball (0 : E) r ∧ φ i (κ i y) = y)
    (hcov : W ⊆ ⋃ i, O i) (F : M → W) (hF : ContMDiff I 𝓘(ℝ, H) ∞ (fun z => (F z : H))) :
    let _ := linearChartedSpace_R74 W κ φ O r hO hφs hφ hκ hcov
    ContMDiff I 𝓘(ℝ, E) ∞ F := by
  dsimp only
  let _ := linearChartedSpace_R74 W κ φ O r hO hφs hφ hκ hcov
  have hc : Continuous F :=
    Topology.IsInducing.subtypeVal.continuous_iff.mpr hF.continuous
  exact fun x => contMDiffAt_of_val_EFE W κ φ O r hO hφs hφ hκ hcov F x hc.continuousAt (hF x)

/-- **Surjective differential through a linear chart**: if `F : M → W` is smooth, `F x` lies in
the piece `O i`, and the chart composite `z ↦ κ i (F z)` has surjective differential at `x`, then
`F` has surjective differential at `x` (the chart is a diffeomorphism near `F x`). -/
theorem surjective_mfderiv_of_chart_EFE (W : Set H) (κ : ι → H →L[ℝ] E) (φ : ι → E → H)
    (O : ι → Set H) (r : ℝ) (hO : ∀ i, IsOpen (O i)) (hφs : ∀ i, ContDiffOn ℝ ∞ (φ i) (ball 0 r))
    (hφ : ∀ i, ∀ b ∈ ball (0 : E) r, φ i b ∈ W ∩ O i ∧ κ i (φ i b) = b)
    (hκ : ∀ i, ∀ y ∈ W ∩ O i, κ i y ∈ ball (0 : E) r ∧ φ i (κ i y) = y)
    (hcov : W ⊆ ⋃ i, O i) (F : M → W) (x : M) (i : ι) (hx : (F x : H) ∈ O i)
    (hFs : let _ := linearChartedSpace_R74 W κ φ O r hO hφs hφ hκ hcov
      ContMDiffAt I 𝓘(ℝ, E) ∞ F x)
    (hsur : Function.Surjective (mfderiv I 𝓘(ℝ, E) (fun z => κ i (F z : H)) x)) :
    let _ := linearChartedSpace_R74 W κ φ O r hO hφs hφ hκ hcov
    Function.Surjective (mfderiv I 𝓘(ℝ, E) F x) := by
  dsimp only at hFs ⊢
  let _ := linearChartedSpace_R74 W κ φ O r hO hφs hφ hκ hcov
  let _ : IsManifold 𝓘(ℝ, E) ∞ W := linearIsManifold_R74 W κ φ O r hO hφs hφ hκ hcov
  let c := linearChart_R74 W (κ i) (φ i) (O i) r (hO i) (hφs i).continuousOn (hφ i) (hκ i) (F x)
  have hmax := linearChart_mem_maximalAtlas_EFE W κ φ O r hO hφs hφ hκ hcov i (F x)
  dsimp only at hmax
  have hcd : c.MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) :=
    ⟨(contMDiffOn_of_mem_maximalAtlas hmax).mdifferentiableOn (by simp),
      (contMDiffOn_symm_of_mem_maximalAtlas hmax).mdifferentiableOn (by simp)⟩
  have hxs : F x ∈ c.source := hx
  have hbij := hcd.mfderiv_bijective hxs
  have hcF : (fun z => κ i (F z : H)) = c ∘ F := rfl
  have hdc : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) c (F x) := hcd.mdifferentiableAt hxs
  have hd : mfderiv I 𝓘(ℝ, E) (c ∘ F) x =
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c (F x)).comp (mfderiv I 𝓘(ℝ, E) F x) :=
    mfderiv_comp x hdc (hFs.mdifferentiableAt (by simp))
  rw [hcF, hd] at hsur
  intro t
  obtain ⟨u, hu⟩ := hsur (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c (F x) t)
  exact ⟨u, hbij.1 hu⟩

end Maps

end DifferentialGeometry.Topology.Manifold
