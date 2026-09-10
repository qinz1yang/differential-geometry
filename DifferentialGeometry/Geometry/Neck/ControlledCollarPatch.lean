import DifferentialGeometry.Geometry.Neck.CollarPartition
import DifferentialGeometry.Geometry.Neck.CollarPatch
import DifferentialGeometry.Geometry.Neck.ScaleComparison
import DifferentialGeometry.Analysis.ODE.Flow.Planar.CollarScaleEstimate

noncomputable section
open Set Bundle Topology
open scoped Manifold ContDiff BigOperators
open DifferentialGeometry DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open Poincare.Geometry.Affine Poincare.Topology.Manifold

namespace Poincare.Geometry.Neck

private instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
local notation "S²" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

private theorem abs_mvfderiv_affine_sign
    {E H W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace W] [ChartedSpace H W]
    (f : W → ℝ) (w : W) (hf : MDifferentiableAt I 𝓘(ℝ) f w)
    (σ c : ℝ) (hσ : σ = 1 ∨ σ = -1) (z : TangentSpace I w) :
    |mvfderiv I (fun y ↦ σ * f y + c) w z| = |mvfderiv I f w z| := by
  have hm : MDifferentiableAt I 𝓘(ℝ) (fun y : W ↦ σ * f y) w :=
    mdifferentiableAt_const.mul hf
  rw [mvfderiv_fun_add hm mdifferentiableAt_const,
    mvfderiv_fun_mul mdifferentiableAt_const hf, mvfderiv_const, mvfderiv_const]
  simp only [add_apply, smul_apply, smul_eq_mul, zero_apply, mul_zero, add_zero, abs_mul]
  rcases hσ with rfl | rfl <;> norm_num

theorem exists_regular_patch_of_controlled_collar_regions (Cₒ : ℝ) (hCₒ : 0 < Cₒ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀
    {E H W F G M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace W] [ChartedSpace H W] [HasSmoothBoundary E H I]
    [IsManifold I ∞ W] [T2Space W]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace G] (J : ModelWithCorners ℝ F G)
    [TopologicalSpace M] [ChartedSpace G M] [IsManifold J ∞ M] [T2Space M]
    [BoundarylessManifold J M],
    ∀ (n : ℕ) (ι : W → M), ContMDiff I J ∞ ι →
    IsEmbedding ι → (∀ w, Function.Injective (mfderiv I J ι w)) →
    Module.finrank ℝ E = Module.finrank ℝ F →
    ∀ (g : SmoothRiemannianMetric J M) (C : Fin (n + 1) → cylindricalChart J (M := M))
      (U : ∀ i, Set (C i).domain), (∀ i, IsOpen (U i)) →
    ∀ ε : ℝ, 0 ≤ ε → ε < ε₀ → (∀ i, (C i).metricCloseOn g ε (U i)) →
    ∀ (s c : Fin n → ℝ), (∀ j, s j = 1 ∨ s j = -1) →
    let a := finiteLineAffineAlignment s c
    let v : Fin (n + 1) → W → ℝ := fun i w ↦ (a i).1 * (C i).axial (ι w) + (a i).2
    let V : Fin (n + 1) → Set W := fun i ↦ ι ⁻¹' (C i).region (U i)
    ∀ (k : Fin n → Fin (n + 1)), (∀ j, k j = j.castSucc ∨ k j = j.succ) →
    ∀ (l r : Fin n → ℝ) (hwidth : ∀ j, 1 ≤ r j - l j),
    ∀ hcollar : ∀ j p t, t ∈ Icc (l j) (r j) → (p, (a (k j)).1 * t) ∈ (C (k j)).domain,
    let e := fun j (x : S² × Icc (l j) (r j)) ↦
      ((C (k j)).chart ⟨(x.1, (a (k j)).1 * (x.2 : ℝ)), hcollar j x.1 x.2 x.2.property⟩ : M)
    (∀ j x, e j x ∈ interior (range ι)) →
    ∀ P Q : Fin n → Set W,
    (∀ j, IsClosed (P j)) → (∀ j, IsClosed (Q j)) → (∀ j, Disjoint (P j) (Q j)) →
    (∀ j, P j ∪ ι ⁻¹' range (e j) ∪ Q j = univ) →
    (∀ j, P j ∩ ι ⁻¹' range (e j) ⊆
      ι ⁻¹' range (fun p : S² ↦ e j (p, ⟨l j, le_rfl, by linarith only [hwidth j]⟩))) →
    (∀ j, Q j ∩ ι ⁻¹' range (e j) ⊆
      ι ⁻¹' range (fun p : S² ↦ e j (p, ⟨r j, by linarith only [hwidth j], le_rfl⟩))) →
    (∀ i j, i < j → interior (Q i) ∪ interior (P j) = univ) →
    (∀ i w, (∀ j : Fin n, i = j.castSucc → w ∉ interior (Q j)) →
      (∀ j : Fin n, i = j.succ → w ∉ interior (P j)) → w ∈ V i) →
    (∀ j, ι ⁻¹' range (e j) ⊆ V j.castSucc ∩ V j.succ) →
    (∀ j, ∀ w ∈ ι ⁻¹' range (e j), |(C j.succ).axial (ι w) -
      (s j * (C j.castSucc).axial (ι w) + c j)| ≤ Cₒ * ε / Real.sqrt (C j.castSucc).scale) →
    (∀ j, ∀ w ∈ ι ⁻¹' range (e j),
      Real.sqrt (g.inner (ι w)
        (gradFun g (C j.succ).axial (ι w) - s j • gradFun g (C j.castSucc).axial (ι w))
        (gradFun g (C j.succ).axial (ι w) - s j • gradFun g (C j.castSucc).axial (ι w))) ≤ Cₒ * ε) →
    ∃ (θ : Fin (n + 2) → C^∞⟮I, W; 𝓘(ℝ), ℝ⟯)
      (horder : ∀ w, Antitone (fun i ↦ θ i w))
      (hfirst : ∀ w, θ 0 w = 1) (hlast : ∀ w, θ (Fin.last (n + 1)) w = 0),
      (∀ j, ∀ w ∈ P j, θ j.succ.castSucc w = 0) ∧
      (∀ j, ∀ w ∈ Q j, θ j.succ.castSucc w = 1) ∧
      let χ := orderedStepPartition θ horder hfirst hlast
      (∀ i, tsupport (χ i) ⊆ V i) ∧
      let u := fun w ↦ ∑ i, χ i w * v i w
      ContMDiff I 𝓘(ℝ) ∞ u ∧ ∀ w, mvfderiv I u w ≠ 0 := by
  classical
  obtain ⟨A, hA, hpartition⟩ := exists_uniform_partition_of_signed_neck_collars
  let C₁ := max Cₒ 17292
  have hC₁ : 0 < C₁ := hCₒ.trans_le (le_max_left _ _)
  obtain ⟨ε₀, hε₀, hthreshold⟩ := Poincare.Analysis.exists_uniform_collar_error_threshold A C₁ hA hC₁
  refine ⟨ε₀, hε₀, ?_⟩
  intro E H W F G M _ _ _ _ I _ _ _ _ _ _ _ _ _ J _ _ _ _ _
  specialize hpartition (W := W) (M := M) I J
  intro n ι hι hemb hfull hdim g C U hU ε hεnonneg hε hmetric s c hs
    a v V k hk l r hwidth hcollar e hinternal P Q hP hQ hPQ hcover hleft hright hsep
    hcontrolled hKV hvalue hgradient
  obtain ⟨heps, hsmallGradient, _, B, hB, hBsmall, hscale⟩ := hthreshold ε hεnonneg hε
  have hlr (j) : l j < r j := by linarith only [hwidth j]
  have herror : Cₒ * ε ≤ C₁ * ε := mul_le_mul_of_nonneg_right (le_max_left _ _) hεnonneg
  have hratio (j : Fin n) : |(C j.castSucc).scale / (C j.succ).scale - 1| ≤ C₁ * ε := by
    let p : S² := ⟨EuclideanSpace.single 0 1, by simp⟩
    let x : S² × Icc (l j) (r j) := (p, ⟨l j, le_rfl, (hlr j).le⟩)
    obtain ⟨w, hw⟩ := interior_subset (hinternal j x)
    have hwK : w ∈ ι ⁻¹' range (e j) := ⟨x, hw.symm⟩
    have hboth := hKV j hwK
    exact ((C j.castSucc).scale_ratio_of_metricCloseOn (C j.succ) g ε heps
      (hmetric j.castSucc) (hmetric j.succ) (ι w) hboth.1 hboth.2).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) hεnonneg)
  let t₀ : Fin n → ℝ := fun j ↦ l j + (r j - l j) / 4
  let t₁ : Fin n → ℝ := fun j ↦ r j - (r j - l j) / 4
  have ht₀ (j) : l j < t₀ j := by dsimp [t₀]; linarith only [hwidth j]
  have ht (j) : t₀ j < t₁ j := by dsimp [t₀, t₁]; linarith only [hwidth j]
  have ht₁ (j) : t₁ j < r j := by dsimp [t₁]; linarith only [hwidth j]
  have hhalf (j) : 1 / 2 ≤ t₁ j - t₀ j := by dsimp [t₀, t₁]; linarith only [hwidth j]
  obtain ⟨β, θ, _, hlocal, horder, hfirst, hlast, hdisj, hinter, hnonadj, hwedge, hactive⟩ :=
    hpartition ι hι hemb hfull hdim n (fun j ↦ C (k j)) (fun j ↦ (a (k j)).1)
      (fun j ↦ finiteLineAffineAlignment_sign s c hs (k j)) l r hlr hcollar hinternal
      P Q hP hQ hPQ hcover hleft hright hsep t₀ t₁ ht₀ ht ht₁
  let χ := orderedStepPartition θ horder hfirst hlast
  let K : Fin n → Set W := fun j ↦ ι ⁻¹' (e j '' {x | t₀ j ≤ (x.2 : ℝ) ∧ (x.2 : ℝ) ≤ t₁ j})
  have hK (j) : K j ⊆ ι ⁻¹' range (e j) := by
    rintro w ⟨x, _, hx⟩
    exact ⟨x, hx⟩
  have hsupp (i) : tsupport (χ i) ⊆ V i := by
    intro w hw
    apply hcontrolled i w
    · intro j hij
      subst i
      exact (hwedge j).1 hw
    · intro j hij
      subst i
      exact (hwedge j).2 hw
  have hsurj (w : W) : Function.Surjective (mfderiv I J ι w) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim
      (f := (mfderiv I J ι w).toLinearMap)).mp (hfull w)
  let D : Fin n → ℝ := fun j ↦ (A / (t₁ j - t₀ j)) * Real.sqrt (C (k j)).scale
  have hD (j) : 0 ≤ D j := mul_nonneg (div_nonneg hA.le (sub_pos.mpr (ht j)).le) (Real.sqrt_nonneg _)
  have hphysical (i) {w : W} (hw : w ∈ V i) :
      MDifferentiableAt I 𝓘(ℝ) ((C i).axial ∘ ι) w := by
    obtain ⟨ν, Y, hax, _⟩ := (C i).exists_least_ricci_field g (hU i) ε heps (hmetric i)
    have htarg : ι w ∈ (C i).target := by
      obtain ⟨y, _, hy⟩ := hw
      exact hy ▸ y.property
    exact (((hax (ι w) htarg).contMDiffAt ((C i).target.isOpen.mem_nhds htarg)).comp w
      hι.contMDiffAt).mdifferentiableAt (by decide)
  refine ⟨θ, horder, hfirst, hlast, (fun j ↦ (hlocal j).2.2.1),
    (fun j ↦ (hlocal j).2.2.2.1), hsupp, ?_⟩
  refine regular_patch_of_ordered_neck_collars ι hι hsurj g C U hU ε (C₁ * ε)
    heps hsmallGradient hmetric s c (fun j ↦ C₁ * ε / Real.sqrt (C j.castSucc).scale) hs
    (fun j ↦ div_nonneg (mul_nonneg hC₁.le hεnonneg) (Real.sqrt_nonneg _))
    θ horder hfirst hlast hsupp K hdisj hnonadj hinter hactive
    (fun j ↦ (hlocal j).2.2.2.2.2.2.2.2.2.1)
    (fun j w hw ↦ hKV j (hK j hw)) (fun j w hw ↦ (hvalue j w (hK j hw)).trans
      (div_le_div_of_nonneg_right herror (Real.sqrt_nonneg _)))
    (fun j w hw ↦ (hgradient j w (hK j hw)).trans herror) k hk D hD ?_ B hB ?_ hBsmall
  · intro j w hw z
    have hwV : w ∈ V (k j) := by
      rcases hk j with h | h
      · exact h ▸ (hKV j (hK j hw)).1
      · exact h ▸ (hKV j (hK j hw)).2
    have heq : |mvfderiv I (v (k j)) w z| = |mvfderiv I ((C (k j)).axial ∘ ι) w z| :=
      abs_mvfderiv_affine_sign ((C (k j)).axial ∘ ι) w (hphysical (k j) hwV)
        (a (k j)).1 (a (k j)).2 (finiteLineAffineAlignment_sign s c hs (k j)) z
    rw [heq]
    exact (hlocal j).2.2.2.2.2.2.2.2.2.2 w z
  · intro j
    have hwhich : (C (k j)).scale = (C j.castSucc).scale ∨ (C (k j)).scale = (C j.succ).scale := by
      rcases hk j with h | h
      · exact Or.inl (congrArg (fun i ↦ (C i).scale) h)
      · exact Or.inr (congrArg (fun i ↦ (C i).scale) h)
    exact (hscale (C j.castSucc).scale (C j.succ).scale (C j.castSucc).scale_pos
      (C j.succ).scale_pos (hratio j) (C (k j)).scale hwhich).2 _ (hhalf j)

end Poincare.Geometry.Neck
