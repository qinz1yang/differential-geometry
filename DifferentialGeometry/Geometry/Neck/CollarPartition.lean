import DifferentialGeometry.Geometry.Neck.Chart
import DifferentialGeometry.Geometry.Boundary.EmbeddedCollarPartition
import DifferentialGeometry.Topology.Manifold.OrientedProductChart

noncomputable section
open Set Filter Topology
open scoped Manifold ContDiff

namespace Poincare.Geometry.Neck

open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open Poincare.Topology.Manifold Poincare.Geometry.Boundary

private instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
local notation "S²" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

private theorem abs_mvfderiv_oriented_height
    {E H W F G M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [TopologicalSpace W] [ChartedSpace H W]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace G]
    {J : ModelWithCorners ℝ F G} [TopologicalSpace M] [ChartedSpace G M]
    (C : cylindricalChart J (M := M)) (U : TopologicalSpace.Opens (S² × ℝ))
    (Ψ : U ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ), J⟯ C.target) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (hinv : ∀ y : C.target, (Ψ.symm y : S² × ℝ) =
      (((C.chart.symm y : C.domain) : S² × ℝ).1,
        σ * ((C.chart.symm y : C.domain) : S² × ℝ).2))
    (ι : W → M) (hι : ContMDiff I J ∞ ι) (w : W) (hw : ι w ∈ C.target)
    (v : TangentSpace I w) :
    let q : M → ℝ := Subtype.val.extend
      (fun y : C.target ↦ ((Ψ.symm y : U) : S² × ℝ).2) (fun _ ↦ 0)
    |mvfderiv I (q ∘ ι) w v| = Real.sqrt C.scale * |mvfderiv I (C.axial ∘ ι) w v| := by
  intro q
  have hs : 0 < Real.sqrt C.scale := Real.sqrt_pos.mpr C.scale_pos
  have hqeq (y : C.target) : q (y : M) = (σ * Real.sqrt C.scale) * C.axial (y : M) := by
    dsimp only [q, cylindricalChart.axial]
    rw [Subtype.val_injective.extend_apply, Subtype.val_injective.extend_apply]
    rw [hinv]
    dsimp only [Prod.snd]
    field_simp
  let f : C.target → ℝ := fun y ↦ (Real.sqrt C.scale)⁻¹ *
    ((C.chart.symm y : C.domain) : S² × ℝ).2
  have hf : ContMDiff J 𝓘(ℝ) ∞ f :=
    contMDiff_const.mul (contMDiff_snd.comp (contMDiff_subtype_val.comp C.chart.symm.contMDiff))
  have hax : ContMDiffOn J 𝓘(ℝ) ∞ C.axial (C.target : Set M) := by
    have h := contMDiffOn_extend_from_open C.target f (fun _ ↦ 0) isOpen_univ hf.contMDiffOn
    have hr : (Subtype.val : C.target → M) '' univ = (C.target : Set M) := by
      ext y
      exact ⟨fun ⟨z, _, hz⟩ ↦ hz ▸ z.property, fun hy ↦ ⟨⟨y, hy⟩, mem_univ _, rfl⟩⟩
    rw [hr] at h
    exact h
  have haxw : MDifferentiableAt I 𝓘(ℝ) (C.axial ∘ ι) w :=
    (((hax (ι w) hw).contMDiffAt (C.target.isOpen.mem_nhds hw)).comp w
      hι.contMDiffAt).mdifferentiableAt (by decide)
  have hlocal : q ∘ ι =ᶠ[𝓝 w] fun z ↦ (σ * Real.sqrt C.scale) * C.axial (ι z) := by
    filter_upwards [(C.target.isOpen.preimage hι.continuous).mem_nhds hw] with z hz
    exact hqeq ⟨ι z, hz⟩
  have hd : mvfderiv I (q ∘ ι) w v =
      (σ * Real.sqrt C.scale) * mvfderiv I (C.axial ∘ ι) w v := by
    change (show ℝ from mfderiv I 𝓘(ℝ) (q ∘ ι) w v) = _
    rw [hlocal.mfderiv_eq]
    change mvfderiv I (fun z ↦ (σ * Real.sqrt C.scale) * C.axial (ι z)) w v = _
    have hm := mvfderiv_fun_mul (I := I) (f := fun _ : W ↦ σ * Real.sqrt C.scale)
      (g := C.axial ∘ ι) mdifferentiableAt_const haxw
    simpa only [Function.comp_apply, mvfderiv_const, add_apply, smul_apply, smul_eq_mul,
      zero_apply, mul_zero, add_zero]
      using DFunLike.congr_fun hm v
  rw [hd, abs_mul, abs_mul, abs_of_pos hs]
  rcases hσ with rfl | rfl <;> norm_num

theorem cylindricalChart.exists_oriented_chart_with_axial_coordinate
    {E H W F G M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [TopologicalSpace W] [ChartedSpace H W]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace G]
    {J : ModelWithCorners ℝ F G} [TopologicalSpace M] [ChartedSpace G M]
    (C : cylindricalChart J (M := M)) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (ι : W → M) (hι : ContMDiff I J ∞ ι) :
    ∃ U : TopologicalSpace.Opens (S² × ℝ),
      ∃ hU : ∀ x : S² × ℝ, x ∈ U ↔ (x.1, σ * x.2) ∈ C.domain,
      ∃ Ψ : U ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ), J⟯ C.target,
        (∀ x : U, Ψ x = C.chart
          ⟨((x : S² × ℝ).1, σ * (x : S² × ℝ).2), (hU x).mp x.property⟩) ∧
        (∀ y : C.target, (Ψ.symm y : S² × ℝ) =
          (((C.chart.symm y : C.domain) : S² × ℝ).1,
            σ * ((C.chart.symm y : C.domain) : S² × ℝ).2)) ∧
        let q : M → ℝ := Subtype.val.extend
          (fun y : C.target ↦ ((Ψ.symm y : U) : S² × ℝ).2) (fun _ ↦ 0)
        (∀ y : C.target, q (y : M) = (σ * Real.sqrt C.scale) * C.axial (y : M)) ∧
        ∀ w, ι w ∈ C.target → ∀ v : TangentSpace I w,
          |mvfderiv I (q ∘ ι) w v| = Real.sqrt C.scale * |mvfderiv I (C.axial ∘ ι) w v| := by
  obtain ⟨U, hU, Ψ, hΨ, hinv⟩ :=
    exists_oriented_product_chart C.domain C.target C.chart σ hσ
  refine ⟨U, hU, Ψ, hΨ, hinv, ?_, ?_⟩
  · intro y
    dsimp only [cylindricalChart.axial]
    rw [Subtype.val_injective.extend_apply, Subtype.val_injective.extend_apply, hinv]
    dsimp only [Prod.snd]
    have hs : 0 < Real.sqrt C.scale := Real.sqrt_pos.mpr C.scale_pos
    field_simp
  · intro w hw v
    exact abs_mvfderiv_oriented_height C U Ψ σ hσ hinv ι hι w hw v

theorem exists_uniform_partition_of_signed_neck_collars :
    ∃ A : ℝ, 0 < A ∧ ∀
    {E H W F G M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace W] [ChartedSpace H W] [HasSmoothBoundary E H I]
    [IsManifold I ∞ W] [T2Space W]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace G] (J : ModelWithCorners ℝ F G)
    [TopologicalSpace M] [ChartedSpace G M] [IsManifold J ∞ M],
    ∀ ι : W → M, ContMDiff I J ∞ ι →
    IsEmbedding ι → (∀ w, Function.Injective (mfderiv I J ι w)) →
    Module.finrank ℝ E = Module.finrank ℝ F → ∀ (n : ℕ)
      (C : Fin n → cylindricalChart J (M := M)) (σ : Fin n → ℝ)
      (_hσ : ∀ j, σ j = 1 ∨ σ j = -1)
      (l r : Fin n → ℝ) (hlr : ∀ j, l j < r j)
      (hcollar : ∀ j p t, t ∈ Icc (l j) (r j) → (p, σ j * t) ∈ (C j).domain),
      let e := fun j (x : S² × Icc (l j) (r j)) ↦
        ((C j).chart ⟨(x.1, σ j * (x.2 : ℝ)), hcollar j x.1 x.2 x.2.property⟩ : M)
      (∀ j x, e j x ∈ interior (range ι)) →
      ∀ P Q : Fin n → Set W,
      (∀ j, IsClosed (P j)) → (∀ j, IsClosed (Q j)) → (∀ j, Disjoint (P j) (Q j)) →
      (∀ j, P j ∪ ι ⁻¹' range (e j) ∪ Q j = univ) →
      (∀ j, P j ∩ ι ⁻¹' range (e j) ⊆
        ι ⁻¹' range (fun p : S² ↦ e j (p, ⟨l j, le_rfl, (hlr j).le⟩))) →
      (∀ j, Q j ∩ ι ⁻¹' range (e j) ⊆
        ι ⁻¹' range (fun p : S² ↦ e j (p, ⟨r j, (hlr j).le, le_rfl⟩))) →
      (∀ i j, i < j → interior (Q i) ∪ interior (P j) = univ) →
      ∀ (a b : Fin n → ℝ), (∀ j, l j < a j) → (∀ j, a j < b j) → (∀ j, b j < r j) →
      let K := fun j ↦ ι ⁻¹' (e j '' {x | a j ≤ (x.2 : ℝ) ∧ (x.2 : ℝ) ≤ b j})
      ∃ (β : Fin n → ℝ → ℝ) (θ : Fin (n + 2) → C^∞⟮I, W; 𝓘(ℝ), ℝ⟯),
        (∀ i w, θ i w ∈ Icc (0 : ℝ) 1) ∧
        (∀ j, ContDiff ℝ ∞ (β j) ∧ Monotone (β j) ∧
          (∀ w ∈ P j, θ j.succ.castSucc w = 0) ∧
          (∀ w ∈ Q j, θ j.succ.castSucc w = 1) ∧
          (∀ w x, ι w = e j x → θ j.succ.castSucc w = β j (x.2 : ℝ)) ∧
          (∀ t, t ≤ a j → β j t = 0) ∧ (∀ t, b j ≤ t → β j t = 1) ∧
          IsCompact (K j) ∧
          (∀ w ∉ K j, θ j.succ.castSucc w = 0 ∨ θ j.succ.castSucc w = 1) ∧
          (∀ w ∉ K j, mvfderiv I (θ j.succ.castSucc) w = 0) ∧
          ∀ w (v : TangentSpace I w),
            |mvfderiv I (θ j.succ.castSucc) w v| ≤
              (A / (b j - a j)) * Real.sqrt (C j).scale * |mvfderiv I ((C j).axial ∘ ι) w v|) ∧
        ∃ (horder : ∀ w, Antitone (fun i ↦ θ i w))
          (hfirst : ∀ w, θ 0 w = 1) (hlast : ∀ w, θ (Fin.last (n + 1)) w = 0),
          let χ := orderedStepPartition θ horder hfirst hlast
          Pairwise (fun i j ↦ Disjoint (K i) (K j)) ∧
          (∀ j : Fin n, tsupport (χ j.castSucc) ∩ tsupport (χ j.succ) ⊆ K j) ∧
          (∀ i j : Fin (n + 1), i.val + 1 < j.val →
            Disjoint (tsupport (χ i)) (tsupport (χ j))) ∧
          (∀ j : Fin n, tsupport (χ j.castSucc) ⊆ (interior (Q j))ᶜ ∧
            tsupport (χ j.succ) ⊆ (interior (P j))ᶜ) ∧
          ∀ j w, w ∈ K j → ∀ i : Fin (n + 1), χ i w ≠ 0 →
            i = j.castSucc ∨ i = j.succ := by
  classical
  obtain ⟨A, hA, hfamily⟩ := exists_uniform_ordered_partition_of_embedded_product_collars
  refine ⟨A, hA, ?_⟩
  intro E H W F G M _ _ _ _ I _ _ _ _ _ _ _ _ _ J _ _ _
  specialize hfamily (W := W) (M := M) (N := S²) I J (𝓡 2)
  intro ι hι hemb hfull hdim n C σ hσ l r hlr hcollar e hinternal
    P Q hP hQ hPQ hcover hleft hright hsep a b hla hab hbr K
  choose U hU Ψ hΨ hinv hcoordinate hderivative using fun j ↦
    (C j).exists_oriented_chart_with_axial_coordinate (σ j) (hσ j) ι hι
  have hcollarU (j : Fin n) : (univ : Set S²) ×ˢ Icc (l j) (r j) ⊆ U j := by
    rintro x ⟨_, hx⟩
    exact (hU j x).mpr (hcollar j x.1 x.2 hx)
  let eU := fun j (x : S² × Icc (l j) (r j)) ↦
    (Ψ j ⟨(x.1, (x.2 : ℝ)), hcollarU j ⟨mem_univ _, x.2.property⟩⟩ : M)
  have heq (j : Fin n) (x : S² × Icc (l j) (r j)) : eU j x = e j x :=
    congrArg (fun y : (C j).target ↦ (y : M)) (hΨ j _)
  have heq' (j : Fin n) : eU j = e j := funext (heq j)
  obtain ⟨β, θ, h01, hlocal, horder, hfirst, hlast, hdisj, hadj, hnon, hwedge, hactive⟩ :=
    hfamily ι hι hemb hfull hdim n U (fun j ↦ (C j).target) Ψ l r hlr hcollarU
      (by intro j x; change eU j x ∈ _; rw [heq]; exact hinternal j x)
      P Q hP hQ hPQ
      (by intro j; change P j ∪ ι ⁻¹' range (eU j) ∪ Q j = univ; rw [heq']; exact hcover j)
      (by
        intro j
        change P j ∩ ι ⁻¹' range (eU j) ⊆
          ι ⁻¹' range (fun p : S² ↦ eU j (p, ⟨l j, le_rfl, (hlr j).le⟩))
        simpa only [heq'] using hleft j)
      (by
        intro j
        change Q j ∩ ι ⁻¹' range (eU j) ⊆
          ι ⁻¹' range (fun p : S² ↦ eU j (p, ⟨r j, (hlr j).le, le_rfl⟩))
        simpa only [heq'] using hright j)
      hsep a b hla hab hbr
  have hK (j : Fin n) :
      ι ⁻¹' (eU j '' {x | a j ≤ (x.2 : ℝ) ∧ (x.2 : ℝ) ≤ b j}) = K j := by rw [heq']
  refine ⟨β, θ, h01, ?_, horder, hfirst, hlast, ?_, ?_, hnon, hwedge, ?_⟩
  · intro j
    obtain ⟨hβ, hmono, hz, ho, hformula, hβzero, hβone, hcompact, hbinary, hoff, hbound⟩ := hlocal j
    change IsCompact (ι ⁻¹' (eU j '' {x | a j ≤ (x.2 : ℝ) ∧ (x.2 : ℝ) ≤ b j})) at hcompact
    change (∀ w ∉ ι ⁻¹' (eU j '' {x | a j ≤ (x.2 : ℝ) ∧ (x.2 : ℝ) ≤ b j}), _) at hbinary
    change (∀ w ∉ ι ⁻¹' (eU j '' {x | a j ≤ (x.2 : ℝ) ∧ (x.2 : ℝ) ≤ b j}), _) at hoff
    rw [hK] at hcompact hbinary hoff
    refine ⟨hβ, hmono, hz, ho, ?_, hβzero, hβone, hcompact, hbinary, hoff, ?_⟩
    · intro w x hx
      apply hformula w x
      change ι w = eU j x
      rwa [heq]
    · intro w v
      by_cases hw : w ∈ K j
      · have hwtarget : ι w ∈ (C j).target := by
          obtain ⟨x, _, hx⟩ := hw
          rw [← hx]
          exact ((C j).chart _).property
        have hd := hderivative j w hwtarget v
        have hb := hbound w v
        rw [hd] at hb
        simpa only [mul_assoc] using hb
      · rw [hoff w hw]
        simp only [zero_apply, abs_zero]
        exact mul_nonneg (mul_nonneg (div_nonneg hA.le (sub_pos.mpr (hab j)).le)
          (Real.sqrt_nonneg _)) (abs_nonneg _)
  · change Pairwise (fun i j ↦
      Disjoint (ι ⁻¹' (eU i '' {x | a i ≤ (x.2 : ℝ) ∧ (x.2 : ℝ) ≤ b i}))
        (ι ⁻¹' (eU j '' {x | a j ≤ (x.2 : ℝ) ∧ (x.2 : ℝ) ≤ b j}))) at hdisj
    simpa only [hK] using hdisj
  · intro j
    have h := hadj j
    change _ ⊆ ι ⁻¹' (eU j '' {x | a j ≤ (x.2 : ℝ) ∧ (x.2 : ℝ) ≤ b j}) at h
    simpa only [hK] using h
  · intro j w hw i hi
    apply hactive j w _ i hi
    change w ∈ ι ⁻¹' (eU j '' {x | a j ≤ (x.2 : ℝ) ∧ (x.2 : ℝ) ≤ b j})
    rwa [hK]

end Poincare.Geometry.Neck
