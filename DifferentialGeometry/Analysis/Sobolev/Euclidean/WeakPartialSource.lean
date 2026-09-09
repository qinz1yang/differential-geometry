import DifferentialGeometry.Analysis.Sobolev.Euclidean.DivergenceForm
import DifferentialGeometry.Analysis.Integration.Lp.Multiplication
import DifferentialGeometry.Analysis.Sobolev.Euclidean.SliceWkp
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

noncomputable section

open Filter MeasureTheory Set
open scoped ContDiff ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

private theorem exists_lp_product_weakPartial_norm_le
    {Z : Type*} [MeasurableSpace Z] {μ : Measure Z} {Ω : Set E}
    (hΩ : IsOpen Ω) (k : Fin d)
    (u v : Lp ℝ 2 (μ.prod (volume.restrict Ω)))
    {A : Z × E → ℝ}
    (hA : MemLp A ∞ (μ.prod (volume.restrict Ω)))
    (hDA : MemLp (fun p => fderiv ℝ (fun x => A (p.1, x)) p.2 (EuclideanSpace.single k 1))
      ∞ (μ.prod (volume.restrict Ω)))
    (hAsmooth : ∀ᵐ t ∂μ, ContDiffOn ℝ (⊤ : ℕ∞) (fun x => A (t, x)) Ω)
    (hweak : ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k
      (fun x => v (t, x)) (fun x => u (t, x)) Ω)
    (C D : ℝ)
    (hC : ∀ᵐ p ∂μ.prod (volume.restrict Ω), ‖A p‖ ≤ C)
    (hD : ∀ᵐ p ∂μ.prod (volume.restrict Ω),
      ‖fderiv ℝ (fun x => A (p.1, x)) p.2 (EuclideanSpace.single k 1)‖ ≤ D) :
    ∃ w : Lp ℝ 2 (μ.prod (volume.restrict Ω)),
      (w =ᵐ[μ.prod (volume.restrict Ω)] fun p =>
        A p * v p + fderiv ℝ (fun x => A (p.1, x)) p.2 (EuclideanSpace.single k 1) * u p) ∧
      (∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k
        (fun x => w (t, x)) (fun x => A (t, x) * u (t, x)) Ω) ∧
      ‖w‖ ≤ C * ‖v‖ + D * ‖u‖ := by
  obtain ⟨w, hw, hweakw⟩ := exists_lp_product_weakPartial (by norm_num) hΩ k u v
    hA hDA hAsmooth hweak
  refine ⟨w, hw, hweakw, ?_⟩
  let a : Bool → Z × E → ℝ := fun b => if b then A else
    fun p => fderiv ℝ (fun x => A (p.1, x)) p.2 (EuclideanSpace.single k 1)
  let K : Bool → ℝ := fun b => if b then C else D
  let V : Bool → Lp ℝ 2 (μ.prod (volume.restrict Ω)) := fun b => if b then v else u
  have ha (b) : MemLp (a b) ∞ (μ.prod (volume.restrict Ω)) := by
    cases b
    · exact hDA
    · exact hA
  have hb (b) : ∀ᵐ p ∂μ.prod (volume.restrict Ω), ‖a b p‖ ≤ K b := by
    cases b
    · exact hD
    · exact hC
  have hsum : w =ᵐ[μ.prod (volume.restrict Ω)] fun p => ∑ b, a b p * V b p := by
    simpa only [Fintype.sum_bool, a, V, Bool.false_eq_true, ↓reduceIte, add_comm] using hw
  have hn := norm_varying_coefficient_sum_le a ha K hb V w hsum
  simpa only [Fintype.sum_bool, K, V, Bool.false_eq_true, ↓reduceIte, add_comm] using hn

theorem exists_lp_sum_product_weakPartial_norm_le
    {Z ι : Type*} [MeasurableSpace Z] [Fintype ι] {μ : Measure Z} {Ω : Set E}
    (hΩ : IsOpen Ω) (k : Fin d)
    (V H : ι → Lp ℝ 2 (μ.prod (volume.restrict Ω)))
    (A : ι → Z × E → ℝ)
    (hA : ∀ i, MemLp (A i) ∞ (μ.prod (volume.restrict Ω)))
    (hDA : ∀ i, MemLp (fun p => fderiv ℝ (fun x => A i (p.1, x)) p.2
      (EuclideanSpace.single k 1)) ∞ (μ.prod (volume.restrict Ω)))
    (hAsmooth : ∀ i, ∀ᵐ t ∂μ, ContDiffOn ℝ (⊤ : ℕ∞) (fun x => A i (t, x)) Ω)
    (hweak : ∀ i, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k
      (fun x => H i (t, x)) (fun x => V i (t, x)) Ω)
    (C D : ι → ℝ)
    (hC : ∀ i, ∀ᵐ p ∂μ.prod (volume.restrict Ω), ‖A i p‖ ≤ C i)
    (hD : ∀ i, ∀ᵐ p ∂μ.prod (volume.restrict Ω),
      ‖fderiv ℝ (fun x => A i (p.1, x)) p.2 (EuclideanSpace.single k 1)‖ ≤ D i) :
    ∃ S F : Lp ℝ 2 (μ.prod (volume.restrict Ω)),
      (S =ᵐ[μ.prod (volume.restrict Ω)] fun p => ∑ i, A i p * V i p) ∧
      (F =ᵐ[μ.prod (volume.restrict Ω)] fun p => ∑ i,
        (A i p * H i p +
          fderiv ℝ (fun x => A i (p.1, x)) p.2 (EuclideanSpace.single k 1) * V i p)) ∧
      (∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k
        (fun x => F (t, x)) (fun x => S (t, x)) Ω) ∧
      ‖F‖ ≤ ∑ i, (C i * ‖H i‖ + D i * ‖V i‖) := by
  classical
  let ν := μ.prod (volume.restrict Ω)
  choose W hW hWweak hWnorm using fun i => exists_lp_product_weakPartial_norm_le hΩ k
    (V i) (H i) (hA i) (hDA i) (hAsmooth i) (hweak i) (C i) (D i) (hC i) (hD i)
  have hS : MemLp (fun p => ∑ i, A i p * V i p) 2 ν :=
    memLp_finsetSum Finset.univ fun i _ => (Lp.memLp (V i)).mul (hA i)
  let S := hS.toLp (fun p => ∑ i, A i p * V i p)
  let F : Lp ℝ 2 ν := ∑ i, W i
  have hF : F =ᵐ[ν] fun p => ∑ i, W i p := by
    filter_upwards [Lp.coeFn_finsetSum (Finset.univ : Finset ι) W] with p hp
    simpa only [F, Finset.sum_apply] using hp
  have hFformula : F =ᵐ[ν] fun p => ∑ i,
      (A i p * H i p +
        fderiv ℝ (fun x => A i (p.1, x)) p.2 (EuclideanSpace.single k 1) * V i p) := by
    filter_upwards [hF, ae_all_iff.mpr hW] with p hp hWp
    rw [hp]
    exact Finset.sum_congr rfl fun i _ => hWp i
  refine ⟨S, F, hS.coeFn_toLp, hFformula, ?_, ?_⟩
  · have hVI := ae_all_iff.mpr (fun i =>
      (((Lp.memLp (V i)).mul (r := 2) (hA i)).prodMk_left (by norm_num)))
    have hWI := ae_all_iff.mpr (fun i => (Lp.memLp (W i)).prodMk_left (by norm_num))
    filter_upwards [ae_all_iff.mpr hWweak, hVI, hWI,
      Measure.ae_ae_of_ae_prod hS.coeFn_toLp, Measure.ae_ae_of_ae_prod hF]
      with t hwt hvt hFt hSt hFvt
    intro φ hφ hφc hφs
    have hI i : Integrable (fun x => A i (t, x) * V i (t, x) *
        fderiv ℝ φ x (EuclideanSpace.single k 1)) (volume.restrict Ω) :=
      (hvt i).locallyIntegrable (by norm_num) |>.integrable_smul_right_of_hasCompactSupport
        ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)
        (hφc.fderiv_apply ℝ (EuclideanSpace.single k 1))
    have hJ i : Integrable (fun x => W i (t, x) * φ x) (volume.restrict Ω) :=
      (hFt i).locallyIntegrable (by norm_num) |>.integrable_smul_right_of_hasCompactSupport
        hφ.continuous hφc
    calc
      (∫ x in Ω, S (t, x) * fderiv ℝ φ x (EuclideanSpace.single k 1)) =
          ∫ x in Ω, (∑ i, A i (t, x) * V i (t, x)) *
            fderiv ℝ φ x (EuclideanSpace.single k 1) := by
        apply integral_congr_ae
        filter_upwards [hSt] with x hx
        rw [hx]
      _ = ∑ i, ∫ x in Ω, A i (t, x) * V i (t, x) *
          fderiv ℝ φ x (EuclideanSpace.single k 1) := by
        simp_rw [Finset.sum_mul]
        exact integral_finsetSum _ fun i _ => hI i
      _ = -∑ i, ∫ x in Ω, W i (t, x) * φ x := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun i _ => hwt i φ hφ hφc hφs
      _ = -(∫ x in Ω, (∑ i, W i (t, x)) * φ x) := by
        simp_rw [Finset.sum_mul]
        rw [integral_finsetSum _ fun i _ => hJ i]
      _ = -(∫ x in Ω, F (t, x) * φ x) := by
        congr 1
        apply integral_congr_ae
        filter_upwards [hFvt] with x hx
        rw [hx]
  · exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hWnorm i)

theorem exists_lp_spatial_weak_partials_of_ae_eq_finite_sum
    {Z ι : Type*} [MeasurableSpace Z] [Fintype ι] {μ : Measure Z}
    {Ω : Set E} (hΩ : IsOpen Ω)
    (f : Lp ℝ 2 (μ.prod (volume.restrict Ω)))
    (Y : ι → Lp ℝ 2 (μ.prod (volume.restrict Ω)))
    (DY : ι → Fin d → Lp ℝ 2 (μ.prod (volume.restrict Ω)))
    (A : ι → Z × E → ℝ)
    (hA : ∀ i, MemLp (A i) ∞ (μ.prod (volume.restrict Ω)))
    (hDA : ∀ i k, MemLp (fun p => fderiv ℝ (fun x => A i (p.1, x)) p.2
      (EuclideanSpace.single k 1)) ∞ (μ.prod (volume.restrict Ω)))
    (hAsmooth : ∀ i, ∀ᵐ t ∂μ, ContDiffOn ℝ (⊤ : ℕ∞) (fun x => A i (t, x)) Ω)
    (hYweak : ∀ i k, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k
      (fun x => DY i k (t, x)) (fun x => Y i (t, x)) Ω)
    (hf : f =ᵐ[μ.prod (volume.restrict Ω)] fun p => ∑ i, A i p * Y i p) :
    ∃ Df : Fin d → Lp ℝ 2 (μ.prod (volume.restrict Ω)),
      (∀ k, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k
        (fun x => Df k (t, x)) (fun x => f (t, x)) Ω) ∧
      (∀ k, Df k =ᵐ[μ.prod (volume.restrict Ω)] fun p => ∑ i,
        (A i p * DY i k p +
          fderiv ℝ (fun x => A i (p.1, x)) p.2 (EuclideanSpace.single k 1) * Y i p)) ∧
      (∀ k, ‖Df k‖ ≤ ∑ i,
        (lpNorm (A i) ∞ (μ.prod (volume.restrict Ω)) * ‖DY i k‖ +
          lpNorm (fun p => fderiv ℝ (fun x => A i (p.1, x)) p.2
            (EuclideanSpace.single k 1)) ∞ (μ.prod (volume.restrict Ω)) * ‖Y i‖)) ∧
    (∀ᵐ t ∂μ, MemWkp 1 2 (fun x => f (t, x)) Ω) ∧
    MemLp (fun t => (iteratedWeakSobolevNorm 1 2
      (fun x => f (t, x)) Ω).toReal) 2 μ := by
  let ν := μ.prod (volume.restrict Ω)
  let DA := fun i k (p : Z × E) =>
    fderiv ℝ (fun x => A i (p.1, x)) p.2 (EuclideanSpace.single k 1)
  let C := fun i => lpNorm (A i) ∞ ν
  let D := fun i k => lpNorm (DA i k) ∞ ν
  have hC (i) : ∀ᵐ p ∂ν, ‖A i p‖ ≤ C i :=
    ae_le_lpNorm_exponent_top (hA i)
  have hD (i k) : ∀ᵐ p ∂ν, ‖DA i k p‖ ≤ D i k :=
    ae_le_lpNorm_exponent_top (hDA i k)
  have hex (k : Fin d) : ∃ S G : Lp ℝ 2 ν,
      (S =ᵐ[ν] fun p => ∑ i, A i p * Y i p) ∧
      (G =ᵐ[ν] fun p => ∑ i, (A i p * DY i k p + DA i k p * Y i p)) ∧
      (∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k
        (fun x => G (t, x)) (fun x => S (t, x)) Ω) ∧
      ‖G‖ ≤ ∑ i, (C i * ‖DY i k‖ + D i k * ‖Y i‖) := by
    exact exists_lp_sum_product_weakPartial_norm_le
      hΩ k Y (fun i => DY i k) A hA (fun i => hDA i k) hAsmooth
      (fun i => hYweak i k) C (fun i => D i k) hC (fun i => hD i k)
  choose S Df hS hDf hweak hnorm using hex
  have hDfweak (k) : ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k
      (fun x => Df k (t, x)) (fun x => f (t, x)) Ω := by
    filter_upwards [hweak k, Measure.ae_ae_of_ae_prod ((hS k).trans hf.symm)] with t ht he
    exact hasWeakPartialDeriv_congr_ae hΩ k he ht
  have hWkp := ae_memWkp_one_and_memLp_wkpNorm_of_weak_partials hΩ
    (by norm_num) (by norm_num) (Lp.memLp f) (fun k => Lp.memLp (Df k)) hDfweak
  exact ⟨Df, hDfweak, hDf, hnorm, hWkp.1, hWkp.2⟩

theorem exists_lp_gradient_source_spatial_derivative_step
    {Z ι : Type*} [Fintype ι] [MeasurableSpace Z]
    {μ : Measure Z} {Ω : Set E} (hΩ : IsOpen Ω)
    (F : Fin d → Lp ℝ 2 (μ.prod (volume.restrict Ω)))
    (Y : Fin d → ι → Lp ℝ 2 (μ.prod (volume.restrict Ω)))
    (DY : Fin d → ι → Fin d → Lp ℝ 2 (μ.prod (volume.restrict Ω)))
    (A : Fin d → ι → Z × E → ℝ)
    (hA : ∀ k i, MemLp (A k i) ∞ (μ.prod (volume.restrict Ω)))
    (hDA : ∀ k i j, MemLp
      (fun p => fderiv ℝ (fun x => A k i (p.1, x)) p.2
        (EuclideanSpace.single j 1)) ∞ (μ.prod (volume.restrict Ω)))
    (hAsmooth : ∀ k i, ∀ᵐ t ∂μ,
      ContDiffOn ℝ (⊤ : ℕ∞) (fun x => A k i (t, x)) Ω)
    (hYweak : ∀ k i j, ∀ᵐ t ∂μ,
      DeGiorgi.HasWeakPartialDeriv j
        (fun x => DY k i j (t, x)) (fun x => Y k i (t, x)) Ω)
    (hF : ∀ k, F k =ᵐ[μ.prod (volume.restrict Ω)]
      fun p => ∑ i, A k i p * Y k i p) :
    ∃ DF : Fin d → Fin d → Lp ℝ 2 (μ.prod (volume.restrict Ω)),
      (∀ k j, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv j
        (fun x => DF k j (t, x)) (fun x => F k (t, x)) Ω) ∧
      (∀ k j, DF k j =ᵐ[μ.prod (volume.restrict Ω)] fun p => ∑ i,
        (A k i p * DY k i j p +
          fderiv ℝ (fun x => A k i (p.1, x)) p.2
            (EuclideanSpace.single j 1) * Y k i p)) ∧
      (∀ k j, ‖DF k j‖ ≤ ∑ i,
        (lpNorm (A k i) ∞ (μ.prod (volume.restrict Ω)) * ‖DY k i j‖ +
          lpNorm (fun p => fderiv ℝ (fun x => A k i (p.1, x)) p.2
            (EuclideanSpace.single j 1)) ∞ (μ.prod (volume.restrict Ω)) * ‖Y k i‖)) := by
  classical
  choose DF hDF hDFformula hDFnorm using fun k =>
    exists_lp_spatial_weak_partials_of_ae_eq_finite_sum hΩ (F k) (Y k) (DY k) (A k)
      (fun i => hA k i) (fun i j => hDA k i j) (fun i => hAsmooth k i)
      (fun i j => hYweak k i j) (hF k)
  exact ⟨DF, (fun k j => hDF k j), (fun k j => hDFformula k j),
    (fun k j => (hDFnorm k).1 j)⟩


theorem exists_lp_second_spatial_weak_partials_of_ae_eq_finite_sum
    {Z ι : Type*} [Fintype ι] [MeasurableSpace Z]
    {μ : Measure Z} {Ω : Set E} (hΩ : IsOpen Ω)
    (F : Fin d → Lp ℝ 2 (μ.prod (volume.restrict Ω)))
    (Y : Fin d → ι → Lp ℝ 2 (μ.prod (volume.restrict Ω)))
    (DY : Fin d → ι → Fin d → Lp ℝ 2 (μ.prod (volume.restrict Ω)))
    (DDY : Fin d → ι → Fin d → Fin d → Lp ℝ 2 (μ.prod (volume.restrict Ω)))
    (A : Fin d → ι → Z × E → ℝ)
    (hA : ∀ k i, MemLp (A k i) ∞ (μ.prod (volume.restrict Ω)))
    (hDA : ∀ k i j, MemLp
      (fun p => fderiv ℝ (fun x => A k i (p.1, x)) p.2
        (EuclideanSpace.single j 1)) ∞ (μ.prod (volume.restrict Ω)))
    (hDDA : ∀ k i j l, MemLp
      (fun p => fderiv ℝ (fun x => fderiv ℝ (fun y => A k i (p.1, y)) x
        (EuclideanSpace.single j 1)) p.2 (EuclideanSpace.single l 1)) ∞
          (μ.prod (volume.restrict Ω)))
    (hAsmooth : ∀ k i, ∀ᵐ t ∂μ,
      ContDiffOn ℝ (⊤ : ℕ∞) (fun x => A k i (t, x)) Ω)
    (hDAsmooth : ∀ k i j, ∀ᵐ t ∂μ,
      ContDiffOn ℝ (⊤ : ℕ∞)
        (fun x => fderiv ℝ (fun y => A k i (t, y)) x (EuclideanSpace.single j 1)) Ω)
    (hYweak : ∀ k i j, ∀ᵐ t ∂μ,
      DeGiorgi.HasWeakPartialDeriv j
        (fun x => DY k i j (t, x)) (fun x => Y k i (t, x)) Ω)
    (hDYweak : ∀ k i j l, ∀ᵐ t ∂μ,
      DeGiorgi.HasWeakPartialDeriv l
        (fun x => DDY k i j l (t, x)) (fun x => DY k i j (t, x)) Ω)
    (hF : ∀ k, F k =ᵐ[μ.prod (volume.restrict Ω)]
      fun p => ∑ i, A k i p * Y k i p)
    : ∃ DF : Fin d → Fin d → Lp ℝ 2 (μ.prod (volume.restrict Ω)),
      (∀ k j, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv j
        (fun x => DF k j (t, x)) (fun x => F k (t, x)) Ω) ∧
      ∃ DDF : Fin d → Fin d → Fin d → Lp ℝ 2 (μ.prod (volume.restrict Ω)),
        (∀ k l m, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv m
          (fun x => DDF k l m (t, x)) (fun x => DF k l (t, x)) Ω) := by
  classical
  obtain ⟨DF, hDF, hDFformula, _⟩ :=
    exists_lp_gradient_source_spatial_derivative_step hΩ F Y DY A hA hDA hAsmooth hYweak hF
  let ι' := ι ⊕ ι
  have hex (k₀ : Fin d) : ∃ DDF : Fin d → Fin d → Lp ℝ 2 (μ.prod (volume.restrict Ω)),
      ∀ l m, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv m
        (fun x => DDF l m (t, x)) (fun x => DF k₀ l (t, x)) Ω := by
    let Y' : Fin d → ι' → Lp ℝ 2 (μ.prod (volume.restrict Ω)) := fun l s =>
      match s with
      | Sum.inl i => DY k₀ i l
      | Sum.inr i => Y k₀ i
    let DY' : Fin d → ι' → Fin d → Lp ℝ 2 (μ.prod (volume.restrict Ω)) := fun l s m =>
      match s with
      | Sum.inl i => DDY k₀ i l m
      | Sum.inr i => DY k₀ i m
    let A' : Fin d → ι' → Z × E → ℝ := fun l s =>
      match s with
      | Sum.inl i => A k₀ i
      | Sum.inr i => fun p => fderiv ℝ (fun x => A k₀ i (p.1, x)) p.2 (EuclideanSpace.single l 1)
    have hA' : ∀ j s, MemLp (A' j s) ∞ (μ.prod (volume.restrict Ω)) := by
      intro j s; rcases s with i | i
      · exact hA k₀ i
      · exact hDA k₀ i j
    have hDA' : ∀ j s l, MemLp (fun p => fderiv ℝ (fun x => A' j s (p.1, x)) p.2
        (EuclideanSpace.single l 1)) ∞ (μ.prod (volume.restrict Ω)) := by
      intro j s l; rcases s with i | i
      · exact hDA k₀ i l
      · exact hDDA k₀ i j l
    have hAsmooth' : ∀ j s, ∀ᵐ t ∂μ, ContDiffOn ℝ (⊤ : ℕ∞) (fun x => A' j s (t, x)) Ω := by
      intro j s; rcases s with i | i
      · exact hAsmooth k₀ i
      · exact hDAsmooth k₀ i j
    have hYweak' : ∀ j s l, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv l
        (fun x => DY' j s l (t, x)) (fun x => Y' j s (t, x)) Ω := by
      intro j s l; rcases s with i | i
      · exact hDYweak k₀ i j l
      · exact hYweak k₀ i l
    have hF' : ∀ l, DF k₀ l =ᵐ[μ.prod (volume.restrict Ω)]
        fun p => ∑ s, A' l s p * Y' l s p := by
      intro l
      have hj := hDFformula k₀ l
      filter_upwards [hj] with p hp
      rw [hp]
      rw [Fintype.sum_sum_type]
      simp only [A', Y']
      simp_rw [Finset.sum_add_distrib]
    obtain ⟨DDF, hDDF, _, _⟩ :=
      exists_lp_gradient_source_spatial_derivative_step hΩ (fun l => DF k₀ l) Y' DY' A'
        hA' hDA' hAsmooth' hYweak' hF'
    exact ⟨DDF, hDDF⟩
  choose DDF hDDF using hex
  exact ⟨DF, hDF, DDF, hDDF⟩
end DifferentialGeometry.Analysis.Sobolev.Euclidean
