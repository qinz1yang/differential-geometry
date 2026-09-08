import DifferentialGeometry.Analysis.Sobolev.Euclidean.Multiplication.SmoothCoefWeakPartialIBP
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivativeProduct
import DifferentialGeometry.Analysis.Integration.Lp.Product

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem exists_lp_product_weakPartial
    {Z : Type*} [MeasurableSpace Z] {μ : Measure Z} {Ω : Set E} {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hΩ : IsOpen Ω) (k : Fin d)
    (u v : Lp ℝ p (μ.prod (volume.restrict Ω)))
    {A : Z × E → ℝ}
    (hA : MemLp A ∞ (μ.prod (volume.restrict Ω)))
    (hDA : MemLp (fun p => fderiv ℝ (fun x => A (p.1, x)) p.2 (EuclideanSpace.single k 1))
      ∞ (μ.prod (volume.restrict Ω)))
    (hAsmooth : ∀ᵐ t ∂μ, ContDiffOn ℝ (⊤ : ℕ∞) (fun x => A (t, x)) Ω)
    (hweak : ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k
      (fun x => v (t, x)) (fun x => u (t, x)) Ω) :
    ∃ w : Lp ℝ p (μ.prod (volume.restrict Ω)),
      (w =ᵐ[μ.prod (volume.restrict Ω)] fun p =>
        A p * v p + fderiv ℝ (fun x => A (p.1, x)) p.2 (EuclideanSpace.single k 1) * u p) ∧
      ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k
        (fun x => w (t, x)) (fun x => A (t, x) * u (t, x)) Ω := by
  let F : Z × E → ℝ := fun p =>
    A p * v p + fderiv ℝ (fun x => A (p.1, x)) p.2 (EuclideanSpace.single k 1) * u p
  have hF : MemLp F p (μ.prod (volume.restrict Ω)) :=
    ((Lp.memLp v).mul hA).add ((Lp.memLp u).mul hDA)
  refine ⟨hF.toLp F, hF.coeFn_toLp, ?_⟩
  have hslices (w : Lp ℝ p (μ.prod (volume.restrict Ω))) :
      ∀ᵐ t ∂μ, MemLp (fun x => w (t, x)) p (volume.restrict Ω) := by
    by_cases hptop : p = ⊤
    · subst p
      exact (Lp.memLp w).prodMk_left_top
    · exact (Lp.memLp w).prodMk_left hptop
  filter_upwards [hweak, hAsmooth, hslices u,
    hslices v, Measure.ae_ae_of_ae_prod hF.coeFn_toLp]
    with t ht hAt hut hvt hFt
  have hw := ht.mul_contDiffOn hΩ hAt (hut.locallyIntegrable hp)
    (hvt.locallyIntegrable hp)
  intro φ hφ hφc hφs
  have he := hw φ hφ hφc hφs
  have hright : (∫ x in Ω, hF.toLp F (t, x) * φ x) = ∫ x in Ω, F (t, x) * φ x := by
    apply integral_congr_ae
    filter_upwards [hFt] with x hx
    rw [hx]
  exact he.trans (congrArg Neg.neg hright.symm)


theorem exists_lp_divergence_of_weakPartials
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [MeasurableSpace Z] [OpensMeasurableSpace Z] {μ : Measure Z} [IsLocallyFiniteMeasure μ] {Ω : Set E} {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hΩ : IsOpen Ω)
    (V : Fin d → Lp ℝ p (μ.prod (volume.restrict Ω)))
    (DV : Fin d → Fin d → Lp ℝ p (μ.prod (volume.restrict Ω)))
    {A : Fin d → Fin d → Z × E → ℝ}
    (hA : ∀ i j, MemLp (A i j) ∞ (μ.prod (volume.restrict Ω)))
    (hDA : ∀ i j, MemLp
      (fun p => fderiv ℝ (fun x => A i j (p.1, x)) p.2 (EuclideanSpace.single j 1))
      ∞ (μ.prod (volume.restrict Ω)))
    (hAsmooth : ∀ i j, ∀ᵐ t ∂μ, ContDiffOn ℝ (⊤ : ℕ∞) (fun x => A i j (t, x)) Ω)
    (hweak : ∀ i j, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv j
      (fun x => DV i j (t, x)) (fun x => V i (t, x)) Ω) :
    ∃ F : Lp ℝ p (μ.prod (volume.restrict Ω)),
      (F =ᵐ[μ.prod (volume.restrict Ω)] fun p => ∑ i, ∑ j,
        (A i j p * DV i j p +
          fderiv ℝ (fun x => A i j (p.1, x)) p.2 (EuclideanSpace.single j 1) * V i p)) ∧
      ∀ (φ : Z × E → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ (univ : Set Z) ×ˢ Ω →
        (∫ p, F p * φ p ∂μ.prod (volume.restrict Ω)) =
          -∑ i, ∑ j, ∫ p, A i j p * V i p *
            fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂μ.prod (volume.restrict Ω) := by
  classical
  let : Fact (1 ≤ p) := ⟨hp⟩
  choose W hW hWweak using fun i j =>
    exists_lp_product_weakPartial hp hΩ j (V i) (DV i j) (hA i j) (hDA i j)
      (hAsmooth i j) (hweak i j)
  let F : Lp ℝ p (μ.prod (volume.restrict Ω)) := ∑ i, ∑ j, W i j
  have hF : F =ᵐ[μ.prod (volume.restrict Ω)] fun p => ∑ i, ∑ j, W i j p := by
    filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i => ∑ j, W i j),
      ae_all_iff.mpr (fun i => Lp.coeFn_finsetSum Finset.univ (W i))] with p hp hi
    simp only [Finset.sum_apply] at hp hi
    rw [hp]
    apply Finset.sum_congr rfl
    intro i himem
    exact hi i
  refine ⟨F, ?_, ?_⟩
  · filter_upwards [hF, ae_all_iff.mpr fun i => ae_all_iff.mpr (hW i)] with p hp hWp
    rw [hp]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    exact hWp i j
  · intro φ hφ hφc hφs
    have hI (i j) : Integrable (fun p => W i j p * φ p) (μ.prod (volume.restrict Ω)) :=
      ((Lp.memLp (W i j)).locallyIntegrable hp).integrable_smul_right_of_hasCompactSupport
        hφ.continuous hφc
    have heq (i j) : (∫ p, W i j p * φ p ∂μ.prod (volume.restrict Ω)) =
        -∫ p, A i j p * V i p * fderiv ℝ φ p (0, EuclideanSpace.single j 1)
          ∂μ.prod (volume.restrict Ω) := by
      have hflux : MemLp (fun p => A i j p * V i p) p (μ.prod (volume.restrict Ω)) :=
        (Lp.memLp (V i)).mul (hA i j)
      have hw := integral_fderiv_prod_eq_neg_of_hasWeakPartialDeriv
        (hflux.locallyIntegrable hp)
        ((Lp.memLp (W i j)).locallyIntegrable hp) j (hWweak i j) φ hφ hφc hφs
      linarith
    calc
      _ = ∫ p, (∑ i, ∑ j, W i j p) * φ p ∂μ.prod (volume.restrict Ω) := by
        apply integral_congr_ae
        filter_upwards [hF] with p hp
        rw [hp]
      _ = ∑ i, ∑ j, ∫ p, W i j p * φ p ∂μ.prod (volume.restrict Ω) := by
        simp_rw [Finset.sum_mul]
        rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hI i j))]
        apply Finset.sum_congr rfl
        intro i hi
        exact integral_finsetSum _ (fun j _ => hI i j)
      _ = _ := by simp_rw [heq, Finset.sum_neg_distrib]


end DifferentialGeometry.Analysis.Sobolev.Euclidean
