import DifferentialGeometry.Analysis.Elliptic.Euclidean.WeakMaximumPrinciple
import DifferentialGeometry.Analysis.Elliptic.Euclidean.LaplaceCoefficient
import DifferentialGeometry.Analysis.Sobolev.Euclidean.DirichletEnergy.HarmonicMinimizer
import DifferentialGeometry.Analysis.Sobolev.Euclidean.ZeroTrace.Composition

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem exists_harmonic_replacement_with_coordinate_bounds
    {ι : Type*} [Fintype ι] (hd : 2 ≤ d) (hΩ : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) {u : E → EuclideanSpace ℝ ι}
    (hu : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => u x i) Ω)
    (C : ι → ℝ) (hC : ∀ᵐ x ∂volume.restrict Ω, ∀ i, |u x i| ≤ C i) :
    ∃ (h : E → EuclideanSpace ℝ ι)
      (hh : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => h x i) Ω),
      (∀ i, DeGiorgi.MemW01p 2 (fun x => h x i - u x i) Ω) ∧
      (∀ᵐ x ∂volume.restrict Ω, ∀ i, |h x i| ≤ C i) ∧
      (∀ i (φ : E → ℝ), DeGiorgi.IsSmoothTestOn Ω φ →
        (∫ x in Ω, inner ℝ ((hh i).weakGrad x) (DeGiorgi.smoothGradField φ x)) = 0) ∧
      ∀ (v : E → EuclideanSpace ℝ ι),
        (∀ i, DeGiorgi.MemW01p 2 (fun x => v x i - u x i) Ω) →
        ∀ hv : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => v x i) Ω,
          (∑ i, ∫ x in Ω, ‖(hh i).weakGrad x‖ ^ 2) ≤
            ∑ i, ∫ x in Ω, ‖(hv i).weakGrad x‖ ^ 2 := by
  let _ : NeZero d := ⟨by omega⟩
  obtain ⟨h, htrace, hh, hmin, heuler⟩ :=
    exists_weakly_harmonic_dirichlet_minimizer hd hΩ hΩb (fun i => (hu i).memW1p)
  have hsol (i : ι) : DeGiorgi.IsHomogeneousWeakSolution (DeGiorgi.EllipticCoeff.identity d Ω)
      (fun x => h x i) := by
    refine ⟨(hh i).memW1p, ?_⟩
    apply DeGiorgi.bilinFormOfCoeff_eq_of_isSmoothTestOn hΩ
      (DeGiorgi.EllipticCoeff.identity d Ω) (fun _ => 0)
      (by intros; simp) (by intros; simp) 0 (by intros; simp) (hh i)
    intro φ hφ
    simpa only [DeGiorgi.bilinFormOfCoeff_identity, DeGiorgi.smoothTestWitness] using heuler i φ hφ
  have hbound (i : ι) : ∀ᵐ x ∂volume.restrict Ω, |h x i| ≤ C i :=
    (hsol i).ae_abs_le_of_memH01_sub hd hΩ hΩb (hu i) (htrace i) (hC.mono fun x hx => hx i)
  exact ⟨h, hh, htrace, ae_all_iff.mpr hbound, heuler, hmin⟩

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {ι κ : Type*} [Fintype ι] [Fintype κ]
local notation "V" => EuclideanSpace ℝ (Fin 2)
local notation "E" => EuclideanSpace ℝ ι
local notation "F" => EuclideanSpace ℝ κ

theorem exists_harmonic_replacement_comp_of_coordinate_bounds
    {b : V} {a : ℝ} {z : V → E} {w : V → F}
    (hz : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => z x i) (Metric.ball b a))
    (C : ι → ℝ) (hzC : ∀ᵐ x ∂volume.restrict (Metric.ball b a), ∀ i, |z x i| ≤ C i)
    (T : E → F) (hT : ContDiff ℝ 1 T) {L : ℝ} (hL : ∀ y, ‖fderiv ℝ T y‖ ≤ L)
    (hTw : (fun x => T (z x)) =ᵐ[volume.restrict (Metric.ball b a)] w)
    {K : Set F} (hTK : MapsTo T {y | ∀ i, |y i| ≤ C i} K) :
    ∃ (h : V → E)
      (hh : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => h x i) (Metric.ball b a))
      (hq : ∀ k, DeGiorgi.MemW1pWitness 2 (fun x => T (h x) k) (Metric.ball b a)),
      (∀ i, DeGiorgi.MemW01p 2 (fun x => h x i - z x i) (Metric.ball b a)) ∧
      (∀ᵐ x ∂volume.restrict (Metric.ball b a), ∀ i, |h x i| ≤ C i) ∧
      (∀ k, DeGiorgi.MemW01p 2 (fun x => T (h x) k - w x k) (Metric.ball b a)) ∧
      (∀ᵐ x ∂volume.restrict (Metric.ball b a), T (h x) ∈ K) ∧
      (∀ k x j, (hq k).weakGrad x j =
        (fderiv ℝ T (h x) (WithLp.toLp 2 (fun i => (hh i).weakGrad x j))) k) ∧
      (∀ i (φ : V → ℝ), DeGiorgi.IsSmoothTestOn (Metric.ball b a) φ →
        (∫ x in Metric.ball b a, inner ℝ ((hh i).weakGrad x) (DeGiorgi.smoothGradField φ x)) = 0) ∧
      ∀ (v : V → E),
        (∀ i, DeGiorgi.MemW01p 2 (fun x => v x i - z x i) (Metric.ball b a)) →
        ∀ hv : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => v x i) (Metric.ball b a),
          (∑ i, ∫ x in Metric.ball b a, ‖(hh i).weakGrad x‖ ^ 2) ≤
            ∑ i, ∫ x in Metric.ball b a, ‖(hv i).weakGrad x‖ ^ 2 := by
  obtain ⟨h, hh, htrace, hbound, hEuler, hmin⟩ :=
    exists_harmonic_replacement_with_coordinate_bounds (by norm_num : 2 ≤ 2)
      Metric.isOpen_ball Metric.isBounded_ball hz C hzC
  obtain ⟨hq, hgrad⟩ := exists_memW1pWitnesses_comp_contDiff_on_ball_of_bounded_fderiv hh T hT hL
  have htraceT := memW01p_comp_sub_of_bounded_fderiv hz htrace T hT hL
  refine ⟨h, hh, hq, htrace, hbound, ?_, hbound.mono (fun x hx => hTK hx), hgrad, hEuler, hmin⟩
  intro k
  apply (htraceT k).congr
  exact hTw.mono fun x hx => by dsimp only at hx ⊢; rw [hx]

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ} [NeZero d] {ι : Type*} [Fintype ι]
local notation "V" => EuclideanSpace ℝ (Fin d)
local notation "F" => EuclideanSpace ℝ ι

theorem ae_norm_sub_le_of_weakly_harmonic_of_memW01p_sub
    {Ω : Set V} (hd : 2 ≤ d) (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    {u h : V → F}
    (hu : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => u x i) Ω)
    (hh : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => h x i) Ω)
    (htrace : ∀ i, DeGiorgi.MemW01p 2 (fun x => h x i - u x i) Ω)
    (hEuler : ∀ i (φ : V → ℝ), DeGiorgi.IsSmoothTestOn Ω φ →
      (∫ x in Ω, inner ℝ ((hh i).weakGrad x) (DeGiorgi.smoothGradField φ x)) = 0)
    (c : F) {K : ℝ} (hK : ∀ᵐ x ∂volume.restrict Ω, ‖u x - c‖ ≤ K) :
    ∀ᵐ x ∂volume.restrict Ω, ‖h x - c‖ ≤ Fintype.card ι * K := by
  classical
  have hsol (i : ι) : DeGiorgi.IsHomogeneousWeakSolution (DeGiorgi.EllipticCoeff.identity d Ω)
      (fun x => h x i) := by
    refine ⟨(hh i).memW1p, ?_⟩
    apply DeGiorgi.bilinFormOfCoeff_eq_of_isSmoothTestOn hΩ
      (DeGiorgi.EllipticCoeff.identity d Ω) (fun _ => 0)
      (by intros; simp) (by intros; simp) 0 (by intros; simp) (hh i)
    intro φ hφ
    simpa only [DeGiorgi.bilinFormOfCoeff_identity, DeGiorgi.smoothTestWitness] using hEuler i φ hφ
  have hcomp (i : ι) : ∀ᵐ x ∂volume.restrict Ω, |h x i - c i| ≤ K :=
    (hsol i).ae_abs_sub_le_of_memH01_sub hd hΩ hΩb (hu i) (htrace i) (c i)
      (hK.mono fun x hx => by
        have hc : |u x i - c i| ≤ ‖u x - c‖ := by
          simpa only [Real.norm_eq_abs, PiLp.sub_apply] using PiLp.norm_apply_le (u x - c) i
        exact hc.trans hx)
  filter_upwards [ae_all_iff.mpr hcomp] with x hx
  have heq : (∑ i, EuclideanSpace.single i ((h x - c) i)) = h x - c := by ext; simp
  calc
    ‖h x - c‖ = ‖∑ i, EuclideanSpace.single i ((h x - c) i)‖ := by rw [heq]
    _ ≤ ∑ i, ‖EuclideanSpace.single i ((h x - c) i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : ι, K := by
      apply Finset.sum_le_sum
      intro i hi
      simpa only [PiLp.norm_single, Real.norm_eq_abs, PiLp.sub_apply] using hx i
    _ = Fintype.card ι * K := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end
