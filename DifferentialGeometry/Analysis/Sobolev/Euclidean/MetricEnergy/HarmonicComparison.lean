import DifferentialGeometry.Analysis.Sobolev.Euclidean.Replacement.Harmonic
import DifferentialGeometry.Analysis.Elliptic.Euclidean.Harmonic.Comparison
import DifferentialGeometry.Analysis.Convex.CoordinateBox

section

set_option autoImplicit false
noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {ι : Type*} [Fintype ι]
local notation "V" => EuclideanSpace ℝ (Fin 2)
local notation "F" => EuclideanSpace ℝ ι

theorem exists_harmonic_replacement_error_bound_of_metric_minimality
    {Ω : Set V} (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    {z : V → F} (hz : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => z x i) Ω)
    (C : ι → ℝ) (hzC : ∀ᵐ x ∂volume.restrict Ω, ∀ i, |z x i| ≤ C i)
    (B : F → F →L[ℝ] F →L[ℝ] ℝ)
    (hB : ContinuousOn B {y : F | ∀ i, |y i| ≤ C i})
    (A₀ : F →L[ℝ] F →L[ℝ] ℝ) (hsym : ∀ v w, A₀ v w = A₀ w v)
    {lam ε : ℝ} (hlam : 0 < lam) (hε : 0 ≤ ε)
    (hcoerce : ∀ v, lam * ‖v‖ ^ 2 ≤ A₀ v v)
    (hclose : ∀ y : F, (∀ i, |y i| ≤ C i) → ‖B y - A₀‖ ≤ ε)
    (hmin : ∀ (q : V → F) (hq : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => q x i) Ω),
      (∀ i, DeGiorgi.MemW01p 2 (fun x => q x i - z x i) Ω) →
      (∀ᵐ x ∂volume.restrict Ω, ∀ i, |q x i| ≤ C i) →
      (1 / 2 : ℝ) * (∑ j : Fin 2, ∫ x in Ω, B (z x)
        (WithLp.toLp 2 (fun i => (hz i).weakGrad x j))
        (WithLp.toLp 2 (fun i => (hz i).weakGrad x j))) ≤
        (1 / 2 : ℝ) * (∑ j : Fin 2, ∫ x in Ω, B (q x)
          (WithLp.toLp 2 (fun i => (hq i).weakGrad x j))
          (WithLp.toLp 2 (fun i => (hq i).weakGrad x j)))) :
    ∃ (h : V → F) (hh : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => h x i) Ω),
      (∀ i, DeGiorgi.MemW01p 2 (fun x => h x i - z x i) Ω) ∧
      (∀ᵐ x ∂volume.restrict Ω, ∀ i, |h x i| ≤ C i) ∧
      (∀ i (φ : V → ℝ), DeGiorgi.IsSmoothTestOn Ω φ →
        (∫ x in Ω, inner ℝ ((hh i).weakGrad x) (DeGiorgi.smoothGradField φ x)) = 0) ∧
      (∑ i, ∫ x in Ω, ‖(hz i).weakGrad x - (hh i).weakGrad x‖ ^ 2) ≤
        (2 * ε / lam) * ∑ i, ∫ x in Ω, ‖(hz i).weakGrad x‖ ^ 2 := by
  classical
  obtain ⟨h, hh, htrace, hhC, hEuler, _⟩ :=
    exists_harmonic_replacement_with_coordinate_bounds (by norm_num : 2 ≤ 2) hΩ hΩb hz C hzC
  let K := {y : F | ∀ i, |y i| ≤ C i}
  have hK : IsCompact K := DifferentialGeometry.Analysis.isCompact_coordinate_box C
  have hBm : Measurable (K.piecewise B 0) :=
    hB.measurable_piecewise continuous_zero.continuousOn hK.measurableSet
  have hm (f : V → F) (hf : MemLp f 2 (volume.restrict Ω))
      (hfK : ∀ᵐ x ∂volume.restrict Ω, f x ∈ K) :
      AEStronglyMeasurable (fun x => B (f x)) (volume.restrict Ω) :=
    (hBm.comp_aemeasurable hf.aemeasurable).aestronglyMeasurable.congr
      (hfK.mono fun x hx => Set.piecewise_eq_of_mem K B 0 hx)
  have hBz := hm z (MemLp.of_eval_piLp fun i => (hz i).memLp) hzC
  have hBh := hm h (MemLp.of_eval_piLp fun i => (hh i).memLp) hhC
  have hle := hmin h hh htrace hhC
  have hle' : (∑ j : Fin 2, ∫ x in Ω, B (z x)
      (WithLp.toLp 2 (fun i => (hz i).weakGrad x j))
      (WithLp.toLp 2 (fun i => (hz i).weakGrad x j))) ≤
      ∑ j : Fin 2, ∫ x in Ω, B (h x)
        (WithLp.toLp 2 (fun i => (hh i).weakGrad x j))
        (WithLp.toLp 2 (fun i => (hh i).weakGrad x j)) := by linarith
  refine ⟨h, hh, htrace, hhC, hEuler, ?_⟩
  exact integral_weakGrad_difference_sq_le_of_harmonic_comparison hΩ hz hh htrace hEuler
    A₀ hsym hlam hε hcoerce B
    (fun v w => (hBz.apply_continuousLinearMap v).apply_continuousLinearMap w)
    (fun v w => (hBh.apply_continuousLinearMap v).apply_continuousLinearMap w)
    (hzC.mono fun x hx => hclose (z x) hx) (hhC.mono fun x hx => hclose (h x) hx) hle'

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end

end

section

set_option autoImplicit false
noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {m : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin 2)
local notation "F" => EuclideanSpace ℝ (Fin m)

theorem exists_uniform_harmonic_comparison_error_of_continuous_metric_minimizer
    {z : V → F} {R a : ℝ} (hR : 0 < R) (ha : 0 < a)
    (hz : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => z x i) (ball (0 : V) R))
    (hzc : ContinuousAt z 0) (hz0 : z 0 = 0)
    (B : F → F →L[ℝ] F →L[ℝ] ℝ) (hB : ContinuousOn B (closedBall (0 : F) a))
    (hsym : ∀ v w, B 0 v w = B 0 w v)
    {lam : ℝ} (hlam : 0 < lam) (hcoerce : ∀ v, lam * ‖v‖ ^ 2 ≤ B 0 v v)
    (hmin : ∀ (c : V) (s : ℝ), 0 < s → ‖c‖ + s < R →
      ∀ (q : V → F) (hq : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => q x i) (ball c s)),
      (∀ i, DeGiorgi.MemW01p 2 (fun x => q x i - z x i) (ball c s)) →
      (∀ᵐ x ∂volume.restrict (ball c s), q x ∈ closedBall (0 : F) a) →
      (1 / 2 : ℝ) * (∑ j : Fin 2, ∫ x in ball c s, B (z x)
        (WithLp.toLp 2 (fun i => (hz i).weakGrad x j))
        (WithLp.toLp 2 (fun i => (hz i).weakGrad x j))) ≤
        (1 / 2 : ℝ) * (∑ j : Fin 2, ∫ x in ball c s, B (q x)
          (WithLp.toLp 2 (fun i => (hq i).weakGrad x j))
          (WithLp.toLp 2 (fun i => (hq i).weakGrad x j))))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ r : ℝ, 0 < r ∧ r < R ∧ ∀ (c : V) (s : ℝ),
      0 < s → ‖c‖ + s < r →
      ∃ (h : V → F) (hh : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => h x i) (ball c s)),
        (∀ i, DeGiorgi.MemW01p 2 (fun x => h x i - z x i) (ball c s)) ∧
        (∀ i (φ : V → ℝ), DeGiorgi.IsSmoothTestOn (ball c s) φ →
          (∫ x in ball c s, inner ℝ ((hh i).weakGrad x) (DeGiorgi.smoothGradField φ x)) = 0) ∧
        (∑ i : Fin m, ∫ x in ball c s, ‖(hz i).weakGrad x - (hh i).weakGrad x‖ ^ 2) ≤
          δ * ∑ i : Fin m, ∫ x in ball c s, ‖(hz i).weakGrad x‖ ^ 2 := by
  let : NormedAddCommGroup (F →L[ℝ] F →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  let ε := δ * lam / 2
  have hε : 0 < ε := by dsimp only [ε]; positivity
  have hB0 : ContinuousAt B (0 : F) := hB.continuousAt
    (closedBall_mem_nhds (0 : F) ha)
  have hnear : closedBall (0 : F) a ∩ {y | ‖B y - B 0‖ < ε} ∈ 𝓝 (0 : F) :=
    inter_mem (closedBall_mem_nhds _ ha) (by
      have h := hB0.preimage_mem_nhds (ball_mem_nhds _ hε)
      have heq : B ⁻¹' ball (B 0) ε = {y | ‖B y - B 0‖ < ε} := by
        ext y
        simp only [mem_preimage, mem_ball, dist_eq_norm, mem_ofPred_eq]
      rwa [heq] at h)
  obtain ⟨τ, hτ, hbox⟩ :=
    DifferentialGeometry.Analysis.exists_pos_coordinate_box_subset_of_mem_nhds_zero hnear
  obtain ⟨r₀, hr₀, hrange⟩ := DifferentialGeometry.Analysis.exists_source_ball_mapsTo_coordinate_box
    hzc hz0 hτ
  let r := min r₀ (R / 2)
  have hr : 0 < r := lt_min hr₀ (half_pos hR)
  have hrR : r < R := (min_le_right _ _).trans_lt (half_lt_self hR)
  have hrr₀ : r ≤ r₀ := min_le_left _ _
  refine ⟨r, hr, hrR, ?_⟩
  intro c s hs hcs
  have hball : ball c s ⊆ ball (0 : V) R := by
    intro x hx
    have hn : ‖x‖ ≤ dist x c + ‖c‖ := by
      simpa only [dist_eq_norm, sub_add_cancel] using norm_add_le (x - c) c
    exact mem_ball_zero_iff.mpr (by have hd := mem_ball.mp hx; linarith)
  have hball₀ : ball c s ⊆ closedBall (0 : V) r₀ := by
    intro x hx
    have hn : ‖x‖ ≤ dist x c + ‖c‖ := by
      simpa only [dist_eq_norm, sub_add_cancel] using norm_add_le (x - c) c
    exact mem_closedBall_zero_iff.mpr (by have hd := mem_ball.mp hx; linarith)
  let hzs (i : Fin m) := (hz i).restrict isOpen_ball hball
  have hzbox : ∀ᵐ x ∂volume.restrict (ball c s), ∀ i, |z x i| ≤ τ := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    exact hrange x (hball₀ hx)
  have hBbox : ContinuousOn B {y : F | ∀ i, |y i| ≤ τ} :=
    hB.mono (fun y hy => (hbox hy).1)
  have hclose : ∀ y : F, (∀ i, |y i| ≤ τ) → ‖B y - B 0‖ ≤ ε :=
    fun y hy => (hbox hy).2.le
  obtain ⟨h, hh, htrace, _, hEuler, herr⟩ :=
    exists_harmonic_replacement_error_bound_of_metric_minimality isOpen_ball isBounded_ball hzs
      (fun _ => τ) hzbox B hBbox (B 0) hsym hlam hε.le hcoerce hclose
      (fun q hq hqz hqbox => hmin c s hs (hcs.trans hrR) q hq hqz
        (hqbox.mono fun x hx => (hbox hx).1))
  refine ⟨h, hh, htrace, hEuler, ?_⟩
  have heq : 2 * ε / lam = δ := by dsimp only [ε]; field_simp
  simpa only [heq, hzs, DeGiorgi.MemW1pWitness.restrict] using herr

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end

end

section

set_option autoImplicit false
noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {ι : Type*} [Fintype ι]
local notation "V" => EuclideanSpace ℝ (Fin 2)
local notation "F" => EuclideanSpace ℝ ι

theorem exists_holder_harmonic_comparison_of_metric_minimality
    {z : V → F} {c : V} {R α Lz lam : ℝ} (hR : 0 < R) (hα : 0 ≤ α) (hLz : 0 ≤ Lz)
    (hz : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => z x i) (ball c R))
    (C : ι → ℝ) (hzC : ∀ᵐ x ∂volume.restrict (ball c R), ∀ i, |z x i| ≤ C i)
    (B : F → F →L[ℝ] F →L[ℝ] ℝ) {L : ℝ≥0}
    (hBLip : LipschitzOnWith L B {y : F | ∀ i, |y i| ≤ C i})
    (hzc : ∀ i, |z c i| ≤ C i)
    (hsym : ∀ v w, B (z c) v w = B (z c) w v)
    (hlam : 0 < lam) (hcoerce : ∀ v, lam * ‖v‖ ^ 2 ≤ B (z c) v v)
    (hHolder : ∀ x ∈ ball c R, ‖z x - z c‖ ≤ Lz * ‖x - c‖ ^ α)
    (hmin : ∀ (q : V → F) (hq : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => q x i) (ball c R)),
      (∀ i, DeGiorgi.MemW01p 2 (fun x => q x i - z x i) (ball c R)) →
      (∀ᵐ x ∂volume.restrict (ball c R), ∀ i, |q x i| ≤ C i) →
      (1 / 2 : ℝ) * (∑ j : Fin 2, ∫ x in ball c R, B (z x)
        (WithLp.toLp 2 (fun i => (hz i).weakGrad x j))
        (WithLp.toLp 2 (fun i => (hz i).weakGrad x j))) ≤
        (1 / 2 : ℝ) * (∑ j : Fin 2, ∫ x in ball c R, B (q x)
          (WithLp.toLp 2 (fun i => (hq i).weakGrad x j))
          (WithLp.toLp 2 (fun i => (hq i).weakGrad x j)))) :
    ∃ (h : V → F) (hh : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => h x i) (ball c R)),
      (∀ i (φ : V → ℝ), DeGiorgi.IsSmoothTestOn (ball c R) φ →
        (∫ x in ball c R, inner ℝ ((hh i).weakGrad x) (DeGiorgi.smoothGradField φ x)) = 0) ∧
      (∑ i, ∫ x in ball c R, ‖(hz i).weakGrad x - (hh i).weakGrad x‖ ^ 2) ≤
        (2 * (L : ℝ) * (Fintype.card ι + 1) * Lz / lam) * R ^ α *
          ∑ i, ∫ x in ball c R, ‖(hz i).weakGrad x‖ ^ 2 := by
  obtain ⟨h, hh, htrace, hhC, hEuler, _⟩ :=
    exists_harmonic_replacement_with_coordinate_bounds (by norm_num : 2 ≤ 2)
      isOpen_ball isBounded_ball hz C hzC
  have hle := hmin h hh htrace hhC
  have hle' : (∑ j : Fin 2, ∫ x in ball c R, B (z x)
      (WithLp.toLp 2 (fun i => (hz i).weakGrad x j))
      (WithLp.toLp 2 (fun i => (hz i).weakGrad x j))) ≤
      ∑ j : Fin 2, ∫ x in ball c R, B (h x)
        (WithLp.toLp 2 (fun i => (hh i).weakGrad x j))
        (WithLp.toLp 2 (fun i => (hh i).weakGrad x j)) := by linarith
  refine ⟨h, hh, hEuler, ?_⟩
  exact integral_weakGrad_difference_sq_le_of_holder_harmonic_comparison hR hα hLz hz hh
    htrace hEuler B (DifferentialGeometry.Analysis.isCompact_coordinate_box C)
    hzC hhC hzc hBLip hsym hlam hcoerce hHolder hle'

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end

end
