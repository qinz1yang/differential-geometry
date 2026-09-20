import DifferentialGeometry.Analysis.Integration.Lp.QuadraticResidual
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Gradient.Columns

noncomputable section

open Filter Set MeasureTheory
open scoped ENNReal NNReal Topology

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ} {ι : Type*} [Fintype ι]

local notation "V" => EuclideanSpace ℝ (Fin d)
local notation "F" => EuclideanSpace ℝ ι

theorem tendsto_integral_weighted_gradient_pair_of_weak_of_energy_tendsto
    {Ω : Set V} (hΩ : MeasurableSet Ω) (f : ℕ → V → F) (v : V → F)
    (hs : ∀ n i, DeGiorgi.MemW1pWitness 2 (fun x => f n x i) Ω)
    (hv : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => v x i) Ω)
    (L : ℕ → ℝ≥0) (hf : ∀ n, LipschitzWith (L n) (f n))
    (hrep : ∀ n i j, (fun x => (hs n i).weakGrad x j) =ᵐ[volume.restrict Ω]
      (fun x => fderiv ℝ (fun y => f n y i) x (EuclideanSpace.single j 1)))
    (hweak : ∀ i (z : Lp V 2 (volume.restrict Ω)),
      Tendsto (fun n => inner ℝ (DeGiorgi.gradLpOfWitness (hs n i)) z) atTop
        (𝓝 (inner ℝ (DeGiorgi.gradLpOfWitness (hv i)) z)))
    {K : Set F} (hK : IsCompact K)
    (A : F → F →L[ℝ] F →L[ℝ] ℝ) (hA : ContinuousOn A K)
    (hpos : ∀ y ∈ K, LinearMap.IsPosSemidef (A y).toBilinForm)
    (hfK : ∀ n, MapsTo (f n) Ω K)
    (hvK : ∀ᵐ x ∂volume.restrict Ω, v x ∈ K)
    (hlim : ∀ᵐ x ∂volume.restrict Ω, Tendsto (fun n => f n x) atTop (𝓝 (v x)))
    (henergy : Tendsto (fun n => ∑ j : Fin d, ∫ x in Ω,
      A (f n x) (fderiv ℝ (f n) x (EuclideanSpace.single j 1))
        (fderiv ℝ (f n) x (EuclideanSpace.single j 1))) atTop
      (𝓝 (∑ j : Fin d, ∫ x in Ω,
        A (v x) (WithLp.toLp 2 (fun i => (hv i).weakGrad x j))
          (WithLp.toLp 2 (fun i => (hv i).weakGrad x j)))))
    (c : V → ℝ) (hcm : AEStronglyMeasurable c (volume.restrict Ω)) {D : ℝ≥0}
    (hc : ∀ᵐ x ∂volume.restrict Ω, |c x| ≤ D) (j k : Fin d) :
    Tendsto (fun n => ∫ x in Ω,
      c x * A (f n x) (fderiv ℝ (f n) x (EuclideanSpace.single j 1))
        (fderiv ℝ (f n) x (EuclideanSpace.single k 1))) atTop
      (𝓝 (∫ x in Ω, c x * A (v x)
        (WithLp.toLp 2 (fun i => (hv i).weakGrad x j))
        (WithLp.toLp 2 (fun i => (hv i).weakGrad x k)))) := by
  classical
  obtain ⟨u, u₀, hu, hu₀, hweak'⟩ :=
    exists_lp_gradient_columns_of_tendsto_inner f v hs hv L hf hrep hweak
  have hm : Measurable (K.piecewise A 0) :=
    hA.measurable_piecewise continuous_zero.continuousOn hK.measurableSet
  have hBm (n : ℕ) : AEStronglyMeasurable (fun x => A (f n x)) (volume.restrict Ω) := by
    have h : AEStronglyMeasurable (K.piecewise A 0 ∘ f n) (volume.restrict Ω) :=
      (hm.comp (hf n).continuous.measurable).aestronglyMeasurable
    apply h.congr
    filter_upwards [ae_restrict_mem hΩ] with x hx
    exact Set.piecewise_eq_of_mem K A 0 (hfK n hx)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hA
  have hBC (n : ℕ) : ∀ᵐ x ∂volume.restrict Ω, ‖A (f n x)‖ ≤ C := by
    filter_upwards [ae_restrict_mem hΩ] with x hx
    exact hC _ (hfK n hx)
  have hBpos (n : ℕ) : ∀ᵐ x ∂volume.restrict Ω,
      LinearMap.IsPosSemidef (A (f n x)).toBilinForm := by
    filter_upwards [ae_restrict_mem hΩ] with x hx
    exact hpos _ (hfK n hx)
  have hBlim : ∀ᵐ x ∂volume.restrict Ω,
      Tendsto (fun n => A (f n x)) atTop (𝓝 (A (v x))) := by
    filter_upwards [hlim, hvK, ae_restrict_mem hΩ] with x hx hxK hxΩ
    exact (hA (v x) hxK).tendsto.comp (tendsto_nhdsWithin_iff.mpr
      ⟨hx, Eventually.of_forall (fun n => hfK n hxΩ)⟩)
  have heq (n : ℕ) (j k : Fin d) (c : V → ℝ) :
      (∫ x in Ω, c x * A (f n x) (u j n x) (u k n x)) =
        ∫ x in Ω, c x * A (f n x)
          (fderiv ℝ (f n) x (EuclideanSpace.single j 1))
          (fderiv ℝ (f n) x (EuclideanSpace.single k 1)) := by
    apply integral_congr_ae
    filter_upwards [hu j n, hu k n] with x hj hk
    rw [hj, hk]
  have heq₀ (j k : Fin d) (c : V → ℝ) :
      (∫ x in Ω, c x * A (v x) (u₀ j x) (u₀ k x)) =
        ∫ x in Ω, c x * A (v x)
          (WithLp.toLp 2 (fun i => (hv i).weakGrad x j))
          (WithLp.toLp 2 (fun i => (hv i).weakGrad x k)) := by
    apply integral_congr_ae
    filter_upwards [hu₀ j, hu₀ k] with x hj hk
    rw [hj, hk]
  have he (n : ℕ) (j : Fin d) := heq n j j (fun _ => 1)
  have he₀ (j : Fin d) := heq₀ j j (fun _ => 1)
  simp only [one_mul] at he he₀
  have henergy' : Tendsto (fun n => ∑ j : Fin d, ∫ x in Ω,
      A (f n x) (u j n x) (u j n x)) atTop
      (𝓝 (∑ j : Fin d, ∫ x in Ω, A (v x) (u₀ j x) (u₀ j x))) := by
    simpa only [he, he₀] using henergy
  have ht := tendsto_integral_weighted_bilinear_of_weak_of_sum_energy_tendsto
    (fun n x => A (f n x)) (fun x => A (v x)) hBm C hBC hBlim hBpos u u₀ hweak'
    henergy' c hcm hc j k
  simpa only [heq, heq₀] using ht

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end
