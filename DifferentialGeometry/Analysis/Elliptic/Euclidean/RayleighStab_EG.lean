import DifferentialGeometry.Analysis.Elliptic.Euclidean.RayleighMinimizer_EG

/-!
# Stability on smooth test functions passes to `H¹₀(Ω)` (S-W-EIG, G2)

If `0 ≤ ∫|∇φ|² + Wφ²` for all `φ ∈ C_c^∞(Ω)` (`W` bounded measurable), the same holds for every
`v ∈ H¹₀(Ω)`: the smooth approximants of `v` converge in `L²` together with their gradients, and the
quadratic forms are `L²`-continuous (`tendsto_weight_sq_of_L2_EG`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology RealInnerProductSpace InnerProductSpace ContDiff

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ} [NeZero d] {Ω : Set (EuclideanSpace ℝ (Fin d))}

local notation "E" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
theorem tendsto_weight_sq_of_L2_EG (hΩ : MeasurableSet Ω) {c : E → ℝ} (hcm : Measurable c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ x ∈ Ω, |c x| ≤ B) {a : ℕ → E → ℝ} {w : E → ℝ}
    (ha : ∀ n, MemLp (a n) 2 (volume.restrict Ω)) (hw : MemLp w 2 (volume.restrict Ω))
    (hlim : Tendsto (fun n => eLpNorm (fun x => a n x - w x) 2 (volume.restrict Ω)) atTop
      (𝓝 0)) :
    Tendsto (fun n => ∫ x in Ω, c x * a n x ^ 2) atTop (𝓝 (∫ x in Ω, c x * w x ^ 2)) := by
  have ht : Tendsto (fun n => (eLpNorm (fun x => a n x - w x) 2 (volume.restrict Ω)).toReal)
      atTop (𝓝 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hlim
    simpa [Function.comp_def] using h
  obtain ⟨T, hT⟩ := ht.bddAbove_range
  have hT' : ∀ n, (eLpNorm (fun x => a n x - w x) 2 (volume.restrict Ω)).toReal ≤ T :=
    fun n => hT ⟨n, rfl⟩
  have hT0 : 0 ≤ T := (ENNReal.toReal_nonneg).trans (hT' 0)
  refine tendsto_weight_sq_EG hΩ hcm hB0 hB (R := T + (eLpNorm w 2 (volume.restrict Ω)).toReal)
    ha hw (by positivity) (fun n => ?_) hlim
  have h1 : eLpNorm (a n) 2 (volume.restrict Ω) ≤
      eLpNorm (fun x => a n x - w x) 2 (volume.restrict Ω) + eLpNorm w 2 (volume.restrict Ω) := by
    have h := eLpNorm_add_le (μ := volume.restrict Ω) (f := fun x => a n x - w x) (g := w)
      (p := 2) (by norm_num)
    have e : ((fun x => a n x - w x) + w) = a n := by
      ext x
      simp
    rwa [e] at h
  have h2 : (eLpNorm (a n) 2 (volume.restrict Ω)).toReal ≤
      (eLpNorm (fun x => a n x - w x) 2 (volume.restrict Ω)).toReal +
        (eLpNorm w 2 (volume.restrict Ω)).toReal := by
    have hab : MemLp (fun x => a n x - w x) 2 (volume.restrict Ω) := (ha n).sub hw
    have hfin : (eLpNorm (fun x => a n x - w x) 2 (volume.restrict Ω) +
        eLpNorm w 2 (volume.restrict Ω)) ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨hab.eLpNorm_lt_top.ne, hw.eLpNorm_lt_top.ne⟩
    rw [← ENNReal.toReal_add hab.eLpNorm_lt_top.ne hw.eLpNorm_lt_top.ne]
    exact ENNReal.toReal_mono hfin h1
  have h3 : (eLpNorm (a n) 2 (volume.restrict Ω)).toReal ≤
      T + (eLpNorm w 2 (volume.restrict Ω)).toReal := by linarith [hT' n]
  rw [← ENNReal.ofReal_toReal (ha n).eLpNorm_lt_top.ne]
  exact ENNReal.ofReal_le_ofReal h3

omit [NeZero d] in
theorem memLp_fderiv_apply_EG {φ : E → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (i : Fin d) :
    MemLp (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) 2 (volume.restrict Ω) := by
  have hderiv : ContDiff ℝ (⊤ : ℕ∞) (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) :=
    (hφ.fderiv_right (m := (⊤ : ℕ∞)) (by norm_cast)).clm_apply contDiff_const
  exact (hderiv.continuous.memLp_of_hasCompactSupport (hc.fderiv_apply (𝕜 := ℝ) _)).restrict Ω

theorem nonneg_h01_of_smooth_stab_EG (hΩ : IsOpen Ω) {W : E → ℝ} (hWm : Measurable W) {B : ℝ}
    (hB0 : 0 ≤ B) (hWB : ∀ x ∈ Ω, |W x| ≤ B)
    (hstab : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      0 ≤ (∫ x in Ω, ∑ i : Fin d, (fderiv ℝ φ x (EuclideanSpace.single i 1)) ^ 2) +
        ∫ x in Ω, W x * φ x ^ 2)
    {v : E → ℝ} (hv0 : DeGiorgi.MemW01p 2 v Ω) (hv : DeGiorgi.MemW1pWitness 2 v Ω) :
    0 ≤ (∫ x in Ω, ‖hv.weakGrad x‖ ^ 2) + ∫ x in Ω, W x * v x ^ 2 := by
  obtain ⟨_, hw, φ, hφs, hφc, hφΩ, hφf, hφg⟩ := hv0
  rw [dir_congr_EG hΩ hv hw]
  have hφL : ∀ n, MemLp (φ n) 2 (volume.restrict Ω) := fun n =>
    ((hφs n).continuous.memLp_of_hasCompactSupport (hφc n)).restrict Ω
  have hPlim := tendsto_weight_sq_of_L2_EG hΩ.measurableSet hWm hB0 hWB hφL hw.memLp hφf
  have hgrad_i : ∀ i : Fin d, Tendsto (fun n => ∫ x in Ω,
      (fderiv ℝ (φ n) x (EuclideanSpace.single i 1)) ^ 2) atTop
      (𝓝 (∫ x in Ω, (hw.weakGrad x i) ^ 2)) := by
    intro i
    have h := tendsto_weight_sq_of_L2_EG hΩ.measurableSet (c := fun _ => (1 : ℝ))
      measurable_const zero_le_one (fun _ _ => by simp)
      (a := fun n x => fderiv ℝ (φ n) x (EuclideanSpace.single i 1))
      (w := fun x => hw.weakGrad x i) (fun n => memLp_fderiv_apply_EG (hφs n) (hφc n) i)
      (hw.weakGrad_component_memLp i) (hφg i)
    simpa using h
  have hsum : Tendsto (fun n => ∑ i : Fin d, ∫ x in Ω,
      (fderiv ℝ (φ n) x (EuclideanSpace.single i 1)) ^ 2) atTop
      (𝓝 (∑ i : Fin d, ∫ x in Ω, (hw.weakGrad x i) ^ 2)) :=
    tendsto_finsetSum _ (fun i _ => hgrad_i i)
  have hnorm : (∫ x in Ω, ‖hw.weakGrad x‖ ^ 2) = ∑ i : Fin d, ∫ x in Ω, (hw.weakGrad x i) ^ 2 := by
    rw [← integral_finsetSum _ (fun i _ => (hw.weakGrad_component_memLp i).integrable_sq)]
    apply integral_congr_ae
    filter_upwards with x
    simp [EuclideanSpace.norm_sq_eq]
  rw [hnorm]
  refine ge_of_tendsto (hsum.add hPlim) (Eventually.of_forall fun n => ?_)
  have h := hstab (φ n) (hφs n) (hφc n) (hφΩ n)
  rwa [integral_finsetSum _ (fun i _ =>
    (memLp_fderiv_apply_EG (hφs n) (hφc n) i).integrable_sq)] at h

end DifferentialGeometry.Analysis.Sobolev.Euclidean
