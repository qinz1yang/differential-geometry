import DifferentialGeometry.Topology.Homeomorph.AffinePeriodic
import DifferentialGeometry.Topology.LoopSpace.AffineLift
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.MorreyDisk
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.MinimizingSequence
import DifferentialGeometry.Topology.LoopSpace.RadialHomeomorphism
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.RadialVariation
import DifferentialGeometry.Analysis.Calculus.Variation.Quadratic

noncomputable section

open Set Filter Function MeasureTheory ContinuousMap
open DifferentialGeometry.Topology
open scoped Topology NNReal ENNReal Manifold ContDiff

namespace DifferentialGeometry.Geometry

theorem exists_circle_variation_of_periodic_lipschitz
    {ψ : ℝ → ℝ} {C : ℝ≥0} (hψ : LipschitzWith C ψ) (hper : Periodic ψ 1) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t| < ε →
      ∃ δ : loopCircle ≃ₜ loopCircle,
        (∀ s : ℝ, δ (s : loopCircle) = ((s + t * ψ s : ℝ) : loopCircle)) ∧
        IsWeaklyMonotoneOnce (⟨δ, δ.continuous⟩ : C(loopCircle, loopCircle)) ∧
        ∃ K L : ℝ≥0, LipschitzWith K δ ∧ LipschitzWith L δ.symm := by
  refine ⟨(2 * ((C : ℝ) + 1))⁻¹, inv_pos.mpr (by positivity), ?_⟩
  intro t ht
  let F : ℝ → ℝ := fun s => s + t * ψ s
  have hfc : Continuous F := continuous_id.add (continuous_const.mul hψ.continuous)
  have hfp : ∀ s, F (s + 1) = F s + 1 := by
    intro s
    dsimp only [F]
    rw [hper]
    ring
  have hsmall : |t| * (C : ℝ) < 1 / 2 := by
    have hd : 0 < 2 * ((C : ℝ) + 1) := by positivity
    have h := (lt_div_iff₀ hd).mp (show |t| < 1 / (2 * ((C : ℝ) + 1)) by
      simpa only [one_div] using ht)
    nlinarith [abs_nonneg t, C.coe_nonneg]
  have hlower : ∀ x y, x ≤ y → (1 / 2 : ℝ) * (y - x) ≤ F y - F x := by
    intro x y hxy
    have hdiff := hψ.dist_le_mul y x
    rw [Real.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hxy)] at hdiff
    have hb : |t * (ψ y - ψ x)| ≤ |t| * (C : ℝ) * (y - x) := by
      rw [abs_mul, mul_assoc]
      exact mul_le_mul_of_nonneg_left hdiff (abs_nonneg t)
    have hbot := (abs_le.mp hb).1
    have hc := mul_le_mul_of_nonneg_right hsmall.le (sub_nonneg.mpr hxy)
    dsimp only [F]
    nlinarith
  obtain ⟨e, L, he, hL⟩ := DifferentialGeometry.Analysis.exists_homeomorph_affinePeriodic_of_lowerSlope
    hfc hfp (by norm_num : (0 : ℝ) < 1 / 2) hlower
  have hep : ∀ s, e (s + 1) = e s + 1 := by simpa only [he] using hfp
  have hemono : Monotone e := by
    intro x y hxy
    have hh := hlower x y hxy
    simp only [he]
    nlinarith
  have hFm : LipschitzWith (‖t‖₊ * C) (fun s => t * ψ s) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq, ← mul_sub, abs_mul, NNReal.coe_mul, coe_nnnorm, Real.norm_eq_abs, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hψ.dist_le_mul x y) (abs_nonneg t)
  have heLip : LipschitzWith (1 + ‖t‖₊ * C) e := by
    have h := LipschitzWith.id.add hFm
    intro x y
    simpa only [he, F, id_eq] using h x y
  let δ := affineCircleHomeomorph e hep
  refine ⟨δ, ?_, ?_, 1 + ‖t‖₊ * C, L, ?_⟩
  · intro s
    change (e s : loopCircle) = ((s + t * ψ s : ℝ) : loopCircle)
    rw [he]
  · refine ⟨e, e.continuous, (fun _ => rfl), Or.inl ⟨hemono, hep⟩⟩
  · exact affineCircleHomeomorph_lipschitz e hep heLip hL


end DifferentialGeometry.Geometry

end

noncomputable section

open Set Filter Function MeasureTheory ContinuousMap
open DifferentialGeometry.Topology
open scoped Topology NNReal ENNReal Manifold ContDiff

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

theorem mem_weaklyMonotoneDiskCompetitors_comp_of_boundary_reparametrization
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : freeLoop M} {u : C(closedDisk, M)}
    (hu : u ∈ weaklyMonotoneDiskCompetitors g γ)
    (φ : C(closedDisk, closedDisk)) {K : ℝ≥0} (hφ : LipschitzWith K φ)
    (δ : C(loopCircle, loopCircle)) (hδ : IsWeaklyMonotoneOnce δ)
    (hboundary : ∀ θ, φ (diskBoundary θ) = diskBoundary (δ θ)) :
    u.comp φ ∈ weaklyMonotoneDiskCompetitors g γ ∧
      diskTrace (u.comp φ) = (diskTrace u).comp δ := by
  obtain ⟨⟨σ, hσ, htrace⟩, L, hL⟩ := hu
  have htr : diskTrace (u.comp φ) = (diskTrace u).comp δ := by
    ext θ
    change u (φ (diskBoundary θ)) = u (diskBoundary (δ θ))
    rw [hboundary]
  refine ⟨⟨⟨σ.comp δ, hσ.comp hδ, ?_⟩, L * K, ?_⟩, htr⟩
  · rw [htr, htrace]
    rfl
  · intro z w
    exact (hL (φ z) (φ w)).trans (by
      change (L : ℝ≥0∞) * edist (φ z) (φ w) ≤ (↑(L * K) : ℝ≥0∞) * edist z w
      rw [ENNReal.coe_mul, mul_assoc]
      gcongr
      exact hφ z w)

theorem disk_energy_inf_le_comp_of_boundary_reparametrization
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : freeLoop M} {u : C(closedDisk, M)}
    (hu : u ∈ weaklyMonotoneDiskCompetitors g γ)
    (φ : C(closedDisk, closedDisk)) {K : ℝ≥0} (hφ : LipschitzWith K φ)
    (δ : C(loopCircle, loopCircle)) (hδ : IsWeaklyMonotoneOnce δ)
    (hboundary : ∀ θ, φ (diskBoundary θ) = diskBoundary (δ θ)) :
    sInf ((fun v : C(closedDisk, M) => riemannianDiskEnergy g v) ''
      weaklyMonotoneDiskCompetitors g γ) ≤ riemannianDiskEnergy g (u.comp φ) := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro _ ⟨v, _, rfl⟩
    exact riemannianDiskEnergy_nonneg g v
  · exact mem_image_of_mem _
      (mem_weaklyMonotoneDiskCompetitors_comp_of_boundary_reparametrization g hu φ hφ δ hδ hboundary).1

theorem exists_free_boundary_disk_variations
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : freeLoop M}
    {ψ : ℝ → ℝ} {C : ℝ≥0} (hψ : LipschitzWith C ψ) (hper : Periodic ψ 1) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t| < ε →
      ∃ δ : loopCircle ≃ₜ loopCircle, ∃ φ : closedDisk ≃ₜ closedDisk,
        (∀ s : ℝ, δ (s : loopCircle) = ((s + t * ψ s : ℝ) : loopCircle)) ∧
        (∀ z : closedDisk, (φ z : ℂ) = radialExtension (geometricCircleHomeomorph δ) z) ∧
        (∀ θ, φ (diskBoundary θ) = diskBoundary (δ θ)) ∧
        (∃ K L : ℝ≥0, LipschitzWith K φ ∧ LipschitzWith L φ.symm) ∧
        ∀ u : C(closedDisk, M), u ∈ weaklyMonotoneDiskCompetitors g γ →
          u.comp ⟨φ, φ.continuous⟩ ∈ weaklyMonotoneDiskCompetitors g γ ∧
          diskTrace (u.comp ⟨φ, φ.continuous⟩) =
            (diskTrace u).comp ⟨δ, δ.continuous⟩ ∧
          sInf ((fun v : C(closedDisk, M) => riemannianDiskEnergy g v) ''
            weaklyMonotoneDiskCompetitors g γ) ≤ riemannianDiskEnergy g (u.comp ⟨φ, φ.continuous⟩) := by
  obtain ⟨ε, hε, hvar⟩ := exists_circle_variation_of_periodic_lipschitz hψ hper
  refine ⟨ε, hε, fun t ht => ?_⟩
  obtain ⟨δ, hδ, hδmono, K, L, hK, hL⟩ := hvar t ht
  obtain ⟨Cf, hf⟩ := geometricCircleHomeomorph_lipschitz δ hK
  obtain ⟨Ci, hi⟩ := geometricCircleHomeomorph_lipschitz δ.symm hL
  rw [← geometricCircleHomeomorph_symm] at hi
  let φ := radialDiskHomeomorph (geometricCircleHomeomorph δ) hf hi
  have hφLip := radialDiskHomeomorph_lipschitz (geometricCircleHomeomorph δ) hf hi
  have hbdry (θ : loopCircle) : φ (diskBoundary θ) = diskBoundary (δ θ) := by
    apply Subtype.ext
    change radialExtension (geometricCircleHomeomorph δ) (AddCircle.toCircle θ : ℂ) =
      (AddCircle.toCircle (δ θ) : ℂ)
    rw [radialExtension_circle, geometricCircleHomeomorph_boundary]
  refine ⟨δ, φ, hδ, fun _ => rfl, hbdry,
    ⟨_, _, hφLip, radialDiskHomeomorph_symm_lipschitz _ hf hi⟩, fun u hu => ?_⟩
  have hcomp := mem_weaklyMonotoneDiskCompetitors_comp_of_boundary_reparametrization
    g hu ⟨φ, φ.continuous⟩ hφLip ⟨δ, δ.continuous⟩ hδmono hbdry
  exact ⟨hcomp.1, hcomp.2, disk_energy_inf_le_comp_of_boundary_reparametrization
    g hu ⟨φ, φ.continuous⟩ hφLip ⟨δ, δ.continuous⟩ hδmono hbdry⟩

end DifferentialGeometry.Geometry

end

noncomputable section

open Set Filter Function MeasureTheory ContinuousMap
open DifferentialGeometry.Topology DifferentialGeometry.Analysis
open scoped Topology NNReal ENNReal Manifold ContDiff

namespace DifferentialGeometry.Geometry


private theorem isWeaklyMonotoneOnce_symm_of_circle_variation
    {ψ : ℝ → ℝ} {C : ℝ≥0} (hψ : LipschitzWith C ψ) (hper : Periodic ψ 1)
    {t : ℝ} (ht : |t| * (C : ℝ) < 1 / 2)
    (δ : loopCircle ≃ₜ loopCircle)
    (hδ : ∀ s : ℝ, δ (s : loopCircle) = ((s + t * ψ s : ℝ) : loopCircle)) :
    IsWeaklyMonotoneOnce (⟨δ.symm, δ.symm.continuous⟩ : C(loopCircle, loopCircle)) := by
  let F : ℝ → ℝ := fun s => s + t * ψ s
  have hfc : Continuous F := continuous_id.add (continuous_const.mul hψ.continuous)
  have hfp : ∀ s, F (s + 1) = F s + 1 := by
    intro s
    dsimp only [F]
    rw [hper]
    ring
  have hlower : ∀ x y, x ≤ y → (1 / 2 : ℝ) * (y - x) ≤ F y - F x := by
    intro x y hxy
    have hdiff := hψ.dist_le_mul y x
    rw [Real.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hxy)] at hdiff
    have hb : |t * (ψ y - ψ x)| ≤ |t| * (C : ℝ) * (y - x) := by
      rw [abs_mul, mul_assoc]
      exact mul_le_mul_of_nonneg_left hdiff (abs_nonneg t)
    have hbot := (abs_le.mp hb).1
    have hc := mul_le_mul_of_nonneg_right ht.le (sub_nonneg.mpr hxy)
    dsimp only [F]
    nlinarith
  obtain ⟨e, L, he, hL⟩ := exists_homeomorph_affinePeriodic_of_lowerSlope
    hfc hfp (by norm_num : (0 : ℝ) < 1 / 2) hlower
  have heperiod : ∀ s, e (s + 1) = e s + 1 := by simpa only [he] using hfp
  have hemono : Monotone e := by
    intro x y hxy
    have h := hlower x y hxy
    simp only [he]
    linarith
  have helift : ∀ s : ℝ, δ (s : loopCircle) = (e s : loopCircle) := by
    intro s
    rw [hδ, he]
  exact isWeaklyMonotoneOnce_symm_of_monotone_lift δ e helift hemono heperiod

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T3Space M]

theorem tendsto_radialDiskEnergyFirstVariation_of_minimizing_sequence
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : freeLoop M}
    {u : ℕ → C(closedDisk, M)} (hu : ∀ n, u n ∈ weaklyMonotoneDiskCompetitors g γ)
    (hmin : Tendsto (fun n => riemannianDiskEnergy g (u n)) atTop
      (𝓝 (sInf ((fun v : C(closedDisk, M) => riemannianDiskEnergy g v) ''
        weaklyMonotoneDiskCompetitors g γ))))
    {ψ : ℝ → ℝ} {C : ℝ≥0} (hψ : Differentiable ℝ ψ)
    (hψLip : LipschitzWith C ψ) (hper : Periodic ψ 1) :
    Tendsto (fun n => radialDiskEnergyFirstVariation g (u n) ψ) atTop (𝓝 0) := by
  classical
  let m := sInf ((fun v : C(closedDisk, M) => riemannianDiskEnergy g v) ''
    weaklyMonotoneDiskCompetitors g γ)
  obtain ⟨ε, hε, hcircle⟩ := exists_circle_variation_of_periodic_lipschitz hψLip hper
  let r := min ε (2 * ((C : ℝ) + 1))⁻¹
  have hr : 0 < r := lt_min hε (inv_pos.mpr (by positivity))
  have hscalar : ∀ t : ℝ, |t| < r → ∀ n : ℕ, ∃ q : ℝ,
      m ≤ q ∧ |q - riemannianDiskEnergy g (u n) -
        t * radialDiskEnergyFirstVariation g (u n) ψ| ≤
      (2 * (C : ℝ) ^ 2) * t ^ 2 * riemannianDiskEnergy g (u n) := by
    intro t ht n
    have hteps : |t| < ε := ht.trans_le (min_le_left _ _)
    have htsmall : |t| * (C : ℝ) < 1 / 2 := by
      have hd : 0 < 2 * ((C : ℝ) + 1) := by positivity
      have htr : |t| < 1 / (2 * ((C : ℝ) + 1)) := by
        simpa only [one_div] using ht.trans_le (min_le_right _ _)
      have h := (lt_div_iff₀ hd).mp htr
      nlinarith [abs_nonneg t, C.coe_nonneg]
    obtain ⟨δ, hδ, hδmono, K, L, hK, hL⟩ := hcircle t hteps
    obtain ⟨Cf, hf⟩ := geometricCircleHomeomorph_lipschitz δ hK
    obtain ⟨Ci, hi⟩ := geometricCircleHomeomorph_lipschitz δ.symm hL
    rw [← geometricCircleHomeomorph_symm] at hi
    let φ := radialDiskHomeomorph (geometricCircleHomeomorph δ) hf hi
    have hφLip := radialDiskHomeomorph_symm_lipschitz _ hf hi
    have hbdry (θ : loopCircle) : φ.symm (diskBoundary θ) = diskBoundary (δ.symm θ) := by
      apply Subtype.ext
      change radialExtension (geometricCircleHomeomorph δ).symm (AddCircle.toCircle θ : ℂ) =
        (AddCircle.toCircle (δ.symm θ) : ℂ)
      rw [radialExtension_circle, geometricCircleHomeomorph_symm, geometricCircleHomeomorph_boundary]
    have hmono := isWeaklyMonotoneOnce_symm_of_circle_variation hψLip hper htsmall δ hδ
    refine ⟨riemannianDiskEnergy g ((u n).comp ⟨φ.symm, φ.symm.continuous⟩), ?_, ?_⟩
    · exact disk_energy_inf_le_comp_of_boundary_reparametrization g (hu n)
        ⟨φ.symm, φ.symm.continuous⟩ hφLip ⟨δ.symm, δ.symm.continuous⟩ hmono hbdry
    · obtain ⟨_, Cu, hCu⟩ := hu n
      exact abs_riemannianDiskEnergy_inverse_radial_sub_le g hCu hψ hψLip htsmall.le δ hδ hf hi
  let Q : ℕ → ℝ → ℝ := fun n t => if ht : |t| < r then (hscalar t ht n).choose else 0
  apply tendsto_zero_of_quadratic_variations (Q := Q) hr hmin
  · intro t ht
    apply Eventually.of_forall
    intro n
    simp only [Q, dite_eq_left ht]
    exact (hscalar t ht n).choose_spec.1
  · intro t ht
    apply Eventually.of_forall
    intro n
    simp only [Q, dite_eq_left ht]
    exact (hscalar t ht n).choose_spec.2

end DifferentialGeometry.Geometry

end
