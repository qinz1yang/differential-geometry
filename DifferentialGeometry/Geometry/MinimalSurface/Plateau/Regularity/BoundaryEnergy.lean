import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.BoundaryCap
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.Subsets
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.Rotation
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.EmbeddedSequence
import DifferentialGeometry.Analysis.Asymptotics.LimsupDecay

noncomputable section

open Manifold Set Metric Filter MeasureTheory
open DifferentialGeometry.Topology DifferentialGeometry.Analysis
open scoped Manifold ContDiff NNReal ENNReal Topology

namespace DifferentialGeometry.Geometry

private theorem integral_annulus_closedDisk_eq_boundaryLens_sdiff (f : ℂ → ℝ) (a b : ℝ) :
    (∫ z in {z : ℂ | dist z (-1) ∈ Icc a b} ∩ closedBall (0 : ℂ) 1, f z) =
      ∫ z in boundaryLens b \ boundaryLens a, f z := by
  have hzero : ∀ᵐ z : ℂ ∂volume, z ∉ sphere (-1 : ℂ) a := by
    rw [ae_iff]
    convert Measure.addHaar_sphere volume (-1 : ℂ) a using 1
    congr 1
    ext z
    simp only [mem_ofPred_eq, not_not]
  apply setIntegral_congr_set
  filter_upwards [hzero] with z hz
  have hne : dist z (-1) ≠ a := hz
  apply propext
  change ((a ≤ dist z (-1) ∧ dist z (-1) ≤ b) ∧ dist z 0 ≤ 1) ↔
    ((dist z (-1) ≤ b ∧ dist z 0 ≤ 1) ∧ ¬ (dist z (-1) ≤ a ∧ dist z 0 ≤ 1))
  constructor
  · rintro ⟨⟨ha, hb⟩, hD⟩
    refine ⟨⟨hb, hD⟩, ?_⟩
    intro h
    exact hne (le_antisymm h.1 ha)
  · rintro ⟨⟨hb, hD⟩, hn⟩
    exact ⟨⟨le_of_not_ge (fun h => hn ⟨h, hD⟩), hb⟩, hD⟩

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PreconnectedSpace M]

theorem exists_uniform_boundary_energy_contraction
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {Φ : M → F}
    (hΦ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) 1 Φ)
    {r : F → M} {N : Set F} (hN : IsOpen N)
    (hr : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ r N)
    (hΦN : range Φ ⊆ N) (hleft : Function.LeftInverse r Φ)
    (γ : freeLoop M) {KΓ J : ℝ≥0}
    (hΓ : LipschitzWith KΓ (fun t : ℝ => Φ (γ (t : loopCircle))))
    (hInv : AntilipschitzWith J (fun θ : loopCircle => Φ (γ θ)))
    {U : Set F} {η : ℝ} (hη : 0 < η)
    (hηU : ∀ p ∈ range Φ, closedBall p η ⊆ U)
    (T : F → F) (LT : ℝ≥0) (hT : Differentiable ℝ T)
    (hLT : ∀ y, ‖fderiv ℝ T y‖ ≤ LT) (hmap : MapsTo T U (range Φ))
    (hfix : ∀ y ∈ range Φ, T y = y) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧ C / (1 + C) < 1 ∧
      ∀ (u : C(closedDisk, M)) (K : ℝ≥0),
      (∀ x y, riemannianEDistOf g (u x) (u y) ≤ (K : ℝ≥0∞) * edist x y) →
      ∀ ψ : CircleDeg1Lift, Continuous ψ →
      (∀ t : ℝ, u (diskBoundary (t : loopCircle)) = γ ((ψ t : ℝ) : loopCircle)) →
      ∀ s : ℝ, 0 < s → s < 1 / 4 →
      (∀ ρ ∈ Ioo s (2 * s), ψ (1 - Real.arccos (ρ / 2) / Real.pi) -
        ψ (Real.arccos (ρ / 2) / Real.pi) ≤ 2 / 3) →
      (∫ z in boundaryLens (2 * s), diskMapEnergyDensity g (diskExtension u) z) ≤ ε₀ →
      (∫ z in boundaryLens s, diskMapEnergyDensity g (diskExtension u) z) ≤
        (C / (1 + C)) *
          (∫ z in boundaryLens (2 * s), diskMapEnergyDensity g (diskExtension u) z) +
          (riemannianDiskEnergy g u -
            sInf ((fun w : C(closedDisk, M) => riemannianDiskEnergy g w) ''
              weaklyMonotoneDiskCompetitors g γ)) / (1 + C) := by
  obtain ⟨ε, Ccap, hε, hCcap, hcap⟩ := exists_uniform_boundary_cap_energy_estimate
    g hΦ.continuous hN hr hΦN hleft γ hΓ hInv hη hηU T LT hT hLT hmap hfix
  obtain ⟨CΦ, hCΦ, hEmbed⟩ :=
    exists_integral_norm_fderiv_comp_diskExtension_sq_le_pullback_on_subsets
      g hΦ hN (hr.of_le (by simp)) hΦN hleft
  let H : ℝ := 4 * (CΦ : ℝ) ^ 2
  have hH : 0 < H := by dsimp only [H]; positivity
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let ε₀ := ε * Real.log 2 / H
  let C := Ccap * H / Real.log 2
  have hC : 0 ≤ C := div_nonneg (mul_nonneg hCcap hH.le) hlog.le
  have hden : 0 < 1 + C := by linarith
  refine ⟨ε₀, C, by exact div_pos (mul_pos hε hlog) hH, hC,
    (div_lt_one hden).mpr (by linarith), ?_⟩
  intro u K hu ψ hψ htrace s hs hsquarter hshort hsmall
  let f : ℂ → F := Φ ∘ diskExtension u
  let d : ℂ → ℝ := diskMapEnergyDensity g (diskExtension u)
  let A := pullbackMetricCoefficients g r
  let e : ℂ → ℝ := fun z =>
    (A (f z) (fderiv ℝ f z 1) (fderiv ℝ f z 1) +
      A (f z) (fderiv ℝ f z Complex.I) (fderiv ℝ f z Complex.I)) / 2
  let S : Set ℂ := {z : ℂ | dist z (-1) ∈ Icc s (2 * s)} ∩ closedBall (0 : ℂ) 1
  have hSD : S ⊆ closedBall (0 : ℂ) 1 := inter_subset_right
  have hScap : S ⊆ boundaryLens (2 * s) := fun z hz => ⟨hz.1.2, hz.2⟩
  have hsub : boundaryLens s ⊆ boundaryLens (2 * s) := by
    intro z hz
    exact ⟨(closedBall_subset_closedBall (by linarith : s ≤ 2 * s)) hz.1, hz.2⟩
  have hdi : IntegrableOn d (closedBall (0 : ℂ) 1) := integrable_diskMapEnergyDensity g hu
  have hd0 (z : ℂ) : 0 ≤ d z := by
    dsimp only [d, diskMapEnergyDensity]
    exact div_nonneg (add_nonneg (metric_inner_self_nonneg g _ _)
      (metric_inner_self_nonneg g _ _)) (by norm_num)
  have heq (V : Set ℂ) (hV : V ⊆ closedBall (0 : ℂ) 1) :
      (∫ z in V, d z) = ∫ z in V, e z := (hEmbed u K hu).2 V hV |>.2.2.1
  have hAnn : (∫ z in S, d z) =
      (∫ z in boundaryLens (2 * s), d z) - ∫ z in boundaryLens s, d z := by
    rw [show S = {z : ℂ | dist z (-1) ∈ Icc s (2 * s)} ∩ closedBall (0 : ℂ) 1 from rfl,
      integral_annulus_closedDisk_eq_boundaryLens_sdiff]
    exact setIntegral_sdiff (isClosed_closedBall.inter isClosed_closedBall).measurableSet
      (hdi.mono_set inter_subset_right) hsub
  have hAnnle : (∫ z in S, d z) ≤ ∫ z in boundaryLens (2 * s), d z :=
    setIntegral_mono_set (hdi.mono_set inter_subset_right)
      (Filter.Eventually.of_forall hd0) (Filter.Eventually.of_forall hScap)
  let B := H * ∫ z in S, d z
  have hB : (∫ z in S, ‖fderiv ℝ f z‖ ^ 2) ≤ B := by
    have h := (hEmbed u K hu).2 S hSD |>.2.2.2
    change (∫ z in S, ‖fderiv ℝ f z‖ ^ 2) ≤ H * ∫ z in S, e z at h
    rw [← heq S hSD] at h
    exact h
  have hratio : (2 * s) / s = 2 := by field_simp [hs.ne']
  have hBsmall : B / Real.log ((2 * s) / s) ≤ ε := by
    rw [hratio]
    apply (div_le_iff₀ hlog).mpr
    have hA : (∫ z in S, d z) ≤ ε₀ := hAnnle.trans hsmall
    have hmul := mul_le_mul_of_nonneg_left hA hH.le
    have heps : H * ε₀ = ε * Real.log 2 := by dsimp only [ε₀]; field_simp
    exact hmul.trans_eq heps
  have hftrace (t : ℝ) : f (circleMap 0 1 (2 * Real.pi * t)) = Φ (γ ((ψ t : ℝ) : loopCircle)) := by
    have hc : circleMap 0 1 (2 * Real.pi * t) = (diskBoundary (t : loopCircle) : ℂ) := by
      simp only [diskBoundary_coe, circleMap_zero, Complex.ofReal_one, one_mul]
    change Φ (diskExtension u _) = _
    rw [hc, diskExtension_coe, htrace]
  have hestimate := hcap f (CΦ * K) (hEmbed u K hu).1
    (fun z _ => mem_range_self (diskExtension u z)) ψ hψ hftrace s (2 * s) B
    hs (by linarith) (by linarith) hshort hB hBsmall
  change (∫ z in boundaryLens s, e z) ≤ Ccap * B / Real.log ((2 * s) / s) +
    ((∫ z in closedBall (0 : ℂ) 1, e z) - _) at hestimate
  rw [← heq (boundaryLens s) inter_subset_right,
    ← heq (closedBall (0 : ℂ) 1) Subset.rfl, hratio] at hestimate
  have hcoef : Ccap * B / Real.log 2 = C * ∫ z in S, d z := by
    dsimp only [C, B]
    ring
  rw [hcoef, hAnn] at hestimate
  change (∫ z in boundaryLens s, d z) ≤
    (C / (1 + C)) * (∫ z in boundaryLens (2 * s), d z) +
      ((∫ z in closedBall (0 : ℂ) 1, d z) - _) / (1 + C)
  rw [div_mul_eq_mul_div, ← add_div]
  apply (le_div_iff₀ hden).mpr
  nlinarith only [hestimate]

end DifferentialGeometry.Geometry

end

noncomputable section

open Manifold Set Metric MeasureTheory
open DifferentialGeometry.Topology DifferentialGeometry.Analysis
open scoped Manifold ContDiff NNReal ENNReal

namespace DifferentialGeometry.Geometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PreconnectedSpace M]

theorem exists_uniform_boundaryLens_radius_of_energy_bound
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {Φ : M → F} (hΦ : Continuous Φ)
    {r : F → M} {N : Set F} (hN : IsOpen N)
    (hr : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ r N)
    (hΦN : range Φ ⊆ N) (hleft : Function.LeftInverse r Φ)
    (γ : freeLoop M) {KΓ J : ℝ≥0}
    (hΓ : LipschitzWith KΓ (fun t : ℝ => Φ (γ (t : loopCircle))))
    (hInv : AntilipschitzWith J (fun θ : loopCircle => Φ (γ θ)))
    {U : Set F} {η : ℝ} (hη : 0 < η)
    (hηU : ∀ p ∈ range Φ, closedBall p η ⊆ U)
    (T : F → F) (LT : ℝ≥0) (hT : Differentiable ℝ T)
    (hLT : ∀ y, ‖fderiv ℝ T y‖ ≤ LT) (hmap : MapsTo T U (range Φ))
    (hfix : ∀ y ∈ range Φ, T y = y)
    {B : ℝ} (hB : 0 ≤ B) {ε R₀ : ℝ} (hε : 0 < ε) (hR₀ : 0 < R₀) :
    let A := pullbackMetricCoefficients g r
    let e : (ℂ → F) → ℂ → ℝ := fun f z =>
      (A (f z) (fderiv ℝ f z 1) (fderiv ℝ f z 1) +
        A (f z) (fderiv ℝ f z Complex.I) (fderiv ℝ f z Complex.I)) / 2
    ∃ a ∈ Ioo (0 : ℝ) (min R₀ 1),
      ∀ (f : ℂ → F) (Kf : ℝ≥0), LipschitzWith Kf f →
      MapsTo f (closedBall (0 : ℂ) 1) (range Φ) →
      ∀ ψ : CircleDeg1Lift, Continuous ψ →
      (∀ t : ℝ, f (circleMap 0 1 (2 * Real.pi * t)) = Φ (γ ((ψ t : ℝ) : loopCircle))) →
      (∀ ρ : ℝ, 0 < ρ → ρ < 1 → ψ (1 - Real.arccos (ρ / 2) / Real.pi) -
        ψ (Real.arccos (ρ / 2) / Real.pi) ≤ 2 / 3) →
      (∫ z in closedBall (0 : ℂ) 1, ‖fderiv ℝ f z‖ ^ 2) ≤ B →
      (∫ z in boundaryLens a, e f z) ≤ ε +
        ((∫ z in closedBall (0 : ℂ) 1, e f z) -
          sInf ((fun w : C(closedDisk, M) => riemannianDiskEnergy g w) ''
            weaklyMonotoneDiskCompetitors g γ)) := by
  obtain ⟨ε₀, C, hε₀, hC, hcap⟩ := exists_uniform_boundary_cap_energy_estimate
    g hΦ hN hr hΦN hleft γ hΓ hInv hη hηU T LT hT hLT hmap hfix
  let κ : ℝ := min ε₀ (ε / (C + 1))
  have hκ : 0 < κ := lt_min hε₀ (by positivity)
  let b : ℝ := min R₀ 1 / 2
  have hb : 0 < b := half_pos (lt_min hR₀ zero_lt_one)
  have hb1 : b < 1 := by dsimp only [b]; linarith [min_le_right R₀ (1 : ℝ)]
  have hbR : b < min R₀ 1 := by dsimp only [b]; linarith [lt_min hR₀ zero_lt_one]
  let logBound : ℝ := B / κ + 1
  have hM : 0 < logBound := by dsimp only [logBound]; positivity
  let a : ℝ := b / Real.exp logBound
  have ha : 0 < a := div_pos hb (Real.exp_pos _)
  have hab : a < b := div_lt_self hb ((Real.one_lt_exp_iff).mpr hM)
  have hlog : Real.log (b / a) = logBound := by
    have heq : b / a = Real.exp logBound := by dsimp only [a]; field_simp
    rw [heq, Real.log_exp]
  have hratio : B / Real.log (b / a) < κ := by
    rw [hlog]
    apply (div_lt_iff₀ hM).mpr
    have heq : κ * logBound = B + κ := by dsimp only [logBound]; field_simp
    rw [heq]
    linarith
  have hratio0 : 0 ≤ B / Real.log (b / a) := by rw [hlog]; positivity
  have hsmall : B / Real.log (b / a) ≤ ε₀ := hratio.le.trans (min_le_left _ _)
  have hCratio : C * B / Real.log (b / a) < ε := by
    have h₁ : C * (B / Real.log (b / a)) ≤ (C + 1) * (B / Real.log (b / a)) :=
      mul_le_mul_of_nonneg_right (by linarith) hratio0
    have h₂ : (C + 1) * (B / Real.log (b / a)) < (C + 1) * κ :=
      mul_lt_mul_of_pos_left hratio (by positivity)
    have h₃ : (C + 1) * κ ≤ ε := by
      have h := mul_le_mul_of_nonneg_left (min_le_right ε₀ (ε / (C + 1)))
        (show 0 ≤ C + 1 by positivity)
      apply h.trans_eq
      field_simp
    simpa only [mul_div_assoc] using h₁.trans_lt (h₂.trans_le h₃)
  refine ⟨a, ⟨ha, hab.trans hbR⟩, ?_⟩
  intro f Kf hf hfK ψ hψ htrace hshort henergy
  have hlocal := hcap f Kf hf hfK ψ hψ htrace a b B ha hab hb1
    (fun ρ hρ => hshort ρ (ha.trans hρ.1) (hρ.2.trans hb1))
    (by
      have hi := hf.integrableOn_norm_fderiv_sq
        (μ := volume) (isCompact_closedBall (0 : ℂ) 1).measure_ne_top
      exact (setIntegral_mono_set hi (Filter.Eventually.of_forall fun _ => sq_nonneg _)
        (Filter.Eventually.of_forall inter_subset_right)).trans henergy) hsmall
  exact hlocal.trans (add_le_add hCratio.le le_rfl)

end DifferentialGeometry.Geometry

end

noncomputable section

open Manifold Set Metric Filter MeasureTheory
open DifferentialGeometry.Topology DifferentialGeometry.Analysis
open scoped Manifold ContDiff NNReal ENNReal Topology

namespace DifferentialGeometry.Geometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PreconnectedSpace M]

theorem exists_uniform_boundary_energy_dyadic_decay
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {Φ : M → F}
    (hΦ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) 1 Φ)
    {r : F → M} {N : Set F} (hN : IsOpen N)
    (hr : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ r N)
    (hΦN : range Φ ⊆ N) (hleft : Function.LeftInverse r Φ)
    (γ : freeLoop M) {KΓ J : ℝ≥0}
    (hΓ : LipschitzWith KΓ (fun t : ℝ => Φ (γ (t : loopCircle))))
    (hInv : AntilipschitzWith J (fun θ : loopCircle => Φ (γ θ)))
    {U : Set F} {η : ℝ} (hη : 0 < η)
    (hηU : ∀ p ∈ range Φ, closedBall p η ⊆ U)
    (T : F → F) (LT : ℝ≥0) (hT : Differentiable ℝ T)
    (hLT : ∀ y, ‖fderiv ℝ T y‖ ≤ LT) (hmap : MapsTo T U (range Φ))
    (hfix : ∀ y ∈ range Φ, T y = y)
    (u : ℕ → C(closedDisk, M)) (hu : ∀ n, u n ∈ weaklyMonotoneDiskCompetitors g γ)
    (hmin : Tendsto (fun n => riemannianDiskEnergy g (u n)) atTop
      (𝓝 (sInf ((fun w : C(closedDisk, M) => riemannianDiskEnergy g w) ''
        weaklyMonotoneDiskCompetitors g γ))))
    (ψ : ℕ → CircleDeg1Lift) (hψ : ∀ n, Continuous (ψ n))
    (htrace : ∀ n (t : ℝ), u n (diskBoundary (t : loopCircle)) = γ ((ψ n t : ℝ) : loopCircle))
    (hthird : ∀ n, ψ n (1 / 3 : ℝ) = ψ n 0 + 1 / 3)
    (htwothird : ∀ n, ψ n (2 / 3 : ℝ) = ψ n 0 + 2 / 3) :
    ∃ δ θ B : ℝ, 0 < δ ∧ δ < 1 ∧ 0 ≤ θ ∧ θ < 1 ∧ 0 ≤ B ∧
      ∀ c ∈ sphere (0 : ℂ) 1, ∀ k : ℕ,
        limsup (fun n => ∫ z in closedBall c (δ / (2 : ℝ) ^ k) ∩ closedBall (0 : ℂ) 1,
          diskMapEnergyDensity g (diskExtension (u n)) z) atTop ≤ θ ^ k * B := by
  obtain ⟨ε₀, C, hε₀, hC, hθ1, hrec⟩ := exists_uniform_boundary_energy_contraction
    g hΦ hN hr hΦN hleft γ hΓ hInv hη hηU T LT hT hLT hmap hfix
  obtain ⟨Kf, _, Bglobal, hBglobal, hf, hfK, _, _, _, hbound, _, htotal, _⟩ :=
    exists_embedded_minimizing_sequence_bounds g hΦ hN (hr.of_le (by simp)) hΦN hleft u hu hmin
  let f : ℕ → ℂ → F := fun n => Φ ∘ diskExtension (u n)
  let A := pullbackMetricCoefficients g r
  let q : (ℂ → F) → ℂ → ℝ := fun v z =>
    (A (v z) (fderiv ℝ v z 1) (fderiv ℝ v z 1) +
      A (v z) (fderiv ℝ v z Complex.I) (fderiv ℝ v z Complex.I)) / 2
  let infimum := sInf ((fun w : C(closedDisk, M) => riemannianDiskEnergy g w) ''
    weaklyMonotoneDiskCompetitors g γ)
  let defect : ℕ → ℝ := fun n => riemannianDiskEnergy g (u n) - infimum
  have hdefect : Tendsto defect atTop (𝓝 0) := by
    simpa only [defect, infimum, sub_self] using hmin.sub_const infimum
  have hftrace (n : ℕ) (t : ℝ) : f n (circleMap 0 1 (2 * Real.pi * t)) =
      Φ (γ ((ψ n t : ℝ) : loopCircle)) := by
    have hc : circleMap 0 1 (2 * Real.pi * t) = (diskBoundary (t : loopCircle) : ℂ) := by
      simp only [diskBoundary_coe, circleMap_zero, Complex.ofReal_one, one_mul]
    change Φ (diskExtension (u n) _) = _
    rw [hc, diskExtension_coe, htrace]
  let ζ : ℝ → Circle := fun d => Circle.exp (2 * Real.pi * d)
  let Ψ : ℕ → ℝ → CircleDeg1Lift := fun n d =>
    ψ n * (CircleDeg1Lift.translate (Multiplicative.ofAdd d) : CircleDeg1Lift)
  have hΨcont (n : ℕ) (d : ℝ) : Continuous (Ψ n d) :=
    (ψ n).continuous_mul_translate (hψ n) d
  have hΨshort (n : ℕ) (d ρ : ℝ) (hρ : ρ < 1) :
      Ψ n d (1 - Real.arccos (ρ / 2) / Real.pi) -
        Ψ n d (Real.arccos (ρ / 2) / Real.pi) ≤ 2 / 3 := by
    change ψ n (d + (1 - Real.arccos (ρ / 2) / Real.pi)) -
      ψ n (d + Real.arccos (ρ / 2) / Real.pi) ≤ 2 / 3
    exact (ψ n).sub_shifted_arccos_endpoints_le_two_thirds (hthird n) (htwothird n) d hρ
  obtain ⟨δ, hδ, hsmallcap⟩ := exists_uniform_boundaryLens_radius_of_energy_bound
    g hΦ.continuous hN hr hΦN hleft γ hΓ hInv hη hηU T LT hT hLT hmap hfix
      hBglobal (half_pos hε₀) (by norm_num : (0 : ℝ) < 1 / 4)
  have hδ0 : 0 < δ := hδ.1
  have hδquarter : δ < 1 / 4 := hδ.2.trans_le (min_le_left _ _)
  have hsmallambient (n : ℕ) (d : ℝ) :
      (∫ z in boundaryLens δ, q (f n ∘ rotation (ζ d)) z) ≤ ε₀ / 2 + defect n := by
    have h := hsmallcap (f n ∘ rotation (ζ d)) (Kf n)
      (lipschitzWith_comp_rotation (hf n) (ζ d))
      (mapsTo_comp_rotation_closedDisk (hfK n) (ζ d))
      (Ψ n d) (hΨcont n d)
      (circle_lift_trace_comp_rotation (f n) (fun θ => Φ (γ θ)) (ψ n) (hftrace n) d)
      (fun ρ _ hρ1 => hΨshort n d ρ hρ1)
      (by rw [(rotation (ζ d)).integral_norm_fderiv_sq_comp_closedBall]; exact hbound n)
    change (∫ z in boundaryLens δ, q (f n ∘ rotation (ζ d)) z) ≤ ε₀ / 2 +
      ((∫ z in closedBall (0 : ℂ) 1, q (f n ∘ rotation (ζ d)) z) - infimum) at h
    have he : (∫ z in closedBall (0 : ℂ) 1, q (f n ∘ rotation (ζ d)) z) =
        riemannianDiskEnergy g (u n) := by
      rw [show (∫ z in closedBall (0 : ℂ) 1, q (f n ∘ rotation (ζ d)) z) =
        ∫ z in closedBall (0 : ℂ) 1, q (f n) z from
          integral_quadratic_fderiv_comp_rotation_closedBall A (f n) (ζ d) 1]
      exact htotal n
    rwa [he] at h
  have huLip (n : ℕ) : ∃ K : ℝ≥0, ∀ x y : closedDisk,
      riemannianEDistOf g (u n x) (u n y) ≤ (K : ℝ≥0∞) * edist x y := (hu n).2
  choose Ku hKu using huLip
  let v : ℕ → ℝ → C(closedDisk, M) := fun n d => rotatedDiskMap (u n) (ζ d)
  let en : ℕ → ℝ → ℂ → ℝ := fun n d => diskMapEnergyDensity g (diskExtension (v n d))
  have hvLip (n : ℕ) (d : ℝ) (x y : closedDisk) :
      riemannianEDistOf g (v n d x) (v n d y) ≤ (Ku n : ℝ≥0∞) * edist x y :=
    riemannian_lipschitz_rotatedDiskMap g (hKu n) (ζ d) x y
  have hvtrace (n : ℕ) (d t : ℝ) :
      v n d (diskBoundary (t : loopCircle)) = γ ((Ψ n d t : ℝ) : loopCircle) :=
    rotatedDiskMap_trace_lift (u n) γ (ψ n) (htrace n) d t
  have hvtotal (n : ℕ) (d : ℝ) : riemannianDiskEnergy g (v n d) =
      riemannianDiskEnergy g (u n) :=
    integral_diskMapEnergyDensity_rotatedDiskMap g (u n) (ζ d)
  have heqcap (n : ℕ) (d a : ℝ) :
      (∫ z in boundaryLens a, en n d z) =
        ∫ z in boundaryLens a, q (f n ∘ rotation (ζ d)) z := by
    rw [show (∫ z in boundaryLens a, en n d z) =
        ∫ z in closedBall (rotation (ζ d) (-1)) a ∩ closedBall (0 : ℂ) 1,
          diskMapEnergyDensity g (diskExtension (u n)) z from
      integral_diskMapEnergyDensity_rotatedDiskMap_boundaryLens g (u n) (ζ d) a]
    rw [show (∫ z in boundaryLens a, q (f n ∘ rotation (ζ d)) z) =
        ∫ z in closedBall (rotation (ζ d) (-1)) a ∩ closedBall (0 : ℂ) 1, q (f n) z from
      integral_quadratic_fderiv_comp_rotation_boundaryLens A (f n) (ζ d) a]
    exact integral_congr_ae (ae_restrict_of_ae
      (diskMapEnergyDensity_ae_eq_pullback_of_lipschitz g hΦ hN (hr.of_le (by simp)) hΦN hleft
        (diskExtension_riemannian_lipschitz g (hKu n))))
  have hsmall : ∀ᶠ n in atTop, ∀ d : ℝ, (∫ z in boundaryLens δ, en n d z) ≤ ε₀ := by
    filter_upwards [hdefect.eventually (gt_mem_nhds (half_pos hε₀))] with n hn
    intro d
    rw [heqcap]
    exact (hsmallambient n d).trans (by linarith)
  let θ := C / (1 + C)
  have hθ : 0 ≤ θ := div_nonneg hC (by linarith)
  let radius : ℕ → ℝ := fun k => δ / (2 : ℝ) ^ k
  have hradpos (k : ℕ) : 0 < radius k := div_pos hδ0 (by positivity)
  have hradle (k : ℕ) : radius k ≤ δ :=
    div_le_self hδ0.le (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
  have hradstep (k : ℕ) : 2 * radius (k + 1) = radius k := by
    dsimp only [radius]
    rw [pow_succ]
    field_simp
  have hdecay (d : ℝ) (k : ℕ) :
      limsup (fun n => ∫ z in boundaryLens (radius k), en n d z) atTop ≤ θ ^ k * ε₀ := by
    let a : ℕ → ℕ → ℝ := fun k n => ∫ z in boundaryLens (radius k), en n d z
    let err : ℕ → ℕ → ℝ := fun _ n => defect n / (1 + C)
    have herr (k : ℕ) : Tendsto (err k) atTop (𝓝 0) := by
      simpa only [err, zero_div] using hdefect.div_const (1 + C)
    have hdi (n : ℕ) : IntegrableOn (en n d) (closedBall (0 : ℂ) 1) :=
      integrable_diskMapEnergyDensity g (hvLip n d)
    have hd0 (n : ℕ) (z : ℂ) : 0 ≤ en n d z := by
      dsimp only [en, diskMapEnergyDensity]
      exact div_nonneg (add_nonneg (metric_inner_self_nonneg g _ _)
        (metric_inner_self_nonneg g _ _)) (by norm_num)
    have ha0 (k : ℕ) : ∀ᶠ n in atTop, 0 ≤ a k n :=
      Eventually.of_forall fun n => integral_nonneg (hd0 n)
    have hB : ∀ᶠ n in atTop, a 0 n ≤ ε₀ := by
      filter_upwards [hsmall] with n hn
      simpa only [a, radius, pow_zero, div_one] using hn d
    have harec (k : ℕ) : ∀ᶠ n in atTop, a (k + 1) n ≤ θ * a k n + err k n := by
      filter_upwards [hsmall] with n hn
      have hsubset : boundaryLens (radius k) ⊆ boundaryLens δ := by
        intro z hz
        exact ⟨(closedBall_subset_closedBall (hradle k)) hz.1, hz.2⟩
      have hsmallk : (∫ z in boundaryLens (2 * radius (k + 1)), en n d z) ≤ ε₀ := by
        rw [hradstep]
        exact (setIntegral_mono_set ((hdi n).mono_set inter_subset_right)
          (Eventually.of_forall (hd0 n)) (Eventually.of_forall hsubset)).trans (hn d)
      have hi := hrec (v n d) (Ku n) (hvLip n d) (Ψ n d) (hΨcont n d) (hvtrace n d)
        (radius (k + 1)) (hradpos _) ((hradle _).trans_lt hδquarter)
        (fun ρ hρ => hΨshort n d ρ (by linarith [hρ.2, hradle (k + 1)])) hsmallk
      rw [hvtotal] at hi
      simpa only [a, θ, err, defect, infimum, hradstep] using hi
    have haBound : IsBoundedUnder (· ≤ ·) atTop (a 0) := isBoundedUnder_of_eventually_le hB
    have hlim0 : limsup (a 0) atTop ≤ ε₀ :=
      limsup_le_of_le (isBoundedUnder_of_eventually_ge (ha0 0)).isCoboundedUnder_le hB
    have hk := limsup_le_pow_mul_limsup_of_eventually_le_succ a err hθ ha0 haBound herr harec k
    exact hk.trans (mul_le_mul_of_nonneg_left hlim0 (pow_nonneg hθ k))
  refine ⟨δ, θ, ε₀, hδ0, by linarith, hθ, hθ1, hε₀.le, ?_⟩
  intro c hc k
  let ξ : Circle := ⟨-c, by
    apply mem_sphere_zero_iff_norm.mpr
    simpa only [mem_sphere, dist_zero_right, norm_neg] using hc⟩
  obtain ⟨α, hα⟩ := Circle.exp_surjective ξ
  let d := α / (2 * Real.pi)
  have hζ : ζ d = ξ := by
    change Circle.exp (2 * Real.pi * (α / (2 * Real.pi))) = ξ
    rw [mul_div_cancel₀ _ (by positivity : 2 * Real.pi ≠ 0), hα]
  have hcenter : rotation (ζ d) (-1) = c := by
    rw [hζ, rotation_apply]
    change (-c) * (-1) = c
    ring
  have heq (n : ℕ) : (∫ z in boundaryLens (radius k), en n d z) =
      ∫ z in closedBall c (radius k) ∩ closedBall (0 : ℂ) 1,
        diskMapEnergyDensity g (diskExtension (u n)) z := by
    have h := integral_diskMapEnergyDensity_rotatedDiskMap_boundaryLens g (u n) (ζ d) (radius k)
    simpa only [hcenter] using h
  have hd := hdecay d k
  simpa only [heq, radius] using hd

end DifferentialGeometry.Geometry

end
