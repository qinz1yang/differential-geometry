import DifferentialGeometry.Analysis.Integration.Integral.ComplexDerivative
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Replacement.WeakLimit
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Replacement.DiskFilling
import DifferentialGeometry.Analysis.Sobolev.Euclidean.TargetApproximation.Subsets
import Mathlib.Topology.Order.LiminfLimsup

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.Analysis

variable {ι : Type*} [Fintype ι]

private theorem liminf_le_of_eventually_le_of_tendsto
    {a b : ℕ → ℝ} {L : ℝ} (ha : ∀ n, 0 ≤ a n) (hab : ∀ᶠ n in atTop, a n ≤ b n)
    (hb : Tendsto b atTop (𝓝 L)) : liminf a atTop ≤ L := by
  have hbounded : IsBoundedUnder (· ≥ ·) atTop a := by
    refine ⟨0, ?_⟩
    change ∀ᶠ n in atTop, 0 ≤ a n
    exact Eventually.of_forall ha
  have h := liminf_le_liminf hab hbounded hb.isCoboundedUnder_ge
  exact h.trans_eq hb.liminf_eq


theorem target_energy_weak_filling_limit_le
    {K : Set (EuclideanSpace ℝ ι)} (hK : IsCompact K)
    (A : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hA : ContinuousOn A K) (hpos : ∀ y ∈ K, ∀ v, 0 ≤ A y v v)
    {Λ D : ℝ} (hΛ : ∀ y ∈ K, ‖A y‖ ≤ Λ) (hΛ0 : 0 ≤ Λ) (hD : 0 ≤ D)
    (u f : ℕ → ℂ → EuclideanSpace ℝ ι) (Cu Cf : ℕ → ℝ≥0)
    (hu : ∀ n, LipschitzWith (Cu n) (u n)) (hf : ∀ n, LipschitzWith (Cf n) (f n))
    {r R : ℝ} (hR1 : R < 1)
    (ρ : ℕ → ℝ) (hρ : ∀ n, ρ n ∈ Icc r R)
    (huK : ∀ n, MapsTo (u n) (Metric.closedBall (0 : ℂ) 1) K)
    (hfK : ∀ n, MapsTo (f n) (Metric.closedBall (0 : ℂ) 1) K)
    (hfix : ∀ n z, ρ n ≤ ‖z‖ → f n z = u n z)
    (hfill : ∀ n, (∫ z in Metric.closedBall (0 : ℂ) (ρ n),
      (‖fderiv ℝ (f n) z 1‖ ^ 2 + ‖fderiv ℝ (f n) z Complex.I‖ ^ 2) / 2) ≤
        D * ∫ z in {z : ℂ | ‖z‖ ∈ Icc r R}, ‖fderiv ℝ (u n) z‖ ^ 2)
    (w : ℂ → EuclideanSpace ℝ ι) (G : Fin 2 → ℂ → EuclideanSpace ℝ ι)
    (hwK : ∀ᵐ z ∂volume.restrict (Metric.ball (0 : ℂ) 1), w z ∈ K)
    (hae : ∀ᵐ z ∂volume.restrict (Metric.ball (0 : ℂ) 1),
      Tendsto (fun n => u n z) atTop (𝓝 (w z)))
    (hG : ∀ j, MemLp (G j) 2 (volume.restrict (Metric.ball (0 : ℂ) 1)))
    (hder : ∀ j : Fin 2, Tendsto (fun n => eLpNorm (fun z =>
      fderiv ℝ (u n) z (Complex.orthonormalBasisOneI j) - G j z)
      2 (volume.restrict (Metric.ball (0 : ℂ) 1))) atTop (𝓝 0))
    (ψ : ℕ → ℕ) (hψ : StrictMono ψ)
    {Eq : ℝ}
    (hLSC : Eq ≤ liminf (fun n => ∑ j : Fin 2,
      ∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1,
        A (f (ψ n) (Complex.orthonormalBasisOneI.repr.symm x))
          (fderiv ℝ (fun y => f (ψ n) (Complex.orthonormalBasisOneI.repr.symm y))
            x (EuclideanSpace.single j 1))
          (fderiv ℝ (fun y => f (ψ n) (Complex.orthonormalBasisOneI.repr.symm y))
            x (EuclideanSpace.single j 1))) atTop) :
    Eq ≤ 4 * Λ * D * (∫ z in {z : ℂ | ‖z‖ ∈ Icc r R},
      ‖G 0 z‖ ^ 2 + ‖G 1 z‖ ^ 2) +
      2 * ∫ z in Metric.ball (0 : ℂ) 1 \ Metric.closedBall 0 r,
        (A (w z) (G 0 z) (G 0 z) + A (w z) (G 1 z) (G 1 z)) / 2 := by
  let S := {z : ℂ | ‖z‖ ∈ Icc r R}
  let O := Metric.ball (0 : ℂ) 1 \ Metric.closedBall 0 r
  have hS : MeasurableSet S := (measurableSet_Icc.preimage continuous_norm.measurable)
  have hO : MeasurableSet O := Metric.isOpen_ball.measurableSet.diff measurableSet_closedBall
  have hS1 : S ⊆ Metric.ball (0 : ℂ) 1 := fun z hz => Metric.mem_ball.mpr
    (by simpa only [dist_zero_right] using hz.2.trans_lt hR1)
  have hO1 : O ⊆ Metric.ball (0 : ℂ) 1 := sdiff_subset
  let Iform := fun _ : EuclideanSpace ℝ ι => innerSL ℝ (E := EuclideanSpace ℝ ι)
  have hlimS := Sobolev.Euclidean.tendsto_complex_target_energy_on_subset_of_strong_approximation
    hK Iform continuousOn_const u Cu hu huK w G hwK hae hG hder hS hS1
  have hlimO := Sobolev.Euclidean.tendsto_complex_target_energy_on_subset_of_strong_approximation
    hK A hA u Cu hu huK w G hwK hae hG hder hO hO1
  have heq (v : EuclideanSpace ℝ ι) : innerSL ℝ v v = ‖v‖ ^ 2 := real_inner_self_eq_norm_sq v
  simp only [Iform, heq, integral_div] at hlimS
  have hlimS' := hlimS.const_mul 2
  simp only [mul_div_cancel₀ _ (show (2 : ℝ) ≠ 0 by norm_num)] at hlimS'
  let e := fun n => ∫ z in Metric.closedBall (0 : ℂ) 1,
    (A (f n z) (fderiv ℝ (f n) z 1) (fderiv ℝ (f n) z 1) +
      A (f n z) (fderiv ℝ (f n) z Complex.I) (fderiv ℝ (f n) z Complex.I)) / 2
  have hballEq : volume.restrict (Metric.ball (0 : ℂ) 1) =
      volume.restrict (Metric.closedBall (0 : ℂ) 1) := by
    apply Measure.restrict_congr_set
    have hnull := measure_eq_zero_iff_ae_notMem.mp (Measure.addHaar_sphere volume (0 : ℂ) 1)
    filter_upwards [hnull] with z hz
    apply propext
    change dist z (0 : ℂ) < 1 ↔ dist z 0 ≤ 1
    exact ⟨le_of_lt, fun h => lt_of_le_of_ne h hz⟩
  have houterEq (n : ℕ) :
      (∫ z in Metric.closedBall (0 : ℂ) 1 \ Metric.closedBall 0 r,
        (A (u n z) (fderiv ℝ (u n) z 1) (fderiv ℝ (u n) z 1) +
          A (u n z) (fderiv ℝ (u n) z Complex.I) (fderiv ℝ (u n) z Complex.I)) / 2) =
      ∫ z in O, (A (u n z) (fderiv ℝ (u n) z 1) (fderiv ℝ (u n) z 1) +
        A (u n z) (fderiv ℝ (u n) z Complex.I) (fderiv ℝ (u n) z Complex.I)) / 2 := by
    have heqS : Metric.closedBall (0 : ℂ) 1 \ Metric.closedBall 0 r =ᵐ[volume] O := by
      have hnull := measure_eq_zero_iff_ae_notMem.mp (Measure.addHaar_sphere volume (0 : ℂ) 1)
      filter_upwards [hnull] with z hz
      apply propext
      change (dist z (0 : ℂ) ≤ 1 ∧ z ∉ Metric.closedBall 0 r) ↔
        (dist z (0 : ℂ) < 1 ∧ z ∉ Metric.closedBall 0 r)
      exact and_congr_left fun _ => ⟨fun h => lt_of_le_of_ne h hz, le_of_lt⟩
    exact setIntegral_congr_set heqS
  have hePos (n : ℕ) : 0 ≤ e n := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_closedBall] with z hz
    exact div_nonneg (add_nonneg (hpos _ (hfK n hz) _) (hpos _ (hfK n hz) _)) (by norm_num)
  have hbound (n : ℕ) : 2 * e n ≤
      4 * Λ * D * (∫ z in S,
        ‖fderiv ℝ (u n) z 1‖ ^ 2 + ‖fderiv ℝ (u n) z Complex.I‖ ^ 2) +
      2 * ∫ z in O, (A (u n z) (fderiv ℝ (u n) z 1) (fderiv ℝ (u n) z 1) +
        A (u n z) (fderiv ℝ (u n) z Complex.I) (fderiv ℝ (u n) z Complex.I)) / 2 := by
    have h := integral_target_energy_le_of_exterior_eq_of_filling_bound
      (hf n) (hu n) A hA hpos hΛ hΛ0 (hρ n).1 ((hρ n).2.trans hR1.le)
      (hfK n) (huK n) (hfix n) (hfill n)
    rw [houterEq n] at h
    have hop := integral_opNorm_sq_le_two_sum_columns (hu n)
      (hS1.trans Metric.ball_subset_closedBall)
    have hc := mul_le_mul_of_nonneg_left hop (mul_nonneg hΛ0 hD)
    change e n ≤ _ at h
    nlinarith
  have hsumEq (n : ℕ) : (∑ j : Fin 2,
      ∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1,
        A (f (ψ n) (Complex.orthonormalBasisOneI.repr.symm x))
          (fderiv ℝ (fun y => f (ψ n) (Complex.orthonormalBasisOneI.repr.symm y))
            x (EuclideanSpace.single j 1))
          (fderiv ℝ (fun y => f (ψ n) (Complex.orthonormalBasisOneI.repr.symm y))
            x (EuclideanSpace.single j 1))) = 2 * e (ψ n) := by
    rw [sum_integral_target_energy_comp_complex_repr_symm (hf (ψ n)) hK A hA (hfK (ψ n))]
    rw [hballEq]
  simp_rw [hsumEq] at hLSC
  exact hLSC.trans (liminf_le_of_eventually_le_of_tendsto
    (fun n => mul_nonneg (by norm_num) (hePos (ψ n)))
    (Eventually.of_forall fun n => hbound (ψ n))
    (((hlimS'.const_mul (4 * Λ * D)).add (hlimO.const_mul 2)).comp hψ.tendsto_atTop))

end DifferentialGeometry.Analysis

end

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.Analysis

variable {ι : Type*} [Fintype ι]

theorem exists_original_weak_replacement_energy_le
    {K U : Set (EuclideanSpace ℝ ι)} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (T : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) (hT : ContDiff ℝ ∞ T)
    (hTK : MapsTo T U K) (hfix : ∀ y ∈ K, T y = y) {L : ℝ}
    (hL : ∀ x, ‖fderiv ℝ T x‖ ≤ L)
    {Ω : Set (EuclideanSpace ℝ (Fin 2))} (hΩ : IsOpen Ω)
    {w : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ ι}
    (hw : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => w x i) Ω)
    (hwK : ∀ᵐ x ∂volume.restrict Ω, w x ∈ K)
    (hball : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ⊆ Ω)
    {r R η : ℝ} (hr : 0 < r) (hrR : r < R) (hR1 : R < 1) (hη : 0 < η)
    (htube : ∀ p ∈ K, Metric.ball p η ⊆ U)
    (A : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hA : ContinuousOn A K) (hpos : ∀ y ∈ K, ∀ v, 0 ≤ A y v v)
    {Λ : ℝ} (hΛ : ∀ y ∈ K, ‖A y‖ ≤ Λ) (hΛ0 : 0 ≤ Λ)
    (hsmall : (4 * Real.pi * R / (R - r)) *
      (∫ z in {z : ℂ | ‖z‖ ∈ Icc r R},
        ‖(WithLp.toLp 2 (fun i => (hw i).weakGrad (Complex.orthonormalBasisOneI.repr z) 0) :
          EuclideanSpace ℝ ι)‖ ^ 2 +
        ‖(WithLp.toLp 2 (fun i => (hw i).weakGrad (Complex.orthonormalBasisOneI.repr z) 1) :
          EuclideanSpace ℝ ι)‖ ^ 2) < η ^ 2) :
    ∃ (q : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ ι)
      (hq : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => q x i) (Metric.ball 0 1)),
      (∀ᵐ x ∂volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1), q x ∈ K) ∧
      (q =ᵐ[volume.restrict
        (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1 \ Metric.closedBall 0 R)] w) ∧
      (∑ j : Fin 2, ∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1,
        A (q x) (WithLp.toLp 2 (fun i => (hq i).weakGrad x j))
          (WithLp.toLp 2 (fun i => (hq i).weakGrad x j))) ≤
        4 * Λ * ((5 * Real.pi ^ 2 * R / (R - r)) * L ^ 2) *
          (∫ z in {z : ℂ | ‖z‖ ∈ Icc r R},
            ‖(WithLp.toLp 2 (fun i => (hw i).weakGrad
              (Complex.orthonormalBasisOneI.repr z) 0) : EuclideanSpace ℝ ι)‖ ^ 2 +
            ‖(WithLp.toLp 2 (fun i => (hw i).weakGrad
              (Complex.orthonormalBasisOneI.repr z) 1) : EuclideanSpace ℝ ι)‖ ^ 2) +
        2 * ∫ z in Metric.ball (0 : ℂ) 1 \ Metric.closedBall 0 r,
          (A (w (Complex.orthonormalBasisOneI.repr z))
              (WithLp.toLp 2 (fun i => (hw i).weakGrad (Complex.orthonormalBasisOneI.repr z) 0))
              (WithLp.toLp 2 (fun i => (hw i).weakGrad (Complex.orthonormalBasisOneI.repr z) 0)) +
            A (w (Complex.orthonormalBasisOneI.repr z))
              (WithLp.toLp 2 (fun i => (hw i).weakGrad (Complex.orthonormalBasisOneI.repr z) 1))
              (WithLp.toLp 2 (fun i => (hw i).weakGrad
                (Complex.orthonormalBasisOneI.repr z) 1))) / 2 := by
  let Bunit := Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1
  let Bcomplex := Metric.ball (0 : ℂ) 1
  let e := Complex.orthonormalBasisOneI.repr
  let G := fun (j : Fin 2) (z : ℂ) =>
    (WithLp.toLp 2 (fun i => (hw i).weakGrad (e z) j) : EuclideanSpace ℝ ι)
  let S := {z : ℂ | ‖z‖ ∈ Icc r R}
  have hS : MeasurableSet S := measurableSet_Icc.preimage continuous_norm.measurable
  have hS1 : S ⊆ Bcomplex := fun z hz => Metric.mem_ball.mpr
    (by simpa only [dist_zero_right] using hz.2.trans_lt hR1)
  have hBG (j : Fin 2) : MemLp (fun x =>
      (WithLp.toLp 2 (fun i => (hw i).weakGrad x j) : EuclideanSpace ℝ ι)) 2
      (volume.restrict Bunit) := MemLp.of_eval_piLp fun i =>
    ((hw i).weakGrad_component_memLp j).mono_measure
      (Measure.restrict_mono_set volume (Metric.ball_subset_closedBall.trans hball))
  have hG (j : Fin 2) : MemLp (G j) 2 (volume.restrict Bcomplex) :=
    (hBG j).comp_measurePreserving
      (Sobolev.Euclidean.measurePreserving_complex_plane_repr_ball 1)
  have hwKc : ∀ᵐ z ∂volume.restrict Bcomplex, w (e z) ∈ K :=
    (Sobolev.Euclidean.measurePreserving_complex_plane_repr_ball 1).quasiMeasurePreserving.ae
      (ae_restrict_of_ae_restrict_of_subset
        (Metric.ball_subset_closedBall.trans hball) hwK)
  obtain ⟨u, Cu, B, hB, hu, hus, huK, hval, hder, hae, hbound, _⟩ :=
    Sobolev.Euclidean.exists_lipschitz_complex_target_approximation_tendsto_energy_on_ball
      hK hU hKU T hT.contDiffOn hTK hfix hΩ hw hwK hball A hA
  let Ifm := fun _ : EuclideanSpace ℝ ι => innerSL ℝ (E := EuclideanSpace ℝ ι)
  have hlim := Sobolev.Euclidean.tendsto_complex_target_energy_on_subset_of_strong_approximation
    hK Ifm continuousOn_const u Cu hu huK (fun z => w (e z)) G hwKc hae hG hder hS hS1
  have heq (v : EuclideanSpace ℝ ι) : innerSL ℝ v v = ‖v‖ ^ 2 := real_inner_self_eq_norm_sq v
  simp only [Ifm, heq, integral_div] at hlim
  have hlim' := hlim.const_mul 2
  simp only [mul_div_cancel₀ _ (show (2 : ℝ) ≠ 0 by norm_num)] at hlim'
  let c := 4 * Real.pi * R / (R - r)
  have hc : 0 ≤ c := by
    have hR : 0 < R := hr.trans hrR
    have hd : 0 < R - r := sub_pos.mpr hrR
    dsimp [c]
    positivity
  have hsmallEventually : ∀ᶠ n in atTop,
      c * (∫ z in S, ‖fderiv ℝ (u n) z 1‖ ^ 2 + ‖fderiv ℝ (u n) z Complex.I‖ ^ 2) < η ^ 2 :=
    (hlim'.const_mul c).eventually (gt_mem_nhds hsmall)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hsmallEventually
  let un := fun n => u (n + N)
  let Cun := fun n => Cu (n + N)
  have hun (n : ℕ) : LipschitzWith (Cun n) (un n) := hu (n + N)
  have hunK (n : ℕ) := huK (n + N)
  have hsmalln (n : ℕ) : (2 * Real.pi * R / (R - r)) *
      (∫ z in S, ‖fderiv ℝ (un n) z‖ ^ 2) < η ^ 2 := by
    have h := hN (n + N) (Nat.le_add_left N n)
    have hop := integral_opNorm_sq_le_two_sum_columns (hun n)
      (hS1.trans Metric.ball_subset_closedBall)
    have hcoef : 0 ≤ 2 * Real.pi * R / (R - r) := by
      have hR : 0 < R := hr.trans hrR
      have hd : 0 < R - r := sub_pos.mpr hrR
      positivity
    apply (mul_le_mul_of_nonneg_left hop hcoef).trans_lt
    have hcEq : (2 * Real.pi * R / (R - r)) *
        (2 * ∫ z in S, ‖fderiv ℝ (un n) z 1‖ ^ 2 +
          ‖fderiv ℝ (un n) z Complex.I‖ ^ 2) =
        c * ∫ z in S, ‖fderiv ℝ (un n) z 1‖ ^ 2 +
          ‖fderiv ℝ (un n) z Complex.I‖ ^ 2 := by dsimp only [c]; ring
    rw [hcEq]
    exact h
  have haeV : ∀ᵐ x ∂volume.restrict Bunit,
      Tendsto (fun n => un n (e.symm x)) atTop (𝓝 (w x)) := by
    have hm := e.symm.measurePreserving.restrict_preimage (s := Bcomplex)
      Metric.isOpen_ball.measurableSet
    have hpre : e.symm ⁻¹' Bcomplex = Bunit := by
      ext x
      simp only [Bcomplex, Bunit, mem_preimage, Metric.mem_ball,
        dist_zero_right, LinearIsometryEquiv.norm_map]
    rw [hpre] at hm
    have h := hm.quasiMeasurePreserving.ae hae
    filter_upwards [h] with x hx
    simpa only [e, LinearIsometryEquiv.apply_symm_apply, un, Function.comp_def] using
      hx.comp (tendsto_add_atTop_nat N)
  have hballEq : volume.restrict (Metric.ball (0 : ℂ) 1) =
      volume.restrict (Metric.closedBall (0 : ℂ) 1) := by
    apply Measure.restrict_congr_set
    have hnull := measure_eq_zero_iff_ae_notMem.mp (Measure.addHaar_sphere volume (0 : ℂ) 1)
    filter_upwards [hnull] with z hz
    apply propext
    change dist z (0 : ℂ) < 1 ↔ dist z 0 ≤ 1
    exact ⟨le_of_lt, fun h => lt_of_le_of_ne h hz⟩
  have hboundn (n : ℕ) :
      (∫ z in Metric.closedBall (0 : ℂ) 1, ‖fderiv ℝ (un n) z‖ ^ 2) ≤ B := by
    rw [← hballEq]
    exact hbound (n + N)
  obtain ⟨ρ, f, q, hq, hρ, hfl, hfixf, htarget, hcap, hqK, hqw, ψ, hs, hψ,
      hrep, haq, hweak, hLSC⟩ :=
    exists_weak_replacement_of_small_annular_energy un Cun hun hK hunK hr hrR hR1 hη htube
      hsmalln hboundn T (hT.differentiable (by simp)) hL hTK hfix haeV
  choose Cf hff using hfl
  have haen : ∀ᵐ z ∂volume.restrict Bcomplex,
      Tendsto (fun n => un n z) atTop (𝓝 (w (e z))) :=
    hae.mono fun z hz => hz.comp (tendsto_add_atTop_nat N)
  have hdern (j : Fin 2) := (hder j).comp (tendsto_add_atTop_nat N)
  have hD : 0 ≤ (5 * Real.pi ^ 2 * R / (R - r)) * L ^ 2 := by
    have hR : 0 < R := hr.trans hrR
    have hd : 0 < R - r := sub_pos.mpr hrR
    positivity
  have ht := target_energy_weak_filling_limit_le hK A hA hpos hΛ hΛ0 hD
    un f Cun Cf hun hff hR1 ρ hρ hunK htarget hfixf hcap
    (fun z => w (e z)) G hwKc haen hG hdern ψ hψ (hLSC A hA hpos)
  exact ⟨q, hq, hqK, hqw, ht⟩

end DifferentialGeometry.Analysis

end
