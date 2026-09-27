import DifferentialGeometry.Analysis.Sobolev.Euclidean.Embedding.Rellich.Lipschitz
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Gradient.QuadraticLowerSemicontinuity
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Replacement.DiskFilling
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal

namespace DifferentialGeometry.Analysis.Sobolev

variable {d : ℕ} [NeZero d] {ι : Type*} [Fintype ι]

omit [NeZero d] [Fintype ι] in
private theorem ae_eq_on_exterior_of_tendsto_of_eventually_eq
    {f u : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ ι}
    {v w : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ ι}
    {R : ℝ} {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (hv : ∀ᵐ x ∂volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1),
      Tendsto (fun n => f (φ n) x) atTop (𝓝 (v x)))
    (hw : ∀ᵐ x ∂volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1),
      Tendsto (fun n => u n x) atTop (𝓝 (w x)))
    (hfix : ∀ n x, R ≤ ‖x‖ → f n x = u n x) :
    v =ᵐ[volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1 \
      Metric.closedBall 0 R)] w := by
  have hsub : Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1 \ Metric.closedBall 0 R ⊆
      Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1 := sdiff_subset
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hv,
    ae_restrict_of_ae_restrict_of_subset hsub hw,
    ae_restrict_mem (Metric.isOpen_ball.measurableSet.diff measurableSet_closedBall)]
      with x hxv hxw hx
  have hRx : R ≤ ‖x‖ := (lt_of_not_ge (by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hx.2)).le
  have heq : (fun n => f (φ n) x) = (fun n => u (φ n) x) := funext fun n => hfix (φ n) x hRx
  rw [heq] at hxv
  exact tendsto_nhds_unique hxv (hxw.comp hφ.tendsto_atTop)

theorem exists_weak_target_replacement_limit_of_lipschitz_fillings
    (f u : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ ι)
    (Klip : ℕ → ℝ≥0) (hf : ∀ n, LipschitzWith (Klip n) (f n))
    {K : Set (EuclideanSpace ℝ ι)} (hK : IsCompact K)
    (himage : ∀ n, ∀ᵐ x ∂volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1),
      f n x ∈ K)
    {B : ℝ} (hB : ∀ n,
      (∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1, ‖fderiv ℝ (f n) x‖ ^ 2) ≤ B)
    {w : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ ι}
    (hw : ∀ᵐ x ∂volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1),
      Tendsto (fun n => u n x) atTop (𝓝 (w x)))
    {R : ℝ} (hfix : ∀ n x, R ≤ ‖x‖ → f n x = u n x) :
    ∃ (hs : ∀ n i, DeGiorgi.MemW1pWitness 2 (fun x => f n x i) (Metric.ball 0 1))
      (φ : ℕ → ℕ) (q : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ ι)
      (hq : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => q x i) (Metric.ball 0 1)),
      StrictMono φ ∧
      (∀ n i x j, (hs n i).weakGrad x j =
        fderiv ℝ (fun y => f n y i) x (EuclideanSpace.single j 1)) ∧
      Tendsto (fun n => eLpNorm (fun x => f (φ n) x - q x) 2
        (volume.restrict (Metric.ball 0 1))) atTop (𝓝 0) ∧
      (∀ᵐ x ∂volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1),
        Tendsto (fun n => f (φ n) x) atTop (𝓝 (q x))) ∧
      (∀ᵐ x ∂volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1), q x ∈ K) ∧
      (q =ᵐ[volume.restrict
        (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1 \ Metric.closedBall 0 R)] w) ∧
      ∀ i (z : Lp (EuclideanSpace ℝ (Fin d)) 2
        (volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1))),
        Tendsto (fun n => inner ℝ (DeGiorgi.gradLpOfWitness (hs (φ n) i)) z) atTop
          (𝓝 (inner ℝ (DeGiorgi.gradLpOfWitness (hq i)) z)) := by
  obtain ⟨D, hD⟩ := hK.isBounded.exists_norm_le
  have hfn : ∀ n, ∀ᵐ x ∂volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1),
      ‖f n x‖ ≤ D := fun n => (himage n).mono fun x hx => hD _ hx
  obtain ⟨hs, φ, q, hq, hφ, hrep, _, hL2, hae, hqK, hweak⟩ :=
    exists_weak_memW1p_subseq_of_lipschitz_of_energy_bound f Klip hf hfn hB hK.isClosed himage
  exact ⟨hs, φ, q, hq, hφ, hrep, hL2, hae, hqK,
    ae_eq_on_exterior_of_tendsto_of_eventually_eq hφ hae hw hfix, hweak⟩

end DifferentialGeometry.Analysis.Sobolev

end

noncomputable section
open Set MeasureTheory Filter
open scoped Topology NNReal ENNReal

namespace DifferentialGeometry.Analysis

variable {ι : Type*} [Fintype ι]

private theorem integral_norm_fderiv_complex_repr
    (f : ℂ → EuclideanSpace ℝ ι) :
    (∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1,
      ‖fderiv ℝ (fun y => f (Complex.orthonormalBasisOneI.repr.symm y)) x‖ ^ 2) =
      ∫ z in Metric.ball (0 : ℂ) 1, ‖fderiv ℝ f z‖ ^ 2 := by
  let e := Complex.orthonormalBasisOneI.repr.symm
  have he (x : EuclideanSpace ℝ (Fin 2)) :
      ‖fderiv ℝ (fun y => f (e y)) x‖ = ‖fderiv ℝ f (e x)‖ := by
    rw [show (fun y => f (e y)) = f ∘ e.toContinuousLinearEquiv by rfl,
      e.toContinuousLinearEquiv.comp_right_fderiv]
    exact ContinuousLinearMap.opNorm_comp_linearIsometryEquiv _ e
  change (∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1,
      ‖fderiv ℝ (fun y => f (e y)) x‖ ^ 2) = _
  simp_rw [he]
  have hs : e ⁻¹' Metric.ball (0 : ℂ) 1 = Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
    ext x
    simp only [mem_preimage, Metric.mem_ball, dist_zero_right, LinearIsometryEquiv.norm_map]
  have h := e.measurePreserving.setIntegral_preimage_emb
    e.toHomeomorph.toMeasurableEquiv.measurableEmbedding (fun z => ‖fderiv ℝ f z‖ ^ 2)
    (Metric.ball (0 : ℂ) 1)
  rw [hs] at h
  exact h

theorem exists_weak_replacement_of_small_annular_energy
    (u : ℕ → ℂ → EuclideanSpace ℝ ι) (Cu : ℕ → ℝ≥0)
    (hu : ∀ n, LipschitzWith (Cu n) (u n))
    {K U : Set (EuclideanSpace ℝ ι)} (hK : IsCompact K)
    (huK : ∀ n, MapsTo (u n) (Metric.closedBall (0 : ℂ) 1) K)
    {r R η : ℝ} (hr : 0 < r) (hrR : r < R) (hR1 : R < 1) (hη : 0 < η)
    (htube : ∀ p ∈ K, Metric.ball p η ⊆ U)
    (hsmall : ∀ n, (2 * Real.pi * R / (R - r)) *
      (∫ z in {z : ℂ | ‖z‖ ∈ Icc r R}, ‖fderiv ℝ (u n) z‖ ^ 2) < η ^ 2)
    {B : ℝ} (hB : ∀ n,
      (∫ z in Metric.closedBall (0 : ℂ) 1, ‖fderiv ℝ (u n) z‖ ^ 2) ≤ B)
    (T : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) (hT : Differentiable ℝ T) {L : ℝ}
    (hL : ∀ x, ‖fderiv ℝ T x‖ ≤ L) (hTK : MapsTo T U K) (hfix : ∀ y ∈ K, T y = y)
    {w : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ ι}
    (hw : ∀ᵐ x ∂volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1),
      Tendsto (fun n => u n (Complex.orthonormalBasisOneI.repr.symm x)) atTop (𝓝 (w x))) :
    ∃ (ρ : ℕ → ℝ) (f : ℕ → ℂ → EuclideanSpace ℝ ι)
      (q : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ ι)
      (hq : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => q x i) (Metric.ball 0 1)),
      (∀ n, ρ n ∈ Icc r R) ∧
      (∀ n, ∃ C : ℝ≥0, LipschitzWith C (f n)) ∧
      (∀ n z, ρ n ≤ ‖z‖ → f n z = u n z) ∧
      (∀ n, MapsTo (f n) (Metric.closedBall (0 : ℂ) 1) K) ∧
      (∀ n, (∫ z in Metric.closedBall (0 : ℂ) (ρ n),
        (‖fderiv ℝ (f n) z 1‖ ^ 2 + ‖fderiv ℝ (f n) z Complex.I‖ ^ 2) / 2) ≤
          (5 * Real.pi ^ 2 * R / (R - r)) * L ^ 2 *
            ∫ z in {z : ℂ | ‖z‖ ∈ Icc r R}, ‖fderiv ℝ (u n) z‖ ^ 2) ∧
      (∀ᵐ x ∂volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1), q x ∈ K) ∧
      (q =ᵐ[volume.restrict
        (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1 \ Metric.closedBall 0 R)] w) ∧
      ∃ (ψ : ℕ → ℕ)
        (hs : ∀ n i, DeGiorgi.MemW1pWitness 2
          (fun x : EuclideanSpace ℝ (Fin 2) =>
            f n (Complex.orthonormalBasisOneI.repr.symm x) i) (Metric.ball 0 1)),
        StrictMono ψ ∧
        (∀ n i x j, (hs n i).weakGrad x j =
          fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 2) =>
            f n (Complex.orthonormalBasisOneI.repr.symm y) i) x (EuclideanSpace.single j 1)) ∧
        (∀ᵐ x ∂volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1),
          Tendsto (fun n => f (ψ n) (Complex.orthonormalBasisOneI.repr.symm x))
            atTop (𝓝 (q x))) ∧
        (∀ i (z : Lp (EuclideanSpace ℝ (Fin 2)) 2
            (volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1))),
          Tendsto (fun n => inner ℝ (DeGiorgi.gradLpOfWitness (hs (ψ n) i)) z) atTop
            (𝓝 (inner ℝ (DeGiorgi.gradLpOfWitness (hq i)) z))) ∧
        ∀ A : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι →L[ℝ] ℝ,
          ContinuousOn A K → (∀ y ∈ K, ∀ v, 0 ≤ A y v v) →
          (∑ j : Fin 2, ∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1,
            A (q x) (WithLp.toLp 2 (fun i => (hq i).weakGrad x j))
              (WithLp.toLp 2 (fun i => (hq i).weakGrad x j))) ≤
            liminf (fun n => ∑ j : Fin 2,
              ∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1,
                A (f (ψ n) (Complex.orthonormalBasisOneI.repr.symm x))
                  (fderiv ℝ (fun y => f (ψ n) (Complex.orthonormalBasisOneI.repr.symm y))
                    x (EuclideanSpace.single j 1))
                  (fderiv ℝ (fun y => f (ψ n) (Complex.orthonormalBasisOneI.repr.symm y))
                    x (EuclideanSpace.single j 1))) atTop := by
  classical
  have hQR : ∀ n, MapsTo (u n) (Metric.closedBall (0 : ℂ) R) K := fun n =>
    (huK n).mono_left (Metric.closedBall_subset_closedBall hR1.le)
  choose ρ hρ f hfl htrace hconst htarget henergy using fun n =>
    exists_radius_retracted_filling_energy_le_annulus (hu n) hr hrR (hQR n) hη htube
      (hsmall n) T hT hL hTK hfix
  choose Cf hf using hfl
  have htarget1 (n : ℕ) : MapsTo (f n) (Metric.closedBall (0 : ℂ) 1) K := by
    intro z hz
    by_cases hn : ‖z‖ ≤ R
    · exact htarget n (Metric.mem_closedBall.mpr (by simpa only [dist_zero_right] using hn))
    · rw [htrace n z ((hρ n).2.trans (lt_of_not_ge hn).le)]
      exact huK n hz
  let D := (5 * Real.pi ^ 2 * R / (R - r)) * L ^ 2
  have hR : 0 < R := hr.trans hrR
  have hdiff : 0 < R - r := sub_pos.mpr hrR
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have huInt (n : ℕ) : IntegrableOn (fun z => ‖fderiv ℝ (u n) z‖ ^ 2)
      (Metric.closedBall (0 : ℂ) 1) := by
    let : IsFiniteMeasure (volume.restrict (Metric.closedBall (0 : ℂ) 1)) :=
      isFiniteMeasure_restrict.mpr (isCompact_closedBall (0 : ℂ) 1).measure_lt_top.ne
    have hm : MemLp (fderiv ℝ (u n)) 2 (volume.restrict (Metric.closedBall (0 : ℂ) 1)) :=
      MemLp.of_bound (measurable_fderiv ℝ (u n)).aestronglyMeasurable (Cu n)
        (Eventually.of_forall fun _ => norm_fderiv_le_of_lipschitz ℝ (hu n))
    exact hm.norm.integrable_sq
  have hfillBound (n : ℕ) : (∫ z in Metric.closedBall (0 : ℂ) (ρ n),
      (‖fderiv ℝ (f n) z 1‖ ^ 2 + ‖fderiv ℝ (f n) z Complex.I‖ ^ 2) / 2) ≤ D * B := by
    apply (henergy n).trans
    apply mul_le_mul_of_nonneg_left _ hD
    apply le_trans _ (hB n)
    exact setIntegral_mono_set (huInt n) (Eventually.of_forall fun z => sq_nonneg _) (by
      apply Eventually.of_forall
      intro z hz
      exact Metric.mem_closedBall.mpr (by simpa only [dist_zero_right] using hz.2.trans hR1.le))
  have hwhole (n : ℕ) : (∫ z in Metric.closedBall (0 : ℂ) 1, ‖fderiv ℝ (f n) z‖ ^ 2) ≤
      4 * (D * B + B) := by
    have h := integral_fderiv_sq_le_of_exterior_eq_of_filling_energy_bound
      (hf n) (hu n) ((hρ n).2.trans hR1.le) (htrace n) (hfillBound n)
    linarith [hB n]
  let fv := fun n x => f n (Complex.orthonormalBasisOneI.repr.symm x)
  have hfV (n : ℕ) : LipschitzWith (Cf n) (fv n) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    exact ((hf n).dist_le_mul _ _).trans_eq
      (congrArg (fun z : ℝ => (Cf n : ℝ) * z)
        (Complex.orthonormalBasisOneI.repr.symm.isometry.dist_eq x y))
  have hfvK (n : ℕ) : ∀ᵐ x ∂volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1),
      fv n x ∈ K := by
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
    apply htarget1 n
    simpa only [Metric.mem_closedBall, dist_zero_right, LinearIsometryEquiv.norm_map] using
      (show ‖x‖ ≤ 1 from by simpa only [dist_zero_right] using (Metric.mem_ball.mp hx).le)
  have hfvB (n : ℕ) : (∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1,
      ‖fderiv ℝ (fv n) x‖ ^ 2) ≤ 4 * (D * B + B) := by
    rw [show fv n = (fun x => f n (Complex.orthonormalBasisOneI.repr.symm x)) by rfl,
      integral_norm_fderiv_complex_repr]
    have hfInt : IntegrableOn (fun z => ‖fderiv ℝ (f n) z‖ ^ 2)
        (Metric.closedBall (0 : ℂ) 1) := by
      let : IsFiniteMeasure (volume.restrict (Metric.closedBall (0 : ℂ) 1)) :=
        isFiniteMeasure_restrict.mpr (isCompact_closedBall (0 : ℂ) 1).measure_lt_top.ne
      have hm : MemLp (fderiv ℝ (f n)) 2 (volume.restrict (Metric.closedBall (0 : ℂ) 1)) :=
        MemLp.of_bound (measurable_fderiv ℝ (f n)).aestronglyMeasurable (Cf n)
          (Eventually.of_forall fun _ => norm_fderiv_le_of_lipschitz ℝ (hf n))
      exact hm.norm.integrable_sq
    exact (setIntegral_mono_set hfInt (Eventually.of_forall fun z => sq_nonneg _)
      (Eventually.of_forall fun z hz => Metric.ball_subset_closedBall hz)).trans (hwhole n)
  obtain ⟨hs, ψ, q, hq, hψ, hrep, hL2, hae, hqK, hqw, hweak⟩ :=
    Sobolev.exists_weak_target_replacement_limit_of_lipschitz_fillings fv
      (fun n x => u n (Complex.orthonormalBasisOneI.repr.symm x)) Cf hfV hK hfvK hfvB hw
      (R := R) (fun n x hx => htrace n _ ((hρ n).2.trans (by
        simpa only [LinearIsometryEquiv.norm_map] using hx)))
  refine ⟨ρ, f, q, hq, hρ, (fun n => ⟨Cf n, hf n⟩), htrace, htarget1, henergy,
    hqK, hqw, ψ, hs, hψ, hrep, hae, hweak, ?_⟩
  intro A hA hpos
  have hc : ContinuousOn (fun y => ‖A y‖) K :=
    (@continuous_norm (EuclideanSpace ℝ ι →L[ℝ]
      EuclideanSpace ℝ ι →L[ℝ] ℝ) inferInstance).comp_continuousOn hA
  obtain ⟨Λ, hΛ⟩ := hK.bddAbove_image hc
  have hmaps (n : ℕ) : MapsTo (fv (ψ n))
      (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1) K := by
    intro x hx
    apply htarget1 (ψ n)
    rw [Metric.mem_closedBall, dist_zero_right, LinearIsometryEquiv.norm_map]
    exact (show ‖x‖ < 1 by simpa only [Metric.mem_ball, dist_zero_right] using hx).le
  have hAm (n : ℕ) : AEStronglyMeasurable (fun x => A (fv (ψ n) x))
      (volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1)) :=
    (hA.comp (hfV (ψ n)).continuous.continuousOn (hmaps n)).aestronglyMeasurable
      Metric.isOpen_ball.measurableSet
  have hAb (n : ℕ) : ∀ᵐ x ∂volume.restrict
      (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1), ‖A (fv (ψ n) x)‖ ≤ Λ := by
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
    exact hΛ (mem_image_of_mem _ (hmaps n hx))
  have hconv : ∀ᵐ x ∂volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1),
      Tendsto (fun n => A (fv (ψ n) x)) atTop (𝓝 (A (q x))) := by
    filter_upwards [hae, hqK, ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx hqx hxB
    exact (show Tendsto A (𝓝[K] q x) (𝓝 (A (q x))) from hA (q x) hqx).comp
      (tendsto_nhdsWithin_iff.mpr
      ⟨hx, Eventually.of_forall fun n => hmaps n hxB⟩)
  exact Sobolev.Euclidean.sum_integral_quadratic_gradient_column_le_liminf_of_tendsto_inner
    (fun n => fv (ψ n)) q (fun n i => hs (ψ n) i) hq (fun n => Cf (ψ n))
    (fun n => hfV (ψ n)) (fun n i j => Eventually.of_forall fun x => hrep (ψ n) i x j)
    hweak (fun n x => A (fv (ψ n) x)) (fun x => A (q x)) hAm Λ hAb hconv
    (fun n => (hfvK (ψ n)).mono fun x hx v => hpos _ hx v)

end DifferentialGeometry.Analysis

end
