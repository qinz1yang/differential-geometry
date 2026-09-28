import DifferentialGeometry.Analysis.Sobolev.Euclidean.Embedding.Rellich.Basic
import DifferentialGeometry.External.DeGiorgi.BallExtensionEstimates
import DifferentialGeometry.External.DeGiorgi.SobolevSpace.Witnesses
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace DifferentialGeometry.Analysis.Sobolev

private theorem eLpNorm_two_le_of_lintegral_le
    {α F : Type*} [MeasurableSpace α] [NormedAddCommGroup F]
    {μ : Measure α} {f : α → F} {A : ℝ≥0∞}
    (hf : AEStronglyMeasurable f μ)
    (hA : ∫⁻ x, (ENNReal.ofReal ‖f x‖) ^ (2 : ℝ) ∂μ ≤ A) :
    eLpNorm f 2 μ ≤ A ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ∞) hf]
  simpa using ENNReal.rpow_le_rpow hA (by norm_num : (0 : ℝ) ≤ 1 / 2)

theorem rellich_kondrachov_W12_seq_unitBall
    {d : ℕ} [NeZero d]
    (u : ℕ → EuclideanSpace ℝ (Fin d) → ℝ)
    (hu : ∀ n, DeGiorgi.MemW1pWitness 2 (u n) (Metric.ball 0 1))
    {R : ℝ}
    (hfun : ∀ n, eLpNorm (u n) 2 (volume.restrict (Metric.ball 0 1)) ≤
      ENNReal.ofReal R)
    (hgrad : ∀ n, eLpNorm (hu n).weakGrad 2 (volume.restrict (Metric.ball 0 1)) ≤
      ENNReal.ofReal R) :
    ∃ (φ : ℕ → ℕ) (v : EuclideanSpace ℝ (Fin d) → ℝ), StrictMono φ ∧
      MemLp v 2 (volume.restrict (Metric.ball 0 1)) ∧
      Tendsto (fun n => eLpNorm (fun x => u (φ n) x - v x) 2
        (volume.restrict (Metric.ball 0 1))) atTop (𝓝 0) := by
  classical
  let E := EuclideanSpace ℝ (Fin d)
  let B : Set E := Metric.ball 0 1
  let Ω : Set E := Metric.ball 0 3
  let U (n : ℕ) := DeGiorgi.unitBallExtension (u n)
  let hu' (n : ℕ) : DeGiorgi.MemW1pWitness (ENNReal.ofReal (2 : ℝ)) (u n) B :=
    { memLp := by simpa using (hu n).memLp
      weakGrad := (hu n).weakGrad
      weakGrad_component_memLp := fun i => by simpa using (hu n).weakGrad_component_memLp i
      isWeakGrad := (hu n).isWeakGrad }
  have hext (n : ℕ) := DeGiorgi.exists_unitBall_W1p_extension (p := (2 : ℝ))
    (by norm_num) (hu' n)
  choose hw hcpt heq hfb hgb using hext
  let hwΩ (n : ℕ) : DeGiorgi.MemW1pWitness 2 (U n) Ω :=
    { memLp := by
        simpa using ((hw n).restrict Metric.isOpen_ball (subset_univ Ω)).memLp
      weakGrad := (hw n).weakGrad
      weakGrad_component_memLp := fun i => by
        simpa only [DeGiorgi.MemW1pWitness.restrict, ENNReal.ofReal_ofNat] using
          ((hw n).restrict Metric.isOpen_ball (subset_univ Ω)).weakGrad_component_memLp i
      isWeakGrad := ((hw n).restrict Metric.isOpen_ball (subset_univ Ω)).isWeakGrad }
  have hsup (n : ℕ) : tsupport (U n) ⊆ Ω := by
    have hs : tsupport (U n) ⊆ Metric.closedBall (0 : E) 2 := by
      apply closure_minimal _ Metric.isClosed_closedBall
      intro x hx
      by_contra hn
      have hnorm : 2 ≤ ‖x‖ := by
        simp only [Metric.mem_closedBall, dist_zero_right, not_le] at hn
        exact hn.le
      exact hx (DeGiorgi.unitBallExtension_eq_zero_of_two_le_norm hnorm)
    exact hs.trans (Metric.closedBall_subset_ball (by norm_num))
  have hU (n : ℕ) : DeGiorgi.MemW01p 2 (U n) Ω := by
    have hmem : DeGiorgi.MemW1p (ENNReal.ofReal (2 : ℝ)) (U n) Ω := by
      simpa using (hwΩ n).memW1p
    simpa using DeGiorgi.memW01p_of_memW1p_of_tsupport_subset Metric.isOpen_ball
      (by norm_num : (1 : ℝ) < 2) hmem (hcpt n) (hsup n)
  let A : ℝ≥0∞ := (ENNReal.ofReal R) ^ (2 : ℝ)
  let F : ℝ≥0∞ := DeGiorgi.CUnitBallExtensionFun d * A
  let G : ℝ≥0∞ := A + DeGiorgi.CUnitBallExtensionGrad d 2 * (A + A)
  let S : ℝ≥0∞ := F ^ (1 / 2 : ℝ) + d * G ^ (1 / 2 : ℝ)
  have hA : A ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
  have hF : F ≠ ∞ := by
    simp only [F, DeGiorgi.CUnitBallExtensionFun]
    exact ENNReal.mul_ne_top (by simp) hA
  have hG : G ≠ ∞ := by
    dsimp only [G, DeGiorgi.CUnitBallExtensionGrad]
    exact ENNReal.add_ne_top.mpr ⟨hA, ENNReal.mul_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (by norm_num)))
      (ENNReal.add_ne_top.mpr ⟨hA, hA⟩)⟩
  have hS : S ≠ ∞ := ENNReal.add_ne_top.mpr
    ⟨ENNReal.rpow_ne_top_of_nonneg (by norm_num) hF,
      ENNReal.mul_ne_top (by simp) (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hG)⟩
  have hfunpow (n : ℕ) :
      (∫⁻ x in B, (ENNReal.ofReal |u n x|) ^ (2 : ℝ)) ≤ A := by
    have hn := DeGiorgi.lintegral_rpow_norm_eq_eLpNorm_pow
      (μ := volume.restrict B) (f := u n) (by norm_num : (0 : ℝ) < 2)
      (hu n).memLp.aestronglyMeasurable
    norm_num only [ENNReal.ofReal_ofNat] at hn
    simpa only [Real.norm_eq_abs] using
      hn.le.trans (ENNReal.rpow_le_rpow (hfun n) (by norm_num : (0 : ℝ) ≤ 2))
  have hgradpow (n : ℕ) :
      (∫⁻ x in B, (ENNReal.ofReal ‖(hu n).weakGrad x‖) ^ (2 : ℝ)) ≤ A := by
    have hn := DeGiorgi.lintegral_rpow_norm_eq_eLpNorm_pow
      (μ := volume.restrict B) (f := (hu n).weakGrad) (by norm_num : (0 : ℝ) < 2)
      (hu n).weakGrad_memLp.aestronglyMeasurable
    norm_num only [ENNReal.ofReal_ofNat] at hn
    exact hn.le.trans (ENNReal.rpow_le_rpow (hgrad n) (by norm_num : (0 : ℝ) ≤ 2))
  have hUF (n : ℕ) : eLpNorm (U n) 2 volume ≤ F ^ (1 / 2 : ℝ) := by
    apply eLpNorm_two_le_of_lintegral_le
      (by simpa only [Measure.restrict_univ] using (hw n).memLp.aestronglyMeasurable)
    simp only [Real.norm_eq_abs]
    exact (hfb n).trans (mul_le_mul' le_rfl (hfunpow n))
  have hWG (n : ℕ) : eLpNorm (hw n).weakGrad 2 volume ≤ G ^ (1 / 2 : ℝ) := by
    apply eLpNorm_two_le_of_lintegral_le
      (by simpa only [Measure.restrict_univ] using (hw n).weakGrad_memLp.aestronglyMeasurable)
    exact (hgb n).trans (add_le_add (hgradpow n)
      (mul_le_mul' le_rfl (add_le_add (hfunpow n) (hgradpow n))))
  have hboundfun (n : ℕ) : eLpNorm (U n) 2 (volume.restrict Ω) ≤ ENNReal.ofReal S.toReal := by
    rw [ENNReal.ofReal_toReal hS]
    exact ((eLpNorm_mono_measure _ Measure.restrict_le_self).trans (hUF n)).trans
      (le_add_right le_rfl)
  have hboundgrad (n : ℕ) :
      (∑ i : Fin d, eLpNorm (fun x => (Classical.choose (hU n).2).weakGrad x i)
        2 (volume.restrict Ω)) ≤ ENNReal.ofReal S.toReal := by
    rw [ENNReal.ofReal_toReal hS]
    have heqgrad : (Classical.choose (hU n).2).weakGrad =ᵐ[volume.restrict Ω]
        (hw n).weakGrad := by
      exact DeGiorgi.MemW1pWitness.ae_eq Metric.isOpen_ball
        (Classical.choose (hU n).2) (hwΩ n)
    have hi (i : Fin d) : eLpNorm (fun x => (Classical.choose (hU n).2).weakGrad x i)
        2 (volume.restrict Ω) ≤ G ^ (1 / 2 : ℝ) := by
      rw [eLpNorm_congr_ae (heqgrad.mono fun x hx => congrArg (fun z => z i) hx)]
      exact ((eLpNorm_mono_ae ((hwΩ n).weakGrad_component_memLp i).aestronglyMeasurable
        (Eventually.of_forall fun x =>
        PiLp.norm_apply_le ((hw n).weakGrad x) i)).trans
        (eLpNorm_mono_measure _ Measure.restrict_le_self)).trans (hWG n)
    have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin d))) => hi i)
    have hs' : (∑ i : Fin d, eLpNorm (fun x => (Classical.choose (hU n).2).weakGrad x i)
        2 (volume.restrict Ω)) ≤ d * G ^ (1 / 2 : ℝ) := by simpa using hsum
    exact hs'.trans (le_add_left le_rfl)
  obtain ⟨φ, hφ, v, hv, ht⟩ := rellich_kondrachov_W01p_seq Metric.isOpen_ball
    Metric.isBounded_ball (by norm_num) (by norm_num) hU hboundfun hboundgrad
  have hBΩ : B ⊆ Ω := Metric.ball_subset_ball (by norm_num)
  refine ⟨φ, v, hφ, hv.mono_measure (Measure.restrict_mono_set volume hBΩ), ?_⟩
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (fun _ => zero_le)
  intro n
  calc
    eLpNorm (fun x => u (φ n) x - v x) 2 (volume.restrict B) =
        eLpNorm (fun x => U (φ n) x - v x) 2 (volume.restrict B) := by
      apply eLpNorm_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
      change u (φ n) x - v x = DeGiorgi.unitBallExtension (u (φ n)) x - v x
      rw [heq (φ n) x hx]
    _ ≤ eLpNorm (fun x => U (φ n) x - v x) 2 (volume.restrict Ω) :=
      eLpNorm_mono_measure _ (Measure.restrict_mono_set volume hBΩ)

end DifferentialGeometry.Analysis.Sobolev

end

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DifferentialGeometry.Analysis.Sobolev

variable {d : ℕ} [NeZero d]

private theorem rellich_kondrachov_W12_seq_unitBall_finset
    {ι : Type*} (s : Finset ι)
    (u : ι → ℕ → EuclideanSpace ℝ (Fin d) → ℝ)
    (hu : ∀ i n, DeGiorgi.MemW1pWitness 2 (u i n) (Metric.ball 0 1))
    (R : ι → ℝ)
    (hfun : ∀ i n, eLpNorm (u i n) 2 (volume.restrict (Metric.ball 0 1)) ≤
      ENNReal.ofReal (R i))
    (hgrad : ∀ i n, eLpNorm (hu i n).weakGrad 2
      (volume.restrict (Metric.ball 0 1)) ≤ ENNReal.ofReal (R i)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i ∈ s,
      ∃ v : EuclideanSpace ℝ (Fin d) → ℝ,
        MemLp v 2 (volume.restrict (Metric.ball 0 1)) ∧
        Tendsto (fun n => eLpNorm (fun x => u i (φ n) x - v x) 2
          (volume.restrict (Metric.ball 0 1))) atTop (𝓝 0) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨id, strictMono_id, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨φ, hφ, hconv⟩ := ih
    obtain ⟨ψ, v, hψ, hv, hlim⟩ := rellich_kondrachov_W12_seq_unitBall
      (fun n => u i (φ n)) (fun n => hu i (φ n))
      (fun n => hfun i (φ n)) (fun n => hgrad i (φ n))
    refine ⟨φ ∘ ψ, hφ.comp hψ, ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact ⟨v, hv, hlim⟩
    · obtain ⟨w, hw, hwlim⟩ := hconv j hj
      exact ⟨w, hw, hwlim.comp hψ.tendsto_atTop⟩

theorem rellich_kondrachov_W12_seq_unitBall_coordinates
    {ι : Type*} [Finite ι]
    (u : ι → ℕ → EuclideanSpace ℝ (Fin d) → ℝ)
    (hu : ∀ i n, DeGiorgi.MemW1pWitness 2 (u i n) (Metric.ball 0 1))
    (R : ι → ℝ)
    (hfun : ∀ i n, eLpNorm (u i n) 2 (volume.restrict (Metric.ball 0 1)) ≤
      ENNReal.ofReal (R i))
    (hgrad : ∀ i n, eLpNorm (hu i n).weakGrad 2
      (volume.restrict (Metric.ball 0 1)) ≤ ENNReal.ofReal (R i)) :
    ∃ (φ : ℕ → ℕ) (v : ι → EuclideanSpace ℝ (Fin d) → ℝ), StrictMono φ ∧
      (∀ i, MemLp (v i) 2 (volume.restrict (Metric.ball 0 1))) ∧
      ∀ i, Tendsto (fun n => eLpNorm (fun x => u i (φ n) x - v i x) 2
        (volume.restrict (Metric.ball 0 1))) atTop (𝓝 0) := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  obtain ⟨φ, hφ, h⟩ := rellich_kondrachov_W12_seq_unitBall_finset Finset.univ
    u hu R hfun hgrad
  choose v hv ht using fun i => h i (Finset.mem_univ i)
  exact ⟨φ, v, hφ, hv, ht⟩

private theorem euclidean_norm_le_sum_norm {ι : Type*} [Fintype ι]
    (v : EuclideanSpace ℝ ι) : ‖v‖ ≤ ∑ i, ‖v i‖ := by
  classical
  have hsum : (∑ i, EuclideanSpace.single i (v i)) = v := by
    ext j
    simp
  calc
    ‖v‖ = ‖∑ i, EuclideanSpace.single i (v i)‖ := by rw [hsum]
    _ ≤ ∑ i, ‖EuclideanSpace.single i (v i)‖ := norm_sum_le _ _
    _ = ∑ i, ‖v i‖ := by simp only [PiLp.norm_single]

theorem rellich_kondrachov_W12_seq_unitBall_euclidean
    {ι : Type*} [Fintype ι]
    (u : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ ι)
    (hu : ∀ i n, DeGiorgi.MemW1pWitness 2 (fun x => u n x i) (Metric.ball 0 1))
    (R : ι → ℝ)
    (hfun : ∀ i n, eLpNorm (fun x => u n x i) 2
      (volume.restrict (Metric.ball 0 1)) ≤ ENNReal.ofReal (R i))
    (hgrad : ∀ i n, eLpNorm (hu i n).weakGrad 2
      (volume.restrict (Metric.ball 0 1)) ≤ ENNReal.ofReal (R i)) :
    ∃ (φ : ℕ → ℕ) (v : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ ι),
      StrictMono φ ∧ MemLp v 2 (volume.restrict (Metric.ball 0 1)) ∧
      Tendsto (fun n => eLpNorm (fun x => u (φ n) x - v x) 2
        (volume.restrict (Metric.ball 0 1))) atTop (𝓝 0) := by
  classical
  obtain ⟨φ, w, hφ, hw, ht⟩ := rellich_kondrachov_W12_seq_unitBall_coordinates
    (fun i n x => u n x i) hu R hfun hgrad
  let v : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ ι :=
    fun x => WithLp.toLp 2 (fun i => w i x)
  have hv : MemLp v 2 (volume.restrict (Metric.ball 0 1)) := MemLp.of_eval_piLp hw
  refine ⟨φ, v, hφ, hv, ?_⟩
  have hbound (n : ℕ) :
      eLpNorm (fun x => u (φ n) x - v x) 2 (volume.restrict (Metric.ball 0 1)) ≤
        ∑ i, eLpNorm (fun x => u (φ n) x i - w i x) 2
          (volume.restrict (Metric.ball 0 1)) := by
    have hum : MemLp (u (φ n)) 2 (volume.restrict (Metric.ball 0 1)) :=
      MemLp.of_eval_piLp (fun i => (hu i (φ n)).memLp)
    have hdiff (i : ι) : AEStronglyMeasurable
        (fun x => u (φ n) x i - w i x) (volume.restrict (Metric.ball 0 1)) :=
      ((hu i (φ n)).memLp.sub (hw i)).aestronglyMeasurable
    calc
      eLpNorm (fun x => u (φ n) x - v x) 2 (volume.restrict (Metric.ball 0 1)) ≤
          eLpNorm (∑ i, fun x => ‖u (φ n) x i - w i x‖) 2
            (volume.restrict (Metric.ball 0 1)) := by
        apply eLpNorm_mono_real (hum.sub hv).aestronglyMeasurable
        intro x
        simpa only [Finset.sum_apply, Pi.sub_apply, PiLp.sub_apply, v, PiLp.toLp_apply] using
          euclidean_norm_le_sum_norm (u (φ n) x - v x)
      _ ≤ ∑ i, eLpNorm (fun x => ‖u (φ n) x i - w i x‖) 2
          (volume.restrict (Metric.ball 0 1)) :=
        eLpNorm_sum_le (by norm_num)
      _ = _ := by simp only [eLpNorm_norm _ (hdiff _)]
  have hsum : Tendsto (fun n => ∑ i, eLpNorm (fun x => u (φ n) x i - w i x) 2
      (volume.restrict (Metric.ball 0 1))) atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ (fun i _ => ht i)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => zero_le) hbound

theorem rellich_kondrachov_W12_seq_unitBall_euclidean_closed_image
    {ι : Type*} [Fintype ι]
    (u : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ ι)
    (hu : ∀ i n, DeGiorgi.MemW1pWitness 2 (fun x => u n x i) (Metric.ball 0 1))
    (R : ι → ℝ)
    (hfun : ∀ i n, eLpNorm (fun x => u n x i) 2
      (volume.restrict (Metric.ball 0 1)) ≤ ENNReal.ofReal (R i))
    (hgrad : ∀ i n, eLpNorm (hu i n).weakGrad 2
      (volume.restrict (Metric.ball 0 1)) ≤ ENNReal.ofReal (R i))
    {K : Set (EuclideanSpace ℝ ι)} (hK : IsClosed K)
    (huK : ∀ n, ∀ᵐ x ∂volume.restrict (Metric.ball 0 1), u n x ∈ K) :
    ∃ (φ : ℕ → ℕ) (v : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ ι),
      StrictMono φ ∧ MemLp v 2 (volume.restrict (Metric.ball 0 1)) ∧
      Tendsto (fun n => eLpNorm (fun x => u (φ n) x - v x) 2
        (volume.restrict (Metric.ball 0 1))) atTop (𝓝 0) ∧
      (∀ᵐ x ∂volume.restrict (Metric.ball 0 1),
        Tendsto (fun n => u (φ n) x) atTop (𝓝 (v x))) ∧
      ∀ᵐ x ∂volume.restrict (Metric.ball 0 1), v x ∈ K := by
  obtain ⟨φ, v, hφ, hv, hlim⟩ := rellich_kondrachov_W12_seq_unitBall_euclidean
    u hu R hfun hgrad
  have hmeasure := tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0) hlim
  obtain ⟨ψ, hψ, hae⟩ := hmeasure.exists_seq_tendsto_ae
  refine ⟨φ ∘ ψ, v, hφ.comp hψ, hv, hlim.comp hψ.tendsto_atTop, hae, ?_⟩
  filter_upwards [hae, ae_all_iff.mpr huK] with x hx hKx
  exact hK.mem_of_tendsto hx (Eventually.of_forall fun n => hKx (φ (ψ n)))

end DifferentialGeometry.Analysis.Sobolev

end
