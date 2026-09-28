import DifferentialGeometry.External.DeGiorgi.MoserIteration.CutoffPrep.Basics
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WitnessCongruence
import DifferentialGeometry.External.DeGiorgi.SobolevChainRule
import DifferentialGeometry.External.DeGiorgi.SobolevSpace.Approximation
import DifferentialGeometry.Analysis.Sobolev.Euclidean.ZeroBoundaryGraph
import Mathlib.Topology.Order.LiminfLimsup
import DifferentialGeometry.External.DeGiorgi.PositivePart
import DifferentialGeometry.External.DeGiorgi.UnitBallApproximationCore.Profiles
import DifferentialGeometry.External.DeGiorgi.WeakFormulation.ExistenceTheory
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Composition.OpenBall

noncomputable section
open Set Filter MeasureTheory
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open scoped Topology ENNReal NNReal ContDiff

namespace DeGiorgi

variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)


private theorem norm_gradLp_compSmoothBounded_le
    {Ω : Set E} (hΩ : IsOpen Ω) {u : E → ℝ} (hu : MemW1pWitness 2 u Ω)
    (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ) (hΦ0 : Φ 0 = 0)
    {L : ℝ≥0} (hL : ∀ x, ‖deriv Φ x‖ ≤ L) :
    ‖gradLpOfWitness (hu.compSmoothBounded hΩ Φ hΦ hΦ0 ⟨(L : ℝ), by simpa only [Real.norm_eq_abs] using hL⟩)‖ ≤
      (L : ℝ) * ‖gradLpOfWitness hu‖ := by
  rw [gradLpOfWitness, gradLpOfWitness, Lp.norm_toLp, Lp.norm_toLp]
  change (eLpNorm (fun x => deriv Φ (u x) • hu.weakGrad x) 2
    (volume.restrict Ω)).toReal ≤ (L : ℝ) *
      (eLpNorm hu.weakGrad 2 (volume.restrict Ω)).toReal
  rw [← ENNReal.coe_toReal L, ← ENNReal.toReal_mul]
  apply ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top hu.weakGrad_memLp.eLpNorm_ne_top)
  have hmono : eLpNorm (fun x => deriv Φ (u x) • hu.weakGrad x) 2
      (volume.restrict Ω) ≤
      eLpNorm (fun x => (L : ℝ) • hu.weakGrad x) 2 (volume.restrict Ω) := by
    apply eLpNorm_mono_ae
      ((hu.compSmoothBounded hΩ Φ hΦ hΦ0
        ⟨(L : ℝ), by simpa only [Real.norm_eq_abs] using hL⟩).weakGrad_memLp.aestronglyMeasurable)
    filter_upwards with x
    change ‖deriv Φ (u x) • hu.weakGrad x‖ ≤ ‖(L : ℝ) • hu.weakGrad x‖
    rw [norm_smul, norm_smul, Real.norm_of_nonneg L.coe_nonneg]
    exact mul_le_mul_of_nonneg_right (hL (u x)) (norm_nonneg _)
  apply hmono.trans_eq
  change eLpNorm ((L : ℝ) • hu.weakGrad) 2 (volume.restrict Ω) = _
  rw [eLpNorm_const_smul]
  simp only [Real.enorm_eq_ofReal_abs, abs_of_nonneg L.coe_nonneg, ENNReal.ofReal_coe_nnreal]

omit [NeZero d] in
private theorem norm_gradLp_add_le
    {Ω : Set E} {u v : E → ℝ} (hu : MemW1pWitness 2 u Ω) (hv : MemW1pWitness 2 v Ω) :
    ‖gradLpOfWitness (hu.add hv)‖ ≤ ‖gradLpOfWitness hu‖ + ‖gradLpOfWitness hv‖ := by
  have hEq : gradLpOfWitness (hu.add hv) = gradLpOfWitness hu + gradLpOfWitness hv := by
    exact MemLp.toLp_add hu.weakGrad_memLp hv.weakGrad_memLp
  rw [hEq]
  exact norm_add_le _ _

omit [NeZero d] in
private theorem eLpNorm_gradient_le_sum
    {Ω : Set E} (f : E → E) (hf : MemLp f 2 (volume.restrict Ω)) :
    eLpNorm f 2 (volume.restrict Ω) ≤
      ∑ j : Fin d, eLpNorm (fun x => f x j) 2 (volume.restrict Ω) := by
  classical
  have hn (v : E) : ‖v‖ ≤ ∑ j : Fin d, ‖v j‖ := by
    have hv : (∑ j : Fin d, EuclideanSpace.single j (v j)) = v := by ext; simp
    calc
      ‖v‖ = ‖∑ j : Fin d, EuclideanSpace.single j (v j)‖ := by rw [hv]
      _ ≤ ∑ j : Fin d, ‖EuclideanSpace.single j (v j)‖ := norm_sum_le _ _
      _ = _ := by simp only [PiLp.norm_single]
  calc
    eLpNorm f 2 (volume.restrict Ω) ≤
        eLpNorm (∑ j : Fin d, fun x => ‖f x j‖) 2 (volume.restrict Ω) :=
      eLpNorm_mono_real hf.aestronglyMeasurable
        (fun x => by simpa only [Finset.sum_apply] using hn (f x))
    _ ≤ ∑ j : Fin d, eLpNorm (fun x => ‖f x j‖) 2 (volume.restrict Ω) :=
      by
        simpa only [Finset.sum_apply] using
          (eLpNorm_sum_le (s := Finset.univ) (f := fun j => fun x => ‖f x j‖)
            (by norm_num : (1 : ℝ≥0∞) ≤ 2))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      exact eLpNorm_norm _ ((hf.eval_piLp j).aestronglyMeasurable)

theorem MemW01p.comp_smooth_of_eq_zero_on_datum
    {Ω : Set E} (hΩ : IsOpen Ω) {u v : E → ℝ}
    (hu : MemW1pWitness 2 u Ω) (hvu : MemW01p 2 (fun x => v x - u x) Ω)
    (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ) (hΦ0 : Φ 0 = 0)
    {L : ℝ≥0} (hL : ∀ x, ‖deriv Φ x‖ ≤ L)
    (hzero : ∀ᵐ x ∂volume.restrict Ω, Φ (u x) = 0) : MemW01p 2 (fun x => Φ (v x)) Ω := by
  classical
  obtain ⟨_, hd, φ, hφs, hφc, hφΩ, hφf, hφg⟩ := hvu
  let hφ (n : ℕ) : IsSmoothTestOn Ω (φ n) := ⟨hφs n, hφc n, hφΩ n⟩
  let hφw (n : ℕ) := smoothTestWitness hΩ (hφ n)
  have hlimGrad : Tendsto (fun n => gradLpOfWitness (hφw n)) atTop
      (𝓝 (gradLpOfWitness hd)) := by
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
      (f_ℒp := fun n => (hφw n).weakGrad_memLp) (f_lim_ℒp := hd.weakGrad_memLp)).mpr
    have hsum : Tendsto (fun n => ∑ j : Fin d, eLpNorm
        (fun x => (hφw n).weakGrad x j - hd.weakGrad x j) 2 (volume.restrict Ω)) atTop (𝓝 0) := by
      simpa only [Finset.sum_const_zero, hφw, smoothTestWitness, smoothGradField,
        PiLp.toLp_apply] using
        tendsto_finsetSum Finset.univ (fun j _ => hφg j)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ => zero_le)
    intro n
    exact eLpNorm_gradient_le_sum _ ((hφw n).weakGrad_memLp.sub hd.weakGrad_memLp)
  obtain ⟨B, hB⟩ := hlimGrad.norm.bddAbove_range
  have hB' (n : ℕ) : ‖gradLpOfWitness (hφw n)‖ ≤ B := hB (mem_range_self n)
  let b := fun x => if Φ (u x) = 0 then u x else 0
  have hbeq : b =ᵐ[volume.restrict Ω] u := hzero.mono fun x hx => by
    dsimp only [b]
    rw [ite_eq_left hx]
  have hbzero (x : E) : Φ (b x) = 0 := by
    dsimp only [b]
    split_ifs with hx
    · exact hx
    · exact hΦ0
  let hb : MemW1pWitness 2 b Ω := hu.congr hbeq.symm
  let fn : ℕ → E → ℝ := fun n x => Φ (b x + φ n x)
  let hfn (n : ℕ) : MemW1pWitness 2 (fn n) Ω :=
    (hb.add (hφw n)).compSmoothBounded hΩ Φ hΦ hΦ0 ⟨(L : ℝ), by simpa only [Real.norm_eq_abs] using hL⟩
  have hfnSupport (n : ℕ) : tsupport (fn n) ⊆ tsupport (φ n) := by
    apply closure_minimal _ (isClosed_tsupport _)
    intro x hx
    apply Classical.byContradiction
    intro hxφ
    have hφzero := image_eq_zero_of_notMem_tsupport hxφ
    have hfnzero : fn n x = 0 := by
      dsimp only [fn]
      rw [hφzero, add_zero]
      exact hbzero x
    exact hx hfnzero
  have hfn0 (n : ℕ) : MemW01p 2 (fn n) Ω := by
    simpa only [ENNReal.ofReal_ofNat] using
      memW01p_of_memW1p_of_tsupport_subset hΩ (by norm_num : (1 : ℝ) < 2)
      (by simpa using (hfn n).memW1p)
      ((hφc n).of_isClosed_subset (isClosed_tsupport _) (hfnSupport n))
      ((hfnSupport n).trans (hφΩ n))
  let hv : MemW1pWitness 2 v Ω := (hu.add hd).congr (Eventually.of_forall fun x => by ring)
  let hΦv : MemW1pWitness 2 (fun x => Φ (v x)) Ω := hv.compSmoothBounded hΩ Φ hΦ hΦ0 ⟨(L : ℝ), by simpa only [Real.norm_eq_abs] using hL⟩
  have hLip : LipschitzWith L Φ := lipschitzWith_of_nnnorm_deriv_le
    (hΦ.differentiable (by simp)) (fun x => by exact_mod_cast hL x)
  have hfunlim : Tendsto (fun n => eLpNorm (fun x => fn n x - Φ (v x)) 2
      (volume.restrict Ω)) atTop (𝓝 0) := by
    have hm := ENNReal.Tendsto.const_mul (a := (L : ℝ≥0∞)) hφf
      (Or.inr ENNReal.coe_ne_top)
    simp only [mul_zero] at hm
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hm (fun _ => zero_le)
    intro n
    calc
      eLpNorm (fun x => fn n x - Φ (v x)) 2 (volume.restrict Ω) ≤
          eLpNorm (fun x => (L : ℝ) * (φ n x - (v x - u x))) 2 (volume.restrict Ω) := by
        apply eLpNorm_mono_ae
          ((hfn n).memLp.sub hΦv.memLp).aestronglyMeasurable
        filter_upwards [hbeq] with x hx
        have hh := hLip.dist_le_mul (b x + φ n x) (v x)
        rw [hx] at hh
        have heq : u x + φ n x - v x = φ n x - (v x - u x) := by ring
        change ‖Φ (b x + φ n x) - Φ (v x)‖ ≤
          ‖(L : ℝ) * (φ n x - (v x - u x))‖
        rw [hx]
        simpa only [Real.dist_eq, heq, norm_mul,
          Real.norm_eq_abs, abs_of_nonneg L.coe_nonneg] using hh
      _ = (L : ℝ≥0∞) * eLpNorm (fun x => φ n x - (v x - u x)) 2 (volume.restrict Ω) := by
        change eLpNorm ((L : ℝ) • (fun x => φ n x - (v x - u x))) 2 _ = _
        rw [eLpNorm_const_smul]
        simp only [Real.enorm_eq_ofReal_abs, abs_of_nonneg L.coe_nonneg,
          ENNReal.ofReal_coe_nnreal]
  have hbound (n : ℕ) : ‖gradLpOfWitness (Classical.choose (hfn0 n).2)‖ ≤
      (L : ℝ) * (‖gradLpOfWitness hb‖ + B) := by
    have heq : gradLpOfWitness (Classical.choose (hfn0 n).2) = gradLpOfWitness (hfn n) := by
      apply MemLp.toLp_congr
      exact MemW1pWitness.ae_eq hΩ (Classical.choose (hfn0 n).2) (hfn n)
    rw [heq]
    exact (norm_gradLp_compSmoothBounded_le hΩ (hb.add (hφw n)) Φ hΦ hΦ0 hL).trans
      (mul_le_mul_of_nonneg_left ((norm_gradLp_add_le hb (hφw n)).trans
        (add_le_add_right (hB' n) _)) L.coe_nonneg)
  exact (exists_weakly_convergent_gradients_of_tendsto_L2
    hΩ hfn0 hΦv.memLp hbound hfunlim).1

end DeGiorgi

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ} {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "F" => EuclideanSpace ℝ ι

private theorem eLpNorm_vector_le_sum
    {J : Type*} [Fintype J] {Ω : Set E}
    (f : E → EuclideanSpace ℝ J) (hf : MemLp f 2 (volume.restrict Ω)) :
    eLpNorm f 2 (volume.restrict Ω) ≤ ∑ j : J, eLpNorm (fun x => f x j) 2 (volume.restrict Ω) := by
  classical
  have hn (v : EuclideanSpace ℝ J) : ‖v‖ ≤ ∑ j : J, ‖v j‖ := by
    have hv : (∑ j : J, EuclideanSpace.single j (v j)) = v := by ext; simp
    calc
      ‖v‖ = ‖∑ j : J, EuclideanSpace.single j (v j)‖ := by rw [hv]
      _ ≤ ∑ j : J, ‖EuclideanSpace.single j (v j)‖ := norm_sum_le _ _
      _ = _ := by simp only [PiLp.norm_single]
  calc
    eLpNorm f 2 (volume.restrict Ω) ≤
        eLpNorm (∑ j : J, fun x => ‖f x j‖) 2 (volume.restrict Ω) :=
      eLpNorm_mono_real hf.aestronglyMeasurable
        (fun x => by simpa only [Finset.sum_apply] using hn (f x))
    _ ≤ ∑ j : J, eLpNorm (fun x => ‖f x j‖) 2 (volume.restrict Ω) :=
      by
        simpa only [Finset.sum_apply] using
          (eLpNorm_sum_le (s := Finset.univ) (f := fun j => fun x => ‖f x j‖)
            (by norm_num : (1 : ℝ≥0∞) ≤ 2))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      exact eLpNorm_norm _ ((hf.eval_piLp j).aestronglyMeasurable)

private theorem exists_smooth_h01_approximation_bounded_gradient
    {Ω : Set E} (hΩ : IsOpen Ω) {u : E → ℝ}
    (hu : DeGiorgi.MemW01p 2 u Ω) :
    ∃ (φ : ℕ → E → ℝ) (B : ℝ),
      ∃ ht : ∀ n, DeGiorgi.IsSmoothTestOn Ω (φ n),
      Tendsto (fun n => eLpNorm (fun x => φ n x - u x) 2 (volume.restrict Ω)) atTop (𝓝 0) ∧
      (∀ n, ‖DeGiorgi.gradLpOfWitness (DeGiorgi.smoothTestWitness hΩ (ht n))‖ ≤ B) := by
  classical
  obtain ⟨_, hw, φ, hφs, hφc, hφΩ, hφf, hφg⟩ := hu
  let ht (n : ℕ) : DeGiorgi.IsSmoothTestOn Ω (φ n) := ⟨hφs n, hφc n, hφΩ n⟩
  have hlim : Tendsto (fun n => DeGiorgi.gradLpOfWitness (DeGiorgi.smoothTestWitness hΩ (ht n)))
      atTop (𝓝 (DeGiorgi.gradLpOfWitness hw)) := by
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
      (f_ℒp := fun n => (DeGiorgi.smoothTestWitness hΩ (ht n)).weakGrad_memLp)
      (f_lim_ℒp := hw.weakGrad_memLp)).mpr
    have hsum : Tendsto (fun n => ∑ j : Fin d, eLpNorm
        (fun x => DeGiorgi.smoothGradField (φ n) x j - hw.weakGrad x j) 2
          (volume.restrict Ω)) atTop (𝓝 0) := by
      simpa only [Finset.sum_const_zero, DeGiorgi.smoothGradField, PiLp.toLp_apply] using
        tendsto_finsetSum Finset.univ (fun j _ => hφg j)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ => zero_le)
    intro n
    exact eLpNorm_vector_le_sum _
      ((DeGiorgi.smoothTestWitness hΩ (ht n)).weakGrad_memLp.sub hw.weakGrad_memLp)
  obtain ⟨B, hB⟩ := hlim.norm.bddAbove_range
  exact ⟨φ, B, ht, hφf, fun n => hB (mem_range_self n)⟩

private theorem eLpNorm_comp_gradient_le
    {κ : Type*} [Fintype κ] {c : E} {a : ℝ} {u : E → F}
    (hu : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => u x i) (Metric.ball c a))
    (T : F → EuclideanSpace ℝ κ)
    (hT : ∀ k, DeGiorgi.MemW1pWitness 2 (fun x => T (u x) k) (Metric.ball c a))
    (hG : ∀ k x j, (hT k).weakGrad x j =
      (fderiv ℝ T (u x) (WithLp.toLp 2 (fun i => (hu i).weakGrad x j))) k)
    {C : ℝ} (hC : ∀ y, ‖fderiv ℝ T y‖ ≤ C) (k : κ) :
    eLpNorm (hT k).weakGrad 2 (volume.restrict (Metric.ball c a)) ≤
      (d : ℝ≥0∞) * ENNReal.ofReal C *
        ∑ i : ι, eLpNorm (hu i).weakGrad 2 (volume.restrict (Metric.ball c a)) := by
  have hC0 : 0 ≤ C := (norm_nonneg (fderiv ℝ T 0)).trans (hC 0)
  apply (eLpNorm_vector_le_sum _ (hT k).weakGrad_memLp).trans
  have hcol (j : Fin d) : eLpNorm (fun x => (hT k).weakGrad x j) 2
      (volume.restrict (Metric.ball c a)) ≤
      ENNReal.ofReal C * ∑ i : ι, eLpNorm (hu i).weakGrad 2
        (volume.restrict (Metric.ball c a)) := by
    let G := fun x => (WithLp.toLp 2 (fun i => (hu i).weakGrad x j) : F)
    have hGm : MemLp G 2 (volume.restrict (Metric.ball c a)) :=
      MemLp.of_eval_piLp fun i => (hu i).weakGrad_component_memLp j
    have hGnorm : eLpNorm G 2 (volume.restrict (Metric.ball c a)) ≤
        ∑ i : ι, eLpNorm (hu i).weakGrad 2 (volume.restrict (Metric.ball c a)) := by
      apply (eLpNorm_vector_le_sum G hGm).trans
      apply Finset.sum_le_sum
      intro i hi
      exact eLpNorm_mono_ae ((hu i).weakGrad_component_memLp j).aestronglyMeasurable
        (Eventually.of_forall fun x => PiLp.norm_apply_le ((hu i).weakGrad x) j)
    have hh : eLpNorm (fun x => (hT k).weakGrad x j) 2
        (volume.restrict (Metric.ball c a)) ≤ ENNReal.ofReal C *
        eLpNorm G 2 (volume.restrict (Metric.ball c a)) := by
      apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul
        ((hT k).weakGrad_component_memLp j).aestronglyMeasurable
      filter_upwards with x
      rw [hG k x j]
      exact (PiLp.norm_apply_le _ k).trans
        (((fderiv ℝ T (u x)).le_opNorm (G x)).trans
          (mul_le_mul_of_nonneg_right (hC (u x)) (norm_nonneg _)))
    exact hh.trans (mul_le_mul_right hGnorm _)
  have hh := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin d))) => hcol j)
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_assoc] using hh

theorem memW01p_comp_sub_of_bounded_fderiv
    [NeZero d] {κ : Type*} [Fintype κ] {c : E} {a : ℝ} {u v : E → F}
    (hu : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => u x i) (Metric.ball c a))
    (hvu : ∀ i, DeGiorgi.MemW01p 2 (fun x => v x i - u x i) (Metric.ball c a))
    (T : F → EuclideanSpace ℝ κ) (hT : ContDiff ℝ 1 T)
    {C : ℝ} (hC : ∀ y, ‖fderiv ℝ T y‖ ≤ C) :
    ∀ k, DeGiorgi.MemW01p 2 (fun x => T (v x) k - T (u x) k) (Metric.ball c a) := by
  classical
  let Ω := Metric.ball c a
  have hΩ : IsOpen Ω := Metric.isOpen_ball
  have hC0 : 0 ≤ C := (norm_nonneg (fderiv ℝ T 0)).trans (hC 0)
  let L : ℝ≥0 := NNReal.mk C hC0
  have hLip : LipschitzWith L T := lipschitzWith_of_nnnorm_fderiv_le
    (hT.differentiable one_ne_zero) hC
  choose φ B ht hφlim hφbound using fun i =>
    exists_smooth_h01_approximation_bounded_gradient hΩ (hvu i)
  let hφw (i : ι) (n : ℕ) := DeGiorgi.smoothTestWitness hΩ (ht i n)
  let φv (n : ℕ) : E → F := fun x => WithLp.toLp 2 fun i => φ i n x
  let s (n : ℕ) : E → F := fun x => u x + φv n x
  let hs (n : ℕ) (i : ι) : DeGiorgi.MemW1pWitness 2 (fun x => s n x i) Ω :=
    (hu i).add (hφw i n)
  let hv (i : ι) : DeGiorgi.MemW1pWitness 2 (fun x => v x i) Ω :=
    ((hu i).add (DeGiorgi.MemW1p.someWitness (hvu i).memW1p)).congr
      (Eventually.of_forall fun x => by ring)
  obtain ⟨hTu, hTug⟩ := exists_memW1pWitnesses_comp_contDiff_on_ball_of_bounded_fderiv hu T hT hC
  obtain ⟨hTv, hTvg⟩ := exists_memW1pWitnesses_comp_contDiff_on_ball_of_bounded_fderiv hv T hT hC
  have hcomps (n : ℕ) :=
    exists_memW1pWitnesses_comp_contDiff_on_ball_of_bounded_fderiv (hs n) T hT hC
  choose hTs hTsg using hcomps
  let fn (n : ℕ) : E → EuclideanSpace ℝ κ := fun x => T (s n x) - T (u x)
  let f : E → EuclideanSpace ℝ κ := fun x => T (v x) - T (u x)
  let hfn (n : ℕ) (k : κ) : DeGiorgi.MemW1pWitness 2 (fun x => fn n x k) Ω :=
    ((hTs n k).add ((hTu k).smul (-1))).congr (Eventually.of_forall fun x => by
      change T (s n x) k + -1 * T (u x) k = T (s n x) k - T (u x) k
      ring)
  let hf (k : κ) : DeGiorgi.MemW1pWitness 2 (fun x => f x k) Ω :=
    ((hTv k).add ((hTu k).smul (-1))).congr (Eventually.of_forall fun x => by
      change T (v x) k + -1 * T (u x) k = T (v x) k - T (u x) k
      ring)
  have hfn0 (n : ℕ) (k : κ) : DeGiorgi.MemW01p 2 (fun x => fn n x k) Ω := by
    let K := ⋃ i : ι, tsupport (φ i n)
    have hK : IsCompact K := isCompact_iUnion fun i => (ht i n).2.1
    have hsupp : tsupport (fun x => fn n x k) ⊆ K := by
      apply closure_minimal _ hK.isClosed
      intro x hx
      by_contra hxK
      have hφx (i : ι) : φ i n x = 0 := image_eq_zero_of_notMem_tsupport
        (fun hi => hxK (mem_iUnion.mpr ⟨i, hi⟩))
      have hsx : s n x = u x := by
        ext i
        change u x i + φ i n x = u x i
        rw [hφx i, add_zero]
      exact hx (by change T (s n x) k - T (u x) k = 0; rw [hsx, sub_self])
    have hKΩ : K ⊆ Ω := iUnion_subset fun i => (ht i n).2.2
    simpa only [ENNReal.ofReal_ofNat] using
      DeGiorgi.memW01p_of_memW1p_of_tsupport_subset hΩ (by norm_num : (1 : ℝ) < 2)
        (by simpa only [ENNReal.ofReal_ofNat] using (hfn n k).memW1p)
        (hK.of_isClosed_subset (isClosed_tsupport _) hsupp) (hsupp.trans hKΩ)
  have hsm (n : ℕ) : MemLp (s n) 2 (volume.restrict Ω) :=
    MemLp.of_eval_piLp fun i => (hs n i).memLp
  have hvm : MemLp v 2 (volume.restrict Ω) := MemLp.of_eval_piLp fun i => (hv i).memLp
  have hsLim : Tendsto (fun n => eLpNorm (fun x => s n x - v x) 2 (volume.restrict Ω))
      atTop (𝓝 0) := by
    have hsum := tendsto_finsetSum Finset.univ (fun i _ => hφlim i)
    simp only [Finset.sum_const_zero] at hsum
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ => zero_le)
    intro n
    have hh := eLpNorm_vector_le_sum (fun x => s n x - v x) ((hsm n).sub hvm)
    apply hh.trans_eq
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    funext x
    change u x i + φ i n x - v x i = φ i n x - (v x i - u x i)
    ring
  have hfnLim : Tendsto (fun n => eLpNorm (fun x => fn n x - f x) 2 (volume.restrict Ω))
      atTop (𝓝 0) := by
    have hlim := ENNReal.Tendsto.const_mul (a := (L : ℝ≥0∞)) hsLim (Or.inr ENNReal.coe_ne_top)
    simp only [mul_zero] at hlim
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le)
    intro n
    change eLpNorm (fun x => (T (s n x) - T (u x)) - (T (v x) - T (u x))) 2 _ ≤ _
    simp only [sub_sub_sub_cancel_right]
    have hTsm : MemLp (fun x => T (s n x)) 2 (volume.restrict Ω) :=
      MemLp.of_eval_piLp fun k => (hTs n k).memLp
    have hTvm : MemLp (fun x => T (v x)) 2 (volume.restrict Ω) :=
      MemLp.of_eval_piLp fun k => (hTv k).memLp
    simpa only [ENNReal.ofReal_coe_nnreal] using
      (eLpNorm_le_mul_eLpNorm_of_ae_le_mul
        (f := fun x => T (s n x) - T (v x))
        (g := fun x => s n x - v x) (c := (L : ℝ))
        ((hTsm.sub hTvm).aestronglyMeasurable)
        (by
          filter_upwards with x
          exact hLip.norm_sub_le (s n x) (v x)) 2)
  let S : ℝ≥0∞ := ∑ i : ι, ENNReal.ofReal (‖DeGiorgi.gradLpOfWitness (hu i)‖ + B i)
  have hS : S ≠ (⊤ : ℝ≥0∞) := ENNReal.sum_ne_top.mpr fun i _ => ENNReal.ofReal_ne_top
  have hsource (n : ℕ) : (∑ i : ι, eLpNorm (hs n i).weakGrad 2 (volume.restrict Ω)) ≤ S := by
    apply Finset.sum_le_sum
    intro i hi
    have heq : DeGiorgi.gradLpOfWitness (hs n i) =
        DeGiorgi.gradLpOfWitness (hu i) + DeGiorgi.gradLpOfWitness (hφw i n) :=
      MemLp.toLp_add (hu i).weakGrad_memLp (hφw i n).weakGrad_memLp
    have hn : ‖DeGiorgi.gradLpOfWitness (hs n i)‖ ≤ ‖DeGiorgi.gradLpOfWitness (hu i)‖ + B i := by
      rw [heq]
      exact (norm_add_le _ _).trans (add_le_add_right (hφbound i n) _)
    rw [← Lp.enorm_toLp (hs n i).weakGrad_memLp]
    simpa only [enorm_eq_nnnorm, ENNReal.coe_nnreal_eq, coe_nnnorm,
      DeGiorgi.gradLpOfWitness] using ENNReal.ofReal_le_ofReal hn
  have htarget (n : ℕ) (k : κ) : eLpNorm (hTs n k).weakGrad 2 (volume.restrict Ω) ≤
      (d : ℝ≥0∞) * ENNReal.ofReal C * S :=
    (eLpNorm_comp_gradient_le (hs n) T (hTs n) (hTsg n) hC k).trans
      (mul_le_mul_right (hsource n) _)
  intro k
  let R : ℝ≥0∞ := (d : ℝ≥0∞) * ENNReal.ofReal C * S +
    eLpNorm (hTu k).weakGrad 2 (volume.restrict Ω)
  have hR : R ≠ (⊤ : ℝ≥0∞) := ENNReal.add_ne_top.mpr
    ⟨ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top) hS,
      (hTu k).weakGrad_memLp.eLpNorm_ne_top⟩
  have hbound (n : ℕ) : ‖DeGiorgi.gradLpOfWitness (Classical.choose (hfn0 n k).2)‖ ≤ R.toReal := by
    have heq : DeGiorgi.gradLpOfWitness (Classical.choose (hfn0 n k).2) =
        DeGiorgi.gradLpOfWitness (hfn n k) := by
      apply MemLp.toLp_congr
      exact DeGiorgi.MemW1pWitness.ae_eq hΩ (Classical.choose (hfn0 n k).2) (hfn n k)
    rw [heq, DeGiorgi.gradLpOfWitness, Lp.norm_toLp]
    apply ENNReal.toReal_mono hR
    have he : (hfn n k).weakGrad = (hTs n k).weakGrad - (hTu k).weakGrad := by
      funext x
      change (hTs n k).weakGrad x + -1 • (hTu k).weakGrad x = _
      simp only [neg_one_smul, Pi.sub_apply, sub_eq_add_neg]
    rw [he]
    exact (eLpNorm_sub_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)).trans
      (add_le_add_left (htarget n k) _)
  have hlimk : Tendsto (fun n => eLpNorm (fun x => fn n x k - f x k) 2
      (volume.restrict Ω)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hfnLim (fun _ => zero_le)
      (fun n => eLpNorm_mono_ae ((hfn n k).memLp.sub (hf k).memLp).aestronglyMeasurable
        (Eventually.of_forall fun x => PiLp.norm_apply_le (fn n x - f x) k))
  exact (exists_weakly_convergent_gradients_of_tendsto_L2 hΩ (fun n => hfn0 n k)
    (hf k).memLp hbound hlimk).1

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end

noncomputable section
open Filter MeasureTheory
open scoped Topology ENNReal

namespace DeGiorgi

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem MemW01p.congr
    {p : ℝ≥0∞} {Ω : Set E} {u v : E → ℝ}
    (hu : MemW01p p u Ω) (huv : u =ᵐ[volume.restrict Ω] v) : MemW01p p v Ω := by
  obtain ⟨_, hw, φ, hφs, hφc, hφΩ, hφf, hφg⟩ := hu
  let hv := hw.congr huv
  refine ⟨hv.memW1p, hv, φ, hφs, hφc, hφΩ, ?_, hφg⟩
  have heq (n : ℕ) : eLpNorm (fun x => φ n x - v x) p (volume.restrict Ω) =
      eLpNorm (fun x => φ n x - u x) p (volume.restrict Ω) := by
    apply eLpNorm_congr_ae
    exact huv.symm.mono fun x hx => by dsimp only; rw [hx]
  simpa only [heq] using hφf

end DeGiorgi

end
