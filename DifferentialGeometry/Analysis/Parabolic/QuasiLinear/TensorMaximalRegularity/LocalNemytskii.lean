import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.ForcingFixedPoint
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.LocallyLipschitzExistence
open DifferentialGeometry.Geometry.Curvature

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal

namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable {X Y : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
variable {T : ℝ}

def aeSetLift {S : Set X} (hzero : (0 : X) ∈ S) (f : timeL2 X T) : ℝ → S :=
  by
    classical
    exact fun t => if ht : f t ∈ S then ⟨f t, ht⟩ else ⟨0, hzero⟩

omit [NormedSpace ℝ X] [CompleteSpace X] in
theorem aeSetLift_coe_ae {S : Set X} (hzero : (0 : X) ∈ S)
    (f : timeL2 X T) (hf : ∀ᵐ t ∂(timeMeasure T), f t ∈ S) :
    (fun t => ((aeSetLift hzero f t : S) : X)) =ᵐ[timeMeasure T] fun t => f t := by
  filter_upwards [hf] with t ht
  simp only [aeSetLift, dif_pos ht]

omit [NormedSpace ℝ X] [CompleteSpace X] in
theorem aeSetLift_aesm {S : Set X} (hzero : (0 : X) ∈ S)
    (f : timeL2 X T) (hf : ∀ᵐ t ∂(timeMeasure T), f t ∈ S) :
    AEStronglyMeasurable (aeSetLift hzero f) (timeMeasure T) := by
  apply (Topology.IsEmbedding.subtypeVal.aestronglyMeasurable_comp_iff).mp
  exact (Lp.aestronglyMeasurable f).congr
    (aeSetLift_coe_ae hzero f hf).symm

omit [NormedSpace ℝ Y] [CompleteSpace Y] in
omit [NormedSpace ℝ X] [CompleteSpace X] in
theorem memLp_on {S : Set X} (hzero : (0 : X) ∈ S)
    {N : S → Y} {L : ℝ≥0} (hN : LipschitzWith L N)
    (f : timeL2 X T) (hf : ∀ᵐ t ∂(timeMeasure T), f t ∈ S) :
    MemLp (fun t => N (aeSetLift hzero f t)) 2 (timeMeasure T) := by
  let z : S := ⟨0, hzero⟩
  have hlift := aeSetLift_aesm hzero f hf
  have hshiftMeas : AEStronglyMeasurable
      (fun t => N (aeSetLift hzero f t) - N z) (timeMeasure T) :=
    (hN.continuous.comp_aestronglyMeasurable hlift).sub
      aestronglyMeasurable_const
  have hshift : MemLp (fun t => N (aeSetLift hzero f t) - N z) 2
      (timeMeasure T) := by
    refine (Lp.memLp f).of_le_mul (c := (L : ℝ)) hshiftMeas ?_
    filter_upwards [hf] with t ht
    have hdist := hN.dist_le_mul (aeSetLift hzero f t) z
    rw [dist_eq_norm] at hdist
    simpa only [aeSetLift, dif_pos ht, z, Subtype.dist_eq, dist_zero_right] using hdist
  have hconst : MemLp (fun _ : ℝ => N z) 2 (timeMeasure T) :=
    memLp_const (N z)
  have hsum := hshift.add hconst
  have hfun : (fun t => N (aeSetLift hzero f t)) =
      fun t => (N (aeSetLift hzero f t) - N z) + N z := by
    funext t
    abel
  rw [hfun]
  exact hsum

def nemytskiiOn {S : Set X} (hzero : (0 : X) ∈ S)
    {N : S → Y} {L : ℝ≥0} (hN : LipschitzWith L N)
    (f : timeL2 X T) (hf : ∀ᵐ t ∂(timeMeasure T), f t ∈ S) :
    timeL2 Y T :=
  (memLp_on hzero hN f hf).toLp (fun t => N (aeSetLift hzero f t))

omit [NormedSpace ℝ Y] [CompleteSpace Y] in
omit [NormedSpace ℝ X] [CompleteSpace X] in
theorem nemytskiiOn_coeFn {S : Set X} (hzero : (0 : X) ∈ S)
    {N : S → Y} {L : ℝ≥0} (hN : LipschitzWith L N)
    (f : timeL2 X T) (hf : ∀ᵐ t ∂(timeMeasure T), f t ∈ S) :
    nemytskiiOn hzero hN f hf =ᵐ[timeMeasure T]
      fun t => N (aeSetLift hzero f t) :=
  (memLp_on hzero hN f hf).coeFn_toLp

omit [NormedSpace ℝ X] [CompleteSpace X] in
omit [NormedSpace ℝ Y] [CompleteSpace Y] in
theorem nemytskiiOn_zero_le {S : Set X} (hzero : (0 : X) ∈ S)
    {N : S → Y} {L : ℝ≥0} (hN : LipschitzWith L N) {T : ℝ}
    (hf : ∀ᵐ t ∂(timeMeasure T), ((0 : timeL2 X T) t) ∈ S) :
    ‖nemytskiiOn hzero hN (0 : timeL2 X T) hf‖ ≤
      Real.sqrt T * ‖N ⟨0, hzero⟩‖ := by
  refine timeL2_norm_le_of_ae_bound _ (norm_nonneg _) ?_
  have hcoe := nemytskiiOn_coeFn hzero hN (0 : timeL2 X T) hf
  have hzeroFn := Lp.coeFn_zero (E := X) (p := 2) (μ := timeMeasure T)
  filter_upwards [hcoe, hzeroFn, hf] with t ht htz hmem
  rw [ht]
  simp only [aeSetLift, dif_pos hmem]
  have hval : ((0 : timeL2 X T) t) = (0 : X) := by
    simpa only [Pi.zero_apply] using htz
  have hsub : (⟨(0 : timeL2 X T) t, hmem⟩ : S) = ⟨0, hzero⟩ :=
    Subtype.ext hval
  rw [hsub]

omit [NormedSpace ℝ X] [CompleteSpace X] [NormedSpace ℝ Y] [CompleteSpace Y] in
theorem timeL2_norm_le_four
    {Z W V : Type*}
    [NormedAddCommGroup Z]
    [NormedAddCommGroup W]
    [NormedAddCommGroup V]
    (h : timeL2 X T) (p : timeL2 Y T) (q : timeL2 Z T)
    (r : timeL2 W T) (s : timeL2 V T) {A B C D : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hbound : ∀ᵐ t ∂(timeMeasure T),
      ‖h t‖ ≤ A * ‖p t‖ + B * ‖q t‖ + C * ‖r t‖ + D * ‖s t‖) :
    ‖h‖ ≤ A * ‖p‖ + B * ‖q‖ + C * ‖r‖ + D * ‖s‖ := by
  let Pf : ℝ → ℝ := fun t => ‖(p : ℝ → Y) t‖
  let Qf : ℝ → ℝ := fun t => ‖(q : ℝ → Z) t‖
  let Rf : ℝ → ℝ := fun t => ‖(r : ℝ → W) t‖
  let Sf : ℝ → ℝ := fun t => ‖(s : ℝ → V) t‖
  have hPm : AEStronglyMeasurable Pf (timeMeasure T) := (Lp.aestronglyMeasurable p).norm
  have hQm : AEStronglyMeasurable Qf (timeMeasure T) := (Lp.aestronglyMeasurable q).norm
  have hRm : AEStronglyMeasurable Rf (timeMeasure T) := (Lp.aestronglyMeasurable r).norm
  have hSm : AEStronglyMeasurable Sf (timeMeasure T) := (Lp.aestronglyMeasurable s).norm
  have hAPm : AEStronglyMeasurable (A • Pf) (timeMeasure T) := hPm.const_smul A
  have hBQm : AEStronglyMeasurable (B • Qf) (timeMeasure T) := hQm.const_smul B
  have hCRm : AEStronglyMeasurable (C • Rf) (timeMeasure T) := hRm.const_smul C
  have hDSm : AEStronglyMeasurable (D • Sf) (timeMeasure T) := hSm.const_smul D
  let major : ℝ → ℝ := A • Pf + B • Qf + C • Rf + D • Sf
  have hmono : eLpNorm (h : ℝ → X) 2 (timeMeasure T) ≤
      eLpNorm major 2 (timeMeasure T) := by
    refine eLpNorm_mono_ae ?_
    filter_upwards [hbound] with t ht
    have happ : major t =
        A * ‖p t‖ + B * ‖q t‖ + C * ‖r t‖ + D * ‖s t‖ := by
      simp only [major, Pf, Qf, Rf, Sf, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hnonneg : 0 ≤ major t := by
      rw [happ]
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg, happ]
    exact ht
  have htri₁ : eLpNorm major 2 (timeMeasure T) ≤
      eLpNorm (A • Pf + B • Qf + C • Rf) 2 (timeMeasure T) +
        eLpNorm (D • Sf) 2 (timeMeasure T) := by
    exact eLpNorm_add_le ((hAPm.add hBQm).add hCRm) hDSm (by norm_num)
  have htri₂ : eLpNorm (A • Pf + B • Qf + C • Rf) 2 (timeMeasure T) ≤
      eLpNorm (A • Pf + B • Qf) 2 (timeMeasure T) +
        eLpNorm (C • Rf) 2 (timeMeasure T) := by
    exact eLpNorm_add_le (hAPm.add hBQm) hCRm (by norm_num)
  have htri₃ : eLpNorm (A • Pf + B • Qf) 2 (timeMeasure T) ≤
      eLpNorm (A • Pf) 2 (timeMeasure T) +
        eLpNorm (B • Qf) 2 (timeMeasure T) :=
    eLpNorm_add_le hAPm hBQm (by norm_num)
  have hscaleP : eLpNorm (A • Pf) 2 (timeMeasure T) =
      ENNReal.ofReal A * eLpNorm (p : ℝ → Y) 2 (timeMeasure T) := by
    rw [eLpNorm_const_smul, eLpNorm_norm, Real.enorm_eq_ofReal hA]
  have hscaleQ : eLpNorm (B • Qf) 2 (timeMeasure T) =
      ENNReal.ofReal B * eLpNorm (q : ℝ → Z) 2 (timeMeasure T) := by
    rw [eLpNorm_const_smul, eLpNorm_norm, Real.enorm_eq_ofReal hB]
  have hscaleR : eLpNorm (C • Rf) 2 (timeMeasure T) =
      ENNReal.ofReal C * eLpNorm (r : ℝ → W) 2 (timeMeasure T) := by
    rw [eLpNorm_const_smul, eLpNorm_norm, Real.enorm_eq_ofReal hC]
  have hscaleS : eLpNorm (D • Sf) 2 (timeMeasure T) =
      ENNReal.ofReal D * eLpNorm (s : ℝ → V) 2 (timeMeasure T) := by
    rw [eLpNorm_const_smul, eLpNorm_norm, Real.enorm_eq_ofReal hD]
  have hfinal : eLpNorm (h : ℝ → X) 2 (timeMeasure T) ≤
      ENNReal.ofReal A * eLpNorm (p : ℝ → Y) 2 (timeMeasure T) +
        ENNReal.ofReal B * eLpNorm (q : ℝ → Z) 2 (timeMeasure T) +
        ENNReal.ofReal C * eLpNorm (r : ℝ → W) 2 (timeMeasure T) +
        ENNReal.ofReal D * eLpNorm (s : ℝ → V) 2 (timeMeasure T) := by
    calc
      eLpNorm (h : ℝ → X) 2 (timeMeasure T) ≤ eLpNorm major 2 (timeMeasure T) := hmono
      _ ≤ eLpNorm (A • Pf + B • Qf + C • Rf) 2 (timeMeasure T) +
          eLpNorm (D • Sf) 2 (timeMeasure T) := htri₁
      _ ≤ (eLpNorm (A • Pf + B • Qf) 2 (timeMeasure T) +
            eLpNorm (C • Rf) 2 (timeMeasure T)) +
          eLpNorm (D • Sf) 2 (timeMeasure T) :=
        add_le_add htri₂ le_rfl
      _ ≤ ((eLpNorm (A • Pf) 2 (timeMeasure T) +
              eLpNorm (B • Qf) 2 (timeMeasure T)) +
            eLpNorm (C • Rf) 2 (timeMeasure T)) +
          eLpNorm (D • Sf) 2 (timeMeasure T) :=
        add_le_add (add_le_add htri₃ le_rfl) le_rfl
      _ = _ := by rw [hscaleP, hscaleQ, hscaleR, hscaleS]
  have hp_top : eLpNorm (p : ℝ → Y) 2 (timeMeasure T) ≠ ⊤ := (Lp.memLp p).2.ne
  have hq_top : eLpNorm (q : ℝ → Z) 2 (timeMeasure T) ≠ ⊤ := (Lp.memLp q).2.ne
  have hr_top : eLpNorm (r : ℝ → W) 2 (timeMeasure T) ≠ ⊤ := (Lp.memLp r).2.ne
  have hs_top : eLpNorm (s : ℝ → V) 2 (timeMeasure T) ≠ ⊤ := (Lp.memLp s).2.ne
  have hp_mul : ENNReal.ofReal A * eLpNorm (p : ℝ → Y) 2 (timeMeasure T) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hp_top
  have hq_mul : ENNReal.ofReal B * eLpNorm (q : ℝ → Z) 2 (timeMeasure T) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hq_top
  have hr_mul : ENNReal.ofReal C * eLpNorm (r : ℝ → W) 2 (timeMeasure T) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hr_top
  have hs_mul : ENNReal.ofReal D * eLpNorm (s : ℝ → V) 2 (timeMeasure T) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hs_top
  have hrhs_ne :
      ENNReal.ofReal A * eLpNorm (p : ℝ → Y) 2 (timeMeasure T) +
        ENNReal.ofReal B * eLpNorm (q : ℝ → Z) 2 (timeMeasure T) +
        ENNReal.ofReal C * eLpNorm (r : ℝ → W) 2 (timeMeasure T) +
        ENNReal.ofReal D * eLpNorm (s : ℝ → V) 2 (timeMeasure T) ≠ ⊤ := by
    exact ENNReal.add_ne_top.mpr
      ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨hp_mul, hq_mul⟩, hr_mul⟩, hs_mul⟩
  change (eLpNorm (h : ℝ → X) 2 (timeMeasure T)).toReal ≤
    A * (eLpNorm (p : ℝ → Y) 2 (timeMeasure T)).toReal +
      B * (eLpNorm (q : ℝ → Z) 2 (timeMeasure T)).toReal +
      C * (eLpNorm (r : ℝ → W) 2 (timeMeasure T)).toReal +
      D * (eLpNorm (s : ℝ → V) 2 (timeMeasure T)).toReal
  refine le_trans (ENNReal.toReal_mono hrhs_ne hfinal) ?_
  rw [ENNReal.toReal_add (ENNReal.add_ne_top.mpr
        ⟨ENNReal.add_ne_top.mpr ⟨hp_mul, hq_mul⟩, hr_mul⟩) hs_mul,
    ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨hp_mul, hq_mul⟩) hr_mul,
    ENNReal.toReal_add hp_mul hq_mul,
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hA, ENNReal.toReal_ofReal hB,
    ENNReal.toReal_ofReal hC, ENNReal.toReal_ofReal hD]

omit [NormedSpace ℝ Y] [CompleteSpace Y] in
omit [CompleteSpace X] in
theorem memLp_tame {S : Set X} (hzero : (0 : X) ∈ S) {R : ℝ} (hR : 0 ≤ R)
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (J : X →L[ℝ] Z) (hstate : ∀ u : S, ‖J (u : X)‖ ≤ R)
    (N : S → Y) (hN : Continuous N) (A B C : ℝ≥0)
    (htame : ∀ u v : S,
      ‖N u - N v‖ ≤
        (A : ℝ) * R * ‖(u : X) - (v : X)‖ +
          (B : ℝ) * ‖J ((u : X) - (v : X))‖ +
          (C : ℝ) * (‖(u : X)‖ + ‖(v : X)‖) *
            ‖J ((u : X) - (v : X))‖)
    (f : timeL2 X T) (hf : ∀ᵐ t ∂(timeMeasure T), f t ∈ S) :
    MemLp (fun t => N (aeSetLift hzero f t)) 2 (timeMeasure T) := by
  let z : S := ⟨0, hzero⟩
  let K : ℝ := (A : ℝ) * R + (C : ℝ) * R
  let Q : ℝ := (B : ℝ) * R + ‖N z‖
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have hlift := aeSetLift_aesm hzero f hf
  have hmeas : AEStronglyMeasurable
      (fun t => N (aeSetLift hzero f t)) (timeMeasure T) :=
    hN.comp_aestronglyMeasurable hlift
  let major : ℝ → ℝ := fun t => K * ‖f t‖ + Q
  have hmajor : MemLp major 2 (timeMeasure T) := by
    have hnorm : MemLp (fun t => ‖f t‖) 2 (timeMeasure T) := (Lp.memLp f).norm
    have hscaled : MemLp (K • fun t => ‖f t‖) 2 (timeMeasure T) := hnorm.const_smul K
    have hconst : MemLp (fun _ : ℝ => Q) 2 (timeMeasure T) := memLp_const Q
    have hadd := hscaled.add hconst
    apply (memLp_congr_ae ?_).1 hadd
    filter_upwards with t
    rfl
  refine hmajor.of_le hmeas ?_
  filter_upwards [hf] with t ht
  let u : S := ⟨f t, ht⟩
  have huJ : ‖J (f t)‖ ≤ R := by
    simpa only [u] using hstate u
  have hdiff : ‖N u - N z‖ ≤ K * ‖f t‖ + (B : ℝ) * R := by
    have hraw := htame u z
    have hraw' : ‖N u - N z‖ ≤
        (A : ℝ) * R * ‖f t‖ + (B : ℝ) * ‖J (f t)‖ +
          (C : ℝ) * ‖f t‖ * ‖J (f t)‖ := by
      simpa only [u, z, Subtype.coe_mk, sub_zero, map_zero, norm_zero, add_zero] using hraw
    calc
      ‖N u - N z‖ ≤
          (A : ℝ) * R * ‖f t‖ + (B : ℝ) * ‖J (f t)‖ +
            (C : ℝ) * ‖f t‖ * ‖J (f t)‖ := hraw'
      _ ≤ (A : ℝ) * R * ‖f t‖ + (B : ℝ) * R +
            (C : ℝ) * ‖f t‖ * R := by
        gcongr
      _ = K * ‖f t‖ + (B : ℝ) * R := by
        dsimp only [K]
        ring
  have hn : ‖N u‖ ≤ major t := by
    calc
      ‖N u‖ = ‖(N u - N z) + N z‖ := by rw [sub_add_cancel]
      _ ≤ ‖N u - N z‖ + ‖N z‖ := norm_add_le _ _
      _ ≤ (K * ‖f t‖ + (B : ℝ) * R) + ‖N z‖ :=
        add_le_add hdiff le_rfl
      _ = major t := by
        dsimp only [major, Q]
        ring
  have hmajor0 : 0 ≤ major t := by
    dsimp only [major]
    exact add_nonneg (mul_nonneg hK (norm_nonneg _)) hQ
  change ‖N (aeSetLift hzero f t)‖ ≤ ‖major t‖
  have hu : aeSetLift hzero f t = u := by
    simp only [aeSetLift, dif_pos ht, u]
  rw [hu, Real.norm_eq_abs, abs_of_nonneg hmajor0]
  exact hn

def nemytskiiTameOn {S : Set X} (hzero : (0 : X) ∈ S) {R : ℝ} (hR : 0 ≤ R)
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (J : X →L[ℝ] Z) (hstate : ∀ u : S, ‖J (u : X)‖ ≤ R)
    {N : S → Y} (hN : Continuous N) {A B C : ℝ≥0}
    (htame : ∀ u v : S,
      ‖N u - N v‖ ≤
        (A : ℝ) * R * ‖(u : X) - (v : X)‖ +
          (B : ℝ) * ‖J ((u : X) - (v : X))‖ +
          (C : ℝ) * (‖(u : X)‖ + ‖(v : X)‖) *
            ‖J ((u : X) - (v : X))‖)
    (f : timeL2 X T) (hf : ∀ᵐ t ∂(timeMeasure T), f t ∈ S) :
    timeL2 Y T :=
  (memLp_tame hzero hR J hstate N hN A B C htame f hf).toLp
    (fun t => N (aeSetLift hzero f t))

omit [NormedSpace ℝ Y] [CompleteSpace Y] in
omit [CompleteSpace X] in
theorem nemytskiiTameOn_coeFn {S : Set X} (hzero : (0 : X) ∈ S) {R : ℝ}
    (hR : 0 ≤ R) {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (J : X →L[ℝ] Z) (hstate : ∀ u : S, ‖J (u : X)‖ ≤ R)
    {N : S → Y} (hN : Continuous N) {A B C : ℝ≥0}
    (htame : ∀ u v : S,
      ‖N u - N v‖ ≤
        (A : ℝ) * R * ‖(u : X) - (v : X)‖ +
          (B : ℝ) * ‖J ((u : X) - (v : X))‖ +
          (C : ℝ) * (‖(u : X)‖ + ‖(v : X)‖) *
            ‖J ((u : X) - (v : X))‖)
    (f : timeL2 X T) (hf : ∀ᵐ t ∂(timeMeasure T), f t ∈ S) :
    nemytskiiTameOn hzero hR J hstate hN htame f hf =ᵐ[timeMeasure T]
      fun t => N (aeSetLift hzero f t) :=
  (memLp_tame hzero hR J hstate N hN A B C htame f hf).coeFn_toLp

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear

end
