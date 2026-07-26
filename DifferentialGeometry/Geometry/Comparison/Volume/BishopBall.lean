import DifferentialGeometry.Geometry.Comparison.Volume.BishopPolarFramed

/-!
# Local Bishop comparison for center-metric normal balls

This file assembles the radial Jacobi comparison uniformly over the unit
sphere in orthonormally framed normal coordinates.  It keeps every radius
inside the selected normal source and does not use cut-time data.
-/

noncomputable section

open Filter Metric Set Bundle MeasureTheory
open scoped ENNReal Manifold Topology

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Integral.Measure

private lemma hypSn_scale (q δ t : Real) (hδ : δ ≠ 0) :
    δ * hypSn (q * δ) t = hypSn q (δ * t) := by
  by_cases hq : q = 0
  · subst q
    simp [hypSn]
  · rw [hypSn, if_neg (mul_ne_zero hq hδ), hypSn, if_neg hq]
    rw [show (q * δ) * t = q * (δ * t) by ring]
    field_simp

private lemma hypDensity_scale (q δ : Real) (d : Nat) (t : Real)
    (hδ : δ ≠ 0) :
    δ ^ d * hypDensity (q * δ) d t = hypDensity q d (δ * t) := by
  rw [hypDensity, hypDensity, ← mul_pow, hypSn_scale q δ t hδ]

private lemma ratio_rescale
    (F : Real → Real) (q δ b : Real) (d : Nat)
    (hq : 0 ≤ q) (hδ : 0 < δ)
    (hanti : AntitoneOn
      (fun t => t ^ d * F (δ * t) / hypDensity (q * δ) d t)
      (Ioo (0 : Real) b)) :
    AntitoneOn
      (fun s => s ^ d * F s / hypDensity q d s)
      (Ioo (0 : Real) (δ * b)) := by
  have hqδ : 0 ≤ q * δ := mul_nonneg hq hδ.le
  have ratio_eq (s : Real) (hs : 0 < s) :
      (s / δ) ^ d * F (δ * (s / δ)) /
          hypDensity (q * δ) d (s / δ) =
        s ^ d * F s / hypDensity q d s := by
    have hδne : δ ≠ 0 := hδ.ne'
    have ht : 0 < s / δ := div_pos hs hδ
    have hscale := hypDensity_scale q δ d (s / δ) hδne
    rw [mul_div_cancel₀ s hδne] at hscale
    rw [mul_div_cancel₀ s hδne, div_pow]
    calc
      (s ^ d / δ ^ d) * F s / hypDensity (q * δ) d (s / δ) =
          s ^ d * F s /
            (δ ^ d * hypDensity (q * δ) d (s / δ)) := by ring
      _ = s ^ d * F s / hypDensity q d s := by rw [hscale]
  intro r hr s hs hrs
  have hrδ : r / δ ∈ Ioo (0 : Real) b := by
    constructor
    · exact div_pos hr.1 hδ
    · exact (div_lt_iff₀ hδ).2 (by simpa only [mul_comm] using hr.2)
  have hsδ : s / δ ∈ Ioo (0 : Real) b := by
    constructor
    · exact div_pos hs.1 hδ
    · exact (div_lt_iff₀ hδ).2 (by simpa only [mul_comm] using hs.2)
  have hrsδ : r / δ ≤ s / δ := div_le_div_of_nonneg_right hrs hδ.le
  simpa only [ratio_eq r hr.1, ratio_eq s hs.1] using hanti hrδ hsδ hrsδ

private lemma radial_lintegral_eq
    (P : Real → Real) (d : Nat) {R : Real} (hR : 0 < R)
    (hcont : ContinuousOn P (Icc (0 : Real) R))
    (hP : ∀ t ∈ Icc (0 : Real) R, 0 ≤ P t) :
    (∫⁻ r : Ioi (0 : Real) in Iio (⟨R, hR⟩ : Ioi (0 : Real)),
        ENNReal.ofReal (P r.1) ∂Measure.volumeIoiPow d) =
      ENNReal.ofReal (∫ t in (0 : Real)..R, t ^ d * P t) := by
  have hpowMeas : Measurable (fun r : Ioi (0 : Real) =>
      ENNReal.ofReal (r.1 ^ d)) :=
    ENNReal.measurable_ofReal.comp (measurable_subtype_coe.pow_const d)
  rw [Measure.volumeIoiPow]
  rw [setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable
    _ hpowMeas _ measurableSet_Iio]
  · have hmul :
        (∫⁻ r : Ioi (0 : Real) in Iio (⟨R, hR⟩ : Ioi (0 : Real)),
            ((fun s : Ioi (0 : Real) => ENNReal.ofReal (s.1 ^ d)) *
              (fun s : Ioi (0 : Real) => ENNReal.ofReal (P s.1))) r
            ∂Measure.comap Subtype.val volume) =
          ∫⁻ r : Ioi (0 : Real) in Iio (⟨R, hR⟩ : Ioi (0 : Real)),
            ENNReal.ofReal (r.1 ^ d * P r.1)
            ∂Measure.comap Subtype.val volume := by
      apply setLIntegral_congr_fun measurableSet_Iio
      intro r _hr
      rw [Pi.mul_apply, ← ENNReal.ofReal_mul (pow_nonneg r.2.le d)]
    rw [hmul]
    rw [setLIntegral_subtype measurableSet_Ioi _
      (fun t : Real => ENNReal.ofReal (t ^ d * P t))]
    rw [image_subtype_val_Ioi_Iio, Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    rw [← ofReal_integral_eq_lintegral_ofReal]
    · rw [intervalIntegral.integral_of_le hR.le]
    · exact (continuousOn_pow d).mul hcont |>.intervalIntegrable_of_Icc hR.le |>.1
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact mul_nonneg (pow_nonneg ht.1.le d) (hP t ⟨ht.1.le, ht.2⟩)
  · filter_upwards [] with r
    exact ENNReal.ofReal_lt_top

private theorem integralRatio_anti_on
    {f g : Real → Real} {b : Real}
    (hf : ContinuousOn f (Icc (0 : Real) b))
    (hg : ContinuousOn g (Icc (0 : Real) b))
    (hgpos : ∀ x ∈ Ioo (0 : Real) b, 0 < g x)
    (hratio : AntitoneOn (fun x => f x / g x) (Ioo (0 : Real) b)) :
    AntitoneOn
      (fun r => (∫ x in (0 : Real)..r, f x) / ∫ x in (0 : Real)..r, g x)
      (Ioo (0 : Real) b) := by
  have hderiv_f : ∀ r ∈ Ioo (0 : Real) b,
      HasDerivAt (fun s => ∫ x in (0 : Real)..s, f x) (f r) r := by
    intro r hr
    have hfr : ContinuousOn f (Icc (0 : Real) r) :=
      hf.mono fun x hx => ⟨hx.1, hx.2.trans hr.2.le⟩
    have hfAt : ContinuousAt f r :=
      (hf r ⟨hr.1.le, hr.2.le⟩).continuousAt (Icc_mem_nhds hr.1 hr.2)
    exact intervalIntegral.integral_hasDerivAt_right
      (hfr.intervalIntegrable_of_Icc hr.1.le)
      (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo
        (hf.mono Ioo_subset_Icc_self) r hr) hfAt
  have hderiv_g : ∀ r ∈ Ioo (0 : Real) b,
      HasDerivAt (fun s => ∫ x in (0 : Real)..s, g x) (g r) r := by
    intro r hr
    have hgr : ContinuousOn g (Icc (0 : Real) r) :=
      hg.mono fun x hx => ⟨hx.1, hx.2.trans hr.2.le⟩
    have hgAt : ContinuousAt g r :=
      (hg r ⟨hr.1.le, hr.2.le⟩).continuousAt (Icc_mem_nhds hr.1 hr.2)
    exact intervalIntegral.integral_hasDerivAt_right
      (hgr.intervalIntegrable_of_Icc hr.1.le)
      (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo
        (hg.mono Ioo_subset_Icc_self) r hr) hgAt
  refine ratio_anti_of_cross hderiv_f hderiv_g ?_ ?_
  · intro r hr
    have hgr : ContinuousOn g (Icc (0 : Real) r) :=
      hg.mono fun x hx => ⟨hx.1, hx.2.trans hr.2.le⟩
    exact intervalIntegral.intervalIntegral_pos_of_pos_on
      (hgr.intervalIntegrable_of_Icc hr.1.le)
      (fun x hx => hgpos x ⟨hx.1, hx.2.trans hr.2⟩) hr.1
  · intro r hr
    have hpoint : ∀ x ∈ Ioo (0 : Real) r,
        f r * g x ≤ g r * f x := by
      intro x hx
      have hxb : x ∈ Ioo (0 : Real) b := ⟨hx.1, hx.2.trans hr.2⟩
      have hdiv := hratio hxb hr hx.2.le
      have hmul := (div_le_div_iff₀ (hgpos r hr) (hgpos x hxb)).mp hdiv
      simpa only [mul_comm] using hmul
    have hfr : ContinuousOn f (Icc (0 : Real) r) :=
      hf.mono fun x hx => ⟨hx.1, hx.2.trans hr.2.le⟩
    have hgr : ContinuousOn g (Icc (0 : Real) r) :=
      hg.mono fun x hx => ⟨hx.1, hx.2.trans hr.2.le⟩
    have hleft : IntervalIntegrable (fun x : Real => f r * g x) volume 0 r :=
      (continuousOn_const.mul hgr).intervalIntegrable_of_Icc hr.1.le
    have hright : IntervalIntegrable (fun x : Real => g r * f x) volume 0 r :=
      (continuousOn_const.mul hfr).intervalIntegrable_of_Icc hr.1.le
    have hint := intervalIntegral.integral_mono_on_of_le_Ioo
      (μ := volume) hr.1.le hleft hright hpoint
    simpa only [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_mul_const, mul_comm] using hint

private theorem clm_sum_apply
    {F κ : Type*} [NormedAddCommGroup F] [NormedSpace Real F] [Fintype κ]
    (B : F →L[Real] F →L[Real] Real) (v : κ → F) (w : F) :
    B (∑ i, v i) w = ∑ i, B (v i) w := by
  rw [map_sum, ContinuousLinearMap.sum_apply]

private theorem clm_smul_apply
    {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
    (B : F →L[Real] F →L[Real] Real) (c : Real) (v w : F) :
    B (c • v) w = c * B v w := by
  have h := congrArg (fun L : F →L[Real] Real => L w) (B.map_smul c v)
  simpa only [ContinuousLinearMap.smul_apply, smul_eq_mul] using h

private theorem linIndep_of_ortho
    {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    [TopologicalSpace H] {I : ModelWithCorners Real E H}
    [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I (⊤ : WithTop ℕ∞) M]
    {κ : Type*} [Finite κ] [DecidableEq κ]
    (g : SmoothRiemannianMetric I M) (x : M) (e : κ → E)
    (hON : ∀ i j, g.inner x (e i) (e j) = if i = j then 1 else 0) :
    LinearIndependent Real e := by
  classical
  letI := Fintype.ofFinite κ
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  have hpair := congrArg (fun z : E => g.inner x z (e j)) hc
  change g.inner x (∑ i, c i • e i) (e j) = g.inner x 0 (e j) at hpair
  rw [clm_sum_apply, map_zero, ContinuousLinearMap.zero_apply] at hpair
  rw [Finset.sum_eq_single j] at hpair
  · calc
      c j = c j * 1 := by rw [mul_one]
      _ = c j * g.inner x (e j) (e j) := by rw [hON j j, if_pos rfl]
      _ = g.inner x (c j • e j) (e j) :=
        (clm_smul_apply (g.inner x) (c j) (e j) (e j)).symm
      _ = 0 := hpair
  · intro i _ hij
    calc
      g.inner x (c i • e i) (e j) = c i * g.inner x (e i) (e j) :=
        clm_smul_apply (g.inner x) (c i) (e i) (e j)
      _ = c i * (if i = j then 1 else 0) := by rw [hON i j]
      _ = c i * 0 := by rw [if_neg (by simpa using hij)]
      _ = 0 := mul_zero _
  · intro hj
    exact (hj (Finset.mem_univ j)).elim

private noncomputable def optionFamily
    {E : Type*} {d : Nat} (x : E) (e : Fin d → E) : Option (Fin d) → E
  | none => x
  | some i => e i

private theorem exists_scaled_basis
    {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    [FiniteDimensional Real E]
    [TopologicalSpace H] {I : ModelWithCorners Real E H}
    [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I (⊤ : WithTop ℕ∞) M]
    {d : Nat} (g : SmoothRiemannianMetric I M) (p : M)
    (x : E) (e : Fin d → E)
    (hON : ∀ i j, g.inner p (optionFamily x e i) (optionFamily x e j) =
      if i = j then 1 else 0)
    (hcard : d + 1 = Module.finrank Real E)
    {δ : Real} (hδ : δ ≠ 0) :
    ∃ B : Module.Basis (Option (Fin d)) Real E,
      B none = δ • x ∧ ∀ i, B (some i) = δ • e i := by
  classical
  have hLI : LinearIndependent Real (optionFamily x e) :=
    linIndep_of_ortho g p (optionFamily x e) hON
  have hcard' : Fintype.card (Option (Fin d)) = Module.finrank Real E := by
    simpa using hcard
  let B₀ : Module.Basis (Option (Fin d)) Real E :=
    basisOfLinearIndependentOfCardEqFinrank hLI hcard'
  let δu : Realˣ := Units.mk0 δ hδ
  let B : Module.Basis (Option (Fin d)) Real E := B₀.unitsSMul (fun _ => δu)
  refine ⟨B, ?_, ?_⟩
  · change B₀.unitsSMul (fun _ => δu) none = δ • x
    rw [Module.Basis.unitsSMul_apply]
    change δ • B₀ none = δ • x
    congr 1
    exact congrFun
      (coe_basisOfLinearIndependentOfCardEqFinrank hLI hcard') none
  · intro i
    change B₀.unitsSMul (fun _ => δu) (some i) = δ • e i
    rw [Module.Basis.unitsSMul_apply]
    change δ • B₀ (some i) = δ • e i
    congr 1
    exact congrFun
      (coe_basisOfLinearIndependentOfCardEqFinrank hLI hcard') (some i)

open BonnetMyers

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (⊤ : WithTop ℕ∞) M] [T2Space M] [SigmaCompactSpace M]
  [T2Space (TangentBundle I M)]

/-- Hyperbolic radial model volume, without the sphere-area factor. -/
def hypRadVol (q : Real) (d : Nat) (R : Real) : Real :=
  ∫ t in (0 : Real)..R, hypDensity q d t

/-- The hyperbolic radial model volume is positive at positive radius. -/
theorem hypRadVol_pos {q R : Real} {d : Nat} (hq : 0 ≤ q) (hR : 0 < R) :
    0 < hypRadVol q d R := by
  exact intervalIntegral.intervalIntegral_pos_of_pos_on
    ((hypDen_continuous q d).intervalIntegrable (0 : Real) R)
    (fun t ht => hypDensity_pos hq ht.1) hR

/-- Volume of a center-metric tangent ball under the framed normal map. -/
def normalBallVolume (g : SmoothRiemannianMetric I M) (p : M)
    (R : Real) : ENNReal :=
  riemannianVolumeMeasure (I := I) (M := M) g
    (framedExpDiffeo (I := I) g p '' ball (0 : E) R)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- On one center-dependent radius, every framed unit direction has an
antitone ratio of its polar density to the hyperbolic model density. -/
theorem exists_framed_ratio
    [PseudoEMetricSpace M] [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (q : Real) (hq : 0 ≤ q)
    (hd : 0 < Module.finrank Real E - 1)
    (hRic : RicciBoundedBelow (I := I) g
      (-(((Module.finrank Real E - 1 : Nat) : Real) * q ^ 2))) :
    ∃ ρ : Real, 0 < ρ ∧
      ball (0 : E) ρ ⊆ (framedExpDiffeo (I := I) g p).source ∧
      ∀ u : sphere (0 : E) 1,
        AntitoneOn
          (fun r =>
            r ^ (Module.finrank Real E - 1) *
                paramDensity (I := I) g (framedExpDiffeo (I := I) g p)
                  (r • u.1) /
              hypDensity q (Module.finrank Real E - 1) r)
          (Ioo (0 : Real) ρ) := by
  let d : Nat := Module.finrank Real E - 1
  obtain ⟨r₀, hr₀, hcmp⟩ :=
    exists_radial_cmp (I := I) (ι := Fin d) g hEnorm p
  let rExp : Real := expMapC2Radius (I := I) g p
  let L : E →L[Real] E :=
    (normalFrame (I := I) g p).toContinuousLinearMap
  let C : Real := ‖L‖
  let a : Real := min r₀ rExp
  let δ : Real := a / (2 * (C + 1))
  let ρ : Real := δ / 2
  have hrExp : 0 < rExp := by
    simpa only [rExp] using expMapC2Radius_pos (I := I) g p
  have hC : 0 ≤ C := by
    simpa only [C] using norm_nonneg L
  have ha : 0 < a := by
    simpa only [a] using lt_min hr₀ hrExp
  have hden : 0 < 2 * (C + 1) :=
    mul_pos (by norm_num) (add_pos_of_nonneg_of_pos hC zero_lt_one)
  have hδ : 0 < δ := by
    simpa only [δ] using div_pos ha hden
  have hρ : 0 < ρ := by
    simpa only [ρ] using div_pos hδ (by norm_num : (0 : Real) < 2)
  have hC1 : 0 < C + 1 := add_pos_of_nonneg_of_pos hC zero_lt_one
  have hδC1 : δ * (C + 1) = a / 2 := by
    dsimp only [δ]
    field_simp [ne_of_gt hC1]
  have hδC_r₀ : δ * C < r₀ := by
    calc
      δ * C ≤ δ * (C + 1) := mul_le_mul_of_nonneg_left (by linarith) hδ.le
      _ = a / 2 := hδC1
      _ < a := by linarith
      _ ≤ r₀ := min_le_left _ _
  have hδC_rExp : δ * C < rExp := by
    calc
      δ * C ≤ δ * (C + 1) := mul_le_mul_of_nonneg_left (by linarith) hδ.le
      _ = a / 2 := hδC1
      _ < a := by linarith
      _ ≤ rExp := min_le_right _ _
  have hballSource :
      ball (0 : E) ρ ⊆ (framedExpDiffeo (I := I) g p).source := by
    intro z hz
    rw [framedExp_source]
    apply mem_expMapDiffeo_source_of_norm_lt_radius (I := I) g p
    have hzρ : ‖z‖ < ρ := by
      simpa only [mem_ball, dist_zero_right] using hz
    have hρδ : ρ < δ := by
      dsimp only [ρ]
      linarith
    have hzδ : ‖z‖ < δ := hzρ.trans hρδ
    have hLz := L.le_opNorm z
    calc
      ‖(show E from normalFrame (I := I) g p z)‖ ≤ C * ‖z‖ := by
        simpa only [L, C] using hLz
      _ ≤ (C + 1) * ‖z‖ :=
        mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg z)
      _ < (C + 1) * δ := mul_lt_mul_of_pos_left hzδ hC1
      _ = δ * (C + 1) := mul_comm _ _
      _ = a / 2 := hδC1
      _ < a := by linarith
      _ ≤ rExp := min_le_right _ _
      _ = expMapC2Radius (I := I) g p := rfl
  refine ⟨ρ, hρ, hballSource, ?_⟩
  intro u
  let x : E := normalFrame (I := I) g p u.1
  have huNorm : ‖u.1‖ = 1 := by
    simpa only [mem_sphere_zero_iff_norm] using u.2
  have hxUnit : g.inner p x x = 1 := by
    dsimp only [x]
    rw [normalFrame_inner, real_inner_self_eq_norm_sq, huNorm, one_pow]
  obtain ⟨e, heON, hePerp⟩ := exists_ortho_perp (I := I) g p x hxUnit
  have hxPerp : ∀ i : Fin d, g.inner p x (e i) = 0 := by
    intro i
    rw [g.symm]
    exact hePerp i
  have hfullON : ∀ i j : Option (Fin d),
      g.inner p (optionFamily x e i) (optionFamily x e j) =
        if i = j then 1 else 0 := by
    intro i j
    cases i with
    | none =>
        cases j with
        | none => simpa only [optionFamily, if_pos] using hxUnit
        | some j => simp [optionFamily, hxPerp j]
    | some i =>
        cases j with
        | none => simp [optionFamily, hePerp i]
        | some j => simpa only [optionFamily, Option.some.injEq] using heON i j
  have hcardPlus : d + 1 = Module.finrank Real E := by
    dsimp only [d]
    omega
  obtain ⟨B, hBnone, hBsome⟩ :=
    exists_scaled_basis g p x e hfullON hcardPlus hδ.ne'
  have hxC : ‖x‖ ≤ C := by
    have hLu := L.le_opNorm u.1
    simpa only [x, L, C, huNorm, mul_one] using hLu
  have heC : ∀ i : Fin d, ‖(show E from e i)‖ ≤ C := by
    intro i
    let w : E := (normalFrame (I := I) g p).symm (e i)
    have hwNorm : ‖w‖ = 1 := by
      have hframe := normalFrame_sqrt (I := I) g p w
      rw [show normalFrame (I := I) g p w = e i by
        exact (normalFrame (I := I) g p).apply_symm_apply (e i)] at hframe
      rw [heON i i, if_pos rfl, Real.sqrt_one] at hframe
      exact hframe.symm
    have hLw := L.le_opNorm w
    have happly : L w = (show E from e i) := by
      dsimp only [L, w]
      exact (normalFrame (I := I) g p).apply_symm_apply (e i)
    rw [happly] at hLw
    simpa only [C, hwNorm, mul_one] using hLw
  have hBnone_r₀ : ‖B none‖ < r₀ := by
    rw [hBnone, norm_smul, Real.norm_of_nonneg hδ.le]
    exact (mul_le_mul_of_nonneg_left hxC hδ.le).trans_lt hδC_r₀
  have hBsome_r₀ : ∀ i : Fin d, ‖B (some i)‖ < r₀ := by
    intro i
    rw [hBsome i, norm_smul, Real.norm_of_nonneg hδ.le]
    exact (mul_le_mul_of_nonneg_left (heC i) hδ.le).trans_lt hδC_r₀
  have hBnone_exp : ‖B none‖ < rExp := by
    rw [hBnone, norm_smul, Real.norm_of_nonneg hδ.le]
    exact (mul_le_mul_of_nonneg_left hxC hδ.le).trans_lt hδC_rExp
  have htransLI : LinearIndependent Real (fun i : Fin d => B (some i)) :=
    B.linearIndependent.comp (fun i : Fin d => some i) (Option.some_injective (Fin d))
  have hscaledPerp : ∀ i : Fin d, g.inner p (B none) (B (some i)) = 0 := by
    intro i
    rw [hBnone, hBsome i]
    calc
      g.inner p (δ • x) (δ • e i) = δ * g.inner p x (δ • e i) :=
        clm_smul_apply (g.inner p) δ x (δ • e i)
      _ = δ * (δ * g.inner p x (e i)) := by
        rw [(g.inner p x).map_smul]
        simp only [smul_eq_mul]
      _ = 0 := by rw [hxPerp i, mul_zero, mul_zero]
  have hscaledInner : g.inner p (B none) (B none) = δ ^ 2 := by
    rw [hBnone]
    have hright : g.inner p x (δ • x) = δ * g.inner p x x := by
      simpa only [smul_eq_mul] using (g.inner p x).map_smul δ x
    calc
      g.inner p (δ • x) (δ • x) = δ * g.inner p x (δ • x) :=
        clm_smul_apply (g.inner p) δ x (δ • x)
      _ = δ * (δ * g.inner p x x) := by rw [hright]
      _ = δ ^ 2 := by rw [hxUnit]; ring
  have hscaledSqrt : Real.sqrt (g.inner p (B none) (B none)) = δ := by
    rw [hscaledInner, Real.sqrt_sq hδ.le]
  have hcard : Fintype.card (Fin d) = Module.finrank Real E - 1 := by
    simp only [Fintype.card_fin, d]
  have hcmpData := hcmp (B none) (fun i : Fin d => B (some i)) q (1 / 2)
    hBnone_r₀ hBsome_r₀ (B.ne_zero none) htransLI hscaledPerp hq
    (by norm_num) (by norm_num) hcard hd hRic
  have hcurve : AntitoneOn
      (fun t =>
        curveDensity (I := I) g (radialCurve (I := I) g p (B none))
            (fun i : Fin d => radialJacobiField (I := I) g p (B none)
              (B (some i))) t /
          hypDensity (q * δ) d t)
      (Ioo (0 : Real) (1 / 2)) := by
    simpa only [hscaledSqrt, Fintype.card_fin] using hcmpData.2
  have hrad : ∀ t ∈ Ioo (0 : Real) (1 / 2),
      ‖t • B none‖ < expMapC2Radius (I := I) g p := by
    intro t ht
    rw [norm_smul, Real.norm_of_nonneg ht.1.le]
    calc
      t * ‖B none‖ ≤ 1 * ‖B none‖ :=
        mul_le_mul_of_nonneg_right
          (le_of_lt (ht.2.trans (by norm_num : (1 / 2 : Real) < 1)))
          (norm_nonneg (B none))
      _ = ‖B none‖ := one_mul _
      _ < rExp := hBnone_exp
      _ = expMapC2Radius (I := I) g p := rfl
  have hsrc : MapsTo (fun t : Real => t • B none)
      (Ioo (0 : Real) (1 / 2)) (expMapDiffeo (I := I) g p).source := by
    intro t ht
    exact mem_expMapDiffeo_source_of_norm_lt_radius (I := I) g p (hrad t ht)
  have hrawScaled := normalRatio_anti (I := I) g p (B none) B rfl
    hscaledPerp (q * δ) hsrc hrad (by
      simpa only [Fintype.card_fin, d] using hcurve)
  let F : Real → Real := fun s =>
    normalChartDensity (I := I) g p (s • x)
  have hrawParam : AntitoneOn
      (fun t => t ^ d * F (δ * t) / hypDensity (q * δ) d t)
      (Ioo (0 : Real) (1 / 2)) := by
    simpa only [F, hBnone, Fintype.card_fin, smul_smul, mul_comm] using hrawScaled
  have hrawPhysical := ratio_rescale F q δ (1 / 2) d hq hδ hrawParam
  have hrawPhysical' : AntitoneOn
      (fun s => s ^ d * normalChartDensity (I := I) g p
          (s • normalFrame (I := I) g p u.1) / hypDensity q d s)
      (Ioo (0 : Real) ρ) := by
    simpa only [F, x, ρ, div_eq_mul_inv, one_mul] using hrawPhysical
  have hframedSrc : MapsTo (fun s : Real => s • u.1)
      (Ioo (0 : Real) ρ) (framedExpDiffeo (I := I) g p).source := by
    intro s hs
    apply hballSource
    rw [mem_ball, dist_zero_right, norm_smul,
      Real.norm_of_nonneg hs.1.le, huNorm, mul_one]
    exact hs.2
  simpa only [d] using
    framedRatio_anti (I := I) g p u.1 q d hframedSrc hrawPhysical'

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- Local Bishop comparison for framed normal balls, in cross-multiplied form. -/
theorem normalBall_cross
    [PseudoEMetricSpace M] [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (q : Real) (hq : 0 ≤ q)
    (hd : 0 < Module.finrank Real E - 1)
    (hRic : RicciBoundedBelow (I := I) g
      (-(((Module.finrank Real E - 1 : Nat) : Real) * q ^ 2))) :
    ∃ ρ : Real, 0 < ρ ∧ ∀ {r R : Real},
      0 < r → r ≤ R → R < ρ →
        normalBallVolume (I := I) g p R *
            ENNReal.ofReal (hypRadVol q (Module.finrank Real E - 1) r) ≤
          normalBallVolume (I := I) g p r *
            ENNReal.ofReal (hypRadVol q (Module.finrank Real E - 1) R) := by
  letI : Nontrivial E := Module.nontrivial_of_finrank_pos
    (Nat.pos_of_ne_zero (NeZero.ne (Module.finrank Real E)))
  letI : MeasurableSpace E := borel E
  letI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace M := borel M
  letI : BorelSpace M := ⟨rfl⟩
  let d : Nat := Module.finrank Real E - 1
  obtain ⟨ρ, hρ, hsource, hratio⟩ :=
    exists_framed_ratio (I := I) g hEnorm p q hq hd hRic
  refine ⟨ρ, hρ, ?_⟩
  intro r R hr hrR hRρ
  have hR : 0 < R := hr.trans_le hrR
  let b : Real := (R + ρ) / 2
  have hb : 0 < b := by
    dsimp only [b]
    linarith
  have hRb : R < b := by
    dsimp only [b]
    linarith
  have hbρ : b < ρ := by
    dsimp only [b]
    linarith
  let P : sphere (0 : E) 1 → Real → Real := fun u t =>
    paramDensity (I := I) g (framedExpDiffeo (I := I) g p) (t • u.1)
  let A : sphere (0 : E) 1 → Real → Real := fun u s =>
    ∫ t in (0 : Real)..s, t ^ d * P u t
  have hP_nonneg (u : sphere (0 : E) 1) (t : Real) : 0 ≤ P u t := by
    dsimp only [P, paramDensity]
    exact Real.sqrt_nonneg _
  have hP_cont (u : sphere (0 : E) 1) {s : Real}
      (hs : 0 ≤ s) (hsρ : s < ρ) : ContinuousOn (P u) (Icc (0 : Real) s) := by
    have hu : ‖u.1‖ = 1 := by
      simpa only [mem_sphere_zero_iff_norm] using u.2
    have hmap : MapsTo (fun t : Real => t • u.1) (Icc (0 : Real) s)
        (framedExpDiffeo (I := I) g p).source := by
      intro t ht
      apply hsource
      rw [mem_ball, dist_zero_right, norm_smul,
        Real.norm_of_nonneg ht.1, hu, mul_one]
      exact ht.2.trans_lt hsρ
    exact (paramDensity_contOn (I := I) g (framedExpDiffeo (I := I) g p)).comp
      (by fun_prop) hmap
  have hA_nonneg (u : sphere (0 : E) 1) {s : Real}
      (hs : 0 ≤ s) : 0 ≤ A u s := by
    dsimp only [A]
    exact intervalIntegral.integral_nonneg hs fun t ht =>
      mul_nonneg (pow_nonneg ht.1 d) (hP_nonneg u t)
  have hmodel_pos {s : Real} (hs : 0 < s) : 0 < hypRadVol q d s := by
    exact intervalIntegral.intervalIntegral_pos_of_pos_on
      ((hypDen_continuous q d).intervalIntegrable (0 : Real) s)
      (fun t ht => hypDensity_pos hq ht.1) hs
  have hpolar (s : Real) (hs : 0 < s) (hsρ : s < ρ) :
      normalBallVolume (I := I) g p s =
        ∫⁻ u : sphere (0 : E) 1, ENNReal.ofReal (A u s)
          ∂(modelHaar (E := E)).toSphere := by
    rw [normalBallVolume, framedBall_polar (I := I) g p hs
      ((Metric.ball_subset_ball hsρ.le).trans hsource)]
    apply lintegral_congr
    intro u
    exact radial_lintegral_eq (P u) d hs
      (hP_cont u hs.le hsρ) (fun t _ht => hP_nonneg u t)
  have hdir_real (u : sphere (0 : E) 1) :
      A u R * hypRadVol q d r ≤ A u r * hypRadVol q d R := by
    have hfcont : ContinuousOn (fun t : Real => t ^ d * P u t)
        (Icc (0 : Real) b) :=
      (continuousOn_pow d).mul (hP_cont u hb.le hbρ)
    have hgcont : ContinuousOn (hypDensity q d) (Icc (0 : Real) b) :=
      (hypDen_continuous q d).continuousOn
    have hpoint : AntitoneOn
        (fun t => (t ^ d * P u t) / hypDensity q d t)
        (Ioo (0 : Real) b) := by
      exact (hratio u).mono fun t ht => ⟨ht.1, ht.2.trans hbρ⟩
    have hcum := integralRatio_anti_on hfcont hgcont
      (fun t ht => hypDensity_pos hq ht.1) hpoint
    have hquot := hcum
      ⟨hr, hrR.trans_lt hRb⟩ ⟨hR, hRb⟩ hrR
    exact (div_le_div_iff₀ (hmodel_pos hR) (hmodel_pos hr)).mp hquot
  have hdir (u : sphere (0 : E) 1) :
      ENNReal.ofReal (A u R) * ENNReal.ofReal (hypRadVol q d r) ≤
        ENNReal.ofReal (A u r) * ENNReal.ofReal (hypRadVol q d R) := by
    rw [← ENNReal.ofReal_mul (hA_nonneg u hR.le),
      ← ENNReal.ofReal_mul (hA_nonneg u hr.le)]
    exact ENNReal.ofReal_le_ofReal (hdir_real u)
  rw [show Module.finrank Real E - 1 = d by rfl]
  rw [hpolar R hR hRρ, hpolar r hr (hrR.trans_lt hRρ)]
  rw [← lintegral_mul_const' (ENNReal.ofReal (hypRadVol q d r))
    (fun u : sphere (0 : E) 1 => ENNReal.ofReal (A u R)) ENNReal.ofReal_ne_top]
  rw [← lintegral_mul_const' (ENNReal.ofReal (hypRadVol q d R))
    (fun u : sphere (0 : E) 1 => ENNReal.ofReal (A u r)) ENNReal.ofReal_ne_top]
  exact lintegral_mono hdir

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The framed normal-ball volume divided by the hyperbolic model volume is
antitone on one center-dependent interval. -/
theorem normalBall_ratio
    [PseudoEMetricSpace M] [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (q : Real) (hq : 0 ≤ q)
    (hd : 0 < Module.finrank Real E - 1)
    (hRic : RicciBoundedBelow (I := I) g
      (-(((Module.finrank Real E - 1 : Nat) : Real) * q ^ 2))) :
    ∃ ρ : Real, 0 < ρ ∧
      AntitoneOn
        (fun R => normalBallVolume (I := I) g p R /
          ENNReal.ofReal (hypRadVol q (Module.finrank Real E - 1) R))
        (Ioo (0 : Real) ρ) := by
  obtain ⟨ρ, hρ, hcross⟩ := normalBall_cross (I := I) g hEnorm p q hq hd hRic
  refine ⟨ρ, hρ, ?_⟩
  intro r hr R hR hrR
  have hmr : 0 < hypRadVol q (Module.finrank Real E - 1) r :=
    hypRadVol_pos hq hr.1
  have hmR : 0 < hypRadVol q (Module.finrank Real E - 1) R :=
    hypRadVol_pos hq hR.1
  have hmr0 : ENNReal.ofReal (hypRadVol q (Module.finrank Real E - 1) r) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr hmr
  have hmR0 : ENNReal.ofReal (hypRadVol q (Module.finrank Real E - 1) R) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr hmR
  rw [ENNReal.div_le_iff hmR0 ENNReal.ofReal_ne_top]
  rw [← ENNReal.mul_div_right_comm]
  rw [ENNReal.le_div_iff_mul_le (Or.inl hmr0) (Or.inl ENNReal.ofReal_ne_top)]
  exact hcross hr.1 hrR hR.2

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
