/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SmoothHandleModelAttachment

open Set Complex
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.PiecewiseLinear

noncomputable def slabChartVec (σ c : ℝ) (p : EuclideanSpace ℝ (Fin 2) × ℝ) :
    EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![σ * p.2 + c, p.1 0, p.1 1]

noncomputable def slabChartInv (σ c : ℝ) (y : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 2) × ℝ :=
  (cornerChartPlane y, σ * (y 0 - c))

def slabChartTarget (σ c : ℝ) (D : Set (EuclideanSpace ℝ (Fin 2) × ℝ)) :
    Set (EuclideanHalfSpace 3) :=
  {y | slabChartInv σ c y.val ∈ D}

theorem slabChartVec_zero_coord (σ c : ℝ) (p : EuclideanSpace ℝ (Fin 2) × ℝ) :
    slabChartVec σ c p 0 = σ * p.2 + c := rfl

theorem slabChartInv_vec {σ : ℝ} (hσ : σ * σ = 1) (c : ℝ) (p : EuclideanSpace ℝ (Fin 2) × ℝ) :
    slabChartInv σ c (slabChartVec σ c p) = p := by
  have h1 : cornerChartPlane (slabChartVec σ c p) = p.1 := by
    ext i
    fin_cases i <;> simp [cornerChartPlane, slabChartVec]
  have h2 : σ * (slabChartVec σ c p 0 - c) = p.2 := by
    rw [slabChartVec_zero_coord, add_sub_cancel_right, ← mul_assoc, hσ, one_mul]
  exact Prod.ext h1 h2

theorem slabChartVec_inv {σ : ℝ} (hσ : σ * σ = 1) (c : ℝ) (y : EuclideanSpace ℝ (Fin 3)) :
    slabChartVec σ c (slabChartInv σ c y) = y := by
  ext i
  fin_cases i
  · change σ * (σ * (y 0 - c)) + c = y 0
    rw [← mul_assoc, hσ, one_mul, sub_add_cancel]
  · simp [cornerChartPlane, slabChartVec, slabChartInv]
  · simp [cornerChartPlane, slabChartVec, slabChartInv]

theorem contDiff_cornerChartPlane : ContDiff ℝ ∞ cornerChartPlane := by
  apply (contDiff_piLp 2).2
  intro i
  fin_cases i
  · exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) 1).contDiff
  · exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) 2).contDiff

theorem contDiff_slabChartVec (σ c : ℝ) : ContDiff ℝ ∞ (slabChartVec σ c) := by
  apply (contDiff_piLp 2).2
  intro i
  fin_cases i
  · change ContDiff ℝ ∞ fun p : EuclideanSpace ℝ (Fin 2) × ℝ => σ * p.2 + c
    exact (contDiff_const.mul contDiff_snd).add contDiff_const
  · change ContDiff ℝ ∞ fun p : EuclideanSpace ℝ (Fin 2) × ℝ => p.1 0
    exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0).contDiff.comp contDiff_fst
  · change ContDiff ℝ ∞ fun p : EuclideanSpace ℝ (Fin 2) × ℝ => p.1 1
    exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 1).contDiff.comp contDiff_fst

theorem contDiff_slabChartInv (σ c : ℝ) : ContDiff ℝ ∞ (slabChartInv σ c) :=
  contDiff_cornerChartPlane.prodMk (contDiff_const.mul
    ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) 0).contDiff.sub contDiff_const))

theorem isOpen_slabChartTarget (σ c : ℝ) {D : Set (EuclideanSpace ℝ (Fin 2) × ℝ)}
    (hD : IsOpen D) : IsOpen (slabChartTarget σ c D) :=
  hD.preimage ((contDiff_slabChartInv σ c).continuous.comp continuous_subtype_val)

theorem slabChart_mem {σ c : ℝ} (hσ : σ * σ = 1) {D W : Set (EuclideanSpace ℝ (Fin 2) × ℝ)}
    (hW : ∀ p ∈ D, (p ∈ W ↔ 0 ≤ σ * p.2 + c)) :
    ∀ p ∈ D, p ∈ W → 0 ≤ slabChartVec σ c p 0 ∧
      toHalfSpace (slabChartVec σ c p) ∈ slabChartTarget σ c D := by
  intro p hp hpW
  have h0 : 0 ≤ slabChartVec σ c p 0 := (hW p hp).mp hpW
  refine ⟨h0, ?_⟩
  change slabChartInv σ c (toHalfSpace (slabChartVec σ c p)).val ∈ D
  rw [toHalfSpace_val h0, slabChartInv_vec hσ]
  exact hp

theorem slabChart_inv_mem {σ c : ℝ} (hσ : σ * σ = 1)
    {D W : Set (EuclideanSpace ℝ (Fin 2) × ℝ)} (hW : ∀ p ∈ D, (p ∈ W ↔ 0 ≤ σ * p.2 + c)) :
    ∀ y ∈ slabChartTarget σ c D, slabChartInv σ c y.val ∈ D ∧ slabChartInv σ c y.val ∈ W := by
  intro y hy
  refine ⟨hy, (hW _ hy).mpr ?_⟩
  change 0 ≤ σ * (σ * (y.val 0 - c)) + c
  rw [← mul_assoc, hσ, one_mul, sub_add_cancel]
  exact y.2

theorem contMDiffAt_slabChartInv (σ c : ℝ) (y : EuclideanHalfSpace 3) :
    ContMDiffAt (𝓡∂ 3) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) ∞
      (fun y : EuclideanHalfSpace 3 => slabChartInv σ c y.val) y :=
  contMDiffAt_comp_val_of_contDiffWithinAt
    (contDiff_slabChartInv σ c).contDiffAt.contDiffWithinAt

noncomputable def cornerModelVec (L : ℝ × ℝ → ℝ × ℝ) (p : EuclideanSpace ℝ (Fin 2) × ℝ) :
    EuclideanSpace ℝ (Fin 3) :=
  cornerChartVec (L (‖p.1‖, p.2)).1 (L (‖p.1‖, p.2)).2 (‖p.1‖⁻¹ • p.1)

noncomputable def cornerModelInv (Linv : ℝ × ℝ → ℝ × ℝ) (y : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 2) × ℝ :=
  ((Linv ((cornerChartInvZ y).re, (cornerChartInvZ y).im)).1 •
      (‖cornerChartPlane y‖⁻¹ • cornerChartPlane y),
    (Linv ((cornerChartInvZ y).re, (cornerChartInvZ y).im)).2)

def cornerModelSource (L : ℝ × ℝ → ℝ × ℝ) (Ω : Set (ℝ × ℝ)) :
    Set (EuclideanSpace ℝ (Fin 2) × ℝ) :=
  {p | p.1 ≠ 0 ∧ L (‖p.1‖, p.2) ∈ Ω}

def cornerModelTarget (Ω : Set (ℝ × ℝ)) : Set (EuclideanHalfSpace 3) :=
  {y | cornerChartPlane y.val ≠ 0 ∧
    ((cornerChartInvZ y.val).re, (cornerChartInvZ y.val).im) ∈ Ω}

theorem isOpen_cornerModelSource {L : ℝ × ℝ → ℝ × ℝ} (hL : Continuous L) {Ω : Set (ℝ × ℝ)}
    (hΩ : IsOpen Ω) : IsOpen (cornerModelSource L Ω) :=
  (isOpen_ne_fun continuous_fst continuous_const).inter
    (hΩ.preimage (hL.comp ((continuous_norm.comp continuous_fst).prodMk continuous_snd)))

theorem isOpen_cornerModelTarget {Ω : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) :
    IsOpen (cornerModelTarget Ω) := by
  have hS : IsOpen {y : EuclideanHalfSpace 3 | cornerChartPlane y.val ≠ 0} :=
    isOpen_ne_fun (contDiff_cornerChartPlane.continuous.comp continuous_subtype_val)
      continuous_const
  have hc : ContinuousOn (fun y : EuclideanHalfSpace 3 =>
      ((cornerChartInvZ y.val).re, (cornerChartInvZ y.val).im))
      {y : EuclideanHalfSpace 3 | cornerChartPlane y.val ≠ 0} :=
    ((continuous_fst.prodMk (continuous_fst.comp continuous_snd)).comp_continuousOn
      continuousOn_cornerChartInv).comp continuous_subtype_val.continuousOn
      fun y hy => ⟨y.2, hy⟩
  exact hc.isOpen_inter_preimage hS hΩ

theorem cornerChartVec_facts {a b : ℝ} (hab : (a : ℂ) + b * I ∈ concaveQuadrant)
    (hab1 : ‖(a : ℂ) + b * I‖ < 1) {w : EuclideanSpace ℝ (Fin 2)} (hw : w ≠ 0) :
    cornerChartInvZ (cornerChartVec a b (‖w‖⁻¹ • w)) = a + b * I ∧
      cornerChartPlane (cornerChartVec a b (‖w‖⁻¹ • w)) ≠ 0 ∧
      ‖cornerChartPlane (cornerChartVec a b (‖w‖⁻¹ • w))‖⁻¹ •
        cornerChartPlane (cornerChartVec a b (‖w‖⁻¹ • w)) = ‖w‖⁻¹ • w := by
  have hu : ‖‖w‖⁻¹ • w‖ = 1 := norm_smul_inv_norm hw
  refine ⟨cornerChartInvZ_cornerChartVec hab hab1 hu, ?_,
    cornerChartPlane_normalize hab hab1 hu⟩
  intro h0
  have hn := norm_cornerChartPlane_cornerChartVec hab hab1 hu
  rw [h0, norm_zero] at hn
  have h := abs_im_concaveCornerMap_lt hab hab1
  linarith [(abs_lt.mp h).1]

theorem cornerModelInv_facts {Linv : ℝ × ℝ → ℝ × ℝ} {Ω : Set (ℝ × ℝ)}
    (hΩr : ∀ q ∈ Ω, 0 < (Linv q).1) {y : EuclideanHalfSpace 3} (hy : y ∈ cornerModelTarget Ω) :
    (cornerModelInv Linv y.val).1 ≠ 0 ∧
      (‖(cornerModelInv Linv y.val).1‖, (cornerModelInv Linv y.val).2) =
        Linv ((cornerChartInvZ y.val).re, (cornerChartInvZ y.val).im) ∧
      ‖(cornerModelInv Linv y.val).1‖⁻¹ • (cornerModelInv Linv y.val).1 =
        ‖cornerChartPlane y.val‖⁻¹ • cornerChartPlane y.val := by
  obtain ⟨hP, hq⟩ := hy
  have hr := hΩr _ hq
  have hu : ‖‖cornerChartPlane y.val‖⁻¹ • cornerChartPlane y.val‖ = 1 := norm_smul_inv_norm hP
  have hn : ‖(cornerModelInv Linv y.val).1‖ =
      (Linv ((cornerChartInvZ y.val).re, (cornerChartInvZ y.val).im)).1 := by
    change ‖(Linv ((cornerChartInvZ y.val).re, (cornerChartInvZ y.val).im)).1 •
      (‖cornerChartPlane y.val‖⁻¹ • cornerChartPlane y.val)‖ = _
    rw [norm_smul, hu, mul_one, Real.norm_of_nonneg hr.le]
  refine ⟨?_, ?_, ?_⟩
  · intro h0
    rw [h0, norm_zero] at hn
    linarith
  · rw [hn]
    rfl
  · rw [hn]
    change (Linv ((cornerChartInvZ y.val).re, (cornerChartInvZ y.val).im)).1⁻¹ •
      (Linv ((cornerChartInvZ y.val).re, (cornerChartInvZ y.val).im)).1 •
        (‖cornerChartPlane y.val‖⁻¹ • cornerChartPlane y.val) = _
    rw [smul_smul, inv_mul_cancel₀ hr.ne', one_smul]

theorem cornerModel_mem {L : ℝ × ℝ → ℝ × ℝ} {Ω : Set (ℝ × ℝ)}
    (hΩ1 : ∀ q ∈ Ω, ‖((q.1 : ℂ) + q.2 * I)‖ < 1) {W : Set (EuclideanSpace ℝ (Fin 2) × ℝ)}
    (hW : ∀ p ∈ cornerModelSource L Ω, (p ∈ W ↔
      ((L (‖p.1‖, p.2)).1 : ℂ) + (L (‖p.1‖, p.2)).2 * I ∈ concaveQuadrant)) :
    ∀ p ∈ cornerModelSource L Ω, p ∈ W → 0 ≤ cornerModelVec L p 0 ∧
      toHalfSpace (cornerModelVec L p) ∈ cornerModelTarget Ω := by
  intro p hp hpW
  have hQ := (hW p hp).mp hpW
  obtain ⟨hZ, hP, -⟩ := cornerChartVec_facts hQ (hΩ1 _ hp.2) hp.1
  have h0 : 0 ≤ cornerModelVec L p 0 := cornerChartVec_nonneg hQ _
  refine ⟨h0, ?_⟩
  change cornerChartPlane (toHalfSpace (cornerModelVec L p)).val ≠ 0 ∧
    ((cornerChartInvZ (toHalfSpace (cornerModelVec L p)).val).re,
      (cornerChartInvZ (toHalfSpace (cornerModelVec L p)).val).im) ∈ Ω
  rw [toHalfSpace_val h0]
  refine ⟨hP, ?_⟩
  change ((cornerChartInvZ (cornerChartVec (L (‖p.1‖, p.2)).1 (L (‖p.1‖, p.2)).2
      (‖p.1‖⁻¹ • p.1))).re, (cornerChartInvZ (cornerChartVec (L (‖p.1‖, p.2)).1
      (L (‖p.1‖, p.2)).2 (‖p.1‖⁻¹ • p.1))).im) ∈ Ω
  rw [hZ]
  simpa using hp.2

theorem cornerModel_inv_mem {L Linv : ℝ × ℝ → ℝ × ℝ} (hLL : ∀ q, L (Linv q) = q)
    {Ω : Set (ℝ × ℝ)} (hΩr : ∀ q ∈ Ω, 0 < (Linv q).1) {W : Set (EuclideanSpace ℝ (Fin 2) × ℝ)}
    (hW : ∀ p ∈ cornerModelSource L Ω, (p ∈ W ↔
      ((L (‖p.1‖, p.2)).1 : ℂ) + (L (‖p.1‖, p.2)).2 * I ∈ concaveQuadrant)) :
    ∀ y ∈ cornerModelTarget Ω, cornerModelInv Linv y.val ∈ cornerModelSource L Ω ∧
      cornerModelInv Linv y.val ∈ W := by
  intro y hy
  obtain ⟨hne, hpair, -⟩ := cornerModelInv_facts hΩr hy
  have hLq : L (‖(cornerModelInv Linv y.val).1‖, (cornerModelInv Linv y.val).2) =
      ((cornerChartInvZ y.val).re, (cornerChartInvZ y.val).im) := by
    rw [hpair, hLL]
  have hsrc : cornerModelInv Linv y.val ∈ cornerModelSource L Ω := by
    refine ⟨hne, ?_⟩
    rw [hLq]
    exact hy.2
  refine ⟨hsrc, (hW _ hsrc).mpr ?_⟩
  rw [hLq]
  simp only [Complex.re_add_im]
  exact cornerChartInvZ_mem y.2

theorem cornerModel_left {L Linv : ℝ × ℝ → ℝ × ℝ} (hLinvL : ∀ q, Linv (L q) = q)
    {Ω : Set (ℝ × ℝ)} (hΩ1 : ∀ q ∈ Ω, ‖((q.1 : ℂ) + q.2 * I)‖ < 1)
    {W : Set (EuclideanSpace ℝ (Fin 2) × ℝ)}
    (hW : ∀ p ∈ cornerModelSource L Ω, (p ∈ W ↔
      ((L (‖p.1‖, p.2)).1 : ℂ) + (L (‖p.1‖, p.2)).2 * I ∈ concaveQuadrant)) :
    ∀ p ∈ cornerModelSource L Ω, p ∈ W → cornerModelInv Linv (cornerModelVec L p) = p := by
  intro p hp hpW
  have hQ := (hW p hp).mp hpW
  obtain ⟨hZ, -, hN⟩ := cornerChartVec_facts hQ (hΩ1 _ hp.2) hp.1
  have hq : ((cornerChartInvZ (cornerModelVec L p)).re,
      (cornerChartInvZ (cornerModelVec L p)).im) = L (‖p.1‖, p.2) := by
    change ((cornerChartInvZ (cornerChartVec (L (‖p.1‖, p.2)).1 (L (‖p.1‖, p.2)).2
      (‖p.1‖⁻¹ • p.1))).re, (cornerChartInvZ (cornerChartVec (L (‖p.1‖, p.2)).1
      (L (‖p.1‖, p.2)).2 (‖p.1‖⁻¹ • p.1))).im) = _
    rw [hZ]
    simp
  have hu : ‖cornerChartPlane (cornerModelVec L p)‖⁻¹ • cornerChartPlane (cornerModelVec L p) =
      ‖p.1‖⁻¹ • p.1 := hN
  have hn : ‖p.1‖ ≠ 0 := norm_ne_zero_iff.mpr hp.1
  unfold cornerModelInv
  rw [hq, hu, hLinvL]
  refine Prod.ext ?_ rfl
  change ‖p.1‖ • ‖p.1‖⁻¹ • p.1 = p.1
  rw [smul_smul, mul_inv_cancel₀ hn, one_smul]

theorem cornerModel_right {L Linv : ℝ × ℝ → ℝ × ℝ} (hLL : ∀ q, L (Linv q) = q)
    {Ω : Set (ℝ × ℝ)} (hΩr : ∀ q ∈ Ω, 0 < (Linv q).1) :
    ∀ y ∈ cornerModelTarget Ω, cornerModelVec L (cornerModelInv Linv y.val) = y.val := by
  intro y hy
  obtain ⟨-, hpair, hdir⟩ := cornerModelInv_facts hΩr hy
  unfold cornerModelVec
  rw [hpair, hdir, hLL]
  exact cornerChartVec_inv y.2 hy.1

theorem continuousOn_cornerModelVec {L : ℝ × ℝ → ℝ × ℝ} (hL : Continuous L) {Ω : Set (ℝ × ℝ)}
    {W : Set (EuclideanSpace ℝ (Fin 2) × ℝ)}
    (hW : ∀ p ∈ cornerModelSource L Ω, (p ∈ W ↔
      ((L (‖p.1‖, p.2)).1 : ℂ) + (L (‖p.1‖, p.2)).2 * I ∈ concaveQuadrant)) :
    ContinuousOn (cornerModelVec L) (cornerModelSource L Ω ∩ W) := by
  have hLp : Continuous (fun p : EuclideanSpace ℝ (Fin 2) × ℝ => L (‖p.1‖, p.2)) :=
    hL.comp ((continuous_norm.comp continuous_fst).prodMk continuous_snd)
  have hdir : ContinuousOn (fun p : EuclideanSpace ℝ (Fin 2) × ℝ => ‖p.1‖⁻¹ • p.1)
      (cornerModelSource L Ω ∩ W) :=
    ((continuous_norm.comp continuous_fst).continuousOn.inv₀
      fun p hp => norm_ne_zero_iff.mpr hp.1.1).smul continuous_fst.continuousOn
  have hg : ContinuousOn (fun p : EuclideanSpace ℝ (Fin 2) × ℝ =>
      ((L (‖p.1‖, p.2)).1, (L (‖p.1‖, p.2)).2, ‖p.1‖⁻¹ • p.1)) (cornerModelSource L Ω ∩ W) :=
    (continuous_fst.comp hLp).continuousOn.prodMk
      ((continuous_snd.comp hLp).continuousOn.prodMk hdir)
  have hmaps : MapsTo (fun p : EuclideanSpace ℝ (Fin 2) × ℝ =>
      ((L (‖p.1‖, p.2)).1, (L (‖p.1‖, p.2)).2, ‖p.1‖⁻¹ • p.1)) (cornerModelSource L Ω ∩ W)
      {q : ℝ × ℝ × EuclideanSpace ℝ (Fin 2) | (q.1 : ℂ) + q.2.1 * I ∈ concaveQuadrant} :=
    fun p hp => (hW p hp.1).mp hp.2
  have hc := continuousOn_cornerChartVec.comp hg hmaps
  exact hc

theorem continuousOn_cornerModelInv {Linv : ℝ × ℝ → ℝ × ℝ} (hLinv : Continuous Linv)
    (Ω : Set (ℝ × ℝ)) :
    ContinuousOn (fun y : EuclideanHalfSpace 3 => cornerModelInv Linv y.val)
      (cornerModelTarget Ω) := by
  have hG : ContinuousOn (fun y : EuclideanHalfSpace 3 =>
      ((cornerChartInvZ y.val).re, (cornerChartInvZ y.val).im,
        ‖cornerChartPlane y.val‖⁻¹ • cornerChartPlane y.val)) (cornerModelTarget Ω) :=
    continuousOn_cornerChartInv.comp continuous_subtype_val.continuousOn
      fun y hy => ⟨y.2, hy.1⟩
  have hF : Continuous (fun t : ℝ × ℝ × EuclideanSpace ℝ (Fin 2) =>
      ((Linv (t.1, t.2.1)).1 • t.2.2, (Linv (t.1, t.2.1)).2)) := by
    have h1 : Continuous (fun t : ℝ × ℝ × EuclideanSpace ℝ (Fin 2) => Linv (t.1, t.2.1)) :=
      hLinv.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
    exact ((continuous_fst.comp h1).smul (continuous_snd.comp continuous_snd)).prodMk
      (continuous_snd.comp h1)
  exact hF.comp_continuousOn hG

theorem contMDiffAt_cornerModelInv {Linv : ℝ × ℝ → ℝ × ℝ} (hLinv : ContDiff ℝ ∞ Linv)
    {Ω : Set (ℝ × ℝ)} (hΩr : ∀ q ∈ Ω, 0 < (Linv q).1) :
    ∀ y ∈ cornerModelTarget Ω,
      (‖(cornerModelInv Linv y.val).1‖, (cornerModelInv Linv y.val).2) ≠ Linv 0 →
      ContMDiffAt (𝓡∂ 3) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) ∞
        (fun y : EuclideanHalfSpace 3 => cornerModelInv Linv y.val) y := by
  intro y hy hne
  obtain ⟨-, hpair, -⟩ := cornerModelInv_facts hΩr hy
  have hZ : cornerChartInvZ y.val ≠ 0 := by
    intro h0
    apply hne
    rw [hpair, h0]
    rfl
  have hG := contDiffAt_cornerChartInv y.2 hy.1 hZ
  have hF : ContDiff ℝ ∞ (fun t : ℝ × ℝ × EuclideanSpace ℝ (Fin 2) =>
      ((Linv (t.1, t.2.1)).1 • t.2.2, (Linv (t.1, t.2.1)).2)) := by
    have h1 : ContDiff ℝ ∞ (fun t : ℝ × ℝ × EuclideanSpace ℝ (Fin 2) => Linv (t.1, t.2.1)) :=
      hLinv.comp (contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd))
    exact ((contDiff_fst.comp h1).smul (contDiff_snd.comp contDiff_snd)).prodMk
      (contDiff_snd.comp h1)
  have h := hF.contDiffAt.comp y.val hG
  exact contMDiffAt_comp_val_of_contDiffWithinAt h.contDiffWithinAt

theorem contDiffAt_cornerModelVec {L Linv : ℝ × ℝ → ℝ × ℝ} (hL : ContDiff ℝ ∞ L)
    (hLinvL : ∀ q, Linv (L q) = q) {Ω : Set (ℝ × ℝ)} {W : Set (EuclideanSpace ℝ (Fin 2) × ℝ)}
    (hW : ∀ p ∈ cornerModelSource L Ω, (p ∈ W ↔
      ((L (‖p.1‖, p.2)).1 : ℂ) + (L (‖p.1‖, p.2)).2 * I ∈ concaveQuadrant)) :
    ∀ p ∈ cornerModelSource L Ω, p ∈ W → (‖p.1‖, p.2) ≠ Linv 0 →
      ContDiffAt ℝ ∞ (cornerModelVec L) p := by
  intro p hp hpW hne
  have hQ := (hW p hp).mp hpW
  have hq0 : ((L (‖p.1‖, p.2)).1 : ℂ) + (L (‖p.1‖, p.2)).2 * I ≠ 0 := by
    intro h0
    apply hne
    have h1 : (L (‖p.1‖, p.2)).1 = 0 := by simpa using congrArg Complex.re h0
    have h2 : (L (‖p.1‖, p.2)).2 = 0 := by simpa using congrArg Complex.im h0
    have h3 : L (‖p.1‖, p.2) = 0 := Prod.ext h1 h2
    rw [← h3, hLinvL]
  have hN : ContDiffAt ℝ ∞ (fun p : EuclideanSpace ℝ (Fin 2) × ℝ => ‖p.1‖) p :=
    (contDiffAt_norm ℝ hp.1).comp p contDiffAt_fst
  have hLp : ContDiffAt ℝ ∞ (fun p : EuclideanSpace ℝ (Fin 2) × ℝ => L (‖p.1‖, p.2)) p :=
    hL.contDiffAt.comp p (hN.prodMk contDiffAt_snd)
  have hdir : ContDiffAt ℝ ∞ (fun p : EuclideanSpace ℝ (Fin 2) × ℝ => ‖p.1‖⁻¹ • p.1) p :=
    (hN.inv (norm_ne_zero_iff.mpr hp.1)).smul contDiffAt_fst
  have hg : ContDiffAt ℝ ∞ (fun p : EuclideanSpace ℝ (Fin 2) × ℝ =>
      ((L (‖p.1‖, p.2)).1, (L (‖p.1‖, p.2)).2, ‖p.1‖⁻¹ • p.1)) p :=
    (contDiffAt_fst.comp p hLp).prodMk ((contDiffAt_snd.comp p hLp).prodMk hdir)
  have hc := (contDiffAt_cornerChartVec hQ hq0 (‖p.1‖⁻¹ • p.1)).comp p hg
  exact hc

end DifferentialGeometry.Topology.PiecewiseLinear
