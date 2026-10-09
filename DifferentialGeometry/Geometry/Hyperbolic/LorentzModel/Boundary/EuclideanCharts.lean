/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Analysis.Calculus.Quasiconformal.MetricDifferentiability
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Boundary.Distortion
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Cusps.Charts

noncomputable section

open Set Filter MeasureTheory
open DifferentialGeometry.ProjectiveOrthogonalGroup
open scoped Topology

namespace DifferentialGeometry.EuclideanBoundary

open Hyperbolic HyperbolicFaithful HyperbolicBoundary BoundaryTopology MobiusBoundary Horospherical
open BoundaryHomeomorph BoundaryVisual BoundaryDistortion

variable {m : ℕ}

def embed (x : Horizontal m) : BoundaryH (m + 1) := horo (fun i => x i)

def coords (v : BoundaryH (m + 1)) : Horizontal m :=
  (EuclideanSpace.equiv (Fin m) ℝ).symm
    (fun i => v.val (Sum.inl i.castSucc) / (1 - v.val (Sum.inl (Fin.last m))))

@[simp] theorem coords_embed (x : Horizontal m) : coords (embed x) = x := by
  ext i
  change (horo (fun j => x j)).val (Sum.inl i.castSucc) /
    (1 - (horo (fun j => x j)).val (Sum.inl (Fin.last m))) = x i
  rw [horo_val_castSucc, horo_val_last, normSq_horizontal]
  have h : ‖x‖ ^ 2 + 1 ≠ 0 := by positivity
  field_simp
  ring

theorem embed_injective : Function.Injective (embed : Horizontal m → BoundaryH (m + 1)) :=
  Function.LeftInverse.injective coords_embed

theorem embed_ne_infty (x : Horizontal m) : embed x ≠ ptInfty := horo_ne_ptInfty _

theorem embed_coords {v : BoundaryH (m + 1)} (hv : v ≠ ptInfty) : embed (coords v) = v := by
  obtain ⟨x, rfl⟩ := exists_horo_eq_of_ne_ptInfty v hv
  let y : Horizontal m := (EuclideanSpace.equiv (Fin m) ℝ).symm x
  change embed (coords (embed y)) = embed y
  rw [coords_embed]

theorem continuous_embed : Continuous (embed : Horizontal m → BoundaryH (m + 1)) := by
  apply isEmbedding_val.continuous_iff.mpr
  apply continuous_pi
  intro i
  rcases i with j | j
  · refine Fin.lastCases ?_ (fun k => ?_) j
    · change Continuous (fun x : Horizontal m => (horo (fun i => x i)).val (Sum.inl (Fin.last m)))
      simp only [horo_val_last, normSq_horizontal]
      exact ((continuous_norm.pow 2).sub continuous_const).div
        ((continuous_norm.pow 2).add continuous_const) (fun x => by positivity)
    · change Continuous (fun x : Horizontal m => (horo (fun i => x i)).val (Sum.inl k.castSucc))
      simp only [horo_val_castSucc, normSq_horizontal]
      exact (continuous_const.mul (EuclideanSpace.proj k).continuous).div
        ((continuous_norm.pow 2).add continuous_const) (fun x => by positivity)
  · have hj : j = 0 := Subsingleton.elim _ _
    subst j
    change Continuous (fun x : Horizontal m => (horo (fun i => x i)).val (Sum.inr 0))
    simp only [horo_val_time]
    exact continuous_const

theorem continuousAt_coords {v : BoundaryH (m + 1)} (hv : v ≠ ptInfty) :
    ContinuousAt coords v := by
  have hden : 1 - v.val (Sum.inl (Fin.last m)) ≠ 0 :=
    sub_ne_zero.mpr (fun h => hv (eq_ptInfty_of_axis_eq_one v h.symm))
  apply (EuclideanSpace.equiv (Fin m) ℝ).symm.continuous.continuousAt.comp
  apply continuousAt_pi.mpr
  intro i
  exact (((continuous_apply _).comp isEmbedding_val.continuous).continuousAt).div
    (continuousAt_const.sub (((continuous_apply _).comp isEmbedding_val.continuous).continuousAt))
    hden

theorem away_infty (φ : BoundaryH (m + 1) ≃ₜ BoundaryH (m + 1))
    (hfix : φ ptInfty = ptInfty) {v : BoundaryH (m + 1)} (hv : v ≠ ptInfty) :
    φ v ≠ ptInfty := fun h => hv (φ.injective (h.trans hfix.symm))

theorem symm_fix_infty (φ : BoundaryH (m + 1) ≃ₜ BoundaryH (m + 1))
    (hfix : φ ptInfty = ptInfty) : φ.symm ptInfty = ptInfty := by
  apply φ.injective
  rw [φ.apply_symm_apply, hfix]

def chart (φ : BoundaryH (m + 1) ≃ₜ BoundaryH (m + 1))
    (hfix : φ ptInfty = ptInfty) : Horizontal m ≃ₜ Horizontal m where
  toFun x := coords (φ (embed x))
  invFun x := coords (φ.symm (embed x))
  left_inv x := by
    change coords (φ.symm (embed (coords (φ (embed x))))) = x
    rw [embed_coords (away_infty φ hfix (embed_ne_infty x)),
      φ.symm_apply_apply, coords_embed]
  right_inv x := by
    change coords (φ (embed (coords (φ.symm (embed x))))) = x
    rw [embed_coords (away_infty φ.symm (symm_fix_infty φ hfix) (embed_ne_infty x)),
      φ.apply_symm_apply, coords_embed]
  continuous_toFun := continuous_iff_continuousAt.mpr fun x =>
    (continuousAt_coords (away_infty φ hfix (embed_ne_infty x))).comp
      (f := fun y : Horizontal m => φ (embed y)) (x := x)
      (φ.continuous.comp continuous_embed).continuousAt
  continuous_invFun := continuous_iff_continuousAt.mpr fun x =>
    (continuousAt_coords (away_infty φ.symm (symm_fix_infty φ hfix) (embed_ne_infty x))).comp
      (f := fun y : Horizontal m => φ.symm (embed y)) (x := x)
      (φ.symm.continuous.comp continuous_embed).continuousAt

theorem embed_chart (φ : BoundaryH (m + 1) ≃ₜ BoundaryH (m + 1))
    (hfix : φ ptInfty = ptInfty) (x : Horizontal m) :
    embed (chart φ hfix x) = φ (embed x) :=
  embed_coords (away_infty φ hfix (embed_ne_infty x))

@[simp] theorem chart_symm (φ : BoundaryH (m + 1) ≃ₜ BoundaryH (m + 1))
    (hfix : φ ptInfty = ptInfty) :
    chart φ.symm (symm_fix_infty φ hfix) = (chart φ hfix).symm := rfl

theorem bratio_embed (x y : Horizontal m) :
    bratioB (embed x) (embed y) =
      2 * dist x y ^ 2 / ((‖x‖ ^ 2 + 1) * (‖y‖ ^ 2 + 1)) := by
  change -lorB (boundaryRep (horoVec (fun i => x i)))
    (boundaryRep (horoVec (fun i => y i))) = _
  simp only [boundaryRep, lorB_smul_left, lorB_smul_right, lorB_horoVec_horoVec,
    tc_horoVec, normSq_horizontal]
  have hsub : normSq ((fun i => x i) - (fun i => y i)) = dist x y ^ 2 := by
    change normSq (fun i => (x - y) i) = dist x y ^ 2
    simpa only [dist_eq_norm] using normSq_horizontal (x - y)
  rw [hsub]
  field_simp

theorem bratio_embed_infty (x : Horizontal m) :
    bratioB (embed x) ptInfty = 2 / (‖x‖ ^ 2 + 1) := by
  change -lorB (boundaryRep (horoVec (fun i => x i))) ptInfty.val = _
  rw [boundaryRep, lorB_smul_left, lorB_ptInfty, vHeight_horoVec, tc_horoVec,
    normSq_horizontal]
  field_simp

theorem chordDist_embed_sq (x y : Horizontal m) :
    chordDist (embed x) (embed y) ^ 2 =
      4 * dist x y ^ 2 / ((‖x‖ ^ 2 + 1) * (‖y‖ ^ 2 + 1)) := by
  rw [chordDist_sq, bratio_embed]
  ring

theorem crossRatio_embed_infty (x y z : Horizontal m) (hxz : x ≠ z) :
    crossRatioSq (embed x) (embed y) (embed z) ptInfty =
      (dist x y / dist x z) ^ 2 := by
  rw [crossRatioSq, bratio_embed, bratio_embed, bratio_embed_infty, bratio_embed_infty,
    div_pow]
  have hd : dist x z ≠ 0 := (dist_pos.mpr hxz).ne'
  have hpos (u : Horizontal m) : ‖u‖ ^ 2 + 1 ≠ 0 := by positivity
  field_simp

variable {n : ℕ}

def actionHomeomorph (hn : 1 ≤ n) (g : PO n 1) : BoundaryH n ≃ₜ BoundaryH n :=
  Classical.choose (po_boundary_homeomorph hn g)

theorem actionHomeomorph_apply (hn : 1 ≤ n) (g : PO n 1) (v : BoundaryH n) :
    actionHomeomorph hn g v = (poBoundaryMulAction hn).smul g v :=
  Classical.choose_spec (po_boundary_homeomorph hn g) v

theorem actionHomeomorph_symm_apply (hn : 1 ≤ n) (g : PO n 1) (v : BoundaryH n) :
    (actionHomeomorph hn g).symm v = (poBoundaryMulAction hn).smul g⁻¹ v := by
  let := poBoundaryMulAction hn
  apply (actionHomeomorph hn g).injective
  rw [Homeomorph.apply_symm_apply, actionHomeomorph_apply]
  change v = g • (g⁻¹ • v)
  simp

theorem crossRatio_smul (hn : 1 ≤ n) (g : PO n 1) (a b c d : BoundaryH n)
    (hac : a ≠ c) (hbd : b ≠ d) :
    crossRatioSq ((poBoundaryMulAction hn).smul g a) ((poBoundaryMulAction hn).smul g b)
      ((poBoundaryMulAction hn).smul g c) ((poBoundaryMulAction hn).smul g d) =
        crossRatioSq a b c d := by
  let := poBoundaryMulAction hn
  have hac' : g • a ≠ g • c := fun h => hac (MulAction.injective g h)
  have hbd' : g • b ≠ g • d := fun h => hbd (MulAction.injective g h)
  change crossRatioSq (g • a) (g • b) (g • c) (g • d) = crossRatioSq a b c d
  rw [crossRatioSq_eq_ratio ((HyperbolicAction.poMulAction hn).smul g basepointH)
    _ _ _ _ hac' hbd']
  change ratio ((HyperbolicAction.poMulAction hn).smul g basepointH)
      ((poBoundaryMulAction hn).smul g a) ((poBoundaryMulAction hn).smul g b) *
    ratio ((HyperbolicAction.poMulAction hn).smul g basepointH)
      ((poBoundaryMulAction hn).smul g c) ((poBoundaryMulAction hn).smul g d) /
    (ratio ((HyperbolicAction.poMulAction hn).smul g basepointH)
      ((poBoundaryMulAction hn).smul g a) ((poBoundaryMulAction hn).smul g c) *
    ratio ((HyperbolicAction.poMulAction hn).smul g basepointH)
      ((poBoundaryMulAction hn).smul g b) ((poBoundaryMulAction hn).smul g d)) = _
  simp only [ratio_smul, ratio_basepoint]
  rfl

theorem crossRatioControl_postcompose (hn : 1 ≤ n)
    (φ : BoundaryH n ≃ₜ BoundaryH n) (hφ : HasCrossRatioControl φ) (g : PO n 1) :
    HasCrossRatioControl (φ.trans (actionHomeomorph hn g)) := by
  obtain ⟨D, α, β, hD, hα, hβ, hbound⟩ := hφ
  refine ⟨D, α, β, hD, hα, hβ, fun a b c d hab hac hbc hbd => ?_⟩
  simp only [Homeomorph.trans_apply, actionHomeomorph_apply]
  rw [crossRatio_smul hn g _ _ _ _ (fun h => hac (φ.injective h)) (fun h => hbd (φ.injective h))]
  exact hbound a b c d hab hac hbc hbd

theorem crossRatioControl_precompose (hn : 1 ≤ n)
    (φ : BoundaryH n ≃ₜ BoundaryH n) (hφ : HasCrossRatioControl φ) (g : PO n 1) :
    HasCrossRatioControl ((actionHomeomorph hn g).trans φ) := by
  let := poBoundaryMulAction hn
  obtain ⟨D, α, β, hD, hα, hβ, hbound⟩ := hφ
  refine ⟨D, α, β, hD, hα, hβ, fun a b c d hab hac hbc hbd => ?_⟩
  simp only [Homeomorph.trans_apply, actionHomeomorph_apply]
  have h := hbound (g • a) (g • b) (g • c) (g • d)
    (fun h => hab (MulAction.injective g h)) (fun h => hac (MulAction.injective g h))
    (fun h => hbc (MulAction.injective g h)) (fun h => hbd (MulAction.injective g h))
  have he : crossRatioSq (g • a) (g • b) (g • c) (g • d) = crossRatioSq a b c d :=
    crossRatio_smul hn g a b c d hac hbd
  rw [he] at h
  exact h

theorem chart_distortion_bound (φ : BoundaryH (m + 1) ≃ₜ BoundaryH (m + 1))
    (hfix : φ ptInfty = ptInfty) (hφ : HasCrossRatioControl φ) :
    ∃ H : ℝ, 0 < H ∧ ∀ x y z : Horizontal m, dist y x ≤ dist z x →
      dist (chart φ hfix y) (chart φ hfix x) ≤
        H * dist (chart φ hfix z) (chart φ hfix x) := by
  obtain ⟨D, α, β, hD, hα, hβ, hbound⟩ := hφ
  let L := max 1 (distortion D α β 1)
  have hL : 0 < L := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hH : 1 ≤ Real.sqrt L := by
    have hs := Real.sq_sqrt hL.le
    have hn := Real.sqrt_nonneg L
    have := le_max_left 1 (distortion D α β 1)
    change 1 ≤ L at this
    nlinarith
  refine ⟨Real.sqrt L, Real.sqrt_pos.mpr hL, fun x y z hyz => ?_⟩
  by_cases hyx : y = x
  · subst y
    simpa using mul_nonneg (Real.sqrt_nonneg L) (dist_nonneg (x := chart φ hfix z))
  by_cases hyzeq : y = z
  · subst z
    exact le_mul_of_one_le_left dist_nonneg hH
  have hxz : x ≠ z := by
    intro h
    rw [← h, dist_self] at hyz
    exact (not_le_of_gt (dist_pos.mpr hyx)) hyz
  have hxy : x ≠ y := Ne.symm hyx
  have ht : (dist x y / dist x z) ^ 2 ≤ 1 := by
    have hrat : dist x y / dist x z ≤ 1 :=
      (div_le_one (dist_pos.mpr hxz)).mpr (by simpa [dist_comm] using hyz)
    nlinarith [div_nonneg (dist_nonneg (x := x) (y := y)) (dist_nonneg (x := x) (y := z))]
  have hb := hbound (embed x) (embed y) (embed z) ptInfty
    (fun h => hxy (embed_injective h)) (fun h => hxz (embed_injective h))
    (fun h => hyzeq (embed_injective h)) (embed_ne_infty y)
  rw [hfix, ← embed_chart φ hfix x, ← embed_chart φ hfix y, ← embed_chart φ hfix z,
    crossRatio_embed_infty x y z hxz,
    crossRatio_embed_infty _ _ _ (fun h => hxz ((chart φ hfix).injective h))] at hb
  have hη := (strictMonoOn_distortion hD hα hβ).monotoneOn
    (sq_nonneg (dist x y / dist x z)) (by norm_num : (0 : ℝ) ≤ 1) ht
  have hh : (dist (chart φ hfix x) (chart φ hfix y) /
      dist (chart φ hfix x) (chart φ hfix z)) ^ 2 ≤ L :=
    hb.trans (hη.trans (le_max_right _ _))
  rw [div_pow, div_le_iff₀ (sq_pos_of_pos
    (dist_pos.mpr (fun h => hxz ((chart φ hfix).injective h))))] at hh
  have hs : dist (chart φ hfix y) (chart φ hfix x) ^ 2 ≤
      (Real.sqrt L * dist (chart φ hfix z) (chart φ hfix x)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hL.le]
    simpa only [dist_comm] using hh
  exact (sq_le_sq₀ dist_nonneg (mul_nonneg (Real.sqrt_nonneg _) dist_nonneg)).mp hs

theorem chart_hasLocalDistortion (φ : BoundaryH (m + 1) ≃ₜ BoundaryH (m + 1))
    (hfix : φ ptInfty = ptInfty) (hφ : HasCrossRatioControl φ) :
    MetricDifferentiability.HasLocalDistortion (chart φ hfix) := by
  obtain ⟨H, hH, hb⟩ := chart_distortion_bound φ hfix hφ
  exact ⟨H, hH, fun x => ⟨1, zero_lt_one, fun y z _ _ hyz => hb x y z hyz⟩⟩

theorem exists_normalized_chart_with_globalDistortion
    (φ : BoundaryH (m + 1) ≃ₜ BoundaryH (m + 1))
    (hφ : HasCrossRatioControl φ) (hφi : HasCrossRatioControl φ.symm) :
    ∃ (a : PO (m + 1) 1) (F : Horizontal m ≃ₜ Horizontal m),
      (poBoundaryMulAction (by omega : 1 ≤ m + 1)).smul a (φ ptInfty) = ptInfty ∧
      (∀ x, embed (F x) = (poBoundaryMulAction (by omega : 1 ≤ m + 1)).smul a (φ (embed x))) ∧
      MetricDifferentiability.HasGlobalDistortion F ∧
      MetricDifferentiability.HasGlobalDistortion F.symm := by
  have hn : 1 ≤ m + 1 := by omega
  obtain ⟨a, ha⟩ := CuspCharts.exists_normalizing_element (φ ptInfty)
  let ψ := φ.trans (actionHomeomorph hn a)
  have hfix : ψ ptInfty = ptInfty := by
    simpa only [ψ, Homeomorph.trans_apply, actionHomeomorph_apply] using ha
  have hψ := crossRatioControl_postcompose hn φ hφ a
  have hψi : HasCrossRatioControl ψ.symm := by
    have he : ψ.symm = (actionHomeomorph hn a⁻¹).trans φ.symm := by
      apply Homeomorph.ext
      intro v
      change φ.symm ((actionHomeomorph hn a).symm v) =
        φ.symm (actionHomeomorph hn a⁻¹ v)
      rw [actionHomeomorph_symm_apply, actionHomeomorph_apply]
    rw [he]
    exact crossRatioControl_precompose hn φ.symm hφi a⁻¹
  refine ⟨a, chart ψ hfix, ha, ?_, chart_distortion_bound ψ hfix hψ, ?_⟩
  · intro x
    rw [embed_chart]
    exact actionHomeomorph_apply hn a (φ (embed x))
  · rw [← chart_symm]
    exact chart_distortion_bound ψ.symm (symm_fix_infty ψ hfix) hψi

theorem exists_normalized_chart
    (φ : BoundaryH (m + 1) ≃ₜ BoundaryH (m + 1))
    (hφ : HasCrossRatioControl φ) (hφi : HasCrossRatioControl φ.symm) :
    ∃ (a : PO (m + 1) 1) (F : Horizontal m ≃ₜ Horizontal m),
      (poBoundaryMulAction (by omega : 1 ≤ m + 1)).smul a (φ ptInfty) = ptInfty ∧
      (∀ x, embed (F x) = (poBoundaryMulAction (by omega : 1 ≤ m + 1)).smul a (φ (embed x))) ∧
      MetricDifferentiability.HasLocalDistortion F ∧
      MetricDifferentiability.HasLocalDistortion F.symm := by
  obtain ⟨a, F, ha, hF, hf, hfi⟩ :=
    exists_normalized_chart_with_globalDistortion φ hφ hφi
  exact ⟨a, F, ha, hF, hf.local, hfi.local⟩

end DifferentialGeometry.EuclideanBoundary
