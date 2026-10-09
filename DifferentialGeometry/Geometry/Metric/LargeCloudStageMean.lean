import DifferentialGeometry.Geometry.Metric.LargeCloudAffineMarkerLocality
import DifferentialGeometry.Geometry.Metric.CloudNormalizedBallCutoffs

/-!
# The weighted mean of a functional on the spectral zero set (EDP01's (SM) and (SW))

Blueprint `master207B.tex`, EDP01 (B:6684–6716) on the spectral section of CFS12/CFS13
(`η(y) = Q(y)(y − Σ_i w_i(y) x_i)`, `Q` the spectral projector of `Σ_i w_i P_i^⊥` near one):

* `functional_eq_weightedMean_of_section_eq_zero_GAFS2`, (SM): if every plane with nonzero weight
  lies in `ker ℓ`, then at a zero of the section `ℓ(y) = Σ_i w_i(y) ℓ(x_i)` ("CFS12's spectral
  projector has the same property, so on its zero set `w_ρ = μ_ρ(w)`").
* `exists_selection_weight_deriv_bound_GAFS2`: CFS12's weight bound `Σ_i ‖Dw_i‖ ≤ c_w / r_x` on the
  reference ball `B(x, 8br_x)` for ANY selection `I ⊆ S` with disjoint balls `B(x_i, r_i)` and the
  tube inclusion (the selection made inside CFS15), with `c_w` depending only on `k, b, B`
  (CFS11's count `large_cloud_selected_center_geometry` + the active-count bound).
* `stage_mean_functional_GAFS2`, (SM) + (SW) for a map into the zero set: for a map `a` sending
  `B(x, r_x)` into the zero set inside `B(x, 8br_x)` with `‖Da‖ ≤ 2`, every functional `ℓ` whose
  contributing planes lie in `ker ℓ` and every `R, β` with `|ℓ(x_i) − R| ≤ β` on the contributing
  centres: `|ℓ(a z) − R| ≤ β` and `‖ℓ ∘ Da(z)‖ ≤ 2c_wβ / r_x` (subtract the SAME constant `R`;
  `Σ_i Dw_i = 0`).
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter DifferentialGeometry.Analysis
open scoped BigOperators NNReal ContDiff Topology

namespace GC.MetricGeometry

universe u

section Mean

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

/-- **(SM)**: if every plane with nonzero weight lies in `ker ℓ`, then at a zero of the spectral
section `Q(z − Σ_i w_i y_i)` (with `Q` the spectral projector of `Σ_i w_i L_i^⊥` near one)
`ℓ(z) = Σ_i w_i ℓ(y_i)`. -/
theorem functional_eq_weightedMean_of_section_eq_zero_GAFS2 {ι : Type*} (S : Finset ι)
    (w : ι → ℝ) (hw : ∑ i ∈ S, w i = 1) (L : ι → Submodule ℝ H) (y : ι → H) (ℓ : H →L[ℝ] ℝ)
    (hplane : ∀ i ∈ S, w i ≠ 0 → L i ≤ LinearMap.ker (ℓ : H →ₗ[ℝ] ℝ)) (z : H)
    (hzero : (⨆ μ ∈ ball (1 : ℝ) (1 / 2), Module.End.eigenspace
        (∑ i ∈ S, w i • (L i)ᗮ.starProjection).toLinearMap μ).starProjection
        (z - ∑ i ∈ S, w i • y i) = 0) :
    ℓ z = ∑ i ∈ S, w i * ℓ (y i) := by
  set V : Submodule ℝ H := (LinearMap.ker (ℓ : H →ₗ[ℝ] ℝ))ᗮ with hV
  have hfix : ∀ v ∈ V, (∑ i ∈ S, w i • (L i)ᗮ.starProjection : H →L[ℝ] H) v = v :=
    fun v hv => Submodule.sum_smul_starProjection_orthogonal_apply_of_mem_orthogonal
      (LinearMap.ker (ℓ : H →ₗ[ℝ] ℝ)) S L w hw hplane hv
  have hQ := Submodule.starProjection_eigenspace_iSup_of_fixed V
    (∑ i ∈ S, w i • (L i)ᗮ.starProjection) (ball (1 : ℝ) (1 / 2))
    (mem_ball_self (by norm_num)) hfix
  set u : H := z - ∑ i ∈ S, w i • y i with hu
  have hVu : V.starProjection u = 0 := by
    have h := congrArg (fun A : H →L[ℝ] H => A u) hQ
    simp only [ContinuousLinearMap.comp_apply] at h
    rw [← h, hzero, map_zero]
  have hperp : u ∈ LinearMap.ker (ℓ : H →ₗ[ℝ] ℝ) := by
    have h := V.sub_starProjection_mem_orthogonal u
    rw [hVu, sub_zero] at h
    rwa [hV, Submodule.orthogonal_orthogonal] at h
  have hℓu : ℓ u = 0 := LinearMap.mem_ker.mp hperp
  rw [hu, map_sub, map_sum] at hℓu
  simp only [map_smul, smul_eq_mul] at hℓu
  linarith

end Mean

section Weights

/-- **CFS12's weight bound for a given selection.** A constant `c_w ≥ 0` depending only on
`k, b, B` such that for every cloud `S ⊆ T` with `k`-planes, (MCb) at the buffer `128b`, the (CS)
tests at quality `δ` with `δ((80B + 31)b + 2) < 1`, and EVERY finite selection `I ⊆ S` with disjoint
balls `B(x_i, r_i)` and the tube inclusion `⋃ B(x, 8br_x) ⊆ ⋃ B(x_i, 20br_i)`, the normalized
cutoff weights at `40br_i` satisfy `Σ_i ‖Dw_i‖ ≤ c_w / r_x` on every reference ball
`B(x, 8br_x)`. -/
theorem exists_selection_weight_deriv_bound_GAFS2 (k : ℕ) (bb B : ℝ) (hbb : 1 ≤ bb)
    (hB : 1 ≤ B) :
    ∃ cw : ℝ, 0 ≤ cw ∧
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
        (S T : Set H), S ⊆ T → ∀ (r : H → ℝ) (P : H → Submodule ℝ H),
        (∀ x ∈ S, Module.finrank ℝ (P x) = k) → (∀ x ∈ S, 0 < r x) →
        ∀ δ : ℝ, 0 < δ → δ * ((80 * B + 31) * bb + 2) < 1 →
        (∀ x ∈ S, ∀ y ∈ S, dist y x ≤ 128 * bb * max (r y) (r x) →
          r x / B ≤ r y ∧ r y ≤ B * r x) →
        (∀ x ∈ S, hausdorffEDist (T ∩ ball x (r x / δ))
          ((AffineSubspace.mk' x (P x) : Set H) ∩ ball x (r x / δ)) ≤ ENNReal.ofReal (δ * r x)) →
        ∀ (I : Set H) (hI : I.Finite), I ⊆ S → I.PairwiseDisjoint (fun i => ball i (r i)) →
        ((⋃ x ∈ S, ball x (8 * bb * r x)) ⊆ ⋃ i ∈ I, ball i (20 * bb * r i)) →
        ∀ x ∈ S, ∀ y ∈ ball x (8 * bb * r x),
          (∑ i ∈ hI.toFinset, ‖fderiv ℝ (fun y' => ballCutoff i (40 * bb * r i)
              (2 * (40 * bb * r i)) y' / (∑ a ∈ hI.toFinset,
                ballCutoff a (40 * bb * r a) (2 * (40 * bb * r a)) y')) y‖) ≤ cw / r x := by
  classical
  have hbpos : 0 < bb := zero_lt_one.trans_le hbb
  have hBpos : 0 < B := zero_lt_one.trans_le hB
  let N : ℕ := ⌈(1 + 2 * B * (80 * B + 31) * bb) ^ k⌉₊
  let Λ' : ℝ≥0 := ⟨B / (40 * bb), by positivity⟩
  obtain ⟨C, hC, hbound⟩ :=
    exists_bound_iteratedFDeriv_normalized_ballCutoffs_of_active_card_le.{u, u} 1 N Λ'
  refine ⟨C, hC, ?_⟩
  intro H _ _ _ S T hST r P hdim hr δ hδ hδsmall hscale hcloud I hI hIS hdisj htube x hx y hy
  have hgeo := large_cloud_selected_center_geometry S T hST r (fun x : S => P x) k
    (fun x => hdim x x.2) I hIS hI hdisj hr bb B δ hbb hB hδ hδsmall hscale
    (fun x => hcloud x x.2) ⟨x, hx⟩
  have htwice (i : H) : 2 * (40 * bb * r i) = 80 * bb * r i := by ring
  let U : Set H := ball x (8 * bb * r x)
  have hUsub : U ⊆ ball x (30 * bb * r x) := by
    have hrx := hr x hx
    exact ball_subset_ball (by nlinarith)
  let J : Set H := I ∩ {i | (closedBall i (80 * bb * r i) ∩ ball x (30 * bb * r x)).Nonempty}
  have hcard : J.ncard ≤ N := by
    have hh := hgeo.1
    have hc : (1 + 2 * B * (80 * B + 31) * bb) ^ k ≤ (N : ℝ) := Nat.le_ceil _
    exact_mod_cast hh.trans hc
  have hsubset : ((hI.toFinset : Set H) ∩
      {i | (closedBall i (2 * (40 * bb * r i)) ∩ U).Nonempty}) ⊆ J := by
    intro i hi
    obtain ⟨z, hz, hzU⟩ := hi.2
    refine ⟨hI.mem_toFinset.mp hi.1, z, ?_, hUsub hzU⟩
    simpa only [htwice] using hz
  have hactive : ((hI.toFinset : Set H) ∩
      {i | (closedBall i (2 * (40 * bb * r i)) ∩ U).Nonempty}).ncard ≤ N :=
    (Set.ncard_le_ncard hsubset (hI.subset (fun _ hi => hi.1))).trans hcard
  have hsc (i : H) (hi : i ∈ hI.toFinset)
      (hmeet : (closedBall i (2 * (40 * bb * r i)) ∩ U).Nonempty) :
      r x ≤ (Λ' : ℝ) * (40 * bb * r i) := by
    have hj : i ∈ J := hsubset ⟨hi, hmeet⟩
    have hlo := (hgeo.2 i hj).1
    have hh := (div_le_iff₀ hBpos).mp hlo
    have heq : (Λ' : ℝ) * (40 * bb * r i) = B * r i := by
      change B / (40 * bb) * (40 * bb * r i) = B * r i
      field_simp [hbpos.ne']
    rw [heq]
    nlinarith
  have hplateau : ∀ z ∈ U, ∃ i ∈ hI.toFinset, dist z i ≤ 40 * bb * r i := by
    intro z hz
    obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp (htube (mem_iUnion₂.mpr ⟨x, hx, hz⟩))
    refine ⟨i, hI.mem_toFinset.mpr hi, ?_⟩
    have hri := hr i (hIS hi)
    have h1 : dist z i < 20 * bb * r i := hzi
    have h2 : 20 * bb * r i ≤ 40 * bb * r i := by nlinarith
    linarith
  have h := hbound H H hI.toFinset (fun i => i) (fun i => 40 * bb * r i) U isOpen_ball hactive
    (fun i hi => by have hri := hr i (hIS (hI.mem_toFinset.mp hi)); positivity)
    (r x) (hr x hx) hsc hplateau 1 le_rfl y hy
  simpa only [norm_iteratedFDeriv_one, pow_one] using h

end Weights

section StageMean

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

/-- **(SM) + (SW) for a map into the spectral zero set.** Weights `w_i ≥ 0` supported in
`B(x_i, 80br_i)`, summing to one and differentiable on `B(x, 8br_x)` with `Σ_i ‖Dw_i‖ ≤ c_w / r_x`
there; a map `a` sending `B(x, r_x)` into the zero set of the spectral section inside
`B(x, 8br_x)`, differentiable at `z` with `‖Da(z)‖ ≤ 2`. For every functional `ℓ` whose contributing
planes lie in `ker ℓ` and every `R, β` with `|ℓ(x_i) − R| ≤ β` on the contributing centres:
`|ℓ(a z) − R| ≤ β` and `‖ℓ ∘ Da(z)‖ ≤ 2c_wβ / r_x`. -/
theorem stage_mean_functional_GAFS2 (S : Set H) (r : H → ℝ) (P : H → Submodule ℝ H)
    (I : Finset H) (hIS : (I : Set H) ⊆ S) (w : H → H → ℝ) {bb cw : ℝ} {x : H} (hx : 0 < r x)
    (hnn : ∀ i y, 0 ≤ w i y) (hsupp : ∀ i ∈ I, ∀ y, w i y ≠ 0 → y ∈ ball i (80 * bb * r i))
    (hsum : ∀ y ∈ ball x (8 * bb * r x), ∑ i ∈ I, w i y = 1)
    (hdiff : ∀ i ∈ I, ∀ y ∈ ball x (8 * bb * r x), DifferentiableAt ℝ (w i) y)
    (hder : ∀ y ∈ ball x (8 * bb * r x), ∑ i ∈ I, ‖fderiv ℝ (w i) y‖ ≤ cw / r x)
    (a : H → H)
    (hmap : ∀ z ∈ ball x (r x), a z ∈ ball x (8 * bb * r x) ∧
      (⨆ μ ∈ ball (1 : ℝ) (1 / 2), Module.End.eigenspace
        (∑ i ∈ I, w i (a z) • (P i)ᗮ.starProjection).toLinearMap μ).starProjection
        (a z - ∑ i ∈ I, w i (a z) • i) = 0)
    {z : H} (hz : z ∈ ball x (r x)) (hda : DifferentiableAt ℝ a z) (hDa : ‖fderiv ℝ a z‖ ≤ 2)
    (ℓ : H →L[ℝ] ℝ)
    (hplane : ∀ i ∈ S, (closedBall i (80 * bb * r i) ∩ ball x (8 * bb * r x)).Nonempty →
      P i ≤ LinearMap.ker (ℓ : H →ₗ[ℝ] ℝ))
    (R β : ℝ)
    (hβ : ∀ i ∈ S, (closedBall i (80 * bb * r i) ∩ ball x (8 * bb * r x)).Nonempty →
      |ℓ i - R| ≤ β) :
    |ℓ (a z) - R| ≤ β ∧ ‖ℓ.comp (fderiv ℝ a z)‖ ≤ 2 * cw * β / r x := by
  classical
  set V8 : Set H := ball x (8 * bb * r x) with hV8
  -- contributing centres
  have hcontrib : ∀ i ∈ I, ∀ y ∈ V8, w i y ≠ 0 →
      (closedBall i (80 * bb * r i) ∩ ball x (8 * bb * r x)).Nonempty :=
    fun i hi y hy hne => ⟨y, ball_subset_closedBall (hsupp i hi y hne), hy⟩
  -- (SM) along `a`
  have hSM : ∀ z' ∈ ball x (r x), ℓ (a z') = ∑ i ∈ I, w i (a z') * ℓ i := by
    intro z' hz'
    obtain ⟨hV, hη⟩ := hmap z' hz'
    exact functional_eq_weightedMean_of_section_eq_zero_GAFS2 I (fun i => w i (a z'))
      (hsum _ hV) P (fun i => i) ℓ
      (fun i hi hne => hplane i (hIS hi) (hcontrib i hi _ hV hne)) (a z') hη
  obtain ⟨hazV, -⟩ := hmap z hz
  -- `β ≥ 0`: some centre is active at `a z`
  have hβ0 : 0 ≤ β := by
    by_contra hneg
    have hzero : ∀ i ∈ I, w i (a z) = 0 := by
      intro i hi
      by_contra hne
      have h := hβ i (hIS hi) (hcontrib i hi _ hazV hne)
      exact hneg ((abs_nonneg _).trans h)
    have h1 := hsum _ hazV
    rw [Finset.sum_eq_zero hzero] at h1
    exact zero_ne_one h1
  -- value
  have hval : |ℓ (a z) - R| ≤ β := by
    have heq : ℓ (a z) - R = ∑ i ∈ I, w i (a z) * (ℓ i - R) := by
      have h1 := hsum _ hazV
      rw [hSM z hz]
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, h1, one_mul]
    rw [heq]
    calc |∑ i ∈ I, w i (a z) * (ℓ i - R)| ≤ ∑ i ∈ I, |w i (a z) * (ℓ i - R)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ I, w i (a z) * β := by
          apply Finset.sum_le_sum
          intro i hi
          rw [abs_mul, abs_of_nonneg (hnn i (a z))]
          by_cases hne : w i (a z) = 0
          · rw [hne, zero_mul, zero_mul]
          · exact mul_le_mul_of_nonneg_left (hβ i (hIS hi) (hcontrib i hi _ hazV hne))
              (hnn i (a z))
      _ = β := by rw [← Finset.sum_mul, hsum _ hazV, one_mul]
  refine ⟨hval, ?_⟩
  -- derivative
  have hV8open : IsOpen V8 := isOpen_ball
  set μf : H → ℝ := fun y => ∑ i ∈ I, w i y * ℓ i with hμf
  have hμd : HasFDerivAt μf (∑ i ∈ I, ℓ i • fderiv ℝ (w i) (a z)) (a z) := by
    have h := HasFDerivAt.fun_sum (u := I) (A := fun i y => w i y * ℓ i)
      (A' := fun i => ℓ i • fderiv ℝ (w i) (a z)) (x := a z) (fun i hi => by
        have hd := (hdiff i hi _ hazV).hasFDerivAt
        simpa only [smul_eq_mul, mul_comm] using hd.mul_const (ℓ i))
    exact h
  have hsum0 : ∑ i ∈ I, fderiv ℝ (w i) (a z) = 0 := by
    have hconst : (fun y => ∑ i ∈ I, w i y) =ᶠ[𝓝 (a z)] fun _ => (1 : ℝ) :=
      Filter.eventually_of_mem (hV8open.mem_nhds hazV) (fun y hy => hsum y hy)
    have h1 : HasFDerivAt (fun y => ∑ i ∈ I, w i y) (∑ i ∈ I, fderiv ℝ (w i) (a z)) (a z) :=
      HasFDerivAt.fun_sum (fun i hi => (hdiff i hi _ hazV).hasFDerivAt)
    have h2 : HasFDerivAt (fun y => ∑ i ∈ I, w i y) (0 : H →L[ℝ] ℝ) (a z) :=
      (hasFDerivAt_const (1 : ℝ) (a z)).congr_of_eventuallyEq hconst
    exact h1.unique h2
  have hloc0 : ∀ i ∈ I, ¬ (closedBall i (80 * bb * r i) ∩ ball x (8 * bb * r x)).Nonempty →
      fderiv ℝ (w i) (a z) = 0 := by
    intro i hi hnot
    have hev : w i =ᶠ[𝓝 (a z)] fun _ => (0 : ℝ) := by
      refine Filter.eventually_of_mem (hV8open.mem_nhds hazV) (fun y hy => ?_)
      by_contra hne
      exact hnot (hcontrib i hi y hy hne)
    rw [hev.fderiv_eq]
    exact fderiv_const_apply _
  have hμ' : ∑ i ∈ I, ℓ i • fderiv ℝ (w i) (a z) =
      ∑ i ∈ I, (ℓ i - R) • fderiv ℝ (w i) (a z) := by
    simp only [sub_smul, Finset.sum_sub_distrib, ← Finset.smul_sum, hsum0, smul_zero, sub_zero]
  have hcw : 0 ≤ cw := by
    have h := (Finset.sum_nonneg (fun i _ => norm_nonneg (fderiv ℝ (w i) (a z)))).trans
      (hder _ hazV)
    by_contra hneg
    exact absurd h (not_le.mpr (div_neg_of_neg_of_pos (not_le.mp hneg) hx))
  have hμn : ‖∑ i ∈ I, ℓ i • fderiv ℝ (w i) (a z)‖ ≤ β * (cw / r x) := by
    rw [hμ']
    calc ‖∑ i ∈ I, (ℓ i - R) • fderiv ℝ (w i) (a z)‖
        ≤ ∑ i ∈ I, ‖(ℓ i - R) • fderiv ℝ (w i) (a z)‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ I, β * ‖fderiv ℝ (w i) (a z)‖ := by
          apply Finset.sum_le_sum
          intro i hi
          rw [norm_smul, Real.norm_eq_abs]
          by_cases hc : (closedBall i (80 * bb * r i) ∩ ball x (8 * bb * r x)).Nonempty
          · exact mul_le_mul_of_nonneg_right (hβ i (hIS hi) hc) (norm_nonneg _)
          · rw [hloc0 i hi hc, norm_zero, mul_zero, mul_zero]
      _ = β * ∑ i ∈ I, ‖fderiv ℝ (w i) (a z)‖ := by rw [Finset.mul_sum]
      _ ≤ β * (cw / r x) := mul_le_mul_of_nonneg_left (hder _ hazV) hβ0
  -- `ℓ ∘ a = μ ∘ a` near `z`
  have hfeq : (fun z' => ℓ (a z')) =ᶠ[𝓝 z] fun z' => μf (a z') :=
    Filter.eventually_of_mem (isOpen_ball.mem_nhds hz) (fun z' hz' => hSM z' hz')
  have hℓa : HasFDerivAt (fun z' => ℓ (a z')) (ℓ.comp (fderiv ℝ a z)) z :=
    ℓ.hasFDerivAt.comp z hda.hasFDerivAt
  have hμa : HasFDerivAt (fun z' => μf (a z'))
      ((∑ i ∈ I, ℓ i • fderiv ℝ (w i) (a z)).comp (fderiv ℝ a z)) z :=
    hμd.comp z hda.hasFDerivAt
  have hD : ℓ.comp (fderiv ℝ a z) = (∑ i ∈ I, ℓ i • fderiv ℝ (w i) (a z)).comp (fderiv ℝ a z) :=
    hℓa.unique (hμa.congr_of_eventuallyEq hfeq)
  rw [hD]
  calc ‖(∑ i ∈ I, ℓ i • fderiv ℝ (w i) (a z)).comp (fderiv ℝ a z)‖
      ≤ ‖∑ i ∈ I, ℓ i • fderiv ℝ (w i) (a z)‖ * ‖fderiv ℝ a z‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ β * (cw / r x) * 2 :=
        mul_le_mul hμn hDa (norm_nonneg _) (mul_nonneg hβ0 (div_nonneg hcw hx.le))
    _ = 2 * cw * β / r x := by ring

/-- **The nearest map of CFS15 with GAF03's locality and EDP01's (SM)/(SW).** For a finite selection
`I ⊆ S` with the tube inclusion, CFS12's weights `w` at `40ε⁻¹r_i` with `Σ_i ‖Dw_i‖ ≤ c_w / r_x` on
the reference balls, and a map `a` with CFS14 (3)'s value and derivative bounds on every `B(x, r_x)`
taking values in the zero set of the spectral section: on every `B(x, r_x)`, `a` keeps every affine
block value shared by the contributing centres and their planes (GAF03), and for every functional
`ℓ` whose contributing planes lie in `ker ℓ` and every `R₀, β` with `|ℓ(x_i) − R₀| ≤ β` on the
contributing centres, `|ℓ(a z) − R₀| ≤ β` and `‖ℓ ∘ Da(z)‖ ≤ 2c_wβ / r_x`. -/
theorem nearest_mean_of_zero_set_GAFS2 (S : Set H) (r : H → ℝ) (P : H → Submodule ℝ H)
    (I : Set H) (hI : I.Finite) (hIS : I ⊆ S) (hr : ∀ x ∈ S, 0 < r x) {ε cw : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1)
    (htube : (⋃ x ∈ S, ball x (8 * ε⁻¹ * r x)) ⊆ ⋃ i ∈ I, ball i (20 * ε⁻¹ * r i))
    (w : H → H → ℝ)
    (hw : w = fun i y => ballCutoff i (40 * ε⁻¹ * r i) (2 * (40 * ε⁻¹ * r i)) y /
      (∑ a ∈ hI.toFinset, ballCutoff a (40 * ε⁻¹ * r a) (2 * (40 * ε⁻¹ * r a)) y))
    (hwb : ∀ x ∈ S, ∀ y ∈ ball x (8 * ε⁻¹ * r x),
      ∑ i ∈ hI.toFinset, ‖fderiv ℝ (w i) y‖ ≤ cw / r x)
    (a : H → H)
    (hval : ∀ x ∈ S, ∀ z ∈ ball x (r x), ‖a z - (x + (P x).starProjection (z - x))‖ ≤ ε * r x ∧
      DifferentiableAt ℝ a z ∧ ‖fderiv ℝ a z - (P x).starProjection‖ ≤ ε)
    (hZ : ∀ x ∈ S, ∀ z ∈ ball x (r x),
      (⨆ μ ∈ ball (1 : ℝ) (1 / 2), Module.End.eigenspace
        (∑ i ∈ hI.toFinset, w i (a z) • (P i)ᗮ.starProjection).toLinearMap μ).starProjection
        (a z - ∑ i ∈ hI.toFinset, w i (a z) • i) = 0) :
    ∀ x ∈ S, ∀ z ∈ ball x (r x),
      (∀ (Kk : Submodule ℝ H) (c : H),
        (∀ i ∈ S, (closedBall i (80 * ε⁻¹ * r i) ∩ ball x (8 * ε⁻¹ * r x)).Nonempty →
          Kk.starProjection i = c ∧ P i ≤ Kkᗮ) →
        Kk.starProjection (a z) = c) ∧
      ∀ ℓ : H →L[ℝ] ℝ,
        (∀ i ∈ S, (closedBall i (80 * ε⁻¹ * r i) ∩ ball x (8 * ε⁻¹ * r x)).Nonempty →
          P i ≤ LinearMap.ker (ℓ : H →ₗ[ℝ] ℝ)) →
        ∀ R₀ β : ℝ,
        (∀ i ∈ S, (closedBall i (80 * ε⁻¹ * r i) ∩ ball x (8 * ε⁻¹ * r x)).Nonempty →
          |ℓ i - R₀| ≤ β) →
        |ℓ (a z) - R₀| ≤ β ∧ ‖ℓ.comp (fderiv ℝ a z)‖ ≤ 2 * cw * β / r x := by
  classical
  intro x hx z hz
  have hrx := hr x hx
  have hinv : 1 ≤ ε⁻¹ := one_le_inv₀ hε |>.mpr hε1
  have hri : ∀ i ∈ hI.toFinset, 0 < 40 * ε⁻¹ * r i := fun i hi => by
    have := hr i (hIS (hI.mem_toFinset.mp hi))
    positivity
  -- `a` maps `B(x, r_x)` into the reference ball
  have hmapV : ∀ z' ∈ ball x (r x), a z' ∈ ball x (8 * ε⁻¹ * r x) := by
    intro z' hz'
    have hzx : ‖z' - x‖ < r x := by rw [← dist_eq_norm]; exact hz'
    have hproj : ‖(P x).starProjection (z' - x)‖ ≤ ‖z' - x‖ :=
      Submodule.norm_starProjection_apply_le (P x) (z' - x)
    have htri : ‖a z' - x‖ ≤ ‖a z' - (x + (P x).starProjection (z' - x))‖ +
        ‖(P x).starProjection (z' - x)‖ := by
      have := norm_add_le (a z' - (x + (P x).starProjection (z' - x)))
        ((P x).starProjection (z' - x))
      rwa [show a z' - (x + (P x).starProjection (z' - x)) + (P x).starProjection (z' - x) =
        a z' - x by abel] at this
    have hv := (hval x hx z' hz').1
    rw [mem_ball, dist_eq_norm]
    have h8 : 2 * r x ≤ 8 * ε⁻¹ * r x := by nlinarith
    nlinarith
  -- the cover of the reference ball by plateaus
  have hcover : ∀ y ∈ ball x (8 * ε⁻¹ * r x), ∃ i ∈ hI.toFinset, dist y i ≤ 40 * ε⁻¹ * r i := by
    intro y hy
    obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.mp (htube (mem_iUnion₂.mpr ⟨x, hx, hy⟩))
    refine ⟨i, hI.mem_toFinset.mpr hi, ?_⟩
    have h1 : dist y i < 20 * ε⁻¹ * r i := hyi
    have h2 := hri i (hI.mem_toFinset.mpr hi)
    linarith
  have htubex : ball x (8 * ε⁻¹ * r x) ⊆ ⋃ i ∈ I, ball i (20 * ε⁻¹ * r i) :=
    fun y hy => htube (mem_iUnion₂.mpr ⟨x, hx, hy⟩)
  refine ⟨fun Kk c hcontrib => ?_, fun ℓ hplane R₀ β hβ => ?_⟩
  · -- GAF03
    have hloc := large_cloud_affine_marker_locality I hI r P hε hε1
      (fun i hi => hr i (hIS hi)) x htubex Kk c (fun i hi hne => hcontrib i (hIS hi) hne)
    subst hw
    exact hloc.2.2 z hz _ (hZ x hx z hz) (hval x hx z hz).1
  · -- EDP01 (SM) + (SW)
    have hda := (hval x hx z hz).2.1
    have hDa : ‖fderiv ℝ a z‖ ≤ 2 := by
      have h1 := norm_add_le (fderiv ℝ a z - (P x).starProjection) (P x).starProjection
      rw [sub_add_cancel] at h1
      have h2 := (hval x hx z hz).2.2
      have h3 := (P x).starProjection_norm_le
      linarith
    have hIS' : ((hI.toFinset : Finset H) : Set H) ⊆ S := by
      intro i hi
      exact hIS (hI.mem_toFinset.mp hi)
    refine stage_mean_functional_GAFS2 S r P hI.toFinset hIS' w hrx ?_ ?_ ?_ ?_ (hwb x hx) a
      (fun z' hz' => ⟨hmapV z' hz', hZ x hx z' hz'⟩) hz hda hDa ℓ hplane R₀ β hβ
    · intro i y
      rw [hw]
      exact normalized_ballCutoff_nonneg hI.toFinset (fun a => a) (fun a => 40 * ε⁻¹ * r a) i y
    · intro i hi y hne
      have hnum : ballCutoff i (40 * ε⁻¹ * r i) (2 * (40 * ε⁻¹ * r i)) y ≠ 0 := by
        intro h0
        apply hne
        rw [hw]
        simp only [h0, zero_div]
      have hb := ballCutoff_support_subset_ball (hri i hi).le (by linarith [hri i hi]) hnum
      have heq : 2 * (40 * ε⁻¹ * r i) = 80 * ε⁻¹ * r i := by ring
      rwa [heq] at hb
    · intro y hy
      rw [hw]
      exact sum_normalized_ballCutoffs_eq_one_of_cover hI.toFinset (fun a => a)
        (fun a => 40 * ε⁻¹ * r a) hri (hcover y hy)
    · intro i _ y hy
      have hcd := contDiffOn_normalized_ballCutoff_of_cover hI.toFinset (fun a => a)
        (fun a => 40 * ε⁻¹ * r a) hri hcover i
      rw [hw]
      exact (hcd.contDiffAt (isOpen_ball.mem_nhds hy)).differentiableAt (by simp)

end StageMean

end GC.MetricGeometry
