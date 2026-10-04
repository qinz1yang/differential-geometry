import DifferentialGeometry.Geometry.Collapse.BoundaryCollar.CollarVerticalAcceleration
import DifferentialGeometry.Geometry.Collapse.BoundaryCollar.CollarOverlap
import DifferentialGeometry.Geometry.Collapse.BoundaryCollar.CollarSplitting
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspBoundaryBandUpperDistance
import DifferentialGeometry.Analysis.Calculus.Taylor.TangentChord

/-!
# Overlapping collars: the `j`-height drops along the `i`-verticals (BCP03, route R-V)

Let `B` be a nearly cuspidal boundary, `i ≠ j`, `e_i`, `e_j` the two collars, and `η` a smoothing
of the `j`-height with the BCP01 bounds on the band `2 ≤ z_j ≤ 98`. At a point
`x = e_i(t, h) = e_j(t', z')` with `3 ≤ h ≤ 97.5` and `z' ≤ 97`:

* `NearlyCuspidalBoundary.height_lower_of_mem_two_collars`: `z' ≥ √(1−δ)/√(1+δ)·(99.9 − h)`
  (the `j`-vertical reaches `∂_j`, which lies outside `e_i{z < 99.9}`; first exit E.3);
* `NearlyCuspidalBoundary.vertical_drop` (step A2): `η(e_i(t, h + 1/10)) − η(x) ≤ −1/12`. The
  `j`-vertical from `x` down to `∂_j` first leaves `e_i{z < h + 1/10}` on the level torus
  `e_i{z = h + 1/10}` (E.2); along it `η` drops at rate `> .99` over a length `≥ .0999` (E.3
  against the vertical upper distance), and the level torus has diameter `O(δ)` (G-diam);
* `NearlyCuspidalBoundary.vertical_transversal` (step B): `∂_z(η ∘ e_i)(t, h) ≤ −7/10`, by the
  chord estimate along the `i`-vertical, whose second derivative is bounded by A1
  (`CuspEmbedding.abs_iteratedDeriv_two_vertical_sub_hessian_le`) and the BCP01 Hessian bound.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint
  DifferentialGeometry.Topology.Manifold DifferentialGeometry.Geometry.Connection
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.Collapse

universe u

variable {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ}

/-- The half-line lift of `0` is the origin. -/
theorem halfSpaceOneLift_zero_eq_halfZero : halfSpaceOneLift 0 = halfZero := by
  apply Subtype.ext
  ext i
  fin_cases i
  change max (0 : ℝ) 0 = 0
  simp

/-- The height of a lifted point. -/
theorem cusp_height_lift (t : Torus) {s : ℝ} (hs : 0 ≤ s) :
    ((t, halfSpaceOneLift s) : CuspHalfSpace).2.val 0 = s := by
  change (halfSpaceOneLift s).1 0 = s
  rw [halfSpaceOneLift_val_zero, max_eq_left hs]

/-- A lifted point of height `< 100` is in the cusp domain. -/
theorem cusp_lift_mem_cuspDomain (t : Torus) {s : ℝ} (hs : 0 ≤ s) (hs' : s < cuspDepth) :
    ((t, halfSpaceOneLift s) : CuspHalfSpace) ∈ cuspDomain := by
  change ((t, halfSpaceOneLift s) : CuspHalfSpace).2.val 0 < cuspDepth
  rw [cusp_height_lift t hs]
  exact hs'

/-- Distance along a vertical: `d_g(e(t, a), e(t, b)) ≤ √(1+δ) |a − b|`, `0 ≤ a, b < 100`. -/
theorem CuspEmbedding.riemannianEDistOf_vertical_le {X : Set W.Carrier}
    (e : CuspEmbedding W g K δ X) (t : Torus) {a b : ℝ} (ha : 0 ≤ a) (ha' : a < cuspDepth)
    (hb : 0 ≤ b) (hb' : b < cuspDepth) :
    riemannianEDistOf g (e.toFun (t, halfSpaceOneLift a)) (e.toFun (t, halfSpaceOneLift b)) ≤
      ENNReal.ofReal (Real.sqrt (1 + δ) * |a - b|) := by
  have h := e.riemannianEDistOf_le_flat (cusp_lift_mem_cuspDomain t ha ha')
    (cusp_lift_mem_cuspDomain t hb hb')
  rw [cusp_height_lift t ha, cusp_height_lift t hb, riemannianEDistOf_self,
    ENNReal.toReal_zero, zero_pow (by norm_num), add_zero, Real.sqrt_sq_eq_abs] at h
  exact h

/-- Continuity of a vertical `σ ↦ e(t, σ)` below height `100`. -/
theorem CuspEmbedding.continuousAt_vertical {X : Set W.Carrier} (e : CuspEmbedding W g K δ X)
    (t : Torus) {s : ℝ} (hs : 0 ≤ s) (hs' : s < cuspDepth) :
    ContinuousAt (fun σ : ℝ => e.toFun (t, halfSpaceOneLift σ)) s := by
  have h1 : Continuous (fun σ : ℝ => ((t, halfSpaceOneLift σ) : CuspHalfSpace)) := by
    refine continuous_const.prodMk ?_
    unfold halfSpaceOneLift
    fun_prop
  exact ContinuousAt.comp (g := e.toFun) (f := fun σ : ℝ => ((t, halfSpaceOneLift σ) : CuspHalfSpace))
    (e.contMDiffOn.continuousOn.continuousAt
      (isOpen_cuspDomain.mem_nhds (cusp_lift_mem_cuspDomain t hs hs'))) h1.continuousAt

/-- **Lower bound for the second height at a point of two collars.** If
`x = e_i(t, h) = e_j(t', z')`, `h < 99.9`, then `√(1+δ) z' ≥ √(1−δ) (99.9 − h)`. -/
theorem NearlyCuspidalBoundary.height_lower_of_mem_two_collars (B : NearlyCuspidalBoundary W g K δ)
    {i j : Fin B.count} (hij : i ≠ j) {t t' : Torus} {h z' : ℝ} (hh0 : 0 ≤ h)
    (hh : h < 999 / 10) (hz'0 : 0 ≤ z') (hz' : z' < cuspDepth)
    (hx : (B.collar i).toFun (t, halfSpaceOneLift h) =
      (B.collar j).toFun (t', halfSpaceOneLift z')) :
    Real.sqrt (1 - δ) * (999 / 10 - h) ≤ Real.sqrt (1 + δ) * z' := by
  have hX : (B.collar j).toFun (t', halfSpaceOneLift 0) ∈ B.component j := by
    rw [halfSpaceOneLift_zero_eq_halfZero]
    exact (B.collar j).boundary_image.subset (mem_range_self t')
  have hnot : (B.collar j).toFun (t', halfSpaceOneLift 0) ∉
      (B.collar i).toFun '' {q : CuspHalfSpace | q.2.val 0 < 999 / 10} := by
    rintro ⟨q, hq, hq'⟩
    have hq2 : q.2.val 0 < 999 / 10 := hq
    exact B.not_mem_image_of_mem_component hij hX
      ⟨q, show q.2.val 0 < cuspDepth from lt_trans hq2 (by norm_num [cuspDepth]), hq'⟩
  have h1 := (B.collar i).ofReal_le_riemannianEDistOf_of_not_mem_image_height_lt
    (by norm_num [cuspDepth]) (p := (t, halfSpaceOneLift h)) (by rw [cusp_height_lift t hh0]; exact hh) hnot
  rw [cusp_height_lift t hh0, hx] at h1
  have h2 := (B.collar j).riemannianEDistOf_vertical_le t' hz'0 hz' le_rfl (by norm_num [cuspDepth])
  rw [sub_zero, abs_of_nonneg hz'0] at h2
  have h3 := h1.trans h2
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h3

/-- Numerical square roots: `999/1000 ≤ √(1 − δ)` and `√(1 + δ) ≤ 1001/1000` for
`δ ≤ 1/1000`. -/
theorem sqrt_one_sub_add_bounds {δ : ℝ} (hδ : δ ≤ 1 / 1000) :
    999 / 1000 ≤ Real.sqrt (1 - δ) ∧ Real.sqrt (1 + δ) ≤ 1001 / 1000 := by
  constructor
  · rw [show (999 / 1000 : ℝ) = Real.sqrt ((999 / 1000) ^ 2) from
      (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith)
  · rw [show (1001 / 1000 : ℝ) = Real.sqrt ((1001 / 1000) ^ 2) from
      (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith)

/-- **Step A2: the `j`-height drops along the `i`-vertical.** -/
theorem NearlyCuspidalBoundary.vertical_drop (B : NearlyCuspidalBoundary W g K δ)
    {i j : Fin B.count} (hij : i ≠ j) (hδ : δ ≤ 1 / 1000) {η : W.Carrier → ℝ}
    (hη : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ η) {ε : ℝ} (hε1 : ε ≤ 1 / 1000)
    (hηz : ∀ p ∈ cuspDomain, 2 ≤ p.2.val 0 → p.2.val 0 ≤ 98 →
      |η ((B.collar j).toFun p) - p.2.val 0| < ε)
    (hηv : ∀ p ∈ cuspDomain, 2 ≤ p.2.val 0 → p.2.val 0 ≤ 98 →
      99 / 100 < (show ℝ from
        mfderiv halfCollarModel 𝓘(ℝ, ℝ) (η ∘ (B.collar j).toFun) p cuspUnitVertical))
    {t t' : Torus} {h z' : ℝ} (hh3 : 3 ≤ h) (hh : h ≤ 975 / 10) (hz'0 : 0 ≤ z')
    (hz' : z' ≤ 97)
    (hx : (B.collar i).toFun (t, halfSpaceOneLift h) =
      (B.collar j).toFun (t', halfSpaceOneLift z')) :
    η ((B.collar i).toFun (t, halfSpaceOneLift (h + 1 / 10))) -
      η ((B.collar i).toFun (t, halfSpaceOneLift h)) ≤ -1 / 12 := by
  have hδ0 : 0 ≤ δ := (B.collar i).delta_nonneg
  obtain ⟨hs1, hs2⟩ := sqrt_one_sub_add_bounds hδ
  set ei := B.collar i with hei
  set ej := B.collar j with hej
  set H : ℝ := h + 1 / 10 with hH
  have hH100 : H < cuspDepth := by
    change h + 1 / 10 < 100
    linarith
  -- the second height of `x` is not small
  have hz'low : 2395 / 1000 ≤ z' := by
    have h1 := B.height_lower_of_mem_two_collars hij (by linarith) (by linarith) hz'0
      (by unfold cuspDepth; linarith) hx
    have h2 := mul_le_mul_of_nonneg_right hs1 (by linarith : (0 : ℝ) ≤ 999 / 10 - h)
    have h3 := mul_le_mul_of_nonneg_right hs2 hz'0
    nlinarith
  -- the `j`-vertical from `x` down to `∂_j`
  set P : ℝ → W.Carrier := fun σ => ej.toFun (t', halfSpaceOneLift (z' - σ)) with hP
  set U : Set W.Carrier := ei.toFun '' {q : CuspHalfSpace | q.2.val 0 < H} with hU
  have hUo : IsOpen U := ei.isOpen_image_height_lt hH100.le
  have hPc : ∀ σ ∈ Icc 0 z', ContinuousAt P σ := by
    intro σ hσ
    have h1 := ej.continuousAt_vertical t' (s := z' - σ) (by linarith [hσ.2])
      (by unfold cuspDepth; linarith [hσ.1])
    exact h1.comp (continuousAt_const.sub continuousAt_id)
  have hPcont : ContinuousOn P (Icc 0 z') := fun σ hσ => (hPc σ hσ).continuousWithinAt
  set S : Set ℝ := Icc 0 z' ∩ P ⁻¹' Uᶜ with hS
  have hSc : IsClosed S := hPcont.preimage_isClosed_of_isClosed isClosed_Icc hUo.isClosed_compl
  have hz'S : z' ∈ S := by
    refine ⟨⟨hz'0, le_rfl⟩, ?_⟩
    change P z' ∉ U
    have hX : P z' ∈ B.component j := by
      change ej.toFun (t', halfSpaceOneLift (z' - z')) ∈ B.component j
      rw [sub_self, halfSpaceOneLift_zero_eq_halfZero]
      exact ej.boundary_image.subset (mem_range_self t')
    rintro ⟨q, hq, hq'⟩
    exact B.not_mem_image_of_mem_component hij hX
      ⟨q, show q.2.val 0 < cuspDepth from lt_trans hq hH100, hq'⟩
  have hSbdd : BddBelow S := ⟨0, fun σ hσ => hσ.1.1⟩
  set σs : ℝ := sInf S with hσs
  have hσS : σs ∈ S := hSc.csInf_mem ⟨z', hz'S⟩ hSbdd
  have hσ0 : 0 ≤ σs := hσS.1.1
  have hσz : σs ≤ z' := hσS.1.2
  have hP0 : P 0 = ei.toFun (t, halfSpaceOneLift h) := by
    change ej.toFun (t', halfSpaceOneLift (z' - 0)) = _
    rw [sub_zero, hx]
  have hxU : P 0 ∈ U := by
    rw [hP0]
    exact ⟨_, show ((t, halfSpaceOneLift h) : CuspHalfSpace).2.val 0 < H by
      rw [cusp_height_lift t (by linarith)]; linarith, rfl⟩
  have hσpos : 0 < σs := by
    rcases hσ0.lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      have := hσS.2
      rw [← heq] at this
      exact this hxU
  have hbefore : ∀ σ, 0 ≤ σ → σ < σs → P σ ∈ U := by
    intro σ h0 hlt
    by_contra hnot
    have hmem : σ ∈ S := ⟨⟨h0, by linarith⟩, hnot⟩
    exact absurd (csInf_le hSbdd hmem) (not_le.mpr hlt)
  -- `P σs` lies on the level torus `e_i{z = H}`
  have hcl : P σs ∈ closure U := by
    have htend : Tendsto P (𝓝[<] σs) (𝓝 (P σs)) :=
      ((hPc σs ⟨hσ0, hσz⟩).tendsto).mono_left nhdsWithin_le_nhds
    refine mem_closure_of_tendsto htend ?_
    filter_upwards [Ioo_mem_nhdsLT hσpos] with σ hσ
    exact hbefore σ hσ.1.le hσ.2
  have hfr : P σs ∈ frontier U := ⟨hcl, by rw [hUo.interior_eq]; exact hσS.2⟩
  rw [ei.frontier_image_height_lt (by linarith) hH100] at hfr
  obtain ⟨p'', hp''H, hp''⟩ := hfr
  have hp''H' : p''.2.val 0 = H := hp''H
  have hp''eq : p'' = (p''.1, halfSpaceOneLift H) := by
    refine Prod.ext rfl ?_
    change p''.2 = halfSpaceOneLift H
    rw [← hp''H', halfSpaceOneLift_val_zero_self]
  -- the `j`-height at `P σs` is not small
  have hzs : 229 / 100 ≤ z' - σs := by
    have hxs : ei.toFun (p''.1, halfSpaceOneLift H) =
        ej.toFun (t', halfSpaceOneLift (z' - σs)) := by
      rw [← hp''eq, hp'']
    have h1 := B.height_lower_of_mem_two_collars hij (t := p''.1) (by linarith) (by linarith)
      (by linarith) (by unfold cuspDepth; linarith) hxs
    have h2 := mul_le_mul_of_nonneg_right hs1 (by linarith : (0 : ℝ) ≤ 999 / 10 - H)
    have h3 := mul_le_mul_of_nonneg_right hs2 (by linarith : (0 : ℝ) ≤ z' - σs)
    nlinarith
  -- the crossing time is not small
  have hσlow : 998 / 10000 ≤ σs := by
    have hnotU : P σs ∉ U := hσS.2
    have h1 := ei.ofReal_le_riemannianEDistOf_of_not_mem_image_height_lt hH100
      (p := (t, halfSpaceOneLift h)) (by rw [cusp_height_lift t (by linarith)]; linarith) hnotU
    rw [cusp_height_lift t (by linarith), hx] at h1
    have h2 := ej.riemannianEDistOf_vertical_le t' (a := z') (b := z' - σs) hz'0
      (by unfold cuspDepth; linarith) (by linarith) (by unfold cuspDepth; linarith)
    rw [show z' - (z' - σs) = σs by ring, abs_of_nonneg hσ0] at h2
    have h3 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp (h1.trans h2)
    rw [hH] at h3
    have h4 := mul_le_mul_of_nonneg_right hs1 (by norm_num : (0 : ℝ) ≤ h + 1 / 10 - h)
    have h5 := mul_le_mul_of_nonneg_right hs2 hσ0
    nlinarith
  -- `η` drops along the `j`-vertical at rate `> .99`
  set ψ : ℝ → ℝ := fun σ => η (P σ) with hψ
  have hψd : ∀ σ ∈ Ioo 0 σs, HasDerivAt ψ (-(show ℝ from mfderiv halfCollarModel 𝓘(ℝ, ℝ)
      (η ∘ ej.toFun) (t', halfSpaceOneLift (z' - σ)) cuspUnitVertical)) σ := by
    intro σ hσ
    have hv := ej.hasDerivAt_vertical (f := η) (x := t') (s := z' - σ) (by linarith [hσ.2])
      (by unfold cuspDepth; linarith [hσ.1]) ((hη _).mdifferentiableAt (by simp))
    have hc := hv.comp σ ((hasDerivAt_const σ z').sub (hasDerivAt_id σ))
    have heq : (fun σ => η (ej.toFun (t', halfSpaceOneLift σ))) ∘ (fun σ => z' - σ) = ψ := rfl
    rw [heq] at hc
    convert hc using 1
    rw [zero_sub, mul_neg_one]
    rfl
  have hk : AntitoneOn (fun σ => ψ σ + 99 / 100 * σ) (Icc 0 σs) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 σs) ?_ ?_ ?_
    · refine ContinuousOn.add ?_ (continuousOn_const.mul continuousOn_id)
      exact hη.continuous.comp_continuousOn (hPcont.mono (Icc_subset_Icc le_rfl hσz))
    · rw [interior_Icc]
      intro σ hσ
      exact ((hψd σ hσ).differentiableAt.add
        ((hasDerivAt_id' σ).const_mul (99 / 100)).differentiableAt).differentiableWithinAt
    · rw [interior_Icc]
      intro σ hσ
      have hσ1 : 0 ≤ z' - σ := by linarith [hσ.2]
      have hσ2 : z' - σ < cuspDepth := by unfold cuspDepth; linarith [hσ.1]
      set Dσ : ℝ := (show ℝ from mfderiv halfCollarModel 𝓘(ℝ, ℝ)
          (η ∘ ej.toFun) (t', halfSpaceOneLift (z' - σ)) cuspUnitVertical) with hDσ
      have hd : HasDerivAt (fun σ => ψ σ + 99 / 100 * σ) (-Dσ + 99 / 100 * 1) σ :=
        (hψd σ hσ).add ((hasDerivAt_id σ).const_mul (99 / 100))
      rw [hd.deriv]
      have hband : 99 / 100 < Dσ :=
        hηv _ (cusp_lift_mem_cuspDomain t' hσ1 hσ2)
          (by rw [cusp_height_lift t' hσ1]; linarith [hσ.2])
          (by rw [cusp_height_lift t' hσ1]; linarith [hσ.1])
      linarith
  have hdrop : ψ σs + 99 / 100 * σs ≤ ψ 0 + 99 / 100 * 0 :=
    hk ⟨le_rfl, hσ0⟩ ⟨hσ0, le_rfl⟩ hσ0
  -- comparison of `P σs` with the point of the `i`-vertical at height `H`
  set y₀ : W.Carrier := ei.toFun (t, halfSpaceOneLift H) with hy₀
  have hdy : riemannianEDistOf g (ej.toFun (t', halfSpaceOneLift (z' - σs))) y₀ <
      ENNReal.ofReal (Real.sqrt (1 - δ) * ((1 / 100) / 2)) := by
    have hPs : ej.toFun (t', halfSpaceOneLift (z' - σs)) = ei.toFun p'' := hp''.symm
    rw [hPs]
    have hy₀d : ((t, halfSpaceOneLift H) : CuspHalfSpace) ∈ cuspDomain :=
      cusp_lift_mem_cuspDomain t (by linarith) hH100
    have hp''d : p'' ∈ cuspDomain := by
      change p''.2.val 0 < cuspDepth
      rw [hp''H']
      exact hH100
    have h1 := ei.riemannianEDistOf_le_of_min_height hp''d hy₀d
    rw [cusp_height_lift t (by linarith), hp''H', sub_self, zero_pow (by norm_num), zero_add,
      min_self] at h1
    have hT := B.torus_riemannianEDistOf_le_two_mul (by linarith) i p''.1 t
    have hT' : (riemannianEDistOf ei.cusp.torusMetric p''.1 t).toReal ≤ 2 * δ :=
      ENNReal.toReal_le_of_le_ofReal (by linarith) hT
    have hT0 : 0 ≤ (riemannianEDistOf ei.cusp.torusMetric p''.1 t).toReal := ENNReal.toReal_nonneg
    have hexp : Real.exp (-H) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hexp0 : 0 < Real.exp (-H) := Real.exp_pos _
    refine h1.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr ?_)
    rw [Real.sqrt_lt' (by positivity)]
    have h2 : (riemannianEDistOf ei.cusp.torusMetric p''.1 t).toReal ^ 2 ≤ (2 * δ) ^ 2 :=
      pow_le_pow_left₀ hT0 hT' 2
    have hA : Real.exp (-H) * (riemannianEDistOf ei.cusp.torusMetric p''.1 t).toReal ^ 2 ≤
        (2 * δ) ^ 2 := by
      calc Real.exp (-H) * (riemannianEDistOf ei.cusp.torusMetric p''.1 t).toReal ^ 2
          ≤ 1 * (2 * δ) ^ 2 := mul_le_mul hexp h2 (sq_nonneg _) zero_le_one
        _ = (2 * δ) ^ 2 := one_mul _
    have hA' : (1 + δ) * (Real.exp (-H) *
        (riemannianEDistOf ei.cusp.torusMetric p''.1 t).toReal ^ 2) ≤ (1 + δ) * (2 * δ) ^ 2 :=
      mul_le_mul_of_nonneg_left hA (by linarith)
    have hB : (999 / 1000 * (1 / 100 / 2)) ^ 2 ≤ (Real.sqrt (1 - δ) * (1 / 100 / 2)) ^ 2 :=
      pow_le_pow_left₀ (by norm_num) (mul_le_mul_of_nonneg_right hs1 (by norm_num)) 2
    have hC : (1 + δ) * (2 * δ) ^ 2 < (999 / 1000 * (1 / 100 / 2)) ^ 2 := by nlinarith
    linarith
  obtain ⟨q₀'', hq₀''d, hq₀'', hq₀''z⟩ := ej.exists_preimage_of_riemannianEDistOf_lt
    (q₀ := (t', halfSpaceOneLift (z' - σs))) (a := 1 / 100)
    (by rw [cusp_height_lift t' (by linarith)]; unfold cuspDepth; linarith) hdy
  rw [cusp_height_lift t' (by linarith)] at hq₀''z
  have hq₀''z' := abs_lt.mp hq₀''z
  have hη₀ := hηz q₀'' hq₀''d (by linarith) (by linarith)
  have hηs := hηz (t', halfSpaceOneLift (z' - σs))
    (cusp_lift_mem_cuspDomain t' (by linarith) (by unfold cuspDepth; linarith))
    (by rw [cusp_height_lift t' (by linarith)]; linarith)
    (by rw [cusp_height_lift t' (by linarith)]; linarith)
  rw [cusp_height_lift t' (by linarith)] at hηs
  rw [hq₀''] at hη₀
  have hψs : ψ σs = η (ej.toFun (t', halfSpaceOneLift (z' - σs))) := rfl
  have hψ0 : ψ 0 = η (ei.toFun (t, halfSpaceOneLift h)) := by
    change η (P 0) = _
    rw [hP0]
  have e1 := abs_lt.mp hη₀
  have e2 := abs_lt.mp hηs
  linarith

/-- **Step B: the `i`-vertical is transverse to the `j`-levels, with the right sign.** At
`x = e_i(t, h) = e_j(t', z')`, `3 ≤ h ≤ 97.5`, `z' ≤ 97`, for a smoothing `η` of the `j`-height
with the BCP01 bounds: `∂_z(η ∘ e_i)(t, h) ≤ −7/10`. -/
theorem NearlyCuspidalBoundary.vertical_transversal (B : NearlyCuspidalBoundary W g K δ)
    {i j : Fin B.count} (hij : i ≠ j) (hK : 1 ≤ K) (hδ : δ ≤ 1 / 1000) {η : W.Carrier → ℝ}
    (hη : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ η) {ε : ℝ} (hε1 : ε ≤ 1 / 1000)
    (hηz : ∀ p ∈ cuspDomain, 2 ≤ p.2.val 0 → p.2.val 0 ≤ 98 →
      |η ((B.collar j).toFun p) - p.2.val 0| < ε)
    (hηv : ∀ p ∈ cuspDomain, 2 ≤ p.2.val 0 → p.2.val 0 ≤ 98 →
      99 / 100 < (show ℝ from
        mfderiv halfCollarModel 𝓘(ℝ, ℝ) (η ∘ (B.collar j).toFun) p cuspUnitVertical))
    (hdη : ∀ p ∈ cuspDomain, 2 ≤ p.2.val 0 → p.2.val 0 ≤ 98 →
      ∀ u : TangentSpace W.model ((B.collar j).toFun p),
        |mvfderiv W.model η ((B.collar j).toFun p) u| ≤
          (1 + 1 / 200) * Real.sqrt (g.inner ((B.collar j).toFun p) u u))
    (hH : ∀ p ∈ cuspDomain, 2 ≤ p.2.val 0 → p.2.val 0 ≤ 98 →
      ∀ u w : TangentSpace W.model ((B.collar j).toFun p),
        |(CovariantDerivative.trivial W.model W.Carrier ℝ).hessian (LeviCivita g) η
            ((B.collar j).toFun p) u w| ≤
          3 / 2 * Real.sqrt (g.inner ((B.collar j).toFun p) u u) *
            Real.sqrt (g.inner ((B.collar j).toFun p) w w))
    {t t' : Torus} {h z' : ℝ} (hh3 : 3 ≤ h) (hh : h ≤ 975 / 10) (hz'0 : 0 ≤ z')
    (hz' : z' ≤ 97)
    (hx : (B.collar i).toFun (t, halfSpaceOneLift h) =
      (B.collar j).toFun (t', halfSpaceOneLift z')) :
    (show ℝ from mfderiv halfCollarModel 𝓘(ℝ, ℝ) (η ∘ (B.collar i).toFun)
      (t, halfSpaceOneLift h) cuspUnitVertical) ≤ -7 / 10 := by
  have hδ0 : 0 ≤ δ := (B.collar i).delta_nonneg
  obtain ⟨hs1, hs2⟩ := sqrt_one_sub_add_bounds hδ
  set ei := B.collar i with hei
  set ej := B.collar j with hej
  set φ : ℝ → ℝ := fun σ => η (ei.toFun (t, halfSpaceOneLift σ)) with hφ
  have hdrop := B.vertical_drop hij hδ hη hε1 hηz hηv hh3 hh hz'0 hz' hx
  have hz'low : 2395 / 1000 ≤ z' := by
    have h1 := B.height_lower_of_mem_two_collars hij (by linarith) (by linarith) hz'0
      (by unfold cuspDepth; linarith) hx
    have h2 := mul_le_mul_of_nonneg_right hs1 (by linarith : (0 : ℝ) ≤ 999 / 10 - h)
    have h3 := mul_le_mul_of_nonneg_right hs2 hz'0
    nlinarith
  -- `φ` is `C²` with `|φ''| ≤ 2` on `[h, h + 1/10]`
  have hC2 : ∀ σ ∈ Icc h (h + 1 / 10), ContDiffAt ℝ 2 φ σ := by
    intro σ hσ
    have hσ0 : 0 < σ := by linarith [hσ.1]
    have hσd : ((t, halfSpaceOneLift σ) : CuspHalfSpace) ∈ cuspDomain :=
      cusp_lift_mem_cuspDomain t hσ0.le (by unfold cuspDepth; linarith [hσ.2])
    have hc : ContMDiffAt 𝓘(ℝ, ℝ) halfCollarModel 2
        (fun σ : ℝ => ((t, halfSpaceOneLift σ) : CuspHalfSpace)) σ :=
      contMDiffAt_const.prodMk
        ((contMDiffOn_halfSpaceOneLift.contMDiffAt (Ici_mem_nhds hσ0)).of_le (by simp))
    have he : ContMDiffAt halfCollarModel W.model 2 ei.toFun (t, halfSpaceOneLift σ) :=
      (ei.contMDiffOn.contMDiffAt (isOpen_cuspDomain.mem_nhds hσd)).of_le
        (by exact_mod_cast Nat.add_le_add_right hK 1)
    exact contMDiffAt_iff_contDiffAt.mp (((hη _).of_le (by simp)).comp σ (he.comp σ hc))
  have hM : ∀ σ ∈ Icc h (h + 1 / 10), ‖iteratedFDeriv ℝ 2 φ σ‖ ≤ 2 := by
    intro σ hσ
    have hσ0 : 0 < σ := by linarith [hσ.1]
    have hσ100 : σ < cuspDepth := by unfold cuspDepth; linarith [hσ.2]
    -- the point `e_i(t, σ)` is in the `j`-band
    have hd1 := ei.riemannianEDistOf_vertical_le t (a := h) (b := σ) (by linarith)
      (by unfold cuspDepth; linarith) hσ0.le hσ100
    rw [hx, abs_of_nonpos (by linarith [hσ.1])] at hd1
    have hd2 : riemannianEDistOf g (ej.toFun (t', halfSpaceOneLift z'))
        (ei.toFun (t, halfSpaceOneLift σ)) <
        ENNReal.ofReal (Real.sqrt (1 - δ) * ((1 / 4) / 2)) := by
      refine hd1.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr ?_)
      have h1 := mul_le_mul_of_nonneg_right hs2 (by linarith [hσ.1] : (0 : ℝ) ≤ -(h - σ))
      have h2 := mul_le_mul_of_nonneg_right hs1 (by norm_num : (0 : ℝ) ≤ (1 / 4) / 2)
      nlinarith [hσ.2]
    obtain ⟨pσ, hpσd, hpσ, hpσz⟩ := ej.exists_preimage_of_riemannianEDistOf_lt
      (q₀ := (t', halfSpaceOneLift z')) (a := 1 / 4)
      (by rw [cusp_height_lift t' hz'0]; unfold cuspDepth; linarith) hd2
    rw [cusp_height_lift t' hz'0] at hpσz
    have hpσz' := abs_lt.mp hpσz
    have h2 : 2 ≤ pσ.2.val 0 := by linarith
    have h98 : pσ.2.val 0 ≤ 98 := by linarith
    have hdf := hdη pσ hpσd h2 h98
    have hHσ := hH pσ hpσd h2 h98
    rw [hpσ] at hdf hHσ
    have hA1 := ei.abs_iteratedDeriv_two_vertical_sub_hessian_le hK hδ0 (by linarith) hη t hσ0
      hσ100 (by norm_num) hdf
    have hσd : ((t, halfSpaceOneLift σ) : CuspHalfSpace) ∈ cuspDomain :=
      cusp_lift_mem_cuspDomain t hσ0.le hσ100
    have hv := ei.pullback_inner_le_one_add_mul hσd cuspUnitVertical
    have hH1 : ei.cusp.metric.inner (t, halfSpaceOneLift σ) cuspUnitVertical cuspUnitVertical = 1 :=
      cusp_inner_unitVertical ei.cusp (t, halfSpaceOneLift σ)
    rw [hH1, mul_one] at hv
    set v := mfderiv halfCollarModel W.model ei.toFun (t, halfSpaceOneLift σ) cuspUnitVertical
      with hvdef
    have hgv : 0 ≤ g.inner (ei.toFun (t, halfSpaceOneLift σ)) v v := metric_inner_self_nonneg _ _ _
    have hHess := hHσ v v
    rw [mul_assoc, ← Real.sqrt_mul hgv, Real.sqrt_mul_self hgv] at hHess
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
    have hA1' := abs_le.mp hA1
    have hHess' := abs_le.mp hHess
    rw [abs_le]
    constructor <;> nlinarith
  have hchord := DifferentialGeometry.Analysis.abs_deriv_sub_chord_le (by norm_num : (0 : ℝ) < 1 / 10)
    hC2 hM
  have hderiv : deriv φ h = (show ℝ from mfderiv halfCollarModel 𝓘(ℝ, ℝ) (η ∘ ei.toFun)
      (t, halfSpaceOneLift h) cuspUnitVertical) :=
    (ei.hasDerivAt_vertical (f := η) (x := t) (by linarith) (by unfold cuspDepth; linarith)
      ((hη _).mdifferentiableAt (by simp))).deriv
  rw [← hderiv]
  have hc := abs_le.mp hchord
  have hdrop' : φ (h + 1 / 10) - φ h ≤ -1 / 12 := hdrop
  have : (φ (h + 1 / 10) - φ h) / (1 / 10) ≤ -10 / 12 := by
    rw [div_le_iff₀ (by norm_num)]
    linarith
  linarith [hc.2]

end DifferentialGeometry.Geometry.Collapse
