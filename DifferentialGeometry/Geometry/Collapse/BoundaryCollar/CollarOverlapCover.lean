import DifferentialGeometry.Geometry.Collapse.BoundaryCollar.CollarOverlapVertical

/-!
# Overlapping collars cover the carrier (BCP03, route R-V, steps P3 and P4)

Same setting as `CollarOverlapVertical`: `B` a nearly cuspidal boundary, `i ≠ j`, and `η` a
smoothing of the `j`-height with the BCP01 bounds on the band `2 ≤ z_j ≤ 98`.

* `NearlyCuspidalBoundary.vertical_antitone`: along an `i`-vertical whose points between
  heights `s₁ < s₂` lie in `e_j{z < 97}`, `η + (7/10)·z_i` is antitone (step B).
* `NearlyCuspidalBoundary.vertical_propagate` (P3): if `e_i(t, s₁)` lies in `e_j{z ≤ 96}`
  (`3 ≤ s₁ ≤ 97.5`), the whole `i`-vertical above it up to height `97.5` stays in
  `e_j{z < 96.5}` and `η` drops at rate `≥ 7/10` along it (a first exit through the level
  `z_j = 96.5` would contradict the drop).
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

/-- A point of a collar is the image of its lifted chart point. -/
theorem cusp_eq_lift (q : CuspHalfSpace) : q = (q.1, halfSpaceOneLift (q.2.val 0)) := by
  refine Prod.ext rfl ?_
  change q.2 = halfSpaceOneLift (q.2.1 0)
  rw [halfSpaceOneLift_val_zero_self]

/-- **`η + (7/10) z_i` is antitone along an `i`-vertical inside `e_j{z < 97}`.** -/
theorem NearlyCuspidalBoundary.vertical_antitone (B : NearlyCuspidalBoundary W g K δ)
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
    (t : Torus) {s₁ s₂ : ℝ} (hs₁ : 3 ≤ s₁) (hs₂ : s₂ ≤ 975 / 10)
    (hin : ∀ s ∈ Ioo s₁ s₂, (B.collar i).toFun (t, halfSpaceOneLift s) ∈
      (B.collar j).toFun '' {q : CuspHalfSpace | q.2.val 0 < 97}) :
    AntitoneOn (fun s => η ((B.collar i).toFun (t, halfSpaceOneLift s)) + 7 / 10 * s)
      (Icc s₁ s₂) := by
  refine antitoneOn_of_deriv_nonpos (convex_Icc s₁ s₂) ?_ ?_ ?_
  · refine ContinuousOn.add (fun s hs => ?_) (continuousOn_const.mul continuousOn_id)
    exact (hη.continuous.continuousAt.comp ((B.collar i).continuousAt_vertical t
      (by linarith [hs.1]) (by unfold cuspDepth; linarith [hs.2]))).continuousWithinAt
  · rw [interior_Icc]
    intro s hs
    have hv := (B.collar i).hasDerivAt_vertical (f := η) (x := t) (s := s) (by linarith [hs.1])
      (by unfold cuspDepth; linarith [hs.2]) ((hη _).mdifferentiableAt (by simp))
    exact (hv.differentiableAt.add
      ((hasDerivAt_id s).const_mul (7 / 10)).differentiableAt).differentiableWithinAt
  · rw [interior_Icc]
    intro s hs
    have hv := (B.collar i).hasDerivAt_vertical (f := η) (x := t) (s := s) (by linarith [hs.1])
      (by unfold cuspDepth; linarith [hs.2]) ((hη _).mdifferentiableAt (by simp))
    set Ds : ℝ := (show ℝ from mfderiv halfCollarModel 𝓘(ℝ, ℝ) (η ∘ (B.collar i).toFun)
      (t, halfSpaceOneLift s) cuspUnitVertical) with hDs
    have hd : HasDerivAt (fun s => η ((B.collar i).toFun (t, halfSpaceOneLift s)) + 7 / 10 * s)
        (Ds + 7 / 10 * 1) s := hv.add ((hasDerivAt_id s).const_mul (7 / 10))
    rw [hd.deriv]
    obtain ⟨q, hq, hqx⟩ := hin s hs
    have hq' : q.2.val 0 < 97 := hq
    have hx : (B.collar i).toFun (t, halfSpaceOneLift s) =
        (B.collar j).toFun (q.1, halfSpaceOneLift (q.2.val 0)) := by
      rw [← cusp_eq_lift, hqx]
    have hB := B.vertical_transversal hij hK hδ hη hε1 hηz hηv hdη hH (by linarith [hs.1])
      (by linarith [hs.2]) q.2.2 hq'.le hx
    have hB' : Ds ≤ -7 / 10 := hB
    linarith

/-- **P3: propagation along an `i`-vertical.** -/
theorem NearlyCuspidalBoundary.vertical_propagate (B : NearlyCuspidalBoundary W g K δ)
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
    (t : Torus) {s₁ : ℝ} (hs₁3 : 3 ≤ s₁) (hs₁ : s₁ ≤ 975 / 10) {q₁ : CuspHalfSpace}
    (hq₁ : q₁ ∈ cuspDomain) (hq₁z : q₁.2.val 0 ≤ 96)
    (hx₁ : (B.collar i).toFun (t, halfSpaceOneLift s₁) = (B.collar j).toFun q₁) :
    ∀ s ∈ Icc s₁ (975 / 10), (B.collar i).toFun (t, halfSpaceOneLift s) ∈
        (B.collar j).toFun '' {q : CuspHalfSpace | q.2.val 0 < 193 / 2} ∧
      η ((B.collar i).toFun (t, halfSpaceOneLift s)) ≤
        η ((B.collar i).toFun (t, halfSpaceOneLift s₁)) - 7 / 10 * (s - s₁) := by
  have hδ0 : 0 ≤ δ := (B.collar i).delta_nonneg
  obtain ⟨hs1, hs2⟩ := sqrt_one_sub_add_bounds hδ
  set ei := B.collar i with hei
  set ej := B.collar j with hej
  set x : ℝ → W.Carrier := fun s => ei.toFun (t, halfSpaceOneLift s) with hxdef
  set U' : Set W.Carrier := ej.toFun '' {q : CuspHalfSpace | q.2.val 0 < 193 / 2} with hU'
  have hU'o : IsOpen U' := ej.isOpen_image_height_lt (by unfold cuspDepth; norm_num)
  have hxc : ∀ s ∈ Icc s₁ (975 / 10), ContinuousAt x s := fun s hs =>
    ei.continuousAt_vertical t (by linarith [hs.1]) (by unfold cuspDepth; linarith [hs.2])
  -- the `j`-height of `x s₁` is at least `2.39`
  have hq₁low : 239 / 100 ≤ q₁.2.val 0 := by
    have hx₁' : ei.toFun (t, halfSpaceOneLift s₁) =
        ej.toFun (q₁.1, halfSpaceOneLift (q₁.2.val 0)) := by rw [← cusp_eq_lift]; exact hx₁
    have h1 := B.height_lower_of_mem_two_collars hij (by linarith) (by linarith) q₁.2.2
      hq₁ hx₁'
    have h2 := mul_le_mul_of_nonneg_right hs1 (by linarith : (0 : ℝ) ≤ 999 / 10 - s₁)
    have h3 := mul_le_mul_of_nonneg_right hs2 q₁.2.2
    nlinarith
  have hηx₁ : η (x s₁) ≤ q₁.2.val 0 + ε := by
    have h := hηz q₁ hq₁ (by linarith) (by linarith)
    change η (ei.toFun (t, halfSpaceOneLift s₁)) ≤ _
    rw [hx₁]
    linarith [(abs_lt.mp h).2]
  have hU'sub : ∀ s, x s ∈ U' → x s ∈ ej.toFun '' {q : CuspHalfSpace | q.2.val 0 < 97} := by
    rintro s ⟨q, hq, hqx⟩
    exact ⟨q, lt_trans (show q.2.val 0 < 193 / 2 from hq) (by norm_num), hqx⟩
  -- no exit through the level `z_j = 96.5`
  set T : Set ℝ := Icc s₁ (975 / 10) ∩ x ⁻¹' U'ᶜ with hT
  have hTc : IsClosed T := (ContinuousOn.preimage_isClosed_of_isClosed
    (fun s hs => (hxc s hs).continuousWithinAt) isClosed_Icc hU'o.isClosed_compl)
  have hTe : T = ∅ := by
    by_contra hne
    obtain ⟨τ₀, hτ₀⟩ := Set.nonempty_iff_ne_empty.mpr hne
    have hbdd : BddBelow T := ⟨s₁, fun s hs => hs.1.1⟩
    set τ : ℝ := sInf T with hτ
    have hτT : τ ∈ T := hTc.csInf_mem ⟨τ₀, hτ₀⟩ hbdd
    have hx₁U : x s₁ ∈ U' := ⟨q₁, show q₁.2.val 0 < 193 / 2 by linarith, hx₁.symm⟩
    have hτpos : s₁ < τ := by
      rcases hτT.1.1.lt_or_eq with hlt | heq
      · exact hlt
      · exfalso
        have := hτT.2
        rw [← heq] at this
        exact this hx₁U
    have hbefore : ∀ s, s₁ ≤ s → s < τ → x s ∈ U' := by
      intro s h0 hlt
      by_contra hnot
      have hmem : s ∈ T := ⟨⟨h0, by linarith [hτT.1.2]⟩, hnot⟩
      exact absurd (csInf_le hbdd hmem) (not_le.mpr hlt)
    have hanti := B.vertical_antitone hij hK hδ hη hε1 hηz hηv hdη hH t hs₁3 hτT.1.2
      (fun s hs => hU'sub s (hbefore s hs.1.le hs.2))
    have hdropτ := hanti ⟨le_rfl, hτpos.le⟩ ⟨hτpos.le, le_rfl⟩ hτpos.le
    simp only at hdropτ
    -- `x τ` lies on the level `z_j = 96.5`
    have hcl : x τ ∈ closure U' := by
      have htend : Tendsto x (𝓝[<] τ) (𝓝 (x τ)) :=
        ((hxc τ hτT.1).tendsto).mono_left nhdsWithin_le_nhds
      refine mem_closure_of_tendsto htend ?_
      filter_upwards [Ioo_mem_nhdsLT hτpos] with s hs
      exact hbefore s hs.1.le hs.2
    have hfr : x τ ∈ frontier U' := ⟨hcl, by rw [hU'o.interior_eq]; exact hτT.2⟩
    rw [ej.frontier_image_height_lt (by norm_num) (by unfold cuspDepth; norm_num)] at hfr
    obtain ⟨qτ, hqτ, hqτx⟩ := hfr
    have hqτ' : qτ.2.val 0 = 193 / 2 := hqτ
    have hqτd : qτ ∈ cuspDomain := by
      change qτ.2.val 0 < cuspDepth
      rw [hqτ']
      unfold cuspDepth
      norm_num
    have hητ := hηz qτ hqτd (by rw [hqτ']; norm_num) (by rw [hqτ']; norm_num)
    rw [hqτ', hqτx] at hητ
    have := (abs_lt.mp hητ).1
    have h7 : 0 ≤ 7 / 10 * (τ - s₁) := by nlinarith
    change η (x τ) + 7 / 10 * τ ≤ η (x s₁) + 7 / 10 * s₁ at hdropτ
    linarith
  have hall : ∀ s ∈ Icc s₁ (975 / 10), x s ∈ U' := by
    intro s hs
    by_contra hnot
    have hmem : s ∈ T := ⟨hs, hnot⟩
    rw [hTe] at hmem
    exact hmem
  intro s hs
  refine ⟨hall s hs, ?_⟩
  have hanti := B.vertical_antitone hij hK hδ hη hε1 hηz hηv hdη hH t hs₁3 (le_refl (975 / 10))
    (fun s hs' => hU'sub s (hall s ⟨hs'.1.le, hs'.2.le⟩))
  have h := hanti ⟨le_rfl, hs₁⟩ hs hs.1
  simp only at h
  linarith

/-- **Level tori are small: spreading along an `i`-level.** If `e_i(t₀, H)` is `e_j q`
(`0 ≤ H < 100`, `z_j(q) ≤ 97`), then every point `e_i(t, H)` of the same `i`-level is `e_j q'`
with `|z_j(q') − z_j(q)| < 1/100` (`δ ≤ 1/1000`; G-diam and the slab membership). -/
theorem NearlyCuspidalBoundary.level_spread (B : NearlyCuspidalBoundary W g K δ)
    (i j : Fin B.count) (hδ : δ ≤ 1 / 1000) {H : ℝ} (hH0 : 0 ≤ H) (hH : H < cuspDepth)
    (t t₀ : Torus) {q : CuspHalfSpace} (hqz : q.2.val 0 ≤ 97)
    (hq : (B.collar i).toFun (t₀, halfSpaceOneLift H) = (B.collar j).toFun q) :
    ∃ q' ∈ cuspDomain, (B.collar j).toFun q' = (B.collar i).toFun (t, halfSpaceOneLift H) ∧
      |q'.2.val 0 - q.2.val 0| < 1 / 100 := by
  have hδ0 : 0 ≤ δ := (B.collar i).delta_nonneg
  obtain ⟨hs1, hs2⟩ := sqrt_one_sub_add_bounds hδ
  have hd₀ : ((t₀, halfSpaceOneLift H) : CuspHalfSpace) ∈ cuspDomain :=
    cusp_lift_mem_cuspDomain t₀ hH0 hH
  have hd : ((t, halfSpaceOneLift H) : CuspHalfSpace) ∈ cuspDomain :=
    cusp_lift_mem_cuspDomain t hH0 hH
  have hdist : riemannianEDistOf g ((B.collar j).toFun q)
      ((B.collar i).toFun (t, halfSpaceOneLift H)) <
      ENNReal.ofReal (Real.sqrt (1 - δ) * ((1 / 100) / 2)) := by
    rw [← hq]
    have h1 := (B.collar i).riemannianEDistOf_le_of_min_height hd₀ hd
    rw [cusp_height_lift t₀ hH0, sub_self, zero_pow (by norm_num), zero_add, min_self] at h1
    have hT := B.torus_riemannianEDistOf_le_two_mul (by linarith) i t₀ t
    have hT' : (riemannianEDistOf (B.collar i).cusp.torusMetric t₀ t).toReal ≤ 2 * δ :=
      ENNReal.toReal_le_of_le_ofReal (by linarith) hT
    have hT0 : 0 ≤ (riemannianEDistOf (B.collar i).cusp.torusMetric t₀ t).toReal :=
      ENNReal.toReal_nonneg
    have hexp : Real.exp (-H) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hexp0 : 0 < Real.exp (-H) := Real.exp_pos _
    refine h1.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr ?_)
    rw [Real.sqrt_lt' (by positivity)]
    have h2 : (riemannianEDistOf (B.collar i).cusp.torusMetric t₀ t).toReal ^ 2 ≤ (2 * δ) ^ 2 :=
      pow_le_pow_left₀ hT0 hT' 2
    have hA : Real.exp (-H) * (riemannianEDistOf (B.collar i).cusp.torusMetric t₀ t).toReal ^ 2 ≤
        (2 * δ) ^ 2 := by
      calc Real.exp (-H) * (riemannianEDistOf (B.collar i).cusp.torusMetric t₀ t).toReal ^ 2
          ≤ 1 * (2 * δ) ^ 2 := mul_le_mul hexp h2 (sq_nonneg _) zero_le_one
        _ = (2 * δ) ^ 2 := one_mul _
    have hA' : (1 + δ) * (Real.exp (-H) *
        (riemannianEDistOf (B.collar i).cusp.torusMetric t₀ t).toReal ^ 2) ≤
        (1 + δ) * (2 * δ) ^ 2 :=
      mul_le_mul_of_nonneg_left hA (by linarith)
    have hB : (999 / 1000 * (1 / 100 / 2)) ^ 2 ≤ (Real.sqrt (1 - δ) * (1 / 100 / 2)) ^ 2 :=
      pow_le_pow_left₀ (by norm_num) (mul_le_mul_of_nonneg_right hs1 (by norm_num)) 2
    have hC : (1 + δ) * (2 * δ) ^ 2 < (999 / 1000 * (1 / 100 / 2)) ^ 2 := by nlinarith
    linarith
  exact (B.collar j).exists_preimage_of_riemannianEDistOf_lt
    (by unfold cuspDepth; linarith) hdist

/-- **The upper `i`-levels lie low in the `j`-collar.** If `e_i(pi) = e_j(pj)` with both heights
`< 92` (the enlarged collars overlap), every point `e_i(t, H)`, `91.9 ≤ H ≤ 97.5`, is `e_j q`
with `z_j(q) < 92.3`. -/
theorem NearlyCuspidalBoundary.overlap_levels (B : NearlyCuspidalBoundary W g K δ)
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
    {pi pj : CuspHalfSpace} (hpj : pj ∈ cuspDomain) (hpiz : pi.2.val 0 < 92)
    (hpjz : pj.2.val 0 < 92) (hp : (B.collar i).toFun pi = (B.collar j).toFun pj)
    (t : Torus) {H : ℝ} (hH1 : 919 / 10 ≤ H) (hH2 : H ≤ 975 / 10) :
    ∃ q ∈ cuspDomain, (B.collar j).toFun q = (B.collar i).toFun (t, halfSpaceOneLift H) ∧
      q.2.val 0 < 923 / 10 := by
  have hδ0 : 0 ≤ δ := (B.collar i).delta_nonneg
  obtain ⟨hs1, hs2⟩ := sqrt_one_sub_add_bounds hδ
  set a : ℝ := pi.2.val 0 with ha
  set b : ℝ := pj.2.val 0 with hb
  set t₀ : Torus := pi.1 with ht₀
  have hpi' : pi = (t₀, halfSpaceOneLift a) := cusp_eq_lift pi
  have hy₀ : (B.collar i).toFun (t₀, halfSpaceOneLift a) =
      (B.collar j).toFun (pj.1, halfSpaceOneLift b) := by
    rw [← hpi', hp, ← cusp_eq_lift]
  have hb0 : 0 ≤ b := pj.2.2
  have ha0 : 0 ≤ a := pi.2.2
  -- `a ≥ 7.88`
  have hale : 788 / 100 ≤ a := by
    have h1 := B.height_lower_of_mem_two_collars hij.symm (by linarith) (by linarith) ha0
      (by unfold cuspDepth; linarith) hy₀.symm
    have h2 := mul_le_mul_of_nonneg_right hs1 (by linarith : (0 : ℝ) ≤ 999 / 10 - b)
    have h3 := mul_le_mul_of_nonneg_right hs2 ha0
    nlinarith
  have hble : 2 ≤ b := by
    have h1 := B.height_lower_of_mem_two_collars hij (by linarith) (by linarith) hb0
      (by unfold cuspDepth; linarith) hy₀
    have h2 := mul_le_mul_of_nonneg_right hs1 (by linarith : (0 : ℝ) ≤ 999 / 10 - a)
    have h3 := mul_le_mul_of_nonneg_right hs2 hb0
    nlinarith
  -- the point of the `t₀`-vertical at height `H`
  have hlow : ∃ q ∈ cuspDomain, (B.collar j).toFun q =
      (B.collar i).toFun (t₀, halfSpaceOneLift H) ∧ q.2.val 0 < 9225 / 100 := by
    rcases le_or_gt a H with haH | haH
    · obtain ⟨⟨q, hq, hqx⟩, hηH⟩ := B.vertical_propagate hij hK hδ hη hε1 hηz hηv hdη hH t₀
        (by linarith) (by linarith) hpj (by linarith) (hy₀.trans (by rw [← cusp_eq_lift])) H
        ⟨haH, hH2⟩
      have hq' : q.2.val 0 < 193 / 2 := hq
      have hqd : q ∈ cuspDomain := lt_trans hq' (by unfold cuspDepth; norm_num)
      -- the `j`-height of `q` is not small
      have hqlow : 239 / 100 ≤ q.2.val 0 := by
        have hxq : (B.collar i).toFun (t₀, halfSpaceOneLift H) =
            (B.collar j).toFun (q.1, halfSpaceOneLift (q.2.val 0)) := by
          rw [← cusp_eq_lift, hqx]
        have h1 := B.height_lower_of_mem_two_collars hij (by linarith) (by linarith) q.2.2
          hqd hxq
        have h2 := mul_le_mul_of_nonneg_right hs1 (by linarith : (0 : ℝ) ≤ 999 / 10 - H)
        have h3 := mul_le_mul_of_nonneg_right hs2 q.2.2
        nlinarith
      have h1 := hηz q hqd (by linarith) (by linarith)
      have h2 := hηz pj hpj hble (by linarith)
      rw [hqx] at h1
      have hy₀' : (B.collar i).toFun (t₀, halfSpaceOneLift a) = (B.collar j).toFun pj := by
        rw [hy₀, ← cusp_eq_lift]
      rw [← hy₀'] at h2
      have h7 : 0 ≤ 7 / 10 * (H - a) := by nlinarith
      refine ⟨q, hqd, hqx, ?_⟩
      have := (abs_lt.mp h1).1
      have := (abs_lt.mp h2).2
      linarith
    · have hd1 := (B.collar i).riemannianEDistOf_vertical_le t₀ (a := a) (b := H) ha0
        (by unfold cuspDepth; linarith) (by linarith) (by unfold cuspDepth; linarith)
      rw [hy₀, abs_of_pos (by linarith : (0 : ℝ) < a - H)] at hd1
      have hd2 : riemannianEDistOf g ((B.collar j).toFun (pj.1, halfSpaceOneLift b))
          ((B.collar i).toFun (t₀, halfSpaceOneLift H)) <
          ENNReal.ofReal (Real.sqrt (1 - δ) * ((1 / 4) / 2)) := by
        refine hd1.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr ?_)
        have h1 := mul_le_mul_of_nonneg_right hs2 (by linarith : (0 : ℝ) ≤ a - H)
        have h2 := mul_le_mul_of_nonneg_right hs1 (by norm_num : (0 : ℝ) ≤ (1 / 4) / 2)
        nlinarith
      obtain ⟨q, hqd, hqx, hqz⟩ := (B.collar j).exists_preimage_of_riemannianEDistOf_lt
        (q₀ := (pj.1, halfSpaceOneLift b)) (a := 1 / 4)
        (by rw [cusp_height_lift pj.1 hb0]; unfold cuspDepth; linarith) hd2
      rw [cusp_height_lift pj.1 hb0] at hqz
      exact ⟨q, hqd, hqx, by linarith [(abs_lt.mp hqz).2]⟩
  obtain ⟨q, hqd, hqx, hqz⟩ := hlow
  obtain ⟨q', hq'd, hq'x, hq'z⟩ := B.level_spread i j hδ (by linarith)
    (by unfold cuspDepth; linarith) t t₀ (q := q) (by linarith) hqx.symm
  exact ⟨q', hq'd, hq'x, by linarith [(abs_lt.mp hq'z).2]⟩

/-- **P4: two overlapping enlarged collars cover the carrier.** If `e_i(pi) = e_j(pj)` with both
heights `< 92`, then `W = e_i{z < 97} ∪ e_j{z < 97}` (`W` connected): this union is open, and
closed because the level `z_i = 97` lies in `e_j{z < 92.3}` and the level `z_j = 97` in
`e_i{z < 92.3}`. -/
theorem NearlyCuspidalBoundary.overlap_cover [ConnectedSpace W.Carrier]
    (B : NearlyCuspidalBoundary W g K δ) {i j : Fin B.count} (hij : i ≠ j) (hK : 1 ≤ K)
    (hδ : δ ≤ 1 / 1000) {ηi ηj : W.Carrier → ℝ} (hηi : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ ηi)
    (hηj : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ ηj) {ε : ℝ} (hε1 : ε ≤ 1 / 1000)
    (hηiz : ∀ p ∈ cuspDomain, 2 ≤ p.2.val 0 → p.2.val 0 ≤ 98 →
      |ηi ((B.collar i).toFun p) - p.2.val 0| < ε)
    (hηiv : ∀ p ∈ cuspDomain, 2 ≤ p.2.val 0 → p.2.val 0 ≤ 98 →
      99 / 100 < (show ℝ from
        mfderiv halfCollarModel 𝓘(ℝ, ℝ) (ηi ∘ (B.collar i).toFun) p cuspUnitVertical))
    (hdηi : ∀ p ∈ cuspDomain, 2 ≤ p.2.val 0 → p.2.val 0 ≤ 98 →
      ∀ u : TangentSpace W.model ((B.collar i).toFun p),
        |mvfderiv W.model ηi ((B.collar i).toFun p) u| ≤
          (1 + 1 / 200) * Real.sqrt (g.inner ((B.collar i).toFun p) u u))
    (hHηi : ∀ p ∈ cuspDomain, 2 ≤ p.2.val 0 → p.2.val 0 ≤ 98 →
      ∀ u w : TangentSpace W.model ((B.collar i).toFun p),
        |(CovariantDerivative.trivial W.model W.Carrier ℝ).hessian (LeviCivita g) ηi
            ((B.collar i).toFun p) u w| ≤
          3 / 2 * Real.sqrt (g.inner ((B.collar i).toFun p) u u) *
            Real.sqrt (g.inner ((B.collar i).toFun p) w w))
    (hηjz : ∀ p ∈ cuspDomain, 2 ≤ p.2.val 0 → p.2.val 0 ≤ 98 →
      |ηj ((B.collar j).toFun p) - p.2.val 0| < ε)
    (hηjv : ∀ p ∈ cuspDomain, 2 ≤ p.2.val 0 → p.2.val 0 ≤ 98 →
      99 / 100 < (show ℝ from
        mfderiv halfCollarModel 𝓘(ℝ, ℝ) (ηj ∘ (B.collar j).toFun) p cuspUnitVertical))
    (hdηj : ∀ p ∈ cuspDomain, 2 ≤ p.2.val 0 → p.2.val 0 ≤ 98 →
      ∀ u : TangentSpace W.model ((B.collar j).toFun p),
        |mvfderiv W.model ηj ((B.collar j).toFun p) u| ≤
          (1 + 1 / 200) * Real.sqrt (g.inner ((B.collar j).toFun p) u u))
    (hHηj : ∀ p ∈ cuspDomain, 2 ≤ p.2.val 0 → p.2.val 0 ≤ 98 →
      ∀ u w : TangentSpace W.model ((B.collar j).toFun p),
        |(CovariantDerivative.trivial W.model W.Carrier ℝ).hessian (LeviCivita g) ηj
            ((B.collar j).toFun p) u w| ≤
          3 / 2 * Real.sqrt (g.inner ((B.collar j).toFun p) u u) *
            Real.sqrt (g.inner ((B.collar j).toFun p) w w))
    {pi pj : CuspHalfSpace} (hpi : pi ∈ cuspDomain) (hpj : pj ∈ cuspDomain)
    (hpiz : pi.2.val 0 < 92) (hpjz : pj.2.val 0 < 92)
    (hp : (B.collar i).toFun pi = (B.collar j).toFun pj) (y : W.Carrier) :
    y ∈ (B.collar i).toFun '' {q : CuspHalfSpace | q.2.val 0 < 97} ∨
      y ∈ (B.collar j).toFun '' {q : CuspHalfSpace | q.2.val 0 < 97} := by
  set Ui := (B.collar i).toFun '' {q : CuspHalfSpace | q.2.val 0 < 97} with hUi
  set Uj := (B.collar j).toFun '' {q : CuspHalfSpace | q.2.val 0 < 97} with hUj
  have hUio : IsOpen Ui := (B.collar i).isOpen_image_height_lt (by unfold cuspDepth; norm_num)
  have hUjo : IsOpen Uj := (B.collar j).isOpen_image_height_lt (by unfold cuspDepth; norm_num)
  have hfi : frontier Ui ⊆ Uj := by
    rw [hUi, (B.collar i).frontier_image_height_lt (by norm_num) (by unfold cuspDepth; norm_num)]
    rintro x ⟨q, hq, rfl⟩
    have hq' : q.2.val 0 = 97 := hq
    obtain ⟨q', hq'd, hq'x, hq'z⟩ := B.overlap_levels hij hK hδ hηj hε1 hηjz hηjv hdηj hHηj hpj
      hpiz hpjz hp q.1 (H := 97) (by norm_num) (by norm_num)
    refine ⟨q', show q'.2.val 0 < 97 by linarith, ?_⟩
    rw [hq'x, ← hq', ← cusp_eq_lift]
  have hfj : frontier Uj ⊆ Ui := by
    rw [hUj, (B.collar j).frontier_image_height_lt (by norm_num) (by unfold cuspDepth; norm_num)]
    rintro x ⟨q, hq, rfl⟩
    have hq' : q.2.val 0 = 97 := hq
    obtain ⟨q', hq'd, hq'x, hq'z⟩ := B.overlap_levels hij.symm hK hδ hηi hε1 hηiz hηiv hdηi
      hHηi hpi hpjz hpiz hp.symm q.1 (H := 97) (by norm_num) (by norm_num)
    refine ⟨q', show q'.2.val 0 < 97 by linarith, ?_⟩
    rw [hq'x, ← hq', ← cusp_eq_lift]
  have hcl : closure (Ui ∪ Uj) ⊆ Ui ∪ Uj := by
    rw [closure_union, closure_eq_self_union_frontier Ui, closure_eq_self_union_frontier Uj]
    rintro x ((hx | hx) | (hx | hx))
    · exact Or.inl hx
    · exact Or.inr (hfi hx)
    · exact Or.inr hx
    · exact Or.inl (hfj hx)
  have hclopen : IsClopen (Ui ∪ Uj) :=
    ⟨closure_subset_iff_isClosed.mp hcl, hUio.union hUjo⟩
  have hne : (Ui ∪ Uj).Nonempty := ⟨(B.collar i).toFun pi, Or.inl ⟨pi, by
    change pi.2.val 0 < 97
    linarith, rfl⟩⟩
  have huniv := hclopen.eq_univ hne
  have hy : y ∈ Ui ∪ Uj := by
    rw [huniv]
    exact mem_univ y
  exact hy

end DifferentialGeometry.Geometry.Collapse
