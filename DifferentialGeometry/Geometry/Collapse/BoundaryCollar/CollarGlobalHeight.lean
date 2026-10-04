import DifferentialGeometry.Geometry.Collapse.BoundaryCollar.CollarHeightLevels
import DifferentialGeometry.Geometry.Collapse.BoundaryCollar.CollarVerticalAcceleration

/-!
# A global regular height for one collar (BCP03, route R-V, step P1)

For a cusp embedding `e : CuspEmbedding W g K δ X` (`K ≥ 1`, `0 ≤ δ ≤ 1/1000`) and
`0 < ε ≤ 1/1000`, `CuspEmbedding.exists_global_height` gives a smoothing `η` of the height with
the BCP01 bounds on the band `2 ≤ z ≤ 98` and ONE smooth function `G` on `W` with

* `G = a < 90` on the boundary component `X`, `G` regular wherever `G < 96`;
* `G = η` near every collar point of height `3 ≤ z ≤ 94`;
* `G ≤ 93` on `e{z ≤ 92.99}`, `G < 96` on `e{z < 95.9}`, every point with `G < 97` in `e{z < 98}`;
* every point with `92 ≤ G ≤ 93` in `e{91.99 ≤ z ≤ 93.01}`.

`G` is the inner-collar function `F` of row E6 below height `45` and the blend
`collarLevelBlend η` (BDY-Z) above, `100` off `e{z < 98}`; both agree with `η` on
`e{40 < z < 50}`. These are the two functions of E7 (`TwoCollarGlue`) for two overlapping collars.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint
  DifferentialGeometry.Topology.Manifold DifferentialGeometry.Geometry.Connection
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

universe u

variable {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ}
  {X : Set W.Carrier}

/-- Above the low cutoff the blend is at least `η` (`2.3 ≤ η ≤ 100`). -/
theorem le_collarLevelBlend {η : W.Carrier → ℝ} {y : W.Carrier} (h1 : 23 / 10 ≤ η y)
    (h2 : η y ≤ 100) : η y ≤ collarLevelBlend η y := by
  rw [collarLevelBlend, innerCollarCutoff_of_ge (by norm_num) h1]
  obtain ⟨ht0, ht1⟩ := innerCollarCutoff_mem (977 / 10) (978 / 10) (η y)
  nlinarith

/-- **P1: the global height of a collar.** -/
theorem CuspEmbedding.exists_global_height (e : CuspEmbedding W g K δ X) (hK : 1 ≤ K)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 1000) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 1000) :
    ∃ (η G : W.Carrier → ℝ) (a : ℝ), a < 90 ∧ ContMDiff W.model 𝓘(ℝ, ℝ) ∞ η ∧
      ContMDiff W.model 𝓘(ℝ, ℝ) ∞ G ∧
      (∀ p ∈ cuspDomain, 2 ≤ p.2.val 0 → p.2.val 0 ≤ 98 → |η (e.toFun p) - p.2.val 0| < ε) ∧
      (∀ p ∈ cuspDomain, 2 ≤ p.2.val 0 → p.2.val 0 ≤ 98 →
        99 / 100 < (show ℝ from
          mfderiv halfCollarModel 𝓘(ℝ, ℝ) (η ∘ e.toFun) p cuspUnitVertical)) ∧
      (∀ p ∈ cuspDomain, 2 ≤ p.2.val 0 → p.2.val 0 ≤ 98 →
        ∀ u : TangentSpace W.model (e.toFun p),
          |mvfderiv W.model η (e.toFun p) u| ≤
            (1 + 1 / 200) * Real.sqrt (g.inner (e.toFun p) u u)) ∧
      (∀ p ∈ cuspDomain, 2 ≤ p.2.val 0 → p.2.val 0 ≤ 98 →
        ∀ u w : TangentSpace W.model (e.toFun p),
          |(CovariantDerivative.trivial W.model W.Carrier ℝ).hessian (LeviCivita g) η
              (e.toFun p) u w| ≤
            3 / 2 * Real.sqrt (g.inner (e.toFun p) u u) * Real.sqrt (g.inner (e.toFun p) w w)) ∧
      (∀ x ∈ X, G x = a) ∧
      (∀ p ∈ cuspDomain, 3 ≤ p.2.val 0 → p.2.val 0 ≤ 94 → G =ᶠ[𝓝 (e.toFun p)] η) ∧
      (∀ y, G y < 96 → mfderiv W.model 𝓘(ℝ, ℝ) G y ≠ 0) ∧
      (∀ y, G y < 97 → y ∈ e.toFun '' {q : CuspHalfSpace | q.2.val 0 < 98}) ∧
      (∀ p ∈ cuspDomain, p.2.val 0 ≤ 9299 / 100 → G (e.toFun p) ≤ 93) ∧
      (∀ p ∈ cuspDomain, p.2.val 0 < 959 / 10 → G (e.toFun p) < 96) ∧
      ∀ y, 92 ≤ G y → G y ≤ 93 →
        ∃ p ∈ cuspDomain, e.toFun p = y ∧ 9199 / 100 ≤ p.2.val 0 ∧ p.2.val 0 ≤ 9301 / 100 := by
  classical
  obtain ⟨η, F, a, har, hη, hF, hZ, hXa, hmid, hchar, hreg, -, -⟩ :=
    e.exists_innerCollar_height hK hε
  -- the BCP01 band clauses in `g`-norms (as in `CuspEmbedding.bcp01`)
  have hband : ∀ p ∈ cuspDomain, 2 ≤ p.2.val 0 → p.2.val 0 ≤ 98 →
      |η (e.toFun p) - p.2.val 0| < ε ∧
      (∀ u : TangentSpace W.model (e.toFun p), |mvfderiv W.model η (e.toFun p) u| ≤
        (1 + 1 / 200) * Real.sqrt (g.inner (e.toFun p) u u)) ∧
      (∃ u : TangentSpace W.model (e.toFun p), 0 < mvfderiv W.model η (e.toFun p) u ∧
        199 / 200 * Real.sqrt (g.inner (e.toFun p) u u) ≤ mvfderiv W.model η (e.toFun p) u) ∧
      (99 / 100 < (show ℝ from mfderiv halfCollarModel 𝓘(ℝ, ℝ) (η ∘ e.toFun) p
          ((0, 0), EuclideanSpace.single 0 1)) ∧
        (show ℝ from mfderiv halfCollarModel 𝓘(ℝ, ℝ) (η ∘ e.toFun) p
          ((0, 0), EuclideanSpace.single 0 1)) < 101 / 100) ∧
      ∀ u w : TangentSpace W.model (e.toFun p),
        |(CovariantDerivative.trivial W.model W.Carrier ℝ).hessian (LeviCivita g) η
            (e.toFun p) u w| ≤
          3 / 2 * Real.sqrt (g.inner (e.toFun p) u u) * Real.sqrt (g.inner (e.toFun p) w w) := by
    intro p hp h2 h98
    obtain ⟨h0, h1, h2'⟩ := hZ p hp h2 h98
    obtain ⟨hb1, hb2, hb3⟩ := e.bcp01b_differential_of_contract hδ hη hε.le hε1 hp h1
    have hz : 0 < p.2.val 0 := by linarith
    have hH := e.bcp01b_hessian_le_of_contract hK hδ hη hε.le hε1 (by linarith) (by linarith) hp
      hz h2' (e.abs_hessian_height_le hK hδ0 (by linarith) hp)
    exact ⟨h0, hb1, hb2, hb3, hH⟩
  have hdom : ∀ {p : CuspHalfSpace} {b : ℝ}, b < cuspDepth → p.2.val 0 ≤ b → p ∈ cuspDomain :=
    fun hb hp => cusp_mem_cuspDomain_of_le hb hp
  have hmemI : ∀ {S : Set CuspHalfSpace} {p : CuspHalfSpace}, S ⊆ cuspDomain → p ∈ cuspDomain →
      (e.toFun p ∈ e.toFun '' S ↔ p ∈ S) := by
    intro S p hS hp
    constructor
    · rintro ⟨q, hq, hqp⟩
      rw [← e.injOn_cuspDomain (hS hq) hp hqp]
      exact hq
    · intro h
      exact ⟨p, h, rfl⟩
  set E1 : Set W.Carrier := e.toFun '' {q : CuspHalfSpace | q.2.val 0 < 45} with hE1
  set E2 : Set W.Carrier := e.toFun '' {q : CuspHalfSpace | q.2.val 0 < 98} with hE2
  have hE1d : {q : CuspHalfSpace | q.2.val 0 < 45} ⊆ cuspDomain := fun q hq =>
    hdom (by unfold cuspDepth; norm_num) (le_of_lt hq)
  have hE2d : {q : CuspHalfSpace | q.2.val 0 < 98} ⊆ cuspDomain := fun q hq =>
    hdom (by unfold cuspDepth; norm_num) (le_of_lt hq)
  set G : W.Carrier → ℝ := fun y =>
    if y ∈ E1 then F y else if y ∈ E2 then collarLevelBlend η y else 100 with hG
  -- values of `G` on the collar
  have hG1 : ∀ p ∈ cuspDomain, p.2.val 0 < 45 → G (e.toFun p) = F (e.toFun p) := by
    intro p hp hz
    have : e.toFun p ∈ E1 := (hmemI hE1d hp).mpr hz
    simp [hG, this]
  have hG2 : ∀ p ∈ cuspDomain, 45 ≤ p.2.val 0 → p.2.val 0 < 98 →
      G (e.toFun p) = collarLevelBlend η (e.toFun p) := by
    intro p hp h1 h2
    have hn : e.toFun p ∉ E1 := fun h => by
      have := (hmemI hE1d hp).mp h
      change p.2.val 0 < 45 at this
      linarith
    have : e.toFun p ∈ E2 := (hmemI hE2d hp).mpr h2
    simp [hG, hn, this]
  have hG3 : ∀ y, y ∉ E2 → G y = 100 := by
    intro y hy
    have hn : y ∉ E1 := fun h => by
      obtain ⟨q, hq, rfl⟩ := h
      exact hy ⟨q, lt_trans (show q.2.val 0 < 45 from hq) (by norm_num), rfl⟩
    simp [hG, hn, hy]
  -- `F ≤ 90` below height `50`
  have hFlow : ∀ p ∈ cuspDomain, p.2.val 0 < 50 → F (e.toFun p) ≤ 90 := by
    intro p hp hz
    by_contra hcon
    push Not at hcon
    rcases le_or_gt (p.2.val 0) 2 with h2 | h2
    · exact absurd ((hchar _).mpr ⟨p, hp, rfl, Or.inl h2⟩) (not_le.mpr hcon)
    · have hFη := hmid p h2.le (by linarith)
      have hηz := (hband p hp h2.le (by linarith)).1
      have : F (e.toFun p) < 51 := by rw [hFη]; linarith [(abs_lt.mp hηz).2]
      linarith
  -- the blend is `η` in the middle range
  have hblend_mid : ∀ p ∈ cuspDomain, 40 < p.2.val 0 → p.2.val 0 < 97 →
      collarLevelBlend η (e.toFun p) = η (e.toFun p) := by
    intro p hp h1 h2
    have hηz := (hband p hp (by linarith) (by linarith)).1
    exact collarLevelBlend_of_mid (by linarith [(abs_lt.mp hηz).1])
      (by linarith [(abs_lt.mp hηz).2])
  -- local forms of `G`
  set E50 : Set W.Carrier := e.toFun '' {q : CuspHalfSpace | q.2.val 0 < 50} with hE50
  have hE50o : IsOpen E50 := e.isOpen_image_height_lt (by unfold cuspDepth; norm_num)
  have hE50d : {q : CuspHalfSpace | q.2.val 0 < 50} ⊆ cuspDomain := fun q hq =>
    hdom (by unfold cuspDepth; norm_num) (le_of_lt hq)
  have hL1 : ∀ y ∈ E50, G y = F y := by
    rintro y ⟨p, hp, rfl⟩
    have hp' : p.2.val 0 < 50 := hp
    have hpd := hE50d hp
    rcases lt_or_ge (p.2.val 0) 45 with h | h
    · exact hG1 p hpd h
    · rw [hG2 p hpd h (by linarith), hblend_mid p hpd (by linarith) (by linarith),
        hmid p (by linarith) (by linarith)]
  set R2 : Set W.Carrier := e.toFun '' {q : CuspHalfSpace | 40 < q.2.val 0 ∧ q.2.val 0 < 98}
    with hR2
  have hR2d : {q : CuspHalfSpace | 40 < q.2.val 0 ∧ q.2.val 0 < 98} ⊆ cuspDomain := fun q hq =>
    hdom (by unfold cuspDepth; norm_num) (le_of_lt hq.2)
  have hR2o : IsOpen R2 := by
    refine e.isOpen_image_of_pos ?_ hR2d fun q hq => lt_trans (by norm_num) hq.1
    exact (isOpen_lt continuous_const continuous_cusp_height).inter
      (isOpen_lt continuous_cusp_height continuous_const)
  have hL2 : ∀ y ∈ R2, G y = collarLevelBlend η y := by
    rintro y ⟨p, hp, rfl⟩
    have hpd := hR2d hp
    rcases lt_or_ge (p.2.val 0) 45 with h | h
    · rw [hG1 p hpd h, hblend_mid p hpd hp.1 (by linarith), hmid p (by linarith [hp.1])
        (by linarith)]
    · exact hG2 p hpd h hp.2
  set C3 : Set W.Carrier := e.toFun '' {q : CuspHalfSpace | 0 ≤ q.2.val 0 ∧ q.2.val 0 ≤ 979 / 10}
    with hC3
  have hC3c : IsClosed C3 := (e.isCompact_image_band (by unfold cuspDepth; norm_num)).isClosed
  have hL3 : ∀ y ∉ C3, G y = 100 := by
    intro y hy
    by_cases hy2 : y ∈ E2
    · obtain ⟨p, hp, rfl⟩ := hy2
      have hp' : p.2.val 0 < 98 := hp
      have hpd := hE2d hp
      have h979 : 979 / 10 < p.2.val 0 := by
        by_contra hle
        push Not at hle
        exact hy ⟨p, ⟨p.2.2, hle⟩, rfl⟩
      rw [hG2 p hpd (by linarith) hp']
      have hηz := (hband p hpd (by linarith) (by linarith)).1
      exact collarLevelBlend_of_high (by linarith [(abs_lt.mp hηz).1])
    · exact hG3 y hy2
  -- smoothness
  have hGs : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ G := by
    intro y
    by_cases h1 : y ∈ E50
    · exact (hF y).congr_of_eventuallyEq
        (Filter.eventuallyEq_of_mem (hE50o.mem_nhds h1) fun y' hy' => hL1 y' hy')
    by_cases h2 : y ∈ R2
    · exact ((contMDiff_collarLevelBlend hη) y).congr_of_eventuallyEq
        (Filter.eventuallyEq_of_mem (hR2o.mem_nhds h2) fun y' hy' => hL2 y' hy')
    have h3 : y ∉ C3 := by
      rintro ⟨p, hp, rfl⟩
      rcases lt_or_ge (p.2.val 0) 50 with h | h
      · exact h1 ⟨p, h, rfl⟩
      · exact h2 ⟨p, ⟨by linarith, by linarith [hp.2]⟩, rfl⟩
    exact contMDiffAt_const.congr_of_eventuallyEq
      (Filter.eventuallyEq_of_mem (hC3c.isOpen_compl.mem_nhds h3) fun y' hy' => hL3 y' hy')
  refine ⟨η, G, a, har, hη, hGs, fun p hp h2 h98 => (hband p hp h2 h98).1,
    fun p hp h2 h98 => (hband p hp h2 h98).2.2.2.1.1, fun p hp h2 h98 => (hband p hp h2 h98).2.1,
    fun p hp h2 h98 => (hband p hp h2 h98).2.2.2.2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `G = a` on `X`
    intro x hx
    obtain ⟨t, rfl⟩ := (Set.ext_iff.mp e.boundary_image x).mpr hx
    have hd : ((t, halfZero) : CuspHalfSpace) ∈ cuspDomain := by
      change (0 : ℝ) < 100
      norm_num
    rw [hG1 _ hd (by change (0 : ℝ) < 45; norm_num)]
    exact hXa _ hx
  · -- `G = η` near collar points of height `3 ≤ z ≤ 94`
    intro p hp h3 h94
    have hηz := (hband p hp (by linarith) (by linarith)).1
    rcases lt_or_ge (p.2.val 0) 50 with h | h
    · have hO : IsOpen (e.toFun '' {q : CuspHalfSpace | 2 < q.2.val 0 ∧ q.2.val 0 < 50}) := by
        refine e.isOpen_image_of_pos ?_ (fun q hq => hdom (by unfold cuspDepth; norm_num)
          (le_of_lt hq.2)) fun q hq => lt_trans (by norm_num) hq.1
        exact (isOpen_lt continuous_const continuous_cusp_height).inter
          (isOpen_lt continuous_cusp_height continuous_const)
      refine Filter.eventuallyEq_of_mem (hO.mem_nhds ⟨p, ⟨by linarith, h⟩, rfl⟩) ?_
      rintro y ⟨q, hq, rfl⟩
      have hqd : q ∈ cuspDomain := hdom (by unfold cuspDepth; norm_num) (le_of_lt hq.2)
      rw [hL1 _ ⟨q, hq.2, rfl⟩]
      exact hmid q hq.1.le (by linarith [hq.2])
    · have hO : IsOpen (R2 ∩ η ⁻¹' Ioo (23 / 10) (977 / 10)) :=
        hR2o.inter (isOpen_Ioo.preimage hη.continuous)
      have hmem : e.toFun p ∈ R2 ∩ η ⁻¹' Ioo (23 / 10) (977 / 10) :=
        ⟨⟨p, ⟨by linarith, by linarith⟩, rfl⟩,
          ⟨by linarith [(abs_lt.mp hηz).1], by linarith [(abs_lt.mp hηz).2]⟩⟩
      refine Filter.eventuallyEq_of_mem (hO.mem_nhds hmem) ?_
      rintro y ⟨hy2, hy3⟩
      rw [hL2 y hy2]
      exact collarLevelBlend_of_mid hy3.1.le hy3.2.le
  · -- regularity where `G < 96`
    intro y hy
    by_cases h1 : y ∈ E50
    · have heq : G =ᶠ[𝓝 y] F :=
        Filter.eventuallyEq_of_mem (hE50o.mem_nhds h1) fun y' hy' => hL1 y' hy'
      rw [heq.mfderiv_eq]
      obtain ⟨p, hp, rfl⟩ := h1
      exact hreg _ (hFlow p (hE50d hp) hp)
    by_cases h2 : y ∈ E2
    · obtain ⟨p, hp, rfl⟩ := h2
      have hp' : p.2.val 0 < 98 := hp
      have hpd := hE2d hp
      have h50 : 50 ≤ p.2.val 0 := by
        by_contra hlt
        push Not at hlt
        exact h1 ⟨p, hlt, rfl⟩
      have hb := hband p hpd (by linarith) hp'.le
      have hηz := hb.1
      have hGp := hG2 p hpd (by linarith) hp'
      rcases lt_or_ge (η (e.toFun p)) (977 / 10) with hlt | hge
      · -- `G = η` near `e p`
        have hO : IsOpen (R2 ∩ η ⁻¹' Ioo (23 / 10) (977 / 10)) :=
          hR2o.inter (isOpen_Ioo.preimage hη.continuous)
        have hmem : e.toFun p ∈ R2 ∩ η ⁻¹' Ioo (23 / 10) (977 / 10) :=
          ⟨⟨p, ⟨by linarith, hp'⟩, rfl⟩, ⟨by linarith [(abs_lt.mp hηz).1], hlt⟩⟩
        have heq : G =ᶠ[𝓝 (e.toFun p)] η := by
          refine Filter.eventuallyEq_of_mem (hO.mem_nhds hmem) ?_
          rintro y ⟨hy2, hy3⟩
          rw [hL2 y hy2]
          exact collarLevelBlend_of_mid hy3.1.le hy3.2.le
        rw [heq.mfderiv_eq]
        intro h0
        obtain ⟨u, hu, -⟩ := hb.2.2.1
        have h := congrArg (fun L : TangentSpace W.model (e.toFun p) →L[ℝ]
          TangentSpace 𝓘(ℝ, ℝ) (G (e.toFun p)) => L u) h0
        have : mvfderiv W.model η (e.toFun p) u = 0 := h
        linarith
      · exfalso
        have hle := le_collarLevelBlend (η := η) (y := e.toFun p) (by linarith)
          (by linarith [(abs_lt.mp hηz).2])
        rw [← hGp] at hle
        linarith
    · exfalso
      rw [hG3 y h2] at hy
      linarith
  · -- `G < 97` forces the collar below height `98`
    intro y hy
    by_contra h2
    rw [hG3 y h2] at hy
    linarith
  · -- `G ≤ 93` on `e{z ≤ 92.99}`
    intro p hp hz
    rcases lt_or_ge (p.2.val 0) 45 with h | h
    · rw [hG1 p hp h]
      linarith [hFlow p hp (by linarith)]
    · have hηz := (hband p hp (by linarith) (by linarith)).1
      rw [hG2 p hp h (by linarith), hblend_mid p hp (by linarith) (by linarith)]
      linarith [(abs_lt.mp hηz).2]
  · -- `G < 96` on `e{z < 95.9}`
    intro p hp hz
    rcases lt_or_ge (p.2.val 0) 45 with h | h
    · rw [hG1 p hp h]
      linarith [hFlow p hp (by linarith)]
    · have hηz := (hband p hp (by linarith) (by linarith)).1
      rw [hG2 p hp h (by linarith), hblend_mid p hp (by linarith) (by linarith)]
      linarith [(abs_lt.mp hηz).2]
  · -- the band `92 ≤ G ≤ 93`
    intro y hy1 hy2
    by_cases hE : y ∈ E2
    · obtain ⟨p, hp, rfl⟩ := hE
      have hp' : p.2.val 0 < 98 := hp
      have hpd := hE2d hp
      rcases lt_or_ge (p.2.val 0) 45 with h | h
      · rw [hG1 p hpd h] at hy1
        linarith [hFlow p hpd (by linarith)]
      · have hηz := (hband p hpd (by linarith) hp'.le).1
        rw [hG2 p hpd h hp'] at hy1 hy2
        rcases le_or_gt (η (e.toFun p)) (977 / 10) with hle | hgt
        · rw [collarLevelBlend_of_mid (by linarith [(abs_lt.mp hηz).1]) hle] at hy1 hy2
          exact ⟨p, hpd, rfl, by linarith [(abs_lt.mp hηz).2], by linarith [(abs_lt.mp hηz).1]⟩
        · exfalso
          have hle := le_collarLevelBlend (η := η) (y := e.toFun p) (by linarith)
            (by linarith [(abs_lt.mp hηz).2])
          linarith
    · rw [hG3 y hE] at hy1 hy2
      linarith

end DifferentialGeometry.Geometry.Collapse
