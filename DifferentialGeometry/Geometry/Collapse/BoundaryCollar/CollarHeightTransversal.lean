import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspBoundaryInverse
import DifferentialGeometry.Geometry.Collapse.BoundaryCollar.CollarLevelTorus

/-!
# The collar height is `C¹` up to the boundary and transverse to it (F-e, E6(i) input)

For a cusp embedding `e : CuspEmbedding W g K δ X` let `z = height ∘ e⁻¹`, i.e.
`z y = (invFunOn e.toFun cuspDomain y).2.val 0` (lane B-5a's `C¹` inverse up to the boundary).

* `CuspEmbedding.contMDiffOn_height`, `CuspEmbedding.height_apply`, `height_nonneg`: `z` is `C¹`
  on the open collar `e '' cuspDomain` (boundary included), `z (e p) = p.2.val 0`, `z ≥ 0`.
* `CuspEmbedding.mfderiv_height_pos_of_mem`: at a point of `X = e (T² × {0})`, `dz v > 0` for
  every chart vector `v` with `v 0 > 0` (an inward vector). Proof: `z ∘ ψ⁻¹` has a minimum on the
  half space at `ψ y`, so `dz ≥ 0` on inward vectors and `dz = 0` on the boundary hyperplane;
  `dz ≠ 0` because `dz ∘ de = d(height) ≠ 0`.
* `CuspEmbedding.continuousOn_mfderiv_height_apply`: `y ↦ dz_y (V y)` is continuous on the open
  collar for every smooth vector field `V`.
* `CuspEmbedding.exists_pos_on_collar`: a function continuous on the open collar and positive on
  `X` is positive on a uniform collar `e (T² × [0, s₀])`, `0 < s₀ ≤ 1` (applied to `dz (V)` for a
  smooth field `V` inward at the boundary).
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint
  DifferentialGeometry.Topology.Manifold

namespace DifferentialGeometry.Geometry.Collapse

universe u

variable {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ}
  {X : Set W.Carrier}

/-- The collar height is `C¹` on the open collar, boundary included. -/
theorem CuspEmbedding.contMDiffOn_height (e : CuspEmbedding W g K δ X) :
    ContMDiffOn W.model 𝓘(ℝ, ℝ) 1 (fun y => (invFunOn e.toFun cuspDomain y).2.val 0)
      (e.toFun '' cuspDomain) :=
  ((contMDiff_halfSpaceOneCoordinate.comp contMDiff_snd).of_le
    (by exact_mod_cast le_top)).comp_contMDiffOn e.contMDiffOn_invFunOn

theorem CuspEmbedding.height_apply (e : CuspEmbedding W g K δ X) {p : CuspHalfSpace}
    (hp : p ∈ cuspDomain) : (invFunOn e.toFun cuspDomain (e.toFun p)).2.val 0 = p.2.val 0 := by
  rw [e.injOn_cuspDomain.leftInvOn_invFunOn hp]

theorem CuspEmbedding.height_nonneg (e : CuspEmbedding W g K δ X) (y : W.Carrier) :
    0 ≤ (invFunOn e.toFun cuspDomain y).2.val 0 :=
  (invFunOn e.toFun cuspDomain y).2.2

/-- **Transversality of the height at the boundary torus.** At a point of `X`, the derivative of
the collar height is positive on every inward chart vector. -/
theorem CuspEmbedding.mfderiv_height_pos_of_mem (e : CuspEmbedding W g K δ X) {y : W.Carrier}
    (hy : y ∈ X) {v : EuclideanSpace ℝ (Fin 3)} (hv : 0 < v 0) :
    0 < (show ℝ from
      mfderiv W.model 𝓘(ℝ, ℝ) (fun y => (invFunOn e.toFun cuspDomain y).2.val 0) y v) := by
  set z : W.Carrier → ℝ := fun y => (invFunOn e.toFun cuspDomain y).2.val 0 with hzdef
  rw [← e.boundary_image] at hy
  obtain ⟨t, rfl⟩ := hy
  set p : CuspHalfSpace := (t, halfZero) with hpdef
  have hp : p ∈ cuspDomain := by
    change (0 : ℝ) < 100
    norm_num
  have hU : IsOpen (e.toFun '' cuspDomain) := e.isOpen_image_cuspDomain
  have hyU : e.toFun p ∈ e.toFun '' cuspDomain := mem_image_of_mem _ hp
  have hzd : MDifferentiableAt W.model 𝓘(ℝ, ℝ) z (e.toFun p) :=
    (e.contMDiffOn_height.contMDiffAt (hU.mem_nhds hyU)).mdifferentiableAt (by simp)
  set L : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ := mfderiv W.model 𝓘(ℝ, ℝ) z (e.toFun p) with hLdef
  -- the chart at the boundary point
  have hby : W.model.IsBoundaryPoint (e.toFun p) := (e.boundary_preimage hp).mpr rfl
  have hrange := CompactCarrier.range_model_eq_of_isBoundaryPoint W hby
  set ψ := extChartAt W.model (e.toFun p) with hψ
  have hψ0 : (ψ (e.toFun p)) 0 = 0 := by
    have h := (ModelWithCorners.isBoundaryPoint_iff (I := W.model)).mp hby
    rw [hrange] at h
    have hsub := frontier_le_subset_eq (continuous_const (y := (0 : ℝ)))
      ((EuclideanSpace.proj (0 : Fin 3)).continuous) h
    exact hsub.symm
  -- `z ∘ ψ⁻¹` has a minimum on the half space at `ψ y`
  have hfd : HasFDerivWithinAt (writtenInExtChartAt W.model 𝓘(ℝ, ℝ) (e.toFun p) z) L
      (range W.model) (ψ (e.toFun p)) := hzd.hasMFDerivAt.2
  have hmin : IsLocalMinOn (writtenInExtChartAt W.model 𝓘(ℝ, ℝ) (e.toFun p) z)
      (range W.model) (ψ (e.toFun p)) := by
    refine Filter.Eventually.of_forall fun w => ?_
    change z (ψ.symm (ψ (e.toFun p))) ≤ z (ψ.symm w)
    rw [ψ.left_inv (mem_extChartAt_source (e.toFun p))]
    change (invFunOn e.toFun cuspDomain (e.toFun p)).2.val 0 ≤ _
    rw [e.height_apply hp]
    exact e.height_nonneg _
  have hcone : ∀ w : EuclideanSpace ℝ (Fin 3), 0 ≤ w 0 →
      w ∈ posTangentConeAt (range W.model) (ψ (e.toFun p)) := by
    intro w hw
    apply mem_posTangentConeAt_of_segment_subset
    rw [hrange, segment_eq_image]
    rintro _ ⟨θ, hθ, rfl⟩
    change 0 ≤ ((1 - θ) • ψ (e.toFun p) + θ • (ψ (e.toFun p) + w)) 0
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, hψ0, mul_zero, zero_add]
    exact mul_nonneg hθ.1 hw
  have hnonneg : ∀ w : EuclideanSpace ℝ (Fin 3), 0 ≤ w 0 → 0 ≤ L w := fun w hw =>
    hmin.hasFDerivWithinAt_nonneg hfd (hcone w hw)
  have hzero : ∀ w : EuclideanSpace ℝ (Fin 3), w 0 = 0 → L w = 0 := by
    intro w hw
    have h1 := hnonneg w hw.ge
    have h2 := hnonneg (-w) (by simp [hw])
    rw [map_neg] at h2
    linarith
  -- `L ≠ 0`: `L ∘ de = d(height)`
  have hLne : L ≠ 0 := by
    intro hL0
    have hed : MDifferentiableAt halfCollarModel W.model e.toFun p :=
      (e.contMDiffOn.contMDiffAt (isOpen_cuspDomain.mem_nhds hp)).mdifferentiableAt (by simp)
    have hev : (z ∘ e.toFun) =ᶠ[𝓝 p] fun q : CuspHalfSpace => q.2.val 0 :=
      Filter.eventuallyEq_of_mem (isOpen_cuspDomain.mem_nhds hp) fun q hq => e.height_apply hq
    set T : ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) × EuclideanSpace ℝ (Fin 1))
        →L[ℝ] ℝ := (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).toContinuousLinearMap.comp
          (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))
            (EuclideanSpace ℝ (Fin 1))) with hTdef
    have hheight : HasMFDerivAt halfCollarModel 𝓘(ℝ, ℝ)
        (fun q : CuspHalfSpace => q.2.val 0) p T :=
      (hasMFDerivAt_halfSpaceOneCoordinate p.2).comp p (hasMFDerivAt_snd p)
    have hcomp : HasMFDerivAt halfCollarModel 𝓘(ℝ, ℝ) (fun q : CuspHalfSpace => q.2.val 0) p
        (L.comp (mfderiv halfCollarModel W.model e.toFun p)) :=
      (hzd.hasMFDerivAt.comp p hed.hasMFDerivAt).congr_of_eventuallyEq hev.symm
    have huniq : L.comp (mfderiv halfCollarModel W.model e.toFun p) = T :=
      hcomp.mfderiv.symm.trans hheight.mfderiv
    rw [hL0] at huniq
    have h1 := congrArg (fun S : ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) ×
      EuclideanSpace ℝ (Fin 1)) →L[ℝ] ℝ => S ((0, 0), EuclideanSpace.single (0 : Fin 1) 1)) huniq
    simp only [Fin.isValue, hTdef, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_snd',
      ContinuousLinearEquiv.coe_coe, PiLp.equivOfUnique_apply, Fin.default_eq_zero,
      PiLp.single_eq_same] at h1
    have h2 : (0 : ℝ) = 1 := h1
    exact zero_ne_one h2
  -- `L = L(b) · proj₀` with `L(b) > 0`
  set b : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single 0 1 with hbdef
  have hdecomp : ∀ w : EuclideanSpace ℝ (Fin 3), L w = w 0 * L b := by
    intro w
    have h := hzero (w - w 0 • b) (by simp [hbdef])
    rw [map_sub, map_smul, smul_eq_mul, sub_eq_zero] at h
    exact h
  have hLb : 0 < L b := by
    rcases (hnonneg b (by simp [hbdef])).lt_or_eq with h | h
    · exact h
    · exfalso
      apply hLne
      ext w
      rw [hdecomp w, ← h, mul_zero]
      rfl
  change 0 < L v
  rw [hdecomp v]
  exact mul_pos hv hLb

/-- The derivative of the collar height along a smooth field is continuous on the open
collar. -/
theorem CuspEmbedding.continuousOn_mfderiv_height_apply (e : CuspEmbedding W g K δ X)
    {V : (y : W.Carrier) → TangentSpace W.model y}
    (hV : ContMDiff W.model W.model.tangent ∞
      (fun y => (⟨y, V y⟩ : TangentBundle W.model W.Carrier))) :
    ContinuousOn (fun y => (show ℝ from mfderiv W.model 𝓘(ℝ, ℝ)
      (fun y => (invFunOn e.toFun cuspDomain y).2.val 0) y (V y))) (e.toFun '' cuspDomain) := by
  set z : W.Carrier → ℝ := fun y => (invFunOn e.toFun cuspDomain y).2.val 0 with hzdef
  have hU : IsOpen (e.toFun '' cuspDomain) := e.isOpen_image_cuspDomain
  have ht := e.contMDiffOn_height.continuousOn_tangentMapWithin le_rfl hU.uniqueMDiffOn
  have hsec : ContinuousOn (fun y => (⟨y, V y⟩ : TangentBundle W.model W.Carrier))
      (e.toFun '' cuspDomain) := hV.continuous.continuousOn
  have hcomp :=
    ((contMDiff_snd_tangentBundle_modelSpace (n := 1) ℝ 𝓘(ℝ, ℝ)).continuous.comp_continuousOn
      (ht.comp hsec fun y hy => hy))
  refine hcomp.congr fun y hy => ?_
  change mfderiv W.model 𝓘(ℝ, ℝ) z y (V y) =
    mfderivWithin W.model 𝓘(ℝ, ℝ) z (e.toFun '' cuspDomain) y (V y)
  rw [mfderivWithin_of_isOpen hU hy]

/-- **A uniform collar.** A function continuous on the open collar and positive on `X` is
positive on `e (T² × [0, s₀])` for some `0 < s₀ ≤ 1`. -/
theorem CuspEmbedding.exists_pos_on_collar (e : CuspEmbedding W g K δ X) {G : W.Carrier → ℝ}
    (hG : ContinuousOn G (e.toFun '' cuspDomain)) (hX : ∀ y ∈ X, 0 < G y) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ s₀ ≤ 1 ∧ ∀ x : Torus, ∀ s ∈ Icc (0 : ℝ) s₀,
      0 < G (e.toFun (x, halfSpaceOneLift s)) := by
  set G' : Torus × ℝ → ℝ := fun q => G (e.toFun (q.1, halfSpaceOneLift q.2)) with hGdef
  set D₀ : Set (Torus × ℝ) := univ ×ˢ Icc (0 : ℝ) 1 with hD₀
  have hD₀c : IsCompact D₀ := isCompact_univ.prod isCompact_Icc
  have hmem : ∀ q ∈ D₀, ((q.1, halfSpaceOneLift q.2) : CuspHalfSpace) ∈ cuspDomain := by
    intro q hq
    change (halfSpaceOneLift q.2).1 0 < cuspDepth
    rw [halfSpaceOneLift_val_zero, max_eq_left hq.2.1]
    exact hq.2.2.trans_lt (by norm_num [cuspDepth])
  have hφc : ContinuousOn (fun q : Torus × ℝ => e.toFun (q.1, halfSpaceOneLift q.2)) D₀ :=
    e.contMDiffOn.continuousOn.comp
      (contMDiffOn_cuspVertical.continuousOn.mono (prod_mono subset_rfl fun s hs => hs.1))
      hmem
  have hGc : ContinuousOn G' D₀ := hG.comp hφc fun q hq => mem_image_of_mem _ (hmem q hq)
  have hG0 : ∀ x : Torus, 0 < G' (x, 0) := by
    intro x
    have h0 : halfSpaceOneLift 0 = halfZero := by
      apply Subtype.ext
      ext i
      fin_cases i
      simp [halfSpaceOneLift_val_zero, halfZero, halfPoint]
    change 0 < G (e.toFun (x, halfSpaceOneLift 0))
    rw [h0]
    exact hX _ ((Set.ext_iff.mp e.boundary_image _).mp ⟨x, rfl⟩)
  set Kbad : Set (Torus × ℝ) := D₀ ∩ G' ⁻¹' Iic 0 with hKbad
  have hKc : IsCompact Kbad := hD₀c.of_isClosed_subset
    (hGc.preimage_isClosed_of_isClosed hD₀c.isClosed isClosed_Iic) inter_subset_left
  rcases Kbad.eq_empty_or_nonempty with hE | hNE
  · refine ⟨1, one_pos, le_rfl, fun x s hs => ?_⟩
    by_contra hneg
    have hq : (x, s) ∈ Kbad := ⟨⟨mem_univ _, hs⟩, not_lt.mp hneg⟩
    rw [hE] at hq
    exact hq
  · obtain ⟨q₀, hq₀, hmin⟩ := hKc.exists_isMinOn hNE continuous_snd.continuousOn
    have hq₀pos : 0 < q₀.2 := by
      rcases hq₀.1.2.1.lt_or_eq with h | h
      · exact h
      · exfalso
        have hG := hq₀.2
        have hq₀eq : q₀ = (q₀.1, 0) := Prod.ext rfl h.symm
        rw [hq₀eq] at hG
        exact absurd (hG0 q₀.1) (not_lt.mpr hG)
    refine ⟨min (q₀.2 / 2) 1, lt_min (half_pos hq₀pos) one_pos, min_le_right _ _,
      fun x s hs => ?_⟩
    by_contra hneg
    have hq : (x, s) ∈ Kbad :=
      ⟨⟨mem_univ _, hs.1, hs.2.trans (min_le_right _ _)⟩, not_lt.mp hneg⟩
    have h1 := hmin hq
    have h2 : s ≤ q₀.2 / 2 := hs.2.trans (min_le_left _ _)
    change q₀.2 ≤ s at h1
    linarith

end DifferentialGeometry.Geometry.Collapse
