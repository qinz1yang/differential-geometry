import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.ShortGeodesicDeepFun

set_option autoImplicit false
noncomputable section
open Set Function Filter Manifold GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open scoped Manifold ContDiff Topology
universe u
namespace GC.LongTime.CuspP1

variable {H : FiniteVolumeHyperbolicModel.{u}} (T : HyperbolicTruncation H)

theorem deepHeight_cuspMap_CPA2 (b : ℝ) (i : Fin T.count) {q : CuspHalfSpace}
    (hq : 0 < q.2.val 0) : deepHeight_CPA2 T b (T.cuspMap i q) = lam_CPA2 (q.2.val 0) - b := by
  rw [deepHeight_CPA2, sum_cuspBump_cuspMap_CPA2 T i hq]

theorem deepHeight_of_forall_not_mem_CPA2 (b : ℝ) {p : H.Carrier}
    (hp : ∀ i, p ∉ cuspW_CPA2 T i) : deepHeight_CPA2 T b p = -b := by
  rw [deepHeight_CPA2, sum_cuspBump_of_forall_not_mem_CPA2 T hp, zero_sub]

theorem exists_cuspMap_of_mem_CPA2 {p : H.Carrier} (h : ∃ i, p ∈ cuspW_CPA2 T i) :
    ∃ (i : Fin T.count) (q : CuspHalfSpace), 0 < q.2.val 0 ∧ T.cuspMap i q = p := by
  obtain ⟨i, q, hq, rfl⟩ := h
  exact ⟨i, q, hq, rfl⟩

/-- `deepHeight ≤ 0` exactly off the tails `{height > b}` of the cusps. -/
theorem deepHeight_le_zero_iff_CPA2 {b : ℝ} (hb : 1 ≤ b) (p : H.Carrier) :
    deepHeight_CPA2 T b p ≤ 0 ↔
      ∀ (i : Fin T.count) (q : CuspHalfSpace), 0 < q.2.val 0 → T.cuspMap i q = p →
        q.2.val 0 ≤ b := by
  classical
  constructor
  · intro h i q hq hp
    subst hp
    rw [deepHeight_cuspMap_CPA2 T b i hq] at h
    by_contra hlt
    have hlt' : b < q.2.val 0 := not_le.mp hlt
    rw [lam_eq_CPA2 (by linarith)] at h
    linarith
  · intro h
    by_cases hw : ∃ i, p ∈ cuspW_CPA2 T i
    · obtain ⟨i, q, hq, rfl⟩ := exists_cuspMap_of_mem_CPA2 T hw
      rw [deepHeight_cuspMap_CPA2 T b i hq]
      have hs := h i q hq rfl
      by_cases h1 : 1 ≤ q.2.val 0
      · rw [lam_eq_CPA2 h1]; linarith
      · have := lam_lt_one_CPA2 (not_le.mp h1)
        linarith
    · have hw' : ∀ i, p ∉ cuspW_CPA2 T i := fun i hi => hw ⟨i, hi⟩
      rw [deepHeight_of_forall_not_mem_CPA2 T b hw']
      linarith

/-- `deepHeight = 0` exactly on the tori at height `b`. -/
theorem deepHeight_eq_zero_iff_CPA2 {b : ℝ} (hb : 1 ≤ b) (p : H.Carrier) :
    deepHeight_CPA2 T b p = 0 ↔
      ∃ (i : Fin T.count) (q : CuspHalfSpace), q.2.val 0 = b ∧ T.cuspMap i q = p := by
  classical
  constructor
  · intro h
    by_cases hw : ∃ i, p ∈ cuspW_CPA2 T i
    · obtain ⟨i, q, hq, rfl⟩ := exists_cuspMap_of_mem_CPA2 T hw
      rw [deepHeight_cuspMap_CPA2 T b i hq] at h
      by_cases h1 : 1 ≤ q.2.val 0
      · rw [lam_eq_CPA2 h1] at h
        exact ⟨i, q, by linarith, rfl⟩
      · have := lam_lt_one_CPA2 (not_le.mp h1)
        linarith
    · have hw' : ∀ i, p ∉ cuspW_CPA2 T i := fun i hi => hw ⟨i, hi⟩
      rw [deepHeight_of_forall_not_mem_CPA2 T b hw'] at h
      linarith
  · rintro ⟨i, q, hq, rfl⟩
    have hq0 : 0 < q.2.val 0 := by rw [hq]; linarith
    rw [deepHeight_cuspMap_CPA2 T b i hq0, lam_eq_CPA2 (by rw [hq]; exact hb), hq]
    ring

/-- The height coordinate of the half collar has nonzero differential at every point. -/
theorem mfderiv_height_ne_zero_CPA2 (c : ℝ) (q : CuspHalfSpace) :
    mfderiv halfCollarModel 𝓘(ℝ, ℝ) (fun q : CuspHalfSpace => q.2.val 0 - c) q ≠ 0 := by
  let Tq := PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)
  have h1 : HasMFDerivAt halfCollarModel 𝓘(ℝ, ℝ) (fun q : CuspHalfSpace => q.2.val 0) q
      (Tq.toContinuousLinearMap.comp (ContinuousLinearMap.snd ℝ
        (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1)))) :=
    (DifferentialGeometry.Topology.Manifold.hasMFDerivAt_halfSpaceOneCoordinate q.2).comp q
      (hasMFDerivAt_snd q)
  have h2 : HasMFDerivAt halfCollarModel 𝓘(ℝ, ℝ) (fun q : CuspHalfSpace => q.2.val 0 - c) q
      (Tq.toContinuousLinearMap.comp (ContinuousLinearMap.snd ℝ
        (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1)))) := by
    have h5 := h1.sub (hasMFDerivAt_const c q)
    exact h5.congr_mfderiv (sub_zero _)
  rw [h2.mfderiv]
  intro h
  have h3 := congrArg (fun L : ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) ×
      EuclideanSpace ℝ (Fin 1)) →L[ℝ] ℝ => L ((0, 0), EuclideanSpace.single 0 1)) h
  have h4 : Tq (EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) = 1 := by simp [Tq]
  change Tq (EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) = 0 at h3
  rw [h4] at h3
  exact one_ne_zero h3

theorem deepHeight_regular_CPA2 (hclosed : ∀ i, IsClosed (range (T.cuspMap i))) {b : ℝ}
    (hb : 2 ≤ b) (p : H.Carrier) (hp : deepHeight_CPA2 T b p = 0) :
    mfderiv (𝓡 3) 𝓘(ℝ, ℝ) (deepHeight_CPA2 T b) p ≠ 0 := by
  obtain ⟨i, q, hqb, rfl⟩ := (deepHeight_eq_zero_iff_CPA2 T (by linarith) p).mp hp
  have hq0 : 0 < q.2.val 0 := by rw [hqb]; linarith
  let d := cuspChart_CPA2 T i
  have hqs : q ∈ d.source := by rw [cuspChart_source_CPA2]; exact hq0
  have hf : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (deepHeight_CPA2 T b) :=
    contMDiff_deepHeight_CPA2 T hclosed b
  have hdq : d q = T.cuspMap i q := cuspChart_apply_CPA2 T i q
  have hmd : MDifferentiableAt halfCollarModel (𝓡 3) d q :=
    ((d.contMDiffOn.contMDiffAt (d.open_source.mem_nhds hqs)).mdifferentiableAt (by simp))
  have hmf : MDifferentiableAt (𝓡 3) 𝓘(ℝ, ℝ) (deepHeight_CPA2 T b) (d q) :=
    (hf (d q)).mdifferentiableAt (by simp)
  have hev : (deepHeight_CPA2 T b ∘ d) =ᶠ[𝓝 q] fun q : CuspHalfSpace => q.2.val 0 - b := by
    have hopen : IsOpen {q' : CuspHalfSpace | 1 < q'.2.val 0} :=
      isOpen_lt continuous_const
        ((EuclideanSpace.proj 0).continuous.comp (continuous_subtype_val.comp continuous_snd))
    filter_upwards [hopen.mem_nhds (show 1 < q.2.val 0 by rw [hqb]; linarith)] with q' hq'
    have hq'0 : 0 < q'.2.val 0 := by linarith [show 1 < q'.2.val 0 from hq']
    change deepHeight_CPA2 T b (d q') = _
    rw [cuspChart_apply_CPA2, deepHeight_cuspMap_CPA2 T b i hq'0,
      lam_eq_CPA2 (le_of_lt (show 1 < q'.2.val 0 from hq'))]
  intro hz
  apply mfderiv_height_ne_zero_CPA2 b q
  have hz' : mfderiv (𝓡 3) 𝓘(ℝ, ℝ) (deepHeight_CPA2 T b) (d q) = 0 := by
    rw [hdq]; exact hz
  have hcomp : mfderiv halfCollarModel 𝓘(ℝ, ℝ) (deepHeight_CPA2 T b ∘ d) q =
      (mfderiv (𝓡 3) 𝓘(ℝ, ℝ) (deepHeight_CPA2 T b) (d q)).comp
        (mfderiv halfCollarModel (𝓡 3) d q) := mfderiv_comp q hmf hmd
  have hmeq : mfderiv halfCollarModel 𝓘(ℝ, ℝ) (fun q : CuspHalfSpace => q.2.val 0 - b) q =
      mfderiv halfCollarModel 𝓘(ℝ, ℝ) (deepHeight_CPA2 T b ∘ d) q := hev.symm.mfderiv_eq
  rw [hmeq, hcomp, hz', ContinuousLinearMap.zero_comp]
  rfl

end GC.LongTime.CuspP1
