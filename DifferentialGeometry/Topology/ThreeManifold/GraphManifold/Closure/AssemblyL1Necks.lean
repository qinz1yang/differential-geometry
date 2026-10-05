import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1NecksRim
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1NecksOrientationHandle
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1NecksFlip
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1NecksSlices
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1WSideRimProduct

/-!
# Chapter-14 assembly, item L1, G3b: the necks of a ball–handle cycle (T1′)

Lane ASM-L1e3, group G2. **T1′** `BallHandleCycle.exists_necks_of_rimProduct` (frozen statement of
`build-logs/scratch/ASM-L1b/Shortcut.lean`, verbatim; the stub of `build-logs/scratch/ASM-L1b3/Cycle.lean`):
under the rim-product clause and with the balls in the interior of `W`, every rim `(k, b)` of the
cycle has a neck `N k b` at scale `ε = 1/8` with the ball / handle / union / fillet clauses, the
targets pairwise disjoint, the handle sides in product form, and the ball signs of consecutive
necks opposite.

Proof from:
* E1 `BallHandleCycle.rimHeight_lt` and E6 (`exists_pairwise_disjoint_open_nhds` on the compact,
  pairwise disjoint rim slices), `AssemblyL1NecksSlices.lean`;
* E2 `BallHandleCycle.exists_rimNeck` (one rim, inside the open neighbourhood of its slice),
  `AssemblyL1NecksRim.lean`;
* E3 flips `flipNeck`, `neckPreservesAt_flipNeck_iff`, `exists_linearIsometryEquiv_det_neg`,
  `AssemblyL1NecksFlip.lean`: every neck is flipped so that it preserves the orientation iff
  `b = false`;
* E4 `neckPreservesAt_iff_det_mul_neg` and E5 `PieceEmbedding.neckPreservesAt_iff_ballNeckDetAmb`
  (lane ASM-L1d, `AssemblyL1NecksOrientation*.lean`) turn the orientation behaviour into the
  determinant clause and the ball-sign clause.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

local instance ballCharts_ASML1e3N : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 2

local instance ballSmooth_ASML1e3N : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 2

local instance diskCharts_ASML1e3N : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

local instance diskSmooth_ASML1e3N : IsManifold (𝓡∂ 2) ∞ (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 1

/-- **T1′ (necks, under the rim-product clause)** — frozen text of
`build-logs/scratch/ASM-L1b/Shortcut.lean`, VERBATIM. -/
theorem BallHandleCycle.exists_necks_of_rimProduct {W : CompactCarrier.{u}} (C : BallHandleCycle W)
    (hprod : C.RimProduct) (hint : ∀ k, range (C.ball k).map ⊆ (W.interior : Set W.Carrier)) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 8 ∧
    ∃ N : Fin C.len → Bool → PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model
        (EuclideanSpace ℝ (Fin 2) × ℝ) W.Carrier ∞,
      (∀ k b, closedNeckDomain ε ⊆ (N k b).source) ∧
      (∀ k b k' b', (k, b) ≠ (k', b') → Disjoint (N k b).target (N k' b').target) ∧
      (∀ k b {q}, q ∈ (N k b).source →
        (N k b q ∈ range (C.ball (rimBall C.len k b)).map ↔ q.2 ≤ 0)) ∧
      (∀ k b {q}, q ∈ (N k b).source →
        (N k b q ∈ range (C.handle k).map ↔ (0 ≤ q.2 ∧ ‖q.1‖ ≤ 1))) ∧
      (∀ k b {q}, q ∈ neckDomain ε → (N k b q ∈ range C.union.map ↔ neckRounding ε q ≤ 0)) ∧
      (∀ k b, (N k b).target ∩ ((⋃ j, range (C.ball j).map) ∪ ⋃ j, range (C.handle j).map) ⊆
        range (C.ball (rimBall C.len k b)).map ∪ range (C.handle k).map) ∧
      (∀ k b, C.fillet k b ⊆ N k b '' {q | q ∈ neckDomain ε ∧ neckRounding ε q ≤ 0}) ∧
      (∀ k, ∃ A : Bool → EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2),
        LinearMap.det (A false).toLinearMap = LinearMap.det (A true).toLinearMap ∧
        ∃ P T : Bool → ℝ → ℝ, (∀ b, ContDiff ℝ ∞ (P b)) ∧ (∀ b, ContDiff ℝ ∞ (T b)) ∧
          (∀ b, P b 1 = 1) ∧ (∀ b s, 0 ≤ s → s ≤ 1 → 0 < P b s) ∧
          (∀ b r, 0 ≤ r → r ≤ 1 → 0 < deriv (fun r : ℝ => r * P b (r ^ 2)) r) ∧
          (∀ b, T b 0 = 0) ∧ (∀ b s, 0 ≤ s → s ≤ 2 * ε → 0 < deriv (T b) s) ∧
          T false (2 * ε) < 1 - T true (2 * ε) ∧
          ∀ b (z : ClosedCell 2) (τ : ℝ) (w : ClosedCell 2) (t : Icc (0 : ℝ) 1),
            0 ≤ τ → τ < 2 * ε →
            (w : EuclideanSpace ℝ (Fin 2)) =
              A b (P b (‖(z : EuclideanSpace ℝ (Fin 2))‖ ^ 2) • z) →
            (t : ℝ) = endCoord b (T b τ) →
            N k b ((z : EuclideanSpace ℝ (Fin 2)), τ) = (C.handle k).map (w, t)) ∧
      (∀ k x₀ x₁, (C.ball (finRotate C.len k)).map ((C.ballModel _).symm x₀) =
          N (finRotate C.len k) false 0 →
        (C.ball (finRotate C.len k)).map ((C.ballModel _).symm x₁) = N k true 0 →
        ballNeckDetAmb (C.ball (finRotate C.len k)) (C.ballModel _) x₀
          (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model (N (finRotate C.len k) false) 0) *
        ballNeckDetAmb (C.ball (finRotate C.len k)) (C.ballModel _) x₁
          (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model (N k true) 0) < 0) := by
  classical
  have hprod' : ∀ k b, RimProductAt (C.rimChart k b) (C.handle k) b := hprod
  choose a ha ha' A ρ σ hρ hσ hρ0 hσ0 hρd hσd heq using hprod'
  obtain ⟨O, hO, hKO, hOd⟩ := exists_pairwise_disjoint_open_nhds
    (K := fun p : Fin C.len × Bool => C.rimSlice p.1 p.2)
    (fun p => C.isCompact_rimSlice p.1 p.2) (fun p p' hpp' => C.disjoint_rimSlice hpp')
  -- the separation of the heights of the two ends of a handle
  have hsep : ∀ k, ∀ y ∈ Ico 0 (a k false), ∀ y' ∈ Ico 0 (a k true),
      σ k false y < 1 - σ k true y' := fun k y hy y' hy' =>
    C.rimHeight_lt k (ha k false) (ha' k false) (ha k true) (ha' k true) (A k false) (A k true)
      (hσ k false) (hσ k true) (hρ0 k false) (hρ0 k true) (hσ0 k false) (hσ0 k true)
      (hσd k false) (hσd k true) (heq k false) (heq k true) hy hy'
  have h0mem : ∀ k b, (0 : ℝ) ∈ Ico 0 (a k b) := fun k b => ⟨le_rfl, by linarith [ha k b]⟩
  have hσlt : ∀ k b, ∀ y ∈ Ico 0 (a k b), σ k b y < 1 := by
    intro k b y hy
    cases b
    · have h := hsep k y hy 0 (h0mem k true)
      rw [hσ0 k true] at h
      linarith
    · have h := hsep k 0 (h0mem k false) y hy
      rw [hσ0 k false] at h
      linarith
  have hE2 := fun k b => C.exists_rimNeck hint k b (ha k b) (ha' k b) (A k b) (hρ k b) (hσ k b)
    (hρ0 k b) (hσ0 k b) (hρd k b) (hσd k b) (hσlt k b) (heq k b) (hO (k, b)) (hKO (k, b))
  choose ε' hε' N₀ hsrc hball hhandle hNO hnotball hquad hheight hunion hfillet P T hP hT hP1
    hPpos hPmono hT0 hTd hTσ hprodN using hE2
  have hT1 : ∀ k b, T k b (2 * (1 / 8)) < 1 := by
    intro k b
    obtain ⟨y, hy, hyT⟩ := hTσ k b
    rw [← hyT]
    exact hσlt k b y hy
  -- the flips
  obtain ⟨R, hR⟩ := exists_linearIsometryEquiv_det_neg
  let F : Fin C.len → Bool → EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) :=
    fun k b => if (NeckPreservesAt (N₀ k b) 0 ↔ b = false) then LinearIsometryEquiv.refl ℝ _
      else R
  let N : Fin C.len → Bool → PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model
      (EuclideanSpace ℝ (Fin 2) × ℝ) W.Carrier ∞ := fun k b => flipNeck (N₀ k b) (F k b)
  have hε'pos : ∀ k b, 0 < ε' k b := fun k b => by linarith [hε' k b]
  have hNsrc : ∀ k b, (N k b).source = neckDomain (ε' k b) := fun k b =>
    flipNeck_source _ _ (hsrc k b)
  have hNtgt : ∀ k b, (N k b).target = (N₀ k b).target := fun k b =>
    flipNeck_target _ _
  have hNapp : ∀ k b q, N k b q = N₀ k b ((F k b) q.1, q.2) := fun k b q =>
    flipNeck_apply _ _ q
  have hdom : ∀ (G : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2)) (ε₀ : ℝ)
      (q : EuclideanSpace ℝ (Fin 2) × ℝ), (G q.1, q.2) ∈ neckDomain ε₀ ↔ q ∈ neckDomain ε₀ := by
    intro G ε₀ q
    simp only [neckDomain, mem_ofPred_eq, LinearIsometryEquiv.norm_map]
  have hround : ∀ (G : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2)) (ε₀ : ℝ)
      (q : EuclideanSpace ℝ (Fin 2) × ℝ), neckRounding ε₀ (G q.1, q.2) = neckRounding ε₀ q := by
    intro G ε₀ q
    simp only [neckRounding, LinearIsometryEquiv.norm_map]
  have hor : ∀ k b, NeckPreservesAt (N k b) 0 ↔ b = false := by
    intro k b
    change NeckPreservesAt (flipNeck (N₀ k b) (F k b)) 0 ↔ b = false
    rw [neckPreservesAt_flipNeck_iff (hε'pos k b) (hsrc k b)]
    by_cases h : (NeckPreservesAt (N₀ k b) 0 ↔ b = false)
    · have hF : F k b = LinearIsometryEquiv.refl ℝ _ := ite_eq_left h
      rw [hF]
      have h1 : LinearMap.det (LinearIsometryEquiv.refl ℝ
          (EuclideanSpace ℝ (Fin 2))).toLinearMap = 1 := LinearMap.det_id
      rw [h1]
      simp only [zero_lt_one, iff_true]
      exact h
    · have hF : F k b = R := ite_eq_right h
      rw [hF]
      have h2 : ¬ (0 < LinearMap.det R.toLinearMap) := not_lt.mpr hR.le
      simp only [h2, iff_false]
      tauto
  have hsrc_iff : ∀ k b (q : EuclideanSpace ℝ (Fin 2) × ℝ), q ∈ (N k b).source →
      ((F k b) q.1, q.2) ∈ (N₀ k b).source := by
    intro k b q hq
    rw [hsrc, hdom]
    rwa [hNsrc] at hq
  have hpre : ∀ k b {z : W.Carrier}, z ∈ (N₀ k b).target →
      ∃ q, q ∈ (N₀ k b).source ∧ N₀ k b q = z := fun k b z hz =>
    ⟨(N₀ k b).symm z, (N₀ k b).map_target hz, (N₀ k b).right_inv hz⟩
  have hprodF : ∀ k b (z : ClosedCell 2) (τ : ℝ) (w : ClosedCell 2) (t : Icc (0 : ℝ) 1),
      0 ≤ τ → τ < 2 * (1 / 8) →
      (w : EuclideanSpace ℝ (Fin 2)) =
        ((F k b).trans (A k b)) (P k b (‖(z : EuclideanSpace ℝ (Fin 2))‖ ^ 2) • z) →
      (t : ℝ) = endCoord b (T k b τ) →
      N k b ((z : EuclideanSpace ℝ (Fin 2)), τ) = (C.handle k).map (w, t) := by
    intro k b z τ w t hτ hτ' hw ht
    rw [hNapp]
    let z' : ClosedCell 2 := ⟨F k b z, by rw [LinearIsometryEquiv.norm_map]; exact z.2⟩
    have := hprodN k b z' τ w t hτ hτ' ?_ ht
    · exact this
    · rw [hw]
      simp only [z', LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.norm_map, map_smul]
  -- the ball case of the disjointness
  have hballcase : ∀ k b k' b' (q q' : EuclideanSpace ℝ (Fin 2) × ℝ), (k, b) ≠ (k', b') →
      q ∈ (N₀ k b).source → q' ∈ (N₀ k' b').source → N₀ k' b' q' = N₀ k b q → q.2 ≤ 0 →
      False := by
    intro k b k' b' q q' hne hq hq' hqq' h0
    have hzO := hNO k b hq h0
    have hzB := (hball k b hq).mpr h0
    by_cases h0' : q'.2 ≤ 0
    · have hzO' := hNO k' b' hq' h0'
      rw [hqq'] at hzO'
      exact Set.disjoint_left.mp (hOd hne) hzO hzO'
    · apply hnotball k' b' hq' (not_le.mp h0')
      rw [hqq']
      exact mem_iUnion.mpr ⟨_, hzB⟩
  refine ⟨1 / 8, by norm_num, le_rfl, N, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the closed neck box
    intro k b q hq
    rw [hNsrc]
    have := hε' k b
    exact ⟨by linarith [hq.1], by linarith [hq.2]⟩
  · -- disjoint targets
    intro k b k' b' hne
    rw [Set.disjoint_left, hNtgt, hNtgt]
    intro z hz hz'
    obtain ⟨q, hq, rfl⟩ := hpre k b hz
    obtain ⟨q', hq', hqq'⟩ := hpre k' b' hz'
    by_cases h0 : q.2 ≤ 0
    · exact hballcase k b k' b' q q' hne hq hq' hqq' h0
    by_cases h0' : q'.2 ≤ 0
    · exact hballcase k' b' k b q' q (Ne.symm hne) hq' hq hqq'.symm h0'
    have hp : 0 < q.2 := not_le.mp h0
    have hp' : 0 < q'.2 := not_le.mp h0'
    by_cases h1 : ‖q.1‖ ≤ 1
    · have hzH := (hhandle k b hq).mpr ⟨hp.le, h1⟩
      by_cases h1' : ‖q'.1‖ ≤ 1
      · have hzH' := (hhandle k' b' hq').mpr ⟨hp'.le, h1'⟩
        rw [hqq'] at hzH'
        have hkk : k = k' := by
          by_contra hkk
          exact Set.disjoint_left.mp (C.handle_disjoint hkk) hzH hzH'
        subst hkk
        have hbb : b ≠ b' := fun hbb => hne (by rw [hbb])
        obtain ⟨w, t, ⟨s, ⟨y, hy, rfl⟩, hst⟩, hwt⟩ := hheight k b hq hp.le h1
        obtain ⟨w', t', ⟨s', ⟨y', hy', rfl⟩, hst'⟩, hwt'⟩ := hheight k b' hq' hp'.le h1'
        rw [hqq', hwt] at hwt'
        have htt0 := congrArg (fun r : ClosedCell 2 × Icc (0 : ℝ) 1 => (r.2 : ℝ))
          ((C.handle k).injective hwt')
        simp only at htt0
        have htt : endCoord b (σ k b y) = endCoord b' (σ k b' y') := by rw [hst, hst', htt0]
        cases b <;> cases b'
        · exact hbb rfl
        · have := hsep k y hy y' hy'
          simp only [endCoord, Bool.false_eq_true, ite_false, ite_true] at htt
          linarith
        · have := hsep k y' hy' y hy
          simp only [endCoord, Bool.false_eq_true, ite_false, ite_true] at htt
          linarith
        · exact hbb rfl
      · have hq'' := hquad k' b' hq' hp' (not_le.mp h1')
        rw [hqq'] at hq''
        exact hq''.2 (Or.inr (mem_iUnion.mpr ⟨k, hzH⟩))
    · have hq'' := hquad k b hq hp (not_le.mp h1)
      by_cases h1' : ‖q'.1‖ ≤ 1
      · have hzH' := (hhandle k' b' hq').mpr ⟨hp'.le, h1'⟩
        rw [hqq'] at hzH'
        exact hq''.2 (Or.inr (mem_iUnion.mpr ⟨k', hzH'⟩))
      · have hq''' := hquad k' b' hq' hp' (not_le.mp h1')
        rw [hqq'] at hq'''
        exact Set.disjoint_left.mp (C.rim_disjoint k b k' b' hne) hq''.1 hq'''.1
  · -- the ball side
    intro k b q hq
    rw [hNapp]
    exact hball k b (hsrc_iff k b q hq)
  · -- the handle side
    intro k b q hq
    rw [hNapp]
    have h := hhandle k b (hsrc_iff k b q hq)
    simp only [LinearIsometryEquiv.norm_map] at h
    exact h
  · -- the union
    intro k b q hq
    rw [hNapp, ← hround (F k b) (1 / 8) q]
    exact hunion k b ((hdom (F k b) (1 / 8) q).mpr hq)
  · -- the pieces
    rintro k b z ⟨hz, hzp⟩
    rw [hNtgt] at hz
    obtain ⟨q, hq, rfl⟩ := hpre k b hz
    by_cases h0 : q.2 ≤ 0
    · exact Or.inl ((hball k b hq).mpr h0)
    · by_cases h1 : ‖q.1‖ ≤ 1
      · exact Or.inr ((hhandle k b hq).mpr ⟨(not_le.mp h0).le, h1⟩)
      · exact ((hquad k b hq (not_le.mp h0) (not_le.mp h1)).2 hzp).elim
  · -- the fillets
    intro k b p hp
    obtain ⟨q, ⟨hq1, hq2⟩, rfl⟩ := hfillet k b hp
    refine ⟨((F k b).symm q.1, q.2), ⟨?_, ?_⟩, ?_⟩
    · rw [← hdom (F k b) (1 / 8)]
      simpa only [LinearIsometryEquiv.apply_symm_apply] using hq1
    · rw [← hround (F k b) (1 / 8)]
      simpa only [LinearIsometryEquiv.apply_symm_apply] using hq2
    · rw [hNapp]
      simp only [LinearIsometryEquiv.apply_symm_apply]
  · -- the handle product form
    intro k
    refine ⟨fun b => (F k b).trans (A k b), ?_, P k, T k, fun b => hP k b, fun b => hT k b,
      fun b => hP1 k b, fun b => hPpos k b, fun b => hPmono k b, fun b => hT0 k b,
      fun b => hTd k b, ?_, fun b => hprodF k b⟩
    · have hE4 := neckPreservesAt_iff_det_mul_neg (C.handle k) (N k false) (N k true)
        (δ := 2 * (1 / 8)) (by norm_num) (by linarith [hε' k false]) (by linarith [hε' k true])
        (hNsrc k false) (hNsrc k true) ((F k false).trans (A k false))
        ((F k true).trans (A k true)) (P k false) (P k true) (T k false) (T k true)
        (hP k false) (hP k true) (hT k false) (hT k true)
        (hPpos k false) (hPpos k true) (hT0 k false)
        (hT0 k true) (hTd k false) (hTd k true) (hT1 k false) (hT1 k true) (hprodF k false)
        (hprodF k true)
      have hL : ¬ (NeckPreservesAt (N k false) 0 ↔ NeckPreservesAt (N k true) 0) := by
        rw [hor, hor]
        simp
      have hnn := not_lt.mp (fun h => hL (hE4.mpr h))
      rcases det_linearIsometryEquiv_eq_one_or_neg_one ((F k false).trans (A k false)) with
        h1 | h1 <;>
      rcases det_linearIsometryEquiv_eq_one_or_neg_one ((F k true).trans (A k true)) with
        h2 | h2 <;>
      simp only [h1, h2] at hnn ⊢ <;> norm_num at hnn
    · obtain ⟨y, hy, hyT⟩ := hTσ k false
      obtain ⟨y', hy', hyT'⟩ := hTσ k true
      rw [← hyT, ← hyT']
      exact hsep k y hy y' hy'
  · -- the ball signs
    intro k x₀ x₁ hx₀ hx₁
    have h0 : ∀ k b, (0 : EuclideanSpace ℝ (Fin 2) × ℝ) ∈ (N k b).source := by
      intro k b
      rw [hNsrc]
      have := hε'pos k b
      refine ⟨?_, ?_⟩ <;> simp <;> linarith
    have hE5 := PieceEmbedding.neckPreservesAt_iff_ballNeckDetAmb (C.ball (finRotate C.len k))
      (C.ballModel _) (h0 _ false) (h0 k true) x₀ x₁ hx₀ hx₁
    have hL : ¬ (NeckPreservesAt (N (finRotate C.len k) false) 0 ↔
        NeckPreservesAt (N k true) 0) := by
      rw [hor, hor]
      simp
    have hle := not_lt.mp (fun h => hL (hE5.mpr h))
    have hne := mul_ne_zero
      (ballNeckDetAmb_ne_zero (C.ball (finRotate C.len k)) (C.ballModel _) x₀ _
        (h0 (finRotate C.len k) false))
      (ballNeckDetAmb_ne_zero (C.ball (finRotate C.len k)) (C.ballModel _) x₁ _ (h0 k true))
    exact lt_of_le_of_ne hle hne

end GC.GraphManifold.Assembly
