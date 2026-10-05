import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1NecksCollar
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1NecksMasterApplications
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1NeckBox
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1NecksBallChartApplications

/-!
# Chapter-14 assembly, item L1, G3b / T1′: the neck of one rim (E2)

Lane ASM-L1e3, group G2. The neck of rim `(k, b)` of a ball–handle cycle, at scale `ε = 1/8`, is
the master bicollar (E2b, `AssemblyL1NecksMaster.lean`, lane ASM-L1m) read with a compressed height:
`N (z, τ) = masterMap … (z, g (8 τ))` on `neckDomain (9/64)`, where
* the ball chart `Bh` of the ball at the rim is `BallHandleCycle.exists_ballCharts` (from `hint`);
* the radial profile `P` of the handle side is `exists_handleRadialProfile`;
* the ball-side collar `G` is E2a (`exists_ballSideCollar`, `AssemblyL1NecksCollar.lean`), whose
  hypotheses on the cycle are `BallHandleCycle.norm_eq_one_of_mem_endDisk`,
  `BallHandleCycle.endDisk_subset_ballChart_image`,
  `BallHandleCycle.eq_zero_or_eq_one_of_mem_ballChart_image`;
* the rim and height compressions are `exists_rimCompression`, `exists_heightCompression`;
* `isLocalDiffeomorphAt_neckHeight`: `(z, τ) ↦ (z, g (8 τ))` is a local diffeomorphism.

**E2** `BallHandleCycle.exists_rimNeck` (frozen statement of
`build-logs/scratch/ASM-L1e2/Targets.lean`, with `hσ1`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

local instance ballCharts_ASML1e3R : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 2

local instance ballSmooth_ASML1e3R : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 2

local instance diskCharts_ASML1e3R : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

local instance diskSmooth_ASML1e3R : IsManifold (𝓡∂ 2) ∞ (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 1

/-! ## The neck height coordinate -/

/-- `(z, τ) ↦ (z, g (8 τ))` is a local diffeomorphism for `g' > 0`. -/
theorem isLocalDiffeomorphAt_neckHeight {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hgd : ∀ y, 0 < deriv g y) (q : EuclideanSpace ℝ (Fin 2) × ℝ) :
    IsLocalDiffeomorphAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) ∞
      (Prod.map (id : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
        (fun τ : ℝ => g (8 * τ))) q := by
  have hF : ContDiff ℝ ∞ (fun τ : ℝ => g (8 * τ)) := hg.comp (contDiff_const.mul contDiff_id)
  have hc : ContDiff ℝ ∞ (Prod.map (id : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
      (fun τ : ℝ => g (8 * τ))) := contDiff_id.prodMap hF
  apply isLocalDiffeomorphAt_of_contDiffOn_of_bijective isOpen_univ (mem_univ q) hc.contDiffOn
  have hd1 : HasDerivAt (fun τ : ℝ => g (8 * τ)) (deriv g (8 * q.2) * 8) q.2 := by
    have hd : HasDerivAt g (deriv g (8 * q.2)) (8 * q.2) :=
      ((hg.differentiable (by simp)) _).hasDerivAt
    have hlin : HasDerivAt (fun τ : ℝ => 8 * τ) 8 q.2 := by
      simpa using (hasDerivAt_id q.2).const_mul 8
    exact hd.comp q.2 hlin
  have hD := (hasFDerivAt_id q.1).prodMap q hd1.hasFDerivAt
  rw [hD.fderiv]
  have hne : deriv g (8 * q.2) * 8 ≠ 0 := by
    have := hgd (8 * q.2)
    positivity
  exact (Prod.map_bijective).mpr ⟨Function.bijective_id, bijective_smulRight_one hne⟩

/-! ## Ball-chart facts of a cycle -/

/-- In a ball chart, the end disk of a handle lies on the unit sphere. -/
theorem BallHandleCycle.norm_eq_one_of_mem_endDisk {W : CompactCarrier.{u}}
    (C : BallHandleCycle W) (k : Fin C.len) (b : Bool)
    (Bh : PartialDiffeomorph (𝓡 3) W.model (EuclideanSpace ℝ (Fin 3)) W.Carrier ∞)
    (hBhsrc : Metric.closedBall 0 1 ⊆ Bh.source)
    (hBhball : ∀ x : ClosedCell 3, Bh x.val =
      (C.ball (rimBall C.len k b)).map ((C.ballModel _).symm x))
    {y : EuclideanSpace ℝ (Fin 3)} (hy : y ∈ Bh.source) (hyd : Bh y ∈ (C.handle k).endDisk b) :
    ‖y‖ = 1 := by
  have hb : Bh y ∈ (C.ball (rimBall C.len k b)).map ''
      (𝓡∂ 3).boundary (C.ball (rimBall C.len k b)).Piece := by
    cases b
    · exact C.start_face k hyd
    · exact C.end_face k hyd
  rw [image_boundary_eq_range_of_ball _ (C.ballModel _)] at hb
  obtain ⟨z, hz⟩ := hb
  have hz1 : ‖(z : EuclideanSpace ℝ (Fin 3))‖ = 1 := mem_sphere_zero_iff_norm.mp z.2
  have hz' : Bh (z : EuclideanSpace ℝ (Fin 3)) = Bh y := (hBhball ⟨z.1, hz1.le⟩).trans hz
  have h := Bh.toPartialEquiv.injOn (hBhsrc (mem_closedBall_zero_iff.mpr hz1.le)) hy hz'
  rw [← h]
  exact hz1

/-- In a ball chart, the end disk of a handle lies in the image of the closed unit ball. -/
theorem BallHandleCycle.endDisk_subset_ballChart_image {W : CompactCarrier.{u}}
    (C : BallHandleCycle W) (k : Fin C.len) (b : Bool)
    (Bh : PartialDiffeomorph (𝓡 3) W.model (EuclideanSpace ℝ (Fin 3)) W.Carrier ∞)
    (hBhball : ∀ x : ClosedCell 3, Bh x.val =
      (C.ball (rimBall C.len k b)).map ((C.ballModel _).symm x)) :
    (C.handle k).endDisk b ⊆ Bh '' Metric.closedBall 0 1 := by
  intro z hz
  obtain ⟨p, rfl⟩ := C.endDisk_subset_range_rimBall_master k b hz
  refine ⟨((C.ballModel _) p : EuclideanSpace ℝ (Fin 3)),
    mem_closedBall_zero_iff.mpr ((C.ballModel _) p).2, ?_⟩
  rw [hBhball, Diffeomorph.symm_apply_apply]

/-- A handle point in the closed unit ball of a ball chart is at an end of the handle. -/
theorem BallHandleCycle.eq_zero_or_eq_one_of_mem_ballChart_image {W : CompactCarrier.{u}}
    (C : BallHandleCycle W) (k : Fin C.len) (b : Bool)
    (Bh : PartialDiffeomorph (𝓡 3) W.model (EuclideanSpace ℝ (Fin 3)) W.Carrier ∞)
    (hBhball : ∀ x : ClosedCell 3, Bh x.val =
      (C.ball (rimBall C.len k b)).map ((C.ballModel _).symm x))
    (w : ClosedCell 2) (t : Icc (0 : ℝ) 1)
    (h : (C.handle k).map (w, t) ∈ Bh '' Metric.closedBall 0 1) :
    (t : ℝ) = 0 ∨ (t : ℝ) = 1 := by
  obtain ⟨y, hy, hyt⟩ := h
  have hmem : (C.handle k).map (w, t) ∈ range (C.ball (rimBall C.len k b)).map := by
    rw [← hyt]
    exact ballChart_mem_range_master _ (C.ballModel _) Bh hBhball (mem_closedBall_zero_iff.mp hy)
  by_contra hcon
  push Not at hcon
  exact C.handle_not_mem_ball_master k _ w (lt_of_le_of_ne t.2.1 (Ne.symm hcon.1))
    (lt_of_le_of_ne t.2.2 hcon.2) hmem

/-! ## E2: one rim -/

/-- **E2 (one rim).** -/
theorem BallHandleCycle.exists_rimNeck {W : CompactCarrier.{u}} (C : BallHandleCycle W)
    (hint : ∀ k, range (C.ball k).map ⊆ (W.interior : Set W.Carrier)) (k : Fin C.len) (b : Bool)
    {a : ℝ} (ha : 3 / 4 < a) (ha' : a ≤ 2)
    (A : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    {ρ σ : ℝ → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hσ : ContDiff ℝ ∞ σ) (hρ0 : ρ 0 = 1) (hσ0 : σ 0 = 0)
    (hρd : ∀ x ∈ Ioc (-a) 0, 0 < ρ x ∧ 0 < deriv ρ x) (hσd : ∀ y ∈ Ico 0 a, 0 < deriv σ y)
    (hσ1 : ∀ y ∈ Ico 0 a, σ y < 1)
    (heq : ∀ (θ : Circle) (x y : ℝ) (w : ClosedCell 2) (t : Icc (0 : ℝ) 1),
      -a < x → x ≤ 0 → 0 ≤ y → y < a →
      (w : EuclideanSpace ℝ (Fin 2)) = ρ x • A (planeOfCircle θ) →
      (t : ℝ) = endCoord b (σ y) → C.rimChart k b (θ, (x, y)) = (C.handle k).map (w, t))
    {O : Set W.Carrier} (hO : IsOpen O) (hslice : C.rimSlice k b ⊆ O) :
    ∃ ε' : ℝ, 1 / 8 < ε' ∧
    ∃ N : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model
        (EuclideanSpace ℝ (Fin 2) × ℝ) W.Carrier ∞,
      N.source = neckDomain ε' ∧
      (∀ {q}, q ∈ N.source → (N q ∈ range (C.ball (rimBall C.len k b)).map ↔ q.2 ≤ 0)) ∧
      (∀ {q}, q ∈ N.source → (N q ∈ range (C.handle k).map ↔ (0 ≤ q.2 ∧ ‖q.1‖ ≤ 1))) ∧
      (∀ {q}, q ∈ N.source → q.2 ≤ 0 → N q ∈ O) ∧
      (∀ {q}, q ∈ N.source → 0 < q.2 → N q ∉ ⋃ j, range (C.ball j).map) ∧
      (∀ {q}, q ∈ N.source → 0 < q.2 → 1 < ‖q.1‖ → N q ∈ (C.rimChart k b).target ∧
        N q ∉ (⋃ j, range (C.ball j).map) ∪ ⋃ j, range (C.handle j).map) ∧
      (∀ {q}, q ∈ N.source → 0 ≤ q.2 → ‖q.1‖ ≤ 1 →
        ∃ (w : ClosedCell 2) (t : Icc (0 : ℝ) 1), (t : ℝ) ∈ endCoord b '' (σ '' Ico 0 a) ∧
          N q = (C.handle k).map (w, t)) ∧
      (∀ {q}, q ∈ neckDomain (1 / 8) →
        (N q ∈ range C.union.map ↔ neckRounding (1 / 8) q ≤ 0)) ∧
      C.fillet k b ⊆ N '' {q | q ∈ neckDomain (1 / 8) ∧ neckRounding (1 / 8) q ≤ 0} ∧
      ∃ P T : ℝ → ℝ, ContDiff ℝ ∞ P ∧ ContDiff ℝ ∞ T ∧ P 1 = 1 ∧
        (∀ s, 0 ≤ s → s ≤ 1 → 0 < P s) ∧
        (∀ r, 0 ≤ r → r ≤ 1 → 0 < deriv (fun r : ℝ => r * P (r ^ 2)) r) ∧ T 0 = 0 ∧
        (∀ s, 0 ≤ s → s ≤ 2 * (1 / 8) → 0 < deriv T s) ∧ T (2 * (1 / 8)) ∈ σ '' Ico 0 a ∧
        ∀ (z : ClosedCell 2) (τ : ℝ) (w : ClosedCell 2) (t : Icc (0 : ℝ) 1),
          0 ≤ τ → τ < 2 * (1 / 8) →
          (w : EuclideanSpace ℝ (Fin 2)) = A (P (‖(z : EuclideanSpace ℝ (Fin 2))‖ ^ 2) • z) →
          (t : ℝ) = endCoord b (T τ) →
          N ((z : EuclideanSpace ℝ (Fin 2)), τ) = (C.handle k).map (w, t) := by
  /- the ball chart of the ball at the rim -/
  obtain ⟨φ, hφ⟩ := C.exists_ballCharts hint
  obtain ⟨hBhsrc, hBhball, -⟩ := hφ (rimBall C.len k b)
  /- the radial profile, the collar (E2a), the rim compression -/
  obtain ⟨P, hP, hP1, hPpos, hPmono, hPρ⟩ := exists_handleRadialProfile ha hρ hρ0 hρd
  obtain ⟨η, hη, G, hG, hGsrc, hGd, hGH, hGχ, hGball⟩ :=
    exists_ballSideCollar (C.handle k) b (C.rimChart k b) (C.rim_source k b)
      (φ (rimBall C.len k b)) hBhsrc
      (fun hy hyd => C.norm_eq_one_of_mem_endDisk k b _ hBhsrc hBhball hy hyd)
      (C.endDisk_subset_ballChart_image k b _ hBhball)
      (C.eq_zero_or_eq_one_of_mem_ballChart_image k b _ hBhball) ha A hσ hσ0 hσd heq hP hP1
      hPpos hPmono hPρ
  obtain ⟨f, hf, hfmono, hfd, hfid, hfb⟩ := exists_rimCompression
  /- the master bicollar (E2b) -/
  have hY : 3 / 4 < (3 / 4 + a) / 2 := by linarith
  have hYa : (3 / 4 + a) / 2 < a := by linarith
  obtain ⟨η', hη', -, hLD, hinj, hball, hhandle, hOm, hnotball, hquad, hprodM⟩ :=
    C.exists_masterDomain k b ha ha' A hσ hσ0 hσd hσ1 heq hP hP1 hPpos hPmono hPρ hf hfd hfid
      hfb (φ (rimBall C.len k b)) hBhsrc hBhball hη G hG hGsrc hGd hGH hGχ hGball hO hslice hY
      hYa
  /- the height compression and the neck -/
  obtain ⟨g, hg, hgmono, hgd, hgid, hgb⟩ := exists_heightCompression hη' hY
  have hg0 : g 0 = 0 := hgid 0 ⟨le_rfl, by norm_num⟩
  have hgle : ∀ y, g y ≤ 0 ↔ y ≤ 0 := fun y => by
    have h := hgmono.le_iff_le (a := y) (b := 0)
    rwa [hg0] at h
  have hglt : ∀ y, 0 < g y ↔ 0 < y := fun y => by
    have h := hgmono.lt_iff_lt (a := 0) (b := y)
    rwa [hg0] at h
  have hgnn : ∀ y, 0 ≤ y → 0 ≤ g y := fun y hy => by
    rw [← hg0]
    exact hgmono.monotone hy
  let M := masterMap (C.rimChart k b) (C.handle k) b (φ (rimBall C.len k b)) G A P σ f
  let κ : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 2) × ℝ :=
    Prod.map id (fun τ : ℝ => g (8 * τ))
  have hκmem : ∀ q ∈ neckDomain (9 / 64), κ q ∈ masterDomain η' ((3 / 4 + a) / 2) := by
    intro q hq
    refine ⟨?_, (hgb _).1, (hgb _).2⟩
    change ‖q.1‖ < 1 + 9 / 32
    have := hq.1
    linarith
  have hLDn : IsLocalDiffeomorphOn 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model ∞ (M ∘ κ)
      (neckDomain (9 / 64)) := by
    intro q
    exact (isLocalDiffeomorphAt_neckHeight hg hgd q).comp W.model W.Carrier
      (hLD ⟨κ q, hκmem q q.2⟩)
  have hinjn : InjOn (M ∘ κ) (neckDomain (9 / 64)) := by
    intro q hq q' hq' h
    have h1 := hinj (hκmem q hq) (hκmem q' hq') h
    have h2 : (κ q).1 = (κ q').1 := congrArg Prod.fst h1
    have h3 : (κ q).2 = (κ q').2 := congrArg Prod.snd h1
    change g (8 * q.2) = g (8 * q'.2) at h3
    have h4 : q.2 = q'.2 := by
      have := hgmono.injective h3
      linarith
    exact Prod.ext h2 h4
  obtain ⟨N, hsrc, -, hfun⟩ := hLDn.exists_partialDiffeomorph_of_injOn (isOpen_neckDomain _)
    ⟨0, by
      refine ⟨?_, ?_⟩ <;> norm_num⟩ hinjn
  have hN : ∀ q, N q = M (q.1, g (8 * q.2)) := fun q => congrFun hfun q
  have hmem : ∀ {q}, q ∈ N.source → (q.1, g (8 * q.2)) ∈ masterDomain η' ((3 / 4 + a) / 2) :=
    fun hq => hκmem _ (hsrc ▸ hq)
  have hσmono := strictMonoOn_Ico_master hσ hσd
  have h0a : (0 : ℝ) ∈ Ico 0 a := ⟨le_rfl, by linarith⟩
  have hgIco : ∀ y, 0 ≤ y → g y ∈ Ico 0 a := fun y hy =>
    ⟨hgnn y hy, lt_trans (hgb y).2 hYa⟩
  have hσnn : ∀ y, 0 ≤ y → 0 ≤ σ (g y) := by
    intro y hy
    rw [← hσ0]
    exact hσmono.monotoneOn h0a (hgIco y hy) (hgnn y hy)
  have hfid' : ∀ x ∈ Icc (0 : ℝ) (3 / 4), f x = x := fun x hx =>
    hfid x ⟨by linarith [hx.1], hx.2⟩
  refine ⟨9 / 64, by norm_num, N, hsrc, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the ball side
    intro q hq
    rw [hN, hball _ (hmem hq)]
    exact hgle _ |>.trans (by constructor <;> intro h <;> linarith)
  · -- the handle side
    intro q hq
    rw [hN, hhandle _ (hmem hq)]
    change (0 ≤ g (8 * q.2) ∧ ‖q.1‖ ≤ 1) ↔ (0 ≤ q.2 ∧ ‖q.1‖ ≤ 1)
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      by_contra hneg
      push Not at hneg
      have := (hglt (8 * q.2)).not.mpr (by linarith)
      have h3 : g (8 * q.2) < 0 := by
        rcases lt_or_eq_of_le ((hgle (8 * q.2)).mpr (by linarith)) with h | h
        · exact h
        · exact absurd (hgmono.injective (h.trans hg0.symm)) (by linarith)
      linarith
    · rintro ⟨h1, h2⟩
      exact ⟨hgnn _ (by linarith), h2⟩
  · -- the ball side lies in `O`
    intro q hq h0
    rw [hN]
    exact hOm _ (hmem hq) ((hgle _).mpr (by linarith))
  · -- the handle side meets no ball
    intro q hq h0
    rw [hN]
    exact hnotball _ (hmem hq) ((hglt _).mpr (by linarith))
  · -- the quadrant
    intro q hq h0 h1
    rw [hN]
    exact hquad _ (hmem hq) ((hglt _).mpr (by linarith)) h1
  · -- the handle heights
    intro q hq h0 h1
    have hs := hgIco (8 * q.2) (by linarith)
    have hσs : σ (g (8 * q.2)) ∈ Icc (0 : ℝ) 1 :=
      ⟨hσnn _ (by linarith), (hσ1 _ hs).le⟩
    refine ⟨diskClamp (handleDiskMap A P q.1),
      ⟨endCoord b (σ (g (8 * q.2))), endCoord_mem_Icc_of_mem b hσs⟩,
      ⟨_, ⟨_, hs, rfl⟩, rfl⟩, ?_⟩
    rw [hN]
    exact hprodM _ (hmem hq) (hgnn _ (by linarith)) h1 _ _
      (diskClamp_val (norm_handleDiskMap_le_one A hP hP1 hPpos hPmono h1)) rfl
  · -- the union
    intro q hq
    have hq' : q ∈ N.source := by
      rw [hsrc]
      exact ⟨by have := hq.1; linarith, by have := hq.2; linarith⟩
    have hround : neckRounding (1 / 8) q = standardRimRounding ((‖q.1‖ - 1) / (1 / 8),
        q.2 / (1 / 8)) := rfl
    by_cases h0 : q.2 ≤ 0
    · have hB := (hball _ (hmem hq')).mpr ((hgle _).mpr (by linarith))
      rw [hN]
      refine ⟨fun _ => ?_, fun _ => C.ball_subset_union _ hB⟩
      rw [hround]
      apply standardRimRounding_nonpos_of
      left
      change q.2 / (1 / 8) ≤ 0
      exact div_nonpos_of_nonpos_of_nonneg h0 (by norm_num)
    push Not at h0
    by_cases h1 : ‖q.1‖ ≤ 1
    · have hH := (hhandle _ (hmem hq')).mpr ⟨hgnn _ (by linarith), h1⟩
      rw [hN]
      refine ⟨fun _ => ?_, fun _ => C.handle_subset_union _ hH⟩
      rw [hround]
      apply standardRimRounding_nonpos_of
      right
      change (‖q.1‖ - 1) / (1 / 8) ≤ 0
      exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by norm_num)
    · push Not at h1
      have hMχ : M (q.1, g (8 * q.2)) = C.rimChart k b
          (planeUnit q.1, (f (8 * (‖q.1‖ - 1)), g (8 * q.2))) :=
        masterMap_of_lt _ _ _ _ _ _ _ _ _ (show 59 / 64 < ‖q.1‖ by linarith)
      have hsrcχ : (planeUnit q.1, (f (8 * (‖q.1‖ - 1)), g (8 * q.2))) ∈
          (C.rimChart k b).source := by
        rw [C.rim_source]
        refine ⟨?_, ?_⟩
        · change |f (8 * (‖q.1‖ - 1))| < 2
          rw [abs_lt]
          constructor <;> linarith [(hfb (8 * (‖q.1‖ - 1))).1, (hfb (8 * (‖q.1‖ - 1))).2]
        · change |g (8 * q.2)| < 2
          rw [abs_lt]
          constructor <;> linarith [(hglt (8 * q.2)).mpr (by linarith), (hgb (8 * q.2)).2]
      rw [hN, hMχ, C.union_rim k b hsrcχ]
      exact neckRounding_compress_nonpos_iff hfmono hgmono hfid' hgid
  · -- the fillet
    rintro z ⟨p, ⟨hx, hy, -, hψ⟩, rfl⟩
    have hband := band_of_standardRimRounding_nonpos p.2 hx hy hψ
    have hnorm : ‖(1 + p.2.1 / 8) • planeOfCircle p.1‖ = 1 + p.2.1 / 8 := by
      rw [norm_smul, norm_planeOfCircle_eq_one, mul_one, Real.norm_of_nonneg (by linarith)]
    refine ⟨((1 + p.2.1 / 8) • planeOfCircle p.1, p.2.2 / 8), ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · change ‖(1 + p.2.1 / 8) • planeOfCircle p.1‖ < 1 + 2 * (1 / 8)
      rw [hnorm]
      linarith
    · change |p.2.2 / 8| < 2 * (1 / 8)
      rw [abs_lt]
      constructor <;> linarith
    · change standardRimRounding ((‖(1 + p.2.1 / 8) • planeOfCircle p.1‖ - 1) / (1 / 8),
        p.2.2 / 8 / (1 / 8)) ≤ 0
      rw [hnorm]
      have h1 : (1 + p.2.1 / 8 - 1) / (1 / 8 : ℝ) = p.2.1 := by ring
      have h2 : p.2.2 / 8 / (1 / 8 : ℝ) = p.2.2 := by ring
      rw [h1, h2]
      exact hψ
    · rw [hN]
      have hgy : g (8 * (p.2.2 / 8)) = p.2.2 := by
        rw [show 8 * (p.2.2 / 8) = p.2.2 by ring]
        exact hgid _ ⟨hy.le, by linarith⟩
      have h59 : 59 / 64 < ‖((1 + p.2.1 / 8) • planeOfCircle p.1, p.2.2 / 8).1‖ := by
        change 59 / 64 < ‖(1 + p.2.1 / 8) • planeOfCircle p.1‖
        rw [hnorm]
        linarith
      have hMeq : M ((1 + p.2.1 / 8) • planeOfCircle p.1, p.2.2) = C.rimChart k b
          (planeUnit ((1 + p.2.1 / 8) • planeOfCircle p.1),
            (f (8 * (‖(1 + p.2.1 / 8) • planeOfCircle p.1‖ - 1)), p.2.2)) :=
        masterMap_of_lt _ _ _ _ _ _ _ _ _ h59
      change M ((1 + p.2.1 / 8) • planeOfCircle p.1, g (8 * (p.2.2 / 8))) = _
      rw [hgy, hMeq]
      rw [hnorm, planeUnit_smul_planeOfCircle (by linarith),
        show 8 * (1 + p.2.1 / 8 - 1) = p.2.1 by ring, hfid' _ ⟨hx.le, by linarith⟩]
  · -- the product form
    have hT : ContDiff ℝ ∞ (fun τ : ℝ => σ (g (8 * τ))) :=
      hσ.comp (hg.comp (contDiff_const.mul contDiff_id))
    refine ⟨P, fun τ => σ (g (8 * τ)), hP, hT, hP1, hPpos, hPmono, ?_, ?_,
      ⟨g (8 * (2 * (1 / 8))), hgIco _ (by norm_num), rfl⟩, ?_⟩
    · change σ (g (8 * 0)) = 0
      rw [mul_zero, hg0, hσ0]
    · intro s hs0 hs1
      have hd : HasDerivAt (fun τ : ℝ => σ (g (8 * τ)))
          (deriv σ (g (8 * s)) * (deriv g (8 * s) * 8)) s := by
        have hσD : HasDerivAt σ (deriv σ (g (8 * s))) (g (8 * s)) :=
          ((hσ.differentiable (by simp)) _).hasDerivAt
        have hgD : HasDerivAt g (deriv g (8 * s)) (8 * s) :=
          ((hg.differentiable (by simp)) _).hasDerivAt
        have hlin : HasDerivAt (fun τ : ℝ => 8 * τ) 8 s := by
          simpa using (hasDerivAt_id s).const_mul 8
        exact hσD.comp s (hgD.comp s hlin)
      rw [hd.deriv]
      have h1 := hσd _ (hgIco (8 * s) (by linarith))
      have h2 := hgd (8 * s)
      positivity
    · intro z τ w t hτ0 hτ1 hw ht
      have hz1 : ‖(z : EuclideanSpace ℝ (Fin 2))‖ ≤ 1 := z.2
      have hzτ : ((z : EuclideanSpace ℝ (Fin 2)), τ) ∈ neckDomain (9 / 64) := by
        refine ⟨?_, ?_⟩
        · change ‖(z : EuclideanSpace ℝ (Fin 2))‖ < 1 + 2 * (9 / 64)
          linarith
        · change |τ| < 2 * (9 / 64)
          rw [abs_lt]
          constructor <;> linarith
      have hqm : ((z : EuclideanSpace ℝ (Fin 2)), g (8 * τ)) ∈
          masterDomain η' ((3 / 4 + a) / 2) := hκmem ((z : EuclideanSpace ℝ (Fin 2)), τ) hzτ
      have hw' : (w : EuclideanSpace ℝ (Fin 2)) =
          handleDiskMap A P ((z : EuclideanSpace ℝ (Fin 2)), g (8 * τ)).1 := hw
      have ht' : (t : ℝ) = endCoord b (σ ((z : EuclideanSpace ℝ (Fin 2)), g (8 * τ)).2) := ht
      have h := hprodM ((z : EuclideanSpace ℝ (Fin 2)), g (8 * τ)) hqm (hgnn _ (by linarith))
        hz1 w t hw' ht'
      rw [hN]
      exact h

end GC.GraphManifold.Assembly
