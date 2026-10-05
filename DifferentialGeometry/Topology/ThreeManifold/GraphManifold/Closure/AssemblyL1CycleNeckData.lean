import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1HandleProductApplications
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1WSideBallApplications
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1WSideApplications

/-!
# Chapter-14 assembly, item L1, group G3b′: the cycle normal form from the neck data of T1′

Lane ASM-L1b3. `BallHandleCycle.cycleNormalForm_of_neckData`: the conclusion clauses of T1′
(`BallHandleCycle.exists_necks_of_rimProduct`) at a fixed scale `ε` and necks `N` give a
`CycleNormalForm` of the cycle with union `range C.union.map`:
* handles: T2′ per handle (`BallHandleCycle.exists_handleReparams_of_product`);
* balls: T3′ in compressed-neck form (`PieceEmbedding.exists_ballReparam_eq_neckCompress`) for
  ball `j` with the necks `(j, false)` and `(j - 1, true)` (`ballRim`);
* the necks of the normal form are the necks compressed by the profile of their ball
  (`neckCompress`); the compression is the identity on the handle side `τ ≥ 0`, keeps the ball
  side, the union (`neckRounding ≤ 0` on `τ ≤ 0`) and the fillets (a fillet point is in no ball,
  so its neck coordinate has `τ > 0`);
* assembly: T4 (`BallHandleCycle.cycleNormalForm_of_necks`).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

local instance diskCharts_ASML1b3D : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

local instance diskSmooth_ASML1b3D : IsManifold (𝓡∂ 2) ∞ (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 1

local instance ballCharts_ASML1b3D : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 2

local instance ballSmooth_ASML1b3D : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 2

/-- The handle whose end `b` lies on the ball `j`: `j` itself at `b = false`, its predecessor
`j - 1` (mod `len`) at `b = true` (inverse of `rimBall · · b`). -/
def ballRim (len : ℕ) (j : Fin len) (b : Bool) : Fin len :=
  cond b ((finRotate len).symm j) j

theorem rimBall_ballRim (len : ℕ) (j : Fin len) (b : Bool) :
    rimBall len (ballRim len j b) b = j := by
  cases b
  · rfl
  · exact Equiv.apply_symm_apply _ j

theorem ballRim_rimBall (len : ℕ) (k : Fin len) (b : Bool) :
    ballRim len (rimBall len k b) b = k := by
  cases b
  · rfl
  · exact Equiv.symm_apply_apply _ k

/-- The compression keeps the handle side `{τ ≥ 0}` of a neck. -/
theorem compress_nonneg_iff {l a : ℝ} (hl : 0 < l) (ha : 0 ≤ a) {τ : ℝ} :
    0 ≤ compress l ha τ ↔ 0 ≤ τ := by
  constructor
  · intro h
    by_contra hτ
    have hτ' : τ < 0 := not_le.mp hτ
    have h0 : compress l ha τ = 0 := le_antisymm (compress_nonpos hl ha hτ'.le) h
    have h1 := compressInv_compress hl ha τ
    have h2 := compressInv_compress hl ha 0
    rw [h0] at h1
    rw [compress_of_nonneg hl ha le_rfl] at h2
    linarith
  · intro h
    rw [compress_of_nonneg hl ha h]
    exact h

/-- The ball side of the neck box lies in the rounded union. -/
theorem neckRounding_nonpos_of_snd_nonpos {ε : ℝ} (hε : 0 < ε)
    {q : EuclideanSpace ℝ (Fin 2) × ℝ} (hq : q.2 ≤ 0) : neckRounding ε q ≤ 0 := by
  unfold neckRounding
  exact standardRimRounding_nonpos_of _ (Or.inl (div_nonpos_of_nonpos_of_nonneg hq hε.le))

/-- **G3b′ from the neck data of T1′.** The hypotheses are the conclusion clauses of T1′
(`BallHandleCycle.exists_necks_of_rimProduct`) at a fixed scale `ε` and necks `N`. Handles: T2′.
Balls: T3′ (compressed-neck form) for ball `j` with the necks `(j, false)` and `(j - 1, true)`.
The necks of the normal form are the necks compressed by the profile of their ball; the handle
side is unchanged. Assembly: T4. -/
theorem BallHandleCycle.cycleNormalForm_of_neckData {W : CompactCarrier.{u}}
    (C : BallHandleCycle W) {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 8)
    (N : Fin C.len → Bool → PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model
      (EuclideanSpace ℝ (Fin 2) × ℝ) W.Carrier ∞)
    (hsrc : ∀ k b, closedNeckDomain ε ⊆ (N k b).source)
    (hdisj : ∀ k b k' b', (k, b) ≠ (k', b') → Disjoint (N k b).target (N k' b').target)
    (hball : ∀ k b {q}, q ∈ (N k b).source →
      (N k b q ∈ range (C.ball (rimBall C.len k b)).map ↔ q.2 ≤ 0))
    (hhandle : ∀ k b {q}, q ∈ (N k b).source →
      (N k b q ∈ range (C.handle k).map ↔ (0 ≤ q.2 ∧ ‖q.1‖ ≤ 1)))
    (hunion : ∀ k b {q}, q ∈ neckDomain ε → (N k b q ∈ range C.union.map ↔ neckRounding ε q ≤ 0))
    (hpieces : ∀ k b, (N k b).target ∩ ((⋃ j, range (C.ball j).map) ∪
      ⋃ j, range (C.handle j).map) ⊆
        range (C.ball (rimBall C.len k b)).map ∪ range (C.handle k).map)
    (hfillet : ∀ k b, C.fillet k b ⊆ N k b '' {q | q ∈ neckDomain ε ∧ neckRounding ε q ≤ 0})
    (hprodN : ∀ k, ∃ A : Bool → EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2),
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
          N k b ((z : EuclideanSpace ℝ (Fin 2)), τ) = (C.handle k).map (w, t))
    (hsb : ∀ k x₀ x₁, (C.ball (finRotate C.len k)).map ((C.ballModel _).symm x₀) =
        N (finRotate C.len k) false 0 →
      (C.ball (finRotate C.len k)).map ((C.ballModel _).symm x₁) = N k true 0 →
      ballNeckDetAmb (C.ball (finRotate C.len k)) (C.ballModel _) x₀
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model (N (finRotate C.len k) false) 0) *
      ballNeckDetAmb (C.ball (finRotate C.len k)) (C.ballModel _) x₁
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model (N k true) 0) < 0) :
    Nonempty (CycleNormalForm W.model W.Carrier C.len ε (range C.union.map)) := by
  -- handles (T2′)
  obtain ⟨h, hh⟩ := C.exists_handleReparams_of_product hε hε' N hprodN
  -- balls (T3′): ball `j` carries the necks `(ballRim j b, b)`
  have hB : ∀ j, ∃ l a : ℝ, ∃ (hl : 0 < l) (ha : 0 ≤ a), ∃ β : ClosedCell 3 → W.Carrier,
      ContMDiff (𝓡∂ 3) W.model ∞ β ∧ (∀ x, Bijective (mfderiv (𝓡∂ 3) W.model β x)) ∧
      Injective β ∧ range β = range (C.ball j).map ∧
      ∀ b x, x ∈ neckCapRegion ε b →
        β x = neckCompress (N (ballRim C.len j b) b) hl ha
          (capMap b (x : EuclideanSpace ℝ (Fin 3))) := by
    intro j
    have hsb' := hsb ((finRotate C.len).symm j)
    rw [Equiv.apply_symm_apply] at hsb'
    exact (C.ball j).exists_ballReparam_eq_neckCompress (C.ballModel j) hε hε'
      (fun b => N (ballRim C.len j b) b) (fun b => hsrc _ b)
      (hdisj j false _ true (by simp))
      (fun b {q} hq => by
        have := hball (ballRim C.len j b) b hq
        rwa [rimBall_ballRim] at this)
      hsb'
  choose l a hl ha β hβs hβd hβi hβr hβc using hB
  -- the necks of the normal form: compressed by the profile of their ball
  let M : Fin C.len → Bool → PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model
      (EuclideanSpace ℝ (Fin 2) × ℝ) W.Carrier ∞ := fun k b =>
    neckCompress (N k b) (hl (rimBall C.len k b)) (ha (rimBall C.len k b))
  have hM : ∀ k b q, M k b q =
      N k b (q.1, compress (l (rimBall C.len k b)) (ha (rimBall C.len k b)) q.2) :=
    fun _ _ _ => rfl
  have hMs : ∀ k b {q}, q ∈ (M k b).source →
      (q.1, compress (l (rimBall C.len k b)) (ha (rimBall C.len k b)) q.2) ∈ (N k b).source :=
    fun k b _ hq => (mem_neckCompress_source (hl (rimBall C.len k b))).mp hq
  refine C.cycleNormalForm_of_necks hε hε' M ?_ ?_ ?_ ?_ ?_ ?_ ?_ h ?_ β
    (fun j => ⟨hβs j, hβd j, hβi j, hβr j⟩) ?_
  · -- sources
    intro k b q hq
    exact (mem_neckCompress_source (hl (rimBall C.len k b))).mpr
      (hsrc k b (neckCompress_mem_closedNeckDomain (hl _) (ha (rimBall C.len k b)) hq))
  · -- disjoint targets
    intro k b k' b' hne
    exact (hdisj k b k' b' hne).mono
      (neckCompress_target_subset (N k b) (hl _) (ha (rimBall C.len k b)))
      (neckCompress_target_subset (N k' b') (hl _) (ha (rimBall C.len k' b')))
  · -- ball side
    intro k b q hq
    exact neckCompress_mem_range_iff (hball k b) (hl _) (ha (rimBall C.len k b)) hq
  · -- handle side
    intro k b q hq
    rw [hM, hhandle k b (hMs k b hq)]
    exact Iff.and (compress_nonneg_iff (hl _) (ha (rimBall C.len k b))) Iff.rfl
  · -- union
    intro k b q hq
    rw [hM, hunion k b (neckCompress_mem_neckDomain (hl _) (ha (rimBall C.len k b)) hq)]
    rcases le_total 0 q.2 with h0 | h0
    · rw [compress_of_nonneg (hl _) (ha (rimBall C.len k b)) h0]
    · exact iff_of_true (neckRounding_nonpos_of_snd_nonpos hε
        (compress_nonpos (hl _) (ha (rimBall C.len k b)) h0))
        (neckRounding_nonpos_of_snd_nonpos hε h0)
  · -- pieces
    intro k b
    exact (inter_subset_inter_left _
      (neckCompress_target_subset (N k b) (hl _) (ha (rimBall C.len k b)))).trans (hpieces k b)
  · -- fillets: their neck points have `τ > 0` (a fillet point is in no ball), where `M = N`
    intro k b p hp
    obtain ⟨q, ⟨hqD, hqR⟩, rfl⟩ := hfillet k b hp
    have hq0 : 0 ≤ q.2 := by
      by_contra hneg
      have hin : N k b q ∈ range (C.ball (rimBall C.len k b)).map :=
        (hball k b (hsrc k b (neckDomain_subset_closedNeckDomain ε hqD))).mpr
          (not_le.mp hneg).le
      obtain ⟨p', hp', hpe⟩ := hp
      have hsrc' : p' ∈ (C.rimChart k b).source := by
        rw [C.rim_source]
        exact ⟨by linarith [hp'.2.2.1.1], by linarith [hp'.2.2.1.2]⟩
      exact C.rim_quadrant k b p' hsrc' hp'.1 hp'.2.1
        (by rw [hpe]; exact Or.inl (mem_iUnion.mpr ⟨_, hin⟩))
    refine ⟨q, ⟨hqD, hqR⟩, ?_⟩
    rw [hM, compress_of_nonneg (hl _) (ha (rimBall C.len k b)) hq0]
  · -- handles agree with the compressed necks on the end strips (the handle side is unchanged)
    intro k
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hh k
    refine ⟨h1, h2, h3, h4, h5, fun b q hq => ?_⟩
    have hc : 0 ≤ (handleEnd b q).2 := (endCoord_mem_Icc (b := b) q.2.2.1 q.2.2.2).1
    rw [h6 b q hq, hM, compress_of_nonneg (hl _) (ha (rimBall C.len k b)) hc]
  · -- caps
    intro k b x hx
    rw [hβc _ b x hx, ballRim_rimBall]

end GC.GraphManifold.Assembly
