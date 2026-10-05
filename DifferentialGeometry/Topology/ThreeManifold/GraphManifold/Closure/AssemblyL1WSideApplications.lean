import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1WSideRimProduct
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1WSideAssembly
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyDiskSmale

/-!
# Consumers of group G1 of lane ASM-L1b (rim-product hypothesis, T4 assembly)

* `RimProductAt.exists_map_mem_endDisk`, `RimProductAt.map_center_mem_rim`: under the rim-product
  clause the bottom edge `{y = 0, x ≤ 0}` of the handle quadrant goes into the end disk `b`, and the
  centre circle `{x = y = 0}` goes onto its rim (the inclusion `⊆` of the certificate field
  `rim_label` follows from the clause).
* `BallHandleCycle.exists_cycleNormalForm_of_necks`: the existential normal form (the shape of
  G3b) from the T4 data.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

local instance diskCharts_ASML1bP : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

local instance ballCharts_ASML1bP : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 2

theorem norm_planeOfCircle (θ : Circle) : ‖planeOfCircle θ‖ = 1 := by
  rw [planeOfCircle, LinearIsometryEquiv.norm_map, Circle.norm_coe]

theorem endCoord_mem_Icc {b : Bool} {s : ℝ} (hs : 0 ≤ s) (hs' : s ≤ 1) :
    endCoord b s ∈ Icc (0 : ℝ) 1 := by
  cases b
  · exact ⟨hs, hs'⟩
  · exact ⟨by simp [endCoord]; linarith, by simp [endCoord]; linarith⟩

namespace RimProductAt

variable {W : CompactCarrier.{u}}
  {χ : PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ × ℝ)) W.model (Circle × (ℝ × ℝ)) W.Carrier ∞}
  {H : EdgeHandle W} {b : Bool}

/-- The centre circle of the rim box goes onto the rim of the end disk `b`. -/
theorem map_center_mem_rim (hχ : RimProductAt χ H b) (θ : Circle) :
    χ (θ, (0, 0)) ∈ (fun x : ClosedCell 2 => H.map (x, iccEnd b)) '' diskRim := by
  obtain ⟨a, ha, -, A, ρ, τ, -, -, hρ0, hτ0, -, -, heq⟩ := hχ
  have hn : ‖ρ 0 • A (planeOfCircle θ)‖ = 1 := by
    rw [hρ0, one_smul, LinearIsometryEquiv.norm_map, norm_planeOfCircle]
  let w : ClosedCell 2 := ⟨ρ 0 • A (planeOfCircle θ), by
    rw [hn]⟩
  refine ⟨w, mem_diskRim_iff.mpr hn, ?_⟩
  symm
  apply heq θ 0 0 w (iccEnd b) (by linarith) le_rfl le_rfl (by linarith) rfl
  rw [hτ0]
  cases b <;> simp [endCoord, iccEnd]

/-- The bottom edge `{y = 0, -a < x ≤ 0}` of the handle quadrant goes into the end disk `b`. -/
theorem exists_map_mem_endDisk (hχ : RimProductAt χ H b) :
    ∃ a : ℝ, 3 / 4 < a ∧ ∀ (θ : Circle) (x : ℝ), -a < x → x ≤ 0 → χ (θ, (x, 0)) ∈ H.endDisk b := by
  obtain ⟨a, ha, -, A, ρ, τ, hρ, -, hρ0, hτ0, hρd, -, heq⟩ := hχ
  refine ⟨a, ha, fun θ x hx hx' => ?_⟩
  -- `ρ` increases on `(-a, 0]`, so `0 < ρ x ≤ 1`
  have hmono : StrictMonoOn ρ (Ioc (-a) 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioc (-a) 0) hρ.continuous.continuousOn
    intro y hy
    rw [interior_Ioc] at hy
    exact (hρd y (Ioo_subset_Ioc_self hy)).2
  have hle : ρ x ≤ 1 := by
    rw [← hρ0]
    exact hmono.monotoneOn ⟨hx, hx'⟩ ⟨by linarith, le_rfl⟩ hx'
  have hpos : 0 < ρ x := (hρd x ⟨hx, hx'⟩).1
  have hn : ‖ρ x • A (planeOfCircle θ)‖ = ρ x := by
    rw [norm_smul, LinearIsometryEquiv.norm_map, norm_planeOfCircle, mul_one,
      Real.norm_of_nonneg hpos.le]
  let w : ClosedCell 2 := ⟨ρ x • A (planeOfCircle θ), by
    rw [hn]
    exact hle⟩
  refine ⟨w, ?_⟩
  symm
  apply heq θ x 0 w (iccEnd b) hx hx' le_rfl (by linarith) rfl
  rw [hτ0]
  cases b <;> simp [endCoord, iccEnd]

end RimProductAt

namespace BallHandleCycle

variable {W : CompactCarrier.{u}}

/-- **Consumer of T4.** The normal form in the shape of G3b from the T4 data. -/
theorem exists_cycleNormalForm_of_necks (C : BallHandleCycle W)
    {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 8)
    (N : Fin C.len → Bool → PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model
      (EuclideanSpace ℝ (Fin 2) × ℝ) W.Carrier ∞)
    (hsrc : ∀ k b, closedNeckDomain ε ⊆ (N k b).source)
    (hdisj : ∀ k b k' b', (k, b) ≠ (k', b') → Disjoint (N k b).target (N k' b').target)
    (hball : ∀ k b {q}, q ∈ (N k b).source →
      (N k b q ∈ range (C.ball (rimBall C.len k b)).map ↔ q.2 ≤ 0))
    (hhandle : ∀ k b {q}, q ∈ (N k b).source →
      (N k b q ∈ range (C.handle k).map ↔ (0 ≤ q.2 ∧ ‖q.1‖ ≤ 1)))
    (hunion : ∀ k b {q}, q ∈ neckDomain ε →
      (N k b q ∈ range C.union.map ↔ neckRounding ε q ≤ 0))
    (hpieces : ∀ k b, (N k b).target ∩ ((⋃ j, range (C.ball j).map) ∪
      ⋃ j, range (C.handle j).map) ⊆
        range (C.ball (rimBall C.len k b)).map ∪ range (C.handle k).map)
    (hfillet : ∀ k b, C.fillet k b ⊆ N k b '' {q | q ∈ neckDomain ε ∧ neckRounding ε q ≤ 0})
    (hH : ∀ k, ∃ h : ClosedCell 2 × Icc (0 : ℝ) 1 → W.Carrier,
      ContMDiff ((𝓡∂ 2).prod (𝓡∂ 1)) W.model ∞ h ∧
      (∀ q, Bijective (mfderiv ((𝓡∂ 2).prod (𝓡∂ 1)) W.model h q)) ∧ Injective h ∧
      range h = range (C.handle k).map ∧
      (∀ b, h '' {q | q.2 = iccEnd b} = (C.handle k).endDisk b) ∧
      ∀ b (q : ClosedCell 2 × Icc (0 : ℝ) 1), |(q.2 : ℝ) - (iccEnd b : ℝ)| < 2 * ε →
        h q = N k b (handleEnd b q))
    (hB : ∀ j, ∃ β : ClosedCell 3 → W.Carrier, ContMDiff (𝓡∂ 3) W.model ∞ β ∧
      (∀ x, Bijective (mfderiv (𝓡∂ 3) W.model β x)) ∧
      Injective β ∧ range β = range (C.ball j).map ∧
      ∀ k b x, rimBall C.len k b = j → x ∈ neckCapRegion ε b →
        β x = N k b (capMap b (x : EuclideanSpace ℝ (Fin 3)))) :
    ∃ ε' : ℝ, Nonempty (CycleNormalForm W.model W.Carrier C.len ε' (range C.union.map)) := by
  choose h hh using hH
  choose β hβ using hB
  exact ⟨ε, C.cycleNormalForm_of_necks hε hε' N hsrc hdisj hball hhandle hunion hpieces hfillet h hh
    β (fun j => ⟨(hβ j).1, (hβ j).2.1, (hβ j).2.2.1, (hβ j).2.2.2.1⟩)
    (fun k b x hx => (hβ _).2.2.2.2 k b x rfl hx)⟩

end BallHandleCycle

end GC.GraphManifold.Assembly
