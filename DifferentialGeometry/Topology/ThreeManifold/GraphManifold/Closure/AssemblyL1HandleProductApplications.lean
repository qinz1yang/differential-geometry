import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1HandleProduct

/-!
# Consumers of T2′ (handles in product form; lane ASM-L1b3)

* `BallHandleCycle.exists_handleReparams_of_product`: from the product clause of T1′ (the handle
  side of both necks of every handle is a product), the family of handle reparametrizations in the
  exact form of the hypothesis `hh` of T4 (`BallHandleCycle.cycleNormalForm_of_necks`).
* `exists_handleProductProfiles`: the profile hypotheses of T2′ are jointly satisfiable (constant
  radial profile `1`, identity height profile), so T2′ is not vacuous on the profile side.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

local instance diskCharts_ASML1b3A : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

local instance diskSmooth_ASML1b3A : IsManifold (𝓡∂ 2) ∞ (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 1

/-- **T2′ for every handle of a cycle**, in the form of the hypothesis `hh` of T4. -/
theorem BallHandleCycle.exists_handleReparams_of_product {W : CompactCarrier.{u}}
    (C : BallHandleCycle W) {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 8)
    (N : Fin C.len → Bool → PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model
      (EuclideanSpace ℝ (Fin 2) × ℝ) W.Carrier ∞)
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
          N k b ((z : EuclideanSpace ℝ (Fin 2)), τ) = (C.handle k).map (w, t)) :
    ∃ h : Fin C.len → ClosedCell 2 × Icc (0 : ℝ) 1 → W.Carrier, ∀ k,
      ContMDiff ((𝓡∂ 2).prod (𝓡∂ 1)) W.model ∞ (h k) ∧
      (∀ q, Bijective (mfderiv ((𝓡∂ 2).prod (𝓡∂ 1)) W.model (h k) q)) ∧ Injective (h k) ∧
      range (h k) = range (C.handle k).map ∧
      (∀ b, h k '' {q | q.2 = iccEnd b} = (C.handle k).endDisk b) ∧
      ∀ b (q : ClosedCell 2 × Icc (0 : ℝ) 1), |(q.2 : ℝ) - (iccEnd b : ℝ)| < 2 * ε →
        h k q = N k b (handleEnd b q) := by
  have hH : ∀ k, ∃ h : ClosedCell 2 × Icc (0 : ℝ) 1 → W.Carrier,
      ContMDiff ((𝓡∂ 2).prod (𝓡∂ 1)) W.model ∞ h ∧
      (∀ q, Bijective (mfderiv ((𝓡∂ 2).prod (𝓡∂ 1)) W.model h q)) ∧ Injective h ∧
      range h = range (C.handle k).map ∧
      (∀ b, h '' {q | q.2 = iccEnd b} = (C.handle k).endDisk b) ∧
      ∀ b (q : ClosedCell 2 × Icc (0 : ℝ) 1), |(q.2 : ℝ) - (iccEnd b : ℝ)| < 2 * ε →
        h q = N k b (handleEnd b q) := fun k => by
    obtain ⟨A, hA, P, T, hP, hT, hP1, hPpos, hPmono, hT0, hTmono, hTsep, heq⟩ := hprodN k
    exact (C.handle k).exists_reparam_eq_necks_of_product hε hε' (N k) A hA P T hP hT hP1 hPpos
      hPmono hT0 hTmono hTsep heq
  choose h hh using hH
  exact ⟨h, hh⟩

/-- The profile hypotheses of T2′ are jointly satisfiable: radial profile `1`, height profile
`s ↦ s`. -/
theorem exists_handleProductProfiles {ε : ℝ} (hε' : ε ≤ 1 / 8) :
    ∃ P T : Bool → ℝ → ℝ, (∀ b, ContDiff ℝ ∞ (P b)) ∧ (∀ b, ContDiff ℝ ∞ (T b)) ∧
      (∀ b, P b 1 = 1) ∧ (∀ b s, 0 ≤ s → s ≤ 1 → 0 < P b s) ∧
      (∀ b r, 0 ≤ r → r ≤ 1 → 0 < deriv (fun r : ℝ => r * P b (r ^ 2)) r) ∧
      (∀ b, T b 0 = 0) ∧ (∀ b s, 0 ≤ s → s ≤ 2 * ε → 0 < deriv (T b) s) ∧
      T false (2 * ε) < 1 - T true (2 * ε) := by
  refine ⟨fun _ _ => 1, fun _ s => s, fun _ => contDiff_const, fun _ => contDiff_id,
    fun _ => rfl, fun _ _ _ _ => one_pos, fun _ r _ _ => ?_, fun _ => rfl, fun _ s _ _ => ?_,
    by linarith⟩
  · simp
  · simp

end GC.GraphManifold.Assembly
