import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1NeckBox
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCertificate

/-!
# Chapter-14 assembly, item L1, group G3b: the rim-product hypothesis

Lead decision of 2026-10-04 (lane ASM-L1b): the normal form of a ball–handle cycle (G3b) and the
L1 statement carry the hypothesis `BallHandleCycle.RimProduct`: on the handle quadrant
`{-a < x ≤ 0, 0 ≤ y < a}` of every rim box (some `a > 3/4`; the fillet lies in `x + y < 3/4`), the
rim chart is the handle map read in a product collar of the rim circle and of the end `b`,
`rimChart k b (θ, x, y) = handle k (ρ x • A θ̂, endCoord b (τ y))`, `θ̂ = planeOfCircle θ`, with
`A ∈ O(2)` and smooth monotone collar profiles `ρ` (`ρ 0 = 1`) and `τ` (`τ 0 = 0`), all existential
per rim. The matching producer clause is `DecompositionCertificate.RimProduct`; it transfers to the
two cycle builders (`BallHandleCycle.rimProduct_ofLoop`; `RimProductAt.of_orient` for the handle
orientation of `dry_cycleOfCertificate`).

Frozen text: `build-logs/scratch/ASM-L1b/Shortcut.lean`.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

local instance diskCharts_ASML1bR : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

/-! ## (a) The hypothesis -/

/-- **The rim-product clause at one rim.** The rim chart `χ` at the end `b` of the handle `H` is,
on the handle quadrant of `rimBox a` (`a > 3/4`), the handle map in a product collar:
`χ (θ, x, y) = H (ρ x • A θ̂, endCoord b (τ y))`. -/
def RimProductAt {W : CompactCarrier.{u}}
    (χ : PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ × ℝ)) W.model (Circle × (ℝ × ℝ)) W.Carrier ∞)
    (H : EdgeHandle W) (b : Bool) : Prop :=
  ∃ a : ℝ, 3 / 4 < a ∧ a ≤ 2 ∧
  ∃ A : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2),
  ∃ ρ τ : ℝ → ℝ, ContDiff ℝ ∞ ρ ∧ ContDiff ℝ ∞ τ ∧ ρ 0 = 1 ∧ τ 0 = 0 ∧
    (∀ x ∈ Ioc (-a) 0, 0 < ρ x ∧ 0 < deriv ρ x) ∧ (∀ y ∈ Ico 0 a, 0 < deriv τ y) ∧
    ∀ (θ : Circle) (x y : ℝ) (w : ClosedCell 2) (t : Icc (0 : ℝ) 1),
      -a < x → x ≤ 0 → 0 ≤ y → y < a →
      (w : EuclideanSpace ℝ (Fin 2)) = ρ x • A (planeOfCircle θ) →
      (t : ℝ) = endCoord b (τ y) →
      χ (θ, (x, y)) = H.map (w, t)

/-- **(a) The G3b hypothesis.** Every rim chart of the cycle is a product in its handle's
coordinates. -/
def BallHandleCycle.RimProduct {W : CompactCarrier.{u}} (C : BallHandleCycle W) : Prop :=
  ∀ k b, RimProductAt (C.rimChart k b) (C.handle k) b

/-! ## (b) The producer clause and the two builders -/

/-- **(b) The certificate clause** (producer-guaranteed field, to be added at the next handover). -/
def DecompositionCertificate.RimProduct {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n}
    (D : DecompositionCertificate W E) : Prop :=
  ∀ h b, RimProductAt (D.rimChart h b) (D.handle h) b

/-- `endCoord` of the opposite end is the reflection `t ↦ 1 - t`. -/
theorem endCoord_not (b : Bool) (s : ℝ) : endCoord (!b) s = 1 - endCoord b s := by
  cases b <;> simp [endCoord]

/-- **Transfer through a reversed handle** (`dry_cycleOfCertificate` runs a handle backwards by
`dry_orient`): the clause at the end `!b` of `H` gives the clause at the end `b` of any `H'` with
`H'.map (w, t) = H.map (w, 1 - t)`. -/
theorem RimProductAt.of_reverse {W : CompactCarrier.{u}}
    {χ : PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ × ℝ)) W.model (Circle × (ℝ × ℝ)) W.Carrier ∞}
    {H H' : EdgeHandle W} {b : Bool}
    (hrev : ∀ w (t t' : Icc (0 : ℝ) 1), (t' : ℝ) = 1 - t → H'.map (w, t) = H.map (w, t'))
    (h : RimProductAt χ H (!b)) : RimProductAt χ H' b := by
  obtain ⟨a, ha, ha', A, ρ, τ, hρ, hτ, hρ0, hτ0, hρd, hτd, heq⟩ := h
  refine ⟨a, ha, ha', A, ρ, τ, hρ, hτ, hρ0, hτ0, hρd, hτd, ?_⟩
  intro θ x y w t hx hx' hy hy' hw ht
  have ht' : (1 - (t : ℝ)) ∈ Icc (0 : ℝ) 1 := ⟨by linarith [t.2.2], by linarith [t.2.1]⟩
  rw [hrev w t ⟨1 - t, ht'⟩ rfl]
  exact heq θ x y w ⟨1 - t, ht'⟩ hx hx' hy hy' hw (by simp [ht, endCoord_not])

/-- **Transfer to the loop builder** `BallHandleCycle.ofLoop`: its rim charts and handle are the
data passed in, so the clause is the same hypothesis on that data. -/
theorem BallHandleCycle.rimProduct_ofLoop {W : CompactCarrier.{u}} (C : BallHandleCycle W)
    (χ : Bool → PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ × ℝ)) W.model (Circle × (ℝ × ℝ))
      W.Carrier ∞) (H : EdgeHandle W)
    (hχ : ∀ k b, C.rimChart k b = χ b) (hH : ∀ k, C.handle k = H)
    (hprod : ∀ b, RimProductAt (χ b) H b) : C.RimProduct := by
  intro k b
  rw [hχ k b, hH k]
  exact hprod b

/-- **Transfer to the dry builder**: per rim, either the handle is used as is (`σ = false`, the
clause is the certificate's at the same end) or reversed (`σ = true`, the certificate's at the
opposite end, `RimProductAt.of_reverse`). -/
theorem RimProductAt.of_orient {W : CompactCarrier.{u}}
    {χ : PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ × ℝ)) W.model (Circle × (ℝ × ℝ)) W.Carrier ∞}
    {H H' : EdgeHandle W} (σ b : Bool)
    (hH' : σ = false → H' = H)
    (hrev : σ = true → ∀ w (t t' : Icc (0 : ℝ) 1), (t' : ℝ) = 1 - t → H'.map (w, t) = H.map (w, t'))
    (h : RimProductAt χ H (xor b σ)) : RimProductAt χ H' b := by
  cases σ
  · rw [hH' rfl]
    simpa using h
  · exact RimProductAt.of_reverse (hrev rfl) (by simpa using h)

end GC.GraphManifold.Assembly
