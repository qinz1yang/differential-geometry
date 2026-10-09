import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GRimFlowHandle

/-!
# FC39 GROUP G, RIMBOX route B: consumer of the flow handle kernel

Lane FC39-G-RIMBOX. `exists_flowHandle_polar_GRIM`: a POLAR end disk (`B ∘ D = κ (1 − ‖w‖)` near the
rim) gives a polar flow handle on EVERY slice (`B (Hm (w, t)) = κ (1 − ‖w‖)` near the rim, the radial
form of the rim-product clause: `ρ` depends on `x` only), with the same exported flow.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Topology.Ehresmann
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0

local instance diskChartsApp_GRIM : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

local instance diskSmoothApp_GRIM : IsManifold (𝓡∂ 2) ∞ (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 1

variable {E H Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace Y] [ChartedSpace H Y] [IsManifold I ∞ Y] [T2Space Y] [SigmaCompactSpace Y]

/-- **A polar end disk gives a polar handle on every slice**, with the same exported flow. -/
theorem exists_flowHandle_polar_GRIM (hdim : Module.finrank ℝ E = 1 + 1 + Module.finrank ℝ ℝ)
    {P B : Y → ℝ} (hP : ContMDiff I 𝓘(ℝ, ℝ) ∞ P) (hB : ContMDiff I 𝓘(ℝ, ℝ) ∞ B) {a b : ℝ}
    (hreg : ∀ y, P y ∈ Ioo a b → 0 ≤ B y → Surjective (mfderiv I 𝓘(ℝ, ℝ) P y))
    (hregb : ∀ y, P y ∈ Ioo a b → B y = 0 →
      Surjective (mfderiv I 𝓘(ℝ, ℝ × ℝ) (fun y => (P y, B y)) y))
    (hprop : ∀ K : Set ℝ, IsCompact K → K ⊆ Ioo a b → IsCompact (P ⁻¹' K ∩ {y | 0 ≤ B y}))
    {a₀ b₀ : ℝ} (ha₀ : a < a₀) (ha₀0 : a₀ < 0) (hb₀1 : 1 < b₀) (hb₀ : b₀ < b)
    (D : ClosedCell 2 → Y) (hD : ContMDiff (𝓡∂ 2) I ∞ D) (hDinj : Injective D)
    (hDimm : ∀ w, Injective (mfderiv (𝓡∂ 2) I D w))
    (hDr : range D = {y | P y = 0 ∧ 0 ≤ B y}) {κ δ : ℝ} (hκ : 0 < κ) (hδ : 0 < δ)
    (hpol : ∀ w : ClosedCell 2, 1 - δ < ‖(w : EuclideanSpace ℝ (Fin 2))‖ →
      B (D w) = κ * (1 - ‖(w : EuclideanSpace ℝ (Fin 2))‖)) :
    ∃ Hm : ClosedCell 2 × Icc (0 : ℝ) 1 → Y,
      ContMDiff ((𝓡∂ 2).prod (𝓡∂ 1)) I ∞ Hm ∧ Injective Hm ∧
      (∀ p, Injective (mfderiv ((𝓡∂ 2).prod (𝓡∂ 1)) I Hm p)) ∧
      (∀ p, P (Hm p) = p.2 ∧ 0 ≤ B (Hm p)) ∧
      range Hm = {y | P y ∈ Icc 0 1 ∧ 0 ≤ B y} ∧
      (∀ w, Hm (w, iccEnd false) = D w) ∧
      ∃ δ' : ℝ, 0 < δ' ∧ δ' ≤ δ ∧
        (∀ p : ClosedCell 2 × Icc (0 : ℝ) 1, 1 - δ' < ‖(p.1 : EuclideanSpace ℝ (Fin 2))‖ →
          B (Hm p) = κ * (1 - ‖(p.1 : EuclideanSpace ℝ (Fin 2))‖)) ∧
      ∃ r' : ℝ, 0 < r' ∧
        ∃ (U : TopologicalSpace.Opens Y) (Fl : ℝ → U ≃ₘ⟮I, I⟯ U),
          ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × U => Fl q.1 q.2) ∧
          Fl 0 = Diffeomorph.refl I U ∞ ∧
          (∀ s t, (Fl s).trans (Fl t) = Fl (s + t)) ∧
          (∀ w, D w ∈ U) ∧
          (∀ p, ∃ hp : D p.1 ∈ U, Hm p = (Fl (p.2 : ℝ) ⟨D p.1, hp⟩ : Y)) ∧
          (∀ z : U, P z = 0 → -r' ≤ B z → ∀ t ∈ Ioo a₀ b₀, P (Fl t z) = t) ∧
          ∀ (z : U) (t : ℝ), |B z| < r' → B (Fl t z) = B z := by
  obtain ⟨Hm, hHm, hinj, himm, hPB, hrange, hend, r', hr', hkeep, U, Fl, hFl, hFl0, hgrp, hDU,
    hHmFl, hFlP, hFlB⟩ :=
    exists_flowHandle_GRIM hdim hP hB hreg hregb hprop ha₀ ha₀0 hb₀1 hb₀ D hD hDinj hDimm hDr
  refine ⟨Hm, hHm, hinj, himm, hPB, hrange, hend, min δ (r' / (2 * κ)),
    lt_min hδ (div_pos hr' (by positivity)), min_le_left _ _, fun p hp => ?_, r', hr', U, Fl,
    hFl, hFl0, hgrp, hDU, hHmFl, hFlP, hFlB⟩
  have hpδ : 1 - δ < ‖(p.1 : EuclideanSpace ℝ (Fin 2))‖ :=
    lt_of_le_of_lt (by linarith [min_le_left δ (r' / (2 * κ))]) hp
  have hBD := hpol p.1 hpδ
  rw [hkeep p ?_, hBD]
  rw [hBD]
  have hp' : 1 - ‖(p.1 : EuclideanSpace ℝ (Fin 2))‖ < r' / (2 * κ) := by
    linarith [min_le_right δ (r' / (2 * κ))]
  calc κ * (1 - ‖(p.1 : EuclideanSpace ℝ (Fin 2))‖) < κ * (r' / (2 * κ)) :=
        mul_lt_mul_of_pos_left hp' hκ
    _ = r' / 2 := by field_simp
    _ < r' := half_lt_self hr'

end GC.GraphManifold.Assembly.FC39P0
