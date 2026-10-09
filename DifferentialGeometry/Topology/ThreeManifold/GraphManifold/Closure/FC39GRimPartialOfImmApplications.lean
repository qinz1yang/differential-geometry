import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GRimPartialOfImm
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GRimRimParam

/-!
# FC39 GROUP G, RIMBOX: consumer of the partial-diffeomorphism kernel — the unscaled rim chart

Lane FC39-G-RIMBOX. On a boundaryless 3-manifold `Y`, the rim parametrization
`F = rimParam_GRIM Fl C κ` (`rimParam_props_GRIM`) is a partial diffeomorphism
`Circle × (ℝ × ℝ) ⇀ Y` with source `{|X| < κ δ, s ∈ (a₀, b₀)}` and target its image, on which
`P = s` and `B = −X` (`exists_rimChartUnscaled_GRIM`).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.GraphManifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0

variable {E H Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace Y] [ChartedSpace H Y] [IsManifold I ∞ Y]

/-- **The unscaled rim chart.** -/
theorem exists_rimChartUnscaled_GRIM (hdim : Module.finrank ℝ E = 3) {P B : Y → ℝ}
    (hP : ContMDiff I 𝓘(ℝ, ℝ) ∞ P) {U : TopologicalSpace.Opens Y} (Fl : ℝ → U ≃ₘ⟮I, I⟯ U)
    (hFl : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × U => Fl q.1 q.2)) {a₀ b₀ r' : ℝ}
    (hFlP : ∀ z : U, P z = 0 → -r' ≤ B z → ∀ t ∈ Ioo a₀ b₀, P (Fl t z) = t)
    (hFlB : ∀ (z : U) (t : ℝ), |B z| < r' → B (Fl t z) = B z)
    (C : EuclideanSpace ℝ (Fin 2) → Y) {δ κ : ℝ} (hκ : 0 < κ) (hδ1 : δ < 1) (hδr : κ * δ ≤ r')
    (hC : ContMDiffOn (𝓡 2) I ∞ C {z | |‖z‖ - 1| < δ}) (hCinj : InjOn C {z | |‖z‖ - 1| < δ})
    (hCimm : ∀ z, |‖z‖ - 1| < δ → Injective (mfderiv (𝓡 2) I C z))
    (hCP : ∀ z, |‖z‖ - 1| < δ → P (C z) = 0 ∧ B (C z) = κ * (1 - ‖z‖))
    (hCU : ∀ z, |‖z‖ - 1| < δ → C z ∈ U) :
    ∃ φ : PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ × ℝ)) I (Circle × (ℝ × ℝ)) Y ∞,
      φ.source = {p | |p.2.1| < κ * δ ∧ p.2.2 ∈ Ioo a₀ b₀} ∧
      φ.target = rimParam_GRIM Fl C κ '' {p | |p.2.1| < κ * δ ∧ p.2.2 ∈ Ioo a₀ b₀} ∧
      (∀ p, φ p = rimParam_GRIM Fl C κ p) ∧
      ∀ p ∈ φ.source, P (φ p) = p.2.2 ∧ B (φ p) = -p.2.1 := by
  obtain ⟨hsm, hinj, himm, hval⟩ :=
    rimParam_props_GRIM hP Fl hFl hFlP hFlB C hκ hδ1 hδr hC hCinj hCimm hCP hCU
  have hΩ : IsOpen {p : Circle × (ℝ × ℝ) | |p.2.1| < κ * δ ∧ p.2.2 ∈ Ioo a₀ b₀} :=
    (isOpen_lt (continuous_abs.comp (continuous_fst.comp continuous_snd)) continuous_const).inter
      (isOpen_Ioo.preimage (continuous_snd.comp continuous_snd))
  have hd : Module.finrank ℝ (EuclideanSpace ℝ (Fin 1) × (ℝ × ℝ)) = Module.finrank ℝ E := by
    rw [hdim]
    simp
  obtain ⟨φ, hs, ht, hφ⟩ := exists_partialDiffeomorph_of_injOn_immersion_GRIM
    (rimParam_GRIM Fl C κ) hΩ hsm hinj (fun p hp => himm p hp.1 hp.2) hd
  refine ⟨φ, hs, ht, hφ, fun p hp => ?_⟩
  rw [hs] at hp
  rw [hφ]
  exact hval p hp.1 hp.2

end GC.GraphManifold.Assembly.FC39P0
