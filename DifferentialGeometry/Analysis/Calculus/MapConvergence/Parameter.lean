import DifferentialGeometry.Analysis.Calculus.MapConvergence.Composition
import DifferentialGeometry.Analysis.Calculus.PartialDerivative.Parameter

set_option autoImplicit false
noncomputable section
open Filter Set
open scoped Topology ContDiff
namespace DifferentialGeometry.CheegerGromovCompactness

variable {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem mapCInfConvergenceOnCompacts_of_tendsto_parameter
    {G : P → E → F} {A : Set P} {V : Set E} (hV : IsOpen V)
    (hG : ContDiffOn ℝ ∞ (Function.uncurry G) (A ×ˢ V))
    (τ : ℕ → P) (hτ : ∀ n, τ n ∈ A) {p : P} (hp : p ∈ A)
    (htend : Tendsto τ atTop (𝓝 p)) :
    MapCInfConvergenceOnCompacts V (fun n => G (τ n)) (G p) := by
  intro K hK hKV m
  have hs (q : P) (hq : q ∈ A) : ContDiffOn ℝ ∞ (G q) V :=
    hG.comp (f := fun x => (q, x)) (contDiffOn_const.prodMk contDiffOn_id)
      (fun _ hx => ⟨hq, hx⟩)
  apply mapCPConvergenceOn_of_tendstoUniformlyOn hV hKV
    (fun n => (hs (τ n) (hτ n)).of_le (by exact_mod_cast le_top))
    ((hs p hp).of_le (by exact_mod_cast le_top))
  intro r _hr
  exact (hG.tendstoUniformlyOn_iteratedFDeriv_snd hV hK hKV r
    (by exact_mod_cast le_top) hp).seq_tendstoUniformlyOn τ
      (tendsto_nhdsWithin_iff.mpr ⟨htend, Filter.Eventually.of_forall hτ⟩)

theorem mapCInfConvergenceOnCompacts_smul_of_tendsto_parameter
    {G : P → E → F} {A : Set P} {V : Set E} (hV : IsOpen V)
    (hG : ContDiffOn ℝ ∞ (Function.uncurry G) (A ×ˢ V))
    (τ : ℕ → P) (hτ : ∀ n, τ n ∈ A) {p : P} (hp : p ∈ A)
    (htend : Tendsto τ atTop (𝓝 p))
    (w : ℕ → ℝ) {w₀ : ℝ} (hw : Tendsto w atTop (𝓝 w₀)) :
    MapCInfConvergenceOnCompacts V (fun n x => w n • G (τ n) x)
      (fun x => w₀ • G p x) := by
  have hfamily : ContDiffOn ℝ ∞
      (fun q : (ℝ × P) × E => q.1.1 • G q.1.2 q.2) ((univ ×ˢ A) ×ˢ V) :=
    contDiffOn_fst.fst.smul
      (hG.comp (f := fun q : (ℝ × P) × E => (q.1.2, q.2))
        (contDiffOn_fst.snd.prodMk contDiffOn_snd) (fun _ hq => ⟨hq.1.2, hq.2⟩))
  exact mapCInfConvergenceOnCompacts_of_tendsto_parameter
    (P := ℝ × P) (A := (univ : Set ℝ) ×ˢ A) (p := (w₀, p))
    (G := fun (q : ℝ × P) (x : E) => q.1 • G q.2 x) hV hfamily (fun n => (w n, τ n))
    (fun n => ⟨mem_univ _, hτ n⟩) ⟨mem_univ _, hp⟩ (hw.prodMk_nhds htend)

end DifferentialGeometry.CheegerGromovCompactness
