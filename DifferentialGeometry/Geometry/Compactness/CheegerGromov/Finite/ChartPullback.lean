import DifferentialGeometry.Analysis.Calculus.MapConvergence.FinitePullback
import DifferentialGeometry.Analysis.Calculus.MapConvergence.FiniteOrder
import DifferentialGeometry.Geometry.Metric.Pullback.Coefficients
import DifferentialGeometry.Geometry.Metric.Pullback.FiniteCoefficients
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# LFR14, interface I-CHART: `C^m` pullback convergence along a fixed coordinate change

Blueprint LFR14 (master207A.tex:25869), step 4 ("`f_{i,a}^* g_i → g` in `C^{K-1}`") and step 5:
the convergence of the pulled-back metric coefficients proved in one coordinate system transfers
to any other coordinate system related by a fixed `C^{m+1}` change of coordinates `τ`.

* `MapCPConvergenceOn.of_comp_add`: `C^p` convergence of a tail `k ↦ Φ (k + k₁)` is `C^p`
  convergence of `Φ`.
* `mapCPConvergenceOn_pullbackMetricCoefficients_comp`: the frozen interface I-CHART of
  `build-logs/scratch/D-LFR14/Interfaces.lean:262`, verbatim.
* Consumer `mapCPConvergenceOn_pullbackMetricCoefficients_comp_clm`: the case of a fixed linear
  change of coordinates.

Route: chain rule (`mfderiv_comp`) on the open `U` gives
`pullbackMetricCoefficients (g i) (f i ∘ τ) = pullbackForm (pullbackMetricCoefficients (g i) (f i) ∘ τ, Dτ)`
for every `i` past the regularity threshold; after the index shift, lane P2's
`mapCPConvergenceOn_pullbackForm_comp_fderiv_locally` (MapConvergence/FinitePullback.lean:77)
with the constant inner sequence `τ` gives the convergence, and the finite-order regularity of the
coefficients is `Bundle.ContMDiffRiemannianMetric.contDiffOn_pullback_inner`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.CheegerGromovCompactness

open DifferentialGeometry.Geometry

/-- `C^p` convergence of a tail of a sequence implies `C^p` convergence of the sequence. -/
theorem MapCPConvergenceOn.of_comp_add {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {K : Set E} {p : ℕ} {Φ : ℕ → E → F}
    {Φinf : E → F} (k₁ : ℕ) (h : MapCPConvergenceOn K p (fun k => Φ (k + k₁)) Φinf) :
    MapCPConvergenceOn K p Φ Φinf := by
  intro ε hε
  obtain ⟨k₀, hk₀⟩ := h ε hε
  refine ⟨k₀ + k₁, fun k hk r hr x hx => ?_⟩
  have hb : mapDerivNorm r (Φ (k - k₁ + k₁)) Φinf x ≤ ε := hk₀ (k - k₁) (by omega) r hr x hx
  rwa [Nat.sub_add_cancel (by omega)] at hb

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

omit [FiniteDimensional ℝ E] in
/-- The chain rule for pulled-back metric coefficients along a coordinate change. -/
theorem pullbackMetricCoefficients_comp_eq_pullbackForm {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M] (g : SmoothRiemannianMetric I M) {f : E → M}
    {τ : E → E} {u : E} (hf : MDifferentiableAt 𝓘(ℝ, E) I f (τ u))
    (hτ : DifferentiableAt ℝ τ u) :
    pullbackMetricCoefficients g (f ∘ τ) u =
      pullbackForm (pullbackMetricCoefficients g f (τ u), fderiv ℝ τ u) := by
  have hd : mfderiv 𝓘(ℝ, E) I (f ∘ τ) u =
      (mfderiv 𝓘(ℝ, E) I f (τ u)).comp (fderiv ℝ τ u) := by
    rw [mfderiv_comp u hf hτ.mdifferentiableAt, mfderiv_eq_fderiv]
    rfl
  ext v w
  rw [pullbackMetricCoefficients_apply, hd, pullbackForm_apply,
    pullbackMetricCoefficients_apply]
  rfl

/-- **I-CHART (LFR14 step 4).** `C^m` convergence of pulled-back smooth metrics along `fᵢ` on the
compacts of `V` transfers along a fixed `C^{m+1}` coordinate change `τ : U → V`. -/
theorem mapCPConvergenceOn_pullbackMetricCoefficients_comp
    {Y : ℕ → Type*} [∀ i, TopologicalSpace (Y i)] [∀ i, ChartedSpace H (Y i)]
    [∀ i, IsManifold I ∞ (Y i)]
    (g : ∀ i, SmoothRiemannianMetric I (Y i)) {m : ℕ}
    (f : ∀ i, E → Y i) (τ : E → E) {U V : Set E} (hU : IsOpen U) (hV : IsOpen V)
    (hτ : ContDiffOn ℝ (m + 1 : ℕ) τ U) (hτUV : MapsTo τ U V)
    (hf : ∀ᶠ i in atTop, ContMDiffOn 𝓘(ℝ, E) I (m + 1 : ℕ) (f i) V)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (hB : ContDiffOn ℝ m B V)
    (hconv : ∀ S : Set E, IsCompact S → S ⊆ V →
      MapCPConvergenceOn S m (fun i => pullbackMetricCoefficients (g i) (f i)) B)
    {L : Set E} (hL : IsCompact L) (hLU : L ⊆ U) :
    MapCPConvergenceOn L m (fun i => pullbackMetricCoefficients (g i) (f i ∘ τ))
      (fun u => (B (τ u)).bilinearComp (fderiv ℝ τ u) (fderiv ℝ τ u)) := by
  obtain ⟨k₁, hk₁⟩ := eventually_atTop.mp hf
  have hfk (k : ℕ) : ContMDiffOn 𝓘(ℝ, E) I (m + 1 : ℕ) (f (k + k₁)) V :=
    hk₁ (k + k₁) (Nat.le_add_left k₁ k)
  let P : ℕ → E → E →L[ℝ] E →L[ℝ] ℝ := fun k =>
    pullbackMetricCoefficients (g (k + k₁)) (f (k + k₁))
  have hPc (k : ℕ) : ContDiffOn ℝ m (P k) V :=
    Bundle.ContMDiffRiemannianMetric.contDiffOn_pullback_inner (g (k + k₁))
      (r := (m : ℕ∞ω)) (s := ((m + 1 : ℕ) : ℕ∞ω)) (by exact_mod_cast le_top)
      (by push_cast; exact le_rfl) hV (hfk k)
  have hPconv : ∀ S : Set E, IsCompact S → S ⊆ V → MapCPConvergenceOn S m P B :=
    fun S hS hSV => (hconv S hS hSV).comp_tendsto_atTop (tendsto_add_atTop_nat k₁)
  have hmain := mapCPConvergenceOn_pullbackForm_comp_fderiv_locally (U := U) (p := m) hV hL
    (A := fun _ => τ) (Ainf := τ) (B := P) (Binf := B) (MapCPConvergenceOn.const_seq τ) hPconv
    ⟨U, hU, hLU, subset_rfl, Eventually.of_forall fun _ => ⟨hτ, hτUV⟩⟩ hτ hPc hB hτUV
  have hm1 : ((m + 1 : ℕ) : ℕ∞ω) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  have heq (k : ℕ) : EqOn (pullbackMetricCoefficients (g (k + k₁)) (f (k + k₁) ∘ τ))
      (fun x => pullbackForm (P k (τ x), fderiv ℝ τ x)) U := by
    intro x hx
    have hfx : MDifferentiableAt 𝓘(ℝ, E) I (f (k + k₁)) (τ x) :=
      ((hfk k).contMDiffAt (hV.mem_nhds (hτUV hx))).mdifferentiableAt hm1
    have hτx : DifferentiableAt ℝ τ x :=
      (hτ.differentiableOn (by exact_mod_cast hm1) x hx).differentiableAt (hU.mem_nhds hx)
    exact pullbackMetricCoefficients_comp_eq_pullbackForm (g (k + k₁)) hfx hτx
  exact MapCPConvergenceOn.of_comp_add k₁
    (hmain.congr hU hLU heq (Set.eqOn_refl _ _))

/-- Consumer: the case of a fixed linear change of coordinates `A` (`U = A⁻¹ V`). -/
theorem mapCPConvergenceOn_pullbackMetricCoefficients_comp_clm
    {Y : ℕ → Type*} [∀ i, TopologicalSpace (Y i)] [∀ i, ChartedSpace H (Y i)]
    [∀ i, IsManifold I ∞ (Y i)]
    (g : ∀ i, SmoothRiemannianMetric I (Y i)) {m : ℕ}
    (f : ∀ i, E → Y i) (A : E →L[ℝ] E) {V : Set E} (hV : IsOpen V)
    (hf : ∀ᶠ i in atTop, ContMDiffOn 𝓘(ℝ, E) I (m + 1 : ℕ) (f i) V)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (hB : ContDiffOn ℝ m B V)
    (hconv : ∀ S : Set E, IsCompact S → S ⊆ V →
      MapCPConvergenceOn S m (fun i => pullbackMetricCoefficients (g i) (f i)) B)
    {L : Set E} (hL : IsCompact L) (hLV : MapsTo A L V) :
    MapCPConvergenceOn L m (fun i => pullbackMetricCoefficients (g i) (f i ∘ A))
      (fun u => (B (A u)).bilinearComp A A) := by
  have h := mapCPConvergenceOn_pullbackMetricCoefficients_comp g f A
    (hV.preimage A.continuous) hV A.contDiff.contDiffOn (fun _ hx => hx) hf B hB hconv hL hLV
  simpa only [ContinuousLinearMap.fderiv] using h

end DifferentialGeometry.CheegerGromovCompactness
