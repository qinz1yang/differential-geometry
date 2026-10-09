import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Finite.ChartPullback

/-!
# Pullback-coefficient convergence along varying coordinate changes (LFR48, tier T3)

LFR48 (A:29037) replaces the `C^K` comparison maps `jᵢ` of LFR14 by smooth maps `j̃ᵢ` and must keep
the convergence of the pulled-back metric coefficients. In a chart, `j̃ᵢ ∘ φ⁻¹ = (jᵢ ∘ φ⁻¹) ∘ Aᵢ`
with `Aᵢ = φ ∘ jᵢ⁻¹ ∘ j̃ᵢ ∘ φ⁻¹ → id`. The interface I-CHART
(`mapCPConvergenceOn_pullbackMetricCoefficients_comp`) treats a FIXED coordinate change; the
wrappers of `Geometry/Metric/Pullback/FiniteCoefficientConvergence.lean` need SMOOTH `Φ i`.

* `mapCPConvergenceOn_pullbackMetricCoefficients_comp_seq` (T3 kernel): if the coefficients of
  `g i` along `f i` (`C^{m+1}` on an open `V`) converge in `C^m` to `B` on the compacts of `V`, and
  the coordinate changes `A i` are eventually `C^{m+1}` on an open `W ⊆ V`, map `W` into `V` and
  converge to the identity in `C^{m+1}` on a compact `L ⊆ W`, then the coefficients along
  `f i ∘ A i` converge in `C^m` to the SAME `B` on `L`.
* Consumer `mapCPConvergenceOn_pullbackMetricCoefficients_comp_seq_const`: one fixed `C^{m+1}`
  map `f` into a fixed manifold.

Route: chain rule (`pullbackMetricCoefficients_comp_eq_pullbackForm`) past a regularity threshold,
the index shift `MapCPConvergenceOn.of_comp_add`, and lane P2's kernel
`mapCPConvergenceOn_pullbackForm_comp_fderiv_locally` with `Ainf = id`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.CheegerGromovCompactness

open DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

/-- **LFR48 T3: pullback coefficients along coordinate changes converging to the identity.** -/
theorem mapCPConvergenceOn_pullbackMetricCoefficients_comp_seq
    {Y : ℕ → Type*} [∀ i, TopologicalSpace (Y i)] [∀ i, ChartedSpace H (Y i)]
    [∀ i, IsManifold I ∞ (Y i)]
    (g : ∀ i, SmoothRiemannianMetric I (Y i)) {m : ℕ}
    (f : ∀ i, E → Y i) (A : ℕ → E → E) {V W L : Set E} (hV : IsOpen V) (hW : IsOpen W)
    (hf : ∀ᶠ i in atTop, ContMDiffOn 𝓘(ℝ, E) I (m + 1 : ℕ) (f i) V)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (hB : ContDiffOn ℝ m B V)
    (hconv : ∀ S : Set E, IsCompact S → S ⊆ V →
      MapCPConvergenceOn S m (fun i => pullbackMetricCoefficients (g i) (f i)) B)
    (hL : IsCompact L) (hLW : L ⊆ W) (hWV : W ⊆ V)
    (hAc : ∀ᶠ i in atTop, ContDiffOn ℝ (m + 1 : ℕ) (A i) W ∧ MapsTo (A i) W V)
    (hA : MapCPConvergenceOn L (m + 1) A id) :
    MapCPConvergenceOn L m (fun i => pullbackMetricCoefficients (g i) (f i ∘ A i)) B := by
  obtain ⟨k₁, hk₁⟩ := eventually_atTop.mp (hf.and hAc)
  have hfk (k : ℕ) : ContMDiffOn 𝓘(ℝ, E) I (m + 1 : ℕ) (f (k + k₁)) V :=
    (hk₁ (k + k₁) (Nat.le_add_left k₁ k)).1
  have hAk (k : ℕ) : ContDiffOn ℝ (m + 1 : ℕ) (A (k + k₁)) W ∧ MapsTo (A (k + k₁)) W V :=
    (hk₁ (k + k₁) (Nat.le_add_left k₁ k)).2
  let P : ℕ → E → E →L[ℝ] E →L[ℝ] ℝ := fun k =>
    pullbackMetricCoefficients (g (k + k₁)) (f (k + k₁))
  have hPc (k : ℕ) : ContDiffOn ℝ m (P k) V :=
    Bundle.ContMDiffRiemannianMetric.contDiffOn_pullback_inner (g (k + k₁))
      (r := (m : ℕ∞ω)) (s := ((m + 1 : ℕ) : ℕ∞ω)) (by exact_mod_cast le_top)
      (by push_cast; exact le_rfl) hV (hfk k)
  have hPconv : ∀ S : Set E, IsCompact S → S ⊆ V → MapCPConvergenceOn S m P B :=
    fun S hS hSV => (hconv S hS hSV).comp_tendsto_atTop (tendsto_add_atTop_nat k₁)
  have hAconv : MapCPConvergenceOn L (m + 1) (fun k => A (k + k₁)) id :=
    hA.comp_tendsto_atTop (tendsto_add_atTop_nat k₁)
  have hmain := mapCPConvergenceOn_pullbackForm_comp_fderiv_locally (U := V) (p := m) hV hL
    (A := fun k => A (k + k₁)) (Ainf := id) (B := P) (Binf := B) hAconv hPconv
    ⟨W, hW, hLW, hWV, Eventually.of_forall fun k => hAk k⟩ contDiffOn_id hPc hB (mapsTo_id _)
  have hm1 : ((m + 1 : ℕ) : ℕ∞ω) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  have heq (k : ℕ) : EqOn (pullbackMetricCoefficients (g (k + k₁)) (f (k + k₁) ∘ A (k + k₁)))
      (fun x => pullbackForm (P k (A (k + k₁) x), fderiv ℝ (A (k + k₁)) x)) W := by
    intro x hx
    have hfx : MDifferentiableAt 𝓘(ℝ, E) I (f (k + k₁)) (A (k + k₁) x) :=
      ((hfk k).contMDiffAt (hV.mem_nhds ((hAk k).2 hx))).mdifferentiableAt hm1
    have hAx : DifferentiableAt ℝ (A (k + k₁)) x :=
      ((hAk k).1.differentiableOn (by exact_mod_cast hm1) x hx).differentiableAt
        (hW.mem_nhds hx)
    exact pullbackMetricCoefficients_comp_eq_pullbackForm (g (k + k₁)) hfx hAx
  have hlim : EqOn B (fun x => pullbackForm (B (id x), fderiv ℝ id x)) W := by
    intro x _
    ext v w
    simp [pullbackForm_apply]
  exact MapCPConvergenceOn.of_comp_add k₁ (hmain.congr hW hLW heq hlim)

/-- Consumer of T3: for ONE `C^{m+1}` map `f` into a fixed manifold, the coefficients along
`f ∘ A i` converge in `C^m` to those along `f` when `A i → id` in `C^{m+1}`. -/
theorem mapCPConvergenceOn_pullbackMetricCoefficients_comp_seq_const
    {Y : Type*} [TopologicalSpace Y] [ChartedSpace H Y] [IsManifold I ∞ Y]
    (g : SmoothRiemannianMetric I Y) {m : ℕ} {f : E → Y} {V W L : Set E} (hV : IsOpen V)
    (hW : IsOpen W) (hf : ContMDiffOn 𝓘(ℝ, E) I (m + 1 : ℕ) f V) (A : ℕ → E → E)
    (hL : IsCompact L) (hLW : L ⊆ W) (hWV : W ⊆ V)
    (hAc : ∀ᶠ i in atTop, ContDiffOn ℝ (m + 1 : ℕ) (A i) W ∧ MapsTo (A i) W V)
    (hA : MapCPConvergenceOn L (m + 1) A id) :
    MapCPConvergenceOn L m (fun i => pullbackMetricCoefficients g (f ∘ A i))
      (pullbackMetricCoefficients g f) := by
  have hB : ContDiffOn ℝ m (pullbackMetricCoefficients g f) V :=
    Bundle.ContMDiffRiemannianMetric.contDiffOn_pullback_inner g
      (r := (m : ℕ∞ω)) (s := ((m + 1 : ℕ) : ℕ∞ω)) (by exact_mod_cast le_top)
      (by push_cast; exact le_rfl) hV hf
  exact mapCPConvergenceOn_pullbackMetricCoefficients_comp_seq (Y := fun _ => Y) (fun _ => g)
    (fun _ => f) A hV hW (Eventually.of_forall fun _ => hf) _ hB
    (fun _ _ _ => MapCPConvergenceOn.const_seq _) hL hLW hWV hAc hA

end DifferentialGeometry.CheegerGromovCompactness
