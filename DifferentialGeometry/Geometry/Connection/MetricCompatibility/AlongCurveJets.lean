import DifferentialGeometry.Geometry.Connection.ParallelTransport.CovariantDerivativeRegularity
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.AlongCurve
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

noncomputable section

open Bundle Filter Set
open scoped Manifold ContDiff Topology Bundle

namespace DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [T2Space M]

omit [FiniteDimensional ℝ E] [BoundarylessManifold I M] [T2Space M] in
private theorem contDiffAt_inner_along
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M}
    {V W : ∀ t, TangentSpace I (γ t)} {t : ℝ} {n : ℕ∞ω}
    (hV : ContMDiffAt 𝓘(ℝ, ℝ) I.tangent n
      (fun s => (⟨γ s, V s⟩ : TangentBundle I M)) t)
    (hW : ContMDiffAt 𝓘(ℝ, ℝ) I.tangent n
      (fun s => (⟨γ s, W s⟩ : TangentBundle I M)) t) (hn : n ≤ ∞) :
    ContDiffAt ℝ n (fun s => g.inner (γ s) (V s) (W s)) t := by
  have hγ := (contMDiff_proj (TangentSpace I)).contMDiffAt.comp t hV
  have hg := (g.contMDiff.contMDiffAt.of_le hn).comp t hγ
  have htotal := ContMDiffAt.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ) (E₃ := Bundle.Trivial M ℝ) hg hV hW
  rw [contMDiffAt_totalSpace] at htotal
  exact htotal.2.contDiffAt

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem eventually_deriv_inner
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M}
    {V W : ∀ t, TangentSpace I (γ t)} {t : ℝ}
    (hV : ContMDiffAt 𝓘(ℝ, ℝ) I.tangent 1
      (fun s => (⟨γ s, V s⟩ : TangentBundle I M)) t)
    (hW : ContMDiffAt 𝓘(ℝ, ℝ) I.tangent 1
      (fun s => (⟨γ s, W s⟩ : TangentBundle I M)) t) :
    deriv (fun s => g.inner (γ s) (V s) (W s)) =ᶠ[𝓝 t]
      fun s => g.inner (γ s) (V s) (covDerivAlong g γ W s) +
        g.inner (γ s) (covDerivAlong g γ V s) (W s) := by
  let : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  have hmetric : @_root_.CovariantDerivative.IsMetricCompatible E _ _ H _ I M
      inferInstance inferInstance E inferInstance inferInstance (TangentSpace I)
      inferInstance inferInstance inferInstance inferInstance (Connection.LeviCivita g)
      inferInstance inferInstance inferInstance inferInstance := by
    apply (_root_.CovariantDerivative.isMetricCompatible_iff _).mpr
    intro x X V W hX hVs hWs
    exact (Connection.LeviCivita_isMetricCompatible g).apply hVs hWs (X x)
  have hVnear := (contMDiffAt_iff_contMDiffAt_nhds (n := 1) (by simp)).mp hV
  have hWnear := (contMDiffAt_iff_contMDiffAt_nhds (n := 1) (by simp)).mp hW
  filter_upwards [hVnear, hWnear] with s hVs hWs
  have hγ := (contMDiff_proj (TangentSpace I)).contMDiffAt.comp s hVs
  have h := hmetric.derivAlongWithin_inner (J := Set.univ)
    (hVs.mdifferentiableAt (by simp)).mdifferentiableWithinAt
    (hWs.mdifferentiableAt (by simp)).mdifferentiableWithinAt
  rw [derivWithin_univ,
    Connection.derivAlongWithin_leviCivita_eq_covDerivAlong g γ V Filter.univ_mem
      (hγ.mdifferentiableAt (by simp)) BoundarylessManifold.isInteriorPoint,
    Connection.derivAlongWithin_leviCivita_eq_covDerivAlong g γ W Filter.univ_mem
      (hγ.mdifferentiableAt (by simp)) BoundarylessManifold.isInteriorPoint] at h
  exact h.trans (add_comm _ _)

theorem iteratedDeriv_inner
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M}
    {V W : ∀ t, TangentSpace I (γ t)} {t : ℝ} (n : ℕ)
    (hV : ContMDiffAt 𝓘(ℝ, ℝ) I.tangent n
      (fun s => (⟨γ s, V s⟩ : TangentBundle I M)) t)
    (hW : ContMDiffAt 𝓘(ℝ, ℝ) I.tangent n
      (fun s => (⟨γ s, W s⟩ : TangentBundle I M)) t) :
    iteratedDeriv n (fun s => g.inner (γ s) (V s) (W s)) t =
      ∑ k ∈ Finset.range (n + 1), n.choose k • g.inner (γ t)
        (((covDerivAlong g γ)^[k]) V t) (((covDerivAlong g γ)^[n - k]) W t) := by
  induction n generalizing V W with
  | zero => simp
  | succ n ih =>
    have hn : (n : ℕ∞ω) ≤ ↑(n + 1) := by exact_mod_cast Nat.le_succ n
    have hone : (1 : ℕ∞ω) ≤ ↑(n + 1) := by exact_mod_cast Nat.succ_pos n
    have hDV := contMDiffAt_covDerivAlong_of_isInteriorPoint g (m := (n : ℕ∞)) hV (by simp)
      BoundarylessManifold.isInteriorPoint
    have hDW := contMDiffAt_covDerivAlong_of_isInteriorPoint g (m := (n : ℕ∞)) hW (by simp)
      BoundarylessManifold.isInteriorPoint
    have hVn := hV.of_le hn
    have hWn := hW.of_le hn
    have hpair₁ := contDiffAt_inner_along g hVn hDW (by exact_mod_cast (le_top : n ≤ (⊤ : ℕ∞)))
    have hpair₂ := contDiffAt_inner_along g hDV hWn (by exact_mod_cast (le_top : n ≤ (⊤ : ℕ∞)))
    rw [iteratedDeriv_succ',
      (eventually_deriv_inner g (hV.of_le hone) (hW.of_le hone)).iteratedDeriv_eq n,
      iteratedDeriv_fun_add hpair₁ hpair₂, ih hVn hDW, ih hDV hWn]
    nth_rw 3 [Finset.sum_range_succ']
    rw [Finset.sum_range_succ']
    simp only [Nat.choose_succ_succ', add_smul, Finset.sum_add_distrib]
    nth_rw 3 [Finset.sum_range_succ]
    have hsub : ∀ i ∈ Finset.range n, 1 ≤ n - i := by simp; omega
    have hcancel (i : ℕ) : n + 1 - i - 1 = n - i := by omega
    have hchoose : n.choose (n + 1) = 0 := Nat.choose_eq_zero_of_lt (Nat.lt_succ_self n)
    simp +contextual only [← Function.iterate_succ_apply, Nat.succ_eq_add_one,
      ← Nat.sub_sub, Nat.sub_add_cancel, hsub, hcancel,
      Nat.choose_zero_right, Function.iterate_zero_apply, Nat.sub_zero,
      one_smul, Nat.sub_self, hchoose, zero_smul, add_zero]
    abel

end DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
