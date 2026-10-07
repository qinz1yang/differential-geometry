import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.BufferedCores

set_option autoImplicit false

noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set
open Manifold GC.LongTime
open scoped Manifold ContDiff ENNReal

universe u

namespace GC.LongTime.Ch12

/-! CH12-O20 G2: the static window of one dyadic step (HPI03 step (i)), from `hLTF04`
(S45 `[FROZEN v2]`, with `InjOn`; `ckErr_S45` written out, defeq) and the inline `Good`
invariant of `hpi03_discrete_of_step_O20` at a precision `b` that beats the hLTF04
threshold `δ`.  Output = the window conjuncts of the step binder `hstep`
(`f t = g₁` on `B(4R)`; smooth, injective, `ckErr < ε` through order `k` on `B(4R)`). -/

theorem dyadic_window_O20 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (H : FiniteVolumeHyperbolicModel.{u})
    (hLTF04 : ∀ (H' : FiniteVolumeHyperbolicModel.{u}) (R' ε' : ℝ) (k' : ℕ), 0 < R' → 0 < ε' →
      ∃ δ' T : ℝ, 0 < δ' ∧ 0 < T ∧ ∀ (t : ℝ) (_ht0 : 0 < t) (_htT : T ≤ t)
        (U : TopologicalSpace.Opens H'.Carrier)
        (f : H'.Carrier → (postStage F.observation t).Carrier),
        riemannianBallOf H'.metric H'.basepoint (2 * R') ⊆ U →
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U →
        IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => f x) →
        (∀ j : ℕ, j ≤ k' + 3 → ∀ p ∈ riemannianBallOf H'.metric H'.basepoint (2 * R'),
          tensor0SFiberNorm H'.metric p (2 + j)
          (iteratedMetricCovariantDerivative H'.metric 2
            (fun q : H'.Carrier =>
              ((continuousMultilinearCurryFin1 ℝ (TangentSpace (𝓡 3) q) ℝ).symm.toContinuousLinearMap.comp
                (t⁻¹ • localPullInner (postMetric F.observation t) f q - H'.metric.inner q)).uncurryLeft) j p) < δ') →
        ∃ fs : (s : ℝ) → s ∈ Icc t (2 * t) → H'.Carrier → (postStage F.observation s).Carrier,
          (∀ p ∈ riemannianBallOf H'.metric H'.basepoint (R'), fs t ⟨le_rfl, by linarith⟩ p = f p) ∧
          ∀ (s : ℝ) (hs : s ∈ Icc t (2 * t)),
            ContMDiffOn (𝓡 3) (𝓡 3) ∞ (fs s hs) (riemannianBallOf H'.metric H'.basepoint (R')) ∧
            Set.InjOn (fs s hs) (riemannianBallOf H'.metric H'.basepoint (R')) ∧
            (∀ j : ℕ, j ≤ k' → ∀ p ∈ riemannianBallOf H'.metric H'.basepoint (R'),
              tensor0SFiberNorm H'.metric p (2 + j)
          (iteratedMetricCovariantDerivative H'.metric 2
            (fun q : H'.Carrier =>
              ((continuousMultilinearCurryFin1 ℝ (TangentSpace (𝓡 3) q) ℝ).symm.toContinuousLinearMap.comp
                (s⁻¹ • localPullInner (postMetric F.observation s) (fs s hs) q - H'.metric.inner q)).uncurryLeft) j p) < ε') ∧
            ∃ (n : ℕ) (first last : Fin ((F.tower.history n).eventCount + 1))
              (ordered : first ≤ last) (a b : ℝ) (_ : a ≤ t) (_ : a ≤ s) (_ : s < b)
              (_ : b ≤ (F.tower.history n).horizon)
              (stages : ∀ r : Icc (0 : ℝ) (F.tower.history n).horizon, (r : ℝ) ∈ Ico a b →
                first ≤ (F.tower.history n).toHistory.activeStage r ∧
                  (F.tower.history n).toHistory.activeStage r ≤ last)
              (φ : H'.Carrier →
                (F.tower.history n).toHistory.backwardSurvivorDomain first last ordered),
              ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ (riemannianBallOf H'.metric H'.basepoint (R')) ∧
              ∀ (r : Icc (0 : ℝ) (F.tower.history n).horizon) (hr : (r : ℝ) ∈ Ico a b)
                (hrs : (r : ℝ) ∈ Icc t (2 * t)),
                ∀ p ∈ riemannianBallOf H'.metric H'.basepoint (R'),
                  HEq ((F.tower.history n).toHistory.backwardSurvivorMap first last ordered
                    ((F.tower.history n).toHistory.activeStage r) (stages r hr).1 (stages r hr).2
                    (φ p)) (fs r hrs p)) (R ε : ℝ) (k : ℕ) (hR : 0 < R) (hε : 0 < ε) :
    ∃ δ Tw : ℝ, 0 < δ ∧ ∀ (t t₂ : ℝ), 0 < t → Tw ≤ t → t₂ = 2 * t →
      ∀ b : ℝ, b ≤ δ → 4 * R ≤ b⁻¹ → (k : ℝ) + 3 ≤ b⁻¹ →
      ∀ g₁ : H.Carrier → (postStage F.observation t).Carrier,
      (∃ U : TopologicalSpace.Opens H.Carrier,
        riemannianBallOf H.metric H.basepoint (2 * b⁻¹) ⊆ U ∧
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ g₁ U ∧
        IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => g₁ x) ∧
        ∀ k : ℕ, k ≤ ⌈b⁻¹⌉₊ → ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * b⁻¹),
          tensor0SFiberNorm H.metric p (2 + k)
          (iteratedMetricCovariantDerivative H.metric 2
            (fun q : H.Carrier =>
              ((continuousMultilinearCurryFin1 ℝ (TangentSpace (𝓡 3) q) ℝ).symm.toContinuousLinearMap.comp
                (t⁻¹ • localPullInner (postMetric F.observation t) g₁ q - H.metric.inner q)).uncurryLeft) k p) < b) →
      ∃ f : (s : ℝ) → s ∈ Icc t t₂ → H.Carrier → (postStage F.observation s).Carrier,
        (∀ (h0 : t ∈ Icc t t₂), ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * R), f t h0 p = g₁ p) ∧
        ∀ s (hs : s ∈ Icc t t₂),
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ (f s hs) (riemannianBallOf H.metric H.basepoint (4 * R)) ∧
          Set.InjOn (f s hs) (riemannianBallOf H.metric H.basepoint (4 * R)) ∧
          ∀ k' : ℕ, k' ≤ k → ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * R),
            tensor0SFiberNorm H.metric p (2 + k')
          (iteratedMetricCovariantDerivative H.metric 2
            (fun q : H.Carrier =>
              ((continuousMultilinearCurryFin1 ℝ (TangentSpace (𝓡 3) q) ℝ).symm.toContinuousLinearMap.comp
                (s⁻¹ • localPullInner (postMetric F.observation s) (f s hs) q - H.metric.inner q)).uncurryLeft) k' p) < ε := by
  obtain ⟨δ', T, hδ', -, hw⟩ := hLTF04 H (4 * R) ε k (by positivity) hε
  refine ⟨δ', T, hδ', ?_⟩
  intro t t₂ ht hTt ht₂ b hbδ hRb hkb g₁ ⟨U, hU, hsm, hemb, herr⟩
  subst ht₂
  have hball : riemannianBallOf H.metric H.basepoint (2 * (4 * R)) ⊆
      riemannianBallOf H.metric H.basepoint (2 * b⁻¹) :=
    riemannianBallOf_mono _ _ (by linarith)
  have hord : ∀ j : ℕ, j ≤ k + 3 → j ≤ ⌈b⁻¹⌉₊ := fun j hj => by
    have h1 : ((k + 3 : ℕ) : ℝ) ≤ (⌈b⁻¹⌉₊ : ℝ) := by
      push_cast
      exact hkb.trans (Nat.le_ceil _)
    exact hj.trans (Nat.cast_le.1 h1)
  obtain ⟨fs, hfs0, hfs⟩ := hw t ht hTt U g₁ (hball.trans hU) hsm hemb
    (fun j hj p hp => (herr j (hord j hj) p (hball hp)).trans_le hbδ)
  exact ⟨fs, fun _ p hp => hfs0 p hp, fun s hs =>
    ⟨(hfs s hs).1, (hfs s hs).2.1, (hfs s hs).2.2.1⟩⟩

/-- Endpoint algebra of one dyadic step (orientation of the transfer isotopy).  With
`A = invFunOn φ U' ∘ f` (S7 output) and a two-time flow `Ψ` (CX3 output) with
`Ψ 0 1 = e.symm ∘ A` on `D` (`e` from S1), the isotopy `E μ := Ψ μ 0` starts at the identity,
is bijective for every `μ` (inverse `Ψ 0 μ`), is the identity off the support `C`, and
satisfies the S8 endpoint identity `f ∘ E 1 = φ ∘ e` at every `p` with `Ψ 1 0 p ∈ D`.
(The sheet's `E 1 := e⁻¹ ∘ A` has the wrong orientation: the endpoint needs `(e⁻¹ ∘ A)⁻¹`.) -/
theorem dyadic_endpoint_algebra_O20 {M M' N : Type*} [Nonempty M'] (f : M → N) (φ : M' → N)
    (U' : Set M') (e : M ≃ M') (Ψ : ℝ → ℝ → M → M) (D C : Set M)
    (hf : ∀ x ∈ D, f x ∈ φ '' U')
    (hΨid : ∀ s y, Ψ s s y = y) (hΨgrp : ∀ s t u y, Ψ t u (Ψ s t y) = Ψ s u y)
    (hΨC : ∀ s t y, y ∉ C → Ψ s t y = y)
    (hΨ1 : ∀ x ∈ D, Ψ 0 1 x = e.symm (Function.invFunOn φ U' (f x))) :
    (∀ p, Ψ 0 0 p = p) ∧
    (∀ μ, Function.Bijective (fun p => Ψ μ 0 p)) ∧
    (∀ μ p, p ∉ C → Ψ μ 0 p = p) ∧
    ∀ p, Ψ 1 0 p ∈ D → f (Ψ 1 0 p) = φ (e p) := by
  refine ⟨fun p => hΨid 0 p, fun μ => ?_, fun μ p hp => hΨC μ 0 p hp, fun p hp => ?_⟩
  · refine ⟨fun x y hxy => ?_, fun y => ⟨Ψ 0 μ y, ?_⟩⟩
    · have h := congrArg (Ψ 0 μ) hxy
      simp only [hΨgrp, hΨid] at h
      exact h
    · simp only [hΨgrp, hΨid]
  · have h1 : Ψ 0 1 (Ψ 1 0 p) = p := by rw [hΨgrp, hΨid]
    rw [hΨ1 _ hp, Equiv.symm_apply_eq] at h1
    rw [← h1]
    exact (Function.invFunOn_eq (hf _ hp)).symm

end GC.LongTime.Ch12
