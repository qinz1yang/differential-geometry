import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.RiemannianEDistIsometry_O26

/-!
# CH12-O26 G2: HPS01 two-model → single-model reduction

`hps01_of_single_O26 (hSM : L1) : hHPS01 v3` (`[FROZEN] CH12-O26`).  With `Ψ := e.symm ∘ f`:
the `C^m` input transfers by N1 (`ckErr_comp_isometry_target_O19`), the `C⁰` anchor by
`riemannianEDistOf_isometry_O26`, `invFunOn f U ∘ e = invFunOn Ψ U` on `O ⊆ Ψ '' U`, and
`CkCloseInAtlas_CX3` only sees a map on an open neighbourhood of `D2`.
`L1` (single-model near-isometry rigidity, 1c+1d of the O19 HANDOVER) is the remaining gap.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set
open Manifold GC.LongTime GC.LongTime.Ch12
open scoped Manifold ContDiff ENNReal Topology

namespace GC.LongTime.Ch12

universe u

/-- `CkCloseInAtlas_CX3` only depends on the map on an open neighbourhood of `D`. -/
theorem CkCloseInAtlas_congr_O26 {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {A : CkAtlas_S15 (𝓡 3) M} {D O : Set M}
    (hO : IsOpen O) (hDO : D ⊆ O) {k : ℕ} {ε : ℝ} {Φ Φ' : M → M} (hEq : EqOn Φ Φ' O)
    (h : CkCloseInAtlas_CX3 A D k ε Φ) : CkCloseInAtlas_CX3 A D k ε Φ' := by
  intro i x hx hxD
  obtain ⟨h1, h2⟩ := h i x hx hxD
  have hxO : (extChartAt (𝓡 3) (A.ctr i)).symm x ∈ O := hDO hxD
  refine ⟨by rw [← hEq hxO]; exact h1, fun j hj => ?_⟩
  have hev : chartDisplacement_CX3 (I := 𝓡 3) (A.ctr i) Φ =ᶠ[𝓝 x]
      chartDisplacement_CX3 (I := 𝓡 3) (A.ctr i) Φ' := by
    have hxt : x ∈ (extChartAt (𝓡 3) (A.ctr i)).target := A.closedBall_sub i hx
    have hcont : ContinuousAt (extChartAt (𝓡 3) (A.ctr i)).symm x :=
      continuousAt_extChartAt_symm'' hxt
    filter_upwards [hcont.preimage_mem_nhds (hO.mem_nhds hxO)] with y hy
    simp only [chartDisplacement_CX3]
    rw [hEq hy]
  rw [← (hev.iteratedFDeriv ℝ j).eq_of_nhds]
  exact h2 j hj

/-- `invFunOn f U ∘ e = invFunOn (e.symm ∘ f) U` on the image `(e.symm ∘ f) '' U`. -/
theorem invFunOn_comp_isometry_O26 {X Y : Type u} [Nonempty X] (e : X ≃ Y) (U : Set X) (f : X → Y)
    (hinj : InjOn f U) {p : X} (hp : p ∈ (fun q => e.symm (f q)) '' U) :
    Function.invFunOn f U (e p) = Function.invFunOn (fun q => e.symm (f q)) U p := by
  obtain ⟨hxU, hxeq⟩ := Function.invFunOn_pos hp
  have hfx : f (Function.invFunOn (fun q => e.symm (f q)) U p) = e p :=
    (Equiv.symm_apply_eq e).1 hxeq
  have hy := Function.invFunOn_pos (b := e p) ⟨_, hxU, hfx⟩
  exact hinj hy.1 hxU (hy.2.trans hfx.symm)

/-- **HPS01 (two-model, hHPS01 v3) from the single-model core `L1`** (`[FROZEN] CH12-O26`). -/
theorem hps01_of_single_O26
    (hSM : ∀ (H : FiniteVolumeHyperbolicModel.{u}) (o : H.Carrier)
      (A : CkAtlas_S15 (𝓡 3) H.Carrier) (D2 : Set H.Carrier), IsCompact D2 → D2 ⊆ A.cover →
      ∀ (k : ℕ) (ρ ε : ℝ), 0 < ρ → 0 < ε →
      ∃ R θ δ : ℝ, 0 < R ∧ 0 < θ ∧ 0 < δ ∧ ∃ m : ℕ, ∃ O : Set H.Carrier, IsOpen O ∧ D2 ⊆ O ∧
        O ⊆ riemannianBallOf H.metric o R ∧
        ∀ (U : TopologicalSpace.Opens H.Carrier) (Ψ : H.Carrier → H.Carrier),
          riemannianBallOf H.metric o (2 * R) ⊆ U → ContMDiffOn (𝓡 3) (𝓡 3) ∞ Ψ U →
          Set.InjOn Ψ U →
          (∀ j : ℕ, j ≤ m → ∀ p ∈ riemannianBallOf H.metric o (2 * R),
            ckErr_O19 H H.metric 1 Ψ j p < δ) →
          (∀ p ∈ riemannianBallOf H.metric o R,
            riemannianEDistOf H.metric p (Ψ p) < ENNReal.ofReal θ) →
          (∀ p ∈ O, riemannianEDistOf H.metric p (Ψ p) < ENNReal.ofReal ρ) ∧
          CkCloseInAtlas_CX3 A D2 k ε Ψ ∧
          O ⊆ Ψ '' (U : Set H.Carrier) ∧
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ (Function.invFunOn Ψ U) O ∧
          (∀ p ∈ O, riemannianEDistOf H.metric p (Function.invFunOn Ψ U p) < ENNReal.ofReal ρ) ∧
          CkCloseInAtlas_CX3 A D2 k ε (Function.invFunOn Ψ U)) :
    ∀ (H : FiniteVolumeHyperbolicModel.{u}) (o : H.Carrier)
    (A : CkAtlas_S15 (𝓡 3) H.Carrier) (D2 : Set H.Carrier), IsCompact D2 → D2 ⊆ A.cover →
    ∀ (k : ℕ) (ρ ε : ℝ), 0 < ρ → 0 < ε →
    ∃ R θ δ : ℝ, 0 < R ∧ 0 < θ ∧ 0 < δ ∧ ∃ m : ℕ, ∃ O : Set H.Carrier, IsOpen O ∧ D2 ⊆ O ∧
      O ⊆ riemannianBallOf H.metric o R ∧
      ∀ (H' : FiniteVolumeHyperbolicModel.{u}) (e : H.Carrier ≃ H'.Carrier),
        ContMDiff (𝓡 3) (𝓡 3) ∞ e → ContMDiff (𝓡 3) (𝓡 3) ∞ e.symm →
        (∀ p, localPullInner H'.metric e p = H.metric.inner p) →
      ∀ (U : TopologicalSpace.Opens H.Carrier) (f : H.Carrier → H'.Carrier),
        riemannianBallOf H.metric o (2 * R) ⊆ U → ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U →
        IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => f x) →
        (∀ j : ℕ, j ≤ m → ∀ p ∈ riemannianBallOf H.metric o (2 * R),
          ckErr_O19 H H'.metric 1 f j p < δ) →
        (∀ p ∈ riemannianBallOf H.metric o R,
          riemannianEDistOf H'.metric (e p) (f p) < ENNReal.ofReal θ) →
        (∀ p ∈ O, riemannianEDistOf H.metric p (e.symm (f p)) < ENNReal.ofReal ρ) ∧
        CkCloseInAtlas_CX3 A D2 k ε (fun p => e.symm (f p)) ∧
        e '' O ⊆ f '' (U : Set H.Carrier) ∧
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ (fun p => Function.invFunOn f U (e p)) O ∧
        (∀ p ∈ O, riemannianEDistOf H.metric p (Function.invFunOn f U (e p)) <
          ENNReal.ofReal ρ) ∧
        CkCloseInAtlas_CX3 A D2 k ε (fun p => Function.invFunOn f U (e p)) := by
  intro H o A D2 hD2 hD2A k ρ ε hρ hε
  obtain ⟨R, θ, δ, hR, hθ, hδ, m, O, hO, hD2O, hOR, hP⟩ := hSM H o A D2 hD2 hD2A k ρ ε hρ hε
  refine ⟨R, θ, δ, hR, hθ, hδ, m, O, hO, hD2O, hOR, ?_⟩
  intro H' e he he' hiso U f hU hf hemb herr hclose
  have hinj : InjOn f U := fun x hx y hy hxy =>
    congrArg Subtype.val (hemb.isEmbedding.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy)
  have hinjΨ : InjOn (fun q => e.symm (f q)) U := fun x hx y hy hxy =>
    hinj hx hy (e.symm.injective hxy)
  have hΨs : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (fun q => e.symm (f q)) U := he'.comp_contMDiffOn hf
  have herrΨ : ∀ j : ℕ, j ≤ m → ∀ p ∈ riemannianBallOf H.metric o (2 * R),
      ckErr_O19 H H.metric 1 (fun q => e.symm (f q)) j p < δ := fun j hj p hp => by
    rw [ckErr_comp_isometry_target_O19 H H H' e he he' hiso U f hf 1 j p (hU hp)]
    exact herr j hj p hp
  have hd : ∀ p, riemannianEDistOf H.metric p (e.symm (f p)) =
      riemannianEDistOf H'.metric (e p) (f p) := fun p => by
    rw [← riemannianEDistOf_isometry_O26 H H' e he he' hiso p (e.symm (f p)),
      Equiv.apply_symm_apply]
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hP U (fun q => e.symm (f q)) hU hΨs hinjΨ herrΨ
    (fun p hp => (hd p).symm ▸ hclose p hp)
  have hinv : EqOn (fun p => Function.invFunOn f U (e p))
      (Function.invFunOn (fun q => e.symm (f q)) U) O := fun p hp =>
    invFunOn_comp_isometry_O26 e U f hinj (h3 hp)
  refine ⟨h1, h2, ?_, h4.congr fun p hp => hinv hp, fun p hp => by
      have h := hinv hp
      dsimp only at h
      rw [h]
      exact h5 p hp,
    CkCloseInAtlas_congr_O26 hO hD2O (fun p hp => (hinv hp).symm) h6⟩
  rintro _ ⟨p, hp, rfl⟩
  obtain ⟨x, hxU, hx⟩ := h3 hp
  exact ⟨x, hxU, (Equiv.symm_apply_eq e).1 hx⟩

end GC.LongTime.Ch12
