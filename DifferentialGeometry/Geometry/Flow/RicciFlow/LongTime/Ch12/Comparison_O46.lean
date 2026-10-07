import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.RiemannianEDistIsometry_O26
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.S7Final_S86
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.StepPieces_O40

/-! CH12-O46 G2 (`[FROZEN] CH12-O46` G2): the comparison step (c) of the P2 producer.  An anchor
`φ` from `H` centred at `y₀` (with `φ y₀ = f basepoint`) and the step map `f` give, by S7 v3
(`hpi02_inverse_comparison_S86` at `H' := {H with basepoint := y₀}`) and S1 v3
(`hps02_Ck_isometry_O26` at `H' := H`, `Tr' := Tr`), an isometry `e` of `H` such that
`e.symm ∘ φ⁻¹ ∘ f` is `C^k`-close to the identity in the atlas (CX3 input). -/

set_option autoImplicit false

noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set TopologicalSpace
open Manifold GC.LongTime GC.LongTime.Ch12 DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12

universe u

/-- Smoothness of a map into an open subset from smoothness of its composite with `val`. -/
theorem contMDiff_codRestrict_opens_O46 {M M' : Type u}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [TopologicalSpace M'] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M']
    (U' : Opens M') (F : M → U') (hF : ContMDiff (𝓡 3) (𝓡 3) ∞ (fun x => (F x : M'))) :
    ContMDiff (𝓡 3) (𝓡 3) ∞ F := by
  intro x
  rw [contMDiffAt_iff_target]
  refine ⟨(continuous_induced_rng.2 hF.continuous).continuousAt, ?_⟩
  have h2 := (contMDiffAt_iff_target.1 (hF x)).2
  convert h2 using 1
  funext y
  rfl

/-- `φ⁻¹ ∘ f` is a smooth embedding on an open `V ⊆ U` where it is smooth and `f(V) ⊆ φ(U')`. -/
theorem isSmoothEmbedding_invFunOn_comp_O46 {M M' N : Type u}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [TopologicalSpace M'] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M'] [IsManifold (𝓡 3) ∞ M']
    [Nonempty M'] [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] [IsManifold (𝓡 3) ∞ N]
    (f : M → N) (φ : M' → N) (U V : Opens M) (U' : Opens M') (hVU : V ≤ U)
    (hfemb : IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => f x))
    (hφemb : IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U' => φ x))
    (hmem : ∀ p ∈ V, f p ∈ φ '' (U' : Set M'))
    (hsm : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (fun p => Function.invFunOn φ U' (f p)) V) :
    IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : V => Function.invFunOn φ U' (f x)) := by
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by decide
  let F' : V → U' := fun x =>
    ⟨Function.invFunOn φ U' (f x), Function.invFunOn_mem (hmem x x.2)⟩
  have hval : ContMDiff (𝓡 3) (𝓡 3) ∞ (fun x : V => (F' x : M')) :=
    hsm.comp_contMDiff contMDiff_subtype_val (fun x => x.2)
  have hF' : ContMDiff (𝓡 3) (𝓡 3) ∞ F' := contMDiff_codRestrict_opens_O46 U' F' hval
  have hcomp : ((fun x : U' => φ x) ∘ F') = fun x : V => f x := by
    funext x
    exact Function.invFunOn_eq (hmem x x.2)
  have hfV := isSmoothEmbedding_restrict_open_S86 f U V hVU hfemb
  have hF'emb : IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ F' :=
    IsSmoothEmbedding.of_comp (g := fun x : U' => φ x) (f := F') (by rw [hcomp]; exact hfV) hn
      hF' hφemb.contMDiff
  have hvalemb : IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (Subtype.val ∘ (id : U' → U')) :=
    DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_fromOpen (𝓡 3) (𝓡 3) U' id
      IsSmoothEmbedding.id
  exact (IsSmoothEmbedding.comp (g := Subtype.val ∘ (id : U' → U')) (f := F') hvalemb hF'emb hn :)

/-- **G2 (c)** `[FROZEN] CH12-O46` verbatim. -/
theorem comparison_O46
    (hHG06 : ∀ (H : FiniteVolumeHyperbolicModel.{u}) (o : H.Carrier) (η : ℝ), 0 < η →
      ∃ ξ : ℝ, 0 < ξ ∧ ∃ n : ℕ, ξ = 1 / ((n : ℝ) + 1) ∧ η⁻¹ < ξ⁻¹ ∧
        ∀ (H' : FiniteVolumeHyperbolicModel.{u}) (Tr : HyperbolicTruncation H)
          (Tr' : HyperbolicTruncation H'), Tr.count ≤ Tr'.count →
        ∀ (U : TopologicalSpace.Opens H.Carrier) (f : H.Carrier → H'.Carrier),
          riemannianClosedBallOf H.metric o ξ⁻¹ ⊆ U →
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U →
          IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => f x) →
          (∀ k : ℕ, k ≤ n + 1 → ∀ p ∈ riemannianClosedBallOf H.metric o ξ⁻¹,
            ckErr_O19 H H'.metric 1 f k p < ξ / 3) →
          ∃ e : H.Carrier ≃ H'.Carrier, ContMDiff (𝓡 3) (𝓡 3) ∞ e ∧
            ContMDiff (𝓡 3) (𝓡 3) ∞ e.symm ∧
            (∀ p, localPullInner H'.metric e p = H.metric.inner p) ∧
            ∀ p ∈ riemannianClosedBallOf H.metric o η⁻¹,
              riemannianEDistOf H'.metric (e p) (f p) < ENNReal.ofReal η)
    (hHPS01 : ∀ (H : FiniteVolumeHyperbolicModel.{u}) (o : H.Carrier)
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
          CkCloseInAtlas_CX3 A D2 k ε (fun p => Function.invFunOn f U (e p)))
    (H : FiniteVolumeHyperbolicModel.{u}) (Tr : HyperbolicTruncation H)
    (A : CkAtlas_S15 (𝓡 3) H.Carrier) (D2 : Set H.Carrier) (hD2 : IsCompact D2)
    (hD2A : D2 ⊆ A.cover) (k : ℕ) (ρ ε : ℝ) (hρ : 0 < ρ) (hε : 0 < ε) :
    ∃ R₂ δ : ℝ, 0 < R₂ ∧ 0 < δ ∧ ∃ m : ℕ, ∃ O : Set H.Carrier, IsOpen O ∧ D2 ⊆ O ∧
      O ⊆ riemannianBallOf H.metric H.basepoint R₂ ∧
      ∀ {N : Type u} [TopologicalSpace N] [T2Space N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
        [IsManifold (𝓡 3) ∞ N] (gN : SmoothRiemannianMetric (𝓡 3) N)
        (U U' : TopologicalSpace.Opens H.Carrier) (f φ : H.Carrier → N) (y₀ : H.Carrier),
        riemannianBallOf H.metric H.basepoint (2 * R₂ + 2) ⊆ U →
        riemannianBallOf H.metric y₀ (8 * R₂ + 8) ⊆ U' →
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U → IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => f x) →
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ U' → IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U' => φ x) →
        f H.basepoint = φ y₀ →
        (∀ j : ℕ, j ≤ m → ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * R₂ + 2),
          ckErr_O19 H gN 1 f j p < δ) →
        (∀ j : ℕ, j ≤ m → ∀ p ∈ riemannianBallOf H.metric y₀ (8 * R₂ + 8),
          ckErr_O19 H gN 1 φ j p < δ) →
        (∀ p ∈ riemannianBallOf H.metric H.basepoint R₂, f p ∈ φ '' (U' : Set H.Carrier)) ∧
        ∃ e : H.Carrier ≃ H.Carrier, ContMDiff (𝓡 3) (𝓡 3) ∞ e ∧
          ContMDiff (𝓡 3) (𝓡 3) ∞ e.symm ∧ (∀ p, localPullInner H.metric e p = H.metric.inner p) ∧
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ (fun p => e.symm (Function.invFunOn φ U' (f p))) O ∧
          (∀ p ∈ O, riemannianEDistOf H.metric p (e.symm (Function.invFunOn φ U' (f p))) <
            ENNReal.ofReal ρ) ∧
          CkCloseInAtlas_CX3 A D2 k ε (fun p => e.symm (Function.invFunOn φ U' (f p)))
    := by
  obtain ⟨δ₀, R₁, hδ₀, hR₁, m₁, O, hO, hD2O, hOR, hS1⟩ :=
    hps02_Ck_isometry_O26 hHG06 hHPS01 H H.basepoint A D2 hD2 hD2A k ρ ε hρ hε
  obtain ⟨δ, hδ, m, hS7⟩ :=
    hpi02_inverse_comparison_S86 H (2 * R₁ + 1) δ₀ m₁ (by linarith) hδ₀
  refine ⟨2 * R₁ + 1, δ, by linarith, hδ, m, O, hO, hD2O,
    hOR.trans (riemannianBallOf_mono H.metric H.basepoint (by linarith)), ?_⟩
  intro N _ _ _ _ gN U U' f φ y₀ hbU hbU' hfU hfemb hφU' hφemb hbase hckf hckφ
  let H' : FiniteVolumeHyperbolicModel.{u} := { H with basepoint := y₀ }
  obtain ⟨hmem, hsm, hck⟩ :=
    hS7 H' gN U U' f φ hbU hbU' hfU hfemb hφU' hφemb hbase hckf hckφ
  refine ⟨hmem, ?_⟩
  let V : Opens H.Carrier := ⟨riemannianBallOf H.metric H.basepoint (2 * R₁ + 1),
    isOpen_riemannianBallOf H.metric H.basepoint _⟩
  have hVU : V ≤ U := fun x hx =>
    hbU (riemannianBallOf_mono H.metric H.basepoint (by linarith) hx)
  have hemb := isSmoothEmbedding_invFunOn_comp_O46 f φ U V U' hVU hfemb hφemb hmem hsm
  obtain ⟨e, he, he', hiso, hsmO, hdist, hclose, -⟩ := hS1 H Tr Tr le_rfl V
    (fun p => Function.invFunOn φ U' (f p))
    (riemannianBallOf_mono H.metric H.basepoint (by linarith)) hsm hemb
    (fun j hj p hp => hck j hj p (riemannianBallOf_mono H.metric H.basepoint (by linarith) hp))
  exact ⟨e, he, he', hiso, hsmO, hdist, hclose⟩

end GC.LongTime.Ch12
