import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.StepIsotopy_O50
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.Comparison_O46
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HCX3ExtNoSpeed_S109
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.BallCompact_S98
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.PatchCore_S61
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HChartFinal_S112
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HCX3ExtV4_S120

set_option autoImplicit false

/-! # CH12-O54 G2: one P2 step (GA + hCX3ext v4 + comparison_O46) and the GOOD transport (GC)

* `exists_ckAtlas_cover_O54`: every compact set is covered by a finite `CkAtlas_S15`.
* `step_core_O54`: for `(ε, R, k)` there are `R₂ δ ρ m` such that every track endpoint `f` and anchor
  `φ` (both `δ`-close at order `m` on `B(bp, 2R₂+2)` / `B(y₀, 8R₂+8)`, `f bp = φ y₀`) give an
  isometry `e` with `edist (e bp) y₀ < ρ` and an isotopy `E` with every non-GOOD conjunct of P2 v4
  (support `B(4R)`, speed `ε`, ckErr `≤ ε` at every point, endpoint `f ∘ E 1 = φ ∘ e` on `B(2R)`).
  Radii: `D = cB(5R/2) ⊆ D1 = cB(3R) ⊆ D2 = cB(7R/2) ⊆ V = B(4R) ⊆ D' = cB(4R)`; the comparison
  is run on `D'` so that its open set contains hCX3ext's `O ⊆ V` (FINDING F3: `hCX3ext_v4_S120`;
  hchart = `hchart_S112`).
* `step_good_O54` (GC): the anchor's GOOD on `B(y₀, 4β⁻¹)` transports to `φ ∘ e` on `B(bp, 2β⁻¹)`. -/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.CheegerGromovCompactness
open Set TopologicalSpace Manifold Bundle
open scoped Manifold ContDiff ENNReal

universe u

namespace GC.LongTime.Ch12

theorem exists_ckAtlas_cover_O54 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Hm : Type*} [TopologicalSpace Hm] {I : ModelWithCorners ℝ E Hm} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace Hm M] {K : Set M} (hK : IsCompact K) :
    ∃ A : CkAtlas_S15 I M, K ⊆ A.cover := by
  have hr : ∀ x : M, ∃ r : ℝ, 0 < r ∧
      Metric.closedBall (extChartAt I x x) r ⊆ (extChartAt I x).target := by
    intro x
    obtain ⟨r, hr, hsub⟩ :=
      Metric.isOpen_iff.1 (isOpen_extChartAt_target (I := I) x) _ (mem_extChartAt_target (I := I) x)
    exact ⟨r / 2, half_pos hr, (Metric.closedBall_subset_ball (half_lt_self hr)).trans hsub⟩
  choose r hr0 hrsub using hr
  let U : M → Set M := fun x =>
    (extChartAt I x).source ∩ extChartAt I x ⁻¹' Metric.ball (extChartAt I x x) (r x)
  have hUo : ∀ x, IsOpen (U x) := fun x => isOpen_extChartAt_preimage' x Metric.isOpen_ball
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover U hUo
    (fun x _ => mem_iUnion.2 ⟨x, mem_extChartAt_source (I := I) x, Metric.mem_ball_self (hr0 x)⟩)
  refine ⟨⟨t.card, fun i => (t.equivFin.symm i : M), fun i => r (t.equivFin.symm i : M),
    fun i => hrsub _⟩, fun y hy => ?_⟩
  obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.1 (ht hy)
  refine mem_iUnion.2 ⟨t.equivFin ⟨x, hx⟩, ?_⟩
  simpa [CkAtlas_S15.U, U] using hyx

/-- GC: GOOD transport through an isometry `e` with `edist (e bp) y₀ < ρ ≤ 2β⁻¹`. -/
theorem step_good_O54 (H : FiniteVolumeHyperbolicModel.{u})
    {N : Type u} [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
    [IsManifold (𝓡 3) ∞ N] (gN : SmoothRiemannianMetric (𝓡 3) N) (c : ℝ) (hc : 0 < c)
    (e : H.Carrier ≃ H.Carrier) (he : ContMDiff (𝓡 3) (𝓡 3) ∞ e)
    (he' : ContMDiff (𝓡 3) (𝓡 3) ∞ e.symm)
    (hiso : ∀ p, localPullInner H.metric e p = H.metric.inner p)
    (φ : H.Carrier → N) (U' : Opens H.Carrier) (y₀ : H.Carrier) {β ρ : ℝ} (hβ : 0 < β)
    (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 2 * β⁻¹)
    (hy : riemannianEDistOf H.metric (e H.basepoint) y₀ < ENNReal.ofReal ρ)
    (hU' : riemannianBallOf H.metric y₀ (4 * β⁻¹) ⊆ U')
    (hφ : ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ U')
    (hemb : IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U' => φ x))
    (herr : ∀ k : ℕ, k ≤ ⌈β⁻¹⌉₊ → ∀ p ∈ riemannianBallOf H.metric y₀ (4 * β⁻¹),
      ckErr_S45 H gN c φ k p < β) :
    ∃ U : Opens H.Carrier,
      riemannianBallOf H.metric H.basepoint (2 * β⁻¹) ⊆ U ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ (fun x => φ (e x)) U ∧
      IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => φ (e x)) ∧
      ∀ k : ℕ, k ≤ ⌈β⁻¹⌉₊ → ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * β⁻¹),
        ckErr_S45 H gN c (fun x => φ (e x)) k p < β := by
  have hβi : 0 ≤ 2 * β⁻¹ := by positivity
  have himg : e '' riemannianBallOf H.metric H.basepoint (2 * β⁻¹) ⊆
      riemannianBallOf H.metric y₀ (4 * β⁻¹) := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' : riemannianEDistOf H.metric (e H.basepoint) (e x) < ENNReal.ofReal (2 * β⁻¹) := by
      rw [riemannianEDistOf_isometry_O26 H H e he he' hiso]; exact hx
    change riemannianEDistOf H.metric y₀ (e x) < ENNReal.ofReal (4 * β⁻¹)
    calc riemannianEDistOf H.metric y₀ (e x)
        ≤ riemannianEDistOf H.metric y₀ (e H.basepoint) +
          riemannianEDistOf H.metric (e H.basepoint) (e x) := riemannianEDistOf_triangle _ _ _ _
      _ < ENNReal.ofReal ρ + ENNReal.ofReal (2 * β⁻¹) := by
          rw [riemannianEDistOf_comm]; exact ENNReal.add_lt_add hy hx'
      _ = ENNReal.ofReal (ρ + 2 * β⁻¹) := (ENNReal.ofReal_add hρ0 hβi).symm
      _ ≤ ENNReal.ofReal (4 * β⁻¹) := ENNReal.ofReal_le_ofReal (by linarith)
  exact good_comp_isometry_O40 H gN c hc e he he' hiso φ β U' (himg.trans hU') hφ hemb
    (fun k hk y hy => herr k hk y (himg hy))

section CX3
open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Geometry.Riemannian.Exponential
attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

/-- One P2 step on `H` (all conjuncts of P2 v4 except GOOD), from GA, hCX3ext v4 and comparison. -/
theorem step_core_O54
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
    {ε R : ℝ} (hε : 0 < ε) (hR : 0 < R) (k : ℕ) :
    ∃ (R₂ δ ρ : ℝ) (m : ℕ), 0 < R₂ ∧ 0 < δ ∧ 0 < ρ ∧
      ∀ {N : Type u} [TopologicalSpace N] [T2Space N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
        [IsManifold (𝓡 3) ∞ N] (gN : SmoothRiemannianMetric (𝓡 3) N)
        (U U' : Opens H.Carrier) (f φ : H.Carrier → N) (y₀ : H.Carrier),
        riemannianBallOf H.metric H.basepoint (2 * R₂ + 2) ⊆ U →
        riemannianBallOf H.metric y₀ (8 * R₂ + 8) ⊆ U' →
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U → IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => f x) →
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ U' → IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U' => φ x) →
        f H.basepoint = φ y₀ →
        (∀ j : ℕ, j ≤ m → ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * R₂ + 2),
          ckErr_O19 H gN 1 f j p < δ) →
        (∀ j : ℕ, j ≤ m → ∀ p ∈ riemannianBallOf H.metric y₀ (8 * R₂ + 8),
          ckErr_O19 H gN 1 φ j p < δ) →
        ∃ (E : ℝ × H.Carrier → H.Carrier) (e : H.Carrier ≃ H.Carrier),
          ContMDiff (𝓡 3) (𝓡 3) ∞ e ∧ ContMDiff (𝓡 3) (𝓡 3) ∞ e.symm ∧
          (∀ p, localPullInner H.metric e p = H.metric.inner p) ∧
          riemannianEDistOf H.metric (e H.basepoint) y₀ < ENNReal.ofReal ρ ∧
          ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) ∞ E ∧
          (∀ μ, ContMDiff (𝓡 3) (𝓡 3) ∞ (fun p => E (μ, p)) ∧
            Function.Bijective (fun p => E (μ, p))) ∧
          (∀ p, E (0, p) = p) ∧
          (∀ μ p, p ∉ riemannianBallOf H.metric H.basepoint (4 * R) → E (μ, p) = p) ∧
          (∀ μ ∈ Icc (0 : ℝ) 1, ∀ p : H.Carrier,
            let v := mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun r => E (r, p)) μ
              ((NormedSpace.fromTangentSpace (𝕜 := ℝ) μ).symm (1 : ℝ));
            H.metric.inner (E (μ, p)) v v ≤ ε ^ 2) ∧
          (∀ μ ∈ Icc (0 : ℝ) 1, ∀ i : ℕ, i ≤ k → ∀ p : H.Carrier,
            ckErr_S45 H H.metric 1 (fun x => E (μ, x)) i p ≤ ε) ∧
          (∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * R), f (E (1, p)) = φ (e p)) := by
  classical
  have hcb : ∀ r : ℝ, IsCompact (riemannianClosedBallOf H.metric H.basepoint r) :=
    fun r => isCompact_closedBall_S98 H r
  have hbo : ∀ r : ℝ, IsOpen (riemannianBallOf H.metric H.basepoint r) :=
    isOpen_riemannianBallOf_S61 H
  have hsub : ∀ r r' : ℝ, 0 ≤ r → r < r' → riemannianClosedBallOf H.metric H.basepoint r ⊆
      riemannianBallOf H.metric H.basepoint r' := fun r r' hr h y hy =>
    lt_of_le_of_lt hy ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hr).2 h)
  have hbc : ∀ r : ℝ, riemannianBallOf H.metric H.basepoint r ⊆
      riemannianClosedBallOf H.metric H.basepoint r := fun r y hy =>
    show riemannianEDistOf H.metric H.basepoint y ≤ ENNReal.ofReal r from le_of_lt hy
  obtain ⟨A, hA⟩ := exists_ckAtlas_cover_O54 (I := 𝓡 3) (hcb (4 * R))
  have hDD1 : riemannianClosedBallOf H.metric H.basepoint (5 / 2 * R) ⊆
      riemannianClosedBallOf H.metric H.basepoint (3 * R) :=
    riemannianClosedBallOf_mono _ _ (by linarith)
  have hD12 : riemannianClosedBallOf H.metric H.basepoint (3 * R) ⊆
      interior (riemannianClosedBallOf H.metric H.basepoint (7 / 2 * R)) :=
    (hsub _ (13 / 4 * R) (by positivity) (by linarith)).trans
      (interior_maximal ((hbc (13 / 4 * R)).trans (riemannianClosedBallOf_mono _ _ (by linarith)))
        (hbo _))
  have hD2D' : riemannianClosedBallOf H.metric H.basepoint (7 / 2 * R) ⊆
      riemannianClosedBallOf H.metric H.basepoint (4 * R) :=
    riemannianClosedBallOf_mono _ _ (by linarith)
  have hD2V : riemannianClosedBallOf H.metric H.basepoint (7 / 2 * R) ⊆
      riemannianBallOf H.metric H.basepoint (4 * R) := hsub _ _ (by positivity) (by linarith)
  let Bop : Opens H.Carrier := ⟨riemannianBallOf H.metric H.basepoint (4 * R), hbo _⟩
  obtain ⟨ε₀, hε₀, hGA⟩ := step_isotopy_O50 H (hchart_S112 H) A
    (riemannianClosedBallOf H.metric H.basepoint (4 * R)) Bop (hcb _) (hbc _) hA k hε
  obtain ⟨O, hO, hD2O, hOV, ρx, hρx, hmain⟩ := hCX3ext_v4_S120 H A (hcb (5 / 2 * R)) (hcb (3 * R))
    (hcb (7 / 2 * R)) hDD1 hD12 (hD2D'.trans hA) (hbo (4 * R)) hD2V (k + 1) (by omega)
  have hεx : 0 < min ε₀ (min ε (R / 2)) := lt_min hε₀ (lt_min hε (by linarith))
  have hεx₀ : min ε₀ (min ε (R / 2)) ≤ ε₀ := min_le_left _ _
  have hεxε : min ε₀ (min ε (R / 2)) ≤ ε := (min_le_right _ _).trans (min_le_left _ _)
  have hεxR : min ε₀ (min ε (R / 2)) ≤ R / 2 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨ε'x, hε'x, hX⟩ := hmain _ hεx
  obtain ⟨R₂, δ, hR₂, hδ, m, Oc, -, hD'Oc, hOcB, hcmp⟩ := comparison_O46 hHG06 hHPS01 H Tr A
    (riemannianClosedBallOf H.metric H.basepoint (4 * R)) (hcb _) hA (k + 1) ρx ε'x hρx hε'x
  refine ⟨R₂, δ, ρx, m, hR₂, hδ, hρx, ?_⟩
  intro N _ _ _ _ gN U U' f φ y₀ hU hU' hf hfemb hφ hφemb hfφ hfck hφck
  obtain ⟨hfimg, e, he, he', hiso, hΦsm, hΦd, hΦck⟩ :=
    hcmp gN U U' f φ y₀ hU hU' hf hfemb hφ hφemb hfφ hfck hφck
  have hOOc : O ⊆ Oc := hOV.trans ((hbc _).trans hD'Oc)
  obtain ⟨X, Ψ, C, -, -, hX0, -, hCc, hΨ, hid, hgrp, hsuppC, -, h1, hCV, hglob, hclose, hspeed,
      hdisp⟩ :=
    hX (fun p => e.symm (Function.invFunOn φ U' (f p))) (hΦsm.mono hOOc)
      (fun p hp => hΦd p (hOOc hp)) (fun i x hx hxD => hΦck i x hx (hD2D' hxD))
  have hDOc : riemannianClosedBallOf H.metric H.basepoint (5 / 2 * R) ⊆
      riemannianBallOf H.metric H.basepoint R₂ :=
    (riemannianClosedBallOf_mono _ _ (by linarith : 5 / 2 * R ≤ 4 * R)).trans (hD'Oc.trans hOcB)
  have hWid : withS99% H as hE', ∀ (X : ∀ p : H.Carrier, TangentSpace (𝓡 3) p) (t : ℝ)
      (y : H.Carrier), X y = 0 → scaledExp_S15 H.metric hE' X t y = y :=
    withS99% H as hE', fun X t y hy => scaledExp_zero_field_S102 H.metric hE' X t hy
  obtain ⟨hEsm, hslice, h00, hsuppB, hck, hend⟩ := hGA Ψ _ C
    (riemannianClosedBallOf H.metric H.basepoint (7 / 2 * R))
    (riemannianClosedBallOf H.metric H.basepoint (5 / 2 * R)) f φ U' e hΨ hid hgrp hCc.isClosed
    hsuppC hCV hglob (hcb _).isClosed (fun t _ y hy => hWid X t y (hX0 y hy))
    (fun t ht i x hx hxD => ⟨(hclose t ht i x hx hxD).1,
      fun j hj => ((hclose t ht i x hx hxD).2 j hj).trans_le hεx₀⟩)
    (fun x hx => hfimg x (hDOc hx)) h1
  have hmem : ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * R),
      Ψ 1 0 p ∈ riemannianClosedBallOf H.metric H.basepoint (5 / 2 * R) := by
    intro p hp
    have h2 := hdisp 1 ⟨zero_le_one, le_rfl⟩ p
    change riemannianEDistOf H.metric H.basepoint (Ψ 1 0 p) ≤ ENNReal.ofReal (5 / 2 * R)
    calc riemannianEDistOf H.metric H.basepoint (Ψ 1 0 p)
        ≤ riemannianEDistOf H.metric H.basepoint p + riemannianEDistOf H.metric p (Ψ 1 0 p) :=
          riemannianEDistOf_triangle _ _ _ _
      _ ≤ ENNReal.ofReal (2 * R) + ENNReal.ofReal (R / 2) :=
          add_le_add (le_of_lt hp) (h2.trans (ENNReal.ofReal_le_ofReal hεxR))
      _ = ENNReal.ofReal (5 / 2 * R) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
  have hy0U' : y₀ ∈ (U' : Set H.Carrier) := hU' (by
    change riemannianEDistOf H.metric y₀ y₀ < ENNReal.ofReal (8 * R₂ + 8)
    rw [riemannianEDistOf_self]; exact ENNReal.ofReal_pos.2 (by linarith))
  have hinj : Set.InjOn φ U' := fun a ha b hb hab =>
    congrArg Subtype.val (hφemb.isEmbedding.injective (a₁ := ⟨a, ha⟩) (a₂ := ⟨b, hb⟩) hab)
  have hbpOc : H.basepoint ∈ Oc := hD'Oc (by
    change riemannianEDistOf H.metric H.basepoint H.basepoint ≤ ENNReal.ofReal (4 * R)
    rw [riemannianEDistOf_self]; exact zero_le)
  have hd := hΦd H.basepoint hbpOc
  rw [hfφ, hinj.leftInvOn_invFunOn hy0U'] at hd
  have hiso' := riemannianEDistOf_isometry_O26 H H e he he' hiso H.basepoint (e.symm y₀)
  rw [e.apply_symm_apply] at hiso'
  refine ⟨fun q => Ψ q.1 0 q.2, e, he, he', hiso, hiso' ▸ hd, hEsm, hslice, h00,
    fun μ p hp => hsuppB μ p hp,
    fun μ hμ p => le_trans (hspeed μ hμ p) (pow_le_pow_left₀ hεx.le hεxε 2),
    fun μ hμ i hi p => hck μ hμ i hi p, fun p hp => hend p (hmem p hp)⟩

end CX3

end GC.LongTime.Ch12
