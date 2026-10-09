import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.S7Embed_S86

/-!
# CH12-S86 G2b: S7 v3 assembly given the path-lifting output

`s7_of_hlift_S86`: the conclusion of S7 v3 (`δ, m` before `H'`), assuming the path-lifting output
`hlift : ∀ p ∈ B(R), ∃ q ∈ B'(8R+8), φ q = f p` (G1 `hlift_S86` produces it).
Route: the lift `ℓ : V → U'` of `f|V` through `φ|U'` is a smooth embedding; `a = val ∘ ℓ` is an open
embedding `V ≅ W := a(V)`; on `V` the metrics `h = H.metric|V`, `g₁ = f^*gN`, `k = A^*h'` satisfy
the hypotheses of `three_metric_closeness_S76` (hyp (ii) = `metricDerivNorm_pullbackCross`).
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.CheegerGromovCompactness TopologicalSpace Set Manifold
open scoped Manifold ContDiff

namespace GC.LongTime.Ch12

universe u

/-- **S7 v3 conclusion, given the lifting output.** -/
theorem s7_of_hlift_S86 (H : FiniteVolumeHyperbolicModel.{u}) (R ε : ℝ) (j₀ : ℕ)
    (hR : 0 < R) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 8 ∧ ∃ m : ℕ, ∀ (H' : FiniteVolumeHyperbolicModel.{u}) {N : Type u}
      [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
      [IsManifold (𝓡 3) ∞ N]
      (gN : SmoothRiemannianMetric (𝓡 3) N) (U : TopologicalSpace.Opens H.Carrier)
      (U' : TopologicalSpace.Opens H'.Carrier) (f : H.Carrier → N) (φ : H'.Carrier → N),
      riemannianBallOf H.metric H.basepoint (2 * R + 2) ⊆ U →
      riemannianBallOf H'.metric H'.basepoint (8 * R + 8) ⊆ U' →
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U → IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => f x) →
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ U' → IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U' => φ x) →
      (∀ j : ℕ, j ≤ m → ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * R + 2),
        ckErr_O19 H gN 1 f j p < δ) →
      (∀ j : ℕ, j ≤ m → ∀ p ∈ riemannianBallOf H'.metric H'.basepoint (8 * R + 8),
        ckErr_O19 H' gN 1 φ j p < δ) →
      (∀ p ∈ riemannianBallOf H.metric H.basepoint R,
        ∃ q ∈ riemannianBallOf H'.metric H'.basepoint (8 * R + 8), φ q = f p) →
      (∀ p ∈ riemannianBallOf H.metric H.basepoint R, f p ∈ φ '' (U' : Set H'.Carrier)) ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ (fun p => Function.invFunOn φ U' (f p))
        (riemannianBallOf H.metric H.basepoint R) ∧
      ∀ j : ℕ, j ≤ j₀ → ∀ p ∈ riemannianBallOf H.metric H.basepoint R,
        ckErr_O19 H H'.metric 1 (fun p => Function.invFunOn φ U' (f p)) j p < ε := by
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by decide
  let V : TopologicalSpace.Opens H.Carrier :=
    ⟨riemannianBallOf H.metric H.basepoint R, isOpen_riemannianBallOf _ _ _⟩
  have : SecondCountableTopology H.Carrier :=
    ChartedSpace.secondCountable_of_sigmaCompact (EuclideanSpace ℝ (Fin 3)) H.Carrier
  have : LocallyCompactSpace V := ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin 3)) V
  obtain ⟨δ₃, hδ₃, h3⟩ := three_metric_closeness_S76 (M := V) j₀ ε hε
  refine ⟨min (1 / 8) δ₃, lt_min (by norm_num) hδ₃, min_le_left _ _, j₀, ?_⟩
  intro H' N _ _ _ gN U U' f φ hbU hbU' hfU hfemb hφU' hφemb hck hck' hlift
  have hVsub : (V : Set H.Carrier) ⊆ U :=
    (riemannianBallOf_mono H.metric H.basepoint (by linarith : R ≤ 2 * R + 2)).trans hbU
  have hVball : (V : Set H.Carrier) ⊆ riemannianBallOf H.metric H.basepoint (2 * R + 2) :=
    riemannianBallOf_mono H.metric H.basepoint (by linarith : R ≤ 2 * R + 2)
  have hrange : ∀ p ∈ V, f p ∈ φ '' (U' : Set H'.Carrier) := fun p hp => by
    obtain ⟨q, hq, hqp⟩ := hlift p hp
    exact ⟨q, hbU' hq, hqp⟩
  have hfV : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f V := hfU.mono hVsub
  obtain ⟨hAsm, -⟩ := invFunOn_lift_S76 H H' U' f φ V hfV hφemb hrange
  -- the lift ℓ and the open embedding a = val ∘ ℓ
  have hgV : IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : V => f x) :=
    isSmoothEmbedding_restrict_open_S86 f U V hVsub hfemb
  have hrg : Set.range (fun x : V => f x) ⊆ Set.range (fun x : U' => φ x) := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨q, hq, hqf⟩ := hrange x x.2
    exact ⟨⟨q, hq⟩, hqf⟩
  let ℓ : V → U' := hφemb.lift (fun x : V => f x) hrg
  have hℓ : IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ ℓ := hφemb.isSmoothEmbedding_lift hgV hn hrg
  have ha : IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (Subtype.val ∘ ℓ) :=
    DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_fromOpen (𝓡 3) (𝓡 3) U' ℓ hℓ
  let a : V → H'.Carrier := Subtype.val ∘ ℓ
  have hrangeOpen : IsOpen (Set.range a) :=
    isOpen_range_of_isSmoothEmbedding (I := 𝓡 3) (J := 𝓡 3) rfl ha
  let W : TopologicalSpace.Opens H'.Carrier := ⟨Set.range a, hrangeOpen⟩
  let a' : V → W := fun x => ⟨a x, x, rfl⟩
  have ha' : IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ a' :=
    DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_intoOpen (𝓡 3) (𝓡 3) W a' ha
  have hsurj : Function.Surjective a' := by
    rintro ⟨y, x, rfl⟩
    exact ⟨x, rfl⟩
  let e : Diffeomorph (𝓡 3) (𝓡 3) V W ∞ := ha'.diffeomorphOfSurjective hsurj
  have hea : ∀ x : V, ((e x : W) : H'.Carrier) = a x := fun x => rfl
  -- identities for a
  have hφa : ∀ x : V, φ (a x) = f x := fun x => hφemb.comp_lift hrg x
  have ha_mem : ∀ x : V, a x ∈ U' := fun x => (ℓ x).2
  have hinjOn : InjOn φ (U' : Set H'.Carrier) := by
    intro x hx y hy hxy
    exact congrArg Subtype.val
      (hφemb.isEmbedding.injective (a₁ := (⟨x, hx⟩ : U')) (a₂ := ⟨y, hy⟩) hxy)
  have hAa : ∀ x : V, Function.invFunOn φ U' (f x) = a x := by
    intro x
    rw [← hφa x]
    exact hinjOn.leftInvOn_invFunOn (ha_mem x)
  have hWball : ∀ x : V, a x ∈ riemannianBallOf H'.metric H'.basepoint (8 * R + 8) := by
    intro x
    obtain ⟨q, hq, hqx⟩ := hlift x x.2
    have : a x = q := hinjOn (ha_mem x) (hbU' hq) (by rw [hφa, hqx])
    rw [this]
    exact hq
  have hWU' : (W : Set H'.Carrier) ⊆ U' := by
    rintro _ ⟨x, rfl⟩
    exact ha_mem x
  -- immersion data
  have hfinjV : ∀ y ∈ V, Function.Injective (mfderiv (𝓡 3) (𝓡 3) f y) := fun y hy =>
    injective_mfderiv_of_embedding_S86 f U hfU hfemb y (hVsub hy)
  have hφinj : ∀ y ∈ U', Function.Injective (mfderiv (𝓡 3) (𝓡 3) φ y) :=
    injective_mfderiv_of_embedding_S86 φ U' hφU' hφemb
  have hφW : ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ W := hφU'.mono hWU'
  have hφinjW : ∀ y ∈ W, Function.Injective (mfderiv (𝓡 3) (𝓡 3) φ y) := fun y hy =>
    hφinj y (hWU' hy)
  have hFV := contMDiff_restrict_C4 f V hfV
  have hinjfV : ∀ z : V, Function.Injective (mfderiv (𝓡 3) (𝓡 3) (fun z : V => f z) z) :=
    fun z v w hvw => hfinjV z z.2
      ((mfderiv_comp_val_C4 f V hfV z v).symm.trans
        (hvw.trans (mfderiv_comp_val_C4 f V hfV z w)))
  have hFW := contMDiff_restrict_C4 φ W hφW
  have hinjφW' : ∀ y : W, Function.Injective (mfderiv (𝓡 3) (𝓡 3) (fun y : W => φ y) y) :=
    fun z v w hvw => hφinjW z z.2
      ((mfderiv_comp_val_C4 φ W hφW z v).symm.trans
        (hvw.trans (mfderiv_comp_val_C4 φ W hφW z w)))
  -- the three metrics on V
  let h : SmoothRiemannianMetric (𝓡 3) V := H.metric.restrictOpen V
  let hW : SmoothRiemannianMetric (𝓡 3) W := H'.metric.restrictOpen W
  let k : SmoothRiemannianMetric (𝓡 3) V :=
    Diffeomorph.pullbackMetricCross (I := 𝓡 3) (J := 𝓡 3) hW e
  let g1 : SmoothRiemannianMetric (𝓡 3) V :=
    gN.pullbackOfImmersion (I := 𝓡 3) (fun z : V => f z) hFV hinjfV
  let gφW : SmoothRiemannianMetric (𝓡 3) W :=
    gN.pullbackOfImmersion (I := 𝓡 3) (fun y : W => φ y) hFW hinjφW'
  have hg1 : g1 = Diffeomorph.pullbackMetricCross (I := 𝓡 3) (J := 𝓡 3) gφW e :=
    pullbackOfImmersion_eq_cross_S86 gN e (fun z : V => f z) (fun y : W => φ y) hFV hinjfV hFW
      hinjφW' (fun x => by
        change φ (a x) = f x
        exact hφa x)
  have hi : ∀ x : V, ∀ j ≤ j₀, metricDerivNorm j g1 h h x < δ₃ := by
    intro x j hj
    have h1 := hck j hj x (hVball x.2)
    rw [ckErr_one_eq_raw_O19, rawNorm_eq_metricDerivNorm_C4 gN H.metric f V hfV hfinjV j x] at h1
    exact lt_of_lt_of_le h1 (min_le_right _ _)
  have hii : ∀ x : V, ∀ j ≤ j₀, metricDerivNorm j g1 k k x < δ₃ := by
    intro x j hj
    have h1 := hck' j hj (a x) (hWball x)
    rw [ckErr_one_eq_raw_O19,
      rawNorm_eq_metricDerivNorm_C4 gN H'.metric φ W hφW hφinjW j ⟨a x, x, rfl⟩] at h1
    have h2 : metricDerivNorm j g1 k k x = metricDerivNorm j gφW hW hW (e x) := by
      rw [hg1]
      exact metricDerivNorm_pullbackCross gφW hW hW e j x
    rw [h2]
    exact lt_of_lt_of_le h1 (min_le_right _ _)
  refine ⟨hrange, hAsm, ?_⟩
  intro j hj p hp
  have hAV : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (fun p => Function.invFunOn φ U' (f p)) V := hAsm
  have hAfun : (fun z : V => Function.invFunOn φ U' (f z)) = a := funext hAa
  have hAinj : ∀ y ∈ V, Function.Injective
      (mfderiv (𝓡 3) (𝓡 3) (fun p => Function.invFunOn φ U' (f p)) y) := by
    intro y hy v w hvw
    have h1 := (mfderiv_comp_val_C4 (fun p => Function.invFunOn φ U' (f p)) V hAV ⟨y, hy⟩ v).trans
      (hvw.trans (mfderiv_comp_val_C4 (fun p => Function.invFunOn φ U' (f p)) V hAV
        ⟨y, hy⟩ w).symm)
    rw [hAfun] at h1
    exact ha.isImmersion.mfderiv_injective hn (⟨y, hy⟩ : V) h1
  rw [ckErr_one_eq_raw_O19,
    rawNorm_eq_metricDerivNorm_C4 H'.metric H.metric (fun p => Function.invFunOn φ U' (f p)) V hAV
      hAinj j ⟨p, hp⟩]
  have hk : ∀ (hG : ContMDiff (𝓡 3) (𝓡 3) ∞ (fun z : V => Function.invFunOn φ U' (f z)))
      (hGinj : ∀ z : V, Function.Injective
        (mfderiv (𝓡 3) (𝓡 3) (fun z : V => Function.invFunOn φ U' (f z)) z)),
      H'.metric.pullbackOfImmersion (I := 𝓡 3) (fun z : V => Function.invFunOn φ U' (f z)) hG
        hGinj = k := by
    intro hG hGinj
    have hvalinj : ∀ y : W, Function.Injective
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : W → H'.Carrier) y) := fun y v w hvw => by
      rwa [mfderiv_subtype_val_apply, mfderiv_subtype_val_apply] at hvw
    rw [pullbackOfImmersion_eq_cross_S86 H'.metric e _ (Subtype.val : W → H'.Carrier) hG hGinj
      contMDiff_subtype_val hvalinj (fun x => (hAa x).symm)]
    change _ = Diffeomorph.pullbackMetricCross (I := 𝓡 3) (J := 𝓡 3) (H'.metric.restrictOpen W) e
    rw [restrictOpen_eq_pullback_val_S86 H'.metric W]
  have hfinal := h3 h g1 k hi hii ⟨p, hp⟩ j hj
  exact (congrArg (fun g => metricDerivNorm j g (H.metric.restrictOpen V)
    (H.metric.restrictOpen V) (⟨p, hp⟩ : V)) (hk _ _)).trans_lt hfinal

end GC.LongTime.Ch12
