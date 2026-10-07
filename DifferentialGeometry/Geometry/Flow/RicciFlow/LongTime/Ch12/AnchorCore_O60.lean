import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.StepWrap_O54
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.RiemannianEDistIsometry_O26

set_option autoImplicit false

/-! # CH12-O60 G1: anchor core pieces and the OLD-CORE case (lead ruling B')

`[FROZEN] CH12-O60` (scratch/FrozenO60.lean).  `good_transport_O60`: GOOD transport along an
isometry `H ≃ H'` (two-model version of O40 (b), arbitrary centre).  `core_anchor_O60`: an anchor
at accuracy `β` from a GOOD core map of a model isometric to `H`.  `anchor_of_levels_O60`: the
accuracy function `βw` from per-level thresholds (`anchor_shape_O46` body).
`old_case_levels_O60`: per-level anchors when `q(bp)` lies in an old core
`mold i t₂ '' B((α i t₂)⁻¹/2)` (old GOOD data + old-core rigidity). -/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set
open Manifold GC.LongTime DifferentialGeometry.CheegerGromovCompactness
open TopologicalSpace Filter
open scoped Manifold ContDiff ENNReal Topology

universe u

namespace GC.LongTime.Ch12

/-- G1: GOOD transport along an isometry `e : H ≃ H'`, recentred at `e.symm z`. -/
theorem good_transport_O60 (H H' : FiniteVolumeHyperbolicModel.{u})
    (e : H.Carrier ≃ H'.Carrier) (he : ContMDiff (𝓡 3) (𝓡 3) ∞ e)
    (he' : ContMDiff (𝓡 3) (𝓡 3) ∞ e.symm)
    (hiso : ∀ p, localPullInner H'.metric e p = H.metric.inner p)
    {N : Type u} [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
    [IsManifold (𝓡 3) ∞ N] (gN : SmoothRiemannianMetric (𝓡 3) N) (c : ℝ) (hc : 0 < c)
    (ψ : H'.Carrier → N) (U : Opens H'.Carrier) (z : H'.Carrier) (r δ : ℝ) (K : ℕ)
    (hU : riemannianBallOf H'.metric z r ⊆ U) (hψ : ContMDiffOn (𝓡 3) (𝓡 3) ∞ ψ U)
    (hemb : IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => ψ x))
    (herr : ∀ k : ℕ, k ≤ K → ∀ p ∈ riemannianBallOf H'.metric z r,
      ckErr_S45 H' gN c ψ k p < δ) :
    ∃ U' : Opens H.Carrier, riemannianBallOf H.metric (e.symm z) r ⊆ U' ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ (fun x => ψ (e x)) U' ∧
      IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U' => ψ (e x)) ∧
      ∀ k : ℕ, k ≤ K → ∀ p ∈ riemannianBallOf H.metric (e.symm z) r,
        ckErr_S45 H gN c (fun x => ψ (e x)) k p < δ := by
  let U' : Opens H.Carrier := ⟨e ⁻¹' U, U.isOpen.preimage he.continuous⟩
  have hinj : ∀ y ∈ U, Function.Injective (mfderiv (𝓡 3) (𝓡 3) ψ y) :=
    injective_mfderiv_of_embedding_S86 ψ U hψ hemb
  have hball : ∀ p ∈ riemannianBallOf H.metric (e.symm z) r,
      e p ∈ riemannianBallOf H'.metric z r := by
    intro p hp
    have h := riemannianEDistOf_isometry_O26 H H' e he he' hiso (e.symm z) p
    rw [e.apply_symm_apply] at h
    change riemannianEDistOf H'.metric z (e p) < ENNReal.ofReal r
    rw [h]
    exact hp
  refine ⟨U', fun p hp => hU (hball p hp), ?_, ?_, fun k hk p hp => ?_⟩
  · exact hψ.comp he.contMDiffOn (fun x hx => hx)
  · let Φ := (isoDiffeo_O19 e he he').toPartialDiffeomorph
    have hUΦ : (U' : Set H.Carrier) ⊆ Φ.source := fun x _ => mem_univ x
    have hW : (⟨(Φ : H.Carrier → H'.Carrier) '' (U' : Set H.Carrier),
        image_opens_isOpen Φ hUΦ⟩ : Opens H'.Carrier) = U := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact hx
      · intro hy
        exact ⟨e.symm y, by simpa [U'] using hy, e.apply_symm_apply y⟩
    have hemb' : IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞
        (fun x : (⟨(Φ : H.Carrier → H'.Carrier) '' (U' : Set H.Carrier),
          image_opens_isOpen Φ hUΦ⟩ : Opens H'.Carrier) => ψ x) := by
      rw [hW]; exact hemb
    exact hemb'.comp_diffeomorph (PartialDiffeomorph.toOpensDiffeo Φ hUΦ)
  · have hep : e p ∈ U := hU (hball p hp)
    change ckErr_O19 H gN c (fun q => ψ (e q)) k p < δ
    rw [ckErr_comp_isometry_source_O19 H H' e he he' hiso gN U ψ hψ hinj c hc k p hep]
    exact herr k hk (e p) (hball p hp)

/-- G1: an anchor at accuracy `β` from a GOOD core map `m` (accuracy `α`) of a model `H₀ ≅ H`. -/
theorem core_anchor_O60 (H H₀ : FiniteVolumeHyperbolicModel.{u})
    (e : H.Carrier ≃ H₀.Carrier) (he : ContMDiff (𝓡 3) (𝓡 3) ∞ e)
    (he' : ContMDiff (𝓡 3) (𝓡 3) ∞ e.symm)
    (hiso : ∀ p, localPullInner H₀.metric e p = H.metric.inner p)
    {N : Type u} [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
    [IsManifold (𝓡 3) ∞ N] (gN : SmoothRiemannianMetric (𝓡 3) N) (c : ℝ) (hc : 0 < c)
    (m : H₀.Carrier → N) (α β ρ : ℝ) (hα : 0 < α) (hρ : 0 ≤ ρ) (hαβ : α ≤ β)
    (hrad : ρ + 4 * β⁻¹ ≤ 2 * α⁻¹)
    (hgood : ∃ U : Opens H₀.Carrier,
      riemannianBallOf H₀.metric H₀.basepoint (2 * α⁻¹) ⊆ U ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ m U ∧
      IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => m x) ∧
      ∀ k : ℕ, k ≤ ⌈α⁻¹⌉₊ → ∀ p ∈ riemannianBallOf H₀.metric H₀.basepoint (2 * α⁻¹),
        ckErr_S45 H₀ gN c m k p < α)
    (z : H₀.Carrier) (hz : z ∈ riemannianBallOf H₀.metric H₀.basepoint ρ) :
    ∃ (φ : H.Carrier → N) (U' : Opens H.Carrier) (y₀ : H.Carrier),
      riemannianBallOf H.metric y₀ (4 * β⁻¹) ⊆ U' ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ U' ∧
      IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U' => φ x) ∧
      (∀ k : ℕ, k ≤ ⌈β⁻¹⌉₊ → ∀ p ∈ riemannianBallOf H.metric y₀ (4 * β⁻¹),
        ckErr_S45 H gN c φ k p < β) ∧
      φ y₀ = m z := by
  obtain ⟨U, hU, hm, hemb, herr⟩ := hgood
  have hβ : 0 < β := lt_of_lt_of_le hα hαβ
  have hsub : riemannianBallOf H₀.metric z (4 * β⁻¹) ⊆
      riemannianBallOf H₀.metric H₀.basepoint (2 * α⁻¹) := by
    intro p hp
    change riemannianEDistOf H₀.metric H₀.basepoint p < ENNReal.ofReal (2 * α⁻¹)
    calc riemannianEDistOf H₀.metric H₀.basepoint p
        ≤ riemannianEDistOf H₀.metric H₀.basepoint z + riemannianEDistOf H₀.metric z p :=
          riemannianEDistOf_triangle _ _ _ _
      _ < ENNReal.ofReal ρ + ENNReal.ofReal (4 * β⁻¹) := ENNReal.add_lt_add hz hp
      _ = ENNReal.ofReal (ρ + 4 * β⁻¹) := (ENNReal.ofReal_add hρ (by positivity)).symm
      _ ≤ ENNReal.ofReal (2 * α⁻¹) := ENNReal.ofReal_le_ofReal hrad
  have hK : ⌈β⁻¹⌉₊ ≤ ⌈α⁻¹⌉₊ := Nat.ceil_mono (inv_anti₀ hα hαβ)
  obtain ⟨U', hU', hφ, hemb', herr'⟩ := good_transport_O60 H H₀ e he he' hiso gN c hc m U z
    (4 * β⁻¹) β ⌈β⁻¹⌉₊ (hsub.trans hU) hm hemb
    (fun k hk p hp => (herr k (hk.trans hK) p (hsub hp)).trans_le hαβ)
  exact ⟨fun x => m (e x), U', e.symm z, hU', hφ, hemb', herr', by simp⟩

/-- G1: `βw` from per-level thresholds (level `n` = accuracy `1/(n+1)`). Output = `anchor_shape_O46`
body verbatim. -/
theorem anchor_of_levels_O60 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (H : FiniteVolumeHyperbolicModel.{u})
    (ε₁ R₁ : ℝ) (k₁ : ℕ) (hε₁ : 0 < ε₁) (hR₁ : 0 < R₁)
    (hlev : ∀ n : ℕ, ∃ T : ℝ, ∀ t₂ : ℝ, T ≤ t₂ →
      ∀ (q : H.Carrier → (postStage F.observation t₂).Carrier) (R'' : ℝ), R₁ ≤ R'' →
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ q (riemannianBallOf H.metric H.basepoint (4 * R'')) →
      Set.InjOn q (riemannianBallOf H.metric H.basepoint (4 * R'')) →
      (∀ k'' : ℕ, k'' ≤ k₁ → ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * R''),
        ckErr_S45 H (postMetric F.observation t₂) t₂⁻¹ q k'' p < ε₁) →
      ∃ (φ : H.Carrier → (postStage F.observation t₂).Carrier)
        (U' : TopologicalSpace.Opens H.Carrier) (y₀ : H.Carrier),
        riemannianBallOf H.metric y₀ (4 * (1 / ((n : ℝ) + 1))⁻¹) ⊆ U' ∧
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ U' ∧
        IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U' => φ x) ∧
        (∀ k : ℕ, k ≤ ⌈(1 / ((n : ℝ) + 1))⁻¹⌉₊ →
          ∀ p ∈ riemannianBallOf H.metric y₀ (4 * (1 / ((n : ℝ) + 1))⁻¹),
          ckErr_S45 H (postMetric F.observation t₂) t₂⁻¹ φ k p < 1 / ((n : ℝ) + 1)) ∧
        φ y₀ = q H.basepoint) :
  ∃ βw : ℝ → ℝ, (∀ t, 0 < βw t) ∧ Filter.Tendsto βw Filter.atTop (nhds 0) ∧
    ∃ (ε₁ R₁ : ℝ) (k₁ : ℕ), 0 < ε₁ ∧ 0 < R₁ ∧ ∃ T₁ : ℝ, ∀ t₂ : ℝ, T₁ ≤ t₂ →
      ∀ (q : H.Carrier → (postStage F.observation t₂).Carrier) (R'' : ℝ), R₁ ≤ R'' →
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ q (riemannianBallOf H.metric H.basepoint (4 * R'')) →
      Set.InjOn q (riemannianBallOf H.metric H.basepoint (4 * R'')) →
      (∀ k'' : ℕ, k'' ≤ k₁ → ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * R''),
        ckErr_S45 H (postMetric F.observation t₂) t₂⁻¹ q k'' p < ε₁) →
      ∃ (φ : H.Carrier → (postStage F.observation t₂).Carrier)
        (U' : TopologicalSpace.Opens H.Carrier) (y₀ : H.Carrier),
        riemannianBallOf H.metric y₀ (4 * (βw t₂)⁻¹) ⊆ U' ∧
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ U' ∧
        IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U' => φ x) ∧
        (∀ k : ℕ, k ≤ ⌈(βw t₂)⁻¹⌉₊ → ∀ p ∈ riemannianBallOf H.metric y₀ (4 * (βw t₂)⁻¹),
          ckErr_S45 H (postMetric F.observation t₂) t₂⁻¹ φ k p < βw t₂) ∧
        φ y₀ = q H.basepoint := by
  classical
  choose T hT using hlev
  let Tm : ℕ → ℝ := fun n => ∑ i ∈ Finset.range (n + 1), |T i|
  have hTm : ∀ n, T n ≤ Tm n := fun n =>
    (le_abs_self _).trans (Finset.single_le_sum (f := fun i => |T i|)
      (fun i _ => abs_nonneg _) (Finset.self_mem_range_succ n))
  let N : ℝ → ℕ := fun t => Nat.findGreatest (fun n => Tm n ≤ t) ⌊t⌋₊
  have hNspec : ∀ t, Tm 0 ≤ t → Tm (N t) ≤ t := fun t ht =>
    Nat.findGreatest_spec (P := fun n => Tm n ≤ t) (Nat.zero_le _) ht
  have hNtend : Tendsto N atTop atTop := by
    refine Filter.tendsto_atTop_atTop.2 fun n₀ => ⟨max (Tm n₀) n₀, fun t ht => ?_⟩
    have h1 : Tm n₀ ≤ t := (le_max_left _ _).trans ht
    have h2 : (n₀ : ℝ) ≤ t := (le_max_right _ _).trans ht
    exact Nat.le_findGreatest (Nat.le_floor h2) h1
  refine ⟨fun t => 1 / ((N t : ℝ) + 1), fun t => by positivity,
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hNtend, ε₁, R₁, k₁, hε₁, hR₁, Tm 0,
    fun t₂ ht₂ q R'' hR hq hinj herr => ?_⟩
  exact hT (N t₂) t₂ ((hTm _).trans (hNspec t₂ ht₂)) q R'' hR hq hinj herr

/-- G1 main: the OLD-CORE case (B'): per-level anchors for every admissible `q` whose basepoint
image lies in an old core `mold i t₂ '' B((α i t₂)⁻¹/2)`. Inputs: old GOOD data `hgood` and the
old-core rigidity `hrig` (`q(bp)` in old core `i` ⇒ `H ≅ Hold i`). -/
theorem old_case_levels_O60 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (H : FiniteVolumeHyperbolicModel.{u})
    (old : ℕ) (Hold : Fin old → FiniteVolumeHyperbolicModel.{u}) (sold : Fin old → ℝ)
    (mold : ∀ i (t : ℝ), sold i ≤ t → (Hold i).Carrier → (postStage F.observation t).Carrier)
    (α : Fin old → ℝ → ℝ) (hαpos : ∀ i t, 0 < α i t)
    (hα0 : ∀ i, Filter.Tendsto (α i) Filter.atTop (nhds 0))
    (hgood : ∀ i t (hi : sold i ≤ t), ∃ U : TopologicalSpace.Opens (Hold i).Carrier,
      riemannianBallOf (Hold i).metric (Hold i).basepoint (2 * (α i t)⁻¹) ⊆ U ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ (mold i t hi) U ∧
      IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => mold i t hi x) ∧
      ∀ k : ℕ, k ≤ ⌈(α i t)⁻¹⌉₊ →
        ∀ p ∈ riemannianBallOf (Hold i).metric (Hold i).basepoint (2 * (α i t)⁻¹),
        ckErr_S45 (Hold i) (postMetric F.observation t) t⁻¹ (mold i t hi) k p < α i t)
    (hrig : ∃ (ε R : ℝ) (k : ℕ), 0 < ε ∧ 0 < R ∧ ∃ T : ℝ,
      ∀ (i : Fin old) (t : ℝ) (hi : sold i ≤ t), T ≤ t →
      ∀ (q : H.Carrier → (postStage F.observation t).Carrier) (R'' : ℝ), R ≤ R'' →
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ q (riemannianBallOf H.metric H.basepoint (4 * R'')) →
      Set.InjOn q (riemannianBallOf H.metric H.basepoint (4 * R'')) →
      (∀ k'' : ℕ, k'' ≤ k → ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * R''),
        ckErr_S45 H (postMetric F.observation t) t⁻¹ q k'' p < ε) →
      ∀ z ∈ riemannianBallOf (Hold i).metric (Hold i).basepoint ((α i t)⁻¹ / 2),
        mold i t hi z = q H.basepoint →
      ∃ e : H.Carrier ≃ (Hold i).Carrier, ContMDiff (𝓡 3) (𝓡 3) ∞ e ∧
        ContMDiff (𝓡 3) (𝓡 3) ∞ e.symm ∧
        ∀ p, localPullInner (Hold i).metric e p = H.metric.inner p) :
    ∃ (ε R : ℝ) (k : ℕ), 0 < ε ∧ 0 < R ∧ ∀ n : ℕ, ∃ T : ℝ, 1 ≤ T ∧ ∀ t₂ : ℝ, T ≤ t₂ →
      ∀ (q : H.Carrier → (postStage F.observation t₂).Carrier) (R'' : ℝ), R ≤ R'' →
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ q (riemannianBallOf H.metric H.basepoint (4 * R'')) →
      Set.InjOn q (riemannianBallOf H.metric H.basepoint (4 * R'')) →
      (∀ k'' : ℕ, k'' ≤ k → ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * R''),
        ckErr_S45 H (postMetric F.observation t₂) t₂⁻¹ q k'' p < ε) →
      ∀ (i : Fin old) (hi : sold i ≤ t₂),
      ∀ z ∈ riemannianBallOf (Hold i).metric (Hold i).basepoint ((α i t₂)⁻¹ / 2),
        mold i t₂ hi z = q H.basepoint →
      ∃ (φ : H.Carrier → (postStage F.observation t₂).Carrier)
        (U' : TopologicalSpace.Opens H.Carrier) (y₀ : H.Carrier),
        riemannianBallOf H.metric y₀ (4 * (1 / ((n : ℝ) + 1))⁻¹) ⊆ U' ∧
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ U' ∧
        IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U' => φ x) ∧
        (∀ k : ℕ, k ≤ ⌈(1 / ((n : ℝ) + 1))⁻¹⌉₊ →
          ∀ p ∈ riemannianBallOf H.metric y₀ (4 * (1 / ((n : ℝ) + 1))⁻¹),
          ckErr_S45 H (postMetric F.observation t₂) t₂⁻¹ φ k p < 1 / ((n : ℝ) + 1)) ∧
        φ y₀ = q H.basepoint := by
  obtain ⟨ε, R, k, hε, hR, T, hT⟩ := hrig
  refine ⟨ε, R, k, hε, hR, fun n => ?_⟩
  have hβ : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  have hev : ∀ᶠ t in atTop, ∀ i, α i t < 3 / 8 * (1 / ((n : ℝ) + 1)) := by
    rw [Filter.eventually_all]
    intro i
    exact (hα0 i).eventually (gt_mem_nhds (by positivity))
  obtain ⟨T', hT'⟩ := Filter.eventually_atTop.1 hev
  refine ⟨max (max T T') 1, le_max_right _ _,
    fun t₂ ht₂ q R'' hR'' hq hinj herr i hi z hz hzq => ?_⟩
  have ht₂T : T ≤ t₂ := (le_max_left _ _).trans ((le_max_left _ _).trans ht₂)
  have ht₂T' : T' ≤ t₂ := (le_max_right _ _).trans ((le_max_left _ _).trans ht₂)
  have ht₂pos : 0 < t₂ := lt_of_lt_of_le one_pos ((le_max_right _ _).trans ht₂)
  obtain ⟨e, he, he', hiso⟩ := hT i t₂ hi ht₂T q R'' hR'' hq hinj herr z hz hzq
  have hαi := hT' t₂ ht₂T' i
  have hαp := hαpos i t₂
  have hrad : (α i t₂)⁻¹ / 2 + 4 * (1 / ((n : ℝ) + 1))⁻¹ ≤ 2 * (α i t₂)⁻¹ := by
    have key : 4 * (1 / ((n : ℝ) + 1))⁻¹ ≤ 3 / 2 * (α i t₂)⁻¹ := by
      rw [show 4 * (1 / ((n : ℝ) + 1))⁻¹ = 4 / (1 / ((n : ℝ) + 1)) by ring,
        show 3 / 2 * (α i t₂)⁻¹ = (3 / 2) / α i t₂ by ring, div_le_div_iff₀ hβ hαp]
      linarith
    linarith
  obtain ⟨φ, U', y₀, h1, h2, h3, h4, h5⟩ := core_anchor_O60 H (Hold i) e he he' hiso
    (postMetric F.observation t₂) t₂⁻¹ (inv_pos.2 ht₂pos) (mold i t₂ hi) (α i t₂)
    (1 / ((n : ℝ) + 1)) ((α i t₂)⁻¹ / 2) hαp (by positivity) (by linarith) hrad
    (hgood i t₂ hi) z hz
  exact ⟨φ, U', y₀, h1, h2, h3, h4, h5.trans hzq⟩

end GC.LongTime.Ch12
