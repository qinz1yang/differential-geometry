import DifferentialGeometry.Geometry.Collapse.LocalExport.SlimSurfaceFactor
import DifferentialGeometry.Geometry.Collapse.FiniteSurface.SurfaceCarrierNoncompact

/-!
# The surface structure of the factor of a slim product model (LFR20 item 3, producer)

Lane LFR20-CMP, packet 2. `nonempty_slimSurfaceFactor`: every LC81 slim product model
`P : SlimProductModel c K` (`K ≥ 4`) whose model `P.N` carries an orientation has a
`SlimSurfaceFactor P`: a smooth oriented surface `S`, isometric to `P.W` through `ψ`, with a
`C^{K-1}` metric `κ` of nonnegative curvature inducing its distance, and `N = ℝ × S` as a `C^K`
Riemannian product through the SAME splitting `P.e`.

Source: LFR16's surface clause on the model's own data (`P.G`, `P.enorm`, `P.sectional_nonneg`,
`P.e`): the smooth carrier `surfaceFactor_smoothCarrier_oriented_noncompact` (oriented from the
given orientation of `N` and the ordered normal factor `∂_t`) and the product map
`splittingProductDiffeomorph` of `exactSplitting_regularity`, composed with the carrier map.
Threshold producers of the orientation: `slimChart_model_comparison_threshold`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter WithLp Manifold Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Geometry.ExactSplitting DifferentialGeometry.Manifold
  DifferentialGeometry.Topology.Manifold GC.MetricGeometry

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] SlimProductModel.instMetricN SlimProductModel.instChartedN
  SlimProductModel.instManifoldN SlimProductModel.instProperN SlimProductModel.instConnectedN
  SlimProductModel.instBundleN SlimProductModel.instRiemannianN SlimProductModel.instMetricW
  SlimProductModel.instCompactW

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "P2" => Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) - Module.finrank ℝ ℝ) → ℝ

local instance nezero_finrank_euclidean_three_surfaceProducer_LFR20CMP :
    NeZero (Module.finrank ℝ E3) :=
  ⟨by rw [finrank_euclideanSpace_fin]; decide⟩

variable {M : Type*} [MetricSpace M] [ChartedSpace E3 M] [IsManifold 𝓘(ℝ, E3) ∞ M]
  [SigmaCompactSpace M] [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E3) x)]
  [IsRiemannianManifold 𝓘(ℝ, E3) M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E3 (fun x : M => TangentSpace 𝓘(ℝ, E3) x)]

/-- A surface metric of natural order `(K - 2) + 1`, re-indexed at order `K - 1`. The inner
product is unchanged. -/
def surfaceMetricReindex {S : Type*} [TopologicalSpace S] [ChartedSpace E2 S]
    [IsManifold (𝓡 2) ∞ S] (K : ℕ) (hK : 2 ≤ K)
    (κ : ContMDiffRiemannianMetric (𝓡 2) ((K - 2 + 1 : ℕ) : ℕ∞ω) E2
      (TangentSpace (𝓡 2) : S → Type _)) :
    ContMDiffRiemannianMetric (𝓡 2) ((K - 1 : ℕ) : ℕ∞ω) E2 (TangentSpace (𝓡 2) : S → Type _) :=
  { κ with
    contMDiff := by
      have h : ((K - 2 + 1 : ℕ) : ℕ∞ω) = ((K - 1 : ℕ) : ℕ∞ω) := by
        rw [show K - 2 + 1 = K - 1 by omega]
      exact h ▸ κ.contMDiff }

/-- The differential of `q ↦ Ψ (q.1, φ q.2)` (general manifolds). -/
theorem mfderiv_comp_prodMap_id_apply {EZ ES EN : Type*} [NormedAddCommGroup EZ]
    [NormedSpace ℝ EZ] [NormedAddCommGroup ES] [NormedSpace ℝ ES] [NormedAddCommGroup EN]
    [NormedSpace ℝ EN] {HZ HS HN : Type*} [TopologicalSpace HZ] [TopologicalSpace HS]
    [TopologicalSpace HN] {IZ : ModelWithCorners ℝ EZ HZ} {IS : ModelWithCorners ℝ ES HS}
    {IN : ModelWithCorners ℝ EN HN} {Z S N : Type*} [TopologicalSpace Z] [ChartedSpace HZ Z]
    [TopologicalSpace S] [ChartedSpace HS S] [TopologicalSpace N] [ChartedSpace HN N]
    (Ψ : ℝ × Z → N) (φ : S → Z) (q : ℝ × S)
    (hΨ : MDifferentiableAt (𝓘(ℝ, ℝ).prod IZ) IN Ψ (q.1, φ q.2))
    (hφ : MDifferentiableAt IS IZ φ q.2) (v : TangentSpace (𝓘(ℝ, ℝ).prod IS) q) :
    mfderiv (𝓘(ℝ, ℝ).prod IS) IN (fun q : ℝ × S => Ψ (q.1, φ q.2)) q v =
      mfderiv (𝓘(ℝ, ℝ).prod IZ) IN Ψ (q.1, φ q.2) (v.1, mfderiv IS IZ φ q.2 v.2) := by
  have hf : (fun q : ℝ × S => Ψ (q.1, φ q.2)) = Ψ ∘ Prod.map id φ := rfl
  rw [hf, mfderiv_comp q hΨ (mdifferentiableAt_id.prodMap' hφ),
    mfderiv_prodMap mdifferentiableAt_id hφ, mfderiv_id]
  rfl

/-- **The product clauses through a carrier** (abstract form). If `Ψ : ℝ × Z → N`,
`Ψ (t, z) = e⁻¹(t, (e (ι z))_W)`, is `C^n` with `C^n` inverse and `Ψ^* b_N = dt² + b_Z`, and
`φ : S → Z` is `C^n` with `C^n` inverse, `b_S = φ^* b_Z`, and `ψ s = (e (ι (φ s)))_W`, then
`(t, s) ↦ e⁻¹(t, ψ s)` is `C^n` with `C^n` inverse `x ↦ ((e x)_ℝ, ψ⁻¹ (e x)_W)` and pulls `b_N`
back to `dt² + b_S`. -/
theorem carrier_product_fields {EZ : Type*} [NormedAddCommGroup EZ] [NormedSpace ℝ EZ]
    {N Z S W : Type*} [MetricSpace N] [ChartedSpace E3 N] [TopologicalSpace Z]
    [ChartedSpace EZ Z] [MetricSpace S] [ChartedSpace E2 S] [MetricSpace W]
    (e : N ≃ᵢ WithLp 2 (ℝ × W)) (ι : Z → N) (Ψ : ℝ × Z → N) (Ψs : N → ℝ × Z) (φ : S → Z)
    (φs : Z → S) (ψ : S ≃ᵢ W) {n : ℕ∞ω} (hn : n ≠ 0)
    (hΨapp : ∀ p, Ψ p = e.symm (toLp 2 (p.1, (e (ι p.2)).snd)))
    (hΨΨs : ∀ x, Ψ (Ψs x) = x) (hφφs : ∀ z, φ (φs z) = z)
    (hψ : ∀ s, ψ s = (e (ι (φ s))).snd)
    (hΨ : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, EZ)) 𝓘(ℝ, E3) n Ψ)
    (hΨs : ContMDiff 𝓘(ℝ, E3) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, EZ)) n Ψs)
    (hφ : ContMDiff (𝓡 2) 𝓘(ℝ, EZ) n φ) (hφs : ContMDiff 𝓘(ℝ, EZ) (𝓡 2) n φs)
    (bN : N → E3 →L[ℝ] E3 →L[ℝ] ℝ) (bZ : Z → EZ →L[ℝ] EZ →L[ℝ] ℝ)
    (bS : S → E2 →L[ℝ] E2 →L[ℝ] ℝ)
    (hΨmet : ∀ (p : ℝ × Z) (v w : ℝ × EZ),
      bN (Ψ p) (mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, EZ)) 𝓘(ℝ, E3) Ψ p v)
        (mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, EZ)) 𝓘(ℝ, E3) Ψ p w) = inner ℝ v.1 w.1 + bZ p.2 v.2 w.2)
    (hκ : ∀ (s : S) (v w : E2),
      bS s v w = bZ (φ s) (mfderiv (𝓡 2) 𝓘(ℝ, EZ) φ s v) (mfderiv (𝓡 2) 𝓘(ℝ, EZ) φ s w)) :
    ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) n
        (fun q : ℝ × S => e.symm (toLp 2 (q.1, ψ q.2))) ∧
      ContMDiff 𝓘(ℝ, E3) (𝓘(ℝ, ℝ).prod (𝓡 2)) n
        (fun x : N => ((e x).fst, ψ.symm (e x).snd)) ∧
      ∀ (q : ℝ × S) (v w : ℝ × E2),
        bN (e.symm (toLp 2 (q.1, ψ q.2)))
          (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3)
            (fun q : ℝ × S => e.symm (toLp 2 (q.1, ψ q.2))) q v)
          (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3)
            (fun q : ℝ × S => e.symm (toLp 2 (q.1, ψ q.2))) q w) =
        inner ℝ v.1 w.1 + bS q.2 v.2 w.2 := by
  have hfun : (fun q : ℝ × S => e.symm (toLp 2 (q.1, ψ q.2))) =
      fun q : ℝ × S => Ψ (q.1, φ q.2) := by
    funext q
    rw [hΨapp, hψ]
  have hkey : ∀ x : N, ((e x).fst, ψ.symm (e x).snd) = ((Ψs x).1, φs (Ψs x).2) := by
    intro x
    have hex : e x = toLp 2 ((Ψs x).1, (e (ι (Ψs x).2)).snd) := by
      conv_lhs => rw [← hΨΨs x, hΨapp]
      exact e.apply_symm_apply _
    rw [hex]
    refine Prod.ext rfl ?_
    change ψ.symm (e (ι (Ψs x).2)).snd = φs (Ψs x).2
    rw [IsometryEquiv.symm_apply_eq, hψ, hφφs]
  have hfunS : (fun x : N => ((e x).fst, ψ.symm (e x).snd)) =
      Prod.map id φs ∘ Ψs := funext hkey
  refine ⟨?_, ?_, fun q v w => ?_⟩
  · rw [hfun]
    exact hΨ.comp (contMDiff_fst.prodMk (hφ.comp contMDiff_snd))
  · rw [hfunS]
    exact (contMDiff_id.prodMap hφs).comp hΨs
  · have hΨq : MDifferentiableAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, EZ)) 𝓘(ℝ, E3) Ψ (q.1, φ q.2) :=
      (hΨ _).mdifferentiableAt hn
    have hφq : MDifferentiableAt (𝓡 2) 𝓘(ℝ, EZ) φ q.2 := (hφ q.2).mdifferentiableAt hn
    have hD : ∀ u : ℝ × E2, mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3)
        (fun q : ℝ × S => e.symm (toLp 2 (q.1, ψ q.2))) q u =
        mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, EZ)) 𝓘(ℝ, E3) Ψ (q.1, φ q.2)
          (u.1, mfderiv (𝓡 2) 𝓘(ℝ, EZ) φ q.2 u.2) := fun u =>
      (congrArg (fun f => mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) f q u) hfun).trans
        (mfderiv_comp_prodMap_id_apply Ψ φ q hΨq hφq u)
    have hpt : e.symm (toLp 2 (q.1, ψ q.2)) = Ψ (q.1, φ q.2) := congrFun hfun q
    have hcongr : ∀ (x y : N) (a b c d : E3), x = y → a = c → b = d → bN x a b = bN y c d := by
      rintro x y a b c d rfl rfl rfl
      rfl
    refine (hcongr _ _ _ _ _ _ hpt (hD v) (hD w)).trans ((hΨmet (q.1, φ q.2) _ _).trans ?_)
    rw [hκ]

/-- **The surface structure of the factor of a slim product model.** -/
theorem nonempty_slimSurfaceFactor {g : SmoothRiemannianMetric 𝓘(ℝ, E3) M}
    {hEnorm : DifferentialGeometry.Geometry.Riemannian.IsMetricNorm g} {Δ σ : ℝ}
    {Y : Type*} [MetricSpace Y] {p : M} {y₀ : Y} {β : ℝ}
    {α : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), y₀)) β}
    {c : SlimChart g hEnorm Δ σ α} {K : ℕ} (hK : 4 ≤ K) (P : SlimProductModel c K)
    (oN : ManifoldOrientation (𝓡 3) P.N 3) : Nonempty (SlimSurfaceFactor P) := by
  have hk : (2 : ℕ∞) ≤ ((K - 2 : ℕ) : ℕ∞) := by exact_mod_cast (show 2 ≤ K - 2 by omega)
  let _ := splittingFactorChartedSpace P.G hk P.enorm P.e
  let _ := splittingFactor_isManifold_one P.G hk P.enorm P.e
  obtain ⟨S, mS, cS, iS, -, -, ⟨O⟩, φ, hφ, hφs, -, ⟨ψ, hψ⟩, κ, hκ, hsecS, hR, hnormS⟩ :=
    surfaceFactor_smoothCarrier_oriented_noncompact P.G hk P.enorm P.sectional_nonneg oN P.e
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hΨ, hΨs, hΨapp, hΨmet, -, -⟩ :=
    exactSplitting_regularity P.G hk P.enorm P.e
  let Z := {x : P.N // (P.e x).fst = 0}
  let Ψ := splittingProductDiffeomorph P.G hk P.enorm P.e
  have hK2 : (((K - 2 : ℕ) : ℕ∞) : ℕ∞ω) + 2 = (K : ℕ∞ω) := by
    rw [withTop_natCast_add_two, show K - 2 + 2 = K by omega]
  have hK2' : ((K - 2 + 2 : ℕ) : ℕ∞ω) = (K : ℕ∞ω) := by rw [show K - 2 + 2 = K by omega]
  have hK0 : (K : ℕ∞ω) ≠ 0 := by exact_mod_cast (show K ≠ 0 by omega)
  replace hΨ := hΨ.of_le hK2.symm.le
  replace hΨs := hΨs.of_le hK2.symm.le
  replace hφ := hφ.of_le hK2'.symm.le
  replace hφs := hφs.of_le hK2'.symm.le
  obtain ⟨hCK, hCKs, hmet⟩ := carrier_product_fields P.e (Subtype.val : Z → P.N)
    (Ψ : ℝ × Z → P.N) (Ψ.symm : P.N → ℝ × Z) φ φ.symm ψ hK0 hΨapp Ψ.apply_symm_apply
    φ.apply_symm_apply hψ hΨ hΨs hφ hφs (fun x => P.G.inner x)
    (fun z => (inducedMetric P.G hk P.enorm P.e).inner z) (fun s => κ.inner s) hΨmet hκ
  exact ⟨{ S := S
           instMetricS := mS
           instChartedS := cS
           instManifoldS := iS
           instBundleS := ⟨κ.toRiemannianMetric⟩
           instRiemannianS := hR
           ψ := ψ
           κ := surfaceMetricReindex K (by omega) κ
           enorm := hnormS
           sectional_nonneg := fun x v w => hsecS x v w
           orientation := O
           product_contMDiff := hCK
           product_symm_contMDiff := hCKs
           product_metric := hmet }⟩

end DifferentialGeometry.Geometry.Collapse
