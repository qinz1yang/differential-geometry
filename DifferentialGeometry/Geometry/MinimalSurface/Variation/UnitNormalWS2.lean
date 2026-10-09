import DifferentialGeometry.Geometry.MinimalSurface.Variation.UnitNormalLinearWS2
import DifferentialGeometry.Geometry.MinimalSurface.Variation.UnitNormalLocalWS2
import DifferentialGeometry.Geometry.Curvature.StabilityConformalWS2
import DifferentialGeometry.Bundle.Orientation.FrameTransport
import DifferentialGeometry.Topology.Manifold.Orientation

/-!
# S-W-STAB-2 G2：定向三维流形中浸入曲面的光滑单位法向 `exists_unit_normal_WS2`

`U : ℂ → M`，`N ⊆ ℂ` 开，`U` 在 `N` 上光滑浸入三维定向（`ManifoldOrientation`）黎曼流形 `(M, g)`。
对 `z ∈ N` 令 `ν z` 为唯一的 `g`-单位法向使得 `(dU_x, dU_y, ν)` 与 `o` 同向（`posNormal_unique_WS2`），
`ν` 光滑：局部用 `exists_local_unit_normal_WS2` 得到光滑单位法向 `ν_loc`，`ν = ± ν_loc`，
符号由 `frame_orientation_isLocallyConstant`（光滑标架的定向相对 `o` 局部常值）局部常值。
-/

set_option autoImplicit false
noncomputable section

open Bundle Filter Manifold Set
open scoped ContDiff Manifold _root_.Topology

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- 标架（沿连续映射 `γ`）的定向相对 `o` 局部常值。 -/
theorem frame_orientation_isLocallyConstant_WS2 (hdim : Module.finrank ℝ E = 3)
    (o : DifferentialGeometry.ManifoldOrientation 𝓘(ℝ, E) M 3) {X : Type*} [TopologicalSpace X]
    (γ : X → M) (hγ : Continuous γ)
    (b : ∀ x, Module.Basis (Fin 3) ℝ (TangentSpace 𝓘(ℝ, E) (γ x)))
    (hb : ∀ i, Continuous (fun x => (⟨γ x, b x i⟩ : TangentBundle 𝓘(ℝ, E) M))) :
    IsLocallyConstant (fun x => (b x).orientation = o.orientation (γ x)) :=
  DifferentialGeometry.VectorBundle.isLocallyConstant_frame_orientation
    (tangentBundleCore 𝓘(ℝ, E) M) hdim γ hγ o.orientation
    (DifferentialGeometry.Topology.Manifold.isCompatibleOrientation_of_manifoldOrientation o) b hb

/-- `g_x` 作为 `T →ₗ T →ₗ ℝ`。 -/
def innerLM_WS2 (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (x : M) :
    TangentSpace 𝓘(ℝ, E) x →ₗ[ℝ] TangentSpace 𝓘(ℝ, E) x →ₗ[ℝ] ℝ :=
  (ContinuousLinearMap.coeLM ℝ).comp (g.inner x).toLinearMap

omit [FiniteDimensional ℝ E] in
theorem innerLM_apply_WS2 (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (x : M)
    (u v : TangentSpace 𝓘(ℝ, E) x) : innerLM_WS2 g x u v = g.inner x u v := rfl

/-- 单射的 `ℂ →L[ℝ] T` 把 `1, i` 送到线性无关对。 -/
theorem linearIndependent_partials_WS2 {T : Type*} [AddCommGroup T] [Module ℝ T]
    [TopologicalSpace T]
    (L : ℂ →L[ℝ] T) (hL : Function.Injective L) :
    LinearIndependent ℝ ![L (1 : ℂ), L Complex.I] := by
  rw [LinearIndependent.pair_iff]
  intro x y hxy
  have h3 : x • (1 : ℂ) + y • Complex.I = 0 :=
    hL (by rw [map_add, map_smul, map_smul, map_zero]; exact hxy)
  exact ⟨by simpa [Complex.real_smul] using congrArg Complex.re h3,
    by simpa [Complex.real_smul] using congrArg Complex.im h3⟩

/-- **G2 `exists_unit_normal_WS2`.**  定向三维黎曼流形 `(M, g, o)` 中，`U : ℂ → M` 在开集 `N` 上
光滑浸入 ⇒ 沿 `U|_N` 存在光滑 `g`-单位法向场 `ν`。 -/
theorem exists_unit_normal_WS2 (hdim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (o : DifferentialGeometry.ManifoldOrientation 𝓘(ℝ, E) M 3) {U : ℂ → M}
    (N : TopologicalSpace.Opens ℂ)
    (hUN : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (fun q : N => U q))
    (hiN : ∀ q : N, Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun p : N => U p) q)) :
    ∃ ν : ∀ q : N, TangentSpace 𝓘(ℝ, E) (U q),
      ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, E).tangent) ∞
        (fun q : N => (⟨U q, ν q⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
      (∀ q : N, g.inner (U q) (ν q) (ν q) = 1) ∧
      ∀ (q : N) (v : ℂ), g.inner (U q) (ν q)
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun p : N => U p) q v) = 0 := by
  classical
  have hUon : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U (N : Set ℂ) := contMDiffOn_of_subtype_WS2 N hUN
  have hdf : ∀ q : N, mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun p : N => U p) q =
      mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U q :=
    fun q => DifferentialGeometry.mfderiv_restrict_open (I := 𝓘(ℝ, ℂ)) (J := 𝓘(ℝ, E)) U N q
  have hinj : ∀ z ∈ (N : Set ℂ), Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z) := by
    intro z hz
    have h := hiN ⟨z, hz⟩
    rwa [hdf] at h
  have hpart : ∀ z ∈ (N : Set ℂ), LinearIndependent ℝ
      ![mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z (1 : ℂ), mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z Complex.I] :=
    fun z hz => linearIndependent_partials_WS2
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z : ℂ →L[ℝ] TangentSpace 𝓘(ℝ, E) (U z)) (hinj z hz)
  have hsym : ∀ (x : M) (u v : TangentSpace 𝓘(ℝ, E) x),
      innerLM_WS2 g x u v = innerLM_WS2 g x v u := fun x u v => g.symm x u v
  have hpos : ∀ (x : M) (u : TangentSpace 𝓘(ℝ, E) x), u ≠ 0 → 0 < innerLM_WS2 g x u u :=
    fun x u hu => g.pos x u hu
  let Pos : ∀ z : ℂ, TangentSpace 𝓘(ℝ, E) (U z) → Prop := fun z n =>
    g.inner (U z) n n = 1 ∧
      (∀ v : ℂ, g.inner (U z) n (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z v) = 0) ∧
      ∃ h : LinearIndependent ℝ ![mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z (1 : ℂ),
          mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z Complex.I, n],
        (frameBasis_WS2 hdim h).orientation = o.orientation (U z)
  have hex : ∀ z : ℂ, ∃ n : TangentSpace 𝓘(ℝ, E) (U z), z ∈ (N : Set ℂ) → Pos z n := by
    intro z
    by_cases hz : z ∈ (N : Set ℂ)
    · obtain ⟨s₀, -, hz₀, -, νl, -, hνunit, hνnor⟩ :=
        exists_local_unit_normal_WS2 hdim g N.isOpen hUon hinj hz
      have hn1 := hνunit z hz₀
      have hn2 := hνnor z hz₀
      rcases posNormal_or_neg_WS2 hdim (innerLM_WS2 g (U z)) (o.orientation (U z)) (hpart z hz)
        (hn2 1) (hn2 Complex.I) hn1 with h | h
      · exact ⟨νl z, fun _ => ⟨hn1, hn2, h⟩⟩
      · exact ⟨-νl z, fun _ => ⟨by simpa using hn1, fun v => by simpa using hn2 v, h⟩⟩
    · exact ⟨0, fun h => absurd h hz⟩
  let νℂ : ∀ z : ℂ, TangentSpace 𝓘(ℝ, E) (U z) := fun z => Classical.choose (hex z)
  have hν : ∀ z ∈ (N : Set ℂ), Pos z (νℂ z) := fun z hz => Classical.choose_spec (hex z) hz
  have hsm : ∀ z₀ ∈ (N : Set ℂ), ContMDiffAt 𝓘(ℝ, ℂ) (𝓘(ℝ, E).tangent) ∞
      (fun z : ℂ => (⟨U z, νℂ z⟩ : TangentBundle 𝓘(ℝ, E) M)) z₀ := by
    intro z₀ hz₀
    obtain ⟨s₀, hs₀, hz₀', hss, νl, hνsm, hνunit, hνnor⟩ :=
      exists_local_unit_normal_WS2 hdim g N.isOpen hUon hinj hz₀
    have hfr : ∀ x : s₀, LinearIndependent ℝ ![mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U x (1 : ℂ),
        mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U x Complex.I, νl x] := fun x =>
      linearIndependent_frame_WS2 (innerLM_WS2 g (U x)) (hpart x (hss x.2))
        (hνnor x x.2 1) (hνnor x x.2 Complex.I) (hνunit x x.2)
    let bb : ∀ x : s₀, Module.Basis (Fin 3) ℝ (TangentSpace 𝓘(ℝ, E) (U x)) :=
      fun x => frameBasis_WS2 hdim (hfr x)
    have hUs₀ : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s₀ := hUon.mono hss
    have hγ : Continuous (fun x : s₀ => U x) := hUs₀.continuousOn.domRestrict
    have hpartc : ∀ v : ℂ, Continuous (fun x : s₀ =>
        (⟨U x, mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U x v⟩ : TangentBundle 𝓘(ℝ, E) M)) := by
      intro v
      exact (contMDiffOn_source_partial (m := ∞) (n := ∞) hs₀ hUs₀ (by simp)
        v).continuousOn.domRestrict
    have hνc : Continuous (fun x : s₀ => (⟨U x, νl x⟩ : TangentBundle 𝓘(ℝ, E) M)) :=
      hνsm.continuousOn.domRestrict
    have hbc : ∀ i, Continuous (fun x : s₀ => (⟨U x, bb x i⟩ : TangentBundle 𝓘(ℝ, E) M)) := by
      intro i
      fin_cases i
      · refine (hpartc 1).congr fun x => ?_
        exact congrArg (Bundle.TotalSpace.mk' E (U x))
          (frameBasis_apply_WS2 hdim (hfr x) 0).symm
      · refine (hpartc Complex.I).congr fun x => ?_
        exact congrArg (Bundle.TotalSpace.mk' E (U x))
          (frameBasis_apply_WS2 hdim (hfr x) 1).symm
      · refine hνc.congr fun x => ?_
        exact congrArg (Bundle.TotalSpace.mk' E (U x))
          (frameBasis_apply_WS2 hdim (hfr x) 2).symm
    have hlc := frame_orientation_isLocallyConstant_WS2 hdim o (fun x : s₀ => U x) hγ bb hbc
    let x₀ : s₀ := ⟨z₀, hz₀'⟩
    have hopen : IsOpen {x : s₀ | ((bb x).orientation = o.orientation (U x)) =
        ((bb x₀).orientation = o.orientation (U x₀))} :=
      hlc.isOpen_fiber ((bb x₀).orientation = o.orientation (U x₀))
    let W : Set ℂ := Subtype.val '' {x : s₀ | ((bb x).orientation = o.orientation (U x)) =
        ((bb x₀).orientation = o.orientation (U x₀))}
    have hW : IsOpen W := hs₀.isOpenEmbedding_subtypeVal.isOpenMap _ hopen
    have hz₀W : z₀ ∈ W := ⟨x₀, rfl, rfl⟩
    have hWs : W ⊆ s₀ := fun z ⟨x, _, hx⟩ => hx ▸ x.2
    have hsign : ∃ ε : ℝ, ∀ z ∈ W, νℂ z = ε • νl z := by
      by_cases hP₀ : (bb x₀).orientation = o.orientation (U x₀)
      · refine ⟨1, fun z hz => ?_⟩
        obtain ⟨x, hx, rfl⟩ := hz
        have hPx : (bb x).orientation = o.orientation (U x) := by
          rw [show ((bb x).orientation = o.orientation (U x)) =
            ((bb x₀).orientation = o.orientation (U x₀)) from hx]
          exact hP₀
        obtain ⟨hu1, hu2, hu3⟩ := hν x (hss x.2)
        rw [one_smul]
        exact posNormal_unique_WS2 hdim (innerLM_WS2 g (U x)) (hsym (U x)) (hpos (U x))
          (o.orientation (U x)) (hpart x (hss x.2)) (hνnor x x.2 1) (hνnor x x.2 Complex.I)
          (hνunit x x.2) (hu2 1) (hu2 Complex.I) hu1 ⟨hfr x, hPx⟩ hu3
      · refine ⟨-1, fun z hz => ?_⟩
        obtain ⟨x, hx, rfl⟩ := hz
        have hPx : ¬ ((bb x).orientation = o.orientation (U x)) := by
          rw [show ((bb x).orientation = o.orientation (U x)) =
            ((bb x₀).orientation = o.orientation (U x₀)) from hx]
          exact hP₀
        have hneg : o.orientation (U x) = -(bb x).orientation :=
          (Module.Basis.orientation_ne_iff_eq_neg (bb x) (o.orientation (U x))).mp
            (Ne.symm hPx)
        have hn1 : g.inner (U x) (-νl x) (-νl x) = 1 := by simpa using hνunit x x.2
        have hn2 : ∀ v : ℂ, g.inner (U x) (-νl x)
            (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U x v) = 0 := fun v => by simpa using hνnor x x.2 v
        have hfr' : LinearIndependent ℝ ![mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U x (1 : ℂ),
            mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U x Complex.I, -νl x] :=
          linearIndependent_frame_WS2 (innerLM_WS2 g (U x)) (hpart x (hss x.2))
            (hn2 1) (hn2 Complex.I) hn1
        obtain ⟨hu1, hu2, hu3⟩ := hν x (hss x.2)
        rw [neg_one_smul]
        exact posNormal_unique_WS2 hdim (innerLM_WS2 g (U x)) (hsym (U x)) (hpos (U x))
          (o.orientation (U x)) (hpart x (hss x.2)) (hn2 1) (hn2 Complex.I) hn1
          (hu2 1) (hu2 Complex.I) hu1
          ⟨hfr', (frameBasis_neg_orientation_WS2 hdim (hfr x) hfr').trans hneg.symm⟩ hu3
    obtain ⟨ε, hε⟩ := hsign
    have hG : ContMDiffOn 𝓘(ℝ, ℂ) (𝓘(ℝ, E).tangent) ∞
        (fun z : ℂ => (⟨U z, ε • νl z⟩ : TangentBundle 𝓘(ℝ, E) M)) W :=
      ContMDiffOn.smul_bundle (contMDiffOn_const) (hνsm.mono hWs)
    have hF : ContMDiffOn 𝓘(ℝ, ℂ) (𝓘(ℝ, E).tangent) ∞
        (fun z : ℂ => (⟨U z, νℂ z⟩ : TangentBundle 𝓘(ℝ, E) M)) W :=
      hG.congr fun z hz => congrArg (Bundle.TotalSpace.mk' E (U z)) (hε z hz)
    exact hF.contMDiffAt (hW.mem_nhds hz₀W)
  refine ⟨fun q => νℂ q, fun q => contMDiffAt_subtype_iff.mpr (hsm q q.2),
    fun q => (hν q q.2).1, fun q v => ?_⟩
  rw [hdf q]
  exact (hν q q.2).2.1 v

section MorreyNuFree

open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Topology MeasureTheory
open DifferentialGeometry.Integral.Measure

private local instance (N : TopologicalSpace.Opens ℂ) : MeasurableSpace N := borel N
private local instance (N : TopologicalSpace.Opens ℂ) : BorelSpace N := ⟨rfl⟩
private local instance (N : TopologicalSpace.Opens ℂ) : LocallyCompactSpace N :=
  N.isOpen.locallyCompactSpace
private local instance (N : TopologicalSpace.Opens ℂ) : SigmaCompactSpace N := by infer_instance

variable [T3Space M]

/-- **G2 `ν`-free 共形 stability.**  `IsMorreyDisk` 的 regular part `N`（`U` 在 `N` 上浸入，
`N ⊆` 开单位盘，`U` 的像在 `interior W`）上，定向三维 `(M, g, o)` 下，不再有 `ν` 参数：
`∃ VJ ∈ C^∞(N)`（`VJ ≤ K_Σ − R/2`），`∀ ψ ∈ C_c^∞(ℂ)`，`tsupport ψ ⊆ N ⇒`
`0 ≤ ∫ ‖dψ‖² + λ·VJ·ψ²`。 -/
theorem IsMorreyDisk.stability_inequality_conformal_nu_free_WS2
    (hdim : Module.finrank ℝ E = 3) {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {γ : freeLoop M}
    (hγ : IsSmoothEmbeddedLoop (E := E) γ) {u : C(closedDisk, M)} (hu : IsMorreyDisk g γ u)
    {U : ℂ → M} (hExt : SmoothDiskExtension (E := E) u U) (W : Set M) (hW : Set.range u ⊆ W)
    (o : DifferentialGeometry.ManifoldOrientation 𝓘(ℝ, E) M 3)
    (N : TopologicalSpace.Opens ℂ) (hNball : (N : Set ℂ) ⊆ Metric.ball 0 1)
    (hUN : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (fun q : N => U q))
    (hiN : ∀ q : N, Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun p : N => U p) q))
    (hint : ∀ z ∈ N, U z ∈ interior W) :
    let gN := g.pullback (fun p : N => U p) hUN hiN
    ∃ VJ : ℂ → ℝ, ContDiffOn ℝ ∞ VJ (N : Set ℂ) ∧
      (∀ q : N, VJ q ≤ scalarCurv gN q / 2 - scalarCurv g (U q) / 2) ∧
      ∀ ψ : ℂ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ (N : Set ℂ) →
        Integrable (fun x => ‖fderiv ℝ ψ x‖ ^ 2 +
          diskMapConformalCoefficient g U x * VJ x * ψ x ^ 2) ∧
        0 ≤ ∫ x, (‖fderiv ℝ ψ x‖ ^ 2 + diskMapConformalCoefficient g U x * VJ x * ψ x ^ 2) := by
  intro gN
  obtain ⟨ν, hν, hunit, hnormal⟩ := exists_unit_normal_WS2 hdim g o N hUN hiN
  obtain ⟨VJ, hC, -, hb, hs⟩ :=
    IsMorreyDisk.stability_inequality_conformal_WS2 hdim hγ hu hExt W hW N hNball hUN hiN hint
      ν hν hunit hnormal
  exact ⟨VJ, hC, hb, hs⟩

/-- **G2 `ν`-free planar 形状（EIG 输入）.**  `ρ = λ`（`diskMapConformalCoefficient`，`C^∞(N)`、`> 0`）、
`Wt = λ·VJ`（`C^∞(N)`），无 `ν`。 -/
theorem IsMorreyDisk.planar_stability_nu_free_WS2
    (hdim : Module.finrank ℝ E = 3) {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {γ : freeLoop M}
    (hγ : IsSmoothEmbeddedLoop (E := E) γ) {u : C(closedDisk, M)} (hu : IsMorreyDisk g γ u)
    {U : ℂ → M} (hExt : SmoothDiskExtension (E := E) u U) (W : Set M) (hW : Set.range u ⊆ W)
    (o : DifferentialGeometry.ManifoldOrientation 𝓘(ℝ, E) M 3)
    (N : TopologicalSpace.Opens ℂ) (hNball : (N : Set ℂ) ⊆ Metric.ball 0 1)
    (hUN : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (fun q : N => U q))
    (hiN : ∀ q : N, Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun p : N => U p) q))
    (hint : ∀ z ∈ N, U z ∈ interior W) :
    ∃ Wt : ℂ → ℝ, ContDiffOn ℝ ∞ (diskMapConformalCoefficient g U) (N : Set ℂ) ∧
      ContDiffOn ℝ ∞ Wt (N : Set ℂ) ∧
      (∀ z ∈ N, 0 < diskMapConformalCoefficient g U z) ∧
      ∀ Ω : Set ℂ, Ω ⊆ (N : Set ℂ) → ∀ ψ : ℂ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ Ω → 0 ≤ ∫ x in Ω, (‖fderiv ℝ ψ x‖ ^ 2 + Wt x * ψ x ^ 2) := by
  have hconf : ∀ z ∈ N, DiskMapConformalAt g U z :=
    fun z hz => hu.conformal_of_extension hExt z (hNball hz)
  obtain ⟨hlamC, hlamP⟩ := conformalFactor_data_WS2 g N hUN hiN hconf
  obtain ⟨VJ, hVJC, -, hstab⟩ :=
    IsMorreyDisk.stability_inequality_conformal_nu_free_WS2 hdim hγ hu hExt W hW o N hNball hUN
      hiN hint
  refine ⟨fun x => diskMapConformalCoefficient g U x * VJ x, hlamC, hlamC.mul hVJC, hlamP, ?_⟩
  intro Ω hΩ ψ hψ hψc hψΩ
  have h := (hstab ψ hψ hψc (hψΩ.trans hΩ)).2
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ω)] at h
  · refine le_of_le_of_eq h (integral_congr_ae (Filter.Eventually.of_forall fun x => ?_))
    simp only [mul_assoc]
  · intro x hx
    have hx' : x ∉ tsupport ψ := fun hh => hx (hψΩ hh)
    obtain ⟨h1, h2⟩ := fderiv_eq_zero_of_notMem_tsupport_WS2 hx'
    simp [h1, h2]

/-- **G2 `ν`-free regular 形式.**  `stability_inequality_regular_WS` 的 `ν` 由 G2 供给：
`∃ ν`（光滑单位法向）使得对一切 `φ ∈ C_c^∞(N)` 与任意 `gN`-标准正交标架 `b`，
`∫_N (|∇φ|² − φ²(Ric(ν,ν) + |II|²)) dμ_{gN} ≥ 0`。 -/
theorem IsMorreyDisk.stability_inequality_regular_nu_free_WS2
    (hdim : Module.finrank ℝ E = 3) {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {γ : freeLoop M}
    (hγ : IsSmoothEmbeddedLoop (E := E) γ) {u : C(closedDisk, M)} (hu : IsMorreyDisk g γ u)
    {U : ℂ → M} (hExt : SmoothDiskExtension (E := E) u U) (W : Set M) (hW : Set.range u ⊆ W)
    (o : DifferentialGeometry.ManifoldOrientation 𝓘(ℝ, E) M 3)
    (N : TopologicalSpace.Opens ℂ) (hNball : (N : Set ℂ) ⊆ Metric.ball 0 1)
    (hUN : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (fun q : N => U q))
    (hiN : ∀ q : N, Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun p : N => U p) q))
    (hint : ∀ z ∈ N, U z ∈ interior W) :
    ∃ ν : ∀ q : N, TangentSpace 𝓘(ℝ, E) (U q),
      ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, E).tangent) ∞
        (fun q : N => (⟨U q, ν q⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
      (∀ q : N, g.inner (U q) (ν q) (ν q) = 1) ∧
      (∀ (q : N) (v : ℂ), g.inner (U q) (ν q)
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun p : N => U p) q v) = 0) ∧
      ∀ (φ : N → ℝ), ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞ φ → HasCompactSupport φ →
        ∀ (b : ∀ q : N, Module.Basis (Fin 2) ℝ (TangentSpace 𝓘(ℝ, ℂ) q)),
          (∀ (q : N) (i j : Fin 2),
            (g.pullback (fun p : N => U p) hUN hiN).inner q (b q i) (b q j) =
              if i = j then 1 else 0) →
          let gN := g.pullback (fun p : N => U p) hUN hiN
          let μ := riemannianVolumeMeasure (I := 𝓘(ℝ, ℂ)) (M := N) gN
          let J : N → ℝ := fun q =>
            let II := secondFundamentalFormAmbientAt gN g (fun p : N => U p) q
            gN.inner q (gradFun gN φ q) (gradFun gN φ q) -
              φ q ^ 2 * ((∑ i : Fin 2, g.inner (U q) ((riemannOp (LeviCivita g) (U q)) (ν q)
                  (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U q (b q i)) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U q (b q i)))
                  (ν q)) +
                ∑ i : Fin 2, ∑ j : Fin 2,
                  g.inner (U q) (II (b q i) (b q j)) (II (b q i) (b q j)))
          Integrable J μ ∧ 0 ≤ ∫ q : N, J q ∂μ := by
  obtain ⟨ν, hν, hunit, hnormal⟩ := exists_unit_normal_WS2 hdim g o N hUN hiN
  exact ⟨ν, hν, hunit, hnormal, fun φ hφ hφc b hb =>
    IsMorreyDisk.stability_inequality_regular_WS hdim hγ hu hExt W hW N hNball hUN hiN hint
      ν hν hunit hnormal φ hφ hφc b hb⟩

end MorreyNuFree

end DifferentialGeometry.Geometry
