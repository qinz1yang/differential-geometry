import DifferentialGeometry.Geometry.Exponential.FiniteMetric.SmoothAgreement
import DifferentialGeometry.Geometry.Exponential.RadialGeodesic
import DifferentialGeometry.Geometry.Exponential.Smoothness.AtZero.Derivative
import DifferentialGeometry.Geometry.Exponential.Smoothness.Domain
import DifferentialGeometry.Geometry.Metric.ParameterTangentMap

/-!
# S-W-STAB G1：parametrized 法向 geodesic 变分族 `F(t, z) = exp_{U z}(t · φ(z) ν(z))`

Route W 的 stability inequality 需要对 regular part `N`（`U` 只在 `N` 上 immersion，可以非单射）上的
`φ ∈ C_c^∞(N)` 构造一族光滑变分，而 IMS03 的 `Normal*Variation` 用 ambient flow（需要 embedding 才能
把 `φ ν` 延拓成 ambient 场）。这里不经 ambient 微分同胚，直接取 geodesic 变分：

* `F` 在开集 `V ⊆ ℝ × ℂ`（`V ⊆ ℝ × N`，`{0} × N ⊆ V`）上光滑（`FiniteMetric.contMDiffOn_expMap`）；
* `F(0, ·) = U`，`∂_t F(0, z) = φ(z) ν(z)`（`mfderiv_expMap_at_zero`）；
* `t ↦ F(t, z)` 是 geodesic，所以 `t = 0` 处加速度为 0（`exp_radial_d2_zero`）——二阶变分里的加速度项整项消失；
* `φ z = 0` 时 `F(t, z) = U z`（`expMap_zero`）。

显式参数：`ν` 的光滑单位法向性质只用到光滑性（`hν`），单位 / 正交性在二阶公式里才用。
-/

set_option autoImplicit false
noncomputable section

open Bundle Filter Manifold Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Geometry

open Riemannian.CovariantDerivativeAlong

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

omit [FiniteDimensional ℝ E] in
private theorem contMDiff_tangent_smul_WS :
    ContMDiff (𝓘(ℝ, ℝ).prod (𝓘(ℝ, E).prod 𝓘(ℝ, E))) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun z : ℝ × TangentBundle 𝓘(ℝ, E) M =>
        (⟨z.2.proj, z.1 • z.2.snd⟩ : TangentBundle 𝓘(ℝ, E) M)) := by
  intro z
  have hs : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓘(ℝ, E).prod 𝓘(ℝ, E))) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (Prod.snd : ℝ × TangentBundle 𝓘(ℝ, E) M → TangentBundle 𝓘(ℝ, E) M) z := contMDiffAt_snd
  obtain ⟨hb, hv⟩ := Bundle.contMDiffAt_totalSpace.mp hs
  apply Bundle.contMDiffAt_totalSpace.mpr
  refine ⟨hb, (contMDiffAt_fst.smul hv).congr_of_eventuallyEq ?_⟩
  let e := trivializationAt E (TangentSpace 𝓘(ℝ, E)) z.2.proj
  have he : ∀ᶠ y : ℝ × TangentBundle 𝓘(ℝ, E) M in 𝓝 z, y.2.proj ∈ e.baseSet :=
    hb.continuousAt (e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt E _ z.2.proj))
  filter_upwards [he] with y hy
  exact (e.linear ℝ hy).map_smul y.1 y.2.snd

/-- **parametrized 法向 geodesic 变分族.**  `ν` 是沿 `U` 的光滑截面（`hν` 已含 `U` 在 `N` 上光滑）、
`φ` 在 `N` 上光滑 ⇒ `F(t, z) = exp_{U z}(t φ(z) ν(z))` 在开集 `V ⊆ ℝ × N`（含 `{0} × N`）上光滑，
`F(0, ·) = U`，`∂_t F(0, z) = φ ν`，`t = 0` 处加速度为 0，`φ z = 0` 处 `F(t, z) = U z`。 -/
theorem exists_normalGeodesicFamily_WS [T2Space M] (hdim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (N : TopologicalSpace.Opens ℂ) (U : ℂ → M)
    (ν : ∀ q : N, TangentSpace 𝓘(ℝ, E) (U q))
    (hν : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, E).tangent) ∞
      (fun q : N => (⟨U q, ν q⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (φ : N → ℝ) (hφ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞ φ) :
    ∃ (F : ℝ × ℂ → M) (V : Set (ℝ × ℂ)), IsOpen V ∧ (∀ p ∈ V, p.2 ∈ N) ∧
      (∀ z ∈ N, ((0 : ℝ), z) ∈ V) ∧
      ContMDiffOn 𝓘(ℝ, ℝ × ℂ) 𝓘(ℝ, E) ∞ F V ∧ (∀ z ∈ N, F (0, z) = U z) ∧
      (∀ (z : ℂ) (hz : z ∈ N),
        (mfderiv 𝓘(ℝ, ℝ × ℂ) 𝓘(ℝ, E) F (0, z) (1, 0) : E) =
          φ ⟨z, hz⟩ • (ν ⟨z, hz⟩ : E)) ∧
      (∀ z ∈ N, covDerivAlong g (fun s : ℝ => F (s, z))
        (fun s => mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun r : ℝ => F (r, z)) s (1 : ℝ)) 0 = 0) ∧
      (∀ (z : ℂ) (hz : z ∈ N), φ ⟨z, hz⟩ = 0 → ∀ t : ℝ, (t, z) ∈ V ∧ F (t, z) = U z) := by
  classical
  have : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  let w : ∀ z : ℂ, TangentSpace 𝓘(ℝ, E) (U z) := fun z =>
    if h : z ∈ N then (φ ⟨z, h⟩ • ν ⟨z, h⟩ : TangentSpace 𝓘(ℝ, E) (U z)) else 0
  let F : ℝ × ℂ → M := fun p => Riemannian.Exponential.expMap g (U p.2) (p.1 • w p.2)
  let Ψ : ℝ × ℂ → TangentBundle 𝓘(ℝ, E) M := fun p => ⟨U p.2, p.1 • w p.2⟩
  let S : Set (ℝ × ℂ) := univ ×ˢ (N : Set ℂ)
  let V : Set (ℝ × ℂ) := S ∩ Ψ ⁻¹' g.expDomain
  have hS : IsOpen S := isOpen_univ.prod N.isOpen
  have hwN (z : ℂ) (hz : z ∈ N) : w z = φ ⟨z, hz⟩ • ν ⟨z, hz⟩ := by
    simp only [w, hz, ↓reduceDIte]
  -- smoothness of `z ↦ ⟨U z, w z⟩` on `N`
  have hwsub : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun q : N => (⟨U q, w q⟩ : TangentBundle 𝓘(ℝ, E) M)) := by
    have h := (contMDiff_tangent_smul_WS (E := E) (M := M)).comp (hφ.prodMk hν)
    refine h.congr ?_
    intro q
    simp only [Function.comp_apply, w, q.property, ↓reduceDIte]
  have hwon : ContMDiffOn 𝓘(ℝ, ℂ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun z : ℂ => (⟨U z, w z⟩ : TangentBundle 𝓘(ℝ, E) M)) (N : Set ℂ) := by
    intro z hz
    exact (contMDiffAt_subtype_iff (U := N)
      (f := fun z : ℂ => (⟨U z, w z⟩ : TangentBundle 𝓘(ℝ, E) M))
      |>.mp (hwsub.contMDiffAt (x := (⟨z, hz⟩ : N)))).contMDiffWithinAt
  have hΨ : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℂ)) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞ Ψ S := by
    have h := (contMDiff_tangent_smul_WS (E := E) (M := M)).comp_contMDiffOn
      (contMDiffOn_fst.prodMk (hwon.comp contMDiffOn_snd (fun p hp => (hp : p ∈ S).2)))
    exact h
  have hV : IsOpen V :=
    hΨ.continuousOn.isOpen_inter_preimage hS (g.isOpen_expDomain (r := ⊤) le_top)
  have hVN (p : ℝ × ℂ) (hp : p ∈ V) : p.2 ∈ N := hp.1.2
  have hFV (p : ℝ × ℂ) (hp : p ∈ V) : F p = g.expMap (Ψ p) :=
    (Bundle.ContMDiffRiemannianMetric.expMap_eq_smooth_expMap g (U p.2) (p.1 • w p.2) hp.2).symm
  have h0V (z : ℂ) (hz : z ∈ N) : ((0 : ℝ), z) ∈ V := by
    refine ⟨⟨mem_univ _, hz⟩, ?_⟩
    change (⟨U z, (0 : ℝ) • w z⟩ : TangentBundle 𝓘(ℝ, E) M) ∈ g.expDomain
    rw [zero_smul]
    exact g.zero_mem_expDomain (U z)
  have hexp : ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ g.expMap g.expDomain :=
    g.contMDiffOn_expMap (r := ⊤) le_top
  have hFsm : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, E) ∞ F V := by
    have h := hexp.comp (hΨ.mono inter_subset_left) (fun p hp => hp.2)
    exact h.congr (fun p hp => hFV p hp)
  have hFd (z : ℂ) (hz : z ∈ N) :
      MDifferentiableAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, E) F (0, z) :=
    ((hFsm (0, z) (h0V z hz)).contMDiffAt (hV.mem_nhds (h0V z hz))).mdifferentiableAt (by simp)
  have hvel (z : ℂ) (hz : z ∈ N) :
      (mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, E) F (0, z) (1, 0) : E) = (w z : E) := by
    have h := mfderiv_parameter_time (hFd z hz) 1
    rw [← h]
    have hzero : (show TangentSpace 𝓘(ℝ, E) (U z) from (0 : ℝ) • (w z : E)) ∈
        Riemannian.Exponential.expDomain g (U z) := by
      rw [zero_smul]
      exact Riemannian.Exponential.zero_mem_expDomain g (U z)
    have h1 := Riemannian.Exponential.mfderiv_expMap_smul g (U z) (w z : E) 0 hzero
    have h2 := Riemannian.Exponential.mfderiv_expMap_at_zero g (U z)
    have key : ∀ x : E, x = 0 →
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun b : E =>
          (Riemannian.Exponential.expMap g (U z) (show TangentSpace 𝓘(ℝ, E) (U z) from b) : M))
            x) (w z : E) = (w z : E) := by
      intro x hx
      subst hx
      rw [h2]
      rfl
    exact h1.trans (key _ (zero_smul ℝ _))
  refine ⟨F, V, hV, hVN, h0V, ?_, ?_, ?_, ?_, ?_⟩
  · rwa [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hFsm
  · intro z _
    change Riemannian.Exponential.expMap g (U z) ((0 : ℝ) • w z) = U z
    rw [zero_smul]
    exact Riemannian.Exponential.expMap_zero g (U z)
  · intro z hz
    have h := hvel z hz
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at h
    rw [h, hwN z hz]
  · intro z _
    exact Riemannian.Exponential.exp_radial_d2_zero g (U z) (w z)
  · intro z hz h0 t
    have hw0 : w z = 0 := by rw [hwN z hz, h0, zero_smul]
    refine ⟨⟨⟨mem_univ _, hz⟩, ?_⟩, ?_⟩
    · change (⟨U z, t • w z⟩ : TangentBundle 𝓘(ℝ, E) M) ∈ g.expDomain
      rw [hw0, smul_zero]
      exact g.zero_mem_expDomain (U z)
    · change Riemannian.Exponential.expMap g (U z) (t • w z) = U z
      rw [hw0, smul_zero]
      exact Riemannian.Exponential.expMap_zero g (U z)

end DifferentialGeometry.Geometry
