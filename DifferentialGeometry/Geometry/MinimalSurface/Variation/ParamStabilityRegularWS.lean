import DifferentialGeometry.Geometry.MinimalSurface.Variation.ParamNormalSecondDensityWS
import DifferentialGeometry.Geometry.MinimalSurface.Variation.ParamNormalMorreyWS
import DifferentialGeometry.Geometry.Submanifold.NormalBundle.DiskWeingartenNorm
import DifferentialGeometry.Geometry.MinimalSurface.Curvature.DiskJacobiPotential
import DifferentialGeometry.Geometry.Measure.Area.InducedVolume
import DifferentialGeometry.Geometry.Metric.Coordinates.InnerExpansion

/-!
# S-W-STAB G2：Morrey attainer 在 regular part 上的 stability inequality

`ParamNormalSecondDensityWS` 的逐点公式 + 最小曲面性质（`hmean`）+ Gauss 型代数
（`normal_jacobi_coefficient_eq_scalar_gauss_of_zero_mean_curvature_complex`）给出
`d²/dt² dens(F_t)(z) = dens(U)(z) · (|∇φ|² − φ²(Ric(ν,ν) + |II|²))`；
再按 `NormalSecondIntegral` 的方式把 `∫_K` 换成 `∫_N ⋯ dμ_{gN}`，与 G1 的 `0 ≤ ∫_K ∂_t² dens` 合并。
-/

set_option autoImplicit false
noncomputable section

open Bundle Filter Manifold Set MeasureTheory DifferentialGeometry
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Topology
open DifferentialGeometry.Integral.Measure
open scoped ContDiff Manifold _root_.Topology BigOperators

namespace DifferentialGeometry.Geometry

open Riemannian Riemannian.CovariantDerivativeAlong

private local instance (N : TopologicalSpace.Opens ℂ) : MeasurableSpace N := borel N
private local instance (N : TopologicalSpace.Opens ℂ) : BorelSpace N := ⟨rfl⟩
private local instance (N : TopologicalSpace.Opens ℂ) : LocallyCompactSpace N :=
  N.isOpen.locallyCompactSpace
private local instance (N : TopologicalSpace.Opens ℂ) : SigmaCompactSpace N := by infer_instance

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

/-- 逐点 Jacobi 形：`d²/dt² dens(F_t)(z) = dens(U)(z) · (|∇φ|² − φ²(C + S))`，
`C = Σ_i ⟨R(ν,P_i)P_i,ν⟩`（= `Ric(ν,ν)`），`S = |II|²`。 -/
theorem deriv2_areaDensity_eq_jacobi_WS (hdim : Module.finrank ℝ E = 3)
    (N : TopologicalSpace.Opens ℂ) (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (U : ℂ → M)
    (hU : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (fun q : N => U q))
    (hi : ∀ q : N, Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun p : N => U p) q))
    (ν : ∀ q : N, TangentSpace 𝓘(ℝ, E) (U q))
    (hν : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, E).tangent) ∞
      (fun q : N => (⟨U q, ν q⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hunit : ∀ q : N, g.inner (U q) (ν q) (ν q) = 1)
    (hnormal : ∀ (q : N) (v : ℂ), g.inner (U q) (ν q)
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun p : N => U p) q v) = 0)
    (φ : N → ℝ) (hφ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞ φ)
    (Wsec : ∀ q : ℂ, TangentSpace 𝓘(ℝ, E) (U q))
    (hW : ContMDiffOn 𝓘(ℝ, ℂ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun q : ℂ => (⟨U q, Wsec q⟩ : TangentBundle 𝓘(ℝ, E) M)) (N : Set ℂ))
    (hW_eq : ∀ q : N, (Wsec q : E) = φ q • (ν q : E))
    {F : ℝ × ℂ → M} {V : Set (ℝ × ℂ)} (hV : IsOpen V) (hVN : ∀ p ∈ V, p.2 ∈ N)
    (hF : ContMDiffOn 𝓘(ℝ, ℝ × ℂ) 𝓘(ℝ, E) ∞ F V)
    (h0V : ∀ z ∈ N, ((0 : ℝ), z) ∈ V) (hF0 : ∀ z ∈ N, F (0, z) = U z)
    (hvel : ∀ (z : ℂ) (hz : z ∈ N),
      (mfderiv 𝓘(ℝ, ℝ × ℂ) 𝓘(ℝ, E) F (0, z) (1, 0) : E) = φ ⟨z, hz⟩ • (ν ⟨z, hz⟩ : E))
    (hacc : ∀ z ∈ N, covDerivAlong g (fun s : ℝ => F (s, z))
      (fun s => mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun r : ℝ => F (r, z)) s (1 : ℝ)) 0 = 0)
    (z : N) (b : Module.Basis (Fin 2) ℝ (TangentSpace 𝓘(ℝ, ℂ) z))
    (hb : ∀ i j, (g.pullback (fun q : N => U q) hU hi).inner z (b i) (b j) =
      if i = j then 1 else 0)
    (hmean : ∑ i : Fin 2, secondFundamentalFormAmbientAt (g.pullback (fun q : N => U q) hU hi)
      g (fun q : N => U q) z (b i) (b i) = 0) :
    let gN := g.pullback (fun q : N => U q) hU hi
    let II := secondFundamentalFormAmbientAt gN g (fun q : N => U q) z
    deriv (deriv (fun t => riemannianAreaDensity g (fun y => F (t, y)) z)) 0 =
      riemannianAreaDensity g U z *
        (gN.inner z (gradFun gN φ z) (gradFun gN φ z) -
          φ z ^ 2 *
            ((∑ i : Fin 2, g.inner (U z) ((riemannOp (LeviCivita g) (U z)) (ν z)
                (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z (b i)) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z (b i)))
                (ν z)) +
              ∑ i : Fin 2, ∑ j : Fin 2,
                g.inner (U z) (II (b i) (b j)) (II (b i) (b j)))) := by
  classical
  intro gN II
  have hpt := (hasDerivAt_deriv_areaDensity_param_normal_WS N g U hU hi ν hnormal φ Wsec hW_eq
    hV hVN hF h0V hF0 hvel hacc z b hb).deriv
  rw [hpt]
  let B : E →L[ℝ] E →L[ℝ] ℝ := g.inner (U z)
  let Q : ℂ →L[ℝ] ℂ →L[ℝ] E := secondFundamentalFormAmbientAt gN g (fun q : N => U q) z
  let n : E := ν z
  let ℓ : E →L[ℝ] ℝ := B n
  let P : ℂ →L[ℝ] E := mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun q : N => U q) z
  have henergy : (∑ i : Fin 2, B (sourceSectionCovariantDerivative g U Wsec z (b i))
        (sourceSectionCovariantDerivative g U Wsec z (b i))) =
      gN.inner z (gradFun gN φ z) (gradFun gN φ z) +
        φ z ^ 2 * ∑ i : Fin 2, ∑ j : Fin 2, B (Q (b i) (b j)) (Q (b i) (b j)) :=
    normalVariation_covariantDerivative_norm_sq_complex N g hdim U hU hi
      ν hν hunit hnormal φ hφ Wsec hW hW_eq z b hb
  have hframe : ∀ i j : Option (Fin 2),
      B ((fun i : Option (Fin 2) => i.elim n (fun j => P (b j))) i)
        ((fun i : Option (Fin 2) => i.elim n (fun j => P (b j))) j) =
          if i = j then 1 else 0 := by
    intro i j
    cases i with
    | none =>
      cases j with
      | none => exact hunit z
      | some j => exact hnormal z (b j)
    | some i =>
      cases j with
      | none => exact (g.symm (U z) _ _).trans (hnormal z (b i))
      | some j =>
        have h' : B (P (b i)) (P (b j)) = if i = j then 1 else 0 := hb i j
        simpa only [Option.elim_some, Option.some.injEq] using h'
  have hcard : Fintype.card (Option (Fin 2)) =
      Module.finrank ℝ (TangentSpace 𝓘(ℝ, E) (U z)) := by
    change Fintype.card (Option (Fin 2)) = Module.finrank ℝ E
    rw [hdim]
    simp
  have hUsm : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (fun q : N => U q) := hU
  have hIInormal (a c w : ℂ) : B (Q a c) (P w) = 0 :=
    secondFundamentalFormAmbientAt_inner_mfderiv_eq_zero_of_inner_map
      hUsm (fun _ _ _ => rfl) z a c w
  have hIInorm (a c : ℂ) : B (Q a c) (Q a c) = (ℓ (Q a c)) ^ 2 := by
    have h' : B (Q a c) (Q a c) = ∑ i : Option (Fin 2),
        (B ((fun i : Option (Fin 2) => i.elim n (fun j => P (b j))) i) (Q a c)) ^ 2 :=
      inner_self_eq_sum_sq g (U z) hcard _ hframe (Q a c)
    change B (Q a c) (Q a c) = (ℓ (Q a c)) ^ 2
    rw [h']
    simp only [Fintype.sum_option, Option.elim_none, Option.elim_some]
    have hz (i : Fin 2) : B (P (b i)) (Q a c) = 0 :=
      (g.symm (U z) _ _).trans (hIInormal a c (b i))
    simp only [ℓ, hz, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero, add_zero]
  have hsym : Q (b 1) (b 0) = Q (b 0) (b 1) :=
    secondFundamentalFormAmbientAt_symmetric gN g (hU.contMDiffAt.of_le (by simp)) (b 1) (b 0)
  have hshape : (ℓ (Q (b 0) (b 0)) - ℓ (Q (b 1) (b 1))) ^ 2 +
      4 * (ℓ (Q (b 0) (b 1))) ^ 2 =
        2 * (∑ i : Fin 2, ∑ j : Fin 2, B (Q (b i) (b j)) (Q (b i) (b j))) -
          (∑ i : Fin 2, ℓ (Q (b i) (b i))) ^ 2 := by
    let β : Fin 2 → ℂ := fun i => b i
    have hsymModel : Q (β 1) (β 0) = Q (β 0) (β 1) := hsym
    change (ℓ (Q (β 0) (β 0)) - ℓ (Q (β 1) (β 1))) ^ 2 +
        4 * (ℓ (Q (β 0) (β 1))) ^ 2 =
          2 * (∑ i : Fin 2, ∑ j : Fin 2, B (Q (β i) (β j)) (Q (β i) (β j))) -
            (∑ i : Fin 2, ℓ (Q (β i) (β i))) ^ 2
    simp_rw [hIInorm]
    simp only [Fin.sum_univ_two, hsymModel]
    ring
  have hnormalMean : (∑ i : Fin 2, ℓ (Q (b i) (b i))) = 0 := by
    calc (∑ i : Fin 2, ℓ (Q (b i) (b i))) = ℓ (∑ i : Fin 2, Q (b i) (b i)) :=
          (map_sum ℓ (fun i : Fin 2 => Q (b i) (b i)) Finset.univ).symm
      _ = ℓ 0 := congrArg (fun v : E => ℓ v) hmean
      _ = 0 := map_zero ℓ
  change riemannianAreaDensity g U z *
      ((∑ i : Fin 2, B (sourceSectionCovariantDerivative g U Wsec z (b i))
          (sourceSectionCovariantDerivative g U Wsec z (b i))) -
        φ z ^ 2 * (∑ i : Fin 2, B ((riemannOp (LeviCivita g) (U z)) (ν z)
          (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z (b i)) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z (b i))) (ν z)) -
        φ z ^ 2 * ((ℓ (Q (b 0) (b 0)) - ℓ (Q (b 1) (b 1))) ^ 2 +
          4 * (ℓ (Q (b 0) (b 1))) ^ 2)) = _
  rw [henergy, hshape, hnormalMean]
  change _ = riemannianAreaDensity g U z *
    (gN.inner z (gradFun gN φ z) (gradFun gN φ z) -
      φ z ^ 2 * ((∑ i : Fin 2, B ((riemannOp (LeviCivita g) (U z)) (ν z)
          (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z (b i)) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z (b i))) (ν z)) +
        ∑ i : Fin 2, ∑ j : Fin 2, B (Q (b i) (b j)) (Q (b i) (b j))))
  ring

omit [FiniteDimensional ℝ E] [T2Space M] in
private theorem contMDiff_tangent_smul_WS2 :
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

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- 任何满足 `Wsec q = φ q • ν q`（`q ∈ N`）的截面 `Wsec` 在 `N` 上光滑（作为 `TM` 值映射）。 -/
theorem contMDiffOn_normalSection_WS (N : TopologicalSpace.Opens ℂ) (U : ℂ → M)
    (ν : ∀ q : N, TangentSpace 𝓘(ℝ, E) (U q))
    (hν : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, E).tangent) ∞
      (fun q : N => (⟨U q, ν q⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (φ : N → ℝ) (hφ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞ φ)
    (Wsec : ∀ q : ℂ, TangentSpace 𝓘(ℝ, E) (U q))
    (hW_eq : ∀ q : N, (Wsec q : E) = φ q • (ν q : E)) :
    ContMDiffOn 𝓘(ℝ, ℂ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun q : ℂ => (⟨U q, Wsec q⟩ : TangentBundle 𝓘(ℝ, E) M)) (N : Set ℂ) := by
  have hsub : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun q : N => (⟨U q, Wsec q⟩ : TangentBundle 𝓘(ℝ, E) M)) := by
    have h := (contMDiff_tangent_smul_WS2 (E := E) (M := M)).comp (hφ.prodMk hν)
    refine h.congr ?_
    intro q
    simp only [Function.comp_apply]
    exact congrArg (fun v : E => (⟨U q, v⟩ : TangentBundle 𝓘(ℝ, E) M)) (hW_eq q)
  intro z hz
  exact (contMDiffAt_subtype_iff (U := N)
    (f := fun q : ℂ => (⟨U q, Wsec q⟩ : TangentBundle 𝓘(ℝ, E) M))
    |>.mp (hsub.contMDiffAt (x := (⟨z, hz⟩ : N)))).contMDiffWithinAt

omit [FiniteDimensional ℝ E] in
private theorem gradFun_eq_zero_of_notMem_tsupport_WS {N : TopologicalSpace.Opens ℂ}
    (gN : SmoothRiemannianMetric 𝓘(ℝ, ℂ) N) {φ : N → ℝ} {q : N} (hq : q ∉ tsupport φ) :
    gradFun gN φ q = 0 := by
  have hev : φ =ᶠ[𝓝 q] fun _ => (0 : ℝ) := notMem_tsupport_iff_eventuallyEq.mp hq
  have hd : mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) φ q = 0 := by
    rw [Filter.EventuallyEq.mfderiv_eq (I := 𝓘(ℝ, ℂ)) (I' := 𝓘(ℝ, ℝ)) hev]
    simp
  rw [gradFun_def, hd]
  exact map_zero _

/-- **G2 `stability_inequality_regular_WS`.**  Morrey attainer `u` 在光滑竞争者类里面积极小，
`N ⊆` 开单位盘是 `U` 的 regular part（immersion），`ν` 光滑单位法向（显式参数），`hmean` 是 `N` 上
平均曲率为 0（显式参数；Morrey disk 由 harmonic + conformal 得到）。则对所有 `φ ∈ C_c^∞(N)`：
`∫_N (|∇φ|² − φ²(Ric(ν,ν) + |II|²)) dμ_{gN} ≥ 0`
（`Ric(ν,ν) = Σ_i⟨R(ν,P_i)P_i,ν⟩`，`P_i = dU(b_i)`）。 -/
theorem stability_inequality_regular_WS (hdim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (W : Set M) (γ : freeLoop M)
    {u : C(closedDisk, M)} {U : ℂ → M} (hExt : SmoothDiskExtension (E := E) u U)
    (hW : Set.range u ⊆ W) (htr : DiskWeakJordanTrace γ u)
    (hmin : ∀ v : C(closedDisk, M), DiskSmoothUpToBoundary (E := E) v →
      DiskWeakJordanTrace γ v → Set.range v ⊆ W → riemannianDiskArea g u ≤ riemannianDiskArea g v)
    (N : TopologicalSpace.Opens ℂ) (hNball : (N : Set ℂ) ⊆ Metric.ball 0 1)
    (hUN : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (fun q : N => U q))
    (hiN : ∀ q : N, Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun p : N => U p) q))
    (hint : ∀ z ∈ N, U z ∈ interior W)
    (ν : ∀ q : N, TangentSpace 𝓘(ℝ, E) (U q))
    (hν : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, E).tangent) ∞
      (fun q : N => (⟨U q, ν q⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hunit : ∀ q : N, g.inner (U q) (ν q) (ν q) = 1)
    (hnormal : ∀ (q : N) (v : ℂ), g.inner (U q) (ν q)
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun p : N => U p) q v) = 0)
    (hmean : ∀ (q : N) (b : Module.Basis (Fin 2) ℝ (TangentSpace 𝓘(ℝ, ℂ) q)),
      (∀ i j, (g.pullback (fun p : N => U p) hUN hiN).inner q (b i) (b j) =
        if i = j then 1 else 0) →
      ∑ i : Fin 2, secondFundamentalFormAmbientAt (g.pullback (fun p : N => U p) hUN hiN)
        g (fun p : N => U p) q (b i) (b i) = 0)
    (φ : N → ℝ) (hφ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞ φ) (hφc : HasCompactSupport φ)
    (b : ∀ q : N, Module.Basis (Fin 2) ℝ (TangentSpace 𝓘(ℝ, ℂ) q))
    (hb : ∀ (q : N) (i j : Fin 2),
      (g.pullback (fun p : N => U p) hUN hiN).inner q (b q i) (b q j) = if i = j then 1 else 0) :
    let gN := g.pullback (fun p : N => U p) hUN hiN
    let μ := riemannianVolumeMeasure (I := 𝓘(ℝ, ℂ)) (M := N) gN
    let J : N → ℝ := fun q =>
      let II := secondFundamentalFormAmbientAt gN g (fun p : N => U p) q
      gN.inner q (gradFun gN φ q) (gradFun gN φ q) -
        φ q ^ 2 * ((∑ i : Fin 2, g.inner (U q) ((riemannOp (LeviCivita g) (U q)) (ν q)
            (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U q (b q i)) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U q (b q i)))
            (ν q)) +
          ∑ i : Fin 2, ∑ j : Fin 2, g.inner (U q) (II (b q i) (b q j)) (II (b q i) (b q j)))
    Integrable J μ ∧ 0 ≤ ∫ q : N, J q ∂μ := by
  classical
  intro gN μ J
  have hi : ∀ z ∈ N, Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z) := by
    intro z hz
    have h' := hiN ⟨z, hz⟩
    rwa [DifferentialGeometry.mfderiv_restrict_open (I := 𝓘(ℝ, ℂ)) (J := 𝓘(ℝ, E)) U N
      ⟨z, hz⟩] at h'
  obtain ⟨F, V, hV, hVN, h0V, hF, hF0, hvel, hacc, htriv⟩ :=
    exists_normalGeodesicFamily_WS hdim g N U ν hν φ hφ
  have hK : IsCompact (Subtype.val '' tsupport φ) := hφc.image continuous_subtype_val
  have hKN : (Subtype.val '' tsupport φ) ⊆ (N : Set ℂ) := by
    rintro _ ⟨q, _, rfl⟩
    exact q.property
  have hKnot (z : ℂ) (hz : z ∈ N) (hzK : z ∉ (Subtype.val '' tsupport φ)) :
      (⟨z, hz⟩ : N) ∉ tsupport φ := fun h => hzK ⟨⟨z, hz⟩, h, rfl⟩
  have htriv' : ∀ z ∈ N, z ∉ (Subtype.val '' tsupport φ) → ∀ t : ℝ,
      (t, z) ∈ V ∧ F (t, z) = U z := by
    intro z hz hzK t
    refine htriv z hz ?_ t
    by_contra hne
    exact hzK ⟨⟨z, hz⟩, subset_tsupport _ (Function.mem_support.mpr hne), rfl⟩
  obtain ⟨hI2, -, -, h2⟩ := area_variation_nonneg_of_family_WS g W γ hExt hW htr hmin N hNball
    hi hV h0V hF hF0 hK hKN (fun z hz => hint z (hKN hz)) htriv'
  let Wsec : ∀ q : ℂ, TangentSpace 𝓘(ℝ, E) (U q) := fun q =>
    if h : q ∈ N then (φ ⟨q, h⟩ • ν ⟨q, h⟩ : TangentSpace 𝓘(ℝ, E) (U q)) else 0
  have hW_eq : ∀ q : N, (Wsec q : E) = φ q • (ν q : E) := by
    intro q
    simp only [Wsec, q.property, ↓reduceDIte]
  have hWc := contMDiffOn_normalSection_WS N U ν hν φ hφ Wsec hW_eq
  let d₂ : ℂ → ℝ := fun z =>
    deriv (deriv (fun t => riemannianAreaDensity g (fun y => F (t, y)) z)) 0
  let J₀ : N → ℝ := fun q => riemannianAreaDensity g U q
  have hpoint (q : N) : d₂ q = J₀ q * J q :=
    deriv2_areaDensity_eq_jacobi_WS hdim N g U hUN hiN ν hν hunit hnormal φ hφ Wsec hWc hW_eq
      hV hVN hF h0V hF0 hvel hacc q (b q) (hb q) (hmean q (b q) (hb q))
  have hJzero (q : N) (hq : q ∉ tsupport φ) : J q = 0 := by
    have hφq : φ q = 0 := by
      by_contra hne
      exact hq (subset_tsupport _ (Function.mem_support.mpr hne))
    change gN.inner q (gradFun gN φ q) (gradFun gN φ q) - φ q ^ 2 * _ = 0
    rw [gradFun_eq_zero_of_notMem_tsupport_WS gN hq, hφq]
    simp
  have hd₂zero (z : ℂ) (hz : z ∈ N) (hzK : z ∉ (Subtype.val '' tsupport φ)) : d₂ z = 0 := by
    have h' := hpoint ⟨z, hz⟩
    rw [hJzero ⟨z, hz⟩ (hKnot z hz hzK), mul_zero] at h'
    exact h'
  have hd₂N : IntegrableOn d₂ (N : Set ℂ) :=
    hI2.of_forall_sdiff_eq_zero N.isOpen.measurableSet (fun z hz => hd₂zero z hz.1 hz.2)
  let μD := Measure.comap (Subtype.val : N → ℂ) (volume : Measure ℂ)
  have hval : MeasurableEmbedding (Subtype.val : N → ℂ) :=
    N.isOpen.isOpenEmbedding_subtypeVal.measurableEmbedding (mα := borel N)
  have hd₂int : Integrable (fun q : N => d₂ q) μD := by
    have hm := hval.integrable_map_iff (μ := μD) (g := d₂)
    rw [hval.map_comap, Subtype.range_coe] at hm
    exact hm.mp hd₂N
  have hUon : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U (N : Set ℂ) := by
    intro z hz
    exact (contMDiffAt_subtype_iff.mp
      (hUN.contMDiffAt (x := (⟨z, hz⟩ : N)))).contMDiffWithinAt
  have hJ₀c : Continuous J₀ :=
    (continuousOn_riemannianAreaDensity g N.isOpen (hUon.of_le (by simp))).domRestrict
  have hJ₀m : Measurable (fun q => ENNReal.ofReal (J₀ q)) :=
    ENNReal.measurable_ofReal.comp hJ₀c.measurable
  have hJ₀finite : ∀ᵐ q ∂μD, ENNReal.ofReal (J₀ q) < (⊤ : ENNReal) :=
    Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hJ₀real (q : N) : (ENNReal.ofReal (J₀ q)).toReal = J₀ q :=
    ENNReal.toReal_ofReal (riemannianAreaDensity_nonneg g U q)
  have hvol := riemannianVolumeMeasure_induced_complex_open N g U hUN hiN
  change μ = μD.withDensity (fun q => ENNReal.ofReal (J₀ q)) at hvol
  have hweighted : Integrable (fun q : N => J₀ q * J q) μD :=
    hd₂int.congr (Eventually.of_forall hpoint)
  have hJint : Integrable J μ := by
    rw [hvol]
    apply (integrable_withDensity_iff_integrable_smul' hJ₀m hJ₀finite).mpr
    simpa only [hJ₀real, smul_eq_mul] using hweighted
  have hsubtype : (∫ q : N, d₂ q ∂μD) = ∫ z in (N : Set ℂ), d₂ z := by
    have hmap := hval.integral_map (μ := μD) d₂
    rw [hval.map_comap, Subtype.range_coe] at hmap
    exact hmap.symm
  have hintegral : (∫ q : N, J q ∂μ) = ∫ z in Subtype.val '' tsupport φ, d₂ z := by
    calc
      (∫ q : N, J q ∂μ) = ∫ q : N, J₀ q * J q ∂μD := by
        rw [hvol, integral_withDensity_eq_integral_toReal_smul hJ₀m hJ₀finite]
        simp only [hJ₀real, smul_eq_mul]
      _ = ∫ q : N, d₂ q ∂μD := integral_congr_ae (Eventually.of_forall fun q => (hpoint q).symm)
      _ = ∫ z in (N : Set ℂ), d₂ z := hsubtype
      _ = ∫ z in Subtype.val '' tsupport φ, d₂ z :=
        setIntegral_eq_of_subset_of_forall_sdiff_eq_zero N.isOpen.measurableSet hKN
          (fun z hz => hd₂zero z hz.1 hz.2)
  exact ⟨hJint, hintegral ▸ h2⟩

end DifferentialGeometry.Geometry
