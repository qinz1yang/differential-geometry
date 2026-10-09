import DifferentialGeometry.Geometry.Collapse.SublevelCore.PointOutwardNormalFlow
import DifferentialGeometry.Geometry.Collapse.SublevelCore.DiskCoreFlow
import DifferentialGeometry.Geometry.Comparison.Soul.NormalBundleRiemannian
import DifferentialGeometry.Topology.VectorBundle.DiscCoreTransport

/-!
# The normal-flow fibre radius of LC54's diffeomorphism (LC45 / LC55 radius data)

For LC54's actual normal-flow diffeomorphism `e : νS ≃ M` (`e = normalFlowMap … ϕ ℓ`), the
fibre radius `u x = ‖(e.symm x).2‖` (fibre norm = `g`, `NormalBundleRiemannian`) is continuous,
has compact sublevels, is smooth off the soul, and is translated at unit speed by the flow `ϕ` of
the field `V` beyond `ℓ`, so `du(V) = 1` on `{u > ℓ}`. These are exactly the `u`-hypotheses of the
LC55 kernel `point_distance_core_isotopy`.

The generic part is stated for any smooth Riemannian vector bundle over a manifold and any
diffeomorphism of its total space: a flow satisfying the ray identity
`e (q, t v) = ϕ (t - ℓ) (e (q, ℓ v))` (`‖v‖ = 1`, `t > ℓ`) translates the radius,
`discCoreRadius_flow_eq_add`, and its generator has `du(W) = 1` beyond `ℓ`,
`mvfderiv_discCoreRadius_eq_one_of_ray`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Topology.VectorBundle

section Generic

variable {EB F : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {Vb : B → Type*} [TopologicalSpace (TotalSpace F Vb)]
  [∀ b, NormedAddCommGroup (Vb b)] [∀ b, InnerProductSpace ℝ (Vb b)]
  [FiberBundle F Vb] [VectorBundle ℝ F Vb]
  {EN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  {HN : Type*} [TopologicalSpace HN] {IN : ModelWithCorners ℝ EN HN}
  {N : Type*} [TopologicalSpace N] [ChartedSpace HN N]

omit [VectorBundle ℝ F Vb] in
/-- **The ray identity translates the fibre radius.** If a flow `ϕ` satisfies
`e (q, t v) = ϕ (t - ℓ) (e (q, ℓ v))` for unit `v` and `t > ℓ ≥ 0`, then beyond `ℓ` the transported
fibre radius increases at unit speed along `ϕ`. -/
theorem discCoreRadius_flow_eq_add
    (e : Diffeomorph (IB.prod 𝓘(ℝ, F)) IN (TotalSpace F Vb) N ∞) {ϕ : Flow ℝ N} {ℓ : ℝ}
    (hℓ : 0 ≤ ℓ)
    (hray : ∀ (q : B) (v : Vb q), ‖v‖ = 1 → ∀ t, ℓ < t →
      e ⟨q, t • v⟩ = ϕ (t - ℓ) (e ⟨q, ℓ • v⟩))
    {x : N} (hx : ℓ < ‖(e.symm x).2‖) {t : ℝ} (ht : ℓ < ‖(e.symm x).2‖ + t) :
    ‖(e.symm (ϕ t x)).2‖ = ‖(e.symm x).2‖ + t := by
  rcases hz : e.symm x with ⟨q, w⟩
  have hxe : x = e ⟨q, w⟩ := by rw [← hz, e.apply_symm_apply]
  rw [hz] at hx ht
  change ℓ < ‖w‖ at hx
  change ℓ < ‖w‖ + t at ht
  change _ = ‖w‖ + t
  set r : ℝ := ‖w‖ with hr
  have hr0 : 0 < r := hℓ.trans_lt hx
  set v : Vb q := r⁻¹ • w with hvdef
  have hv : ‖v‖ = 1 := by
    rw [hvdef, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hr0, ← hr,
      inv_mul_cancel₀ hr0.ne']
  have hwv : w = r • v := by
    rw [hvdef, smul_smul, mul_inv_cancel₀ hr0.ne', one_smul]
  have key : ϕ t x = e ⟨q, (r + t) • v⟩ := by
    rw [hray q v hv (r + t) ht, hxe, hwv, hray q v hv r hx, ← Flow.map_add]
    congr 1
    ring
  rw [key, e.symm_apply_apply]
  change ‖(r + t) • v‖ = r + t
  rw [norm_smul, hv, mul_one, Real.norm_eq_abs, abs_of_pos (hℓ.trans_lt ht)]

variable [IsContMDiffRiemannianBundle IB ∞ F Vb]

/-- The transported fibre radius is continuous. -/
theorem continuous_discCoreRadius_of_isContMDiffRiemannianBundle
    (e : Diffeomorph (IB.prod 𝓘(ℝ, F)) IN (TotalSpace F Vb) N ∞) :
    Continuous (fun x : N => ‖(e.symm x).2‖) := by
  have h := (contMDiff_fiberRadiusSquared.comp e.symm.contMDiff).continuous.sqrt
  simpa only [Function.comp_def, fiberRadiusSquared, ← norm_eq_sqrt_real_inner] using h

/-- **`du(W) = 1` beyond `ℓ` (LC45 flow clause, generic).** For a flow `ϕ` with the ray identity
and generator `W`, the transported fibre radius `u` has `du(W) = 1` on `{u > ℓ}`. -/
theorem mvfderiv_discCoreRadius_eq_one_of_ray
    (e : Diffeomorph (IB.prod 𝓘(ℝ, F)) IN (TotalSpace F Vb) N ∞) {ϕ : Flow ℝ N} {ℓ : ℝ}
    (hℓ : 0 ≤ ℓ)
    (hray : ∀ (q : B) (v : Vb q), ‖v‖ = 1 → ∀ t, ℓ < t →
      e ⟨q, t • v⟩ = ϕ (t - ℓ) (e ⟨q, ℓ • v⟩))
    (W : (x : N) → TangentSpace IN x)
    (hW : ∀ x, HasMFDerivAt 𝓘(ℝ, ℝ) IN (fun t => ϕ t x) 0 ((1 : ℝ →L[ℝ] ℝ).smulRight (W x)))
    {x : N} (hx : ℓ < ‖(e.symm x).2‖) :
    mvfderiv (I := IN) (fun y : N => ‖(e.symm y).2‖) x (W x) = 1 := by
  have hcont := continuous_discCoreRadius_of_isContMDiffRiemannianBundle e
  have hopen : IsOpen {y : N | 0 < ‖(e.symm y).2‖} := isOpen_lt continuous_const hcont
  have hxpos : 0 < ‖(e.symm x).2‖ := hℓ.trans_lt hx
  have hsub : {y : N | 0 < ‖(e.symm y).2‖} ⊆ {y : N | (e.symm y).2 ≠ 0} :=
    fun y hy => norm_pos_iff.mp hy
  have hdiff : MDifferentiableAt IN 𝓘(ℝ, ℝ) (fun y : N => ‖(e.symm y).2‖) x :=
    (((contMDiffOn_discCoreRadius_off_zero e).mono hsub).contMDiffAt
      (hopen.mem_nhds hxpos)).mdifferentiableAt (by norm_num)
  refine mvfderiv_eq_one_of_translating hdiff (Flow.map_zero_apply ϕ x) (hW x) ?_
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), ℓ - ‖(e.symm x).2‖ < t := eventually_gt_nhds (by linarith)
  filter_upwards [hev] with t ht
  exact discCoreRadius_flow_eq_add e hℓ hray hx (by linarith)

end Generic

open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Geometry.Topology
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [ConnectedSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)]

omit [I.Boundaryless] [IsManifold I ∞ M] [SigmaCompactSpace M] [ConnectedSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)] in
/-- The total space of the soul's normal bundle has the dimension of `M`: the model
`(Fin d → ℝ) × (Fin (n - d) → ℝ)` has rank `(n - 1) + 1`. This is the dimension input of the
disc-core diffeomorphisms (`unitDiscCoreDiffeomorph`). -/
theorem normalBundle_totalSpace_finrank (S : Set M) :
    Module.finrank ℝ ((Fin (maxSliceDim I S) → ℝ) ×
      (Fin (Module.finrank ℝ E - maxSliceDim I S) → ℝ)) = (Module.finrank ℝ E - 1) + 1 := by
  rw [Module.finrank_prod, Module.finrank_fin_fun, Module.finrank_fin_fun]
  have h1 := maxSliceDim_le (I := I) S
  have h2 := Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E))
  omega

/-- **Radius data of LC54's normal-flow diffeomorphism.** For the actual normal-flow map
`e = normalFlowMap … ϕ ℓ` of a field `V` with flow `ϕ`, the fibre radius `u x = ‖(e.symm x).2‖`
is continuous, has compact sublevels, is smooth off the soul, and has `du(V) = 1` on `{u > ℓ}`. -/
theorem normalFlow_radius_core_data (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) {S : Set M} (hconv : IsTotallyConvex g S)
    (hB : relBoundary I S = ∅) (hScomp : IsCompact S) (V : Cₛ^∞⟮I; E, TangentSpace I⟯)
    (ϕ : Flow ℝ M) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (hIntegral : ∀ q, IsMIntegralCurve (fun t => ϕ t q) V) :
    let hS := isEmbeddedSlice_of_relBoundary_eq_empty hEnorm hconv hB
    let _ := embeddedSliceChartedSpace hS
    let a := normalBundlePrebundle g hEnorm hconv hB
    let _ := a.totalSpaceTopology
    let _ := a.toFiberBundle
    let _ := a.toVectorBundle
    ∀ e : TotalSpace (Fin (Module.finrank ℝ E - maxSliceDim I S) → ℝ)
        (normalBundleFiber g S) ≃ₘ⟮
          (𝓘(ℝ, Fin (maxSliceDim I S) → ℝ)).prod
            𝓘(ℝ, Fin (Module.finrank ℝ E - maxSliceDim I S) → ℝ), I⟯ M,
      (∀ z, e z = normalFlowMap (I := I) g hEnorm S ϕ ℓ z) →
      Continuous (fun x => ‖(e.symm x).2‖) ∧
      (∀ T, IsCompact {x | ‖(e.symm x).2‖ ≤ T}) ∧
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun x => ‖(e.symm x).2‖) {x | 0 < ‖(e.symm x).2‖} ∧
      ∀ x, ℓ < ‖(e.symm x).2‖ → mvfderiv (I := I) (fun y => ‖(e.symm y).2‖) x (V x) = 1 := by
  intro hS _ a _ _ _ e he
  let _ := embeddedSlice_isManifold hS
  let _ := normalBundle_isContMDiff g hEnorm hconv hB
  let _ := normalBundle_isContMDiffRiemannianBundle g hEnorm hconv hB
  have : CompactSpace S := isCompact_iff_compactSpace.mp hScomp
  have hray : ∀ (q : S) (v : normalBundleFiber g S q), ‖v‖ = 1 → ∀ t, ℓ < t →
      e ⟨q, t • v⟩ = ϕ (t - ℓ) (e ⟨q, ℓ • v⟩) := by
    intro q v hv t ht
    have hg : g.inner q.1 v.1 v.1 = 1 := by
      rw [← normalBundleFiber_inner_eq hEnorm q v v, real_inner_self_eq_norm_sq, hv, one_pow]
    rw [he, he]
    exact normalFlowMap_ray g hEnorm S ϕ hℓ ht q v hg
  have hsub : {x : M | 0 < ‖(e.symm x).2‖} ⊆ {x : M | (e.symm x).2 ≠ 0} :=
    fun x hx => norm_pos_iff.mp hx
  refine ⟨continuous_discCoreRadius_of_isContMDiffRiemannianBundle e,
    isCompact_discCore e, (contMDiffOn_discCoreRadius_off_zero e).mono hsub, ?_⟩
  intro x hx
  refine mvfderiv_discCoreRadius_eq_one_of_ray e hℓ hray (fun y => V y) (fun y => ?_) hx
  have h := hIntegral y 0
  have hV : (V (ϕ 0 y) : E) = V y := by rw [Flow.map_zero_apply]
  rw [hV] at h
  exact h

/-- **LC54 with its radius data, unbundled.** One PC soul `S`, LC54's field `V`, flow `ϕ`, radius
`ℓ`, margin `A₂`, and a function `u : M → ℝ` (the fibre radius of the actual normal-flow
diffeomorphism `e`) that is continuous, has compact sublevels, vanishes on `S`, is smooth off the
soul, and has `du(V) = 1` on `{u > ℓ}`; `e` is retained with `u = ‖(e.symm ·).2‖`. -/
theorem exists_point_outward_normalFlow_radius [NoncompactSpace M]
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hsec : ∀ x : M, metricRm04At (I := I) g x ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M)) (p : M) :
    ∃ (S : Set M) (hconv : IsTotallyConvex g S) (hB : relBoundary I S = ∅),
      S.Nonempty ∧ IsCompact S ∧
      ∃ V : Cₛ^∞⟮I; E, TangentSpace I⟯, ∃ ϕ : Flow ℝ M, ∃ ℓ : ℝ, 0 < ℓ ∧ ∃ A₂ : ℝ, 0 < A₂ ∧
        (∀ q, g.inner q (V q) (V q) ≤ 4) ∧
        ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun z : ℝ × M => ϕ z.1 z.2) ∧
        (∀ q, IsMIntegralCurve (fun t => ϕ t q) V) ∧
        (∀ q, A₂ ≤ dist p q → ∀ w ∈ inwardMinimizingDirections (I := I) g hEnorm p q,
          g.inner q (V q) w ≤ -(1 / 4)) ∧
        ∃ u : M → ℝ, Continuous u ∧ (∀ T, IsCompact {x | u x ≤ T}) ∧ (∀ x, 0 ≤ u x) ∧
          (∀ q ∈ S, u q = 0) ∧ ContMDiffOn I 𝓘(ℝ, ℝ) ∞ u {x | 0 < u x} ∧
          (∀ x, ℓ < u x → mvfderiv (I := I) u x (V x) = 1) ∧
          let hS := isEmbeddedSlice_of_relBoundary_eq_empty hEnorm hconv hB
          let _ := embeddedSliceChartedSpace hS
          let a := normalBundlePrebundle g hEnorm hconv hB
          let _ := a.totalSpaceTopology
          let _ := a.toFiberBundle
          let _ := a.toVectorBundle
          ∃ e : TotalSpace (Fin (Module.finrank ℝ E - maxSliceDim I S) → ℝ)
              (normalBundleFiber g S) ≃ₘ⟮
                (𝓘(ℝ, Fin (maxSliceDim I S) → ℝ)).prod
                  𝓘(ℝ, Fin (Module.finrank ℝ E - maxSliceDim I S) → ℝ), I⟯ M,
            (∀ z, e z = normalFlowMap (I := I) g hEnorm S ϕ ℓ z) ∧
            (∀ q : S, e ⟨q, 0⟩ = q.1) ∧ ∀ x, u x = ‖(e.symm x).2‖ := by
  obtain ⟨S, hconv, hB, hSne, hScomp, V, ϕ, ℓ, hℓ, A₂, hA₂, hVB, hϕ, hIntegral, hVdir, hdata⟩ :=
    exists_point_outward_normalFlow_data g hEnorm hsec p
  refine ⟨S, hconv, hB, hSne, hScomp, V, ϕ, ℓ, hℓ, A₂, hA₂, hVB, hϕ, hIntegral, hVdir, ?_⟩
  let hS := isEmbeddedSlice_of_relBoundary_eq_empty hEnorm hconv hB
  let _ := embeddedSliceChartedSpace hS
  let a := normalBundlePrebundle g hEnorm hconv hB
  let _ := a.totalSpaceTopology
  let _ := a.toFiberBundle
  let _ := a.toVectorBundle
  obtain ⟨e, he, hezero⟩ := hdata
  obtain ⟨hcont, hcpt, hsmooth, hdu⟩ :=
    normalFlow_radius_core_data g hEnorm hconv hB hScomp V ϕ hℓ.le hIntegral e he
  refine ⟨fun x => ‖(e.symm x).2‖, hcont, hcpt, fun x => norm_nonneg _, ?_, hsmooth, hdu, ?_⟩
  · intro q hq
    change ‖(e.symm (⟨q, hq⟩ : S).1).2‖ = 0
    rw [← hezero ⟨q, hq⟩, e.symm_apply_apply]
    exact norm_zero
  · exact ⟨e, he, hezero, fun x => rfl⟩

end DifferentialGeometry.Geometry.Collapse
