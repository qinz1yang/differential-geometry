import DifferentialGeometry.Geometry.Collapse.SublevelCore.PointDistanceCore
import DifferentialGeometry.Geometry.Collapse.SublevelCore.PointNormalFlowRadius

/-!
# LC55 binding at the normalized scale: the smoothed core is a disc core of `νS`

Master207A, A:22905 (LC55), option (b): the selected radial function `ζ` with its LC30/LC55
clauses (`|ζ - d_p| < 1/80`, `Lip(ζ - d_p) ≤ 1/64`, smooth near the collar) and the collar
bounds on the field are the row's inputs at the normalized scale; the quantifier over the scale
`R ≥ R_*` stays with the caller.

* `sublevel_eq_discCore_trans_symm` (generic): if an ambient diffeomorphism `H` carries `D` onto
  the sublevel `{u ≤ ρ}` of `u = c ‖(e.symm ·).2‖`, then `D` is the radius-`ρ/c` disc core of the
  diffeomorphism `e.trans H.symm`.
* `point_distance_core_isotopy_discCore` (generic in the bundle): the LC55 kernel
  `point_distance_core_isotopy` for `u = c ‖(e.symm ·).2‖` (any smooth Riemannian bundle over a
  compact base), with the conclusion `D = {x | ‖(e'.symm x).2‖ ≤ ρ/c}` for `e' = e.trans H₁⁻¹`, so
  `D ≅ D(E)` by X84's `unitDiscCoreDiffeomorph e'`.
* `point_distance_core_normalFlow_discCore` (binding): the same for LC54's actual normal-flow
  diffeomorphism `e = normalFlowMap … ϕ ℓ` of the soul's normal bundle, at any level
  `T₀ > ℓ` whose sublevel lies in `B(p, 1/2)`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped Topology ContDiff Manifold NNReal

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

omit [∀ b, InnerProductSpace ℝ (Vb b)] [VectorBundle ℝ F Vb] in
/-- **A diffeomorphic preimage of a radius sublevel is a disc core.** If `H '' D = {u ≤ ρ}` for
`u = c ‖(e.symm ·).2‖`, then `D = {x | ‖((e.trans H.symm).symm x).2‖ ≤ ρ / c}`. -/
theorem sublevel_eq_discCore_trans_symm
    (e : Diffeomorph (IB.prod 𝓘(ℝ, F)) IN (TotalSpace F Vb) N ∞)
    (Hm : Diffeomorph IN IN N N ∞) {c : ℝ} (hc : 0 < c) {u : N → ℝ}
    (hue : ∀ x, u x = c * ‖(e.symm x).2‖) {D : Set N} {ρ : ℝ}
    (hD : Hm '' D = {x | u x ≤ ρ}) :
    D = {x | ‖((e.trans Hm.symm).symm x).2‖ ≤ ρ / c} := by
  ext x
  have hsymm : (e.trans Hm.symm).symm x = e.symm (Hm x) := rfl
  change x ∈ D ↔ ‖((e.trans Hm.symm).symm x).2‖ ≤ ρ / c
  rw [hsymm, le_div_iff₀ hc, mul_comm, ← hue]
  constructor
  · intro hx
    have h : Hm x ∈ Hm '' D := mem_image_of_mem Hm hx
    rw [hD] at h
    exact h
  · intro hx
    have h : Hm x ∈ Hm '' D := by
      rw [hD]
      exact hx
    obtain ⟨y, hy, hyx⟩ := h
    rwa [← Hm.injective hyx]

end Generic

open DifferentialGeometry.Geometry.Riemannian

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

section Bundle

variable {EB F : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B] [CompactSpace B]
  {Vb : B → Type*} [TopologicalSpace (TotalSpace F Vb)]
  [∀ b, NormedAddCommGroup (Vb b)] [∀ b, InnerProductSpace ℝ (Vb b)]
  [FiberBundle F Vb] [VectorBundle ℝ F Vb] [IsContMDiffRiemannianBundle IB ∞ F Vb]

/-- **LC55 at the normalized scale with a disc-core radius** (generic in the bundle). For the
LC55 inputs (`ζ` with the errors `1/80`, `1/64`, smooth near the collar; the field `V` with the
collar bounds) and the fibre radius `u = c ‖(e.symm ·).2‖` of a diffeomorphism `e : E ≃ M` from
a smooth Riemannian bundle over a compact base, with `du(V) > 0` beyond `T₀ > 0` and
`{u ≤ T₀} ⊆ B(p, 1/2)`: the kernel's conclusions hold, and for every `ρ ∈ (T₀, T₁)` the core
`D = {ζ ≤ 1}` is the radius-`ρ/c` disc core of `e' = e.trans H₁⁻¹`. -/
theorem point_distance_core_isotopy_discCore
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g) (p : M)
    {ζ : M → ℝ} {ε : ℝ≥0} (hε : (ε : ℝ) ≤ 1 / 64)
    (hclose : ∀ x, |ζ x - dist p x| < 1 / 80)
    (hlip : LipschitzWith ε (fun x => ζ x - dist p x))
    {Wζ : Set M} (hWζ : IsOpen Wζ)
    (hcollarW : ∀ x, 3 / 4 < dist p x → dist p x < 5 / 4 → x ∈ Wζ)
    (hζW : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ ζ Wζ)
    (V : (x : M) → TangentSpace I x)
    (hVB : ∀ x, 3 / 4 < dist p x → dist p x < 5 / 4 → g.inner x (V x) (V x) ≤ 4)
    (hVdir : ∀ x, 3 / 4 < dist p x → dist p x < 5 / 4 →
      ∀ w ∈ inwardMinimizingDirections (I := I) g hEnorm p x, g.inner x (V x) w ≤ -(1 / 4))
    (e : Diffeomorph (IB.prod 𝓘(ℝ, F)) I (TotalSpace F Vb) M ∞) {c : ℝ} (hc : 0 < c)
    {u : M → ℝ} (hue : ∀ x, u x = c * ‖(e.symm x).2‖)
    {T₀ : ℝ} (hT₀pos : 0 < T₀) (hT₀ : {x | u x ≤ T₀} ⊆ Metric.ball p (1 / 2))
    {Wu : Set M} (hWu : IsOpen Wu) (hWuT : {x | T₀ ≤ u x} ⊆ Wu)
    (hVW : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (fun x => (⟨x, V x⟩ : TangentBundle I M)) Wu)
    (huV : ∀ x, T₀ ≤ u x → 0 < mvfderiv (I := I) u x (V x)) :
    IsCompact {x | ζ x ≤ 1} ∧
      Metric.closedBall p (1 / 2) ⊆ interior {x | ζ x ≤ 1} ∧
      {x | ζ x ≤ 1} ⊆ Metric.ball p 2 ∧
      frontier {x | ζ x ≤ 1} ⊆ {x | 79 / 80 < dist p x ∧ dist p x < 81 / 80} ∧
      (∀ x, 3 / 4 < dist p x → dist p x < 5 / 4 → 7 / 32 ≤ mvfderiv (I := I) ζ x (V x)) ∧
      ∃ T₁ : ℝ, T₀ < T₁ ∧ ∀ ρ ∈ Ioo T₀ T₁, ∃ Hs : ℝ → Diffeomorph I I M M ∞,
        Hs 0 = Diffeomorph.refl I M ∞ ∧
        ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Hs q.1 q.2) ∧
        ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => (Hs q.1).symm q.2) ∧
        (∃ S : Set M, IsCompact S ∧ S ⊆ u ⁻¹' Ioo T₀ T₁ ∧
          ∀ t x, x ∉ S → Hs t x = x ∧ (Hs t).symm x = x) ∧
        Hs 1 '' {x | ζ x ≤ 1} = {x | u x ≤ ρ} ∧
        ∃ e' : Diffeomorph (IB.prod 𝓘(ℝ, F)) I (TotalSpace F Vb) M ∞,
          (∀ z, e' z = (Hs 1).symm (e z)) ∧
          {x | ζ x ≤ 1} = {x | ‖(e'.symm x).2‖ ≤ ρ / c} := by
  have hrad := continuous_discCoreRadius_of_isContMDiffRiemannianBundle e
  have hu : Continuous u := (continuous_const.mul hrad).congr fun x => (hue x).symm
  have hucpt : ∀ T, IsCompact {x | u x ≤ T} := by
    intro T
    have hset : {x | u x ≤ T} = {x | ‖(e.symm x).2‖ ≤ T / c} := by
      ext x
      change u x ≤ T ↔ ‖(e.symm x).2‖ ≤ T / c
      rw [hue, le_div_iff₀ hc, mul_comm]
    rw [hset]
    exact isCompact_discCore e (T / c)
  have hsub : {x : M | 0 < u x} ⊆ {x : M | (e.symm x).2 ≠ 0} := by
    intro x hx
    have hx' : 0 < c * ‖(e.symm x).2‖ := by rw [← hue]; exact hx
    exact norm_pos_iff.mp (pos_of_mul_pos_right hx' hc.le)
  have hupos : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ u {x | 0 < u x} := by
    have h := ((contDiff_const (c := c)).mul contDiff_id).contMDiff.comp_contMDiffOn
      ((contMDiffOn_discCoreRadius_off_zero e).mono hsub)
    exact h.congr fun x _ => (hue x).trans (by rfl)
  have hWu' : IsOpen (Wu ∩ {x | 0 < u x}) := hWu.inter (isOpen_lt continuous_const hu)
  have hWuT' : {x | T₀ ≤ u x} ⊆ Wu ∩ {x | 0 < u x} := fun x hx =>
    ⟨hWuT hx, lt_of_lt_of_le hT₀pos hx⟩
  obtain ⟨h1, h2, h3, h4, h5, T₁, hT₁, hiso⟩ :=
    point_distance_core_isotopy g hEnorm p hε hclose hlip hWζ hcollarW hζW V hVB hVdir hu hucpt
      hT₀ hWu' hWuT' (hupos.mono inter_subset_right) (hVW.mono inter_subset_left) huV
  refine ⟨h1, h2, h3, h4, h5, T₁, hT₁, fun ρ hρ => ?_⟩
  obtain ⟨Hs, h0, hs1, hs2, hsupp, himg⟩ := hiso ρ hρ
  exact ⟨Hs, h0, hs1, hs2, hsupp, himg, e.trans (Hs 1).symm, fun z => rfl,
    sublevel_eq_discCore_trans_symm e (Hs 1) hc hue himg⟩

end Bundle

open DifferentialGeometry.Geometry.Topology

variable [ConnectedSpace M] [T2Space (TangentBundle I M)]

/-- **LC55 binding at the normalized scale** for LC54's actual normal-flow diffeomorphism
`e = normalFlowMap … ϕ ℓ` of the soul's normal bundle. With the LC55 inputs for `ζ` and the
collar bounds for the field `V` (both at the normalized scale), and a level `T₀ > ℓ` whose
fibre-radius sublevel lies in `B(p, 1/2)`: `D = {ζ ≤ 1}` is a compact core between the balls with
frontier in the collar and `dζ(V) ≥ 7/32` there, and for every `ρ ∈ (T₀, T₁)` a compactly
supported isotopy carries `D` onto `{u ≤ ρ}` and `D = {x | ‖(e'.symm x).2‖ ≤ ρ}` for
`e' = e.trans H₁⁻¹`; hence `D ≅ D(νS)` (`unitDiscCoreDiffeomorph e'`). -/
theorem point_distance_core_normalFlow_discCore
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g) (p : M)
    {S : Set M} (hconv : IsTotallyConvex g S) (hB : relBoundary I S = ∅) (hScomp : IsCompact S)
    (V : Cₛ^∞⟮I; E, TangentSpace I⟯) (ϕ : Flow ℝ M) {ℓ : ℝ} (hℓ : 0 ≤ ℓ)
    (hIntegral : ∀ q, IsMIntegralCurve (fun t => ϕ t q) V)
    (hVB : ∀ x, 3 / 4 < dist p x → dist p x < 5 / 4 → g.inner x (V x) (V x) ≤ 4)
    (hVdir : ∀ x, 3 / 4 < dist p x → dist p x < 5 / 4 →
      ∀ w ∈ inwardMinimizingDirections (I := I) g hEnorm p x, g.inner x (V x) w ≤ -(1 / 4))
    {ζ : M → ℝ} {ε : ℝ≥0} (hε : (ε : ℝ) ≤ 1 / 64)
    (hclose : ∀ x, |ζ x - dist p x| < 1 / 80)
    (hlip : LipschitzWith ε (fun x => ζ x - dist p x))
    {Wζ : Set M} (hWζ : IsOpen Wζ)
    (hcollarW : ∀ x, 3 / 4 < dist p x → dist p x < 5 / 4 → x ∈ Wζ)
    (hζW : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ ζ Wζ) {T₀ : ℝ} (hℓT₀ : ℓ < T₀) :
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
      {x | ‖(e.symm x).2‖ ≤ T₀} ⊆ Metric.ball p (1 / 2) →
      IsCompact {x | ζ x ≤ 1} ∧
      Metric.closedBall p (1 / 2) ⊆ interior {x | ζ x ≤ 1} ∧
      {x | ζ x ≤ 1} ⊆ Metric.ball p 2 ∧
      frontier {x | ζ x ≤ 1} ⊆ {x | 79 / 80 < dist p x ∧ dist p x < 81 / 80} ∧
      (∀ x, 3 / 4 < dist p x → dist p x < 5 / 4 → 7 / 32 ≤ mvfderiv (I := I) ζ x (V x)) ∧
      ∃ T₁ : ℝ, T₀ < T₁ ∧ ∀ ρ ∈ Ioo T₀ T₁, ∃ Hs : ℝ → Diffeomorph I I M M ∞,
        Hs 0 = Diffeomorph.refl I M ∞ ∧
        ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Hs q.1 q.2) ∧
        ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => (Hs q.1).symm q.2) ∧
        (∃ K : Set M, IsCompact K ∧ K ⊆ (fun x => ‖(e.symm x).2‖) ⁻¹' Ioo T₀ T₁ ∧
          ∀ t x, x ∉ K → Hs t x = x ∧ (Hs t).symm x = x) ∧
        Hs 1 '' {x | ζ x ≤ 1} = {x | ‖(e.symm x).2‖ ≤ ρ} ∧
        ∃ e' : TotalSpace (Fin (Module.finrank ℝ E - maxSliceDim I S) → ℝ)
            (normalBundleFiber g S) ≃ₘ⟮
              (𝓘(ℝ, Fin (maxSliceDim I S) → ℝ)).prod
                𝓘(ℝ, Fin (Module.finrank ℝ E - maxSliceDim I S) → ℝ), I⟯ M,
          (∀ z, e' z = (Hs 1).symm (e z)) ∧
          {x | ζ x ≤ 1} = {x | ‖(e'.symm x).2‖ ≤ ρ} := by
  intro hS _ a _ _ _ e he hT₀
  let _ := embeddedSlice_isManifold hS
  let _ := normalBundle_isContMDiff g hEnorm hconv hB
  let _ := normalBundle_isContMDiffRiemannianBundle g hEnorm hconv hB
  have : CompactSpace S := isCompact_iff_compactSpace.mp hScomp
  obtain ⟨-, -, -, hdu⟩ :=
    normalFlow_radius_core_data g hEnorm hconv hB hScomp V ϕ hℓ hIntegral e he
  have hT₀pos : 0 < T₀ := hℓ.trans_lt hℓT₀
  obtain ⟨h1, h2, h3, h4, h5, T₁, hT₁, hiso⟩ :=
    point_distance_core_isotopy_discCore g hEnorm p hε hclose hlip hWζ hcollarW hζW
      (fun x => V x) hVB hVdir e one_pos (u := fun x => ‖(e.symm x).2‖)
      (fun x => (one_mul _).symm) hT₀pos hT₀ isOpen_univ (subset_univ _)
      V.contMDiff.contMDiffOn (fun x hx => by rw [hdu x (by linarith)]; exact one_pos)
  refine ⟨h1, h2, h3, h4, h5, T₁, hT₁, fun ρ hρ => ?_⟩
  obtain ⟨Hs, h0, hs1, hs2, hsupp, himg, e', he', hD⟩ := hiso ρ hρ
  refine ⟨Hs, h0, hs1, hs2, hsupp, himg, e', he', ?_⟩
  rw [hD, div_one]

end DifferentialGeometry.Geometry.Collapse
