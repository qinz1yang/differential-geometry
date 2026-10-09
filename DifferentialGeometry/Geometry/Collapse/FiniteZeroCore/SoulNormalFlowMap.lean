import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.SoulStrictOutward
import DifferentialGeometry.Geometry.Collapse.SublevelCore.PointOutwardNormalFlow

/-!
# The actual normal-flow map of the soul, with its formulas (LFR46, smooth carrier)

Frozen blueprint master207A, lemma `lem:collapse-finite-normal-flow-map` (LFR46, lines
28884–28973). For the SAME soul `S`, normal bundle `E = νS` and normal tube `Φ` as in LFR45
(`exists_soul_strict_outward_tube`), there are `ℓ > 0`, a bounded field `V` (`|V| ≤ 2`), its
complete flow `ϕ` and a diffeomorphism `e : E → M` fixing the zero section with (LFR46.1)

  `e(s, w) = Φ(s, w)` for `|w| ≤ ℓ`,   `e(s, w) = ϕ_{|w| - ℓ}(Φ(s, ℓ w / |w|))` for `|w| > ℓ`,

`V = ∇d_S` on a neighbourhood of a closed tube annulus `{a ≤ d_S ≤ b}` with `a < ℓ < b`, `V`
strictly outward from `S` on `{d_S ≥ ℓ/3}`, and (LFR46.2) the point margin `g(V, u) ≤ -1/4` for
every inward unit minimizing direction `u` to `p` once `d(p, q) ≥ A₂`. The field is chosen before
the map: `e = normalFlowMap … ϕ ℓ` is built from this `V`.

This is LC54 (`exists_point_outward_normalFlow_data`, `SublevelCore/PointOutwardNormalFlow.lean`)
run again with its internal facts exported, together with LFR45's strict outward directions and
tube for the same `S`. As in LC54, no LC21 cone is used (the point margin comes from LC52/LC53).

Scope: SMOOTH metric. The row's `C^{m-3}` statement for a `C^m` metric needs the finite-order
geodesic flow (LFR01), which this tree does not have. Not delivered: the optional inner profile
`V = a(d_S) ∇d_S` toward `S` (here `V` near `S` is the PC soul's own outward field; the profile is
used only by LFR47's identification of `V` in the finite carrier).
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set Metric
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Topology

namespace DifferentialGeometry.Geometry.Collapse

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

/-- **LFR46 (smooth carrier).** One PC soul `S` with LFR45's strict outward directions, a bounded
smooth field `V` (gradient of `d_S` near the seam, soul-outward on `{d_S ≥ ℓ/3}`, point-outward far
out), its complete flow `ϕ`, a tube `Φ = normalExp` of radius `ε > ℓ`, and the actual normal-flow
diffeomorphism `e = normalFlowMap … ϕ ℓ` with its two formulas (LFR46.1). -/
theorem exists_soul_normalFlow_map_data [NoncompactSpace M]
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hsec : ∀ x : M, metricRm04At (I := I) g x ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M)) (p : M) :
    ∃ (S : Set M) (hconv : IsTotallyConvex g S) (hB : relBoundary I S = ∅),
      S.Nonempty ∧ IsCompact S ∧ PathConnectedSpace S ∧
      maxSliceDim I S < Module.finrank ℝ E ∧
      (∀ q : M, q ∉ S → ∃ v : TangentSpace I q, g.inner q v v = 1 ∧
        ∀ u : TangentSpace I q, g.inner q u u = 1 →
          intrinsicGeodesic g hEnorm q u (infDist q S) ∈ S → g.inner q v u < 0) ∧
      ∃ V : Cₛ^∞⟮I; E, TangentSpace I⟯, ∃ ϕ : Flow ℝ M, ∃ ℓ : ℝ, 0 < ℓ ∧ ∃ A₂ : ℝ, 0 < A₂ ∧
        (∀ q, g.inner q (V q) (V q) ≤ 4) ∧
        ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun z : ℝ × M => ϕ z.1 z.2) ∧
        (∀ q, IsMIntegralCurve (fun t => ϕ t q) V) ∧
        (∀ q, A₂ ≤ dist p q → ∀ w ∈ inwardMinimizingDirections (I := I) g hEnorm p q,
          g.inner q (V q) w ≤ -(1 / 4)) ∧
        (∀ q : M, ℓ / 3 ≤ infDist q S → ∀ u : TangentSpace I q, g.inner q u u = 1 →
          intrinsicGeodesic g hEnorm q u (infDist q S) ∈ S → g.inner q (V q) u < 0) ∧
        (∃ a b : ℝ, 0 < a ∧ a < ℓ ∧ ℓ < b ∧
          ∀ᶠ q in 𝓝ˢ {q : M | a ≤ infDist q S ∧ infDist q S ≤ b},
            V q = gradientFun g (fun x => infDist x S) q) ∧
        let hS := isEmbeddedSlice_of_relBoundary_eq_empty hEnorm hconv hB
        let _ := embeddedSliceChartedSpace hS
        let a := normalBundlePrebundle g hEnorm hconv hB
        let _ := a.totalSpaceTopology
        let _ := a.toFiberBundle
        let _ := a.toVectorBundle
        (∃ ε : ℝ, ℓ < ε ∧ ∃ Φ : PartialDiffeomorph
            ((𝓘(ℝ, Fin (maxSliceDim I S) → ℝ)).prod
              𝓘(ℝ, Fin (Module.finrank ℝ E - maxSliceDim I S) → ℝ)) I
            (TotalSpace (Fin (Module.finrank ℝ E - maxSliceDim I S) → ℝ)
              (normalBundleFiber g S)) M ∞,
          Φ.source = {z | Real.sqrt (g.inner z.proj.1 z.snd.1 z.snd.1) < ε} ∧
          Φ.target = {q | infDist q S < ε} ∧
          (Φ : TotalSpace (Fin (Module.finrank ℝ E - maxSliceDim I S) → ℝ)
              (normalBundleFiber g S) → M) = normalExp (I := I) g hEnorm S ∧
          ∀ z ∈ Φ.source, Real.sqrt (g.inner z.proj.1 z.snd.1 z.snd.1) = infDist (Φ z) S) ∧
        ∃ e : TotalSpace (Fin (Module.finrank ℝ E - maxSliceDim I S) → ℝ)
            (normalBundleFiber g S) ≃ₘ⟮
              (𝓘(ℝ, Fin (maxSliceDim I S) → ℝ)).prod
                𝓘(ℝ, Fin (Module.finrank ℝ E - maxSliceDim I S) → ℝ), I⟯ M,
          (∀ z, e z = normalFlowMap (I := I) g hEnorm S ϕ ℓ z) ∧
          (∀ s : S, e ⟨s, 0⟩ = s.1) ∧
          (∀ z : TotalSpace (Fin (Module.finrank ℝ E - maxSliceDim I S) → ℝ)
              (normalBundleFiber g S),
            Real.sqrt (g.inner z.proj.1 z.snd.1 z.snd.1) ≤ ℓ →
              e z = normalExp (I := I) g hEnorm S z) ∧
          ∀ (s : S) (v : normalBundleFiber (I := I) g S s), g.inner s.1 v.1 v.1 = 1 →
            ∀ t : ℝ, ℓ < t → e ⟨s, t • v⟩ = ϕ (t - ℓ) (e ⟨s, ℓ • v⟩) := by
  classical
  obtain ⟨S, hSne, hScomp, hconv, hB, hdim, r₀, hr₀, hd, hradial, hfields⟩ :=
    exists_soul_set_with_radial_outward_field g hEnorm hsec p
  have hstrict := exists_unit_strict_outward_of_fields g hEnorm hSne hScomp hr₀
    (fun r hr hrr₀ => by
      obtain ⟨W, -, -, hW⟩ := hfields r hr hrr₀
      exact ⟨fun x => W x, hW⟩)
  refine ⟨S, hconv, hB, hSne, hScomp, IsTotallyConvex.pathConnectedSpace g hEnorm hconv hSne,
    hdim, hstrict, ?_⟩
  let hS := isEmbeddedSlice_of_relBoundary_eq_empty hEnorm hconv hB
  let _ := embeddedSliceChartedSpace hS
  let _ := embeddedSlice_isManifold hS
  let a := normalBundlePrebundle g hEnorm hconv hB
  let _ := a.totalSpaceTopology
  let _ := a.toFiberBundle
  let _ := a.toVectorBundle
  let _ := normalBundle_isContMDiff g hEnorm hconv hB
  let FN := Fin (Module.finrank ℝ E - maxSliceDim I S) → ℝ
  let NB := TotalSpace FN (normalBundleFiber g S)
  obtain ⟨ε, hε, Φ, hsource, htarget, hΦ, -, hradius⟩ :=
    exists_normal_tube g hEnorm hsec hSne hScomp hconv hB
  let r := min r₀ ε
  have hr : 0 < r := lt_min hr₀ hε
  have hrr₀ : r ≤ r₀ := min_le_left _ _
  have hrε : r ≤ ε := min_le_right _ _
  -- The soul's own bounded radial field and the LC53 two-target field for the same soul.
  obtain ⟨W₀, hW₀bound, hW₀rad, hW₀out⟩ := hfields r hr hrr₀
  obtain ⟨A₀, A₁, hA₀, hA₀₁, -, X, hXbound, -, hXout⟩ :=
    exists_smooth_outward_field_two_targets (I := I) g hEnorm hsec p hScomp
  -- A ball containing the tube annulus and `B̄(p, A₁)`, and the cutoff `χ`.
  set T : Set M := {q : M | r / 4 ≤ infDist q S ∧ infDist q S ≤ r / 2} with hTdef
  have hT : IsCompact T :=
    (isCompact_infDist_sublevel g hEnorm hScomp hSne (r / 2)).of_isClosed_subset
      ((isClosed_le continuous_const (continuous_infDist_pt S)).inter
        (isClosed_le (continuous_infDist_pt S) continuous_const)) (fun _ hq => hq.2)
  obtain ⟨RT, hRT⟩ := hT.isBounded.subset_closedBall p
  set R' : ℝ := max A₁ RT + 1 with hR'def
  have hA₁R' : A₁ < R' := by simp only [hR'def]; linarith [le_max_left A₁ RT]
  have hTR' : T ⊆ closedBall p R' := fun q hq =>
    closedBall_subset_closedBall (by simp only [hR'def]; linarith [le_max_right A₁ RT]) (hRT hq)
  have hdisj : Disjoint (closedBall p R') (ball p (R' + 1))ᶜ :=
    Set.disjoint_compl_right_iff_subset.mpr (closedBall_subset_ball (by linarith))
  obtain ⟨χ, hχzero, hχone, hχrange⟩ :=
    exists_contMDiffMap_zero_one_nhds_of_isClosed (n := (⊤ : ℕ∞)) I
      isClosed_closedBall isOpen_ball.isClosed_compl hdisj
  have hχ0 : ∀ q ∈ closedBall p R', χ q = 0 := fun q hq => hχzero.self_of_nhdsSet q hq
  have hχ1 : ∀ q ∉ ball p (R' + 1), χ q = 1 := fun q hq => hχone.self_of_nhdsSet q hq
  -- The patched field.
  have hsmooth : ContMDiff I I.tangent ∞
      (T% fun q => (1 - χ q) • W₀ q + χ q • X q) :=
    ((contMDiff_const.sub χ.contMDiff).smul_section W₀.contMDiff).add_section
      (χ.contMDiff.smul_section X.contMDiff)
  let V : Cₛ^∞⟮I; E, TangentSpace I⟯ := ⟨fun q => (1 - χ q) • W₀ q + χ q • X q, hsmooth⟩
  have hVapply : ∀ q, V q = (1 - χ q) • W₀ q + χ q • X q := fun _ => rfl
  have hVW₀ : ∀ q, χ q = 0 → V q = W₀ q := by
    intro q hq
    rw [hVapply, hq, sub_zero, one_smul, zero_smul, add_zero]
  have hVX : ∀ q, χ q = 1 → V q = X q := by
    intro q hq
    rw [hVapply, hq, sub_self, zero_smul, one_smul, zero_add]
  -- Norm bound by convexity.
  have hVbound : ∀ q, g.inner q (V q) (V q) ≤ 4 := by
    intro q
    have h0 := (hχrange q).1
    have h1 : 0 ≤ 1 - χ q := sub_nonneg.mpr (hχrange q).2
    have hvar : g.inner q (V q) (V q) =
        (1 - χ q) * g.inner q (W₀ q) (W₀ q) + χ q * g.inner q (X q) (X q) -
          (1 - χ q) * χ q * g.inner q (W₀ q - X q) (W₀ q - X q) := by
      rw [hVapply]
      simp only [map_add, map_smul, add_apply, _root_.smul_apply, smul_eq_mul,
        map_sub, sub_apply, g.symm q (X q) (W₀ q)]
      ring
    have hpos := mul_nonneg (mul_nonneg h1 h0) (gInner_self_nonneg g q (W₀ q - X q))
    have hW := mul_le_mul_of_nonneg_left (hW₀bound q) h1
    have hX := mul_le_mul_of_nonneg_left (hXbound q).le h0
    nlinarith
  -- Outward from `S` on `{d_S ≥ r/8}`.
  have hVout : ∀ q : M, r / 8 ≤ infDist q S → ∀ u : TangentSpace I q, g.inner q u u = 1 →
      intrinsicGeodesic g hEnorm q u (infDist q S) ∈ S → g.inner q (V q) u < 0 := by
    intro q hq u hu hend
    have hW := hW₀out q hq u hu hend
    by_cases hχq : χ q = 0
    · rw [hVW₀ q hχq]
      exact hW
    · have hfar : A₁ ≤ dist p q := by
        by_contra hlt
        push Not at hlt
        exact hχq (hχ0 q (by rw [mem_closedBall, dist_comm]; linarith))
      have hXu := hXout q hfar u (Or.inr ⟨hu, hend⟩)
      have hpos : 0 < χ q := lt_of_le_of_ne (hχrange q).1 (Ne.symm hχq)
      have h1 : 0 ≤ 1 - χ q := sub_nonneg.mpr (hχrange q).2
      rw [hVapply]
      simp only [map_add, map_smul, add_apply, _root_.smul_apply, smul_eq_mul]
      nlinarith [mul_nonpos_of_nonneg_of_nonpos h1 hW.le]
  -- Point margin far out.
  have hVpoint : ∀ q, R' + 1 ≤ dist p q → ∀ w ∈ inwardMinimizingDirections (I := I) g hEnorm p q,
      g.inner q (V q) w ≤ -(1 / 4) := by
    intro q hq w hw
    rw [hVX q (hχ1 q (by rw [mem_ball, dist_comm]; linarith))]
    exact hXout q (by linarith) w (Or.inl hw)
  -- `V` is the gradient of `d_S` on a neighbourhood of the closed annulus `T`.
  have hVgrad : ∀ᶠ q in 𝓝ˢ T, V q = gradientFun g (fun x => infDist x S) q := by
    have hχT : ∀ᶠ q in 𝓝ˢ T, χ q = 0 := hχzero.filter_mono (nhdsSet_mono hTR')
    filter_upwards [hχT, hW₀rad] with q hq hqrad
    rw [hVW₀ q hq]
    exact hqrad
  -- The complete escape flow of `V`.
  have hr8 : 0 < r / 8 := by positivity
  obtain ⟨ϕ, hϕsmooth, hIntegral, -⟩ := exists_complete_infDist_escape_flow g hEnorm hScomp hSne
    V 2 (by norm_num) (fun q => by simpa only [show (2 : ℝ) ^ 2 = 4 by norm_num] using hVbound q)
    hr8 hVout
  -- The PC normal-flow gluing with this field.
  let ℓ := 3 * r / 8
  let δ := r / 16
  have hℓ : 0 < ℓ := by dsimp only [ℓ]; positivity
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hδℓ : δ < ℓ := by dsimp only [δ, ℓ]; linarith
  have hℓδε : ℓ + δ < ε := by dsimp only [δ, ℓ]; linarith
  have hℓmem : ℓ ∈ Ioo (r / 4) (r / 2) := by
    dsimp only [ℓ]
    constructor <;> linarith
  have hdAnn : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun q => infDist q S)
      {q | r / 4 < infDist q S ∧ infDist q S < r / 2} :=
    hd.mono (fun q hq => ⟨by linarith [hq.1], by linarith [hq.2]⟩)
  have hVAnn (q : M) (hqlo : r / 4 < infDist q S) (hqhi : infDist q S < r / 2) :
      V q = gradientFun g (fun x => infDist x S) q := by
    have hqT : q ∈ T := ⟨hqlo.le, hqhi.le⟩
    rw [hVW₀ q (hχ0 q (hTR' hqT))]
    exact hW₀rad.self_of_nhdsSet q hqT
  have houtℓ (q : M) (hq : ℓ ≤ infDist q S) (u : TangentSpace I q)
      (hu : g.inner q u u = 1)
      (hend : intrinsicGeodesic g hEnorm q u (infDist q S) ∈ S) :
      g.inner q (V q) u < 0 :=
    hVout q (by dsimp only [ℓ] at hq; linarith) u hu hend
  obtain ⟨e, he, hezero⟩ := exists_normalFlow_diffeomorph g hEnorm hSne hScomp hconv hB
    hℓ hδ hδℓ hℓδε V V.contMDiff.continuous ϕ hϕsmooth hIntegral houtℓ
    Φ hsource htarget hΦ hradius (by
      intro z hzlo hzhi
      let R := Real.sqrt (g.inner z.proj.1 z.snd.1 z.snd.1)
      have hRmem : R ∈ Ioo (r / 4) (r / 2) := by
        change ℓ - δ < R at hzlo
        change R < ℓ + δ at hzhi
        dsimp only [ℓ, δ] at hzlo hzhi
        constructor <;> linarith
      have hR : 0 < R := by linarith [hRmem.1]
      let v : normalSpace g S z.proj.1 := R⁻¹ • z.snd
      have hR2 : R ^ 2 = g.inner z.proj.1 z.snd.1 z.snd.1 :=
        Real.sq_sqrt (gInner_self_nonneg g z.proj.1 z.snd.1)
      have hv : g.inner z.proj.1 v.1 v.1 = 1 := by
        change g.inner z.proj.1 (R⁻¹ • z.snd.1) (R⁻¹ • z.snd.1) = 1
        rw [gInner_smul_self, ← hR2]
        field_simp [hR.ne']
      have hcal : ∀ t ∈ Ioo (r / 4) (r / 2),
          infDist (intrinsicGeodesic g hEnorm z.proj.1 v.1 t) S = t := by
        intro t ht
        exact hradial z.proj v hv t (by linarith [ht.1]) (by linarith [ht.2])
      have hflow := flow_eq_intrinsicGeodesic_on_annulus g hEnorm hScomp hSne
        z.proj.1 v.1 hv (by positivity : 0 ≤ r / 4) hdAnn hcal V hVAnn ϕ hIntegral hℓmem hRmem
      have hparam (t : ℝ) : intrinsicGeodesic g hEnorm z.proj.1 v.1 t =
          normalExp g hEnorm S (⟨z.proj, (t / R) • z.snd⟩ : NB) := by
        rw [← expMapIntrinsic_smul_eq_intrinsicGeodesic]
        change expMapIntrinsic g hEnorm z.proj.1 (t • (R⁻¹ • z.snd.1)) =
          expMapIntrinsic g hEnorm z.proj.1 ((t / R) • z.snd.1)
        rw [smul_smul, div_eq_mul_inv]
      have hparamR : intrinsicGeodesic g hEnorm z.proj.1 v.1 R = normalExp g hEnorm S z := by
        simpa only [div_self hR.ne', one_smul] using hparam R
      change ϕ (R - ℓ) (normalExp g hEnorm S ⟨z.proj, (ℓ / R) • z.snd⟩) =
        normalExp g hEnorm S z
      rw [← hparam ℓ, ← hparamR]
      exact hflow)
  refine ⟨V, ϕ, ℓ, hℓ, R' + 1, by linarith, hVbound, hϕsmooth, hIntegral, hVpoint,
    fun q hq => hVout q (by dsimp only [ℓ] at hq; linarith), ⟨r / 4, r / 2, by positivity,
      hℓmem.1, hℓmem.2, hVgrad⟩, ⟨ε, by linarith, Φ, hsource, htarget, hΦ, hradius⟩,
    e, he, hezero, ?_, ?_⟩
  · intro z hz
    rw [he z]
    simp only [normalFlowMap, hz, ite_true]
  · intro s v hv t ht
    rw [he, he]
    exact normalFlowMap_ray g hEnorm S ϕ hℓ.le ht s v hv

end DifferentialGeometry.Geometry.Collapse
