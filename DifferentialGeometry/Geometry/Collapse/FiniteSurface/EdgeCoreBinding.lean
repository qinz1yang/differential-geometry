import DifferentialGeometry.Geometry.Collapse.FiniteSurface.EndpointDiskBand
import DifferentialGeometry.Geometry.Collapse.FiniteSurface.EndpointLevelCircle
import DifferentialGeometry.Geometry.Collapse.FiniteSurface.EdgeCoreLevelKernels
import DifferentialGeometry.Geometry.Collapse.FiniteSurface.EdgeCoreSmoothDisk

/-!
# LFR24: a smooth edge-model core on the finite metric (the row binding)

Row LFR24 (`thm:collapse-finite-edge-model-core`, master207A:26862). On the LFR23 surface (model
`𝓡 2`, orientable, complete, connected, `C^{r+1}`, `r ≥ 3`, `K ≥ 0`) with an endpoint model of error
`δ ≤ δ₀(ε) = ε²/24000000`, for every `0 < μ < 1/100`, the function `h = ψ ∘ F` (`F` from LFR02 with
`Y = {z₀}`, `ψ = edgeSublevelProfile`, W4-F7c's `edgeModelCore`) has every clause of the row.

* `exists_disk_sublevel_of_smoothing`: for an LFR02 smoothing `F` (`|F - r| < μ ≤ 1/100`, smooth near
  `3/4 ≤ r ≤ 91/10`, `|dF(w) + ⟨v, w⟩| ≤ ε/25 |w|`, `ε ≤ 1`) and `s ∈ [3, 6]`, the sublevel `{F ≤ s}` is a
  topological closed disk with boundary circle `{F = s}`: the level is a cross-section of the band
  product of LFR23's outward flow (`strictMonoOn_comp_hittingTime_of_rate`,
  `exists_embedding_level_of_band_product`), a compact connected regular level hence a Jordan circle,
  the frontier of the sublevel (`F` grows along the flow), and the Jordan-domain recognition in
  `S² / ℝ² / S¹ × ℝ` (LFR22; torus excluded by SF-FT2) gives the disk. This replaces the blueprint's
  "radius-two disk of LFR23 with a collar attached" (same conclusion).
* `finiteSurface_edge_model_core`: the row. The smooth disk is SF-C's `edgeCoreSublevel_smooth_disk`
  (Hirsch 9.3.7 replaced), the other clauses are W4-F7c's `EdgeModelCore` kernels, and the SAME field
  is LFR23's (`exists_endpoint_field`), with `dh(V) > 1/2` on the collar `2.1 ≤ r ≤ 8`.

Deviations (recorded): LFR24.1's gradient clause is the dual form `|dh(w) + ⟨v, w⟩| ≤ (ε/25)|w|`
(stronger than `‖∇h + v‖ < ε`); the product enclosure (LFR24.2) is stated for every `Δ > 0` with the
time coordinate scaled by `Δ` and `r = d(z₀, ·)` of the given metric (the physical-scale form applies
the row to the rescaled metric `Δ⁻¹ k`); the transversality clause is the regularity `dh ≠ 0` on the
level `h = 4` inside `r < 9`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Metric Function Topology
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Topology DifferentialGeometry.Topology.Surface
open DifferentialGeometry.Geometry.FiniteSoul

local notation "E2" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

open DifferentialGeometry.Topology.Handle in
attribute [local instance] closedCellChartedSpaceSucc closedCellIsManifold

variable {Z : Type*} [MetricSpace Z] [ChartedSpace E2 Z] [IsManifold (𝓡 2) ∞ Z]
  [RiemannianBundle (fun x : Z => TangentSpace (𝓡 2) x)] [IsRiemannianManifold (𝓡 2) Z]
  [CompleteSpace Z] [ConnectedSpace Z]

omit [RiemannianBundle (fun x : Z => TangentSpace (𝓡 2) x)] [IsRiemannianManifold (𝓡 2) Z]
  [CompleteSpace Z] [ConnectedSpace Z] in
/-- `dF(V) > 1/2` for an LFR02 gradient bound and a field of norm `< 2` with pairing `< -3/4`. -/
theorem one_half_lt_mvfderiv_of_gradient {r : ℕ∞}
    (k : ContMDiffRiemannianMetric (𝓡 2) ((r : ℕ∞ω) + 1) E2 (TangentSpace (𝓡 2) : Z → Type _))
    {F : Z → ℝ} {y : Z} {v V : TangentSpace (𝓡 2) y} {ε : ℝ} (hε : ε ≤ 1)
    (hgrad : |mvfderiv (𝓡 2) F y V + k.inner y v V| ≤ ε / 25 * Real.sqrt (k.inner y V V))
    (hVR : k.inner y V V < 2 ^ 2) (hVv : k.inner y V v < -(3 / 4)) :
    1 / 2 < mvfderiv (𝓡 2) F y V := by
  have h3 : k.inner y v V = k.inner y V v := k.symm y v V
  have h4 : Real.sqrt (k.inner y V V) < 2 := by
    rw [show (2 : ℝ) = Real.sqrt (2 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (k.inner_self_nonneg' y V) hVR
  have h5 := abs_le.1 hgrad
  rw [h3] at h5
  have h6 : ε / 25 * Real.sqrt (k.inner y V V) ≤ 1 / 25 * 2 := by
    have h7 : 0 ≤ Real.sqrt (k.inner y V V) := Real.sqrt_nonneg _
    have h8 : ε / 25 ≤ 1 / 25 := by linarith
    nlinarith
  linarith [h5.1]

/-- **LFR24's topological disk.** For an LFR02 smoothing `F` of `r = d(z₀, ·)` on the LFR23 surface
and `s ∈ [3, 6]`, the sublevel `{F ≤ s}` is a closed disk with boundary circle `{F = s}`. -/
theorem exists_disk_sublevel_of_smoothing (o : ManifoldOrientation (𝓡 2) Z 2) {r : ℕ∞}
    (k : ContMDiffRiemannianMetric (𝓡 2) ((r : ℕ∞ω) + 1) E2 (TangentSpace (𝓡 2) : Z → Type _))
    (hr : 3 ≤ r)
    (hnorm : ∀ (x : Z) (w : TangentSpace (𝓡 2) x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (k.inner x w w)))
    (hK : ∀ x (v w : TangentSpace (𝓡 2) x), 0 ≤ k.sectionalCurvature x v w)
    {z₀ : Z} {q : Z → ℝ} {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 9600) (hq0 : q z₀ = 0)
    (hqnn : ∀ y ∈ closedBall z₀ 10, 0 ≤ q y)
    (hdist : ∀ y ∈ closedBall z₀ 10, ∀ y' ∈ closedBall z₀ 10,
      |dist (q y) (q y') - dist y y'| ≤ δ)
    (hdense : ∀ t ∈ Icc (0 : ℝ) 10, ∃ y ∈ closedBall z₀ 10, |q y - t| ≤ δ)
    {F : Z → ℝ} (hFc : Continuous F) {μ : ℝ} (hμ : μ ≤ 1 / 100)
    (hFr : ∀ x, |F x - infDist x ({z₀} : Set Z)| < μ) {OF : Set Z} (hOF : IsOpen OF)
    (hFs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ F OF)
    (hCOF : ∀ x, 3 / 4 ≤ dist x z₀ → dist x z₀ ≤ 91 / 10 → x ∈ OF) {ε : ℝ} (hε : ε ≤ 1)
    (hgrad : ∀ x ∈ OF, ∀ v ∈ k.finiteMinimizingDirectionsTo ({z₀} : Set Z) x,
      ∀ w : TangentSpace (𝓡 2) x,
        |mvfderiv (𝓡 2) F x w + k.inner x v w| ≤ ε / 25 * Real.sqrt (k.inner x w w))
    {s : ℝ} (hs : s ∈ Icc (3 : ℝ) 6) :
    ∃ φ : Disk 2 → Z, IsClosedEmbedding φ ∧ range φ = {x | F x ≤ s} ∧
      φ '' diskSphere 2 = {x | F x = s} := by
  have : NeZero (Module.finrank ℝ E2) := ⟨by simp⟩
  have : ProperSpace Z := Manifold.properSpace_of_isRiemannianManifold (𝓡 2)
  have hr2 : 2 ≤ r := le_trans (by norm_num) hr
  have hdim : Module.finrank ℝ E2 = 2 := by simp
  set η : Z → ℝ := fun x => infDist x ({z₀} : Set Z) with hη
  have hηd : ∀ x, η x = dist x z₀ := fun x => infDist_singleton
  have hFr' : ∀ x, |F x - η x| < μ := hFr
  ---------------------------------------------------------------- the outward field and flow
  obtain ⟨V, -, hVR, O, hO, hAO, hOout, Φ, hΦ, hΦ0, hΦadd, hder, hrate, -, hspec, e, he1, -, he3,
    he4, -⟩ := exists_endpoint_field k hr2 hnorm hK hδ hδ' hq0 hqnn hdist hdense
  set W : Set Z := OF ∩ O with hW
  have hWo : IsOpen W := hOF.inter hO
  have hdFV : ∀ y ∈ W, 1 / 2 ≤ mvfderiv (𝓡 2) F y (V y) := by
    intro y hy
    obtain ⟨v, hv⟩ := (k.finiteMinimizingDirectionsTo_nonempty_isCompact hr2 hnorm
      isClosed_singleton (singleton_nonempty z₀) y).1
    exact (one_half_lt_mvfderiv_of_gradient k hε (hgrad y hy.1 v hv (V y)) (hVR y)
      (hOout y hy.2 v hv)).le
  have hFrate := add_mul_le_comp_flow_of_mvfderiv hWo (hFs.mono inter_subset_left) hΦ0 hder hdFV
  ---------------------------------------------------------------- the band `1 ≤ r ≤ 9`
  have hC₀W : ∀ x, η x ∈ Icc (1 : ℝ) 9 → x ∈ W ∩ ({z₀} : Set Z)ᶜ := by
    intro x hx
    have hxd : dist x z₀ ∈ Icc (1 : ℝ) 9 := by rw [← hηd]; exact hx
    refine ⟨⟨hCOF x (by linarith [hxd.1]) (by linarith [hxd.2]), hAO ⟨by linarith [hx.1],
      by linarith [hx.2]⟩⟩, fun hxz => ?_⟩
    rw [mem_singleton_iff] at hxz
    rw [hxz, dist_self] at hxd
    linarith [hxd.1]
  have hIcc : ∀ t : ℝ, t ∈ Icc (1 : ℝ) 9 → t ∈ Icc (1 / 2 : ℝ) (37 / 4) := fun t ht =>
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  set P := {x : Z // infDist x ({z₀} : Set Z) = 5}
  have hPc : CompactSpace P := by
    have hK' : IsCompact {x : Z | infDist x ({z₀} : Set Z) = 5} := by
      refine (isCompact_closedBall z₀ 5).of_isClosed_subset
        (isClosed_eq (continuous_infDist_pt _) continuous_const) fun x hx => ?_
      have hx' : infDist x ({z₀} : Set Z) = 5 := hx
      rw [infDist_singleton] at hx'
      exact hx'.le
    exact isCompact_iff_compactSpace.mp hK'
  have hPconn : ConnectedSpace P := by
    have h := (isPathConnected_sphere_of_endpoint k hr2 hnorm hK hδ hδ' hq0 hqnn hdist hdense
      (a := 5) ⟨by norm_num, by norm_num⟩).isConnected
    have hset : sphere z₀ 5 = {x : Z | infDist x ({z₀} : Set Z) = 5} := by
      ext y
      change dist y z₀ = 5 ↔ infDist y ({z₀} : Set Z) = 5
      rw [infDist_singleton]
    rw [hset] at h
    exact isConnected_iff_connectedSpace.mp h
  set e₁ : P × Icc (1 : ℝ) 9 → Z :=
    fun q => (e (q.1, ⟨q.2.1, hIcc q.2.1 q.2.2⟩) : Z) with he₁
  have he₁c : Continuous e₁ := by
    refine continuous_subtype_val.comp (e.continuous.comp (continuous_fst.prodMk ?_))
    exact (continuous_subtype_val.comp continuous_snd).subtype_mk _
  have he₁i : Injective e₁ := by
    intro q q' hqq'
    have h := e.injective (Subtype.ext hqq')
    obtain ⟨h1, h2⟩ := Prod.ext_iff.1 h
    have h3 : ((q.2 : ℝ)) = q'.2 := by
      have h4 := congrArg (fun z : Icc (1 / 2 : ℝ) (37 / 4) => (z : ℝ)) h2
      exact h4
    exact Prod.ext h1 (Subtype.ext h3)
  ---------------------------------------------------------------- `F` along the fibres
  have hmono : ∀ p, StrictMono (fun t : Icc (1 : ℝ) 9 => F (e₁ (p, t))) := by
    intro p t t' htt'
    have hp : η (p : Z) ∈ Icc (1 : ℝ) 9 := by
      change infDist (p : Z) ({z₀} : Set Z) ∈ _
      rw [p.2]; norm_num
    have hp' : η (p : Z) ∈ Icc (1 / 2 : ℝ) (37 / 4) := hIcc _ hp
    have h := strictMonoOn_comp_hittingTime_of_rate hΦadd (by norm_num : (0 : ℝ) < 3 / 4)
      (by norm_num : (0 : ℝ) < 1 / 2) (U := W ∩ ({z₀} : Set Z)ᶜ)
      (fun x u hu hU => hrate x u hu fun s hs => ⟨(hU s hs).1.2, (hU s hs).2⟩)
      (fun x u hu hU => hFrate x u hu fun s hs => (hU s hs).1) hC₀W hp
      (τ := fun s => hittingTime Φ η p s)
      (fun s hs => (hspec p hp' s (hIcc s hs)).1) (fun s hs => (hspec p hp' s (hIcc s hs)).2.1)
      t.2 t'.2 htt'
    change F (e (p, ⟨t.1, hIcc t.1 t.2⟩) : Z) < F (e (p, ⟨t'.1, hIcc t'.1 t'.2⟩) : Z)
    rw [he1, he1]
    exact h
  have hkey : ∀ (p : P) (t : Icc (1 : ℝ) 9), η (e₁ (p, t)) = t := fun p t =>
    he4 (p, ⟨t.1, hIcc t.1 t.2⟩)
  have hlow : ∀ p : P, F (e₁ (p, ⟨1, left_mem_Icc.2 (by norm_num)⟩)) < s := fun p => by
    have h1 := hkey p ⟨1, left_mem_Icc.2 (by norm_num)⟩
    have h2 := abs_lt.1 (hFr' (e₁ (p, ⟨1, left_mem_Icc.2 (by norm_num)⟩)))
    rw [h1] at h2
    linarith [h2.2, hs.1]
  have hhigh : ∀ p : P, s < F (e₁ (p, ⟨9, right_mem_Icc.2 (by norm_num)⟩)) := fun p => by
    have h1 := hkey p ⟨9, right_mem_Icc.2 (by norm_num)⟩
    have h2 := abs_lt.1 (hFr' (e₁ (p, ⟨9, right_mem_Icc.2 (by norm_num)⟩)))
    rw [h1] at h2
    linarith [h2.1, hs.2]
  obtain ⟨c₀, hc₀c, hc₀i, hc₀r⟩ := exists_embedding_level_of_band_product (by norm_num)
    he₁c he₁i hFc hmono hlow hhigh
  have hlev19 : ∀ x, F x = s → η x ∈ Icc (1 : ℝ) 9 := fun x hx => by
    have h2 := abs_lt.1 (hFr' x)
    rw [hx] at h2
    exact ⟨by linarith [h2.2, hs.1], by linarith [h2.1, hs.2]⟩
  have hrange0 : range c₀ = {x | F x = s} := by
    rw [hc₀r]
    ext x
    refine ⟨fun hx => hx.2, fun hx => ⟨?_, hx⟩⟩
    have hx19 := hlev19 x hx
    set y : {x : Z // infDist x ({z₀} : Set Z) ∈ Icc (1 / 2 : ℝ) (37 / 4)} :=
      ⟨x, hIcc _ hx19⟩ with hy
    refine ⟨((e.symm y).1, ⟨η x, hx19⟩), ?_⟩
    have hq : ((e.symm y).1, (⟨η x, hIcc _ hx19⟩ : Icc (1 / 2 : ℝ) (37 / 4))) = e.symm y :=
      Prod.ext rfl (Subtype.ext (he3 y).symm)
    change (e ((e.symm y).1, ⟨η x, hIcc _ hx19⟩) : Z) = x
    rw [hq, e.apply_symm_apply]
  ---------------------------------------------------------------- `{F = s}` is a Jordan circle
  have hcpt : IsCompact {x | F x = s} := by rw [← hrange0]; exact isCompact_range hc₀c
  have hconn : IsConnected {x | F x = s} := by rw [← hrange0]; exact isConnected_range hc₀c
  obtain ⟨c₁, hc₁c, hc₁i, hc₁r⟩ := exists_circle_of_regular_level (W := ⟨W, hWo⟩) hdim
    (hFs.mono inter_subset_left) (fun y hy => (hC₀W y (hlev19 y hy)).1)
    (fun y hy => ⟨V y, (lt_of_lt_of_le (by norm_num) (hdFV y (hC₀W y (hlev19 y hy)).1)).ne'⟩)
    hcpt hconn
  ---------------------------------------------------------------- the sublevel
  have hfr : frontier {x | F x ≤ s} = range c₁ := by
    rw [hc₁r]
    refine Subset.antisymm (frontier_le_subset_eq hFc continuous_const) fun x hx => ?_
    exact mem_frontier_le_of_rate hΦ.continuous hΦ0 hWo (by norm_num : (0 : ℝ) < 1 / 2) hFrate
      (hC₀W x (hlev19 x hx)).1 hx
  have hD : IsCompact {x | F x ≤ s} := by
    refine (isCompact_closedBall z₀ 7).of_isClosed_subset (isClosed_le hFc continuous_const)
      fun x hx => ?_
    have h2 := abs_lt.1 (hFr' x)
    rw [hηd] at h2
    change F x ≤ s at hx
    change dist x z₀ ≤ 7
    linarith [h2.1, hs.2]
  have hint : (interior {x | F x ≤ s}).Nonempty := by
    have hsub : {x | F x < s} ⊆ interior {x | F x ≤ s} :=
      interior_maximal (fun x (hx : F x < s) => hx.le) (isOpen_lt hFc continuous_const)
    have h2 := abs_lt.1 (hFr' z₀)
    rw [hηd, dist_self] at h2
    exact ⟨z₀, hsub (show F z₀ < s by linarith [h2.2, hs.1])⟩
  rw [← hc₁r]
  rcases finiteSurface_types o k hr hnorm hK with ⟨-, hS | ⟨hT, -⟩⟩ | ⟨-, hP | hC⟩
  · obtain ⟨Φ'⟩ := hS
    exact exists_disk_of_homeomorph_recognition Φ'.toHomeomorph
      (fun D' hD' hint' c' hc' hinj' hfr'' =>
        exists_disk_of_jordan_frontier_sphereTwo hD' hint' hc' hinj' hfr'') hD hint hc₁c hc₁i hfr
  · exfalso
    obtain ⟨Φ'⟩ := hT
    obtain ⟨u, -, hiso, hz⟩ := exists_endpoint_far_segment k hr2 hnorm (by linarith) hq0 hqnn hdist
      hdense
    exact Bundle.ContMDiffRiemannianMetric.false_of_nonneg_torus_of_endpoint_interval hdim k
      (two_le_coe_add_one_of_three_le hr) hnorm Φ'.symm hK hq0 hqnn hdist (by linarith)
      (γ := fun t => k.expMap (⟨z₀, t • u⟩ : TangentBundle (𝓡 2) Z)) hz
      (fun t ht t' ht' => hiso t ⟨ht.1, by linarith [ht.2]⟩ t' ⟨ht'.1, by linarith [ht'.2]⟩)
  · obtain ⟨φ⟩ := hP
    exact exists_disk_of_homeomorph_recognition φ
      (fun D' hD' hint' c' hc' hinj' hfr'' =>
        exists_disk_of_jordan_frontier_plane hD' hint' hc' hinj' hfr'') hD hint hc₁c hc₁i hfr
  · obtain ⟨φ⟩ := hC
    exact exists_disk_of_homeomorph_recognition
      (φ.trans ((AddCircle.homeomorphCircle one_ne_zero).prodCongr (Homeomorph.refl ℝ)))
      (fun D' hD' hint' c' hc' hinj' hfr'' =>
        exists_disk_of_jordan_frontier_cylinder hD' hint' hc' hinj' hfr'') hD hint hc₁c hc₁i hfr

/-- **LFR24 (the row).** Fix `0 < ε < 1/100`. There is `δ₀ > 0` (namely `ε²/24000000`) such that for
every LFR23 endpoint model with error `δ ≤ δ₀` and EVERY `0 < μ < 1/100` the function
`h = edgeModelCore F` (`F` from LFR02) is smooth near `B̄(z₀, 9)`, vanishes near `B̄(z₀, 1/2)`, lies in
`[0, 2]` on `r ≤ 1`, satisfies (LFR24.1) on `2.1 ≤ r ≤ 9`; every sublevel `D_s`, `s ∈ [3, 6]`, is a
smooth compact disk with boundary the level, between `B̄(z₀, s - μ)` and `B(z₀, s + μ)`; LFR23's SAME
outward field has `dh(V) > 1/2` on the collar `2.1 ≤ r ≤ 8`; the level `h = 4` is regular; and the
product enclosure (LFR24.2) holds. The metric is `k` throughout. -/
theorem finiteSurface_edge_model_core (o : ManifoldOrientation (𝓡 2) Z 2) {r : ℕ∞}
    (k : ContMDiffRiemannianMetric (𝓡 2) ((r : ℕ∞ω) + 1) E2 (TangentSpace (𝓡 2) : Z → Type _))
    (hr : 3 ≤ r)
    (hnorm : ∀ (x : Z) (w : TangentSpace (𝓡 2) x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (k.inner x w w)))
    (hK : ∀ x (v w : TangentSpace (𝓡 2) x), 0 ≤ k.sectionalCurvature x v w)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1 / 100) :
    ∃ δ₀ > 0, ∀ (z₀ : Z) (q : Z → ℝ) (δ : ℝ), 0 < δ → δ ≤ δ₀ → q z₀ = 0 →
      (∀ y ∈ closedBall z₀ 10, 0 ≤ q y) →
      (∀ y ∈ closedBall z₀ 10, ∀ y' ∈ closedBall z₀ 10, |dist (q y) (q y') - dist y y'| ≤ δ) →
      (∀ t ∈ Icc (0 : ℝ) 10, ∃ y ∈ closedBall z₀ 10, |q y - t| ≤ δ) →
      ∀ μ : ℝ, 0 < μ → μ < 1 / 100 →
      ∃ h : Z → ℝ,
        (∃ W : Set Z, IsOpen W ∧ closedBall z₀ 9 ⊆ W ∧ ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ h W) ∧
        (∃ O : Set Z, IsOpen O ∧ closedBall z₀ (1 / 2) ⊆ O ∧ EqOn h 0 O) ∧
        (∀ x, dist x z₀ ≤ 1 → h x ∈ Icc (0 : ℝ) 2) ∧
        (∀ x, 21 / 10 ≤ dist x z₀ → dist x z₀ ≤ 9 → |h x - dist x z₀| < μ ∧
          ∀ v ∈ k.finiteMinimizingDirectionsTo ({z₀} : Set Z) x, ∀ w : TangentSpace (𝓡 2) x,
            |mvfderiv (𝓡 2) h x w + k.inner x v w| ≤ ε / 25 * Real.sqrt (k.inner x w w)) ∧
        (∀ s ∈ Icc (3 : ℝ) 6,
          IsCompact {x | dist x z₀ < 9 ∧ h x ≤ s} ∧
          closedBall z₀ (s - μ) ⊆ {x | dist x z₀ < 9 ∧ h x ≤ s} ∧
          {x | dist x z₀ < 9 ∧ h x ≤ s} ⊆ ball z₀ (s + μ) ∧
          ∃ b : ClosedCell 2 → Z, Manifold.IsSmoothEmbedding (𝓡∂ 2) (𝓡 2) ∞ b ∧
            range b = {x | dist x z₀ < 9 ∧ h x ≤ s} ∧
            range (b ∘ cellBoundaryInclusion 2) = {x | dist x z₀ < 9 ∧ h x = s}) ∧
        (∃ V : (x : Z) → TangentSpace (𝓡 2) x,
          ContMDiff (𝓡 2) (𝓡 2).tangent ∞ (fun x => (⟨x, V x⟩ : TangentBundle (𝓡 2) Z)) ∧
          (∀ x, k.inner x (V x) (V x) < 2 ^ 2) ∧
          (∃ O : Set Z, IsOpen O ∧
            (fun x => infDist x ({z₀} : Set Z)) ⁻¹' Icc (1 / 2 : ℝ) (37 / 4) ⊆ O ∧
            ∀ x ∈ O, ∀ u ∈ k.finiteMinimizingDirectionsTo ({z₀} : Set Z) x,
              k.inner x (V x) u < -(3 / 4)) ∧
          ∀ x, 21 / 10 ≤ dist x z₀ → dist x z₀ ≤ 8 → 1 / 2 < mvfderiv (𝓡 2) h x (V x)) ∧
        (∀ x, dist x z₀ < 9 → h x = 4 → mvfderiv (𝓡 2) h x ≠ 0) ∧
        ∀ Δ : ℝ, 0 < Δ →
          {p : ℝ × Z | p.1 ∈ Ioo (-(6 * Δ)) (6 * Δ) ∧ dist p.2 z₀ < 9 ∧
              (p.1, Δ * h p.2) ∈ Icc (-(4 * Δ)) (4 * Δ) ×ˢ Iic (4 * Δ)} =
            Icc (-(4 * Δ)) (4 * Δ) ×ˢ {x | dist x z₀ < 9 ∧ h x ≤ 4} ∧
          Icc (-(4 * Δ)) (4 * Δ) ×ˢ {x | dist x z₀ < 9 ∧ h x ≤ 4} ⊆
            interior (Icc (-(9 / 2 * Δ)) (9 / 2 * Δ) ×ˢ {z | dist z z₀ ≤ 5}) := by
  have hε' : ε ≤ 1 := by linarith
  refine ⟨ε ^ 2 / 24000000, by positivity, fun z₀ q δ hδ hδ₀ hq0 hqnn hdist hdense μ hμ hμ1 => ?_⟩
  have : NeZero (Module.finrank ℝ E2) := ⟨by simp⟩
  have : ProperSpace Z := Manifold.properSpace_of_isRiemannianManifold (𝓡 2)
  have hr2 : 2 ≤ r := le_trans (by norm_num) hr
  have hdim : Module.finrank ℝ E2 = 2 := by simp
  have hε2 : ε ^ 2 ≤ 1 := by nlinarith
  have hδ1 : δ ≤ 1 / 9600 := hδ₀.trans (by linarith)
  ---------------------------------------------------------------- LFR02 with `ε` and `μ`
  set U : Set Z := {x | 1 / 2 < dist x z₀ ∧ dist x z₀ < 37 / 4} with hU
  set C : Set Z := {x | 3 / 4 ≤ dist x z₀ ∧ dist x z₀ ≤ 91 / 10} with hC
  have hUo : IsOpen U :=
    (isOpen_lt continuous_const (continuous_id.dist continuous_const)).inter
      (isOpen_lt (continuous_id.dist continuous_const) continuous_const)
  have hUY : U ⊆ ({z₀} : Set Z)ᶜ := fun x hx hxz => by
    rw [mem_singleton_iff] at hxz
    have := hx.1
    rw [hxz, dist_self] at this
    linarith
  have hCc : IsCompact C := (isCompact_closedBall z₀ (91 / 10)).of_isClosed_subset
    ((isClosed_le continuous_const (continuous_id.dist continuous_const)).inter
      (isClosed_le (continuous_id.dist continuous_const) continuous_const)) fun x hx => hx.2
  have hCU : C ⊆ U := fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hsqrt : 2 * Real.sqrt (600 * δ) ≤ min 1 ε / 100 := by
    have h1 : Real.sqrt (600 * δ) ≤ ε / 200 := by
      rw [show ε / 200 = Real.sqrt ((ε / 200) ^ 2) by rw [Real.sqrt_sq (by positivity)]]
      exact Real.sqrt_le_sqrt (by nlinarith)
    rw [min_eq_right hε']
    linarith
  obtain ⟨F, OF, hOF, hCOF, hFs, hFr, -, -, hFlip, -, -, hgrad⟩ :=
    exists_localized_distance_smoothing_lfr02 k hr2 hnorm hε isClosed_singleton
      (singleton_nonempty z₀) hUo hUY (fun x hx v hv v' hv' => by
        have hx₁ : 1 / 2 ≤ dist z₀ x := by rw [dist_comm]; exact hx.1.le
        have hx₂ : dist z₀ x ≤ 37 / 4 := by rw [dist_comm]; exact hx.2.le
        exact (sqrt_inner_sub_lt_of_endpoint_band k hr2 hnorm hK hδ (by linarith) hq0 hqnn hdist
          hdense hx₁ hx₂ hv hv').trans_le hsqrt) hCc hCU (e := μ) hμ
  have hFc : Continuous F := hFlip.continuous
  have hμ' : μ ≤ 1 / 100 := hμ1.le
  have hFr2 : ∀ x, |F x - (fun x => dist x z₀) x| < μ := fun x => by
    have h := hFr x
    rwa [infDist_singleton] at h
  have hA : ∀ x, 3 / 4 ≤ (fun x => dist x z₀) x → (fun x => dist x z₀) x ≤ 9 → x ∈ OF :=
    fun x h1 h2 => hCOF ⟨h1, by linarith [h2]⟩
  ---------------------------------------------------------------- LFR23's field
  obtain ⟨V, hV, hVR, O, hO, hAO, hOout, -⟩ :=
    exists_endpoint_field k hr2 hnorm hK hδ hδ1 hq0 hqnn hdist hdense
  have hdFV : ∀ x, 21 / 10 ≤ (fun x => dist x z₀) x → (fun x => dist x z₀) x ≤ 8 →
      1 / 2 < mvfderiv (𝓡 2) F x (V x) := by
    intro x h1 h2
    have hxO : x ∈ O := hAO (show infDist x ({z₀} : Set Z) ∈ Icc (1 / 2 : ℝ) (37 / 4) by
      rw [infDist_singleton]; exact ⟨by linarith [h1], by linarith [h2]⟩)
    obtain ⟨v, hv⟩ := (k.finiteMinimizingDirectionsTo_nonempty_isCompact hr2 hnorm
      isClosed_singleton (singleton_nonempty z₀) x).1
    exact one_half_lt_mvfderiv_of_gradient k hε' (hgrad x (hA x (by linarith) (by linarith)) v hv
      (V x)) (hVR x) (hOout x hxO v hv)
  have hcpt7 : IsCompact {x : Z | (fun x => dist x z₀) x ≤ 7} := isCompact_closedBall z₀ 7
  refine ⟨edgeModelCore F, ?_, edgeModelCore_eqOn_zero hFc hμ' hFr2,
    fun x hx => edgeModelCore_mem_Icc hμ' hFr2 hx, fun x h1 h2 => ⟨abs_edgeModelCore_sub_lt hμ' hFr2 h1,
      fun v hv w => by
        rw [mvfderiv_edgeModelCore_eq hFc hμ' hFr2 h1]
        exact hgrad x (hA x (by linarith) h2) v hv w⟩, fun s hs => ?_,
    ⟨V, hV, hVR, ⟨O, hO, hAO, hOout⟩, fun x h1 h2 => edgeModelCore_field hFc hμ' hFr2 V hdFV h1 h2⟩,
    fun x hx hx4 => mvfderiv_edgeModelCore_ne_zero hFc hμ' hFr2 V hdFV (s := 4)
      ⟨by norm_num, by norm_num⟩ hx hx4,
    fun Δ hΔ => edgeModelCore_product_enclosure hΔ (continuous_id.dist continuous_const) hμ' hFr2⟩
  · obtain ⟨W, hW, hW9, hWs⟩ := contMDiffOn_edgeModelCore hFc hOF hFs hA hμ' hFr2
    exact ⟨W, hW, hW9, hWs⟩
  · have hD : edgeCoreSublevel (fun x => dist x z₀) F s = {x | F x ≤ s} :=
      edgeCoreSublevel_eq hμ' hFr2 hs
    have hcpt : IsCompact (edgeCoreSublevel (fun x => dist x z₀) F s) := by
      rw [hD]
      refine (isCompact_closedBall z₀ 7).of_isClosed_subset (isClosed_le hFc continuous_const)
        fun x hx => ?_
      have h2 := abs_lt.1 (hFr2 x)
      change F x ≤ s at hx
      change dist x z₀ ≤ 7
      change -μ < F x - dist x z₀ ∧ F x - dist x z₀ < μ at h2
      linarith [h2.1, hs.2]
    obtain ⟨φ, hφ, hφr, hφb⟩ := exists_disk_sublevel_of_smoothing o k hr hnorm hK hδ hδ1 hq0 hqnn
      hdist hdense hFc hμ' hFr hOF hFs (fun x h1 h2 => hCOF ⟨h1, h2⟩) hε' hgrad hs
    obtain ⟨b, hb, hbr, hbb⟩ := edgeCoreSublevel_smooth_disk hdim hFc hOF hFs hA hμ' hFr2 hcpt7 V
      hV.contMDiffOn hdFV hs hφ.continuous hφ.injective (hφr.trans hD.symm) hφb
    refine ⟨hcpt, subset_edgeCoreSublevel hμ' hFr2 hs, edgeCoreSublevel_subset hμ' hFr2 hs, b, hb,
      hbr, ?_⟩
    rw [hbb]
    exact (edgeCoreLevel_eq hμ' hFr2 hs).symm

end DifferentialGeometry.Geometry.Collapse
