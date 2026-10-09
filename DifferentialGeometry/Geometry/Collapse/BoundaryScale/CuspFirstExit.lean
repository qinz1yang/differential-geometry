import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspBoundaryInverse
import DifferentialGeometry.Geometry.Collapse.BoundaryCollar.CollarLevelTorus
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspProductLowerLength
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspMetricEquivalence
import DifferentialGeometry.Geometry.Metric.Distance.InducedMetricSpace
import Mathlib.Topology.EMetricSpace.BoundedVariation

/-!
# First exit from the cusp collar (statement E of the boundary-geometry route)

For a cusp embedding `e : CuspEmbedding W g K δ X`, `z` the height and `m = √(1 - δ)`
(interfaces `build-logs/scratch/BDY-FILL/BoundaryInterfaces.lean:33–60`):

* E.1 `CuspEmbedding.isOpen_image_height_lt`: `U_h = e(T² × [0, h))` is open for `h ≤ 100`;
* E.2 `CuspEmbedding.frontier_image_height_lt`: `frontier U_h = e(T² × {h})` for `0 < h < 100`;
* lift form `CuspEmbedding.ofReal_mul_abs_height_sub_le_pathELength`: along a `C¹` curve of the
  cusp domain, `m |Δz| ≤ length_g (e ∘ c)` (pointwise `‖dz‖_g ≤ 1/m`, then integration);
* `CuspEmbedding.exists_exit_le_pathELength`: a `C¹` curve leaving `e{α < z < β}` (`β < 100`)
  meets `e{z = α}` or `e{z = β}` at a cost `m |z_exit - z_start|`;
* E.3 `CuspEmbedding.ofReal_le_riemannianEDistOf_of_not_mem_image_height_lt`: for `y ∉ U_h`,
  `d_g(e p, y) ≥ m (h - z(p))` (no hypothesis on `δ`); hence every curve (rectifiable or not)
  from `e p` to `W \ U_h` has length at least `m (h - z(p))`;
* E.4 `NearlyCuspidalBoundary.exists_collar_coordinate`: a point at distance `≤ b` from `∂W` is a
  collar point of height `≤ b / m` (interface erratum: `0 ≤ b` is added; for `b < 0` a boundary
  point has distance `0 ≤ ofReal b` but no height in `[0, b / m]`).

The curves are those of the Riemannian distance (`C¹` on `[0, 1]`); no almost-everywhere gradient
formula is used. The first exit time is the infimum of the closed set of exit times; the curve up
to that time lies in the open collar and lifts by `CuspEmbedding.exists_lift`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function Bundle Manifold MeasureTheory DifferentialGeometry
open DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.Geometry.Collapse

universe u

theorem continuous_cusp_height : Continuous (fun p : CuspHalfSpace => p.2.val 0) := by
  fun_prop

/-- E.1: every height sub-band `e(T² × [0, h))`, `h ≤ 100`, is open (height `0` included). -/
theorem CuspEmbedding.isOpen_image_height_lt {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ} {X : Set W.Carrier}
    (e : CuspEmbedding W g K δ X) {h : ℝ} (hh : h ≤ cuspDepth) :
    IsOpen (e.toFun '' {p : CuspHalfSpace | p.2.val 0 < h}) :=
  e.isOpen_image (isOpen_lt continuous_cusp_height continuous_const)
    fun _ hp => lt_of_lt_of_le hp hh

/-- E.2: the frontier of `e(T² × [0, h))` is the level torus `e(T² × {h})`, `0 < h < 100`. -/
theorem CuspEmbedding.frontier_image_height_lt {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ} {X : Set W.Carrier}
    (e : CuspEmbedding W g K δ X) {h : ℝ} (hh0 : 0 < h) (hh : h < cuspDepth) :
    frontier (e.toFun '' {p : CuspHalfSpace | p.2.val 0 < h}) =
      e.toFun '' {p : CuspHalfSpace | p.2.val 0 = h} := by
  have hU := e.isOpen_image_height_lt hh.le
  have hK : IsClosed (e.toFun '' {p : CuspHalfSpace | 0 ≤ p.2.val 0 ∧ p.2.val 0 ≤ h}) :=
    (e.isCompact_image_band hh).isClosed
  rw [hU.frontier_eq]
  ext y
  constructor
  · rintro ⟨hcl, hnot⟩
    have hsub : e.toFun '' {p : CuspHalfSpace | p.2.val 0 < h} ⊆
        e.toFun '' {p : CuspHalfSpace | 0 ≤ p.2.val 0 ∧ p.2.val 0 ≤ h} :=
      image_mono fun p hp => ⟨p.2.2, (show p.2.val 0 < h from hp).le⟩
    obtain ⟨q, ⟨-, hqh⟩, rfl⟩ := hK.closure_subset_iff.mpr hsub hcl
    refine ⟨q, ?_, rfl⟩
    rcases hqh.lt_or_eq with hlt | heq
    · exact absurd ⟨q, hlt, rfl⟩ hnot
    · exact heq
  · rintro ⟨q, hq, rfl⟩
    have hq' : q.2.val 0 = h := hq
    have hqd : q ∈ cuspDomain := by
      change q.2.val 0 < cuspDepth
      rw [hq']
      exact hh
    refine ⟨?_, ?_⟩
    · -- approach `q` vertically from below
      let c : ℝ → CuspHalfSpace := fun s => (q.1, halfSpaceOneLift s)
      have hc : Continuous c := by
        refine continuous_const.prodMk ?_
        unfold halfSpaceOneLift
        fun_prop
      have hcq : c h = q := by
        refine Prod.ext rfl ?_
        change halfSpaceOneLift h = q.2
        rw [← hq']
        exact halfSpaceOneLift_val_zero_self q.2
      have hcont : ContinuousAt (e.toFun ∘ c) h := by
        refine ContinuousAt.comp ?_ hc.continuousAt
        rw [hcq]
        exact e.contMDiffOn.continuousOn.continuousAt (isOpen_cuspDomain.mem_nhds hqd)
      have htend : Tendsto (e.toFun ∘ c) (𝓝[<] h) (𝓝 (e.toFun q)) := by
        have h1 := hcont.tendsto
        rw [comp_apply, hcq] at h1
        exact h1.mono_left nhdsWithin_le_nhds
      refine mem_closure_of_tendsto htend ?_
      filter_upwards [Ioo_mem_nhdsLT hh0] with s hs
      refine ⟨c s, ?_, rfl⟩
      change (halfSpaceOneLift s).1 0 < h
      rw [halfSpaceOneLift_val_zero, max_eq_left hs.1.le]
      exact hs.2
    · rintro ⟨q', hq'h, hqq'⟩
      have hq'd : q' ∈ cuspDomain := lt_trans (show q'.2.val 0 < h from hq'h) hh
      have := e.injOn_cuspDomain hq'd hqd hqq'
      rw [this] at hq'h
      exact absurd hq' (ne_of_lt hq'h)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- Height bound along a lifted curve (pointwise `‖dz‖_g ≤ 1/√(1-δ)`, integrated):
`√(1 - δ) |z(c b) - z(c a)| ≤ length_g (e ∘ c)` on `[a, b]`. -/
theorem CuspEmbedding.ofReal_mul_abs_height_sub_le_pathELength {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ} {X : Set W.Carrier}
    (e : CuspEmbedding W g K δ X) {c : ℝ → CuspHalfSpace} {a b : ℝ} (hab : a ≤ b)
    (hc : ContMDiffOn 𝓘(ℝ, ℝ) halfCollarModel 1 c (Icc a b))
    (hdom : ∀ t ∈ Icc a b, c t ∈ cuspDomain) :
    letI : RiemannianBundle (fun x : W.Carrier => TangentSpace W.model x) :=
      ⟨g.toRiemannianMetric⟩
    ENNReal.ofReal (Real.sqrt (1 - δ) * |(c b).2.val 0 - (c a).2.val 0|) ≤
      pathELength W.model (e.toFun ∘ c) a b := by
  let : RiemannianBundle (fun x : W.Carrier => TangentSpace W.model x) := ⟨g.toRiemannianMetric⟩
  rcases le_or_gt 1 δ with hδ | hδ
  · rw [Real.sqrt_eq_zero'.mpr (by linarith), zero_mul, ENNReal.ofReal_zero]
    exact bot_le
  let A : ℝ → ℝ := fun t => (mfderiv 𝓘(ℝ, ℝ) halfCollarModel c t 1).2 0
  have hdiff : ∀ t ∈ Ioo a b, MDifferentiableAt 𝓘(ℝ, ℝ) halfCollarModel c t :=
    fun t ht => (hc.contMDiffAt (Icc_mem_nhds ht.1 ht.2)).mdifferentiableAt one_ne_zero
  have hheight : ENNReal.ofReal |(c b).2.val 0 - (c a).2.val 0| ≤
      ∫⁻ t in Ioo a b, ENNReal.ofReal |A t| := by
    have hζ : ContDiffOn ℝ 1 (fun s => (c s).2.val 0) (Icc a b) := by
      have h1 : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) 1
          ((EuclideanSpace.proj (0 : Fin 1) : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ) ∘
            (𝓡∂ 1) ∘ Prod.snd ∘ c) (Icc a b) :=
        (ContinuousLinearMap.contMDiff _).comp_contMDiffOn
          ((𝓡∂ 1).contMDiff.comp_contMDiffOn (contMDiff_snd.comp_contMDiffOn hc))
      exact contMDiffOn_iff_contDiffOn.mp h1
    have h := enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc hζ hab
    rw [← restrict_Ioo_eq_restrict_Icc] at h
    rw [Real.enorm_eq_ofReal_abs] at h
    refine h.trans (setLIntegral_mono' measurableSet_Ioo fun t ht => ?_)
    have hsnd := (hasMFDerivAt_snd (c t)).comp t (hdiff t ht).hasMFDerivAt
    have hderiv := (hasDerivAt_val_zero_of_hasMFDerivAt hsnd).deriv
    change ‖deriv (fun s => (c s).2.val 0) t‖ₑ ≤ _
    rw [show (fun s => (c s).2.val 0) = fun s => ((Prod.snd ∘ c) s).val 0 from rfl, hderiv,
      Real.enorm_eq_ofReal_abs]
    rfl
  have hpt : ∀ t ∈ Ioo a b, ENNReal.ofReal (Real.sqrt (1 - δ)) * ENNReal.ofReal |A t| ≤
      ‖mfderiv 𝓘(ℝ, ℝ) W.model (e.toFun ∘ c) t 1‖ₑ := by
    intro t ht
    have htI : t ∈ Icc a b := Ioo_subset_Icc_self ht
    have hed : MDifferentiableAt halfCollarModel W.model e.toFun (c t) :=
      (e.contMDiffOn.contMDiffAt (isOpen_cuspDomain.mem_nhds (hdom t htI))).mdifferentiableAt
        (by simp)
    rw [mfderiv_comp t hed (hdiff t ht)]
    set v := mfderiv 𝓘(ℝ, ℝ) halfCollarModel c t 1 with hv
    have hz := e.abs_height_deriv_le hδ (hdom t htI) v
    rw [← ofReal_norm, norm_eq_sqrt_real_inner, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    change Real.sqrt (1 - δ) * |v.2 0| ≤
      Real.sqrt (g.inner (e.toFun (c t)) (mfderiv halfCollarModel W.model e.toFun (c t) v)
        (mfderiv halfCollarModel W.model e.toFun (c t) v))
    have hs : 0 < Real.sqrt (1 - δ) := Real.sqrt_pos.mpr (by linarith)
    calc Real.sqrt (1 - δ) * |v.2 0| ≤ Real.sqrt (1 - δ) * ((Real.sqrt (1 - δ))⁻¹ *
          Real.sqrt (g.inner (e.toFun (c t)) (mfderiv halfCollarModel W.model e.toFun (c t) v)
            (mfderiv halfCollarModel W.model e.toFun (c t) v))) := by gcongr
      _ = _ := by rw [← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul]
  rw [ENNReal.ofReal_mul (Real.sqrt_nonneg _), pathELength_eq_lintegral_mfderiv_Ioo]
  calc ENNReal.ofReal (Real.sqrt (1 - δ)) * ENNReal.ofReal |(c b).2.val 0 - (c a).2.val 0|
      ≤ ENNReal.ofReal (Real.sqrt (1 - δ)) * ∫⁻ t in Ioo a b, ENNReal.ofReal |A t| := by
        gcongr
    _ ≤ ∫⁻ t in Ioo a b, ENNReal.ofReal (Real.sqrt (1 - δ)) * ENNReal.ofReal |A t| :=
        lintegral_const_mul_le _ _
    _ ≤ ∫⁻ t in Ioo a b, ‖mfderiv 𝓘(ℝ, ℝ) W.model (e.toFun ∘ c) t 1‖ₑ :=
        setLIntegral_mono' measurableSet_Ioo hpt

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- **First exit.** A `C¹` curve starting at `e p`, `α < z(p) < β < 100`, and ending outside
`e{α < z < β}` reaches a collar point `e q` of height `α` or `β`, and its length is at least
`√(1 - δ) |z(q) - z(p)|`. -/
theorem CuspEmbedding.exists_exit_le_pathELength {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ} {X : Set W.Carrier}
    (e : CuspEmbedding W g K δ X) {γ : ℝ → W.Carrier}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) W.model 1 γ (Icc 0 1)) {α β : ℝ} (hβ : β < cuspDepth)
    {p : CuspHalfSpace} (hpα : α < p.2.val 0) (hpβ : p.2.val 0 < β) (h0 : γ 0 = e.toFun p)
    (h1 : γ 1 ∉ e.toFun '' {q : CuspHalfSpace | α < q.2.val 0 ∧ q.2.val 0 < β}) :
    letI : RiemannianBundle (fun x : W.Carrier => TangentSpace W.model x) :=
      ⟨g.toRiemannianMetric⟩
    ∃ q ∈ cuspDomain, (q.2.val 0 = α ∨ q.2.val 0 = β) ∧
      ENNReal.ofReal (Real.sqrt (1 - δ) * |q.2.val 0 - p.2.val 0|) ≤
        pathELength W.model γ 0 1 := by
  let : RiemannianBundle (fun x : W.Carrier => TangentSpace W.model x) := ⟨g.toRiemannianMetric⟩
  set V : Set CuspHalfSpace := {q | α < q.2.val 0 ∧ q.2.val 0 < β} with hV
  have hVo : IsOpen V := (isOpen_lt continuous_const continuous_cusp_height).inter
    (isOpen_lt continuous_cusp_height continuous_const)
  have hVd : V ⊆ cuspDomain := fun q hq => lt_trans hq.2 hβ
  have hU : IsOpen (e.toFun '' V) := e.isOpen_image hVo hVd
  have hK : IsClosed (e.toFun '' {q : CuspHalfSpace | α ≤ q.2.val 0 ∧ q.2.val 0 ≤ β}) :=
    (e.isCompact_image_band hβ).isClosed
  have hpd : p ∈ cuspDomain := lt_trans hpβ hβ
  have hγc : ContinuousOn γ (Icc 0 1) := hγ.continuousOn
  -- the first exit time
  set A : Set ℝ := Icc 0 1 ∩ γ ⁻¹' (e.toFun '' V)ᶜ with hA
  have hAc : IsClosed A := hγc.preimage_isClosed_of_isClosed isClosed_Icc hU.isClosed_compl
  have h1A : (1 : ℝ) ∈ A := ⟨⟨zero_le_one, le_rfl⟩, h1⟩
  have hAne : A.Nonempty := ⟨1, h1A⟩
  have hAbdd : BddBelow A := ⟨0, fun t ht => ht.1.1⟩
  set s := sInf A with hs
  have hsA : s ∈ A := hAc.csInf_mem hAne hAbdd
  have hs1 : s ≤ 1 := csInf_le hAbdd h1A
  have hbefore : ∀ t ∈ Ico 0 s, γ t ∈ e.toFun '' V := by
    intro t ht
    by_contra hcon
    exact absurd (csInf_le hAbdd ⟨⟨ht.1, ht.2.le.trans hs1⟩, hcon⟩) (not_le.mpr ht.2)
  have hs0 : 0 < s := by
    rcases hsA.1.1.lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      apply hsA.2
      rw [← heq, h0]
      exact ⟨p, ⟨hpα, hpβ⟩, rfl⟩
  -- the exit point
  have hcl : γ s ∈ closure (e.toFun '' V) := by
    have hcw : ContinuousWithinAt γ (Ico 0 s) s :=
      (hγc s hsA.1).mono (fun t ht => ⟨ht.1, ht.2.le.trans hs1⟩)
    have hmem : s ∈ closure (Ico 0 s) := by
      rw [closure_Ico hs0.ne]
      exact ⟨hs0.le, le_rfl⟩
    have himg : γ '' Ico 0 s ⊆ e.toFun '' V := by
      rintro _ ⟨t, ht, rfl⟩
      exact hbefore t ht
    exact closure_mono himg (hcw.mem_closure_image hmem)
  have hsub : e.toFun '' V ⊆ e.toFun '' {q : CuspHalfSpace | α ≤ q.2.val 0 ∧ q.2.val 0 ≤ β} :=
    image_mono fun q hq => ⟨hq.1.le, hq.2.le⟩
  obtain ⟨q, ⟨hqα, hqβ⟩, hqs⟩ := hK.closure_subset_iff.mpr hsub hcl
  have hqd : q ∈ cuspDomain := lt_of_le_of_lt hqβ hβ
  have hqside : q.2.val 0 = α ∨ q.2.val 0 = β := by
    by_contra hcon
    push Not at hcon
    exact hsA.2 (hqs ▸ ⟨q, ⟨lt_of_le_of_ne hqα hcon.1.symm, lt_of_le_of_ne hqβ hcon.2⟩, rfl⟩)
  -- the lift up to the exit time
  have hmaps : MapsTo γ (Icc 0 s) (e.toFun '' cuspDomain) := by
    intro t ht
    rcases ht.2.lt_or_eq with hlt | heq
    · exact image_mono hVd (hbefore t ⟨ht.1, hlt⟩)
    · rw [heq, ← hqs]
      exact ⟨q, hqd, rfl⟩
  obtain ⟨c, hc, hcd, hce⟩ := e.exists_lift (hγ.mono (Icc_subset_Icc le_rfl hs1)) hmaps
  have hc0 : c 0 = p := e.injOn_cuspDomain (hcd ⟨le_rfl, hs0.le⟩) hpd
    ((hce 0 ⟨le_rfl, hs0.le⟩).trans h0)
  have hcs : c s = q := e.injOn_cuspDomain (hcd ⟨hs0.le, le_rfl⟩) hqd
    ((hce s ⟨hs0.le, le_rfl⟩).trans hqs.symm)
  refine ⟨q, hqd, hqside, ?_⟩
  have hlen := e.ofReal_mul_abs_height_sub_le_pathELength hs0.le hc hcd
  rw [hc0, hcs] at hlen
  calc _ ≤ pathELength W.model (e.toFun ∘ c) 0 s := hlen
    _ = pathELength W.model γ 0 s := pathELength_congr fun t ht => hce t ht
    _ ≤ pathELength W.model γ 0 1 := pathELength_mono le_rfl hs1

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- E.3 (first exit, distance form): leaving `e(T² × [0, h))` from height `z(p) < h` costs
`√(1 - δ) (h - z(p))`; no hypothesis on `δ`. -/
theorem CuspEmbedding.ofReal_le_riemannianEDistOf_of_not_mem_image_height_lt
    {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ}
    {X : Set W.Carrier} (e : CuspEmbedding W g K δ X) {h : ℝ} (hh : h < cuspDepth)
    {p : CuspHalfSpace} (hph : p.2.val 0 < h) {y : W.Carrier}
    (hy : y ∉ e.toFun '' {q : CuspHalfSpace | q.2.val 0 < h}) :
    ENNReal.ofReal (Real.sqrt (1 - δ) * (h - p.2.val 0)) ≤ riemannianEDistOf g (e.toFun p) y := by
  let : RiemannianBundle (fun x : W.Carrier => TangentSpace W.model x) := ⟨g.toRiemannianMetric⟩
  refine le_of_forall_gt fun r hr => ?_
  change Manifold.riemannianEDist W.model (e.toFun p) y < r at hr
  obtain ⟨γ, hγ0, hγ1, hγ, hlen⟩ := Manifold.exists_lt_of_riemannianEDist_lt hr
  have hy' : γ 1 ∉ e.toFun '' {q : CuspHalfSpace | -1 < q.2.val 0 ∧ q.2.val 0 < h} := by
    rw [hγ1]
    rintro ⟨q, hq, hqy⟩
    exact hy ⟨q, hq.2, hqy⟩
  obtain ⟨q, -, hqside, hq⟩ := e.exists_exit_le_pathELength hγ hh
    (lt_of_lt_of_le neg_one_lt_zero p.2.2) hph hγ0 hy'
  rcases hqside with hq1 | hqh
  · exact absurd hq1 (ne_of_gt (lt_of_lt_of_le neg_one_lt_zero q.2.2))
  · rw [hqh, abs_of_nonneg (by linarith)] at hq
    exact lt_of_le_of_lt hq hlen

/-- E.3, curve form (the reviewer's wording): every curve from `e p` to a point outside
`e(T² × [0, h))`, measured by its variation for the distance `d_g` (no regularity assumed), has
length at least `√(1 - δ) (h - z(p))`. -/
theorem CuspEmbedding.ofReal_le_eVariationOn_of_not_mem_image_height_lt {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ} {X : Set W.Carrier}
    (e : CuspEmbedding W g K δ X) {h : ℝ} (hh : h < cuspDepth) {p : CuspHalfSpace}
    (hph : p.2.val 0 < h) {γ : ℝ → W.Carrier} {a b : ℝ} (hab : a ≤ b) (hγa : γ a = e.toFun p)
    (hγb : γ b ∉ e.toFun '' {q : CuspHalfSpace | q.2.val 0 < h}) :
    letI := inducedEMetricSpace g
    ENNReal.ofReal (Real.sqrt (1 - δ) * (h - p.2.val 0)) ≤ eVariationOn γ (Icc a b) := by
  let := inducedEMetricSpace g
  calc _ ≤ riemannianEDistOf g (e.toFun p) (γ b) :=
        e.ofReal_le_riemannianEDistOf_of_not_mem_image_height_lt hh hph hγb
    _ = edist (γ a) (γ b) := by rw [inducedEMetricSpace_edist, hγa]
    _ ≤ eVariationOn γ (Icc a b) := eVariationOn.edist_le γ ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩

/-- E.4 (localisation): a point within `b ≥ 0` of `∂W` is a collar point of height
`≤ b / √(1 - δ)`. (Interface erratum: without `0 ≤ b` the statement fails at boundary points.) -/
theorem NearlyCuspidalBoundary.exists_collar_coordinate {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ}
    (B : NearlyCuspidalBoundary W g K δ) (hδ : δ < 1) {b : ℝ} (hb0 : 0 ≤ b)
    (hb : b / Real.sqrt (1 - δ) < cuspDepth) {q : W.Carrier}
    (hq : distanceToBoundary W g q ≤ ENNReal.ofReal b) :
    ∃ i, ∃ x : Torus, ∃ z₁ : ℝ, 0 ≤ z₁ ∧ z₁ ≤ b / Real.sqrt (1 - δ) ∧
      (B.collar i).toFun (x, halfSpaceOneLift z₁) = q := by
  set m := Real.sqrt (1 - δ) with hm
  have hmpos : 0 < m := Real.sqrt_pos.mpr (by linarith)
  set h₀ := b / m with hh₀
  have hh₀0 : 0 ≤ h₀ := div_nonneg hb0 hmpos.le
  by_contra H
  push Not at H
  have hchoice : ∀ i, ∃ hi : ℝ, h₀ < hi ∧ hi < cuspDepth ∧
      q ∉ (B.collar i).toFun '' {p : CuspHalfSpace | p.2.val 0 < hi} := by
    intro i
    have hmid : h₀ < (h₀ + cuspDepth) / 2 ∧ (h₀ + cuspDepth) / 2 < cuspDepth :=
      ⟨by linarith, by linarith⟩
    by_cases hqi : q ∈ (B.collar i).toFun '' cuspDomain
    · obtain ⟨p, hpd, hpq⟩ := hqi
      have hpz : h₀ < p.2.val 0 := by
        by_contra hle
        push Not at hle
        refine H i p.1 (p.2.val 0) p.2.2 hle ?_
        rw [halfSpaceOneLift_val_zero_self]
        exact hpq
      refine ⟨min (p.2.val 0) ((h₀ + cuspDepth) / 2), lt_min hpz hmid.1,
        lt_of_le_of_lt (min_le_right _ _) hmid.2, ?_⟩
      rintro ⟨p', hp', hp'q⟩
      have hp'z : p'.2.val 0 < min (p.2.val 0) ((h₀ + cuspDepth) / 2) := hp'
      have hp'd : p' ∈ cuspDomain := lt_trans (lt_of_lt_of_le hp'z (min_le_right _ _)) hmid.2
      have := (B.collar i).injOn_cuspDomain hp'd hpd (hp'q.trans hpq.symm)
      rw [this] at hp'z
      exact absurd (lt_of_lt_of_le hp'z (min_le_left _ _)) (lt_irrefl _)
    · refine ⟨(h₀ + cuspDepth) / 2, hmid.1, hmid.2, ?_⟩
      rintro ⟨p', hp', hp'q⟩
      exact hqi ⟨p', lt_trans (show p'.2.val 0 < _ from hp') hmid.2, hp'q⟩
  choose hi hhi using hchoice
  have hne : (Finset.univ : Finset (Fin B.count)).Nonempty := ⟨⟨0, B.count_pos⟩, Finset.mem_univ _⟩
  set hs := Finset.univ.inf' hne hi with hhs
  have hs_le : ∀ i, hs ≤ hi i := fun i => Finset.inf'_le _ (Finset.mem_univ i)
  have hs_gt : h₀ < hs := (Finset.lt_inf'_iff hne).mpr fun i _ => (hhi i).1
  have hs_lt : hs < cuspDepth := lt_of_le_of_lt (hs_le ⟨0, B.count_pos⟩) (hhi _).2.1
  have hs0 : 0 < hs := lt_of_le_of_lt hh₀0 hs_gt
  have hlow : ENNReal.ofReal (m * hs) ≤ distanceToBoundary W g q := by
    refine le_iInf fun w => ?_
    have hw : (w : W.Carrier) ∈ ⋃ i, B.component i := by rw [B.covers]; exact w.2
    obtain ⟨i, hwi⟩ := mem_iUnion.mp hw
    rw [← (B.collar i).boundary_image] at hwi
    obtain ⟨t, ht⟩ := hwi
    have ht' : (B.collar i).toFun (t, halfZero) = w := ht
    have h0 : (t, halfZero).2.val 0 = 0 := rfl
    have hqU : q ∉ (B.collar i).toFun '' {p : CuspHalfSpace | p.2.val 0 < hs} := by
      rintro ⟨p, hp, hpq⟩
      exact (hhi i).2.2 ⟨p, lt_of_lt_of_le hp (hs_le i), hpq⟩
    have hd := (B.collar i).ofReal_le_riemannianEDistOf_of_not_mem_image_height_lt hs_lt
      (p := (t, halfZero)) (by rw [h0]; exact hs0) hqU
    rw [h0, sub_zero, ht'] at hd
    rw [riemannianEDistOf_comm]
    exact hd
  have hlt : ENNReal.ofReal b < ENNReal.ofReal (m * hs) := by
    rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)]
    have := mul_lt_mul_of_pos_left hs_gt hmpos
    rwa [hh₀, mul_div_cancel₀ _ hmpos.ne'] at this
  exact absurd (hlow.trans hq) (not_le.mpr hlt)

end DifferentialGeometry.Geometry.Collapse
