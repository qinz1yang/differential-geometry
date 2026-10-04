import DifferentialGeometry.Topology.Manifold.FiberHeightCoordinate
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.Algebra.LieGroup

/-!
# LC59: smooth interior straightening of a continuous graph

Blueprint LC59 (`master207A.tex:23320`). Let `X` be a compact boundaryless smooth manifold,
`h : X → ℝ` CONTINUOUS (no smoothness), `a < c < r` and `c < h`. With the smooth structure of
`X × ℝ` there is a fibre-preserving diffeomorphism `P` of the open sets `X × (a, r)` and
`Ω_h = {(x, u) : a < u < h x}`, the identity for `u ≤ c` and strictly increasing on fibres.

Proof (blueprint A:23343–23395, with one simplification of the majorant). Instead of the
partition-of-unity majorant `m > (h - u)⁻¹`, take a smooth `f ≥ 0` with support exactly the open
subgraph `{u < h x}` (Mathlib `IsOpen.exists_contMDiff_support_eq`) and the weight
`w = 1 + χ(u - c) / f` (`χ` = `Real.smoothTransition`). Along a fibre `f` vanishes at `u = h x`
and is Lipschitz, so `f ≤ K (h x - u)` and `∫^{h x} w = ∞` (logarithm). The height coordinate
`Q(x, u) = c + ∫_c^u w(x, s) ds` is smooth on `{u < h x}` (`contMDiffOn_fiberIntegral`), equals
`u` for `u ≤ c`, has `∂_u Q = w ≥ 1`, and maps each fibre `(-∞, h x)` onto `ℝ`; so
`z ↦ (z.1, Q z)` is an injective local diffeomorphism onto `X × ℝ` (inverse function theorem),
i.e. a partial diffeomorphism `Q̂_h` (`exists_openSubgraph_heightCoordinate`). The same for the
constant height `r` gives `Q̂_r`, and `P = Q̂_h⁻¹ ∘ Q̂_r` (`exists_openGraph_straightening`).

The blueprint's upper bounds `h < b`, `r < b` are not used (strengthening); the verbatim form is
the `example` at the end. The level is called `X` (`Σ` is reserved syntax).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function MeasureTheory
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

/-! ### The fibre estimate: the weight is not integrable up to the zero of `f` -/

/-- **Divergence of the fibre integral.** If `g` is `C¹`, positive on `(-∞, H)` and `g H = 0`,
`c < H`, then `u ↦ c + ∫_c^u (1 + χ(s - c) / g s) ds` is unbounded above on `[c, H)`. -/
theorem exists_lt_add_integral_weight {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) {c H : ℝ} (hcH : c < H)
    (hpos : ∀ s < H, 0 < g s) (hH : g H = 0) (B : ℝ) :
    ∃ u, c ≤ u ∧ u < H ∧
      B < c + ∫ s in c..u, (1 + Real.smoothTransition (s - c) / g s) := by
  set w : ℝ → ℝ := fun s => 1 + Real.smoothTransition (s - c) / g s with hw
  have hwc : ContinuousOn w (Iio H) := by
    refine continuousOn_const.add ?_
    refine ContinuousOn.div ?_ hg.continuous.continuousOn fun s hs => (hpos s hs).ne'
    exact (Real.smoothTransition.continuous.comp (continuous_id.sub continuous_const)).continuousOn
  have hint : ∀ u v, u < H → v < H → IntervalIntegrable w volume u v := by
    intro u v hu hv
    refine (hwc.mono fun s hs => ?_).intervalIntegrable
    rcases le_total u v with huv | huv
    · rw [uIcc_of_le huv] at hs
      exact lt_of_le_of_lt hs.2 hv
    · rw [uIcc_of_ge huv] at hs
      exact lt_of_le_of_lt hs.2 hu
  set s₀ := (c + H) / 2 with hs₀
  have hcs₀ : c < s₀ := by rw [hs₀]; linarith
  have hs₀H : s₀ < H := by rw [hs₀]; linarith
  obtain ⟨K, hK⟩ := hg.contDiffOn.exists_lipschitzOnWith one_ne_zero (convex_Icc s₀ H)
    (isCompact_Icc (a := s₀) (b := H))
  set K' : ℝ := (K : ℝ) + 1 with hK'
  have hK'pos : 0 < K' := by rw [hK']; positivity
  have hgle : ∀ s ∈ Icc s₀ H, g s ≤ K' * (H - s) := by
    intro s hs
    have h1 := hK.dist_le_mul s hs H ⟨hs₀H.le, le_rfl⟩
    rw [Real.dist_eq, Real.dist_eq, hH, sub_zero, abs_sub_comm s H,
      abs_of_nonneg (show (0 : ℝ) ≤ H - s by linarith [hs.2])] at h1
    have h2 : (K : ℝ) * (H - s) ≤ K' * (H - s) := by
      rw [hK']; nlinarith [hs.2]
    exact (le_abs_self _).trans (h1.trans h2)
  set κ := Real.smoothTransition (s₀ - c) with hκ
  have hκpos : 0 < κ := Real.smoothTransition.pos_of_pos (by linarith)
  have hwlow : ∀ s ∈ Icc s₀ H, s < H → κ / K' * (H - s)⁻¹ ≤ w s := by
    intro s hs hsH
    have hgs : 0 < g s := hpos s hsH
    have hHs : 0 < H - s := by linarith
    have hχ : κ ≤ Real.smoothTransition (s - c) :=
      Real.smoothTransition.monotone (by linarith [hs.1])
    have h1 : κ / K' * (H - s)⁻¹ = κ / (K' * (H - s)) := by
      field_simp
    have h2 : κ / (K' * (H - s)) ≤ κ / g s :=
      div_le_div_of_nonneg_left hκpos.le hgs (hgle s hs)
    have h3 : κ / g s ≤ Real.smoothTransition (s - c) / g s :=
      div_le_div_of_nonneg_right hχ hgs.le
    have h4 : 0 ≤ (1 : ℝ) := zero_le_one
    rw [hw, h1]
    linarith
  -- the target height
  set q₀ := c + ∫ s in c..s₀, w s with hq₀
  set T : ℝ := (|B - q₀| + 1) * K' / κ with hT
  have hTpos : 0 < T := by rw [hT]; positivity
  set u := H - (H - s₀) * Real.exp (-T) with hu
  have hexp : 0 < Real.exp (-T) := Real.exp_pos _
  have hexp1 : Real.exp (-T) < 1 := by
    have h1 := Real.exp_lt_exp.mpr (show -T < 0 by linarith)
    rwa [Real.exp_zero] at h1
  have hHu : H - u = (H - s₀) * Real.exp (-T) := by rw [hu]; ring
  have hHupos : 0 < H - u := by rw [hHu]; exact mul_pos (by linarith) hexp
  have huH : u < H := by linarith
  have hs₀u : s₀ < u := by
    have : (H - s₀) * Real.exp (-T) < H - s₀ := by
      have hHs₀ : 0 < H - s₀ := by linarith
      nlinarith
    linarith
  refine ⟨u, by linarith, huH, ?_⟩
  -- splitting the integral at `s₀`
  have hsplit : (∫ s in c..u, w s) = (∫ s in c..s₀, w s) + ∫ s in s₀..u, w s :=
    (intervalIntegral.integral_add_adjacent_intervals (hint c s₀ (by linarith) hs₀H)
      (hint s₀ u hs₀H huH)).symm
  have hlogint : (∫ s in s₀..u, κ / K' * (H - s)⁻¹) = κ / K' * T := by
    rw [intervalIntegral.integral_const_mul]
    congr 1
    have hsub := intervalIntegral.integral_comp_sub_left (a := s₀) (b := u)
      (fun x : ℝ => x⁻¹) H
    rw [hsub, integral_inv_of_pos hHupos (by linarith), hHu]
    have hne : H - s₀ ≠ 0 := by linarith
    rw [div_mul_cancel_left₀ hne, ← Real.exp_neg, neg_neg, Real.log_exp]
  have hmono : (∫ s in s₀..u, κ / K' * (H - s)⁻¹) ≤ ∫ s in s₀..u, w s := by
    refine intervalIntegral.integral_mono_on hs₀u.le ?_ (hint s₀ u hs₀H huH) ?_
    · refine ContinuousOn.intervalIntegrable ?_
      refine continuousOn_const.mul ((continuousOn_const.sub continuousOn_id).inv₀ ?_)
      intro s hs
      rw [uIcc_of_le hs₀u.le] at hs
      have : s < H := lt_of_le_of_lt hs.2 huH
      exact sub_ne_zero.mpr this.ne'
    · intro s hs
      exact hwlow s ⟨hs.1, hs.2.trans huH.le⟩ (lt_of_le_of_lt hs.2 huH)
  have hbig : B < q₀ + κ / K' * T := by
    have h1 : κ / K' * T = |B - q₀| + 1 := by
      rw [hT]
      field_simp
    rw [h1]
    linarith [le_abs_self (B - q₀)]
  change B < c + ∫ s in c..u, w s
  rw [hsplit]
  rw [hq₀] at hbig
  linarith

/-! ### The height coordinate of an open subgraph -/

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {HX : Type*} [TopologicalSpace HX] {J : ModelWithCorners ℝ F HX}
  {X : Type*} [TopologicalSpace X] [ChartedSpace HX X]

/-- The weight `w = 1 + χ(u - c) / f` of the height coordinate. -/
def openSubgraphWeight (f : X × ℝ → ℝ) (c : ℝ) (z : X × ℝ) : ℝ :=
  1 + Real.smoothTransition (z.2 - c) / f z

/-- The height coordinate `Q(x, u) = c + ∫_c^u w(x, s) ds`. -/
def openSubgraphHeight (f : X × ℝ → ℝ) (c : ℝ) (z : X × ℝ) : ℝ :=
  c + ∫ s in c..z.2, openSubgraphWeight f c (z.1, s)

omit [TopologicalSpace X] in
theorem openSubgraphHeight_of_le (f : X × ℝ → ℝ) {c : ℝ} {z : X × ℝ} (hz : z.2 ≤ c) :
    openSubgraphHeight f c z = z.2 := by
  have hEq : EqOn (fun s => openSubgraphWeight f c (z.1, s)) (fun _ => (1 : ℝ)) (uIcc c z.2) := by
    intro s hs
    rw [uIcc_of_ge hz] at hs
    simp only [openSubgraphWeight]
    rw [Real.smoothTransition.zero_of_nonpos (by linarith [hs.2]), zero_div, add_zero]
  rw [openSubgraphHeight, intervalIntegral.integral_congr hEq, intervalIntegral.integral_const,
    smul_eq_mul, mul_one]
  ring

omit [TopologicalSpace X] in
/-- On the open subgraph (the support of `f ≥ 0`) the weight is at least `1`. -/
theorem openSubgraphWeight_one_le {h : X → ℝ} {f : X × ℝ → ℝ}
    (hfsupp : f.support = {z | z.2 < h z.1}) (hfnn : ∀ z, 0 ≤ f z) (c : ℝ) {z : X × ℝ}
    (hz : z.2 < h z.1) : 1 ≤ openSubgraphWeight f c z := by
  have hf : 0 < f z := lt_of_le_of_ne (hfnn z) (Ne.symm (by
    change z ∈ f.support
    rw [hfsupp]
    exact hz))
  have : 0 ≤ Real.smoothTransition (z.2 - c) / f z :=
    div_nonneg (Real.smoothTransition.nonneg _) hf.le
  simp only [openSubgraphWeight]
  linarith

theorem contMDiffOn_openSubgraphWeight {h : X → ℝ} {f : X × ℝ → ℝ}
    (hfsupp : f.support = {z | z.2 < h z.1}) (hfsm : ContMDiff (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ f)
    (c : ℝ) :
    ContMDiffOn (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (openSubgraphWeight f c) {z | z.2 < h z.1} := by
  have hχ : ContMDiff (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (fun z : X × ℝ => Real.smoothTransition (z.2 - c)) :=
    ((Real.smoothTransition.contDiff (n := ⊤)).comp
      (contDiff_id.sub contDiff_const)).contMDiff.comp contMDiff_snd
  have hdiv := ContMDiffOn.div₀ hχ.contMDiffOn hfsm.contMDiffOn (s := {z | z.2 < h z.1})
    (fun z hz => by
      change z ∈ f.support
      rw [hfsupp]
      exact hz)
  exact contMDiffOn_const.add hdiv

theorem contMDiffOn_openSubgraphHeight [IsManifold J ∞ X] [J.Boundaryless] {h : X → ℝ}
    (hh : Continuous h) {c : ℝ} (hch : ∀ x, c < h x) {f : X × ℝ → ℝ}
    (hfsupp : f.support = {z | z.2 < h z.1}) (hfsm : ContMDiff (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ f) :
    ContMDiffOn (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (openSubgraphHeight f c) {z | z.2 < h z.1} := by
  have hU : IsOpen {z : X × ℝ | z.2 < h z.1} :=
    isOpen_lt continuous_snd (hh.comp continuous_fst)
  have hint := DifferentialGeometry.Topology.Manifold.contMDiffOn_fiberIntegral (J := J) hU
    (contMDiffOn_openSubgraphWeight hfsupp hfsm c) c hU (fun z hz s hs => by
      change s < h z.1
      have hz' : z.2 < h z.1 := hz
      rcases le_total c z.2 with hcz | hcz
      · rw [uIcc_of_le hcz] at hs
        exact lt_of_le_of_lt hs.2 hz'
      · rw [uIcc_of_ge hcz] at hs
        exact lt_of_le_of_lt hs.2 (hch z.1))
  exact contMDiffOn_const.add hint

theorem hasDerivAt_openSubgraphHeight {h : X → ℝ} {f : X × ℝ → ℝ}
    (hfsupp : f.support = {z | z.2 < h z.1}) (hfsm : ContMDiff (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ f)
    {c : ℝ} (hch : ∀ x, c < h x) {z : X × ℝ} (hz : z.2 < h z.1) :
    HasDerivAt (fun s => openSubgraphHeight f c (z.1, s)) (openSubgraphWeight f c z) z.2 := by
  have hwc : ContinuousOn (fun s => openSubgraphWeight f c (z.1, s)) (Iio (h z.1)) :=
    (contMDiffOn_openSubgraphWeight hfsupp hfsm c).continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn (fun s hs => hs)
  have hsub : uIcc c z.2 ⊆ Iio (h z.1) := by
    intro s hs
    rcases le_total c z.2 with hcz | hcz
    · rw [uIcc_of_le hcz] at hs
      exact lt_of_le_of_lt hs.2 hz
    · rw [uIcc_of_ge hcz] at hs
      exact lt_of_le_of_lt hs.2 (hch z.1)
  have hd := intervalIntegral.integral_hasDerivAt_right ((hwc.mono hsub).intervalIntegrable)
    (hwc.stronglyMeasurableAtFilter isOpen_Iio z.2 hz) (hwc.continuousAt (Iio_mem_nhds hz))
  exact hd.const_add c

theorem strictMonoOn_openSubgraphHeight {h : X → ℝ} {f : X × ℝ → ℝ}
    (hfsupp : f.support = {z | z.2 < h z.1}) (hfsm : ContMDiff (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ f)
    (hfnn : ∀ z, 0 ≤ f z) {c : ℝ} (hch : ∀ x, c < h x) (x : X) :
    StrictMonoOn (fun u => openSubgraphHeight f c (x, u)) (Iio (h x)) := by
  have hd : ∀ u ∈ Iio (h x),
      HasDerivAt (fun s => openSubgraphHeight f c (x, s)) (openSubgraphWeight f c (x, u)) u :=
    fun u hu => hasDerivAt_openSubgraphHeight (z := (x, u)) hfsupp hfsm hch hu
  refine strictMonoOn_of_deriv_pos (convex_Iio (h x)) (fun u hu => (hd u hu).continuousAt.continuousWithinAt)
    fun u hu => ?_
  rw [interior_Iio] at hu
  rw [(hd u hu).deriv]
  exact lt_of_lt_of_le zero_lt_one (openSubgraphWeight_one_le (z := (x, u)) hfsupp hfnn c hu)

theorem exists_openSubgraphHeight_eq {h : X → ℝ} {f : X × ℝ → ℝ}
    (hfsupp : f.support = {z | z.2 < h z.1}) (hfsm : ContMDiff (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ f)
    (hfnn : ∀ z, 0 ≤ f z) {c : ℝ} (hch : ∀ x, c < h x) (x : X) (v : ℝ) :
    ∃ u < h x, openSubgraphHeight f c (x, u) = v := by
  rcases le_or_gt v c with hvc | hcv
  · exact ⟨v, lt_of_le_of_lt hvc (hch x), openSubgraphHeight_of_le f (z := (x, v)) hvc⟩
  · have hgs : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun s : ℝ => f (x, s)) :=
      hfsm.comp (contMDiff_const.prodMk contMDiff_id)
    have hg : ContDiff ℝ 1 (fun s : ℝ => f (x, s)) :=
      (contMDiff_iff_contDiff.mp hgs).of_le (by simp)
    have hpos : ∀ s < h x, 0 < f (x, s) := fun s hs =>
      lt_of_le_of_ne (hfnn _) (Ne.symm (by
        change (x, s) ∈ f.support
        rw [hfsupp]
        exact hs))
    have hH : f (x, h x) = 0 := by
      have : (x, h x) ∉ f.support := by
        rw [hfsupp]
        exact lt_irrefl (h x)
      exact notMem_support.mp this
    obtain ⟨u₁, hcu₁, hu₁H, hbig⟩ := exists_lt_add_integral_weight hg (hch x) hpos hH v
    have hcont : ContinuousOn (fun u => openSubgraphHeight f c (x, u)) (Icc c u₁) := fun u hu =>
      (hasDerivAt_openSubgraphHeight (z := (x, u)) hfsupp hfsm hch
        (lt_of_le_of_lt hu.2 hu₁H)).continuousAt.continuousWithinAt
    have hc : openSubgraphHeight f c (x, c) = c := openSubgraphHeight_of_le f (z := (x, c)) le_rfl
    obtain ⟨u, hu, hEq⟩ := intermediate_value_Icc hcu₁ hcont
      (show v ∈ Icc (openSubgraphHeight f c (x, c)) (openSubgraphHeight f c (x, u₁)) from
        ⟨by rw [hc]; exact hcv.le, hbig.le⟩)
    exact ⟨u, lt_of_le_of_lt hu.2 hu₁H, hEq⟩

/-- **Height coordinate of the open subgraph of a continuous function.** For `h : X → ℝ`
continuous with `c < h`, there is a partial diffeomorphism of `X × ℝ` from the open subgraph
`{u < h x}` onto `X × ℝ`, fibre preserving, the identity for `u ≤ c` and strictly increasing on
every fibre. -/
theorem exists_openSubgraph_heightCoordinate [FiniteDimensional ℝ F] [J.Boundaryless]
    [IsManifold J ∞ X] [CompactSpace X] [T2Space X] {c : ℝ} (h : X → ℝ) (hh : Continuous h)
    (hch : ∀ x, c < h x) :
    ∃ Φ : PartialDiffeomorph (J.prod 𝓘(ℝ, ℝ)) (J.prod 𝓘(ℝ, ℝ)) (X × ℝ) (X × ℝ) ∞,
      Φ.source = {z | z.2 < h z.1} ∧ Φ.target = univ ∧ (∀ z, (Φ z).1 = z.1) ∧
      (∀ z, z.2 ≤ c → Φ z = z) ∧ ∀ x, StrictMonoOn (fun u => (Φ (x, u)).2) (Iio (h x)) := by
  rcases isEmpty_or_nonempty X with hX | hX
  · refine ⟨(Diffeomorph.refl (J.prod 𝓘(ℝ, ℝ)) (X × ℝ) ∞).toPartialDiffeomorph,
      Set.ext fun z => isEmptyElim z.1, rfl, fun z => isEmptyElim z.1, fun z => isEmptyElim z.1,
      fun x => isEmptyElim x⟩
  set U : Set (X × ℝ) := {z | z.2 < h z.1} with hUdef
  have hU : IsOpen U := isOpen_lt continuous_snd (hh.comp continuous_fst)
  obtain ⟨f, hfsupp, hfsm, hfnn⟩ : ∃ f : X × ℝ → ℝ, f.support = U ∧
      ContMDiff (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ f ∧ ∀ z, 0 ≤ f z :=
    IsOpen.exists_contMDiff_support_eq (J.prod 𝓘(ℝ, ℝ)) hU
  set Q := openSubgraphHeight f c with hQdef
  have hQ : ContMDiffOn (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ Q U :=
    contMDiffOn_openSubgraphHeight hh hch hfsupp hfsm
  have hloc : IsLocalDiffeomorphOn (J.prod 𝓘(ℝ, ℝ)) (J.prod 𝓘(ℝ, ℝ)) ∞
      (fun z => (z.1, Q z)) U := fun z =>
    DifferentialGeometry.Topology.Manifold.isLocalDiffeomorphAt_fst_prodMk hU hQ z.2
      (hasDerivAt_openSubgraphHeight hfsupp hfsm hch z.2)
      (lt_of_lt_of_le zero_lt_one (openSubgraphWeight_one_le hfsupp hfnn c z.2)).ne'
  have hmono := strictMonoOn_openSubgraphHeight hfsupp hfsm hfnn hch
  have hinj : InjOn (fun z : X × ℝ => (z.1, Q z)) U := by
    intro z₁ h₁ z₂ h₂ heq
    have heq' : ((z₁.1, Q z₁) : X × ℝ) = (z₂.1, Q z₂) := heq
    obtain ⟨e1, e2⟩ := Prod.mk.inj heq'
    obtain ⟨x₁, u₁⟩ := z₁
    obtain ⟨x₂, u₂⟩ := z₂
    simp only at e1
    subst e1
    have h₁' : u₁ ∈ Iio (h x₁) := h₁
    have h₂' : u₂ ∈ Iio (h x₁) := h₂
    rw [(hmono x₁).injOn h₁' h₂' e2]
  have hne : U.Nonempty := ⟨(Classical.arbitrary X, c), hch _⟩
  obtain ⟨Φ, hsrc, htgt, hfun⟩ :=
    IsLocalDiffeomorphOn.exists_partialDiffeomorph_of_injOn hloc hU hne hinj
  have happ : ∀ z, Φ z = (z.1, Q z) := fun z => by
    rw [hfun]
  refine ⟨Φ, hsrc, ?_, fun z => by rw [happ], fun z hz => ?_, fun x => ?_⟩
  · rw [htgt]
    refine eq_univ_of_forall fun y => ?_
    obtain ⟨u, hu, hQu⟩ := exists_openSubgraphHeight_eq hfsupp hfsm hfnn hch y.1 y.2
    exact ⟨(y.1, u), hu, Prod.ext rfl hQu⟩
  · rw [happ, hQdef, openSubgraphHeight_of_le f hz]
  · intro u₁ hu₁ u₂ hu₂ h12
    simp only [happ]
    exact hmono x hu₁ hu₂ h12

/-! ### LC59 -/

/-- **LC59: smooth interior straightening of a continuous graph** (`master207A.tex:23320`).
`X` compact boundaryless, `h : X → ℝ` continuous, `a < c < r`, `c < h`: a partial diffeomorphism
`P` of `X × ℝ` from `X × (a, r)` onto `{a < u < h x}`, fibre preserving, the identity for `u ≤ c`
and strictly increasing on every fibre. -/
theorem exists_openGraph_straightening [FiniteDimensional ℝ F] [J.Boundaryless]
    [IsManifold J ∞ X] [CompactSpace X] [T2Space X] {a c r : ℝ} (hac : a < c) (hcr : c < r)
    (h : X → ℝ) (hh : Continuous h) (hch : ∀ x, c < h x) :
    ∃ P : PartialDiffeomorph (J.prod 𝓘(ℝ, ℝ)) (J.prod 𝓘(ℝ, ℝ)) (X × ℝ) (X × ℝ) ∞,
      P.source = {z | a < z.2 ∧ z.2 < r} ∧ P.target = {z | a < z.2 ∧ z.2 < h z.1} ∧
      (∀ z ∈ P.source, (P z).1 = z.1) ∧ (∀ z ∈ P.source, z.2 ≤ c → P z = z) ∧
      ∀ x, StrictMonoOn (fun u => (P (x, u)).2) (Ioo a r) := by
  obtain ⟨Φh, hsh, hth, hfh, hidh, hmh⟩ :=
    exists_openSubgraph_heightCoordinate (J := J) (c := c) h hh hch
  obtain ⟨Φr, hsr, htr, hfr, hidr, hmr⟩ :=
    exists_openSubgraph_heightCoordinate (J := J) (c := c) (fun _ : X => r) continuous_const
      (fun _ => hcr)
  -- level `a` is preserved in both directions by a height coordinate
  have hlevel : ∀ (Φ : PartialDiffeomorph (J.prod 𝓘(ℝ, ℝ)) (J.prod 𝓘(ℝ, ℝ)) (X × ℝ) (X × ℝ) ∞)
      (k : X → ℝ), Φ.source = {z | z.2 < k z.1} → (∀ z, (Φ z).1 = z.1) →
      (∀ z, z.2 ≤ c → Φ z = z) → (∀ x, StrictMonoOn (fun u => (Φ (x, u)).2) (Iio (k x))) →
      (∀ x, c < k x) → ∀ z ∈ Φ.source, (a < (Φ z).2 ↔ a < z.2) := by
    intro Φ k hs hf hid hm hck z hz
    rcases le_or_gt z.2 c with hzc | hcz
    · rw [hid z hzc]
    · have hz' : z.2 ∈ Iio (k z.1) := by rw [hs] at hz; exact hz
      have hc' : c ∈ Iio (k z.1) := hck z.1
      have hlt := hm z.1 hc' hz' hcz
      have hcc : (Φ (z.1, c)).2 = c := by rw [hid (z.1, c) le_rfl]
      change (Φ (z.1, c)).2 < (Φ (z.1, z.2)).2 at hlt
      rw [hcc] at hlt
      constructor <;> intro _ <;> linarith
  have hlh := hlevel Φh h hsh hfh hidh hmh hch
  have hlr := hlevel Φr (fun _ => r) hsr hfr hidr hmr (fun _ => hcr)
  -- inverse coordinates
  have hsymm_fst : ∀ (Φ : PartialDiffeomorph (J.prod 𝓘(ℝ, ℝ)) (J.prod 𝓘(ℝ, ℝ)) (X × ℝ)
      (X × ℝ) ∞), Φ.target = univ → (∀ z, (Φ z).1 = z.1) → ∀ y, (Φ.symm y).1 = y.1 := by
    intro Φ ht hf y
    have hy : y ∈ Φ.target := by rw [ht]; exact mem_univ y
    have h1 := Φ.right_inv' hy
    have h2 := hf (Φ.symm y)
    change (Φ (Φ.symm y)).1 = (Φ.symm y).1 at h2
    change Φ (Φ.symm y) = y at h1
    rw [← h2, h1]
  have hsymm_mem : ∀ (Φ : PartialDiffeomorph (J.prod 𝓘(ℝ, ℝ)) (J.prod 𝓘(ℝ, ℝ)) (X × ℝ)
      (X × ℝ) ∞), Φ.target = univ → ∀ y, Φ.symm y ∈ Φ.source := by
    intro Φ ht y
    exact Φ.map_target' (by rw [ht]; exact mem_univ y)
  have hsymm_app : ∀ (Φ : PartialDiffeomorph (J.prod 𝓘(ℝ, ℝ)) (J.prod 𝓘(ℝ, ℝ)) (X × ℝ)
      (X × ℝ) ∞), Φ.target = univ → ∀ y, Φ (Φ.symm y) = y := by
    intro Φ ht y
    exact Φ.right_inv' (by rw [ht]; exact mem_univ y)
  have hglob : ∀ (Φ : PartialDiffeomorph (J.prod 𝓘(ℝ, ℝ)) (J.prod 𝓘(ℝ, ℝ)) (X × ℝ)
      (X × ℝ) ∞), Φ.target = univ →
      ContMDiff (J.prod 𝓘(ℝ, ℝ)) (J.prod 𝓘(ℝ, ℝ)) ∞ (Φ.symm : X × ℝ → X × ℝ) := by
    intro Φ ht
    rw [← contMDiffOn_univ]
    have h1 := Φ.symm.contMDiffOn_toFun
    change ContMDiffOn _ _ _ _ Φ.target at h1
    rwa [ht] at h1
  set S : Set (X × ℝ) := {z | a < z.2 ∧ z.2 < r} with hSdef
  set T : Set (X × ℝ) := {z | a < z.2 ∧ z.2 < h z.1} with hTdef
  have hSsub : S ⊆ Φr.source := fun z hz => by rw [hsr]; exact hz.2
  have hTsub : T ⊆ Φh.source := fun z hz => by rw [hsh]; exact hz.2
  have hS : IsOpen S := (isOpen_lt continuous_const continuous_snd).inter
    (isOpen_lt continuous_snd continuous_const)
  have hT : IsOpen T := (isOpen_lt continuous_const continuous_snd).inter
    (isOpen_lt continuous_snd (hh.comp continuous_fst))
  have hmaps : ∀ z ∈ S, Φh.symm (Φr z) ∈ T := by
    intro z hz
    have hm := hsymm_mem Φh hth (Φr z)
    refine ⟨?_, by rw [hsh] at hm; exact hm⟩
    have h1 : a < (Φr z).2 := (hlr z (hSsub hz)).mpr hz.1
    have h2 := hlh (Φh.symm (Φr z)) hm
    rw [hsymm_app Φh hth] at h2
    exact h2.mp h1
  have hmaps' : ∀ z ∈ T, Φr.symm (Φh z) ∈ S := by
    intro z hz
    have hm := hsymm_mem Φr htr (Φh z)
    refine ⟨?_, by rw [hsr] at hm; exact hm⟩
    have h1 : a < (Φh z).2 := (hlh z (hTsub hz)).mpr hz.1
    have h2 := hlr (Φr.symm (Φh z)) hm
    rw [hsymm_app Φr htr] at h2
    exact h2.mp h1
  let P : PartialDiffeomorph (J.prod 𝓘(ℝ, ℝ)) (J.prod 𝓘(ℝ, ℝ)) (X × ℝ) (X × ℝ) ∞ :=
    { toFun := fun z => Φh.symm (Φr z)
      invFun := fun z => Φr.symm (Φh z)
      source := S
      target := T
      map_source' := hmaps
      map_target' := hmaps'
      left_inv' := fun z hz => by
        rw [hsymm_app Φh hth]
        exact Φr.left_inv' (hSsub hz)
      right_inv' := fun z hz => by
        rw [hsymm_app Φr htr]
        exact Φh.left_inv' (hTsub hz)
      open_source := hS
      open_target := hT
      contMDiffOn_toFun := (hglob Φh hth).comp_contMDiffOn (Φr.contMDiffOn_toFun.mono hSsub)
      contMDiffOn_invFun := (hglob Φr htr).comp_contMDiffOn (Φh.contMDiffOn_toFun.mono hTsub) }
  have hPapp : ∀ z, P z = Φh.symm (Φr z) := fun _ => rfl
  refine ⟨P, rfl, rfl, fun z _ => ?_, fun z hz hzc => ?_, fun x => ?_⟩
  · rw [hPapp, hsymm_fst Φh hth hfh, hfr]
  · have hz₁ : Φr z = z := hidr z hzc
    have hz₂ : Φh z = z := hidh z hzc
    have hzs : z ∈ Φh.source := by rw [hsh]; exact lt_of_le_of_lt hzc (hch z.1)
    rw [hPapp, hz₁]
    have := Φh.left_inv' hzs
    change Φh.symm (Φh z) = z at this
    rwa [hz₂] at this
  · intro u₁ hu₁ u₂ hu₂ h12
    simp only [hPapp]
    have hr12 : (Φr (x, u₁)).2 < (Φr (x, u₂)).2 := hmr x hu₁.2 hu₂.2 h12
    -- strict monotonicity of the inverse fibre map of `Φh`
    set y₁ := Φr (x, u₁) with hy₁
    set y₂ := Φr (x, u₂) with hy₂
    have hy₁x : y₁.1 = x := hfr (x, u₁)
    have hy₂x : y₂.1 = x := hfr (x, u₂)
    set w₁ := Φh.symm y₁ with hw₁
    set w₂ := Φh.symm y₂ with hw₂
    have hw₁x : w₁.1 = x := (hsymm_fst Φh hth hfh y₁).trans hy₁x
    have hw₂x : w₂.1 = x := (hsymm_fst Φh hth hfh y₂).trans hy₂x
    have hw₁s : w₁.2 ∈ Iio (h x) := by
      have := hsymm_mem Φh hth y₁
      rw [hsh] at this
      change w₁.2 < h w₁.1 at this
      rwa [hw₁x] at this
    have hw₂s : w₂.2 ∈ Iio (h x) := by
      have := hsymm_mem Φh hth y₂
      rw [hsh] at this
      change w₂.2 < h w₂.1 at this
      rwa [hw₂x] at this
    by_contra hcon
    push Not at hcon
    have hle := (hmh x).monotoneOn hw₂s hw₁s hcon
    have e₁ : (Φh (x, w₁.2)).2 = y₁.2 := by
      have : ((x, w₁.2) : X × ℝ) = w₁ := Prod.ext hw₁x.symm rfl
      rw [this, hw₁, hsymm_app Φh hth]
    have e₂ : (Φh (x, w₂.2)).2 = y₂.2 := by
      have : ((x, w₂.2) : X × ℝ) = w₂ := Prod.ext hw₂x.symm rfl
      rw [this, hw₂, hsymm_app Φh hth]
    change (Φh (x, w₂.2)).2 ≤ (Φh (x, w₁.2)).2 at hle
    rw [e₁, e₂] at hle
    linarith

/-- LC59 in the blueprint's verbatim form (upper bound `b` of `h` and `r`; unused). -/
example [FiniteDimensional ℝ F] [J.Boundaryless] [IsManifold J ∞ X] [CompactSpace X] [T2Space X]
    {a c b r : ℝ} (hac : a < c) (hcr : c < r) (hrb : r < b) (h : X → ℝ) (hh : Continuous h)
    (hch : ∀ x, c < h x) (hhb : ∀ x, h x < b) :
    ∃ P : PartialDiffeomorph (J.prod 𝓘(ℝ, ℝ)) (J.prod 𝓘(ℝ, ℝ)) (X × ℝ) (X × ℝ) ∞,
      P.source = {z | a < z.2 ∧ z.2 < r} ∧ P.target = {z | a < z.2 ∧ z.2 < h z.1} ∧
      (∀ z ∈ P.source, (P z).1 = z.1) ∧ (∀ z ∈ P.source, z.2 ≤ c → P z = z) ∧
      ∀ x, StrictMonoOn (fun u => (P (x, u)).2) (Ioo a r) :=
  (fun _ _ => exists_openGraph_straightening hac hcr h hh hch) hrb hhb

end DifferentialGeometry.Geometry.Collapse
