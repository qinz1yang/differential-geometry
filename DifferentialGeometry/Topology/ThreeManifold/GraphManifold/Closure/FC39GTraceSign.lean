import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
# FC39 GROUP G, lane FC39-G-TRACE: sign lemmas (generic)

Generic first-order sign facts used by the labelled trace atlas (`FC39GTraceRows.lean`,
`FC39GTraceAtlas.lean`; sheet `build-logs/resume/sheet-FC39-G-TRACE.md`):

* along the chart line through an interior point `x` in a direction `v` with `df_x v < 0`, a
  function vanishing at `x` is eventually negative (`eventually_lt_chartLine_GTR`);
* **the three-sides lemma** `false_of_three_sides_GTR`: at an interior point, a region side cut out
  by finitely many functions with a common descent direction and two sides cut out by functions
  with nonzero differential cannot be pairwise disjoint (the HH exclusion of external draft 58
  §二 F2 for faces of different owners);
* **the quadrant lemma** `not_eventually_quadrant_iff_GTR`: near `0 ∈ ℝ × ℝ` the closed quadrant is
  not the sublevel `{g ≤ 0}` of a function with `g 0 = 0` and nonzero derivative (a registered
  corner is not a smooth one-face boundary point).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open scoped Manifold Topology

namespace GC.GraphManifold.Assembly.FC39P0

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- The chart line through `x` in the direction `v`. -/
def chartLine_GTR (I : ModelWithCorners ℝ E H) (x : M) (v : E) (t : ℝ) : M :=
  (extChartAt I x).symm (extChartAt I x x + t • v)

/-- The differential of a real function, typed as a functional on the model space. -/
def mderivR_GTR (I : ModelWithCorners ℝ E H) (f : M → ℝ) (x : M) : E →L[ℝ] ℝ :=
  mfderiv I 𝓘(ℝ, ℝ) f x

/-- The directional derivative `df_x v` of a real function, read in `ℝ`. -/
def dirDeriv_GTR (I : ModelWithCorners ℝ E H) (f : M → ℝ) (x : M) (v : E) : ℝ :=
  mderivR_GTR I f x v

theorem tendsto_chartLine_GTR (x : M) (v : E) :
    Tendsto (chartLine_GTR I x v) (𝓝 0) (𝓝 x) := by
  have h2 : Tendsto (fun t : ℝ => extChartAt I x x + t • v) (𝓝 0) (𝓝 (extChartAt I x x)) := by
    have hc : Continuous (fun t : ℝ => extChartAt I x x + t • v) :=
      continuous_const.add (continuous_id.smul continuous_const)
    simpa using hc.tendsto 0
  have h := (continuousAt_extChartAt_symm (I := I) x).tendsto.comp h2
  rwa [extChartAt_to_inv] at h

theorem eventually_lt_chartLine_GTR {x : M} (hx : I.IsInteriorPoint x) (v : E) {f : M → ℝ}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x) (hv : dirDeriv_GTR I f x v < 0) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), f (chartLine_GTR I x v t) < f x := by
  have hfd : HasFDerivWithinAt (writtenInExtChartAt I 𝓘(ℝ, ℝ) x f) (mfderiv I 𝓘(ℝ, ℝ) f x)
      (range I) (extChartAt I x x) := hf.hasMFDerivAt.2
  have hfd' := hfd.hasFDerivAt (mem_interior_iff_mem_nhds.1 hx)
  have hline : HasDerivAt (fun t : ℝ => extChartAt I x x + t • v) v 0 := by
    have h1 := HasDerivAt.smul_const (hasDerivAt_id (0 : ℝ)) v
    have h2 := HasDerivAt.const_add (extChartAt I x x) h1
    simpa using h2
  have hcomp : HasDerivAt
      (fun t : ℝ => writtenInExtChartAt I 𝓘(ℝ, ℝ) x f (extChartAt I x x + t • v))
      (dirDeriv_GTR I f x v) 0 := by
    have hfd'' : HasFDerivAt (writtenInExtChartAt I 𝓘(ℝ, ℝ) x f) (mfderiv I 𝓘(ℝ, ℝ) f x)
        (extChartAt I x x + (0 : ℝ) • v) := by simpa using hfd'
    exact hfd''.comp_hasDerivAt (0 : ℝ) hline
  have hslope := hcomp.tendsto_slope_zero_right
  have hev := hslope (Iio_mem_nhds hv)
  filter_upwards [hev, self_mem_nhdsWithin] with t ht htpos
  simp only [mem_preimage, mem_Iio, zero_add, zero_smul, add_zero, smul_eq_mul] at ht
  have hw : ∀ y, writtenInExtChartAt I 𝓘(ℝ, ℝ) x f y = f ((extChartAt I x).symm y) := by
    intro y
    simp [writtenInExtChartAt]
  rw [hw, hw, extChartAt_to_inv] at ht
  have htpos' : (0 : ℝ) < t := htpos
  unfold chartLine_GTR
  have : f ((extChartAt I x).symm (extChartAt I x x + t • v)) - f x < 0 := by
    by_contra hcon
    push Not at hcon
    have := mul_nonneg (inv_nonneg.2 htpos'.le) hcon
    linarith
  linarith

theorem dirDeriv_add_smul_GTR (f : M → ℝ) (x : M) (v w : E) (s : ℝ) :
    dirDeriv_GTR I f x (v + s • w) = dirDeriv_GTR I f x v + s * dirDeriv_GTR I f x w := by
  unfold dirDeriv_GTR
  rw [map_add, map_smul, smul_eq_mul]

theorem dirDeriv_neg_GTR (f : M → ℝ) (x : M) (v : E) :
    dirDeriv_GTR I f x (-v) = -dirDeriv_GTR I f x v := by
  unfold dirDeriv_GTR
  rw [map_neg]

theorem exists_dirDeriv_neg_GTR {f : M → ℝ} {x : M} (hf : mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0) :
    ∃ w : E, dirDeriv_GTR I f x w < 0 := by
  by_contra hcon
  push Not at hcon
  have hz : ∀ u : E, dirDeriv_GTR I f x u = 0 := by
    intro u
    have h1 := hcon u
    have h2 := hcon (-u)
    rw [dirDeriv_neg_GTR] at h2
    linarith
  apply hf
  ext u
  exact hz u

/-- Along a direction on which every function of a finite family vanishing at `x` has negative
derivative, the chart line eventually lies in any set containing the common negative side near `x`. -/
theorem eventually_chartLine_mem_GTR {x : M} (hx : I.IsInteriorPoint x) {ι : Type*}
    (L : Finset ι) (f : ι → M → ℝ) (hfd : ∀ g ∈ L, MDifferentiableAt I 𝓘(ℝ, ℝ) (f g) x)
    (hf0 : ∀ g ∈ L, f g x = 0) {v : E} (hv : ∀ g ∈ L, dirDeriv_GTR I (f g) x v < 0)
    {S : Set M} (hS : ∀ᶠ y in 𝓝 x, (∀ g ∈ L, f g y < 0) → y ∈ S) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), chartLine_GTR I x v t ∈ S := by
  have h1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ g ∈ L, f g (chartLine_GTR I x v t) < 0 := by
    rw [Filter.eventually_all_finset]
    intro g hg
    have h := eventually_lt_chartLine_GTR hx v (hfd g hg) (hv g hg)
    rw [hf0 g hg] at h
    exact h
  have h2 := ((tendsto_chartLine_GTR (I := I) x v).mono_left
    (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)).eventually hS
  filter_upwards [h1, h2] with t ht1 ht2 using ht2 ht1

/-- The single-function form of `eventually_chartLine_mem_GTR`. -/
theorem eventually_chartLine_mem_one_GTR {x : M} (hx : I.IsInteriorPoint x) {b : M → ℝ}
    (hb : MDifferentiableAt I 𝓘(ℝ, ℝ) b x) (hb0 : b x = 0) {v : E}
    (hv : dirDeriv_GTR I b x v < 0) {S : Set M} (hS : ∀ᶠ y in 𝓝 x, b y < 0 → y ∈ S) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), chartLine_GTR I x v t ∈ S := by
  have h1 := eventually_lt_chartLine_GTR hx v hb hv
  rw [hb0] at h1
  have h2 := ((tendsto_chartLine_GTR (I := I) x v).mono_left
    (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)).eventually hS
  filter_upwards [h1, h2] with t ht1 ht2 using ht2 ht1

/-- **The three-sides lemma.** At an interior point `x`, let the functions `ψ g` (`g ∈ L`) vanish
at `x` with a common direction of negative derivative (the "region side" `{∀ g, ψ g < 0}` lies in
`R` near `x`), and let `a`, `a'` be two functions vanishing at `x` with nonzero differentials (their
negative sides lie in `A`, `A'` near `x`). Then `R`, `A`, `A'` cannot be pairwise disjoint.
(Proof: `da > 0` and `da' > 0` on a region direction `v₀`, so `−v₀` enters `A ∩ A'`.) -/
theorem false_of_three_sides_GTR {x : M} (hx : I.IsInteriorPoint x) {ι : Type*} (L : Finset ι)
    (ψ : ι → M → ℝ) (hψd : ∀ g ∈ L, MDifferentiableAt I 𝓘(ℝ, ℝ) (ψ g) x)
    (hψ0 : ∀ g ∈ L, ψ g x = 0) {v₀ : E} (hv₀ : ∀ g ∈ L, dirDeriv_GTR I (ψ g) x v₀ < 0)
    {a a' : M → ℝ} (had : MDifferentiableAt I 𝓘(ℝ, ℝ) a x) (ha0 : a x = 0)
    (hda : mfderiv I 𝓘(ℝ, ℝ) a x ≠ 0) (had' : MDifferentiableAt I 𝓘(ℝ, ℝ) a' x)
    (ha0' : a' x = 0) (hda' : mfderiv I 𝓘(ℝ, ℝ) a' x ≠ 0) {R A A' : Set M}
    (hR : ∀ᶠ y in 𝓝 x, (∀ g ∈ L, ψ g y < 0) → y ∈ R)
    (hA : ∀ᶠ y in 𝓝 x, a y < 0 → y ∈ A) (hA' : ∀ᶠ y in 𝓝 x, a' y < 0 → y ∈ A')
    (hRA : Disjoint R A) (hRA' : Disjoint R A') (hAA' : Disjoint A A') : False := by
  -- on the region cone, the derivative of an owner function is nonnegative
  have hcone : ∀ {b : M → ℝ} {B : Set M}, MDifferentiableAt I 𝓘(ℝ, ℝ) b x → b x = 0 →
      (∀ᶠ y in 𝓝 x, b y < 0 → y ∈ B) → Disjoint R B → ∀ v : E,
      (∀ g ∈ L, dirDeriv_GTR I (ψ g) x v < 0) → 0 ≤ dirDeriv_GTR I b x v := by
    intro b B hb hb0 hB hRB v hv
    by_contra hneg
    push Not at hneg
    obtain ⟨t, ht1, ht2⟩ := ((eventually_chartLine_mem_GTR hx L ψ hψd hψ0 hv hR).and
      (eventually_chartLine_mem_one_GTR hx hb hb0 hneg hB)).exists
    exact Set.disjoint_left.1 hRB ht1 ht2
  -- hence it is positive on `v₀`
  have hpos : ∀ {b : M → ℝ} {B : Set M}, MDifferentiableAt I 𝓘(ℝ, ℝ) b x → b x = 0 →
      mfderiv I 𝓘(ℝ, ℝ) b x ≠ 0 → (∀ᶠ y in 𝓝 x, b y < 0 → y ∈ B) → Disjoint R B →
      0 < dirDeriv_GTR I b x v₀ := by
    intro b B hb hb0 hbd hB hRB
    obtain ⟨w, hw⟩ := exists_dirDeriv_neg_GTR hbd
    have hev : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ g ∈ L, dirDeriv_GTR I (ψ g) x (v₀ + s • w) < 0 := by
      rw [Filter.eventually_all_finset]
      intro g hg
      have hc : Continuous fun s : ℝ => dirDeriv_GTR I (ψ g) x (v₀ + s • w) := by
        simp only [dirDeriv_add_smul_GTR]
        exact continuous_const.add (continuous_id.mul continuous_const)
      refine hc.continuousAt.eventually_lt continuousAt_const ?_
      simpa using hv₀ g hg
    have hev' : ∀ᶠ s in 𝓝[>] (0 : ℝ), ∀ g ∈ L, dirDeriv_GTR I (ψ g) x (v₀ + s • w) < 0 :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds hev
    obtain ⟨s, hs, hspos⟩ := (hev'.and
      (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ))).exists
    have h := hcone hb hb0 hB hRB _ hs
    rw [dirDeriv_add_smul_GTR] at h
    have hspos' : (0 : ℝ) < s := hspos
    nlinarith
  have hp := hpos had ha0 hda hA hRA
  have hp' := hpos had' ha0' hda' hA' hRA'
  have hn : dirDeriv_GTR I a x (-v₀) < 0 := by rw [dirDeriv_neg_GTR]; linarith
  have hn' : dirDeriv_GTR I a' x (-v₀) < 0 := by rw [dirDeriv_neg_GTR]; linarith
  obtain ⟨t, ht1, ht2⟩ := ((eventually_chartLine_mem_one_GTR hx had ha0 hn hA).and
    (eventually_chartLine_mem_one_GTR hx had' ha0' hn' hA')).exists
  exact Set.disjoint_left.1 hAA' ht1 ht2

/-! ## The quadrant lemma -/

/-- Along a ray from `p`, a function vanishing at `p` with negative directional derivative is
eventually negative. -/
theorem eventually_neg_of_hasFDerivAt_GTR {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : F → ℝ} {ℓ : F →L[ℝ] ℝ} {p : F} (hg : HasFDerivAt g ℓ p) (hg0 : g p = 0) {v : F}
    (hv : ℓ v < 0) : ∀ᶠ t in 𝓝[>] (0 : ℝ), g (p + t • v) < 0 := by
  have hline : HasDerivAt (fun t : ℝ => p + t • v) v 0 := by
    have h1 := HasDerivAt.smul_const (hasDerivAt_id (0 : ℝ)) v
    have h2 := HasDerivAt.const_add p h1
    simpa using h2
  have hcomp : HasDerivAt (fun t : ℝ => g (p + t • v)) (ℓ v) 0 := by
    have hg' : HasFDerivAt g ℓ (p + (0 : ℝ) • v) := by simpa using hg
    exact hg'.comp_hasDerivAt (0 : ℝ) hline
  have hslope := hcomp.tendsto_slope_zero_right
  filter_upwards [hslope (Iio_mem_nhds hv), self_mem_nhdsWithin] with t ht htpos
  simp only [mem_preimage, mem_Iio, zero_add, zero_smul, add_zero, smul_eq_mul, hg0,
    sub_zero] at ht
  have htpos' : (0 : ℝ) < t := htpos
  by_contra hcon
  push Not at hcon
  have := mul_nonneg (inv_nonneg.2 htpos'.le) hcon
  linarith

/-- The decomposition of a linear functional on `ℝ × ℝ` on the standard basis. -/
theorem apply_eq_basis_GTR (ℓ : ℝ × ℝ →L[ℝ] ℝ) (v : ℝ × ℝ) :
    ℓ v = v.1 * ℓ (1, 0) + v.2 * ℓ (0, 1) := by
  have hv : v = v.1 • ((1 : ℝ), (0 : ℝ)) + v.2 • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  conv_lhs => rw [hv]
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

/-- **The quadrant lemma.** Near `0 ∈ ℝ × ℝ`, the closed quadrant `{0 ≤ x, 0 ≤ y}` is not the
sublevel set `{g ≤ 0}` of a function `g` with `g 0 = 0` and a nonzero derivative at `0`. -/
theorem not_eventually_quadrant_iff_GTR {g : ℝ × ℝ → ℝ} {ℓ : ℝ × ℝ →L[ℝ] ℝ}
    (hg : HasFDerivAt g ℓ 0) (hg0 : g 0 = 0) (hℓ : ℓ ≠ 0) :
    ¬ ∀ᶠ q in 𝓝 (0 : ℝ × ℝ), (g q ≤ 0 ↔ 0 ≤ q.1 ∧ 0 ≤ q.2) := by
  intro hQ
  have hray : ∀ v : ℝ × ℝ, ∀ᶠ t in 𝓝[>] (0 : ℝ),
      (g (t • v) ≤ 0 ↔ 0 ≤ (t • v).1 ∧ 0 ≤ (t • v).2) := by
    intro v
    have ht : Tendsto (fun t : ℝ => t • v) (𝓝[>] 0) (𝓝 0) := by
      have h : Tendsto (fun t : ℝ => t • v) (𝓝 0) (𝓝 ((0 : ℝ) • v)) :=
        (continuous_id.smul continuous_const).tendsto 0
      rw [zero_smul] at h
      exact h.mono_left nhdsWithin_le_nhds
    exact ht.eventually hQ
  have hneg : ∀ v : ℝ × ℝ, ℓ v < 0 → ∀ᶠ t in 𝓝[>] (0 : ℝ), g (t • v) < 0 := by
    intro v hv
    simpa using eventually_neg_of_hasFDerivAt_GTR hg hg0 hv
  have hpos : ∀ v : ℝ × ℝ, 0 < ℓ v → ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < g (t • v) := by
    intro v hv
    have h := eventually_neg_of_hasFDerivAt_GTR hg.neg (by simp [hg0]) (v := v)
      (by simpa using hv)
    filter_upwards [h] with t ht
    simp only [zero_add, Pi.neg_apply] at ht
    linarith
  have hin : ∀ v : ℝ × ℝ, ℓ v < 0 → 0 ≤ v.1 ∧ 0 ≤ v.2 := by
    intro v hv
    obtain ⟨t, h1, h2, ht⟩ := ((hneg v hv).and ((hray v).and self_mem_nhdsWithin)).exists
    have htpos : (0 : ℝ) < t := ht
    have h3 := h2.1 h1.le
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h3
    exact ⟨nonneg_of_mul_nonneg_right h3.1 htpos, nonneg_of_mul_nonneg_right h3.2 htpos⟩
  have hout : ∀ v : ℝ × ℝ, 0 < ℓ v → ¬ (0 ≤ v.1 ∧ 0 ≤ v.2) := by
    intro v hv hvq
    obtain ⟨t, h1, h2, ht⟩ := ((hpos v hv).and ((hray v).and self_mem_nhdsWithin)).exists
    have htpos : (0 : ℝ) < t := ht
    have h3 : 0 ≤ (t • v).1 ∧ 0 ≤ (t • v).2 := by
      simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      exact ⟨mul_nonneg htpos.le hvq.1, mul_nonneg htpos.le hvq.2⟩
    have := h2.2 h3
    linarith
  set α := ℓ (1, 0)
  set β := ℓ (0, 1)
  have hab : β ≤ α := by
    by_contra hcon
    push Not at hcon
    have h := hin (1, -1) (by rw [apply_eq_basis_GTR]; simp; linarith)
    norm_num at h
  have hba : α ≤ β := by
    by_contra hcon
    push Not at hcon
    have h := hin (-1, 1) (by rw [apply_eq_basis_GTR]; simp; linarith)
    norm_num at h
  have hα : α ≤ 0 := by
    by_contra hcon
    push Not at hcon
    exact hout (1, 1) (by rw [apply_eq_basis_GTR]; simp; linarith) (by norm_num)
  have hα' : α ≠ 0 := by
    intro h0
    apply hℓ
    refine ContinuousLinearMap.ext fun v => ?_
    rw [apply_eq_basis_GTR]
    simp only [zero_apply]
    have hβ0 : β = 0 := by linarith
    change v.1 * α + v.2 * β = 0
    rw [h0, hβ0]
    ring
  have h := hin (2, -1) (by
    rw [apply_eq_basis_GTR]
    have : α < 0 := lt_of_le_of_ne hα hα'
    simp only
    linarith)
  norm_num at h

end GC.GraphManifold.Assembly.FC39P0

