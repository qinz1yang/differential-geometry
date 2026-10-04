import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveSplitCappedModel
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.OriginalTubularEmbedding
import DifferentialGeometry.Topology.ThreeManifold.PrimeDecomposition.Irreducible
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Open
import DifferentialGeometry.Topology.Manifold.ProductSectionEmbedding

/-!
# Assembly of the split tube

Lane N2c, tier 1 (assembly). `SplitCharts M` packages three maps into a smooth `3`-manifold
`M`: `solid` (the solid torus over the disc of radius `3`), `hostMap` (the host over the round
pants) and `seam` (the seam chart), local diffeomorphisms on the interiors, injective there,
with disjoint interior images, the seam torus disjoint from both, and the seam chart reading
`solid` for negative and `hostMap` for positive height through the linear matching
`(t₁, t₂) ↦ (t₂^{e₀}, t₁^{e₁} t₂^d)`. `tubeMap` sweeps the levels `h` of the split sphere: the
meridian disc `solid (6 (x₁ + i x₂), tubeFibre e₀ s h)` on the caps, the fibre cylinder
`hostMap (bandModel …)` on the band, and the seam chart on the two junction circles. It agrees
with the seam chart near the junctions (`tubeMap_eq_seam`), is a local diffeomorphism
(`isLocalDiffeomorphAt_tubeMap`) and is injective (`tubeMap_injOn`) for `|h| < 3`, hence an open
embedding of `S² × (-3, 3)`, whose restriction to `S² × [-2, 2]` is the one-tube system
`SplitCharts.tubeSystem` with middle sphere `tubeMap (·, 0)`.
-/

set_option autoImplicit false

noncomputable section
open Set Filter Function Metric
open DifferentialGeometry DifferentialGeometry.Topology
open scoped Manifold ContDiff Topology

namespace GC.Seifert.SplitTube

local notation "S2" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

local instance : Fact ((-2 : ℝ) < 2) := ⟨by norm_num⟩

theorem circleExp_zpow (a : ℝ) (n : ℤ) : Circle.exp a ^ n = Circle.exp (n * a) := by
  apply Circle.ext
  rw [Circle.coe_zpow, Circle.coe_exp, Circle.coe_exp, ← Complex.exp_int_mul]
  push_cast
  ring_nf

theorem tubeFibre_zpow {e : ℤ} (he : e = 1 ∨ e = -1) (s : Bool) (h : ℝ) :
    tubeFibre e s h ^ e = Circle.exp ((if s then 1 else -1) * hostTheta h) := by
  rw [tubeFibre, circleExp_zpow]
  congr 1
  have : (e : ℝ) * e = 1 := by rcases he with rfl | rfl <;> norm_num
  calc (e : ℝ) * (e * (if s then 1 else -1) * hostTheta h) =
      ((e : ℝ) * e) * ((if s then 1 else -1) * hostTheta h) := by ring
    _ = _ := by rw [this, one_mul]

theorem tubeFibre_zpow_d (e d : ℤ) (s : Bool) (h : ℝ) :
    tubeFibre e s h ^ d = Circle.exp (e * d * (if s then 1 else -1) * hostTheta h) := by
  rw [tubeFibre, circleExp_zpow]
  congr 1
  ring

theorem latRadius_heightOf (p : S2) : latRadius (heightOf p) = ‖planeOf p‖ :=
  (norm_planeOf p).symm

theorem seamHeight_neg_iff (p : S2) :
    seamHeight (heightOf p) < 0 ↔ ‖planeOf p‖ < 1 / 2 := by
  rw [seamHeight, latRadius_heightOf]
  constructor <;> intro h <;> linarith

theorem heightOf_ne_zero_of_seamHeight_lt {p : S2} (h : seamHeight (heightOf p) < 1 / 2) :
    1 / 2 < |heightOf p| := by
  have h1 := planeOf_sq_add p
  rw [seamHeight, latRadius_heightOf] at h
  have h2 : ‖planeOf p‖ < 5 / 8 := by linarith
  have h3 : ‖planeOf p‖ ^ 2 < 25 / 64 := by nlinarith [norm_nonneg (planeOf p)]
  have h4 : 1 / 4 < |heightOf p| ^ 2 := by rw [sq_abs]; linarith
  nlinarith [abs_nonneg (heightOf p)]

theorem abs_heightOf_lt_of_seamHeight_pos {p : S2} (h : 0 < seamHeight (heightOf p)) :
    |heightOf p| < 1 := by
  have h1 := planeOf_sq_add p
  rw [seamHeight, latRadius_heightOf] at h
  have h2 : 1 / 4 < ‖planeOf p‖ ^ 2 := by nlinarith [norm_nonneg (planeOf p)]
  have h4 : |heightOf p| ^ 2 < 3 / 4 := by rw [sq_abs]; linarith
  nlinarith [abs_nonneg (heightOf p)]

theorem abs_heightOf_lt_of_seamHeight_gt {p : S2} (h : -1 < seamHeight (heightOf p)) :
    |heightOf p| < 1 := by
  have h1 := planeOf_sq_add p
  rw [seamHeight, latRadius_heightOf] at h
  have h2 : 1 / 16 < ‖planeOf p‖ ^ 2 := by nlinarith [norm_nonneg (planeOf p)]
  have h4 : |heightOf p| ^ 2 < 1 := by rw [sq_abs]; linarith
  nlinarith [abs_nonneg (heightOf p)]

theorem continuous_seamHeight_heightOf :
    Continuous fun q : S2 × ℝ => seamHeight (heightOf q.1) := by
  unfold seamHeight latRadius
  exact (continuous_const.mul ((continuous_const.sub
    ((contMDiff_heightOf.continuous.comp continuous_fst).pow 2)).sqrt)).sub continuous_const

theorem hostRadius_ge_angleScale (l : ℕ) {r h : ℝ} (hr0 : 0 ≤ r) (hr : r < 1 / 2)
    (hh : |h| < 3) : angleScale h ≤ hostRadius l r := by
  have h1 := angleScale_le h
  have h2 := abs_tubeSlope_mul_lt hh
  have h3 : (tubeSlope * h) ^ 2 < 1 / 100 := by
    rw [← sq_abs]
    nlinarith [abs_nonneg (tubeSlope * h)]
  have h4 : angleScale h ≤ 1 + 1 / 100 := by linarith
  unfold hostRadius
  split_ifs
  · linarith
  · rw [le_div_iff₀ (by linarith)]
    have := mul_le_mul h4 (show 2 + r ≤ 2 + 1 / 2 by linarith) (by linarith)
      (by norm_num)
    linarith

variable (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

structure SplitCharts where
  host : Fin 3
  e₀ : ℤ
  e₁ : ℤ
  d : ℤ
  he₀ : e₀ = 1 ∨ e₀ = -1
  he₁ : e₁ = 1 ∨ e₁ = -1
  δ : ℝ
  hδ : 0 < δ
  hδ1 : δ ≤ 1 / 2
  solid : ℂ × Circle → M
  hostMap : ℂ × Circle → M
  seam : GC.Endpoint.Torus × ℝ → M
  solid_local : ∀ q : ℂ × Circle, ‖q.1‖ < 3 →
    IsLocalDiffeomorphAt (𝓘(ℝ, ℂ).prod (𝓡 1)) (𝓡 3) ∞ solid q
  host_local : ∀ q : ℂ × Circle, q.1 ∈ pantsInterior →
    IsLocalDiffeomorphAt (𝓘(ℝ, ℂ).prod (𝓡 1)) (𝓡 3) ∞ hostMap q
  seam_local : ∀ q : GC.Endpoint.Torus × ℝ, |q.2| < δ →
    IsLocalDiffeomorphAt GC.Endpoint.signedCollarModel (𝓡 3) ∞ seam q
  solid_inj : ∀ q q' : ℂ × Circle, ‖q.1‖ < 3 → ‖q'.1‖ < 3 → solid q = solid q' → q = q'
  host_inj : ∀ q q' : ℂ × Circle, q.1 ∈ pantsInterior → q'.1 ∈ pantsInterior →
    hostMap q = hostMap q' → q = q'
  seam_inj : ∀ t t' : GC.Endpoint.Torus, seam (t, 0) = seam (t', 0) → t = t'
  solid_ne_host : ∀ q q' : ℂ × Circle, ‖q.1‖ < 3 → q'.1 ∈ pantsInterior → solid q ≠ hostMap q'
  seam_ne_solid : ∀ (t : GC.Endpoint.Torus) (q : ℂ × Circle), ‖q.1‖ < 3 → seam (t, 0) ≠ solid q
  seam_ne_host : ∀ (t : GC.Endpoint.Torus) (q : ℂ × Circle), q.1 ∈ pantsInterior →
    seam (t, 0) ≠ hostMap q
  seam_neg : ∀ (t : GC.Endpoint.Torus) (r : ℝ), -δ < r → r < 0 →
    seam (t, r) = solid ((3 + 3 * r / 2 : ℝ) • (t.1 : ℂ), t.2)
  seam_pos : ∀ (t : GC.Endpoint.Torus) (r : ℝ), 0 < r → r < δ →
    seam (t, r) = hostMap (planarCollarFormula 3 host (((t.2 ^ e₀ : Circle) : ℂ), r),
      t.1 ^ e₁ * t.2 ^ d)

variable {M}

namespace SplitCharts

variable (C : SplitCharts M)

def side (q : S2 × ℝ) : Bool := decide (0 < heightOf q.1)

def tubeMap (q : S2 × ℝ) : M :=
  if seamHeight (heightOf q.1) < 0 then C.solid (capModel C.e₀ (side q) q)
  else if 0 < seamHeight (heightOf q.1) then C.hostMap (bandModel C.e₀ C.e₁ C.d C.host q)
  else C.seam (seamModel C.e₀ (side q) q)

theorem side_eq_of_sgnR {s : Bool} {q : S2 × ℝ} (h : 0 < sgnR s * heightOf q.1) : side q = s := by
  unfold side
  cases s <;> simp only [sgnR, Bool.false_eq_true, ite_false, ite_true] at h
  · simp only [decide_eq_false_iff_not, not_lt]
    linarith
  · simp only [decide_eq_true_eq]
    linarith

theorem sgnR_side_pos {q : S2 × ℝ} (h : heightOf q.1 ≠ 0) : 0 < sgnR (side q) * heightOf q.1 := by
  unfold side sgnR
  by_cases h0 : 0 < heightOf q.1
  · simp [h0]
  · have : heightOf q.1 < 0 := lt_of_le_of_ne (not_lt.mp h0) h
    simp [h0]
    linarith

theorem seam_seamModel_of_neg {q : S2 × ℝ} (s : Bool) (hr : -C.δ < seamHeight (heightOf q.1))
    (hr0 : seamHeight (heightOf q.1) < 0) :
    C.seam (seamModel C.e₀ s q) = C.solid (capModel C.e₀ s q) := by
  unfold seamModel capModel
  rw [C.seam_neg _ _ hr hr0]
  congr 1
  refine Prod.ext ?_ rfl
  simp only
  have hu := GC.GraphManifold.norm_smul_unitOf (planeOf q.1)
  have e : (3 + 3 * seamHeight (heightOf q.1) / 2 : ℝ) = 6 * ‖planeOf q.1‖ := by
    rw [seamHeight, latRadius_heightOf]
    ring
  rw [e, mul_smul, hu]

theorem seam_seamModel_of_pos {q : S2 × ℝ} (hr0 : 0 < seamHeight (heightOf q.1))
    (hr : seamHeight (heightOf q.1) < C.δ) (hh : |q.2| < 3) :
    C.seam (seamModel C.e₀ (side q) q) = C.hostMap (bandModel C.e₀ C.e₁ C.d C.host q) := by
  have hδ := C.hδ1
  have hx := heightOf_ne_zero_of_seamHeight_lt (p := q.1) (by linarith)
  have hR := hostRadius_ge_angleScale C.host.val hr0.le (by linarith) hh
  have hr2 : -2 < seamHeight (heightOf q.1) := by linarith
  unfold seamModel bandModel
  rw [C.seam_pos _ _ hr0 hr]
  congr 1
  rcases lt_or_gt_of_ne (show heightOf q.1 ≠ 0 by intro h0; rw [h0, abs_zero] at hx; linarith)
    with hneg | hpos
  · have hs : side q = false := by simp [side, not_lt.mpr hneg.le]
    have hx' : heightOf q.1 ≤ -1 / 2 := by
      rw [abs_of_neg hneg] at hx
      linarith
    rw [hs]
    refine Prod.ext ?_ ?_
    · simp only
      rw [bandBase, bandHeight_of_le _ hx', neg_div, strip_bot _ hR, tubeFibre_zpow C.he₀,
        ← hostChart_collar C.host _ hr2]
      congr 2
      rw [Circle.coe_exp]
      push_cast
      ring_nf
    · simp only
      rw [tubeFibre_zpow_d, bandPhase, smoothSign_of_le hx']
      simp
  · have hs : side q = true := by simp [side, hpos]
    have hx' : 1 / 2 ≤ heightOf q.1 := by
      rw [abs_of_pos hpos] at hx
      linarith
    rw [hs]
    refine Prod.ext ?_ ?_
    · simp only
      rw [bandBase, bandHeight_of_ge _ hx', strip_top _ hR, tubeFibre_zpow C.he₀,
        ← hostChart_collar C.host _ hr2]
      congr 2
      rw [Circle.coe_exp]
      simp
    · simp only
      rw [tubeFibre_zpow_d, bandPhase, smoothSign_of_ge hx']
      simp

theorem tubeMap_eq_seam {q : S2 × ℝ} (hr : |seamHeight (heightOf q.1)| < C.δ) (hh : |q.2| < 3) :
    C.tubeMap q = C.seam (seamModel C.e₀ (side q) q) := by
  have hr' := abs_lt.mp hr
  unfold tubeMap
  split_ifs with h1 h2
  · exact (C.seam_seamModel_of_neg (side q) hr'.1 h1).symm
  · exact (C.seam_seamModel_of_pos h2 hr'.2 hh).symm
  · rfl

theorem isLocalDiffeomorphAt_tubeMap {q : S2 × ℝ} (hh : |q.2| < 3) :
    IsLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ C.tubeMap q := by
  have hcont := continuous_seamHeight_heightOf
  have hcx : Continuous fun q : S2 × ℝ => heightOf q.1 :=
    contMDiff_heightOf.continuous.comp continuous_fst
  rcases lt_trichotomy (seamHeight (heightOf q.1)) 0 with hneg | hzero | hpos
  · have hx := heightOf_ne_zero_of_seamHeight_lt (p := q.1) (by linarith)
    have hx0 : heightOf q.1 ≠ 0 := fun h0 => by rw [h0, abs_zero] at hx; linarith
    set s := side q with hsdef
    have hs : 0 < sgnR s * heightOf q.1 := sgnR_side_pos hx0
    let U : Set (S2 × ℝ) := {q' | seamHeight (heightOf q'.1) < 0 ∧ 0 < sgnR s * heightOf q'.1}
    have hU : IsOpen U := (isOpen_lt hcont continuous_const).inter
      (isOpen_lt continuous_const (continuous_const.mul hcx))
    have heq : C.tubeMap =ᶠ[𝓝 q] C.solid ∘ capModel C.e₀ s := by
      refine Filter.eventuallyEq_of_mem (hU.mem_nhds ⟨hneg, hs⟩) fun q' hq' => ?_
      have hside := side_eq_of_sgnR hq'.2
      simp only [Function.comp_apply, tubeMap, hq'.1, ↓reduceIte, hside]
    refine IsLocalDiffeomorphAt.of_eventuallyEq heq ?_
    have hnorm : ‖(capModel C.e₀ s q).1‖ < 3 := by
      simp only [capModel, norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 6)]
      have := (seamHeight_neg_iff q.1).mp hneg
      linarith
    exact (isLocalDiffeomorphAt_capModel C.he₀ s hs).comp (𝓡 3) M (C.solid_local _ hnorm)
  · have hx := heightOf_ne_zero_of_seamHeight_lt (p := q.1) (by linarith)
    have hx0 : heightOf q.1 ≠ 0 := fun h0 => by rw [h0, abs_zero] at hx; linarith
    have hx1 := abs_heightOf_lt_of_seamHeight_gt (p := q.1) (by linarith)
    set s := side q with hsdef
    have hs : 0 < sgnR s * heightOf q.1 := sgnR_side_pos hx0
    let U : Set (S2 × ℝ) := {q' | |seamHeight (heightOf q'.1)| < C.δ ∧
      0 < sgnR s * heightOf q'.1 ∧ |q'.2| < 3}
    have hU : IsOpen U := (isOpen_lt (continuous_abs.comp hcont) continuous_const).inter
      ((isOpen_lt continuous_const (continuous_const.mul hcx)).inter
        (isOpen_lt (continuous_abs.comp continuous_snd) continuous_const))
    have hqU : q ∈ U := ⟨by rw [hzero, abs_zero]; exact C.hδ, hs, hh⟩
    have heq : C.tubeMap =ᶠ[𝓝 q] C.seam ∘ seamModel C.e₀ s := by
      refine Filter.eventuallyEq_of_mem (hU.mem_nhds hqU) fun q' hq' => ?_
      have hside := side_eq_of_sgnR hq'.2.1
      rw [Function.comp_apply, C.tubeMap_eq_seam hq'.1 hq'.2.2, hside]
    refine IsLocalDiffeomorphAt.of_eventuallyEq heq ?_
    refine (isLocalDiffeomorphAt_seamModel C.he₀ s hx1 hx0).comp (𝓡 3) M (C.seam_local _ ?_)
    change |seamHeight (heightOf q.1)| < C.δ
    rw [hzero, abs_zero]
    exact C.hδ
  · have hx1 := abs_heightOf_lt_of_seamHeight_pos hpos
    obtain ⟨hmem, hne⟩ := hostChart_strip_mem C.host hx1 hpos hh
    let U : Set (S2 × ℝ) := {q' | 0 < seamHeight (heightOf q'.1)}
    have hU : IsOpen U := isOpen_lt continuous_const hcont
    have heq : C.tubeMap =ᶠ[𝓝 q] C.hostMap ∘ bandModel C.e₀ C.e₁ C.d C.host := by
      refine Filter.eventuallyEq_of_mem (hU.mem_nhds hpos) fun q' hq' => ?_
      have hq'' : ¬ seamHeight (heightOf q'.1) < 0 := not_lt.mpr (le_of_lt hq')
      have hq''' : 0 < seamHeight (heightOf q'.1) := hq'
      simp only [Function.comp_apply, tubeMap, hq'', hq''', ↓reduceIte]
    refine IsLocalDiffeomorphAt.of_eventuallyEq heq ?_
    exact (isLocalDiffeomorphAt_bandModel C.e₀ C.e₁ C.d C.he₁ C.host hx1 hne).comp (𝓡 3) M
      (C.host_local _ hmem)

theorem tubeMap_of_neg {q : S2 × ℝ} (h : seamHeight (heightOf q.1) < 0) :
    C.tubeMap q = C.solid (capModel C.e₀ (side q) q) := by
  simp only [tubeMap, h, ↓reduceIte]

theorem tubeMap_of_pos {q : S2 × ℝ} (h : 0 < seamHeight (heightOf q.1)) :
    C.tubeMap q = C.hostMap (bandModel C.e₀ C.e₁ C.d C.host q) := by
  have h' : ¬ seamHeight (heightOf q.1) < 0 := not_lt.mpr h.le
  simp only [tubeMap, h, h', ↓reduceIte]

theorem tubeMap_of_zero {q : S2 × ℝ} (h : seamHeight (heightOf q.1) = 0) :
    C.tubeMap q = C.seam (seamModel C.e₀ (side q) q) := by
  have h1 : ¬ seamHeight (heightOf q.1) < 0 := by rw [h]; exact lt_irrefl 0
  have h2 : ¬ 0 < seamHeight (heightOf q.1) := by rw [h]; exact lt_irrefl 0
  simp only [tubeMap, h1, h2, ↓reduceIte]

theorem seamModel_of_zero {e : ℤ} {s : Bool} {q : S2 × ℝ} (h : seamHeight (heightOf q.1) = 0) :
    seamModel e s q = ((GC.GraphManifold.unitOf (planeOf q.1), tubeFibre e s q.2), 0) := by
  simp only [seamModel, h]

theorem heightOf_eq_of_abs {q q' : S2 × ℝ} (habs : |heightOf q.1| = |heightOf q'.1|)
    (hs : side q = side q') (hx : heightOf q.1 ≠ 0) (hx' : heightOf q'.1 ≠ 0) :
    heightOf q.1 = heightOf q'.1 := by
  unfold side at hs
  rcases lt_or_gt_of_ne hx with h | h <;> rcases lt_or_gt_of_ne hx' with h' | h'
  · rw [abs_of_neg h, abs_of_neg h'] at habs; linarith
  · simp [not_lt.mpr h.le, h'] at hs
  · simp [h, not_lt.mpr h'.le] at hs
  · rw [abs_of_pos h, abs_of_pos h'] at habs; exact habs

theorem abs_heightOf_eq_of_norm {p p' : S2} (h : ‖planeOf p‖ = ‖planeOf p'‖) :
    |heightOf p| = |heightOf p'| := by
  have h1 := planeOf_sq_add p
  have h2 := planeOf_sq_add p'
  rw [h] at h1
  have : |heightOf p| ^ 2 = |heightOf p'| ^ 2 := by rw [sq_abs, sq_abs]; linarith
  exact (sq_eq_sq₀ (abs_nonneg _) (abs_nonneg _)).mp this

theorem planeOf_eq_of_unitOf {p p' : S2}
    (hu : GC.GraphManifold.unitOf (planeOf p) = GC.GraphManifold.unitOf (planeOf p'))
    (hn : ‖planeOf p‖ = ‖planeOf p'‖) : planeOf p = planeOf p' := by
  rw [← GC.GraphManifold.norm_smul_unitOf (planeOf p),
    ← GC.GraphManifold.norm_smul_unitOf (planeOf p'), hu, hn]

theorem tubeMap_injOn {q q' : S2 × ℝ} (hh : |q.2| < 3) (hh' : |q'.2| < 3)
    (heq : C.tubeMap q = C.tubeMap q') : q = q' := by
  have key : ∀ {q q' : S2 × ℝ}, planeOf q.1 = planeOf q'.1 → heightOf q.1 = heightOf q'.1 →
      q.2 = q'.2 → q = q' := fun h1 h2 h3 => Prod.ext (eq_of_planeOf_heightOf h1 h2) h3
  have hcap : ∀ {q : S2 × ℝ}, seamHeight (heightOf q.1) < 0 →
      ‖(capModel C.e₀ (side q) q).1‖ < 3 := by
    intro q h
    simp only [capModel, norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 6)]
    have := (seamHeight_neg_iff q.1).mp h
    linarith
  have hband : ∀ {q : S2 × ℝ}, 0 < seamHeight (heightOf q.1) → |q.2| < 3 →
      (bandModel C.e₀ C.e₁ C.d C.host q).1 ∈ pantsInterior := fun h hh =>
    (hostChart_strip_mem C.host (abs_heightOf_lt_of_seamHeight_pos h) h hh).1
  have hx0 : ∀ {q : S2 × ℝ}, seamHeight (heightOf q.1) < 1 / 2 → heightOf q.1 ≠ 0 := by
    intro q h h0
    have := heightOf_ne_zero_of_seamHeight_lt (p := q.1) h
    rw [h0, abs_zero] at this
    linarith
  rcases lt_trichotomy (seamHeight (heightOf q.1)) 0 with h1 | h1 | h1 <;>
    rcases lt_trichotomy (seamHeight (heightOf q'.1)) 0 with h2 | h2 | h2
  · rw [C.tubeMap_of_neg h1, C.tubeMap_of_neg h2] at heq
    have e := C.solid_inj _ _ (hcap h1) (hcap h2) heq
    simp only [capModel, Prod.mk.injEq] at e
    obtain ⟨hs, hhh⟩ := tubeFibre_injOn C.he₀ hh hh' e.2
    have hp : planeOf q.1 = planeOf q'.1 := smul_right_injective ℂ (by norm_num : (6 : ℝ) ≠ 0) e.1
    refine key hp ?_ hhh
    exact heightOf_eq_of_abs (abs_heightOf_eq_of_norm (congrArg norm hp)) hs
      (hx0 (by linarith)) (hx0 (by linarith))
  · rw [C.tubeMap_of_neg h1, C.tubeMap_of_zero h2, seamModel_of_zero h2] at heq
    exact absurd heq.symm (C.seam_ne_solid _ _ (hcap h1))
  · rw [C.tubeMap_of_neg h1, C.tubeMap_of_pos h2] at heq
    exact absurd heq (C.solid_ne_host _ _ (hcap h1) (hband h2 hh'))
  · rw [C.tubeMap_of_zero h1, C.tubeMap_of_neg h2, seamModel_of_zero h1] at heq
    exact absurd heq (C.seam_ne_solid _ _ (hcap h2))
  · rw [C.tubeMap_of_zero h1, C.tubeMap_of_zero h2] at heq
    rw [seamModel_of_zero h1, seamModel_of_zero h2] at heq
    have e := C.seam_inj _ _ heq
    simp only [Prod.mk.injEq] at e
    obtain ⟨hs, hhh⟩ := tubeFibre_injOn C.he₀ hh hh' e.2
    have hn : ‖planeOf q.1‖ = ‖planeOf q'.1‖ := by
      rw [seamHeight, latRadius_heightOf] at h1 h2
      linarith
    refine key (planeOf_eq_of_unitOf e.1 hn) ?_ hhh
    exact heightOf_eq_of_abs (abs_heightOf_eq_of_norm hn) hs (hx0 (by linarith))
      (hx0 (by linarith))
  · rw [C.tubeMap_of_zero h1, C.tubeMap_of_pos h2, seamModel_of_zero h1] at heq
    exact absurd heq (C.seam_ne_host _ _ (hband h2 hh'))
  · rw [C.tubeMap_of_pos h1, C.tubeMap_of_neg h2] at heq
    exact absurd heq.symm (C.solid_ne_host _ _ (hcap h2) (hband h1 hh))
  · rw [C.tubeMap_of_pos h1, C.tubeMap_of_zero h2, seamModel_of_zero h2] at heq
    exact absurd heq.symm (C.seam_ne_host _ _ (hband h1 hh))
  · rw [C.tubeMap_of_pos h1, C.tubeMap_of_pos h2] at heq
    have e := C.host_inj _ _ (hband h1 hh) (hband h2 hh') heq
    simp only [bandModel, Prod.mk.injEq] at e
    have hx1 := abs_heightOf_lt_of_seamHeight_pos h1
    have hx2 := abs_heightOf_lt_of_seamHeight_pos h2
    obtain ⟨-, hne1⟩ := hostChart_strip_mem C.host hx1 h1 hh
    obtain ⟨-, hne2⟩ := hostChart_strip_mem C.host hx2 h2 hh'
    have hst := hostChart_injOn C.host hne1 hne2 e.1
    have hYh := (stripDiffeo C.host).injective hst
    simp only [Prod.mk.injEq] at hYh
    obtain ⟨hY, hhh⟩ := hYh
    rw [hhh] at hY
    have hb : bandHeight C.host.val (heightOf q.1) = bandHeight C.host.val (heightOf q'.1) := by
      have := angleScale_pos q'.2
      field_simp at hY
      exact hY
    have hx : heightOf q.1 = heightOf q'.1 :=
      (strictMonoOn_bandHeight C.host.val).injOn (abs_lt.mp hx1) (abs_lt.mp hx2) hb
    rw [hx, hhh] at e
    have hu := mul_right_cancel e.2
    have hu' : GC.GraphManifold.unitOf (planeOf q.1) = GC.GraphManifold.unitOf (planeOf q'.1) := by
      rw [← zpow_zpow_unit C.he₁ (GC.GraphManifold.unitOf (planeOf q.1)), hu,
        zpow_zpow_unit C.he₁]
    have hn : ‖planeOf q.1‖ = ‖planeOf q'.1‖ := by
      rw [← latRadius_heightOf, ← latRadius_heightOf, hx]
    exact key (planeOf_eq_of_unitOf hu' hn) hx hhh

section Tube

open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Topology.ThreeManifold.Surgery

theorem abs_lt_three_of_mem {q : S2 × ℝ} (hq : q ∈ bufferedCylinder (1 / 2)) : |q.2| < 3 := by
  have h : -(1 / 2 : ℝ)⁻¹ - 1 < q.2 ∧ q.2 < (1 / 2 : ℝ)⁻¹ + 1 := hq
  norm_num at h
  exact abs_lt.mpr h

def cylMap (q : bufferedCylinder (1 / 2)) : M := C.tubeMap q.1

theorem isLocalDiffeomorph_cylMap :
    IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ)) (𝓡 3) ∞ C.cylMap := fun q =>
  ((isLocalDiffeomorph_subtype_val (I := (𝓡 2).prod 𝓘(ℝ)) (bufferedCylinder (1 / 2))) q).comp
    (𝓡 3) M (C.isLocalDiffeomorphAt_tubeMap (abs_lt_three_of_mem q.2))

theorem injective_cylMap : Injective C.cylMap := fun q q' h =>
  Subtype.ext (C.tubeMap_injOn (abs_lt_three_of_mem q.2) (abs_lt_three_of_mem q'.2) h)

theorem isOpenEmbedding_cylMap : Topology.IsOpenEmbedding C.cylMap :=
  C.isLocalDiffeomorph_cylMap.isLocalHomeomorph.isOpenEmbedding_of_injective C.injective_cylMap

def sphere (z : S2) : M := C.tubeMap (z, 0)

variable [IsManifold (𝓡 3) ∞ M]

theorem isSmoothEmbedding_tube :
    Manifold.IsSmoothEmbedding ((𝓡 2).prod (𝓡∂ 1)) (𝓡 3) ∞
      (originalTubularMap (by norm_num) (by norm_num) C.cylMap) :=
  originalTubularMap_isSmoothEmbedding (𝓡 3) (by simp) _ _ _ C.isOpenEmbedding_cylMap
    C.isLocalDiffeomorph_cylMap

def sliceZero (z : S2) : bufferedCylinder (1 / 2) := ⟨(z, 0), by
  change -(1 / 2 : ℝ)⁻¹ - 1 < 0 ∧ (0 : ℝ) < (1 / 2 : ℝ)⁻¹ + 1
  norm_num⟩

theorem isSmoothEmbedding_sliceZero :
    Manifold.IsSmoothEmbedding (𝓡 2) ((𝓡 2).prod 𝓘(ℝ)) ∞ sliceZero := by
  apply DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_intoOpen (𝓡 2)
    ((𝓡 2).prod 𝓘(ℝ)) (bufferedCylinder (1 / 2)) sliceZero
  exact Manifold.isSmoothEmbedding_prodMk_const (I := 𝓡 2) (M := S2) (0 : ℝ)

omit [IsManifold (𝓡 3) ∞ M] in
theorem sphere_eq : C.sphere = C.cylMap ∘ sliceZero := rfl

theorem isSmoothEmbedding_sphere : Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ C.sphere := by
  have hc : Manifold.IsSmoothEmbedding ((𝓡 2).prod 𝓘(ℝ)) (𝓡 3) ∞ C.cylMap :=
    DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_of_isLocalDiffeomorph_of_injective
      C.isLocalDiffeomorph_cylMap C.injective_cylMap
  rw [sphere_eq]
  exact hc.comp isSmoothEmbedding_sliceZero (by simp)

end Tube

universe u

open DifferentialGeometry.Topology.ThreeManifold.Surgery in
def tubeSystem {Q : ClosedOrientedManifold.{u} 3} (C : SplitCharts Q.Carrier) :
    SphericalTubeSystem Q where
  Index := Unit
  tube _ := ⟨originalTubularMap (by norm_num) (by norm_num) C.cylMap,
    C.isSmoothEmbedding_tube.isEmbedding.continuous⟩
  smooth _ := C.isSmoothEmbedding_tube
  disjoint a b hab := (hab (Subsingleton.elim a b)).elim

theorem tubeMiddleSphere_tubeSystem {Q : ClosedOrientedManifold.{u} 3}
    (C : SplitCharts Q.Carrier) : GC.Endpoint.tubeMiddleSphere C.tubeSystem () = C.sphere :=
  rfl

end SplitCharts

end GC.Seifert.SplitTube
