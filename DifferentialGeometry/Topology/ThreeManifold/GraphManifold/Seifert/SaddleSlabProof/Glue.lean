import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.SaddleSlabProof.Pair

/-!
# The glued map between two one-saddle slabs

Lane RG03c. For strips `D`, `D'` with the same model, a level matching `ψ` and a map `h` of the
lower levels, `glue D D' ψ h` is defined by three formulas:
* on `regI D = χ (openBox 2ε)` it is the chart identity `mapI = χ' ∘ χ⁻¹`;
* on `regII D`, the points above level `f p + ε / 2` whose flow line meets the level `f p + ε` in
  `χ (topBox ε)`, it is `mapII`: flow down to level `f p + ε`, apply `χ' ∘ χ⁻¹`, flow up to level
  `ψ (f x)`;
* elsewhere it is `mapIII`: flow down to the lower level, apply `h`, flow up to level `ψ (f x)`.
`mem_regions`: every point of the slab lies in one of `regI D`, `regII D`, `lowDomain D`.
On their overlaps the formulas agree (`mapIII_eq_mapI`, `mapII_eq_mapI`, `mapII_eq_mapIII`)
as soon as `h (arc D σ t) = arc D' σ t` for the bottom points with `t² ≤ 2ε`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Topology DifferentialGeometry.Topology.Morse
open DifferentialGeometry.Topology.Morse.CellAttachment (morseNorm morseNormalForm)

namespace GC.Seifert.SaddleSlabProof

def topBox (ε : ℝ) : Set (MorseModel 2) := {y | |saddleQ y - ε| < ε / 2 ∧ |saddleK y| < 2 * ε}

theorem saddleBox_subset_openBox {ε : ℝ} (hε : 0 < ε) : saddleBox ε ⊆ openBox (2 * ε) :=
  fun _ hy => ⟨by linarith [hy.1], by linarith [hy.2]⟩

theorem isOpen_topBox (ε : ℝ) : IsOpen (topBox ε) :=
  (isOpen_lt (continuous_abs.comp (continuous_saddleQ.sub continuous_const)) continuous_const).inter
    (isOpen_lt (continuous_abs.comp continuous_saddleK) continuous_const)

variable {H H' : Type} [TopologicalSpace H] [TopologicalSpace H'] {M M' : Type*}
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace M'] [ChartedSpace H' M']
  {I : ModelWithCorners ℝ (MorseModel 2) H} {I' : ModelWithCorners ℝ (MorseModel 2) H'}
  [IsManifold I ∞ M] [IsManifold I' ∞ M'] {f : M → ℝ} {f' : M' → ℝ} {a b a' b' : ℝ} {p : M}
  {p' : M'}

theorem lt_rmD_of_bounds (D : GradientLikeStrip I f a b {p}) (hrm : 8 * (ch D).r₀ ≤ rmD D)
    {y : MorseModel 2} (hy : |saddleQ y| + |saddleK y| < 8 * eps D) :
    morseNorm 2 y < rmD D := by
  have hr := r₀_pos D
  have hn := normSq_le_two_mul y
  rw [morseNorm_lt_iff (by linarith)]
  unfold eps at hy
  nlinarith

theorem mem_ball_of_bounds (D : GradientLikeStrip I f a b {p}) (hrm : 8 * (ch D).r₀ ≤ rmD D)
    {y : MorseModel 2} (hy : |saddleQ y| + |saddleK y| < 8 * eps D) :
    y ∈ Metric.ball (0 : MorseModel 2) (ch D).R' :=
  lt_rmD_subset_ball D (lt_rmD_of_bounds D hrm hy)

theorem chart_symm_chart (D : GradientLikeStrip I f a b {p}) (hrm : 8 * (ch D).r₀ ≤ rmD D)
    {y : MorseModel 2} (hy : |saddleQ y| + |saddleK y| < 8 * eps D) :
    (ch D).χ.symm ((ch D).χ y) = y :=
  (ch D).χ.left_inv ((ch D).hball (mem_ball_of_bounds D hrm hy))

theorem f_chart_of_bounds (D : GradientLikeStrip I f a b {p}) (hk : (ch D).k = 1)
    (hrm : 8 * (ch D).r₀ ≤ rmD D) {y : MorseModel 2}
    (hy : |saddleQ y| + |saddleK y| < 8 * eps D) : f ((ch D).χ y) = f p + saddleQ y :=
  f_chart D hk (lt_rmD_of_bounds D hrm hy)

theorem bounds_of_openBox {ε : ℝ} {y : MorseModel 2} (hy : y ∈ openBox (2 * ε)) :
    |saddleQ y| + |saddleK y| < 8 * ε := by
  linarith [hy.1, hy.2, abs_nonneg (saddleQ y), abs_nonneg (saddleK y)]

theorem bounds_of_topBox {ε : ℝ} (hε : 0 < ε) {y : MorseModel 2} (hy : y ∈ topBox ε) :
    |saddleQ y| + |saddleK y| < 8 * ε := by
  have h1 := abs_lt.mp hy.1
  have h2 : |saddleQ y| < 2 * ε := abs_lt.mpr ⟨by linarith [h1.1], by linarith [h1.2]⟩
  linarith [hy.2]

variable [T2Space M] [T2Space M'] [I.Boundaryless] [I'.Boundaryless]

def regI (D : GradientLikeStrip I f a b {p}) : Set M := (ch D).χ '' openBox (2 * eps D)

def regII (D : GradientLikeStrip I f a b {p}) : Set M :=
  {x | f p + eps D / 2 < f x ∧ D.flow (f x - (f p + eps D)) x ∈ (ch D).χ '' topBox (eps D)}

def mapI (D : GradientLikeStrip I f a b {p}) (D' : GradientLikeStrip I' f' a' b' {p'})
    (x : M) : M' :=
  (ch D').χ ((ch D).χ.symm x)

def mapII (D : GradientLikeStrip I f a b {p}) (D' : GradientLikeStrip I' f' a' b' {p'})
    (ψ : ℝ → ℝ) (x : M) : M' :=
  D'.flow (-(ψ (f x) - (f' p' + eps D'))) (mapI D D' (D.flow (f x - (f p + eps D)) x))

def mapIII (D : GradientLikeStrip I f a b {p}) (D' : GradientLikeStrip I' f' a' b' {p'})
    (ψ : ℝ → ℝ) (h : M → M') (x : M) : M' :=
  D'.flow (-(ψ (f x) - a')) (h (D.π a x))

open Classical in
def glue (D : GradientLikeStrip I f a b {p}) (D' : GradientLikeStrip I' f' a' b' {p'})
    (ψ : ℝ → ℝ) (h : M → M') (x : M) : M' :=
  if x ∈ regI D then mapI D D' x else if x ∈ regII D then mapII D D' ψ x else mapIII D D' ψ h x

omit [T2Space M] [T2Space M'] [I.Boundaryless] [I'.Boundaryless] in
theorem boxSet_subset_regI (D : GradientLikeStrip I f a b {p}) : boxSet D ⊆ regI D :=
  image_mono (saddleBox_subset_openBox (eps_pos D))

theorem f_flow_to_level (D : GradientLikeStrip I f a b {p}) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hk : (ch D).k = 1) {x : M} {ℓ : ℝ} (hx : f x ∈ Icc a b) (hℓ : ℓ ∈ Icc a b)
    (hxp : f p + eps D / 2 ≤ f x) (hℓp : f p + eps D / 2 ≤ ℓ) :
    ∀ s ∈ uIcc 0 (f x - ℓ), f (D.flow s x) = f x - s :=
  GradientLikeStrip.f_flow_eq_sub_of_levels hf hx (by rw [sub_sub_cancel]; exact hℓ)
    fun y hy q hq hyq => by
      obtain rfl := Finset.mem_singleton.mp hq
      have h1 := abs_lt.mp (abs_f_sub_lt_of_mem_smallBall D hk hyq)
      rw [sub_sub_cancel, mem_uIcc] at hy
      unfold eps at hxp hℓp
      rcases hy with ⟨h2, -⟩ | ⟨h2, -⟩ <;> linarith [h1.2]

theorem mem_regions (D : GradientLikeStrip I f a b {p}) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hk : (ch D).k = 1) (hrm : 8 * (ch D).r₀ ≤ rmD D) (ha : a < f p - 2 * eps D)
    (hb : f p + 2 * eps D < b) {x : M} (hx : f x ∈ Icc a b) :
    x ∈ regI D ∨ x ∈ regII D ∨ x ∈ lowDomain D := by
  have hε := eps_pos D
  by_cases hbox : x ∈ boxSet D
  · exact Or.inl (boxSet_subset_regI D hbox)
  right
  by_cases hle : f x ≤ f p + eps D
  · right
    intro s hs
    rw [uIcc_of_le (by linarith [hx.1])] at hs
    exact flow_notMem_boxSet_desc D hf hk hrm hbox hle hx (T := f x - a) (by linarith) s hs
  push Not at hle
  set s₀ := f x - (f p + eps D) with hs₀
  set z := D.flow s₀ x with hz
  have hfz : f z = f p + eps D := by
    have h := f_flow_to_level D hf hk hx (ℓ := f p + eps D) ⟨by linarith, by linarith⟩
      (by linarith) (by linarith) s₀ right_mem_uIcc
    rw [hz, h, hs₀]
    ring
  by_cases hzb : z ∈ boxSet D
  · left
    refine ⟨by linarith, ?_⟩
    obtain ⟨w, hw, hwz⟩ := hzb
    refine ⟨w, ⟨?_, ?_⟩, hwz⟩
    · have h1 := f_chart D hk (saddleBox_subset_lt D hrm hw)
      rw [hwz, hfz] at h1
      have hq : saddleQ w = eps D := by linarith
      rw [hq, sub_self, abs_zero]
      linarith
    · have := hw.2
      unfold eps at hε ⊢
      linarith
  · right
    intro s hs
    have hs0 : 0 ≤ f x - a := by linarith [hx.1]
    rw [uIcc_of_le hs0] at hs
    rcases lt_trichotomy s s₀ with hlt | heq | hgt
    · intro hmem
      have h1 := (f_mem_of_mem_boxSet D hk hrm hmem).2
      have h2 := GradientLikeStrip.sub_le_f_flow (D := D) hf x hs.1
      unfold eps at hs₀ hle
      linarith
    · rw [heq]
      exact hzb
    · have hdesc := flow_notMem_boxSet_desc D hf hk hrm hzb hfz.le
        ⟨by rw [hfz]; linarith, by rw [hfz]; linarith⟩ (T := f p + eps D - a)
        (by rw [hfz]; linarith) (s - s₀) ⟨by linarith, by linarith [hs.2]⟩
      rwa [hz, ← GradientLikeStrip.flow_add, add_sub_cancel] at hdesc

omit [T2Space M] [T2Space M'] [I.Boundaryless] [I'.Boundaryless] in
theorem eps_eq (D : GradientLikeStrip I f a b {p}) (D' : GradientLikeStrip I' f' a' b' {p'})
    (hr : (ch D').r₀ = (ch D).r₀) : eps D' = eps D := by
  unfold eps
  rw [hr]

theorem arc_of_bottom (D : GradientLikeStrip I f a b {p}) {z : MorseModel 2} {σ : ℝ}
    (hzσ : z = footPt (eps D) σ (z 1)) :
    D.flow (f p - eps D - a) ((ch D).χ z) = arc D σ (z 1) := by
  unfold arc
  rw [← hzσ]

omit [T2Space M] [I.Boundaryless] in
theorem arc_of_bottom' (D : GradientLikeStrip I f a b {p})
    (D' : GradientLikeStrip I' f' a' b' {p'}) (hr : (ch D').r₀ = (ch D).r₀) {z : MorseModel 2}
    {σ : ℝ} (hzσ : z = footPt (eps D) σ (z 1)) :
    D'.flow (f' p' - eps D - a') ((ch D').χ z) = arc D' σ (z 1) := by
  unfold arc
  rw [eps_eq D D' hr, ← hzσ]

theorem mapIII_eq_mapI (D : GradientLikeStrip I f a b {p})
    (D' : GradientLikeStrip I' f' a' b' {p'})
    (hk : (ch D).k = 1) (hk' : (ch D').k = 1) (hr : (ch D').r₀ = (ch D).r₀)
    (hrm : 8 * (ch D).r₀ ≤ rmD D) (hrm' : 8 * (ch D').r₀ ≤ rmD D')
    (ha : a < f p - 2 * eps D) {ψ : ℝ → ℝ}
    (hψ : ∀ t ∈ Icc (f p - 2 * eps D) (f p + 2 * eps D), ψ t = t - f p + f' p') {h : M → M'}
    (hH : ∀ σ t, σ ^ 2 = 1 → t ^ 2 ≤ 2 * eps D → h (arc D σ t) = arc D' σ t) {x : M}
    (hI : x ∈ regI D) (hIII : x ∈ lowDomain D) : mapIII D D' ψ h x = mapI D D' x := by
  have hε := eps_pos D
  have hεr : (ch D).r₀ ^ 2 = eps D := rfl
  have hε' := eps_eq D D' hr
  obtain ⟨y, hy, rfl⟩ := hI
  have hyb := bounds_of_openBox hy
  have hfy := f_chart_of_bounds D hk hrm hyb
  have hQ := abs_lt.mp hy.1
  have hK := hy.2
  unfold mapI
  rw [chart_symm_chart D hrm hyb]
  by_cases hA : |saddleK y| ≤ eps D ∧ -eps D ≤ saddleQ y
  · exfalso
    by_cases hQe : saddleQ y ≤ eps D
    · apply hIII 0 left_mem_uIcc
      rw [GradientLikeStrip.flow_zero]
      exact ⟨y, ⟨abs_le.mpr ⟨hA.2, hQe⟩, hA.1⟩, rfl⟩
    · push Not at hQe
      obtain ⟨z, hz, -, hzq, hzk, -⟩ := flow_chart_pair D D' hk hk' hr hrm hrm'
        (y := y) (T := saddleQ y - eps D) 1 fun w hwk hwq => by
          rw [sub_sub_cancel, uIcc_of_ge hQe.le] at hwq
          refine ⟨good_of_bounds (r₀_pos D) (Or.inl ?_) ?_, coord_one_ne (Or.inr ?_)⟩
          · rw [abs_of_pos (by linarith [hwq.1]), show (ch D).r₀ ^ 2 = eps D from rfl]
            linarith [hwq.1]
          · rw [hwk, abs_of_pos (by linarith [hwq.1]), show (ch D).r₀ ^ 2 = eps D from rfl]
            linarith [hwq.2]
          · linarith [hwq.1]
      apply hIII (saddleQ y - eps D)
      · rw [hfy, uIcc_of_le (by linarith)]
        exact ⟨by linarith, by linarith⟩
      · rw [hz]
        refine ⟨z, ⟨abs_le.mpr ⟨by rw [hzq]; linarith, by rw [hzq]; linarith⟩, ?_⟩, rfl⟩
        rw [hzk]
        exact hA.1
  · have hcase : eps D < |saddleK y| ∨ saddleQ y < -eps D := by
      by_contra hc
      push Not at hc
      exact hA ⟨hc.1, hc.2⟩
    obtain ⟨z, hz, hz', hzq, hzk, -⟩ := flow_chart_pair D D' hk hk' hr hrm hrm'
      (y := y) (T := saddleQ y + eps D) 0 fun w hwk hwq => by
        rw [show saddleQ y - (saddleQ y + eps D) = -eps D by ring] at hwq
        have hwq' : |saddleQ w| < 2 * eps D := by
          rw [mem_uIcc] at hwq
          rw [abs_lt]
          rcases hwq with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;> linarith
        refine ⟨good_of_bounds (r₀_pos D) ?_ ?_, coord_zero_ne ?_⟩
        · rcases hcase with hc | hc
          · right
            rw [hwk]
            unfold eps at hc
            linarith
          · left
            rw [mem_uIcc] at hwq
            have : saddleQ w ≤ -eps D := by
              rcases hwq with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
            rw [abs_of_neg (by linarith)]
            unfold eps at this
            linarith
        · rw [hwk]
          unfold eps at hwq' hK
          linarith
        · rcases hcase with hc | hc
          · left
            rw [hwk]
            intro h0
            rw [h0, abs_zero] at hc
            linarith
          · right
            rw [mem_uIcc] at hwq
            rcases hwq with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
    have hzq' : saddleQ z = -eps D := by rw [hzq]; ring
    obtain ⟨σ, hσ, hzσ⟩ := eq_footPt_of_saddleQ hzq'
    have ht : z 1 ^ 2 ≤ 2 * eps D := sq_le_of_abs_saddleK_footPt hε hσ (by
      rw [← hzσ, hzk]
      unfold eps at hK ⊢
      linarith)
    have hπ : D.π a ((ch D).χ y) = arc D σ (z 1) := by
      change D.flow (f ((ch D).χ y) - a) ((ch D).χ y) = _
      rw [hfy, show f p + saddleQ y - a = (saddleQ y + eps D) + (f p - eps D - a) by ring,
        GradientLikeStrip.flow_add, hz, arc_of_bottom D hzσ]
    have hψy : ψ (f ((ch D).χ y)) = f' p' + saddleQ y := by
      rw [hfy, hψ _ ⟨by linarith [hQ.1], by linarith [hQ.2]⟩]
      ring
    unfold mapIII
    rw [hπ, hH σ (z 1) hσ ht, ← arc_of_bottom' D D' hr hzσ, hψy, GradientLikeStrip.flow_flow,
      show f' p' - eps D - a' + -(f' p' + saddleQ y - a') = -(saddleQ y + eps D) by ring, ← hz',
      GradientLikeStrip.flow_neg_flow]

theorem regII_data (D : GradientLikeStrip I f a b {p}) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hk : (ch D).k = 1) (hrm : 8 * (ch D).r₀ ≤ rmD D) (hb : f p + 2 * eps D < b)
    (ha : a < f p - 2 * eps D) {x : M} (hx : f x ∈ Icc a b) (hII : x ∈ regII D) :
    ∃ w ∈ topBox (eps D), saddleQ w = eps D ∧
      D.flow (f x - (f p + eps D)) x = (ch D).χ w := by
  have hε := eps_pos D
  obtain ⟨hfx, w, hw, hwx⟩ := hII
  have h1 := f_flow_to_level D hf hk hx (ℓ := f p + eps D) ⟨by linarith, by linarith⟩
    hfx.le (by linarith) (f x - (f p + eps D)) right_mem_uIcc
  have h2 := f_chart_of_bounds D hk hrm (bounds_of_topBox hε hw)
  rw [hwx, h1] at h2
  exact ⟨w, hw, by linarith, hwx.symm⟩

theorem mapII_eq_mapI (D : GradientLikeStrip I f a b {p})
    (D' : GradientLikeStrip I' f' a' b' {p'})
    (hk : (ch D).k = 1) (hk' : (ch D').k = 1) (hr : (ch D').r₀ = (ch D).r₀)
    (hrm : 8 * (ch D).r₀ ≤ rmD D) (hrm' : 8 * (ch D').r₀ ≤ rmD D') {ψ : ℝ → ℝ}
    (hψ : ∀ t ∈ Icc (f p - 2 * eps D) (f p + 2 * eps D), ψ t = t - f p + f' p') {x : M}
    (hI : x ∈ regI D) (hII : x ∈ regII D) : mapII D D' ψ x = mapI D D' x := by
  have hε := eps_pos D
  have hεr : (ch D).r₀ ^ 2 = eps D := rfl
  have hε' := eps_eq D D' hr
  obtain ⟨y, hy, rfl⟩ := hI
  have hyb := bounds_of_openBox hy
  have hfy := f_chart_of_bounds D hk hrm hyb
  have hQ := abs_lt.mp hy.1
  have hK := hy.2
  have hQy : eps D / 2 < saddleQ y := by have := hII.1; rw [hfy] at this; linarith
  obtain ⟨z, hz, hz', hzq, hzk, -⟩ := flow_chart_pair D D' hk hk' hr hrm hrm'
    (y := y) (T := saddleQ y - eps D) 1 fun w hwk hwq => by
      rw [sub_sub_cancel] at hwq
      have hw1 : eps D / 2 < saddleQ w := by
        rw [mem_uIcc] at hwq
        rcases hwq with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
      have hw2 : saddleQ w < 2 * eps D := by
        rw [mem_uIcc] at hwq
        rcases hwq with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
      refine ⟨good_of_bounds (r₀_pos D) (Or.inl ?_) ?_, coord_one_ne (Or.inr (by linarith))⟩
      · rw [abs_of_pos (by linarith), hεr]
        linarith
      · rw [hwk, abs_of_pos (by linarith), hεr]
        linarith
  have hzb : |saddleQ z| + |saddleK z| < 8 * eps D := by
    rw [hzq, hzk, show saddleQ y - (saddleQ y - eps D) = eps D by ring, abs_of_pos hε]
    linarith
  unfold mapII mapI
  rw [hfy, chart_symm_chart D hrm hyb, show f p + saddleQ y - (f p + eps D) =
    saddleQ y - eps D by ring, hz, chart_symm_chart D hrm hzb, ← hz',
    hψ _ ⟨by linarith, by linarith⟩, hε', show f p + saddleQ y - f p + f' p' - (f' p' + eps D) =
    saddleQ y - eps D by ring, GradientLikeStrip.flow_neg_flow]

theorem mapII_eq_mapIII (D : GradientLikeStrip I f a b {p})
    (D' : GradientLikeStrip I' f' a' b' {p'}) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hk : (ch D).k = 1) (hk' : (ch D').k = 1) (hr : (ch D').r₀ = (ch D).r₀)
    (hrm : 8 * (ch D).r₀ ≤ rmD D) (hrm' : 8 * (ch D').r₀ ≤ rmD D')
    (ha : a < f p - 2 * eps D) (hb : f p + 2 * eps D < b) {ψ : ℝ → ℝ} {h : M → M'}
    (hH : ∀ σ t, σ ^ 2 = 1 → t ^ 2 ≤ 2 * eps D → h (arc D σ t) = arc D' σ t) {x : M}
    (hx : f x ∈ Icc a b) (hII : x ∈ regII D) (hIII : x ∈ lowDomain D) :
    mapII D D' ψ x = mapIII D D' ψ h x := by
  have hε := eps_pos D
  have hεr : (ch D).r₀ ^ 2 = eps D := rfl
  have hε' := eps_eq D D' hr
  obtain ⟨w, hw, hwq, hwx⟩ := regII_data D hf hk hrm hb ha hx hII
  have hwb := bounds_of_topBox hε hw
  have hfx := hII.1
  set s₀ := f x - (f p + eps D) with hs₀
  have hKw : eps D < |saddleK w| := by
    by_contra hcon
    push Not at hcon
    by_cases hs : 0 ≤ s₀
    · apply hIII s₀
      · rw [uIcc_of_le (by linarith [hx.1])]
        exact ⟨hs, by linarith⟩
      · rw [hwx]
        refine ⟨w, ⟨abs_le.mpr ⟨by rw [hwq, hεr]; linarith, by rw [hwq, hεr]⟩, ?_⟩, rfl⟩
        rw [hεr]
        exact hcon
    · push Not at hs
      obtain ⟨z₀, hz₀, hz₀q, hz₀k, -⟩ := flow_chart_eq D hk (y := w) (T := -s₀) 1
        fun v hvk hvq => by
          rw [hwq, sub_neg_eq_add] at hvq
          have hv1 : eps D / 2 < saddleQ v ∧ saddleQ v ≤ eps D := by
            rw [mem_uIcc] at hvq
            rcases hvq with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;> linarith
          refine ⟨annulus_of_good D hrm (good_of_bounds (r₀_pos D) (Or.inl ?_) ?_),
            coord_one_ne (Or.inr (by linarith))⟩
          · rw [abs_of_pos (by linarith), hεr]
            linarith
          · rw [hvk, abs_of_pos (by linarith), hεr]
            linarith [hw.2]
      have hxz : x = (ch D).χ z₀ := by
        rw [← hz₀, ← hwx, GradientLikeStrip.flow_flow, add_neg_cancel,
          GradientLikeStrip.flow_zero]
      apply hIII 0 left_mem_uIcc
      rw [GradientLikeStrip.flow_zero, hxz]
      refine ⟨z₀, ⟨abs_le.mpr ⟨by rw [hz₀q, hwq, hεr]; linarith, by rw [hz₀q, hwq, hεr]; linarith⟩,
        ?_⟩, rfl⟩
      rw [hz₀k, hεr]
      exact hcon
  have hKw2 := hw.2
  obtain ⟨z, hz, hz', hzq, hzk, -⟩ := flow_chart_pair D D' hk hk' hr hrm hrm'
    (y := w) (T := 2 * eps D) 0 fun v hvk hvq => by
      rw [hwq, show eps D - 2 * eps D = -eps D by ring] at hvq
      have hv1 : |saddleQ v| ≤ eps D := by
        rw [mem_uIcc] at hvq
        rw [abs_le]
        rcases hvq with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;> linarith
      refine ⟨good_of_bounds (r₀_pos D) (Or.inr ?_) ?_, coord_zero_ne (Or.inl ?_)⟩
      · rw [hvk, hεr]
        linarith
      · rw [hvk, hεr]
        linarith
      · rw [hvk]
        intro h0
        rw [h0, abs_zero] at hKw
        linarith
  have hzq' : saddleQ z = -eps D := by rw [hzq, hwq]; ring
  obtain ⟨σ, hσ, hzσ⟩ := eq_footPt_of_saddleQ hzq'
  have ht : z 1 ^ 2 ≤ 2 * eps D := sq_le_of_abs_saddleK_footPt hε hσ (by
    rw [← hzσ, hzk]
    linarith)
  have hπ : D.π a x = arc D σ (z 1) := by
    change D.flow (f x - a) x = _
    rw [show f x - a = s₀ + (2 * eps D + (f p - eps D - a)) by rw [hs₀]; ring,
      GradientLikeStrip.flow_add, hwx, GradientLikeStrip.flow_add, hz, arc_of_bottom D hzσ]
  have hwb' : |saddleQ w| + |saddleK w| < 8 * eps D := hwb
  unfold mapIII mapII mapI
  rw [hπ, hH σ (z 1) hσ ht, ← arc_of_bottom' D D' hr hzσ, ← hz', hwx, chart_symm_chart D hrm hwb',
    GradientLikeStrip.flow_flow, GradientLikeStrip.flow_flow, hε']
  congr 1
  ring

omit [T2Space M] [T2Space M'] [I.Boundaryless] [I'.Boundaryless] in
theorem isOpen_regI (D : GradientLikeStrip I f a b {p}) (hrm : 8 * (ch D).r₀ ≤ rmD D) :
    IsOpen (regI D) :=
  ((ch D).χ.isOpen_image_iff_of_subset_source fun _ hy =>
    (ch D).hball (mem_ball_of_bounds D hrm (bounds_of_openBox hy))).2 (isOpen_openBox _)

omit [T2Space M] [T2Space M'] [I.Boundaryless] [I'.Boundaryless] in
theorem isOpen_chart_topBox (D : GradientLikeStrip I f a b {p}) (hrm : 8 * (ch D).r₀ ≤ rmD D) :
    IsOpen ((ch D).χ '' topBox (eps D)) :=
  ((ch D).χ.isOpen_image_iff_of_subset_source fun _ hy =>
    (ch D).hball (mem_ball_of_bounds D hrm (bounds_of_topBox (eps_pos D) hy))).2
    (isOpen_topBox _)

theorem isOpen_regII (D : GradientLikeStrip I f a b {p}) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hrm : 8 * (ch D).r₀ ≤ rmD D) : IsOpen (regII D) :=
  (isOpen_lt continuous_const hf.continuous).inter
    ((isOpen_chart_topBox D hrm).preimage (D.continuous_π hf (f p + eps D)))

omit [T2Space M] [T2Space M'] [I.Boundaryless] [I'.Boundaryless] in
theorem contMDiffAt_mapI (D : GradientLikeStrip I f a b {p})
    (D' : GradientLikeStrip I' f' a' b' {p'}) (hr : (ch D').r₀ = (ch D).r₀)
    (hrm : 8 * (ch D).r₀ ≤ rmD D) (hrm' : 8 * (ch D').r₀ ≤ rmD D') {y : MorseModel 2}
    (hy : |saddleQ y| + |saddleK y| < 8 * eps D) :
    ContMDiffAt I I' ∞ (mapI D D') ((ch D).χ y) := by
  have hball := mem_ball_of_bounds D hrm hy
  have hball' := mem_ball_of_bounds D' hrm' (by rw [eps_eq D D' hr]; exact hy)
  have h1 := (ch D).contMDiffAt_symm (mem_image_of_mem _ hball)
  have h2 := (ch D').contMDiffAt_chart hball'
  rw [← chart_symm_chart D hrm hy] at h2
  exact h2.comp ((ch D).χ y) h1

theorem glue_eq_mapI (D : GradientLikeStrip I f a b {p})
    (D' : GradientLikeStrip I' f' a' b' {p'}) (ψ : ℝ → ℝ) (h : M → M') {x : M}
    (hx : x ∈ regI D) : glue D D' ψ h x = mapI D D' x := by
  unfold glue
  rw [ite_eq_left hx]

theorem glue_eq_mapII (D : GradientLikeStrip I f a b {p})
    (D' : GradientLikeStrip I' f' a' b' {p'})
    (hk : (ch D).k = 1) (hk' : (ch D').k = 1) (hr : (ch D').r₀ = (ch D).r₀)
    (hrm : 8 * (ch D).r₀ ≤ rmD D) (hrm' : 8 * (ch D').r₀ ≤ rmD D') {ψ : ℝ → ℝ}
    (hψ : ∀ t ∈ Icc (f p - 2 * eps D) (f p + 2 * eps D), ψ t = t - f p + f' p') (h : M → M')
    {x : M} (hx : x ∈ regII D) : glue D D' ψ h x = mapII D D' ψ x := by
  unfold glue
  by_cases hI : x ∈ regI D
  · rw [ite_eq_left hI, mapII_eq_mapI D D' hk hk' hr hrm hrm' hψ hI hx]
  · rw [ite_eq_right hI, ite_eq_left hx]

theorem glue_eq_mapIII (D : GradientLikeStrip I f a b {p})
    (D' : GradientLikeStrip I' f' a' b' {p'}) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hk : (ch D).k = 1) (hk' : (ch D').k = 1) (hr : (ch D').r₀ = (ch D).r₀)
    (hrm : 8 * (ch D).r₀ ≤ rmD D) (hrm' : 8 * (ch D').r₀ ≤ rmD D')
    (ha : a < f p - 2 * eps D) (hb : f p + 2 * eps D < b) {ψ : ℝ → ℝ}
    (hψ : ∀ t ∈ Icc (f p - 2 * eps D) (f p + 2 * eps D), ψ t = t - f p + f' p') {h : M → M'}
    (hH : ∀ σ t, σ ^ 2 = 1 → t ^ 2 ≤ 2 * eps D → h (arc D σ t) = arc D' σ t) {x : M}
    (hx : f x ∈ Icc a b) (hIII : x ∈ lowDomain D) : glue D D' ψ h x = mapIII D D' ψ h x := by
  unfold glue
  by_cases hI : x ∈ regI D
  · rw [ite_eq_left hI, mapIII_eq_mapI D D' hk hk' hr hrm hrm' ha hψ hH hI hIII]
  · rw [ite_eq_right hI]
    by_cases hII : x ∈ regII D
    · rw [ite_eq_left hII, mapII_eq_mapIII D D' hf hk hk' hr hrm hrm' ha hb hH hx hII hIII]
    · rw [ite_eq_right hII]

theorem contMDiffWithinAt_glue (D : GradientLikeStrip I f a b {p})
    (D' : GradientLikeStrip I' f' a' b' {p'}) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hk : (ch D).k = 1) (hk' : (ch D').k = 1) (hr : (ch D').r₀ = (ch D).r₀)
    (hrm : 8 * (ch D).r₀ ≤ rmD D) (hrm' : 8 * (ch D').r₀ ≤ rmD D')
    (ha : a < f p - 2 * eps D) (hb : f p + 2 * eps D < b) {ψ : ℝ → ℝ} (hψs : ContDiff ℝ ∞ ψ)
    (hψ : ∀ t ∈ Icc (f p - 2 * eps D) (f p + 2 * eps D), ψ t = t - f p + f' p') {h : M → M'}
    (hH : ∀ σ t, σ ^ 2 = 1 → t ^ 2 ≤ 2 * eps D → h (arc D σ t) = arc D' σ t)
    (hsm : ∀ x ∈ lowDomain D, f x ∈ Icc a b →
      ContMDiffWithinAt I I' ∞ (fun y => h (D.π a y)) (f ⁻¹' Icc a b) x)
    {x : M} (hx : f x ∈ Icc a b) :
    ContMDiffWithinAt I I' ∞ (glue D D' ψ h) (f ⁻¹' Icc a b) x := by
  have hε := eps_pos D
  have hreal : ∀ c : ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y => -(ψ (f y) - c)) := fun c =>
    ((hψs.contMDiff.comp hf).sub contMDiff_const).neg
  rcases mem_regions D hf hk hrm (by linarith) (by linarith) hx with hI | hII | hIII
  · obtain ⟨y, hy, rfl⟩ := hI
    have heq : glue D D' ψ h =ᶠ[𝓝 ((ch D).χ y)] mapI D D' :=
      eventually_of_mem ((isOpen_regI D hrm).mem_nhds ⟨y, hy, rfl⟩) fun z hz =>
        glue_eq_mapI D D' ψ h hz
    exact ((contMDiffAt_mapI D D' hr hrm hrm' (bounds_of_openBox hy)).congr_of_eventuallyEq
      heq).contMDiffWithinAt
  · have heq : glue D D' ψ h =ᶠ[𝓝 x] mapII D D' ψ :=
      eventually_of_mem ((isOpen_regII D hf hrm).mem_nhds hII) fun z hz =>
        glue_eq_mapII D D' hk hk' hr hrm hrm' hψ h hz
    obtain ⟨w, hw, -, hwx⟩ := regII_data D hf hk hrm hb ha hx hII
    have hπ : ContMDiffAt I I' ∞ (fun y => mapI D D' (D.π (f p + eps D) y)) x := by
      have h1 := contMDiffAt_mapI D D' hr hrm hrm' (bounds_of_topBox hε hw)
      have hπx : D.π (f p + eps D) x = (ch D).χ w := hwx
      rw [← hπx] at h1
      exact h1.comp x (D.contMDiff_π hf _).contMDiffAt
    have hII' : ContMDiffAt I I' ∞ (mapII D D' ψ) x :=
      D'.contMDiff_flow_joint.contMDiffAt.comp x ((hreal _).contMDiffAt.prodMk hπ)
    exact (hII'.congr_of_eventuallyEq heq).contMDiffWithinAt
  · have heq : glue D D' ψ h =ᶠ[𝓝[f ⁻¹' Icc a b] x] mapIII D D' ψ h := by
      have hmem : f ⁻¹' Icc a b ∩ lowDomain D ∈ 𝓝[f ⁻¹' Icc a b] x :=
        inter_mem_nhdsWithin _ ((isOpen_lowDomain D hf.continuous hrm).mem_nhds hIII)
      exact eventually_of_mem hmem fun z hz =>
        glue_eq_mapIII D D' hf hk hk' hr hrm hrm' ha hb hψ hH hz.1 hz.2
    have hIII' : ContMDiffWithinAt I I' ∞ (mapIII D D' ψ h) (f ⁻¹' Icc a b) x :=
      D'.contMDiff_flow_joint.contMDiffAt.comp_contMDiffWithinAt x
        ((hreal a').contMDiffAt.contMDiffWithinAt.prodMk (hsm x hIII hx))
    exact hIII'.congr_of_eventuallyEq heq (glue_eq_mapIII D D' hf hk hk' hr hrm hrm' ha hb hψ hH
      hx hIII)

end GC.Seifert.SaddleSlabProof
