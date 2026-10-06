import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundarySlimBaseCuspEquationOBD

/-!
# BCF02 G4, group G2: the signed face function of ONE label (lane S-BCF02-G4)

A purely topological gluing lemma, used once per label of the relative edge restriction
(`BoundaryRelativeEdgeRestrictionV2`, frozen target G4, TB32:529).

**`exists_signed_function_BG4`.** Let `f : W → H` be continuous and proper on `X` over `B = f(X)`
(`H` a metric space). Let `R` be open and `P` a set with `R ∪ P` closed, `R ∩ P = ∅`, and suppose
every whole fibre `X ∩ f⁻¹{y}` lies in `R`, in `P` or in `(R ∪ P)ᶜ`. Suppose near `P ∩ X`, on an
open `O`, a function `d : W → ℝ` with sign `d < 0 ⟺ R`, `d = 0 ⟺ P` is the pull back `a ∘ f` of a
function `a : H → ℝ` continuous on an open `Ω ∋ f(O ∩ X)`. Then there is `h : H → ℝ`, continuous
on `B`, negative exactly on the base points whose fibre lies in `R`, zero exactly where it lies in
`P`, positive exactly where it lies in `(R ∪ P)ᶜ`, and equal to `a` on a whole open neighbourhood
in `H` of every base point whose fibre lies in `P`.

(Urysohn in the metric space `B`: `h = χ a + (1 - χ) ε` with `ε = -1, 0, 1` the locally constant
sign and `χ = 1` near the zero fibres; outside `B` the function is `a`, so that it is smooth on an
open subset of `H` around each zero.)
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Topology Filter

namespace DifferentialGeometry.Geometry.Collapse

section SignedFunction

variable {W H : Type*} [TopologicalSpace W] [MetricSpace H]

/-- **The signed face function of one label** (see the module docstring). -/
theorem exists_signed_function_BG4 {X : Set W} {f : W → H} {B : Set H}
    (hcont : ContinuousOn f X) (himg : f '' X = B)
    (hproper : ∀ K ⊆ B, IsCompact K → IsCompact (X ∩ f ⁻¹' K))
    {R P : Set W} (hR : IsOpen R) (hRP : IsClosed (R ∪ P)) (hdisj : Disjoint R P)
    (hdich : ∀ y ∈ B, X ∩ f ⁻¹' {y} ⊆ R ∨ X ∩ f ⁻¹' {y} ⊆ P ∨ X ∩ f ⁻¹' {y} ⊆ (R ∪ P)ᶜ)
    {O : Set W} (hO : IsOpen O) (hPO : P ∩ X ⊆ O) {a : H → ℝ} {d : W → ℝ} {Ω : Set H}
    (hΩ : IsOpen Ω) (ha : ContinuousOn a Ω) (hΩO : ∀ p ∈ O ∩ X, f p ∈ Ω)
    (hsame : ∀ p ∈ O ∩ X, a (f p) = d p) (hneg : ∀ p ∈ O ∩ X, p ∈ R ↔ d p < 0)
    (hzero : ∀ p ∈ O ∩ X, p ∈ P ↔ d p = 0) :
    ∃ h : H → ℝ, ContinuousOn h B ∧
      (∀ y ∈ B, (h y < 0 ↔ X ∩ f ⁻¹' {y} ⊆ R) ∧ (h y = 0 ↔ X ∩ f ⁻¹' {y} ⊆ P) ∧
        (0 < h y ↔ X ∩ f ⁻¹' {y} ⊆ (R ∪ P)ᶜ)) ∧
      (∀ y ∈ B, X ∩ f ⁻¹' {y} ⊆ P → ∃ V : Set H, IsOpen V ∧ y ∈ V ∧ ∀ z ∈ V, h z = a z) := by
  classical
  have hne : ∀ y ∈ B, (X ∩ f ⁻¹' {y}).Nonempty := by
    intro y hy
    rw [← himg] at hy
    obtain ⟨p, hp, rfl⟩ := hy
    exact ⟨p, hp, rfl⟩
  have hRP' : IsOpen (R ∪ P)ᶜ := hRP.isOpen_compl
  -- openness (in `B`) of the fibre-sign sets, by the tube lemma
  have hNeg : ∀ y₀ ∈ B, X ∩ f ⁻¹' {y₀} ⊆ R → ∃ V : Set H, IsOpen V ∧ y₀ ∈ V ∧
      ∀ y ∈ B, y ∈ V → X ∩ f ⁻¹' {y} ⊆ R := by
    intro y₀ hy₀ hfib
    obtain ⟨V, hV, hyV, hVsub⟩ := exists_open_fibre_subset_of_proper_OBD hcont himg hproper hR hy₀
      hfib
    exact ⟨V, hV, hyV, fun y _ hy q hq => hVsub q hq.1 (by rw [show f q = y from hq.2]; exact hy)⟩
  have hPos : ∀ y₀ ∈ B, X ∩ f ⁻¹' {y₀} ⊆ (R ∪ P)ᶜ → ∃ V : Set H, IsOpen V ∧ y₀ ∈ V ∧
      ∀ y ∈ B, y ∈ V → X ∩ f ⁻¹' {y} ⊆ (R ∪ P)ᶜ := by
    intro y₀ hy₀ hfib
    obtain ⟨V, hV, hyV, hVsub⟩ := exists_open_fibre_subset_of_proper_OBD hcont himg hproper hRP'
      hy₀ hfib
    exact ⟨V, hV, hyV, fun y _ hy q hq => hVsub q hq.1 (by rw [show f q = y from hq.2]; exact hy)⟩
  have hPhi : ∀ y₀ ∈ B, X ∩ f ⁻¹' {y₀} ⊆ P → ∃ V : Set H, IsOpen V ∧ y₀ ∈ V ∧
      ∀ q ∈ X, f q ∈ V → q ∈ O := by
    intro y₀ hy₀ hfib
    exact exists_open_fibre_subset_of_proper_OBD hcont himg hproper hO hy₀
      (fun q hq => hPO ⟨hfib hq, hq.1⟩)
  -- the three fibre classes are exclusive
  have hexc1 : ∀ y ∈ B, X ∩ f ⁻¹' {y} ⊆ R → ¬ X ∩ f ⁻¹' {y} ⊆ P := by
    intro y hy h1 h2
    obtain ⟨p, hp⟩ := hne y hy
    exact Set.disjoint_left.mp hdisj (h1 hp) (h2 hp)
  have hexc2 : ∀ y ∈ B, X ∩ f ⁻¹' {y} ⊆ R → ¬ X ∩ f ⁻¹' {y} ⊆ (R ∪ P)ᶜ := by
    intro y hy h1 h2
    obtain ⟨p, hp⟩ := hne y hy
    exact h2 hp (Or.inl (h1 hp))
  have hexc3 : ∀ y ∈ B, X ∩ f ⁻¹' {y} ⊆ P → ¬ X ∩ f ⁻¹' {y} ⊆ (R ∪ P)ᶜ := by
    intro y hy h1 h2
    obtain ⟨p, hp⟩ := hne y hy
    exact h2 hp (Or.inr (h1 hp))
  -- the zero fibres and a tube around them
  choose! V hVo hyV hVsub using hPhi
  let Nset : Set H := ⋃ y₀ ∈ {y | y ∈ B ∧ X ∩ f ⁻¹' {y} ⊆ P}, V y₀
  have hNsetO : IsOpen Nset := isOpen_biUnion fun y₀ hy₀ => hVo y₀ hy₀.1 hy₀.2
  have hNsetF : ∀ y ∈ B, y ∈ Nset → ∀ q ∈ X ∩ f ⁻¹' {y}, q ∈ O := by
    intro y hy hyN q hq
    obtain ⟨y₀, hy₀, hyV'⟩ := mem_iUnion₂.mp hyN
    exact hVsub y₀ hy₀.1 hy₀.2 q hq.1 (by rw [show f q = y from hq.2]; exact hyV')
  have hNsetΩ : ∀ y ∈ B, y ∈ Nset → y ∈ Ω := by
    intro y hy hyN
    obtain ⟨p, hp⟩ := hne y hy
    have := hΩO p ⟨hNsetF y hy hyN p hp, hp.1⟩
    rwa [show f p = y from hp.2] at this
  -- sign of `a` on the tube
  have haneg : ∀ y ∈ B, y ∈ Nset → X ∩ f ⁻¹' {y} ⊆ R → a y < 0 := by
    intro y hy hyN hfib
    obtain ⟨p, hp⟩ := hne y hy
    have hpO := hNsetF y hy hyN p hp
    have := hsame p ⟨hpO, hp.1⟩
    rw [show f p = y from hp.2] at this
    rw [this]
    exact (hneg p ⟨hpO, hp.1⟩).1 (hfib hp)
  have hazero : ∀ y ∈ B, y ∈ Nset → X ∩ f ⁻¹' {y} ⊆ P → a y = 0 := by
    intro y hy hyN hfib
    obtain ⟨p, hp⟩ := hne y hy
    have hpO := hNsetF y hy hyN p hp
    have := hsame p ⟨hpO, hp.1⟩
    rw [show f p = y from hp.2] at this
    rw [this]
    exact (hzero p ⟨hpO, hp.1⟩).1 (hfib hp)
  have hapos : ∀ y ∈ B, y ∈ Nset → X ∩ f ⁻¹' {y} ⊆ (R ∪ P)ᶜ → 0 < a y := by
    intro y hy hyN hfib
    obtain ⟨p, hp⟩ := hne y hy
    have hpO := hNsetF y hy hyN p hp
    have := hsame p ⟨hpO, hp.1⟩
    rw [show f p = y from hp.2] at this
    rw [this]
    have hp' := hfib hp
    have h1 : ¬ p ∈ R := fun h => hp' (Or.inl h)
    have h2 : ¬ p ∈ P := fun h => hp' (Or.inr h)
    have h3 : ¬ d p < 0 := fun h => h1 ((hneg p ⟨hpO, hp.1⟩).2 h)
    have h4 : d p ≠ 0 := fun h => h2 ((hzero p ⟨hpO, hp.1⟩).2 h)
    exact lt_of_le_of_ne (not_lt.mp h3) (Ne.symm h4)
  -- work in the metric space `B`
  let FY : ↥B → Set W := fun y => X ∩ f ⁻¹' {(y : H)}
  have hFneg : ∀ y : ↥B, FY y ⊆ R → ¬ FY y ⊆ P := fun y => hexc1 y.1 y.2
  let NegY : Set ↥B := {y | FY y ⊆ R}
  let PosY : Set ↥B := {y | FY y ⊆ (R ∪ P)ᶜ}
  let PhiY : Set ↥B := {y | FY y ⊆ P}
  have hNegY : IsOpen NegY := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    obtain ⟨Vn, hVn, hyVn, hsub⟩ := hNeg y.1 y.2 hy
    have : Subtype.val ⁻¹' Vn ∈ 𝓝 y := (hVn.preimage continuous_subtype_val).mem_nhds hyVn
    exact Filter.mem_of_superset this fun z hz => hsub z.1 z.2 hz
  have hPosY : IsOpen PosY := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    obtain ⟨Vn, hVn, hyVn, hsub⟩ := hPos y.1 y.2 hy
    have : Subtype.val ⁻¹' Vn ∈ 𝓝 y := (hVn.preimage continuous_subtype_val).mem_nhds hyVn
    exact Filter.mem_of_superset this fun z hz => hsub z.1 z.2 hz
  have hPhiY : IsClosed PhiY := by
    have : PhiYᶜ = NegY ∪ PosY := by
      ext y
      simp only [mem_compl_iff, mem_union]
      constructor
      · intro hy
        rcases hdich y.1 y.2 with h | h | h
        · exact Or.inl h
        · exact absurd h hy
        · exact Or.inr h
      · rintro (h | h) hy
        · exact hFneg y h hy
        · exact hexc3 y.1 y.2 hy h
    rw [← isOpen_compl_iff, this]
    exact hNegY.union hPosY
  let NY : Set ↥B := Subtype.val ⁻¹' Nset
  have hNY : IsOpen NY := hNsetO.preimage continuous_subtype_val
  have hPhiNY : PhiY ⊆ NY := by
    intro y hy
    exact mem_biUnion (show y.1 ∈ {y | y ∈ B ∧ X ∩ f ⁻¹' {y} ⊆ P} from ⟨y.2, hy⟩)
      (hyV y.1 y.2 hy)
  obtain ⟨u₁, hu₁, hPu₁, hcu₁⟩ := normal_exists_closure_subset hPhiY hNY hPhiNY
  obtain ⟨u₂, hu₂, hPu₂, hcu₂⟩ := normal_exists_closure_subset hPhiY hu₁ hPu₁
  obtain ⟨χ, hχ0, hχ1, hχI⟩ := exists_continuous_zero_one_of_isClosed hu₁.isClosed_compl
    isClosed_closure (Set.disjoint_left.mpr fun y hy hy' => hy (hcu₂ hy'))
  -- the sign function
  let ε : ↥B → ℝ := fun y => if FY y ⊆ R then -1 else if FY y ⊆ P then 0 else 1
  let hY : ↥B → ℝ := fun y => χ y * a y + (1 - χ y) * ε y
  have hεneg : ∀ y ∈ NegY, ε y = -1 := fun y hy => by
    have hy' : FY y ⊆ R := hy
    simp [ε, hy']
  have hεpos : ∀ y ∈ PosY, ε y = 1 := by
    intro y hy
    have h1 : ¬ FY y ⊆ R := fun h => hexc2 y.1 y.2 h hy
    have h2 : ¬ FY y ⊆ P := fun h => hexc3 y.1 y.2 h hy
    simp [ε, h1, h2]
  have hχ_one : ∀ y ∈ u₂, χ y = 1 := fun y hy => hχ1 (subset_closure hy)
  have hχ_zero : ∀ y, y ∉ u₁ → χ y = 0 := fun y hy => hχ0 hy
  have hu₁N : ∀ y, y ∈ u₁ → y ∈ NY := fun y hy => hcu₁ (subset_closure hy)
  have haY : ∀ y : ↥B, y ∈ NY → ContinuousAt (fun z : ↥B => a z.1) y := by
    intro y hy
    have hΩy : y.1 ∈ Ω := hNsetΩ y.1 y.2 hy
    exact (ha.continuousAt (hΩ.mem_nhds hΩy)).comp continuous_subtype_val.continuousAt
  have hεcont : ∀ y : ↥B, y ∉ PhiY → ContinuousAt ε y := by
    intro y hy
    rcases hdich y.1 y.2 with h | h | h
    · have : ε =ᶠ[𝓝 y] fun _ => (-1 : ℝ) :=
        Filter.mem_of_superset (hNegY.mem_nhds h) fun z hz => hεneg z hz
      exact continuousAt_const.congr this.symm
    · exact absurd h hy
    · have : ε =ᶠ[𝓝 y] fun _ => (1 : ℝ) :=
        Filter.mem_of_superset (hPosY.mem_nhds h) fun z hz => hεpos z hz
      exact continuousAt_const.congr this.symm
  have hYcont : Continuous hY := by
    rw [continuous_iff_continuousAt]
    intro y
    by_cases hy : y ∈ PhiY
    · have hy2 : y ∈ u₂ := hPu₂ hy
      have heq : hY =ᶠ[𝓝 y] fun z : ↥B => a z.1 := by
        filter_upwards [hu₂.mem_nhds hy2] with z hz
        simp only [hY, hχ_one z hz]
        ring
      exact (haY y (hPhiNY hy)).congr heq.symm
    · have hε := hεcont y hy
      have hχa : ContinuousAt (fun z : ↥B => χ z * a z.1) y := by
        by_cases hyc : y ∈ closure u₁
        · exact χ.continuous.continuousAt.mul (haY y (hcu₁ hyc))
        · have : (fun z : ↥B => χ z * a z.1) =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
            filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hyc] with z hz
            rw [hχ_zero z (fun hz' => hz (subset_closure hz'))]
            simp
          exact continuousAt_const.congr this.symm
      exact hχa.add ((continuousAt_const.sub χ.continuous.continuousAt).mul hε)
  have hneg' : ∀ y : ↥B, FY y ⊆ R → hY y < 0 := by
    intro y hy
    have hε : ε y = -1 := hεneg y hy
    have h0 : 0 ≤ χ y := (hχI y).1
    by_cases hyN : y ∈ NY
    · have ha' := haneg y.1 y.2 hyN hy
      simp only [hY, hε]
      rcases h0.eq_or_lt with h | h
      · rw [← h]
        norm_num
      · nlinarith [mul_pos h (neg_pos.mpr ha'), (hχI y).2]
    · have : y ∉ u₁ := fun h => hyN (hu₁N y h)
      simp only [hY, hε, hχ_zero y this]
      norm_num
  have hpos' : ∀ y : ↥B, FY y ⊆ (R ∪ P)ᶜ → 0 < hY y := by
    intro y hy
    have hε : ε y = 1 := hεpos y hy
    have h0 : 0 ≤ χ y := (hχI y).1
    by_cases hyN : y ∈ NY
    · have ha' := hapos y.1 y.2 hyN hy
      simp only [hY, hε]
      rcases h0.eq_or_lt with h | h
      · rw [← h]
        norm_num
      · nlinarith [mul_pos h ha', (hχI y).2]
    · have : y ∉ u₁ := fun h => hyN (hu₁N y h)
      simp only [hY, hε, hχ_zero y this]
      norm_num
  have hzero' : ∀ y : ↥B, FY y ⊆ P → hY y = 0 := by
    intro y hy
    have hyu : y ∈ u₂ := hPu₂ hy
    have := hazero y.1 y.2 (hPhiNY hy) hy
    simp only [hY, hχ_one y hyu]
    rw [this]
    ring
  refine ⟨fun z => if hz : z ∈ B then hY ⟨z, hz⟩ else a z, ?_, ?_, ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    have : (B.domRestrict fun z => if hz : z ∈ B then hY ⟨z, hz⟩ else a z) = hY := by
      funext z
      simp [Set.domRestrict, z.2]
    rw [this]
    exact hYcont
  · intro y hy
    simp only [hy, dite_true]
    have h1 := hneg' ⟨y, hy⟩
    have h2 := hzero' ⟨y, hy⟩
    have h3 := hpos' ⟨y, hy⟩
    refine ⟨⟨fun hlt => ?_, h1⟩, ⟨fun h0 => ?_, h2⟩, ⟨fun hgt => ?_, h3⟩⟩
    · rcases hdich y hy with h | h | h
      · exact h
      · have := h2 h
        linarith
      · have := h3 h
        linarith
    · rcases hdich y hy with h | h | h
      · have := h1 h
        linarith
      · exact h
      · have := h3 h
        linarith
    · rcases hdich y hy with h | h | h
      · have := h1 h
        linarith
      · have := h2 h
        linarith
      · exact h
  · intro y hy hfib
    have hyP : (⟨y, hy⟩ : ↥B) ∈ PhiY := hfib
    have hyu : (⟨y, hy⟩ : ↥B) ∈ u₂ := hPu₂ hyP
    obtain ⟨Vh, hVh, hVu⟩ := isOpen_induced_iff.mp hu₂
    refine ⟨Vh, hVh, ?_, fun z hz => ?_⟩
    · have : (⟨y, hy⟩ : ↥B) ∈ Subtype.val ⁻¹' Vh := by rw [hVu]; exact hyu
      exact this
    · by_cases hzB : z ∈ B
      · simp only [hzB, dite_true]
        have hzu : (⟨z, hzB⟩ : ↥B) ∈ u₂ := by
          rw [← hVu]
          exact hz
        simp only [hY, hχ_one _ hzu]
        ring
      · simp only [hzB, dite_false]

end SignedFunction

end DifferentialGeometry.Geometry.Collapse
