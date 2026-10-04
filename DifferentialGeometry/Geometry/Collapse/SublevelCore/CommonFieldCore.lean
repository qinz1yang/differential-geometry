import DifferentialGeometry.Geometry.Collapse.SublevelCore.FieldBand
import DifferentialGeometry.Geometry.Collapse.SublevelCore.GraphIsotopy
import DifferentialGeometry.Geometry.Comparison.Soul.SmoothFlowCrossing

/-!
# A common outward field recognizes the core (LC47)

Frozen blueprint master207A, lemma `lem:collapse-common-field-isotopy` (LC47, lines 22289–22347).
Let `η` be continuous, smooth on an open `W` containing the compact band `K = η⁻¹[a, b]`, and let
`Y` be a field smooth on `W` with `dη(Y) > 0` on `K` (the LC46 hypotheses). Let `D` be a closed
domain with `{η ≤ a} ⊆ int D`, `D ⊆ {η < b}`, whose frontier is smooth and strictly crossed by `Y`
outward: every frontier point has a local defining function `f` (`D = {f ≤ 0}` near it) with
`df(Y) > 0` there. Then, for every `ρ ∈ (a, b)`, a smooth ambient isotopy supported in one compact
subset of `η⁻¹(a, b)` carries `D` onto `{η ≤ ρ}`.

Structure of the proof (as in the blueprint, using the LC46 flow `Φ` of `Y / dη(Y)` from
`exists_field_band_product_of_contMDiffOn`):
* `exists_unique_crossing_of_transverse` — a one-dimensional kernel: a closed set of times that
  contains a neighbourhood of `a`, misses `b`, and is crossed transversally at each of its boundary
  points is exactly `[a, h]` for one `h ∈ (a, b)`, and `h` is its only boundary point.
* along every flow line through the band the core is a subgraph, with a crossing height that is
  constant along the flow line and smooth on the open band (implicit function theorem through
  `exists_smooth_flow_levelTime`);
* the isotopy moves every flow line by the one-dimensional flow of `GraphIsotopy`
  (`exists_real_flow_translating`), sending the crossing height to `ρ`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Bundle
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

/-- **One-dimensional crossing kernel.** A closed set of times `T` containing a neighbourhood of
`a` and not containing `b`, crossed transversally (locally `T` on the left, its complement on the
right) at each of its boundary points in `[a, b]`, meets `[a, b]` exactly in `[a, h]` for one
`h ∈ (a, b)`; `h` is its only boundary point in `[a, b]`. -/
theorem exists_unique_crossing_of_transverse {T : Set ℝ} {a b : ℝ} (hab : a < b)
    (hT : IsClosed T) (haT : ∃ δ > 0, Icc a (a + δ) ⊆ T) (hbT : b ∉ T)
    (htrans : ∀ s ∈ Icc a b, s ∈ T → (∀ ε > 0, ∃ s' ∈ Ioo (s - ε) (s + ε), s' ∉ T) →
      ∃ δ > 0, (∀ s' ∈ Ioo (s - δ) s, s' ∈ T) ∧ (∀ s' ∈ Ioo s (s + δ), s' ∉ T)) :
    ∃ h ∈ Ioo a b, (∀ s ∈ Icc a b, s ∈ T ↔ s ≤ h) ∧
      ∀ s ∈ Icc a b, (s ∈ T ∧ ∀ ε > 0, ∃ s' ∈ Ioo (s - ε) (s + ε), s' ∉ T) ↔ s = h := by
  obtain ⟨δ₀, hδ₀, hδ₀T⟩ := haT
  set C : Set ℝ := T ∩ Icc a b with hCdef
  have hC : IsCompact C := isCompact_Icc.inter_left hT
  have hCne : C.Nonempty := ⟨a, hδ₀T ⟨le_rfl, by linarith⟩, le_rfl, hab.le⟩
  set h : ℝ := sSup C with hhdef
  have hhC : h ∈ C := hC.sSup_mem hCne
  have hle : ∀ s ∈ C, s ≤ h := fun s hs => le_csSup hC.bddAbove hs
  have hhb : h < b := lt_of_le_of_ne hhC.2.2 (fun hhb => hbT (hhb ▸ hhC.1))
  have hah : a < h := by
    have hmem : min (a + δ₀) b ∈ C :=
      ⟨hδ₀T ⟨le_min (by linarith) hab.le, min_le_left _ _⟩,
        le_min (by linarith) hab.le, min_le_right _ _⟩
    have := hle _ hmem
    rcases min_choice (a + δ₀) b with hm | hm <;> rw [hm] at this <;> linarith
  -- `h` is a boundary point: points just to its right are outside `T`.
  have hbdry : ∀ ε > 0, ∃ s' ∈ Ioo (h - ε) (h + ε), s' ∉ T := by
    intro ε hε
    refine ⟨min (h + ε / 2) b, ⟨?_, ?_⟩, fun hs' => ?_⟩
    · rcases min_choice (h + ε / 2) b with hm | hm <;> rw [hm] <;> linarith
    · exact (min_le_left _ _).trans_lt (by linarith)
    · have hmem : min (h + ε / 2) b ∈ C :=
        ⟨hs', by rcases min_choice (h + ε / 2) b with hm | hm <;> rw [hm] <;> linarith,
          min_le_right _ _⟩
      have := hle _ hmem
      rcases min_choice (h + ε / 2) b with hm | hm <;> rw [hm] at this <;> linarith
  -- Every point of `[a, h]` lies in `T`.
  have hfill : ∀ s ∈ Icc a h, s ∈ T := by
    intro s hs
    by_contra hsT
    set C' : Set ℝ := T ∩ Icc s b with hC'def
    have hC' : IsCompact C' := isCompact_Icc.inter_left hT
    have hC'ne : C'.Nonempty := ⟨h, hhC.1, hs.2, hhC.2.2⟩
    set s₂ : ℝ := sInf C' with hs₂def
    have hs₂C : s₂ ∈ C' := hC'.sInf_mem hC'ne
    have hge : ∀ u ∈ C', s₂ ≤ u := fun u hu => csInf_le hC'.bddBelow hu
    have hss₂ : s < s₂ := lt_of_le_of_ne hs₂C.2.1 (fun he => hsT (he ▸ hs₂C.1))
    have hs₂ab : s₂ ∈ Icc a b := ⟨hs.1.trans hs₂C.2.1, hs₂C.2.2⟩
    have hleft : ∀ u ∈ Ioo s s₂, u ∉ T := fun u hu huT =>
      (not_le.mpr hu.2) (hge u ⟨huT, hu.1.le, hu.2.le.trans hs₂C.2.2⟩)
    -- Midpoints between `max s (s₂ - ε)` and `s₂` lie in `(s, s₂)`, hence outside `T`.
    have hmid : ∀ ε > 0, (max s (s₂ - ε) + s₂) / 2 ∈ Ioo s s₂ ∧
        (max s (s₂ - ε) + s₂) / 2 ∈ Ioo (s₂ - ε) (s₂ + ε) := by
      intro ε hε
      have h1 := le_max_left s (s₂ - ε)
      have h2 := le_max_right s (s₂ - ε)
      have h3 : max s (s₂ - ε) < s₂ := max_lt hss₂ (by linarith)
      exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
    obtain ⟨δ, hδ, hδT, -⟩ := htrans s₂ hs₂ab hs₂C.1 (fun ε hε =>
      ⟨_, (hmid ε hε).2, hleft _ (hmid ε hε).1⟩)
    have hu := hmid δ hδ
    exact hleft _ hu.1 (hδT _ ⟨hu.2.1, hu.1.2⟩)
  have hiff : ∀ s ∈ Icc a b, s ∈ T ↔ s ≤ h := fun s hs =>
    ⟨fun hsT => hle s ⟨hsT, hs⟩, fun hsh => hfill s ⟨hs.1, hsh⟩⟩
  refine ⟨h, ⟨hah, hhb⟩, hiff, fun s hs => ⟨fun ⟨hsT, hsb⟩ => ?_, fun hsh => hsh ▸ ⟨hhC.1, hbdry⟩⟩⟩
  have hsh : s ≤ h := (hiff s hs).1 hsT
  by_contra hne
  have hslt : s < h := lt_of_le_of_ne hsh hne
  obtain ⟨δ, hδ, -, hδout⟩ := htrans s hs hsT hsb
  have hu : min (s + δ / 2) h ∈ Ioo s (s + δ) := by
    constructor
    · rcases min_choice (s + δ / 2) h with hm | hm <;> rw [hm] <;> linarith
    · exact (min_le_left _ _).trans_lt (by linarith)
  exact hδout _ hu ((hiff _ ⟨by linarith [hu.1, hs.1], (min_le_right _ _).trans hhb.le⟩).2
    (min_le_right _ _))

/-- A positive derivative at a zero gives the strict sign pattern on both sides. -/
theorem exists_sign_pattern_of_hasDerivAt {φ : ℝ → ℝ} {d s : ℝ} (hφ : HasDerivAt φ d s)
    (hd : 0 < d) (hs : φ s = 0) :
    ∃ δ > 0, (∀ s' ∈ Ioo (s - δ) s, φ s' < 0) ∧ (∀ s' ∈ Ioo s (s + δ), 0 < φ s') := by
  have hslope := (hasDerivAt_iff_tendsto_slope.mp hφ).eventually (lt_mem_nhds hd)
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hslope
  obtain ⟨δ, hδ, hδs⟩ := hslope
  refine ⟨δ, hδ, fun s' hs' => ?_, fun s' hs' => ?_⟩
  · have hne : s' ≠ s := hs'.2.ne
    have hpos := hδs (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hs'.1, hs'.2]) hne
    rw [slope_def_field, hs, sub_zero] at hpos
    have hneg : s' - s < 0 := by linarith [hs'.2]
    exact (div_pos_iff.mp hpos).elim (fun h => absurd h.2 (not_lt.mpr hneg.le)) (fun h => h.1)
  · have hne : s' ≠ s := hs'.1.ne'
    have hpos := hδs (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hs'.1, hs'.2]) hne
    rw [slope_def_field, hs, sub_zero] at hpos
    have hposd : 0 < s' - s := by linarith [hs'.1]
    exact (div_pos_iff.mp hpos).elim (fun h => h.1) (fun h => absurd h.2 (not_lt.mpr hposd.le))

section Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

omit [FiniteDimensional ℝ E] in
/-- Chain rule for a scalar function along a curve with a prescribed velocity. -/
theorem hasDerivAt_comp_of_hasMFDerivAt {γ : ℝ → M} {f : M → ℝ} {t : ℝ}
    {w : TangentSpace I (γ t)}
    (hγ : HasMFDerivAt 𝓘(ℝ, ℝ) I γ t ((1 : ℝ →L[ℝ] ℝ).smulRight w))
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f (γ t)) :
    HasDerivAt (fun s => f (γ s)) (mvfderiv (I := I) f (γ t) w) t := by
  have h := hf.hasMFDerivAt.comp t hγ
  rw [hasMFDerivAt_iff_hasFDerivAt] at h
  have h2 : HasFDerivAt (fun s => f (γ s))
      ((1 : ℝ →L[ℝ] ℝ).smulRight (mvfderiv (I := I) f (γ t) w)) t :=
    h.congr_fderiv (ContinuousLinearMap.ext_ring (by
      change (mfderiv I 𝓘(ℝ, ℝ) f (γ t)) ((1 : ℝ →L[ℝ] ℝ).smulRight w 1) =
        (1 : ℝ →L[ℝ] ℝ).smulRight (mvfderiv (I := I) f (γ t) w) 1
      simp only [ContinuousLinearMap.smulRight_apply, one_apply_eq_self, one_smul]
      rfl))
  simpa using h2.hasDerivAt

end Manifold

section Band

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

/-- **LC47, graph part.** Under the LC46 hypotheses, with `D` closed, `{η ≤ a} ⊆ int D`,
`D ⊆ {η < b}` and every frontier point of `D` crossed strictly outward by `Y` (a local defining
function `f`, `D = {f ≤ 0}` near the point, `df(Y) > 0` there), the LC46 flow `Φ` and one height
function `ht` satisfy: along the flow line `s ↦ Φ (s - η x) x` through any band point `x`, the core
is exactly `s ≤ ht x`, its frontier is exactly `s = ht x`, `ht x ∈ (a, b)`, `ht` is constant along
flow lines and smooth on the open band. No relation between `Y` and the gradient of `η` is used. -/
theorem exists_crossing_height_of_common_outward_field {η : M → ℝ} (hη : Continuous η)
    {W : Set M} (hW : IsOpen W) (hηW : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ η W) {a b : ℝ} (hab : a < b)
    (hK : IsCompact (η ⁻¹' Icc a b)) (hKW : η ⁻¹' Icc a b ⊆ W)
    (Y : (x : M) → TangentSpace I x)
    (hY : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (fun x => (⟨x, Y x⟩ : TangentBundle I M)) W)
    (hpos : ∀ x ∈ η ⁻¹' Icc a b, 0 < mvfderiv (I := I) η x (Y x))
    {D : Set M} (hD : IsClosed D) (hAD : {x | η x ≤ a} ⊆ interior D)
    (hDb : D ⊆ {x | η x < b})
    (hdef : ∀ q ∈ frontier D, ∃ U : Set M, IsOpen U ∧ q ∈ U ∧ ∃ f : M → ℝ,
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f U ∧ D ∩ U = {x | f x ≤ 0} ∩ U ∧
        0 < mvfderiv (I := I) f q (Y q)) :
    ∃ Φ : ℝ → Diffeomorph I I M M ∞,
      Φ 0 = Diffeomorph.refl I M ∞ ∧
      ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M => Φ p.1 p.2) ∧
      (∀ s t x, Φ (s + t) x = Φ t (Φ s x)) ∧
      (∀ x, η x ∈ Icc a b → ∀ s ∈ Icc a b, η (Φ (s - η x) x) = s) ∧
      ∃ ht : M → ℝ, (∀ x ∈ η ⁻¹' Icc a b, ht x ∈ Ioo a b) ∧
        (∀ x ∈ η ⁻¹' Icc a b, ∀ s ∈ Icc a b, Φ (s - η x) x ∈ D ↔ s ≤ ht x) ∧
        (∀ x ∈ η ⁻¹' Icc a b, ∀ s ∈ Icc a b, Φ (s - η x) x ∈ frontier D ↔ s = ht x) ∧
        (∀ x ∈ η ⁻¹' Icc a b, ∀ s ∈ Icc a b, ht (Φ (s - η x) x) = ht x) ∧
        ContMDiffOn I 𝓘(ℝ, ℝ) ∞ ht (η ⁻¹' Ioo a b) := by
  classical
  obtain ⟨Φ, hΦ0, hΦj, -, hadd, hlevel, -, hvel, -⟩ :=
    exists_field_band_product_of_contMDiffOn hη hW hηW hab (c := a) ⟨le_rfl, hab.le⟩ hK hKW Y hY
      hpos
  have hΦ0x : ∀ x, Φ 0 x = x := fun x => by rw [hΦ0]; rfl
  have hγc : ∀ x, Continuous (fun s : ℝ => Φ (s - η x) x) := fun x =>
    hΦj.continuous.comp ((continuous_id.sub continuous_const).prodMk continuous_const)
  have hfrD : frontier D ⊆ D := hD.frontier_subset
  -- A defining function vanishes at frontier points.
  have hf0 : ∀ q ∈ frontier D, ∀ (U : Set M) (f : M → ℝ), IsOpen U → q ∈ U →
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f U → D ∩ U = {x | f x ≤ 0} ∩ U → f q = 0 := by
    intro q hq U f hU hqU hf hDU
    have hle : f q ≤ 0 := by
      have : q ∈ D ∩ U := ⟨hfrD hq, hqU⟩
      rw [hDU] at this
      exact this.1
    by_contra hne
    have hlt : f q < 0 := lt_of_le_of_ne hle hne
    have hopen : IsOpen (U ∩ f ⁻¹' Iio 0) := hf.continuousOn.isOpen_inter_preimage hU isOpen_Iio
    have hsub : U ∩ f ⁻¹' Iio 0 ⊆ D := by
      intro y hy
      have : y ∈ {x | f x ≤ 0} ∩ U := ⟨(show f y < 0 from hy.2).le, hy.1⟩
      rw [← hDU] at this
      exact this.1
    exact hq.2 (interior_maximal hsub hopen ⟨hqU, hlt⟩)
  -- The sign pattern along a flow line at a transverse zero of a defining function.
  have hpattern : ∀ x ∈ η ⁻¹' Icc a b, ∀ s ∈ Icc a b, ∀ (U : Set M) (f : M → ℝ), IsOpen U →
      Φ (s - η x) x ∈ U → ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f U → D ∩ U = {y | f y ≤ 0} ∩ U →
      f (Φ (s - η x) x) = 0 → 0 < mvfderiv (I := I) f (Φ (s - η x) x) (Y (Φ (s - η x) x)) →
      ∃ δ > 0, (∀ s' ∈ Ioo (s - δ) s, Φ (s' - η x) x ∈ D) ∧
        (∀ s' ∈ Ioo s (s + δ), Φ (s' - η x) x ∉ D) := by
    intro x hx s hs U f hU hqU hf hDU hfq hfY
    have hqK : η (Φ (s - η x) x) ∈ Icc a b := by rw [hlevel x hx s hs]; exact hs
    have hdη := hpos _ hqK
    have hv := hvel x (s - η x) hqK
    have hfd : MDifferentiableAt I 𝓘(ℝ, ℝ) f (Φ (s - η x) x) :=
      (hf.contMDiffAt (hU.mem_nhds hqU)).mdifferentiableAt (by norm_num)
    have hd := (hasDerivAt_comp_of_hasMFDerivAt hv hfd).comp_sub_const s (η x)
    rw [map_smul, smul_eq_mul] at hd
    obtain ⟨δ₁, hδ₁, hneg, hposs⟩ :=
      exists_sign_pattern_of_hasDerivAt hd (mul_pos (inv_pos.mpr hdη) hfY) hfq
    obtain ⟨δ₂, hδ₂, hδ₂U⟩ := Metric.eventually_nhds_iff.mp
      ((hγc x).continuousAt.preimage_mem_nhds (hU.mem_nhds hqU))
    have hin : ∀ s' : ℝ, |s' - s| < min δ₁ δ₂ → Φ (s' - η x) x ∈ U := fun s' hs' =>
      hδ₂U (by rw [Real.dist_eq]; exact hs'.trans_le (min_le_right _ _))
    refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun s' hs' => ?_, fun s' hs' hD' => ?_⟩
    · have hU' := hin s' (by rw [abs_lt]; constructor <;> linarith [hs'.1, hs'.2])
      have : Φ (s' - η x) x ∈ {y | f y ≤ 0} ∩ U :=
        ⟨(hneg s' ⟨by linarith [hs'.1, min_le_left δ₁ δ₂], hs'.2⟩).le, hU'⟩
      rw [← hDU] at this
      exact this.1
    · have hU' := hin s' (by rw [abs_lt]; constructor <;> linarith [hs'.1, hs'.2])
      have : Φ (s' - η x) x ∈ D ∩ U := ⟨hD', hU'⟩
      rw [hDU] at this
      exact (not_le.mpr (hposs s' ⟨hs'.1, by linarith [hs'.2, min_le_left δ₁ δ₂]⟩)) this.1
  -- A point of `D` with outside points arbitrarily close on its flow line is a frontier point.
  have hfront : ∀ x : M, ∀ s : ℝ, Φ (s - η x) x ∈ D →
      (∀ ε > 0, ∃ s' ∈ Ioo (s - ε) (s + ε), Φ (s' - η x) x ∉ D) →
      Φ (s - η x) x ∈ frontier D := by
    intro x s hsD hout
    rw [frontier_eq_closure_inter_closure]
    refine ⟨subset_closure hsD, mem_closure_iff_nhds.mpr fun N hN => ?_⟩
    obtain ⟨ε, hε, hεN⟩ := Metric.eventually_nhds_iff.mp
      ((hγc x).continuousAt.preimage_mem_nhds hN)
    obtain ⟨s', hs', hs'D⟩ := hout ε hε
    exact ⟨_, hεN (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hs'.1, hs'.2]), hs'D⟩
  -- The crossing structure on each flow line.
  have hcross : ∀ x ∈ η ⁻¹' Icc a b, ∃ h ∈ Ioo a b,
      (∀ s ∈ Icc a b, Φ (s - η x) x ∈ D ↔ s ≤ h) ∧
      (∀ s ∈ Icc a b, Φ (s - η x) x ∈ frontier D ↔ s = h) := by
    intro x hx
    set T : Set ℝ := {s | Φ (s - η x) x ∈ D} with hTdef
    have hT : IsClosed T := hD.preimage (hγc x)
    have haT : ∃ δ > 0, Icc a (a + δ) ⊆ T := by
      have hai : Φ (a - η x) x ∈ interior D := hAD (by
        change η (Φ (a - η x) x) ≤ a
        rw [hlevel x hx a ⟨le_rfl, hab.le⟩])
      obtain ⟨ε, hε, hεT⟩ := Metric.eventually_nhds_iff.mp
        ((hγc x).continuousAt.preimage_mem_nhds (isOpen_interior.mem_nhds hai))
      refine ⟨ε / 2, by positivity, fun s hs => show Φ (s - η x) x ∈ D from interior_subset (hεT ?_)⟩
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [hs.1, hs.2]
    have hbT : b ∉ T := fun hb => by
      have := hDb hb
      change η (Φ (b - η x) x) < b at this
      rw [hlevel x hx b ⟨hab.le, le_rfl⟩] at this
      exact lt_irrefl _ this
    have htrans : ∀ s ∈ Icc a b, s ∈ T → (∀ ε > 0, ∃ s' ∈ Ioo (s - ε) (s + ε), s' ∉ T) →
        ∃ δ > 0, (∀ s' ∈ Ioo (s - δ) s, s' ∈ T) ∧ (∀ s' ∈ Ioo s (s + δ), s' ∉ T) := by
      intro s hs hsT hout
      have hq := hfront x s hsT hout
      obtain ⟨U, hU, hqU, f, hf, hDU, hfq⟩ := hdef _ hq
      exact hpattern x hx s hs U f hU hqU hf hDU (hf0 _ hq U f hU hqU hf hDU) hfq
    obtain ⟨h, hh, hiff, hbd⟩ := exists_unique_crossing_of_transverse hab hT haT hbT htrans
    refine ⟨h, hh, hiff, fun s hs => ⟨fun hq => (hbd s hs).1 ⟨hfrD hq, ?_⟩,
      fun hsh => hfront x s ((hiff s hs).2 hsh.le) (fun ε hε => ?_)⟩⟩
    · obtain ⟨U, hU, hqU, f, hf, hDU, hfq⟩ := hdef _ hq
      obtain ⟨δ, hδ, -, hδout⟩ :=
        hpattern x hx s hs U f hU hqU hf hDU (hf0 _ hq U f hU hqU hf hDU) hfq
      intro ε hε
      refine ⟨s + min δ ε / 2, ⟨?_, ?_⟩, hδout _ ⟨?_, ?_⟩⟩ <;>
        linarith [min_le_left δ ε, min_le_right δ ε, lt_min hδ hε]
    · obtain ⟨s', hs', hs'T⟩ := ((hbd s hs).2 hsh).2 ε hε
      exact ⟨s', hs', hs'T⟩
  -- The height function.
  let ht : M → ℝ := fun x => if hx : x ∈ η ⁻¹' Icc a b then (hcross x hx).choose else a
  have hht : ∀ x (hx : x ∈ η ⁻¹' Icc a b), ht x ∈ Ioo a b ∧
      (∀ s ∈ Icc a b, Φ (s - η x) x ∈ D ↔ s ≤ ht x) ∧
      (∀ s ∈ Icc a b, Φ (s - η x) x ∈ frontier D ↔ s = ht x) := by
    intro x hx
    simp only [ht, hx, dite_true]
    exact (hcross x hx).choose_spec
  -- The flow line through a point of a flow line is the same curve.
  have hline : ∀ x ∈ η ⁻¹' Icc a b, ∀ s ∈ Icc a b, ∀ s' : ℝ,
      Φ (s' - η (Φ (s - η x) x)) (Φ (s - η x) x) = Φ (s' - η x) x := by
    intro x hx s hs s'
    rw [hlevel x hx s hs, ← hadd, show s - η x + (s' - s) = s' - η x by ring]
  have hinv : ∀ x ∈ η ⁻¹' Icc a b, ∀ s ∈ Icc a b, ht (Φ (s - η x) x) = ht x := by
    intro x hx s hs
    have hyK : Φ (s - η x) x ∈ η ⁻¹' Icc a b := by
      change η (Φ (s - η x) x) ∈ Icc a b
      rw [hlevel x hx s hs]
      exact hs
    obtain ⟨hy1, hy2, -⟩ := hht _ hyK
    obtain ⟨hx1, hx2, -⟩ := hht x hx
    have e1 : ∀ s' ∈ Icc a b, Φ (s' - η x) x ∈ D ↔ s' ≤ ht (Φ (s - η x) x) := fun s' hs' => by
      rw [← hline x hx s hs s']
      exact hy2 s' hs'
    apply le_antisymm
    · exact (hx2 _ ⟨hy1.1.le, hy1.2.le⟩).1 ((e1 _ ⟨hy1.1.le, hy1.2.le⟩).2 le_rfl)
    · exact (e1 _ ⟨hx1.1.le, hx1.2.le⟩).1 ((hx2 _ ⟨hx1.1.le, hx1.2.le⟩).2 le_rfl)
  -- Smoothness of the height on the open band, by the implicit function theorem along the flow.
  let ϕ : Flow ℝ M :=
    { toFun := fun t x => Φ t x
      cont' := hΦj.continuous
      map_add' := fun t₁ t₂ x => by rw [add_comm]; exact hadd t₂ t₁ x
      map_zero' := hΦ0x }
  have hϕ : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun z : ℝ × M => ϕ z.1 z.2) := hΦj
  have hsmooth : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ ht (η ⁻¹' Ioo a b) := by
    intro y₀ hy₀
    have hy₀K : y₀ ∈ η ⁻¹' Icc a b := Ioo_subset_Icc_self hy₀
    obtain ⟨hh1, hh2, hh3⟩ := hht y₀ hy₀K
    have hhIcc : ht y₀ ∈ Icc a b := ⟨hh1.1.le, hh1.2.le⟩
    have hq₀ := (hh3 (ht y₀) hhIcc).2 rfl
    obtain ⟨U, hU, hqU, f, hf, hDU, hfq⟩ := hdef _ hq₀
    have hq₀K : η (Φ (ht y₀ - η y₀) y₀) ∈ Icc a b := by rw [hlevel y₀ hy₀K _ hhIcc]; exact hhIcc
    -- The open set where `f` is smooth, `df(Y) > 0` and `η ∈ (a, b)`.
    have hdYf : ∀ z ∈ U ∩ W, ContMDiffAt I 𝓘(ℝ, ℝ) ∞
        (fun p => mvfderiv (I := I) f p (Y p)) z := fun z hz =>
      mvfderiv_apply_contMDiffAt_of_section (hf.contMDiffAt (hU.mem_nhds hz.1))
        (hY.contMDiffAt (hW.mem_nhds hz.2))
    set Up : Set M := (U ∩ W) ∩ ((fun p => mvfderiv (I := I) f p (Y p)) ⁻¹' Ioi 0 ∩
      η ⁻¹' Ioo a b) with hUpdef
    have hUp : IsOpen Up := by
      have hc : ContinuousOn (fun p => (mvfderiv (I := I) f p (Y p), η p)) (U ∩ W) :=
        ContinuousOn.prodMk (fun z hz => (hdYf z hz).continuousAt.continuousWithinAt)
          hη.continuousOn
      have := hc.isOpen_inter_preimage (hU.inter hW)
        ((isOpen_Ioi (a := (0 : ℝ))).prod (isOpen_Ioo (a := a) (b := b)))
      convert this using 1
      ext z
      simp only [hUpdef, mem_inter_iff, mem_preimage, mem_prod]
    have hqUp : Φ (ht y₀ - η y₀) y₀ ∈ Up :=
      ⟨⟨hqU, hKW hq₀K⟩, hfq, by rw [mem_preimage, hlevel y₀ hy₀K _ hhIcc]; exact hh1⟩
    have hv := hvel y₀ (ht y₀ - η y₀) hq₀K
    have hfd : MDifferentiableAt I 𝓘(ℝ, ℝ) f (Φ (ht y₀ - η y₀) y₀) :=
      (hf.contMDiffAt (hU.mem_nhds hqU)).mdifferentiableAt (by norm_num)
    have htime := hasDerivAt_comp_of_hasMFDerivAt hv hfd
    rw [map_smul, smul_eq_mul] at htime
    have hdne := (mul_pos (inv_pos.mpr (hpos _ hq₀K)) hfq).ne'
    obtain ⟨τ, W', hW', hy₀W', hτ, hτ0, hroot⟩ :=
      DifferentialGeometry.Geometry.Topology.exists_smooth_flow_levelTime ϕ hϕ hUp (hf.mono fun z hz => hz.1.1)
        (t := ht y₀ - η y₀) hqUp htime hdne
    have hf0q := hf0 _ hq₀ U f hU hqU hf hDU
    -- Points of `W'` whose level time lands in the open band.
    have hsumc : ContinuousOn (fun x => η x + τ x) W' := hη.continuousOn.add hτ.continuousOn
    set W'' : Set M := W' ∩ ((fun x => η x + τ x) ⁻¹' Ioo a b ∩ η ⁻¹' Ioo a b) with hW''def
    have hW'' : IsOpen W'' := by
      have := (hsumc.prodMk hη.continuousOn).isOpen_inter_preimage hW'
        ((isOpen_Ioo (a := a) (b := b)).prod (isOpen_Ioo (a := a) (b := b)))
      convert this using 1
      ext z
      simp only [hW''def, mem_inter_iff, mem_preimage, mem_prod]
    have hy₀W'' : y₀ ∈ W'' := ⟨hy₀W', by simp only [mem_preimage]; rw [hτ0]; simpa using hh1, hy₀⟩
    have heq : ∀ x ∈ W'', ht x = η x + τ x := by
      intro x hx
      have hxK : x ∈ η ⁻¹' Icc a b := Ioo_subset_Icc_self hx.2.2
      have hsx : η x + τ x ∈ Icc a b := Ioo_subset_Icc_self hx.2.1
      have hτx : η x + τ x - η x = τ x := by ring
      obtain ⟨hzUp, hfz⟩ := hroot x hx.1
      change Φ (τ x) x ∈ Up at hzUp
      change f (Φ (τ x) x) = f (Φ (ht y₀ - η y₀) y₀) at hfz
      rw [hf0q] at hfz
      rw [← hτx] at hzUp hfz
      have hzD : Φ (η x + τ x - η x) x ∈ D := by
        have : Φ (η x + τ x - η x) x ∈ {y | f y ≤ 0} ∩ U := ⟨hfz.le, hzUp.1.1⟩
        rw [← hDU] at this
        exact this.1
      obtain ⟨δ, hδ, -, hδout⟩ := hpattern x hxK _ hsx U f hU hzUp.1.1 hf hDU hfz hzUp.2.1
      have hz := hfront x _ hzD (fun ε hε => ⟨η x + τ x + min δ ε / 2, ⟨by
        linarith [lt_min hδ hε], by linarith [min_le_right δ ε, lt_min hδ hε]⟩,
        hδout _ ⟨by linarith [lt_min hδ hε], by linarith [min_le_left δ ε, lt_min hδ hε]⟩⟩)
      exact (((hht x hxK).2.2 _ hsx).1 hz).symm
    have hsum : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun x => η x + τ x) y₀ :=
      (hηW.contMDiffAt (hW.mem_nhds (hKW hy₀K))).add (hτ.contMDiffAt (hW'.mem_nhds hy₀W'))
    exact (hsum.congr_of_eventuallyEq (Filter.eventuallyEq_of_mem (hW''.mem_nhds hy₀W'')
      heq)).contMDiffWithinAt
  exact ⟨Φ, hΦ0, hΦj, hadd, hlevel, ht, fun x hx => (hht x hx).1, fun x hx => (hht x hx).2.1,
    fun x hx => (hht x hx).2.2, hinv, hsmooth⟩

/-- **LC47.** Under the LC46 hypotheses (`η` continuous, smooth on an open `W ⊇ K = η⁻¹[a, b]`,
`K` compact, `Y` smooth on `W` with `dη(Y) > 0` on `K`), let `D` be closed with
`{η ≤ a} ⊆ int D`, `D ⊆ {η < b}`, and let every frontier point of `D` have a local defining
function `f` (`D = {f ≤ 0}` near it, `f` smooth there) with `df(Y) > 0` at the point. Then for every
`ρ ∈ (a, b)` a smooth isotopy `Hs`, jointly smooth with its inverse, `Hs 0 = id`, equal to the
identity off ONE compact subset of `η⁻¹(a, b)`, carries `D` onto `{η ≤ ρ}`. -/
theorem exists_isotopy_of_common_outward_field {η : M → ℝ} (hη : Continuous η)
    {W : Set M} (hW : IsOpen W) (hηW : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ η W) {a b ρ : ℝ}
    (hρ : ρ ∈ Ioo a b) (hK : IsCompact (η ⁻¹' Icc a b)) (hKW : η ⁻¹' Icc a b ⊆ W)
    (Y : (x : M) → TangentSpace I x)
    (hY : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (fun x => (⟨x, Y x⟩ : TangentBundle I M)) W)
    (hpos : ∀ x ∈ η ⁻¹' Icc a b, 0 < mvfderiv (I := I) η x (Y x))
    {D : Set M} (hD : IsClosed D) (hAD : {x | η x ≤ a} ⊆ interior D)
    (hDb : D ⊆ {x | η x < b})
    (hdef : ∀ q ∈ frontier D, ∃ U : Set M, IsOpen U ∧ q ∈ U ∧ ∃ f : M → ℝ,
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f U ∧ D ∩ U = {x | f x ≤ 0} ∩ U ∧
        0 < mvfderiv (I := I) f q (Y q)) :
    ∃ Hs : ℝ → Diffeomorph I I M M ∞,
      Hs 0 = Diffeomorph.refl I M ∞ ∧
      ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M => Hs p.1 p.2) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M => (Hs p.1).symm p.2) ∧
      (∃ S : Set M, IsCompact S ∧ S ⊆ η ⁻¹' Ioo a b ∧
        ∀ t x, x ∉ S → Hs t x = x ∧ (Hs t).symm x = x) ∧
      Hs 1 '' D = {x | η x ≤ ρ} := by
  classical
  have hab : a < b := hρ.1.trans hρ.2
  obtain ⟨Φ, hΦ0, hΦj, hadd, hlevel, ht, hht1, hht2, -, hinv, hsm⟩ :=
    exists_crossing_height_of_common_outward_field hη hW hηW hab hK hKW Y hY hpos hD hAD hDb hdef
  have hΦ0x : ∀ x, Φ 0 x = x := fun x => by rw [hΦ0]; rfl
  set K : Set M := η ⁻¹' Icc a b with hKdef
  set O : Set M := η ⁻¹' Ioo a b with hOdef
  have hO : IsOpen O := isOpen_Ioo.preimage hη
  have hOK : O ⊆ K := fun x hx => Ioo_subset_Icc_self hx
  -- Bounds `a < m₁ ≤ m₂ < b` for `ρ` and all heights.
  set Lρ : Set M := η ⁻¹' {ρ} with hLdef
  have hLO : Lρ ⊆ O := fun x hx => by
    simp only [hLdef, mem_preimage, mem_singleton_iff] at hx
    change η x ∈ Ioo a b
    rw [hx]
    exact hρ
  have hL : IsCompact Lρ :=
    hK.of_isClosed_subset (isClosed_singleton.preimage hη) (fun x hx => hOK (hLO hx))
  set Kh : Set ℝ := insert ρ (ht '' Lρ) with hKhdef
  have hKh : IsCompact Kh := (hL.image_of_continuousOn (hsm.continuousOn.mono hLO)).insert ρ
  have hKhne : Kh.Nonempty := ⟨ρ, mem_insert ρ _⟩
  have hKhab : Kh ⊆ Ioo a b := by
    rintro u (rfl | ⟨x, hx, rfl⟩)
    · exact hρ
    · exact hht1 x (hOK (hLO hx))
  set m₁ : ℝ := sInf Kh with hm₁def
  set m₂ : ℝ := sSup Kh with hm₂def
  have hmem : ∀ u ∈ Kh, u ∈ Icc m₁ m₂ := fun u hu =>
    ⟨csInf_le hKh.bddBelow hu, le_csSup hKh.bddAbove hu⟩
  have hρm : ρ ∈ Icc m₁ m₂ := hmem ρ (mem_insert ρ _)
  have hhtm : ∀ x ∈ K, ht x ∈ Icc m₁ m₂ := by
    intro x hx
    have hρI : ρ ∈ Icc a b := Ioo_subset_Icc_self hρ
    have hy : Φ (ρ - η x) x ∈ Lρ := by
      simp only [hLdef, mem_preimage, mem_singleton_iff]
      exact hlevel x hx ρ hρI
    rw [← hinv x hx ρ hρI]
    exact hmem _ (mem_insert_of_mem ρ ⟨_, hy, rfl⟩)
  obtain ⟨a', b', ha', hab', hb', ψ, hψ, hψ0, hψadd, hψfix, hψmono, hψtrans⟩ :=
    exists_real_flow_translating (hKhab (hKh.sInf_mem hKhne)).1 (hρm.1.trans hρm.2)
      (hKhab (hKh.sSup_mem hKhne)).2
  have hψab : ∀ u, ∀ s ∈ Icc a b, ψ u s ∈ Icc a b := by
    intro u s hs
    have hfa := hψfix u a (fun h => by linarith [h.1])
    have hfb := hψfix u b (fun h => by linarith [h.2])
    exact ⟨hfa ▸ (hψmono u).monotone hs.1, hfb ▸ (hψmono u).monotone hs.2⟩
  have hψinv : ∀ u s, ψ (-u) (ψ u s) = s := fun u s => by
    rw [← hψadd, add_neg_cancel, hψ0]
  -- The isotopy.
  let G : ℝ → M → M := fun t x =>
    if η x ∈ Icc a b then Φ (ψ (t * (ρ - ht x)) (η x) - η x) x else x
  have hGband : ∀ t, ∀ x ∈ K, G t x = Φ (ψ (t * (ρ - ht x)) (η x) - η x) x := fun t x hx => by
    simp only [G, show η x ∈ Icc a b from hx, ite_true]
  have hGfix : ∀ t x, η x ∉ Icc a' b' → G t x = x := by
    intro t x hx
    by_cases hxK : η x ∈ Icc a b
    · rw [hGband t x hxK, hψfix _ _ hx, sub_self, hΦ0x]
    · simp only [G, hxK, ite_false]
  have hGK : ∀ t, ∀ x ∈ K, G t x ∈ K ∧ η (G t x) = ψ (t * (ρ - ht x)) (η x) ∧
      ht (G t x) = ht x := by
    intro t x hx
    have hs := hψab (t * (ρ - ht x)) (η x) hx
    rw [hGband t x hx]
    refine ⟨?_, hlevel x hx _ hs, hinv x hx _ hs⟩
    change η _ ∈ Icc a b
    rw [hlevel x hx _ hs]
    exact hs
  have hGinv : ∀ t x, G (-t) (G t x) = x := by
    intro t x
    by_cases hxK : x ∈ K
    · obtain ⟨hyK, hyη, hyh⟩ := hGK t x hxK
      rw [hGband (-t) _ hyK, hyη, hyh, show -t * (ρ - ht x) = -(t * (ρ - ht x)) by ring,
        hψinv, hGband t x hxK, ← hadd]
      rw [show ψ (t * (ρ - ht x)) (η x) - η x + (η x - ψ (t * (ρ - ht x)) (η x)) = 0 by ring,
        hΦ0x]
    · have h1 : G t x = x := by simp only [G, show η x ∉ Icc a b from hxK, ite_false]
      rw [h1]
      simp only [G, show η x ∉ Icc a b from hxK, ite_false]
  -- Joint smoothness.
  have hψm : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (fun p : ℝ × ℝ => ψ p.1 p.2) := by
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    exact contMDiff_iff_contDiff.mpr hψ
  have hGj : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M => G p.1 p.2) := by
    intro p
    by_cases hp : p.2 ∈ O
    · -- On `ℝ × O` the map is the flow formula.
      have hηO : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ η O := hηW.mono (fun x hx => hKW (hOK hx))
      have hO' : IsOpen (univ ×ˢ O : Set (ℝ × M)) := isOpen_univ.prod hO
      have hηp : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun q : ℝ × M => η q.2)
          (univ ×ˢ O) := hηO.comp contMDiff_snd.contMDiffOn (fun q hq => hq.2)
      have hhtp : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun q : ℝ × M => ht q.2)
          (univ ×ˢ O) := hsm.comp contMDiff_snd.contMDiffOn (fun q hq => hq.2)
      have hpoly : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
          (fun q : ℝ × ℝ => q.1 * (ρ - q.2)) := by
        rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
        exact contMDiff_iff_contDiff.mpr (by fun_prop)
      have harg : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
          (fun q : ℝ × M => q.1 * (ρ - ht q.2)) (univ ×ˢ O) :=
        hpoly.comp_contMDiffOn (contMDiff_fst.contMDiffOn.prodMk hhtp)
      have hψq : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
          (fun q : ℝ × M => ψ (q.1 * (ρ - ht q.2)) (η q.2) - η q.2) (univ ×ˢ O) :=
        (hψm.comp_contMDiffOn (harg.prodMk hηp)).sub hηp
      have hF : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞
          (fun q : ℝ × M => Φ (ψ (q.1 * (ρ - ht q.2)) (η q.2) - η q.2) q.2) (univ ×ˢ O) :=
        hΦj.comp_contMDiffOn (hψq.prodMk contMDiff_snd.contMDiffOn)
      have hpO : p ∈ univ ×ˢ O := ⟨mem_univ _, hp⟩
      refine (hF.contMDiffAt (hO'.mem_nhds hpO)).congr_of_eventuallyEq ?_
      filter_upwards [hO'.mem_nhds hpO] with q hq
      exact hGband q.1 q.2 (hOK hq.2)
    · -- Off the open band, `G` is the identity near `p`.
      have hout : η p.2 ≤ a ∨ b ≤ η p.2 := by
        by_contra hcon
        push Not at hcon
        exact hp hcon
      have hnear : ∀ᶠ q in 𝓝 p, η q.2 ∉ Icc a' b' := by
        rcases hout with hle | hge
        · filter_upwards [(hη.comp continuous_snd).continuousAt.eventually
            (gt_mem_nhds (show η p.2 < a' by linarith))] with q hq
          exact fun h => by linarith [h.1, show η q.2 < a' from hq]
        · filter_upwards [(hη.comp continuous_snd).continuousAt.eventually
            (lt_mem_nhds (show b' < η p.2 by linarith))] with q hq
          exact fun h => by linarith [h.2, show b' < η q.2 from hq]
      refine contMDiffAt_snd.congr_of_eventuallyEq ?_
      filter_upwards [hnear] with q hq
      exact hGfix q.1 q.2 hq
  have hGjs : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M => G (-p.1) p.2) :=
    hGj.comp (contMDiff_fst.neg.prodMk contMDiff_snd)
  have hslice : ∀ {F : ℝ × M → M}, ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ F → ∀ t : ℝ,
      ContMDiff I I ∞ (fun x => F (t, x)) :=
    fun hF t => hF.comp (contMDiff_const.prodMk contMDiff_id)
  let Hs : ℝ → Diffeomorph I I M M ∞ := fun t =>
    { toFun := G t
      invFun := G (-t)
      left_inv := hGinv t
      right_inv := fun x => by simpa only [neg_neg] using hGinv (-t) x
      contMDiff_toFun := hslice hGj t
      contMDiff_invFun := hslice hGjs t }
  refine ⟨Hs, ?_, hGj, hGjs, ⟨η ⁻¹' Icc a' b', ?_, ?_,
    fun t x hx => ⟨hGfix t x hx, hGfix (-t) x hx⟩⟩, ?_⟩
  rotate_left
  · exact hK.of_isClosed_subset (isClosed_Icc.preimage hη)
      (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩)
  · intro x hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  rotate_left
  · ext x
    change G 0 x = x
    by_cases hxK : x ∈ K
    · rw [hGband 0 x hxK, zero_mul, hψ0, sub_self, hΦ0x]
    · simp only [G, show η x ∉ Icc a b from hxK, ite_false]
  · rw [Diffeomorph.image_eq_preimage_symm]
    ext w
    change G (-1) w ∈ D ↔ η w ≤ ρ
    by_cases hwK : w ∈ K
    · have hs := hψab (-1 * (ρ - ht w)) (η w) hwK
      rw [hGband (-1) w hwK, hht2 w hwK _ hs]
      have hlev : ψ (-1 * (ρ - ht w)) ρ = ht w := by
        rw [hψtrans _ _ hρm (by rw [show ρ + -1 * (ρ - ht w) = ht w by ring]; exact hhtm w hwK)]
        ring
      have key := (hψmono (-1 * (ρ - ht w))).le_iff_le (a := η w) (b := ρ)
      rwa [hlev] at key
    · have h1 : G (-1) w = w := by simp only [G, show η w ∉ Icc a b from hwK, ite_false]
      rw [h1]
      rcases lt_or_gt_of_ne (show η w ≠ a from fun h => hwK ⟨h.ge, h ▸ hab.le⟩) with hlt | hgt
      · exact ⟨fun _ => by linarith [hρ.1], fun _ => interior_subset (hAD hlt.le)⟩
      · have hwb : b < η w := by
          by_contra hle
          push Not at hle
          exact hwK ⟨hgt.le, hle⟩
        exact ⟨fun hwD => absurd (hDb hwD) (by simp only [mem_ofPred_eq]; linarith),
          fun hle => by linarith [hρ.2]⟩

/-- **Kernel of LC48 (source side).** Patch a field `Z` that is outward on the frontier of the core
and increases `η` on an open collar `Wc` of that frontier with a field `Y₀` that increases `η` on
the whole band (for LC48, `Y₀ = ∇η`), by a smooth cutoff equal to one near the frontier and
supported in the collar. The patched field `Y = θ Z + (1 - θ) Y₀` satisfies the LC46/LC47
hypotheses, so the core is carried onto every `{η ≤ ρ}`, `ρ ∈ (a, b)`, by one compactly supported
smooth isotopy. Only the collar, not the whole band, needs the margin for `Z`. -/
theorem exists_isotopy_of_collar_field {η : M → ℝ} (hη : Continuous η)
    {W : Set M} (hW : IsOpen W) (hηW : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ η W) {a b ρ : ℝ}
    (hρ : ρ ∈ Ioo a b) (hK : IsCompact (η ⁻¹' Icc a b)) (hKW : η ⁻¹' Icc a b ⊆ W)
    (Y₀ : (x : M) → TangentSpace I x)
    (hY₀ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (fun x => (⟨x, Y₀ x⟩ : TangentBundle I M)) W)
    (hpos₀ : ∀ x ∈ η ⁻¹' Icc a b, 0 < mvfderiv (I := I) η x (Y₀ x))
    {D : Set M} (hD : IsClosed D) (hAD : {x | η x ≤ a} ⊆ interior D)
    (hDb : D ⊆ {x | η x < b}) {Wc : Set M} (hWc : IsOpen Wc) (hfrWc : frontier D ⊆ Wc)
    (Z : (x : M) → TangentSpace I x)
    (hZ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (fun x => (⟨x, Z x⟩ : TangentBundle I M)) Wc)
    (hZpos : ∀ x ∈ Wc ∩ η ⁻¹' Icc a b, 0 < mvfderiv (I := I) η x (Z x))
    (hdef : ∀ q ∈ frontier D, ∃ U : Set M, IsOpen U ∧ q ∈ U ∧ ∃ f : M → ℝ,
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f U ∧ D ∩ U = {x | f x ≤ 0} ∩ U ∧
        0 < mvfderiv (I := I) f q (Z q)) :
    ∃ Hs : ℝ → Diffeomorph I I M M ∞,
      Hs 0 = Diffeomorph.refl I M ∞ ∧
      ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M => Hs p.1 p.2) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M => (Hs p.1).symm p.2) ∧
      (∃ S : Set M, IsCompact S ∧ S ⊆ η ⁻¹' Ioo a b ∧
        ∀ t x, x ∉ S → Hs t x = x ∧ (Hs t).symm x = x) ∧
      Hs 1 '' D = {x | η x ≤ ρ} := by
  classical
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  have hab : a < b := hρ.1.trans hρ.2
  -- The frontier lies in the open band, hence in `W`.
  have hfrK : frontier D ⊆ η ⁻¹' Icc a b := by
    intro q hq
    refine ⟨?_, (hDb (hD.frontier_subset hq)).le⟩
    by_contra hlt
    push Not at hlt
    exact hq.2 (hAD hlt.le)
  -- The cutoff: `θ = 0` near the complement of `Wc ∩ W`, `θ = 1` near the frontier.
  have hdisj : Disjoint (Wc ∩ W)ᶜ (frontier D) :=
    Set.disjoint_compl_left_iff_subset.mpr (fun q hq => ⟨hfrWc hq, hKW (hfrK hq)⟩)
  obtain ⟨θ, hθ0, hθ1, hθr⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed (n := (⊤ : ℕ∞)) I
    (hWc.inter hW).isClosed_compl isClosed_frontier hdisj
  have hθsupp : tsupport (θ : M → ℝ) ⊆ Wc ∩ W := by
    intro q hq
    by_contra hqU
    have hz : (θ : M → ℝ) =ᶠ[𝓝 q] 0 := hθ0.filter_mono (nhds_le_nhdsSet hqU)
    exact (notMem_tsupport_iff_eventuallyEq.mpr hz) hq
  have hθ1' : ∀ q ∈ frontier D, θ q = 1 := fun q hq => hθ1.self_of_nhdsSet q hq
  -- The patched field.
  let Y : (x : M) → TangentSpace I x := fun x => θ x • Z x + (1 - θ x) • Y₀ x
  have hθZ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (fun x => (⟨x, θ x • Z x⟩ : TangentBundle I M)) :=
    θ.contMDiff.contMDiffOn.smul_section_of_tsupport (hWc.inter hW) hθsupp
      (hZ.mono inter_subset_left)
  have hY : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (fun x => (⟨x, Y x⟩ : TangentBundle I M)) W :=
    hθZ.contMDiffOn.add_section
      ((contMDiff_const.sub θ.contMDiff).contMDiffOn.smul_section hY₀)
  have hYpos : ∀ x ∈ η ⁻¹' Icc a b, 0 < mvfderiv (I := I) η x (Y x) := by
    intro x hx
    have h0 := (hθr x).1
    have h1 : 0 ≤ 1 - θ x := sub_nonneg.mpr (hθr x).2
    change 0 < mvfderiv (I := I) η x (θ x • Z x + (1 - θ x) • Y₀ x)
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    by_cases hθx : θ x = 0
    · rw [hθx, zero_mul, zero_add, sub_zero, one_mul]
      exact hpos₀ x hx
    · have hxWc : x ∈ Wc := (hθsupp (subset_tsupport _ hθx)).1
      have hp := hZpos x ⟨hxWc, hx⟩
      have hθpos : 0 < θ x := lt_of_le_of_ne h0 (Ne.symm hθx)
      nlinarith [mul_nonneg h1 (hpos₀ x hx).le]
  have hYdef : ∀ q ∈ frontier D, ∃ U : Set M, IsOpen U ∧ q ∈ U ∧ ∃ f : M → ℝ,
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f U ∧ D ∩ U = {x | f x ≤ 0} ∩ U ∧
        0 < mvfderiv (I := I) f q (Y q) := by
    intro q hq
    obtain ⟨U, hU, hqU, f, hf, hDU, hfq⟩ := hdef q hq
    refine ⟨U, hU, hqU, f, hf, hDU, ?_⟩
    change 0 < mvfderiv (I := I) f q (θ q • Z q + (1 - θ q) • Y₀ q)
    rw [hθ1' q hq, one_smul, sub_self, zero_smul, add_zero]
    exact hfq
  exact exists_isotopy_of_common_outward_field hη hW hηW hρ hK hKW Y hY hYpos hD hAD hDb hYdef

end Band

end DifferentialGeometry.Geometry.Collapse
