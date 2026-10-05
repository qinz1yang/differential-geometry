import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GRimRimChart
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GRimRimParam
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GRimPartialOfImm
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GRimEndProfile
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GRimCornerScale

/-!
# FC39 GROUP G, RIMBOX route B (sheet §3 K4–K7): the rim-chart kit on the slab

Lane FC39-G-RIMBOXc, dispositions D62-3 (b), (d), (e), (g), (i). Abstract pieces of the per-end rim
chart, stated on a boundaryless manifold `Y` with the transport flow `Fl`, the two-sided collar `C`
(`κ = 1`) and the unscaled rim parametrization `F = rimParam_GRIM Fl C 1` (G6a):

* `rimParamReparam_props_GRIM` — `G = F ∘ rimReparam_GRIM lam τ b` (ONE scale `lam`, profile `τ`,
  D62-3 (d)) is a smooth injective immersion of `S¹ × rimBox 3` with `P ∘ G = endCoord b ∘ τ` and
  `B ∘ G = -(lam x)`;
* `exists_rimChart_of_param_GRIM` — an injective immersion `G` of `S¹ × rimBox 2` into `Y`, followed by
  a partial diffeomorphism `ι : Y → M` defined on all of `Y` (here: the slab interior into the
  carrier, whose model has boundary), is a partial diffeomorphism with source `S¹ × rimBox 2`;
* `exists_tube_box_GRIM` — the tube lemma at the central rim (D62-3 (g): FIRST shrink into the raw
  tube by compactness of the central rim);
* `exists_endProfile_of_curve_GRIM` — the end profile `τ` from a curve `γ` in the edge base read by the
  axial coordinate (`q = d ∘ γ`, `q 0 = 0`, `q ≥ 0` inward, `dd ≠ 0`; G3 kernel with `a = 3`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0

section Param

variable {E H Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace Y] [ChartedSpace H Y]

/-- **The scaled rim parametrization** `G = F ∘ rimReparam_GRIM lam τ b` on `S¹ × rimBox 3`. -/
theorem rimParamReparam_props_GRIM {P B : Y → ℝ} (hP : ContMDiff I 𝓘(ℝ, ℝ) ∞ P)
    {U : TopologicalSpace.Opens Y} (Fl : ℝ → U ≃ₘ⟮I, I⟯ U)
    (hFl : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × U => Fl q.1 q.2)) {a₀ b₀ r' : ℝ}
    (hFlP : ∀ z : U, P z = 0 → -r' ≤ B z → ∀ t ∈ Ioo a₀ b₀, P (Fl t z) = t)
    (hFlB : ∀ (z : U) (t : ℝ), |B z| < r' → B (Fl t z) = B z)
    (C : EuclideanSpace ℝ (Fin 2) → Y) {δ : ℝ} (hδ1 : δ < 1) (hδr : δ ≤ r')
    (hC : ContMDiffOn (𝓡 2) I ∞ C {z | |‖z‖ - 1| < δ}) (hCinj : InjOn C {z | |‖z‖ - 1| < δ})
    (hCimm : ∀ z, |‖z‖ - 1| < δ → Injective (mfderiv (𝓡 2) I C z))
    (hCP : ∀ z, |‖z‖ - 1| < δ → P (C z) = 0 ∧ B (C z) = 1 - ‖z‖)
    (hCU : ∀ z, |‖z‖ - 1| < δ → C z ∈ U) {lam : ℝ} (hlam : 0 < lam) (hlamδ : 3 * lam < δ)
    {τ : ℝ → ℝ} (hτ : ContDiff ℝ ∞ τ) (hτd : ∀ y ∈ Icc (-3 : ℝ) 3, 0 < deriv τ y) (b : Bool)
    (hτw : ∀ y ∈ Icc (-3 : ℝ) 3, endCoord b (τ y) ∈ Ioo a₀ b₀) :
    ContMDiffOn ((𝓡 1).prod 𝓘(ℝ, ℝ × ℝ)) I ∞
        (rimParam_GRIM Fl C 1 ∘ rimReparam_GRIM lam τ b) {p | p.2 ∈ rimBox 3} ∧
      InjOn (rimParam_GRIM Fl C 1 ∘ rimReparam_GRIM lam τ b) {p | p.2 ∈ rimBox 3} ∧
      (∀ p : Circle × (ℝ × ℝ), p.2 ∈ rimBox 3 → Injective (mfderiv ((𝓡 1).prod 𝓘(ℝ, ℝ × ℝ)) I
        (rimParam_GRIM Fl C 1 ∘ rimReparam_GRIM lam τ b) p)) ∧
      ∀ p : Circle × (ℝ × ℝ), p.2 ∈ rimBox 3 →
        P ((rimParam_GRIM Fl C 1 ∘ rimReparam_GRIM lam τ b) p) = endCoord b (τ p.2.2) ∧
          B ((rimParam_GRIM Fl C 1 ∘ rimReparam_GRIM lam τ b) p) = -(lam * p.2.1) := by
  have hCP' : ∀ z, |‖z‖ - 1| < δ → P (C z) = 0 ∧ B (C z) = 1 * (1 - ‖z‖) := fun z hz =>
    ⟨(hCP z hz).1, by rw [one_mul]; exact (hCP z hz).2⟩
  obtain ⟨hsm, hinj, himm, hval⟩ :=
    rimParam_props_GRIM hP Fl hFl hFlP hFlB C one_pos hδ1 (by rw [one_mul]; exact hδr) hC hCinj
      hCimm hCP' hCU
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have hmaps : ∀ p : Circle × (ℝ × ℝ), p.2 ∈ rimBox 3 →
      |(rimReparam_GRIM lam τ b p).2.1| < 1 * δ ∧ (rimReparam_GRIM lam τ b p).2.2 ∈ Ioo a₀ b₀ := by
    intro p hp
    refine ⟨?_, hτw _ ⟨(abs_lt.mp hp.2).1.le, (abs_lt.mp hp.2).2.le⟩⟩
    change |lam * p.2.1| < 1 * δ
    rw [abs_mul, abs_of_pos hlam, one_mul]
    nlinarith [hp.1, abs_nonneg p.2.1]
  have hΩ : IsOpen {p : Circle × (ℝ × ℝ) | |p.2.1| < 1 * δ ∧ p.2.2 ∈ Ioo a₀ b₀} :=
    (isOpen_lt (continuous_abs.comp (continuous_fst.comp continuous_snd)) continuous_const).inter
      (isOpen_Ioo.preimage (continuous_snd.comp continuous_snd))
  have hR := contMDiff_rimReparam_GRIM lam hτ b
  refine ⟨hsm.comp hR.contMDiffOn fun p hp => hmaps p hp, hinj.comp
    (rimReparam_injOn_GRIM hlam.ne' hτ hτd b) fun p hp => hmaps p hp, fun p hp => ?_,
    fun p hp => ?_⟩
  · have hFd : MDifferentiableAt ((𝓡 1).prod 𝓘(ℝ, ℝ × ℝ)) I (rimParam_GRIM Fl C 1)
        (rimReparam_GRIM lam τ b p) :=
      ((hsm _ (hmaps p hp)).contMDiffAt (hΩ.mem_nhds (hmaps p hp))).mdifferentiableAt hn
    have hRd := (hR p).mdifferentiableAt hn
    rw [mfderiv_comp p hFd hRd]
    exact (himm _ (hmaps p hp).1 (hmaps p hp).2).comp (rimReparam_mfderiv_injective_GRIM
      hlam.ne' hτ b p (hτd _ ⟨(abs_lt.mp hp.2).1.le, (abs_lt.mp hp.2).2.le⟩).ne')
  · obtain ⟨h1, h2⟩ := hval _ (hmaps p hp).1 (hmaps p hp).2
    exact ⟨h1, h2⟩

end Param

section Chart

variable {Y M HM : Type*} [TopologicalSpace Y] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Y]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞ Y] [TopologicalSpace HM]
  {J : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 3)) HM} [TopologicalSpace M] [ChartedSpace HM M]

/-- **A rim chart from an injective immersion through a globally defined partial diffeomorphism.** -/
theorem exists_rimChart_of_param_GRIM (ι : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) J Y M ∞)
    (hι : ι.source = univ) (G : Circle × (ℝ × ℝ) → Y)
    (hG : ContMDiffOn ((𝓡 1).prod 𝓘(ℝ, ℝ × ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞ G
      {p | p.2 ∈ rimBox 2})
    (hGinj : InjOn G {p | p.2 ∈ rimBox 2})
    (hGimm : ∀ p : Circle × (ℝ × ℝ), p.2 ∈ rimBox 2 →
      Injective (mfderiv ((𝓡 1).prod 𝓘(ℝ, ℝ × ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) G p)) :
    ∃ χ : PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ × ℝ)) J (Circle × (ℝ × ℝ)) M ∞,
      (∀ p, p ∈ χ.source ↔ p.2 ∈ rimBox 2) ∧ ∀ p, p.2 ∈ rimBox 2 → χ p = ι (G p) := by
  have hΩ : IsOpen {p : Circle × (ℝ × ℝ) | p.2 ∈ rimBox 2} :=
    (isOpen_rimBox_GRIM 2).preimage continuous_snd
  have hd : Module.finrank ℝ (EuclideanSpace ℝ (Fin 1) × (ℝ × ℝ)) =
      Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) := by
    simp
  obtain ⟨χY, hs, -, hχY⟩ := exists_partialDiffeomorph_of_injOn_immersion_GRIM G hΩ hG hGinj
    (fun p hp => hGimm p hp) hd
  refine ⟨χY.trans ι, fun p => ?_, fun p _ => ?_⟩
  · change p ∈ χY.source ∩ χY ⁻¹' ι.source ↔ _
    rw [hs, hι, preimage_univ, inter_univ]
    rfl
  · change ι (χY p) = ι (G p)
    rw [hχY]

end Chart

/-- **The tube lemma at the central rim**: a map continuous on an open set containing `S¹ × {z₀}`
which sends `S¹ × {z₀}` into an open set `T` sends a whole box `S¹ × (z₀ + (-η, η)²)` into `T`. -/
theorem exists_tube_box_GRIM {Z : Type*} [TopologicalSpace Z] (F : Circle × (ℝ × ℝ) → Z)
    {Ω : Set (Circle × (ℝ × ℝ))} (hΩ : IsOpen Ω) (hF : ContinuousOn F Ω) {T : Set Z}
    (hT : IsOpen T) (z₀ : ℝ × ℝ) (hz₀ : ∀ θ : Circle, (θ, z₀) ∈ Ω ∧ F (θ, z₀) ∈ T) :
    ∃ η : ℝ, 0 < η ∧ ∀ (θ : Circle) (X s : ℝ), |X - z₀.1| < η → |s - z₀.2| < η →
      (θ, (X, s)) ∈ Ω ∧ F (θ, (X, s)) ∈ T := by
  have hS : IsOpen (Ω ∩ F ⁻¹' T) := hF.isOpen_inter_preimage hΩ hT
  have hsub : (univ : Set Circle) ×ˢ ({z₀} : Set (ℝ × ℝ)) ⊆ Ω ∩ F ⁻¹' T := by
    rintro ⟨θ, z⟩ ⟨-, hz⟩
    have hz' : z = z₀ := hz
    rw [hz']
    exact hz₀ θ
  obtain ⟨U₁, V₁, -, hV₁, hsU, hzV, hUV⟩ := generalized_tube_lemma isCompact_univ
    isCompact_singleton hS hsub
  obtain ⟨η, hη, hball⟩ := Metric.isOpen_iff.mp hV₁ z₀ (hzV rfl)
  refine ⟨η, hη, fun θ X s hX hs => ?_⟩
  have hmem : (X, s) ∈ Metric.ball z₀ η := by
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq]
    exact ⟨hX, hs⟩
  exact hUV ⟨hsU (mem_univ θ), hball hmem⟩

/-- **The end profile from a curve in the edge base** (sheet §3 K4, D62-3 (d)): `q = d ∘ γ` with
`φ ∘ γ` affine of nonzero slope, `q 0 = 0`, `q ≥ 0` inward and `dd ≠ 0` has `q' 0 > 0`; for every
small scale `l` the profile `τ` with `q ∘ τ = l y` on `[-3, 3]`, `τ' > 0`, `τ ∈ (-η, η)` exists. -/
theorem exists_endProfile_of_curve_GRIM {N : Type*} [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 1)) N] {γ : ℝ → N} {φ d : N → ℝ}
    {Ud : Set N} (hUd : IsOpen Ud) (hd : ContMDiffOn (𝓡 1) 𝓘(ℝ, ℝ) ∞ d Ud) (hγ0 : γ 0 ∈ Ud)
    {δ₀ : ℝ} (hδ₀ : 0 < δ₀) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 1) ∞ γ (Ioo (-δ₀) δ₀))
    {Vφ : Set N} (hVφ : IsOpen Vφ) (hφ : ContMDiffOn (𝓡 1) 𝓘(ℝ, ℝ) ∞ φ Vφ) (hγV : γ 0 ∈ Vφ)
    {a c : ℝ} (ha : a ≠ 0) (hφγ : ∀ s ∈ Ioo (-δ₀) δ₀, φ (γ s) = a * s + c)
    (hd0 : mfderiv (𝓡 1) 𝓘(ℝ, ℝ) d (γ 0) ≠ 0) (hdγ0 : d (γ 0) = 0)
    (hpos : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 ≤ d (γ s)) {η : ℝ} (hη : 0 < η) :
    ∃ l₀ : ℝ, 0 < l₀ ∧ ∀ l, 0 < l → l ≤ l₀ → ∃ τ : ℝ → ℝ, ContDiff ℝ ∞ τ ∧ τ 0 = 0 ∧
      ∀ y ∈ Icc (-3 : ℝ) 3, d (γ (τ y)) = l * y ∧ 0 < deriv τ y ∧ τ y ∈ Ioo (-η) η := by
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have h0 : (0 : ℝ) ∈ Ioo (-δ₀) δ₀ := ⟨by linarith, hδ₀⟩
  have hγc : ContinuousAt γ 0 := (hγ.continuousOn).continuousAt (isOpen_Ioo.mem_nhds h0)
  obtain ⟨δ₁, hδ₁, hδ₁U⟩ : ∃ δ₁ > 0, ∀ s, |s| < δ₁ → γ s ∈ Ud := by
    have hev : ∀ᶠ s in 𝓝 (0 : ℝ), γ s ∈ Ud := hγc.eventually (hUd.mem_nhds hγ0)
    obtain ⟨δ₁, hδ₁, h⟩ := Metric.eventually_nhds_iff.mp hev
    exact ⟨δ₁, hδ₁, fun s hs => h (by rw [Real.dist_eq, sub_zero]; exact hs)⟩
  set δq : ℝ := min (min δ₀ δ₁) η with hδq
  have hδq0 : 0 < δq := lt_min (lt_min hδ₀ hδ₁) hη
  have hsub : ∀ s ∈ Ioo (-δq) δq, s ∈ Ioo (-δ₀) δ₀ ∧ |s| < δ₁ ∧ s ∈ Ioo (-η) η := by
    intro s hs
    have h1 : δq ≤ δ₀ := (min_le_left _ _).trans (min_le_left _ _)
    have h2 : δq ≤ δ₁ := (min_le_left _ _).trans (min_le_right _ _)
    have h3 : δq ≤ η := min_le_right _ _
    exact ⟨⟨by linarith [hs.1], by linarith [hs.2]⟩, abs_lt.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩,
      ⟨by linarith [hs.1], by linarith [hs.2]⟩⟩
  -- smoothness of `q = d ∘ γ` on `(-δq, δq)`
  have hqm : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun s => d (γ s)) (Ioo (-δq) δq) :=
    hd.comp (hγ.mono fun s hs => (hsub s hs).1) fun s hs => hδ₁U s (hsub s hs).2.1
  have hq : ContDiffOn ℝ ∞ (fun s => d (γ s)) (Ioo (-δq) δq) := contMDiffOn_iff_contDiffOn.mp hqm
  have h0q : (0 : ℝ) ∈ Ioo (-δq) δq := ⟨by linarith, hδq0⟩
  have hqd : DifferentiableAt ℝ (fun s => d (γ s)) 0 :=
    (hq.contDiffAt (isOpen_Ioo.mem_nhds h0q)).differentiableAt (by simp)
  -- the derivative is nonzero and positive
  have hγd : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 1) γ 0 :=
    ((hγ.contMDiffAt (isOpen_Ioo.mem_nhds h0)).mdifferentiableAt hn)
  have hφd : MDifferentiableAt (𝓡 1) 𝓘(ℝ, ℝ) φ (γ 0) :=
    ((hφ.contMDiffAt (hVφ.mem_nhds hγV)).mdifferentiableAt hn)
  have hdd : MDifferentiableAt (𝓡 1) 𝓘(ℝ, ℝ) d (γ 0) :=
    ((hd.contMDiffAt (hUd.mem_nhds hγ0)).mdifferentiableAt hn)
  have hφγe : (fun s => φ (γ s)) =ᶠ[𝓝 (0 : ℝ)] fun s => a * s + c :=
    Filter.eventually_of_mem (isOpen_Ioo.mem_nhds h0) fun s hs => hφγ s hs
  have hne := deriv_comp_ne_zero_of_coordinate_GRIM hγd hφd hdd ha hφγe hd0
  have hposd := deriv_pos_of_nonneg_right_GRIM hqd hdγ0 hne hpos
  obtain ⟨l₀, hl₀, hτ⟩ := exists_endProfile_GRIM hδq0 hq hdγ0 hposd (by norm_num : (0 : ℝ) < 3)
  refine ⟨l₀, hl₀, fun l hl hll => ?_⟩
  obtain ⟨τ, hτc, hτ0, hτy⟩ := hτ l hl hll
  exact ⟨τ, hτc, hτ0, fun y hy => ⟨(hτy y hy).1, (hτy y hy).2.1, (hsub _ (hτy y hy).2.2).2.2⟩⟩

end GC.GraphManifold.Assembly.FC39P0
