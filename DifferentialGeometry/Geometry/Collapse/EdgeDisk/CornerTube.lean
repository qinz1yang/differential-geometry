import DifferentialGeometry.Geometry.Collapse.EdgeDisk.FaceIndependence
import DifferentialGeometry.Topology.Manifold.InverseFunction
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph

/-!
# R0 / R1: the rank-two descended corner chart and the whole corner tube (rim boxes)

Packages R0 (`exists_rankTwo_descended_chart74`) and R1 (`exists_whole_corner_tube74`) of draft 74
(§3.8 `LabelledCornerTubes`, §5.2 E; disposition D74-14). Blueprint `master207B.tex`, EDP06
(B:7092–7133: "`(g_i, T)` is a smooth function of `E` ... Its source differential has rank two by
EDP04, and `E` is a submersion to the two-dimensional `B₁`. Its descended differential on `B₁` is
therefore invertible") and FDC03 (B:7285–7365, the rim boxes). With `x = T - level`, `y = h_F`, the
four layers of D74-14:

1. descent — `x`, `y` are pulled back from smooth `T̄`, `h̄` on the base by the circle map `f`;
2. rank — `d(x, y)` of rank two at one point of the centre fibre gives an invertible descended
   differential (`EdgeDisk.bijective_of_comp_surjective_of_finrank_eq_two`), hence a descended
   chart `(T̄, h̄)` by the inverse function theorem (**R0**);
3. whole-tube shrinking — a closed (e.g. proper) circle map puts the WHOLE preimage of a smaller
   open base set into any open neighbourhood of the whole centre fibre;
4. sign model — the three-sided model `V = {y ≤ 0}`, `P = {y ≥ 0, x ≤ 0}`, `M₃ = {x ≥ 0, y ≥ 0}`,
   given on such a neighbourhood, holds on the WHOLE tube in the chart coordinates (**R1**).

Abstract kernels: an ambient charted space `Y` (model `I`), a base manifold `B` of dimension two
(model `IB`, boundaryless), a map `f : Y → B`. The binding (circle map `E` onto `B₁`, `T = A/s`,
`h_F` the zero ratio / slim endpoint coordinate, actual `V`, `P`, `M₃`) is a separate step; the
sign model on an ambient neighbourhood is an INPUT (rank two alone gives neither the sides nor
the exclusion of extra branches, D74-14).
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Manifold
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Geometry.Collapse.EdgeDisk

variable {E H Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace Y] [ChartedSpace H Y]
  {EB HB B : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [FiniteDimensional ℝ EB]
  [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} [IB.Boundaryless]
  [TopologicalSpace B] [ChartedSpace HB B] [IsManifold IB ∞ B]

/-- **R0 (`exists_rankTwo_descended_chart74`): the descended corner chart.** Let `f : Y → B` be
differentiable at `x₀`, `B` two-dimensional, and let the pair `(T, h)` agree near `x₀` with `(T̄ ∘
f, h̄ ∘ f)` for `T̄, h̄` smooth on an open `V ∋ f x₀` (descent). If `d(T, h)(x₀)` is onto `ℝ²` (rank
two), then `(T̄, h̄)` restricts to a partial diffeomorphism `Φ` of `B` onto an open set of `ℝ²` with
`f x₀ ∈ Φ.source ⊆ V`. -/
theorem exists_rankTwo_descended_chart74 (hEB : Module.finrank ℝ EB = 2) {f : Y → B} {x₀ : Y}
    (hf : MDifferentiableAt I IB f x₀) {T h : Y → ℝ} {V : TopologicalSpace.Opens B}
    (hx₀ : f x₀ ∈ V) {Tb hb : B → ℝ} (hTb : ContMDiffOn IB 𝓘(ℝ) ∞ Tb V)
    (hhb : ContMDiffOn IB 𝓘(ℝ) ∞ hb V)
    (hdesc : (fun z => (T z, h z)) =ᶠ[𝓝 x₀] fun z => (Tb (f z), hb (f z)))
    (hrank : Surjective (mfderiv I 𝓘(ℝ, ℝ × ℝ) (fun z => (T z, h z)) x₀)) :
    ∃ Φ : PartialDiffeomorph IB 𝓘(ℝ, ℝ × ℝ) B (ℝ × ℝ) ∞,
      f x₀ ∈ Φ.source ∧ Φ.source ⊆ V ∧ ∀ c ∈ Φ.source, Φ c = (Tb c, hb c) := by
  have : CompleteSpace EB := FiniteDimensional.complete ℝ EB
  let Q : B → ℝ × ℝ := fun c => (Tb c, hb c)
  have hQ : ContMDiffOn IB 𝓘(ℝ, ℝ × ℝ) ∞ Q V := hTb.prodMk_space hhb
  have hQd : MDifferentiableAt IB 𝓘(ℝ, ℝ × ℝ) Q (f x₀) :=
    ((hQ (f x₀) hx₀).contMDiffAt (V.isOpen.mem_nhds hx₀)).mdifferentiableAt (by simp)
  have hcomp : mfderiv I 𝓘(ℝ, ℝ × ℝ) (fun z => (T z, h z)) x₀ =
      (mfderiv IB 𝓘(ℝ, ℝ × ℝ) Q (f x₀)).comp (mfderiv I IB f x₀) := by
    rw [hdesc.mfderiv_eq]
    exact mfderiv_comp x₀ hQd hf
  have hsurj : Surjective ((mfderiv IB 𝓘(ℝ, ℝ × ℝ) Q (f x₀) : EB →L[ℝ] ℝ × ℝ).toLinearMap ∘ₗ
      (mfderiv I IB f x₀ : E →L[ℝ] EB).toLinearMap) := by
    intro v
    obtain ⟨w, hw⟩ := hrank v
    refine ⟨w, ?_⟩
    rw [hcomp] at hw
    exact hw
  have hbij := bijective_of_comp_surjective_of_finrank_eq_two hEB _ _ hsurj
  have hinv : (mfderiv IB 𝓘(ℝ, ℝ × ℝ) Q (f x₀)).IsInvertible := by
    let L : EB →L[ℝ] ℝ × ℝ := mfderiv IB 𝓘(ℝ, ℝ × ℝ) Q (f x₀)
    have hL : Bijective L := hbij
    exact ⟨(LinearEquiv.ofBijective (L : EB →ₗ[ℝ] ℝ × ℝ) hL).toContinuousLinearEquiv, rfl⟩
  obtain ⟨Φ', hx₀Φ', hEq⟩ :=
    DifferentialGeometry.Topology.isLocalDiffeomorphAt_of_contMDiffOn_of_isInvertible_mfderiv
      V.isOpen hx₀ hQ hinv
  refine ⟨DifferentialGeometry.Topology.PartialDiffeomorph.restrict Φ' (Φ'.source ∩ V)
    (Φ'.open_source.inter V.isOpen), ?_, ?_, ?_⟩
  · change f x₀ ∈ Φ'.source ∩ (Φ'.source ∩ V)
    exact ⟨hx₀Φ', hx₀Φ', hx₀⟩
  · intro c hc
    exact hc.2.2
  · intro c hc
    exact (hEq hc.1).symm

omit [FiniteDimensional ℝ EB] [IB.Boundaryless] [IsManifold IB ∞ B] in
/-- **Whole-tube shrinking** (layer 3): for a closed map `f`, an open `N` containing the WHOLE fibre
over `c₀` contains the whole preimage of an open neighbourhood of `c₀` inside any given open `V`. -/
theorem exists_open_tube_subset_EFC {f : Y → B} (hf : IsClosedMap f) {N : Set Y} (hN : IsOpen N)
    {c₀ : B} (hfib : f ⁻¹' {c₀} ⊆ N) {V : Set B} (hV : IsOpen V) (hc₀ : c₀ ∈ V) :
    ∃ U : Set B, IsOpen U ∧ c₀ ∈ U ∧ U ⊆ V ∧ f ⁻¹' U ⊆ N := by
  refine ⟨V ∩ (f '' Nᶜ)ᶜ, hV.inter (hf _ hN.isClosed_compl).isOpen_compl, ⟨hc₀, ?_⟩,
    inter_subset_left, ?_⟩
  · rintro ⟨y, hy, hyc⟩
    exact hy (hfib hyc)
  · intro y hy
    by_contra hyN
    exact hy.2 ⟨y, hyN, rfl⟩

/-- **R1 (`exists_whole_corner_tube74`): the whole labelled corner tube.** Let `f : Y → B` be
continuous and closed (whole-circle properness), `B` two-dimensional; `x = T`, `y = h` descend over
an open `V ∋ c₀` to smooth `T̄`, `h̄` (on the WHOLE preimage of `V`), with `T̄(c₀) = h̄(c₀) = 0`,
and `d(T, h)` of rank two at one point `x₀` of the centre fibre. Let an open `N ⊇ f⁻¹(c₀)` carry the
three-sided sign model for sets `Vtx`, `Edg`, `Reg`. Then there is a corner chart `Φ` with `c₀ ∈
Φ.source ⊆ V`, `Φ(c₀) = (0, 0)`, the whole tube `f⁻¹(Φ.source)` inside `N`, `Φ ∘ f = (T, h)` on the
tube, and on the WHOLE tube `Vtx = {y ≤ 0}`, `Edg = {y ≥ 0, x ≤ 0}`, `Reg = {x ≥ 0, y ≥ 0}` in the
chart coordinates. -/
theorem exists_whole_corner_tube74 (hEB : Module.finrank ℝ EB = 2) {f : Y → B}
    (hfc : Continuous f) (hfcl : IsClosedMap f) {c₀ : B} {T h : Y → ℝ}
    {V : TopologicalSpace.Opens B} (hc₀ : c₀ ∈ V) {Tb hb : B → ℝ}
    (hTb : ContMDiffOn IB 𝓘(ℝ) ∞ Tb V) (hhb : ContMDiffOn IB 𝓘(ℝ) ∞ hb V)
    (hdesc : ∀ y, f y ∈ V → T y = Tb (f y) ∧ h y = hb (f y)) (hcen : Tb c₀ = 0 ∧ hb c₀ = 0)
    {x₀ : Y} (hx₀ : f x₀ = c₀) (hf : MDifferentiableAt I IB f x₀)
    (hrank : Surjective (mfderiv I 𝓘(ℝ, ℝ × ℝ) (fun z => (T z, h z)) x₀))
    {N : Set Y} (hN : IsOpen N) (hfib : f ⁻¹' {c₀} ⊆ N) {Vtx Edg Reg : Set Y}
    (hsign : ∀ y ∈ N, (y ∈ Vtx ↔ h y ≤ 0) ∧ (y ∈ Edg ↔ 0 ≤ h y ∧ T y ≤ 0) ∧
      (y ∈ Reg ↔ 0 ≤ T y ∧ 0 ≤ h y)) :
    ∃ Φ : PartialDiffeomorph IB 𝓘(ℝ, ℝ × ℝ) B (ℝ × ℝ) ∞,
      c₀ ∈ Φ.source ∧ Φ.source ⊆ V ∧ Φ c₀ = (0, 0) ∧ f ⁻¹' Φ.source ⊆ N ∧
      (∀ y, f y ∈ Φ.source → (Φ (f y)).1 = T y ∧ (Φ (f y)).2 = h y) ∧
      ∀ y, f y ∈ Φ.source → (y ∈ Vtx ↔ (Φ (f y)).2 ≤ 0) ∧
        (y ∈ Edg ↔ 0 ≤ (Φ (f y)).2 ∧ (Φ (f y)).1 ≤ 0) ∧
        (y ∈ Reg ↔ 0 ≤ (Φ (f y)).1 ∧ 0 ≤ (Φ (f y)).2) := by
  have hx₀V : f x₀ ∈ V := hx₀ ▸ hc₀
  have hev : (fun z => (T z, h z)) =ᶠ[𝓝 x₀] fun z => (Tb (f z), hb (f z)) := by
    filter_upwards [hfc.continuousAt.preimage_mem_nhds (V.isOpen.mem_nhds hx₀V)] with z hz
    obtain ⟨h1, h2⟩ := hdesc z hz
    rw [h1, h2]
  obtain ⟨Φ₀, hΦ₀x, hΦ₀V, hΦ₀eq⟩ :=
    exists_rankTwo_descended_chart74 hEB hf hx₀V hTb hhb hev hrank
  rw [hx₀] at hΦ₀x
  obtain ⟨U, hU, hc₀U, hUΦ, hUN⟩ :=
    exists_open_tube_subset_EFC hfcl hN hfib Φ₀.open_source hΦ₀x
  let Φ := DifferentialGeometry.Topology.PartialDiffeomorph.restrict Φ₀ U hU
  have hsrc : Φ.source = Φ₀.source ∩ U := rfl
  have happ : ∀ c, Φ c = Φ₀ c := fun _ => rfl
  have hsrcU : Φ.source = U := by rw [hsrc]; exact inter_eq_right.mpr hUΦ
  have hcoord : ∀ y, f y ∈ Φ.source → (Φ (f y)).1 = T y ∧ (Φ (f y)).2 = h y := by
    intro y hy
    rw [hsrcU] at hy
    have hyV : f y ∈ V := hΦ₀V (hUΦ hy)
    rw [happ, hΦ₀eq (f y) (hUΦ hy)]
    obtain ⟨h1, h2⟩ := hdesc y hyV
    exact ⟨h1.symm, h2.symm⟩
  refine ⟨Φ, hsrcU ▸ hc₀U, fun c hc => hΦ₀V (hUΦ (hsrcU ▸ hc)), ?_, ?_, hcoord, ?_⟩
  · rw [happ, hΦ₀eq c₀ hΦ₀x, hcen.1, hcen.2]
  · rw [hsrcU]
    exact hUN
  · intro y hy
    obtain ⟨h1, h2⟩ := hcoord y hy
    have hyN : y ∈ N := hUN (hsrcU ▸ hy)
    rw [h1, h2]
    exact hsign y hyN

end DifferentialGeometry.Geometry.Collapse.EdgeDisk
