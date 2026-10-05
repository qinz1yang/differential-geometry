import DifferentialGeometry.Geometry.Fibration.ActualEdgeDiskCoverage
import DifferentialGeometry.Geometry.Fibration.ActualEdgeBufferCollarApplications

/-!
# EDP04's original whole-disk / rim coverage on the final family (physical units)

Lane C14-EDP3. Blueprint `master207B.tex`, EDP04 (B:6949–7038; "The initial fiber is exactly the
original `{η_i = a, t ≤ 4Δ}` in its radius-`100Δ` domain, by LFR27. It is LFR28's closed smooth
disk"), external review 53 §2.3 (supplied by `edgeDisk` + EDP03's derived lemmas). At an edge
centre `j` of `LocalChartPacketsC14`, with `η = η_j`, `t = Fs/ρ` and the physical fibres
`FibP a = {p ∈ B(j, 100Δρ(j)) : η p = a, t p ≤ 4Δ}`:

* `edp04_original_slab_C14`: for `-4Δ < a₀ < 0 < b₀ < 4Δ`, `FibP 0 × (a₀, b₀)` is homeomorphic to
  the WHOLE original slab `{p ∈ B(j, 100Δρ(j)) : η p ∈ (a₀, b₀), t p ≤ 4Δ}`, with `η ∘ Φ = pr₂`,
  `Φ(x, 0) = x` and the rim `{t = 4Δ}` onto the rim.
* `edp04_fibre_closedCell_phys_EDP3`: every `FibP a`, `|a| < 4Δ`, is homeomorphic to
  `ClosedCell 2`, compact and connected.
* `edp04_original_fibre_C14`: the same, together with `FibP 0 ≃ₜ FibP a` matching the rims.
* `edp04_initial_fibre_EDP3` (consumer, with EDP03's E-free clauses): for `|a| < 4Δ` the initial
  fibre of EDP04's homotopy (EI) in `Y_j`, `{p ∈ Y_j : η p = a, H₀ p ≤ 4Δ}`, is the whole original
  fibre `FibP a`, its rim `{H₀ = 4Δ}` is `{t = 4Δ}`, and `FibP a` lies in `B(j, 6Δρ(j))` and in
  the interior of EDP03's compact buffer `Q_j`; `edp04_initial_fibre_staged_EDP3`: the same for
  an admissible staged prefix, with no numerical hypothesis.

The transport of these fibres along the adjusted pair `(g_j, T)` of EDP04 needs the GAF02 final
map and EDP01's `s` (sheet-C14-EDP3.md §4); it is not here.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology NNReal
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis DifferentialGeometry.Topology

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}

/-- **The whole original slab is covered by the original disk trivialization** (EDP04, physical
units): see the module docstring. -/
theorem edp04_original_slab_C14
    (L : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz) (hΔ : 0 < Δ) {j : X} (hj : j ∈ L.edge.centres) {a₀ b₀ : ℝ}
    (ha₀ : -(4 * Δ) < a₀) (h0 : (0 : ℝ) ∈ Ioo a₀ b₀) (hb₀ : b₀ < 4 * Δ) :
    ∃ Φ : {p : X // p ∈ ball j (100 * Δ * ρ j) ∧ L.edge.coord j p = 0 ∧
          L.edge.smoothing p / ρ p ≤ 4 * Δ} × Ioo a₀ b₀ ≃ₜ
        {p : X // p ∈ ball j (100 * Δ * ρ j) ∧ L.edge.coord j p ∈ Ioo a₀ b₀ ∧
          L.edge.smoothing p / ρ p ≤ 4 * Δ},
      (∀ q, L.edge.coord j (Φ q : X) = q.2) ∧ (∀ x, (Φ (x, ⟨0, h0⟩) : X) = x) ∧
      ∀ q, L.edge.smoothing (Φ q : X) / ρ (Φ q : X) = 4 * Δ ↔
        L.edge.smoothing (q.1 : X) / ρ (q.1 : X) = 4 * Δ := by
  have hrj := hρ j
  have hq : ∀ y, L.edge.smoothing y / ρ j / (ρ y / ρ j) = L.edge.smoothing y / ρ y := fun y => by
    have := hρ y
    field_simp
  have hHle : ∀ y, edgeRowHeight Δ (fun x => L.edge.smoothing x / ρ j) (fun x => ρ x / ρ j) y ≤
      4 * Δ ↔ L.edge.smoothing y / ρ y ≤ 4 * Δ := fun y => by
    rw [edgeRowHeight_le_iff hΔ, hq]
  have hH4 : ∀ y, edgeRowHeight Δ (fun x => L.edge.smoothing x / ρ j) (fun x => ρ x / ρ j) y =
      4 * Δ ↔ L.edge.smoothing y / ρ y = 4 * Δ := fun y => by
    rw [edgeRowHeight_eq_four_iff_EDP3 hΔ, hq]
  set Bp : Set X := ball j (100 * Δ * ρ j) with hBp
  have hball : ∀ y, (ρ j)⁻¹ * dist y j < 100 * Δ ↔ y ∈ Bp := fun y => by
    rw [hBp, mem_ball, inv_mul_lt_iff₀ hrj]
    constructor <;> intro h <;> linarith
  have hD := L.edgeDisk j hj
  have hcc := L.edge.chart_center j hj
  set η := L.edge.coord j with hηdef
  set Fs := L.edge.smoothing with hFsdef
  let c := L.edge.chart j hj
  let hMc : CompleteSpace X := complete_of_compact
  let _ := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let _ := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let _ : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let _ : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let _ : CompleteSpace X := (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
  have hc : η = c.coord := by
    rw [hηdef]
    unfold EdgeFamily.coord
    rw [dite_eq_left hj]
  obtain ⟨P, hP⟩ := hD
  have hPc : P.coord = η := by
    rw [hc]
    exact congrArg EdgeChart.coord hP
  have hPb : ∀ y, y ∈ ball P.center (100 * Δ) ↔ y ∈ Bp := fun y => by
    have hcen : P.center = j := (congrArg EdgeChart.center hP).trans hcc
    rw [hcen, ← hball y]
    rfl
  obtain ⟨Φn, h1, h2, h3⟩ := P.slab_homeomorph_EDP3 hΔ ha₀ h0 hb₀
  have hZ : {y : X | y ∈ ball P.center (100 * Δ) ∧ P.coord y = 0 ∧
      edgeRowHeight Δ (fun x => Fs x / ρ j) (fun x => ρ x / ρ j) y ≤ 4 * Δ} =
      {p : X | p ∈ Bp ∧ η p = 0 ∧ Fs p / ρ p ≤ 4 * Δ} := by
    ext y
    simp only [mem_ofPred_eq, hPb, hPc, hHle]
  have hS : {y : X | y ∈ ball P.center (100 * Δ) ∧ P.coord y ∈ Ioo a₀ b₀ ∧
      edgeRowHeight Δ (fun x => Fs x / ρ j) (fun x => ρ x / ρ j) y ≤ 4 * Δ} =
      {p : X | p ∈ Bp ∧ η p ∈ Ioo a₀ b₀ ∧ Fs p / ρ p ≤ 4 * Δ} := by
    ext y
    simp only [mem_ofPred_eq, hPb, hPc, hHle]
  let eZ := Homeomorph.setCongr hZ
  let eS := Homeomorph.setCongr hS
  refine ⟨((eZ.symm.prodCongr (Homeomorph.refl _)).trans Φn).trans eS, fun q => ?_, fun x => ?_,
    fun q => ?_⟩
  · exact (congrFun hPc _).symm.trans (h1 (eZ.symm q.1, q.2))
  · exact h2 (eZ.symm x)
  · have h := h3 (eZ.symm q.1, q.2)
    rw [hH4, hH4] at h
    exact h

/-- **Every whole original fibre is a closed disk, in physical units** (LFR28's disk at every
`|a| < 4Δ`): `FibP a ≃ₜ ClosedCell 2`, compact and connected. -/
theorem edp04_fibre_closedCell_phys_EDP3
    (L : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz) (hΔ : 0 < Δ) {j : X} (hj : j ∈ L.edge.centres) {a : ℝ} (ha : |a| < 4 * Δ) :
    Nonempty ({p : X // p ∈ ball j (100 * Δ * ρ j) ∧ L.edge.coord j p = a ∧
        L.edge.smoothing p / ρ p ≤ 4 * Δ} ≃ₜ ClosedCell 2) ∧
      CompactSpace {p : X // p ∈ ball j (100 * Δ * ρ j) ∧ L.edge.coord j p = a ∧
        L.edge.smoothing p / ρ p ≤ 4 * Δ} ∧
      ConnectedSpace {p : X // p ∈ ball j (100 * Δ * ρ j) ∧ L.edge.coord j p = a ∧
        L.edge.smoothing p / ρ p ≤ 4 * Δ} := by
  have hrj := hρ j
  have hq : ∀ y, L.edge.smoothing y / ρ j / (ρ y / ρ j) = L.edge.smoothing y / ρ y := fun y => by
    have := hρ y
    field_simp
  have hHle : ∀ y, edgeRowHeight Δ (fun x => L.edge.smoothing x / ρ j) (fun x => ρ x / ρ j) y ≤
      4 * Δ ↔ L.edge.smoothing y / ρ y ≤ 4 * Δ := fun y => by
    rw [edgeRowHeight_le_iff hΔ, hq]
  set Bp : Set X := ball j (100 * Δ * ρ j) with hBp
  have hball : ∀ y, (ρ j)⁻¹ * dist y j < 100 * Δ ↔ y ∈ Bp := fun y => by
    rw [hBp, mem_ball, inv_mul_lt_iff₀ hrj]
    constructor <;> intro h <;> linarith
  have hD := L.edgeDisk j hj
  have hcc := L.edge.chart_center j hj
  set η := L.edge.coord j with hηdef
  set Fs := L.edge.smoothing with hFsdef
  let c := L.edge.chart j hj
  let hMc : CompleteSpace X := complete_of_compact
  let _ := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let _ := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let _ : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let _ : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let _ : CompleteSpace X := (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
  have hc : η = c.coord := by
    rw [hηdef]
    unfold EdgeFamily.coord
    rw [dite_eq_left hj]
  obtain ⟨P, hP⟩ := hD
  have hPc : P.coord = η := by
    rw [hc]
    exact congrArg EdgeChart.coord hP
  have hPb : ∀ y, y ∈ ball P.center (100 * Δ) ↔ y ∈ Bp := fun y => by
    have hcen : P.center = j := (congrArg EdgeChart.center hP).trans hcc
    rw [hcen, ← hball y]
    rfl
  obtain ⟨⟨ψ⟩, -, hconn⟩ := P.fibre_closedCell_EDP3 hΔ ha
  have hF : {y : X | y ∈ ball P.center (100 * Δ) ∧ P.coord y = a ∧
      edgeRowHeight Δ (fun x => Fs x / ρ j) (fun x => ρ x / ρ j) y ≤ 4 * Δ} =
      {p : X | p ∈ Bp ∧ η p = a ∧ Fs p / ρ p ≤ 4 * Δ} := by
    ext y
    simp only [mem_ofPred_eq, hPb, hPc, hHle]
  let eF := Homeomorph.setCongr hF
  have hcell : ConnectedSpace (ClosedCell 2) := (eF.symm.trans ψ).connectedSpace_iff.mp
    (eF.connectedSpace_iff.mp hconn)
  exact ⟨⟨eF.symm.trans ψ⟩, (eF.symm.trans ψ).symm.compactSpace,
    (eF.symm.trans ψ).symm.connectedSpace_iff.mp hcell⟩

/-- **Every whole original fibre is a closed disk** (EDP04's initial fibre, physical units): for
`|a| < 4Δ`, `FibP a ≃ₜ ClosedCell 2`, compact, connected, and `FibP 0 ≃ₜ FibP a` matching the rims
`{t = 4Δ}`. -/
theorem edp04_original_fibre_C14
    (L : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz) (hΔ : 0 < Δ) {j : X} (hj : j ∈ L.edge.centres) {a : ℝ} (ha : |a| < 4 * Δ) :
    Nonempty ({p : X // p ∈ ball j (100 * Δ * ρ j) ∧ L.edge.coord j p = a ∧
        L.edge.smoothing p / ρ p ≤ 4 * Δ} ≃ₜ ClosedCell 2) ∧
      CompactSpace {p : X // p ∈ ball j (100 * Δ * ρ j) ∧ L.edge.coord j p = a ∧
        L.edge.smoothing p / ρ p ≤ 4 * Δ} ∧
      ConnectedSpace {p : X // p ∈ ball j (100 * Δ * ρ j) ∧ L.edge.coord j p = a ∧
        L.edge.smoothing p / ρ p ≤ 4 * Δ} ∧
      ∃ φ : {p : X // p ∈ ball j (100 * Δ * ρ j) ∧ L.edge.coord j p = 0 ∧
          L.edge.smoothing p / ρ p ≤ 4 * Δ} ≃ₜ
        {p : X // p ∈ ball j (100 * Δ * ρ j) ∧ L.edge.coord j p = a ∧
          L.edge.smoothing p / ρ p ≤ 4 * Δ},
        ∀ x, L.edge.smoothing (φ x : X) / ρ (φ x : X) = 4 * Δ ↔
          L.edge.smoothing (x : X) / ρ (x : X) = 4 * Δ := by
  have hab := abs_nonneg a
  have h0 : (0 : ℝ) ∈ Ioo (-((|a| + 4 * Δ) / 2)) ((|a| + 4 * Δ) / 2) :=
    ⟨by linarith, by linarith⟩
  have haI : a ∈ Ioo (-((|a| + 4 * Δ) / 2)) ((|a| + 4 * Δ) / 2) :=
    ⟨by linarith [neg_abs_le a], by linarith [le_abs_self a]⟩
  obtain ⟨Φ, hcoord, -, hrim⟩ := edp04_original_slab_C14 L hΔ hj (by linarith) h0 (by linarith)
  let φ : {p : X // p ∈ ball j (100 * Δ * ρ j) ∧ L.edge.coord j p = 0 ∧
        L.edge.smoothing p / ρ p ≤ 4 * Δ} ≃ₜ
      {p : X // p ∈ ball j (100 * Δ * ρ j) ∧ L.edge.coord j p = a ∧
        L.edge.smoothing p / ρ p ≤ 4 * Δ} :=
    { toFun := fun x => ⟨(Φ (x, ⟨a, haI⟩) : X), (Φ (x, ⟨a, haI⟩)).2.1, hcoord _,
        (Φ (x, ⟨a, haI⟩)).2.2.2⟩
      invFun := fun y => (Φ.symm ⟨y.1, y.2.1, by rw [y.2.2.1]; exact haI, y.2.2.2⟩).1
      left_inv := fun x => by simp
      right_inv := fun y => by
        apply Subtype.ext
        set q := Φ.symm ⟨y.1, y.2.1, by rw [y.2.2.1]; exact haI, y.2.2.2⟩ with hq
        have hq2 : (q.2 : ℝ) = a := by
          have h := hcoord q
          rw [hq, Homeomorph.apply_symm_apply] at h
          rw [← h]
          exact y.2.2.1
        have he : (q.1, (⟨a, haI⟩ : Ioo (-((|a| + 4 * Δ) / 2)) ((|a| + 4 * Δ) / 2))) = q :=
          Prod.ext rfl (Subtype.ext hq2.symm)
        change (Φ (q.1, ⟨a, haI⟩) : X) = y.1
        rw [he, hq, Homeomorph.apply_symm_apply]
      continuous_toFun := ((continuous_subtype_val.comp Φ.continuous).comp
        (continuous_id.prodMk continuous_const)).subtype_mk _
      continuous_invFun := continuous_fst.comp
        (Φ.symm.continuous.comp (continuous_subtype_val.subtype_mk _)) }
  obtain ⟨hcell, hc, hconn⟩ := edp04_fibre_closedCell_phys_EDP3 L hΔ hj ha
  exact ⟨hcell, hc, hconn, φ, fun x => hrim _⟩

/-- **EDP04's initial fibre is the whole original disk** (consumer of EDP03's E-free clauses and of
the coverage above): for `|a| < 4Δ`, in `Y = {p ∈ B(j, 100Δρ(j)) : |η| < 5Δ, t < 5Δ}`, the initial
fibre `{p ∈ Y : η p = a, H₀ p ≤ 4Δ}` of the homotopy (EI) is the whole original fibre
`F_a = {p ∈ B(j, 100Δρ(j)) : η p = a, t p ≤ 4Δ}`, its rim `{H₀ = 4Δ}` is `{t = 4Δ}`, `F_a` lies in
`B(j, 6Δρ(j))` and in the interior of a compact buffer `Q ⊆ Y` carrying (EBuf), and `F_a` is a
compact connected closed disk. -/
theorem edp04_initial_fibre_EDP3
    (L : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz)
    (hΔ : 1 ≤ Δ) (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8) (hlam : 100 * Δ * Λ ≤ 1 / 10 ^ 8)
    (hσc : σc ≤ 1 / 1000) (hb : b * (1000 * Δ) ≤ 1) {j : X} (hj : j ∈ L.edge.centres) {a : ℝ}
    (ha : |a| < 4 * Δ) :
    let η := L.edge.coord j
    let t : X → ℝ := fun z => L.edge.smoothing z / ρ z
    let H₀ := edgeRowHeight Δ L.edge.smoothing ρ
    let Y : Set X := {p | p ∈ ball j (100 * Δ * ρ j) ∧ |η p| < 5 * Δ ∧ t p < 5 * Δ}
    let Fa : Set X := {p | p ∈ ball j (100 * Δ * ρ j) ∧ η p = a ∧ t p ≤ 4 * Δ}
    {p | p ∈ Y ∧ η p = a ∧ H₀ p ≤ 4 * Δ} = Fa ∧
    {p | p ∈ Y ∧ η p = a ∧ H₀ p = 4 * Δ} = {p | p ∈ Fa ∧ t p = 4 * Δ} ∧
    Fa ⊆ ball j (6 * Δ * ρ j) ∧
    (∃ Q : Set X, IsCompact Q ∧ Q ⊆ Y ∧
      {p | p ∈ ball j (100 * Δ * ρ j) ∧ |η p| ≤ 41 / 10 * Δ ∧ t p ≤ 41 / 10 * Δ} ⊆
        interior Q ∧ Fa ⊆ interior Q) ∧
    Nonempty (Fa ≃ₜ ClosedCell 2) ∧ IsCompact Fa ∧ IsConnected Fa := by
  intro η t H₀ Y Fa
  have hΔ0 : 0 < Δ := by linarith
  have hab := abs_nonneg a
  obtain ⟨-, -, -, -, Q, hQc, hQY, hQi⟩ :=
    edp03_buffer L.toLocalChartFamilyE hΔ hμ hτ hlam hσc hb hj
  have hFa41 : Fa ⊆ {p | p ∈ ball j (100 * Δ * ρ j) ∧ |η p| ≤ 41 / 10 * Δ ∧
      t p ≤ 41 / 10 * Δ} := fun p hp => by
    refine ⟨hp.1, ?_, by linarith [hp.2.2]⟩
    have he : L.edge.coord j p = a := hp.2.1
    change |L.edge.coord j p| ≤ 41 / 10 * Δ
    rw [he]
    linarith
  have hHle : ∀ p, H₀ p ≤ 4 * Δ ↔ t p ≤ 4 * Δ := fun p => edgeRowHeight_le_iff hΔ0
  have hH4 : ∀ p, H₀ p = 4 * Δ ↔ t p = 4 * Δ := fun p => edgeRowHeight_eq_four_iff_EDP3 hΔ0
  have hYa : ∀ p, p ∈ ball j (100 * Δ * ρ j) → η p = a → t p ≤ 4 * Δ → p ∈ Y :=
    fun p hp he ht => ⟨hp, by rw [he]; linarith, by linarith⟩
  obtain ⟨hcell, hcpt, hconn⟩ := edp04_fibre_closedCell_phys_EDP3 L hΔ0 hj ha
  refine ⟨?_, ?_, fun p hp => ?_, ⟨Q, hQc, hQY, hQi, hFa41.trans hQi⟩, hcell,
    isCompact_iff_compactSpace.mpr hcpt, isConnected_iff_connectedSpace.mpr hconn⟩
  · ext p
    constructor
    · rintro ⟨hY, he, hH⟩
      exact ⟨hY.1, he, (hHle p).mp hH⟩
    · rintro ⟨hp, he, ht⟩
      exact ⟨hYa p hp he ht, he, (hHle p).mpr ht⟩
  · ext p
    constructor
    · rintro ⟨hY, he, hH⟩
      exact ⟨⟨hY.1, he, ((hH4 p).mp hH).le⟩, (hH4 p).mp hH⟩
    · rintro ⟨⟨hp, he, ht⟩, ht4⟩
      exact ⟨hYa p hp he ht, he, (hH4 p).mpr ht4⟩
  · have h41 := hFa41 hp
    exact (L.edge_enclosure_KC hΔ0 hμ hτ hlam hj (by norm_num) (by norm_num) hp.1 h41.2.1
      h41.2.2).2 (by norm_num)

/-- **EDP04's initial fibre for an admissible staged prefix** (no numerical hypothesis): for a
family with the parameters of `P : C14PreFinal`, the conclusion of `edp04_initial_fibre_EDP3`. -/
theorem edp04_initial_fibre_staged_EDP3 (P : C14PreFinal)
    (L : LocalChartPacketsC14 X g hmetric ρ hρ P.Λ β P.Δ σs K P.σc P.μ P.b s b' s' ε P.γc P.βc
      Lmax P.τ γ δ εr e T V vs ζ Λz)
    {j : X} (hj : j ∈ L.edge.centres) {a : ℝ} (ha : |a| < 4 * P.Δ) :
    let η := L.edge.coord j
    let t : X → ℝ := fun z => L.edge.smoothing z / ρ z
    let H₀ := edgeRowHeight P.Δ L.edge.smoothing ρ
    let Y : Set X := {p | p ∈ ball j (100 * P.Δ * ρ j) ∧ |η p| < 5 * P.Δ ∧ t p < 5 * P.Δ}
    let Fa : Set X := {p | p ∈ ball j (100 * P.Δ * ρ j) ∧ η p = a ∧ t p ≤ 4 * P.Δ}
    {p | p ∈ Y ∧ η p = a ∧ H₀ p ≤ 4 * P.Δ} = Fa ∧
    {p | p ∈ Y ∧ η p = a ∧ H₀ p = 4 * P.Δ} = {p | p ∈ Fa ∧ t p = 4 * P.Δ} ∧
    Fa ⊆ ball j (6 * P.Δ * ρ j) ∧
    (∃ Q : Set X, IsCompact Q ∧ Q ⊆ Y ∧
      {p | p ∈ ball j (100 * P.Δ * ρ j) ∧ |η p| ≤ 41 / 10 * P.Δ ∧ t p ≤ 41 / 10 * P.Δ} ⊆
        interior Q ∧ Fa ⊆ interior Q) ∧
    Nonempty (Fa ≃ₜ ClosedCell 2) ∧ IsCompact Fa ∧ IsConnected Fa := by
  obtain ⟨hΔ, hμ, hτ, hlam, hσc, hb, -, -, -⟩ := c14_edp03_params_EDP3 P.toC14PreSplit
  exact edp04_initial_fibre_EDP3 L hΔ hμ hτ hlam hσc hb hj ha

end DifferentialGeometry.Geometry.Collapse
