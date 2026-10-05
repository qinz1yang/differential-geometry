import DifferentialGeometry.Geometry.Metric.LargeCloudNearestBindings
import DifferentialGeometry.Geometry.Metric.LargeCloudStageMean
import DifferentialGeometry.Topology.Manifold.OpenSubtype

/-!
# CFS15's native stage output on one construction (`Cfs15StageOutput`)

Blueprint `master207B.tex`, CFS15 (B:2628–2748) with CFS12's weights, GAF03's affine locality
(B:5871) and EDP01's mean (B:6684–6716); external draft 59 §2 (disposition D59-3).

The kernel `exists_uniform_large_cloud_nearest_blueprint_budget` returns, on ONE finite selection
`I`, the zero set of the spectral section with its manifold structure, embedding, nearest-point
submersion, ambient jets and complete local graphs. `Cfs15StageOutput` stores exactly that one
construction as data (selection, charts of the zero set, nearest map, local graphs) with the
kernel's conclusions as proof fields, plus CFS12's weight-derivative budget for the SAME selection.
The plane `P` and the radius `r` are explicit parameters (the stage plane witness of D59-2 is
plugged in there).

* Domains (draft 59 §2.1): `cfs15Omega_C15` (`Ω = ⋃_{x ∈ S} B(x, r_x)`), `cfs15Tube_C15`
  (`U_b = ⋃_{i ∈ I} B(i, 20ε⁻¹r_i)`), `cfs15ZeroSet_C15` (`Z = {z ∈ U_b | η z = 0}`; NOT `p(Ω)`).
* `Cfs15StageOutput k K ε cw S T r P`: the output; `Cfs15StageOutput.ambient` (`a = ι ∘ p` on `Ω`,
  (EXT) `ambient_eq`), `eqOn_of_extension`, smoothness and bounds of `a`.
* Exits (§2.3): `section_orth_C15`, `zeroSet_subset_stageQ`, `projected_nearest_eq_native`.
* Locality, (SM), (SMV) on the same output (§2.4): `locality_C15` (three levels), `mean_C15`,
  `smv_C15`, and their forms with contributor hypotheses on the whole cloud `S`.
* `exists_cfs15StageOutput_C15`: the output from ONE kernel call at jet order `K`, with the early
  weight constant `c_w` of `exists_selection_weight_deriv_bound_GAFS2`.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter DifferentialGeometry.Analysis
open scoped BigOperators NNReal ContDiff Manifold Topology

namespace GC.MetricGeometry

universe u

section Defs

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

/-- `Ω_j = ⋃_{x ∈ S} B(x, r_x)`, the domain of CFS15's nearest map (the kernel's literal `Ω`). -/
def cfs15Omega_C15 (S : Set H) (r : H → ℝ) : TopologicalSpace.Opens H :=
  ⟨⋃ x : S, ((⟨ball (x : H) (r x), isOpen_ball⟩ : TopologicalSpace.Opens H) : Set H),
    isOpen_iUnion (fun x : S =>
      (⟨ball (x : H) (r x), isOpen_ball⟩ : TopologicalSpace.Opens H).isOpen)⟩

/-- CFS12's normalized cutoff weights of the selection `I` at `40ε⁻¹r_i`. -/
def cfs15Weight_C15 (ε : ℝ) (r : H → ℝ) {I : Set H} (hI : I.Finite) (i y : H) : ℝ :=
  ballCutoff i (40 * ε⁻¹ * r i) (2 * (40 * ε⁻¹ * r i)) y /
    (∑ a ∈ hI.toFinset, ballCutoff a (40 * ε⁻¹ * r a) (2 * (40 * ε⁻¹ * r a)) y)

/-- The spectral space `Q(y)` of `Σ_i w_i(y) P_i^⊥` near one. -/
def cfs15Spectral_C15 (ε : ℝ) (r : H → ℝ) (P : H → Submodule ℝ H) {I : Set H} (hI : I.Finite)
    (y : H) : Submodule ℝ H :=
  ⨆ μ ∈ ball (1 : ℝ) (1 / 2), Module.End.eigenspace
    (∑ i ∈ hI.toFinset, cfs15Weight_C15 ε r hI i y • (P i)ᗮ.starProjection).toLinearMap μ

/-- The spectral section `η(y) = Q(y)(y − Σ_i w_i(y) i)`. -/
def cfs15Section_C15 (ε : ℝ) (r : H → ℝ) (P : H → Submodule ℝ H) {I : Set H} (hI : I.Finite)
    (y : H) : H :=
  (cfs15Spectral_C15 ε r P hI y).starProjection
    (y - ∑ i ∈ hI.toFinset, cfs15Weight_C15 ε r hI i y • i)

/-- The tube `U_{b} = ⋃_{i ∈ I} B(i, 20ε⁻¹r_i)` (`b = ε⁻¹`). -/
def cfs15Tube_C15 (ε : ℝ) (r : H → ℝ) (I : Set H) : Set H :=
  ⋃ i ∈ I, ball i (20 * ε⁻¹ * r i)

/-- The native zero set `Z = {z ∈ U_b | η z = 0}` (the task's `W⁰`; not `p(Ω)`). -/
def cfs15ZeroSet_C15 (ε : ℝ) (r : H → ℝ) (P : H → Submodule ℝ H) {I : Set H}
    (hI : I.Finite) : Set H :=
  {z | z ∈ cfs15Tube_C15 ε r I ∧ cfs15Section_C15 ε r P hI z = 0}

omit [InnerProductSpace ℝ H] [FiniteDimensional ℝ H] in
theorem mem_cfs15Omega_C15 {S : Set H} {r : H → ℝ} {z : H} :
    z ∈ cfs15Omega_C15 S r ↔ ∃ x ∈ S, z ∈ ball x (r x) := by
  change z ∈ ⋃ x : S, ball (x : H) (r x) ↔ _
  simp only [mem_iUnion, Subtype.exists, exists_prop]

omit [InnerProductSpace ℝ H] [FiniteDimensional ℝ H] in
theorem mem_cfs15Omega_of_mem_C15 {S : Set H} {r : H → ℝ} {x z : H} (hx : x ∈ S)
    (hz : z ∈ ball x (r x)) : z ∈ cfs15Omega_C15 S r :=
  mem_cfs15Omega_C15.mpr ⟨x, hx, hz⟩

omit [InnerProductSpace ℝ H] [FiniteDimensional ℝ H] in
theorem cfs15Omega_coe_C15 (S : Set H) (r : H → ℝ) :
    (cfs15Omega_C15 S r : Set H) = ⋃ x ∈ S, ball x (r x) := by
  ext z
  change z ∈ ⋃ x : S, ball (x : H) (r x) ↔ _
  simp only [mem_iUnion, Subtype.exists, exists_prop]

omit [InnerProductSpace ℝ H] [FiniteDimensional ℝ H] in
theorem isOpen_cfs15Tube_C15 (ε : ℝ) (r : H → ℝ) (I : Set H) : IsOpen (cfs15Tube_C15 ε r I) :=
  isOpen_biUnion fun _ _ => isOpen_ball

omit [InnerProductSpace ℝ H] [FiniteDimensional ℝ H] in
theorem cfs15Weight_nonneg_C15 (ε : ℝ) (r : H → ℝ) {I : Set H} (hI : I.Finite) (i y : H) :
    0 ≤ cfs15Weight_C15 ε r hI i y :=
  normalized_ballCutoff_nonneg hI.toFinset (fun a => a) (fun a => 40 * ε⁻¹ * r a) i y

omit [InnerProductSpace ℝ H] [FiniteDimensional ℝ H] in
/-- A weight is nonzero only in `B(i, 80ε⁻¹r_i)`. -/
theorem cfs15Weight_mem_ball_C15 {ε : ℝ} (hε : 0 < ε) {r : H → ℝ} {I : Set H} (hI : I.Finite)
    {i y : H} (hri : 0 < r i) (hne : cfs15Weight_C15 ε r hI i y ≠ 0) :
    y ∈ ball i (80 * ε⁻¹ * r i) := by
  have hpos : 0 < 40 * ε⁻¹ * r i := by positivity
  have hnum : ballCutoff i (40 * ε⁻¹ * r i) (2 * (40 * ε⁻¹ * r i)) y ≠ 0 := by
    intro h0
    apply hne
    simp only [cfs15Weight_C15, h0, zero_div]
  have hb := ballCutoff_support_subset_ball hpos.le (by linarith) hnum
  have heq : 2 * (40 * ε⁻¹ * r i) = 80 * ε⁻¹ * r i := by ring
  rwa [heq] at hb

omit [InnerProductSpace ℝ H] [FiniteDimensional ℝ H] in
/-- Every point of the tube lies on a plateau `B̄(i, 40ε⁻¹r_i)`. -/
theorem cfs15Tube_plateau_C15 {ε : ℝ} (hε : 0 < ε) {r : H → ℝ} {I : Set H} (hI : I.Finite)
    (hr : ∀ i ∈ I, 0 < r i) {y : H} (hy : y ∈ cfs15Tube_C15 ε r I) :
    ∃ i ∈ hI.toFinset, dist y i ≤ 40 * ε⁻¹ * r i := by
  obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.mp hy
  refine ⟨i, hI.mem_toFinset.mpr hi, ?_⟩
  have h1 : dist y i < 20 * ε⁻¹ * r i := hyi
  have h2 : 0 < ε⁻¹ * r i := by have := hr i hi; positivity
  linarith

omit [InnerProductSpace ℝ H] [FiniteDimensional ℝ H] in
/-- The weights sum to one on the tube. -/
theorem cfs15Weight_sum_C15 {ε : ℝ} (hε : 0 < ε) {r : H → ℝ} {I : Set H} (hI : I.Finite)
    (hr : ∀ i ∈ I, 0 < r i) {y : H} (hy : y ∈ cfs15Tube_C15 ε r I) :
    ∑ i ∈ hI.toFinset, cfs15Weight_C15 ε r hI i y = 1 :=
  sum_normalized_ballCutoffs_eq_one_of_cover hI.toFinset (fun a => a) (fun a => 40 * ε⁻¹ * r a)
    (fun a ha => by have := hr a (hI.mem_toFinset.mp ha); positivity)
    (cfs15Tube_plateau_C15 hε hI hr hy)

omit [FiniteDimensional ℝ H] in
/-- The weights are smooth on the tube. -/
theorem cfs15Weight_contDiffOn_C15 {ε : ℝ} (hε : 0 < ε) {r : H → ℝ} {I : Set H} (hI : I.Finite)
    (hr : ∀ i ∈ I, 0 < r i) (i : H) :
    ContDiffOn ℝ ∞ (cfs15Weight_C15 ε r hI i) (cfs15Tube_C15 ε r I) :=
  contDiffOn_normalized_ballCutoff_of_cover hI.toFinset (fun a => a) (fun a => 40 * ε⁻¹ * r a)
    (fun a ha => by have := hr a (hI.mem_toFinset.mp ha); positivity)
    (fun _ hy => cfs15Tube_plateau_C15 hε hI hr hy) i

end Defs

section Output

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

/-- **CFS15's native stage output on one construction** (draft 59 §2.2). Parameters: model dimension
`k`, jet order `K`, accuracy `ε` (`b = ε⁻¹`), the early weight constant `c_w`, the cloud `S ⊆ T`,
the radius `r` and the plane `P` (explicit slot for the stage plane witness). Data: the selection
`I`, the charts of the zero set `Z`, the nearest map `p : Ω → Z`, the local graphs `g`. Proof
fields: the kernel's conclusions on this selection, verbatim up to the domain definitions, and
CFS12's total weight-derivative budget `Σ_i ‖Dw_i‖ ≤ c_w / r_x` for the same selection. -/
structure Cfs15StageOutput (k K : ℕ) (ε cw : ℝ) (S T : Set H) (r : H → ℝ)
    (P : H → Submodule ℝ H) where
  eps_pos : 0 < ε
  eps_le : ε ≤ 1 / 10
  radius_pos : ∀ x ∈ S, 0 < r x
  /-- The selection `I_j`. -/
  I : Set H
  hI : I.Finite
  I_subset : I ⊆ S
  disjoint : I.PairwiseDisjoint (fun i => ball i (r i))
  cover : ∀ x ∈ S, ∃ i ∈ I, r x ≤ 2 * r i ∧ dist x i < 3 * r i
  tube : (⋃ x ∈ S, ball x (8 * ε⁻¹ * r x)) ⊆ cfs15Tube_C15 ε r I
  /-- CFS12's total weight-derivative budget on the reference balls (early constant `c_w`). -/
  weight_bound : ∀ x ∈ S, ∀ y ∈ ball x (8 * ε⁻¹ * r x),
    ∑ i ∈ hI.toFinset, ‖fderiv ℝ (cfs15Weight_C15 ε r hI i) y‖ ≤ cw / r x
  /-- `Z → U_b` is proper (relative to the tube, not `Z → H`). -/
  proper : IsProperMap (fun z : cfs15ZeroSet_C15 ε r P hI => (⟨z.1, z.2.1⟩ : cfs15Tube_C15 ε r I))
  /-- The charts of the zero set (model dimension `k`). -/
  [cs : ChartedSpace (Fin k → ℝ) (cfs15ZeroSet_C15 ε r P hI)]
  isManifold : IsManifold 𝓘(ℝ, Fin k → ℝ) ∞ (cfs15ZeroSet_C15 ε r P hI)
  /-- `ι_j : Z ↪ H` is a smooth embedding. -/
  embedding : _root_.Manifold.IsSmoothEmbedding 𝓘(ℝ, Fin k → ℝ) 𝓘(ℝ, H) ∞
    (Subtype.val : cfs15ZeroSet_C15 ε r P hI → H)
  /-- The nearest-point map `p_j : Ω_j → Z_j`. -/
  p : C^∞⟮𝓘(ℝ, H), cfs15Omega_C15 S r; 𝓘(ℝ, Fin k → ℝ), cfs15ZeroSet_C15 ε r P hI⟯
  submersion : _root_.Manifold.IsSubmersion 𝓘(ℝ, H) 𝓘(ℝ, Fin k → ℝ) ∞ p
  nearest : ∀ z : cfs15Omega_C15 S r,
    IsMinOn (fun y => dist (z : H) y) (cfs15ZeroSet_C15 ε r P hI) (p z : H) ∧
      (∀ y ∈ cfs15ZeroSet_C15 ε r P hI,
        IsMinOn (fun w => dist (z : H) w) (cfs15ZeroSet_C15 ε r P hI) y → y = (p z : H))
  value_deriv : ∀ x : S, ∀ (z : H) (hz : z ∈ ball (x : H) (r x)),
    ‖(p ⟨z, mem_iUnion.mpr ⟨x, hz⟩⟩ : H) - ((x : H) + (P x).starProjection (z - x))‖ ≤
        ε * r x ∧
      (let D : H →L[ℝ] H := mfderiv 𝓘(ℝ, H) 𝓘(ℝ, H) (fun y : cfs15Omega_C15 S r => (p y : H))
          ⟨z, mem_iUnion.mpr ⟨x, hz⟩⟩;
        ‖D - (P x).starProjection‖ ≤ ε)
  /-- The ambient jets of `a = nearestAmbientExtension Ω Z p` up to order `K`. -/
  ambient_jets : ∀ x : S, ∀ z ∈ ball (x : H) (r x), ∀ j ≤ K,
    ‖iteratedFDeriv ℝ j (fun y => nearestAmbientExtension (cfs15Omega_C15 S r)
        (cfs15ZeroSet_C15 ε r P hI) p y - ((x : H) + (P x).starProjection (y - x))) z‖ ≤
      (ε / 3) * r x * ((r x)⁻¹) ^ j
  retraction : ∀ z : cfs15ZeroSet_C15 ε r P hI, ∀ hz : (z : H) ∈ cfs15Omega_C15 S r,
    p ⟨(z : H), hz⟩ = z
  normal_proj : ∀ x : S, ∀ z : cfs15ZeroSet_C15 ε r P hI, (z : H) ∈ ball (x : H) (r x) →
    ‖actualZeroSetNormalProjector k (cfs15ZeroSet_C15 ε r P hI) z - (P x)ᗮ.starProjection‖ ≤ ε
  proper_over : IsProperMap (Subtype.val :
    {z : (⋃ x ∈ S, ball x (r x) : Set H) | (z : H) ∈ cfs15ZeroSet_C15 ε r P hI} →
      (⋃ x ∈ S, ball x (r x) : Set H))
  near_cloud : cfs15ZeroSet_C15 ε r P hI ⊆ ⋃ q ∈ T, ball q (ε * r q)
  hausdorff : ∀ x ∈ S,
    hausdorffEDist (((fun y => (r x)⁻¹ • (y - x)) '' T) ∩ closedBall 0 ε⁻¹)
        (((fun y => (r x)⁻¹ • (y - x)) '' cfs15ZeroSet_C15 ε r P hI) ∩ closedBall 0 ε⁻¹) ≤
        ENNReal.ofReal (7 * ε / 16) ∧
      hausdorffEDist (((fun y => (r x)⁻¹ • (y - x)) '' T) ∩ ball 0 ε⁻¹)
        (((fun y => (r x)⁻¹ • (y - x)) '' cfs15ZeroSet_C15 ε r P hI) ∩ ball 0 ε⁻¹) ≤
        ENNReal.ofReal (7 * ε / 16)
  /-- The local graphs `g_x : B_{P_x}(0, 4ε⁻¹r_x) → P_xᗮ`. -/
  g : ∀ x : S, P x → (P x)ᗮ
  graph_smooth : ∀ x : S, ContDiffOn ℝ ∞ (g x) (ball 0 (4 * ε⁻¹ * r x))
  graph_mem : ∀ x : S, ∀ t ∈ ball (0 : P x) (4 * ε⁻¹ * r x), ‖g x t‖ ≤ r x / 4 ∧
    (x : H) + orthogonalCoordinateSum (P x) (t, g x t) ∈ cfs15ZeroSet_C15 ε r P hI
  /-- Uniqueness of the normal coordinate (the converse is `graph_mem`; both: `graph_unique_iff`). -/
  graph_unique : ∀ x : S, ∀ t ∈ ball (0 : P x) (4 * ε⁻¹ * r x),
    ∀ n ∈ closedBall (0 : (P x)ᗮ) (r x),
      cfs15Section_C15 ε r P hI ((x : H) + orthogonalCoordinateSum (P x) (t, n)) = 0 →
        n = g x t
  /-- The two-sided set equality: the WHOLE zero set near `x` is the graph. -/
  graph_eq : ∀ x : S, cfs15ZeroSet_C15 ε r P hI ∩ ball (x : H) (3 * ε⁻¹ * r x) =
    {z : H | ∃ t ∈ ball (0 : P x) (4 * ε⁻¹ * r x),
      z = (x : H) + orthogonalCoordinateSum (P x) (t, g x t)} ∩ ball (x : H) (3 * ε⁻¹ * r x)
  graph_jets : ∀ x : S, ∀ t ∈ ball (0 : P x) (4 * ε⁻¹ * r x), ∀ j ≤ K + 1,
    ‖iteratedFDeriv ℝ j (g x) t‖ ≤ (ε / 3) * r x * ((r x)⁻¹) ^ j

namespace Cfs15StageOutput

variable {k K : ℕ} {ε cw : ℝ} {S T : Set H} {r : H → ℝ} {P : H → Submodule ℝ H}

/-- The native zero set `Z_j` of the output. -/
abbrev Z (O : Cfs15StageOutput k K ε cw S T r P) : Set H := cfs15ZeroSet_C15 ε r P O.hI

/-- The ambient nearest map `a_j = nearestAmbientExtension Ω_j Z_j p_j`. -/
def ambient (O : Cfs15StageOutput k K ε cw S T r P) : H → H :=
  nearestAmbientExtension (cfs15Omega_C15 S r) (cfs15ZeroSet_C15 ε r P O.hI) O.p

/-- **(EXT)** `a_j = ι_j ∘ p_j` on `Ω_j`. -/
theorem ambient_eq (O : Cfs15StageOutput k K ε cw S T r P) (z : H)
    (hz : z ∈ cfs15Omega_C15 S r) : O.ambient z = O.p ⟨z, hz⟩ :=
  dite_eq_left hz

/-- Any ambient extension of `p_j` agrees with `a_j` on the open set `Ω_j`. -/
theorem eqOn_of_extension (O : Cfs15StageOutput k K ε cw S T r P) (a : H → H)
    (ha : ∀ y (hy : y ∈ cfs15Omega_C15 S r), a y = O.p ⟨y, hy⟩) :
    EqOn a O.ambient (cfs15Omega_C15 S r : Set H) :=
  fun y hy => (ha y hy).trans (O.ambient_eq y hy).symm

theorem ambient_mem (O : Cfs15StageOutput k K ε cw S T r P) {z : H}
    (hz : z ∈ cfs15Omega_C15 S r) : O.ambient z ∈ O.Z := by
  rw [O.ambient_eq z hz]
  exact (O.p ⟨z, hz⟩).2

theorem ambient_contDiffAt (O : Cfs15StageOutput k K ε cw S T r P) {z : H}
    (hz : z ∈ cfs15Omega_C15 S r) : ContDiffAt ℝ ∞ O.ambient z := by
  let _ := O.cs
  have heq : (fun y : cfs15Omega_C15 S r => O.ambient y) =
      (fun y : cfs15Omega_C15 S r => (O.p y : H)) := funext fun y => O.ambient_eq y y.2
  have hsm : ContMDiff 𝓘(ℝ, H) 𝓘(ℝ, H) ∞ (fun y : cfs15Omega_C15 S r => (O.p y : H)) :=
    O.embedding.contMDiff.comp O.p.contMDiff
  have h : ContMDiffAt 𝓘(ℝ, H) 𝓘(ℝ, H) ∞ (fun y : cfs15Omega_C15 S r => O.ambient y)
      (⟨z, hz⟩ : cfs15Omega_C15 S r) := by
    rw [heq]
    exact hsm _
  exact contMDiffAt_iff_contDiffAt.mp (contMDiffAt_subtype_iff.mp h)

/-- The derivative of `a_j` on `Ω_j` is the manifold derivative of `p_j`. -/
theorem ambient_fderiv (O : Cfs15StageOutput k K ε cw S T r P) {z : H}
    (hz : z ∈ cfs15Omega_C15 S r) :
    fderiv ℝ O.ambient z =
      mfderiv 𝓘(ℝ, H) 𝓘(ℝ, H) (fun y : cfs15Omega_C15 S r => (O.p y : H)) ⟨z, hz⟩ := by
  have heq : (fun y : cfs15Omega_C15 S r => O.ambient y) =
      (fun y : cfs15Omega_C15 S r => (O.p y : H)) := funext fun y => O.ambient_eq y y.2
  change fderiv ℝ O.ambient ((⟨z, hz⟩ : cfs15Omega_C15 S r) : H) = _
  rw [← heq, DifferentialGeometry.mfderiv_restrict_open, mfderiv_eq_fderiv]
  rfl

theorem ambient_contDiffOn (O : Cfs15StageOutput k K ε cw S T r P) :
    ContDiffOn ℝ ∞ O.ambient (⋃ x ∈ S, ball x (r x)) := by
  intro y hy
  obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.mp hy
  exact (O.ambient_contDiffAt (mem_cfs15Omega_of_mem_C15 hx hyx)).contDiffWithinAt

/-- CFS14 (3)'s value and derivative bounds for `a_j` on every `B(x, r_x)`. -/
theorem ambient_value_deriv (O : Cfs15StageOutput k K ε cw S T r P) {x : H} (hx : x ∈ S)
    {z : H} (hz : z ∈ ball x (r x)) :
    ‖O.ambient z - (x + (P x).starProjection (z - x))‖ ≤ ε * r x ∧
      DifferentiableAt ℝ O.ambient z ∧ ‖fderiv ℝ O.ambient z - (P x).starProjection‖ ≤ ε := by
  have hzΩ := mem_cfs15Omega_of_mem_C15 hx hz
  have hv := O.value_deriv ⟨x, hx⟩ z hz
  refine ⟨?_, (O.ambient_contDiffAt hzΩ).differentiableAt (by simp), ?_⟩
  · rw [O.ambient_eq z hzΩ]
    exact hv.1
  · rw [O.ambient_fderiv hzΩ]
    exact hv.2

theorem section_ambient_eq_zero (O : Cfs15StageOutput k K ε cw S T r P) {z : H}
    (hz : z ∈ cfs15Omega_C15 S r) : cfs15Section_C15 ε r P O.hI (O.ambient z) = 0 :=
  (O.ambient_mem hz).2

theorem radius_pos_I (O : Cfs15StageOutput k K ε cw S T r P) : ∀ i ∈ O.I, 0 < r i :=
  fun i hi => O.radius_pos i (O.I_subset hi)

theorem ball_subset_tube (O : Cfs15StageOutput k K ε cw S T r P) {x : H} (hx : x ∈ S) :
    ball x (8 * ε⁻¹ * r x) ⊆ cfs15Tube_C15 ε r O.I :=
  fun _ hy => O.tube (mem_iUnion₂.mpr ⟨x, hx, hy⟩)

/-- `a_j` maps `B(x, r_x)` into the reference ball `B(x, 8ε⁻¹r_x)`. -/
theorem ambient_mem_ball (O : Cfs15StageOutput k K ε cw S T r P) {x : H} (hx : x ∈ S)
    {z : H} (hz : z ∈ ball x (r x)) : O.ambient z ∈ ball x (8 * ε⁻¹ * r x) := by
  have hrx := O.radius_pos x hx
  have hinv : 1 ≤ ε⁻¹ := one_le_inv₀ O.eps_pos |>.mpr (O.eps_le.trans (by norm_num))
  have hzx : ‖z - x‖ < r x := by rw [← dist_eq_norm]; exact hz
  have hproj : ‖(P x).starProjection (z - x)‖ ≤ ‖z - x‖ :=
    Submodule.norm_starProjection_apply_le (P x) (z - x)
  have htri : ‖O.ambient z - x‖ ≤ ‖O.ambient z - (x + (P x).starProjection (z - x))‖ +
      ‖(P x).starProjection (z - x)‖ := by
    have := norm_add_le (O.ambient z - (x + (P x).starProjection (z - x)))
      ((P x).starProjection (z - x))
    rwa [show O.ambient z - (x + (P x).starProjection (z - x)) +
      (P x).starProjection (z - x) = O.ambient z - x by abel] at this
  have hv := (O.ambient_value_deriv hx hz).1
  have hε1 : ε ≤ 1 := O.eps_le.trans (by norm_num)
  rw [mem_ball, dist_eq_norm]
  have h8 : 2 * r x ≤ 8 * ε⁻¹ * r x := by nlinarith
  nlinarith

/-- The local graph equation (kernel form, both directions): for `t ∈ B_{P_x}(0, 4ε⁻¹r_x)` and
`‖n‖ ≤ r_x`, `η(x + (t, n)) = 0 ↔ n = g_x(t)`. -/
theorem graph_unique_iff {O : Cfs15StageOutput k K ε cw S T r P} {x : S} {t : P x}
    (ht : t ∈ ball (0 : P x) (4 * ε⁻¹ * r x)) {n : (P x)ᗮ}
    (hn : n ∈ closedBall (0 : (P x)ᗮ) (r x)) :
    cfs15Section_C15 ε r P O.hI ((x : H) + orthogonalCoordinateSum (P x) (t, n)) = 0 ↔
      n = O.g x t := by
  refine ⟨O.graph_unique x t ht n hn, fun h => ?_⟩
  rw [h]
  exact ((O.graph_mem x t ht).2).2

/-! ### Exits of §2.3: the zero set lies in `Q_j` -/

/-- With every cloud centre in `Q` and every plane inside `Q`: `π_{Q^⊥} η(z) = π_{Q^⊥} z` on the
tube. -/
theorem section_orth_C15 (O : Cfs15StageOutput k K ε cw S T r P) (Q : Submodule ℝ H)
    (hSQ : ∀ x ∈ S, x ∈ Q) (hPQ : ∀ x ∈ S, P x ≤ Q) :
    ∀ z ∈ cfs15Tube_C15 ε r O.I,
      Qᗮ.starProjection (cfs15Section_C15 ε r P O.hI z) = Qᗮ.starProjection z := by
  intro z hz
  have h := Submodule.affine_marker_weighted_normal_spectral_section O.hI.toFinset
    (cfs15Tube_C15 ε r O.I) (cfs15Weight_C15 ε r O.hI)
    (fun y hy => cfs15Weight_sum_C15 O.eps_pos O.hI O.radius_pos_I hy) P (fun i => i) Qᗮ 0
    (fun i hi _ => by
      rw [Submodule.starProjection_apply_eq_zero_iff, Submodule.orthogonal_orthogonal]
      exact hSQ i (O.I_subset (O.hI.mem_toFinset.mp hi)))
    (fun i hi _ => by
      rw [Submodule.orthogonal_orthogonal]
      exact hPQ i (O.I_subset (O.hI.mem_toFinset.mp hi))) z hz
  rw [sub_zero] at h
  exact h

/-- **`Z_j ⊆ Q_j`** (draft 59 §2.3): every selected centre is in `Q` and every plane lies in `Q`. -/
theorem zeroSet_subset_stageQ (O : Cfs15StageOutput k K ε cw S T r P) (Q : Submodule ℝ H)
    (hSQ : ∀ x ∈ S, x ∈ Q) (hPQ : ∀ x ∈ S, P x ≤ Q) : O.Z ⊆ Q := by
  intro z hz
  have h := O.section_orth_C15 Q hSQ hPQ z hz.1
  rw [hz.2, map_zero] at h
  have h0 : z ∈ Qᗮᗮ := (Submodule.starProjection_apply_eq_zero_iff Qᗮ).mp h.symm
  rwa [Submodule.orthogonal_orthogonal] at h0

/-- **(PNATIVE)** `P_j(z) = π_{Q_j} a_j(z) = a_j(z) = ι_j p_j(z)` on `Ω_j`. -/
theorem projected_nearest_eq_native (O : Cfs15StageOutput k K ε cw S T r P) (Q : Submodule ℝ H)
    (hSQ : ∀ x ∈ S, x ∈ Q) (hPQ : ∀ x ∈ S, P x ≤ Q) (z : H) (hz : z ∈ cfs15Omega_C15 S r) :
    Q.starProjection (O.ambient z) = O.p ⟨z, hz⟩ := by
  rw [Submodule.starProjection_eq_self_iff.mpr (O.zeroSet_subset_stageQ Q hSQ hPQ
    (O.ambient_mem hz)), O.ambient_eq z hz]

/-! ### Locality, (SM), (SMV) on the same output (§2.4) -/

/-- **GAF03's affine locality, three levels.** If every selected centre `i` of the closed-support
contributor list at `x` (`B̄(i, 80ε⁻¹r_i) ∩ B(x, 8ε⁻¹r_x) ≠ ∅`) has `π_K i = c` and `P i ⊥ K`:
`π_K η(z) = π_K z − c` on `B(x, 8ε⁻¹r_x)`, `π_K w = c` on `Z ∩ B(x, 8ε⁻¹r_x)`, and
`π_K a(z) = c` on `B(x, r_x)`. -/
theorem locality_C15 (O : Cfs15StageOutput k K ε cw S T r P) {x : H} (hx : x ∈ S)
    (Kk : Submodule ℝ H) (c : H)
    (hcontrib : ∀ i ∈ O.I, (closedBall i (80 * ε⁻¹ * r i) ∩ ball x (8 * ε⁻¹ * r x)).Nonempty →
      Kk.starProjection i = c ∧ P i ≤ Kkᗮ) :
    (∀ z ∈ ball x (8 * ε⁻¹ * r x),
      Kk.starProjection (cfs15Section_C15 ε r P O.hI z) = Kk.starProjection z - c) ∧
    (∀ w ∈ O.Z ∩ ball x (8 * ε⁻¹ * r x), Kk.starProjection w = c) ∧
    (∀ z ∈ ball x (r x), Kk.starProjection (O.ambient z) = c) := by
  have hloc := large_cloud_affine_marker_locality O.I O.hI r P O.eps_pos
    (O.eps_le.trans (by norm_num)) O.radius_pos_I x (O.ball_subset_tube hx) Kk c hcontrib
  refine ⟨hloc.1, fun w hw => hloc.2.1 w hw.2 hw.1.2, fun z hz => ?_⟩
  exact hloc.2.2 z hz (O.ambient z) (O.section_ambient_eq_zero (mem_cfs15Omega_of_mem_C15 hx hz))
    (O.ambient_value_deriv hx hz).1

/-- **(SM)** on the zero set: if every plane of the contributor list at `x` lies in `ker ℓ`, then
`ℓ(w) = Σ_i w_i(w) ℓ(i)` on `Z ∩ B(x, 8ε⁻¹r_x)`. -/
theorem mean_C15 (O : Cfs15StageOutput k K ε cw S T r P) {x : H} (ℓ : H →L[ℝ] ℝ)
    (hplane : ∀ i ∈ O.I, (closedBall i (80 * ε⁻¹ * r i) ∩ ball x (8 * ε⁻¹ * r x)).Nonempty →
      P i ≤ LinearMap.ker (ℓ : H →ₗ[ℝ] ℝ)) :
    ∀ w ∈ O.Z ∩ ball x (8 * ε⁻¹ * r x),
      ℓ w = ∑ i ∈ O.hI.toFinset, cfs15Weight_C15 ε r O.hI i w * ℓ i := by
  intro w hw
  exact functional_eq_weightedMean_of_section_eq_zero_GAFS2 O.hI.toFinset
    (fun i => cfs15Weight_C15 ε r O.hI i w)
    (cfs15Weight_sum_C15 O.eps_pos O.hI O.radius_pos_I hw.1.1) P (fun i => i) ℓ
    (fun i hi hne => hplane i (O.hI.mem_toFinset.mp hi)
      ⟨w, ball_subset_closedBall (cfs15Weight_mem_ball_C15 O.eps_pos O.hI
        (O.radius_pos_I i (O.hI.mem_toFinset.mp hi)) hne), hw.2⟩) w hw.1.2

/-- **(SMV)** for `a_j`: if every plane of the contributor list at `x` lies in `ker ℓ` and
`|ℓ(i) − R₀| ≤ β` on the list, then on `B(x, r_x)`: `|ℓ(a z) − R₀| ≤ β` and
`‖ℓ ∘ Da(z)‖ ≤ 2c_wβ / r_x` (`c_w` the early total weight budget). -/
theorem smv_C15 (O : Cfs15StageOutput k K ε cw S T r P) {x : H} (hx : x ∈ S) (ℓ : H →L[ℝ] ℝ)
    (hplane : ∀ i ∈ O.I, (closedBall i (80 * ε⁻¹ * r i) ∩ ball x (8 * ε⁻¹ * r x)).Nonempty →
      P i ≤ LinearMap.ker (ℓ : H →ₗ[ℝ] ℝ)) (R₀ β : ℝ)
    (hβ : ∀ i ∈ O.I, (closedBall i (80 * ε⁻¹ * r i) ∩ ball x (8 * ε⁻¹ * r x)).Nonempty →
      |ℓ i - R₀| ≤ β) :
    ∀ z ∈ ball x (r x),
      |ℓ (O.ambient z) - R₀| ≤ β ∧ ‖ℓ.comp (fderiv ℝ O.ambient z)‖ ≤ 2 * cw * β / r x := by
  intro z hz
  have hrx := O.radius_pos x hx
  have hvd := O.ambient_value_deriv hx hz
  have hDa : ‖fderiv ℝ O.ambient z‖ ≤ 2 := by
    have h1 := norm_add_le (fderiv ℝ O.ambient z - (P x).starProjection) (P x).starProjection
    rw [sub_add_cancel] at h1
    have h3 := (P x).starProjection_norm_le
    have h4 : ε ≤ 1 := O.eps_le.trans (by norm_num)
    linarith [hvd.2.2]
  have hIS : ((O.hI.toFinset : Finset H) : Set H) ⊆ O.I := fun i hi => O.hI.mem_toFinset.mp hi
  refine stage_mean_functional_GAFS2 O.I r P O.hI.toFinset hIS (cfs15Weight_C15 ε r O.hI)
    hrx (cfs15Weight_nonneg_C15 ε r O.hI)
    (fun i hi y hne => cfs15Weight_mem_ball_C15 O.eps_pos O.hI
      (O.radius_pos_I i (O.hI.mem_toFinset.mp hi)) hne)
    (fun y hy => cfs15Weight_sum_C15 O.eps_pos O.hI O.radius_pos_I (O.ball_subset_tube hx hy))
    (fun i _ y hy => ((cfs15Weight_contDiffOn_C15 O.eps_pos O.hI O.radius_pos_I i).contDiffAt
      ((isOpen_cfs15Tube_C15 ε r O.I).mem_nhds (O.ball_subset_tube hx hy))).differentiableAt
        (by simp))
    (O.weight_bound x hx) O.ambient
    (fun z' hz' => ⟨O.ambient_mem_ball hx hz',
      O.section_ambient_eq_zero (mem_cfs15Omega_of_mem_C15 hx hz')⟩)
    hz hvd.2.1 hDa ℓ hplane R₀ β hβ

/-- `locality_C15` with the contributor hypothesis on the whole cloud `S` (GAF03's form). -/
theorem locality_of_cloud_C15 (O : Cfs15StageOutput k K ε cw S T r P) {x : H} (hx : x ∈ S)
    (Kk : Submodule ℝ H) (c : H)
    (hcontrib : ∀ i ∈ S, (closedBall i (80 * ε⁻¹ * r i) ∩ ball x (8 * ε⁻¹ * r x)).Nonempty →
      Kk.starProjection i = c ∧ P i ≤ Kkᗮ) :
    (∀ z ∈ ball x (8 * ε⁻¹ * r x),
      Kk.starProjection (cfs15Section_C15 ε r P O.hI z) = Kk.starProjection z - c) ∧
    (∀ w ∈ O.Z ∩ ball x (8 * ε⁻¹ * r x), Kk.starProjection w = c) ∧
    (∀ z ∈ ball x (r x), Kk.starProjection (O.ambient z) = c) :=
  O.locality_C15 hx Kk c fun i hi => hcontrib i (O.I_subset hi)

/-- `mean_C15` with the plane hypothesis on the whole cloud `S`. -/
theorem mean_of_cloud_C15 (O : Cfs15StageOutput k K ε cw S T r P) {x : H}
    (ℓ : H →L[ℝ] ℝ)
    (hplane : ∀ i ∈ S, (closedBall i (80 * ε⁻¹ * r i) ∩ ball x (8 * ε⁻¹ * r x)).Nonempty →
      P i ≤ LinearMap.ker (ℓ : H →ₗ[ℝ] ℝ)) :
    ∀ w ∈ O.Z ∩ ball x (8 * ε⁻¹ * r x),
      ℓ w = ∑ i ∈ O.hI.toFinset, cfs15Weight_C15 ε r O.hI i w * ℓ i :=
  O.mean_C15 ℓ fun i hi => hplane i (O.I_subset hi)

/-- `smv_C15` with the contributor hypotheses on the whole cloud `S` (EDP01's form). -/
theorem smv_of_cloud_C15 (O : Cfs15StageOutput k K ε cw S T r P) {x : H} (hx : x ∈ S)
    (ℓ : H →L[ℝ] ℝ)
    (hplane : ∀ i ∈ S, (closedBall i (80 * ε⁻¹ * r i) ∩ ball x (8 * ε⁻¹ * r x)).Nonempty →
      P i ≤ LinearMap.ker (ℓ : H →ₗ[ℝ] ℝ)) (R₀ β : ℝ)
    (hβ : ∀ i ∈ S, (closedBall i (80 * ε⁻¹ * r i) ∩ ball x (8 * ε⁻¹ * r x)).Nonempty →
      |ℓ i - R₀| ≤ β) :
    ∀ z ∈ ball x (r x),
      |ℓ (O.ambient z) - R₀| ≤ β ∧ ‖ℓ.comp (fderiv ℝ O.ambient z)‖ ≤ 2 * cw * β / r x :=
  O.smv_C15 hx ℓ (fun i hi => hplane i (O.I_subset hi)) R₀ β (fun i hi => hβ i (O.I_subset hi))

end Cfs15StageOutput

end Output

/-! ### The output from one kernel call -/

/-- **The stage output from ONE kernel call** (jet order `K`). For `1 ≤ B`, `0 < ε ≤ 1/10` there
are an early weight constant `c_w ≥ 0` (CFS12's total budget, depending on `k, ε, B`) and a
threshold `δ₀ > 0` such that every cloud with CFS15's hypotheses at quality `δ ≤ δ₀` has a
`Cfs15StageOutput k K ε c_w S T r P` (all its fields from the same selection of the kernel at jet
order `K`, the weight budget for that selection). -/
theorem exists_cfs15StageOutput_C15 (k K : ℕ) (B ε : ℝ) (hB : 1 ≤ B) (hε : 0 < ε)
    (hεsmall : ε ≤ 1 / 10) :
    ∃ cw : ℝ, 0 ≤ cw ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
        (S T : Set H), S ⊆ T → TotallyBounded S →
        ∀ (r : H → ℝ) (P : H → Submodule ℝ H),
        (∀ x ∈ S, Module.finrank ℝ (P x) = k) →
        ∀ rmin R δ : ℝ, 0 < rmin → (∀ x ∈ S, rmin ≤ r x) → (∀ x ∈ S, r x ≤ R) →
        0 < δ → δ ≤ δ₀ →
        (∀ x ∈ T, ∀ y ∈ T, dist y x ≤ 128 * ε⁻¹ * max (r y) (r x) →
          r x / B ≤ r y ∧ r y ≤ B * r x) →
        (∀ x ∈ S, hausdorffEDist (T ∩ ball x (r x / δ))
          ((AffineSubspace.mk' x (P x) : Set H) ∩ ball x (r x / δ)) ≤
            ENNReal.ofReal (δ * r x)) →
        Nonempty (Cfs15StageOutput k K ε cw S T r P) := by
  obtain ⟨F, -, C, -, δK, hδK, -, hker⟩ :=
    exists_uniform_large_cloud_nearest_blueprint_budget.{u} k K B ε hB hε hεsmall
  have hinv : 1 ≤ ε⁻¹ := one_le_inv₀ hε |>.mpr (by linarith)
  obtain ⟨cw, hcw, hwb⟩ := exists_selection_weight_deriv_bound_GAFS2.{u} k ε⁻¹ B hinv hB
  have hApos : 0 < (80 * B + 31) * ε⁻¹ + 2 := by positivity
  refine ⟨cw, hcw, min δK (1 / (2 * ((80 * B + 31) * ε⁻¹ + 2))),
    lt_min hδK (by positivity), ?_⟩
  intro H _ _ _ S T hST htb r P hdim rmin R δ hrmin hlo hhi hδ hδ₀ hmcb hcloud
  have hδA : δ * ((80 * B + 31) * ε⁻¹ + 2) < 1 := by
    have hs : δ ≤ 1 / (2 * ((80 * B + 31) * ε⁻¹ + 2)) := hδ₀.trans (min_le_right _ _)
    have hm : δ * (2 * ((80 * B + 31) * ε⁻¹ + 2)) ≤ 1 := (le_div_iff₀ (by positivity)).mp hs
    nlinarith
  have hr : ∀ x ∈ S, 0 < r x := fun x hx => hrmin.trans_le (hlo x hx)
  obtain ⟨I, hI, hIS, hdisj, hcov, htube, hrest⟩ :=
    hker H S T hST htb r P hdim rmin R δ hrmin hlo hhi hδ (hδ₀.trans (min_le_left _ _)) hmcb hcloud
  have hwb' := hwb H S T hST r P hdim hr δ hδ hδA
    (fun x hx y hy hd => hmcb x (hST hx) y (hST hy) hd) hcloud I hI hIS hdisj htube
  obtain ⟨⟨hprop, cs, hcs⟩, hpo, hnc, hhaus, g, hg⟩ := hrest
  obtain ⟨hman, hemb, p, hsub, hnearest, hval, -, hjets, hretr, hnorm⟩ := hcs
  exact ⟨{
    eps_pos := hε
    eps_le := hεsmall
    radius_pos := hr
    I := I
    hI := hI
    I_subset := hIS
    disjoint := hdisj
    cover := hcov
    tube := htube
    weight_bound := hwb'
    proper := hprop
    cs := cs
    isManifold := hman
    embedding := hemb
    p := p
    submersion := hsub
    nearest := hnearest
    value_deriv := fun x z hz => hval x ⟨z, hz⟩
    ambient_jets := hjets
    retraction := hretr
    normal_proj := hnorm
    proper_over := hpo
    near_cloud := hnc
    hausdorff := hhaus
    g := g
    graph_smooth := fun x => (hg x).1
    graph_mem := fun x => (hg x).2.1
    graph_unique := fun x t ht n hn => ((hg x).2.2.1 t ht n hn).mp
    graph_eq := fun x => (hg x).2.2.2.2.1
    graph_jets := fun x => (hg x).2.2.2.2.2 }⟩

end GC.MetricGeometry
