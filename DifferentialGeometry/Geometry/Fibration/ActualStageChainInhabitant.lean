import DifferentialGeometry.Geometry.Fibration.ActualStageChainRow
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsDihedralInhabitant
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsInhabitants

/-!
# Inhabitants of the GAF02 chain object `Gaf02Chain` (lane C14-CHAIN-INST)

Lanes build on `Gaf02Chain` (`ActualStageChain.lean`), so it needs compiled inhabitants.

* **Finding.** `isEmpty_gaf02Chain_of_isEmpty_CHI`, `isEmpty_gaf02Chain_pempty_CHI`: over an empty
  manifold the chain type is empty, because the selections `sel : Fin 3 → BlockSpace … → X` are
  total and `BlockSpace …` contains `0`. So the pempty family fixtures cannot host a chain. This is
  harmless for every nonempty `X`.
* **Fixture.** `dihedralTinyStdBase_CHI`: the nonempty closed family of
  `LocalChartPacketsDihedralInhabitant.lean` on `RP³ # RP³`, at values that satisfy
  `Gaf02Chain.std`. Its stage families, stage clouds and enlarged clouds are empty
  (`dihedralTinyStd_stageCentres_CHI`, `dihedralTinyStd_cloud_CHI`,
  `dihedralTinyStd_cloudEnlarged_CHI`; generic `gafCloudEnlarged_eq_empty_CHI`).
* **G1.** `exists_gaf02Chain_inactive_CHI`: at GAF01's numbers (`gaf02_chain_choice_GAF8`), a chain
  with three `inactive` slots (constant selections, planes `⊥`, tests vacuous), with `E = 𝓔⁰` and
  scale exit `ρ`.
* **G3.** `exists_cfs15StageOutput_dihedralTiny_CHI`: CFS15's kernel on the empty stage clouds,
  for every selection, every plane field (for instance the explicit `⊥`) and every `Σ`.
  `exists_gaf02Chain_active_CHI`: a chain with three `active` slots. Again `E = 𝓔⁰`, since the
  actual cutoffs vanish on empty families. `cutoff_bindings` is a theorem of the chain, not a field,
  so it puts no condition on an active slot. The flat-cloud inhabitant of
  `Cfs15StageOutputApplications.lean` (cloud `L ∩ B̄(0, 1)`) cannot fill a slot, because a slot's
  cloud is the family's own stage cloud.
* Consumer `gaf02_core_dihedralTiny_CHI`: the chain's GAF02 CORE theorems on the G1 chain.

State chain statements about this fixture on `dihedralTinyStdBase_CHI` (the base projection). On
the `LocalChartPacketsC14` term, the elaborator times out unifying the two `toLocalChartFamily`
paths.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] dihedralTinyMetricSpace_CHI

section Generic

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}

/-- An empty stage family has an empty enlarged stage cloud. -/
theorem gafCloudEnlarged_eq_empty_CHI (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s
    b' s' ε γc βc Lmax τ γ δ εr e T V)
    {st : Fin 3} (h : gafStageCentres P st = ∅) :
    gafCloudEnlarged P.toLocalChartFamily P.zero st = ∅ := by
  have hcore : gafStageEnlargement P.toLocalChartFamily P.zero st = ∅ := by
    fin_cases st
    · refine Set.eq_empty_iff_forall_notMem.mpr fun p hp => ?_
      obtain ⟨j, -⟩ := hp
      have hj := (Set.Finite.mem_toFinset _).mp j.2
      simp only [gafStageCentres] at h
      simp_all
    · refine Set.eq_empty_iff_forall_notMem.mpr fun p hp => ?_
      obtain ⟨j, -⟩ := hp
      have hj := (Set.Finite.mem_toFinset _).mp j.2
      simp only [gafStageCentres] at h
      simp_all
    · refine Set.eq_empty_iff_forall_notMem.mpr fun p hp => ?_
      obtain ⟨j, -⟩ := hp
      have hj := (Set.Finite.mem_toFinset _).mp j.2
      simp only [gafStageCentres] at h
      simp_all
  simp [gafCloudEnlarged, hcore]

/-- **The chain object has no inhabitant over an empty manifold**: its selections
`sel : Fin 3 → BlockSpace … → X` are total functions and `BlockSpace …` contains `0`. -/
theorem isEmpty_gaf02Chain_of_isEmpty_CHI [IsEmpty X]
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (Kj : ℕ) (Ξ Γ S eg c cw : Fin 3 → ℝ) : IsEmpty (Gaf02Chain P Kj Ξ Γ S eg c cw) :=
  ⟨fun C => IsEmpty.false (C.sel 0 0)⟩

end Generic

section PEmpty

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- The metric on `PEmpty` (the same term as the instance used by `metricPEmpty_FAM`). -/
local instance metricSpacePEmpty_CHI : MetricSpace PEmpty.{1} :=
  (MetricSpace.induced (PEmpty.elim : PEmpty.{1} → ℝ) (fun x => x.elim)
    inferInstance).replaceTopology (by ext s; simp only [Set.eq_empty_of_isEmpty s, isOpen_empty])

/-- The empty three-manifold (the same term as the instance used by `metricPEmpty_FAM`). -/
local instance chartedSpacePEmpty_CHI : ChartedSpace E3 PEmpty.{1} :=
  ChartedSpace.empty E3 PEmpty.{1}

/-- **Finding (lane C14-CHAIN-INST): `Gaf02Chain` is not inhabited on the pempty fixtures.** For
every family over the empty manifold (for instance the projections of
`nonempty_localChartPacketsC14Z_pempty_FAMZ`), the chain type is empty: its selections are total
functions into `X = PEmpty`. Harmless for every nonempty `X` (see `dihedralTinyPackets_CHI`). -/
theorem isEmpty_gaf02Chain_pempty_CHI {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}
    (P : LocalChartPackets PEmpty.{1} metricPEmpty_FAM (fun a => a.elim) (fun a => a.elim)
      (fun a => a.elim) Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (Kj : ℕ) (Ξ Γ S eg c cw : Fin 3 → ℝ) : IsEmpty (Gaf02Chain P Kj Ξ Γ S eg c cw) :=
  isEmpty_gaf02Chain_of_isEmpty_CHI P Kj Ξ Γ S eg c cw

end PEmpty

/-! ### The dihedral fixture at the packet values of `Gaf02Chain.std` -/

/-- The dihedral family at the values `Λ = 0`, `β ≡ 0`, `Δ = 1`, `L_max = 4(10 + 4·10⁶ + 1/3)`,
`δ = 1/2`, `e = 1/100`, `T = V = 1.6·10⁹`, all other parameters `0` (they satisfy
`Gaf02Chain.std`). -/
abbrev dihedralTinyStdPackets_CHI :
    LocalChartPacketsC14 dihedralZeroSource dihedralTinyMetric_CHI dihedralTiny_hmetric_CHI
      dihedralTinyRho_CHI dihedralTinyRho_pos_CHI 0 (fun _ => 0) 1 0 0 0 0 0 0 0 0 0 0 0
      (4 * (10 + 2 * (2000000 * 1) + 1 / 3)) 0 0 (1 / 2) 0 (1 / 100) 1600000000 1600000000 0 0 0 :=
  dihedralTinyPackets_CHI (fun _ _ _ => by norm_num) (by norm_num) (by norm_num) (by norm_num)
    le_rfl (by norm_num) (by norm_num) (by norm_num) le_rfl

/-- The base projection of the fixture (the packet type of `Gaf02Chain`). -/
abbrev dihedralTinyStdBase_CHI :
    LocalChartPackets dihedralZeroSource dihedralTinyMetric_CHI dihedralTiny_hmetric_CHI
      dihedralTinyRho_CHI dihedralTinyRho_pos_CHI 0 (fun _ => 0) 1 0 0 0 0 0 0 0 0 0 0 0
      (4 * (10 + 2 * (2000000 * 1) + 1 / 3)) 0 0 (1 / 2) 0 (1 / 100) 1600000000 1600000000 :=
  dihedralTinyStdPackets_CHI.toLocalChartPackets

/-- The three stage families of the fixture are empty. -/
theorem dihedralTinyStd_stageCentres_CHI (st : Fin 3) :
    gafStageCentres dihedralTinyStdBase_CHI st = ∅ := by
  fin_cases st <;> rfl

/-- The stage clouds of the fixture are empty. -/
theorem dihedralTinyStd_cloud_CHI (st : Fin 3) :
    gafCloud dihedralTinyStdBase_CHI.toLocalChartFamily dihedralTinyStdBase_CHI.zero st = ∅ :=
  gafCloud_eq_empty_GAF8 dihedralTinyStdBase_CHI (dihedralTinyStd_stageCentres_CHI st)

/-- The enlarged stage clouds of the fixture are empty. -/
theorem dihedralTinyStd_cloudEnlarged_CHI (st : Fin 3) :
    gafCloudEnlarged dihedralTinyStdBase_CHI.toLocalChartFamily dihedralTinyStdBase_CHI.zero st =
      ∅ :=
  gafCloudEnlarged_eq_empty_CHI dihedralTinyStdBase_CHI (dihedralTinyStd_stageCentres_CHI st)

/-- The packet hypotheses `Gaf02Chain.std` hold at the fixture's values. -/
theorem dihedralTinyStd_std_CHI :
    (0 : ℝ) ≤ 0 ∧ (1 : ℝ) ≤ 1 ∧ (0 : ℝ) ≤ 1 / 100 ∧ (0 : ℝ) ≤ 1 / 100 ∧
      1000000 * (1 : ℝ) * 0 < 1 / 100000 ∧
      4 * (10 + 2 * (2000000 * (1 : ℝ)) + 1 / 3) ≤ 4 * (10 + 2 * (2000000 * 1) + 1 / 3) ∧
      (1 / 100 : ℝ) < 1 / 40 ∧ 1600 * (1000000 * (1 : ℝ)) ≤ 1600000000 ∧
      (0 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ 1 / 100 ∧ (0 : ℝ) ∈ Icc (0 : ℝ) 1 ∧ (0 : ℝ) ∈ Icc (0 : ℝ) 1 ∧
      (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by
  norm_num

/-- **G1: a chain with three inactive slots on a nonempty closed family.** On the dihedral fixture
(`LocalChartPacketsC14` on `RP³ # RP³`, empty stage families) at GAF01's numbers
(`gaf02_chain_choice_GAF8`), for every jet order and weight constants, there is a `Gaf02Chain`
whose slots are all `inactive`. Its selections are constant, its planes are `⊥` and its tests hold
vacuously on the empty clouds. Its final map is the original map `E = 𝓔⁰`, and its scale exit is
`ρ`. -/
theorem exists_gaf02Chain_inactive_CHI (Kj : ℕ) (cw : Fin 3 → ℝ) :
    ∃ (Ξ Γ S eg c : Fin 3 → ℝ) (C : Gaf02Chain dihedralTinyStdBase_CHI Kj Ξ Γ S eg c cw),
      (∀ st, ∃ h, C.slot st = .inactive h) ∧
      C.E = cgpGlobalMap dihedralTinyStdBase_CHI.toLocalChartFamily dihedralTinyStdBase_CHI.zero ∧
      ∀ p, C.scale p = dihedralTinyRho_CHI p := by
  obtain ⟨-, Ξ, c, Γ, S, eg, -, -, -, -, -, -, -, hnum⟩ := gaf02_chain_choice_GAF8 Kj one_pos
  have hc : ∀ st x, x ∉ gafCloud dihedralTinyStdBase_CHI.toLocalChartFamily
      dihedralTinyStdBase_CHI.zero st := fun st x => by
    rw [dihedralTinyStd_cloud_CHI st]; exact notMem_empty x
  let C : Gaf02Chain dihedralTinyStdBase_CHI Kj (fun j => Ξ j (Γ j)) Γ S eg c cw :=
    { std := dihedralTinyStd_std_CHI
      numbers := hnum
      sel := fun _ _ => dihedralTinyBase_CHI
      hsel := fun st x hx => by
        rw [dihedralTinyStd_cloudEnlarged_CHI st] at hx
        exact absurd hx (notMem_empty x)
      plane := fun _ _ => ⊥
      test0 := ⟨fun x hx => absurd hx (hc 0 x), fun _ _ x hx => absurd hx (hc 0 x),
        fun x hx => absurd hx (hc 0 x), fun x hx => absurd hx (hc 0 x),
        fun x hx => absurd hx (hc 0 x)⟩
      test1 := ⟨fun x hx => absurd hx (hc 1 x), fun _ _ x hx => absurd hx (hc 1 x),
        fun x hx => absurd hx (hc 1 x), fun x hx => absurd hx (hc 1 x)⟩
      test2 := ⟨fun x hx => absurd hx (hc 2 x), fun _ _ x hx => absurd hx (hc 2 x),
        fun x hx => absurd hx (hc 2 x), fun x hx => absurd hx (hc 2 x)⟩
      slot := fun st => .inactive (dihedralTinyStd_stageCentres_CHI st) }
  have hid := C.inactive_stage_id
  have hE : C.E = cgpGlobalMap dihedralTinyStdBase_CHI.toLocalChartFamily
      dihedralTinyStdBase_CHI.zero := by
    rw [Gaf02Chain.E, Gaf02Chain.g₂, Gaf02Chain.g₁, hid.1 _ rfl, hid.2.1 _ rfl, hid.2.2 _ rfl]
    rfl
  refine ⟨fun j => Ξ j (Γ j), Γ, S, eg, c, C, fun st => ⟨_, rfl⟩, hE, fun p => ?_⟩
  rw [Gaf02Chain.scale, hE]
  exact gafScaleMarker_globalMap_GAF2 _ _ p

/-- **G3: active slots on the fixture's empty stage clouds.** For `0 < Ξ ≤ 1/10` there is a
weight constant `c_w ≥ 0` (CFS15's kernel `exists_cfs15StageOutput_C15`, ratio `B = 1`) such that,
for every selection, every plane field (for instance the explicit `fun _ => ⊥`) and every `Σ`, the
fixture's stage cloud carries a `Cfs15StageOutput` with radius `Σρ ∘ sel` and these planes, the
data of an `active` slot. -/
theorem exists_cfs15StageOutput_dihedralTiny_CHI (st : Fin 3) (Kj : ℕ) {Ξ : ℝ} (hΞ : 0 < Ξ)
    (hΞ1 : Ξ ≤ 1 / 10) :
    ∃ cw : ℝ, 0 ≤ cw ∧ ∀ (sel : BlockSpace (fun _ : CGPTag
        dihedralTinyStdBase_CHI.toLocalChartFamily dihedralTinyStdBase_CHI.zero => ℝ²) →
          dihedralZeroSource)
      (plane : BlockSpace (fun _ : CGPTag dihedralTinyStdBase_CHI.toLocalChartFamily
        dihedralTinyStdBase_CHI.zero => ℝ²) → Submodule ℝ (BlockSpace (fun _ : CGPTag
          dihedralTinyStdBase_CHI.toLocalChartFamily dihedralTinyStdBase_CHI.zero => ℝ²)))
      (sg : ℝ),
      Nonempty (Cfs15StageOutput (gafStageDim st) Kj Ξ cw
        (gafCloud dihedralTinyStdBase_CHI.toLocalChartFamily dihedralTinyStdBase_CHI.zero st)
        (gafCloudEnlarged dihedralTinyStdBase_CHI.toLocalChartFamily dihedralTinyStdBase_CHI.zero
          st) (fun x => sg * dihedralTinyRho_CHI (sel x)) plane) := by
  obtain ⟨cw, hcw, δ₀, hδ₀, hout⟩ := exists_cfs15StageOutput_C15 (gafStageDim st) Kj 1 Ξ le_rfl hΞ
    hΞ1
  refine ⟨cw, hcw, fun sel plane sg => ?_⟩
  have hS := dihedralTinyStd_cloud_CHI st
  have hT := dihedralTinyStd_cloudEnlarged_CHI st
  refine hout _ _ _ (by rw [hS]; exact empty_subset _) (by rw [hS]; exact totallyBounded_empty)
    (fun x => sg * dihedralTinyRho_CHI (sel x)) plane
    (fun x hx => absurd hx (by rw [hS]; exact notMem_empty x)) 1 1 δ₀ one_pos
    (fun x hx => absurd hx (by rw [hS]; exact notMem_empty x))
    (fun x hx => absurd hx (by rw [hS]; exact notMem_empty x)) hδ₀ le_rfl
    (fun x hx => absurd hx (by rw [hT]; exact notMem_empty x))
    (fun x hx => absurd hx (by rw [hS]; exact notMem_empty x))

/-- **G3: a chain with three active slots.** At GAF01's numbers (whose `Ξ_j < 1/512`), with the
weight constants of `exists_cfs15StageOutput_dihedralTiny_CHI`, there is a `Gaf02Chain` on the
fixture whose three slots are `active` (CFS15 outputs on the empty stage clouds, planes `⊥`). The
actual cutoffs vanish on the empty families (`empty_family_stage_id`), so again `E = 𝓔⁰` and the
scale exit is `ρ`. -/
theorem exists_gaf02Chain_active_CHI (Kj : ℕ) :
    ∃ (Ξ Γ S eg c cw : Fin 3 → ℝ) (C : Gaf02Chain dihedralTinyStdBase_CHI Kj Ξ Γ S eg c cw),
      (∀ st, ∃ O, C.slot st = .active O) ∧
      C.E = cgpGlobalMap dihedralTinyStdBase_CHI.toLocalChartFamily dihedralTinyStdBase_CHI.zero ∧
      ∀ p, C.scale p = dihedralTinyRho_CHI p := by
  obtain ⟨-, Ξ, c, Γ, S, eg, -, -, -, -, -, -, -, hnum⟩ := gaf02_chain_choice_GAF8 Kj one_pos
  obtain ⟨hpos, hv₁, hc₀, hd₁, -, -, hv₂, hc₁, hd₂, -, -, -, -, -⟩ := id hnum
  have hC := gafCutoffConstant_nonneg
  have hD := one_le_gafDerivativeBound
  obtain ⟨hΞ₀, hS₀, -, he₀⟩ := hpos 0
  obtain ⟨hΞ₁, hS₁, -, he₁⟩ := hpos 1
  obtain ⟨hΞ₂, hS₂, -, he₂⟩ := hpos 2
  have hcp₀ : 0 < c 0 := lt_of_le_of_lt (by positivity) hv₁
  have hcp₁ : 0 < c 1 := lt_of_le_of_lt (by positivity) hv₂
  have hΞle : ∀ j, Ξ j (Γ j) ≤ 1 / 10 := by
    intro j
    fin_cases j
    · have h1 : 0 ≤ 5 / 3 * Ξ 0 (Γ 0) * S 0 * gafCutoffConstant * gafDerivativeBound := by
        positivity
      have h2 : Ξ 0 (Γ 0) ≤ Ξ 0 (Γ 0) * gafDerivativeBound := le_mul_of_one_le_right hΞ₀.le hD
      change Ξ 0 (Γ 0) ≤ 1 / 10
      linarith
    · have h1 : 0 ≤ (5 / 3 * Ξ 1 (Γ 1) * S 1 + (1 + Ξ 1 (Γ 1)) * c 0) * gafCutoffConstant *
          (gafDerivativeBound + c 0) := by positivity
      have h2 : Ξ 1 (Γ 1) ≤ Ξ 1 (Γ 1) * (gafDerivativeBound + c 0) :=
        le_mul_of_one_le_right hΞ₁.le (by linarith)
      change Ξ 1 (Γ 1) ≤ 1 / 10
      linarith
    · have h1 : 0 ≤ (5 / 3 * Ξ 2 (Γ 2) * S 2 + (1 + Ξ 2 (Γ 2)) * c 1) * gafCutoffConstant *
          (gafDerivativeBound + c 1) := by positivity
      have h2 : Ξ 2 (Γ 2) ≤ Ξ 2 (Γ 2) * (gafDerivativeBound + c 1) :=
        le_mul_of_one_le_right hΞ₂.le (by linarith)
      change Ξ 2 (Γ 2) ≤ 1 / 10
      linarith
  choose cw hcw hout using fun j : Fin 3 =>
    exists_cfs15StageOutput_dihedralTiny_CHI j Kj ((hpos j).1) (hΞle j)
  have hc : ∀ st x, x ∉ gafCloud dihedralTinyStdBase_CHI.toLocalChartFamily
      dihedralTinyStdBase_CHI.zero st := fun st x => by
    rw [dihedralTinyStd_cloud_CHI st]; exact notMem_empty x
  let C : Gaf02Chain dihedralTinyStdBase_CHI Kj (fun j => Ξ j (Γ j)) Γ S eg c cw :=
    { std := dihedralTinyStd_std_CHI
      numbers := hnum
      sel := fun _ _ => dihedralTinyBase_CHI
      hsel := fun st x hx => by
        rw [dihedralTinyStd_cloudEnlarged_CHI st] at hx
        exact absurd hx (notMem_empty x)
      plane := fun _ _ => ⊥
      test0 := ⟨fun x hx => absurd hx (hc 0 x), fun _ _ x hx => absurd hx (hc 0 x),
        fun x hx => absurd hx (hc 0 x), fun x hx => absurd hx (hc 0 x),
        fun x hx => absurd hx (hc 0 x)⟩
      test1 := ⟨fun x hx => absurd hx (hc 1 x), fun _ _ x hx => absurd hx (hc 1 x),
        fun x hx => absurd hx (hc 1 x), fun x hx => absurd hx (hc 1 x)⟩
      test2 := ⟨fun x hx => absurd hx (hc 2 x), fun _ _ x hx => absurd hx (hc 2 x),
        fun x hx => absurd hx (hc 2 x), fun x hx => absurd hx (hc 2 x)⟩
      slot := fun st => .active (hout st (fun _ => dihedralTinyBase_CHI) (fun _ => ⊥) (S st)).some }
  have hid := C.empty_family_stage_id
  have hE : C.E = cgpGlobalMap dihedralTinyStdBase_CHI.toLocalChartFamily
      dihedralTinyStdBase_CHI.zero := by
    rw [Gaf02Chain.E, Gaf02Chain.g₂, Gaf02Chain.g₁, hid.1 rfl, hid.2.1 rfl, hid.2.2 rfl]
    rfl
  refine ⟨fun j => Ξ j (Γ j), Γ, S, eg, c, cw, C, fun st => ⟨_, rfl⟩, hE, fun p => ?_⟩
  rw [Gaf02Chain.scale, hE]
  exact gafScaleMarker_globalMap_GAF2 _ _ p

/-- **Consumer** (the chain's own GAF02 CORE theorems `stage_smooth`, `stage_error_lt`,
`stage_derivative_lt`, `scale_pos`, run on the inactive chain of the fixture): `E` is smooth,
`‖E − 𝓔⁰‖ < c₃ρ`, the derivative error has a budget below `c₃`, and the scale exit is positive. -/
theorem gaf02_core_dihedralTiny_CHI (Kj : ℕ) (cw : Fin 3 → ℝ) :
    ∃ (Ξ Γ S eg c : Fin 3 → ℝ) (C : Gaf02Chain dihedralTinyStdBase_CHI Kj Ξ Γ S eg c cw),
      ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace (fun _ : CGPTag dihedralTinyStdBase_CHI.toLocalChartFamily
        dihedralTinyStdBase_CHI.zero => ℝ²)) ∞ C.E ∧
      (∀ p, ‖C.E p - cgpGlobalMap dihedralTinyStdBase_CHI.toLocalChartFamily
        dihedralTinyStdBase_CHI.zero p‖ < c 2 * dihedralTinyRho_CHI p) ∧
      (∃ Hd : ℝ, Hd < c 2 ∧ ∀ p w, ‖mvfderiv 𝓘(ℝ, E3) C.E p w -
        mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap dihedralTinyStdBase_CHI.toLocalChartFamily
          dihedralTinyStdBase_CHI.zero) p w‖ ≤
            Hd * Real.sqrt (dihedralTinyMetric_CHI.inner p w w)) ∧
      ∀ p, 0 < C.scale p := by
  obtain ⟨Ξ, Γ, S, eg, c, C, -, -, -⟩ := exists_gaf02Chain_inactive_CHI Kj cw
  exact ⟨Ξ, Γ, S, eg, c, C, C.stage_smooth.2.2, C.stage_error_lt.2.2, C.stage_derivative_lt.2.2,
    fun p => (C.scale_pos p).2⟩

end DifferentialGeometry.Geometry.Collapse
