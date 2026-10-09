import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1NecksCollarDomain
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1NecksCharts
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCycleBallVertex

/-!
# Chapter-14 assembly, item L1, G3b / T1′: the master bicollar of a rim (E2b)

Lane ASM-L1m (statement frozen in `build-logs/scratch/ASM-L1e2/Targets.lean`, lane ASM-L1e2).

The master bicollar `masterMap` of rim `(k, b)` of a ball–handle cycle reads, on
`ℝ² × ℝ ∋ (z, s)`,
* the rim chart in polar coordinates, radial coordinate compressed by `f`, for `‖z‖ > 59/64`;
* the handle in product coordinates `(handleDiskMap A P z, endCoord b (σ s))` for `‖z‖ ≤ 59/64`,
  `s > 0`;
* the ball chart composed with a ball-side collar `G` for `‖z‖ ≤ 59/64`, `s ≤ 0`.

**E2b** `BallHandleCycle.exists_masterDomain`: on `masterDomain η' Y` (radius `1 + 9/32`, heights
`(-η', Y)`) for a small `η'`, the master map is an injective local diffeomorphism, the ball side is
`s ≤ 0`, the handle side is `s ≥ 0, ‖z‖ ≤ 1` (in product form), the ball side lies in a given
open neighbourhood `O` of the rim slice, and `s > 0, ‖z‖ > 1` is the open quadrant of the rim
chart.

Proof. The three forms are local diffeomorphisms (`isLocalDiffeomorphAt_rimForm_master`: polar
coordinates `planePolar` and `isLocalDiffeomorphAt_rimCoord`;
`EdgeHandle.isLocalDiffeomorphAt_handleRead_master` composed with
`isLocalDiffeomorphAt_handleProfile_master`: the handle read
`(w, t) ↦ H.map (diskClamp w, projIcc t)` at interior points, via the immersion criterion for the
inclusion `ClosedCell 2 × Icc 0 1 → ℝ² × ℝ` and the inverse function theorem at an interior point
of `W`; `isLocalDiffeomorphAt_ballForm_master`) and agree on overlaps (`heq`/`hPρ`, `hGχ`, `hGH`),
so `masterMap` is a local diffeomorphism at every height in `(-min η 1, Y)`
(`BallHandleCycle.isLocalDiffeomorphAt_masterMap`). It is injective on all heights `[0, Y)`
(handle form and rim form are injective, separated by membership in the handle). On the compact
slice `closedBall 0 (1 + 9/32) × {0}` it is injective and maps into the rim slice `⊆ O`; by
`Set.InjOn.exists_isOpen_superset` and a thickening, both hold on a slab `|s| < δ`. Heights
`s ≤ 0` go into the ball, heights `s > 0` into no ball, which separates the two sides.

Overlap with the collar (E2a, lane ASM-L1e3): `EdgeHandle.isLocalDiffeomorphAt_handleRead_master`
is the handle-read local diffeomorphism promised by the collar route; it is stated here with the
suffix `_master`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
  Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

local instance ballCharts_ASML1m : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 2

local instance ballSmooth_ASML1m : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 2

local instance diskCharts_ASML1m : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

local instance diskSmooth_ASML1m : IsManifold (𝓡∂ 2) ∞ (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 1

local instance diskChartsSucc_ASML1m :
    ChartedSpace (EuclideanHalfSpace (1 + 1)) (ClosedCell (1 + 1)) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

local instance diskSmoothSucc_ASML1m : IsManifold (𝓡∂ (1 + 1)) ∞ (ClosedCell (1 + 1)) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 1

/-- `diskClamp` is smooth at points of the open disk. -/
theorem contMDiffAt_diskClamp_master {w : EuclideanSpace ℝ (Fin 2)} (hw : ‖w‖ < 1) :
    ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) (𝓡∂ 2) ∞ diskClamp w := by
  have hev : (Subtype.val ∘ diskClamp : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
      =ᶠ[𝓝 w] id := by
    filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hw] with v hv
    exact diskClamp_val (le_of_lt hv)
  apply (ContMDiffAt.iff_comp_isImmersionAt
    ((DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_closedCell_inclusion
      1).isImmersion.isImmersionAt (diskClamp w))).mpr
  refine ⟨?_, ?_⟩
  · exact (Topology.IsInducing.subtypeVal.continuousAt_iff).mpr
      (continuousAt_id.congr hev.symm)
  · exact hev.contMDiffAt_iff.mpr contMDiffAt_id

theorem contMDiffAt_projIcc_master {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    ContMDiffAt 𝓘(ℝ, ℝ) (𝓡∂ 1) ∞ (projIcc (0 : ℝ) 1 zero_le_one) t :=
  contMDiffOn_projIcc.contMDiffAt (Icc_mem_nhds ht.1 ht.2)

/-- The handle read in product coordinates: `(w, t) ↦ (diskClamp w, projIcc t)`. -/
def handleRead_master (p : EuclideanSpace ℝ (Fin 2) × ℝ) : ClosedCell 2 × Icc (0 : ℝ) 1 :=
  (diskClamp p.1, projIcc (0 : ℝ) 1 zero_le_one p.2)

theorem contMDiffAt_handleRead_master {p : EuclideanSpace ℝ (Fin 2) × ℝ} (hp1 : ‖p.1‖ < 1)
    (hp2 : p.2 ∈ Ioo (0 : ℝ) 1) :
    ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) ((𝓡∂ 2).prod (𝓡∂ 1)) ∞ handleRead_master p :=
  ((contMDiffAt_diskClamp_master hp1).comp p contDiff_fst.contMDiff.contMDiffAt).prodMk
    ((contMDiffAt_projIcc_master hp2).comp p contDiff_snd.contMDiff.contMDiffAt)

theorem handleRead_master_eventuallyEq {p : EuclideanSpace ℝ (Fin 2) × ℝ} (hp1 : ‖p.1‖ < 1)
    (hp2 : p.2 ∈ Ioo (0 : ℝ) 1) :
    (Prod.map Subtype.val Subtype.val ∘ handleRead_master :
      EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 2) × ℝ) =ᶠ[𝓝 p] id := by
  have hU : IsOpen {p : EuclideanSpace ℝ (Fin 2) × ℝ | ‖p.1‖ < 1 ∧ 0 < p.2 ∧ p.2 < 1} :=
    (isOpen_lt (continuous_norm.comp continuous_fst) continuous_const).inter
      ((isOpen_lt continuous_const continuous_snd).inter
        (isOpen_lt continuous_snd continuous_const))
  filter_upwards [hU.mem_nhds ⟨hp1, hp2.1, hp2.2⟩] with x hx
  refine Prod.ext ?_ ?_
  · exact diskClamp_val hx.1.le
  · exact congrArg Subtype.val (projIcc_of_mem zero_le_one ⟨hx.2.1.le, hx.2.2.le⟩)

theorem bijective_mfderiv_handleRead_master {p : EuclideanSpace ℝ (Fin 2) × ℝ}
    (hp1 : ‖p.1‖ < 1) (hp2 : p.2 ∈ Ioo (0 : ℝ) 1) :
    Bijective (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) ((𝓡∂ 2).prod (𝓡∂ 1))
      handleRead_master p) := by
  let ι : ClosedCell 2 × Icc (0 : ℝ) 1 → EuclideanSpace ℝ (Fin 2) × ℝ :=
    Prod.map Subtype.val Subtype.val
  have hι : IsSmoothEmbedding ((𝓡∂ 2).prod (𝓡∂ 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) ∞ ι := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact (DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_closedCell_inclusion 1).prodMap
      (isSmoothEmbedding_subtypeVal_Icc (x := (0 : ℝ)) (y := 1))
  have hιb : Bijective (mfderiv ((𝓡∂ 2).prod (𝓡∂ 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) ι
      (handleRead_master p)) :=
    DifferentialGeometry.Topology.Manifold.bijective_mfderiv_of_isImmersionAt _ _ ι _
      (hι.isImmersion.isImmersionAt _) (by simp)
  have hchain := mfderiv_comp p (hι.contMDiff.mdifferentiableAt (by simp))
    ((contMDiffAt_handleRead_master hp1 hp2).mdifferentiableAt (by simp))
  rw [(handleRead_master_eventuallyEq hp1 hp2).mfderiv_eq, mfderiv_id] at hchain
  set L := mfderiv ((𝓡∂ 2).prod (𝓡∂ 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) ι
    (handleRead_master p) with hL
  set D := mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) ((𝓡∂ 2).prod (𝓡∂ 1))
    handleRead_master p with hD
  have hLD : ∀ v, L (D v) = v := fun v => by
    have := congrArg (fun T => T v) hchain
    exact this.symm
  refine ⟨fun v v' h => ?_, fun y => ⟨L y, hιb.1 (hLD (L y))⟩⟩
  rw [← hLD v, ← hLD v', h]

theorem EdgeHandle.isLocalDiffeomorphAt_handleRead_master {W : CompactCarrier.{u}}
    (H : EdgeHandle W) {p : EuclideanSpace ℝ (Fin 2) × ℝ} (hp1 : ‖p.1‖ < 1)
    (hp2 : p.2 ∈ Ioo (0 : ℝ) 1) :
    IsLocalDiffeomorphAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model ∞
      (H.map ∘ handleRead_master) p := by
  have hU : IsOpen {p : EuclideanSpace ℝ (Fin 2) × ℝ | ‖p.1‖ < 1 ∧ 0 < p.2 ∧ p.2 < 1} :=
    (isOpen_lt (continuous_norm.comp continuous_fst) continuous_const).inter
      ((isOpen_lt continuous_const continuous_snd).inter
        (isOpen_lt continuous_snd continuous_const))
  refine isLocalDiffeomorphAt_of_bijective_of_isInteriorPoint hU ⟨hp1, hp2.1, hp2.2⟩ ?_ ?_ ?_
  · intro x hx
    exact (H.smooth.contMDiffAt.comp x
      (contMDiffAt_handleRead_master hx.1 ⟨hx.2.1, hx.2.2⟩)).contMDiffWithinAt
  · rw [mfderiv_comp p (H.smooth.mdifferentiableAt (by simp))
      ((contMDiffAt_handleRead_master hp1 hp2).mdifferentiableAt (by simp))]
    exact (H.mfderiv_bijective _).comp (bijective_mfderiv_handleRead_master hp1 hp2)
  · exact H.interior ⟨_, rfl⟩

/-! ## The three local forms -/

theorem contDiff_endCoord_comp_master {σ : ℝ → ℝ} (hσ : ContDiff ℝ ∞ σ) (b : Bool) :
    ContDiff ℝ ∞ (fun s => endCoord b (σ s)) := by
  cases b
  · exact hσ
  · exact contDiff_const.sub hσ

theorem exists_hasDerivAt_endCoord_comp_master {σ : ℝ → ℝ} (hσ : ContDiff ℝ ∞ σ) (b : Bool)
    {s : ℝ} (hs : deriv σ s ≠ 0) :
    ∃ c : ℝ, c ≠ 0 ∧ HasDerivAt (fun s => endCoord b (σ s)) c s := by
  have hd : HasDerivAt σ (deriv σ s) s := ((hσ.differentiable (by simp)) s).hasDerivAt
  cases b
  · exact ⟨deriv σ s, hs, hd⟩
  · exact ⟨-deriv σ s, neg_ne_zero.mpr hs, hd.const_sub 1⟩

theorem bijective_smulRight_one_master {c : ℝ} (hc : c ≠ 0) :
    Bijective ((1 : ℝ →L[ℝ] ℝ).smulRight c) := by
  refine ⟨fun v w hvw => ?_, fun w => ⟨w / c, ?_⟩⟩
  · have h1 : v * c = w * c := by simpa using hvw
    exact mul_right_cancel₀ hc h1
  · have h2 : w / c * c = w := div_mul_cancel₀ w hc
    simpa using h2

/-- The handle side of a neck in product coordinates, `(z, s) ↦ (handleDiskMap A P z,
endCoord b (σ s))`, is a local diffeomorphism of `ℝ² × ℝ` on the closed unit disk times the
heights where `σ' ≠ 0`. -/
theorem isLocalDiffeomorphAt_handleProfile_master
    (A : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2)) {P σ : ℝ → ℝ}
    (hP : ContDiff ℝ ∞ P) (hPpos : ∀ s, 0 ≤ s → s ≤ 1 → 0 < P s)
    (hPmono : ∀ r, 0 ≤ r → r ≤ 1 → 0 < deriv (fun r : ℝ => r * P (r ^ 2)) r)
    (hσ : ContDiff ℝ ∞ σ) (b : Bool) {q : EuclideanSpace ℝ (Fin 2) × ℝ} (hq : ‖q.1‖ ≤ 1)
    (hσq : deriv σ q.2 ≠ 0) :
    IsLocalDiffeomorphAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) ∞
      (Prod.map (handleDiskMap A P) (fun s => endCoord b (σ s))) q := by
  have hc : ContDiff ℝ ∞ (Prod.map (handleDiskMap A P) (fun s => endCoord b (σ s))) :=
    (contDiff_handleDiskMap A hP).prodMap (contDiff_endCoord_comp_master hσ b)
  apply isLocalDiffeomorphAt_of_contDiffOn_of_bijective isOpen_univ (mem_univ q) hc.contDiffOn
  obtain ⟨c, hc0, hcd⟩ := exists_hasDerivAt_endCoord_comp_master hσ b hσq
  have h1 : HasFDerivAt (handleDiskMap A P) (fderiv ℝ (handleDiskMap A P) q.1) q.1 :=
    ((contDiff_handleDiskMap A hP).differentiable (by simp) q.1).hasFDerivAt
  have hD := h1.prodMap q hcd.hasFDerivAt
  rw [hD.fderiv]
  exact (Prod.map_bijective (f := ⇑(fderiv ℝ (handleDiskMap A P) q.1))
    (g := ⇑((1 : ℝ →L[ℝ] ℝ).smulRight c))).mpr
      ⟨bijective_fderiv_handleDiskMap A hP hPpos hPmono hq, bijective_smulRight_one_master hc0⟩

/-- The rim side: `(z, s) ↦ χ (planeUnit z, (f (8 (‖z‖ - 1)), s))` is a local diffeomorphism off
the axis. -/
theorem isLocalDiffeomorphAt_rimForm_master {W : CompactCarrier.{u}}
    (χ : PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ × ℝ)) W.model (Circle × (ℝ × ℝ)) W.Carrier ∞)
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hfd : ∀ x, 0 < deriv f x)
    {q : EuclideanSpace ℝ (Fin 2) × ℝ} (hq : q.1 ≠ 0)
    (hχ : (planeUnit q.1, (f (8 * (‖q.1‖ - 1)), q.2)) ∈ χ.source) :
    IsLocalDiffeomorphAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model ∞
      (fun q : EuclideanSpace ℝ (Fin 2) × ℝ => χ (planeUnit q.1, (f (8 * (‖q.1‖ - 1)), q.2)))
      q :=
  ((planePolar.isLocalDiffeomorphAt _ _ _ hq).comp
    _ _ (isLocalDiffeomorphAt_rimCoord hf hfd _)).comp _ _ (χ.isLocalDiffeomorphAt _ _ _ hχ)

/-- The ball side: `Bh ∘ G` is a local diffeomorphism on the collar domain. -/
theorem isLocalDiffeomorphAt_ballForm_master {W : CompactCarrier.{u}}
    (Bh : PartialDiffeomorph (𝓡 3) W.model (EuclideanSpace ℝ (Fin 3)) W.Carrier ∞) {η : ℝ}
    {G : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 3)}
    (hG : ContDiffOn ℝ ∞ G (collarDomain η)) (hGsrc : ∀ q ∈ collarDomain η, G q ∈ Bh.source)
    (hGd : ∀ q ∈ collarDomain η, Bijective (fderiv ℝ G q)) {q : EuclideanSpace ℝ (Fin 2) × ℝ}
    (hq : q ∈ collarDomain η) :
    IsLocalDiffeomorphAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model ∞ (Bh ∘ G) q :=
  (isLocalDiffeomorphAt_of_contDiffOn_of_bijective (isOpen_collarDomain η) hq hG
    (hGd q hq)).comp _ _ (Bh.isLocalDiffeomorphAt _ _ _ (hGsrc q hq))

/-! ## Scalar facts -/

theorem strictMonoOn_Ico_master {σ : ℝ → ℝ} {a : ℝ} (hσ : ContDiff ℝ ∞ σ)
    (hσd : ∀ y ∈ Ico 0 a, 0 < deriv σ y) : StrictMonoOn σ (Ico 0 a) :=
  strictMonoOn_of_deriv_pos (convex_Ico 0 a) hσ.continuous.continuousOn
    (fun x hx => hσd x (interior_subset hx))

theorem endCoord_mem_Icc_master (b : Bool) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    endCoord b t ∈ Icc (0 : ℝ) 1 := by
  cases b
  · exact ⟨ht0, ht1⟩
  · exact ⟨show (0 : ℝ) ≤ 1 - t by linarith, show 1 - t ≤ (1 : ℝ) by linarith⟩

theorem endCoord_mem_Ioo_master (b : Bool) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    endCoord b t ∈ Ioo (0 : ℝ) 1 := by
  cases b
  · exact ⟨ht0, ht1⟩
  · exact ⟨show (0 : ℝ) < 1 - t by linarith, show 1 - t < (1 : ℝ) by linarith⟩

theorem endCoord_injective_master (b : Bool) : Injective (endCoord b) := by
  intro x y h
  cases b
  · exact h
  · have h' : 1 - x = 1 - y := h
    linarith

theorem iccEnd_val_eq_endCoord_master (b : Bool) :
    ((iccEnd b : Icc (0 : ℝ) 1) : ℝ) = endCoord b 0 := by
  cases b <;> simp [iccEnd, endCoord]

/-! ## The master bicollar -/

/-- The master bicollar of a rim: the rim chart in polar coordinates (radial coordinate
compressed by `f`) near the rim, the handle in product coordinates on the handle side, the ball
chart composed with the collar on the ball side. -/
def masterMap {W : CompactCarrier.{u}}
    (χ : PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ × ℝ)) W.model (Circle × (ℝ × ℝ)) W.Carrier ∞)
    (H : EdgeHandle W) (b : Bool)
    (Bh : PartialDiffeomorph (𝓡 3) W.model (EuclideanSpace ℝ (Fin 3)) W.Carrier ∞)
    (G : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 3))
    (A : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2)) (P σ f : ℝ → ℝ)
    (q : EuclideanSpace ℝ (Fin 2) × ℝ) : W.Carrier :=
  if 59 / 64 < ‖q.1‖ then χ (planeUnit q.1, (f (8 * (‖q.1‖ - 1)), q.2))
  else if 0 < q.2 then
    H.map (diskClamp (handleDiskMap A P q.1), Set.projIcc 0 1 zero_le_one (endCoord b (σ q.2)))
  else Bh (G q)

/-- The domain of the master bicollar. -/
def masterDomain (η Y : ℝ) : Set (EuclideanSpace ℝ (Fin 2) × ℝ) :=
  {q | ‖q.1‖ < 1 + 9 / 32 ∧ -η < q.2 ∧ q.2 < Y}

section MasterMap

variable {W : CompactCarrier.{u}}
  (χ : PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ × ℝ)) W.model (Circle × (ℝ × ℝ)) W.Carrier ∞)
  (H : EdgeHandle W) (b : Bool)
  (Bh : PartialDiffeomorph (𝓡 3) W.model (EuclideanSpace ℝ (Fin 3)) W.Carrier ∞)
  (G : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 3))
  (A : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2)) (P σ f : ℝ → ℝ)
  {q : EuclideanSpace ℝ (Fin 2) × ℝ}

theorem masterMap_of_lt (hq : 59 / 64 < ‖q.1‖) :
    masterMap χ H b Bh G A P σ f q = χ (planeUnit q.1, (f (8 * (‖q.1‖ - 1)), q.2)) := by
  rw [masterMap, ite_eq_left hq]

theorem masterMap_of_pos (hq : ‖q.1‖ ≤ 59 / 64) (hs : 0 < q.2) :
    masterMap χ H b Bh G A P σ f q = H.map (diskClamp (handleDiskMap A P q.1),
      Set.projIcc 0 1 zero_le_one (endCoord b (σ q.2))) := by
  rw [masterMap, ite_eq_right (not_lt.mpr hq), ite_eq_left hs]

theorem masterMap_of_nonpos (hq : ‖q.1‖ ≤ 59 / 64) (hs : q.2 ≤ 0) :
    masterMap χ H b Bh G A P σ f q = Bh (G q) := by
  rw [masterMap, ite_eq_right (not_lt.mpr hq), ite_eq_right (not_lt.mpr hs)]

end MasterMap

/-! ## Agreement of the three forms -/

/-- On the outer handle annulus the rim chart is the handle read through `handleDiskMap`. -/
theorem BallHandleCycle.rimForm_eq_handle_master {W : CompactCarrier.{u}} (C : BallHandleCycle W)
    (k : Fin C.len) (b : Bool) {a : ℝ} (ha : 3 / 4 < a)
    (A : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2)) {ρ σ : ℝ → ℝ}
    (heq : ∀ (θ : Circle) (x y : ℝ) (w : ClosedCell 2) (t : Icc (0 : ℝ) 1),
      -a < x → x ≤ 0 → 0 ≤ y → y < a →
      (w : EuclideanSpace ℝ (Fin 2)) = ρ x • A (planeOfCircle θ) →
      (t : ℝ) = endCoord b (σ y) → C.rimChart k b (θ, (x, y)) = (C.handle k).map (w, t))
    {P : ℝ → ℝ} (hPρ : ∀ r, 1 - 11 / 128 ≤ r → r ≤ 1 → r * P (r ^ 2) = ρ (8 * (r - 1)))
    {z : EuclideanSpace ℝ (Fin 2)} (hz1 : 1 - 11 / 128 ≤ ‖z‖) (hz2 : ‖z‖ ≤ 1) {s : ℝ}
    (hs0 : 0 ≤ s) (hsa : s < a) (w : ClosedCell 2) (t : Icc (0 : ℝ) 1)
    (hw : (w : EuclideanSpace ℝ (Fin 2)) = handleDiskMap A P z)
    (ht : (t : ℝ) = endCoord b (σ s)) :
    C.rimChart k b (planeUnit z, (8 * (‖z‖ - 1), s)) = (C.handle k).map (w, t) := by
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hz1
    norm_num at hz1
  apply heq (planeUnit z) (8 * (‖z‖ - 1)) s w t (by linarith) (by linarith) hs0 hsa _ ht
  rw [hw, handleDiskMap_eq_of_mul A hz0 (hPρ ‖z‖ hz1 hz2), planeOfCircle_planeUnit hz0, map_smul,
    smul_smul, div_eq_mul_inv]

/-- **Clause 8 (product form on the handle side).** -/
theorem BallHandleCycle.masterMap_eq_handle {W : CompactCarrier.{u}} (C : BallHandleCycle W)
    (k : Fin C.len) (b : Bool) {a : ℝ} (ha : 3 / 4 < a)
    (A : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    {ρ σ : ℝ → ℝ} (hσ : ContDiff ℝ ∞ σ) (hσ0 : σ 0 = 0) (hσd : ∀ y ∈ Ico 0 a, 0 < deriv σ y)
    (hσ1 : ∀ y ∈ Ico 0 a, σ y < 1)
    (heq : ∀ (θ : Circle) (x y : ℝ) (w : ClosedCell 2) (t : Icc (0 : ℝ) 1),
      -a < x → x ≤ 0 → 0 ≤ y → y < a →
      (w : EuclideanSpace ℝ (Fin 2)) = ρ x • A (planeOfCircle θ) →
      (t : ℝ) = endCoord b (σ y) → C.rimChart k b (θ, (x, y)) = (C.handle k).map (w, t))
    {P : ℝ → ℝ} (hP : ContDiff ℝ ∞ P) (hP1 : P 1 = 1) (hPpos : ∀ s, 0 ≤ s → s ≤ 1 → 0 < P s)
    (hPmono : ∀ r, 0 ≤ r → r ≤ 1 → 0 < deriv (fun r : ℝ => r * P (r ^ 2)) r)
    (hPρ : ∀ r, 1 - 11 / 128 ≤ r → r ≤ 1 → r * P (r ^ 2) = ρ (8 * (r - 1)))
    {f : ℝ → ℝ} (hfid : ∀ x ∈ Icc (-3 / 4 : ℝ) (3 / 4), f x = x)
    (Bh : PartialDiffeomorph (𝓡 3) W.model (EuclideanSpace ℝ (Fin 3)) W.Carrier ∞)
    {η : ℝ} (hη : 0 < η) (G : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 3))
    (hGH : ∀ q ∈ collarDomain η, 0 ≤ q.2 → ∀ (w : ClosedCell 2) (t : Icc (0 : ℝ) 1),
      (w : EuclideanSpace ℝ (Fin 2)) = handleDiskMap A P q.1 →
      (t : ℝ) = endCoord b (σ q.2) → Bh (G q) = (C.handle k).map (w, t))
    {q : EuclideanSpace ℝ (Fin 2) × ℝ} (hq0 : 0 ≤ q.2) (hqa : q.2 < a) (hq1 : ‖q.1‖ ≤ 1)
    (w : ClosedCell 2) (t : Icc (0 : ℝ) 1)
    (hw : (w : EuclideanSpace ℝ (Fin 2)) = handleDiskMap A P q.1)
    (ht : (t : ℝ) = endCoord b (σ q.2)) :
    masterMap (C.rimChart k b) (C.handle k) b Bh G A P σ f q = (C.handle k).map (w, t) := by
  by_cases hz : 59 / 64 < ‖q.1‖
  · rw [masterMap_of_lt _ _ _ _ _ _ _ _ _ hz, hfid _ ⟨by linarith, by linarith⟩]
    exact C.rimForm_eq_handle_master k b ha A heq hPρ (by linarith) hq1 hq0 hqa w t hw ht
  · have hz' : ‖q.1‖ ≤ 59 / 64 := not_lt.mp hz
    rcases lt_or_eq_of_le hq0 with hs | hs
    · rw [masterMap_of_pos _ _ _ _ _ _ _ _ _ hz' hs]
      have hσs : σ q.2 ∈ Ico (0 : ℝ) 1 :=
        ⟨nonneg_of_deriv_pos_Ico hσ hσ0 hσd ⟨hq0, hqa⟩, hσ1 q.2 ⟨hq0, hqa⟩⟩
      congr 1
      refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
      · rw [diskClamp_val (norm_handleDiskMap_le_one A hP hP1 hPpos hPmono hq1), hw]
      · exact (congrArg Subtype.val (projIcc_of_mem zero_le_one
          (endCoord_mem_Icc_master b hσs.1 hσs.2.le))).trans ht.symm
    · rw [masterMap_of_nonpos _ _ _ _ _ _ _ _ _ hz' hs.symm.le]
      refine hGH q ⟨by linarith, ?_⟩ hq0 w t hw ht
      rw [← hs, abs_zero]
      exact hη

/-- On the collar domain the master map is the ball chart composed with the collar. -/
theorem BallHandleCycle.masterMap_eq_ballForm {W : CompactCarrier.{u}} (C : BallHandleCycle W)
    (k : Fin C.len) (b : Bool) {a : ℝ}
    (A : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    {σ : ℝ → ℝ} (hσ : ContDiff ℝ ∞ σ) (hσ0 : σ 0 = 0) (hσd : ∀ y ∈ Ico 0 a, 0 < deriv σ y)
    (hσ1 : ∀ y ∈ Ico 0 a, σ y < 1)
    {P : ℝ → ℝ} (hP : ContDiff ℝ ∞ P) (hP1 : P 1 = 1) (hPpos : ∀ s, 0 ≤ s → s ≤ 1 → 0 < P s)
    (hPmono : ∀ r, 0 ≤ r → r ≤ 1 → 0 < deriv (fun r : ℝ => r * P (r ^ 2)) r)
    {f : ℝ → ℝ} (hfid : ∀ x ∈ Icc (-3 / 4 : ℝ) (3 / 4), f x = x)
    (Bh : PartialDiffeomorph (𝓡 3) W.model (EuclideanSpace ℝ (Fin 3)) W.Carrier ∞)
    {η : ℝ} (G : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 3))
    (hGH : ∀ q ∈ collarDomain η, 0 ≤ q.2 → ∀ (w : ClosedCell 2) (t : Icc (0 : ℝ) 1),
      (w : EuclideanSpace ℝ (Fin 2)) = handleDiskMap A P q.1 →
      (t : ℝ) = endCoord b (σ q.2) → Bh (G q) = (C.handle k).map (w, t))
    (hGχ : ∀ q ∈ collarDomain η, 59 / 64 ≤ ‖q.1‖ →
      Bh (G q) = C.rimChart k b (planeUnit q.1, (8 * (‖q.1‖ - 1), q.2)))
    {q : EuclideanSpace ℝ (Fin 2) × ℝ} (hq : q ∈ collarDomain η) (hqa : q.2 < a) :
    masterMap (C.rimChart k b) (C.handle k) b Bh G A P σ f q = Bh (G q) := by
  have hq1 : ‖q.1‖ < 15 / 16 := hq.1
  by_cases hz : 59 / 64 < ‖q.1‖
  · rw [masterMap_of_lt _ _ _ _ _ _ _ _ _ hz, hfid _ ⟨by linarith, by linarith⟩]
    exact (hGχ q hq hz.le).symm
  · have hz' : ‖q.1‖ ≤ 59 / 64 := not_lt.mp hz
    by_cases hs : 0 < q.2
    · rw [masterMap_of_pos _ _ _ _ _ _ _ _ _ hz' hs]
      have hσs : σ q.2 ∈ Ico (0 : ℝ) 1 :=
        ⟨nonneg_of_deriv_pos_Ico hσ hσ0 hσd ⟨hs.le, hqa⟩, hσ1 q.2 ⟨hs.le, hqa⟩⟩
      refine (hGH q hq hs.le _ _ ?_ ?_).symm
      · exact diskClamp_val (norm_handleDiskMap_le_one A hP hP1 hPpos hPmono (by linarith))
      · exact congrArg Subtype.val (projIcc_of_mem zero_le_one
          (endCoord_mem_Icc_master b hσs.1 hσs.2.le))
    · rw [masterMap_of_nonpos _ _ _ _ _ _ _ _ _ hz' (not_lt.mp hs)]

/-! ## The master map is a local diffeomorphism -/

/-- **The master map is a local diffeomorphism** at every height in `(-η, a) ∩ (-2, a)`. -/
theorem BallHandleCycle.isLocalDiffeomorphAt_masterMap {W : CompactCarrier.{u}}
    (C : BallHandleCycle W) (k : Fin C.len) (b : Bool) {a : ℝ} (ha : 3 / 4 < a) (ha' : a ≤ 2)
    (A : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    {ρ σ : ℝ → ℝ} (hσ : ContDiff ℝ ∞ σ) (hσ0 : σ 0 = 0) (hσd : ∀ y ∈ Ico 0 a, 0 < deriv σ y)
    (hσ1 : ∀ y ∈ Ico 0 a, σ y < 1)
    (heq : ∀ (θ : Circle) (x y : ℝ) (w : ClosedCell 2) (t : Icc (0 : ℝ) 1),
      -a < x → x ≤ 0 → 0 ≤ y → y < a →
      (w : EuclideanSpace ℝ (Fin 2)) = ρ x • A (planeOfCircle θ) →
      (t : ℝ) = endCoord b (σ y) → C.rimChart k b (θ, (x, y)) = (C.handle k).map (w, t))
    {P : ℝ → ℝ} (hP : ContDiff ℝ ∞ P) (hP1 : P 1 = 1) (hPpos : ∀ s, 0 ≤ s → s ≤ 1 → 0 < P s)
    (hPmono : ∀ r, 0 ≤ r → r ≤ 1 → 0 < deriv (fun r : ℝ => r * P (r ^ 2)) r)
    (hPρ : ∀ r, 1 - 11 / 128 ≤ r → r ≤ 1 → r * P (r ^ 2) = ρ (8 * (r - 1)))
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hfd : ∀ x, 0 < deriv f x)
    (hfid : ∀ x ∈ Icc (-3 / 4 : ℝ) (3 / 4), f x = x) (hfb : ∀ x, -1 < f x ∧ f x < 1)
    (Bh : PartialDiffeomorph (𝓡 3) W.model (EuclideanSpace ℝ (Fin 3)) W.Carrier ∞)
    {η : ℝ} (hη : 0 < η) (G : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 3))
    (hG : ContDiffOn ℝ ∞ G (collarDomain η))
    (hGsrc : ∀ q ∈ collarDomain η, G q ∈ Bh.source)
    (hGd : ∀ q ∈ collarDomain η, Bijective (fderiv ℝ G q))
    (hGH : ∀ q ∈ collarDomain η, 0 ≤ q.2 → ∀ (w : ClosedCell 2) (t : Icc (0 : ℝ) 1),
      (w : EuclideanSpace ℝ (Fin 2)) = handleDiskMap A P q.1 →
      (t : ℝ) = endCoord b (σ q.2) → Bh (G q) = (C.handle k).map (w, t))
    (hGχ : ∀ q ∈ collarDomain η, 59 / 64 ≤ ‖q.1‖ →
      Bh (G q) = C.rimChart k b (planeUnit q.1, (8 * (‖q.1‖ - 1), q.2)))
    {q : EuclideanSpace ℝ (Fin 2) × ℝ} (hqη : -η < q.2) (hq2 : -2 < q.2) (hqa : q.2 < a) :
    IsLocalDiffeomorphAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model ∞
      (masterMap (C.rimChart k b) (C.handle k) b Bh G A P σ f) q := by
  by_cases hz : 59 / 64 < ‖q.1‖
  · -- the rim form
    have hq0 : q.1 ≠ 0 := by
      intro h
      rw [h, norm_zero] at hz
      norm_num at hz
    have hsrc : (planeUnit q.1, (f (8 * (‖q.1‖ - 1)), q.2)) ∈ (C.rimChart k b).source := by
      apply (C.rim_source k b).mpr
      obtain ⟨h1, h2⟩ := hfb (8 * (‖q.1‖ - 1))
      exact ⟨abs_lt.mpr ⟨by linarith, by linarith⟩, abs_lt.mpr ⟨hq2, by linarith⟩⟩
    refine DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq ?_
      (isLocalDiffeomorphAt_rimForm_master (C.rimChart k b) hf hfd hq0 hsrc)
    filter_upwards [(isOpen_lt continuous_const (continuous_norm.comp continuous_fst)).mem_nhds hz]
      with q' hq'
    exact masterMap_of_lt _ _ _ _ _ _ _ _ _ hq'
  · have hz' : ‖q.1‖ ≤ 59 / 64 := not_lt.mp hz
    by_cases hs : 0 < q.2
    · -- the handle form
      have hσs : σ q.2 ∈ Ioo (0 : ℝ) 1 := by
        refine ⟨?_, hσ1 q.2 ⟨hs.le, hqa⟩⟩
        have := strictMonoOn_Ico_master hσ hσd (⟨le_rfl, by linarith⟩ : (0 : ℝ) ∈ Ico 0 a)
          ⟨hs.le, hqa⟩ hs
        rwa [hσ0] at this
      have hΦ := isLocalDiffeomorphAt_handleProfile_master A hP hPpos hPmono hσ b (q := q)
        (by linarith) (hσd q.2 ⟨hs.le, hqa⟩).ne'
      have hR := (C.handle k).isLocalDiffeomorphAt_handleRead_master
        (p := Prod.map (handleDiskMap A P) (fun s => endCoord b (σ s)) q)
        (norm_handleDiskMap_lt_one A hP hP1 hPpos hPmono (by linarith))
        (endCoord_mem_Ioo_master b hσs.1 hσs.2)
      refine DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq ?_ (hΦ.comp _ _ hR)
      have hU : IsOpen {q : EuclideanSpace ℝ (Fin 2) × ℝ | ‖q.1‖ < 1 ∧ 0 < q.2 ∧ q.2 < a} :=
        (isOpen_lt (continuous_norm.comp continuous_fst) continuous_const).inter
          ((isOpen_lt continuous_const continuous_snd).inter
            (isOpen_lt continuous_snd continuous_const))
      filter_upwards [hU.mem_nhds ⟨by linarith, hs, hqa⟩] with q' hq'
      have hσs' : σ q'.2 ∈ Ico (0 : ℝ) 1 :=
        ⟨nonneg_of_deriv_pos_Ico hσ hσ0 hσd ⟨hq'.2.1.le, hq'.2.2⟩, hσ1 q'.2 ⟨hq'.2.1.le, hq'.2.2⟩⟩
      refine C.masterMap_eq_handle k b ha A hσ hσ0 hσd hσ1 heq hP hP1 hPpos hPmono hPρ hfid Bh hη
        G hGH hq'.2.1.le hq'.2.2 hq'.1.le _ _ ?_ ?_
      · exact diskClamp_val (norm_handleDiskMap_le_one A hP hP1 hPpos hPmono hq'.1.le)
      · exact congrArg Subtype.val (projIcc_of_mem zero_le_one
          (endCoord_mem_Icc_master b hσs'.1 hσs'.2.le))
    · -- the ball form
      have hq : q ∈ collarDomain η :=
        ⟨by linarith, abs_lt.mpr ⟨hqη, by linarith [not_lt.mp hs]⟩⟩
      refine DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq ?_
        (isLocalDiffeomorphAt_ballForm_master Bh hG hGsrc hGd hq)
      filter_upwards [((isOpen_collarDomain η).inter
        (isOpen_lt continuous_snd continuous_const)).mem_nhds ⟨hq, hqa⟩] with q' hq'
      exact C.masterMap_eq_ballForm k b A hσ hσ0 hσd hσ1 hP hP1 hPpos hPmono hfid Bh G hGH hGχ
        hq'.1 hq'.2

/-! ## Injectivity of the rim and handle forms; membership -/

/-- The rim form is injective off the axis. -/
theorem rimForm_injective_master {W : CompactCarrier.{u}}
    (χ : PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ × ℝ)) W.model (Circle × (ℝ × ℝ)) W.Carrier ∞)
    {f : ℝ → ℝ} (hf : StrictMono f) {q q' : EuclideanSpace ℝ (Fin 2) × ℝ} (hq : q.1 ≠ 0)
    (hq' : q'.1 ≠ 0) (hs : (planeUnit q.1, (f (8 * (‖q.1‖ - 1)), q.2)) ∈ χ.source)
    (hs' : (planeUnit q'.1, (f (8 * (‖q'.1‖ - 1)), q'.2)) ∈ χ.source)
    (h : χ (planeUnit q.1, (f (8 * (‖q.1‖ - 1)), q.2)) =
      χ (planeUnit q'.1, (f (8 * (‖q'.1‖ - 1)), q'.2))) : q = q' := by
  have h1 := χ.toPartialEquiv.injOn hs hs' h
  simp only [Prod.mk.injEq] at h1
  obtain ⟨hθ, hx, hy⟩ := h1
  have hn : ‖q.1‖ = ‖q'.1‖ := by
    have := hf.injective hx
    linarith
  refine Prod.ext ?_ hy
  rw [← norm_smul_planeOfCircle_planeUnit hq, ← norm_smul_planeOfCircle_planeUnit hq', hn, hθ]

/-- The handle form is injective on the closed unit disk times `[0, a)`. -/
theorem handleForm_injective_master {W : CompactCarrier.{u}} (H : EdgeHandle W)
    (A : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2)) {P σ : ℝ → ℝ}
    (hP : ContDiff ℝ ∞ P) (hPpos : ∀ s, 0 ≤ s → s ≤ 1 → 0 < P s)
    (hPmono : ∀ r, 0 ≤ r → r ≤ 1 → 0 < deriv (fun r : ℝ => r * P (r ^ 2)) r)
    (hσ : ContDiff ℝ ∞ σ) {a : ℝ} (hσd : ∀ y ∈ Ico 0 a, 0 < deriv σ y) (b : Bool)
    {q q' : EuclideanSpace ℝ (Fin 2) × ℝ} (hq1 : ‖q.1‖ ≤ 1) (hq1' : ‖q'.1‖ ≤ 1)
    (hq2 : q.2 ∈ Ico 0 a) (hq2' : q'.2 ∈ Ico 0 a) (w w' : ClosedCell 2) (t t' : Icc (0 : ℝ) 1)
    (hw : (w : EuclideanSpace ℝ (Fin 2)) = handleDiskMap A P q.1)
    (ht : (t : ℝ) = endCoord b (σ q.2))
    (hw' : (w' : EuclideanSpace ℝ (Fin 2)) = handleDiskMap A P q'.1)
    (ht' : (t' : ℝ) = endCoord b (σ q'.2)) (h : H.map (w, t) = H.map (w', t')) : q = q' := by
  have h1 := H.injective h
  simp only [Prod.mk.injEq] at h1
  obtain ⟨hww, htt⟩ := h1
  refine Prod.ext ?_ ?_
  · apply handleDiskMap_injOn A hP hPpos hPmono (mem_closedBall_zero_iff.mpr hq1)
      (mem_closedBall_zero_iff.mpr hq1')
    rw [← hw, ← hw', hww]
  · apply (strictMonoOn_Ico_master hσ hσd).injOn hq2 hq2'
    apply endCoord_injective_master b
    rw [← ht, ← ht', htt]

/-- A handle point at a height strictly between `0` and `1` lies in no ball. -/
theorem BallHandleCycle.handle_not_mem_ball_master {W : CompactCarrier.{u}}
    (C : BallHandleCycle W) (k j : Fin C.len) (w : ClosedCell 2) {t : Icc (0 : ℝ) 1}
    (ht0 : 0 < (t : ℝ)) (ht1 : (t : ℝ) < 1) :
    (C.handle k).map (w, t) ∉ range (C.ball j).map := by
  intro hmem
  have hend : ∀ b', (C.handle k).map (w, t) ∈ (C.handle k).endDisk b' → False := by
    rintro b' ⟨x, hx⟩
    have h1 := congrArg (fun p : ClosedCell 2 × Icc (0 : ℝ) 1 => (p.2 : ℝ))
      ((C.handle k).injective hx)
    simp only at h1
    rw [iccEnd_val_eq_endCoord_master] at h1
    cases b'
    · exact absurd h1 (ne_of_lt ht0)
    · have h2 : endCoord true (0 : ℝ) = 1 := by simp [endCoord]
      rw [h2] at h1
      exact absurd h1 (ne_of_gt ht1)
  have hx : (C.handle k).map (w, t) ∈ range (C.handle k).map ∩ range (C.ball j).map :=
    ⟨⟨_, rfl⟩, hmem⟩
  rw [C.handle_ball_inter k j] at hx
  rcases hx with hx | hx
  · split_ifs at hx
    · exact hend false hx
    · exact hx
  · split_ifs at hx
    · exact hend true hx
    · exact hx

/-- The end disk `b` of handle `k` lies in the ball at that end. -/
theorem BallHandleCycle.endDisk_subset_range_rimBall_master {W : CompactCarrier.{u}}
    (C : BallHandleCycle W) (k : Fin C.len) (b : Bool) :
    (C.handle k).endDisk b ⊆ range (C.ball (rimBall C.len k b)).map := by
  cases b
  · exact (C.start_face k).trans (image_subset_range _ _)
  · exact (C.end_face k).trans (image_subset_range _ _)

/-- A point of the open unit ball of a ball chart is not on the boundary sphere of the ball. -/
theorem ballChart_not_mem_boundary_master {W : CompactCarrier.{u}} (B : PieceEmbedding W)
    (e : B.Piece ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ClosedCell 3)
    (Bh : PartialDiffeomorph (𝓡 3) W.model (EuclideanSpace ℝ (Fin 3)) W.Carrier ∞)
    (hBhsrc : Metric.closedBall 0 1 ⊆ Bh.source)
    (hBhball : ∀ x : ClosedCell 3, Bh x.val = B.map (e.symm x)) {y : EuclideanSpace ℝ (Fin 3)}
    (hy : ‖y‖ < 1) : Bh y ∉ B.map '' (𝓡∂ 3).boundary B.Piece := by
  rw [image_boundary_eq_range_of_ball B e]
  rintro ⟨z, hz⟩
  have hz1 : ‖(z : EuclideanSpace ℝ (Fin 3))‖ = 1 := mem_sphere_zero_iff_norm.mp z.2
  have hz' : Bh (z : EuclideanSpace ℝ (Fin 3)) = Bh y := (hBhball ⟨z.1, hz1.le⟩).trans hz
  have h := Bh.toPartialEquiv.injOn (hBhsrc (mem_closedBall_zero_iff.mpr hz1.le))
    (hBhsrc (mem_closedBall_zero_iff.mpr hy.le)) hz'
  rw [← h] at hy
  linarith

/-- A point of the closed unit ball of a ball chart lies in the ball. -/
theorem ballChart_mem_range_master {W : CompactCarrier.{u}} (B : PieceEmbedding W)
    (e : B.Piece ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ClosedCell 3)
    (Bh : PartialDiffeomorph (𝓡 3) W.model (EuclideanSpace ℝ (Fin 3)) W.Carrier ∞)
    (hBhball : ∀ x : ClosedCell 3, Bh x.val = B.map (e.symm x)) {y : EuclideanSpace ℝ (Fin 3)}
    (hy : ‖y‖ ≤ 1) : Bh y ∈ range B.map :=
  ⟨e.symm ⟨y, hy⟩, (hBhball ⟨y, hy⟩).symm⟩

/-! ## E2b -/

/-- **E2b (master bicollar of a rim).** -/
theorem BallHandleCycle.exists_masterDomain {W : CompactCarrier.{u}} (C : BallHandleCycle W)
    (k : Fin C.len) (b : Bool) {a : ℝ} (ha : 3 / 4 < a) (ha' : a ≤ 2)
    (A : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    {ρ σ : ℝ → ℝ} (hσ : ContDiff ℝ ∞ σ) (hσ0 : σ 0 = 0) (hσd : ∀ y ∈ Ico 0 a, 0 < deriv σ y)
    (hσ1 : ∀ y ∈ Ico 0 a, σ y < 1)
    (heq : ∀ (θ : Circle) (x y : ℝ) (w : ClosedCell 2) (t : Icc (0 : ℝ) 1),
      -a < x → x ≤ 0 → 0 ≤ y → y < a →
      (w : EuclideanSpace ℝ (Fin 2)) = ρ x • A (planeOfCircle θ) →
      (t : ℝ) = endCoord b (σ y) → C.rimChart k b (θ, (x, y)) = (C.handle k).map (w, t))
    {P : ℝ → ℝ} (hP : ContDiff ℝ ∞ P) (hP1 : P 1 = 1) (hPpos : ∀ s, 0 ≤ s → s ≤ 1 → 0 < P s)
    (hPmono : ∀ r, 0 ≤ r → r ≤ 1 → 0 < deriv (fun r : ℝ => r * P (r ^ 2)) r)
    (hPρ : ∀ r, 1 - 11 / 128 ≤ r → r ≤ 1 → r * P (r ^ 2) = ρ (8 * (r - 1)))
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hfd : ∀ x, 0 < deriv f x)
    (hfid : ∀ x ∈ Icc (-3 / 4 : ℝ) (3 / 4), f x = x) (hfb : ∀ x, -1 < f x ∧ f x < 1)
    (Bh : PartialDiffeomorph (𝓡 3) W.model (EuclideanSpace ℝ (Fin 3)) W.Carrier ∞)
    (hBhsrc : Metric.closedBall 0 1 ⊆ Bh.source)
    (hBhball : ∀ x : ClosedCell 3, Bh x.val =
      (C.ball (rimBall C.len k b)).map ((C.ballModel _).symm x))
    {η : ℝ} (hη : 0 < η) (G : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 3))
    (hG : ContDiffOn ℝ ∞ G (collarDomain η))
    (hGsrc : ∀ q ∈ collarDomain η, G q ∈ Bh.source)
    (hGd : ∀ q ∈ collarDomain η, Bijective (fderiv ℝ G q))
    (hGH : ∀ q ∈ collarDomain η, 0 ≤ q.2 → ∀ (w : ClosedCell 2) (t : Icc (0 : ℝ) 1),
      (w : EuclideanSpace ℝ (Fin 2)) = handleDiskMap A P q.1 →
      (t : ℝ) = endCoord b (σ q.2) → Bh (G q) = (C.handle k).map (w, t))
    (hGχ : ∀ q ∈ collarDomain η, 59 / 64 ≤ ‖q.1‖ →
      Bh (G q) = C.rimChart k b (planeUnit q.1, (8 * (‖q.1‖ - 1), q.2)))
    (hGball : ∀ q ∈ collarDomain η, q.2 < 0 → ‖G q‖ < 1)
    {O : Set W.Carrier} (hO : IsOpen O) (hslice : C.rimSlice k b ⊆ O) {Y : ℝ} (hY : 3 / 4 < Y)
    (hYa : Y < a) :
    ∃ η' : ℝ, 0 < η' ∧ η' ≤ η ∧
      let M := masterMap (C.rimChart k b) (C.handle k) b Bh G A P σ f
      IsLocalDiffeomorphOn 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model ∞ M (masterDomain η' Y) ∧
      InjOn M (masterDomain η' Y) ∧
      (∀ q ∈ masterDomain η' Y, (M q ∈ range (C.ball (rimBall C.len k b)).map ↔ q.2 ≤ 0)) ∧
      (∀ q ∈ masterDomain η' Y, (M q ∈ range (C.handle k).map ↔ (0 ≤ q.2 ∧ ‖q.1‖ ≤ 1))) ∧
      (∀ q ∈ masterDomain η' Y, q.2 ≤ 0 → M q ∈ O) ∧
      (∀ q ∈ masterDomain η' Y, 0 < q.2 → M q ∉ ⋃ j, range (C.ball j).map) ∧
      (∀ q ∈ masterDomain η' Y, 0 < q.2 → 1 < ‖q.1‖ → M q ∈ (C.rimChart k b).target ∧
        M q ∉ (⋃ j, range (C.ball j).map) ∪ ⋃ j, range (C.handle j).map) ∧
      (∀ q ∈ masterDomain η' Y, 0 ≤ q.2 → ‖q.1‖ ≤ 1 → ∀ (w : ClosedCell 2) (t : Icc (0 : ℝ) 1),
        (w : EuclideanSpace ℝ (Fin 2)) = handleDiskMap A P q.1 →
        (t : ℝ) = endCoord b (σ q.2) → M q = (C.handle k).map (w, t)) := by
  -- scalar facts
  have ha0 : 0 < a := by linarith
  have hfmono : StrictMono f := strictMono_of_deriv_pos hfd
  have hf0 : f 0 = 0 := hfid 0 ⟨by norm_num, by norm_num⟩
  have hfpos : ∀ x, 0 < x → 0 < f x := fun x hx => hf0 ▸ hfmono hx
  set η₀ : ℝ := min η 1
  have hη₀ : 0 < η₀ := lt_min hη one_pos
  have hη₀η : η₀ ≤ η := min_le_left η 1
  have hη₀1 : η₀ ≤ 1 := min_le_right η 1
  set M := masterMap (C.rimChart k b) (C.handle k) b Bh G A P σ f
  -- the three forms
  have hMχ : ∀ q : EuclideanSpace ℝ (Fin 2) × ℝ, 59 / 64 < ‖q.1‖ →
      M q = C.rimChart k b (planeUnit q.1, (f (8 * (‖q.1‖ - 1)), q.2)) :=
    fun q hz => masterMap_of_lt _ _ _ _ _ _ _ _ _ hz
  have hMpos : ∀ q : EuclideanSpace ℝ (Fin 2) × ℝ, ‖q.1‖ ≤ 59 / 64 → 0 < q.2 →
      M q = (C.handle k).map (diskClamp (handleDiskMap A P q.1),
        Set.projIcc 0 1 zero_le_one (endCoord b (σ q.2))) :=
    fun q hz hs => masterMap_of_pos _ _ _ _ _ _ _ _ _ hz hs
  have hMnonpos : ∀ q : EuclideanSpace ℝ (Fin 2) × ℝ, ‖q.1‖ ≤ 59 / 64 → q.2 ≤ 0 →
      M q = Bh (G q) :=
    fun q hz hs => masterMap_of_nonpos _ _ _ _ _ _ _ _ _ hz hs
  have hMH : ∀ q : EuclideanSpace ℝ (Fin 2) × ℝ, 0 ≤ q.2 → q.2 < a → ‖q.1‖ ≤ 1 →
      ∀ (w : ClosedCell 2) (t : Icc (0 : ℝ) 1),
        (w : EuclideanSpace ℝ (Fin 2)) = handleDiskMap A P q.1 →
        (t : ℝ) = endCoord b (σ q.2) → M q = (C.handle k).map (w, t) :=
    fun q h0 hqa h1 w t hw ht => C.masterMap_eq_handle k b ha A hσ hσ0 hσd hσ1 heq hP hP1 hPpos
      hPmono hPρ hfid Bh hη G hGH h0 hqa h1 w t hw ht
  have hMH' : ∀ q : EuclideanSpace ℝ (Fin 2) × ℝ, 0 ≤ q.2 → q.2 < a → ‖q.1‖ ≤ 1 →
      ∃ (w : ClosedCell 2) (t : Icc (0 : ℝ) 1),
        (w : EuclideanSpace ℝ (Fin 2)) = handleDiskMap A P q.1 ∧
        (t : ℝ) = endCoord b (σ q.2) ∧ M q = (C.handle k).map (w, t) := by
    intro q h0 hqa h1
    have hσs : σ q.2 ∈ Ico (0 : ℝ) 1 :=
      ⟨nonneg_of_deriv_pos_Ico hσ hσ0 hσd ⟨h0, hqa⟩, hσ1 q.2 ⟨h0, hqa⟩⟩
    let w : ClosedCell 2 :=
      ⟨handleDiskMap A P q.1, norm_handleDiskMap_le_one A hP hP1 hPpos hPmono h1⟩
    let t : Icc (0 : ℝ) 1 := ⟨endCoord b (σ q.2), endCoord_mem_Icc_master b hσs.1 hσs.2.le⟩
    exact ⟨w, t, rfl, rfl, hMH q h0 hqa h1 w t rfl rfl⟩
  have hMend : ∀ q : EuclideanSpace ℝ (Fin 2) × ℝ, q.2 = 0 → ‖q.1‖ ≤ 1 →
      M q ∈ (C.handle k).endDisk b := by
    intro q h0 h1
    let w : ClosedCell 2 :=
      ⟨handleDiskMap A P q.1, norm_handleDiskMap_le_one A hP hP1 hPpos hPmono h1⟩
    refine ⟨w, (hMH q h0.ge (by rw [h0]; exact ha0) h1 w (iccEnd b) rfl ?_).symm⟩
    rw [iccEnd_val_eq_endCoord_master, h0, hσ0]
  have hnz : ∀ q : EuclideanSpace ℝ (Fin 2) × ℝ, 59 / 64 < ‖q.1‖ → q.1 ≠ 0 := by
    intro q hz h
    rw [h, norm_zero] at hz
    norm_num at hz
  have hsrc : ∀ q : EuclideanSpace ℝ (Fin 2) × ℝ, -2 < q.2 → q.2 < 2 →
      (planeUnit q.1, (f (8 * (‖q.1‖ - 1)), q.2)) ∈ (C.rimChart k b).source := by
    intro q h1 h2
    apply (C.rim_source k b).mpr
    obtain ⟨h3, h4⟩ := hfb (8 * (‖q.1‖ - 1))
    exact ⟨abs_lt.mpr ⟨by linarith, by linarith⟩, abs_lt.mpr ⟨h1, h2⟩⟩
  -- local diffeomorphism
  have hLD : ∀ q : EuclideanSpace ℝ (Fin 2) × ℝ, -η₀ < q.2 → q.2 < Y →
      IsLocalDiffeomorphAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model ∞ M q :=
    fun q h1 h2 => C.isLocalDiffeomorphAt_masterMap k b ha ha' A hσ hσ0 hσd hσ1 heq hP hP1 hPpos
      hPmono hPρ hf hfd hfid hfb Bh hη G hG hGsrc hGd hGH hGχ (by linarith) (by linarith)
      (by linarith)
  -- membership
  have hball_nonpos : ∀ q : EuclideanSpace ℝ (Fin 2) × ℝ, -η₀ < q.2 → q.2 ≤ 0 →
      M q ∈ range (C.ball (rimBall C.len k b)).map := by
    intro q h1 h2
    by_cases hz : 59 / 64 < ‖q.1‖
    · rw [hMχ q hz]
      exact (C.rim_ball k b (hsrc q (by linarith) (by linarith))).mpr h2
    · rcases lt_or_eq_of_le h2 with hs | hs
      · rw [hMnonpos q (not_lt.mp hz) h2]
        exact ballChart_mem_range_master _ _ Bh hBhball
          (hGball q ⟨by linarith [not_lt.mp hz], abs_lt.mpr ⟨by linarith, by linarith⟩⟩ hs).le
      · exact C.endDisk_subset_range_rimBall_master k b (hMend q hs (by linarith [not_lt.mp hz]))
  have hball_pos : ∀ q : EuclideanSpace ℝ (Fin 2) × ℝ, 0 < q.2 → q.2 < a →
      M q ∉ ⋃ j, range (C.ball j).map := by
    intro q h1 h2 hmem
    obtain ⟨j, hj⟩ := mem_iUnion.mp hmem
    by_cases hz : 59 / 64 < ‖q.1‖
    · rw [hMχ q hz] at hj
      have hs := hsrc q (by linarith) (by linarith)
      by_cases hjj : j = rimBall C.len k b
      · subst hjj
        exact absurd ((C.rim_ball k b hs).mp hj) (not_le.mpr h1)
      · exact Set.disjoint_left.mp (C.disjoint_ball_target k b j hjj) hj
          (C.mem_target_of_mem_source hs)
    · rw [hMpos q (not_lt.mp hz) h1] at hj
      have hσs : σ q.2 ∈ Ioo (0 : ℝ) 1 := by
        refine ⟨?_, hσ1 q.2 ⟨h1.le, h2⟩⟩
        have := strictMonoOn_Ico_master hσ hσd (⟨le_rfl, ha0⟩ : (0 : ℝ) ∈ Ico 0 a) ⟨h1.le, h2⟩ h1
        rwa [hσ0] at this
      have hmem' := endCoord_mem_Ioo_master b hσs.1 hσs.2
      have hval : ((Set.projIcc 0 1 zero_le_one (endCoord b (σ q.2)) : Icc (0 : ℝ) 1) : ℝ) =
          endCoord b (σ q.2) :=
        congrArg Subtype.val (projIcc_of_mem zero_le_one ⟨hmem'.1.le, hmem'.2.le⟩)
      have ht0 : 0 < ((Set.projIcc 0 1 zero_le_one (endCoord b (σ q.2)) : Icc (0 : ℝ) 1) : ℝ) := by
        rw [hval]
        exact hmem'.1
      have ht1 : ((Set.projIcc 0 1 zero_le_one (endCoord b (σ q.2)) : Icc (0 : ℝ) 1) : ℝ) < 1 := by
        rw [hval]
        exact hmem'.2
      exact C.handle_not_mem_ball_master k j _ ht0 ht1 hj
  have hhandle : ∀ q : EuclideanSpace ℝ (Fin 2) × ℝ, -η₀ < q.2 → q.2 < Y →
      (M q ∈ range (C.handle k).map ↔ (0 ≤ q.2 ∧ ‖q.1‖ ≤ 1)) := by
    intro q h1 h2
    constructor
    · intro hmem
      by_contra hcon
      rcases lt_or_ge q.2 0 with hs | hs
      · by_cases hz : 59 / 64 < ‖q.1‖
        · rw [hMχ q hz] at hmem
          exact absurd ((C.rim_handle k b (hsrc q (by linarith) (by linarith))).mp hmem).1
            (not_le.mpr hs)
        · have hqc : q ∈ collarDomain η :=
            ⟨by linarith [not_lt.mp hz], abs_lt.mpr ⟨by linarith, by linarith⟩⟩
          have hbd := C.handle_inter_ball_subset k (rimBall C.len k b)
            ⟨hmem, hball_nonpos q h1 hs.le⟩
          rw [hMnonpos q (not_lt.mp hz) hs.le] at hbd
          exact ballChart_not_mem_boundary_master _ _ Bh hBhsrc hBhball (hGball q hqc hs) hbd
      · have hz1 : 1 < ‖q.1‖ := by
          by_contra h
          exact hcon ⟨hs, not_lt.mp h⟩
        rw [hMχ q (by linarith)] at hmem
        have h3 := ((C.rim_handle k b (hsrc q (by linarith) (by linarith))).mp hmem).2
        linarith [hfpos (8 * (‖q.1‖ - 1)) (by linarith)]
    · rintro ⟨h0, h1'⟩
      obtain ⟨w, t, -, -, hMq⟩ := hMH' q h0 (by linarith) h1'
      exact ⟨_, hMq.symm⟩
  have hquad : ∀ q : EuclideanSpace ℝ (Fin 2) × ℝ, 0 < q.2 → q.2 < Y → 1 < ‖q.1‖ →
      M q ∈ (C.rimChart k b).target ∧
        M q ∉ (⋃ j, range (C.ball j).map) ∪ ⋃ j, range (C.handle j).map := by
    intro q h1 h2 h3
    rw [hMχ q (by linarith)]
    have hs := hsrc q (by linarith) (by linarith)
    exact ⟨C.mem_target_of_mem_source hs,
      C.rim_quadrant k b _ hs (hfpos _ (by linarith)) h1⟩
  -- injectivity on the nonnegative side
  have hinj_nonneg : ∀ q q' : EuclideanSpace ℝ (Fin 2) × ℝ, 0 ≤ q.2 → q.2 < Y → 0 ≤ q'.2 →
      q'.2 < Y → M q = M q' → q = q' := by
    intro q q' h0 h1 h0' h1' hMqq
    have hV : -η₀ < q.2 := by linarith
    have hV' : -η₀ < q'.2 := by linarith
    by_cases hz : ‖q.1‖ ≤ 1 <;> by_cases hz' : ‖q'.1‖ ≤ 1
    · obtain ⟨w, t, hw, ht, hMq⟩ := hMH' q h0 (by linarith) hz
      obtain ⟨w', t', hw', ht', hMq'⟩ := hMH' q' h0' (by linarith) hz'
      rw [hMq, hMq'] at hMqq
      exact handleForm_injective_master (C.handle k) A hP hPpos hPmono hσ hσd b hz hz'
        ⟨h0, by linarith⟩ ⟨h0', by linarith⟩ w w' t t' hw ht hw' ht' hMqq
    · exact absurd ((hhandle q' hV' h1').mp (hMqq ▸ (hhandle q hV h1).mpr ⟨h0, hz⟩)).2 hz'
    · exact absurd ((hhandle q hV h1).mp (hMqq.symm ▸ (hhandle q' hV' h1').mpr ⟨h0', hz'⟩)).2 hz
    · have hz1 : 59 / 64 < ‖q.1‖ := by linarith [not_le.mp hz]
      have hz1' : 59 / 64 < ‖q'.1‖ := by linarith [not_le.mp hz']
      rw [hMχ q hz1, hMχ q' hz1'] at hMqq
      exact rimForm_injective_master (C.rimChart k b) hfmono (hnz q hz1) (hnz q' hz1')
        (hsrc q (by linarith) (by linarith)) (hsrc q' (by linarith) (by linarith)) hMqq
  -- the compact slice `K₀` at height `0`
  set R : ℝ := 1 + 9 / 32
  set K₀ : Set (EuclideanSpace ℝ (Fin 2) × ℝ) :=
    Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) R ×ˢ ({0} : Set ℝ)
  have hK₀c : IsCompact K₀ := (isCompact_closedBall _ _).prod isCompact_singleton
  have hK₀mem : ∀ q ∈ K₀, ‖q.1‖ ≤ R ∧ q.2 = 0 := fun q hq =>
    ⟨mem_closedBall_zero_iff.mp hq.1, hq.2⟩
  have hY0 : 0 < Y := by linarith
  have hK₀V : ∀ q ∈ K₀, -η₀ < q.2 ∧ q.2 < Y := fun q hq => by
    rw [(hK₀mem q hq).2]
    exact ⟨by linarith, hY0⟩
  have hK₀inj : InjOn M K₀ := fun q hq q' hq' h =>
    hinj_nonneg q q' (hK₀mem q hq).2.ge (hK₀V q hq).2 (hK₀mem q' hq').2.ge (hK₀V q' hq').2 h
  have hK₀O : ∀ q ∈ K₀, M q ∈ O := by
    intro q hq
    obtain ⟨-, hq2⟩ := hK₀mem q hq
    apply hslice
    by_cases hz : ‖q.1‖ ≤ 1
    · exact Or.inl (hMend q hq2 hz)
    · right
      have hz1 : 1 < ‖q.1‖ := not_le.mp hz
      rw [hMχ q (by linarith)]
      exact ⟨(planeUnit q.1, (f (8 * (‖q.1‖ - 1)), q.2)),
        ⟨mem_univ _, ⟨(hfpos _ (by linarith)).le, (hfb _).2.le⟩,
          show q.2 ∈ ({0} : Set ℝ) from hq2⟩, rfl⟩
  -- an open neighbourhood of `K₀` on which `M` is injective and maps into `O`
  set V : Set (EuclideanSpace ℝ (Fin 2) × ℝ) := {q | -η₀ < q.2 ∧ q.2 < Y}
  have hVo : IsOpen V :=
    (isOpen_lt continuous_const continuous_snd).inter (isOpen_lt continuous_snd continuous_const)
  have hcontOn : ContinuousOn M V := fun q hq =>
    (hLD q hq.1 hq.2).contMDiffAt.continuousAt.continuousWithinAt
  obtain ⟨T, hTo, hK₀T, hTinj⟩ := hK₀inj.exists_isOpen_superset hK₀c
    (fun q hq => (hLD q (hK₀V q hq).1 (hK₀V q hq).2).contMDiffAt.continuousAt)
    (fun q hq => by
      obtain ⟨Φ, hxΦ, hEq⟩ := hLD q (hK₀V q hq).1 (hK₀V q hq).2
      refine ⟨Φ.source, Φ.open_source.mem_nhds hxΦ, fun x hx y hy hxy =>
        Φ.toPartialEquiv.injOn hx hy ?_⟩
      rw [← hEq hx, ← hEq hy]
      exact hxy)
  have hO'o : IsOpen (V ∩ M ⁻¹' O) := hcontOn.isOpen_inter_preimage hVo hO
  have hK₀N : K₀ ⊆ T ∩ (V ∩ M ⁻¹' O) := fun q hq => ⟨hK₀T hq, hK₀V q hq, hK₀O q hq⟩
  obtain ⟨δ, hδ, hthick⟩ := hK₀c.exists_thickening_subset_open (hTo.inter hO'o) hK₀N
  have hslab : ∀ q : EuclideanSpace ℝ (Fin 2) × ℝ, ‖q.1‖ ≤ R → |q.2| < δ →
      q ∈ T ∩ (V ∩ M ⁻¹' O) := by
    intro q hq1 hq2
    apply hthick
    rw [Metric.mem_thickening_iff]
    refine ⟨(q.1, 0), ⟨mem_closedBall_zero_iff.mpr hq1, rfl⟩, ?_⟩
    rw [Prod.dist_eq, dist_self, Real.dist_eq, sub_zero]
    exact max_lt hδ hq2
  -- the width
  have hdom : ∀ q ∈ masterDomain (min η₀ δ) Y,
      -η₀ < q.2 ∧ q.2 < Y ∧ ‖q.1‖ < R ∧ (q.2 ≤ 0 → |q.2| < δ) := by
    intro q hq
    obtain ⟨h1, h2, h3⟩ := hq
    have hm1 : min η₀ δ ≤ η₀ := min_le_left _ _
    have hm2 : min η₀ δ ≤ δ := min_le_right _ _
    exact ⟨by linarith, h3, h1, fun hs => abs_lt.mpr ⟨by linarith, by linarith⟩⟩
  refine ⟨min η₀ δ, lt_min hη₀ hδ, (min_le_left _ _).trans hη₀η, ?_⟩
  intro M'
  refine ⟨fun x => hLD x.1 (hdom x.1 x.2).1 (hdom x.1 x.2).2.1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q hq q' hq' hMqq'
    have hMqq : M q = M q' := hMqq'
    obtain ⟨h1, h2, h3, h4⟩ := hdom q hq
    obtain ⟨h1', h2', h3', h4'⟩ := hdom q' hq'
    rcases le_or_gt q.2 0 with hs | hs <;> rcases le_or_gt q'.2 0 with hs' | hs'
    · exact hTinj (hslab q h3.le (h4 hs)).1 (hslab q' h3'.le (h4' hs')).1 hMqq
    · exact absurd (mem_iUnion.mpr ⟨_, hMqq ▸ hball_nonpos q h1 hs⟩)
        (hball_pos q' hs' (by linarith))
    · exact absurd (mem_iUnion.mpr ⟨_, hMqq.symm ▸ hball_nonpos q' h1' hs'⟩)
        (hball_pos q hs (by linarith))
    · exact hinj_nonneg q q' hs.le h2 hs'.le h2' hMqq
  · intro q hq
    obtain ⟨h1, h2, -, -⟩ := hdom q hq
    refine ⟨fun h => ?_, hball_nonpos q h1⟩
    by_contra hs
    exact hball_pos q (not_le.mp hs) (by linarith) (mem_iUnion.mpr ⟨_, h⟩)
  · intro q hq
    obtain ⟨h1, h2, -, -⟩ := hdom q hq
    exact hhandle q h1 h2
  · intro q hq hs
    obtain ⟨-, -, h3, h4⟩ := hdom q hq
    exact (hslab q h3.le (h4 hs)).2.2
  · intro q hq hs
    obtain ⟨-, h2, -, -⟩ := hdom q hq
    exact hball_pos q hs (by linarith)
  · intro q hq hs hz
    obtain ⟨-, h2, -, -⟩ := hdom q hq
    exact hquad q hs h2 hz
  · intro q hq hs hz w t hw ht
    obtain ⟨-, h2, -, -⟩ := hdom q hq
    exact hMH q hs (by linarith) hz w t hw ht

end GC.GraphManifold.Assembly
