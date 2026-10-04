import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspFinitePatch
import DifferentialGeometry.Topology.Collar.InteriorLevelChart
import DifferentialGeometry.Topology.Manifold.HalfLine

/-!
# Level tori and compact bands of a cusp collar (F-e, E2 delta and E4 binding)

For a cusp embedding `e : Torus × ℍ¹ → W` (`CuspEmbedding`) the vertical chart
`j (x, s) = e (x, s)`, `0 < s < 100`, is a `C^{K+1}` injective immersion into the interior of `W`
(interior points from Codex X87's finite inverse patches, `CuspFinitePatch.lean`).

* `CuspEmbedding.isCompact_image_band`, `CuspEmbedding.isOpen_image_of_pos` (E2 delta): the image
  of a closed height band `a ≤ z ≤ b < 100` is compact; the image of an open set of positive heights
  in the cusp domain is open.
* `CuspEmbedding.exists_diffeomorph_level_torus` (E4 binding, BCP01 "the levels of the height are
  tori"): a smooth `η` on `W` whose derivative along the verticals of the collar is positive on
  `a < z < b`, whose level `c` meets every vertical and lies in the collar, has a level that is a
  smooth surface embedded in `W` and smoothly diffeomorphic to the torus.

The carrier is in universe `0` (the Morse library is).
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint
  DifferentialGeometry.Topology.Manifold

namespace DifferentialGeometry.Geometry.Collapse

universe u

theorem halfSpaceOneLift_val_zero (t : ℝ) : (halfSpaceOneLift t).1 0 = max t 0 := rfl

theorem halfSpaceOneLift_val_zero_self (y : EuclideanHalfSpace 1) :
    halfSpaceOneLift (y.1 0) = y := by
  rw [halfSpaceOneLift_eq]
  have heq : (⟨max 0 (y.1 0), le_max_left 0 (y.1 0)⟩ : Ici (0 : ℝ)) =
      halfSpaceOneHomeomorph y := Subtype.ext (max_eq_right y.2)
  rw [heq]
  exact halfSpaceOneHomeomorph.symm_apply_apply y

/-- The vertical parametrisation `(x, s) ↦ (x, s)` of the half collar. -/
theorem contMDiffOn_cuspVertical :
    ContMDiffOn (torusModel.prod 𝓘(ℝ, ℝ)) halfCollarModel ∞
      (fun p : Torus × ℝ => (p.1, halfSpaceOneLift p.2)) (univ ×ˢ Ici 0) :=
  contMDiff_fst.contMDiffOn.prodMk
    (contMDiffOn_halfSpaceOneLift.comp contMDiff_snd.contMDiffOn fun _ hp => hp.2)

theorem injective_mfderiv_cuspVertical {p : Torus × ℝ} (hp : 0 < p.2) :
    Injective (mfderiv (torusModel.prod 𝓘(ℝ, ℝ)) halfCollarModel
      (fun p : Torus × ℝ => (p.1, halfSpaceOneLift p.2)) p) := by
  let P : Torus × ℝ → CuspHalfSpace := fun p => (p.1, halfSpaceOneLift p.2)
  let Q : CuspHalfSpace → Torus × ℝ := fun q => (q.1, q.2.1 0)
  have hQ : ContMDiff halfCollarModel (torusModel.prod 𝓘(ℝ, ℝ)) ∞ Q :=
    contMDiff_fst.prodMk (contMDiff_halfSpaceOneCoordinate.comp contMDiff_snd)
  have hO : IsOpen ((univ : Set Torus) ×ˢ Ioi (0 : ℝ)) := isOpen_univ.prod isOpen_Ioi
  have hpO : p ∈ (univ : Set Torus) ×ˢ Ioi (0 : ℝ) := ⟨mem_univ _, hp⟩
  have hP : MDifferentiableAt (torusModel.prod 𝓘(ℝ, ℝ)) halfCollarModel P p :=
    ((contMDiffOn_cuspVertical.mono (prod_mono subset_rfl Ioi_subset_Ici_self)).contMDiffAt
      (hO.mem_nhds hpO)).mdifferentiableAt (by simp)
  have hQd : MDifferentiableAt halfCollarModel (torusModel.prod 𝓘(ℝ, ℝ)) Q (P p) :=
    (hQ (P p)).mdifferentiableAt (by simp)
  have hev : Q ∘ P =ᶠ[𝓝 p] id := Filter.eventuallyEq_of_mem (hO.mem_nhds hpO) fun q hq => by
    change (q.1, (halfSpaceOneLift q.2).1 0) = q
    rw [halfSpaceOneLift_val_zero, max_eq_left (le_of_lt hq.2)]
  have hid : mfderiv (torusModel.prod 𝓘(ℝ, ℝ)) (torusModel.prod 𝓘(ℝ, ℝ)) (Q ∘ P) p =
      ContinuousLinearMap.id ℝ _ :=
    ((hasMFDerivAt_id p).congr_of_eventuallyEq_abuse hev).mfderiv
  rw [mfderiv_comp p hQd hP] at hid
  intro v w hvw
  have h := congrArg (fun T => T v) hid
  have h' := congrArg (fun T => T w) hid
  simp only [ContinuousLinearMap.comp_apply] at h h'
  change mfderiv _ _ P p v = mfderiv _ _ P p w at hvw
  exact h.symm.trans ((congrArg (mfderiv halfCollarModel (torusModel.prod 𝓘(ℝ, ℝ)) Q (P p))
    hvw).trans h')

variable {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ}
  {X : Set W.Carrier}

/-- The vertical chart of a cusp collar is `C^{K+1}` on `0 < z < 100`. -/
theorem CuspEmbedding.contMDiffOn_vertical (e : CuspEmbedding W g K δ X) {a b : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ cuspDepth) :
    ContMDiffOn (torusModel.prod 𝓘(ℝ, ℝ)) W.model (K + 1)
      (fun p : Torus × ℝ => e.toFun (p.1, halfSpaceOneLift p.2)) (univ ×ˢ Ioo a b) := by
  refine e.contMDiffOn.comp ((contMDiffOn_cuspVertical.of_le (by exact_mod_cast le_top)).mono
    (prod_mono subset_rfl fun s hs => le_of_lt (ha.trans_lt hs.1))) ?_
  intro p hp
  change (halfSpaceOneLift p.2).1 0 < cuspDepth
  rw [halfSpaceOneLift_val_zero, max_eq_left (ha.trans hp.2.1.le)]
  exact hp.2.2.trans_le hb

theorem CuspEmbedding.vertical_mem_cuspDomain {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ cuspDepth)
    {p : Torus × ℝ} (hp : p ∈ (univ : Set Torus) ×ˢ Ioo a b) :
    ((p.1, halfSpaceOneLift p.2) : CuspHalfSpace) ∈ cuspDomain ∧
      0 < ((p.1, halfSpaceOneLift p.2) : CuspHalfSpace).2.val 0 := by
  have h0 : ((p.1, halfSpaceOneLift p.2) : CuspHalfSpace).2.val 0 = p.2 := by
    change (halfSpaceOneLift p.2).1 0 = p.2
    rw [halfSpaceOneLift_val_zero, max_eq_left (ha.trans hp.2.1.le)]
  refine ⟨?_, ?_⟩
  · change ((p.1, halfSpaceOneLift p.2) : CuspHalfSpace).2.val 0 < cuspDepth
    rw [h0]
    exact hp.2.2.trans_le hb
  · rw [h0]
    exact ha.trans_lt hp.2.1

theorem CuspEmbedding.injOn_vertical (e : CuspEmbedding W g K δ X) {a b : ℝ} (ha : 0 ≤ a)
    (hb : b ≤ cuspDepth) :
    InjOn (fun p : Torus × ℝ => e.toFun (p.1, halfSpaceOneLift p.2)) (univ ×ˢ Ioo a b) := by
  intro p hp q hq hpq
  have hP := (CuspEmbedding.vertical_mem_cuspDomain ha hb hp).1
  have hQ := (CuspEmbedding.vertical_mem_cuspDomain ha hb hq).1
  have h := congrArg Subtype.val (e.isEmbedding.injective
    (a₁ := ⟨_, hP⟩) (a₂ := ⟨_, hQ⟩) hpq)
  simp only [Prod.mk.injEq] at h
  have h2 := congrArg (fun y : EuclideanHalfSpace 1 => y.1 0) h.2
  simp only [halfSpaceOneLift_val_zero] at h2
  rw [max_eq_left (ha.trans hp.2.1.le), max_eq_left (ha.trans hq.2.1.le)] at h2
  exact Prod.ext h.1 h2

theorem CuspEmbedding.injective_mfderiv_vertical (e : CuspEmbedding W g K δ X) {a b : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ cuspDepth) {p : Torus × ℝ}
    (hp : p ∈ (univ : Set Torus) ×ˢ Ioo a b) :
    Injective (mfderiv (torusModel.prod 𝓘(ℝ, ℝ)) W.model
      (fun p : Torus × ℝ => e.toFun (p.1, halfSpaceOneLift p.2)) p) := by
  have hPd := CuspEmbedding.vertical_mem_cuspDomain ha hb hp
  have hO : IsOpen ((univ : Set Torus) ×ˢ Ioi (0 : ℝ)) := isOpen_univ.prod isOpen_Ioi
  have hpO : p ∈ (univ : Set Torus) ×ˢ Ioi (0 : ℝ) := ⟨mem_univ _, ha.trans_lt hp.2.1⟩
  have hP : MDifferentiableAt (torusModel.prod 𝓘(ℝ, ℝ)) halfCollarModel
      (fun p : Torus × ℝ => ((p.1, halfSpaceOneLift p.2) : CuspHalfSpace)) p :=
    ((contMDiffOn_cuspVertical.mono (prod_mono subset_rfl Ioi_subset_Ici_self)).contMDiffAt
      (hO.mem_nhds hpO)).mdifferentiableAt (by simp)
  have he : MDifferentiableAt halfCollarModel W.model e.toFun (p.1, halfSpaceOneLift p.2) :=
    (e.contMDiffOn.contMDiffAt (isOpen_cuspDomain.mem_nhds hPd.1)).mdifferentiableAt
      (by simp)
  have hcomp := mfderiv_comp p he hP
  change Injective (mfderiv (torusModel.prod 𝓘(ℝ, ℝ)) W.model
    (e.toFun ∘ fun p : Torus × ℝ => ((p.1, halfSpaceOneLift p.2) : CuspHalfSpace)) p)
  rw [hcomp]
  exact (e.immersion _ hPd.1).comp (injective_mfderiv_cuspVertical (ha.trans_lt hp.2.1))

theorem CuspEmbedding.isInteriorPoint_vertical (e : CuspEmbedding W g K δ X) {a b : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ cuspDepth) {p : Torus × ℝ}
    (hp : p ∈ (univ : Set Torus) ×ˢ Ioo a b) :
    W.model.IsInteriorPoint (e.toFun (p.1, halfSpaceOneLift p.2)) := by
  obtain ⟨hd, hz⟩ := CuspEmbedding.vertical_mem_cuspDomain ha hb hp
  obtain ⟨Φ, hpΦ, -, heq, -, hΦT⟩ := e.exists_finiteInteriorPatch hd hz
  have hmem : e.toFun (p.1, halfSpaceOneLift p.2) ∈ Φ.target := by
    rw [heq hpΦ]
    exact Φ.map_source hpΦ
  exact hΦT hmem

/-- **E2 delta (compact bands).** The image of a closed height band below the cusp depth is
compact. -/
theorem CuspEmbedding.isCompact_image_band (e : CuspEmbedding W g K δ X) {a b : ℝ}
    (hb : b < cuspDepth) :
    IsCompact (e.toFun '' {p : CuspHalfSpace | a ≤ p.2.val 0 ∧ p.2.val 0 ≤ b}) := by
  have hset : {p : CuspHalfSpace | a ≤ p.2.val 0 ∧ p.2.val 0 ≤ b} =
      (fun p : Torus × ℝ => ((p.1, halfSpaceOneLift p.2) : CuspHalfSpace)) ''
        (univ ×ˢ Icc (max a 0) b) := by
    ext q
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨(q.1, q.2.1 0), ⟨mem_univ _, max_le h1 q.2.2, h2⟩, ?_⟩
      exact Prod.ext rfl (halfSpaceOneLift_val_zero_self q.2)
    · rintro ⟨p, ⟨-, hp1, hp2⟩, rfl⟩
      have h0 : (halfSpaceOneLift p.2).1 0 = p.2 := by
        rw [halfSpaceOneLift_val_zero, max_eq_left ((le_max_right a 0).trans hp1)]
      change a ≤ (halfSpaceOneLift p.2).1 0 ∧ (halfSpaceOneLift p.2).1 0 ≤ b
      rw [h0]
      exact ⟨(le_max_left a 0).trans hp1, hp2⟩
  have hK : IsCompact ((univ : Set Torus) ×ˢ Icc (max a 0) b) :=
    isCompact_univ.prod isCompact_Icc
  have hPc : ContinuousOn (fun p : Torus × ℝ => ((p.1, halfSpaceOneLift p.2) : CuspHalfSpace))
      (univ ×ˢ Icc (max a 0) b) :=
    contMDiffOn_cuspVertical.continuousOn.mono
      (prod_mono subset_rfl fun s hs => (le_max_right a 0).trans hs.1)
  have hband : IsCompact {p : CuspHalfSpace | a ≤ p.2.val 0 ∧ p.2.val 0 ≤ b} := by
    rw [hset]
    exact hK.image_of_continuousOn hPc
  apply hband.image_of_continuousOn
  apply e.contMDiffOn.continuousOn.mono
  intro q hq
  exact hq.2.trans_lt hb

/-- **E2 delta (open sub-bands).** The image of an open set of positive heights in the cusp
domain is open. -/
theorem CuspEmbedding.isOpen_image_of_pos (e : CuspEmbedding W g K δ X) {S : Set CuspHalfSpace}
    (hS : IsOpen S) (hSd : S ⊆ cuspDomain) (hSz : ∀ p ∈ S, 0 < p.2.val 0) :
    IsOpen (e.toFun '' S) := by
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨p, hp, rfl⟩
  obtain ⟨Φ, hpΦ, -, heq, -, -⟩ := e.exists_finiteInteriorPatch (hSd hp) (hSz p hp)
  have hopen : IsOpen (Φ '' (Φ.source ∩ S)) :=
    Φ.toOpenPartialHomeomorph.isOpen_image_source_inter hS
  have hmem : e.toFun p ∈ Φ '' (Φ.source ∩ S) := ⟨p, ⟨hpΦ, hp⟩, (heq hpΦ).symm⟩
  apply Filter.mem_of_superset (hopen.mem_nhds hmem)
  rintro z ⟨q, ⟨hqΦ, hqS⟩, rfl⟩
  exact ⟨q, hqS, heq hqΦ⟩

/-- **E4 binding (BCP01, level tori).** Let `η` be smooth on the carrier, with positive
derivative along the verticals `s ↦ e (x, s)` of the collar on `a < s < b ≤ 100`; suppose every
vertical meets the level `η = c` and the level lies in `e (T² × (a, b))`. Then the level carries a
smooth structure (model `MorseModel 2`) with smooth inclusion into the carrier, and it is smoothly
diffeomorphic to the torus. -/
theorem CuspEmbedding.exists_diffeomorph_level_torus {W : CompactCarrier.{0}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ} {X : Set W.Carrier}
    (e : CuspEmbedding W g K δ X) {η : W.Carrier → ℝ} (hη : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ η)
    {a b c : ℝ} (ha : 0 ≤ a) (hb : b ≤ cuspDepth)
    (hvert : ∀ x : Torus, ∀ s ∈ Ioo a b,
      0 < deriv (fun s : ℝ => η (e.toFun (x, halfSpaceOneLift s))) s)
    (hcross : ∀ x : Torus, ∃ s ∈ Ioo a b, η (e.toFun (x, halfSpaceOneLift s)) = c)
    (hlevel : ∀ y, η y = c → ∃ x : Torus, ∃ s ∈ Ioo a b, e.toFun (x, halfSpaceOneLift s) = y) :
    ∃ cs : ChartedSpace (Topology.Morse.MorseModel 2) {y : W.Carrier // η y = c},
      letI := cs
      IsManifold 𝓘(ℝ, Topology.Morse.MorseModel 2) ∞ {y : W.Carrier // η y = c} ∧
      ContMDiff 𝓘(ℝ, Topology.Morse.MorseModel 2) W.model ∞
        (Subtype.val : {y : W.Carrier // η y = c} → W.Carrier) ∧
      Nonempty ({y : W.Carrier // η y = c} ≃ₘ⟮𝓘(ℝ, Topology.Morse.MorseModel 2), torusModel⟯
        Torus) := by
  have hdimE : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) =
      Module.finrank ℝ (Topology.Morse.MorseModel (2 + 1)) := by
    simp
  have hdimF : Module.finrank ℝ (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) = 2 := by
    simp
  exact Topology.exists_diffeomorph_level_of_vertical_chart
    (ContinuousLinearEquiv.ofFinrankEq hdimE) hdimF hη (Nat.le_add_left 1 K)
    (e.contMDiffOn_vertical ha hb) (e.injOn_vertical ha hb)
    (fun p hp => e.injective_mfderiv_vertical ha hb hp)
    (fun p hp => e.isInteriorPoint_vertical ha hb hp) hvert hcross
    (fun y hy => by
      obtain ⟨x, s, hs, rfl⟩ := hlevel y hy
      exact ⟨(x, s), ⟨mem_univ _, hs⟩, rfl⟩)

end DifferentialGeometry.Geometry.Collapse
