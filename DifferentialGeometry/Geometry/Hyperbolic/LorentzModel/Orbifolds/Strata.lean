/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Cusps.ParabolicRegions
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Orbifolds.ShortDisplacementCompactness

noncomputable section

open Set Filter MeasureTheory
open DifferentialGeometry.ProjectiveOrthogonalGroup
open scoped Topology

namespace DifferentialGeometry.OrbifoldStrata

open Hyperbolic HyperbolicAction HyperbolicFaithful
open BoundaryStabilizer OrbifoldCompactness

variable {n : ℕ}

def closedSmallElements (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (ε : ℝ) (x : HUpper n) : Set (PO n 1) :=
  {g | g ∈ Γ ∧ dist ((poMulAction hn).smul g x) x ≤ ε}

def closedSmallSubgroup (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (ε : ℝ) (x : HUpper n) : Subgroup (PO n 1) :=
  Subgroup.closure (closedSmallElements hn Γ ε x)

theorem closedSmallSubgroup_le (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (ε : ℝ) (x : HUpper n) : closedSmallSubgroup hn Γ ε x ≤ Γ :=
  (Subgroup.closure_le Γ).mpr (fun _ hg => hg.1)

theorem smallSubgroup_le_closedSmallSubgroup (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (ε : ℝ) (x : HUpper n) :
    Margulis.smallSubgroup hn Γ ε x ≤ closedSmallSubgroup hn Γ ε x :=
  Subgroup.closure_mono (fun _ hg => ⟨hg.1, hg.2.le⟩)

theorem closedSmallSubgroup_le_smallSubgroup (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    {r ε : ℝ} (hr : r < ε) (x : HUpper n) :
    closedSmallSubgroup hn Γ r x ≤ Margulis.smallSubgroup hn Γ ε x :=
  Subgroup.closure_mono (fun _ hg => ⟨hg.1, hg.2.trans_lt hr⟩)

theorem finite_closedSmallElements (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (hΓ : IsDiscrete (SetLike.coe Γ)) (ε : ℝ) (x : HUpper n) :
    (closedSmallElements hn Γ ε x).Finite := by
  apply ((finite_setOf_displacement_le hn Γ hΓ x ε).image
    (fun γ : Γ => (γ : PO n 1))).subset
  intro g hg
  exact ⟨⟨g, hg.1⟩, hg.2, rfl⟩

theorem fg_closedSmallSubgroup (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (hΓ : IsDiscrete (SetLike.coe Γ)) (ε : ℝ) (x : HUpper n) :
    Group.FG (closedSmallSubgroup hn Γ ε x) := by
  apply (Group.fg_iff_subgroup_fg _).mpr
  exact (Subgroup.fg_iff _).mpr
    ⟨closedSmallElements hn Γ ε x, rfl, finite_closedSmallElements hn Γ hΓ ε x⟩

theorem closedSmallSubgroup_geometry (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    {r ε : ℝ} (hr : r < ε) (x : HUpper n)
    (hgeom : ElementaryGeometry hn (Margulis.smallSubgroup hn Γ ε x)) :
    ElementaryGeometry hn (closedSmallSubgroup hn Γ r x) := by
  let ι := Subgroup.inclusion (closedSmallSubgroup_le_smallSubgroup hn Γ hr x)
  rcases hgeom with ⟨hf, p, hp⟩ | ⟨ξ, η, hne, hpair⟩ | ⟨ξ, hfix⟩
  · let := hf
    exact Or.inl ⟨Finite.of_injective ι (Subgroup.inclusion_injective _),
      p, fun γ => hp (ι γ)⟩
  · exact Or.inr (Or.inl ⟨ξ, η, hne, fun γ => hpair (ι γ)⟩)
  · exact Or.inr (Or.inr ⟨ξ, fun γ => hfix (ι γ)⟩)

theorem finite_closedSmallSubgroups_on_compact (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (hΓ : IsDiscrete (SetLike.coe Γ)) (ε : ℝ)
    {K : Set (HUpper n)} (hK : IsCompact K) :
    ((closedSmallSubgroup hn Γ ε) '' K).Finite := by
  let S : Set Γ :=
    {γ | ∃ x ∈ K, dist ((poMulAction hn).smul (γ : PO n 1) x) x ≤ ε}
  have hS : S.Finite := ParabolicRegions.finite_short_on_compact hn Γ hΓ ε hK
  let T : Set (PO n 1) := (fun γ : Γ => (γ : PO n 1)) '' S
  have hT : T.Finite := hS.image _
  apply (hT.powerset.image (Subgroup.closure (G := PO n 1))).subset
  rintro D ⟨x, hx, rfl⟩
  refine ⟨closedSmallElements hn Γ ε x, ?_, rfl⟩
  intro g hg
  exact ⟨⟨g, hg.1⟩, ⟨x, hx, hg.2⟩, rfl⟩

theorem locallyFinite_closedSmallSubgroup_fibers (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (hΓ : IsDiscrete (SetLike.coe Γ)) (ε : ℝ) :
    LocallyFinite (fun D : Subgroup (PO n 1) =>
      {x : HUpper n | closedSmallSubgroup hn Γ ε x = D}) := by
  intro x
  refine ⟨Metric.ball x 1, Metric.ball_mem_nhds x zero_lt_one, ?_⟩
  apply (finite_closedSmallSubgroups_on_compact hn Γ hΓ ε (isCompact_closedBall x 1)).subset
  rintro D ⟨y, hy, hyball⟩
  exact ⟨y, Metric.ball_subset_closedBall hyball, hy⟩

theorem eventually_closedSmallElements_subset (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (hΓ : IsDiscrete (SetLike.coe Γ)) (ε : ℝ) (x : HUpper n) :
    ∀ᶠ y in 𝓝 x, closedSmallElements hn Γ ε y ⊆ closedSmallElements hn Γ ε x := by
  let A : Γ → Set (HUpper n) :=
    fun γ => {y | dist ((poMulAction hn).smul (γ : PO n 1) y) y ≤ ε}
  have hA : LocallyFinite A := ParabolicRegions.locallyFinite_displacement_sublevels hn Γ hΓ ε
  have hc (γ : Γ) : IsClosed (A γ) := by
    have hcont : Continuous (fun y : HUpper n =>
        dist ((poMulAction hn).smul (γ : PO n 1) y) y) := by
      simpa only [dist_comm] using LatticeCompactness.continuous_displacement hn γ
    exact isClosed_le hcont continuous_const
  filter_upwards [hA.iInter_compl_mem_nhds hc x] with y hy
  intro g hg
  refine ⟨hg.1, ?_⟩
  by_contra hnot
  have hxm : x ∉ A (⟨g, hg.1⟩ : Γ) := hnot
  have hym : y ∉ A (⟨g, hg.1⟩ : Γ) := mem_iInter₂.mp hy ⟨g, hg.1⟩ hxm
  exact hym hg.2

theorem eventually_closedSmallSubgroup_le (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (hΓ : IsDiscrete (SetLike.coe Γ)) (ε : ℝ) (x : HUpper n) :
    ∀ᶠ y in 𝓝 x, closedSmallSubgroup hn Γ ε y ≤ closedSmallSubgroup hn Γ ε x := by
  filter_upwards [eventually_closedSmallElements_subset hn Γ hΓ ε x] with y hy
  exact Subgroup.closure_mono hy

def finiteLocus (hn : 1 ≤ n) (Γ : Subgroup (PO n 1)) (ε : ℝ) : Set (HUpper n) :=
  {x | Finite (closedSmallSubgroup hn Γ ε x)}

theorem isOpen_finiteLocus (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (hΓ : IsDiscrete (SetLike.coe Γ)) (ε : ℝ) : IsOpen (finiteLocus hn Γ ε) := by
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  let : Finite (closedSmallSubgroup hn Γ ε x) := hx
  filter_upwards [eventually_closedSmallSubgroup_le hn Γ hΓ ε x] with y hy
  exact Finite.of_injective (Subgroup.inclusion hy) (Subgroup.inclusion_injective hy)

def fixedLocus (hn : 1 ≤ n) (D : Subgroup (PO n 1)) : Set (HUpper n) :=
  {p | ∀ γ : D, (poMulAction hn).smul (γ : PO n 1) p = p}

theorem fixedLocus_antitone (hn : 1 ≤ n) {D E : Subgroup (PO n 1)} (hDE : D ≤ E) :
    fixedLocus hn E ⊆ fixedLocus hn D :=
  fun _ hp γ => hp ⟨γ, hDE γ.property⟩

theorem isClosed_fixedLocus (hn : 1 ≤ n) (D : Subgroup (PO n 1)) :
    IsClosed (fixedLocus hn D) := by
  have he : fixedLocus hn D = ⋂ γ : D,
      {p : HUpper n | (poMulAction hn).smul (γ : PO n 1) p = p} := by
    ext p
    simp only [fixedLocus, mem_ofPred_eq, mem_iInter]
  rw [he]
  exact isClosed_iInter fun γ =>
    isClosed_eq ((ContinuousAction.continuous_po_smul hn).comp
      (continuous_const.prodMk continuous_id)) continuous_id

theorem fixedLocus_nonempty_iff_finite (hn : 1 ≤ n) (D : Subgroup (PO n 1))
    (hD : IsDiscrete (SetLike.coe D)) :
    (fixedLocus hn D).Nonempty ↔ Finite D := by
  constructor
  · rintro ⟨p, hp⟩
    let := EquivariantMap.subAction hn D
    let : Finite (MulAction.stabilizer D p) := EquivariantMap.finite_stabilizer hn D hD p
    let f : D → MulAction.stabilizer D p := fun γ => ⟨γ, hp γ⟩
    exact Finite.of_injective f (fun _ _ he => congrArg Subtype.val he)
  · intro hfinite
    let := hfinite
    let := Fintype.ofFinite D
    obtain ⟨p, hp, _⟩ := EquivariantMap.exists_fixed_point_of_finite_subgroup hn D
    exact ⟨p, fun γ => hp γ γ.property⟩

def fixedStratum (hn : 1 ≤ n) (Γ : Subgroup (PO n 1)) (ε : ℝ)
    (σ : Set (HUpper n)) : Set (HUpper n) :=
  {x | fixedLocus hn (closedSmallSubgroup hn Γ ε x) = σ}

theorem finite_fixedLoci_on_compact (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (hΓ : IsDiscrete (SetLike.coe Γ)) (ε : ℝ)
    {K : Set (HUpper n)} (hK : IsCompact K) :
    ((fun x => fixedLocus hn (closedSmallSubgroup hn Γ ε x)) '' K).Finite := by
  simpa only [image_image, Function.comp_def] using
    (finite_closedSmallSubgroups_on_compact hn Γ hΓ ε hK).image (fixedLocus hn)

theorem locallyFinite_fixedStratum (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (hΓ : IsDiscrete (SetLike.coe Γ)) (ε : ℝ) :
    LocallyFinite (fixedStratum hn Γ ε) := by
  intro x
  refine ⟨Metric.ball x 1, Metric.ball_mem_nhds x zero_lt_one, ?_⟩
  apply (finite_fixedLoci_on_compact hn Γ hΓ ε (isCompact_closedBall x 1)).subset
  rintro σ ⟨y, hy, hyball⟩
  exact ⟨y, Metric.ball_subset_closedBall hyball, hy⟩

theorem eventually_fixedLocus_subset (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (hΓ : IsDiscrete (SetLike.coe Γ)) (ε : ℝ) (x : HUpper n) :
    ∀ᶠ y in 𝓝 x, fixedLocus hn (closedSmallSubgroup hn Γ ε x) ⊆
      fixedLocus hn (closedSmallSubgroup hn Γ ε y) := by
  filter_upwards [eventually_closedSmallSubgroup_le hn Γ hΓ ε x] with y hy
  exact fixedLocus_antitone hn hy

theorem fixedStratum_subset_finiteLocus (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (hΓ : IsDiscrete (SetLike.coe Γ)) (ε : ℝ) {σ : Set (HUpper n)}
    (hσ : σ.Nonempty) : fixedStratum hn Γ ε σ ⊆ finiteLocus hn Γ ε := by
  intro x hx
  exact (fixedLocus_nonempty_iff_finite hn _
    (hΓ.mono (closedSmallSubgroup_le hn Γ ε x))).mp (hx.symm ▸ hσ)

theorem finiteLocus_eq_iUnion_fixedStratum (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (hΓ : IsDiscrete (SetLike.coe Γ)) (ε : ℝ) :
    finiteLocus hn Γ ε =
      ⋃ σ : {σ : Set (HUpper n) // σ.Nonempty}, fixedStratum hn Γ ε σ.val := by
  ext x
  constructor
  · intro hx
    have hf : (fixedLocus hn (closedSmallSubgroup hn Γ ε x)).Nonempty :=
      (fixedLocus_nonempty_iff_finite hn _
        (hΓ.mono (closedSmallSubgroup_le hn Γ ε x))).mpr hx
    exact mem_iUnion.mpr ⟨⟨_, hf⟩, rfl⟩
  · intro hx
    obtain ⟨σ, hxσ⟩ := mem_iUnion.mp hx
    exact fixedStratum_subset_finiteLocus hn Γ hΓ ε σ.property hxσ

theorem closure_finiteLocus_eq_iUnion (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (hΓ : IsDiscrete (SetLike.coe Γ)) (ε : ℝ) :
    closure (finiteLocus hn Γ ε) =
      ⋃ σ : {σ : Set (HUpper n) // σ.Nonempty}, closure (fixedStratum hn Γ ε σ.val) := by
  have hf : LocallyFinite (fun σ : {σ : Set (HUpper n) // σ.Nonempty} =>
      fixedStratum hn Γ ε σ.val) :=
    (locallyFinite_fixedStratum hn Γ hΓ ε).comp_injective Subtype.val_injective
  rw [finiteLocus_eq_iUnion_fixedStratum hn Γ hΓ ε]
  exact hf.closure_iUnion

theorem exists_boundedShortLocus_for_fixedStratum (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (hΓ : IsDiscrete (SetLike.coe Γ)) (ε : ℝ) {σ : Set (HUpper n)} (hσ : σ.Nonempty) :
    ∃ N : ℕ, fixedStratum hn Γ ε σ ⊆ boundedShortLocus hn Γ ε N := by
  obtain ⟨p, hp⟩ := hσ
  let := EquivariantMap.subAction hn Γ
  let H := MulAction.stabilizer Γ p
  let : Finite H := EquivariantMap.finite_stabilizer hn Γ hΓ p
  refine ⟨Nat.card H, fun x hx => ?_⟩
  apply mem_boundedShortLocus_of_finite_subgroup hn Γ ε H
  intro γ hγ
  have hpx : p ∈ fixedLocus hn (closedSmallSubgroup hn Γ ε x) := by
    rw [show fixedLocus hn (closedSmallSubgroup hn Γ ε x) = σ from hx]
    exact hp
  exact hpx ⟨γ, Subgroup.subset_closure ⟨γ.property, hγ.le⟩⟩

theorem exists_compact_cover_closure_fixedStratum (hn : 1 ≤ n)
    (Γ : Subgroup (PO n 1)) (hΓ : IsDiscrete (SetLike.coe Γ))
    [HasFundamentalDomain Γ (PO n 1)] (hcov : covolume Γ (PO n 1) ≠ ⊤)
    {ε : ℝ} (hε : 0 < ε) {σ : Set (HUpper n)} (hσ : σ.Nonempty) :
    ∃ K : Set (HUpper n), IsCompact K ∧
      ∀ x ∈ closure (fixedStratum hn Γ ε σ), ∃ γ : Γ,
        (poMulAction hn).smul (γ : PO n 1) x ∈ K := by
  obtain ⟨N, hN⟩ := exists_boundedShortLocus_for_fixedStratum hn Γ hΓ ε hσ
  have hc : closure (fixedStratum hn Γ ε σ) ⊆ boundedShortLocus hn Γ ε N :=
    (isClosed_boundedShortLocus hn Γ ε N).closure_subset_iff.mpr hN
  obtain ⟨K, hK, _, hcover⟩ := exists_compact_boundedShort_core hn Γ hΓ hcov hε N
  exact ⟨K, hK, fun x hx => hcover x (hc hx)⟩

theorem isCompact_closure_quotient_fixedStratum (hn : 1 ≤ n)
    (Γ : Subgroup (PO n 1)) (hΓ : IsDiscrete (SetLike.coe Γ))
    [HasFundamentalDomain Γ (PO n 1)] (hcov : covolume Γ (PO n 1) ≠ ⊤)
    {ε : ℝ} (hε : 0 < ε) {σ : Set (HUpper n)} (hσ : σ.Nonempty) :
    letI := EquivariantMap.subAction hn Γ
    IsCompact (closure ((Quotient.mk (MulAction.orbitRel Γ (HUpper n))) ''
      fixedStratum hn Γ ε σ)) := by
  obtain ⟨K, hK, hcover⟩ := exists_compact_cover_closure_fixedStratum hn Γ hΓ hcov hε hσ
  exact isCompact_closure_quotient_of_compact_cover hn Γ hΓ hK
    (fun x hx => hcover x (subset_closure hx))

theorem image_closedSmallElements_conj (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (ε : ℝ) (x : HUpper n) (δ : Γ) :
    (MulAut.conj (δ : PO n 1)) '' closedSmallElements hn Γ ε x =
      closedSmallElements hn Γ ε ((poMulAction hn).smul (δ : PO n 1) x) := by
  let := poMulAction hn
  apply Subset.antisymm
  · rintro _ ⟨g, hg, rfl⟩
    refine ⟨Γ.mul_mem (Γ.mul_mem δ.property hg.1) (Γ.inv_mem δ.property), ?_⟩
    change dist (((δ : PO n 1) * g * (δ : PO n 1)⁻¹) • ((δ : PO n 1) • x))
      ((δ : PO n 1) • x) ≤ ε
    rw [mul_smul, inv_smul_smul, mul_smul, po_dist_smul hn]
    exact hg.2
  · intro g hg
    refine ⟨(δ : PO n 1)⁻¹ * g * δ, ⟨?_, ?_⟩, ?_⟩
    · exact Γ.mul_mem (Γ.mul_mem (Γ.inv_mem δ.property) hg.1) δ.property
    · have h := hg.2
      rw [dist_comm, LatticeCompactness.displacement_conj, dist_comm] at h
      exact h
    · change (δ : PO n 1) * ((δ : PO n 1)⁻¹ * g * δ) * (δ : PO n 1)⁻¹ = g
      group

theorem closedSmallSubgroup_map_conj (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (ε : ℝ) (x : HUpper n) (δ : Γ) :
    (closedSmallSubgroup hn Γ ε x).map (MulAut.conj (δ : PO n 1)).toMonoidHom =
      closedSmallSubgroup hn Γ ε ((poMulAction hn).smul (δ : PO n 1) x) := by
  simp only [closedSmallSubgroup, MonoidHom.map_closure]
  exact congrArg Subgroup.closure (image_closedSmallElements_conj hn Γ ε x δ)

theorem image_fixedLocus_conj (hn : 1 ≤ n) (D : Subgroup (PO n 1)) (g : PO n 1) :
    (fun p : HUpper n => (poMulAction hn).smul g p) '' fixedLocus hn D =
      fixedLocus hn (D.map (MulAut.conj g).toMonoidHom) := by
  let := poMulAction hn
  apply Subset.antisymm
  · rintro _ ⟨p, hp, rfl⟩ γ
    obtain ⟨d, hd, he⟩ := γ.property
    change g * d * g⁻¹ = (γ : PO n 1) at he
    change (γ : PO n 1) • (g • p) = g • p
    have hdp : d • p = p := hp ⟨d, hd⟩
    rw [← he, mul_smul, inv_smul_smul, mul_smul, hdp]
  · intro p hp
    refine ⟨g⁻¹ • p, ?_, smul_inv_smul _ _⟩
    intro γ
    have hg : g * (γ : PO n 1) * g⁻¹ ∈ D.map (MulAut.conj g).toMonoidHom :=
      ⟨γ, γ.property, rfl⟩
    have he := hp ⟨_, hg⟩
    change (g * (γ : PO n 1) * g⁻¹) • p = p at he
    have h := congrArg (fun q : HUpper n => g⁻¹ • q) he
    change (γ : PO n 1) • (g⁻¹ • p) = g⁻¹ • p
    simpa only [mul_smul, inv_smul_smul] using h

theorem fixedLocus_closedSmallSubgroup_smul (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (ε : ℝ) (x : HUpper n) (δ : Γ) :
    fixedLocus hn (closedSmallSubgroup hn Γ ε ((poMulAction hn).smul (δ : PO n 1) x)) =
      (fun p : HUpper n => (poMulAction hn).smul (δ : PO n 1) p) ''
        fixedLocus hn (closedSmallSubgroup hn Γ ε x) := by
  rw [← closedSmallSubgroup_map_conj hn Γ ε x δ, ← image_fixedLocus_conj]

theorem smul_mem_fixedStratum (hn : 1 ≤ n) (Γ : Subgroup (PO n 1)) (ε : ℝ)
    {σ : Set (HUpper n)} {x : HUpper n} (hx : x ∈ fixedStratum hn Γ ε σ) (δ : Γ) :
    (poMulAction hn).smul (δ : PO n 1) x ∈ fixedStratum hn Γ ε
      ((fun p : HUpper n => (poMulAction hn).smul (δ : PO n 1) p) '' σ) := by
  change fixedLocus hn (closedSmallSubgroup hn Γ ε _) = _
  rw [fixedLocus_closedSmallSubgroup_smul, show fixedLocus hn (closedSmallSubgroup hn Γ ε x) = σ from hx]

theorem image_fixedStratum (hn : 1 ≤ n) (Γ : Subgroup (PO n 1)) (ε : ℝ)
    (σ : Set (HUpper n)) (δ : Γ) :
    (fun x : HUpper n => (poMulAction hn).smul (δ : PO n 1) x) '' fixedStratum hn Γ ε σ =
      fixedStratum hn Γ ε
        ((fun p : HUpper n => (poMulAction hn).smul (δ : PO n 1) p) '' σ) := by
  let := poMulAction hn
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact smul_mem_fixedStratum hn Γ ε hx δ
  · intro x hx
    have hi := smul_mem_fixedStratum hn Γ ε hx δ⁻¹
    change (δ : PO n 1)⁻¹ • x ∈ fixedStratum hn Γ ε
      ((fun p : HUpper n => (δ : PO n 1)⁻¹ • p) ''
        ((fun p : HUpper n => (δ : PO n 1) • p) '' σ)) at hi
    simp only [image_image, inv_smul_smul, image_id'] at hi
    exact ⟨(δ : PO n 1)⁻¹ • x, hi, smul_inv_smul _ _⟩

theorem smul_mem_closure_fixedStratum (hn : 1 ≤ n) (Γ : Subgroup (PO n 1)) (ε : ℝ)
    {σ : Set (HUpper n)} {x : HUpper n} (hx : x ∈ closure (fixedStratum hn Γ ε σ))
    (δ : Γ) :
    (poMulAction hn).smul (δ : PO n 1) x ∈ closure (fixedStratum hn Γ ε
      ((fun p : HUpper n => (poMulAction hn).smul (δ : PO n 1) p) '' σ)) := by
  have hc : Continuous (fun x : HUpper n => (poMulAction hn).smul (δ : PO n 1) x) :=
    (ContinuousAction.continuous_po_smul hn).comp (continuous_const.prodMk continuous_id)
  have h := (image_closure_subset_closure_image (s := fixedStratum hn Γ ε σ) hc) ⟨x, hx, rfl⟩
  rwa [image_fixedStratum] at h

theorem fixedLocus_subset_of_incident (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (hΓ : IsDiscrete (SetLike.coe Γ)) (ε : ℝ)
    {σ τ : Set (HUpper n)} {x : HUpper n}
    (hx : x ∈ fixedStratum hn Γ ε σ) (hxt : x ∈ closure (fixedStratum hn Γ ε τ)) :
    σ ⊆ τ := by
  obtain ⟨y, hy, hyt⟩ := mem_closure_iff_nhds.mp hxt _
    (eventually_fixedLocus_subset hn Γ hΓ ε x)
  change fixedLocus hn (closedSmallSubgroup hn Γ ε x) ⊆
    fixedLocus hn (closedSmallSubgroup hn Γ ε y) at hy
  rwa [show fixedLocus hn (closedSmallSubgroup hn Γ ε x) = σ from hx,
    show fixedLocus hn (closedSmallSubgroup hn Γ ε y) = τ from hyt] at hy

theorem fixedLocus_ssubset_of_incident (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (hΓ : IsDiscrete (SetLike.coe Γ)) (ε : ℝ)
    {σ τ : Set (HUpper n)} (hne : σ ≠ τ) {x : HUpper n}
    (hx : x ∈ fixedStratum hn Γ ε σ) (hxt : x ∈ closure (fixedStratum hn Γ ε τ)) :
    σ ⊂ τ :=
  (fixedLocus_subset_of_incident hn Γ hΓ ε hx hxt).ssubset_of_ne hne

theorem exists_finite_incident_representatives (hn : 1 ≤ n)
    (Γ : Subgroup (PO n 1)) (hΓ : IsDiscrete (SetLike.coe Γ))
    [HasFundamentalDomain Γ (PO n 1)] (hcov : covolume Γ (PO n 1) ≠ ⊤)
    {ε : ℝ} (hε : 0 < ε) {σ : Set (HUpper n)} (hσ : σ.Nonempty) :
    ∃ S : Set (Set (HUpper n)), S.Finite ∧ ∀ τ : Set (HUpper n),
      (closure (fixedStratum hn Γ ε σ) ∩ closure (fixedStratum hn Γ ε τ)).Nonempty →
        ∃ δ : Γ, (fun p : HUpper n => (poMulAction hn).smul (δ : PO n 1) p) '' τ ∈ S := by
  obtain ⟨K, hK, hcover⟩ := exists_compact_cover_closure_fixedStratum hn Γ hΓ hcov hε hσ
  refine ⟨{τ | (closure (fixedStratum hn Γ ε τ) ∩ K).Nonempty},
    (locallyFinite_fixedStratum hn Γ hΓ ε).closure.finite_nonempty_inter_compact hK, ?_⟩
  rintro τ ⟨x, hxσ, hxτ⟩
  obtain ⟨δ, hδ⟩ := hcover x hxσ
  exact ⟨δ, (poMulAction hn).smul (δ : PO n 1) x,
    smul_mem_closure_fixedStratum hn Γ ε hxτ δ, hδ⟩

theorem exists_finite_parabolic_neighbors (hn : 1 ≤ n)
    (Γ : Subgroup (PO n 1)) (hΓ : IsDiscrete (SetLike.coe Γ))
    [HasFundamentalDomain Γ (PO n 1)] (hcov : covolume Γ (PO n 1) ≠ ⊤)
    {ε : ℝ} (hε : 0 < ε) {σ : Set (HUpper n)} (hσ : σ.Nonempty) :
    ∃ S : Set (HyperbolicBoundary.BoundaryH n), S.Finite ∧
      ∀ ξ : HyperbolicBoundary.BoundaryH n,
        (closure (fixedStratum hn Γ ε σ) ∩
          closure (ParabolicRegions.region hn Γ ε ξ)).Nonempty →
          ∃ δ : Γ, (HyperbolicBoundary.poBoundaryMulAction hn).smul (δ : PO n 1) ξ ∈ S := by
  obtain ⟨K, hK, hcover⟩ := exists_compact_cover_closure_fixedStratum hn Γ hΓ hcov hε hσ
  refine ⟨{ξ | (ParabolicRegions.closedRegion hn Γ ε ξ ∩ K).Nonempty},
    ParabolicRegions.finite_centers_meeting_compact hn Γ hΓ ε hK, ?_⟩
  rintro ξ ⟨x, hxσ, hxξ⟩
  obtain ⟨δ, hδ⟩ := hcover x hxσ
  have hc : Continuous (fun x : HUpper n => (poMulAction hn).smul (δ : PO n 1) x) :=
    (ContinuousAction.continuous_po_smul hn).comp (continuous_const.prodMk continuous_id)
  have h := (image_closure_subset_closure_image (s := ParabolicRegions.region hn Γ ε ξ) hc)
    ⟨x, hxξ, rfl⟩
  rw [ParabolicRegions.image_region] at h
  exact ⟨δ, (poMulAction hn).smul (δ : PO n 1) x,
    ParabolicRegions.closure_region_subset_closedRegion hn Γ hΓ ε _ h, hδ⟩

end DifferentialGeometry.OrbifoldStrata
