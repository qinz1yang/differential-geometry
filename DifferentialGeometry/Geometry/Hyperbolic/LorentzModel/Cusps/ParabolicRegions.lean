/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Boundary.Stabilizer

noncomputable section

open Set Filter
open DifferentialGeometry.ProjectiveOrthogonalGroup
open scoped Topology

namespace DifferentialGeometry.ParabolicRegions

open Hyperbolic HyperbolicAction HyperbolicFaithful HyperbolicBoundary
open BoundaryFixedPoints BoundaryStabilizer BusemannCocycle
open ElementaryGroups AsymptoticRays

variable {n : ℕ}

structure IsParabolicAt (hn : 1 ≤ n) (g : PO n 1) (ξ : BoundaryH n) : Prop where
  infinite_order : ¬IsOfFinOrder g
  fix : (poBoundaryMulAction hn).smul g ξ = ξ
  unique : ∀ η : BoundaryH n, (poBoundaryMulAction hn).smul g η = η → η = ξ

theorem IsParabolicAt.scale_one {hn : 1 ≤ n} {g : PO n 1} {ξ : BoundaryH n}
    (hg : IsParabolicAt hn g ξ) : poConfFactor hn g ξ = 1 :=
  poConfFactor_eq_one_of_unique_boundary_fixed hn g ξ hg.fix hg.unique

theorem IsParabolicAt.ne_one {hn : 1 ≤ n} {g : PO n 1} {ξ : BoundaryH n}
    (hg : IsParabolicAt hn g ξ) : g ≠ 1 := by
  rintro rfl
  exact hg.infinite_order (isOfFinOrder_iff_pow_eq_one.mpr ⟨1, by decide, one_pow 1⟩)

theorem IsParabolicAt.conj {hn : 1 ≤ n} {g : PO n 1} {ξ : BoundaryH n}
    (hg : IsParabolicAt hn g ξ) (a : PO n 1) :
    IsParabolicAt hn (a * g * a⁻¹) ((poBoundaryMulAction hn).smul a ξ) := by
  let := poBoundaryMulAction hn
  have hfix : g • ξ = ξ := hg.fix
  refine ⟨?_, ?_, ?_⟩
  · intro h
    exact hg.infinite_order
      (((MulAut.conj a).injective.isOfFinOrder_iff
        (f := (MulAut.conj a).toMonoidHom)).mp h)
  · change (a * g * a⁻¹) • (a • ξ) = a • ξ
    rw [mul_smul, inv_smul_smul, mul_smul, hfix]
  · intro η hη
    change (a * g * a⁻¹) • η = η at hη
    change η = a • ξ
    have he : g • (a⁻¹ • η) = a⁻¹ • η := by
      have h := congrArg (fun ζ : BoundaryH n => a⁻¹ • ζ) hη
      simpa only [mul_smul, inv_smul_smul] using h
    have h := congrArg (fun ζ : BoundaryH n => a • ζ) (hg.unique _ he)
    simpa only [smul_inv_smul] using h

theorem IsParabolicAt.pow {hn : 1 ≤ n} {g : PO n 1} {ξ : BoundaryH n}
    (hg : IsParabolicAt hn g ξ) (Γ : Subgroup (PO n 1))
    (hΓ : IsDiscrete (SetLike.coe Γ)) (hgΓ : g ∈ Γ) {k : ℕ} (hk : k ≠ 0) :
    IsParabolicAt hn (g ^ k) ξ := by
  have hfix := boundary_pow_fixed hn g ξ hg.fix k
  have hscale : poConfFactor hn (g ^ k) ξ = 1 := by
    rw [poConfFactor_pow_of_fixed hn g ξ hg.fix, hg.scale_one, one_pow]
  refine ⟨fun h => hg.infinite_order (h.of_pow hk), hfix, ?_⟩
  intro η hη
  by_contra hne
  have hfin := isOfFinOrder_of_interior_fixed hn Γ hΓ ⟨g ^ k, Γ.pow_mem hgΓ k⟩ _
    (smul_boundaryPairPoint_of_two_fixed_scale_one hn (g ^ k) (Ne.symm hne) hfix hη hscale)
  exact hg.infinite_order (hfin.of_pow hk)

theorem IsParabolicAt.not_preserves_pair {hn : 1 ≤ n} {g : PO n 1} {ξ : BoundaryH n}
    (hg : IsParabolicAt hn g ξ) (Γ : Subgroup (PO n 1))
    (hΓ : IsDiscrete (SetLike.coe Γ)) (hgΓ : g ∈ Γ)
    {u v : BoundaryH n} (huv : u ≠ v) :
    ¬((poBoundaryMulAction hn).smul g u ∈ ({u, v} : Set (BoundaryH n)) ∧
      (poBoundaryMulAction hn).smul g v ∈ ({u, v} : Set (BoundaryH n))) := by
  let := poBoundaryMulAction hn
  intro hp
  change g • u ∈ ({u, v} : Set (BoundaryH n)) ∧
    g • v ∈ ({u, v} : Set (BoundaryH n)) at hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  have hpow := hg.pow Γ hΓ hgΓ (k := 2) (by decide)
  have hgu : g ^ 2 • u = u := by
    rcases hp.1 with hu | hu
    · rw [pow_two, mul_smul, hu, hu]
    · rcases hp.2 with hv | hv
      · rw [pow_two, mul_smul, hu, hv]
      · exact (huv ((MulAction.toPerm g).injective (hu.trans hv.symm))).elim
  have hgv : g ^ 2 • v = v := by
    rcases hp.2 with hv | hv
    · rcases hp.1 with hu | hu
      · exact (huv ((MulAction.toPerm g).injective (hu.trans hv.symm))).elim
      · rw [pow_two, mul_smul, hv, hu]
    · rw [pow_two, mul_smul, hv, hv]
  exact huv ((hpow.unique u hgu).trans (hpow.unique v hgv).symm)

theorem horospherical_of_contains_parabolic (hn : 1 ≤ n) (D : Subgroup (PO n 1))
    (hD : IsDiscrete (SetLike.coe D)) (hgeom : ElementaryGeometry hn D)
    {ξ : BoundaryH n} (g : D) (hg : IsParabolicAt hn (g : PO n 1) ξ) :
    ∀ a : D, (poBoundaryMulAction hn).smul (a : PO n 1) ξ = ξ ∧
      poConfFactor hn (a : PO n 1) ξ = 1 := by
  rcases hgeom with ⟨hfinite, _⟩ | ⟨u, v, huv, hp⟩ | ⟨ζ, hζ⟩
  · let := hfinite
    exact (hg.infinite_order (D.subtype.isOfFinOrder (isOfFinOrder_of_finite g))).elim
  · exact (hg.not_preserves_pair D hD g.property huv (hp g)).elim
  · have he : ζ = ξ := hg.unique ζ (hζ g).1
    simpa only [he] using hζ

theorem smallSubgroup_horospherical (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (hΓ : IsDiscrete (SetLike.coe Γ)) (ε : ℝ) (x : HUpper n)
    (hgeom : ElementaryGeometry hn (Margulis.smallSubgroup hn Γ ε x))
    {ξ : BoundaryH n} (g : Γ) (hg : IsParabolicAt hn (g : PO n 1) ξ)
    (hshort : dist ((poMulAction hn).smul (g : PO n 1) x) x < ε) :
    ∀ a : Margulis.smallSubgroup hn Γ ε x,
      (poBoundaryMulAction hn).smul (a : PO n 1) ξ = ξ ∧
        poConfFactor hn (a : PO n 1) ξ = 1 :=
  horospherical_of_contains_parabolic hn _
    (hΓ.mono (Margulis.smallSubgroup_le hn Γ ε x)) hgeom
    ⟨g, Subgroup.subset_closure ⟨g.property, hshort⟩⟩ hg

def region (hn : 1 ≤ n) (Γ : Subgroup (PO n 1)) (ε : ℝ) (ξ : BoundaryH n) :
    Set (HUpper n) :=
  {x | ∃ g : Γ, IsParabolicAt hn (g : PO n 1) ξ ∧
    dist ((poMulAction hn).smul (g : PO n 1) x) x < ε}

theorem region_mono (hn : 1 ≤ n) (Γ : Subgroup (PO n 1)) {r ε : ℝ}
    (hr : r ≤ ε) (ξ : BoundaryH n) :
    region hn Γ r ξ ⊆ region hn Γ ε ξ := by
  rintro x ⟨g, hg, hx⟩
  exact ⟨g, hg, hx.trans_le hr⟩

theorem region_subset_compl_thickPart (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (ε : ℝ) (ξ : BoundaryH n) :
    region hn Γ ε ξ ⊆ (LatticeCompactness.thickPart hn Γ ε)ᶜ := by
  rintro x ⟨g, hg, hx⟩ hthick
  have hne : g ≠ 1 := fun h => hg.ne_one (congrArg Subtype.val h)
  have hle := hthick g hne
  rw [dist_comm] at hle
  exact (not_lt_of_ge hle) hx

theorem isOpen_region (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (ε : ℝ) (ξ : BoundaryH n) : IsOpen (region hn Γ ε ξ) := by
  have he : region hn Γ ε ξ = ⋃ g : Γ, ⋃ (_ : IsParabolicAt hn (g : PO n 1) ξ),
      {x : HUpper n | dist x ((poMulAction hn).smul (g : PO n 1) x) < ε} := by
    ext x
    simp only [region, mem_ofPred_eq, mem_iUnion, dist_comm x, exists_prop]
  rw [he]
  exact isOpen_iUnion fun g => isOpen_iUnion fun _ =>
    isOpen_lt (LatticeCompactness.continuous_displacement hn g) continuous_const

theorem center_eq_of_mem_regions (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (hΓ : IsDiscrete (SetLike.coe Γ)) (ε : ℝ)
    (hgeom : ∀ x : HUpper n, ElementaryGeometry hn (Margulis.smallSubgroup hn Γ ε x))
    {ξ η : BoundaryH n} {x : HUpper n}
    (hx : x ∈ region hn Γ ε ξ) (hy : x ∈ region hn Γ ε η) : ξ = η := by
  obtain ⟨g, hg, hgx⟩ := hx
  obtain ⟨a, ha, hax⟩ := hy
  have hfix := smallSubgroup_horospherical hn Γ hΓ ε x (hgeom x) g hg hgx
    ⟨a, Subgroup.subset_closure ⟨a.property, hax⟩⟩
  exact ha.unique ξ hfix.1

theorem disjoint_regions (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (hΓ : IsDiscrete (SetLike.coe Γ)) (ε : ℝ)
    (hgeom : ∀ x : HUpper n, ElementaryGeometry hn (Margulis.smallSubgroup hn Γ ε x))
    {ξ η : BoundaryH n} (hne : ξ ≠ η) :
    Disjoint (region hn Γ ε ξ) (region hn Γ ε η) :=
  Set.disjoint_left.mpr fun _ hx hy => hne (center_eq_of_mem_regions hn Γ hΓ ε hgeom hx hy)

theorem smul_mem_region (hn : 1 ≤ n) (Γ : Subgroup (PO n 1)) (ε : ℝ)
    {ξ : BoundaryH n} {x : HUpper n} (hx : x ∈ region hn Γ ε ξ) (δ : Γ) :
    (poMulAction hn).smul (δ : PO n 1) x ∈
      region hn Γ ε ((poBoundaryMulAction hn).smul (δ : PO n 1) ξ) := by
  let := poMulAction hn
  obtain ⟨g, hg, hgx⟩ := hx
  refine ⟨δ * g * δ⁻¹, hg.conj δ, ?_⟩
  change dist (((δ : PO n 1) * (g : PO n 1) * (δ : PO n 1)⁻¹) •
    ((δ : PO n 1) • x)) ((δ : PO n 1) • x) < ε
  rw [mul_smul, inv_smul_smul, mul_smul, po_dist_smul hn]
  exact hgx

theorem image_region (hn : 1 ≤ n) (Γ : Subgroup (PO n 1)) (ε : ℝ)
    (ξ : BoundaryH n) (δ : Γ) :
    (fun x : HUpper n => (poMulAction hn).smul (δ : PO n 1) x) '' region hn Γ ε ξ =
      region hn Γ ε ((poBoundaryMulAction hn).smul (δ : PO n 1) ξ) := by
  let := poMulAction hn
  let := poBoundaryMulAction hn
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact smul_mem_region hn Γ ε hx δ
  · intro x hx
    have hi := smul_mem_region hn Γ ε hx δ⁻¹
    change (δ : PO n 1)⁻¹ • x ∈ region hn Γ ε
      ((δ : PO n 1)⁻¹ • ((δ : PO n 1) • ξ)) at hi
    rw [inv_smul_smul] at hi
    exact ⟨(δ : PO n 1)⁻¹ • x, hi, smul_inv_smul _ _⟩

theorem precisely_invariant_region (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (hΓ : IsDiscrete (SetLike.coe Γ)) (ε : ℝ)
    (hgeom : ∀ x : HUpper n, ElementaryGeometry hn (Margulis.smallSubgroup hn Γ ε x))
    (ξ : BoundaryH n) (δ : Γ) :
    ((poBoundaryMulAction hn).smul (δ : PO n 1) ξ = ξ →
      (fun x : HUpper n => (poMulAction hn).smul (δ : PO n 1) x) '' region hn Γ ε ξ =
        region hn Γ ε ξ) ∧
    ((poBoundaryMulAction hn).smul (δ : PO n 1) ξ ≠ ξ →
      Disjoint
        ((fun x : HUpper n => (poMulAction hn).smul (δ : PO n 1) x) '' region hn Γ ε ξ)
        (region hn Γ ε ξ)) := by
  rw [image_region]
  exact ⟨fun h => congrArg (region hn Γ ε) h, disjoint_regions hn Γ hΓ ε hgeom⟩

theorem finite_short_on_compact (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (hΓ : IsDiscrete (SetLike.coe Γ)) (r : ℝ)
    {K : Set (HUpper n)} (hK : IsCompact K) :
    {g : Γ | ∃ x ∈ K, dist ((poMulAction hn).smul (g : PO n 1) x) x ≤ r}.Finite := by
  let := poMulAction hn
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall basepointH
  apply (DirichletDomain.finite_setOf_coe_le hn Γ hΓ (2 * R + r)).subset
  rintro g ⟨x, hx, hshort⟩
  have hxR : dist x basepointH ≤ R := Metric.mem_closedBall.mp (hR hx)
  have h1 := dist_triangle ((g : PO n 1) • basepointH) ((g : PO n 1) • x) basepointH
  have h2 := dist_triangle ((g : PO n 1) • x) x basepointH
  rw [po_dist_smul hn, dist_comm basepointH x] at h1
  change dist ((g : PO n 1) • x) x ≤ r at hshort
  change dist ((g : PO n 1) • basepointH) basepointH ≤ 2 * R + r
  linarith

theorem locallyFinite_displacement_sublevels (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (hΓ : IsDiscrete (SetLike.coe Γ)) (r : ℝ) :
    LocallyFinite (fun g : Γ =>
      {x : HUpper n | dist ((poMulAction hn).smul (g : PO n 1) x) x ≤ r}) := by
  intro x
  refine ⟨Metric.ball x 1, Metric.ball_mem_nhds x zero_lt_one, ?_⟩
  apply (finite_short_on_compact hn Γ hΓ r (isCompact_closedBall x 1)).subset
  rintro g ⟨y, hy, hyball⟩
  exact ⟨y, Metric.ball_subset_closedBall hyball, hy⟩

def closedRegion (hn : 1 ≤ n) (Γ : Subgroup (PO n 1)) (r : ℝ) (ξ : BoundaryH n) :
    Set (HUpper n) :=
  {x | ∃ g : Γ, IsParabolicAt hn (g : PO n 1) ξ ∧
    dist ((poMulAction hn).smul (g : PO n 1) x) x ≤ r}

theorem isClosed_closedRegion (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (hΓ : IsDiscrete (SetLike.coe Γ)) (r : ℝ) (ξ : BoundaryH n) :
    IsClosed (closedRegion hn Γ r ξ) := by
  let P := {g : Γ // IsParabolicAt hn (g : PO n 1) ξ}
  have he : closedRegion hn Γ r ξ = ⋃ g : P,
      {x : HUpper n | dist ((poMulAction hn).smul ((g : Γ) : PO n 1) x) x ≤ r} := by
    ext x
    simp only [closedRegion, mem_ofPred_eq, mem_iUnion]
    exact ⟨fun ⟨g, hg, hx⟩ => ⟨⟨g, hg⟩, hx⟩,
      fun ⟨g, hx⟩ => ⟨g, g.property, hx⟩⟩
  rw [he]
  apply ((locallyFinite_displacement_sublevels hn Γ hΓ r).comp_injective
    (Subtype.val_injective (p := fun g : Γ => IsParabolicAt hn (g : PO n 1) ξ))).isClosed_iUnion
  intro g
  have hc := LatticeCompactness.continuous_displacement hn ((g : Γ) : PO n 1)
  have hc' : Continuous (fun x : HUpper n =>
      dist ((poMulAction hn).smul ((g : Γ) : PO n 1) x) x) := by
    simpa only [dist_comm] using hc
  exact isClosed_le hc' continuous_const

theorem closure_region_subset_closedRegion (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (hΓ : IsDiscrete (SetLike.coe Γ)) (r : ℝ) (ξ : BoundaryH n) :
    closure (region hn Γ r ξ) ⊆ closedRegion hn Γ r ξ :=
  (isClosed_closedRegion hn Γ hΓ r ξ).closure_subset_iff.mpr
    (fun _ ⟨g, hg, hx⟩ => ⟨g, hg, hx.le⟩)

theorem closedRegion_subset_region (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    {r ε : ℝ} (hr : r < ε) (ξ : BoundaryH n) :
    closedRegion hn Γ r ξ ⊆ region hn Γ ε ξ :=
  fun _ ⟨g, hg, hx⟩ => ⟨g, hg, hx.trans_lt hr⟩

theorem disjoint_closure_regions (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (hΓ : IsDiscrete (SetLike.coe Γ)) {r ε : ℝ} (hr : r < ε)
    (hgeom : ∀ x : HUpper n, ElementaryGeometry hn (Margulis.smallSubgroup hn Γ ε x))
    {ξ η : BoundaryH n} (hne : ξ ≠ η) :
    Disjoint (closure (region hn Γ r ξ)) (closure (region hn Γ r η)) :=
  (disjoint_regions hn Γ hΓ ε hgeom hne).mono
    ((closure_region_subset_closedRegion hn Γ hΓ r ξ).trans
      (closedRegion_subset_region hn Γ hr ξ))
    ((closure_region_subset_closedRegion hn Γ hΓ r η).trans
      (closedRegion_subset_region hn Γ hr η))

theorem finite_centers_meeting_compact (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (hΓ : IsDiscrete (SetLike.coe Γ)) (r : ℝ)
    {K : Set (HUpper n)} (hK : IsCompact K) :
    {ξ : BoundaryH n | (closedRegion hn Γ r ξ ∩ K).Nonempty}.Finite := by
  let S : Set Γ :=
    {g | ∃ x ∈ K, dist ((poMulAction hn).smul (g : PO n 1) x) x ≤ r}
  have hS : S.Finite := finite_short_on_compact hn Γ hΓ r hK
  have hcenter (g : Γ) : {ξ : BoundaryH n | IsParabolicAt hn (g : PO n 1) ξ}.Finite := by
    apply Set.Subsingleton.finite
    intro ξ hξ η hη
    exact hη.unique ξ hξ.fix
  apply (hS.biUnion (fun g _ => hcenter g)).subset
  rintro ξ ⟨x, ⟨g, hg, hx⟩, hxK⟩
  exact Set.mem_iUnion₂.mpr ⟨g, ⟨x, hxK, hx⟩, hg⟩

theorem locallyFinite_closedRegion (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (hΓ : IsDiscrete (SetLike.coe Γ)) (r : ℝ) :
    LocallyFinite (closedRegion hn Γ r) := by
  intro x
  refine ⟨Metric.ball x 1, Metric.ball_mem_nhds x zero_lt_one, ?_⟩
  apply (finite_centers_meeting_compact hn Γ hΓ r (isCompact_closedBall x 1)).subset
  rintro ξ ⟨y, hy, hyball⟩
  exact ⟨y, hy, Metric.ball_subset_closedBall hyball⟩

theorem locallyFinite_region (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (hΓ : IsDiscrete (SetLike.coe Γ)) (r : ℝ) : LocallyFinite (region hn Γ r) :=
  (locallyFinite_closedRegion hn Γ hΓ r).subset
    (fun _ _ ⟨g, hg, hx⟩ => ⟨g, hg, hx.le⟩)

theorem cosh_displacement_rayTo_sub_one (hn : 1 ≤ n) (g : PO n 1) (ξ : BoundaryH n)
    (hfix : (poBoundaryMulAction hn).smul g ξ = ξ)
    (hscale : poConfFactor hn g ξ = 1) (p : HUpper n) (t : ℝ) :
    Real.cosh (dist ((poMulAction hn).smul g (rayTo p ξ t)) (rayTo p ξ t)) - 1 =
      (Real.cosh (dist ((poMulAction hn).smul g p) p) - 1) * Real.exp (-(2 * t)) := by
  let p' : HUpper n := (poMulAction hn).smul g p
  have hb : Busemann.busemann ξ p' = Busemann.busemann ξ p := by
    have h := po_busemann_smul hn g ξ p
    simpa only [hfix, hscale, Real.log_one, sub_zero] using h
  have hpair : lorB p'.val ξ.val = lorB p.val ξ.val := by
    have h := congrArg Real.exp hb
    change Real.exp (Real.log (-lorB p'.val ξ.val)) =
      Real.exp (Real.log (-lorB p.val ξ.val)) at h
    rw [Real.exp_log (Busemann.neg_lorB_upper_boundary_pos p' ξ),
      Real.exp_log (Busemann.neg_lorB_upper_boundary_pos p ξ)] at h
    exact neg_injective h
  have he := BoundaryExtension.po_smul_rayTo hn g p ξ t
  change (poMulAction hn).smul g (rayTo p ξ t) =
    rayTo ((poMulAction hn).smul g p) ((poBoundaryMulAction hn).smul g ξ) t at he
  rw [hfix] at he
  change lorB ((poMulAction hn).smul g p).val ξ.val = lorB p.val ξ.val at hpair
  rw [he, cosh_dist_rayTo_rayTo, hpair,
    div_self (lorB_hUpper_boundary_neg p ξ).ne]
  have hE : (Real.cosh t - Real.sinh t) ^ 2 = Real.exp (-(2 * t)) := by
    rw [cosh_sub_sinh, pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hE, HyperbolicConvexity.cosh_dist]
  ring

theorem displacement_rayTo_le (hn : 1 ≤ n) (g : PO n 1) (ξ : BoundaryH n)
    (hfix : (poBoundaryMulAction hn).smul g ξ = ξ)
    (hscale : poConfFactor hn g ξ = 1) (p : HUpper n) {t : ℝ} (ht : 0 ≤ t) :
    dist ((poMulAction hn).smul g (rayTo p ξ t)) (rayTo p ξ t) ≤
      dist ((poMulAction hn).smul g p) p := by
  have h := cosh_displacement_rayTo_sub_one hn g ξ hfix hscale p t
  have hE : Real.exp (-(2 * t)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hC : 0 ≤ Real.cosh (dist ((poMulAction hn).smul g p) p) - 1 :=
    sub_nonneg.mpr (Real.one_le_cosh _)
  have hle := mul_le_mul_of_nonneg_left hE hC
  have hc : Real.cosh (dist ((poMulAction hn).smul g (rayTo p ξ t)) (rayTo p ξ t)) ≤
      Real.cosh (dist ((poMulAction hn).smul g p) p) := by linarith
  simpa only [abs_of_nonneg dist_nonneg] using Real.cosh_le_cosh.mp hc

theorem tendsto_displacement_rayTo (hn : 1 ≤ n) (g : PO n 1) (ξ : BoundaryH n)
    (hfix : (poBoundaryMulAction hn).smul g ξ = ξ)
    (hscale : poConfFactor hn g ξ = 1) (p : HUpper n) :
    Tendsto (fun t : ℝ => dist ((poMulAction hn).smul g (rayTo p ξ t)) (rayTo p ξ t))
      atTop (𝓝 0) := by
  have hE : Tendsto (fun t : ℝ => Real.exp (-(2 * t))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop (by norm_num))
  have hc : Tendsto
      (fun t : ℝ => Real.cosh (dist ((poMulAction hn).smul g (rayTo p ξ t)) (rayTo p ξ t)))
      atTop (𝓝 1) := by
    have h := (hE.const_mul (Real.cosh (dist ((poMulAction hn).smul g p) p) - 1)).const_add 1
    have h' : Tendsto (fun t : ℝ => 1 +
        (Real.cosh (dist ((poMulAction hn).smul g p) p) - 1) * Real.exp (-(2 * t)))
        atTop (𝓝 1) := by simpa only [mul_zero, add_zero] using h
    apply h'.congr
    intro t
    linarith [cosh_displacement_rayTo_sub_one hn g ξ hfix hscale p t]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hcε : 1 < Real.cosh ε := by
    have h : Real.cosh 0 < Real.cosh ε :=
      Real.cosh_lt_cosh.mpr (by simpa only [abs_zero, abs_of_pos hε] using hε)
    simpa only [Real.cosh_zero] using h
  filter_upwards [hc.eventually (Iio_mem_nhds hcε)] with t ht
  have hlt := Real.cosh_lt_cosh.mp ht
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg, abs_of_pos hε] using hlt

theorem rayTo_mem_region (hn : 1 ≤ n) (Γ : Subgroup (PO n 1)) (ε : ℝ)
    {ξ : BoundaryH n} {x : HUpper n} (hx : x ∈ region hn Γ ε ξ)
    {t : ℝ} (ht : 0 ≤ t) : rayTo x ξ t ∈ region hn Γ ε ξ := by
  obtain ⟨g, hg, hx⟩ := hx
  exact ⟨g, hg, (displacement_rayTo_le hn g ξ hg.fix hg.scale_one x ht).trans_lt hx⟩

theorem eventually_rayTo_mem_region (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    {ε : ℝ} (hε : 0 < ε) {ξ : BoundaryH n} (g : Γ)
    (hg : IsParabolicAt hn (g : PO n 1) ξ) (p : HUpper n) :
    ∀ᶠ t : ℝ in atTop, rayTo p ξ t ∈ region hn Γ ε ξ := by
  filter_upwards [(tendsto_displacement_rayTo hn g ξ hg.fix hg.scale_one p).eventually
    (Iio_mem_nhds hε)] with t ht
  exact ⟨g, hg, ht⟩

theorem region_nonempty (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    {ε : ℝ} (hε : 0 < ε) {ξ : BoundaryH n} (g : Γ)
    (hg : IsParabolicAt hn (g : PO n 1) ξ) : (region hn Γ ε ξ).Nonempty := by
  obtain ⟨t, ht⟩ := (eventually_rayTo_mem_region hn Γ hε g hg basepointH).exists
  exact ⟨rayTo basepointH ξ t, ht⟩

theorem virtuallyNilpotent_of_fg_horospherical (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (hΓ : IsDiscrete (SetLike.coe Γ)) [Group.FG Γ] (ξ : BoundaryH n)
    (hfix : ∀ g : Γ, (poBoundaryMulAction hn).smul (g : PO n 1) ξ = ξ ∧
      poConfFactor hn (g : PO n 1) ξ = 1) :
    Group.IsVirtuallyNilpotent Γ := by
  obtain ⟨ε, hε, hMargulis⟩ := Margulis.exists_margulis_constant hn
  obtain ⟨S, hgen, hS⟩ :=
    (Subgroup.fg_iff Γ).mp ((Group.fg_iff_subgroup_fg Γ).mp inferInstance)
  have hSΓ : S ⊆ Γ := fun g hg => hgen ▸ Subgroup.subset_closure hg
  have hshort : ∀ᶠ t : ℝ in atTop, ∀ g ∈ S,
      dist ((poMulAction hn).smul g (rayTo basepointH ξ t)) (rayTo basepointH ξ t) < ε := by
    apply hS.eventually_all.mpr
    intro g hg
    exact (tendsto_displacement_rayTo hn g ξ (hfix ⟨g, hSΓ hg⟩).1
      (hfix ⟨g, hSΓ hg⟩).2 basepointH).eventually (Iio_mem_nhds hε)
  obtain ⟨t, ht⟩ := hshort.exists
  have heq : Margulis.smallSubgroup hn Γ ε (rayTo basepointH ξ t) = Γ := by
    apply le_antisymm (Margulis.smallSubgroup_le hn Γ ε _)
    calc
      Γ = Subgroup.closure S := hgen.symm
      _ ≤ Margulis.smallSubgroup hn Γ ε (rayTo basepointH ξ t) := by
        apply (Subgroup.closure_le _).mpr
        intro g hg
        exact Subgroup.subset_closure ⟨hSΓ hg, ht g hg⟩
  have h := hMargulis Γ hΓ (rayTo basepointH ξ t)
  rwa [heq] at h

end DifferentialGeometry.ParabolicRegions
