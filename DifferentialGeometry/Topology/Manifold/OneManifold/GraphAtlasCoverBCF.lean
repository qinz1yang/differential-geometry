import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Topology.Instances.Real.Lemmas
import DifferentialGeometry.Topology.Maps.RelativeInteriorRemoval

/-!
# The shared `K₃` kernel, part (K-a): one-dimensional bases in graph-chart form and a finite
chart-interval cover with coverage and regularity (lane B-BCF134; ZSP04 / BCF01-G1)

Blueprint `master207B.tex`, ZSP04 (B:6531–6595) and BCF01 (B:9642–9716): "Use finitely many
relatively compact coordinate intervals, enlarge them slightly with endpoints avoiding `∂D₃`, and
take their union". Lead decision 14:4x: one generic kernel for the closed (C14-ZSP35c) and the
boundary (B-BCF134) bindings; the base is given in GRAPH-CHART form (closed `slimBase_chart_BAS`).

* `GraphAtlas1_BCF ι Bs`: charts `j : ι` with a continuous LINEAR coordinate `coord j : H →L[ℝ] ℝ`,
  a smooth parametrization `param j : ℝ → H` on an open `dom j ⊆ ℝ`, `coord j ∘ param j = id` on
  `dom j`, every piece `param j '' dom j` relatively open in `Bs`, and the pieces covering `Bs`.
* `GraphAtlas1_BCF.image_relOpen_BCF`: `param j '' O` is relatively open in `Bs` for open
  `O ⊆ dom j`.
* `GraphAtlas1_BCF.exists_interval_cover_BCF`: a compact `Kset ⊆ Bs` is covered by the images of
  finitely many open chart intervals `(a r, b r)` with `[a r, b r] ⊆ dom (c r)` and endpoints
  outside a prescribed finite set `Fset` (the face points `∂D₃`).
* `GraphAtlas1_BCF.cover_union_spec_BCF` (K-a): for such a cover,
  `K' = ⋃_r param (c r) '' [a r, b r]` is compact, lies in `Bs`, contains `Kset` in its relative
  interior, and `K' ∩ Dset` is regular in `Bs` (every point is a limit of relative interior points)
  whenever `Dset ⊆ cl(int_{Bs} Dset)` and the relative frontier `Dset \ int_{Bs} Dset` lies in
  `Kset`.

Part (K-b) (merging `K'` into finitely many disjoint smooth arcs and loops) is the next package.
Relative interiors are written `Subtype.val '' interior (Subtype.val ⁻¹' Z : Set Y)` (the same term
as the boundary route's `relInterior_BIF Y Z`).
-/

set_option autoImplicit false

open Set Function Filter Topology
open scoped ContDiff

namespace DifferentialGeometry.Topology

/-- **A one-dimensional base in graph-chart form**: charts indexed by `ι`, each a smooth
parametrization `param j` of a relatively open piece of `Bs` on an open `dom j ⊆ ℝ` with a
continuous linear left inverse `coord j`; the pieces cover `Bs`. -/
structure GraphAtlas1_BCF {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] (ι : Type*)
    (Bs : Set H) where
  /-- The linear chart coordinate `κ_j`. -/
  coord : ι → H →L[ℝ] ℝ
  /-- The smooth parametrization `ψ_j`. -/
  param : ι → ℝ → H
  /-- The open parameter domain. -/
  dom : ι → Set ℝ
  isOpen_dom : ∀ j, IsOpen (dom j)
  param_smooth : ∀ j, ContDiffOn ℝ ∞ (param j) (dom j)
  coord_param : ∀ j, ∀ b ∈ dom j, coord j (param j b) = b
  piece_relOpen : ∀ j, ∃ V : Set H, IsOpen V ∧ V ∩ Bs = param j '' dom j
  cover : Bs = ⋃ j, param j '' dom j

namespace GraphAtlas1_BCF

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] {ι : Type*} {Bs : Set H}
  (At : GraphAtlas1_BCF ι Bs)

/-- A chart point lies in `Bs`. -/
theorem param_mem_BCF {j : ι} {b : ℝ} (hb : b ∈ At.dom j) : At.param j b ∈ Bs :=
  (Set.ext_iff.mp At.cover _).mpr (mem_iUnion.mpr ⟨j, b, hb, rfl⟩)

/-- `param j` is continuous on its domain. -/
theorem continuousOn_param_BCF (j : ι) : ContinuousOn (At.param j) (At.dom j) :=
  (At.param_smooth j).continuousOn

/-- **Open chart sets are relatively open**: `param j '' O = V ∩ Bs` for an open `V`. -/
theorem image_relOpen_BCF {j : ι} {O : Set ℝ} (hO : IsOpen O) (hOD : O ⊆ At.dom j) :
    ∃ V : Set H, IsOpen V ∧ V ∩ Bs = At.param j '' O := by
  obtain ⟨V, hV, hVB⟩ := At.piece_relOpen j
  refine ⟨V ∩ At.coord j ⁻¹' O, hV.inter (hO.preimage (At.coord j).continuous), ?_⟩
  ext y
  constructor
  · rintro ⟨⟨hyV, hyO⟩, hyB⟩
    obtain ⟨b, hb, rfl⟩ : y ∈ At.param j '' At.dom j := hVB ▸ ⟨hyV, hyB⟩
    have hcb : At.coord j (At.param j b) = b := At.coord_param j b hb
    exact ⟨b, hcb ▸ hyO, rfl⟩
  · rintro ⟨b, hbO, rfl⟩
    have hmem : At.param j b ∈ V ∩ Bs := hVB ▸ mem_image_of_mem _ (hOD hbO)
    refine ⟨⟨hmem.1, ?_⟩, hmem.2⟩
    change At.coord j (At.param j b) ∈ O
    rw [At.coord_param j b (hOD hbO)]
    exact hbO

/-- An open chart interval lies in the relative interior of the closed one. -/
theorem image_Ioo_subset_relInterior_BCF {j : ι} {a b : ℝ} (hab : Icc a b ⊆ At.dom j)
    {Z : Set H} (hZ : At.param j '' Icc a b ⊆ Z) :
    At.param j '' Ioo a b ⊆ Subtype.val '' interior (Subtype.val ⁻¹' Z : Set Bs) := by
  obtain ⟨V, hV, hVB⟩ := At.image_relOpen_BCF isOpen_Ioo (Ioo_subset_Icc_self.trans hab)
  intro y hy
  have hyVB : y ∈ V ∩ Bs := hVB ▸ hy
  refine mem_image_interior_preimage_val_iff.mpr ⟨hyVB.2, V, hV, hyVB.1, fun z hz => ?_⟩
  obtain ⟨t, ht, rfl⟩ : z ∈ At.param j '' Ioo a b := hVB ▸ hz
  exact hZ ⟨t, Ioo_subset_Icc_self ht, rfl⟩

/-- A closed chart interval has compact image. -/
theorem isCompact_image_Icc_BCF {j : ι} {a b : ℝ} (hab : Icc a b ⊆ At.dom j) :
    IsCompact (At.param j '' Icc a b) :=
  isCompact_Icc.image_of_continuousOn ((At.continuousOn_param_BCF j).mono hab)

/-- The endpoints of a chart interval are limits of its interior points. -/
theorem endpoints_mem_closure_BCF {j : ι} {a b : ℝ} (hlt : a < b) (hab : Icc a b ⊆ At.dom j) :
    At.param j a ∈ closure (At.param j '' Ioo a b) ∧
      At.param j b ∈ closure (At.param j '' Ioo a b) := by
  have hcl : closure (Ioo a b) = Icc a b := closure_Ioo hlt.ne
  have hcont : ContinuousOn (At.param j) (closure (Ioo a b)) :=
    hcl ▸ (At.continuousOn_param_BCF j).mono hab
  have himg := hcont.image_closure
  rw [hcl] at himg
  exact ⟨himg ⟨a, left_mem_Icc.mpr hlt.le, rfl⟩, himg ⟨b, right_mem_Icc.mpr hlt.le, rfl⟩⟩

/-- **Finite chart-interval cover** (ZSP04's base step on the atlas): a compact `Kset ⊆ Bs` is
covered by the images of finitely many open chart intervals with closures in the domains and
endpoints outside a finite set `Fset`. -/
theorem exists_interval_cover_BCF {Kset Fset : Set H} (hK : IsCompact Kset) (hKB : Kset ⊆ Bs)
    (hF : Fset.Finite) :
    ∃ (n : ℕ) (c : Fin n → ι) (a b : Fin n → ℝ),
      (∀ r, a r < b r ∧ Icc (a r) (b r) ⊆ At.dom (c r) ∧ At.param (c r) (a r) ∉ Fset ∧
        At.param (c r) (b r) ∉ Fset) ∧
      Kset ⊆ ⋃ r, At.param (c r) '' Ioo (a r) (b r) := by
  have hloc : ∀ y : Kset, ∃ q : ι × ℝ × ℝ, (q.2.1 < q.2.2 ∧ Icc q.2.1 q.2.2 ⊆ At.dom q.1 ∧
      At.param q.1 q.2.1 ∉ Fset ∧ At.param q.1 q.2.2 ∉ Fset) ∧
      (y : H) ∈ At.param q.1 '' Ioo q.2.1 q.2.2 := by
    rintro ⟨y, hy⟩
    obtain ⟨j, b₀, hb₀, rfl⟩ : ∃ j, ∃ b₀ ∈ At.dom j, At.param j b₀ = y := by
      have h1 : y ∈ ⋃ j, At.param j '' At.dom j := (Set.ext_iff.mp At.cover y).mp (hKB hy)
      obtain ⟨j, hj⟩ := mem_iUnion.mp h1
      exact ⟨j, hj⟩
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (At.isOpen_dom j) b₀ hb₀
    have hFc : (At.coord j '' Fset).Finite := hF.image _
    obtain ⟨a, ⟨ha1, ha2⟩, haF⟩ :=
      ((Set.Ioo_infinite (by linarith : b₀ - ε / 2 < b₀)).sdiff hFc).nonempty
    obtain ⟨b, ⟨hb1, hb2⟩, hbF⟩ :=
      ((Set.Ioo_infinite (by linarith : b₀ < b₀ + ε / 2)).sdiff hFc).nonempty
    have hsub : Icc a b ⊆ At.dom j := fun t ht => hball (by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [ht.1, ht.2])
    refine ⟨(j, a, b), ⟨by simp only; linarith, hsub, fun hmem => haF ?_, fun hmem => hbF ?_⟩,
      b₀, ⟨ha2, hb1⟩, rfl⟩
    · exact ⟨_, hmem, At.coord_param j a (hsub (left_mem_Icc.mpr (by linarith)))⟩
    · exact ⟨_, hmem, At.coord_param j b (hsub (right_mem_Icc.mpr (by linarith)))⟩
  choose q hq hyq using hloc
  have hopen : ∀ y : Kset, ∃ V : Set H, IsOpen V ∧
      V ∩ Bs = At.param (q y).1 '' Ioo (q y).2.1 (q y).2.2 :=
    fun y => At.image_relOpen_BCF isOpen_Ioo (Ioo_subset_Icc_self.trans (hq y).2.1)
  choose V hV hVB using hopen
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun y : Kset => V y) (fun y => hV y)
    (fun y hy => mem_iUnion.mpr ⟨⟨y, hy⟩, ((hVB ⟨y, hy⟩).symm ▸ hyq ⟨y, hy⟩ : y ∈ _ ∩ Bs).1⟩)
  classical
  let e := t.equivFin
  refine ⟨t.card, fun r => (q (e.symm r).1).1, fun r => (q (e.symm r).1).2.1,
    fun r => (q (e.symm r).1).2.2, fun r => hq _, fun y hy => ?_⟩
  obtain ⟨z, hzt, hyz⟩ := mem_iUnion₂.mp (ht hy)
  refine mem_iUnion.mpr ⟨e ⟨z, hzt⟩, ?_⟩
  simp only [Equiv.symm_apply_apply]
  exact hVB z ▸ ⟨hyz, hKB hy⟩

/-- **(K-a) Coverage and regularity of the union of closed chart intervals**: for a finite family
of chart intervals whose open images cover `Kset`, the union `K'` of the closed images is compact,
lies in `Bs`, contains `Kset` in its relative interior, and `K' ∩ Dset` is regular in `Bs` when
`Dset` is regular with relative frontier inside `Kset`. -/
theorem cover_union_spec_BCF {n : ℕ} {c : Fin n → ι} {a b : Fin n → ℝ}
    (hab : ∀ r, a r < b r ∧ Icc (a r) (b r) ⊆ At.dom (c r))
    {Kset Dset : Set H} (hKcov : Kset ⊆ ⋃ r, At.param (c r) '' Ioo (a r) (b r))
    (hDreg : Dset ⊆ closure (Subtype.val '' interior (Subtype.val ⁻¹' Dset : Set Bs)))
    (hKfront : Dset \ Subtype.val '' interior (Subtype.val ⁻¹' Dset : Set Bs) ⊆ Kset) :
    IsCompact (⋃ r, At.param (c r) '' Icc (a r) (b r)) ∧
      (⋃ r, At.param (c r) '' Icc (a r) (b r)) ⊆ Bs ∧
      Kset ⊆ Subtype.val '' interior
        (Subtype.val ⁻¹' (⋃ r, At.param (c r) '' Icc (a r) (b r)) : Set Bs) ∧
      (⋃ r, At.param (c r) '' Icc (a r) (b r)) ∩ Dset ⊆ closure (Subtype.val '' interior
        (Subtype.val ⁻¹' ((⋃ r, At.param (c r) '' Icc (a r) (b r)) ∩ Dset) : Set Bs)) := by
  set K' := ⋃ r, At.param (c r) '' Icc (a r) (b r) with hK'
  have hrel : ∀ r, ∃ V : Set H, IsOpen V ∧ V ∩ Bs = At.param (c r) '' Ioo (a r) (b r) :=
    fun r => At.image_relOpen_BCF isOpen_Ioo (Ioo_subset_Icc_self.trans (hab r).2)
  choose V hV hVB using hrel
  have hVK : ∀ r, V r ∩ Bs ⊆ K' := fun r z hz => by
    rw [hVB r] at hz
    obtain ⟨t, ht, rfl⟩ := hz
    exact mem_iUnion.mpr ⟨r, t, Ioo_subset_Icc_self ht, rfl⟩
  -- a point of `V r ∩ Bs` with a relative neighbourhood inside `Dset` is in `int_{Bs}(K' ∩ Dset)`
  have hkey : ∀ r z, z ∈ V r → z ∈ Subtype.val '' interior (Subtype.val ⁻¹' Dset : Set Bs) →
      z ∈ Subtype.val '' interior (Subtype.val ⁻¹' (K' ∩ Dset) : Set Bs) := by
    intro r z hzV hzD
    obtain ⟨hzB, O, hO, hzO, hOD⟩ := mem_image_interior_preimage_val_iff.mp hzD
    exact mem_image_interior_preimage_val_iff.mpr ⟨hzB, V r ∩ O, (hV r).inter hO, ⟨hzV, hzO⟩,
      fun w hw => ⟨hVK r ⟨hw.1.1, hw.2⟩, hOD ⟨hw.1.2, hw.2⟩⟩⟩
  refine ⟨isCompact_iUnion fun r => At.isCompact_image_Icc_BCF (hab r).2, ?_, ?_, ?_⟩
  · refine iUnion_subset fun r => ?_
    rintro _ ⟨t, ht, rfl⟩
    exact At.param_mem_BCF ((hab r).2 ht)
  · intro y hy
    obtain ⟨r, hr⟩ := mem_iUnion.mp (hKcov hy)
    exact At.image_Ioo_subset_relInterior_BCF (hab r).2
      (subset_iUnion (fun r => At.param (c r) '' Icc (a r) (b r)) r) hr
  · rintro y ⟨hyK, hyD⟩
    rw [_root_.mem_closure_iff]
    intro N hN hyN
    by_cases hyU : ∃ r, y ∈ At.param (c r) '' Ioo (a r) (b r)
    · -- interior case: `y ∈ V r`, and `y` is a limit of relative interior points of `Dset`
      obtain ⟨r, hr⟩ := hyU
      have hyV : y ∈ V r := ((hVB r).symm ▸ hr : y ∈ V r ∩ Bs).1
      obtain ⟨z, ⟨hzN, hzV⟩, hzD⟩ :=
        _root_.mem_closure_iff.mp (hDreg hyD) (N ∩ V r) (hN.inter (hV r)) ⟨hyN, hyV⟩
      exact ⟨z, hzN, hkey r z hzV hzD⟩
    · -- endpoint case: `y ∉ Kset`, hence `y ∈ int_{Bs} Dset`, and `y` is a limit of chart points
      have hyKs : y ∉ Kset := fun h => hyU (mem_iUnion.mp (hKcov h))
      have hyD' : y ∈ Subtype.val '' interior (Subtype.val ⁻¹' Dset : Set Bs) := by
        by_contra h
        exact hyKs (hKfront ⟨hyD, h⟩)
      obtain ⟨-, O, hO, hyO, hOD⟩ := mem_image_interior_preimage_val_iff.mp hyD'
      obtain ⟨r, t, ht, rfl⟩ := mem_iUnion.mp hyK
      have hend : t = a r ∨ t = b r := by
        by_contra h
        have h1 : t ≠ a r := fun e => h (Or.inl e)
        have h2 : t ≠ b r := fun e => h (Or.inr e)
        exact hyU ⟨r, t, ⟨lt_of_le_of_ne ht.1 (Ne.symm h1), lt_of_le_of_ne ht.2 h2⟩, rfl⟩
      have hcl : At.param (c r) t ∈ closure (At.param (c r) '' Ioo (a r) (b r)) := by
        rcases hend with rfl | rfl
        · exact (At.endpoints_mem_closure_BCF (hab r).1 (hab r).2).1
        · exact (At.endpoints_mem_closure_BCF (hab r).1 (hab r).2).2
      obtain ⟨z, ⟨hzN, hzO⟩, hzI⟩ :=
        _root_.mem_closure_iff.mp hcl (N ∩ O) (hN.inter hO) ⟨hyN, hyO⟩
      have hzVB : z ∈ V r ∩ Bs := (hVB r).symm ▸ hzI
      exact ⟨z, hzN, hkey r z hzVB.1
        (mem_image_interior_preimage_val_iff.mpr ⟨hzVB.2, O, hO, hzO, hOD⟩)⟩

/-- **(K-a), the kernel's first half in one statement**: a compact `Kset ⊆ Bs`, a finite face set
`Fset` and a regular `Dset ⊆ Bs` with relative frontier in `Kset` admit finitely many closed
chart intervals with endpoints outside `Fset` whose union `K'` is compact, lies in `Bs`, contains
`Kset` in its relative interior, and meets `Dset` in a regular set. -/
theorem exists_cover_union_BCF {Kset Fset Dset : Set H} (hK : IsCompact Kset) (hKB : Kset ⊆ Bs)
    (hF : Fset.Finite)
    (hDreg : Dset ⊆ closure (Subtype.val '' interior (Subtype.val ⁻¹' Dset : Set Bs)))
    (hKfront : Dset \ Subtype.val '' interior (Subtype.val ⁻¹' Dset : Set Bs) ⊆ Kset) :
    ∃ (n : ℕ) (c : Fin n → ι) (a b : Fin n → ℝ),
      (∀ r, a r < b r ∧ Icc (a r) (b r) ⊆ At.dom (c r) ∧ At.param (c r) (a r) ∉ Fset ∧
        At.param (c r) (b r) ∉ Fset) ∧
      IsCompact (⋃ r, At.param (c r) '' Icc (a r) (b r)) ∧
      (⋃ r, At.param (c r) '' Icc (a r) (b r)) ⊆ Bs ∧
      Kset ⊆ Subtype.val '' interior
        (Subtype.val ⁻¹' (⋃ r, At.param (c r) '' Icc (a r) (b r)) : Set Bs) ∧
      (⋃ r, At.param (c r) '' Icc (a r) (b r)) ∩ Dset ⊆ closure (Subtype.val '' interior
        (Subtype.val ⁻¹' ((⋃ r, At.param (c r) '' Icc (a r) (b r)) ∩ Dset) : Set Bs)) := by
  obtain ⟨n, c, a, b, hab, hcov⟩ := At.exists_interval_cover_BCF hK hKB hF
  exact ⟨n, c, a, b, hab,
    At.cover_union_spec_BCF (fun r => ⟨(hab r).1, (hab r).2.1⟩) hcov hDreg hKfront⟩

end GraphAtlas1_BCF

/-- **Inhabitant**: the real line as a one-chart graph atlas of itself. -/
def lineGraphAtlas_BCF : GraphAtlas1_BCF Unit (univ : Set ℝ) where
  coord := fun _ => ContinuousLinearMap.id ℝ ℝ
  param := fun _ => id
  dom := fun _ => univ
  isOpen_dom := fun _ => isOpen_univ
  param_smooth := fun _ => contDiffOn_id
  coord_param := fun _ _ _ => rfl
  piece_relOpen := fun _ => ⟨univ, isOpen_univ, by simp⟩
  cover := by simp [iUnion_const]

end DifferentialGeometry.Topology
