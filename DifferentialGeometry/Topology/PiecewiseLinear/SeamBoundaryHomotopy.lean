/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BoundaryWordWitness

/-!
# The boundary homotopy of the cross seam resolution

`LoopTheorem.CrossSeamResolution` replaces the two bent transverse arcs of the boundary cross
reglue by the two disjoint chords of the cross section square.  Both replacements are
restrictions of a single affine map of the plane,

```
F₊(x, y) = ((x + y + 1) / 2, (x + y - 1) / 2)    F₋(x, y) = ((x + y - 1) / 2, (x + y + 1) / 2)
```

and this file builds the straight line homotopy between the raw and the resolved map, first in
the model and then on the boundary curve of a singular two cell.

## The model homotopy

`crossSeamResolveHomotopy s q = ((1 - s) • p + s • F(p), t)` where `q = (label, (p, t))` runs
over the *source labelled* strips `bentSource`.  Two qualifications are essential.

* It is a homotopy of maps *on the source*, not of the old image figure.  The two source sheets
  have coincident image points before the resolution and different ones after it, which is
  exactly why the branch disappears; a homotopy of the image figure could not do that.  This is
  the reason the model carries the separate labels of `bentSource`.
* It moves a point only inside the cross section disk through it.  `crossSeamResolveHomotopy_snd`
  says the base coordinate never moves, and `crossSeamResolveHomotopy_mem_endDisk` says the
  cross section coordinate stays in the square, both by the convexity of that square and the
  segment containment `segment_crossSeamResolvePos_subset` already proved in the model.

On the four lateral attaching points the two chord maps fix their arguments, so
`crossSeamResolveHomotopy_eq_of_mem_lateral` makes the homotopy *stationary* there.  That is
what lets the model homotopy be glued to the constant homotopy outside the strips.

## The boundary statement

`exists_lift_homotopic_of_crossSeamBoundary` is the global statement.  The raw curve `g` and
the resolved curve `h` are compared over a closed cover `Ω₁ ∪ Ω₂` of the parameter space: on
`Ω₁` both are the transported model maps through a tube chart, on `Ω₂` they agree, on the
overlap the model coordinate is lateral, and on `Ω₁` the base coordinate is `0` or `1`, which
is the hypothesis that the strips meet the source boundary exactly in their two end edges.

The conclusion is a homotopy **in the ambient loop space `X`**, not in the manifold.  This is
the point of the statement and not a formality: the candidate boundary curves already bound
disks in the manifold, so a homotopy there would carry no information for the elimination
step.  The hypothesis that pays for it is `hdisk`, which asks that the two *end disks* of the
tube lie in the image of the inclusion `ρ : X → M`; together with `hγ`, which puts the raw
curve in that image, it covers the whole track of the homotopy, because
`crossSeamResolveHomotopy_mem_endDisk` confines the moving part to the end disks.  The lift is
then unique and continuous because `ρ` is a topological embedding, which is what the inclusion
of a boundary neighbourhood subspace is.  The homotopy is stationary on all of `Ω₂`, including
the overlap with `Ω₁`.

## The producer

`exists_boundaryWordWitness_of_crossSeamBoundary` turns a `BoundaryWordWitness` for the raw
cross reglued cell into one for the resolved cell, over the same combinatorial word.  The raw
cell's own witness is a hypothesis: producing it is a different obligation, and the tree
currently records the boundary of the raw cross reglue only as a two arc word while the
selection step needs a four arc one.

The hypotheses of the producer are exactly the boundary trace of the cross seam normal form.
Four of them are field for field the content of `CrossSeamRegluedData`, restricted to the
boundary circle: `domain_eq` gives `hdomain`, `reglued_eq` gives `hraw`, `resolved_eq` gives
`hres` and `eqOn_compl` gives `hrest`.  Three are extra, and are recorded here because
`CrossSeamRegluedData` does not carry them: the continuity of the model coordinate `coord`
(its label component is not determined by the reglued map, precisely because the two sheets
share their image), the closed cover with lateral overlap, and the end edge condition `hends`.

## Non-vacuity

`exists_lift_homotopic_crossSeamExample` instantiates the global statement with the model
cylinder as the ambient loop space.  That space is a *proper* subspace of the model ambient,
`crossSeamExampleSpace_ne_univ`, so the instance does not degenerate to the ambient being the
model itself; the raw and resolved curves really differ, `crossSeamExampleRaw_ne_resolved`, so
the homotopy really moves; and the overlap of the closed cover is a nonempty subset of the
parameter space, so the lateral clause is not vacuous either.
`exists_lift_homotopic_crossSeamLoopExample` is the same instance over `loopCircle`, so that
what is produced is an honest `freeLoop` of a proper ambient loop space, which is the object
that `BoundaryWordWitness` stores.

The cell level producer is *not* instantiated: a `SingularTwoCell` pair in cross seam normal
form is exactly what `IsCrossSeamTubeProducer` is missing, and that statement is explicitly
unproved in `LoopTheorem.CrossSeamTube`.  Nothing else stands between the two.
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u v w

/-! ### Continuity of the model chord maps -/

/-- The first chord map is continuous, being affine. -/
theorem continuous_crossSeamChordPos : Continuous crossSeamChordPos := by
  unfold crossSeamChordPos
  exact (((continuous_fst.add continuous_snd).add continuous_const).div_const 2).prodMk
    (((continuous_fst.add continuous_snd).sub continuous_const).div_const 2)

/-- The second chord map is continuous, being affine. -/
theorem continuous_crossSeamChordNeg : Continuous crossSeamChordNeg := by
  unfold crossSeamChordNeg
  exact (((continuous_fst.add continuous_snd).sub continuous_const).div_const 2).prodMk
    (((continuous_fst.add continuous_snd).add continuous_const).div_const 2)

/-- The fiberwise resolution of the first seam is continuous. -/
theorem continuous_crossSeamResolvePos : Continuous crossSeamResolvePos := by
  unfold crossSeamResolvePos
  exact continuous_crossSeamChordPos.prodMap continuous_id

/-- The fiberwise resolution of the second seam is continuous. -/
theorem continuous_crossSeamResolveNeg : Continuous crossSeamResolveNeg := by
  unfold crossSeamResolveNeg
  exact continuous_crossSeamChordNeg.prodMap continuous_id

/-- **The resolved map of the model is continuous.**  The source label runs over `Bool`, which
is discrete, so the two label sheets form a closed cover of the source on each part of which
the resolved map is one of the two fiberwise resolutions. -/
theorem continuous_crossSeamResolve : Continuous crossSeamResolve := by
  have hcover : (({true} : Set Bool) ×ˢ (univ : Set ((ℝ × ℝ) × ℝ))) ∪
      (({false} : Set Bool) ×ˢ (univ : Set ((ℝ × ℝ) × ℝ))) = univ := by
    ext ⟨b, x⟩
    cases b <;> simp
  rw [← continuousOn_univ, ← hcover]
  refine ContinuousOn.union_of_isClosed ?_ ?_ ((isClosed_discrete _).prod isClosed_univ)
    ((isClosed_discrete _).prod isClosed_univ)
  · refine ContinuousOn.congr
      (f := fun q : Bool × ((ℝ × ℝ) × ℝ) => crossSeamResolvePos q.2) ?_ ?_
    · exact (continuous_crossSeamResolvePos.comp continuous_snd).continuousOn
    · rintro ⟨b, x⟩ ⟨hb, -⟩
      rw [Set.mem_singleton_iff] at hb
      subst hb
      exact crossSeamResolve_true x
  · refine ContinuousOn.congr
      (f := fun q : Bool × ((ℝ × ℝ) × ℝ) => crossSeamResolveNeg q.2) ?_ ?_
    · exact (continuous_crossSeamResolveNeg.comp continuous_snd).continuousOn
    · rintro ⟨b, x⟩ ⟨hb, -⟩
      rw [Set.mem_singleton_iff] at hb
      subst hb
      exact crossSeamResolve_false x

/-! ### The straight line homotopy of the model resolution -/

/-- **The model boundary homotopy.**  On each source labelled strip of `bentSource` the point
`(p, t)` travels along the straight segment from `p` to its chord image, at constant base
coordinate `t`.  This is a homotopy of maps on the source, not a deformation of the old image
figure: the two labels are carried along, and it is exactly because the two labelled sheets
separate that the branch is deleted. -/
noncomputable def crossSeamResolveHomotopy (s : ℝ) (q : Bool × ((ℝ × ℝ) × ℝ)) : (ℝ × ℝ) × ℝ :=
  ((1 - s) • q.2.1 + s • (crossSeamResolve q).1, q.2.2)

/-- The base coordinate never moves: the homotopy is fiberwise over the base interval of the
tube, so a boundary point stays in its own cross section disk. -/
theorem crossSeamResolveHomotopy_snd (s : ℝ) (q : Bool × ((ℝ × ℝ) × ℝ)) :
    (crossSeamResolveHomotopy s q).2 = q.2.2 := rfl

/-- At time `0` the model homotopy is the raw cross reglue. -/
theorem crossSeamResolveHomotopy_zero (q : Bool × ((ℝ × ℝ) × ℝ)) :
    crossSeamResolveHomotopy 0 q = crossSeamInclude q := by
  simp [crossSeamResolveHomotopy, crossSeamInclude]

/-- At time `1` the model homotopy is the chord resolution. -/
theorem crossSeamResolveHomotopy_one (q : Bool × ((ℝ × ℝ) × ℝ)) :
    crossSeamResolveHomotopy 1 q = crossSeamResolve q := by
  obtain ⟨b, x⟩ := q
  refine Prod.ext ?_ ?_
  · simp [crossSeamResolveHomotopy]
  · cases b
    · exact (crossSeamResolveNeg_snd x).symm
    · exact (crossSeamResolvePos_snd x).symm

/-- **The model homotopy is continuous**, jointly in the time and the source point. -/
theorem continuous_crossSeamResolveHomotopy :
    Continuous fun z : ℝ × (Bool × ((ℝ × ℝ) × ℝ)) => crossSeamResolveHomotopy z.1 z.2 := by
  unfold crossSeamResolveHomotopy
  refine Continuous.prodMk ?_ continuous_snd.snd.snd
  exact ((continuous_const.sub continuous_fst).smul continuous_snd.snd.fst).add
    (continuous_fst.smul (continuous_crossSeamResolve.comp continuous_snd).fst)

/-- **The homotopy moves a boundary point inside its own cross section disk.**  This is the
convexity of the cross section square, in the form already proved in the model as
`segment_crossSeamResolvePos_subset`.  With `crossSeamResolveHomotopy_snd` it says that at the
two ends of the tube the boundary curve moves inside the end disk and nowhere else. -/
theorem crossSeamResolveHomotopy_mem_endDisk {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    {q : Bool × ((ℝ × ℝ) × ℝ)} (hq : q ∈ bentSource) :
    crossSeamResolveHomotopy s q ∈ spliceSquare ×ˢ ({q.2.2} : Set ℝ) := by
  obtain ⟨b, x⟩ := q
  have hs0 : (0 : ℝ) ≤ 1 - s := by linarith [hs.2]
  have hsum : (1 - s) + s = 1 := by ring
  rcases mem_bentSource.mp hq with ⟨hb, hx⟩ | ⟨hb, hx⟩ <;> subst hb
  · refine segment_crossSeamResolvePos_subset hx ⟨1 - s, s, hs0, hs.1, hsum, ?_⟩
    refine Prod.ext rfl ?_
    have h2 : (crossSeamResolvePos x).2 = x.2 := crossSeamResolvePos_snd x
    simp only [Prod.snd_add, Prod.smul_snd, h2, smul_eq_mul, crossSeamResolveHomotopy_snd]
    ring
  · refine segment_crossSeamResolveNeg_subset hx ⟨1 - s, s, hs0, hs.1, hsum, ?_⟩
    refine Prod.ext rfl ?_
    have h2 : (crossSeamResolveNeg x).2 = x.2 := crossSeamResolveNeg_snd x
    simp only [Prod.snd_add, Prod.smul_snd, h2, smul_eq_mul, crossSeamResolveHomotopy_snd]
    ring

/-- Every intermediate point of the model homotopy stays in the model cylinder. -/
theorem crossSeamResolveHomotopy_mem_spliceCylinder {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    {q : Bool × ((ℝ × ℝ) × ℝ)} (hq : q ∈ bentSource) :
    crossSeamResolveHomotopy s q ∈ spliceCylinder := by
  have hbase : q.2.2 ∈ Icc (0 : ℝ) 1 := by
    rcases mem_bentSource.mp hq with ⟨-, hx⟩ | ⟨-, hx⟩
    · exact hx.2
    · exact hx.2
  exact ⟨(crossSeamResolveHomotopy_mem_endDisk hs hq).1, hbase⟩

/-- **The homotopy is stationary on the four lateral attaching intervals.**  Both chord maps
fix the endpoints of their bent arcs, so a source point over the lateral boundary of the square
does not move at any time.  This is what allows the model homotopy to be glued to the constant
homotopy outside the two strips. -/
theorem crossSeamResolveHomotopy_eq_of_mem_lateral (s : ℝ) {q : Bool × ((ℝ × ℝ) × ℝ)}
    (hq : q ∈ bentSource) (hlat : q.2.1 ∈ spliceSquareBoundary) :
    crossSeamResolveHomotopy s q = q.2 := by
  obtain ⟨b, x⟩ := q
  have hfix : (crossSeamResolve (b, x)).1 = x.1 := by
    rcases mem_bentSource.mp hq with ⟨hb, hx⟩ | ⟨hb, hx⟩ <;> subst hb
    · have hid : crossSeamResolvePos x = x :=
        crossSeamResolvePos_eqOn_lateral
          (⟨hx, hlat, hx.2⟩ : x ∈ bentSheetPos ∩ (spliceSquareBoundary ×ˢ Icc (0 : ℝ) 1))
      rw [crossSeamResolve_true, hid]
    · have hid : crossSeamResolveNeg x = x :=
        crossSeamResolveNeg_eqOn_lateral
          (⟨hx, hlat, hx.2⟩ : x ∈ bentSheetNeg ∩ (spliceSquareBoundary ×ˢ Icc (0 : ℝ) 1))
      rw [crossSeamResolve_false, hid]
  refine Prod.ext ?_ rfl
  change (1 - s) • x.1 + s • (crossSeamResolve (b, x)).1 = x.1
  rw [hfix, ← add_smul, show (1 - s) + s = (1 : ℝ) by ring, one_smul]

/-! ### The boundary curves are homotopic in the ambient loop space -/

/-- **The boundary homotopy, in the ambient loop space.**  The raw curve `g` and the resolved
curve `h` are read over a closed cover `Ω₁ ∪ Ω₂` of the parameter space: over `Ω₁` both are the
transported model maps through the tube chart, over `Ω₂` they agree, over the overlap the model
coordinate is lateral, and over `Ω₁` the base coordinate is an endpoint of the base interval,
which is the hypothesis that the two strips meet the source boundary exactly in their end
edges.

The conclusion is a homotopy in `X`.  The two hypotheses that buy it are `hdisk`, the two end
disks of the tube lie in the image of the inclusion `ρ`, and `hγ`, the raw boundary curve is
read in `X`; together they cover the whole track of the homotopy, since the moving part of it
lies in the end disks and nothing else moves.  A homotopy in the manifold would be worthless
here, because the candidate boundary curves already bound disks there.

The homotopy is stationary on the whole of `Ω₂`, overlap included, and on `Ω₁` its track stays
in the cross section disk of the point it starts from. -/
theorem exists_lift_homotopic_of_crossSeamBoundary
    {M : Type u} [TopologicalSpace M] {X : Type v} [TopologicalSpace X] {Θ : Type w}
    [TopologicalSpace Θ] {ρ : X → M} (hρ : IsEmbedding ρ)
    {chart : (ℝ × ℝ) × ℝ → M} (hchart : ContinuousOn chart spliceCylinder)
    {Ω₁ Ω₂ : Set Θ} (hΩ₁ : IsClosed Ω₁) (hΩ₂ : IsClosed Ω₂) (hcover : Ω₁ ∪ Ω₂ = univ)
    {co : Θ → Bool × ((ℝ × ℝ) × ℝ)} (hco : ContinuousOn co Ω₁)
    (hsource : MapsTo co Ω₁ bentSource) {g h : C(Θ, M)}
    (hraw : ∀ θ ∈ Ω₁, g θ = chart (crossSeamInclude (co θ)))
    (hres : ∀ θ ∈ Ω₁, h θ = chart (crossSeamResolve (co θ)))
    (hrest : ∀ θ ∈ Ω₂, h θ = g θ)
    (hlateral : ∀ θ ∈ Ω₁ ∩ Ω₂, (co θ).2.1 ∈ spliceSquareBoundary)
    (hends : ∀ θ ∈ Ω₁, (co θ).2.2 = 0 ∨ (co θ).2.2 = 1)
    (hdisk : ∀ p ∈ spliceSquare, ∀ t : ℝ, t = 0 ∨ t = 1 → chart (p, t) ∈ range ρ)
    (γ : C(Θ, X)) (hγ : ∀ θ, ρ (γ θ) = g θ) :
    ∃ (δ : C(Θ, X)) (H : ContinuousMap.Homotopy γ δ), (∀ θ, ρ (δ θ) = h θ) ∧
      (∀ θ ∈ Ω₂, ∀ s : unitInterval, H (s, θ) = γ θ) ∧
      ∀ θ ∈ Ω₁, ∀ s : unitInterval,
        ρ (H (s, θ)) ∈ chart '' (spliceSquare ×ˢ ({(co θ).2.2} : Set ℝ)) := by
  classical
  obtain ⟨F, hFstrip, hFout⟩ :
      ∃ F : unitInterval × Θ → M,
        (∀ z : unitInterval × Θ, z.2 ∈ Ω₁ →
            F z = chart (crossSeamResolveHomotopy (z.1 : ℝ) (co z.2))) ∧
          ∀ z : unitInterval × Θ, z.2 ∉ Ω₁ → F z = g z.2 :=
    ⟨fun z => if z.2 ∈ Ω₁ then chart (crossSeamResolveHomotopy (z.1 : ℝ) (co z.2)) else g z.2,
      fun _ hz => if_pos hz, fun _ hz => if_neg hz⟩
  have hother : ∀ θ : Θ, θ ∉ Ω₁ → θ ∈ Ω₂ := by
    intro θ hθ
    have hmem : θ ∈ Ω₁ ∪ Ω₂ := by rw [hcover]; exact mem_univ θ
    exact hmem.resolve_left hθ
  have hstat : ∀ z : unitInterval × Θ, z.2 ∈ Ω₂ → F z = g z.2 := by
    intro z hz
    by_cases hz₁ : z.2 ∈ Ω₁
    · rw [hFstrip z hz₁,
        crossSeamResolveHomotopy_eq_of_mem_lateral _ (hsource hz₁) (hlateral z.2 ⟨hz₁, hz⟩)]
      exact (hraw z.2 hz₁).symm
    · exact hFout z hz₁
  have hcyl : ∀ z : unitInterval × Θ, z.2 ∈ Ω₁ →
      crossSeamResolveHomotopy (z.1 : ℝ) (co z.2) ∈ spliceCylinder := fun z hz =>
    crossSeamResolveHomotopy_mem_spliceCylinder z.1.2 (hsource hz)
  have hcont : Continuous F := by
    rw [← continuousOn_univ]
    have huniv : (univ : Set (unitInterval × Θ)) = univ ×ˢ Ω₁ ∪ univ ×ˢ Ω₂ := by
      rw [← Set.prod_union, hcover, Set.univ_prod_univ]
    rw [huniv]
    refine ContinuousOn.union_of_isClosed ?_ ?_ (isClosed_univ.prod hΩ₁)
      (isClosed_univ.prod hΩ₂)
    · have hinner : ContinuousOn (fun z : unitInterval × Θ => ((z.1 : ℝ), co z.2))
          (univ ×ˢ Ω₁) :=
        ((continuous_subtype_val.comp continuous_fst).continuousOn).prodMk
          (hco.comp continuous_snd.continuousOn fun z hz => hz.2)
      have hmodel : ContinuousOn
          (fun z : unitInterval × Θ => crossSeamResolveHomotopy (z.1 : ℝ) (co z.2))
          (univ ×ˢ Ω₁) :=
        continuous_crossSeamResolveHomotopy.comp_continuousOn hinner
      have hcomp : ContinuousOn
          (fun z : unitInterval × Θ => chart (crossSeamResolveHomotopy (z.1 : ℝ) (co z.2)))
          (univ ×ˢ Ω₁) :=
        ContinuousOn.comp hchart hmodel fun z hz => hcyl z hz.2
      exact ContinuousOn.congr hcomp fun z hz => hFstrip z hz.2
    · exact ContinuousOn.congr ((g.continuous.comp continuous_snd).continuousOn)
        fun z hz => hstat z hz.2
  have hF0 : ∀ θ : Θ, F (0, θ) = g θ := by
    intro θ
    by_cases hθ : θ ∈ Ω₁
    · rw [hFstrip (0, θ) hθ]
      simp only [Set.Icc.coe_zero, crossSeamResolveHomotopy_zero]
      exact (hraw θ hθ).symm
    · exact hFout (0, θ) hθ
  have hF1 : ∀ θ : Θ, F (1, θ) = h θ := by
    intro θ
    by_cases hθ : θ ∈ Ω₁
    · rw [hFstrip (1, θ) hθ]
      simp only [Set.Icc.coe_one, crossSeamResolveHomotopy_one]
      exact (hres θ hθ).symm
    · rw [hFout (1, θ) hθ]
      exact (hrest θ (hother θ hθ)).symm
  have hFrange : ∀ z : unitInterval × Θ, F z ∈ range ρ := by
    intro z
    by_cases hz : z.2 ∈ Ω₁
    · have hmem := crossSeamResolveHomotopy_mem_endDisk z.1.2 (hsource hz)
      rw [hFstrip z hz]
      exact hdisk _ hmem.1 _ (hends z.2 hz)
    · rw [hFout z hz]
      exact ⟨γ z.2, hγ z.2⟩
  choose L hL using hFrange
  have hLcont : Continuous L := by
    rw [hρ.isInducing.continuous_iff, show ρ ∘ L = F from funext hL]
    exact hcont
  have hL0 : ∀ θ : Θ, L (0, θ) = γ θ := fun θ =>
    hρ.injective ((hL (0, θ)).trans ((hF0 θ).trans (hγ θ).symm))
  refine ⟨⟨fun θ => L (1, θ), hLcont.comp (continuous_const.prodMk continuous_id)⟩,
    { toFun := L, continuous_toFun := hLcont, map_zero_left := hL0,
      map_one_left := fun _ => rfl }, fun θ => ?_, fun θ hθ s => ?_, fun θ hθ s => ?_⟩
  · exact (hL (1, θ)).trans (hF1 θ)
  · exact hρ.injective ((hL (s, θ)).trans ((hstat (s, θ) hθ).trans (hγ θ).symm))
  · change ρ (L (s, θ)) ∈ chart '' (spliceSquare ×ˢ ({(co θ).2.2} : Set ℝ))
    rw [hL (s, θ), hFstrip (s, θ) hθ]
    exact mem_image_of_mem _ (crossSeamResolveHomotopy_mem_endDisk s.2 (hsource hθ))

/-! ### The boundary word witness of the resolved cell -/

/-- **The producer.**  A boundary word witness for the raw cross reglued cell `G` is turned
into a boundary word witness for the resolved cell, over the *same* combinatorial word.  The
two cells share their source disk, the boundary circle is read through the parametrisation of
the given witness, and the boundary trace of the cross seam normal form is supplied by the
remaining hypotheses.

Nothing about the word is used: the new witness parametrises the boundary of the resolved cell
literally, by the loop produced in `X` by `exists_lift_homotopic_of_crossSeamBoundary`, and
compares it with the word through the free homotopy of the old witness composed with the
boundary homotopy.  This is the comparison that `BoundaryWordWitness.loopClassMeets_iff`
transports, so the selection step of a Lemma 2 boundary branch cut accepts it unchanged.

The witness for the raw cell is a hypothesis on purpose: producing it is a separate obligation,
at which the tree currently records the boundary of the raw cross reglue as a two arc word
while the selection step consumes a four arc one. -/
theorem exists_boundaryWordWitness_of_crossSeamBoundary
    {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {X : Type v} [TopologicalSpace X] {ρ : X → M} (hρ : IsEmbedding ρ)
    {G cell : SingularTwoCell M} (hdomain : cell.domain = G.domain)
    {chart : (ℝ × ℝ) × ℝ → M} (hchart : ContinuousOn chart spliceCylinder)
    {word : freeLoop X} (W : BoundaryWordWitness G ρ word)
    {Ω₁ Ω₂ : Set loopCircle} (hΩ₁ : IsClosed Ω₁) (hΩ₂ : IsClosed Ω₂) (hcover : Ω₁ ∪ Ω₂ = univ)
    {co : loopCircle → Bool × ((ℝ × ℝ) × ℝ)} (hco : ContinuousOn co Ω₁)
    (hsource : MapsTo co Ω₁ bentSource)
    (hraw : ∀ θ ∈ Ω₁, G (W.param θ) = chart (crossSeamInclude (co θ)))
    (hres : ∀ θ ∈ Ω₁, cell (W.param θ) = chart (crossSeamResolve (co θ)))
    (hrest : ∀ θ ∈ Ω₂, cell (W.param θ) = G (W.param θ))
    (hlateral : ∀ θ ∈ Ω₁ ∩ Ω₂, (co θ).2.1 ∈ spliceSquareBoundary)
    (hends : ∀ θ ∈ Ω₁, (co θ).2.2 = 0 ∨ (co θ).2.2 = 1)
    (hdisk : ∀ p ∈ spliceSquare, ∀ t : ℝ, t = 0 ∨ t = 1 → chart (p, t) ∈ range ρ) :
    Nonempty (BoundaryWordWitness cell ρ word) := by
  let e : loopCircle ≃ₜ frontier cell.domain :=
    W.param.trans (Homeomorph.setCongr (congrArg frontier hdomain)).symm
  obtain ⟨δ, H, hδ, -, -⟩ := exists_lift_homotopic_of_crossSeamBoundary hρ hchart hΩ₁ hΩ₂
    hcover hco hsource (g := G.boundary.comp ⟨⇑W.param, W.param.continuous⟩)
    (h := cell.boundary.comp ⟨⇑e, e.continuous⟩)
    (fun θ hθ => hraw θ hθ) (fun θ hθ => hres θ hθ) (fun θ hθ => hrest θ hθ)
    (fun θ hθ => hlateral θ hθ) hends hdisk W.loop W.realizes
  have hhom : ContinuousMap.Homotopic W.loop δ := ⟨H⟩
  exact ⟨{ param := e
           loop := δ
           realizes := hδ
           homotopic :=
             ContinuousMap.Homotopic.trans (ContinuousMap.Homotopic.symm hhom) W.homotopic }⟩

/-! ### Non-vacuity -/

section NonVacuity

/-- The ambient loop space of the instance: the model cylinder, read as a subspace of the
model ambient.  It is a *proper* subspace, `crossSeamExampleSpace_ne_univ`, so the instance
does not collapse the ambient loop space onto the ambient of the model. -/
abbrev crossSeamExampleSpace : Type := (spliceCylinder : Set ((ℝ × ℝ) × ℝ))

/-- The inclusion of the ambient loop space of the instance into the model ambient. -/
abbrev crossSeamExampleIncl : crossSeamExampleSpace → (ℝ × ℝ) × ℝ := Subtype.val

/-- The ambient loop space of the instance is a proper subspace of the model ambient, so the
homotopy produced below is not merely a homotopy in the ambient. -/
theorem crossSeamExampleSpace_ne_univ : range crossSeamExampleIncl ≠ univ := by
  rw [Subtype.range_coe]
  intro hcontra
  have hmem : (((2 : ℝ), (0 : ℝ)), (0 : ℝ)) ∈ spliceCylinder := by rw [hcontra]; trivial
  have h2 : (2 : ℝ) ≤ 1 := hmem.1.1.2
  linarith

/-- The model coordinate of the instance: the first bent arc traversed from its centre to its
endpoint `e₁`, at the bottom end of the tube. -/
noncomputable def crossSeamExampleCoord (t : unitInterval) : Bool × ((ℝ × ℝ) × ℝ) :=
  (true, (((t : ℝ), (0 : ℝ)), (0 : ℝ)))

/-- The model coordinate of the instance lands in the two source strips. -/
theorem crossSeamExampleCoord_mem (t : unitInterval) :
    crossSeamExampleCoord t ∈ bentSource := by
  refine mem_bentSource.mpr (Or.inl ⟨rfl, ?_, ?_⟩)
  · exact mem_bentArcPos.mpr (Or.inl ⟨⟨t.2.1, t.2.2⟩, rfl⟩)
  · exact ⟨le_refl 0, zero_le_one⟩

/-- The model coordinate of the instance is continuous. -/
theorem continuous_crossSeamExampleCoord : Continuous crossSeamExampleCoord := by
  unfold crossSeamExampleCoord
  exact continuous_const.prodMk ((continuous_subtype_val.prodMk continuous_const).prodMk
    continuous_const)

/-- The raw boundary curve of the instance. -/
noncomputable def crossSeamExampleRaw : C(unitInterval, (ℝ × ℝ) × ℝ) :=
  ⟨fun t => crossSeamInclude (crossSeamExampleCoord t),
    continuous_crossSeamExampleCoord.snd⟩

/-- The resolved boundary curve of the instance. -/
noncomputable def crossSeamExampleResolved : C(unitInterval, (ℝ × ℝ) × ℝ) :=
  ⟨fun t => crossSeamResolve (crossSeamExampleCoord t),
    continuous_crossSeamResolve.comp continuous_crossSeamExampleCoord⟩

/-- The raw boundary curve of the instance lies in the model cylinder, hence in the ambient
loop space of the instance. -/
theorem crossSeamExampleRaw_mem (t : unitInterval) :
    crossSeamExampleRaw t ∈ spliceCylinder := by
  have hmem := crossSeamResolveHomotopy_mem_spliceCylinder (s := 0)
    ⟨le_refl 0, zero_le_one⟩ (crossSeamExampleCoord_mem t)
  rwa [crossSeamResolveHomotopy_zero] at hmem

/-- The raw and the resolved boundary curve of the instance really differ, so the homotopy
produced below really moves: at the centre of the transverse cross the chord map displaces the
point onto the chord. -/
theorem crossSeamExampleRaw_ne_resolved : crossSeamExampleRaw ≠ crossSeamExampleResolved := by
  intro hcontra
  have h := congrArg (fun f : C(unitInterval, (ℝ × ℝ) × ℝ) => (f 0).1.1) hcontra
  simp only [crossSeamExampleRaw, crossSeamExampleResolved, crossSeamExampleCoord,
    ContinuousMap.coe_mk, crossSeamInclude, crossSeamResolve_true, crossSeamResolvePos_fst,
    crossSeamChordPos_fst, Set.Icc.coe_zero] at h
  norm_num at h

/-- The raw boundary curve of the instance, read in the ambient loop space. -/
noncomputable def crossSeamExampleLoop : C(unitInterval, crossSeamExampleSpace) :=
  ⟨fun t => ⟨crossSeamExampleRaw t, crossSeamExampleRaw_mem t⟩,
    crossSeamExampleRaw.continuous.subtype_mk _⟩

/-- **Non-vacuity of the boundary homotopy theorem.**  Every hypothesis of
`exists_lift_homotopic_of_crossSeamBoundary` is met at once by an instance which is degenerate
in none of the ways that matter: the ambient loop space is a proper subspace of the ambient of
the model, `crossSeamExampleSpace_ne_univ`; the raw and the resolved curve really differ,
`crossSeamExampleRaw_ne_resolved`, so the homotopy really moves and the produced lift really
differs from the given one; and the overlap of the closed cover, the set where the parameter
takes the value `1`, is a nonempty subset of the parameter space, so the lateral clause is not
vacuous either. -/
theorem exists_lift_homotopic_crossSeamExample :
    ∃ (δ : C(unitInterval, crossSeamExampleSpace))
      (_ : ContinuousMap.Homotopy crossSeamExampleLoop δ),
      (∀ t, crossSeamExampleIncl (δ t) = crossSeamExampleResolved t) ∧
        δ ≠ crossSeamExampleLoop := by
  have hlat : ∀ t : unitInterval, (t : ℝ) = 1 →
      (crossSeamExampleCoord t).2.1 ∈ spliceSquareBoundary := by
    intro t ht
    have hpt : (crossSeamExampleCoord t).2.1 = ((1 : ℝ), (0 : ℝ)) := Prod.ext ht rfl
    rw [hpt]
    refine mem_spliceSquareBoundary.mpr ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, Or.inr (Or.inl rfl)⟩ <;> norm_num
  have hdisk : ∀ p ∈ spliceSquare, ∀ t : ℝ, t = 0 ∨ t = 1 →
      (id (p, t) : (ℝ × ℝ) × ℝ) ∈ range crossSeamExampleIncl := by
    intro p hp t ht
    refine ⟨⟨(p, t), hp, ?_⟩, rfl⟩
    rcases ht with hq | hq
    · rw [hq]; exact ⟨le_refl 0, zero_le_one⟩
    · rw [hq]; exact ⟨zero_le_one, le_refl 1⟩
  obtain ⟨δ, H, hδ, -, -⟩ := exists_lift_homotopic_of_crossSeamBoundary
    (ρ := crossSeamExampleIncl) (chart := id) (Θ := unitInterval)
    IsEmbedding.subtypeVal continuousOn_id isClosed_univ
    (isClosed_eq continuous_subtype_val continuous_const)
    (Set.univ_union _) continuous_crossSeamExampleCoord.continuousOn
    (fun t _ => crossSeamExampleCoord_mem t)
    (g := crossSeamExampleRaw) (h := crossSeamExampleResolved)
    (fun _ _ => rfl) (fun _ _ => rfl)
    (fun t ht => by
      have hfix := crossSeamResolveHomotopy_eq_of_mem_lateral 1
        (crossSeamExampleCoord_mem t) (hlat t ht)
      rw [crossSeamResolveHomotopy_one] at hfix
      exact hfix)
    (fun t ht => hlat t ht.2) (fun _ _ => Or.inl rfl) hdisk
    crossSeamExampleLoop (fun _ => rfl)
  refine ⟨δ, H, hδ, ?_⟩
  intro hcontra
  refine crossSeamExampleRaw_ne_resolved (ContinuousMap.ext fun t => ?_)
  have hval := hδ t
  rw [hcontra] at hval
  exact hval

/-- The model coordinate of the loop instance: the constant coordinate at the centre of the
transverse cross, at the bottom end of the tube.  This is the point that the raw cross reglue
sends onto the branch and that the resolution displaces onto the chord. -/
noncomputable def crossSeamExampleCentre : Bool × ((ℝ × ℝ) × ℝ) :=
  (true, (((0 : ℝ), (0 : ℝ)), (0 : ℝ)))

/-- The centre coordinate of the loop instance lies in the two source strips. -/
theorem crossSeamExampleCentre_mem : crossSeamExampleCentre ∈ bentSource := by
  refine mem_bentSource.mpr (Or.inl ⟨rfl, ?_, ?_⟩)
  · exact mem_bentArcPos.mpr (Or.inl ⟨⟨le_refl 0, zero_le_one⟩, rfl⟩)
  · exact ⟨le_refl 0, zero_le_one⟩

/-- The raw image of the centre coordinate lies in the model cylinder. -/
theorem crossSeamExampleCentre_mem_spliceCylinder :
    crossSeamInclude crossSeamExampleCentre ∈ spliceCylinder := by
  have hmem := crossSeamResolveHomotopy_mem_spliceCylinder (s := 0)
    ⟨le_refl 0, zero_le_one⟩ crossSeamExampleCentre_mem
  rwa [crossSeamResolveHomotopy_zero] at hmem

/-- The raw boundary loop of the loop instance, read in the ambient loop space: the constant
free loop at the centre of the transverse cross. -/
noncomputable def crossSeamExampleCentreLoop : freeLoop crossSeamExampleSpace :=
  ContinuousMap.const loopCircle
    ⟨crossSeamInclude crossSeamExampleCentre, crossSeamExampleCentre_mem_spliceCylinder⟩

/-- **Non-vacuity at the loop type of the boundary word witness.**  The same instance run over
`loopCircle`, so that the object produced is an honest `freeLoop` of the ambient loop space,
which is what `BoundaryWordWitness` stores.  The ambient loop space is again the proper
subspace `crossSeamExampleSpace`, and the produced loop really differs from the given one,
because the resolution displaces the centre of the transverse cross onto the chord. -/
theorem exists_lift_homotopic_crossSeamLoopExample :
    ∃ (δ : freeLoop crossSeamExampleSpace)
      (_ : ContinuousMap.Homotopy crossSeamExampleCentreLoop δ),
      (∀ θ, crossSeamExampleIncl (δ θ) = crossSeamResolve crossSeamExampleCentre) ∧
        δ ≠ crossSeamExampleCentreLoop := by
  have hdisk : ∀ p ∈ spliceSquare, ∀ t : ℝ, t = 0 ∨ t = 1 →
      (id (p, t) : (ℝ × ℝ) × ℝ) ∈ range crossSeamExampleIncl := by
    intro p hp t ht
    refine ⟨⟨(p, t), hp, ?_⟩, rfl⟩
    rcases ht with hq | hq
    · rw [hq]; exact ⟨le_refl 0, zero_le_one⟩
    · rw [hq]; exact ⟨zero_le_one, le_refl 1⟩
  obtain ⟨δ, H, hδ, -, -⟩ := exists_lift_homotopic_of_crossSeamBoundary
    (ρ := crossSeamExampleIncl) (chart := id) (Θ := loopCircle)
    (co := fun _ => crossSeamExampleCentre)
    IsEmbedding.subtypeVal continuousOn_id isClosed_univ isClosed_empty
    (Set.union_empty _) continuousOn_const (fun _ _ => crossSeamExampleCentre_mem)
    (g := ContinuousMap.const loopCircle (crossSeamInclude crossSeamExampleCentre))
    (h := ContinuousMap.const loopCircle (crossSeamResolve crossSeamExampleCentre))
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ hθ => hθ.elim) (fun _ hθ => hθ.2.elim)
    (fun _ _ => Or.inl rfl) hdisk crossSeamExampleCentreLoop (fun _ => rfl)
  refine ⟨δ, H, hδ, ?_⟩
  intro hcontra
  have hval := hδ 0
  rw [hcontra] at hval
  have hfst := congrArg (fun y : (ℝ × ℝ) × ℝ => y.1.1) hval
  simp only [crossSeamExampleCentre, crossSeamExampleCentreLoop, crossSeamInclude,
    crossSeamResolve_true, crossSeamResolvePos_fst, crossSeamChordPos_fst,
    ContinuousMap.const_apply] at hfst
  norm_num at hfst

end NonVacuity

end DifferentialGeometry.Topology.PiecewiseLinear
