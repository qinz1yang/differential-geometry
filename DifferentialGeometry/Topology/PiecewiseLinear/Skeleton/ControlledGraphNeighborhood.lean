/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LabelledCellAssembly
import DifferentialGeometry.Topology.PiecewiseLinear.Section34Frame

/-!
# Sorry-first skeleton of the controlled form of Moise 35.1

The assembly `controlledGraphNeighborhood` proves the endpoint
`ControlledGraphNeighborhoodStatement` for real from the eight leaves of this file; every `sorry`
is a leaf and none sits inside an assembly.  The endpoint statement is unchanged by review W.
It changed earlier only through `Section34CarrierControl`, which also asks that each carrier
`H t` lie in one piecewise linear chart of `M₂`.  The endpoint is **not** a producer of
`Section34NormalPlus`: it supplies
P1 only, that is the cut frame and the graph frame, conditional on `Moise341`.  The exterior
clause and the Lemma 11 trace certificate remain obligations of the other half.

The realisation ambient `Ea` is universally quantified in the endpoint, next to the
triangulation it realises; it is never the chart model.  `LocallyFinitePLPieceIn Ea 3 M₁ U`
realises all of `U` inside `Ea`, so writing `EuclideanSpace ℝ (Fin 3)` there would exclude
`U = S³`.

Quantifier order is the content.  The triangulation `𝒦` and the carrier control `(η, H)` come
first, because Section 34 chooses them once for the whole approximation problem; only then the
prescribed neighbourhood `W` of the one skeleton and the free tolerance `ψ`, which Moise 35.2
supplies afresh; and the subdivision `𝒦'`, the cut diagram, the regular neighbourhood and `f₁`
stand in one existential, because Lemma 1's incidence clauses are read off a jointly chosen
neighbourhood and map.

What comes from Moise and what is this project's own device.  The order
`C'_v → S_e, T_e → C''_v → ε_v → f_v → general position` and conditions (1)--(8) are pages
248--250.  The *outer torus* `S_{2σ}` of a triangle with `h '' Bd σ` as its spine is **page
240**, Section 34 Lemma 2, imported here because the controlled conclusion carries Lemma 2's
generator clause; pages 248--251 contain no nested tori.  The *compact envelopes* `K_w ⊇ Q w`
and the label-wise finite descent that replace Moise's one sentence minimising a single global
component count over an infinite family are the project's own, as is the separation of the
*pierced* cells `C'_v` from the *enlarged* cells `C''_v` into two named families.  The slight
alteration of page 248 alters one cell of each edge and is only asked to stay in a prescribed
neighbourhood of it, so `C_v ⊆ C'_v` is not claimed; what the later stages need is
`C_v ⊆ C''_v`, and that is what the preparation records.

`Section34VertexPreparation` fixes, before any map, the endpoint assignment of the edges, `C'_v`
with the graph core in `Int C'_v`, the piercing circle `Bd C'_v ∩ Bd C'_w` inside the splitting
disk, the two compatible regular neighbourhoods `T_e ⊆ Int S_e` of that circle with their solid
torus structure, the pairwise disjointness of the tubes `S_e`, the annuli `A_e = Bd C'_v ∩ T_e`
and `B_e ⊆ Bd C'_w` with their designated boundary circles and their source side inside and
outside marking, the middle annulus `B_e⁰ ⊆ B_e ∩ Int T_e` with its two collar circles, the
enlarged cells `C''_v ⊇ C_v ∪ C'_v ∪ ⋃_{e ∋ v} S_e`, one piecewise linear chart of `M₂`
containing `h '' C''_v`, and only then the tolerances `ε_v`, two-sided wherever two
approximations meet.  It no longer chooses the outer torus.

The outer torus and the fine carriers are chosen **together**, by the leaf that chooses `Q`.  A
common chart is far too weak: with `U = M₁ = M₂ = ℝ³`, `h` an affine shear and the `Q_w` large,
`hQint` and `hQchart` hold while the buffer `c_σ (⋃ Q) ⊆ Int S_{2σ}` puts a `2`-cell bounded by
`c_σ (h (Bd σ))` inside the torus, and a spine circle cannot bound.  `Section34OuterTorus`
therefore records the chart, the solid torus, the spine clause in the exact form
`moise308Nested` consumes, the buffer, and the smallness of `Q` that makes the pair consistent:
no piecewise linear `2`-cell with intrinsic boundary `h '' Bd σ` lies inside the union of the
carriers of the vertices incident to `σ`.  That union is a neighbourhood of the rim only, not of
the triangle, because each `Q_w` is a neighbourhood of `h '' C_w` and each `C_w` sits on the one
skeleton; the smallness clause is what forbids the carriers from filling the rim in.

The vertex chart is what makes step 6 a theorem instead of a leaf: the piecewise linear
parametrisation of `C''_v` carries the problem to a polyhedral `3`-cell of `ℝ³` whose image
lies in one chart, which is the hypothesis of the proved chart local
`Moise341.exists_isPLHomeomorphInto_dist_lt_of_mapsTo_chart`, and the result is conjugated back
by `exists_isPLHomeomorphInto_of_isPLHomeomorphOn`.

`Section34PiercingConditions` is conditions (2)--(8) together with four geometric certificates
the removal step and the matching consume: that `G_w` is a piecewise linear embedding of the
pierced ball `C'_w` and not only of `C''_w`, the disjointness of every marker from every target
tube, the disjointness of a tube from the boundary of a ball of a vertex that is not one of its
ends, and the disjointness of the images of two pierced balls with disjoint sources.  The last
three are proved by `section34MarginConditions`; the first is what
`section34Marker_of_dist_lt` turns, through `image_interior_stable_of_dist_lt` and the margin
between `Bd C'_w` and the marker, into the per-ball marker
`h '' simplexBody 𝒦' w ⊆ interior (G w '' C'_w)`, which is therefore no longer a field.  The
restriction of an `IsPLHomeomorphInto` to a subset is not available in the tree, which is why
the embedding of `C'_w` has to be asked for and cannot be cut down from that of `C''_w`.  The
general position clause is the local crossing model
`HasPLCrossingAt` read in a piecewise linear chart at every intersection point, not the
containment of the intersection polygons in the two relative interiors, which the tangent pair
`{(θ, u, 0)}`, `{(θ, u, |u|)}` satisfies.  The supports are pairwise disjoint and locally finite
**in the target subspace `h '' U`**, not in `⋃ Q`: thin spikes on far tubes accumulate at points
of `h '' U` lying in no `C''_v`.

The leaves, with content and review state.

`image_interior_stable_of_dist_lt` (**new, unreviewed**): the one degree-theoretic input.  For a
piecewise linear `3`-cell `S` with intrinsic boundary `B`, two embeddings of `S` that are
`ε`-close on `S`, and a compact `K ⊆ S \ B` whose `F`-image is at distance at least `ε` from
`F '' B`, the conclusion `F '' K ⊆ G '' S`.  Only this containment is a leaf; the upgrade from
`G '' S` to `interior (G '' S)` is the proved `mem_interior_image_of_notMem_image_boundary` of
`Section34Frame`, because `G '' B = frontier (G '' S)` splits the complement of `G '' B` into
the interior of `G '' S` and the exterior.  What is missing is exactly the statement that the
exterior component is excluded, that is the equality of the degrees of two `ε`-close embeddings
of the boundary sphere about a point `ε`-far from both images; the tree has no degree.

`exists_section34CutFrame` (steps 1--5): **changed after review W (joint outer torus),
unreviewed**.  Added to the earlier statement, which was reviewed three times: the two outputs
`ct` and `Sd`, and the single clause `Section34OuterTorus 𝒦 𝒦' h Q ct Sd`.  Nothing else
changed.  It produces `𝒦'`, the cut frame, the regular neighbourhood `N = ⋃ C_v` of the one
skeleton inside `W`, the assignment `car` with finite fibres, the fine carriers `Q v`, the
carrier separation, and now the triangle charts and outer tori.

`exists_section34VertexPreparation` (**changed after review W, unreviewed**): it no longer
receives `hQchart` and no longer produces `ct`, `Sd` or their clauses; it gained the middle
annulus `B_e⁰` with its two collars, the collar margin, the tube-versus-marker and
tube-versus-foreign-boundary margins, and the margin between two pierced balls with disjoint
sources.

`exists_section34PiercingPackage` (**changed after review W, unreviewed**): it now receives
`hQsub : ∀ w, Q w ⊆ h '' U` and the carrier local finiteness `hQlfU` in that subspace, which is
what `locallyFinite_support_of_section34CutFrame` turns into the package's `hSpLF`.  What it
still owes is only the clauses that `section34MarginConditions` and
`image_interior_stable_of_dist_lt` do not give: the containments whose ambient set is a solid
torus rather than a cell, the component certificates of (7), and the general position of (8).

`exists_section34ProtectedCircleRemovalStep` (**FIX of review W, restated**): one modification
inside `Int S'_{e₀}`.  It already concludes `Section34PiercingConditions` for the new family, and
its first field is `∀ w, IsPLHomeomorphInto 3 (G' w) (C''_w)`, so the replacement is a piecewise
linear embedding of all of `C''_w` and not a set level surgery.  That the markers and the
boundaries of the balls of the other vertices are untouched is no longer assumed: it is the
proved `section34Step_eqOn_marker_and_boundary`, from the `EqOn` off the support together with
the two new disjointness certificates.

`exists_section34ProtectedCircleRemoval` (reviewed **OK**): unchanged except that `hprep` names
the three new sets of the preparation and no longer names `ct`, `Sd`.

`exists_section34DeletedBalls` (**new, unreviewed**): the first half of page 251.  It outputs the
deleted balls `D_v = G_w(C'_w)` minus the interiors of the pierced balls of the other end of
each incident edge, their `3`-cell certificates, the prescribed intersection disks `D_v ∩ D_w`
with their `2`-cell certificates and exact meets, disjointness of different intersections, the
adjacency criterion, and the markers.

`exists_section34EdgeMatching` (**changed after review W, unreviewed**): only the three stage
relative matching is left.  It receives the certificates above and outputs the maps `G'` of the
*original* cells with `G' w '' C_w = D_v`, their compatibility and exact meets, the rim
containment and the nested torus certificate, whose outer torus and chart are the `S_{2σ}` and
`c_σ` of `Section34OuterTorus` and whose only new datum is the inner torus `S_{1σ}`.

Proved here, not leaves: `Moise341.exists_section34VertexApproximation`,
`image_interior_stable_of_dist_lt`, `section34Step_eqOn_marker_and_boundary`,
`exists_section34PiercingConditions_count_le_one`, and the assembly, which in particular proves
conditions (2) and (3) of Section 34 Lemma 1 from the carrier separation and the combinatorics
of the splitting disks, the `ψ` estimate, and the generator clause from the nested torus
certificate.  Proved in `Section34Frame`: `section34MarginConditions`,
`section34FaceTorus_subset_outerTorus`, `mem_interior_image_of_notMem_image_boundary`,
`finite_splitDisk_of_section34CutFrame` and `locallyFinite_support_of_section34CutFrame`.
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

def ControlledGraphNeighborhoodStatement : Prop :=
  ∀ {M₁ M₂ : Type u} [TopologicalSpace M₁] [T2Space M₁] [SecondCountableTopology M₁]
    [MetricSpace M₂] [SecondCountableTopology M₂]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
    [HasGroupoid M₁ (plGroupoid 3)] [HasGroupoid M₂ (plGroupoid 3)] {U : Set M₁}, IsOpen U →
    ∀ {h : M₁ → M₂}, Topology.IsEmbedding (U.domRestrict h) →
    ∀ (Ea : Type) [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
      (𝒦 : LocallyFinitePLPieceIn Ea 3 M₁ U), IsCombinatorialManifold 3 𝒦.complex →
    ∀ (η : M₁ → ℝ) (H : Finset Ea → Set M₂), Section34CarrierControl U 𝒦 h η H →
    ∀ {W : Set M₁}, IsOpen W → graphSkeletonSpace 𝒦 ⊆ W → W ⊆ U →
    ∀ ψ : M₁ → ℝ, ContinuousOn ψ U → (∀ x ∈ U, 0 < ψ x) →
    ∃ (𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U)
      (src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁)
      (car : Section34VertexIndex 𝒦 𝒦' → Finset Ea) (f₁ : M₁ → M₂),
      Section34CutFrame U 𝒦 𝒦' src srcBd ∧
        Section34GraphFrame U W h ψ H 𝒦 𝒦' src car f₁

section Leaves

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂] {U W : Set M₁} {h : M₁ → M₂}
  {η ψ : M₁ → ℝ} {H : Finset Ea → Set M₂}
  {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁}
  {Q : Section34VertexIndex 𝒦 𝒦' → Set M₂}
  {Cp CpBd Cc CcBd : Section34VertexIndex 𝒦 𝒦' → Set M₁}
  {ε : Section34VertexIndex 𝒦 𝒦' → ℝ}
  {ct : Section34SimplexIndex 𝒦 3 → OpenPartialHomeomorph M₂ (EuclideanSpace ℝ (Fin 3))}
  {Sd : Section34SimplexIndex 𝒦 3 → Set (EuclideanSpace ℝ (Fin 3))}
  {ends : Section34EdgeIndex 𝒦 𝒦' →
    Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦'}
  {Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ : Section34EdgeIndex 𝒦 𝒦' → Set M₁}
  {Sp Tp : Section34EdgeIndex 𝒦 𝒦' → Set M₂} {cnt : Section34EdgeIndex 𝒦 𝒦' → ℕ}
  {Pg : Section34EdgeIndex 𝒦 𝒦' → ℕ → Set M₂}
  {G : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂}

theorem image_subset_of_dist_lt_of_isPLCellOn {S B Kc : Set M₁} {F G : M₁ → M₂} {δ : ℝ}
    (hS : IsPLCellOn 3 S B) (hG : IsPLHomeomorphInto 3 G S) (hFc : ContinuousOn F S)
    (hFi : InjOn F S) (hKc : Kc ⊆ S \ B) (hclose : ∀ z ∈ S, dist (F z) (G z) < δ)
    (hfar : ∀ x ∈ Kc, ∀ y ∈ B, δ ≤ dist (F x) (F y)) :
    F '' Kc ⊆ G '' S := by
  sorry

theorem image_interior_stable_of_dist_lt {S B Kc : Set M₁} {F G : M₁ → M₂} {δ : ℝ}
    (hS : IsPLCellOn 3 S B) (hG : IsPLHomeomorphInto 3 G S) (hFc : ContinuousOn F S)
    (hFi : InjOn F S) (hKc : Kc ⊆ S \ B) (hclose : ∀ z ∈ S, dist (F z) (G z) < δ)
    (hfar : ∀ x ∈ Kc, ∀ y ∈ B, δ ≤ dist (F x) (F y)) :
    F '' Kc ⊆ interior (G '' S) := by
  have himg := image_subset_of_dist_lt_of_isPLCellOn hS hG hFc hFi hKc hclose hfar
  rintro _ ⟨x, hx, rfl⟩
  refine mem_interior_image_of_notMem_image_boundary hS hG (himg ⟨x, hx, rfl⟩) ?_
  rintro ⟨y, hy, hxy⟩
  have h1 : dist (F y) (G y) < δ := hclose y (hS.boundary_subset hy)
  have h2 : δ ≤ dist (F x) (F y) := hfar x hx y hy
  rw [hxy, dist_comm] at h1
  linarith

theorem exists_section34CutFrame [T2Space M₁] [SecondCountableTopology M₁]
    [SecondCountableTopology M₂] [HasGroupoid M₁ (plGroupoid 3)] [HasGroupoid M₂ (plGroupoid 3)]
    (hU : IsOpen U) (hh : Topology.IsEmbedding (U.domRestrict h))
    (𝒦 : LocallyFinitePLPieceIn Ea 3 M₁ U) (h𝒦 : IsCombinatorialManifold 3 𝒦.complex)
    (η : M₁ → ℝ) (H : Finset Ea → Set M₂) (hH : Section34CarrierControl U 𝒦 h η H)
    (hW : IsOpen W) (hΓW : graphSkeletonSpace 𝒦 ⊆ W) (hWU : W ⊆ U)
    (ψ : M₁ → ℝ) (hψc : ContinuousOn ψ U) (hψpos : ∀ x ∈ U, 0 < ψ x) :
    ∃ (𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U)
      (src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁)
      (car : Section34VertexIndex 𝒦 𝒦' → Finset Ea)
      (Q : Section34VertexIndex 𝒦 𝒦' → Set M₂)
      (ct : Section34SimplexIndex 𝒦 3 → OpenPartialHomeomorph M₂ (EuclideanSpace ℝ (Fin 3)))
      (Sd : Section34SimplexIndex 𝒦 3 → Set (EuclideanSpace ℝ (Fin 3))),
      Section34CutFrame U 𝒦 𝒦' src srcBd ∧
        IsLocallyFiniteRegularNeighborhoodOf (n := 3) (section34CutNeighborhood src)
          (graphSkeletonSpace 𝒦) U ∧
        section34CutNeighborhood src ⊆ W ∧
        (∀ w, car w ∈ 𝒦.complex.faces) ∧
        (∀ w, src (.vertexBall w) ⊆ Section34CarrierSupport 𝒦 (car w)) ∧
        (∀ t : Finset Ea, {w | car w = t}.Finite) ∧
        (∀ w, h '' src (.vertexBall w) ⊆ interior (Q w)) ∧
        (∀ w, Q w ⊆ H (car w)) ∧
        (∀ w, ∀ x ∈ src (.vertexBall w), ∀ y ∈ Q w, ∀ z ∈ Q w, dist y z < ψ x) ∧
        (∀ (w : Section34VertexIndex 𝒦 𝒦') (s : Section34SimplexIndex 𝒦 3),
          (Q w ∩ h '' simplexBody 𝒦 s.1).Nonempty → Section34Incident w.1 s.1) ∧
        (∀ (w : Section34VertexIndex 𝒦 𝒦') (s : Section34SimplexIndex 𝒦 3),
          Section34Incident w.1 s.1 → Q w ⊆ H s.1) ∧
        Section34OuterTorus 𝒦 𝒦' h Q ct Sd := by
  sorry

theorem exists_section34VertexPreparation [T2Space M₁] [SecondCountableTopology M₁]
    [SecondCountableTopology M₂] [HasGroupoid M₁ (plGroupoid 3)] [HasGroupoid M₂ (plGroupoid 3)]
    (hU : IsOpen U) (hh : Topology.IsEmbedding (U.domRestrict h))
    (hframe : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hN : IsLocallyFiniteRegularNeighborhoodOf (n := 3) (section34CutNeighborhood src)
      (graphSkeletonSpace 𝒦) U)
    (hQint : ∀ w, h '' src (Section34Label.vertexBall w) ⊆ interior (Q w)) :
    ∃ (Cp CpBd Cc CcBd : Section34VertexIndex 𝒦 𝒦' → Set M₁)
      (ends : Section34EdgeIndex 𝒦 𝒦' →
        Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦')
      (Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ : Section34EdgeIndex 𝒦 𝒦' → Set M₁)
      (ε : Section34VertexIndex 𝒦 𝒦' → ℝ),
      Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Sn Tn Aa Ab₀ Ab₁
        Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε := by
  sorry

omit [FiniteDimensional ℝ Ea] in
theorem Moise341.exists_section34VertexApproximation (h341 : Moise341)
    [HasGroupoid M₂ (plGroupoid 3)] (hh : Topology.IsEmbedding (U.domRestrict h))
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε) :
    ∃ G : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂,
      (∀ w, IsPLHomeomorphInto 3 (G w) (Cc w)) ∧
        ∀ w, ∀ x ∈ Cc w, dist (G w x) (h x) < ε w := by
  classical
  obtain ⟨hεpos, hcc, hsub, hchart, -⟩ := hprep
  have hcontU : ContinuousOn h U :=
    continuousOn_iff_continuous_domRestrict.mpr hh.continuous
  have hinjU : InjOn h U := by
    intro x hx y hy hxy
    have hxy' : U.domRestrict h ⟨x, hx⟩ = U.domRestrict h ⟨y, hy⟩ := hxy
    exact congrArg Subtype.val (hh.injective hxy')
  have key : ∀ w : Section34VertexIndex 𝒦 𝒦', ∃ F : M₁ → M₂,
      IsPLHomeomorphInto 3 F (Cc w) ∧ ∀ x ∈ Cc w, dist (F x) (h x) < ε w := by
    intro w
    obtain ⟨P, r, u, hr, hu, hCceq, -⟩ := hcc w
    obtain ⟨c, hc, hcsrc⟩ := hchart w
    have hPball : IsPLBall 3 P := ⟨r, hr⟩
    have hmem : ∀ x ∈ P, u x ∈ Cc w := by
      intro x hx
      rw [hCceq]
      exact ⟨x, hx, rfl⟩
    have hback : ∀ y ∈ Cc w, ∃ x ∈ P, u x = y := by
      intro y hy
      rw [hCceq] at hy
      exact hy
    have huP : MapsTo u P U := fun x hx => (hsub w).2.2 (hmem x hx)
    have hcont : ContinuousOn (h ∘ u) P := hcontU.comp hu.continuousOn huP
    have hinj : InjOn (h ∘ u) P := hinjU.comp hu.injOn huP
    have hmap : MapsTo (h ∘ u) P c.source := fun x hx => hcsrc ⟨u x, hmem x hx, rfl⟩
    obtain ⟨f, hf, -, hfd⟩ :=
      h341.exists_isPLHomeomorphInto_dist_lt_of_mapsTo_chart hPball hcont hinj c hc hmap
        (τ := fun _ => ε w) continuousOn_const fun _ _ => hεpos w
    refine ⟨f ∘ Function.invFunOn u P, ?_, ?_⟩
    · rw [hCceq]
      exact (exists_isPLHomeomorphInto_of_isPLHomeomorphOn hu hf
        hPball.isPolyhedron.isPLHomeomorphOn_id).1
    · intro x hx
      obtain ⟨z, hz, rfl⟩ := hback x hx
      have hzz : Function.invFunOn u P (u z) = z := hu.injOn.leftInvOn_invFunOn hz
      have hd := hfd z hz
      simp only [Function.comp_apply, hzz] at hd ⊢
      exact hd
  choose G hG hGd using key
  exact ⟨G, hG, hGd⟩

theorem exists_section34PiercingPackage [T2Space M₁] [SecondCountableTopology M₁]
    [SecondCountableTopology M₂] [HasGroupoid M₁ (plGroupoid 3)] [HasGroupoid M₂ (plGroupoid 3)]
    (hU : IsOpen U) (hh : Topology.IsEmbedding (U.domRestrict h))
    (hframe : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hN : IsLocallyFiniteRegularNeighborhoodOf (n := 3) (section34CutNeighborhood src)
      (graphSkeletonSpace 𝒦) U)
    (hQsub : ∀ w, Q w ⊆ h '' U)
    (hQlfU : LocallyFinite fun w => {y : h '' U | (y : M₂) ∈ Q w})
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hG : ∀ w, IsPLHomeomorphInto 3 (G w) (Cc w))
    (hGdist : ∀ w, ∀ x ∈ Cc w, dist (G w x) (h x) < ε w) :
    ∃ (Sp Tp : Section34EdgeIndex 𝒦 𝒦' → Set M₂) (cnt : Section34EdgeIndex 𝒦 𝒦' → ℕ)
      (Pg : Section34EdgeIndex 𝒦 𝒦' → ℕ → Set M₂)
      (G' : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂),
      Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁
          Sp Tp cnt Pg G' ∧
        ∀ w, ∀ x ∈ Cc w, dist (G' w x) (h x) < ε w := by
  sorry

theorem exists_section34ProtectedCircleRemovalStep
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G)
    (e₀ : Section34EdgeIndex 𝒦 𝒦') (hlt : 1 < cnt e₀) :
    ∃ (G' : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂) (cnt' : Section34EdgeIndex 𝒦 𝒦' → ℕ)
      (Pg' : Section34EdgeIndex 𝒦 𝒦' → ℕ → Set M₂),
      Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁
          Sp Tp cnt' Pg' G' ∧
        cnt' e₀ < cnt e₀ ∧
        (∀ e, e ≠ e₀ → cnt' e = cnt e) ∧
        (∀ w, EqOn (G' w) (G w) {x ∈ Cc w | G w x ∉ interior (Sp e₀)}) ∧
        ∀ e, e ≠ e₀ → G' (ends e).1 '' Aa e = G (ends e).1 '' Aa e ∧
          G' (ends e).2 '' Bb e = G (ends e).2 '' Bb e := by
  sorry

omit [FiniteDimensional ℝ Ea] in
theorem section34Marker_of_dist_lt (hh : Topology.IsEmbedding (U.domRestrict h))
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hGp : ∀ w, IsPLHomeomorphInto 3 (G w) (Cp w))
    (hGdist : ∀ w, ∀ x ∈ Cc w, dist (G w x) (h x) < ε w) (w : Section34VertexIndex 𝒦 𝒦') :
    h '' simplexBody 𝒦' w.1 ⊆ interior (G w '' Cp w) := by
  obtain ⟨-, -, hsubs, -, hcpcell, hbody, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, hcpmar, -⟩ := hprep
  have hcp : ∀ v, IsPLCellOn 3 (Cp v) (CpBd v) := hcpcell
  have hCpU : Cp w ⊆ U := (hsubs w).2.1.trans (hsubs w).2.2
  have hcontU : ContinuousOn h U := continuousOn_iff_continuous_domRestrict.mpr hh.continuous
  have hinjU : InjOn h U := by
    intro x hx y hy hxy
    have hxy' : U.domRestrict h ⟨x, hx⟩ = U.domRestrict h ⟨y, hy⟩ := hxy
    exact congrArg Subtype.val (hh.injective hxy')
  refine image_interior_stable_of_dist_lt (δ := ε w) (hcp w) (hGp w) (hcontU.mono hCpU)
    (hinjU.mono hCpU) ?_ ?_ ?_
  · rw [(hcp w).sdiff_boundary_eq_interior]
    exact hbody w
  · intro z hz
    rw [dist_comm]
    exact hGdist w z ((hsubs w).2.1 hz)
  · intro x hx y hy
    have hlt := hcpmar w y hy (h x) ⟨x, hx, rfl⟩
    rw [dist_comm] at hlt
    exact hlt.le

omit [FiniteDimensional ℝ Ea] in
theorem section34Step_eqOn_marker_and_boundary
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G)
    (G' : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂) (e₀ : Section34EdgeIndex 𝒦 𝒦')
    (hoff : ∀ w, EqOn (G' w) (G w) {x ∈ Cc w | G w x ∉ interior (Sp e₀)}) :
    (∀ w, EqOn (G' w) (G w) (simplexBody 𝒦' w.1)) ∧
      ∀ w, w ≠ (ends e₀).1 → w ≠ (ends e₀).2 → EqOn (G' w) (G w) (CpBd w) := by
  obtain ⟨-, -, hsubs, -, hcpcell, hbody, -⟩ := hprep
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hmark, hbd, -⟩ := hpack
  have hcp : ∀ w, IsPLCellOn 3 (Cp w) (CpBd w) := hcpcell
  constructor
  · intro w
    refine eqOn_of_eqOn_off_support (hoff w) ?_ ?_
    · exact ((hbody w).trans interior_subset).trans (hsubs w).2.1
    · exact (hmark w e₀).mono_right interior_subset
  · intro w hw1 hw2
    refine eqOn_of_eqOn_off_support (hoff w) ?_ ?_
    · exact ((hcp w).boundary_subset).trans (hsubs w).2.1
    · exact ((hbd e₀ w hw1 hw2).symm).mono_right interior_subset

theorem exists_section34PiercingConditions_count_le_one
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (e₀ : Section34EdgeIndex 𝒦 𝒦')
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) :
    ∃ (G' : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂) (cnt' : Section34EdgeIndex 𝒦 𝒦' → ℕ)
      (Pg' : Section34EdgeIndex 𝒦 𝒦' → ℕ → Set M₂),
      Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁
          Sp Tp cnt' Pg' G' ∧
        cnt' e₀ ≤ 1 ∧ (∀ e, e ≠ e₀ → cnt' e = cnt e) ∧
        (∀ w, EqOn (G' w) (G w) {x ∈ Cc w | G w x ∉ interior (Sp e₀)}) ∧
        (∀ w, EqOn (G' w) (G w) (simplexBody 𝒦' w.1)) ∧
        ∀ e, e ≠ e₀ → G' (ends e).1 '' Aa e = G (ends e).1 '' Aa e ∧
          G' (ends e).2 '' Bb e = G (ends e).2 '' Bb e := by
  classical
  suffices H : ∀ n : ℕ, ∀ (G : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂)
      (cnt : Section34EdgeIndex 𝒦 𝒦' → ℕ) (Pg : Section34EdgeIndex 𝒦 𝒦' → ℕ → Set M₂),
      Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁
        Sp Tp cnt Pg G → cnt e₀ ≤ n →
      ∃ (G' : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂) (cnt' : Section34EdgeIndex 𝒦 𝒦' → ℕ)
        (Pg' : Section34EdgeIndex 𝒦 𝒦' → ℕ → Set M₂),
        Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁
            Sp Tp cnt' Pg' G' ∧
          cnt' e₀ ≤ 1 ∧ (∀ e, e ≠ e₀ → cnt' e = cnt e) ∧
          (∀ w, EqOn (G' w) (G w) {x ∈ Cc w | G w x ∉ interior (Sp e₀)}) ∧
          (∀ w, EqOn (G' w) (G w) (simplexBody 𝒦' w.1)) ∧
          ∀ e, e ≠ e₀ → G' (ends e).1 '' Aa e = G (ends e).1 '' Aa e ∧
            G' (ends e).2 '' Bb e = G (ends e).2 '' Bb e by
    exact H (cnt e₀) G cnt Pg hpack le_rfl
  intro n
  induction n with
  | zero =>
      intro G cnt Pg hp hle
      exact ⟨G, cnt, Pg, hp, by omega, fun _ _ => rfl, fun w => Set.eqOn_refl (G w) _,
        fun w => Set.eqOn_refl (G w) _, fun _ _ => ⟨rfl, rfl⟩⟩
  | succ n ih =>
      intro G cnt Pg hp hle
      by_cases h1 : cnt e₀ ≤ 1
      · exact ⟨G, cnt, Pg, hp, h1, fun _ _ => rfl, fun w => Set.eqOn_refl (G w) _,
          fun w => Set.eqOn_refl (G w) _, fun _ _ => ⟨rfl, rfl⟩⟩
      · obtain ⟨G₁, cnt₁, Pg₁, hp₁, hdrop, hfix, hoff, him⟩ :=
          exists_section34ProtectedCircleRemovalStep hprep hp e₀ (by omega)
        have hcore := (section34Step_eqOn_marker_and_boundary hprep hp G₁ e₀ hoff).1
        obtain ⟨G₂, cnt₂, Pg₂, hp₂, hle₂, hfix₂, hoff₂, hcore₂, him₂⟩ :=
          ih G₁ cnt₁ Pg₁ hp₁ (by omega)
        refine ⟨G₂, cnt₂, Pg₂, hp₂, hle₂, fun e he => (hfix₂ e he).trans (hfix e he), ?_, ?_,
          fun e he => ⟨((him₂ e he).1).trans (him e he).1,
            ((him₂ e he).2).trans (him e he).2⟩⟩
        · intro w x hx
          have hx1 : G₁ w x = G w x := hoff w hx
          have hx2 : x ∈ {x ∈ Cc w | G₁ w x ∉ interior (Sp e₀)} := by
            refine ⟨hx.1, ?_⟩
            rw [hx1]
            exact hx.2
          exact (hoff₂ w hx2).trans hx1
        · exact fun w x hx => (hcore₂ w hx).trans (hcore w hx)

theorem exists_section34ProtectedCircleRemoval
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G)
    (K : Section34VertexIndex 𝒦 𝒦' → Set M₂)
    (hK : ∀ w, IsCompact (K w) ∧ Q w ⊆ K w ∧ K w ⊆ h '' U) :
    ∃ (G' : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂) (cnt' : Section34EdgeIndex 𝒦 𝒦' → ℕ)
      (Pg' : Section34EdgeIndex 𝒦 𝒦' → ℕ → Set M₂),
      Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁
          Sp Tp cnt' Pg' G' ∧
        (∀ e, cnt' e = 1) ∧
        (∀ w, EqOn (G' w) (G w) {x ∈ Cc w | ∀ e, G w x ∉ interior (Sp e)}) ∧
        ∀ w, EqOn (G' w) (G w) (simplexBody 𝒦' w.1) := by
  sorry

theorem exists_section34DeletedBalls [T2Space M₁] [SecondCountableTopology M₁]
    [SecondCountableTopology M₂] [HasGroupoid M₁ (plGroupoid 3)] [HasGroupoid M₂ (plGroupoid 3)]
    (hU : IsOpen U) (hh : Topology.IsEmbedding (U.domRestrict h))
    (hframe : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hN : IsLocallyFiniteRegularNeighborhoodOf (n := 3) (section34CutNeighborhood src)
      (graphSkeletonSpace 𝒦) U)
    (hQlf : ∀ y ∈ ⋃ w, Q w, ∃ V ∈ 𝓝 y, {w | (Q w ∩ V).Nonempty}.Finite)
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G)
    (hone : ∀ e, cnt e = 1) :
    ∃ (Dv DvBd : Section34VertexIndex 𝒦 𝒦' → Set M₂)
      (Dd DdBd : Section34EdgeIndex 𝒦 𝒦' → Set M₂),
      (∀ w, Dv w = G w '' Cp w \
        ⋃ (e : Section34EdgeIndex 𝒦 𝒦') (_ : (ends e).2 = w),
          interior (G (ends e).1 '' Cp (ends e).1)) ∧
        (∀ w, IsPLCellOn 3 (Dv w) (DvBd w)) ∧
        (∀ w, Dv w ⊆ Q w) ∧
        (∀ e, IsPLCellOn 2 (Dd e) (DdBd e)) ∧
        (∀ e, Dv (ends e).1 ∩ Dv (ends e).2 = Dd e) ∧
        (∀ e, Dd e ⊆ DvBd (ends e).1 ∩ DvBd (ends e).2) ∧
        (∀ w w', w ≠ w' → (Dv w ∩ Dv w').Nonempty → ∃ e : Section34EdgeIndex 𝒦 𝒦',
          (w = (ends e).1 ∧ w' = (ends e).2) ∨ (w = (ends e).2 ∧ w' = (ends e).1)) ∧
        (∀ e d, e ≠ d → Disjoint (Dd e) (Dd d)) ∧
        (∀ w, h '' simplexBody 𝒦' w.1 ⊆ interior (Dv w)) ∧
        (⋃ w, Dv w) ∈ nhdsSet (h '' graphSkeletonSpace 𝒦) := by
  sorry

theorem exists_section34EdgeMatching [T2Space M₁] [SecondCountableTopology M₁]
    [SecondCountableTopology M₂] [HasGroupoid M₁ (plGroupoid 3)] [HasGroupoid M₂ (plGroupoid 3)]
    (hU : IsOpen U) (hh : Topology.IsEmbedding (U.domRestrict h))
    (hframe : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hN : IsLocallyFiniteRegularNeighborhoodOf (n := 3) (section34CutNeighborhood src)
      (graphSkeletonSpace 𝒦) U)
    (hQsep : ∀ (w : Section34VertexIndex 𝒦 𝒦') (s : Section34SimplexIndex 𝒦 3),
      (Q w ∩ h '' simplexBody 𝒦 s.1).Nonempty → Section34Incident w.1 s.1)
    (hQlf : ∀ y ∈ ⋃ w, Q w, ∃ V ∈ 𝓝 y, {w | (Q w ∩ V).Nonempty}.Finite)
    (htor : Section34OuterTorus 𝒦 𝒦' h Q ct Sd)
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G)
    (Dv DvBd : Section34VertexIndex 𝒦 𝒦' → Set M₂)
    (Dd DdBd : Section34EdgeIndex 𝒦 𝒦' → Set M₂)
    (hDvdef : ∀ w, Dv w = G w '' Cp w \
      ⋃ (e : Section34EdgeIndex 𝒦 𝒦') (_ : (ends e).2 = w),
        interior (G (ends e).1 '' Cp (ends e).1))
    (hDv : ∀ w, IsPLCellOn 3 (Dv w) (DvBd w))
    (hDd : ∀ e, IsPLCellOn 2 (Dd e) (DdBd e))
    (hDmeet : ∀ e, Dv (ends e).1 ∩ Dv (ends e).2 = Dd e)
    (hDdBd : ∀ e, Dd e ⊆ DvBd (ends e).1 ∩ DvBd (ends e).2)
    (hDadj : ∀ w w', w ≠ w' → (Dv w ∩ Dv w').Nonempty → ∃ e : Section34EdgeIndex 𝒦 𝒦',
      (w = (ends e).1 ∧ w' = (ends e).2) ∨ (w = (ends e).2 ∧ w' = (ends e).1))
    (hDddisj : ∀ e d, e ≠ d → Disjoint (Dd e) (Dd d)) :
    ∃ G' : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂,
      (∀ w, IsPLHomeomorphInto 3 (G' w) (src (.vertexBall w))) ∧
        (∀ w, G' w '' src (.vertexBall w) = Dv w) ∧
        (∀ w w', EqOn (G' w) (G' w') (src (.vertexBall w) ∩ src (.vertexBall w'))) ∧
        (∀ w w', G' w '' (src (.vertexBall w) ∩ src (.vertexBall w')) =
          G' w '' src (.vertexBall w) ∩ G' w' '' src (.vertexBall w')) ∧
        (∀ s : Section34SimplexIndex 𝒦 3, h '' simplexRim 𝒦 s.1 ⊆
          interior (section34FaceTorus (fun w => G' w '' src (.vertexBall w)) s)) ∧
        ∀ s : Section34SimplexIndex 𝒦 3,
          ∃ (S₁ Te : Set (EuclideanSpace ℝ (Fin 3)))
            (Φ : section34FaceTorus (fun w => G' w '' src (.vertexBall w)) s ≃ₜ Te),
            section34FaceTorus (fun w => G' w '' src (.vertexBall w)) s ⊆ (ct s).source ∧
              (∀ y : section34FaceTorus (fun w => G' w '' src (.vertexBall w)) s,
                (Φ y : EuclideanSpace ℝ (Fin 3)) = ct s (y : M₂)) ∧
              (∀ y : section34FaceTorus (fun w => G' w '' src (.vertexBall w)) s,
                (y : M₂) ∈ h '' simplexRim 𝒦 s.1 ↔
                  (Φ y : EuclideanSpace ℝ (Fin 3)) ∈ ct s '' (h '' simplexRim 𝒦 s.1)) ∧
              IsTopologicalSolidTorus S₁ ∧ IsCombinatorialSolidTorus Te ∧
              S₁ ⊆ interior Te ∧ Te ⊆ interior (Sd s) ∧
              IsToroidalShell (closure (Sd s \ S₁)) (frontier S₁) (frontier (Sd s)) ∧
              IsSpine S₁ (ct s '' (h '' simplexRim 𝒦 s.1)) ∧
              ct s '' (h '' simplexRim 𝒦 s.1) ⊆ Te := by
  sorry

end Leaves

theorem controlledGraphNeighborhood (h341 : Moise341) :
    ControlledGraphNeighborhoodStatement.{u} := by
  intro M₁ M₂ _ _ _ _ _ _ _ _ _ U hU h hh Ea _ _ _ 𝒦 h𝒦 η H hH W hW hΓW hWU ψ hψc hψpos
  obtain ⟨-, hHsub, hHlf, -, hHcell, -⟩ := id hH
  obtain ⟨𝒦', src, srcBd, car, Q, ct, Sd, hframe, hN, hNW, hcarF, hcarS, hcarfib, hQint, hQH,
      hQsmall, hQsep, -, htorus⟩ :=
    exists_section34CutFrame hU hh 𝒦 h𝒦 η H hH hW hΓW hWU ψ hψc hψpos
  have hHfib : ∀ y ∈ h '' U, ∃ V ∈ 𝓝[h '' U] y,
      {t | ∃ w : Section34VertexIndex 𝒦 𝒦', car w = t ∧ (H t ∩ V).Nonempty}.Finite := by
    intro y hy
    obtain ⟨V, hV, hfin⟩ := hHlf y hy
    refine ⟨V, hV, hfin.subset ?_⟩
    rintro t ⟨w, hw, hmem⟩
    exact ⟨hw ▸ hcarF w, hmem⟩
  have hQlf : ∀ y ∈ ⋃ w, Q w, ∃ V ∈ 𝓝 y, {w | (Q w ∩ V).Nonempty}.Finite :=
    exists_nhds_finite_of_subset_carriers (h '' U) Q H car hQH
      (fun w => hHsub _ (hcarF w)) hcarfib hHfib
  have hQsub : ∀ w : Section34VertexIndex 𝒦 𝒦', Q w ⊆ h '' U := fun w =>
    (hQH w).trans (hHsub _ (hcarF w))
  have hQlfU : LocallyFinite fun w : Section34VertexIndex 𝒦 𝒦' =>
      {y : h '' U | (y : M₂) ∈ Q w} :=
    locallyFinite_subtype_of_subset_carriers (h '' U) Q H car hQH hcarfib hHfib
  obtain ⟨Cp, CpBd, Cc, CcBd, ends, Sn, Tn, Aa, Ab₀, Ab₁, Bb, Bb₀, Bb₁, Bc, Bc₀, Bc₁, ε,
      hprep⟩ := exists_section34VertexPreparation hU hh hframe hN hQint
  obtain ⟨G₀, hG₀, hG₀dist⟩ := h341.exists_section34VertexApproximation hh hprep
  obtain ⟨Sp, Tp, cnt, Pg, G₁, hpack, -⟩ :=
    exists_section34PiercingPackage hU hh hframe hN hQsub hQlfU hprep hG₀ hG₀dist
  have hK : ∀ w, IsCompact (H (car w)) ∧ Q w ⊆ H (car w) ∧ H (car w) ⊆ h '' U := fun w =>
    ⟨(hHcell _ (hcarF w)).isCompact, hQH w, hHsub _ (hcarF w)⟩
  obtain ⟨G₂, cnt₂, Pg₂, hpack₂, hone, -, -⟩ :=
    exists_section34ProtectedCircleRemoval hprep hpack (fun w => H (car w)) hK
  obtain ⟨Dv, DvBd, Dd, DdBd, hDvdef, hDv, hDvQ, hDd, hDmeet, hDdBd, hDadj, hDddisj, hDmark,
      hDnbhd⟩ :=
    exists_section34DeletedBalls hU hh hframe hN hQlf hprep hpack₂ hone
  obtain ⟨G, hG, hGD, hcompat, hmeet, hrim, hcert⟩ :=
    exists_section34EdgeMatching hU hh hframe hN hQsep hQlf htorus hprep hpack₂ Dv DvBd Dd
      DdBd hDvdef hDv hDd hDmeet hDdBd hDadj hDddisj
  have hGQ : ∀ w, G w '' src (Section34Label.vertexBall w) ⊆ Q w := by
    intro w
    rw [hGD w]
    exact hDvQ w
  have hmarker : ∀ w, h '' simplexBody 𝒦' w.1 ⊆
      interior (G w '' src (Section34Label.vertexBall w)) := by
    intro w
    rw [hGD w]
    exact hDmark w
  have hGnbhd : (⋃ w, G w '' src (Section34Label.vertexBall w)) ∈
      nhdsSet (h '' graphSkeletonSpace 𝒦) := by
    have hEq : (⋃ w, G w '' src (Section34Label.vertexBall w)) = ⋃ w, Dv w :=
      iUnion_congr fun w => hGD w
    rw [hEq]
    exact hDnbhd
  obtain ⟨-, -, -, hcell, -, -, -, hLF, hcover, -, -, -, -, -, -, -, -, -, -, -, -, -,
      hsplit, -, -⟩ := id hframe
  obtain ⟨-, -, htor, -, -⟩ := id htorus
  have hCclosed : ∀ w, IsClosed (src (Section34Label.vertexBall w)) := fun w =>
    (hcell _).isCompact.isClosed
  have hDclosed : ∀ w, IsClosed (G w '' src (Section34Label.vertexBall w)) := fun w =>
    ((hcell _).isCompact.image_of_continuousOn (hG w).continuousOn).isClosed
  have hsub : ∀ w, src (Section34Label.vertexBall w) ⊆ U := fun w =>
    (subset_iUnion src (Section34Label.vertexBall w)).trans hcover.subset
  have hsrcLF : ∀ x ∈ ⋃ w, src (Section34Label.vertexBall w), ∃ V ∈ 𝓝 x,
      {w | (src (Section34Label.vertexBall w) ∩ V).Nonempty}.Finite := by
    intro x hx
    obtain ⟨w₀, hw₀⟩ := mem_iUnion.mp hx
    obtain ⟨V, hV, hfin⟩ := hLF x (hsub w₀ hw₀)
    refine ⟨V, hV, Set.Finite.of_finite_image (f := fun w =>
      (Section34Label.vertexBall w : Section34CutLabelOf 𝒦 𝒦'))
      (hfin.subset ?_) ?_⟩
    · rintro _ ⟨w, hw, rfl⟩
      exact hw
    · intro a _ b _ hab
      simpa using hab
  have htgtLF : ∀ y ∈ ⋃ w, G w '' src (Section34Label.vertexBall w), ∃ V ∈ 𝓝 y,
      {w | (G w '' src (Section34Label.vertexBall w) ∩ V).Nonempty}.Finite := by
    refine exists_nhds_finite_of_subset_carriers (h '' U) _ H car
      (fun w => (hGQ w).trans (hQH w)) (fun w => hHsub _ (hcarF w)) hcarfib ?_
    intro y hy
    obtain ⟨V, hV, hfin⟩ := hHlf y hy
    refine ⟨V, hV, hfin.subset ?_⟩
    rintro t ⟨w, hw, hmem⟩
    exact ⟨hw ▸ hcarF w, hmem⟩
  obtain ⟨f₁, hf₁, hf₁G, hf₁im⟩ :=
    exists_isPLHomeomorphInto_dualCellPaste h (fun w => src (.vertexBall w)) G hCclosed
      hDclosed hG hcompat hmeet hsrcLF htgtLF
  have himg : ∀ w, f₁ '' src (Section34Label.vertexBall w) =
      G w '' src (Section34Label.vertexBall w) := fun w => (hf₁G w).image_eq
  have hfun : (fun w => f₁ '' src (Section34Label.vertexBall w)) =
      fun w => G w '' src (Section34Label.vertexBall w) := funext himg
  have hf₁Q : ∀ w, f₁ '' src (Section34Label.vertexBall w) ⊆ Q w := by
    intro w
    rw [himg w]
    exact hGQ w
  have hnbhd : f₁ '' section34CutNeighborhood src ∈ nhdsSet (h '' graphSkeletonSpace 𝒦) := by
    have hrw : f₁ '' section34CutNeighborhood src =
        ⋃ w, G w '' src (Section34Label.vertexBall w) := hf₁im
    rw [hrw]
    exact hGnbhd
  have hmer : ∀ s : Section34SimplexIndex 𝒦 3,
      CarriesFundamentalGroupOnto (h '' simplexRim 𝒦 s.1)
        (section34FaceTorus (fun w => G w '' src (Section34Label.vertexBall w)) s) := by
    intro s
    obtain ⟨S₁, Te, Φ, -, -, hΦ, hS₁, hTe, h₁T, hT₂, hshell, hspine, hJe⟩ := hcert s
    exact carriesFundamentalGroupOnto_of_nestedSolidTorus
      ((hrim s).trans interior_subset) Φ hΦ hS₁ (htor s).1 hTe h₁T hT₂ hshell hspine hJe
  refine ⟨𝒦', src, srcBd, car, f₁, hframe, hN, hNW, hf₁, hnbhd, ?_, ?_, ?_, ?_, ?_, ?_,
    hcarF, hcarS, hcarfib, ?_⟩
  · intro x hx
    obtain ⟨w, hw⟩ := mem_iUnion.mp hx
    refine hQsmall w x hw (f₁ x) (hf₁Q w ⟨x, hw, rfl⟩) (h x) ?_
    exact interior_subset (hQint w ⟨x, hw, rfl⟩)
  · intro w
    rw [himg w]
    exact hmarker w
  · intro e s hne
    obtain ⟨w, w', hww', hunion, hdisk⟩ := hsplit e
    have hwsub : src (Section34Label.splitDisk e) ⊆
        src (Section34Label.vertexBall w) := hdisk ▸ inter_subset_left
    have hw'sub : src (Section34Label.splitDisk e) ⊆
        src (Section34Label.vertexBall w') := hdisk ▸ inter_subset_right
    have hw : Section34Incident w.1 s.1 := by
      refine hQsep w s ?_
      obtain ⟨y, hy₁, hy₂⟩ := hne
      exact ⟨y, hf₁Q w (image_mono hwsub hy₁), hy₂⟩
    have hw' : Section34Incident w'.1 s.1 := by
      refine hQsep w' s ?_
      obtain ⟨y, hy₁, hy₂⟩ := hne
      exact ⟨y, hf₁Q w' (image_mono hw'sub hy₁), hy₂⟩
    have hkey : ((e.1 : Finset Ea) : Set Ea) ⊆ convexHull ℝ ((s.1 : Finset Ea) : Set Ea) := by
      rw [hunion]
      exact union_subset hw hw'
    exact hkey
  · intro w s hne
    obtain ⟨y, hy₁, hy₂⟩ := hne
    exact hQsep w s ⟨y, hf₁Q w hy₁, hy₂⟩
  · intro s
    rw [hfun]
    exact hrim s
  · intro s
    rw [hfun]
    exact hmer s
  · intro w
    refine union_subset ?_ ((hf₁Q w).trans (hQH w))
    exact fun y hy => hQH w (interior_subset (hQint w hy))

end DifferentialGeometry.Topology.PiecewiseLinear
