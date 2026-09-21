/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DoublePointFibreAgreement
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.GeneralPositionInDoubleAssembly
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.LemmaTwoBuffered

/-!
# Sorry-first skeleton of general position in the double

The assembly `generalPositionInDoubleBuffered` below is proved for real from the five leaves of
this file, from `SingularTwoCell.nonempty_normalSingularCellData_of_fields`, from
`doublePointSet_subset_of_preimage_singleton_eq_off` and from
`exists_boundary_loop_of_buffered_homotopy`; every `sorry` is a leaf, none is inside the
assembly.  The chain is: adapted half-space charts at every point of the double, a finite cover
of the double point set by regions `closure (W j) ⊆ V j` with `V j` inside one adapted chart and
`V j ⊆ ⋃ i, W i`, then a chart-by-chart induction whose step cuts out a source piece carrying
all sheets over `closure (W k)`, perturbs the vertex map of that piece relative to a frozen
collar and glues the result back; at the last index every double point lies in the already
normalised region, which is the `crossing` field of `NormalSingularCellData`.  The leaves are
open obligations, all owned by lane H, and none of them has been reviewed.

`exists_adaptedHalfSpaceChart_in_double` (lane H, H8 and (11), unreviewed): every point of the
double of a combinatorial three manifold with boundary has arbitrarily small charts of the
maximal `plGroupoid 3` atlas adapted to the actual pair, `x ∈ C ↔ 0 ≤ ℓ (ec x)` and
`x ∈ Bd ↔ ℓ (ec x) = 0`.  Interior charts are included: there `ℓ` is positive on the whole chart
domain, so this single half-space form covers both cases and no disjunction is needed.

`exists_finiteAdaptedCover_of_doublePointSet` (lane H, H7 and B7 setup, unreviewed): from those
pointwise charts, a finite family `closure (W j) ⊆ V j` covering the compact double point set,
with the corrected invariant `V j ⊆ ⋃ i, W i` of `consult/C-answer-digest.md`, each `V j` inside
one adapted chart.  Indices beyond `n` carry the empty region, which is what lets the induction
run over `ℕ` and stop at `n`.

`SingularTwoCell.exists_cutOutPiece_of_closure_subset` (lane H, H4 and B4, unreviewed): the
cut-out source piece with boundary.  `Rc` is a finite combinatorial two manifold with boundary
inside the source disk, `Lc` its physical boundary part, `Ω` an open set with
`D.domain ∩ ⇑D ⁻¹' closure V₀ ⊆ Ω` and `D.domain ∩ Ω ⊆ Rc.space`, which is condition (10), all
sheets through the region counted in the whole source; `Ac` is the frozen collar subcomplex, a
neighbourhood in `Rc.space` of the artificial frontier `Rc.space \ Ω`, and
`Disjoint Ac.space (⇑D ⁻¹' closure V₀)` keeps the frozen set off the region to be normalised.
No hypothesis makes `⇑D ⁻¹' V` both compact and open, and the piece is not forced to be all of
`⇑D ⁻¹' V`.

`exists_small_vertexMap_relative_in_adaptedChart` (lane H, H5 and B5, unreviewed): the relative
guarded half-space general position on that piece, read in the adapted chart.  The new vertex
map agrees with `ec ∘ ⇑D` on `Ac.space` only, so the region to be normalised is not frozen; the
half-space conditions are kept with the physical boundary subcomplex `Lc` in place of
`boundaryComplex 2 Rc`; and the affine independence conclusion is the guarded arbitrary-subset
form of `exists_small_vertexMap_transverse_in_halfSpace`, with the guard
`(s ∩ Bv).card ≤ Module.finrank ℝ (LinearMap.ker ℓ) + 1` retained and with the frozen part of
`s` exempted, since frozen vertex images cannot be moved apart.

`exists_normalizationStep_on_prescribedRegion` (lane H, H6 and B6, unreviewed): the manifold
level step on a prescribed region `closure W ⊆ V`.  The uniform scale `ε` is produced before the
perturbation, as the quantifier correction of `consult/D-answer-digest.md` requires, and any
perturbation of that size glues back to a cell with the same source disk, with fibres unchanged
over the complement of `V`, the running invariants preserved, normal crossings on an open set
containing `Z ∪ closure W`, and a boundary homotopy whose whole track stays inside `Bd` and in
the relative interior of `B` there, which is condition (12).
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

open Classical in
theorem exists_adaptedHalfSpaceChart_in_double {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (K : Geometry.SimplicialComplex ℝ E)
    [Finite K.faces] (hK : IsCombinatorialManifoldWithBoundary 3 K) :
    letI := combinatorialChartedSpace (double 3 K)
      (isCombinatorialManifold_double_succ_succ K hK)
    let ι := simplicialMap K (glueEmbed₂ (PiecewiseLinear.boundaryComplex 3 K) id)
    let C := ((↑) : (double 3 K).space → E × E × ℝ) ⁻¹' (ι '' K.space)
    let Bd := ((↑) : (double 3 K).space → E × E × ℝ) ⁻¹'
      (ι '' (PiecewiseLinear.boundaryComplex 3 K).space)
    ∀ (y : (double 3 K).space) (U : Set (double 3 K).space), U ∈ 𝓝 y →
      ∃ (ec : OpenPartialHomeomorph (double 3 K).space (EuclideanSpace ℝ (Fin 3)))
        (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ),
        ec ∈ (plGroupoid 3).maximalAtlas (double 3 K).space ∧ ℓ ≠ 0 ∧
          y ∈ ec.source ∧ ec.source ⊆ U ∧
          (∀ x ∈ ec.source, x ∈ C ↔ 0 ≤ ℓ (ec x)) ∧
          (∀ x ∈ ec.source, x ∈ Bd ↔ ℓ (ec x) = 0) := by
  sorry

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

theorem exists_finiteAdaptedCover_of_doublePointSet [T2Space M] (D : SingularTwoCell M)
    (BdM C : Set M) (hloc : ∀ x ∈ D.domain, ∃ U ∈ 𝓝[D.domain] x, InjOn (⇑D) U)
    (hchart : ∀ y ∈ doublePointSet (⇑D) D.domain, ∀ U ∈ 𝓝 y,
      ∃ (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
        (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ),
        ec ∈ (plGroupoid 3).maximalAtlas M ∧ ℓ ≠ 0 ∧ y ∈ ec.source ∧ ec.source ⊆ U ∧
          (∀ x ∈ ec.source, x ∈ C ↔ 0 ≤ ℓ (ec x)) ∧
          (∀ x ∈ ec.source, x ∈ BdM ↔ ℓ (ec x) = 0)) :
    ∃ (n : ℕ) (W V : ℕ → Set M),
      (∀ j, IsOpen (W j)) ∧ (∀ j, IsOpen (V j)) ∧ (∀ j, closure (W j) ⊆ V j) ∧
        (∀ j, V j ⊆ ⋃ i, W i) ∧ (∀ j, n ≤ j → W j = ∅) ∧
        doublePointSet (⇑D) D.domain ⊆ ⋃ j, W j ∧
        ∀ j < n, ∃ (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
          (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ),
          ec ∈ (plGroupoid 3).maximalAtlas M ∧ ℓ ≠ 0 ∧ V j ⊆ ec.source ∧
            (∀ x ∈ ec.source, x ∈ C ↔ 0 ≤ ℓ (ec x)) ∧
            (∀ x ∈ ec.source, x ∈ BdM ↔ ℓ (ec x) = 0) := by
  sorry

theorem SingularTwoCell.exists_cutOutPiece_of_closure_subset [T2Space M] (D : SingularTwoCell M)
    {V₀ V : Set M} (hV : IsOpen V) (hV₀ : closure V₀ ⊆ V) :
    ∃ (Rc Lc Ac : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
      (Ω Nb : Set (EuclideanSpace ℝ (Fin 2))),
      Rc.faces.Finite ∧ IsCombinatorialManifoldWithBoundary 2 Rc ∧
        Lc.faces ⊆ Rc.faces ∧ Ac.faces ⊆ Rc.faces ∧
        Rc.space ⊆ D.domain ∧ Rc.space ⊆ ⇑D ⁻¹' V ∧
        Lc.space = Rc.space ∩ frontier D.domain ∧
        IsOpen Ω ∧ D.domain ∩ ⇑D ⁻¹' closure V₀ ⊆ Ω ∧ D.domain ∩ Ω ⊆ Rc.space ∧
        IsOpen Nb ∧ Rc.space \ Ω ⊆ Nb ∧ Rc.space ∩ Nb ⊆ Ac.space ∧
        Disjoint Ac.space (⇑D ⁻¹' closure V₀) := by
  sorry

open Classical in
theorem exists_small_vertexMap_relative_in_adaptedChart [T2Space M] (D : SingularTwoCell M)
    {BdM C V : Set M} (hloc : ∀ x ∈ D.domain, ∃ U ∈ 𝓝[D.domain] x, InjOn (⇑D) U)
    (hfiber : ∀ y, (D.domain ∩ ⇑D ⁻¹' {y}).encard ≤ 2)
    (hproper : D.domain ∩ ⇑D ⁻¹' BdM = frontier D.domain)
    (hmapC : MapsTo (⇑D) D.domain C)
    (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ) (hec : ec ∈ (plGroupoid 3).maximalAtlas M)
    (hℓ : ℓ ≠ 0) (hVec : V ⊆ ec.source)
    (hCchart : ∀ x ∈ ec.source, x ∈ C ↔ 0 ≤ ℓ (ec x))
    (hBdchart : ∀ x ∈ ec.source, x ∈ BdM ↔ ℓ (ec x) = 0)
    (Rc Lc Ac : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    (hRfin : Rc.faces.Finite) (hRman : IsCombinatorialManifoldWithBoundary 2 Rc)
    (hLR : Lc.faces ⊆ Rc.faces) (hAR : Ac.faces ⊆ Rc.faces)
    (hRdom : Rc.space ⊆ D.domain) (hRV : Rc.space ⊆ ⇑D ⁻¹' V)
    (hLspace : Lc.space = Rc.space ∩ frontier D.domain) {ε : ℝ} (hε : 0 < ε) :
    ∃ (Rs : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
      (Bv : Finset (EuclideanSpace ℝ (Fin 2)))
      (φ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)),
      IsSubdivision Rs Rc ∧ Rs.faces.Finite ∧
        (Bv : Set (EuclideanSpace ℝ (Fin 2))) ⊆ Rs.vertices ∧
        (∀ v ∈ Rs.vertices, v ∈ Bv ↔ v ∈ Lc.space) ∧
        EqOn (simplicialMap Rs φ) (fun x => ec (D x)) Ac.space ∧
        IsPiecewiseAffineOn (simplicialMap Rs φ) Rc.space ∧
        (∀ x ∈ Rc.space, dist (simplicialMap Rs φ x) (ec (D x)) < ε) ∧
        IsLocallyInjective (Rc.space.domRestrict (simplicialMap Rs φ)) ∧
        (∀ y, (Rc.space ∩ simplicialMap Rs φ ⁻¹' {y}).encard ≤ 2) ∧
        (∀ x ∈ Rc.space, 0 ≤ ℓ (simplicialMap Rs φ x)) ∧
        (∀ x ∈ Rc.space, ℓ (simplicialMap Rs φ x) = 0 ↔ x ∈ Lc.space) ∧
        ∀ s : Finset (EuclideanSpace ℝ (Fin 2)),
          (s : Set (EuclideanSpace ℝ (Fin 2))) ⊆ Rs.vertices → s.card ≤ 4 →
            (s ∩ Bv).card ≤ Module.finrank ℝ (LinearMap.ker ℓ) + 1 →
            AffineIndependent ℝ
              (fun v : (s.filter fun x => x ∈ Ac.space) => φ (v : EuclideanSpace ℝ (Fin 2))) →
            AffineIndependent ℝ (fun v : s => φ (v : EuclideanSpace ℝ (Fin 2))) := by
  sorry

open Classical in
theorem exists_normalizationStep_on_prescribedRegion [T2Space M] (D : SingularTwoCell M)
    {BdM B C Z O W V : Set M}
    (hloc : ∀ x ∈ D.domain, ∃ U ∈ 𝓝[D.domain] x, InjOn (⇑D) U)
    (hfiber : ∀ y, (D.domain ∩ ⇑D ⁻¹' {y}).encard ≤ 2)
    (hproper : D.domain ∩ ⇑D ⁻¹' BdM = frontier D.domain)
    (hmapC : MapsTo (⇑D) D.domain C)
    (hbuffer : ∀ z ∈ Set.range D.boundary, B ∈ 𝓝[BdM] z)
    (hOopen : IsOpen O) (hZO : Z ⊆ O)
    (hnormal : ∀ y ∈ doublePointSet (⇑D) D.domain ∩ O,
      ∃ e₀ ∈ atlas (EuclideanSpace ℝ (Fin 3)) M, y ∈ e₀.source ∧
        HasPLNormalDoubleCrossingAt (e₀ ∘ ⇑D) (D.domain ∩ ⇑D ⁻¹' e₀.source)
          (e₀ '' (e₀.source ∩ BdM)) (e₀ y))
    (hWopen : IsOpen W) (hWV : closure W ⊆ V)
    (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ) (hec : ec ∈ (plGroupoid 3).maximalAtlas M)
    (hℓ : ℓ ≠ 0) (hVec : V ⊆ ec.source)
    (hCchart : ∀ x ∈ ec.source, x ∈ C ↔ 0 ≤ ℓ (ec x))
    (hBdchart : ∀ x ∈ ec.source, x ∈ BdM ↔ ℓ (ec x) = 0)
    (Rc Lc Ac : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    {Ω Nb : Set (EuclideanSpace ℝ (Fin 2))}
    (hRfin : Rc.faces.Finite) (hRman : IsCombinatorialManifoldWithBoundary 2 Rc)
    (hLR : Lc.faces ⊆ Rc.faces) (hAR : Ac.faces ⊆ Rc.faces)
    (hRdom : Rc.space ⊆ D.domain) (hRV : Rc.space ⊆ ⇑D ⁻¹' V)
    (hLspace : Lc.space = Rc.space ∩ frontier D.domain)
    (hΩ : IsOpen Ω) (hΩcover : D.domain ∩ ⇑D ⁻¹' closure W ⊆ Ω)
    (hΩR : D.domain ∩ Ω ⊆ Rc.space) (hNb : IsOpen Nb) (hNbfr : Rc.space \ Ω ⊆ Nb)
    (hNbA : Rc.space ∩ Nb ⊆ Ac.space) (hAfree : Disjoint Ac.space (⇑D ⁻¹' closure W)) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ (Rs : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
        (Bv : Finset (EuclideanSpace ℝ (Fin 2)))
        (φ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)),
        IsSubdivision Rs Rc → Rs.faces.Finite →
        (Bv : Set (EuclideanSpace ℝ (Fin 2))) ⊆ Rs.vertices →
        (∀ v ∈ Rs.vertices, v ∈ Bv ↔ v ∈ Lc.space) →
        EqOn (simplicialMap Rs φ) (fun x => ec (D x)) Ac.space →
        IsPiecewiseAffineOn (simplicialMap Rs φ) Rc.space →
        (∀ x ∈ Rc.space, dist (simplicialMap Rs φ x) (ec (D x)) < ε) →
        IsLocallyInjective (Rc.space.domRestrict (simplicialMap Rs φ)) →
        (∀ y, (Rc.space ∩ simplicialMap Rs φ ⁻¹' {y}).encard ≤ 2) →
        (∀ x ∈ Rc.space, 0 ≤ ℓ (simplicialMap Rs φ x)) →
        (∀ x ∈ Rc.space, ℓ (simplicialMap Rs φ x) = 0 ↔ x ∈ Lc.space) →
        (∀ s : Finset (EuclideanSpace ℝ (Fin 2)),
          (s : Set (EuclideanSpace ℝ (Fin 2))) ⊆ Rs.vertices → s.card ≤ 4 →
            (s ∩ Bv).card ≤ Module.finrank ℝ (LinearMap.ker ℓ) + 1 →
            AffineIndependent ℝ
              (fun v : (s.filter fun x => x ∈ Ac.space) => φ (v : EuclideanSpace ℝ (Fin 2))) →
            AffineIndependent ℝ (fun v : s => φ (v : EuclideanSpace ℝ (Fin 2)))) →
        ∃ (D' : SingularTwoCell M) (O' : Set M)
          (H : ContinuousMap (unitInterval × frontier D.domain) M),
          D'.domain = D.domain ∧ MapsTo (⇑D') D'.domain C ∧
            (∀ z ∉ V, (⇑D') ⁻¹' {z} = (⇑D) ⁻¹' {z}) ∧
            (∀ x ∈ D'.domain, ∃ U ∈ 𝓝[D'.domain] x, InjOn (⇑D') U) ∧
            (∀ y, (D'.domain ∩ ⇑D' ⁻¹' {y}).encard ≤ 2) ∧
            D'.domain ∩ ⇑D' ⁻¹' BdM = frontier D'.domain ∧
            IsOpen O' ∧ Z ∪ closure W ⊆ O' ∧
            (∀ y ∈ doublePointSet (⇑D') D'.domain ∩ O',
              ∃ e₁ ∈ atlas (EuclideanSpace ℝ (Fin 3)) M, y ∈ e₁.source ∧
                HasPLNormalDoubleCrossingAt (e₁ ∘ ⇑D') (D'.domain ∩ ⇑D' ⁻¹' e₁.source)
                  (e₁ '' (e₁.source ∩ BdM)) (e₁ y)) ∧
            (∀ x : frontier D.domain, H (0, x) = D x) ∧
            (∀ x : frontier D.domain, H (1, x) = D' x) ∧
            ∀ (t : unitInterval) (x : frontier D.domain),
              H (t, x) ∈ BdM ∧ B ∈ 𝓝[BdM] (H (t, x)) := by
  sorry

open Classical in
theorem generalPositionInDoubleBuffered : GeneralPositionInDoubleBufferedStatement := by
  classical
  intro E _ _ _ S K
  let _ : Finite K.faces := S.manifoldComplex_faces_finite.to_subtype
  let _ := combinatorialChartedSpace (double 3 K)
    (isCombinatorialManifold_double_succ_succ K S.isManifold)
  let _ : PathConnectedSpace S.boundaryNeighborhoodSpace :=
    S.boundaryNeighborhoodPathConnectedSpace
  intro ι C Bd B G β γ hloc hfiber _ hbuffer _ hmapC hproper hsurj hparam havoid
  have hBspace : S.boundaryNeighborhood.space ⊆ K.space := fun x hx =>
    PiecewiseLinear.boundaryComplex_space_subset 3 K
      (derivedNeighborhood_space_subset S.boundaryComplex S.loopComplex hx)
  obtain ⟨n, W, V, hWopen, hVopen, hWV, hVW, hWn, hdpG, hcharts⟩ :=
    exists_finiteAdaptedCover_of_doublePointSet G Bd C hloc
      fun y _ U hU => exists_adaptedHalfSpaceChart_in_double K S.isManifold y U hU
  have hUW : ⋃ j, W j ⊆ ⋃ j, ⋃ (_ : j < n), closure (W j) := by
    refine iUnion_subset fun j => ?_
    by_cases hj : j < n
    · exact fun x hx => mem_iUnion.2 ⟨j, mem_iUnion.2 ⟨hj, subset_closure hx⟩⟩
    · rw [hWn j (not_lt.mp hj)]
      exact empty_subset _
  have key : ∀ k : ℕ, ∃ (cell : SingularTwoCell (double 3 K).space)
      (Ok : Set (double 3 K).space) (b : ContinuousMap loopCircle (frontier cell.domain))
      (g : freeLoop S.boundaryNeighborhoodSpace),
      cell.domain = G.domain ∧ MapsTo (⇑cell) cell.domain C ∧
        (∀ x ∈ cell.domain, ∃ U ∈ 𝓝[cell.domain] x, InjOn (⇑cell) U) ∧
        (∀ y, (cell.domain ∩ ⇑cell ⁻¹' {y}).encard ≤ 2) ∧
        cell.domain ∩ ⇑cell ⁻¹' Bd = frontier cell.domain ∧
        (∀ z ∈ Set.range cell.boundary, B ∈ 𝓝[Bd] z) ∧
        doublePointSet (⇑cell) cell.domain ⊆ ⋃ j, W j ∧
        IsOpen Ok ∧ (⋃ j, ⋃ (_ : j < k), closure (W j)) ⊆ Ok ∧
        (∀ y ∈ doublePointSet (⇑cell) cell.domain ∩ Ok,
          ∃ e₂ ∈ atlas (EuclideanSpace ℝ (Fin 3)) (double 3 K).space, y ∈ e₂.source ∧
            HasPLNormalDoubleCrossingAt (e₂ ∘ ⇑cell) (cell.domain ∩ ⇑cell ⁻¹' e₂.source)
              (e₂ '' (e₂.source ∩ Bd)) (e₂ y)) ∧
        Function.Surjective b ∧
        (∀ θ, ((cell (b θ) : (double 3 K).space) : E × E × ℝ) = ι (g θ)) ∧
        ¬loopClassMeets g S.basepoint S.normalSubgroup := by
    intro k
    induction k with
    | zero =>
        refine ⟨G, ∅, β, γ, rfl, hmapC, hloc, hfiber, hproper, hbuffer, hdpG, isOpen_empty,
          ?_, ?_, hsurj, hparam, havoid⟩
        · exact iUnion_subset fun j => iUnion_subset fun hj => absurd hj (Nat.not_lt_zero j)
        · exact fun y hy => absurd hy.2 (notMem_empty y)
    | succ k ih =>
        obtain ⟨cell, Ok, b, g, hdom, hcellC, hcellloc, hcellfib, hcellpr, hcellbuf,
          hcelldp, hOkopen, hOkZ, hOkcross, hbsurj, hbparam, hbavoid⟩ := ih
        by_cases hk : k < n
        · obtain ⟨ec, ℓ, hec, hℓ, hVec, hCchart, hBdchart⟩ := hcharts k hk
          obtain ⟨Rc, Lc, Ac, Ω, Nb, hRfin, hRman, hLR, hAR, hRdom, hRV, hLspace, hΩ,
            hΩcover, hΩR, hNb, hNbfr, hNbA, hAfree⟩ :=
            cell.exists_cutOutPiece_of_closure_subset (V₀ := W k) (hVopen k) (hWV k)
          obtain ⟨ε, hε, hstep⟩ :=
            exists_normalizationStep_on_prescribedRegion (Z := Ok) cell hcellloc hcellfib
              hcellpr hcellC hcellbuf hOkopen Subset.rfl hOkcross (hWopen k) (hWV k) ec ℓ
              hec hℓ hVec hCchart hBdchart Rc Lc Ac hRfin hRman hLR hAR hRdom hRV hLspace
              hΩ hΩcover hΩR hNb hNbfr hNbA hAfree
          obtain ⟨Rs, Bv, φ, hsub, hRsfin, hBvsub, hBvL, hfrozen, hpl, hsmall, hplocinj,
            hpcard, hpnonneg, hpzero, hguard⟩ :=
            exists_small_vertexMap_relative_in_adaptedChart cell hcellloc hcellfib hcellpr
              hcellC ec ℓ hec hℓ hVec hCchart hBdchart Rc Lc Ac hRfin hRman hLR hAR hRdom
              hRV hLspace hε
          obtain ⟨cell', O', H, hdom', hC', hfib', hloc', hcard', hpr', hO'open, hO'Z,
            hcross', hH0, hH1, hHtrack⟩ :=
            hstep Rs Bv φ hsub hRsfin hBvsub hBvL hfrozen hpl hsmall hplocinj hpcard
              hpnonneg hpzero hguard
          have hbuf' : ∀ z ∈ Set.range cell'.boundary, B ∈ 𝓝[Bd] z := by
            rintro _ ⟨x, rfl⟩
            have hx : (x : EuclideanSpace ℝ (Fin 2)) ∈ frontier cell.domain := by
              rw [← hdom']
              exact x.2
            have h1 := hHtrack 1 ⟨(x : EuclideanSpace ℝ (Fin 2)), hx⟩
            rw [hH1 ⟨(x : EuclideanSpace ℝ (Fin 2)), hx⟩] at h1
            exact h1.2
          have hdpnew : doublePointSet (⇑cell') cell'.domain ⊆ ⋃ j, W j := by
            rw [hdom']
            exact doublePointSet_subset_of_preimage_singleton_eq_off cell.domain hfib'
              hcelldp (hVW k)
          have hHB : ∀ (t : unitInterval) (x : frontier cell.domain), H (t, x) ∈ B :=
            fun t x => mem_of_mem_nhdsWithin (hHtrack t x).1 (hHtrack t x).2
          obtain ⟨c, δ, hcδ, hδavoid⟩ :=
            exists_boundary_loop_of_buffered_homotopy S K cell cell' b g hdom' hC' hbparam
              hbavoid hbsurj H hH0 hH1 hHB hBspace
          refine ⟨cell', O', ⟨c, c.continuous⟩, δ, hdom'.trans hdom, hC', hloc', hcard',
            hpr', hbuf', hdpnew, hO'open, ?_, hcross', c.surjective, hcδ, hδavoid⟩
          refine iUnion_subset fun j => iUnion_subset fun hj => ?_
          by_cases hjk : j < k
          · exact fun x hx =>
              hO'Z (mem_union_left _ (hOkZ (mem_iUnion.2 ⟨j, mem_iUnion.2 ⟨hjk, hx⟩⟩)))
          · have hjeq : j = k := by omega
            subst hjeq
            exact fun x hx => hO'Z (mem_union_right _ hx)
        · refine ⟨cell, Ok, b, g, hdom, hcellC, hcellloc, hcellfib, hcellpr, hcellbuf,
            hcelldp, hOkopen, ?_, hOkcross, hbsurj, hbparam, hbavoid⟩
          refine iUnion_subset fun j => iUnion_subset fun hj => ?_
          by_cases hjk : j < k
          · exact fun x hx => hOkZ (mem_iUnion.2 ⟨j, mem_iUnion.2 ⟨hjk, hx⟩⟩)
          · rw [hWn j (by omega), closure_empty]
            exact empty_subset _
  obtain ⟨A, On, b, g, hdom, hAC, hAloc, hAfib, hApr, hAbuf, hAdp, -, hOnZ, hAcross,
    hbsurj, hbparam, hbavoid⟩ := key n
  have hAcross' : ∀ y ∈ doublePointSet (⇑A) A.domain,
      ∃ e₃ ∈ atlas (EuclideanSpace ℝ (Fin 3)) (double 3 K).space, y ∈ e₃.source ∧
        HasPLNormalDoubleCrossingAt (e₃ ∘ ⇑A) (A.domain ∩ ⇑A ⁻¹' e₃.source)
          (e₃ '' (e₃.source ∩ Bd)) (e₃ y) :=
    fun y hy => hAcross y ⟨hy, hOnZ (hUW (hAdp hy))⟩
  have hAbd : Set.range A.boundary ⊆ B := by
    rintro _ ⟨x, rfl⟩
    have hx : (x : EuclideanSpace ℝ (Fin 2)) ∈ A.domain ∩ ⇑A ⁻¹' Bd := by
      rw [hApr]
      exact x.2
    exact mem_of_mem_nhdsWithin hx.2 (hAbuf _ ⟨x, rfl⟩)
  have hAimage : A '' A.domain ∩ Bd = Set.range A.boundary := by
    rw [← image_inter_preimage, hApr]
    ext y
    exact ⟨fun ⟨x, hx, hxy⟩ => ⟨⟨x, hx⟩, hxy⟩, fun ⟨x, hxy⟩ => ⟨x, x.2, hxy⟩⟩
  obtain ⟨hA⟩ := SingularTwoCell.nonempty_normalSingularCellData_of_fields (double 3 K)
    (isCombinatorialManifold_double_succ_succ K S.isManifold) A Bd B hAloc hAfib hAbd
    hAimage hAcross'
  obtain ⟨c, δ, hcδ, hδavoid⟩ :=
    exists_boundary_loop_of_buffered_homotopy S K A A b g rfl hAC hbparam hbavoid hbsurj
      ⟨fun z => A.boundary z.2, A.boundary.continuous.comp continuous_snd⟩
      (fun _ => rfl) (fun _ => rfl) (fun _ x => hAbd (mem_range_self x)) hBspace
  exact ⟨A, hA, hdom, hAC, hAbuf, c, δ, hcδ, hδavoid⟩

end DifferentialGeometry.Topology.PiecewiseLinear
