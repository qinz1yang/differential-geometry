import DifferentialGeometry.Geometry.Comparison.FiniteSoul.RelativeShaveDrop
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.SoulStrictOutward
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.ExhaustionConsumers

/-!
# SOUL3: the finite soul with strict outward directions, any dimension (CMS3-REL, G4)

Lane CMS3-REL, frozen interface SOUL3 of `build-logs/scratch/D-CMS3/FiniteSoulThreeInterfaces.lean`
(`exists_finite_soul_strict_outward`, LFR45 first clause; design §0 decision 5, §3 SOUL3, review §8).

* `exists_soul_flag_of_isCompact` (the flag): every nonempty compact totally convex `C` contains a
  nonempty compact totally convex `S` with empty relative boundary such that every `q ∈ C \ S` has a unit
  vector with negative pairing against all minimizing directions to `S`. Strong induction on the
  relative dimension: if `B = relBoundary C ≠ ∅`, DROP gives the argmax set `C₁` of `h = d(·, B)` of
  strictly smaller relative dimension; points of `C \ C₁` are handled by S-SEP (kernel K2
  `exists_unit_strict_outward_of_lt`) with `φ = -h`, convex along the arcs of `C` by the REL binding —
  no boundary exception (review §3).
* `exists_finite_soul_strict_outward` (SOUL3, verbatim): the flag started at
  `C₀ = {rayExhaustion o ≤ 0}` (compact, totally convex, CMS-A); points off `C₀` are handled by K2 with
  `C = M`, `φ = rayExhaustion o`. The terminal set is a compact connected totally convex totally geodesic
  `C^r` slice without relative boundary, of dimension `< dim` (a full-dimensional one would be open and
  closed in the connected noncompact `M`).
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Metric
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.Geometry.FiniteSoul

open DifferentialGeometry.Geometry.Topology (rayExhaustion lipschitzWith_rayExhaustion
  rayExhaustion_self)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {r : ℕ∞}

/-- **The flag** (`3 ≤ r`, `sec ≥ 0`, any dimension). -/
theorem exists_soul_flag_of_isCompact [NeZero (Module.finrank ℝ E)]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 3 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂) :
    ∀ (n : ℕ) (C : Set M), maxSliceDimOfOrder I (r : ℕ∞ω) C = n → IsCompact C → C.Nonempty →
      IsTotallyConvexFinite g C →
      ∃ S ⊆ C, S.Nonempty ∧ IsCompact S ∧ IsTotallyConvexFinite g S ∧
        relBoundaryOfOrder I (r : ℕ∞ω) S = ∅ ∧
        ∀ q ∈ C, q ∉ S → ∃ v : E, g.inner q v v = 1 ∧
          ∀ u ∈ g.finiteMinimizingDirectionsTo S q, g.inner q v u < 0 := by
  have hr2 : 2 ≤ r := le_trans (by norm_num) hr
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro C hn hCc hCne hconv
    by_cases hB : (relBoundaryOfOrder I (r : ℕ∞ω) C).Nonempty
    · have hdrop := maxSliceDimOfOrder_argmax_lt g hr hnorm hsec hCc hconv hB
      dsimp only at hdrop
      obtain ⟨hC₁ne, hC₁c, hC₁conv, -, hlt⟩ := hdrop
      set B := relBoundaryOfOrder I (r : ℕ∞ω) C with hBdef
      set C₁ := {x ∈ C | ∀ y ∈ C, infDist y B ≤ infDist x B} with hC₁def
      obtain ⟨S, hSC₁, hSne, hSc, hSconv, hSB, hout⟩ :=
        ih (maxSliceDimOfOrder I (r : ℕ∞ω) C₁) (hn ▸ hlt) C₁ rfl hC₁c hC₁ne hC₁conv
      have hSC : S ⊆ C := fun x hx => (hSC₁ hx).1
      refine ⟨S, hSC, hSne, hSc, hSconv, hSB, fun q hqC hqS => ?_⟩
      by_cases hq₁ : q ∈ C₁
      · exact hout q hq₁ hqS
      · refine exists_unit_strict_outward_of_lt g hr2 hnorm hconv hSC hSc.isClosed hSne
          (φ := fun x => -infDist x B) (lipschitz_infDist_pt B).neg
          (fun p ℓ _ hmaps => (concaveOn_infDist_relBoundaryOfOrder_geodesicFlow g hr hnorm hsec
            hCc.isClosed hconv p ℓ hmaps).neg) hqC hqS fun s hs => ?_
        have hnot : ¬ ∀ y ∈ C, infDist y B ≤ infDist q B := fun h => hq₁ ⟨hqC, h⟩
        push Not at hnot
        obtain ⟨y, hyC, hy⟩ := hnot
        have hsy := (hSC₁ hs).2 y hyC
        change -infDist s B < -infDist q B
        linarith
    · refine ⟨C, subset_rfl, hCne, hCc, hconv, not_nonempty_iff_eq_empty.1 hB,
        fun q hq hqS => absurd hq hqS⟩

/-- **SOUL3** (`3 ≤ r`, i.e. `m ≥ 4`; LFR45 asks `m ≥ 8`). The frozen D-CMS3 statement, verbatim. -/
theorem exists_finite_soul_strict_outward [NeZero (Module.finrank ℝ E)] [NoncompactSpace M]
    [ConnectedSpace M]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 3 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂) :
    ∃ S : Set M, S.Nonempty ∧ IsCompact S ∧ IsConnected S ∧ IsTotallyConvexFinite g S ∧
      IsEmbeddedSliceOfOrder I (r : ℕ∞ω) (maxSliceDimOfOrder I (r : ℕ∞ω) S) S ∧
      relBoundaryOfOrder I (r : ℕ∞ω) S = ∅ ∧
      maxSliceDimOfOrder I (r : ℕ∞ω) S < Module.finrank ℝ E ∧ IsTotallyGeodesicFinite g S ∧
      ∀ q ∉ S, ∃ v : E, g.inner q v v = 1 ∧
        ∀ u ∈ g.finiteMinimizingDirectionsTo S q, g.inner q v u < 0 := by
  have hr2 : 2 ≤ r := le_trans (by norm_num) hr
  obtain ⟨o⟩ : Nonempty M := inferInstance
  have : ProperSpace M := Manifold.properSpace_of_isRiemannianManifold I
  have : SigmaCompactSpace M := inferInstance
  set C₀ : Set M := {x | rayExhaustion o x ≤ 0} with hC₀def
  obtain ⟨hC₀c, hC₀conv⟩ := isCompact_isTotallyConvexFinite_rayExhaustion_sublevel g hr2 hnorm hsec o 0
  have hoC₀ : o ∈ C₀ := by
    change rayExhaustion o o ≤ 0
    rw [rayExhaustion_self]
  obtain ⟨S, hSC₀, hSne, hSc, hSconv, hSB, hout⟩ :=
    exists_soul_flag_of_isCompact g hr hnorm hsec _ C₀ rfl hC₀c ⟨o, hoC₀⟩ hC₀conv
  have hSeq : maxSliceLocusOfOrder I (r : ℕ∞ω) S = S := relBoundaryOfOrder_eq_empty_iff.1 hSB
  have hslice : IsEmbeddedSliceOfOrder I (r : ℕ∞ω) (maxSliceDimOfOrder I (r : ℕ∞ω) S) S := by
    have h := isEmbeddedSliceOfOrder_maxSliceLocusOfOrder g hr2 hnorm hSconv
    rwa [hSeq] at h
  have htg : IsTotallyGeodesicFinite g S := by
    have h := isTotallyGeodesicFinite_maxSliceLocusOfOrder g hr2 hnorm hSconv
    rwa [hSeq] at h
  have hdim : maxSliceDimOfOrder I (r : ℕ∞ω) S < Module.finrank ℝ E := by
    by_contra hge
    push Not at hge
    have heq : maxSliceDimOfOrder I (r : ℕ∞ω) S = Module.finrank ℝ E :=
      le_antisymm (maxSliceDimOfOrder_le S) hge
    have hint := maxSliceLocusOfOrder_eq_interior g hr2 hnorm hSconv heq
    rw [hSeq] at hint
    have hopen : IsOpen S := by rw [hint]; exact isOpen_interior
    have huniv : S = univ := (IsClopen.eq_univ ⟨hSc.isClosed, hopen⟩ hSne)
    exact noncompact_univ M (huniv ▸ hSc)
  refine ⟨S, hSne, hSc, ⟨hSne, hSconv.isPreconnected_of_finite hr2 hnorm⟩, hSconv, hslice, hSB, hdim,
    htg, fun q hqS => ?_⟩
  by_cases hqC₀ : q ∈ C₀
  · exact hout q hqC₀ hqS
  · refine exists_unit_strict_outward_of_lt g hr2 hnorm (isTotallyConvexFinite_univ g)
      (subset_univ S) hSc.isClosed hSne (φ := rayExhaustion o) (lipschitzWith_rayExhaustion o)
      (fun p ℓ _ _ => (convexOn_rayExhaustion_geodesicFlow g hr2 hnorm hsec o p).subset
        (subset_univ _) (convex_Icc 0 ℓ)) (mem_univ q) hqS fun s hs => ?_
    have hs0 : rayExhaustion o s ≤ 0 := hSC₀ hs
    have hq0 : ¬ rayExhaustion o q ≤ 0 := hqC₀
    push Not at hq0
    linarith

end DifferentialGeometry.Geometry.FiniteSoul

end
