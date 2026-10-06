import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.LateCutGeometry

set_option autoImplicit false

/-!
# The stage/range adapter for `LateCutFamily.seam_image`

Source contract: `review-CH12-R1.md`, section 7.2, at commit `4230848283`.
The sole stage equality is directed from `postStage` to the regular slice. A
pointwise equality is proved in the slice carrier before ranges are compared.
The optional torus reparametrisation acts on the cusp side of that equality.

The assembly lemmas take the prospective fields separately: they do not require
an already constructed `LateCutFamily`, or assume its `seam_image` field.
-/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint GC.Topology Set

namespace GC.LongTime.Ch12

universe u v

/-- Compare ranges after a specified type equality, allowing a change of source
parameter. No topological identification of the target types is substituted for
the equality `hXY`. -/
theorem range_cast_eq_of_pointwise_CX4 {X Y : Type u} {A : Type v}
    (hXY : X = Y) (f : A → X) (g : A → Y) (e : A ≃ A)
    (hpoint : ∀ x, cast hXY (f (e x)) = g x) :
    range (fun x => cast hXY (f x)) = range g := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨e.symm x, by simpa using (hpoint (e.symm x)).symm⟩
  · rintro ⟨x, rfl⟩
    exact ⟨e x, hpoint x⟩

/-- Package an equality of transported ranges as the heterogeneous equality of
the original ranges. All elimination of target-type equality is localized here. -/
theorem heq_range_of_cast_range_eq_CX4 {X Y : Type u} {A : Type v}
    (hXY : X = Y) (f : A → X) (g : A → Y)
    (hrange : range (fun x => cast hXY (f x)) = range g) :
    HEq (range f) (range g) := by
  subst Y
  exact heq_of_eq hrange

variable {P : OrientedThreeStage.{u}} {g : P.Metric}
  {F : GC.Interface.RawSurgery P g}

/-- The frozen direction `e_j : postStage(t_j) = stage(slices j)`. -/
theorem postStage_eq_sliceStage_CX4 (s : RegularSlice F.observation) :
    postStage F.observation s.time = s.stage :=
  postStage_regularSlice F.observation s

/-- Cast points along the frozen stage equality, from the post-surgery carrier
to the regular-slice carrier. -/
def sliceCast_CX4 (s : RegularSlice F.observation) :
    (postStage F.observation s.time).Carrier → s.stage.Carrier :=
  cast (congrArg (fun Q : OrientedThreeStage.{u} => Q.Carrier)
    (postStage_eq_sliceStage_CX4 s))

/-- Range equality in the actual slice carrier, retaining the parametrised maps. -/
theorem sliceRange_of_pointwise_CX4 (s : RegularSlice F.observation)
    (f : Torus → (postStage F.observation s.time).Carrier)
    (seam : Torus → s.stage.Carrier) (e : Torus ≃ Torus)
    (hpoint : ∀ x, sliceCast_CX4 s (f (e x)) = seam x) :
    range (fun x => sliceCast_CX4 s (f x)) = range seam :=
  range_cast_eq_of_pointwise_CX4 _ f seam e hpoint

/-- The generic regular-slice adapter: first compare transported ranges, then
return `HEq` of the untransported ranges. -/
theorem sliceRange_heq_of_pointwise_CX4 (s : RegularSlice F.observation)
    (f : Torus → (postStage F.observation s.time).Carrier)
    (seam : Torus → s.stage.Carrier) (e : Torus ≃ Torus)
    (hpoint : ∀ x, sliceCast_CX4 s (f (e x)) = seam x) :
    HEq (range f) (range seam) :=
  heq_range_of_cast_range_eq_CX4 _ f seam
    (sliceRange_of_pointwise_CX4 s f seam e hpoint)

/-- The homogeneous range equality for a core cusp and a decomposition seam. -/
theorem seamRange_of_pointwise_CX4 {K : ℕ}
    (cores : PersistentHyperbolicCores F K) (s : RegularSlice F.observation)
    (ht : cores.start ≤ s.time) (i : Fin cores.count)
    (T : HyperbolicTruncation (cores.model i)) (q : Fin T.count)
    (C : ConnectedComponents s.stage.Carrier)
    (D : TorusDecomposition (s.stage.toClosedOrientedManifold.component C))
    (b : Fin D.boundary.count) (e : Torus ≃ Torus)
    (hpoint : ∀ x, sliceCast_CX4 s
      (cores.map i s.time ht (T.cuspMap q (e x, halfZero))) =
        (D.reconstructionAtlas.torusInPrime D.reconstruction b x).val) :
    range (fun x : Torus => sliceCast_CX4 s
      (cores.map i s.time ht (T.cuspMap q (x, halfZero)))) =
        range (fun x : Torus =>
          (D.reconstructionAtlas.torusInPrime D.reconstruction b x).val) :=
  sliceRange_of_pointwise_CX4 s _ _ e hpoint

/-- Direct adapter for one entry of the prospective `LateCutFamily.seam_image`
field. Choose `e := Equiv.refl Torus` when no reparametrisation is needed. -/
theorem seamImage_of_pointwise_CX4 {K : ℕ}
    (cores : PersistentHyperbolicCores F K) (s : RegularSlice F.observation)
    (ht : cores.start ≤ s.time) (i : Fin cores.count)
    (T : HyperbolicTruncation (cores.model i)) (q : Fin T.count)
    (C : ConnectedComponents s.stage.Carrier)
    (D : TorusDecomposition (s.stage.toClosedOrientedManifold.component C))
    (b : Fin D.boundary.count) (e : Torus ≃ Torus)
    (hpoint : ∀ x, sliceCast_CX4 s
      (cores.map i s.time ht (T.cuspMap q (e x, halfZero))) =
        (D.reconstructionAtlas.torusInPrime D.reconstruction b x).val) :
    HEq (range (fun x : Torus => cores.map i s.time ht (T.cuspMap q (x, halfZero))))
      (range (fun x : Torus =>
        (D.reconstructionAtlas.torusInPrime D.reconstruction b x).val)) :=
  heq_range_of_cast_range_eq_CX4 _ _ _
    (seamRange_of_pointwise_CX4 cores s ht i T q C D b e hpoint)

/-- Family version with exactly the binders, port lookup, and conclusion of
`LateCutFamily.seam_image`. This can fill that field during A09 assembly. -/
theorem seamImageFamily_of_pointwise_CX4 {K : ℕ}
    (slices : ℕ → RegularSlice F.observation)
    (cores : PersistentHyperbolicCores F (K + 4))
    (decomposition : ∀ j (C : ConnectedComponents (slices j).stage.Carrier),
      TorusDecomposition ((slices j).stage.toClosedOrientedManifold.component C))
    (first : ℕ) (time_late : ∀ j, first ≤ j → cores.start ≤ (slices j).time)
    (truncation : ∀ (_j : ℕ) (i : Fin cores.count), HyperbolicTruncation (cores.model i))
    (port : ∀ j, first ≤ j →
      (Σ C : ConnectedComponents (slices j).stage.Carrier,
        Fin (decomposition j C).boundary.count) ≃
          Σ i : Fin cores.count, Fin (truncation j i).count)
    (reparam : ∀ j, first ≤ j → ∀ C,
      Fin (decomposition j C).boundary.count → Torus ≃ Torus)
    (hpoint : ∀ j (hj : first ≤ j) C (b : Fin (decomposition j C).boundary.count),
      let p := port j hj ⟨C, b⟩;
      ∀ x, sliceCast_CX4 (slices j)
        (cores.map p.1 (slices j).time (time_late j hj)
          ((truncation j p.1).cuspMap p.2 (reparam j hj C b x, halfZero))) =
            ((decomposition j C).reconstructionAtlas.torusInPrime
              (decomposition j C).reconstruction b x).val) :
    ∀ j (hj : first ≤ j) C (b : Fin (decomposition j C).boundary.count),
      let p := port j hj ⟨C, b⟩;
      HEq (range (fun x : Torus => cores.map p.1 (slices j).time (time_late j hj)
        ((truncation j p.1).cuspMap p.2 (x, halfZero))))
        (range (fun x : Torus => ((decomposition j C).reconstructionAtlas.torusInPrime
          (decomposition j C).reconstruction b x).val)) := by
  intro j hj C b
  exact seamImage_of_pointwise_CX4 cores (slices j) (time_late j hj)
    (port j hj ⟨C, b⟩).1 (truncation j (port j hj ⟨C, b⟩).1)
    (port j hj ⟨C, b⟩).2 C (decomposition j C) b (reparam j hj C b)
    (hpoint j hj C b)

end GC.LongTime.Ch12
