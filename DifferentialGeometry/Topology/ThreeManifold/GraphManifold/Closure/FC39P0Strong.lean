import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyFC42FinalTheorem
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCycleIncidence
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCyclePartitionBallFace
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.SphereCertificate

/-!
# FC39 producer, packet P0 (gate 1), §4.1–§4.2: the strong certificate and leaf bounds

Task-47 draft §4 (dispositions D2, D3, D7).

* `StrongCertificate W E = {D : DecompositionCertificate W E // D.RimProduct}` and
  `StrongClosedCertificate W` (D2: `DecompositionCertificate` is NOT edited; FC42 stays in form
  (b)).
  The closed wrapper `StrongCertificate.toClosed` keeps the proof; the consumer
  `StrongCertificate.raw_or_aux_nonneg` is FC42 form (b)
  (`exists_rawGraphPresentation_or_aux_nonneg_of_certificate_of_rimProduct`) applied to
  the SAME witness; the interior hint `StrongCertificate.hint` is derived from the underlying
  certificate (the dry S14 proof), no new field.
* `UpperLeafBound` / `LowerLeafBound` / `TailLeafBound` — the generic shapes of the analytic leaf
  witnesses of §4.2 (`Out` must be the output of the concrete leaf, never rows or certificates).
  The validity records `BoundaryThresholdValidity`, `ClosedThresholdValidity`,
  `ClosedAnalyticSupply` and `RowsAt` are NOT installed: their slot leaves are UNSURE in the draft
  (§4.2) and stay targets for the review of gate 1 (`build-logs/scratch/FC39-P0/Targets.lean`).
* Inhabitants: the strong form of `standardSphereCertificate` (no handle, so its rim-product
  clause is vacuous — the nontrivial strong inhabitant is the four-kind S³ certificate of G3), and
  one elementary leaf of each shape.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

/-! ## §4.1 The strong certificate -/

/-- **§4.1** A certificate together with its rim-product clause. -/
abbrev StrongCertificate (W : CompactCarrier.{u}) {n : ℕ} (E : BoundaryTori W n) :=
  { D : DecompositionCertificate W E // D.RimProduct }

/-- **§4.1** The closed strong certificate. -/
abbrev StrongClosedCertificate (W : CompactCarrier.{u}) :=
  Σ E : BoundaryTori W 0, { D : DecompositionCertificate W E // D.RimProduct }

variable {W : CompactCarrier.{u}}

/-- The closed wrapper of a strong certificate without ports (the proof is kept). -/
def StrongCertificate.toClosed {E : BoundaryTori W 0} (D : StrongCertificate W E) :
    StrongClosedCertificate W :=
  ⟨E, D⟩

/-- The underlying closed certificate of a closed strong certificate. -/
def StrongClosedCertificate.toClosedCertificate (D : StrongClosedCertificate W) :
    ClosedDecompositionCertificate W :=
  ⟨D.1, D.2.1⟩

/-- The rim-product clause travels with the closed certificate. -/
theorem StrongClosedCertificate.rimProduct (D : StrongClosedCertificate W) :
    D.toClosedCertificate.cert.RimProduct :=
  D.2.2

/-- **The consumer**: FC42 form (b) on the SAME witness. -/
theorem StrongCertificate.raw_or_aux_nonneg (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
    {n : ℕ} {E : BoundaryTori W n} (D : StrongCertificate W E) :
    Nonempty (RawGraphPresentation W) ∨
      (W.model.boundary W.Carrier = ∅ ∧ ∃ g' : SmoothRiemannianMetric W.model W.Carrier,
        DifferentialGeometry.Geometry.Riemannian.SectionalBoundedBelow g' 0) :=
  exists_rawGraphPresentation_or_aux_nonneg_of_certificate_of_rimProduct W D.1 D.2

/-- A vertex whose model boundary image lies in the interior lies in the interior. -/
theorem image_subset_interior_of_boundaryImage {v : Vertex W}
    (h : v.boundaryImage ⊆ (W.interior : Set W.Carrier)) :
    v.image ⊆ (W.interior : Set W.Carrier) := by
  intro z hz
  rw [Vertex.image_eq_range_piece] at hz
  obtain ⟨m, rfl⟩ := hz
  by_cases hm : (𝓡∂ 3).IsBoundaryPoint m
  · exact h ⟨m, hm, rfl⟩
  · have hm' : (𝓡∂ 3).IsInteriorPoint m := by
      rw [(𝓡∂ 3).isInteriorPoint_iff_not_isBoundaryPoint]
      exact hm
    exact (v.piece.smooth.mdifferentiableAt (by simp)).isInteriorPoint_of_surjective_mfderiv
      (v.piece.mfderiv_bijective m).2 hm'

/-- **The interior hint**, derived from the underlying certificate (§4.1; the dry S14 proof). -/
theorem StrongCertificate.hint {n : ℕ} {E : BoundaryTori W n} (D : StrongCertificate W E) :
    ∀ k, (D.1.vertex k).IsBall → (D.1.vertex k).image ⊆ (W.interior : Set W.Carrier) := by
  intro k hk
  obtain ⟨x, hx⟩ := hk.boundaryImage_nonempty
  rw [← D.1.face_exhausted k] at hx
  obtain ⟨f, hx⟩ := mem_iUnion.mp hx
  obtain ⟨hfo, -⟩ := mem_iUnion.mp hx
  have hfeq := D.1.face_eq_boundaryImage_of_isBall hk hfo
  cases hkind : D.1.faceKind f with
  | partitioned => exact D.1.ball_image_subset_interior hk ⟨f, hfo, hkind⟩
  | external i =>
      exact (hk.false_of_homeomorph_torus ((D.1.face_external f i hkind).1.symm.trans hfeq)
        (E.torusMap_isEmbedding i).toHomeomorph.symm).elim
  | torusSeam c b =>
      refine image_subset_interior_of_boundaryImage ?_
      rw [← hfeq, (D.1.face_torusSeam f c b hkind).1]
      rintro _ ⟨t, rfl⟩
      have hz : (t, (0 : ℝ)) ∈ (D.1.torusSeam c).collar.source := by
        rw [(D.1.torusSeam c).source_eq]
        exact ⟨by norm_num, by norm_num⟩
      exact (D.1.torusSeam c).target_interior ((D.1.torusSeam c).collar.map_source hz)
  | sphereSeam c b =>
      refine image_subset_interior_of_boundaryImage ?_
      rw [← hfeq, (D.1.face_sphereSeam f c b hkind).1]
      rintro _ ⟨z, rfl⟩
      have hz : (z, (0 : ℝ)) ∈ (D.1.sphereSeam c).collar.source := by
        rw [(D.1.sphereSeam c).source_eq]
        exact ⟨by norm_num, by norm_num⟩
      exact (D.1.sphereSeam c).target_interior ((D.1.sphereSeam c).collar.map_source hz)

/-- The strong form of the handle-free sphere certificate (rim-product clause vacuous). -/
def standardStrongSphereCertificate :
    StrongCertificate (NoCuts.carrier standardThreeSphereLift.{u})
      (BoundaryTori.empty (NoCuts.carrier standardThreeSphereLift.{u})) :=
  ⟨standardSphereCertificate, fun h => h.elim0⟩

/-! ## §4.2 Analytic leaf witnesses -/

/-- **§4.2** An upper leaf bound: a positive bound per requirement, sound for the leaf's own
output `Out` (a local packet, an estimate, a projection, …) below the bound. -/
structure UpperLeafBound (Req : Type*) (Input : Req → Type*)
    (Hyp Out : (r : Req) → Input r → ℝ → Prop) where
  bound : Req → ℝ
  positive : ∀ r, 0 < bound r
  sound : ∀ r (x : Input r) q, 0 < q → q < bound r → Hyp r x q → Out r x q

/-- **§4.2** A lower leaf bound: sound above the bound. -/
structure LowerLeafBound (Req : Type*) (Input : Req → Type*)
    (Hyp Out : (r : Req) → Input r → ℝ → Prop) where
  bound : Req → ℝ
  sound : ∀ r (x : Input r) q, bound r ≤ q → Hyp r x q → Out r x q

/-- **§4.2** An integer tail of a leaf: sound from the tail on. -/
structure TailLeafBound (Req : Type*) (Input : Req → Type*)
    (Hyp Out : (r : Req) → Input r → ℕ → Prop) where
  tail : Req → ℕ
  sound : ∀ r (x : Input r) m, tail r ≤ m → Hyp r x m → Out r x m

/-- An elementary upper leaf: `|x| < q` below the bound `1` gives `|x| < 1`. -/
def unitUpperLeaf :
    UpperLeafBound Unit (fun _ => ℝ) (fun _ x q => |x| < q) (fun _ x _ => |x| < 1) where
  bound _ := 1
  positive _ := one_pos
  sound _ _ _ _ hq hx := hx.trans hq

/-- An elementary lower leaf: `q ≤ |x|` above the bound `1` gives `1 ≤ |x|`. -/
def unitLowerLeaf :
    LowerLeafBound Unit (fun _ => ℝ) (fun _ x q => q ≤ |x|) (fun _ x _ => 1 ≤ |x|) where
  bound _ := 1
  sound _ _ _ hq hx := hq.trans hx

/-- An elementary tail leaf: `k ≤ m` gives `k < m + 1`. -/
def natTailLeaf :
    TailLeafBound Unit (fun _ => ℕ) (fun _ k m => k ≤ m) (fun _ k m => k < m + 1) where
  tail _ := 0
  sound _ _ _ _ h := Nat.lt_succ_of_le h

end GC.GraphManifold.Assembly.FC39P0
