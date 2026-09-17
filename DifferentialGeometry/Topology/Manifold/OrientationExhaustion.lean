import DifferentialGeometry.Topology.Manifold.SmoothOrientationOpen
import DifferentialGeometry.Topology.Manifold.SmoothOrientationComparison
import DifferentialGeometry.Topology.Manifold.SmoothOrientationComposition
import DifferentialGeometry.Bundle.Orientation.Classes
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Order.OrderIsoNat
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Orientation

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.Manifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem exists_smoothOrientation_inclusion {U V : Opens M} (hUV : U ≤ V)
    (o : SmoothOrientation I V) :
    ∃ oU : SmoothOrientation I U, ∀ x : U, oU.val x = o.val ⟨x.val, hUV x.property⟩ := by
  let hbij : ∀ x : U, Bijective (mfderiv I I (Opens.inclusion hUV : U → V) x) := by
    intro x
    rw [DifferentialGeometry.mfderiv_opens_incl]
    exact bijective_id
  refine ⟨pullbackSmoothOrientation I I (Opens.inclusion hUV) (contMDiff_inclusion hUV)
    hbij o, fun x => ?_⟩
  rw [pullbackSmoothOrientation_apply]
  have he : differentialEquivOfBijective I I (Opens.inclusion hUV) hbij x =
      ContinuousLinearEquiv.refl ℝ E := by
    apply ContinuousLinearEquiv.ext
    funext v
    change mfderiv I I (Opens.inclusion hUV : U → V) x v = v
    rw [DifferentialGeometry.mfderiv_opens_incl]
    rfl
  rw [he]
  exact tangentOrientationEquiv_refl _

theorem exists_subsequence_smoothOrientation_on_monotone_open_cover
    (U : ℕ → Opens M) (hU : Monotone U) (hcover : ∀ x : M, ∃ i, x ∈ U i)
    (hconn : ∀ i, IsPreconnected (U i : Set M))
    (p : M) (hp : ∀ i, p ∈ U i) (o : ∀ i, SmoothOrientation I (U i)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ O : SmoothOrientation I M,
      ∀ i (x : U (φ i)), O.val x.val = (o (φ i)).val x := by
  classical
  let f : ℕ → Orientation ℝ E (Fin (Module.finrank ℝ E)) :=
    fun i => (o i).val ⟨p, hp i⟩
  let : Finite (Orientation ℝ E (Fin (Module.finrank ℝ E))) :=
    Finite.of_equiv Bool (VectorBundle.orientationEquivBool (Module.finBasis ℝ E)).symm
  obtain ⟨a, ha⟩ := Finite.exists_infinite_fiber f
  let _ := ha
  let φ : ℕ → ℕ := Nat.orderEmbeddingOfSet (f ⁻¹' {a})
  have hφ : StrictMono φ := (Nat.orderEmbeddingOfSet (f ⁻¹' {a})).strictMono
  have hf : ∀ i, f (φ i) = a := fun i => (Nat.Subtype.ofNat (f ⁻¹' {a}) i).2
  have hcoverφ : ∀ x : M, ∃ i, x ∈ U (φ i) := by
    intro x
    obtain ⟨i, hi⟩ := hcover x
    exact ⟨i, hU (hφ.le_apply) hi⟩
  have heq_of_le : ∀ i j (hij : i ≤ j), ∀ x : U (φ i),
      (o (φ i)).val x = (o (φ j)).val ⟨x.val, hU (hφ.monotone hij) x.property⟩ := by
    intro i j hij x
    let : PreconnectedSpace (U (φ i)) := isPreconnected_iff_preconnectedSpace.mp (hconn (φ i))
    obtain ⟨oj, hoj⟩ := exists_smoothOrientation_inclusion I (hU (hφ.monotone hij)) (o (φ j))
    have hbase : (o (φ i)).val ⟨p, hp (φ i)⟩ = oj.val ⟨p, hp (φ i)⟩ := by
      rw [hoj]
      exact (hf i).trans (hf j).symm
    exact (smoothOrientation_eq_of_eq_at I (o (φ i)) oj ⟨p, hp (φ i)⟩ hbase x).trans (hoj x)
  have heq : ∀ i j (x : M) (hi : x ∈ U (φ i)) (hj : x ∈ U (φ j)),
      (o (φ i)).val ⟨x, hi⟩ = (o (φ j)).val ⟨x, hj⟩ := by
    intro i j x hi hj
    rcases le_total i j with hij | hji
    · exact heq_of_le i j hij ⟨x, hi⟩
    · exact (heq_of_le j i hji ⟨x, hj⟩).symm
  refine ⟨φ, hφ, glueSmoothOrientations I (fun i => U (φ i)) (fun i => o (φ i)) hcoverφ heq,
    fun i x => ?_⟩
  exact glueSmoothOrientations_apply I (fun i => U (φ i)) (fun i => o (φ i)) hcoverφ heq i x

theorem exists_subsequence_preserves_smoothOrientation_on_monotone_open_cover
    {N : ℕ → Type*} [∀ i, TopologicalSpace (N i)] [∀ i, ChartedSpace H (N i)]
    [∀ i, IsManifold I ∞ (N i)]
    (U : ℕ → Opens M) (hU : Monotone U) (hcover : ∀ x : M, ∃ i, x ∈ U i)
    (hconn : ∀ i, IsPreconnected (U i : Set M)) (p : M) (hp : ∀ i, p ∈ U i)
    (Φ : ∀ i, _root_.PartialDiffeomorph I I M (N i) ∞)
    (hΦ : ∀ i, (U i : Set M) ⊆ (Φ i).source) (o : ∀ i, SmoothOrientation I (N i)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ O : SmoothOrientation I M,
      ∀ i (x : M), x ∈ U (φ i) →
        ∃ hf : Bijective (mfderiv I I (Φ (φ i) : M → N (φ i)) x),
          Orientation.map (Fin (Module.finrank ℝ E))
            (LinearEquiv.ofBijective (mfderiv I I (Φ (φ i) : M → N (φ i)) x).toLinearMap hf)
            (O.val x) = (o (φ i)).val (Φ (φ i) x) := by
  let oU := fun i => PartialDiffeomorph.pullbackSmoothOrientation (Φ i) (hΦ i) (o i)
  obtain ⟨φ, hφ, O, hO⟩ := exists_subsequence_smoothOrientation_on_monotone_open_cover I
    U hU hcover hconn p hp oU
  refine ⟨φ, hφ, O, fun i x hx => ?_⟩
  let A := ((Φ (φ i)).isLocalDiffeomorphAt I I ∞ (hΦ (φ i) hx)).mfderivToContinuousLinearEquiv
    (by simp)
  refine ⟨A.bijective, ?_⟩
  have he : LinearEquiv.ofBijective
      (mfderiv I I (Φ (φ i) : M → N (φ i)) x).toLinearMap A.bijective = A.toLinearEquiv := by
    ext v
    rfl
  rw [he, hO i ⟨x, hx⟩]
  exact PartialDiffeomorph.pullbackSmoothOrientation_map (Φ (φ i)) (hΦ (φ i))
    (o (φ i)) ⟨x, hx⟩

end DifferentialGeometry.Topology.Manifold
