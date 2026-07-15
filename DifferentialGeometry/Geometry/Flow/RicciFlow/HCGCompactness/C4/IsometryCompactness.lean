import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MapConvergence
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option autoImplicit false

/-!
# Compactness of a sequence of isometries (MSM135 Chapter 4, `lbl374`)

The corollary to Arzelà–Ascoli (Lemma 3.14) that a sequence of isometries
`Φₖ : (𝒰, gₖ) → (𝒱, hₖ)` between bounded open sets of `ℝⁿ`, with the `gₖ`/`hₖ`
uniformly equivalent to the Euclidean metric and all Euclidean covariant derivatives
bounded, has a subsequence converging in `C^∞` uniformly on compact sets to a `C^∞`
diffeomorphism `Φ_∞`.

**Honest-input boundary.**  The book derives, from the isometry relation
`(gₖ)_{ab} = ∂Φₖ^α/∂xᵃ · ∂Φₖ^β/∂xᵇ · (hₖ)_{αβ}` (`lbl375`), that all iterated
Euclidean derivatives of `Φₖ` are uniformly bounded on compact sets — by expressing
`∂²Φₖ`, then inductively all `∂ʳΦₖ`, as polynomials in `gₖ, gₖ⁻¹, hₖ, hₖ⁻¹` and their
first derivatives and `∂Φₖ`.  The book attributes this explicit polynomial recursion to
§5 of [H6].  We take that conclusion as the honest-input predicate
`IsometryDerivBounds` and prove the analytic corollary on top of it via the
Arzelà–Ascoli-for-maps engine `exists_cInf_subseq` (`MapConvergence.lean`).
-/

namespace DifferentialGeometry
namespace HCGCompactness

open Filter Topology

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- **Honest-input (MSM135 `lbl375` → [H6] §5).**  The derivative-bound conclusion of
the isometry relation: for an isometry sequence between metrics uniformly equivalent to
the Euclidean metric with bounded Euclidean covariant derivatives, every iterated
Euclidean derivative `∇ʳΦₖ` is uniformly bounded (over `k`) on each compact set.

This is exactly the hypothesis the Arzelà–Ascoli-for-maps engine consumes; the geometric
derivation (the polynomial recursion the book cites to §5 of [H6]) is taken as input. -/
def IsometryDerivBounds (Φ : ℕ → E → F) : Prop :=
  ∀ r : ℕ, ∀ K : Set E, IsCompact K →
    ∃ M : ℝ, ∀ k : ℕ, ∀ x ∈ K, ‖iteratedFDeriv ℝ r (Φ k) x‖ ≤ M

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- A sub-sequence still has the uniform derivative bounds. -/
theorem IsometryDerivBounds.comp_subseq {Φ : ℕ → E → F} (h : IsometryDerivBounds Φ)
    (φ : ℕ → ℕ) : IsometryDerivBounds (fun k => Φ (φ k)) := by
  intro r K hK
  obtain ⟨M, hM⟩ := h r K hK
  exact ⟨M, fun k x hx => hM (φ k) x hx⟩

/-- **MSM135 Corollary "Compactness of a sequence of isometries"** (`lbl374`),
convergence core.  From the honest-input derivative bounds (`lbl375`/[H6] §5), a
subsequence of the smooth maps `Φₖ` converges in `C^∞` uniformly on compact sets to a
smooth limit.  (Pure application of the Arzelà–Ascoli-for-maps engine; the diffeomorphism
clause is added in `isometry_seq_diffeo`.) -/
theorem isometry_seq_cInf
    (Φ : ℕ → E → F) (hΦ : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (Φ k))
    (hbdd : IsometryDerivBounds Φ) :
    ∃ (φ : ℕ → ℕ) (Φinf : E → F),
      StrictMono φ ∧ ContDiff ℝ (⊤ : ℕ∞) Φinf ∧
        MapCInfConvOnCompacts Set.univ (fun k => Φ (φ k)) Φinf :=
  exists_cInf_subseq Φ hΦ hbdd

omit [FiniteDimensional ℝ E] in
/-- **Invertibility of the limit (the "by symmetry" step of `lbl374`).**  If `Φₖ → Φ_∞`
and `Ψₖ → Ψ_∞` in `C^∞` uniformly on compacts, `Φ_∞` is continuous, and `Φₖ ∘ Ψₖ = id`,
then `Φ_∞ ∘ Ψ_∞ = id` pointwise.  Used both ways to make the limit a diffeomorphism;
proved by the uniform-limit composition rule `TendstoUniformlyOn.tendsto_comp` over a
compact neighborhood of `Ψ_∞ x`, plus uniqueness of limits. -/
theorem comp_eq_id_of_cInf
    {Φ : ℕ → F → E} {Φinf : F → E} {Ψ : ℕ → E → F} {Ψinf : E → F}
    (hΦ : MapCInfConvOnCompacts Set.univ Φ Φinf) (hΦc : Continuous Φinf)
    (hΨ : MapCInfConvOnCompacts Set.univ Ψ Ψinf)
    (hid : ∀ k x, Φ k (Ψ k x) = x) :
    ∀ x, Φinf (Ψinf x) = x := by
  intro x
  have hΨx : Tendsto (fun k => Ψ k x) atTop (𝓝 (Ψinf x)) :=
    tendsto_of_cInf hΨ (Set.mem_univ x)
  obtain ⟨K, hKmem, hKcomp, -⟩ := exists_mem_nhds_isCompact_isClosed (Ψinf x)
  have hΦunif : TendstoUniformlyOn Φ Φinf atTop K :=
    tendstoUniformlyOn_of_cPConv (hΦ K hKcomp (Set.subset_univ K) 0)
  have hΨxK : Tendsto (fun k => Ψ k x) atTop (𝓝[K] (Ψinf x)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hΨx (hΨx.eventually_mem hKmem)
  have hcomp : Tendsto (fun k => Φ k (Ψ k x)) atTop (𝓝 (Φinf (Ψinf x))) :=
    hΦunif.tendsto_comp hΦc.continuousWithinAt hΨxK
  simp only [hid] at hcomp
  exact (tendsto_nhds_unique tendsto_const_nhds hcomp).symm

/-- **MSM135 Corollary "Compactness of a sequence of isometries"** (`lbl374`), full
statement.  A sequence of smooth invertible maps `Φₖ : E → F` (with smooth inverses `Ψₖ`)
whose families `Φₖ`, `Ψₖ` both satisfy the honest-input isometry derivative bounds
(`lbl375`/[H6] §5) has a subsequence converging in `C^∞` uniformly on compact sets to a
`C^∞` diffeomorphism: the limit `Φ_∞` has a smooth two-sided inverse `Ψ_∞` obtained as the
limit of the `Ψₖ`. -/
theorem isometry_seq_diffeo
    (Φ : ℕ → E → F) (Ψ : ℕ → F → E)
    (hΦ : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (Φ k)) (hΨ : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (Ψ k))
    (hbΦ : IsometryDerivBounds Φ) (hbΨ : IsometryDerivBounds Ψ)
    (hLeft : ∀ k x, Ψ k (Φ k x) = x) (hRight : ∀ k y, Φ k (Ψ k y) = y) :
    ∃ (φ : ℕ → ℕ) (Φinf : E → F) (Ψinf : F → E),
      StrictMono φ ∧ ContDiff ℝ (⊤ : ℕ∞) Φinf ∧ ContDiff ℝ (⊤ : ℕ∞) Ψinf ∧
        MapCInfConvOnCompacts Set.univ (fun k => Φ (φ k)) Φinf ∧
        MapCInfConvOnCompacts Set.univ (fun k => Ψ (φ k)) Ψinf ∧
        (∀ x, Ψinf (Φinf x) = x) ∧ (∀ y, Φinf (Ψinf y) = y) := by
  obtain ⟨φ1, Φinf, hφ1, hΦinf, hΦconv⟩ := exists_cInf_subseq Φ hΦ hbΦ
  obtain ⟨φ2, Ψinf, hφ2, hΨinf, hΨconv⟩ :=
    exists_cInf_subseq (fun k => Ψ (φ1 k)) (fun k => hΨ (φ1 k)) (hbΨ.comp_subseq φ1)
  have hΦconv' : MapCInfConvOnCompacts Set.univ (fun k => Φ (φ1 (φ2 k))) Φinf :=
    hΦconv.comp_subseq hφ2
  refine ⟨φ1 ∘ φ2, Φinf, Ψinf, hφ1.comp hφ2, hΦinf, hΨinf, hΦconv', hΨconv, ?_, ?_⟩
  · exact comp_eq_id_of_cInf hΨconv hΨinf.continuous hΦconv'
      (fun k x => hLeft (φ1 (φ2 k)) x)
  · exact comp_eq_id_of_cInf hΦconv' hΦinf.continuous hΨconv
      (fun k y => hRight (φ1 (φ2 k)) y)

end HCGCompactness
end DifferentialGeometry
