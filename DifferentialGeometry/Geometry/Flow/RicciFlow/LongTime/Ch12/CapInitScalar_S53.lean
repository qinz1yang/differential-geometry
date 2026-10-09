import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CapScalarLowerAbs_S53

/-!
# CH12-S53, group 1c: the initial scalar lower bound on the restricted window

`window_init_scalar_S53`: for a canonical static insertion witness `w` of radius `Dbig`, order
`m ≥ 2` and accuracy `ζ ≤ ε₁` (`ε₁` universal), the restriction of `w.windowMetric` to the radius-`D`
window (`D ≤ Dbig`) has `R ≥ 1/2` on `‖z‖ < D`.  (`S.base.metric 0` of the cap-window kernel.)
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.Topology.Manifold Manifold
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff Topology

namespace GC.LongTime.Ch12

universe u

theorem metricScalarAt_restrictOpenOfSubset_S53 {M : Type*} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M] [T2Space M]
    {U V : TopologicalSpace.Opens M} (hUV : U ≤ V) (g : SmoothRiemannianMetric ThreeModel V)
    (x : U) :
    metricScalarAt (g.restrictOpenOfSubset hUV) x =
      metricScalarAt g (TopologicalSpace.Opens.inclusion hUV x) := by
  have hinc : IsLocalDiffeomorph ThreeModel ThreeModel ∞ (TopologicalSpace.Opens.inclusion hUV) :=
    fun y => isLocalDiffeomorphAt_subtypeCodRestrict
      (fun z : U => hUV z.property)
      (isLocalDiffeomorph_subtype_val U y)
  have heq : g.restrictOpenOfSubset hUV =
      localPullMetric g (TopologicalSpace.Opens.inclusion hUV) hinc := by
    apply SmoothRiemannianMetric.ext_inner
    intro y v w
    rw [localPullMetric_inner, mfderiv_opens_incl]
    rfl
  rw [heq, metricScalarAt_localPull]

theorem window_init_scalar_S53 :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧
      ∀ {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
        [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
        {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
        {d : normalizedDatum g x₀ δ k} {A : ℝ} {hA : 0 < A} {Dbig : ℝ}
        {m : ℕ} {ζ : ℝ} (w : StandardCap.CanonicalStaticInsertionWitness d A hA Dbig m ζ)
        (D : ℝ) (hDD : D ≤ Dbig),
        ζ ≤ ε₁ → 2 ≤ m → ∀ z : standardCapWindow D, ‖z.val‖ < D →
          1 / 2 ≤ metricScalarAt (w.windowMetric.restrictOpenOfSubset
            (show standardCapWindow D ≤ standardCapWindow Dbig from
              fun _ hx => hx.trans_le (add_le_add hDD (le_refl 1)))) z := by
  obtain ⟨ε₁, hε₁, hb⟩ := StandardCap.exists_uniform_window_scalar_lower_bound
  refine ⟨ε₁, hε₁, ?_⟩
  intro E H M _ _ _ _ _ I _ _ _ _ _ g x₀ δ k d A hA Dbig m ζ w D hDD hζ hm z hz
  rw [metricScalarAt_restrictOpenOfSubset_S53]
  exact hb w hζ hm _ (by simpa using hz.trans_le hDD)

/-- The kernel's `map ∘ Ξ` (`map = backwardSurvivorIncomingMap`) is an injective local
diffeomorphism, as needed by `cap_scalar_lower_S53`. -/
theorem incoming_comp_isLocalDiffeo_S53 {M : Type*} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M]
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last) {s : ℝ}
    (G : (H.stage last).IncomingSlab (H.time last) s)
    (Ξ : M → H.backwardSurvivorIncomingDomain first last hle G)
    (hΞs : IsSmoothEmbedding ThreeModel ThreeModel ∞ Ξ)
    (hΞ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ξ) :
    IsLocalDiffeomorph ThreeModel ThreeModel ∞ (H.backwardSurvivorIncomingMap first last hle G ∘ Ξ) ∧
      Function.Injective (H.backwardSurvivorIncomingMap first last hle G ∘ Ξ) :=
  ⟨isLocalDiffeomorph_comp (H.backwardSurvivorIncomingMap_isLocalDiffeomorph first last hle G) hΞ,
    (H.backwardSurvivorIncomingMap_injective first last hle G).comp hΞs.isEmbedding.injective⟩

end GC.LongTime.Ch12
