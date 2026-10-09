import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ClosedThresholdA01
import DifferentialGeometry.Geometry.Collapse.LocalExport.ClosedMemberModel
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.RawLiftAlongUL
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.RegularSublevelAtlas

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Manifold Set MeasureTheory
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff ENNReal
namespace DifferentialGeometry.Geometry.Collapse
universe u

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

namespace ClosedModel

variable {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier}
  (M : ClosedModel W g)

theorem psi_bij_UL (x : M.X) :
    Function.Bijective (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) W.model M.ψ x) :=
  (M.ψ.mfderivToContinuousLinearEquiv (by simp) x).bijective

/-- The orientation of the universe-`0` carrier of a closed model: the pullback of the member's
orientation along `ψ`. -/
def orientation_UL : ManifoldOrientation (𝓡 3) M.X 3 :=
  Topology.Manifold.manifoldOrientationPullback (𝓡 3) W.model finrank_euclideanSpace_fin M.ψ
    M.ψ.contMDiff M.psi_bij_UL W.orientation

/-- The universe-`0` compact carrier of a closed model. -/
abbrev carrier_UL : CompactCarrier.{0} where
  kind := .closed
  Carrier := M.X
  orientation := M.orientation_UL

/-- `ψ` as a diffeomorphism of the universe-`0` carrier onto the member. -/
def psi_UL : M.carrier_UL.Carrier ≃ₘ⟮M.carrier_UL.model, W.model⟯ W.Carrier := M.ψ

theorem psi_UL_preservesOrientation :
    M.psi_UL.preservesOrientation M.carrier_UL.orientation W.orientation := by
  rintro (x : M.X)
  refine Eq.trans ?_ (Topology.Manifold.orientation_map_manifoldOrientationPullback (𝓡 3)
    W.model finrank_euclideanSpace_fin M.ψ M.ψ.contMDiff M.psi_bij_UL W.orientation x)
  exact congrArg (fun L : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) x ≃ₗ[ℝ]
      TangentSpace W.model (M.ψ x) => Orientation.map (Fin 3) L (M.orientation_UL.orientation x))
    (LinearEquiv.ext fun v => rfl)

theorem curvatureRadius_ne_top_UL (hfin : ∀ p, curvatureRadius g p ≠ ⊤) (p : M.X) :
    curvatureRadius M.gX p ≠ ⊤ := by
  rw [M.curvatureRadius_eq]
  exact hfin _

theorem closedCollapseHypotheses_UL {K : ℕ} {A : ℝ → ℝ} {w₀ : ℝ}
    (h : closedCollapseHypotheses W g K A w₀) :
    closedCollapseHypotheses M.carrier_UL M.gX K A w₀ := by
  refine ⟨?_, ?_, ?_⟩
  · have hb := M.ψ.preimage_boundary (n := ∞) (by simp)
    rw [h.1] at hb
    exact hb.symm.trans (Set.preimage_empty)
  · rintro (p : M.X) r hr hrad
    have e1 : curvatureRadius g (M.ψ p) = ENNReal.ofReal r := by
      rw [← M.curvatureRadius_eq]
      exact hrad
    exact (M.ballVolume_eq p r).trans_le (h.2.1 (M.ψ p) r hr e1)
  · rintro (p : M.X) w r hw hw' hr hrad hvol k hk (q : M.X) hq
    have e1 : ENNReal.ofReal r < curvatureRadius g (M.ψ p) := by
      rw [← M.curvatureRadius_eq]
      exact hrad
    have e2 : ENNReal.ofReal (w * r ^ 3) ≤ ballVolume g (M.ψ p) r := by
      rw [← M.ballVolume_eq]
      exact hvol
    have e3 : M.ψ q ∈ riemannianBallOf g (M.ψ p) r := (M.ball_eq_preimage p r).le hq
    have e4 := h.2.2 (M.ψ p) w r hw hw' hr e1 e2 k hk (M.ψ q) e3
    rw [← M.curvatureDerivativeNorm_eq] at e4
    exact e4

end ClosedModel

/-- **The auxiliary closed gate output lifts from universe `0` to every universe**: lower the
member to a universe-`0` carrier through its closed model, apply the universe-`0` statement, lift
the Raw presentation along `ψ` (`liftAlong_UL`) or pull back the nonnegative metric along `ψ⁻¹`. -/
theorem closed_aux_univ_UL {K : ℕ} {A : ℝ → ℝ} {w₀ : ℝ}
    (hDI : ∀ (W : CompactCarrier.{0}) [ConnectedSpace W.Carrier]
      (g : SmoothRiemannianMetric W.model W.Carrier),
      (∀ p, curvatureRadius g p ≠ ⊤) → closedCollapseHypotheses W g K A w₀ →
        Nonempty (RawGraphPresentation W) ∨
          (W.model.boundary W.Carrier = ∅ ∧ ∃ g' : SmoothRiemannianMetric W.model W.Carrier,
            Riemannian.SectionalBoundedBelow g' 0))
    (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
    (g : SmoothRiemannianMetric W.model W.Carrier)
    (hfin : ∀ p, curvatureRadius g p ≠ ⊤) (hcol : closedCollapseHypotheses W g K A w₀) :
    Nonempty (RawGraphPresentation W) ∨
      (W.model.boundary W.Carrier = ∅ ∧ ∃ g' : SmoothRiemannianMetric W.model W.Carrier,
        Riemannian.SectionalBoundedBelow g' 0) := by
  obtain ⟨M⟩ := nonempty_closedModel_VAL W g ⟨hcol.1, inferInstance⟩
  have : ConnectedSpace M.carrier_UL.Carrier :=
    M.ψ.toHomeomorph.connectedSpace_iff.mpr inferInstance
  rcases hDI M.carrier_UL M.gX (M.curvatureRadius_ne_top_UL hfin)
      (M.closedCollapseHypotheses_UL hcol) with ⟨⟨G₀⟩⟩ | ⟨-, g₀, hg₀⟩
  · exact Or.inl ⟨G₀.liftAlong_UL M.psi_UL M.psi_UL_preservesOrientation⟩
  · exact Or.inr ⟨hcol.1, Diffeomorph.pullbackMetricCross g₀ M.psi_UL.symm,
      sectionalBoundedBelow_pullbackMetricCross g₀ M.psi_UL.symm hg₀⟩

/-- **The closed endpoint input at every universe** (the admitted
`exists_closed_graph_threshold_of_finite_scales_disj.{u}` without its positivity hypothesis on
`A`; the verbatim form with `hA` is the consumer example): `a01_of_closed_final_A01` is the
universe-`0` theorem; the threshold `w₀` is the same for every `u`. -/
theorem a02_closed_univ_UL (K : ℕ) (hK : staticDerivativeOrder ≤ K) (A : ℝ → ℝ) :
    ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
      ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
        (g : SmoothRiemannianMetric W.model W.Carrier),
        (∀ p, curvatureRadius g p ≠ ⊤) → closedCollapseHypotheses W g K A w₀ →
          Nonempty (RawGraphPresentation W) ∨
            ∃ G : GC.Geometry.GeometricStructure W.model W.Carrier,
              G.model = .spherical ∨ G.model = .sphericalProduct ∨ G.model = .euclidean := by
  obtain ⟨w₀, hw₀, hwu, hDI⟩ := pbr03_threshold_final_FCW K hK (fun w => max (A w) 1)
    (fun _ _ => lt_max_of_lt_right one_pos)
  exact ⟨w₀, hw₀, hwu, fun W _ g hfin hcol => finite_scales_disj_of_raw_or_aux_nonneg
    (closed_aux_univ_UL hDI) W g hfin
    (closedCollapseHypotheses_mono_control_A01 (fun w => le_max_left (A w) 1) hcol)⟩

end DifferentialGeometry.Geometry.Collapse
