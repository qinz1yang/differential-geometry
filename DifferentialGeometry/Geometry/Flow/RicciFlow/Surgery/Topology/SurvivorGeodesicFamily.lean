import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Geodesic.FamilyLift
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Geodesic.LocalPullback
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventAction

noncomputable section
open Set Bundle Filter Manifold TopologicalSpace
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent
universe u v
variable {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : MetricCutCapEvent P Q a s)
variable {A : Type v} [NormedAddCommGroup A] [NormedSpace ℝ A]

theorem exists_survivor_geodesic_family_to_time
    (W : Opens E.incoming.terminalRegularOpen)
    (F : PartialDiffeomorph ThreeModel ThreeModel E.incoming.terminalRegularOpen Q.Carrier ∞)
    (hsource : F.source = W)
    {D : RealTimeInterval} (S : SolutionOn (I := ThreeModel) (M := W) D) (hS : IsSolutionOn S)
    (hcross : ∀ z : W, E.RegularCrossing z.val.val (F z.val))
    (T : ℝ) {t₀ t₁ : ℝ}
    {α : A × ℝ → Q.Carrier} {V : Set A} {K : Set ℝ} {a0 : A}
    (hV : IsOpen V) (hK : IsOpen K) (ha0 : a0 ∈ V) (ht₀K : t₀ ∈ K)
    (hα : ContMDiffOn (𝓘(ℝ, A).prod 𝓘(ℝ, ℝ)) ThreeModel ∞ α (V ×ˢ K))
    {η : ℝ → W} {L : Set ℝ} (hL : IsOpen L) (hLconn : IsPreconnected L)
    (ht₀L : t₀ ∈ L) (ht₁L : t₁ ∈ L) (hη : IsLRegularizedGeodesicOn S T η L)
    (hcenter : (fun r => α (a0, r)) =ᶠ[𝓝 t₀] (fun z : W => F z.val) ∘ η) :
    ∃ U : Set A, IsOpen U ∧ a0 ∈ U ∧ U ⊆ V ∧
      ∃ C : Set ℝ, IsOpen C ∧ IsPreconnected C ∧ t₀ ∈ C ∧ t₁ ∈ C ∧
        ∃ β : A × ℝ → W,
          ContMDiffOn (𝓘(ℝ, A).prod 𝓘(ℝ, ℝ)) ThreeModel ∞ β (U ×ˢ C) ∧
          (∀ z ∈ U, F (β (z, t₀)).val = α (z, t₀) ∧
            mfderiv ThreeModel ThreeModel (fun q : W => F q.val) (β (z, t₀))
              (lVelocity (I := ThreeModel) (fun r => β (z, r)) t₀) =
              lVelocity (I := ThreeModel) (fun r => α (z, r)) t₀ ∧
            IsLRegularizedGeodesicOn S T (fun r => β (z, r)) C) ∧
          EqOn (fun r => β (a0, r)) η (C ∩ L) ∧
          (∀ z ∈ U, ∀ r ∈ C,
            E.RegularCrossing (β (z, r)).val.val (F (β (z, r)).val)) ∧
          ContMDiffOn (𝓘(ℝ, A).prod 𝓘(ℝ, ℝ)) ThreeModel ∞
            (fun p : A × ℝ => (β p).val.val) (U ×ˢ C) ∧
          ContMDiffOn (𝓘(ℝ, A).prod 𝓘(ℝ, ℝ)) ThreeModel ∞
            (fun p : A × ℝ => F (β p).val) (U ×ˢ C) := by
  have hg : IsLocalDiffeomorph ThreeModel ThreeModel ∞ (fun q : W => F q.val) := by
    intro q
    have hFq : IsLocalDiffeomorphAt ThreeModel ThreeModel ∞ F q.val :=
      ⟨F, (hsource ▸ q.property), fun _ _ => rfl⟩
    exact (isLocalDiffeomorph_subtype_val W q).comp ThreeModel _ hFq
  obtain ⟨U, hU, haU, hUV, C, hC, hCconn, ht₀C, ht₁C, β, hβ, hphase, hβcenter⟩ :=
    exists_lRegularizedGeodesicFamily_lift_to_time S hS T (fun q : W => F q.val) hg
      hV hK ha0 ht₀K hα hL hLconn ht₀L ht₁L hη hcenter
  refine ⟨U, hU, haU, hUV, C, hC, hCconn, ht₀C, ht₁C, β, hβ, hphase, hβcenter,
    (fun z _ r _ => hcross (β (z, r))), ?_, ?_⟩
  · exact contMDiff_subtype_val.comp_contMDiffOn (contMDiff_subtype_val.comp_contMDiffOn hβ)
  · exact hg.contMDiff.comp_contMDiffOn hβ

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

end

noncomputable section
open Set Bundle Filter Manifold TopologicalSpace
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent
universe u v
variable {P Q : OrientedThreeStage.{u}} {a s b : ℝ} (E : MetricCutCapEvent P Q a s)
variable {A : Type v} [NormedAddCommGroup A] [NormedSpace ℝ A]

theorem exists_survivor_geodesic_family_across_event
    (G : Q.IncomingSlab s b)
    (W : Opens E.incoming.terminalRegularOpen)
    (F : PartialDiffeomorph ThreeModel ThreeModel E.incoming.terminalRegularOpen Q.Carrier ∞)
    (hsource : F.source = W)
    {D : RealTimeInterval} (S : SolutionOn (I := ThreeModel) (M := W) D) (hS : IsSolutionOn S)
    (hg : IsLocalDiffeomorph ThreeModel ThreeModel ∞ (fun z : W => F z.val))
    (hf : IsLocalDiffeomorph ThreeModel ThreeModel ∞ (fun z : W => z.val.val))
    (hcross : ∀ z : W, E.RegularCrossing z.val.val (F z.val))
    (T : ℝ) {c w d t₀ t₁ : ℝ} (ht₀ : t₀ ∈ Ioo c w) (ht₁ : t₁ ∈ Ioo w d)
    (hnewClock : ∀ r ∈ Ioo c w, T - r ^ 2 ∈ (RealTimeInterval.closedOpen s b G.lt).regular)
    (holdClock : ∀ r ∈ Ioo w d, T - r ^ 2 ∈ (RealTimeInterval.closedOpen a s E.incoming.lt).regular)
    (hnewMetric : ∀ r ∈ Ioo c w, S.base.metric (T - r ^ 2) =
      localPullMetric (G.flow.base.metric (T - r ^ 2)) (fun z : W => F z.val) hg)
    (holdMetric : ∀ r ∈ Ioo w d, S.base.metric (T - r ^ 2) =
      localPullMetric (E.incoming.flow.base.metric (T - r ^ 2)) (fun z : W => z.val.val) hf)
    {α : A × ℝ → Q.Carrier} {V : Set A} {K : Set ℝ} {a0 : A}
    (hV : IsOpen V) (hK : IsOpen K) (hKconn : IsPreconnected K) (ha0 : a0 ∈ V) (ht₀K : t₀ ∈ K)
    (hα : ContMDiffOn (𝓘(ℝ, A).prod 𝓘(ℝ, ℝ)) ThreeModel ∞ α (V ×ˢ K))
    (hαgeo : ∀ z ∈ V, IsLRegularizedGeodesicOn G.flow T (fun r => α (z, r)) K)
    {η : ℝ → W} (hη : IsLRegularizedGeodesicOn S T η (Ioo c d))
    (hcenter : EqOn (fun r => α (a0, r)) ((fun z : W => F z.val) ∘ η) (Ioo c w)) :
    ∃ U : Set A, IsOpen U ∧ a0 ∈ U ∧ U ⊆ V ∧
      ∃ C : Set ℝ, IsOpen C ∧ IsPreconnected C ∧ t₀ ∈ C ∧ t₁ ∈ C ∧ w ∈ C ∧
        ∃ β : A × ℝ → W,
          ContMDiffOn (𝓘(ℝ, A).prod 𝓘(ℝ, ℝ)) ThreeModel ∞ β (U ×ˢ C) ∧
          (∀ z ∈ U, IsLRegularizedGeodesicOn S T (fun r => β (z, r)) C) ∧
          EqOn (fun r => β (a0, r)) η (C ∩ Ioo c d) ∧
          EqOn (fun p : A × ℝ => F (β p).val) α (U ×ˢ (C ∩ K ∩ Ioo c w)) ∧
          (∀ z ∈ U, E.RegularCrossing (β (z, w)).val.val (F (β (z, w)).val)) ∧
          (∀ z ∈ U, IsLRegularizedGeodesicOn E.incoming.flow T
            (fun r => (β (z, r)).val.val) (C ∩ Ioo w d)) := by
  have ht₀L : t₀ ∈ Ioo c d := ⟨ht₀.1, ht₀.2.trans (ht₁.1.trans ht₁.2)⟩
  have ht₁L : t₁ ∈ Ioo c d := ⟨ht₀.1.trans (ht₀.2.trans ht₁.1), ht₁.2⟩
  have hcenterGerm : (fun r => α (a0, r)) =ᶠ[𝓝 t₀] (fun z : W => F z.val) ∘ η :=
    hcenter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds ht₀)
  obtain ⟨U, hU, haU, hUV, C, hC, hCconn, ht₀C, ht₁C, β, hβ, hphase, hβcenter, _, _, _⟩ :=
    E.exists_survivor_geodesic_family_to_time W F hsource S hS hcross T
      hV hK ha0 ht₀K hα isOpen_Ioo isPreconnected_Ioo ht₀L ht₁L hη hcenterGerm
  have hwC : w ∈ C := hCconn.ordConnected.out ht₀C ht₁C ⟨ht₀.2.le, ht₁.1.le⟩
  have htime : IsOpen (C ∩ K ∩ Ioo c w) := (hC.inter hK).inter isOpen_Ioo
  have htimeconn : IsPreconnected (C ∩ K ∩ Ioo c w) :=
    ((hCconn.ordConnected.inter hKconn.ordConnected).inter ordConnected_Ioo).isPreconnected
  have ht₀time : t₀ ∈ C ∩ K ∩ Ioo c w := ⟨⟨ht₀C, ht₀K⟩, ht₀⟩
  have heq := lRegularizedGeodesicFamily_eqOn_of_localPullMetric S hS G.flow G.equation
    (fun z : W => F z.val) hg T htime htimeconn ht₀time
    (fun z hz r hr => (hphase z hz).2.2 r hr.1.1)
    (fun z hz r hr => hαgeo z (hUV hz) r hr.1.2)
    (fun r hr => hnewMetric r hr.2) (fun r hr => hnewClock r hr.2)
    (fun z hz => (hphase z hz).1) (fun z hz => (hphase z hz).2.1)
  refine ⟨U, hU, haU, hUV, C, hC, hCconn, ht₀C, ht₁C, hwC, β, hβ,
    (fun z hz => (hphase z hz).2.2), hβcenter, heq, (fun z _ => hcross _), ?_⟩
  intro z hz
  exact (show IsLRegularizedGeodesicOn S T (fun r => β (z, r)) (C ∩ Ioo w d) from
    fun r hr => (hphase z hz).2.2 r hr.1).comp_of_localPullMetric S hS E.incoming.flow
      (fun z : W => z.val.val) hf (hC.inter isOpen_Ioo) (fun r hr => holdMetric r hr.2)
      (fun r hr => holdClock r hr.2)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent
