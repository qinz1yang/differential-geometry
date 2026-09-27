import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Geodesic.FamilyLift
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Geodesic.FamilyContinuation
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

theorem exists_survivor_geodesic_family_across_event_of_germ
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
    (hcenter : (fun r => α (a0, r)) =ᶠ[𝓝 t₀] (fun z : W => F z.val) ∘ η) :
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
  obtain ⟨U, hU, haU, hUV, C, hC, hCconn, ht₀C, ht₁C, β, hβ, hphase, hβcenter, _, _, _⟩ :=
    E.exists_survivor_geodesic_family_to_time W F hsource S hS hcross T
      hV hK ha0 ht₀K hα isOpen_Ioo isPreconnected_Ioo ht₀L ht₁L hη hcenter
  have hwC : w ∈ C := hCconn.ordConnected.out ht₀C ht₁C ⟨ht₀.2.le, ht₁.1.le⟩
  have htime : IsOpen (C ∩ K ∩ Ioo c w) := (hC.inter hK).inter isOpen_Ioo
  have htimeconn : IsPreconnected (C ∩ K ∩ Ioo c w) :=
    ((hCconn.ordConnected.inter hKconn.ordConnected).inter ordConnected_Ioo).isPreconnected
  have ht₀time : t₀ ∈ C ∩ K ∩ Ioo c w := ⟨⟨ht₀C, ht₀K⟩, ht₀⟩
  have heq := lRegularizedGeodesicFamily_eqOn_of_localPullMetric S G.flow G.equation
    (fun z : W => F z.val) hg T htime htimeconn ht₀time
    (fun z hz r hr => (hphase z hz).2.2 r hr.1.1)
    (fun z hz r hr => hαgeo z (hUV hz) r hr.1.2)
    (fun r hr => hnewMetric r hr.2) (fun r hr => hnewClock r hr.2)
    (fun z hz => (hphase z hz).1) (fun z hz => (hphase z hz).2.1)
  refine ⟨U, hU, haU, hUV, C, hC, hCconn, ht₀C, ht₁C, hwC, β, hβ,
    (fun z hz => (hphase z hz).2.2), hβcenter, heq, (fun z _ => hcross _), ?_⟩
  intro z hz
  exact (show IsLRegularizedGeodesicOn S T (fun r => β (z, r)) (C ∩ Ioo w d) from
    fun r hr => (hphase z hz).2.2 r hr.1).comp_of_localPullMetric
      (S' := E.incoming.flow) hf (fun r hr => holdMetric r hr.2)
      (fun r hr _ => holdClock r hr.2) (fun r hr => by
        filter_upwards [hC.mem_nhds hr.1] with v hv
        exact ((hphase z hz).2.2 v hv).2.1)

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
  exact E.exists_survivor_geodesic_family_across_event_of_germ G W F hsource S hS hg hf
    hcross T ht₀ ht₁ hnewClock holdClock hnewMetric holdMetric hV hK hKconn ha0 ht₀K
    hα hαgeo hη (hcenter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds ht₀))

theorem exists_survivor_geodesic_family_to_older_time_of_germ
    (G : Q.IncomingSlab s b)
    (W : Opens E.incoming.terminalRegularOpen)
    (F : PartialDiffeomorph ThreeModel ThreeModel E.incoming.terminalRegularOpen Q.Carrier ∞)
    (hsource : F.source = W)
    {D : RealTimeInterval} (S : SolutionOn (I := ThreeModel) (M := W) D) (hS : IsSolutionOn S)
    (hg : IsLocalDiffeomorph ThreeModel ThreeModel ∞ (fun z : W => F z.val))
    (hf : IsLocalDiffeomorph ThreeModel ThreeModel ∞ (fun z : W => z.val.val))
    (hcross : ∀ z : W, E.RegularCrossing z.val.val (F z.val))
    (T : ℝ) {c w d t₀ t₁ e z : ℝ}
    (ht₀ : t₀ ∈ Ioo c w) (ht₁ : t₁ ∈ Ioo w d) (hde : d ≤ e) (hz : z ∈ Ioo w e)
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
    (hcenter : (fun r => α (a0, r)) =ᶠ[𝓝 t₀] (fun z : W => F z.val) ∘ η)
    {γ : ℝ → P.Carrier} (hγ : IsLRegularizedGeodesicOn E.incoming.flow T γ (Ioo w e))
    (hηold : EqOn (fun r => (η r).val.val) γ (Icc w d)) :
    ∃ U : Set A, IsOpen U ∧ a0 ∈ U ∧ U ⊆ V ∧
      ∃ J : Set ℝ, IsOpen J ∧ IsPreconnected J ∧ w ∈ J ∧ z ∈ J ∧
        ∃ β : A × ℝ → P.Carrier,
          ContMDiffOn (𝓘(ℝ, A).prod 𝓘(ℝ, ℝ)) ThreeModel ∞ β (U ×ˢ J) ∧
          (∀ p ∈ U, IsLRegularizedGeodesicOn E.incoming.flow T (fun r => β (p, r)) (J ∩ Ioo w e)) ∧
          EqOn (fun r => β (a0, r)) γ (J ∩ Icc w e) ∧
          ∃ U₁ : Set A, IsOpen U₁ ∧ U ⊆ U₁ ∧ U₁ ⊆ V ∧ a0 ∈ U₁ ∧
            ∃ C : Set ℝ, IsOpen C ∧ IsPreconnected C ∧ t₀ ∈ C ∧ t₁ ∈ C ∧ w ∈ C ∧
              ∃ θ : A × ℝ → W,
                ContMDiffOn (𝓘(ℝ, A).prod 𝓘(ℝ, ℝ)) ThreeModel ∞ θ (U₁ ×ˢ C) ∧
                (∀ p ∈ U₁, IsLRegularizedGeodesicOn S T (fun r => θ (p, r)) C) ∧
                EqOn (fun p : A × ℝ => F (θ p).val) α (U₁ ×ˢ (C ∩ K ∩ Ioo c w)) ∧
                EqOn (fun r => θ (a0, r)) η (C ∩ Ioo c d) ∧
                EqOn β (fun p : A × ℝ => (θ p).val.val) (U ×ˢ (C ∩ Ioo c d ∩ Iio e)) ∧
                (∀ p ∈ U, β (p, w) = (θ (p, w)).val.val) ∧
                ∀ p ∈ U, E.RegularCrossing (β (p, w)) (F (θ (p, w)).val) := by
  obtain ⟨U₁, hU₁, haU₁, hU₁V, C, hC, hCconn, ht₀C, ht₁C, hwC,
    θ, hθ, hθgeo, hθcenter, hθnew, hθcross, hθoldgeo⟩ :=
    E.exists_survivor_geodesic_family_across_event_of_germ G W F hsource S hS hg hf hcross T ht₀ ht₁
      hnewClock holdClock hnewMetric holdMetric hV hK hKconn ha0 ht₀K hα hαgeo hη hcenter
  let J₀ := C ∩ Ioo c d
  have hJ₀ : IsOpen J₀ := hC.inter isOpen_Ioo
  have hJ₀conn : IsPreconnected J₀ := (hCconn.ordConnected.inter ordConnected_Ioo).isPreconnected
  have hwJ₀ : w ∈ J₀ := ⟨hwC, ht₀.1.trans ht₀.2, ht₁.1.trans ht₁.2⟩
  have ht₁J₀ : t₁ ∈ J₀ := ⟨ht₁C, (ht₀.1.trans ht₀.2).trans ht₁.1, ht₁.2⟩
  let β₀ : A × ℝ → P.Carrier := fun p => (θ p).val.val
  have hβ₀ : ContMDiffOn (𝓘(ℝ, A).prod 𝓘(ℝ, ℝ)) ThreeModel ∞ β₀ (U₁ ×ˢ J₀) :=
    contMDiff_subtype_val.comp_contMDiffOn
      (contMDiff_subtype_val.comp_contMDiffOn (hθ.mono (prod_mono subset_rfl inter_subset_left)))
  have hgeo : ∀ p ∈ U₁, IsLRegularizedGeodesicOn E.incoming.flow T (fun r => β₀ (p, r)) (J₀ ∩ Ioo w e) := by
    intro p hp r hr
    exact hθoldgeo p hp r ⟨hr.1.1, hr.2.1, hr.1.2.2⟩
  have hcenterOld : EqOn (fun r => β₀ (a0, r)) γ (J₀ ∩ Icc w e) := by
    intro r hr
    have hh := congrArg (fun q : W => q.val.val) (hθcenter hr.1)
    exact hh.trans (hηold ⟨hr.2.1, hr.1.2.2.le⟩)
  obtain ⟨U, hU, haU, hUU₁, J, hJ, hJconn, hwJ, hzJ, β, hβ, hβeq, hβgeo, hβcenter⟩ :=
    exists_lRegularizedGeodesicFamily_extension_from_boundary E.incoming.flow E.incoming.equation T
      hU₁ haU₁ hJ₀ hJ₀conn hwJ₀ ht₁J₀ ⟨ht₁.1, ht₁.2.trans_le hde⟩ hz hβ₀ hgeo hγ hcenterOld
  have hwE : w < e := ht₁.1.trans (ht₁.2.trans_le hde)
  refine ⟨U, hU, haU, hUU₁.trans hU₁V, J, hJ, hJconn, hwJ, hzJ, β, hβ, hβgeo, hβcenter,
    U₁, hU₁, hUU₁, hU₁V, haU₁, C, hC, hCconn, ht₀C, ht₁C, hwC, θ, hθ, hθgeo, hθnew, hθcenter, hβeq, ?_, ?_⟩
  · intro p hp
    exact hβeq (show (p, w) ∈ U ×ˢ (J₀ ∩ Iio e) from ⟨hp, hwJ₀, hwE⟩)
  · intro p hp
    rw [hβeq (show (p, w) ∈ U ×ˢ (J₀ ∩ Iio e) from ⟨hp, hwJ₀, hwE⟩)]
    exact hθcross p (hUU₁ hp)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

end
