import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RecentPreparedCapProductExclusion
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalTraceConstruction

set_option autoImplicit false
noncomputable section
open Set Function Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

theorem exists_uniform_backward_trace_of_prepared_caps_and_product_chart
    (D r eps a₀ : ℝ) (C : ℝ≥0) (ha₀ : 0 < a₀)
    (heps : 0 < eps) (hepssmall : eps ≤ 1 / 1000)
    (hr : StandardCap.transitionEnd + eps⁻¹ + 1 < r)
    (hfit : 64 * (r + eps⁻¹) < D) :
    ∃ θ Qmin R εprod ε₀ δ₀ : ℝ,
      0 < θ ∧ 0 < Qmin ∧ 0 < R ∧ 0 < εprod ∧ εprod ≤ 1 / 4 ∧
      0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ 0 < δ₀ ∧
      ∀ (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
        (s : ℝ) (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric),
      G.flow.base.metric (H.time last) = H.initialMetric last →
      ∀ (parameters : CutoffParameters) (records : ∀ j : Fin H.eventCount, GeometricCutoffRecord H j parameters),
      (∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x) →
      (∀ x, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) x) →
      (∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last → ∀ b, (records j).delta b ≤ δ₀) →
      ∀ (q₀ Q : ℝ) (hq₀ : 0 < q₀) (hthreshold : 2 * q₀ < Q), Qmin ≤ Q →
      (∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
        ∀ x : (H.stage j.castSucc).Carrier, ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
          q₀ < (H.event j).incoming.flow.scalar t x →
          |derivWithin (fun v => (H.event j).incoming.flow.scalar v x) (Iic t) t| ≤
            C * (H.event j).incoming.flow.scalar t x ^ 2) →
      (∀ x : (H.stage last).Carrier, ∀ t ∈ Ioo (H.time last) s,
        q₀ < G.flow.scalar t x →
        |derivWithin (fun v => G.flow.scalar v x) (Iic t) t| ≤ C * G.flow.scalar t x ^ 2) →
      (∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last → s - θ / Q < H.time j.succ) →
      ∀ {fixed : StaticCapScaffold} {Dbig ζ : ℝ} {m : ℕ} (hmargin : D + 1 ≤ Dbig),
      ⌈eps⁻¹⌉₊ + 2 ≤ m → ζ ≤ ε₀ →
      ∀ (S : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
        ∀ b : (H.event j).RetainedBoundaryIndex, (H.event j).PresentedStaticCap fixed Dbig m ζ b),
      (∀ j : Fin H.eventCount, ∀ hf : first ≤ j.castSucc, ∀ hl : j.succ ≤ last,
        ∀ (b : (H.event j).RetainedBoundaryIndex) (z : ThreeBall),
          (S j hf hl b).neck.scale / 2 ≤
            metricScalarAt (S j hf hl b).witness.metric ((S j hf hl b).witness.cap z)) →
      ∀ (center : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
          (H.event j).RetainedBoundaryIndex → (H.event j).incoming.terminalRegularOpen)
        (precision : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
          (H.event j).RetainedBoundaryIndex → ℝ)
        (order : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
          (H.event j).RetainedBoundaryIndex → ℕ)
        (d : ∀ j : Fin H.eventCount, ∀ hf : first ≤ j.castSucc, ∀ hl : j.succ ≤ last,
          ∀ b : (H.event j).RetainedBoundaryIndex,
          normalizedDatum (H.event j).terminal.metric (center j hf hl b)
            (precision j hf hl b) (order j hf hl b))
        (w : ∀ j : Fin H.eventCount, ∀ hf : first ≤ j.castSucc, ∀ hl : j.succ ≤ last,
          ∀ b : (H.event j).RetainedBoundaryIndex,
          StandardCap.CanonicalStaticInsertionWitness (d j hf hl b)
            fixed.collarLength fixed.collar_pos Dbig m ζ)
        (Jbig : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
          (H.event j).RetainedBoundaryIndex → standardCapWindow Dbig → (H.stage j.succ).Carrier),
      (∀ j hf hl b, IsSmoothEmbedding ThreeModel ThreeModel ∞ (Jbig j hf hl b)) →
      (∀ j hf hl b x (v z : TangentSpace ThreeModel x),
        (w j hf hl b).windowMetric.inner x v z =
          (S j hf hl b).neck.scale * (H.initialMetric j.succ).inner (Jbig j hf hl b x)
            (mfderiv ThreeModel ThreeModel (Jbig j hf hl b) x v)
            (mfderiv ThreeModel ThreeModel (Jbig j hf hl b) x z)) →
      (∀ j hf hl b z, ∃ u : standardCapWindow D,
        ‖u.val‖ ≤ StandardCap.transitionEnd ∧
        Jbig j hf hl b ⟨u.val, by
          have hu := u.property
          change ‖u.val‖ < D + 1 at hu
          change ‖u.val‖ < Dbig + 1
          linarith⟩ = (S j hf hl b).inclusion ((S j hf hl b).witness.cap z)) →
      ∀ (x : G.terminalRegularOpen), Q = metricScalarAt L.metric x →
      ∀ {F H' : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
        [TopologicalSpace H'] {Jp : ModelWithCorners ℝ F H'} [Jp.Boundaryless]
        {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold Jp ∞ N]
        [T2Space N] [ConnectedSpace N] [SigmaCompactSpace N]
        (hprod : SmoothRiemannianMetric Jp N), Module.finrank ℝ F = 2 →
      ∀ (O : TopologicalSpace.Opens (N × ℝ)) (V : TopologicalSpace.Opens G.terminalRegularOpen)
        (Φ : O ≃ₘ⟮Jp.prod 𝓘(ℝ), ThreeModel⟯ V),
      riemannianBallOf (scaleMetric Q (by linarith) L.metric) x R ⊆ V →
      (∀ y : V, ∀ n : ℕ, n ≤ 2 →
        metricDerivNorm n (Diffeomorph.pullbackMetricCross
          ((scaleMetric Q (by linarith) L.metric).restrictOpen V) Φ)
          ((hprod.prod (euclideanMetric (E := ℝ))).restrictOpen O)
          ((hprod.prod (euclideanMetric (E := ℝ))).restrictOpen O) (Φ.symm y) ≤ εprod) →
      Nonempty (BackwardPointTrace H first last hle x.val) := by
  obtain ⟨θ₀,Qmin,R,εprod,ε₀,δ₀,hθ₀,hQmin,hR,hεprod,hεquarter,hε₀,hεhalf,hδ₀,hexclude⟩ :=
    exists_uniform_recent_prepared_cap_product_exclusion.{u, 0, 0, u}
      D r eps a₀ C ha₀ heps hepssmall hr hfit
  let θ := min θ₀ (min (1/4) (6 * (C : ℝ) + 1)⁻¹)
  have hθ : 0 < θ := lt_min hθ₀ (lt_min (by norm_num) (by positivity))
  have hθsmall : θ ≤ 1/4 := (min_le_right _ _).trans (min_le_left _ _)
  have hbudget : 6 * (C : ℝ) * θ ≤ 1 := by
    have hh : θ ≤ (6 * (C : ℝ) + 1)⁻¹ := (min_le_right _ _).trans (min_le_right _ _)
    have hb := (le_div_iff₀ (by positivity : 0 < 6 * (C : ℝ) + 1)).mp
      (show θ ≤ 1 / (6 * (C : ℝ) + 1) by simpa only [one_div] using hh)
    nlinarith [hθ.le]
  refine ⟨θ,Qmin,R,εprod,ε₀,δ₀,hθ,hQmin,hR,hεprod,hεquarter,hε₀,hεhalf,hδ₀,?_⟩
  intro H first last hle s G L hinit parameters records hfixed hlower hδ
    q₀ Q hq₀ hthreshold hQlower hderiv hfinal hcrossTime fixed Dbig ζ m hmargin
    hm hζ S hcap center precision order d w Jbig hJbig hzero hmark x hQeq
    F H' _ _ _ _ Jp _ N _ _ _ _ _ _ hprod hdim O V Φ hcapture hproduct
  have hQ : 0 < Q := by linarith
  rcases H.exists_backwardPointTrace_or_recent_presented_cap_of_incoming_slab
      first last hle G L hinit x hq₀ (by linarith) hθsmall hbudget hcrossTime
      (by rw [← hQeq]; linarith) (fun j hf hl => hderiv j hf.le hl) (hfinal x.val)
      (fun j _ _ => (records j).old_eq_retained) S hcap with htrace | ⟨j,hf,hl,A,b,z,hpres,hbirth,hscalar,hqcap,hagepos,hage,_⟩
  · exact htrace
  · obtain ⟨u,hu,hmarku⟩ := hmark j hf hl b z
    have hageQ : Q * (s - H.time j.succ) ≤ θ₀ := by
      have hh := hcrossTime j hf hl
      have ht : s - H.time j.succ < θ / Q := by linarith
      have hm := (lt_div_iff₀ hQ).mp ht
      exact (by nlinarith : Q * (s - H.time j.succ) ≤ θ).trans (min_le_left _ _)
    have hrmark : ‖u.val‖ < r := hu.trans_lt (by linarith [inv_pos.mpr heps])
    let _ : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp [ThreeSpace]⟩
    exact False.elim (hexclude (w j hf hl b) hmargin hm hζ H j.succ last hl s G L hinit
      (Jbig j hf hl b) (hJbig j hf hl b) (S j hf hl b).neck.scale q₀
      (S j hf hl b).neck.scale_pos hq₀ (hzero j hf hl b) parameters records hfixed hlower
      (fun k hk hkl => hδ k ((hf.trans j.castSucc_lt_succ.le).trans hk) hkl)
      (fun k hk hkl => hderiv k ((hf.trans j.castSucc_lt_succ.le).trans hk) hkl)
      hfinal u x A hrmark (hbirth.trans hmarku.symm) Q hQ hQeq hthreshold hQlower
      hqcap.le hageQ hprod hdim O V Φ hcapture hproduct)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
