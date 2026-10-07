import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.StrongWindowSpliceFarC12X
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.StrongWindowSurviveBC12X
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.StrongWindowAssemblyC12X
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.RecordHypFarC12X
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.UniformCapWindowSpatialCanonicalWitness

/-!
# Splice glue: the far-early branch `HwinFar_C12X` (C12X, S16 `hwin`; O-C12X-S16H G4e5)

* `hwinFar_of_splicePost_C12X`: for `0 < ε < 1/11`, `1 < θ`, `θ₀ < 1`, the far-early branch
  `HwinFar_C12X (RecordHypFar_C12X θ) ε θ₀ D₀ CS` holds, given the post-surgery closeness
  statement of S16J (`RetainedCoreHistory.exists_splicePost_C12X`, G3 [FROZEN v2]) as an explicit
  hypothesis.  Constants: `CS` = the uniform cap-window spatial witness constant,
  `D₀ = max D₀(post) transitionEnd`; per history: Deep neck (`RecordHypFar_C12X.deep`) ⇒
  survivor (`exists_spliceSurvivor_C12X`) ⇒ post (`hPost`, band `2 (ε⁻¹ + 1)`) ⇒ point lemma
  (`far_full_of_splice_C12X`) ⇒ full neck clause of the spatial witness.
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

universe u

/-- **Far-early branch, conditional on the post-surgery closeness (S16J G3).** -/
theorem hwinFar_of_splicePost_C12X {ε : ℝ} (hε : 0 < ε) (hε11 : ε < 1 / 11) {θ : ℝ}
    (hθ : 1 < θ) {θ₀ : ℝ} (hθ₀ : θ₀ < 1)
    (hPost : ∀ (r : ℕ) {η : ℝ}, 0 < η → ∀ {L : ℝ}, 0 ≤ L →
      ∃ D₀ : ℝ, 0 < D₀ ∧
      ∀ (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) (Ctime : ℝ≥0) (Dw θw : ℝ),
        0 < Dw → θw < 1 →
      ∃ (Rw : ℝ) (mw : ℕ), Dw + 1 < Rw ∧
      ∀ qcan : ℝ, 0 < qcan →
      ∃ (δmax ρmax εcap : ℝ), 0 < δmax ∧ 0 < ρmax ∧ 0 < εcap ∧
      ∀ (p₀ : CutoffParameters) (δbound ρbound : ℝ),
        p₀.modelAccuracy ≤ εcap → Rw ≤ p₀.modelRadius → mw ≤ p₀.modelOrder →
        δbound ≤ δmax → ρbound ≤ ρmax →
      ∀ H : RetainedCoreHistory.{u}, Nonempty (InitialIdentification P₀ g₀ H.toHistory) →
        p₀.recenterConstant * δbound ≤ 1 / 2 →
      ∀ (p : CutoffParameters) (records : ∀ i, GeometricCutoffRecord H.toHistory i p),
        H.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records →
        (∀ i b, ((records i).static b).witness.HasRadialCoordinates) →
      ∀ (k : Fin (H.eventCount + 1)) (s : ℝ) (Gk : (H.stage k).IncomingSlab (H.time k) s),
        Gk.flow.base.metric (H.time k) = H.initialMetric k →
        H.EventSlabsDerivative Ctime qcan k → Gk.DerivativeBoundBefore Ctime qcan s →
      ∀ (y : (H.stage k).Carrier) (t : ℝ), t ∈ Ioo (H.time k) s →
      ∀ d : H.WindowDatum_C12X records k y t Dw θw, D₀ + 1 ≤ ‖d.x.val‖ →
        t - H.time d.j.succ ≤ θ₀ * d.scale⁻¹ →
      ∀ {θ : ℝ} (D : IncomingBackwardNeckDeep_C12X H.toHistory d.j ((records d.j).neck d.b.1.1)
          ((records d.j).nominalRadius ⟨d.b.1.1⟩) θ)
        (Sv : H.toHistory.SpliceSurvivor_C12X D k d.hl)
        (P : H.toHistory.SurvivorNeckPackage_C12X k Gk Sv.first Sv.hle) (u : Sv.U)
        (ys : neckBuffer ((records d.j).static d.b).delta)
        (hys : 0 < ys.1.2 ∧ ys.1.2 < (((records d.j).static d.b).delta)⁻¹),
        ((records d.j).static d.b).witness.window d.x =
          ((records d.j).static d.b).witness.retained ⟨ys.1, hys.1.le, hys.2⟩ →
        u.1 = ⟨(ys.1.1, (if d.b.1.2 then 1 else -1) * (1 + ys.1.2)),
          (records d.j).recenter_in_buffer d.b ys⟩ →
        |(d.scale)⁻¹ * Gk.flow.scalar t y - (1 - d.scale * (t - H.time d.j.succ))⁻¹| ≤ η ∧
        ∀ τ ∈ Icc 0 (d.scale * (t - H.time d.j.succ)),
        ∀ w : neckBuffer ((records d.j).delta d.b.1.1), |w.1.2 - u.1.1.2| ≤ L →
          ∃ hw : w ∈ Sv.U, ∀ q ≤ r,
            metricDerivNorm q (localPullMetric (scaleMetric d.scale d.scale_pos
                (P.gflow (H.time d.j.succ + τ / d.scale))) Sv.Ψ Sv.Ψ_diffeo)
              (((cylFam_C12X τ).restrictOpen
                (neckBuffer ((records d.j).delta d.b.1.1))).restrictOpen Sv.U)
              (((cylFam_C12X τ).restrictOpen
                (neckBuffer ((records d.j).delta d.b.1.1))).restrictOpen Sv.U)
              ⟨w, hw⟩ < η) :
    ∃ D₀ CS : ℝ, 0 < D₀ ∧ 1 ≤ CS ∧ HwinFar_C12X (RecordHypFar_C12X.{u} θ) ε θ₀ D₀ CS := by
  obtain ⟨η, hη, pp, δ₁, hδ₁, hpt⟩ :=
    RetainedCoreHistory.far_full_of_splice_C12X.{u} hε hε11 hθ hθ₀
  obtain ⟨Cs, hCs, hW⟩ :=
    RetainedCoreHistory.exists_uniform_capWindowPoint_spatialCanonicalWitness.{u} hε hε11
  obtain ⟨D₁, hD₁, hP⟩ := hPost pp hη (L := 2 * (ε⁻¹ + 1)) (by positivity)
  refine ⟨max D₁ StandardCap.transitionEnd, Cs, lt_max_of_lt_left hD₁, hCs, ?_⟩
  intro P₀ g₀ Ctime Cgrad Dw θw hDw hθw
  obtain ⟨Rc, mc, hRc, hW⟩ := hW P₀ g₀ Ctime Cgrad Dw θw hDw hθw
  obtain ⟨Rp, mp, -, hP⟩ := hP P₀ g₀ Ctime Dw θw hDw hθw
  refine ⟨max Rc Rp, max (max mc mp) pp, lt_max_of_lt_left hRc, fun qcan hqcan => ?_⟩
  obtain ⟨δc, ρc, εc, hδc, hρc, hεc, hW⟩ := hW qcan hqcan
  obtain ⟨δp, ρp, εp, hδp, hρp, hεp, hP⟩ := hP qcan hqcan
  refine ⟨min (min δc δp) δ₁, min ρc ρp, min εc εp, lt_min (lt_min hδc hδp) hδ₁,
    lt_min hρc hρp, lt_min hεc hεp, ?_⟩
  intro p₀ δbound ρbound hacc hrad hord hδb hρb H hId hΛδ p records hrec hdeep k s Gk hinit
    hderiv hderG hgrad y t ht hRy d hfar hT
  have hmc : max mc mp ≤ p₀.modelOrder := (le_max_left _ _).trans hord
  obtain ⟨W, hWc⟩ := hW p₀ δbound ρbound (hacc.trans (min_le_left _ _))
    ((le_max_left _ _).trans hrad) ((le_max_left _ _).trans hmc)
    (hδb.trans ((min_le_left _ _).trans (min_le_left _ _))) (hρb.trans (min_le_left _ _))
    H hId hΛδ p records hrec k s Gk hinit hderiv t ht.1 ht.2
    (Gk.derivativeBoundBefore_mono ht.2.le hderG) y
    (RetainedCoreHistory.capWindowPoint_iff_nonempty_windowDatum_C12X.mpr ⟨d⟩) hRy
    (hgrad y t ht hRy)
  refine ⟨W, hWc, fun _ => ?_⟩
  have hfar' : StandardCap.transitionEnd < ‖d.x.val‖ := by
    have := le_max_right D₁ StandardCap.transitionEnd
    linarith
  obtain ⟨D⟩ := RecordHypFar_C12X.deep hdeep d.j d.b.1.1
  obtain ⟨Sv, P, u, ys, hys, hyu, -, hwin, hu⟩ :=
    RetainedCoreHistory.exists_spliceSurvivor_C12X hrec Gk hinit d hfar' D
  obtain ⟨hsc, hpost⟩ := hP p₀ δbound ρbound (hacc.trans (min_le_right _ _))
    ((le_max_right _ _).trans hrad) ((le_max_right _ _).trans hmc)
    (hδb.trans ((min_le_left _ _).trans (min_le_right _ _))) (hρb.trans (min_le_right _ _))
    H hId hΛδ p records hrec (RecordHypFar_C12X.radial hdeep) k s Gk hinit hderiv hderG y t ht
    d (by have := le_max_left D₁ StandardCap.transitionEnd; linarith) hT D Sv P u ys hys hwin hu
  exact hpt hrec (hδb.trans (min_le_right _ _)) ((le_max_right _ _).trans hord) Gk ht d hT D Sv
    P u ys hys hyu hu hsc hpost

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
