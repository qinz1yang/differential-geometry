import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BoundedCurvatureAtDistanceSliceEvent
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CapWindowPointTimeSlack
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SliceBallBoundTransfer

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem RetainedCoreHistory.exists_scalar_bound_at_distance_of_not_capWindowPoint_event_of_sliver
    {ε : ℝ} (hεle : ε ≤ coneAccuracy) (κ C1 C2 : ℝ) (hκ : 0 < κ) (Ctime Cgrad : ℝ≥0)
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi) (A : ℝ) (hA : 0 < A)
    (Cq θ : ℝ) (hθ : 0 < θ) :
    ∃ Q Λ Dcap Rrad ζ₀ : ℝ, 1 ≤ Q ∧ 1 ≤ Λ ∧ StandardCap.transitionEnd < Dcap ∧ Dcap ≤ Rrad ∧
    0 < ζ₀ ∧
    ∀ (H : RetainedCoreHistory.{u})
      (p₀ : CutoffParameters) (δbound ρbound : ℝ) {p : CutoffParameters}
      (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p),
      H.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records →
      Rrad ≤ p₀.modelRadius → 2 ≤ p₀.modelOrder → p₀.modelAccuracy ≤ ζ₀ →
      ∀ (j : Fin H.eventCount) {t₀ t : ℝ} (_ : H.time j.castSucc < t₀) (_ : t₀ ≤ t)
        (_ : t < H.time j.succ) (y : (H.stage j.castSucc).Carrier) (q ρ : ℝ),
      0 < q → q ≤ Cq * (H.toHistory.event j).incoming.flow.scalar t y →
      Λ ≤ (H.toHistory.event j).incoming.flow.scalar t y →
      Λ ≤ (H.toHistory.event j).incoming.flow.scalar t y * t₀ →
      (∀ x, |(H.toHistory.event j).incoming.flow.scalar t x -
          (H.toHistory.event j).incoming.flow.scalar t₀ x| ≤
        (H.toHistory.event j).incoming.flow.scalar t y / 4) →
      (∀ x (v : TangentSpace ThreeModel x),
        ((H.toHistory.event j).incoming.flow.base.metric t₀).inner x v v ≤
          Real.exp 1 * ((H.toHistory.event j).incoming.flow.base.metric t).inner x v v) →
      (H.toHistory.event j).incoming.SpatiallyCanonicalBefore ε C1 C2 q t₀ →
      H.EventSlabsDerivative Ctime q j.castSucc →
      (H.toHistory.event j).incoming.DerivativeBoundBefore Ctime q t₀ →
      (H.toHistory.event j).incoming.GradientBoundBefore Cgrad q t₀ →
      H.EventSlabsPinched phi → H.NoncollapsedBefore κ ρ t₀ →
      Λ ≤ ρ * Real.sqrt ((H.toHistory.event j).incoming.flow.scalar t y) →
      ¬ H.CapWindowPoint records j.castSucc y t₀ Dcap θ →
      ∀ z ∈ riemannianBallOf ((H.toHistory.event j).incoming.flow.base.metric t) y
        (A / Real.sqrt ((H.toHistory.event j).incoming.flow.scalar t y)),
        (H.toHistory.event j).incoming.flow.scalar t z ≤
          Q * (H.toHistory.event j).incoming.flow.scalar t y := by
  obtain ⟨Q, Λ, Dcap, Rrad, ζ₀, hQ, hΛ, hD, hDR, hζ, hmain⟩ :=
    RetainedCoreHistory.exists_scalar_bound_at_distance_of_not_capWindowPoint_event.{u} hεle κ
      C1 C2 hκ Ctime Cgrad hphi (2 * Real.sqrt (Real.exp 1) * A) (by positivity) (2 * Cq)
      (θ / 2) (half_pos hθ)
  refine ⟨2 * Q + 1, 4 * Λ, Dcap, Rrad, ζ₀, by linarith, by linarith, hD, hDR, hζ, ?_⟩
  intro H p₀ δb ρb p records hrec hR hord hacc j t₀ t ht₀ ht₀t hts y q ρ hq hqy hΛy hΛt
    hclose hmet hW hslabs hder hgrad hpinch hnc hρ hnot z hz
  obtain ⟨S, hS, hSb⟩ := H.exists_forall_neck_scale_le records
  obtain ⟨σ, haσ, hσt₀, hσS, hqσ, hΛσ, hΛσt, hρσ, htransfer⟩ :=
    (H.toHistory.event j).incoming.exists_earlier_slice_scalar_ball_transfer y ht₀ ht₀t hts hq
      hqy (by linarith) hΛy hΛt hclose hmet hρ hA hθ hS
  refine htransfer Q (by linarith) (hmain H p₀ δb ρb records hrec hR hord hacc j haσ
    ((hσt₀.trans_le ht₀t).trans hts) y q ρ hq hqσ (by linarith) (by linarith)
    (fun x hx => hW x σ ⟨haσ, hσt₀⟩ hx) hslabs
    ((H.toHistory.event j).incoming.derivativeBoundBefore_mono hσt₀.le hder)
    ((H.toHistory.event j).incoming.gradientBoundBefore_mono hσt₀.le hgrad) hpinch
    (H.noncollapsedBefore_mono hσt₀.le hnc) (by linarith)
    (fun hcw => hnot (hcw.of_le_time hσt₀.le hSb (by linarith)))) z hz

theorem RetainedCoreHistory.exists_scalar_bound_at_distance_of_not_capWindowPoint_terminal_of_sliver
    {ε : ℝ} (hεle : ε ≤ coneAccuracy) (κ C1 C2 : ℝ) (hκ : 0 < κ) (Ctime Cgrad : ℝ≥0)
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi) (A : ℝ) (hA : 0 < A)
    (Cq θ : ℝ) (hθ : 0 < θ) :
    ∃ Q Λ Dcap Rrad ζ₀ : ℝ, 1 ≤ Q ∧ 1 ≤ Λ ∧ StandardCap.transitionEnd < Dcap ∧ Dcap ≤ Rrad ∧
    0 < ζ₀ ∧
    ∀ (H : RetainedCoreHistory.{u})
      (hend : H.time (Fin.last H.eventCount) = H.horizon) {s : ℝ}
      (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
      (hG : G.flow.base.metric (H.time (Fin.last H.eventCount)) =
        H.initialMetric (Fin.last H.eventCount))
      (p₀ : CutoffParameters) (δbound ρbound : ℝ) {p : CutoffParameters}
      (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p),
      H.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records →
      Rrad ≤ p₀.modelRadius → 2 ≤ p₀.modelOrder → p₀.modelAccuracy ≤ ζ₀ →
      ∀ {t₀ t : ℝ} (_ : H.time (Fin.last H.eventCount) < t₀) (_ : t₀ ≤ t) (_ : t < s)
        (y : (H.stage (Fin.last H.eventCount)).Carrier) (q ρ : ℝ),
      0 < q → q ≤ Cq * G.flow.scalar t y → Λ ≤ G.flow.scalar t y →
      Λ ≤ G.flow.scalar t y * t₀ →
      (∀ x, |G.flow.scalar t x - G.flow.scalar t₀ x| ≤ G.flow.scalar t y / 4) →
      (∀ x (v : TangentSpace ThreeModel x),
        (G.flow.base.metric t₀).inner x v v ≤ Real.exp 1 * (G.flow.base.metric t).inner x v v) →
      G.SpatiallyCanonicalBefore ε C1 C2 q t₀ →
      H.EventSlabsDerivative Ctime q (Fin.last H.eventCount) →
      G.DerivativeBoundBefore Ctime q t₀ → G.GradientBoundBefore Cgrad q t₀ →
      H.EventSlabsPinched phi →
      Perelman.PhiAlmostNonnegative G.flow (Ico (H.time (Fin.last H.eventCount)) s) phi →
      H.TerminalNoncollapsedBefore hend G hG κ ρ t₀ →
      Λ ≤ ρ * Real.sqrt (G.flow.scalar t y) →
      ¬ H.CapWindowPoint records (Fin.last H.eventCount) y t₀ Dcap θ →
      ∀ z ∈ riemannianBallOf (G.flow.base.metric t) y (A / Real.sqrt (G.flow.scalar t y)),
        G.flow.scalar t z ≤ Q * G.flow.scalar t y := by
  obtain ⟨Q, Λ, Dcap, Rrad, ζ₀, hQ, hΛ, hD, hDR, hζ, hmain⟩ :=
    RetainedCoreHistory.exists_scalar_bound_at_distance_of_not_capWindowPoint_terminal.{u} hεle
      κ C1 C2 hκ Ctime Cgrad hphi (2 * Real.sqrt (Real.exp 1) * A) (by positivity) (2 * Cq)
      (θ / 2) (half_pos hθ)
  refine ⟨2 * Q + 1, 4 * Λ, Dcap, Rrad, ζ₀, by linarith, by linarith, hD, hDR, hζ, ?_⟩
  intro H hend s G hG p₀ δb ρb p records hrec hR hord hacc t₀ t ht₀ ht₀t hts y q ρ hq hqy
    hΛy hΛt hclose hmet hW hslabs hder hgrad hpinch hpinchG hnc hρ hnot z hz
  obtain ⟨S, hS, hSb⟩ := H.exists_forall_neck_scale_le records
  obtain ⟨σ, haσ, hσt₀, hσS, hqσ, hΛσ, hΛσt, hρσ, htransfer⟩ :=
    G.exists_earlier_slice_scalar_ball_transfer y ht₀ ht₀t hts hq hqy (by linarith) hΛy hΛt
      hclose hmet hρ hA hθ hS
  refine htransfer Q (by linarith) (hmain H hend G hG p₀ δb ρb records hrec hR hord hacc haσ
    ((hσt₀.trans_le ht₀t).trans hts) y q ρ hq hqσ (by linarith) (by linarith)
    (fun x hx => hW x σ ⟨haσ, hσt₀⟩ hx) hslabs (G.derivativeBoundBefore_mono hσt₀.le hder)
    (G.gradientBoundBefore_mono hσt₀.le hgrad) hpinch hpinchG
    (fun T hT hTs hTle => hnc T hT hTs (hTle.trans hσt₀.le)) (by linarith)
    (fun hcw => hnot (hcw.of_le_time hσt₀.le hSb (by linarith)))) z hz

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
