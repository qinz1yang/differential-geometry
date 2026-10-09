import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BoundedCurvatureAtDistanceSliceTerminal
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCoreHistoryPrefixTransport

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem RetainedCoreHistory.exists_scalar_bound_at_distance_of_not_capWindowPoint_event
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
      ∀ (j : Fin H.eventCount) {t : ℝ} (_ : H.time j.castSucc < t) (_ : t < H.time j.succ)
        (y : (H.stage j.castSucc).Carrier) (q ρ : ℝ),
      0 < q → q ≤ Cq * (H.toHistory.event j).incoming.flow.scalar t y →
      Λ ≤ (H.toHistory.event j).incoming.flow.scalar t y →
      Λ ≤ (H.toHistory.event j).incoming.flow.scalar t y * t →
      (∀ x, q < (H.toHistory.event j).incoming.flow.scalar t x →
        ∃ W : SpatialCanonicalWitness ((H.toHistory.event j).incoming.flow.base.metric t)
          ε C1 C2 x, W.capTubeHasNeckChart ε) →
      H.EventSlabsDerivative Ctime q j.castSucc →
      (H.toHistory.event j).incoming.DerivativeBoundBefore Ctime q t →
      (H.toHistory.event j).incoming.GradientBoundBefore Cgrad q t →
      H.EventSlabsPinched phi → H.NoncollapsedBefore κ ρ t →
      Λ ≤ ρ * Real.sqrt ((H.toHistory.event j).incoming.flow.scalar t y) →
      ¬ H.CapWindowPoint records j.castSucc y t Dcap θ →
      ∀ z ∈ riemannianBallOf ((H.toHistory.event j).incoming.flow.base.metric t) y
        (A / Real.sqrt ((H.toHistory.event j).incoming.flow.scalar t y)),
        (H.toHistory.event j).incoming.flow.scalar t z ≤
          Q * (H.toHistory.event j).incoming.flow.scalar t y := by
  obtain ⟨Q, Λ, Dcap, Rrad, ζ₀, hQ, hΛ, hD, hDR, hζ, hmain⟩ :=
    RetainedCoreHistory.exists_scalar_bound_at_distance_of_not_capWindowPoint_terminal.{u} hεle κ
      C1 C2 hκ Ctime Cgrad hphi A hA Cq θ hθ
  refine ⟨Q, Λ, Dcap, Rrad, ζ₀, hQ, hΛ, hD, hDR, hζ, ?_⟩
  intro H p₀ δb ρb p records hrec hR hord hacc j t htj htj' y q ρ hq hqy hΛy hΛt hW hslabs hder
    hgrad hpinch hnc hρ hnot z hz
  exact hmain (H.prefixAt j.castSucc) rfl (H.toHistory.event j).incoming (H.event_initial j) p₀
    δb ρb (H.prefixRecords j.castSucc records) (H.isCanonicalCutoffRecordFamily_prefixAt _ hrec)
    hR hord hacc htj htj' y q ρ hq hqy hΛy hΛt hW (H.eventSlabsDerivative_prefixAt _ hslabs) hder
    hgrad (H.eventSlabsPinched_prefixAt _ hpinch) (hpinch j)
    (H.terminalNoncollapsedBefore_prefixAt j hnc) hρ
    (fun h => hnot (H.capWindowPoint_of_prefixAt j records h)) z hz

theorem RetainedCoreHistory.eventually_scalar_bound_at_distance_of_not_capWindowPoint_event
    {ε : ℝ} (hεle : ε ≤ coneAccuracy) {κ C1 C2 : ℝ} (hκ : 0 < κ) {Ctime Cgrad : ℝ≥0}
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi) {Cq θ₀ : ℝ} (hθ₀ : 0 < θ₀)
    (H : ℕ → RetainedCoreHistory.{u})
    (p₀ : ℕ → CutoffParameters) (δbound ρbound : ℕ → ℝ) {p : ℕ → CutoffParameters}
    (records : ∀ n (i : Fin (H n).eventCount), GeometricCutoffRecord (H n).toHistory i (p n))
    (hrec : ∀ n, (H n).IsCanonicalCutoffRecordFamily (p₀ n) (δbound n) (ρbound n) (records n))
    (hradius : Tendsto (fun n => (p₀ n).modelRadius) atTop atTop)
    (horder : ∀ n, 2 ≤ (p₀ n).modelOrder)
    (haccuracy : ∀ ζ : ℝ, 0 < ζ → ∀ᶠ n in atTop, (p₀ n).modelAccuracy ≤ ζ)
    (j : ∀ n, Fin (H n).eventCount) (t : ℕ → ℝ)
    (ht : ∀ n, (H n).time (j n).castSucc < t n) (hts : ∀ n, t n < (H n).time (j n).succ)
    (y : ∀ n, ((H n).stage (j n).castSucc).Carrier) (q ρ : ℕ → ℝ) (hq : ∀ n, 0 < q n)
    (hqy : ∀ n, q n ≤ Cq * ((H n).toHistory.event (j n)).incoming.flow.scalar (t n) (y n))
    (hR : Tendsto (fun n => ((H n).toHistory.event (j n)).incoming.flow.scalar (t n) (y n))
      atTop atTop)
    (hRt : Tendsto (fun n => ((H n).toHistory.event (j n)).incoming.flow.scalar (t n) (y n) *
      t n) atTop atTop)
    (hW : ∀ n x, q n < ((H n).toHistory.event (j n)).incoming.flow.scalar (t n) x →
      ∃ W : SpatialCanonicalWitness
        (((H n).toHistory.event (j n)).incoming.flow.base.metric (t n)) ε C1 C2 x,
        W.capTubeHasNeckChart ε)
    (hslabs : ∀ n, (H n).EventSlabsDerivative Ctime (q n) (j n).castSucc)
    (hder : ∀ n, ((H n).toHistory.event (j n)).incoming.DerivativeBoundBefore Ctime (q n) (t n))
    (hgrad : ∀ n, ((H n).toHistory.event (j n)).incoming.GradientBoundBefore Cgrad (q n) (t n))
    (hpinch : ∀ n, (H n).EventSlabsPinched phi)
    (hnc : ∀ n, (H n).NoncollapsedBefore κ (ρ n) (t n))
    (hρ : Tendsto (fun n => ρ n *
      Real.sqrt (((H n).toHistory.event (j n)).incoming.flow.scalar (t n) (y n))) atTop atTop)
    (D θ : ℕ → ℝ) (hD : Tendsto D atTop atTop) (hθ : ∀ n, θ₀ ≤ θ n)
    (hnot : ∀ n, ¬ (H n).CapWindowPoint (records n) (j n).castSucc (y n) (t n) (D n) (θ n)) :
    ∀ A : ℝ, 0 < A → ∃ Q : ℝ, 1 ≤ Q ∧ ∀ᶠ n in atTop,
      ∀ z ∈ riemannianBallOf (((H n).toHistory.event (j n)).incoming.flow.base.metric (t n)) (y n)
        (A / Real.sqrt (((H n).toHistory.event (j n)).incoming.flow.scalar (t n) (y n))),
        ((H n).toHistory.event (j n)).incoming.flow.scalar (t n) z ≤
          Q * ((H n).toHistory.event (j n)).incoming.flow.scalar (t n) (y n) := by
  intro A hA
  obtain ⟨Q, Λ, Dcap, Rrad, ζ₀, hQ, _, _, _, hζ₀, hmain⟩ :=
    RetainedCoreHistory.exists_scalar_bound_at_distance_of_not_capWindowPoint_event hεle κ C1
      C2 hκ Ctime Cgrad hphi A hA Cq θ₀ hθ₀
  refine ⟨Q, hQ, ?_⟩
  filter_upwards [hradius.eventually_ge_atTop Rrad, haccuracy ζ₀ hζ₀, hR.eventually_ge_atTop Λ,
    hRt.eventually_ge_atTop Λ, hρ.eventually_ge_atTop Λ, hD.eventually_ge_atTop Dcap]
    with n hn1 hn2 hn3 hn4 hn5 hn6
  exact hmain (H n) (p₀ n) (δbound n) (ρbound n) (records n) (hrec n) hn1 (horder n) hn2
    (j n) (ht n) (hts n) (y n) (q n) (ρ n) (hq n) (hqy n) hn3 hn4 (hW n) (hslabs n) (hder n)
    (hgrad n) (hpinch n) (hnc n) hn5 (fun hcw => hnot n (hcw.mono hn6 (hθ n)))

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
