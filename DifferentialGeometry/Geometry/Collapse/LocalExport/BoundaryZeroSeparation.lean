import DifferentialGeometry.Geometry.Collapse.BoundaryScale.RestrictedBoundaryBuffers
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspHeightOnePoint
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CurvatureBuffers
import DifferentialGeometry.Geometry.Collapse.LocalExport.ZeroModelBallApplications
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.BoundaryRowBindings

/-!
# Selected zero balls avoid the actual cusp collars

The same packet height is used at every point of a selected ball. Curvature pinching bounds
its radius, and first exit gives the whole-ball band needed for BCP02. Selection only requires
the ball to meet rank zero. Its centre is not assumed rank zero, and the sequence index is
chosen after the finite upper factor.
-/

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint GC.MetricGeometry
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Collapse

universe u

variable {W : CompactCarrier.{u}} [connectedW : ConnectedSpace W.Carrier]
  {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {A : ℝ → ℝ} {w₀ ε : ℝ}

theorem exists_boundary_curvature_scale_buffer :
    ∃ δStar > 0, ∀ _P : BoundaryExportPacket W g K A w₀ ε,
      2 ≤ K → 0 ≤ w₀ → w₀ ≤ δStar →
      ∀ {n w' : ℝ}, 3 ≤ n → w₀ * (16 * n ^ 4) ≤ 1 → n⁻¹ ≤ w' →
      ∀ ρ : W.Carrier → ℝ, (∀ p, ρ p ≤ 2 * firstVolumeScale g p w') →
      ∀ p, ENNReal.ofReal (n * ρ p) < curvatureRadius g p := by
  obtain ⟨δStar, hδStar, h4⟩ := bsa04_row
  refine ⟨δStar, hδStar, ?_⟩
  intro P hK hw₀ hδ n w' hn hδn hw' ρ hρ p
  have hn0 : 0 < n := by linarith
  have hstand := (h4 W g K w₀ hK hw₀ hδ P.cusp P.volume P.derivatives hn hδn p).1
  have hanti := firstVolumeScale_anti_of_le g p (inv_pos.mpr hn0) hw'
  have hbound : ρ p ≤ 2 * firstVolumeScale g p n⁻¹ := by
    nlinarith [hρ p]
  exact (ENNReal.ofReal_le_ofReal (by nlinarith)).trans_lt hstand

theorem BoundaryExportPacket.zeroBall_curvature_bounds
    (P : BoundaryExportPacket W g K A w₀ ε) (i : Fin P.cusp.count)
    {z : W.Carrier} {R ρ V n : ℝ} (hρ : 0 < ρ) (hVn : V < n)
    (hR : R ≤ V * ρ) (hscale : ENNReal.ofReal (n * ρ) < curvatureRadius g z)
    {p : CuspHalfSpace} (hp : p ∈ cuspDomain)
    (hmeet : (P.cusp.collar i).toFun p ∈ riemannianBallOf g z R) :
    curvatureRadius g z ≤ ENNReal.ofReal (Real.sqrt 8) ∧
      ρ < 3 / n ∧ R < 3 * V / n := by
  obtain ⟨v, w, hgram⟩ := exists_carrier_gram_pos W g ((P.cusp.collar i).toFun p)
  have hneg := (P.pinching i p hp v w).2
  obtain ⟨hcurv, hρn, hRn⟩ := zeroBall_small_of_negative_plane g hmeet hR hρ hVn
    hscale v w hgram hneg
  have hfin : curvatureRadius g z ≠ ⊤ := ne_top_of_lt hcurv
  have hxR : (P.cusp.collar i).toFun p ∈
      riemannianBallOf g z (curvatureRadius g z).toReal := by
    change riemannianEDistOf g z ((P.cusp.collar i).toFun p) < _
    rw [ENNReal.ofReal_toReal hfin]
    calc _ < ENNReal.ofReal R := hmeet
      _ ≤ ENNReal.ofReal (V * ρ) := ENNReal.ofReal_le_ofReal hR
      _ ≤ ENNReal.ofReal (n * ρ) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hVn.le hρ.le)
      _ < curvatureRadius g z := hscale
  have hlower := sectionalBoundedBelowAt_of_curvatureRadius_ne_top g hfin _ hxR v w
  have hκ : 1 / 8 ≤ (((curvatureRadius g z).toReal) ^ 2)⁻¹ := by
    nlinarith
  have hRp : 0 < (curvatureRadius g z).toReal :=
    ENNReal.toReal_pos (curvatureRadius_pos g z).ne' hfin
  have hmul := mul_le_mul_of_nonneg_right hκ (sq_nonneg (curvatureRadius g z).toReal)
  rw [inv_mul_cancel₀ (pow_ne_zero 2 hRp.ne')] at hmul
  have hsqrt : (curvatureRadius g z).toReal ≤ Real.sqrt 8 :=
    Real.le_sqrt_of_sq_le (by nlinarith)
  refine ⟨?_, hρn, hRn⟩
  rw [← ENNReal.ofReal_toReal hfin]
  exact ENNReal.ofReal_le_ofReal hsqrt

theorem BoundaryExportPacket.zeroBall_disjoint_enlargedCollar
    (P : BoundaryExportPacket W g K A w₀ ε)
    (i : Fin P.cusp.count) (ρ : W.Carrier → ℝ) (hρ : ∀ y, 0 < ρ y)
    (βs : ℕ → ℝ) {γ L : ℝ} (hβ : 0 < βs 1) (hβγ : βs 1 < γ)
    (hγ1 : γ < 1) (hL : 0 ≤ L) (hδβ : w₀ ≤ βs 1 ^ 2 / 1000)
    (hεβ : ε ≤ βs 1 ^ 2 / 1000)
    (hsmall : ∀ q ∈ cuspDomain, q.2.val 0 ≤ 98 →
      ρ ((P.cusp.collar i).toFun q) ≤ βs 1 ^ 3 / (2000 * (1 + L)))
    {z : W.Carrier} {R V n : ℝ} (hV : 0 ≤ V) (hn : 300 * V < n)
    (hR : R ≤ V * ρ z)
    (hscale : ENNReal.ofReal (n * ρ z) < curvatureRadius g z)
    (hz : ENNReal.ofReal 10 < distanceToBoundary W g z)
    (hzero : ∃ y ∈ riemannianBallOf g z R,
      @scaledSplittingRank.{u, 0} W.Carrier (inducedMetricSpace g) ρ hρ βs y = 0) :
    Disjoint (riemannianBallOf g z R)
      ((P.cusp.collar i).toFun '' {p : CuspHalfSpace | p.2.val 0 < 92}) := by
  apply Set.disjoint_left.mpr
  intro x hx hxc
  obtain ⟨p, hp, rfl⟩ := hxc
  change p.2.val 0 < 92 at hp
  have hpd : p ∈ cuspDomain := by
    change p.2.val 0 < 100
    linarith
  have hVn : V < n := by linarith
  have hRn := (P.zeroBall_curvature_bounds i (hρ z) hVn hR hscale hpd hx).2.2
  have hn0 : 0 < n := by linarith
  have hRsmall : R < 1 / 100 := by
    have hbound : 3 * V / n < 1 / 100 := by
      rw [div_lt_iff₀ hn0]
      linarith
    exact hRn.trans hbound
  obtain ⟨y, hy, hyzero⟩ := hzero
  obtain ⟨q, hqd, hqy, hq6, hq93, hη5, hη95⟩ :=
    P.small_ball_height_band i hRsmall hz hp hx y hy
  have hrank := P.one_le_scaledSplittingRank i ρ hρ βs hβ hβγ hγ1 hL hδβ hεβ
    hsmall (by linarith : 2 ≤ q.2.val 0) (by linarith : q.2.val 0 ≤ 98)
    (by simpa only [hqy] using hη5.le) (by simpa only [hqy] using hη95.le)
  rw [hqy, hyzero] at hrank
  omega

theorem BoundaryExportPacket.restricted_ball_above_five
    (P : BoundaryExportPacket W g K A w₀ ε) {p : W.Carrier}
    (hp : ENNReal.ofReal 10 < distanceToBoundary W g p) {ρ C n : ℝ}
    (hρ : 0 < ρ) (hCn : 4 * C < n)
    (hratio : n / 2 < (distanceToBoundary W g p).toReal / ρ) :
    ∀ y ∈ riemannianBallOf g p (C * ρ),
      ENNReal.ofReal 5 < distanceToBoundary W g y := by
  have hfinite := ne_of_lt (P.cusp.distanceToBoundary_lt_top p)
  have hd : 10 < (distanceToBoundary W g p).toReal :=
    (ENNReal.ofReal_lt_iff_lt_toReal (by norm_num) hfinite).mp hp
  have hR := boundary_scale_buffer (distanceToBoundary W g p).toReal ρ n C hρ hCn hratio
  intro y hy
  have hR0 : 0 < C * ρ := ENNReal.ofReal_pos.mp (zero_le.trans_lt hy)
  by_contra hnot
  have h5 : distanceToBoundary W g y ≤ ENNReal.ofReal 5 := not_lt.mp hnot
  have hlt : distanceToBoundary W g p < ENNReal.ofReal (5 + C * ρ) := by
    calc _ ≤ distanceToBoundary W g y + riemannianEDistOf g p y :=
          distanceToBoundary_le_add W g p y
      _ < ENNReal.ofReal 5 + ENNReal.ofReal (C * ρ) :=
        ENNReal.add_lt_add_of_le_of_lt (ne_top_of_le_ne_top ENNReal.ofReal_ne_top h5) h5 hy
      _ = ENNReal.ofReal (5 + C * ρ) :=
        (ENNReal.ofReal_add (by norm_num) hR0.le).symm
  have hr := (ENNReal.toReal_lt_toReal hfinite ENNReal.ofReal_ne_top).mpr hlt
  rw [ENNReal.toReal_ofReal (by linarith : 0 ≤ 5 + C * ρ)] at hr
  linarith

theorem BoundaryExportPacket.zeroRegion_disjoint_collar_blocks
    (P : BoundaryExportPacket W g K A w₀ ε)
    {J : Type*} (z : J → W.Carrier) (R : J → ℝ)
    (ρ : W.Carrier → ℝ) (hρ : ∀ y, 0 < ρ y) (βs : ℕ → ℝ)
    {γ L V n : ℝ} (hβ : 0 < βs 1) (hβγ : βs 1 < γ) (hγ1 : γ < 1)
    (hL : 0 ≤ L) (hδβ : w₀ ≤ βs 1 ^ 2 / 1000) (hεβ : ε ≤ βs 1 ^ 2 / 1000)
    (hsmall : ∀ i, ∀ q ∈ cuspDomain, q.2.val 0 ≤ 98 →
      ρ ((P.cusp.collar i).toFun q) ≤ βs 1 ^ 3 / (2000 * (1 + L)))
    (hV : 0 ≤ V) (hn : 300 * V < n)
    (hR : ∀ l, R l ≤ V * ρ (z l))
    (hscale : ∀ l, ENNReal.ofReal (n * ρ (z l)) < curvatureRadius g (z l))
    (hz : ∀ l, ENNReal.ofReal 10 < distanceToBoundary W g (z l))
    (hzero : ∀ l, ∃ y ∈ riemannianBallOf g (z l) (R l),
      @scaledSplittingRank.{u, 0} W.Carrier (inducedMetricSpace g) ρ hρ βs y = 0) :
    Disjoint (⋃ l, riemannianBallOf g (z l) (R l))
      (⋃ i, tsupport (P.toBoundaryCollarPacket.block i)) := by
  apply Set.disjoint_left.mpr
  intro x hx hb
  obtain ⟨l, hl⟩ := mem_iUnion.mp hx
  obtain ⟨i, hi⟩ := mem_iUnion.mp hb
  obtain ⟨q, hq, hqx⟩ := P.toBoundaryCollarPacket.tsupport_block_subset i hi
  have hq92 : q.2.val 0 < 92 := by
    have hh : q.2.val 0 ≤ 90 + ε := hq.2
    linarith [P.tolerance_le_one]
  have hdis := P.zeroBall_disjoint_enlargedCollar i ρ hρ βs hβ hβγ hγ1 hL hδβ hεβ
    (hsmall i) hV hn (hR l) (hscale l) (hz l) (hzero l)
  exact Set.disjoint_left.mp hdis hl ⟨q, hq92, hqx⟩

end DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Analysis.Calculus
namespace DifferentialGeometry.Geometry.Collapse
variable {W : CompactCarrier.{0}} [connectedW : ConnectedSpace W.Carrier]
  {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {A : ℝ → ℝ} {w₀ ε : ℝ}

theorem BoundaryExportPacket.zeroModelFamily_disjoint_collar_blocks
    (P : BoundaryExportPacket W g K A w₀ ε)
    (ρ : W.Carrier → ℝ) (hρ : ∀ y, 0 < ρ y) (βs : ℕ → ℝ)
    {ι : Type} (N C : ι → Type) [metricN : ∀ b, MetricSpace (N b)]
    [chartsN : ∀ b, ChartedSpace W.kind.Space (N b)]
    [metricC : ∀ b, MetricSpace (C b)] (o : ∀ b, C b)
    {δ εr e T V n γ L : ℝ} (he : e < 1 / 10)
    (hβ : 0 < βs 1) (hβγ : βs 1 < γ) (hγ1 : γ < 1)
    (hL : 0 ≤ L) (hδβ : w₀ ≤ βs 1 ^ 2 / 1000) (hεβ : ε ≤ βs 1 ^ 2 / 1000)
    (hsmall : ∀ i, ∀ q ∈ cuspDomain, q.2.val 0 ≤ 98 →
      ρ ((P.cusp.collar i).toFun q) ≤ βs 1 ^ 3 / (2000 * (1 + L)))
    (hV : 0 ≤ V) (hn : 300 * V < n) :
    letI _metricW := inducedMetricSpace g
    ∀ F : ZeroModelFamily W.model W.Carrier g ρ hρ βs N C o δ εr e T V,
    (∀ z ∈ F.centres, ENNReal.ofReal (n * ρ z) < curvatureRadius g z) →
    (∀ z ∈ F.centres, ENNReal.ofReal 10 < distanceToBoundary W g z) →
    Disjoint (⋃ z, ⋃ hz : z ∈ F.centres, Metric.ball z (F.zero z hz).radius)
      (⋃ i, tsupport (P.toBoundaryCollarPacket.block i)) ∧
    ∀ z (hz : z ∈ F.centres),
      Disjoint (tsupport (fun x => annularCutoff cutoffProfile ((F.zero z hz).radial x)))
        (⋃ i, tsupport (P.toBoundaryCollarPacket.block i)) := by
  let _metricW := inducedMetricSpace g
  intro F hscale hz
  have hmeets (l : F.centres) : ∃ y ∈ riemannianBallOf g l.val (F.zero l.val l.property).radius,
      @scaledSplittingRank.{0, 0} W.Carrier (inducedMetricSpace g) ρ hρ βs y = 0 := by
    obtain ⟨y, hy, hzero⟩ := F.meets_stratum l.val l.property
    refine ⟨y, ?_, hzero⟩
    rwa [inducedMetricSpace_ball] at hy
  have hreg := P.zeroRegion_disjoint_collar_blocks
    (fun l : F.centres => l.val) (fun l : F.centres => (F.zero l.val l.property).radius)
    ρ hρ βs hβ hβγ hγ1 hL hδβ hεβ hsmall hV hn
    (fun l => (F.radius_mem l.val l.property).2)
    (fun l => hscale l.val l.property) (fun l => hz l.val l.property) hmeets
  have hballs : Disjoint (⋃ z, ⋃ hz : z ∈ F.centres, Metric.ball z (F.zero z hz).radius)
      (⋃ i, tsupport (P.toBoundaryCollarPacket.block i)) := by
    apply Set.disjoint_left.mpr
    intro x hx hsupp
    obtain ⟨z, hx⟩ := mem_iUnion.mp hx
    obtain ⟨hz, hx⟩ := mem_iUnion.mp hx
    exact Set.disjoint_left.mp hreg (mem_iUnion.mpr ⟨⟨z, hz⟩, by
      rwa [inducedMetricSpace_ball] at hx⟩) hsupp
  refine ⟨hballs, fun z hz => ?_⟩
  have hsub := (F.zero z hz).tsupport_cutoff_subset_ball
  rw [F.zero_center z hz] at hsub
  have hsub' : tsupport (fun x => annularCutoff cutoffProfile ((F.zero z hz).radial x)) ⊆
      Metric.ball z (F.zero z hz).radius :=
    hsub.trans (Metric.ball_subset_ball (by nlinarith [(F.zero z hz).radius_pos]))
  exact hballs.mono_left (hsub'.trans fun x hx =>
    mem_iUnion.mpr ⟨z, mem_iUnion.mpr ⟨hz, hx⟩⟩)

end DifferentialGeometry.Geometry.Collapse
