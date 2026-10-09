import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCollarAlternativeApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryLocalization
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspCollarBalls

/-!
# Actual restricted boundary buffers

The index is enlarged after every finite scale factor has been fixed. First exit in the
original collar and boundary-distance comparison put every point of a meeting small ball
in the same packet height band. The centre need not belong to a splitting stratum.
-/

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Collapse

universe u

theorem boundary_scale_buffer (d ρ n C : ℝ) (hρ : 0 < ρ)
    (hCn : 4 * C < n) (hratio : n / 2 < d / ρ) :
    C * ρ < d / 2 := by
  have h1 := (lt_div_iff₀ hρ).mp hratio
  nlinarith

variable {W : CompactCarrier.{u}} [connectedW : ConnectedSpace W.Carrier]
  {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {A : ℝ → ℝ} {w₀ ε : ℝ}

private theorem height_gt_six (P : BoundaryExportPacket W g K A w₀ ε)
    (i : Fin P.cusp.count) {q : CuspHalfSpace} (hq : q ∈ cuspDomain)
    (h9 : ENNReal.ofReal 9 < distanceToBoundary W g ((P.cusp.collar i).toFun q)) :
    6 < q.2.val 0 := by
  have hbd := ((P.cusp.collar i).boundary_preimage
    (mem_cuspDomain_halfZero q.1)).mpr halfZero_val_zero
  have hle := distanceToBoundary_le_riemannianEDistOf W g
    (p := (P.cusp.collar i).toFun q) hbd
  have hup := (P.cusp.collar i).riemannianEDistOf_le_flat hq
    (mem_cuspDomain_halfZero q.1)
  rw [riemannianEDistOf_self, ENNReal.toReal_zero, halfZero_val_zero, sub_zero,
    zero_pow two_ne_zero, add_zero, Real.sqrt_sq q.2.2] at hup
  have h9r : 9 < Real.sqrt (1 + w₀) * q.2.val 0 :=
    (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by norm_num)).mp (h9.trans_le (hle.trans hup))
  have hs : Real.sqrt (1 + w₀) < 3 / 2 :=
    (Real.sqrt_lt' (by norm_num)).mpr (by linarith [P.threshold])
  nlinarith [Real.sqrt_nonneg (1 + w₀), q.2.2]

theorem BoundaryExportPacket.small_ball_height_band
    (P : BoundaryExportPacket W g K A w₀ ε)
    (i : Fin P.cusp.count) {z : W.Carrier} {R : ℝ} (hR : R < 1 / 100)
    (hz : ENNReal.ofReal 10 < distanceToBoundary W g z)
    {p : CuspHalfSpace} (hp : p.2.val 0 < 92)
    (hmeet : (P.cusp.collar i).toFun p ∈ riemannianBallOf g z R) :
    ∀ y ∈ riemannianBallOf g z R, ∃ q ∈ cuspDomain,
      (P.cusp.collar i).toFun q = y ∧ 6 < q.2.val 0 ∧ q.2.val 0 < 93 ∧
        5 < P.height i y ∧ P.height i y < 95 := by
  have hR0 : 0 < R := ENNReal.ofReal_pos.mp (zero_le.trans_lt hmeet)
  intro y hy
  have hdist : riemannianEDistOf g ((P.cusp.collar i).toFun p) y <
      ENNReal.ofReal (2 * R) := by
    calc _ ≤ riemannianEDistOf g ((P.cusp.collar i).toFun p) z +
          riemannianEDistOf g z y := riemannianEDistOf_triangle g _ _ _
      _ < ENNReal.ofReal R + ENNReal.ofReal R := by
        rw [riemannianEDistOf_comm g ((P.cusp.collar i).toFun p) z]
        exact ENNReal.add_lt_add hmeet hy
      _ = ENNReal.ofReal (2 * R) := by
        rw [← ENNReal.ofReal_add hR0.le hR0.le]
        congr 1
        ring
  obtain ⟨q, hq, hqy⟩ := (P.cusp.collar i).riemannianBallOf_subset_image_window_of_le_hundredth
    (by linarith [P.threshold]) (by linarith : p.2.val 0 ≤ 96)
    (by linarith : 2 * R ≤ 1) hdist
  have hq93 : q.2.val 0 < 93 := by
    have ha := (abs_lt.mp hq.1).2
    linarith
  have hqd : q ∈ cuspDomain := by
    change q.2.val 0 < 100
    linarith
  have h9 := nine_lt_distanceToBoundary_of_mem_ball W g (by linarith : R ≤ 1) hz hy
  have hq6 : 6 < q.2.val 0 := height_gt_six P i hqd (hqy ▸ h9)
  have hheight := abs_lt.mp (P.height_contract i q hqd (by linarith) (by linarith)).1
  refine ⟨q, hqd, hqy, hq6, hq93, ?_, ?_⟩ <;>
    rw [← hqy] <;> linarith [P.tolerance_le_one]

end DifferentialGeometry.Geometry.Collapse
