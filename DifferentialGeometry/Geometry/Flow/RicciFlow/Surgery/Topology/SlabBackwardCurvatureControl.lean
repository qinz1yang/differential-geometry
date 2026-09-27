import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ClosedWindowScalarPropagation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.RmNormFromEigenvalues
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornGeometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventData

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace OrientedThreeStage.IncomingSlab

theorem scalar_le_on_backward_cylinder_of_canonicalWitness
    {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s)
    {eps C1 C2 Q t' : ℝ} {x' : P.Carrier} (hC2 : 0 ≤ C2) (hQ : 0 < Q)
    (hx' : G.flow.scalar t' x' ≤ Q) (ht' : t' < s)
    (ha : a < t' - 2 * localPropagationRadius C2 / Q)
    (hcan : ∀ (y : P.Carrier) (t : ℝ), a < t → t ≤ t' → 2 * Q ≤ G.flow.scalar t y →
      Nonempty (CanonicalWitness G.flow eps C1 C2 y t))
    {y : P.Carrier} {t : ℝ}
    (hy : y ∈ riemannianClosedBallOf (I := I3) (G.flow.base.metric t') x'
      (localPropagationRadius C2 / Real.sqrt (2 * Q)))
    (ht : t ∈ Icc (t' - localPropagationRadius C2 / (2 * Q)) t') :
    G.flow.scalar t y ≤ 8 * Q := by
  have : IsManifold I3 1 P.Carrier := IsManifold.of_le (n := ∞) (by decide)
  have hc : 0 < localPropagationRadius C2 := localPropagationRadius_pos hC2
  have hh := scalar_le_of_left_derivative_bounds (I := I3) G.equation
    (CStar := C2) (Q := Q) (Hd := 2 * localPropagationRadius C2) (L := 2) (t0 := t')
    (s := t') (v := t) (z := x') (y := y) hC2 hQ (by norm_num) le_rfl
    (fun r hr => show r ∈ Ico a s from ⟨ha.le.trans hr.1, hr.2.trans_lt ht'⟩)
    (fun r hr => Filter.mem_of_superset (Icc_mem_nhdsLE (ha.trans_le hr.1))
      (fun q hq => show q ∈ Ico a s from
        ⟨hq.1, hq.2.trans_lt (hr.2.trans_lt ht')⟩))
    (by
      intro w r hr hR
      obtain ⟨W⟩ := hcan w r (ha.trans_le hr.1) hr.2 hR
      refine ⟨fun v => ?_, W.time_derivative⟩
      have hR0 : 0 ≤ G.flow.scalar r w := W.Q_pos.le
      have hnn : 0 ≤ C2 * (G.flow.scalar r w * Real.sqrt (G.flow.scalar r w)) *
          Real.sqrt ((G.flow.base.metric r).inner w v v) :=
        mul_nonneg (mul_nonneg hC2 (mul_nonneg hR0 (Real.sqrt_nonneg _)))
          (Real.sqrt_nonneg _)
      linarith [W.gradient v])
    ⟨by
      have h0 : 0 ≤ 2 * localPropagationRadius C2 / (2 * Q) := by positivity
      linarith, le_rfl⟩
    (by linarith)
    (by rwa [mul_comm Q 2])
    (by rwa [mul_comm Q 2])
  linarith

theorem sqrt_rmNormSq_le_on_backward_cylinder_of_canonicalWitness
    {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s)
    {eps C1 C2 Q t' : ℝ} {x' : P.Carrier} {Phi : ℝ → ℝ} (hC2 : 0 ≤ C2) (hQ : 0 < Q)
    (hPhi : Perelman.AdmissiblePinchingFunction Phi)
    (hpinch : Perelman.PhiAlmostNonnegative G.flow (Ico a s) Phi)
    (hx' : G.flow.scalar t' x' ≤ Q) (ht' : t' < s)
    (ha : a < t' - 2 * localPropagationRadius C2 / Q)
    (hcan : ∀ (y : P.Carrier) (t : ℝ), a < t → t ≤ t' → 2 * Q ≤ G.flow.scalar t y →
      Nonempty (CanonicalWitness G.flow eps C1 C2 y t))
    {y : P.Carrier} {t : ℝ}
    (hy : y ∈ riemannianClosedBallOf (I := I3) (G.flow.base.metric t') x'
      (localPropagationRadius C2 / Real.sqrt (2 * Q)))
    (ht : t ∈ Icc (t' - localPropagationRadius C2 / (2 * Q)) t') :
    Real.sqrt (Perelman.FlowMetricBall.rmNormSq G.flow t y) ≤
      4 * Real.sqrt 3 * (2 * Q + Phi (8 * Q) + Phi 0) := by
  have : IsManifold I3 1 P.Carrier := IsManifold.of_le (n := ∞) (by decide)
  have hscalar := G.scalar_le_on_backward_cylinder_of_canonicalWitness hC2 hQ hx' ht' ha
    hcan hy ht
  have hc : 0 < localPropagationRadius C2 := localPropagationRadius_pos hC2
  have hshift : localPropagationRadius C2 / (2 * Q) ≤ 2 * localPropagationRadius C2 / Q := by
    rw [div_le_div_iff₀ (by positivity) hQ]
    nlinarith [mul_pos hc hQ]
  have htmem : t ∈ Ico a s := ⟨by linarith [ht.1], ht.2.trans_lt ht'⟩
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  have hbridge : RmNormBoundOn G.flow (2 * Real.sqrt 3) :=
    fun r w basis horth c hc' =>
      sqrt_rmNormSq_le_of_abs_orderedSectionalCurvaturesAt_le G.flow r w basis horth hc'
  have hrm := sqrt_rmNormSq_le_of_scalar_le (I := I3)
    (by positivity : 0 ≤ 2 * Real.sqrt 3) hbridge hPhi hpinch hdim htmem y
    (by positivity : 0 < 2 * Q) (by linarith : G.flow.scalar t y ≤ 4 * (2 * Q))
  rw [show 4 * (2 * Q) = 8 * Q by ring] at hrm
  exact hrm.trans_eq (by ring)

end OrientedThreeStage.IncomingSlab

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
