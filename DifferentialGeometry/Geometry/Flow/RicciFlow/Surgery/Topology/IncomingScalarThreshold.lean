import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ScalarCrossingTime
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventData
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.RmNormFromEigenvalues

set_option autoImplicit false

open Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem OrientedThreeStage.IncomingSlab.exists_scalar_gt_of_singularEndpoint
    {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s)
    (hsing : G.SingularEndpoint) {Phi : ℝ → ℝ} (hPhi : AdmissiblePinchingFunction Phi)
    (hpinch : PhiAlmostNonnegative G.flow (Ico a s) Phi)
    (B : ℝ) {d : ℝ} (hd : d ∈ Ico a s) :
    ∃ t ∈ Ioo d s, ∃ x : P.Carrier, B < G.flow.scalar t x := by
  obtain ⟨C, hC, hbound⟩ := exists_rmNormLeOfCurvatureOperatorBounds.{u} ThreeModel
  have hnorm := hbound P.Carrier G.flow
  let A := max B 1
  have hA : 0 < A := zero_lt_one.trans_le (le_max_right _ _)
  let K := 2 * C * (A + Phi (4 * A) + Phi 0)
  obtain ⟨t, ht, x, hx⟩ := hsing (max K 0 + 1) (by positivity) d hd
  refine ⟨t, ht, x, ?_⟩
  by_contra h
  have hscalar : G.flow.scalar t x ≤ 4 * A :=
    (le_of_not_gt h).trans ((le_max_left _ _).trans (by linarith))
  have hub : G.riemannNorm t x ≤ K :=
    sqrt_rmNormSq_le_of_scalar_le hC hnorm hPhi hpinch (by simp [ThreeSpace])
      ⟨hd.1.trans ht.1.le, ht.2⟩ x hA hscalar
  have hK : K ≤ max K 0 := le_max_left _ _
  linarith

theorem exists_scalar_first_crossing_time_lower_bound_of_singularEndpoint :
    ∃ C : ℝ, 0 < C ∧ ∀ {P : OrientedThreeStage.{u}} {a s : ℝ}
      (G : P.IncomingSlab a s), G.SingularEndpoint →
      ∀ {Phi : ℝ → ℝ}, AdmissiblePinchingFunction Phi →
      PhiAlmostNonnegative G.flow (Ico a s) Phi →
      ∀ {A B : ℝ}, 0 < A → A < B →
      (∀ x : P.Carrier, G.flow.scalar a x ≤ A) →
      (∀ t ∈ Ioo a s, ∀ x : P.Carrier, A < G.flow.scalar t x →
        ∃ eps kappa : ℝ, eps ≤ 1 / 4 ∧
          Nonempty (WindowedModelWitness eps kappa G.flow x t)) →
      ∃ t ∈ Ioo a s, ∃ x : P.Carrier, G.flow.scalar t x = B ∧
        (∀ v ∈ Ico a t, ∀ y : P.Carrier, G.flow.scalar v y < B) ∧
        (∀ y : P.Carrier, G.flow.scalar t y ≤ B) ∧
        (A⁻¹ - B⁻¹) / C ≤ t - a := by
  obtain ⟨C, hC, hcross⟩ := exists_scalar_first_crossing_time_lower_bound.{u}
  refine ⟨C, hC, ?_⟩
  intro P a s G hsing Phi hPhi hpinch A B hA hAB hreset hcover
  obtain ⟨b, hb, x, hx⟩ := G.exists_scalar_gt_of_singularEndpoint hsing hPhi hpinch B
    ⟨le_rfl, G.lt⟩
  have hslab : Icc a b ⊆ (RealTimeInterval.closedOpen a s G.lt).carrier :=
    fun t ht => ⟨ht.1, ht.2.trans_lt hb.2⟩
  have hmodel : ∀ t ∈ Ioo a b, ∀ x : P.Carrier, A < G.flow.scalar t x →
      ∃ eps kappa : ℝ, eps ≤ 1 / 4 ∧
        Nonempty (WindowedModelWitness eps kappa G.flow x t) ∧
        Ioo (t - (eps * G.flow.scalar t x)⁻¹) t ⊆
          (RealTimeInterval.closedOpen a s G.lt).regular := by
    intro t ht x hhigh
    obtain ⟨eps, kappa, heps, ⟨W⟩⟩ := hcover t ⟨ht.1, ht.2.trans hb.2⟩ x hhigh
    refine ⟨eps, kappa, heps, ⟨W⟩, ?_⟩
    simpa only [RealTimeInterval.closedOpen, interior_Icc, interior_Ico] using
      interior_mono W.window_mem
  obtain ⟨t, ht, y, hy, hbefore, hlevel, htime⟩ :=
    hcross G.equation hb.1.le hA hAB hslab hreset ⟨x, hx.le⟩ hmodel
  exact ⟨t, ⟨ht.1, ht.2.trans_lt hb.2⟩, y, hy, hbefore, hlevel, htime⟩

theorem exists_incomingSlab_singular_time_lower_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {P : OrientedThreeStage.{u}} {a s : ℝ}
      (G : P.IncomingSlab a s), G.SingularEndpoint →
      ∀ {Phi : ℝ → ℝ}, AdmissiblePinchingFunction Phi →
      PhiAlmostNonnegative G.flow (Ico a s) Phi →
      ∀ {A : ℝ}, 0 < A →
      (∀ x : P.Carrier, G.flow.scalar a x ≤ A) →
      (∀ t ∈ Ioo a s, ∀ x : P.Carrier, A < G.flow.scalar t x →
        ∃ eps kappa : ℝ, eps ≤ 1 / 4 ∧
          Nonempty (WindowedModelWitness eps kappa G.flow x t)) →
      A⁻¹ / C ≤ s - a := by
  obtain ⟨C, hC, hcross⟩ := exists_scalar_first_crossing_time_lower_bound_of_singularEndpoint.{u}
  refine ⟨C, hC, ?_⟩
  intro P a s G hsing Phi hPhi hpinch A hA hreset hcover
  have hbound : ∀ᶠ B : ℝ in Filter.atTop, (A⁻¹ - B⁻¹) / C ≤ s - a := by
    filter_upwards [Filter.eventually_gt_atTop A] with B hAB
    obtain ⟨t, ht, x, hx, hbefore, hlevel, htime⟩ :=
      hcross G hsing hPhi hpinch hA hAB hreset hcover
    exact htime.trans (sub_le_sub_right ht.2.le a)
  have hlim : Filter.Tendsto (fun B : ℝ => (A⁻¹ - B⁻¹) / C)
      Filter.atTop (nhds (A⁻¹ / C)) := by
    simpa only [sub_zero] using
      (tendsto_const_nhds.sub tendsto_inv_atTop_zero).div_const C
  exact le_of_tendsto hlim hbound

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
