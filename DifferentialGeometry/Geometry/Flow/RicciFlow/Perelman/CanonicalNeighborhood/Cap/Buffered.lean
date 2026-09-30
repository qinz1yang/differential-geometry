import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.BufferedCanonical
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckDiameter

section
set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem exists_common_buffer_constant_of_cap_collar
    (A C : ℝ) (hC : 1 ≤ C) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
      [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
      (D : RealTimeInterval) (S : SolutionOn (I := I3) (M := M) D)
      (eps alpha H : ℝ) (p v : M) (t : ℝ) (K : CanonicalWitness S eps A C p t),
      eps < alpha → ∀ cap : LocalCap S eps p t K.domain.carrier,
      (∃ depth, K.alternative = CanonicalAlternative.cap cap depth) →
      ∀ neck : StrongNeck S alpha v t, v ∈ cap.tube →
      (∀ y ∈ neck.map '' (univ ×ˢ ({0} : Set ℝ)),
        H / Real.sqrt (S.scalar t p) ≤ metricDistance (S.base.metric t) p y) →
      ∃ out : BufferedCanonical S alpha B H p t,
        out.tolerance = eps ∧ out.witness.domain.carrier = K.domain.carrier ∧ out.witness.radius = K.radius ∧
        ∃ cap' depth, out.witness.alternative = CanonicalAlternative.cap cap' depth ∧ HEq cap' cap := by
  obtain ⟨Cd, hCd, hdiam⟩ := metricDistance_core_le_of_neckCoreDiameterBound.{u} neckCoreDiameterBound_holds
  let C0 := max C (Cd * Real.sqrt C)
  have hC0 : C ≤ C0 := le_max_left _ _
  have hCd0 : Cd * Real.sqrt C ≤ C0 := le_max_right _ _
  refine ⟨max A C0 + 1, by linarith [le_max_right A C0], ?_⟩
  intro M _ _ _ _ _ D S eps alpha H p v t K heps cap hcap neck hv hfar
  have hCp : 0 < C := zero_lt_one.trans_le hC
  have hvK : v ∈ K.domain.carrier := cap.union_eq.symm ▸ Or.inr hv
  have hprod : S.scalar t p ≤ C * S.scalar t v := by
    have hh := mul_le_mul_of_nonneg_left (K.scalar_bounds v hvK).1 hCp.le
    simpa only [← mul_assoc, mul_inv_cancel₀ hCp.ne', one_mul] using hh
  have hroot : Real.sqrt (S.scalar t p) ≤ Real.sqrt C * Real.sqrt (S.scalar t v) := by
    simpa only [Real.sqrt_mul hCp.le] using Real.sqrt_le_sqrt hprod
  let K0 := K.enlargeConstants le_rfl hC0
  have hK0cap : ∃ depth, K0.alternative = CanonicalAlternative.cap cap depth := by
    obtain ⟨depth, hdepth⟩ := hcap
    refine ⟨depth, ?_⟩
    change K.alternative.monoConstant (zero_lt_one.trans_le K.one_le_comparison_constant) hC0 K.Q_pos.le = _
    rw [hdepth]
    rfl
  have hvU : v ∈ K0.domain.carrier := cap.union_eq.symm ▸ Or.inr hv
  have hscalar := K0.scalar_bounds v hvU
  have hinv : (max A C0 + 1)⁻¹ ≤ C0⁻¹ := inv_anti₀
    (zero_lt_one.trans_le K0.one_le_comparison_constant) (by linarith [le_max_right A C0])
  have hCinc : C0 ≤ max A C0 + 1 := by linarith [le_max_right A C0]
  have hcentral : neck.map '' (univ ×ˢ ({0} : Set ℝ)) ⊆ neck.map '' (univ ×ˢ Icc (-10 : ℝ) 10) := by
    apply image_mono
    intro z hz
    have hz0 : z.2 = 0 := hz.2
    exact ⟨hz.1, by rw [hz0]; norm_num⟩
  have hdiam' (y : M) (hy : y ∈ neck.map '' (univ ×ˢ ({0} : Set ℝ)))
      (z : M) (hz : z ∈ neck.map '' (univ ×ˢ ({0} : Set ℝ))) :
      metricDistance (S.base.metric t) y z ≤ (max A C0 + 1) / Real.sqrt (S.scalar t p) := by
    have hh := hdiam M D S alpha v t neck y (hcentral hy) z (hcentral hz)
    have hratio : Cd / Real.sqrt (S.scalar t v) ≤ (Cd * Real.sqrt C) / Real.sqrt (S.scalar t p) := by
      apply (div_le_div_iff₀ (Real.sqrt_pos.mpr neck.Q_pos) (Real.sqrt_pos.mpr K.Q_pos)).mpr
      have hh := mul_le_mul_of_nonneg_left hroot hCd.le
      simpa only [mul_assoc] using hh
    exact hh.trans (hratio.trans (div_le_div_of_nonneg_right (hCd0.trans hCinc) (Real.sqrt_nonneg _)))
  obtain ⟨hCfinal, hAfinal, hCfinal0, hscal, hrm, hvol⟩ := K0.strict_curvature_volume_reserves
  let Kfinal := K0.enlargeConstants hAfinal.le hCfinal0.le
  obtain ⟨a, b, margin, ha, _har, hm, hbm, hinner, houter⟩ := Kfinal.exists_radial_reserve
  have hKfinalCap : ∃ depth, Kfinal.alternative = CanonicalAlternative.cap cap depth := by
    obtain ⟨depth, hdepth⟩ := hK0cap
    refine ⟨depth, ?_⟩
    change K0.alternative.monoConstant (zero_lt_one.trans_le K0.one_le_comparison_constant) hCfinal0.le K0.Q_pos.le = _
    rw [hdepth]
    rfl
  let B : BufferedCanonical S alpha (max A C0 + 1) H p t := {
    tolerance := eps
    tolerance_pos := K.eps_pos
    tolerance_lt := heps
    witness := Kfinal
    a := a
    b := b
    margin := margin
    a_pos := ha
    margin_pos := hm
    radial_margin := hbm.le
    inner_ball := hinner
    outer_ball := houter
    scalar_reserve := hscal
    rm_reserve := hrm
    volume_reserve := fun hv => hvol (by
      simpa only [Kfinal, CanonicalWitness.enlarge_constants_requiresVolume] using hv)
    cap_collar := by
      intro cap' hc
      obtain ⟨depth0, hzero⟩ := hKfinalCap
      obtain ⟨depth', heq⟩ := hc
      rw [hzero] at heq
      cases heq
      exact ⟨v, neck, hv,
        (mul_le_mul_of_nonneg_right hinv K.Q_pos.le).trans hscalar.1,
        hscalar.2.trans (mul_le_mul_of_nonneg_right hCinc K.Q_pos.le), hfar, hdiam'⟩ }
  obtain ⟨depth, halt⟩ := hKfinalCap
  exact ⟨B, rfl, rfl, rfl, cap, depth, halt, HEq.rfl⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

end

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
  {eps A C alpha H : ℝ} {p v : M} {t : ℝ}

theorem CanonicalWitness.exists_bufferedCanonical_of_cap_collar
    (K : CanonicalWitness S eps A C p t) (heps : eps < alpha)
    (cap : LocalCap S eps p t K.domain.carrier)
    (hcap : ∃ depth, K.alternative = CanonicalAlternative.cap cap depth)
    (neck : StrongNeck S alpha v t) (hv : v ∈ cap.tube)
    (hfar : ∀ y ∈ neck.map '' (univ ×ˢ ({0} : Set ℝ)),
      H / Real.sqrt (S.scalar t p) ≤ metricDistance (S.base.metric t) p y) :
    ∃ C' : ℝ, 1 ≤ C' ∧ ∃ B : BufferedCanonical S alpha C' H p t,
      B.tolerance = eps ∧ B.witness.domain.carrier = K.domain.carrier ∧ B.witness.radius = K.radius ∧
      ∃ cap' depth, B.witness.alternative = CanonicalAlternative.cap cap' depth ∧ HEq cap' cap := by
  obtain ⟨C', hC', hbuffer⟩ := exists_common_buffer_constant_of_cap_collar.{u}
    A C K.one_le_comparison_constant
  obtain ⟨B, hBeps, hBdomain, hBradius, hBcap⟩ :=
    hbuffer M D S eps alpha H p v t K heps cap hcap neck hv hfar
  exact ⟨C', hC', B, hBeps, hBdomain, hBradius, hBcap⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
