import DifferentialGeometry.Geometry.Compactness.CheegerGromov.BoundedGeometry.BranchMin



import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Gluing.CageScale

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Bundle Manifold Set TopologicalSpace
open scoped ContDiff Manifold NNReal Topology

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

namespace BoundedGeometryNormalData

omit [CompleteSpace E] in
theorem exists_live_scale
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    (d : BoundedGeometryNormalData (I := I) X hd)
    (hre : hd.RealizesEdist)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M) :
    let N : NNReal :=
      ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
        (E × E) →L[Real] (E × E))‖₊
    let T : NNReal := N⁻¹
    ∃ aMin : Real, 0 < aMin ∧
      ∀ {D : Real} (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
        (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real),
        ∃ q : LiveSlot L pb r → NNReal,
          ∃ δ : LiveSlot L pb r → Real,
            (∀ gamma : LiveSlot L pb r,
              let Rgamma := L.rInf (gamma.1 : Nat) + 1
              let rho := aMin * hd.mu Rgamma
              0 < q gamma ∧ 0 < δ gamma ∧ 0 < rho ∧
                2 * rho < (q gamma : Real) ∧
                6 * (q gamma : Real) < d.phaseRadius Rgamma ∧
                3 * d.metricC 1 * (2 * (q gamma : Real)) ^ 2 ≤
                  (2 / 3 : Real) * (q gamma : Real) ∧
                PhaseFlow.phaseErr (d.phaseK (2 * q gamma)) < T ∧
                N * (T - PhaseFlow.phaseErr
                    (d.phaseK (2 * q gamma)))⁻¹ *
                    PhaseFlow.phaseErr (d.phaseK (2 * q gamma)) < 1 / 24) ∧
            ∀ᶠ n in Filter.atTop, ∀ gamma : LiveSlot L pb r,
              let Rgamma := L.rInf (gamma.1 : Nat) + 1
              let rho := aMin * hd.mu Rgamma
              let x := seqCenterD hd P L n (gamma.1 : Nat)
              letI : TopologicalSpace (X.obj (L.φ n)).M :=
                (X.obj (L.φ n)).topology
              letI : ChartedSpace H (X.obj (L.φ n)).M :=
                (X.obj (L.φ n)).charted
              letI : IsManifold I ∞ (X.obj (L.φ n)).M :=
                (X.obj (L.φ n)).smooth
              letI : SigmaCompactSpace (X.obj (L.φ n)).M :=
                (X.obj (L.φ n)).sigmaCompact
              letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
              letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
                (X.obj (L.φ n)).t2TangentBundle
              ∃ e : OpenPartialHomeomorph (E × E) (E × E),
                IsNormalDiag (I := I) (X.obj (L.φ n))
                    (hcomplete.complete (L.φ n)) (hconn (L.φ n))
                    x (q gamma) (δ gamma) e (c := d.chart (L.φ n) x) ∧
                  NormalDiagFence (I := I) (X.obj (L.φ n))
                    x (q gamma) e (c := d.chart (L.φ n) x) ∧
                  ApproximatesLinearOn
                    (e.symm : E × E → E × E)
                    ((PhaseFlow.freeDiagCLE (E := E)).symm :
                      (E × E) →L[Real] (E × E))
                    e.target
                    (N * (T - PhaseFlow.phaseErr
                      (d.phaseK (2 * q gamma)))⁻¹ *
                      PhaseFlow.phaseErr (d.phaseK (2 * q gamma))) ∧
                  rho ≤ (d.chart (L.φ n) x).radius / 4 := by
  classical
  let N : NNReal :=
    ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
      (E × E) →L[Real] (E × E))‖₊
  let T : NNReal := N⁻¹
  obtain ⟨aq, aδ, aMin, haq, haδ, haMin, hscale⟩ :=
    d.exists_min_scale hcomplete hconn
  refine ⟨aMin, haMin, ?_⟩
  intro D P L pb r
  have hslot : ∀ gamma : LiveSlot L pb r,
      ∃ (q : NNReal) (δ : Real),
        let Rgamma := L.rInf (gamma.1 : Nat) + 1
        let rho := aMin * hd.mu Rgamma
        0 < q ∧ 0 < δ ∧ 0 < rho ∧ 2 * rho < (q : Real) ∧
          6 * (q : Real) < d.phaseRadius Rgamma ∧
          3 * d.metricC 1 * (2 * (q : Real)) ^ 2 ≤
            (2 / 3 : Real) * (q : Real) ∧
          PhaseFlow.phaseErr (d.phaseK (2 * q)) < T ∧
          N * (T - PhaseFlow.phaseErr (d.phaseK (2 * q)))⁻¹ *
              PhaseFlow.phaseErr (d.phaseK (2 * q)) < 1 / 24 ∧
          ∀ k (x : (X.obj k).M),
            hd.dist k x (X.obj k).basepoint ≤ Rgamma →
            letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
            letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
            letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
            letI : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
            letI : T2Space (X.obj k).M := (X.obj k).t2
            letI : T2Space (TangentBundle I (X.obj k).M) :=
              (X.obj k).t2TangentBundle
            ∃ e : OpenPartialHomeomorph (E × E) (E × E),
              IsNormalDiag (I := I) (X.obj k) (hcomplete.complete k)
                  (hconn k) x q δ e (c := d.chart k x) ∧
                NormalDiagFence (I := I) (X.obj k) x q e
                  (c := d.chart k x) ∧
                ApproximatesLinearOn
                  (e.symm : E × E → E × E)
                  ((PhaseFlow.freeDiagCLE (E := E)).symm :
                    (E × E) →L[Real] (E × E))
                  e.target
                  (N * (T - PhaseFlow.phaseErr (d.phaseK (2 * q)))⁻¹ *
                    PhaseFlow.phaseErr (d.phaseK (2 * q))) ∧
                rho ≤ (d.chart k x).radius / 4 := by
    intro gamma
    let Rgamma := L.rInf (gamma.1 : Nat) + 1
    have hR : 0 ≤ Rgamma := by
      dsimp only [Rgamma]
      nlinarith [(L.rInf_mem (gamma.1 : Nat)).1]
    obtain ⟨q, δ, hq, hδ, _hqeq, _hδlower, hqWide, hqAcc,
        herr, hinvErr, hqMin, hbranch⟩ := hscale Rgamma hR
    refine ⟨q, δ, ?_⟩
    dsimp only
    refine ⟨hq, hδ, mul_pos haMin (hd.mu_pos Rgamma), hqMin,
      hqWide, hqAcc, herr, hinvErr, ?_⟩
    intro k x hx
    let : TopologicalSpace (X.obj k).M := (X.obj k).topology
    let : ChartedSpace H (X.obj k).M := (X.obj k).charted
    let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    let : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
    let : T2Space (X.obj k).M := (X.obj k).t2
    let : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    obtain ⟨e, he, hf, happrox, _hradius⟩ := hbranch k x hx
    have hphase :
        d.phaseRadius Rgamma ≤ (d.chart k x).radius / 4 := by
      rw [phaseRadius, d.radius_eq]
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hd.mu_antitone hx) d.ratio_pos.le)
        (by norm_num)
    have hrhoPhase :
        aMin * hd.mu Rgamma < d.phaseRadius Rgamma := by
      nlinarith
    exact ⟨e, he, hf, happrox, (le_of_lt hrhoPhase).trans hphase⟩
  choose q δ hdata using hslot
  refine ⟨q, δ, ?_, ?_⟩
  · intro gamma
    rcases hdata gamma with
      ⟨hq, hδ, hrho, hqMin, hqWide, hqAcc, herr, hinvErr, _hbranch⟩
    exact ⟨hq, hδ, hrho, hqMin, hqWide, hqAcc, herr, hinvErr⟩
  filter_upwards [liveCenters_rInf hd P hre L pb r] with n hn
  intro gamma
  rcases hdata gamma with
    ⟨_hq, _hδ, _hrho, _hqMin, _hqWide, _hqAcc, _herr, _hinvErr,
      hbranch⟩
  exact hbranch (L.φ n) (seqCenterD hd P L n (gamma.1 : Nat))
    (hn gamma).le

end BoundedGeometryNormalData

end HCGCompactness
end DifferentialGeometry
