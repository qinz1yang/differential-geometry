import DifferentialGeometry.Geometry.Geodesic.CompactDisplacement
import DifferentialGeometry.Geometry.Comparison.Variation.SmoothEnergy
import DifferentialGeometry.Analysis.Calculus.SecondDerivative.Minimum
import DifferentialGeometry.Topology.Manifold.SmoothInterval

noncomputable section
open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold ContDiff Topology ENNReal
open DifferentialGeometry
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Geodesic

namespace DifferentialGeometry.Geometry.Riemannian


def IsTwistedPath {M : Type*} (F : M → M) (L : ℝ) (c : ℝ → M) : Prop :=
  c L = F (c 0)


def IsTwistedVariation {M : Type*} (F : M → M) (L ε : ℝ) (f : ℝ → ℝ → M) : Prop :=
  ∀ s ∈ Ioo (-ε) ε, IsTwistedPath F L (f s)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]


def SmoothNearInterval (c : ℝ → M) (L : ℝ) : Prop :=
  ∃ U : Set ℝ, IsOpen U ∧ Icc 0 L ⊆ U ∧ ContMDiffOn 𝓘(ℝ, ℝ) I ∞ c U

theorem SmoothNearInterval.energy_integrable {c : ℝ → M} {L : ℝ}
    (hc : SmoothNearInterval (I := I) c L) (hL : 0 ≤ L)
    (g : SmoothRiemannianMetric I M) :
    IntegrableOn (fun t => g.inner (c t) (mfderiv 𝓘(ℝ, ℝ) I c t 1)
      (mfderiv 𝓘(ℝ, ℝ) I c t 1)) (Icc 0 L) := by
  obtain ⟨U, hU, hsub, hcU⟩ := hc
  obtain ⟨d, hd, heq⟩ := DifferentialGeometry.Topology.Manifold.exists_global_smooth_curve_eq_near_interval
    hL hU hsub hcU
  have hfd : ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞ (fun p : ℝ × ℝ => d p.2) :=
    hd.comp (contDiff_snd.contMDiff)
  have hD := (Variation.curveEnergyDensity_contDiff g (fun p : ℝ × ℝ => d p.2) hfd).continuous
  have hcont : Continuous (fun t => g.inner (d t) (mfderiv 𝓘(ℝ, ℝ) I d t 1)
      (mfderiv 𝓘(ℝ, ℝ) I d t 1)) := hD.comp ((continuous_const (y := (0 : ℝ))).prodMk continuous_id)
  apply (hcont.continuousOn.congr ?_).integrableOn_Icc
  intro t ht
  have hbase := (heq t ht).eq_of_nhds
  have hderiv := (heq t ht).mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := I)
  change g.inner (c t) (mfderiv 𝓘(ℝ, ℝ) I c t 1) (mfderiv 𝓘(ℝ, ℝ) I c t 1) = _
  dsimp only
  rw [hbase, hderiv]
  rfl

omit [IsManifold I ∞ M] in
theorem SmoothNearInterval.contMDiffOn {c : ℝ → M} {L : ℝ}
    (hc : SmoothNearInterval (I := I) c L) :
    ContMDiffOn 𝓘(ℝ, ℝ) I 1 c (Icc 0 L) := by
  obtain ⟨U, _, hsub, hc⟩ := hc
  exact (hc.of_le (by simp)).mono hsub

omit [IsManifold I ∞ M] in
theorem smoothNearInterval_slice {f : ℝ × ℝ → M} {L ε s : ℝ}
    {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hsub : (Ioo (-ε) ε ×ˢ Icc 0 L) ⊆ U)
    (hf : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ f U) (hs : s ∈ Ioo (-ε) ε) :
    SmoothNearInterval (I := I) (fun t => f (s, t)) L := by
  let V := (fun t : ℝ => (s, t)) ⁻¹' U
  have hi : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ (fun t : ℝ => (s, t)) :=
    (contDiff_const.prodMk contDiff_id).contMDiff
  refine ⟨V, hU.preimage hi.continuous, fun t ht => hsub ⟨hs, ht⟩, ?_⟩
  exact hf.comp hi.contMDiffOn (fun _ ht => ht)

variable [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [T2Space M] [CompactSpace M] [ConnectedSpace M]

theorem exists_minimal_twisted_geodesic (g : SmoothRiemannianMetric I M) (F : M → M)
    (hF : Continuous F) (hfree : ∀ x, F x ≠ x) :
    ∃ (p : M) (L : ℝ) (γ : ℝ → M), 0 < L ∧
      riemannianEDistOf (I := I) g p (F p) = ENNReal.ofReal L ∧
      (∀ x, L ≤ (riemannianEDistOf (I := I) g x (F x)).toReal) ∧
      γ 0 = p ∧ γ L = F p ∧ ContMDiff 𝓘(ℝ, ℝ) I ∞ γ ∧
      IsGeodesic (I := I) g γ ∧
      (∀ t, g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1)
        (mfderiv 𝓘(ℝ, ℝ) I γ t 1) = 1) ∧
      curveEnergy (I := I) g γ 0 L = L ∧
      (∀ c : ℝ → M, SmoothNearInterval (I := I) c L → IsTwistedPath F L c →
        L ≤ curveEnergy (I := I) g c 0 L) := by
  obtain ⟨p, L, γ, hL, hd, hm, h0, h1, hs, hg, hv, hE, hmin⟩ :=
    exists_minimal_displacement_geodesic g F hF hfree
  refine ⟨p, L, γ, hL, hd, hm, h0, h1, hs, hg, hv, hE, ?_⟩
  intro c hc htw
  exact hmin c hc.contMDiffOn (hc.energy_integrable hL.le g) htw

theorem exists_minimal_twisted_geodesic_with_derivative_test
    (g : SmoothRiemannianMetric I M) (F : M → M)
    (hF : Continuous F) (hfree : ∀ x, F x ≠ x) :
    ∃ (L : ℝ) (γ : ℝ → M), 0 < L ∧ ContMDiff 𝓘(ℝ, ℝ) I ∞ γ ∧
      IsGeodesic (I := I) g γ ∧ IsTwistedPath F L γ ∧
      (∀ t, g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1)
        (mfderiv 𝓘(ℝ, ℝ) I γ t 1) = 1) ∧
      curveEnergy (I := I) g γ 0 L = L ∧
      (∀ (ε : ℝ) (f : ℝ × ℝ → M) (U : Set (ℝ × ℝ)),
        0 < ε → IsOpen U → (Ioo (-ε) ε ×ˢ Icc 0 L) ⊆ U →
        ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ f U →
        IsTwistedVariation F L ε (fun s t => f (s, t)) →
        (fun t => f (0, t)) = γ →
        deriv (fun s => curveEnergy (I := I) g (fun t => f (s, t)) 0 L) 0 = 0 ∧
        0 ≤ deriv (deriv (fun s => curveEnergy (I := I) g (fun t => f (s, t)) 0 L)) 0) := by
  obtain ⟨p, L, γ, hL, _, _, h0, h1, hs, hg, hv, hE, hmin⟩ :=
    exists_minimal_twisted_geodesic g F hF hfree
  refine ⟨L, γ, hL, hs, hg, ?_, hv, hE, ?_⟩
  · exact h1.trans (congrArg F h0.symm)
  intro ε f U hε hU hsub hf htw hcenter
  have hmem : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith, hε⟩
  have hnb : Ioo (-ε) ε ∈ 𝓝 (0 : ℝ) := isOpen_Ioo.mem_nhds hmem
  have hlocal : IsLocalMin (fun s => curveEnergy (I := I) g (fun t => f (s, t)) 0 L) 0 := by
    filter_upwards [hnb] with s hs
    change curveEnergy (I := I) g (fun t => f (0, t)) 0 L ≤ _
    rw [hcenter, hE]
    exact hmin _ (smoothNearInterval_slice hU hsub hf hs) (htw s hs)
  have hsmooth := Variation.curveEnergy_contDiffOn_of_smooth_near_strip g f hL.le hU hsub hf
  exact ⟨hlocal.deriv_eq_zero, DifferentialGeometry.Analysis.second_deriv_nonneg_of_isLocalMin
    hlocal (hsmooth.contDiffAt hnb).continuousAt⟩

end DifferentialGeometry.Geometry.Riemannian
