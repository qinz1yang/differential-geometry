import DifferentialGeometry.Geometry.Metric.Comparison.CurveEnergy
import DifferentialGeometry.Geometry.Comparison.Distance.Continuity
import DifferentialGeometry.Analysis.Calculus.Compactness.ArzelaAscoli

noncomputable section
namespace DifferentialGeometry.Geometry.Riemannian
open Filter Set
open scoped ContDiff Manifold Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
  {M : Type*} [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem exists_strictMono_tendstoUniformly_of_curveEnergy_le
    (gRef : SmoothRiemannianMetric I M)
    (a b B : Real)
    (alpha : Nat → Real → M)
    (halpha : ∀ n, ContMDiffOn 𝓘(Real, Real) I 1 (alpha n) (Icc a b))
    (henergy : ∀ n, curveEnergy (I := I) gRef (alpha n) a b ≤ B)
    (Q : Set M) (hQc : IsCompact Q)
    (hQ : ∀ n (s : Icc a b), alpha n s.1 ∈ Q) :
    ∃ (phi : Nat → Nat) (g : C(Icc a b, M)),
      StrictMono phi ∧
        TendstoUniformly
          (fun n (s : Icc a b) ↦ alpha (phi n) s.1) g atTop := by
  classical
  have hE (n : Nat) := integrableOn_inner_mfderiv_self_of_contMDiffOn gRef (halpha n)
  have hriedist (n : Nat) {s t : Real}
      (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) :
      riemannianEDistOf (I := I) gRef (alpha n s) (alpha n t) ≤
        ENNReal.ofReal (Real.sqrt (t - s) * Real.sqrt B) := by
    have hsub : Icc s t ⊆ Icc a b := Icc_subset_Icc has htb
    have hsubE : curveEnergy (I := I) gRef (alpha n) s t ≤
        curveEnergy (I := I) gRef (alpha n) a b :=
      curveEnergy_mono (I := I) gRef has hst htb (hE n)
    exact edistOf_le_budget (I := I) gRef hst
      ((halpha n).mono hsub) ((hE n).mono_set hsub)
      (hsubE.trans (henergy n))
  let f : Nat → C(Icc a b, M) := fun n ↦
    ⟨fun s ↦ alpha n s.1, (halpha n).continuousOn.domRestrict⟩
  have hmod : Tendsto (fun r : Real ↦ Real.sqrt r * Real.sqrt B)
      (𝓝 0) (𝓝 0) := by
    have hcont : Continuous (fun r : Real ↦ Real.sqrt r * Real.sqrt B) :=
      Real.continuous_sqrt.mul continuous_const
    simpa only [Real.sqrt_zero, zero_mul] using hcont.tendsto (0 : Real)
  have hunif : UniformEquicontinuous (fun n ↦ (f n : Icc a b → M)) := by
    rw [Metric.uniformEquicontinuous_iff]
    intro epsilon hepsilon
    obtain ⟨rho, hrho, htoDist⟩ :=
      dist_lt_riedist_compact (I := I) gRef Q hQc hepsilon
    obtain ⟨delta, hdelta, hmodDelta⟩ :=
      Metric.tendsto_nhds_nhds.1 hmod rho hrho
    refine ⟨delta, hdelta, ?_⟩
    intro s t hst n
    have hsmall : Real.sqrt (dist s t) * Real.sqrt B < rho := by
      have h := hmodDelta (x := dist s t) (by simpa using hst)
      simpa only [Real.dist_eq, sub_zero,
        abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
        using h
    have hofReal : ENNReal.ofReal (Real.sqrt (dist s t) * Real.sqrt B) <
        ENNReal.ofReal rho := (ENNReal.ofReal_lt_ofReal_iff hrho).2 hsmall
    rcases le_total s.1 t.1 with hst' | hts
    · have hriem := hriedist n s.2.1 hst' t.2.2
      have hriem' := hriem.trans_lt (by
        simpa only [Subtype.dist_eq, Real.dist_eq,
          abs_of_nonpos (sub_nonpos.mpr hst'), neg_sub] using hofReal)
      change dist (alpha n s.1) (alpha n t.1) < epsilon
      exact htoDist (alpha n s.1) (hQ n s) (alpha n t.1) (hQ n t) hriem'
    · have hriem := hriedist n t.2.1 hts s.2.2
      have hriem' := hriem.trans_lt (by
        simpa only [Subtype.dist_eq, Real.dist_eq,
          abs_of_nonneg (sub_nonneg.mpr hts)] using hofReal)
      have hout :=
        htoDist (alpha n t.1) (hQ n t) (alpha n s.1) (hQ n s) hriem'
      change dist (alpha n s.1) (alpha n t.1) < epsilon
      simpa only [dist_comm] using hout
  obtain ⟨phi, g, hphi, hconv⟩ :=
    DifferentialGeometry.Analysis.arzela_subseq_compact Q hQc f hQ hunif.equicontinuous
  refine ⟨phi, g, hphi, ?_⟩
  change TendstoUniformly (fun n s => alpha (phi n) s.1) g atTop at hconv
  exact hconv

theorem exists_strictMono_tendstoUniformly_of_curveEnergy_le_of_endpoints
    (gRef : SmoothRiemannianMetric I M)
    (a b B : Real) (hab : a ≤ b)
    (alpha : Nat → Real → M)
    (halpha : ∀ n, ContMDiffOn 𝓘(Real, Real) I 1 (alpha n) (Icc a b))
    (henergy : ∀ n, curveEnergy (I := I) gRef (alpha n) a b ≤ B)
    (Q : Set M) (hQc : IsCompact Q)
    (hQ : ∀ n (s : Icc a b), alpha n s.1 ∈ Q)
    (x y : M) (hfixa : ∀ n, alpha n a = x)
    (hfixb : ∀ n, alpha n b = y) :
    ∃ (phi : Nat → Nat) (g : C(Icc a b, M)),
      StrictMono phi ∧
        TendstoUniformly
          (fun n (s : Icc a b) ↦ alpha (phi n) s.1) g atTop ∧
        g ⟨a, le_rfl, hab⟩ = x ∧ g ⟨b, hab, le_rfl⟩ = y := by
  obtain ⟨phi, g, hphi, hconv⟩ :=
    exists_strictMono_tendstoUniformly_of_curveEnergy_le (I := I) gRef a b B alpha halpha henergy Q hQc hQ
  refine ⟨phi, g, hphi, hconv, ?_, ?_⟩
  · have hlim := hconv.tendsto_at (⟨a, le_rfl, hab⟩ : Icc a b)
    have hlim' : Tendsto (fun _ : Nat ↦ x) atTop
        (𝓝 (g ⟨a, le_rfl, hab⟩)) := by
      simpa only [hfixa] using hlim
    exact tendsto_nhds_unique hlim' tendsto_const_nhds
  · have hlim := hconv.tendsto_at (⟨b, hab, le_rfl⟩ : Icc a b)
    have hlim' : Tendsto (fun _ : Nat ↦ y) atTop
        (𝓝 (g ⟨b, hab, le_rfl⟩)) := by
      simpa only [hfixb] using hlim
    exact tendsto_nhds_unique hlim' tendsto_const_nhds

end DifferentialGeometry.Geometry.Riemannian
