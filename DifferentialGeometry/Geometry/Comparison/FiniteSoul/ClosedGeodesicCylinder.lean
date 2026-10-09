import DifferentialGeometry.Geometry.Comparison.FiniteSoul.ClosedGeodesicTubeConsumers
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.ClosedGeodesicOrientation
import DifferentialGeometry.Topology.Manifold.AddCircle

/-!
# The orientable tube: `S¹ × (−ε, ε)` (S-TUBE, D3, σ = 1)

Package CM-S (finite soul), lane CMS-T.

* `normalLineBundleOneHomeomorph`: for trivial holonomy the normal line bundle is the cylinder,
  `NormalLineBundle 1 ≃ₜ AddCircle 1 × ℝ`, `[t, h] ↦ (t mod 1, h)`, with `fiberAbs = |·.2|`.
* `exists_closedGeodesic_cylinderTube_of_orientation`: on an oriented complete surface a
  continuous unit normal along a simple closed unit geodesic is periodic, and for some `ε > 0`
  the map `(t mod 1, h) ↦ exp_{γ(ℓ t)}(h ν(ℓ t))` is a calibrated homeomorphism from
  `S¹ × (−ε, ε)` onto `{d_S < ε}` (the form consumed by S6).
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.FiniteSoul

theorem holonomyPow_one_left (k : ℤ) : holonomyPow 1 k = 1 := by
  simp [holonomyPow]

namespace NormalLineBundle

/-- The projection of the trivial line bundle to the cylinder. -/
def toCylinder : NormalLineBundle 1 → AddCircle (1 : ℝ) × ℝ :=
  Quotient.lift (fun z : NormalCover 1 =>
    (((NormalCover.time 1 z : ℝ) : AddCircle (1 : ℝ)), NormalCover.fiber 1 z)) (by
    intro a b hab
    obtain ⟨n, rfl⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp hab)
    change (((NormalCover.time 1 (n • b) : ℝ) : AddCircle (1 : ℝ)), NormalCover.fiber 1 (n • b)) =
      (((NormalCover.time 1 b : ℝ) : AddCircle (1 : ℝ)), NormalCover.fiber 1 b)
    rw [NormalCover.smul_def, NormalCover.time_mk, NormalCover.fiber_mk, holonomyPow_one_left,
      one_mul, AddCircle.coe_add]
    congr 1
    rw [add_eq_left, AddCircle.coe_eq_zero_iff]
    exact ⟨Multiplicative.toAdd n, by simp⟩)

@[simp] theorem toCylinder_mk (t h : ℝ) : toCylinder (mk 1 t h) = ((t : AddCircle (1 : ℝ)), h) :=
  rfl

theorem continuous_toCylinder : Continuous toCylinder :=
  Continuous.quotient_lift
    ((continuous_quotient_mk'.comp (NormalCover.continuous_time 1)).prodMk
      (NormalCover.continuous_fiber 1)) _

theorem bijective_toCylinder : Function.Bijective toCylinder := by
  constructor
  · intro q q' hqq'
    obtain ⟨t, -, h, rfl⟩ := exists_mk_eq 1 q
    obtain ⟨t', -, h', rfl⟩ := exists_mk_eq 1 q'
    rw [toCylinder_mk, toCylinder_mk, Prod.mk.injEq] at hqq'
    obtain ⟨h1, h2⟩ := hqq'
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp (QuotientAddGroup.eq.mp h1)
    rw [mk_eq_mk_iff]
    refine ⟨k, ?_, by rw [holonomyPow_one_left, one_mul, h2]⟩
    rw [zsmul_eq_mul, mul_one] at hk
    linarith
  · rintro ⟨c, h⟩
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective c
    exact ⟨mk 1 t h, rfl⟩

theorem isOpenMap_toCylinder : IsOpenMap toCylinder := by
  intro W hW
  have hpre : IsOpen ((fun p : ℝ × ℝ => mk 1 p.1 p.2) ⁻¹' W) := hW.preimage (continuous_mk 1)
  have hopen : IsOpenMap (fun p : ℝ × ℝ => ((p.1 : AddCircle (1 : ℝ)), p.2)) :=
    (QuotientAddGroup.isOpenMap_coe (N := AddSubgroup.zmultiples (1 : ℝ))).prodMap IsOpenMap.id
  convert hopen _ hpre using 1
  ext ⟨c, h⟩
  constructor
  · rintro ⟨q, hq, hqc⟩
    obtain ⟨t, -, h', rfl⟩ := exists_mk_eq 1 q
    exact ⟨(t, h'), hq, hqc⟩
  · rintro ⟨⟨t, h'⟩, hq, hqc⟩
    exact ⟨mk 1 t h', hq, hqc⟩

/-- **For trivial holonomy the normal line bundle is the cylinder** `AddCircle 1 × ℝ`. -/
def toCylinderHomeomorph : NormalLineBundle 1 ≃ₜ AddCircle (1 : ℝ) × ℝ :=
  (Equiv.ofBijective toCylinder bijective_toCylinder).toHomeomorphOfContinuousOpen
    continuous_toCylinder isOpenMap_toCylinder

@[simp] theorem toCylinderHomeomorph_apply (q : NormalLineBundle 1) :
    toCylinderHomeomorph q = toCylinder q := rfl

theorem fiberAbs_eq_abs_toCylinder (q : NormalLineBundle 1) : fiberAbs 1 q = |(toCylinder q).2| := by
  obtain ⟨t, -, h, rfl⟩ := exists_mk_eq 1 q
  rfl

end NormalLineBundle

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {r : ℕ∞}

/-- **The orientable tube** `S¹ × (−ε, ε) ≃ₜ {d_S < ε}` around a simple closed unit geodesic of an
oriented complete surface: the unit normal is periodic (σ = 1) and the tube map
`(t mod 1, h) ↦ exp_{γ(ℓ t)}(h ν(ℓ t))` is a calibrated homeomorphism. -/
theorem exists_closedGeodesic_cylinderTube_of_orientation [CompleteSpace M]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hdim : Module.finrank ℝ E = 2) (p : TangentBundle I M) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hunit : g.inner p.proj p.snd p.snd = 1) (hper : g.geodesicFlow p ℓ = p)
    (hinj : InjOn (fun t => (g.geodesicFlow p t).proj) (Ico 0 ℓ)) {ν : ℝ → E}
    (hν : Continuous (fun t => (⟨(g.geodesicFlow p t).proj, ν t⟩ : TangentBundle I M)))
    (hνunit : ∀ t, g.inner (g.geodesicFlow p t).proj (ν t) (ν t) = 1)
    (hνperp : ∀ t, g.inner (g.geodesicFlow p t).proj (ν t) (g.geodesicFlow p t).snd = 0)
    (o : DifferentialGeometry.ManifoldOrientation I M 2) :
    (∀ t, ν (t + ℓ) = ν t) ∧ ∃ ε > 0, ∃ F : AddCircle (1 : ℝ) × ℝ → M,
      (∀ t h : ℝ, F ((t : AddCircle (1 : ℝ)), h) =
        g.expMap (⟨(g.geodesicFlow p (ℓ * t)).proj, h • ν (ℓ * t)⟩ : TangentBundle I M)) ∧
      (∀ q : AddCircle (1 : ℝ) × ℝ, |q.2| < ε →
        infDist (F q) (range fun t => (g.geodesicFlow p t).proj) = |q.2|) ∧
      ∃ e : ({q : AddCircle (1 : ℝ) × ℝ | |q.2| < ε} : Set (AddCircle (1 : ℝ) × ℝ)) ≃ₜ
          ({y | infDist y (range fun t => (g.geodesicFlow p t).proj) < ε} : Set M),
        ∀ q, (e q : M) = F q := by
  have hr1 : 1 ≤ r := le_trans (by norm_num) hr
  have hdom := g.geodesicFlowDomain_eq_univ hr hnorm
  obtain ⟨σ, hσ, ε, hε, F, hFexp, -, hcal, e, he⟩ :=
    exists_closedGeodesic_normalTube_homeomorph g hr hnorm hdim p hℓ hunit hper hinj hν hνunit
      hνperp
  have hσ1 := holonomy_eq_one_of_orientation g hr1 hdom hdim p hunit hper hν hνunit hνperp o hσ
  subst hσ1
  set φ := NormalLineBundle.toCylinderHomeomorph with hφ
  have hφabs : ∀ q, NormalLineBundle.fiberAbs 1 q = |(φ q).2| := fun q =>
    NormalLineBundle.fiberAbs_eq_abs_toCylinder q
  refine ⟨fun t => by simpa using hσ t, ε, hε, F ∘ φ.symm, fun t h => ?_, fun q hq => ?_,
    ((φ.subtype (p := fun q => q ∈ {q : NormalLineBundle 1 | NormalLineBundle.fiberAbs 1 q < ε})
      (q := fun c => c ∈ {c : AddCircle (1 : ℝ) × ℝ | |c.2| < ε})
      (fun q => by simp only [mem_ofPred_eq, hφabs])).symm.trans e), fun q => ?_⟩
  · have hq : φ.symm ((t : AddCircle (1 : ℝ)), h) = NormalLineBundle.mk 1 t h := by
      rw [Homeomorph.symm_apply_eq]
      rfl
    simp only [Function.comp_apply, hq]
    exact hFexp t h
  · simp only [Function.comp_apply]
    have hq' : NormalLineBundle.fiberAbs 1 (φ.symm q) < ε := by
      rw [hφabs, Homeomorph.apply_symm_apply]; exact hq
    rw [hcal _ hq', hφabs, Homeomorph.apply_symm_apply]
  · rw [Homeomorph.trans_apply, he]
    rfl

end DifferentialGeometry.Geometry.FiniteSoul
