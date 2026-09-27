import DifferentialGeometry.Geometry.Comparison.ConvexTangentCone

set_option autoImplicit false
noncomputable section

open Bundle Filter Manifold Set
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.HopfRinow

namespace DifferentialGeometry.Geometry.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [ConnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)]

theorem intrinsicGeodesic_mem_maxSliceLocus_Ioc
    {g : SmoothRiemannianMetric I M} (hEnorm : IsMetricNorm (I := I) g)
    {C : Set M} (hC : IsTotallyConvex (I := I) g C)
    {p : M} (v : TangentSpace I p) {a b : ℝ} (hab : a ≤ b)
    (hmap : MapsTo (intrinsicGeodesic (I := I) g hEnorm p v) (Icc a b) C)
    (hb : intrinsicGeodesic (I := I) g hEnorm p v b ∈ maxSliceLocus I C) :
    MapsTo (intrinsicGeodesic (I := I) g hEnorm p v) (Ioc a b) (maxSliceLocus I C) := by
  rcases hab.eq_or_lt with rfl | hab
  · intro t ht
    exact (not_lt_of_ge ht.2 ht.1).elim
  let γ := intrinsicGeodesic (I := I) g hEnorm p v
  have hγ : Continuous γ := intrinsicGeodesic_continuous (I := I) g hEnorm p v
  let A : Set (Ioc a b) := {t | γ t ∈ maxSliceLocus I C}
  let γC : Ioc a b → C := fun t => ⟨γ t, hmap ⟨t.property.1.le, t.property.2⟩⟩
  have hγC : Continuous γC := (hγ.comp continuous_subtype_val).subtype_mk _
  have hAopen : IsOpen A := (isOpen_maxSliceLocus hEnorm hC).preimage hγC
  have hAcomp : IsOpen Aᶜ := by
    rw [isOpen_iff_mem_nhds]
    intro s hs
    change γ (s : ℝ) ∉ maxSliceLocus I C at hs
    have hsne : (s : ℝ) ≠ b := by
      intro hsb
      apply hs
      rw [hsb]
      exact hb
    have hsIoo : (s : ℝ) ∈ Ioo a b := ⟨s.property.1, lt_of_le_of_ne s.property.2 hsne⟩
    let r : Ioc a b → ℝ := fun u => 2 * (s : ℝ) - (u : ℝ)
    have hr : Continuous r := continuous_const.sub continuous_subtype_val
    have hrs : r s = (s : ℝ) := by dsimp only [r]; ring
    have hrmem : ∀ᶠ u in 𝓝 s, r u ∈ Ioo a b :=
      hr.continuousAt (isOpen_Ioo.mem_nhds (by rwa [hrs]))
    let B := standardDiagonalInverseBranch (I := I) g hEnorm (γ s)
    let pair : Ioc a b → M × M := fun u => (γ u, γ (r u))
    have hpairlim : Tendsto pair (𝓝 s) (𝓝 (γ s, γ s)) := by
      have hc : Continuous pair := (hγ.comp continuous_subtype_val).prodMk (hγ.comp hr)
      simpa only [ContinuousAt, pair, hrs] using (hc.continuousAt (x := s))
    have hpair := hpairlim.eventually (maxSliceLocus_pair hEnorm hC B)
    let times : Ioc a b → ℝ × ℝ := fun u => ((u : ℝ), r u)
    have htimes : Tendsto times (𝓝 s) (𝓝 ((s : ℝ), (s : ℝ))) := by
      have hc : Continuous times := continuous_subtype_val.prodMk hr
      simpa only [ContinuousAt, times, hrs] using (hc.continuousAt (x := s))
    have hchord := htimes.eventually (minJoin_intrinsicGeodesic_near v (s : ℝ) B)
    filter_upwards [hrmem, hpair, hchord] with u hru hpair hchord
    intro hu
    change γ (u : ℝ) ∈ maxSliceLocus I C at hu
    have hmid := hpair hu (hmap ⟨hru.1.le, hru.2.le⟩) (1 / 2 : ℝ)
      (by constructor <;> norm_num)
    rw [hchord (1 / 2 : ℝ)] at hmid
    have htime : (1 / 2 : ℝ) * ((u : ℝ) - r u) + r u = (s : ℝ) := by
      dsimp only [r]
      ring
    rw [htime] at hmid
    exact hs hmid
  have hAclosed : IsClosed A := isOpen_compl_iff.1 hAcomp
  let : PreconnectedSpace (Ioc a b) := Subtype.preconnectedSpace isPreconnected_Ioc
  have hAne : A.Nonempty := ⟨⟨b, ⟨hab, le_rfl⟩⟩, hb⟩
  have hAuniv : A = univ := IsClopen.eq_univ ⟨hAclosed, hAopen⟩ hAne
  intro t ht
  have hmem : (⟨t, ht⟩ : Ioc a b) ∈ A := by rw [hAuniv]; exact mem_univ _
  exact hmem

theorem isInnerDirection_of_intrinsicGeodesic_endpoint
    {g : SmoothRiemannianMetric I M} (hEnorm : IsMetricNorm (I := I) g)
    {C : Set M} (hC : IsTotallyConvex (I := I) g C) {p : M} (hp : p ∈ C)
    {v : TangentSpace I p} {l : ℝ} (hl : 0 < l)
    (hend : intrinsicGeodesic (I := I) g hEnorm p v l ∈ maxSliceLocus I C) :
    IsInnerDirection (I := I) g hEnorm C p v := by
  have hmap : MapsTo (intrinsicGeodesic (I := I) g hEnorm p v) (Icc 0 l) C :=
    hC hl.le ((intrinsicGeodesic_isGeodesic (I := I) g hEnorm p v).isGeodesicOn _)
      (intrinsicGeodesic_continuous (I := I) g hEnorm p v).continuousOn
      (by simpa only [intrinsicGeodesic_zero] using hp) (maxSliceLocus_subset hend)
  have hprop := intrinsicGeodesic_mem_maxSliceLocus_Ioc hEnorm hC v hl.le hmap hend
  rw [isInnerDirection_iff]
  filter_upwards [Ioo_mem_nhdsGT hl] with t ht
  exact hprop ⟨ht.1, ht.2.le⟩

end DifferentialGeometry.Geometry.Topology
