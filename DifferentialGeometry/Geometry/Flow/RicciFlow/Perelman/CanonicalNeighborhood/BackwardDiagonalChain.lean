import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.DiagonalModelChain
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckLimitTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckParabolicTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalCapTransport

section
set_option autoImplicit false

noncomputable section

open Bundle Filter Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open Surgery.Topology
open KappaSolutions

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact

theorem exists_diagonal_tube_chain_of_backward_comparisons
    (F : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval)
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (q : ℕ → F.M)
    {P : PointedRiemannianManifold.{u, 0, 0} I3} {rho : ℕ → ℕ}
    (Phi : PointedRiemannianConvergenceMaps (backwardSliceSequence F tau htau q) P rho)
    (Sm : SolutionOn (I := I3) (M := P.M) ancientTimeInterval) (hSm : IsSolutionOn Sm)
    (d : Geometry.CylinderDiagonalQuotient ≃ₘ⟮IC, I3⟯ P.M)
    (hmetric : ∀ t : ℝ, ∀ ht : t ≤ 0,
      localPullMetric (Diffeomorph.pullbackMetricCross (Sm.base.metric t) d) cylinderDiagonalQuotientMap
        cylinderDiagonalQuotientMap_isLocalDiffeomorph =
          scalarOneShrinkingCylinderMetric t (ht.trans_lt (by norm_num)))
    (b : ℝ) (hsigma : ∀ i, 0 < tau (rho i) + b)
    (hcompare : ∀ K : Set P.M, IsCompact K → ∀ A : ℝ, 0 < A → ∀ order : ℕ,
      ∀ delta : ℝ, 0 < delta → ∀ᶠ i in atTop,
        Nonempty (MetricComparisonOn Sm.base.metric
          (fun s => scaleMetric (tau (rho i) + b)⁻¹ (inv_pos.mpr (hsigma i))
            (F.S.base.metric (-tau (rho i) + (tau (rho i) + b) * s)))
          (Phi.map i) K (Icc (-A) 0) order delta))
    {alpha : ℝ} (ha : 0 < alpha) (hsmall : 2 * alpha < 1 / 11)
    (p : Sphere 2) (L R : ℝ) (hL : (neckModelTolerance alpha)⁻¹ < L)
    (hLR : L < R) (hwidth : R - L < (2 * alpha)⁻¹) :
    ∃ nk : StrongNeck Sm (neckModelTolerance alpha) (d (cylinderDiagonalQuotientMap (p, L))) 0,
      nk.map.source = univ ×ˢ Ioi (-L) ∧
      (∀ z : Cylinder, nk.map z = d (cylinderDiagonalQuotientMap (z.1, z.2 + L))) ∧
      ∀ᶠ i in atTop, ∃ ns : StrongNeck F.S (2 * alpha)
          (Phi.map i (d (cylinderDiagonalQuotientMap (p, L)))) (-tau (rho i)),
        ns.map = nk.map.trans (Phi.partialDiffeomorph i) ∧
        univ ×ˢ Icc (0 : ℝ) (R - L) ⊆ ns.map.source ∧
        ∃ chain : OrderedNeckChain F.S (2 * alpha) (-tau (rho i))
            (Phi.map i '' (d '' (cylinderDiagonalQuotientMap '' (univ ×ˢ Icc L R)))),
          chain.count = 1 ∧ ∀ j, chain.centers j = Phi.map i (d (cylinderDiagonalQuotientMap (p, L))) ∧
            (chain.necks j).map = ns.map ∧ chain.lo j = 0 ∧ chain.hi j = R - L := by
  have hbpos : 0 < neckModelTolerance alpha := neckModelTolerance_pos ha
  have hbsmall : neckModelTolerance alpha < 1 / 11 :=
    (neckModelTolerance_le alpha).trans_lt (by linarith)
  obtain ⟨nk, _hcenter, hsource, hmap⟩ := exists_strongNeck_diagonal_projection_translate
    Sm d hmetric hbpos hbsmall p L hL.le
  have hLalpha : alpha⁻¹ < L :=
    (inv_anti₀ hbpos (neckModelTolerance_le alpha)).trans_lt hL
  let B : Set Cylinder := univ ×ˢ Icc (-alpha⁻¹) alpha⁻¹
  have hBc : IsCompact B := isCompact_univ.prod isCompact_Icc
  have hBsource : B ⊆ nk.map.source := by
    intro z hz
    rw [hsource]
    exact ⟨mem_univ _, lt_of_lt_of_le (neg_lt_neg hLalpha) hz.2.1⟩
  let K := nk.map '' B
  have hK : IsCompact K := hBc.image_of_continuousOn
    (nk.map.contMDiffOn_toFun.continuousOn.mono hBsource)
  let _ : LocallyCompactSpace P.M := ChartedSpace.locallyCompactSpace ThreeSpace P.M
  let _ : RegularSpace P.M := inferInstance
  obtain ⟨U, hUopen, hKU, _hUuniv, hUc⟩ :=
    exists_open_between_and_isCompact_closure hK isOpen_univ (subset_univ K)
  let O : TopologicalSpace.Opens P.M := ⟨U, hUopen⟩
  obtain ⟨N, hN⟩ := Phi.source_subset hUc
  have hcapture : ∀ᶠ i in atTop, (O : Set P.M) ⊆ (Phi.partialDiffeomorph i).source :=
    (eventually_ge_atTop N).mono fun i hi => subset_closure.trans (hN i hi)
  let htime (i : ℕ) : -tau (rho i) ∈ ancientTimeInterval.carrier := neg_nonpos.mpr (htau (rho i)).le
  let S i := parabolicSolution F.S (-tau (rho i)) (tau (rho i) + b)⁻¹
    (inv_pos.mpr (hsigma i)) (htime i)
  have hS i : IsSolutionOn (S i) := parabolicSolution_isSolutionOn F.S F.isSolution _ _ _ _
  have htimes : ∀ A : ℝ, 0 < A → ∀ᶠ i in atTop,
      Icc (-A) 0 ⊆ (parabolicInterval ancientTimeInterval (-tau (rho i))
        (tau (rho i) + b)⁻¹ (htime i)).carrier ∧
      Ioo (-A) 0 ⊆ (parabolicInterval ancientTimeInterval (-tau (rho i))
        (tau (rho i) + b)⁻¹ (htime i)).regular := by
    intro A _hA
    refine Eventually.of_forall fun i => ⟨?_, ?_⟩
    · intro s hs
      exact parabolicTime_nonpos (neg_nonpos.mpr (htau (rho i)).le) (inv_pos.mpr (hsigma i)) hs.2
    · intro s hs
      exact parabolicTime_neg (neg_nonpos.mpr (htau (rho i)).le) (inv_pos.mpr (hsigma i)) hs.2
  have hcmp : ∀ A : ℝ, 0 < A → ∀ order : ℕ, ∀ delta : ℝ, 0 < delta → ∀ᶠ i in atTop,
      Nonempty (MetricComparisonOn Sm.base.metric (S i).base.metric
        (Phi.partialDiffeomorph i) O (Icc (-A) 0) order delta) := by
    intro A hA order delta hdelta
    filter_upwards [hcompare (closure U) hUc A hA order delta hdelta] with i hi
    obtain ⟨C⟩ := hi
    have heq : (S i).base.metric = fun s => scaleMetric (tau (rho i) + b)⁻¹
        (inv_pos.mpr (hsigma i)) (F.S.base.metric (-tau (rho i) + (tau (rho i) + b) * s)) := by
      funext s
      change scaleMetric (tau (rho i) + b)⁻¹ (inv_pos.mpr (hsigma i))
        (F.S.base.metric (parabolicTime (-tau (rho i)) (tau (rho i) + b)⁻¹ s)) = _
      rw [parabolicTime, div_inv_eq_mul, mul_comm s]
    rw [heq]
    exact ⟨C.mono subset_closure le_rfl le_rfl⟩
  have houter : ∀ z ∈ univ ×ˢ Ioo (-alpha⁻¹) alpha⁻¹, nk.map z ∈ K :=
    fun z hz => ⟨z, ⟨hz.1, hz.2.1.le, hz.2.2.le⟩, rfl⟩
  refine ⟨nk, hsource, hmap, ?_⟩
  filter_upwards [nk.eventually_transport_of_comparisons hSm ha hsmall O hUc hK hKU
    houter S hS (fun i => Phi.partialDiffeomorph i) hcapture htimes hcmp] with i hi
  obtain ⟨ns, hns⟩ := hi
  have hex : ∃ ns' : StrongNeck F.S (2 * alpha)
      (Phi.map i (d (cylinderDiagonalQuotientMap (p, L)))) (-tau (rho i)), ns'.map = ns.map := by
    have hh : ∃ nt : StrongNeck F.S (2 * alpha)
        (Phi.map i (d (cylinderDiagonalQuotientMap (p, L))))
        (parabolicTime (-tau (rho i)) (tau (rho i) + b)⁻¹ 0), nt.map = ns.map :=
      ⟨ns.ofParabolic (-tau (rho i)) (tau (rho i) + b)⁻¹
        (inv_pos.mpr (hsigma i)) (htime i) 0, rfl⟩
    have ht0 : parabolicTime (-tau (rho i)) (tau (rho i) + b)⁻¹ 0 = -tau (rho i) := by
      simp only [parabolicTime, zero_div, add_zero]
    exact Eq.mp (congrArg (fun t : ℝ => ∃ nt : StrongNeck F.S (2 * alpha)
      (Phi.map i (d (cylinderDiagonalQuotientMap (p, L)))) t, nt.map = ns.map) ht0) hh
  obtain ⟨ns', hmapNative⟩ := hex
  have htrans : partialDiffeomorphTransMixed nk.map (Phi.partialDiffeomorph i) =
      nk.map.trans (Phi.partialDiffeomorph i) := rfl
  have hmap' : ns'.map = nk.map.trans (Phi.partialDiffeomorph i) :=
    hmapNative.trans (hns.trans htrans)
  have hinside : univ ×ˢ Icc (0 : ℝ) (R - L) ⊆ ns'.map.source := by
    intro z hz
    exact ns'.domain ⟨hz.1, (neg_neg_of_pos (inv_pos.mpr (by positivity : 0 < 2 * alpha))).trans_le hz.2.1,
      hz.2.2.trans_lt hwidth⟩
  refine ⟨ns', hmap', hinside, ?_⟩
  have himage : ns'.map '' (univ ×ˢ Icc (0 : ℝ) (R - L)) =
      Phi.map i '' (d '' (cylinderDiagonalQuotientMap '' (univ ×ˢ Icc L R))) := by
    rw [hmap', partialDiffeomorph_image_trans]
    congr 1
    ext y
    constructor
    · rintro ⟨⟨z, s⟩, ⟨_, hs⟩, rfl⟩
      exact ⟨cylinderDiagonalQuotientMap (z, s + L),
        ⟨(z, s + L), ⟨mem_univ _, by constructor <;> linarith [hs.1, hs.2]⟩, rfl⟩,
        (hmap (z, s)).symm⟩
    · rintro ⟨x, ⟨⟨z, s⟩, ⟨_, hs⟩, rfl⟩, rfl⟩
      exact ⟨(z, s - L), ⟨mem_univ _, by constructor <;> linarith [hs.1, hs.2]⟩,
        by rw [hmap, sub_add_cancel]⟩
  rw [← himage]
  exact ⟨OrderedNeckChain.singleInterval ns' (sub_pos.mpr hLR)
    (neg_neg_of_pos (inv_pos.mpr (by positivity : 0 < 2 * alpha))) hwidth,
    rfl, fun _ => ⟨rfl, rfl, rfl, rfl⟩⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

end
