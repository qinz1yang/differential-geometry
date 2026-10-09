import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.BackwardCapTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.DiagonalCanonicalWitness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.BackwardDiagonalChain
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalCapTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalToleranceMonotone

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
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

theorem exists_diagonal_basepoint_cap_transport
    (F : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval) {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F)
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (q : ℕ → F.M)
    {P : PointedRiemannianManifold.{u, 0, 0} I3} {rho : ℕ → ℕ}
    (Phi : PointedRiemannianConvergenceMaps (backwardSliceSequence F tau htau q) P rho)
    (Sm : SolutionOn (I := I3) (M := P.M) ancientTimeInterval) (hSm : IsSolutionOn Sm)
    [PreconnectedSpace P.M] (hcomplete : RiemannianMetricComplete (Sm.base.metric 0))
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
    {alpha : ℝ} (ha : 0 < alpha) (hsmall : 2 * alpha < 1 / 11) :
    ∃ p : Cylinder, d (cylinderDiagonalQuotientMap p) = P.basepoint ∧
      ∃ L r C : ℝ, (neckModelTolerance alpha)⁻¹ < L ∧ |p.2| < L ∧ 1 ≤ r ∧ 1 ≤ C ∧
        let U := d '' (cylinderDiagonalQuotientMap '' (univ ×ˢ Icc (-(L + 1)) (L + 1)))
        ∃ cap : LocalCap Sm (neckModelTolerance alpha) (d (cylinderDiagonalQuotientMap p)) 0 U,
          cap.core.carrier = d '' (cylinderDiagonalQuotientMap '' (univ ×ˢ Icc (-L) L)) ∧
          cap.tube = d '' (cylinderDiagonalQuotientMap '' (univ ×ˢ Icc L (L + 1))) ∧
          (∀ z : Cylinder, cap.tubeMap z = d (cylinderDiagonalQuotientMap (z.1, L + z.2))) ∧
          cap.chain.count = 1 ∧
          (∀ j, cap.chain.centers j = d (cylinderDiagonalQuotientMap (p.1, L)) ∧
            (∀ z : Cylinder, (cap.chain.necks j).map z = d (cylinderDiagonalQuotientMap (z.1, z.2 + L))) ∧
            cap.chain.lo j = 0 ∧ cap.chain.hi j = 1) ∧
          (∀ y ∈ cap.tube, 40000 < metricDistance (Sm.base.metric 0) P.basepoint y) ∧
          (∃ K : CanonicalWitness Sm (neckModelTolerance alpha) r C (d (cylinderDiagonalQuotientMap p)) 0,
            K.domain.carrier = U ∧ K.radius = r ∧
            ∃ cap' depth, K.alternative = CanonicalAlternative.cap cap' depth ∧ HEq cap' cap) ∧
          Tendsto (fun i => (tau (rho i) + b) * F.S.scalar (-tau (rho i)) (q (rho i))) atTop (𝓝 1) ∧
          ∃ B : Set P.M, IsCompact B ∧ U ⊆ interior B ∧
            ∀ᶠ i in atTop, B ⊆ Phi.source i ∧
              ∃ cap' : LocalCap F.S (2 * alpha) (q (rho i)) (-tau (rho i)) (Phi.map i '' U),
                cap'.core.carrier = Phi.map i '' cap.core.carrier ∧
                cap'.tube = Phi.map i '' cap.tube ∧
                cap'.tubeMap = cap.tubeMap.trans (Phi.partialDiffeomorph i) ∧
                cap'.chain.count = 1 ∧
                (∀ j, cap'.chain.centers j = Phi.map i (d (cylinderDiagonalQuotientMap (p.1, L))) ∧
                  (∀ z : Cylinder, (cap'.chain.necks j).map z = Phi.map i (d (cylinderDiagonalQuotientMap (z.1, z.2 + L)))) ∧
                  cap'.chain.lo j = 0 ∧ cap'.chain.hi j = 1) ∧
                (∀ y ∈ cap'.tube, 10000 / Real.sqrt (F.S.scalar (-tau (rho i)) (q (rho i))) ≤
                  metricDistance (F.S.base.metric (-tau (rho i))) (q (rho i)) y) := by
  obtain ⟨p, hp⟩ := cylinderDiagonalQuotientMap_surjective (d.symm P.basepoint)
  have hpbase : d (cylinderDiagonalQuotientMap p) = P.basepoint :=
    (congrArg d hp).trans (d.apply_symm_apply P.basepoint)
  have hbpos : 0 < neckModelTolerance alpha := neckModelTolerance_pos ha
  have hbsmall : neckModelTolerance alpha < 1 / 11 :=
    (neckModelTolerance_le alpha).trans_lt (by linarith)
  obtain ⟨L, r, C, hL, hpL, hr, hC, cap, hcore, htube, hmap, hmodelCount, hmodelChain, hdepth, hK⟩ :=
    exists_canonicalWitness_diagonal_shrinking_model Sm d hmetric hbpos hbsmall p 40000
  have hscalar : Sm.scalar 0 P.basepoint = 1 := scalar_eq_one_of_diagonal_shrinking_model Sm d hmetric _
  have hcompareOne := fun K hK order delta hdelta => hcompare K hK 1 zero_lt_one order delta hdelta
  have hlim := tendsto_original_base_scalar_of_backward_comparisons F tau htau q Phi Sm
    hscalar b hsigma hcompareOne
  have hfar : ∀ y ∈ cap.tube, 40000 < metricDistance (Sm.base.metric 0) P.basepoint y := by
    intro y hy
    have hh := hdepth y hy
    simpa only [max_eq_right (by norm_num : (10000 : ℝ) ≤ 40000), hpbase] using hh
  have hdeep := eventually_original_image_depth_of_backward_comparisons F hF tau htau q Phi
    Sm hcomplete hscalar b hsigma hcompareOne cap.isCompact_tube (fun y hy => (hfar y hy).le)
  have hwidth : (L + 1) - L < (2 * alpha)⁻¹ := by
    have hlt : 2 * alpha < 1 := hsmall.trans (by norm_num)
    have hi : 1 < (2 * alpha)⁻¹ := (one_lt_inv₀ (by positivity : 0 < 2 * alpha)).mpr hlt
    linarith
  obtain ⟨_nk, _hsource, _hnkmap, hsourceChains⟩ := exists_diagonal_tube_chain_of_backward_comparisons
    F tau htau q Phi Sm hSm d hmetric b hsigma hcompare ha hsmall p.1 L (L + 1) hL
      (by linarith) hwidth
  let _ : LocallyCompactSpace P.M := ChartedSpace.locallyCompactSpace ThreeSpace P.M
  let _ : RegularSpace P.M := inferInstance
  obtain ⟨O, hOo, hUO, _hOuniv, hOc⟩ := exists_open_between_and_isCompact_closure
    cap.isCompact_carrier isOpen_univ (subset_univ _)
  have hbuffer : d '' (cylinderDiagonalQuotientMap '' (univ ×ˢ Icc (-(L + 1)) (L + 1))) ⊆
      interior (closure O) := hUO.trans (by
    calc
      O = interior O := hOo.interior_eq.symm
      _ ⊆ interior (closure O) := interior_mono subset_closure)
  obtain ⟨N, hN⟩ := Phi.source_subset hOc
  refine ⟨p, hpbase, L, r, C, hL, hpL, hr, hC, cap, hcore, htube, hmap, hmodelCount, hmodelChain, hfar, hK, hlim,
    closure O, hOc, hbuffer, ?_⟩
  filter_upwards [eventually_ge_atTop N, hsourceChains, hdeep] with i hi hci hdi
  obtain ⟨ns, hns, _hinside, chain, hcount, hchain⟩ := hci
  have hsrc : d '' (cylinderDiagonalQuotientMap '' (univ ×ˢ Icc (-(L + 1)) (L + 1))) ⊆
      (Phi.partialDiffeomorph i).source := (hUO.trans subset_closure).trans (hN i hi)
  have htol : neckModelTolerance alpha ≤ 2 * alpha := (neckModelTolerance_le alpha).trans (by linarith)
  let cap0 := cap.monoEps htol hsmall
  have hcExists : ∃ hc : OrderedNeckChain F.S (2 * alpha) (-tau (rho i))
      ((Phi.partialDiffeomorph i) '' cap0.tube), hc.count = 1 ∧
      ∀ j, hc.centers j = Phi.map i (d (cylinderDiagonalQuotientMap (p.1, L))) ∧
        (∀ z : Cylinder, (hc.necks j).map z = Phi.map i (d (cylinderDiagonalQuotientMap (z.1, z.2 + L)))) ∧
        hc.lo j = 0 ∧ hc.hi j = 1 := by
    let property (V : Set F.M) : Prop := ∃ hc : OrderedNeckChain F.S (2 * alpha) (-tau (rho i)) V,
      hc.count = 1 ∧ ∀ j, hc.centers j = Phi.map i (d (cylinderDiagonalQuotientMap (p.1, L))) ∧
        (∀ z : Cylinder, (hc.necks j).map z = Phi.map i (d (cylinderDiagonalQuotientMap (z.1, z.2 + L)))) ∧
        hc.lo j = 0 ∧ hc.hi j = 1
    have hh : property (Phi.map i '' (d '' (cylinderDiagonalQuotientMap '' (univ ×ˢ Icc L (L + 1))))) := by
      refine ⟨chain, hcount, ?_⟩
      intro j
      obtain ⟨hcenter, hneckmap, hlo, hhi⟩ := hchain j
      refine ⟨hcenter, ?_, hlo, by simpa only [add_sub_cancel_left] using hhi⟩
      intro z
      calc
        (chain.necks j).map z = ns.map z := congrArg (fun e => e z) hneckmap
        _ = Phi.map i (_nk.map z) := by rw [hns]; rfl
        _ = Phi.map i (d (cylinderDiagonalQuotientMap (z.1, z.2 + L))) := congrArg (Phi.map i) (_hnkmap z)
    have hset : Phi.map i '' (d '' (cylinderDiagonalQuotientMap '' (univ ×ˢ Icc L (L + 1)))) =
        (Phi.partialDiffeomorph i) '' cap0.tube := congrArg (fun V : Set P.M => Phi.map i '' V) htube.symm
    exact Eq.mp (congrArg property hset) hh
  obtain ⟨hc, hhc, hhcfields⟩ := hcExists
  let cap' := cap0.map (Phi.partialDiffeomorph i) hsrc hc
  have hbase : (Phi.partialDiffeomorph i) (d (cylinderDiagonalQuotientMap p)) = q (rho i) := by
    rw [hpbase]
    exact Phi.basepoint_map i
  refine ⟨hN i hi, ?_⟩
  have hout : ∃ cap' : LocalCap F.S (2 * alpha)
      ((Phi.partialDiffeomorph i) (d (cylinderDiagonalQuotientMap p))) (-tau (rho i))
      (Phi.map i '' (d '' (cylinderDiagonalQuotientMap '' (univ ×ˢ Icc (-(L + 1)) (L + 1))))),
      cap'.core.carrier = Phi.map i '' cap.core.carrier ∧ cap'.tube = Phi.map i '' cap.tube ∧
      cap'.tubeMap = cap.tubeMap.trans (Phi.partialDiffeomorph i) ∧ cap'.chain.count = 1 ∧
      (∀ j, cap'.chain.centers j = Phi.map i (d (cylinderDiagonalQuotientMap (p.1, L))) ∧
        (∀ z : Cylinder, (cap'.chain.necks j).map z = Phi.map i (d (cylinderDiagonalQuotientMap (z.1, z.2 + L)))) ∧
        cap'.chain.lo j = 0 ∧ cap'.chain.hi j = 1) ∧
      (∀ y ∈ cap'.tube, 10000 / Real.sqrt (F.S.scalar (-tau (rho i)) (q (rho i))) ≤
        metricDistance (F.S.base.metric (-tau (rho i))) (q (rho i)) y) := by
    exact ⟨cap', rfl, rfl, rfl, hhc, hhcfields, hdi⟩
  rwa [hbase] at hout

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

end

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
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

theorem exists_diagonal_basepoint_canonical_transport
    (F : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval) {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F)
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (q : ℕ → F.M)
    {P : PointedRiemannianManifold.{u, 0, 0} I3} {rho : ℕ → ℕ}
    (Phi : PointedRiemannianConvergenceMaps (backwardSliceSequence F tau htau q) P rho)
    (Sm : SolutionOn (I := I3) (M := P.M) ancientTimeInterval) (hSm : IsSolutionOn Sm)
    [PreconnectedSpace P.M] (hcomplete : RiemannianMetricComplete (Sm.base.metric 0))
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
    {alpha : ℝ} (ha : 0 < alpha) (hsmall : 2 * alpha < 1 / 11) :
    ∃ p : Cylinder, d (cylinderDiagonalQuotientMap p) = P.basepoint ∧
      ∃ L r C rsource Csource : ℝ, (neckModelTolerance alpha)⁻¹ < L ∧ |p.2| < L ∧ 1 ≤ r ∧ 1 ≤ C ∧ 1 < rsource ∧ rsource ≤ max r 2 ∧ 1 ≤ Csource ∧
        let U := d '' (cylinderDiagonalQuotientMap '' (univ ×ˢ Icc (-(L + 1)) (L + 1)))
        ∃ cap : LocalCap Sm (neckModelTolerance alpha) (d (cylinderDiagonalQuotientMap p)) 0 U,
          cap.core.carrier = d '' (cylinderDiagonalQuotientMap '' (univ ×ˢ Icc (-L) L)) ∧
          cap.tube = d '' (cylinderDiagonalQuotientMap '' (univ ×ˢ Icc L (L + 1))) ∧
          (∀ z : Cylinder, cap.tubeMap z = d (cylinderDiagonalQuotientMap (z.1, L + z.2))) ∧
          cap.chain.count = 1 ∧
          (∀ j, cap.chain.centers j = d (cylinderDiagonalQuotientMap (p.1, L)) ∧
            (∀ z : Cylinder, (cap.chain.necks j).map z = d (cylinderDiagonalQuotientMap (z.1, z.2 + L))) ∧
            cap.chain.lo j = 0 ∧ cap.chain.hi j = 1) ∧
          (∀ y ∈ cap.tube, 40000 < metricDistance (Sm.base.metric 0) P.basepoint y) ∧
          (∃ K : CanonicalWitness Sm (neckModelTolerance alpha) r C (d (cylinderDiagonalQuotientMap p)) 0,
            K.domain.carrier = U ∧ K.radius = r ∧
            ∃ cap' depth, K.alternative = CanonicalAlternative.cap cap' depth ∧ HEq cap' cap) ∧
          Tendsto (fun i => (tau (rho i) + b) * F.S.scalar (-tau (rho i)) (q (rho i))) atTop (𝓝 1) ∧
          ∃ B : Set P.M, IsCompact B ∧ U ⊆ interior B ∧
            ∀ᶠ i in atTop, B ⊆ Phi.source i ∧
              ∃ cap' : LocalCap F.S (2 * alpha) (q (rho i)) (-tau (rho i)) (Phi.map i '' U),
                cap'.core.carrier = Phi.map i '' cap.core.carrier ∧
                cap'.tube = Phi.map i '' cap.tube ∧
                cap'.tubeMap = cap.tubeMap.trans (Phi.partialDiffeomorph i) ∧
                cap'.chain.count = 1 ∧
                (∀ j, cap'.chain.centers j = Phi.map i (d (cylinderDiagonalQuotientMap (p.1, L))) ∧
                  (∀ z : Cylinder, (cap'.chain.necks j).map z = Phi.map i (d (cylinderDiagonalQuotientMap (z.1, z.2 + L)))) ∧
                  cap'.chain.lo j = 0 ∧ cap'.chain.hi j = 1) ∧
                (∀ y ∈ cap'.tube, 10000 / Real.sqrt (F.S.scalar (-tau (rho i)) (q (rho i))) ≤
                  metricDistance (F.S.base.metric (-tau (rho i))) (q (rho i)) y) ∧
                ∃ Ks : CanonicalWitness F.S (2 * alpha) (2 * max r 2) Csource (q (rho i)) (-tau (rho i)),
                  Ks.domain.carrier = Phi.map i '' U ∧ Ks.radius = Real.sqrt (tau (rho i) + b) * rsource ∧
                  ∃ cap'' depth, Ks.alternative = CanonicalAlternative.cap cap'' depth ∧ HEq cap'' cap' := by
  obtain ⟨p, hpbase, L, r, C, hL, hpL, hr, hC, cap, hcore, htube, hmap, hcount, hchain,
      hfar, hK, hlim, B, hBc, hUB, hcaps⟩ := exists_diagonal_basepoint_cap_transport
    F hF tau htau q Phi Sm hSm hcomplete d hmetric b hsigma hcompare ha hsmall
  have hKbase : ∃ Km : CanonicalWitness Sm (neckModelTolerance alpha) r C P.basepoint 0,
      Km.domain.carrier = d '' (cylinderDiagonalQuotientMap '' (univ ×ˢ Icc (-(L + 1)) (L + 1))) ∧
      Km.alternative.requiresVolume := by
    rw [← hpbase]
    obtain ⟨Km, hKm, _hKradius, capm, depthm, halt, _hcap⟩ := hK
    refine ⟨Km, hKm, ?_⟩
    rw [halt]
    trivial
  obtain ⟨Km, hKm, hKmVol⟩ := hKbase
  have hscalar : Sm.scalar 0 P.basepoint = 1 := scalar_eq_one_of_diagonal_shrinking_model Sm d hmetric _
  have hcompareOne := fun A hA order delta hdelta => hcompare A hA 1 zero_lt_one order delta hdelta
  obtain ⟨rsource, Csource, hrs, hrsC, hCs, hKs⟩ :=
    Km.exists_eventually_image_cap_witness_of_backward_comparisons F hF tau htau q Phi Sm
      hcomplete hscalar b hsigma hcompareOne hKmVol
  refine ⟨p, hpbase, L, r, C, rsource, Csource, hL, hpL, hr, hC, hrs, hrsC, hCs,
    cap, hcore, htube, hmap, hcount, hchain, hfar, hK, hlim, B, hBc, hUB, ?_⟩
  filter_upwards [hcaps, hKs] with i hci hki
  obtain ⟨hBi, cap', hcore', htube', hmap', hcount', hchain', hdepth'⟩ := hci
  let property (V : Set P.M) : Prop :=
    ∀ cap' : LocalCap F.S (2 * alpha) (q (rho i)) (-tau (rho i)) (Phi.map i '' V),
      (∀ y ∈ cap'.tube, 10000 / Real.sqrt (F.S.scalar (-tau (rho i)) (q (rho i))) ≤
        metricDistance (F.S.base.metric (-tau (rho i))) (q (rho i)) y) →
      ∃ Ks : CanonicalWitness F.S (2 * alpha) (2 * max r 2) Csource (q (rho i)) (-tau (rho i)),
        Ks.domain.carrier = Phi.map i '' V ∧ Ks.radius = Real.sqrt (tau (rho i) + b) * rsource ∧
        ∃ cap'' depth, Ks.alternative = CanonicalAlternative.cap cap'' depth ∧ HEq cap'' cap'
  have hki' : property (d '' (cylinderDiagonalQuotientMap '' (univ ×ˢ Icc (-(L + 1)) (L + 1)))) :=
    Eq.mp (congrArg property hKm) (hki (2 * alpha))
  exact ⟨hBi, cap', hcore', htube', hmap', hcount', hchain', hdepth', hki' cap' hdepth'⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

end
