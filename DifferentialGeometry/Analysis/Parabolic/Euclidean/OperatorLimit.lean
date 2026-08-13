import DifferentialGeometry.Analysis.Parabolic.Euclidean.LowerOrder
import DifferentialGeometry.Analysis.Schauder.ParabolicJetLimit

noncomputable section

open Filter Set
open scoped Topology

namespace DifferentialGeometry.Analysis.Parabolic.Euclidean

open DifferentialGeometry.Analysis.Schauder

private abbrev Euc (n : Type*) := EuclideanSpace Real n

variable {n F P : Type*} [Fintype n]
  [NormedAddCommGroup F] [NormedSpace Real F]

def parabolicNondivergenceJetOperator
    (a : n → n → P → Real) (b : n → P → Real) (c : P → Real)
    (u dtimeU : P → F) (du : P → Euc n →L[Real] F)
    (d2u : P → Euc n →L[Real] Euc n →L[Real] F) : P → F := by
  classical
  exact fun p ↦ dtimeU p - matrixLap (fun i j ↦ a i j p) (d2u p) -
    ((∑ i, b i p • du p (EuclideanSpace.basisFun n Real i)) + c p • u p)

theorem parabolicNondivergenceOperator_eq_jetOperator
    {Q : Set (ParabolicPoint (Euc n))} (hQ : IsOpen Q)
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (b : n → ParabolicPoint (Euc n) → Real)
    (c : ParabolicPoint (Euc n) → Real)
    (u dtimeU : ParabolicPoint (Euc n) → F)
    (du : ParabolicPoint (Euc n) → Euc n →L[Real] F)
    (d2u : ParabolicPoint (Euc n) → Euc n →L[Real] Euc n →L[Real] F)
    (hrealize : ParabolicJetRealizesOn Q u dtimeU du d2u)
    {p : ParabolicPoint (Euc n)} (hp : p ∈ Q) :
    parabolicNondivergenceOperator a b c
        (fun t x ↦ u (parabolicPoint t x)) p =
      parabolicNondivergenceJetOperator a b c u dtimeU du d2u p := by
  classical
  have htime : parabolicTimeDerivative
      (fun t x ↦ u (parabolicPoint t x)) p = dtimeU p := by
    unfold parabolicTimeDerivative
    rw [(hrealize.hasDerivAt_time hp).hasFDerivAt.fderiv]
    simp only [ContinuousLinearMap.toSpanSingleton_apply, one_smul]
  have hfirst : continuousMultilinearCurryFin1 Real (Euc n) F
      (parabolicSpatialJet 1 (fun t x ↦ u (parabolicPoint t x)) p) = du p := by
    ext v
    simp only [parabolicSpatialJet, continuousMultilinearCurryFin1_apply,
      iteratedFDeriv_one_apply]
    rw [(hrealize.hasFDerivAt_space hp).fderiv]
    rfl
  let spaceSlice : Euc n → ParabolicPoint (Euc n) :=
    fun x ↦ parabolicPoint p.time x
  let spaceDomain : Set (Euc n) := spaceSlice ⁻¹' Q
  have hspaceSlice : Continuous spaceSlice := by
    simpa only [spaceSlice, parabolicPoint] using
      (continuous_const : Continuous
        (fun _ : Euc n ↦ Metric.Snowflaking.toSnowflaking p.time)).prodMk continuous_id
  have hspaceDomain : IsOpen spaceDomain := hQ.preimage hspaceSlice
  have hpSpace : p.space ∈ spaceDomain := by
    change parabolicPoint p.time p.space ∈ Q
    simpa only [parabolicPoint_time_space] using hp
  have hgradient : fderiv Real (fun x ↦ u (spaceSlice x)) =ᶠ[nhds p.space]
      fun x ↦ du (spaceSlice x) := by
    filter_upwards [hspaceDomain.mem_nhds hpSpace] with x hx
    exact (hrealize.hasFDerivAt_space hx).fderiv
  have hsecond : hessianCurryEquiv (Euc n) F
      (parabolicSpatialJet 2 (fun t x ↦ u (parabolicPoint t x)) p) = d2u p := by
    ext v w
    simp only [hessianCurryEquiv, LinearIsometryEquiv.trans_apply,
      continuousMultilinearCurryFin1_apply,
      continuousMultilinearCurryRightEquiv_apply', parabolicSpatialJet,
      iteratedFDeriv_two_apply]
    rw [show (fun x ↦ u (parabolicPoint p.time x)) = fun x ↦ u (spaceSlice x) by
      rfl, hgradient.fderiv_eq, (hrealize.hasFDerivAt_gradient hp).fderiv]
    rfl
  unfold parabolicNondivergenceOperator parabolicVariableMatrixOperator
    parabolicVariableMatrixLap parabolicLowerOrderTerm parabolicDriftTerm
    parabolicGradientComponent parabolicPotentialTerm
    parabolicNondivergenceJetOperator
  simp only [Pi.sub_apply, Pi.add_apply, parabolicPoint_time_space]
  rw [htime, hfirst, hsecond]

theorem tendsto_parabolicNondivergenceJetOperator_apply
    {iota : Type*} {l : Filter iota}
    {aApprox : iota → n → n → P → Real}
    {bApprox : iota → n → P → Real} {cApprox : iota → P → Real}
    {uApprox dtimeUApprox : iota → P → F}
    {duApprox : iota → P → Euc n →L[Real] F}
    {d2uApprox : iota → P → Euc n →L[Real] Euc n →L[Real] F}
    {a : n → n → P → Real} {b : n → P → Real} {c : P → Real}
    {u dtimeU : P → F} {du : P → Euc n →L[Real] F}
    {d2u : P → Euc n →L[Real] Euc n →L[Real] F} {p : P}
    (ha : ∀ i j, Tendsto (fun k ↦ aApprox k i j p) l (nhds (a i j p)))
    (hb : ∀ i, Tendsto (fun k ↦ bApprox k i p) l (nhds (b i p)))
    (hc : Tendsto (fun k ↦ cApprox k p) l (nhds (c p)))
    (hu : Tendsto (fun k ↦ uApprox k p) l (nhds (u p)))
    (hdtimeU : Tendsto (fun k ↦ dtimeUApprox k p) l (nhds (dtimeU p)))
    (hdu : Tendsto (fun k ↦ duApprox k p) l (nhds (du p)))
    (hd2u : Tendsto (fun k ↦ d2uApprox k p) l (nhds (d2u p))) :
    Tendsto
      (fun k ↦ parabolicNondivergenceJetOperator (aApprox k) (bApprox k)
        (cApprox k) (uApprox k) (dtimeUApprox k) (duApprox k) (d2uApprox k) p)
      l (nhds (parabolicNondivergenceJetOperator a b c u dtimeU du d2u p)) := by
  have hlap : Tendsto
      (fun k ↦ matrixLap (fun i j ↦ aApprox k i j p) (d2uApprox k p)) l
      (nhds (matrixLap (fun i j ↦ a i j p) (d2u p))) := by
    classical
    unfold matrixLap
    refine tendsto_finset_sum Finset.univ fun i _ ↦
      tendsto_finset_sum Finset.univ fun j _ ↦ ?_
    have hi := Filter.Tendsto.comp
      ((ContinuousLinearMap.apply Real (Euc n →L[Real] F))
        (EuclideanSpace.basisFun n Real i)).continuous.continuousAt hd2u
    have hij := Filter.Tendsto.comp
      ((ContinuousLinearMap.apply Real F)
        (EuclideanSpace.basisFun n Real j)).continuous.continuousAt hi
    exact (ha i j).smul hij
  have hdrift : Tendsto
      (fun k ↦ ∑ i, bApprox k i p •
        duApprox k p (EuclideanSpace.basisFun n Real i)) l
      (nhds (∑ i, b i p • du p (EuclideanSpace.basisFun n Real i))) := by
    classical
    refine tendsto_finset_sum Finset.univ fun i _ ↦ ?_
    have hi := Filter.Tendsto.comp
      ((ContinuousLinearMap.apply Real F)
        (EuclideanSpace.basisFun n Real i)).continuous.continuousAt hdu
    exact (hb i).smul hi
  unfold parabolicNondivergenceJetOperator
  exact (hdtimeU.sub hlap).sub (hdrift.add (hc.smul hu))

theorem parabolicNondivergenceJetOperator_eq_of_tendsto
    {iota : Type*} {l : Filter iota} [NeBot l]
    {aApprox : iota → n → n → P → Real}
    {bApprox : iota → n → P → Real} {cApprox : iota → P → Real}
    {uApprox dtimeUApprox sourceApprox : iota → P → F}
    {duApprox : iota → P → Euc n →L[Real] F}
    {d2uApprox : iota → P → Euc n →L[Real] Euc n →L[Real] F}
    {a : n → n → P → Real} {b : n → P → Real} {c : P → Real}
    {u dtimeU source : P → F} {du : P → Euc n →L[Real] F}
    {d2u : P → Euc n →L[Real] Euc n →L[Real] F} {p : P}
    (ha : ∀ i j, Tendsto (fun k ↦ aApprox k i j p) l (nhds (a i j p)))
    (hb : ∀ i, Tendsto (fun k ↦ bApprox k i p) l (nhds (b i p)))
    (hc : Tendsto (fun k ↦ cApprox k p) l (nhds (c p)))
    (hu : Tendsto (fun k ↦ uApprox k p) l (nhds (u p)))
    (hdtimeU : Tendsto (fun k ↦ dtimeUApprox k p) l (nhds (dtimeU p)))
    (hdu : Tendsto (fun k ↦ duApprox k p) l (nhds (du p)))
    (hd2u : Tendsto (fun k ↦ d2uApprox k p) l (nhds (d2u p)))
    (hsource : Tendsto (fun k ↦ sourceApprox k p) l (nhds (source p)))
    (hequation : ∀ᶠ k in l,
      parabolicNondivergenceJetOperator (aApprox k) (bApprox k) (cApprox k)
        (uApprox k) (dtimeUApprox k) (duApprox k) (d2uApprox k) p =
          sourceApprox k p) :
    parabolicNondivergenceJetOperator a b c u dtimeU du d2u p = source p := by
  apply tendsto_nhds_unique
    (tendsto_parabolicNondivergenceJetOperator_apply
      ha hb hc hu hdtimeU hdu hd2u)
  exact hsource.congr' (hequation.mono fun _ h ↦ h.symm)

theorem parabolic_nondivergence_equation_on_of_tendsto_locally_uniformly_on
    {iota : Type*} {l : Filter iota} [NeBot l]
    {Q : Set (ParabolicPoint (Euc n))} (hQ : IsOpen Q)
    {aApprox : iota → n → n → ParabolicPoint (Euc n) → Real}
    {bApprox : iota → n → ParabolicPoint (Euc n) → Real}
    {cApprox : iota → ParabolicPoint (Euc n) → Real}
    {uApprox dtimeUApprox sourceApprox : iota → ParabolicPoint (Euc n) → F}
    {duApprox : iota → ParabolicPoint (Euc n) → Euc n →L[Real] F}
    {d2uApprox : iota → ParabolicPoint (Euc n) →
      Euc n →L[Real] Euc n →L[Real] F}
    {a : n → n → ParabolicPoint (Euc n) → Real}
    {b : n → ParabolicPoint (Euc n) → Real}
    {c : ParabolicPoint (Euc n) → Real}
    {u dtimeU source : ParabolicPoint (Euc n) → F}
    {du : ParabolicPoint (Euc n) → Euc n →L[Real] F}
    {d2u : ParabolicPoint (Euc n) → Euc n →L[Real] Euc n →L[Real] F}
    (ha : ∀ p ∈ Q, ∀ i j,
      Tendsto (fun k ↦ aApprox k i j p) l (nhds (a i j p)))
    (hb : ∀ p ∈ Q, ∀ i, Tendsto (fun k ↦ bApprox k i p) l (nhds (b i p)))
    (hc : ∀ p ∈ Q, Tendsto (fun k ↦ cApprox k p) l (nhds (c p)))
    (hu : TendstoLocallyUniformlyOn uApprox u l Q)
    (hdtimeU : TendstoLocallyUniformlyOn dtimeUApprox dtimeU l Q)
    (hdu : TendstoLocallyUniformlyOn duApprox du l Q)
    (hd2u : TendstoLocallyUniformlyOn d2uApprox d2u l Q)
    (hsource : ∀ p ∈ Q, Tendsto (fun k ↦ sourceApprox k p) l (nhds (source p)))
    (hrealize : ∀ k, ParabolicJetRealizesOn Q
      (uApprox k) (dtimeUApprox k) (duApprox k) (d2uApprox k))
    (hequation : ∀ᶠ k in l, Set.EqOn
      (parabolicNondivergenceOperator (aApprox k) (bApprox k) (cApprox k)
        (fun t x ↦ uApprox k (parabolicPoint t x))) (sourceApprox k) Q) :
    Set.EqOn (parabolicNondivergenceOperator a b c
      (fun t x ↦ u (parabolicPoint t x))) source Q := by
  have hlimit := parabolic_jet_realizes_on_of_tendsto_locally_uniformly_on hQ
    hu hdtimeU hdu hd2u hrealize
  intro p hp
  rw [parabolicNondivergenceOperator_eq_jetOperator hQ a b c u dtimeU du d2u
    hlimit hp]
  apply parabolicNondivergenceJetOperator_eq_of_tendsto
    (ha p hp) (hb p hp) (hc p hp) (hu.tendsto_at hp) (hdtimeU.tendsto_at hp)
    (hdu.tendsto_at hp) (hd2u.tendsto_at hp) (hsource p hp)
  exact hequation.mono fun k hk ↦ by
    rw [← parabolicNondivergenceOperator_eq_jetOperator hQ (aApprox k) (bApprox k)
      (cApprox k) (uApprox k) (dtimeUApprox k) (duApprox k) (d2uApprox k)
        (hrealize k) hp]
    exact hk hp

end DifferentialGeometry.Analysis.Parabolic.Euclidean

end
