import DifferentialGeometry.Analysis.Calculus.Inverse.MovingImplicit
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.CenterOfMass.NormalCoordinates.InverseVelocityConvergence
import DifferentialGeometry.Analysis.Calculus.MapConvergence.Configuration
import DifferentialGeometry.Geometry.Exponential.NormalBall.Chart

noncomputable section
open Set
open scoped ContDiff Topology BigOperators

namespace DifferentialGeometry.CheegerGromovCompactness.NormalBranchHessian

variable {E P : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] {ι : Type*} [Fintype ι]

theorem exists_diagonal_invVelocity_compactRootTube
    {D : Set (P × E)} {S K : Set P} (hD : IsOpen D) (hS : IsOpen S)
    (hK : IsCompact K) (hKS : K ⊆ S)
    (e : OpenPartialHomeomorph (E × E) (E × E))
    (mu : P → ι → ℝ) (center : P → E)
    (hmuC : ContDiffOn ℝ ∞ mu S) (hcenterC : ContDiffOn ℝ ∞ center S)
    (hinvC : ContDiffOn ℝ ∞ (e.symm : E × E → E × E) e.target)
    (hfst : MapsTo Prod.fst D S)
    (hmap : ∀ q ∈ D, (q.2, center q.1) ∈ e.target)
    (hgraph : MapsTo (fun p => (p, center p)) S D)
    (hdiag : ∀ p ∈ S, e.symm (center p, center p) = (center p, 0))
    {eta : NNReal}
    (happrox : ApproximatesLinearOn (e.symm : E × E → E × E)
      ((PhaseFlow.freeDiagCLE (E := E)).symm : (E × E) →L[ℝ] (E × E)) e.target eta)
    (hmu : ∀ p ∈ K, ∀ i, 0 ≤ mu p i)
    (hsum : ∀ p ∈ K, ∑ i, mu p i = 1) (heta : eta < 1) :
    Nonempty (Analysis.CompactRootTube D S K
      (fun q => invVelocitySum e (mu q.1) (fun _ => center q.1) q.2) center) := by
  let F : P × E → E := fun q =>
    invVelocitySum e (mu q.1) (fun _ => center q.1) q.2
  have hFC : ContDiffOn ℝ ∞ F D := by
    apply invVelocitySum_contDiff hinvC
      (hmuC.comp contDiff_fst.contDiffOn hfst)
      (contDiffOn_pi.mpr (fun _ => hcenterC.comp contDiff_fst.contDiffOn hfst))
      contDiff_snd.contDiffOn
    intro q hq _
    exact hmap q hq
  have hroot : ∀ p ∈ S, F (p, center p) = 0 := by
    intro p hp
    simp only [F, invVelocitySum, hdiag p hp, smul_zero, Finset.sum_const_zero]
  have hinvertible : ∀ p ∈ K,
      (Analysis.partialFDeriv₂ F p (center p)).IsInvertible := by
    intro p hp
    have hpd : (p, center p) ∈ D := hgraph (hKS hp)
    obtain ⟨L, hL⟩ := invVelocitySum_inv e (mu p) (fun _ : ι => center p)
      hinvC (fun _ => hmap (p, center p) hpd) happrox (hmu p hp) (hsum p hp) heta
    have hFAt : DifferentiableAt ℝ F (p, center p) :=
      (hFC.contDiffAt (hD.mem_nhds hpd)).differentiableAt (by simp)
    have hslice : HasFDerivAt (fun y => F (p, y)) (L : E →L[ℝ] E) (center p) := hL
    exact ⟨L, (Analysis.partialFDeriv₂_eq hFAt hslice).symm⟩
  exact Analysis.exists_compactRootTube hD hS hK hKS hFC hcenterC hgraph hroot hinvertible

theorem exists_diagonal_invVelocity_rootTube
    {S K : Set P} (hS : IsOpen S) (hK : IsCompact K) (hKS : K ⊆ S)
    (e : OpenPartialHomeomorph (E × E) (E × E))
    (mu : P → ι → ℝ) (center : P → E)
    (hmuC : ContDiffOn ℝ ∞ mu S) (hcenterC : ContDiffOn ℝ ∞ center S)
    (hinvC : ContDiffOn ℝ ∞ (e.symm : E × E → E × E) e.target)
    (hdiag : ∀ p ∈ S, (center p, center p) ∈ e.target ∧
      e.symm (center p, center p) = (center p, 0))
    {eta : NNReal}
    (happrox : ApproximatesLinearOn (e.symm : E × E → E × E)
      ((PhaseFlow.freeDiagCLE (E := E)).symm : (E × E) →L[ℝ] (E × E)) e.target eta)
    (hmu : ∀ p ∈ K, ∀ i, 0 ≤ mu p i)
    (hsum : ∀ p ∈ K, ∑ i, mu p i = 1) (heta : eta < 1) :
    Nonempty (Analysis.CompactRootTube
      ((S ×ˢ Set.univ) ∩ (fun q : P × E => (q.2, center q.1)) ⁻¹' e.target)
      S K (fun q => invVelocitySum e (mu q.1) (fun _ => center q.1) q.2) center) := by
  have hcenter : ContinuousOn (fun q : P × E => center q.1) (S ×ˢ Set.univ) :=
    hcenterC.continuousOn.comp continuous_fst.continuousOn (fun _ hq => hq.1)
  have hD := (continuous_snd.continuousOn.prodMk hcenter).isOpen_inter_preimage
    (hS.prod isOpen_univ) e.open_target
  exact exists_diagonal_invVelocity_compactRootTube hD hS hK hKS e mu center
    hmuC hcenterC hinvC (fun _ hq => hq.1.1) (fun _ hq => hq.2)
    (fun p hp => ⟨⟨hp, Set.mem_univ _⟩, (hdiag p hp).1⟩)
    (fun p hp => (hdiag p hp).2) happrox hmu hsum heta

omit [FiniteDimensional ℝ E] in
theorem invVelocitySum_hasFDerivAt_of_diagonal_derivative
    (e : OpenPartialHomeomorph (E × E) (E × E)) (mu : ι → ℝ) {z : E}
    (hinv : HasFDerivAt (e.symm : E × E → E × E)
      ((PhaseFlow.freeDiagCLE (E := E)).symm : (E × E) →L[ℝ] (E × E)) (z, z))
    (hsum : ∑ i, mu i = 1) :
    HasFDerivAt (invVelocitySum e mu (fun _ => z))
      (-ContinuousLinearMap.id ℝ E) z := by
  classical
  have heq : invVelocitySum e mu (fun _ => z) = fun y => (e.symm (y, z)).2 := by
    funext y
    simp only [invVelocitySum, ← Finset.sum_smul, hsum, one_smul]
  rw [heq]
  have hpair : HasFDerivAt (fun y : E => (y, z))
      ((ContinuousLinearMap.id ℝ E).prod 0) z := by
    fun_prop
  have hcomp := (hinv.comp z hpair (f := fun y : E => (y, z))).snd
  convert hcomp using 1 <;> ext v <;> simp

omit [FiniteDimensional ℝ E] in
theorem invVelocitySum_hasFDerivAt_of_zero_section_derivative
    (e : OpenPartialHomeomorph (E × E) (E × E)) (mu : ι → ℝ) {z : E}
    (htarget : (z, z) ∈ e.target) (hdiag : e.symm (z, z) = (z, 0))
    (hforward : HasFDerivAt (e : E × E → E × E)
      (PhaseFlow.freeDiagCLE (E := E) : (E × E) →L[ℝ] (E × E)) (z, 0))
    (hsum : ∑ i, mu i = 1) :
    HasFDerivAt (invVelocitySum e mu (fun _ => z))
      (-ContinuousLinearMap.id ℝ E) z := by
  apply invVelocitySum_hasFDerivAt_of_diagonal_derivative e mu _ hsum
  apply e.hasFDerivAt_symm htarget
  simpa only [hdiag] using hforward

end DifferentialGeometry.CheegerGromovCompactness.NormalBranchHessian
end

noncomputable section
open Set Filter
open scoped ContDiff Topology BigOperators

namespace DifferentialGeometry.CheegerGromovCompactness.NormalBranchHessian

variable {E P : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] {ι : Type*} [Fintype ι]

theorem exists_diagonal_invVelocity_compactRootTube_buffered
    {S K : Set P} (hS : IsOpen S) (hK : IsCompact K) (hKS : K ⊆ S)
    (e : OpenPartialHomeomorph (E × E) (E × E))
    (mu : P → ι → ℝ) (center : P → E)
    (hmuC : ContDiffOn ℝ ∞ mu S) (hcenterC : ContDiffOn ℝ ∞ center S)
    (hinvC : ContDiffOn ℝ ∞ (e.symm : E × E → E × E) e.target)
    {V : Set (E × E)} (hV : IsOpen V) (hVtarget : V ⊆ e.target)
    {O : Set E} (hO : IsOpen O) (hcenterO : MapsTo center S O)
    (hdiagV : ∀ p ∈ S, (center p, center p) ∈ V)
    (hdiag : ∀ p ∈ S, e.symm (center p, center p) = (center p, 0))
    {eta : NNReal}
    (happrox : ApproximatesLinearOn (e.symm : E × E → E × E)
      ((PhaseFlow.freeDiagCLE (E := E)).symm : (E × E) →L[ℝ] (E × E)) e.target eta)
    (hmu : ∀ p ∈ K, ∀ i, 0 ≤ mu p i)
    (hsum : ∀ p ∈ K, ∑ i, mu p i = 1) (heta : eta < 1)
    {configuration : ℕ → P → (ι → ℝ) × (ι → E)}
    (hconfiguration : MapCInfConvergenceOnCompacts S configuration
      (fun p => (mu p, fun _ => center p))) :
    ∃ (D : Set (P × E)),
      Nonempty (Analysis.CompactRootTube D S K
        (fun q => invVelocitySum e (mu q.1) (fun _ => center q.1) q.2) center) ∧
      IsCompact (closure D) ∧
      MapsTo Prod.fst (closure D) S ∧
      MapsTo Prod.snd (closure D) O ∧
      MapsTo (fun q : P × E => (q.2, center q.1)) (closure D) V ∧
      ∀ᶠ k in atTop, ∀ q ∈ closure D, ∀ i,
        (q.2, (configuration k q.1).2 i) ∈ V := by
  let D₀ : Set (P × E) :=
    (S ×ˢ O) ∩ (fun q : P × E => (q.2, center q.1)) ⁻¹' V
  have hpairC : ContinuousOn (fun q : P × E => (q.2, center q.1)) (S ×ˢ O) :=
    continuous_snd.continuousOn.prodMk
      (hcenterC.continuousOn.comp continuous_fst.continuousOn (fun _ hq => hq.1))
  have hD₀ : IsOpen D₀ :=
    hpairC.isOpen_inter_preimage (hS.prod hO) hV
  obtain ⟨T₀⟩ := exists_diagonal_invVelocity_compactRootTube hD₀ hS hK hKS e mu center
    hmuC hcenterC hinvC
    (fun _ hq => hq.1.1)
    (fun _ hq => hVtarget hq.2)
    (fun p hp => ⟨⟨hp, hcenterO hp⟩, hdiagV p hp⟩)
    hdiag happrox hmu hsum heta
  obtain ⟨D, T, hDcompact, hDD₀, hparameter, hrho⟩ := T₀.exists_domain_buffer
  have hfst : MapsTo Prod.fst (closure D) S := fun _ hq => (hDD₀ hq).1.1
  have hsnd : MapsTo Prod.snd (closure D) O := fun _ hq => (hDD₀ hq).1.2
  have hpair : MapsTo (fun q : P × E => (q.2, center q.1)) (closure D) V :=
    fun _ hq => (hDD₀ hq).2
  refine ⟨D, ⟨T⟩, hDcompact, hfst, hsnd, hpair, ?_⟩
  exact hconfiguration.eventually_configuration_pairs_mem hDcompact hfst
    (hcenterC.continuousOn.mono (image_subset_iff.mpr hfst)) hV hpair

end DifferentialGeometry.CheegerGromovCompactness.NormalBranchHessian
end

noncomputable section
open Filter Set
open scoped ContDiff Topology

namespace DifferentialGeometry.CheegerGromovCompactness.NormalBranchHessian

variable {E P : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] {ι : Type*} [Fintype ι]
  {S : Set P} {D : Set (P × E)} {V : Set (E × E)}
  {W₀ K : Set P} {PhiInf : P → E}
  {configuration : ℕ → P → (ι → ℝ) × (ι → E)}
  {configurationInf : P → (ι → ℝ) × (ι → E)}
  {e : ℕ → OpenPartialHomeomorph (E × E) (E × E)}
  {eInf : OpenPartialHomeomorph (E × E) (E × E)}

theorem exists_invVelocity_root
    (T : Analysis.CompactRootTube D W₀ K
      (fun q => invVelocitySum eInf (configurationInf q.1).1
        (configurationInf q.1).2 q.2) PhiInf)
    (hS : IsOpen S) (hV : IsOpen V)
    (hfst : MapsTo Prod.fst D S)
    (hconfiguration : MapCInfConvergenceOnCompacts S configuration configurationInf)
    (hconfigurationC : ∀ k, ContDiffOn ℝ ∞ (configuration k) S)
    (hconfigurationInfC : ContDiffOn ℝ ∞ configurationInf S)
    (hinverse : MapCInfConvergenceOnCompacts V
      (fun k => ((e k).symm : E × E → E × E)) eInf.symm)
    (hinverseC : ∀ᶠ k in atTop, ContDiffOn ℝ ∞ ((e k).symm : E × E → E × E) V)
    (hinverseInfC : ContDiffOn ℝ ∞ (eInf.symm : E × E → E × E) V)
    (hmap : ∀ᶠ k in atTop, ∀ q ∈ D, ∀ i,
      (q.2, (configuration k q.1).2 i) ∈ V)
    (hmapInf : ∀ q ∈ D, ∀ i, (q.2, (configurationInf q.1).2 i) ∈ V)
    : ∃ N : Nat, ∃ Phi : Nat → P → E,
      MapCInfConvergenceOnCompacts T.parameterDomain Phi PhiInf ∧
      (∀ k, ContDiffOn ℝ ∞ (Phi k) T.parameterDomain) ∧
      (∀ k ≥ N, ∀ p ∈ closure T.parameterDomain,
        dist (Phi k p) (PhiInf p) < T.rho / 2 ∧
        invVelocitySum (e k) (configuration k p).1 (configuration k p).2 (Phi k p) = 0 ∧
        (Analysis.partialFDeriv₂
          (fun q : P × E => invVelocitySum (e k) (configuration k q.1).1
            (configuration k q.1).2 q.2) p (Phi k p)).IsInvertible) ∧
      ∀ k ≥ N, ∀ p ∈ closure T.parameterDomain, ∀ y,
        dist y (PhiInf p) < T.rho →
          (invVelocitySum (e k) (configuration k p).1 (configuration k p).2 y = 0 ↔
            y = Phi k p) := by
  have hcfg : MapCInfConvergenceOnCompacts D
      (fun k q => configuration k q.1) (fun q => configurationInf q.1) :=
    hconfiguration.precomp T.isOpen_domain hS contDiff_fst.contDiffOn hfst
      hconfigurationC hconfigurationInfC
  have hcfgC : ∀ k, ContDiffOn ℝ ∞ (fun q : P × E => configuration k q.1) D :=
    fun k => (hconfigurationC k).comp contDiff_fst.contDiffOn hfst
  have hcfgInfC : ContDiffOn ℝ ∞ (fun q : P × E => configurationInf q.1) D :=
    hconfigurationInfC.comp contDiff_fst.contDiffOn hfst
  have hF : MapCInfConvergenceOnCompacts D
      (fun k q => invVelocitySum (e k) (configuration k q.1).1
        (configuration k q.1).2 q.2)
      (fun q => invVelocitySum eInf (configurationInf q.1).1
        (configurationInf q.1).2 q.2) :=
    invVelocityConfiguration_tail T.isOpen_domain hV hinverse hcfg
      (mapCInfConvergence_const Prod.snd) hinverseC hinverseInfC hcfgC hcfgInfC
      (fun _ => contDiff_snd.contDiffOn) contDiff_snd.contDiffOn hmap hmapInf
  have hFC : ∀ᶠ k in atTop, ContDiffOn ℝ ∞
      (fun q : P × E => invVelocitySum (e k) (configuration k q.1).1
        (configuration k q.1).2 q.2) D := by
    filter_upwards [hinverseC, hmap] with k hkC hkmap
    exact invVelocitySum_contDiff hkC (hcfgC k).fst (hcfgC k).snd
      contDiff_snd.contDiffOn hkmap
  exact T.exists_cInf_tail hFC hF

end DifferentialGeometry.CheegerGromovCompactness.NormalBranchHessian
end

noncomputable section
open Filter Set
open scoped ContDiff Topology Manifold

namespace DifferentialGeometry.CheegerGromovCompactness.NormalBranchHessian

variable {E P : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] {ι : Type*} [Fintype ι]
  {S : Set P} {D : Set (P × E)} {V : Set (E × E)}
  {W₀ K : Set P} {PhiInf : P → E}
  {configuration : ℕ → P → (ι → ℝ) × (ι → E)}
  {configurationInf : P → (ι → ℝ) × (ι → E)}
  {e : ℕ → OpenPartialHomeomorph (E × E) (E × E)}
  {eInf : OpenPartialHomeomorph (E × E) (E × E)}

variable {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : ℕ → Type*} [∀ k, TopologicalSpace (M k)] [∀ k, ChartedSpace H (M k)]
  (p₀ : ∀ k, M k)
  (c : ∀ k, Geometry.Riemannian.NormalCoordinates.NormalBallChart (I := I) (p₀ k))

theorem exists_source_invVelocity_root
    (T : Analysis.CompactRootTube D W₀ K
      (fun q => invVelocitySum eInf (configurationInf q.1).1
        (configurationInf q.1).2 q.2) PhiInf)
    (hS : IsOpen S) (hV : IsOpen V)
    (hfst : MapsTo Prod.fst D S)
    (hconfiguration : MapCInfConvergenceOnCompacts S configuration configurationInf)
    (hconfigurationC : ∀ k, ContDiffOn ℝ ∞ (configuration k) S)
    (hconfigurationInfC : ContDiffOn ℝ ∞ configurationInf S)
    (hinverse : MapCInfConvergenceOnCompacts V
      (fun k => ((e k).symm : E × E → E × E)) eInf.symm)
    (hinverseC : ∀ᶠ k in atTop, ContDiffOn ℝ ∞ ((e k).symm : E × E → E × E) V)
    (hinverseInfC : ContDiffOn ℝ ∞ (eInf.symm : E × E → E × E) V)
    (hmap : ∀ᶠ k in atTop, ∀ q ∈ D, ∀ i,
      (q.2, (configuration k q.1).2 i) ∈ V)
    (hmapInf : ∀ q ∈ D, ∀ i, (q.2, (configurationInf q.1).2 i) ∈ V)
    (hchartDomain : ∀ k p y, (p, y) ∈ D → y ∈ Metric.ball (0 : E) (c k).radius) :
    ∃ (N : Nat) (F : ∀ k, P → M k) (Phi : Nat → P → E),
      (∀ k p, F k p = (c k).hom (Phi k p)) ∧
      MapCInfConvergenceOnCompacts T.parameterDomain Phi PhiInf ∧
      MapCInfConvergenceOnCompacts T.parameterDomain
        (fun k p => (c k).inv (F k p)) PhiInf ∧
      (∀ k, ContDiffOn ℝ ∞ (Phi k) T.parameterDomain) ∧
      (∀ k ≥ N, ContMDiffOn 𝓘(ℝ, P) I ∞ (F k) T.parameterDomain) ∧
      (∀ k ≥ N, ∀ p ∈ closure T.parameterDomain,
        F k p ∈ (c k).restrictBall.target ∧
        (c k).inv (F k p) = Phi k p ∧
        dist (Phi k p) (PhiInf p) < T.rho / 2 ∧
        invVelocitySum (e k) (configuration k p).1 (configuration k p).2 (Phi k p) = 0) ∧
      (∀ k ≥ N, ∀ p ∈ closure T.parameterDomain, ∀ y,
        dist y (PhiInf p) < T.rho →
          (invVelocitySum (e k) (configuration k p).1 (configuration k p).2 y = 0 ↔
            y = Phi k p)) ∧
      ∀ k ≥ N, ∀ p ∈ closure T.parameterDomain,
        (∀ i, (configuration k p).1 i ≠ 0 → (configuration k p).2 i = PhiInf p) →
        (e k).symm (PhiInf p, PhiInf p) = (PhiInf p, 0) →
          F k p = (c k).hom (PhiInf p) := by
  obtain ⟨N, Phi, hPhi, hPhiC, hspec, huniq⟩ := exists_invVelocity_root T hS hV hfst
    hconfiguration hconfigurationC hconfigurationInfC hinverse hinverseC hinverseInfC hmap hmapInf
  let F : ∀ k, P → M k := fun k p => (c k).hom (Phi k p)
  have hPhiSource : ∀ k ≥ N, ∀ p ∈ closure T.parameterDomain,
      Phi k p ∈ Metric.ball (0 : E) (c k).radius := by
    intro k hk p hp
    apply hchartDomain k p
    apply T.tube_subset p hp
    change dist (Phi k p) (PhiInf p) ≤ T.rho
    exact (hspec k hk p hp).1.le.trans (by linarith [T.rho_pos])
  have hinv : ∀ k ≥ N, ∀ p ∈ closure T.parameterDomain, (c k).inv (F k p) = Phi k p := by
    intro k hk p hp
    exact (c k).restrictBall.left_inv (hPhiSource k hk p hp)
  refine ⟨N, F, Phi, fun _ _ => rfl, hPhi, ?_, hPhiC, ?_, ?_, huniq, ?_⟩
  · apply hPhi.congr_eventually T.isOpen_parameterDomain
    · filter_upwards [eventually_ge_atTop N] with k hk p hp
      exact hinv k hk p (subset_closure hp)
    · exact Set.eqOn_refl _ _
  · intro k hk
    exact (c k).smooth_to.comp (by simpa only [contMDiffOn_iff_contDiffOn] using hPhiC k)
      (fun p hp => hPhiSource k hk p (subset_closure hp))
  · intro k hk p hp
    exact ⟨(c k).restrictBall.map_source (hPhiSource k hk p hp), hinv k hk p hp,
      (hspec k hk p hp).1, (hspec k hk p hp).2.1⟩
  · intro k hk p hp hactive hdiag
    have hz : invVelocitySum (e k) (configuration k p).1 (configuration k p).2 (PhiInf p) = 0 := by
      rw [invVelocitySum_congr_ne (e k) (configuration k p).1 (configuration k p).2
        (fun _ => PhiInf p) (PhiInf p) hactive]
      simp only [invVelocitySum, hdiag, smul_zero, Finset.sum_const_zero]
    have heq := (huniq k hk p hp (PhiInf p) (by simpa using T.rho_pos)).mp hz
    exact congrArg (fun y => (c k).hom y) heq.symm

end DifferentialGeometry.CheegerGromovCompactness.NormalBranchHessian
end

noncomputable section
open Set Filter
open scoped ContDiff Topology Manifold

namespace DifferentialGeometry.CheegerGromovCompactness.NormalBranchHessian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : ℕ → Type*} [∀ k, TopologicalSpace (M k)] [∀ k, ChartedSpace H (M k)]

theorem exists_source_invVelocity_root_near
    {p₀ : ∀ k, M k}
    (c : ∀ k, Geometry.Riemannian.NormalCoordinates.NormalBallChart (I := I) (p₀ k))
    {U : Set E} (hU : IsOpen U) {a : E} (ha : a ∈ U)
    (mu : E → ι → ℝ) (xi : ℕ → E → ι → E)
    (hmuC : ContDiffOn ℝ ∞ mu U)
    (hconfigurationC : ∀ k, ContDiffOn ℝ ∞ (fun z => (mu z, xi k z)) U)
    (hconfiguration : MapCInfConvergenceOnCompacts U
      (fun k z => (mu z, xi k z)) (fun z => (mu z, fun _ => z - a)))
    (hmu : ∀ i, 0 ≤ mu a i) (hsum : ∑ i, mu a i = 1)
    (e : ℕ → OpenPartialHomeomorph (E × E) (E × E))
    (eInf : OpenPartialHomeomorph (E × E) (E × E))
    {q ε R : ℝ} (hq : 0 < q) (hε : 0 < ε) (hR : 0 < R)
    (hchart : ∀ k, R ≤ (c k).radius)
    (hinverse : MapCInfConvergenceOnCompacts (Metric.ball (0 : E × E) ε)
      (fun k => ((e k).symm : E × E → E × E)) eInf.symm)
    (hinverseC : ∀ᶠ k in atTop, ContDiffOn ℝ ∞ ((e k).symm : E × E → E × E)
      (Metric.ball (0 : E × E) ε))
    (hinverseInfC : ContDiffOn ℝ ∞ (eInf.symm : E × E → E × E) eInf.target)
    (hVtarget : Metric.ball (0 : E × E) ε ⊆ eInf.target)
    (hdiag : ∀ z ∈ Metric.ball (0 : E) q, eInf.symm (z, z) = (z, 0))
    {eta : NNReal}
    (happrox : ApproximatesLinearOn (eInf.symm : E × E → E × E)
      ((PhaseFlow.freeDiagCLE (E := E)).symm : (E × E) →L[ℝ] (E × E)) eInf.target eta)
    (heta : eta < 1) :
    ∃ (W : Set E) (r : ℝ) (N : Nat) (F : ∀ k, E → M k) (Phi : Nat → E → E),
      IsOpen W ∧ a ∈ W ∧ IsCompact (closure W) ∧ closure W ⊆ U ∧
      (∀ z ∈ closure W, z - a ∈ Metric.ball (0 : E) q ∧
        z - a ∈ Metric.ball (0 : E) ε ∧ z - a ∈ Metric.ball (0 : E) R) ∧ 0 < r ∧
      (∀ k z, F k z = (c k).hom (Phi k z)) ∧
      MapCInfConvergenceOnCompacts W Phi (fun z => z - a) ∧
      MapCInfConvergenceOnCompacts W (fun k z => (c k).inv (F k z)) (fun z => z - a) ∧
      (∀ k, ContDiffOn ℝ ∞ (Phi k) W) ∧
      (∀ k ≥ N, ContMDiffOn (modelWithCornersSelf ℝ E) I ∞ (F k) W) ∧
      (∀ k ≥ N, ∀ z ∈ closure W,
        Phi k z ∈ Metric.ball (0 : E) R ∧
        F k z ∈ (c k).restrictBall.target ∧
        (c k).inv (F k z) = Phi k z ∧
        dist (Phi k z) (z - a) < r / 2 ∧
        invVelocitySum (e k) (mu z) (xi k z) (Phi k z) = 0 ∧
        ∀ i, (Phi k z, xi k z i) ∈ Metric.ball (0 : E × E) ε) ∧
      (∀ k ≥ N, ∀ z ∈ closure W, ∀ y, dist y (z - a) < r →
        (invVelocitySum (e k) (mu z) (xi k z) y = 0 ↔ y = Phi k z)) ∧
      ∀ k ≥ N, ∀ z ∈ closure W,
        (∀ i, mu z i ≠ 0 → xi k z i = z - a) →
        (e k).symm (z - a, z - a) = (z - a, 0) →
          F k z = (c k).hom (z - a) := by
  let S : Set E := U ∩ (fun z : E => z - a) ⁻¹'
    (Metric.ball 0 q ∩ Metric.ball 0 ε ∩ Metric.ball 0 R)
  have hS : IsOpen S := hU.inter
    (((Metric.isOpen_ball.inter Metric.isOpen_ball).inter Metric.isOpen_ball).preimage
      (continuous_id.sub continuous_const))
  have haS : a ∈ S := by
    refine ⟨ha, ?_⟩
    simp only [Set.mem_preimage, sub_self, Set.mem_inter_iff, Metric.mem_ball, dist_self]
    exact ⟨⟨hq, hε⟩, hR⟩
  have hSU : S ⊆ U := inter_subset_left
  have hcenterC : ContDiffOn ℝ ∞ (fun z : E => z - a) S :=
    (contDiff_id.sub contDiff_const).contDiffOn
  have hconfigurationS : MapCInfConvergenceOnCompacts S
      (fun k z => (mu z, xi k z)) (fun z => (mu z, fun _ => z - a)) :=
    fun K hK hKS => hconfiguration K hK (hKS.trans hSU)
  obtain ⟨D, ⟨T⟩, hDcompact, hfst, hsnd, hpair, hmap⟩ :=
    exists_diagonal_invVelocity_compactRootTube_buffered hS (isCompact_singleton (x := a))
      (singleton_subset_iff.mpr haS) eInf mu (fun z => z - a)
      (hmuC.mono hSU) hcenterC hinverseInfC Metric.isOpen_ball hVtarget
      Metric.isOpen_ball (fun _ hz => hz.2.2)
      (fun z hz => by
        simpa only [Metric.mem_ball, Prod.dist_eq, Prod.fst_zero, Prod.snd_zero,
          max_self] using hz.2.1.2)
      (fun z hz => hdiag (z - a) hz.2.1.1) happrox
      (fun z hz => by simpa only [mem_singleton_iff.mp hz] using hmu)
      (fun z hz => by simpa only [mem_singleton_iff.mp hz] using hsum)
      heta hconfigurationS
  obtain ⟨N, F, Phi, hF, hPhi, hcoords, hPhiC, hFC, hspec, huniq, hanchor⟩ :=
    exists_source_invVelocity_root p₀ c T hS Metric.isOpen_ball
      (fun _ hz => hfst (subset_closure hz)) hconfigurationS
      (fun k => (hconfigurationC k).mono hSU)
      ((hmuC.mono hSU).prodMk (contDiffOn_pi.mpr fun _ => hcenterC))
      hinverse hinverseC (hinverseInfC.mono hVtarget)
      (hmap.mono fun k hk z hz i => hk z (subset_closure hz) i)
      (fun z hz _ => hpair (subset_closure hz))
      (fun k z y hzy => Metric.ball_subset_ball (hchart k) (hsnd (subset_closure hzy)))
  obtain ⟨Nmap, hNmap⟩ := Filter.eventually_atTop.mp hmap
  refine ⟨T.parameterDomain, T.rho, max N Nmap, F, Phi, T.isOpen_parameterDomain,
    T.K_subset_parameterDomain (mem_singleton a), T.isCompact_closure_parameterDomain,
    T.closure_parameterDomain_subset.trans hSU, ?_, T.rho_pos, hF, hPhi, hcoords, hPhiC,
    (fun k hk => hFC k ((le_max_left N Nmap).trans hk)), ?_,
    (fun k hk => huniq k ((le_max_left N Nmap).trans hk)),
    (fun k hk => hanchor k ((le_max_left N Nmap).trans hk))⟩
  · intro z hz
    have hzS := T.closure_parameterDomain_subset hz
    exact ⟨hzS.2.1.1, hzS.2.1.2, hzS.2.2⟩
  intro k hk z hz
  have hkN := (le_max_left N Nmap).trans hk
  have hrootD : (z, Phi k z) ∈ D := by
    apply T.tube_subset z hz
    change dist (Phi k z) (z - a) ≤ T.rho
    exact (hspec k hkN z hz).2.2.1.le.trans (by linarith [T.rho_pos])
  obtain ⟨htarget, hcoords, hdist, hroot⟩ := hspec k hkN z hz
  exact ⟨hsnd (subset_closure hrootD), htarget, hcoords, hdist, hroot,
    hNmap k ((le_max_right N Nmap).trans hk) (z, Phi k z) (subset_closure hrootD)⟩

end DifferentialGeometry.CheegerGromovCompactness.NormalBranchHessian
end
