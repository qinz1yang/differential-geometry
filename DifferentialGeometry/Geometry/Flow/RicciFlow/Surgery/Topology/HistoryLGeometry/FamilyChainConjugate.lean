import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryLGeometry.FamilyChainExists

set_option autoImplicit false

noncomputable section

open Set Filter Bundle
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.Tensor.Coordinates (chartModelBasis)
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

universe u

theorem mfderiv_sum_smul {X N : Type*} [TopologicalSpace X] [ChartedSpace ThreeSpace X]
    [TopologicalSpace N] [ChartedSpace ThreeSpace N] (f : X → N) (x : X) {ι : Type*}
    (t : Finset ι) (a : ι → ℝ) (v : ι → ThreeSpace) :
    (mfderiv ThreeModel ThreeModel f x (∑ i ∈ t, a i • v i) : ThreeSpace) =
      ∑ i ∈ t, a i • (mfderiv ThreeModel ThreeModel f x (v i) : ThreeSpace) := by
  classical
  induction t using Finset.induction_on with
  | empty => exact (mfderiv ThreeModel ThreeModel f x).map_zero
  | insert i t hi ih =>
    have hs : (∑ j ∈ insert i t, a j • v j : ThreeSpace) = a i • v i + ∑ j ∈ t, a j • v j :=
      Finset.sum_insert hi
    rw [Finset.sum_insert hi, ← ih]
    exact (congrArg (fun y : ThreeSpace => (mfderiv ThreeModel ThreeModel f x y : ThreeSpace))
      hs).trans (((mfderiv ThreeModel ThreeModel f x).map_add _ _).trans
      (congrArg (· + _) ((mfderiv ThreeModel ThreeModel f x).map_smul _ _)))

variable {H : ObservedHistory.{u}} {first last fst : Fin (H.eventCount + 1)} {hle : first ≤ last}
  {hfst : first ≤ fst} {T w v : ℝ} {p : (H.stage last).Carrier}
  {Z₀ : H.historyLExpDomain hle T w p}

namespace LFamilyChain

variable (ch : H.LFamilyChain hle hfst T w v p Z₀)

private def jacobiFieldOf (B : ThreeSpace) : ch.toLWindowChain.Field :=
  fun k s => ch.bump k s • ch.familyDeriv k B s

private theorem isLRegularizedJacobi_jacobiFieldOf (B : ThreeSpace) {k : ℕ} (hk : k < ch.n) :
    ∃ a b, a < ch.c k ∧ ch.c (k + 1) < b ∧
      IsLRegularizedJacobi (ch.W k).S T (ch.γ k) (ch.jacobiFieldOf B k) (Ioo a b) := by
  obtain ⟨δ, hδ, -, hone, -, hsub⟩ := ch.bump_spec hk
  refine ⟨ch.c k - δ, ch.c (k + 1) + δ, by linarith, by linarith, fun s hs => ?_⟩
  have hJ := isLRegularizedJacobi_mfderiv_of_contMDiffOn (ch.W k).S T (ch.isOpen_V k)
    (ch.isOpen_K k) (ch.smooth k) (ch.family k) (ch.mem_V k) B s (hsub hs)
  refine HasLRegularizedJacobiAt.congr_of_eqOn _ _ _ _ s _ isOpen_Ioo hs
    (fun r hr => ch.curve k r (hsub hr)) (fun r hr => ?_) hJ
  change _ = ch.bump k r • ch.familyDeriv k B r
  rw [hone r hr, one_smul]
  rfl

private theorem familyDeriv_add (k : ℕ) (B₁ B₂ : ThreeSpace) (s : ℝ) :
    ch.familyDeriv k (B₁ + B₂) s = ch.familyDeriv k B₁ s + ch.familyDeriv k B₂ s :=
  (mfderiv 𝓘(ℝ, ThreeSpace) ThreeModel (fun Z => ch.β k (Z, s))
    (show ThreeSpace from Z₀.1)).map_add B₁ B₂

private theorem familyDeriv_smul (k : ℕ) (c : ℝ) (B : ThreeSpace) (s : ℝ) :
    ch.familyDeriv k (c • B) s = c • ch.familyDeriv k B s :=
  (mfderiv 𝓘(ℝ, ThreeSpace) ThreeModel (fun Z => ch.β k (Z, s))
    (show ThreeSpace from Z₀.1)).map_smul c B

private theorem familyDeriv_zero (k : ℕ) (s : ℝ) : ch.familyDeriv k 0 s = 0 :=
  (mfderiv 𝓘(ℝ, ThreeSpace) ThreeModel (fun Z => ch.β k (Z, s))
    (show ThreeSpace from Z₀.1)).map_zero

private theorem familyDeriv_sum {ι : Type*} (t : Finset ι) (k : ℕ) (B : ι → ThreeSpace) (s : ℝ) :
    ch.familyDeriv k (∑ i ∈ t, B i) s = ∑ i ∈ t, ch.familyDeriv k (B i) s := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using ch.familyDeriv_zero k s
  | insert i t hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, familyDeriv_add, ih]

private theorem jacobiFieldOf_sum (a : Fin (Module.finrank ℝ ThreeSpace) → ℝ) :
    ch.jacobiFieldOf (∑ i, a i • chartModelBasis ThreeSpace i) =
      ∑ i, a i • ch.jacobiField i := by
  funext k s
  rw [Finset.sum_apply, Finset.sum_apply]
  change ch.bump k s • ch.familyDeriv k (∑ i, a i • chartModelBasis ThreeSpace i) s =
    ∑ i, a i • (ch.bump k s • ch.familyDeriv k (chartModelBasis ThreeSpace i) s)
  rw [familyDeriv_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [familyDeriv_smul, smul_comm]

private theorem contMDiff_jacobiFieldOf (B : ThreeSpace) {k : ℕ} (hk : k < ch.n) :
    ContMDiff 𝓘(ℝ, ℝ) ThreeModel.tangent ∞ (fun t => (TotalSpace.mk' ThreeSpace (ch.γ k t)
      (ch.jacobiFieldOf B k t) : TangentBundle ThreeModel (ch.W k).X)) := by
  obtain ⟨δ, -, hρ, -, hzero, -⟩ := ch.bump_spec hk
  intro t
  by_cases ht : t ∈ ch.K k
  · exact contMDiffAt_totalSpace_smul (V := fun t => (ch.familyDeriv k B t :
      TangentSpace ThreeModel (ch.γ k t))) hρ.contMDiff.contMDiffAt
      (ch.contMDiffAt_familyDeriv _ ht)
  · refine (contMDiffAt_totalSpace_zero (ch.contMDiff k).contMDiffAt).congr_of_eventuallyEq ?_
    filter_upwards [hzero t ht] with r hr
    simp only [jacobiFieldOf, hr, zero_smul]
    rfl

private theorem jacobiFieldOf_zero_piece_false (hn : 0 < ch.n) {B : ThreeSpace} (hB : B ≠ 0)
    (hzero : ∀ s ∈ Icc (ch.c 0) (ch.c 1), ch.jacobiFieldOf B 0 s = 0) : False := by
  have : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  obtain ⟨xb, L, hL, hbase⟩ := ch.base
  obtain ⟨δ, hδ, -, hone, -, hsubK⟩ := ch.bump_spec hn
  have hc1 : 0 < ch.c 1 := by
    have := ch.lt 0 hn
    rwa [ch.c_zero] at this
  set z₀ : ThreeSpace := Z₀.1 with hz₀
  have hU : ∀ s ∈ Ioo (0 : ℝ) (ch.c 1), s ∈ ch.K 0 ∧ ch.bump 0 s = 1 := fun s hs =>
    ⟨hsubK ⟨by rw [ch.c_zero]; linarith [hs.1], by linarith [hs.2]⟩,
      hone s ⟨by rw [ch.c_zero]; linarith [hs.1], by linarith [hs.2]⟩⟩
  have hJF : ∀ s ∈ ch.K 0, (ch.familyDeriv 0 B s : ThreeSpace) =
      lRegularizedJacobiField (ch.W 0).S T xb (L z₀) (L B) s := by
    intro s hs
    have hev : (fun Z : ThreeSpace => ch.β 0 (Z, s)) =ᶠ[𝓝 z₀]
        (fun Z : ThreeSpace => lRegularizedCurve (ch.W 0).S T xb (L Z) s) := by
      filter_upwards [(ch.isOpen_V 0).mem_nhds (ch.mem_V 0)] with Z hZ
      exact (hbase Z hZ s hs).2
    have hdom := (hbase z₀ (ch.mem_V 0) s hs).1
    have hg : MDifferentiableAt 𝓘(ℝ, ThreeSpace) ThreeModel
        (fun W : ThreeSpace => lRegularizedCurve (ch.W 0).S T xb W s) (L z₀) :=
      ((lRegularizedCurve_smooth (ch.W 0).S (ch.W 0).solution T xb hdom).comp (L z₀)
        (contMDiffAt_id.prodMk contMDiffAt_const)).mdifferentiableAt (by simp)
    unfold familyDeriv
    rw [hev.mfderiv_eq]
    have hcomp := mfderiv_comp_apply z₀ hg L.mdifferentiableAt B
    exact (hcomp.trans (by rw [L.mfderiv_eq]; rfl))
  have hzU : ∀ s ∈ Ioo (0 : ℝ) (ch.c 1),
      (lRegularizedJacobiField (ch.W 0).S T xb (L z₀) (L B) s : ThreeSpace) = 0 := by
    intro s hs
    have h := hzero s ⟨by rw [ch.c_zero]; exact hs.1.le, hs.2.le⟩
    change ch.bump 0 s • ch.familyDeriv 0 B s = 0 at h
    rw [(hU s hs).2, one_smul] at h
    rw [← hJF s (hU s hs).1]
    exact h
  set s₀ := ch.c 1 / 2 with hs₀
  have hs₀U : s₀ ∈ Ioo (0 : ℝ) (ch.c 1) := ⟨by linarith, by linarith⟩
  have hdom := (hbase z₀ (ch.mem_V 0) s₀ (hU s₀ hs₀U).1).1
  have hLB : L B ≠ 0 := fun h => hB (hL (h.trans L.map_zero.symm))
  have hcov := DifferentialGeometry.Geometry.Riemannian.covDerivAlong_congr_curve
    (I := ThreeModel) ((ch.W 0).S.base.metric (T - s₀ ^ 2))
    (lRegularizedJacobiField (ch.W 0).S T xb (L z₀) (L B))
    (fun s => (0 : TangentSpace ThreeModel (lRegularizedCurve (ch.W 0).S T xb (L z₀) s)))
    (t := s₀) (Filter.EventuallyEq.refl _ _)
    (Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hs₀U) fun s hs => hzU s hs)
  rw [covDerivAlong_zero] at hcov
  exact covDerivAlong_lRegularizedJacobiField_ne_zero (ch.W 0).S (ch.W 0).solution T xb (L z₀)
    (L B) hs₀U.1 hdom hLB (hzU s₀ hs₀U) hcov

private theorem jacobiFieldOf_apply_sum (a : Fin (Module.finrank ℝ ThreeSpace) → ℝ) (k : ℕ)
    (s : ℝ) :
    ch.jacobiFieldOf (∑ i, a i • chartModelBasis ThreeSpace i) k s =
      ∑ i, a i • ch.jacobiField i k s := by
  rw [ch.jacobiFieldOf_sum a, Finset.sum_apply, Finset.sum_apply]
  rfl

private theorem covDerivField_jacobiFieldOf_sum (a : Fin (Module.finrank ℝ ThreeSpace) → ℝ) {k : ℕ}
    (hk : k < ch.n) (s : ℝ) :
    (ch.toLWindowChain.covDerivField (ch.jacobiFieldOf (∑ i, a i • chartModelBasis ThreeSpace i))
        k s : ThreeSpace) =
      ∑ i, a i • (ch.toLWindowChain.covDerivField (ch.jacobiField i) k s : ThreeSpace) := by
  have hfun : ch.jacobiFieldOf (∑ i, a i • chartModelBasis ThreeSpace i) k =
      fun u => ∑ i, a i • ch.jacobiField i k u := funext fun u => ch.jacobiFieldOf_apply_sum a k u
  change (covDerivAlong (I := ThreeModel) ((ch.W k).S.base.metric (T - s ^ 2)) (ch.γ k)
    (ch.jacobiFieldOf (∑ i, a i • chartModelBasis ThreeSpace i) k) s : ThreeSpace) = _
  have hsm : ∀ i, ContMDiff 𝓘(ℝ, ℝ) ThreeModel.tangent ∞ fun t => (TotalSpace.mk' ThreeSpace
      (ch.γ k t) (a i • ch.jacobiField i k t) : TangentBundle ThreeModel (ch.W k).X) :=
    fun i t => contMDiffAt_totalSpace_smul (ρ := fun _ => a i) contMDiffAt_const
      (ch.contMDiff_jacobiField i hk t)
  rw [hfun, covDerivAlong_sum (I := ThreeModel) _ _ Finset.univ
    (fun i u => a i • ch.jacobiField i k u) s (fun i _ =>
      differentiableAt_chartRepAt_of_contMDiff_two (I := ThreeModel)
        ((hsm i).of_le (natCast_le_infty 2)) s)]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact covDerivAlong_smul (I := ThreeModel) _ _ (a i) _ s

theorem linearIndependent_historyLJacobiField {B₀ : ℝ}
    (hfloor : ∀ j, ∀ t ∈ H.stageDomain j, ∀ x : (H.stage j).Carrier,
      -B₀ ≤ metricScalarAt (H.stageMetric j t) x)
    (hgeo : H.IsHistoryLGeodesicOn hle T w (H.historyLCurve hle T w p Z₀))
    (hac : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (H.historyLCurve hle T w p Z₀ j)
      (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T w j.val))
    (hmin : H.regularizedExtendedAction first last T B₀ 0 w (H.historyLCurve hle T w p Z₀) =
      H.regularizedCost first last hle T B₀ 0 w (H.historyLCurve hle T w p Z₀ ⟨last, hle, le_rfl⟩ 0)
        (H.historyLCurve hle T w p Z₀ ⟨first, le_rfl, hle⟩ w))
    (hfin : H.regularizedExtendedAction first last T B₀ 0 w (H.historyLCurve hle T w p Z₀) ≠ ⊤)
    (hv : 0 < v) (hvw : v ≤ w) (hfl : fst ≤ last) (hvk : T - v ^ 2 ∈ H.stageDomain fst)
    {k₀ : ℕ} (hk₀ : k₀ + 1 < ch.n) :
    LinearIndependent ℝ (fun i => (H.historyLJacobiField hle T w p Z₀
      ⟨ch.stage (k₀ + 1), (hfst.trans (ch.first_le k₀)).trans
        (ch.bottom (Nat.lt_of_succ_lt hk₀)).property.1,
        (ch.bottom (Nat.lt_of_succ_lt hk₀)).property.2.trans (ch.le_last k₀)⟩ i
      (ch.c (k₀ + 1)) : ThreeSpace)) := by
  classical
  have hk' : k₀ < ch.n := Nat.lt_of_succ_lt hk₀
  obtain ⟨hK, -, h0, hone, -⟩ := ch.node_facts hk₀
  rw [Fintype.linearIndependent_iff]
  intro a ha
  by_contra hne
  push Not at hne
  set B := ∑ i, a i • chartModelBasis ThreeSpace i with hBdef
  have hB : B ≠ 0 := by
    intro hB0
    obtain ⟨i, hi⟩ := hne
    exact hi (Fintype.linearIndependent_iff.1 (chartModelBasis ThreeSpace).linearIndependent a
      hB0 i)
  have hFd : (mfderiv ThreeModel ThreeModel ((ch.W k₀).f (ch.bottom hk'))
      (ch.γ k₀ (ch.c (k₀ + 1))) (ch.jacobiFieldOf B k₀ (ch.c (k₀ + 1))) : ThreeSpace) = 0 := by
    have h1 := ch.jacobiFieldOf_apply_sum a k₀ (ch.c (k₀ + 1))
    refine (congrArg (fun y : ThreeSpace => (mfderiv ThreeModel ThreeModel
      ((ch.W k₀).f (ch.bottom hk')) (ch.γ k₀ (ch.c (k₀ + 1))) y : ThreeSpace)) h1).trans ?_
    refine (mfderiv_sum_smul _ _ Finset.univ a _).trans ?_
    refine (Finset.sum_congr rfl fun i _ => congrArg (a i • ·) (ch.mfderiv_jacobiField_eq
      (ch.bottom hk') i hK h0 (ch.node k₀ hk₀).1 hone.self_of_nhds)).trans ?_
    exact ha
  have hX1 : ch.jacobiFieldOf B k₀ (ch.c (k₀ + 1)) = 0 := by
    have hF := (ch.W k₀).localDiffeomorph (ch.bottom hk')
    have h2 : (mfderiv ThreeModel ThreeModel ((ch.W k₀).f (ch.bottom hk'))
        (ch.γ k₀ (ch.c (k₀ + 1))) (ch.jacobiFieldOf B k₀ (ch.c (k₀ + 1)))) =
        mfderiv ThreeModel ThreeModel ((ch.W k₀).f (ch.bottom hk'))
          (ch.γ k₀ (ch.c (k₀ + 1))) 0 := hFd.trans (map_zero _).symm
    rw [← hF.mfderivToContinuousLinearEquiv_coe infty_ne_zero] at h2
    exact (hF.mfderivToContinuousLinearEquiv infty_ne_zero _).injective h2
  have hG : ∀ Y ∈ range ch.jacobiField, ch.toLWindowChain.IsGlued Y := by
    rintro _ ⟨i, rfl⟩
    exact ch.isGlued_jacobiField i
  have hXmem : ch.jacobiFieldOf B ∈ Submodule.span ℝ (range ch.jacobiField) := by
    rw [ch.jacobiFieldOf_sum a]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hXg := ch.toLWindowChain.isGlued_of_mem_span hG hXmem
  have hXcg : ∀ k (hk : k + 1 < ch.n),
      ch.toLWindowChain.GluedAt (ch.toLWindowChain.covDerivField (ch.jacobiFieldOf B)) hk := by
    intro k hk
    have hk1 : k < ch.n := Nat.lt_of_succ_lt hk
    change (mfderiv ThreeModel ThreeModel ((ch.W k).f (ch.bottom hk1)) (ch.γ k (ch.c (k + 1)))
      (ch.toLWindowChain.covDerivField (ch.jacobiFieldOf B) k (ch.c (k + 1))) : ThreeSpace) =
      mfderiv ThreeModel ThreeModel ((ch.W (k + 1)).f (ch.top hk)) (ch.γ (k + 1) (ch.c (k + 1)))
        (ch.toLWindowChain.covDerivField (ch.jacobiFieldOf B) (k + 1) (ch.c (k + 1)))
    refine (congrArg (fun y : ThreeSpace => (mfderiv ThreeModel ThreeModel
      ((ch.W k).f (ch.bottom hk1)) (ch.γ k (ch.c (k + 1))) y : ThreeSpace))
      (ch.covDerivField_jacobiFieldOf_sum a hk1 _)).trans ?_
    refine (mfderiv_sum_smul _ _ Finset.univ a _).trans ?_
    refine (Finset.sum_congr rfl fun i _ =>
      congrArg (a i • ·) (ch.isGlued_covDerivField_jacobiField i k hk)).trans ?_
    refine (mfderiv_sum_smul _ _ Finset.univ a _).symm.trans ?_
    exact (congrArg (fun y : ThreeSpace => (mfderiv ThreeModel ThreeModel
      ((ch.W (k + 1)).f (ch.top hk)) (ch.γ (k + 1) (ch.c (k + 1))) y : ThreeSpace))
      (ch.covDerivField_jacobiFieldOf_sum a hk _)).symm
  have hX0 : ch.jacobiFieldOf B 0 0 = 0 := by
    rw [ch.jacobiFieldOf_apply_sum a]
    exact Finset.sum_eq_zero fun i _ => by rw [ch.jacobiField_zero (by omega) i, smul_zero]
  have hzero := LWindowChain.eqOn_zero_of_conjugate_of_minimizer hfloor hgeo hac hmin hfin hv hvw
    hfst hfl hvk ch.toLWindowChain hk₀ (ch.jacobiFieldOf B)
    (fun k hk => ch.contMDiff_jacobiFieldOf B (by omega))
    (fun k hk => ch.isLRegularizedJacobi_jacobiFieldOf B (by omega))
    (fun k hk _ => ⟨hXg k hk, hXcg k hk⟩) hX0 hX1
  exact ch.jacobiFieldOf_zero_piece_false (by omega) hB
    (fun s hs => hzero 0 (Nat.zero_le _) s hs)

end LFamilyChain

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
