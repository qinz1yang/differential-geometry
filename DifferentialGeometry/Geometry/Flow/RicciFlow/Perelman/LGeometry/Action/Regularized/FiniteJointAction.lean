import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.JointRegularity
import DifferentialGeometry.Topology.Manifold.InverseFunctionTheorem.FiniteParameterGraph

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.Exponential
open scoped Manifold ContDiff Topology BigOperators

universe uM uE uH uP

variable {n : ℕ} {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type uH} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {P : Type uP} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {M : Fin (n + 1) → Type uM} [∀ i, TopologicalSpace (M i)]
  [∀ i, ChartedSpace H (M i)] [∀ i, IsManifold I ∞ (M i)] [∀ i, T2Space (M i)]
  {D : Fin (n + 1) → RealTimeInterval}

/-- Action of the same finite family, with only the last upper clock variable. -/
def finiteJointAction
    (S : (i : Fin (n + 1)) → SolutionOn (I := I) (M := M i) (D i))
    (T : ℝ) (f : (i : Fin (n + 1)) → P × ℝ → M i)
    (a b : Fin (n + 1) → ℝ) (z : P × ℝ) : ℝ :=
  (∑ i : Fin n, lRegularizedAction (S i.castSucc) T
    (fun r => f i.castSucc (z.1, r)) (a i.castSucc) (b i.castSucc)) +
  lRegularizedAction (S (Fin.last n)) T
    (fun r => f (Fin.last n) (z.1, r)) (a (Fin.last n)) z.2

omit [I.Boundaryless] in
theorem contDiffOn_finiteJointAction
    (S : (i : Fin (n + 1)) → SolutionOn (I := I) (M := M i) (D i))
    (hS : ∀ i, IsSolutionOn (S i)) (T : ℝ)
    (f : (i : Fin (n + 1)) → P × ℝ → M i)
    (a b : Fin (n + 1) → ℝ) {V : Set P} (hV : IsOpen V)
    (K : Fin (n + 1) → Set ℝ) (hK : ∀ i, IsOpen (K i))
    (hKconn : ∀ i, IsPreconnected (K i))
    (ha : ∀ i, a i ∈ K i) (hb : ∀ i, b i ∈ K i)
    (hf : ∀ i, ContMDiffOn (𝓘(ℝ, P).prod 𝓘(ℝ, ℝ)) I (8 : ℕ)
      (f i) (V ×ˢ K i))
    (hreg : ∀ i r, r ∈ K i → T - r ^ 2 ∈ (D i).regular) :
    ContDiffOn ℝ 2 (finiteJointAction S T f a b) (V ×ˢ K (Fin.last n)) := by
  have hact (i : Fin (n + 1)) := contDiffOn_lRegularizedAction_joint
    (S i) (hS i) T (a i) hV (hK i) (hKconn i) (ha i) (hf i) (hreg i)
  have hfixed (i : Fin n) : ContDiffOn ℝ 2
      (fun z : P × ℝ => lRegularizedAction (S i.castSucc) T
        (fun r => f i.castSucc (z.1, r)) (a i.castSucc) (b i.castSucc))
      (V ×ˢ K (Fin.last n)) :=
    (hact i.castSucc).comp (contDiffOn_fst.prodMk contDiffOn_const)
      (fun _ hz => ⟨hz.1, hb i.castSucc⟩)
  exact (ContDiffOn.sum (s := Finset.univ) (fun i _ => hfixed i)).add (hact (Fin.last n))

/-- The actual C2 joint action branch of a finite family with its physical
terminal exponential germ. This constructs the endpoint/time parametrization;
the history competitor theorem is responsible for the subsequent cost bound. -/
theorem exists_finiteJointAction_endpoint_branch
    [FiniteDimensional ℝ P]
    (S : (i : Fin (n + 1)) → SolutionOn (I := I) (M := M i) (D i))
    (hS : ∀ i, IsSolutionOn (S i)) (T C : ℝ)
    (f : (i : Fin (n + 1)) → P × ℝ → M i)
    (a b : Fin (n + 1) → ℝ) {V : Set P} (hV : IsOpen V) (h0 : (0 : P) ∈ V)
    (K : Fin (n + 1) → Set ℝ) (hK : ∀ i, IsOpen (K i))
    (hKconn : ∀ i, IsPreconnected (K i))
    (ha : ∀ i, a i ∈ K i) (hb : ∀ i, b i ∈ K i)
    (hf : ∀ i, ContMDiffOn (𝓘(ℝ, P).prod 𝓘(ℝ, ℝ)) I (8 : ℕ)
      (f i) (V ×ˢ K i))
    (hreg : ∀ i r, r ∈ K i → T - r ^ 2 ∈ (D i).regular)
    (q : M (Fin.last n)) (B : P ≃L[ℝ] E)
    (hexp : (fun z => f (Fin.last n) (z, b (Fin.last n))) =ᶠ[𝓝 (0 : P)]
      (fun z => expMap ((S (Fin.last n)).base.metric (T - (b (Fin.last n)) ^ 2))
        q (show TangentSpace I q from B z))) :
    ∃ (U : Set (M (Fin.last n) × ℝ)) (psi : M (Fin.last n) × ℝ → P)
      (F : M (Fin.last n) × ℝ → ℝ),
      IsOpen U ∧ (q, b (Fin.last n)) ∈ U ∧
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, P) 2 psi U ∧
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) 2 F U ∧
      psi (q, b (Fin.last n)) = 0 ∧
      F (q, b (Fin.last n)) = C + finiteJointAction S T f a b (0, b (Fin.last n)) ∧
      ∀ z ∈ U, psi z ∈ V ∧ z.2 ∈ K (Fin.last n) ∧
        f (Fin.last n) (psi z, z.2) = z.1 ∧
        F z = C + finiteJointAction S T f a b (psi z, z.2) := by
  let last := Fin.last n
  have hlast2 : ContMDiffAt (𝓘(ℝ, P).prod 𝓘(ℝ, ℝ)) I 2 (f last) (0, b last) :=
    ((hf last).contMDiffAt ((hV.prod (hK last)).mem_nhds ⟨h0, hb last⟩)).of_le
      (by norm_num)
  obtain ⟨hcenter, hloc⟩ :=
    DifferentialGeometry.Coordinates.isLocalDiffeomorphAt_parameter_graph_of_exponential_germ_two
      ((S last).base.metric (T - (b last) ^ 2)) q B hlast2 hexp
  let W : Set (P × ℝ) := V ×ˢ K last
  let U : Set (M last × ℝ) := hloc.localInverse.source ∩ hloc.localInverse ⁻¹' W
  have hWopen : IsOpen W := hV.prod (hK last)
  have hUopen : IsOpen U :=
    hloc.contMDiffOn_localInverse.continuousOn.isOpen_inter_preimage
      hloc.localInverse_open_source hWopen
  have hinv : hloc.localInverse (q, b last) = (0, b last) := by
    simpa only [hcenter] using hloc.localInverse_left_inv hloc.localInverse_mem_target
  have hqU : (q, b last) ∈ U := by
    refine ⟨?_, ?_⟩
    · simpa only [hcenter] using hloc.localInverse_mem_source
    · change hloc.localInverse (q, b last) ∈ W
      rw [hinv]
      exact ⟨h0, hb last⟩
  let psi : M last × ℝ → P := fun z => (hloc.localInverse z).1
  let F : M last × ℝ → ℝ := fun z => C + finiteJointAction S T f a b (hloc.localInverse z)
  have hInv := hloc.contMDiffOn_localInverse.mono
    (inter_subset_left : U ⊆ hloc.localInverse.source)
  have hfst : ContMDiffOn (𝓘(ℝ, P).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, P) 2
      (Prod.fst : P × ℝ → P) (Set.univ : Set (P × ℝ)) :=
    contMDiff_fst.contMDiffOn
  have hpsi : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, P) 2 psi U :=
    hfst.comp hInv (fun z _ =>
      show hloc.localInverse z ∈ (Set.univ : Set (P × ℝ)) from mem_univ _)
  have hact : ContMDiffOn (𝓘(ℝ, P).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) 2
      (finiteJointAction S T f a b) W := by
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    exact contMDiffOn_iff_contDiffOn.mpr
      (contDiffOn_finiteJointAction S hS T f a b hV K hK hKconn ha hb hf hreg)
  have hF : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) 2 F U :=
    contMDiffOn_const.add (hact.comp hInv (fun _ hz => hz.2))
  refine ⟨U, psi, F, hUopen, hqU, hpsi, hF, ?_, ?_, ?_⟩
  · change (hloc.localInverse (q, b last)).1 = 0
    rw [hinv]
  · change C + finiteJointAction S T f a b (hloc.localInverse (q, b last)) = _
    rw [hinv]
  · intro z hz
    have hright := hloc.localInverse_right_inv hz.1
    change (f last (hloc.localInverse z), (hloc.localInverse z).2) = z at hright
    have hclock : (hloc.localInverse z).2 = z.2 := congrArg Prod.snd hright
    have hpair : hloc.localInverse z = (psi z, z.2) :=
      Prod.ext rfl hclock
    refine ⟨hz.2.1, ?_, ?_, ?_⟩
    · rw [← hclock]
      exact hz.2.2
    · have hp := congrArg Prod.fst hright
      rwa [hpair] at hp
    · change C + finiteJointAction S T f a b (hloc.localInverse z) = _
      rw [hpair]

end DifferentialGeometry.PDE.RicciFlow.Perelman
