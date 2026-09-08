import DifferentialGeometry.Geometry.Connection.ParallelLineSplitting
import DifferentialGeometry.Geometry.Flow.RicciFlow.LocalProduct

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Set
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

universe uE uH uM
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [T2Space M]

theorem exists_local_product_from_common_parallel_unit_section
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : Set ℝ) (t₀ : ℝ) (ht₀ : t₀ ∈ T) (hT : T ⊆ D.regular)
    (x : M) {U : Set M} (hUopen : IsOpen U) (hxU : x ∈ U)
    (s : Cₛ^∞⟮I; E, TangentSpace I⟯)
    (hunit : ∀ y ∈ U, (S.family.metric t₀).inner y (s y) (s y) = 1)
    (hparallel : ∀ a ∈ T, ∀ y ∈ U, ∀ v : TangentSpace I y,
      (LeviCivita (I := I) (S.family.metric a)) s y v = 0)
    (hdual : ∀ a ∈ T, ∀ y ∈ U, ∀ v : TangentSpace I y,
      (S.family.metric a).inner y (s y) v = (S.family.metric t₀).inner y (s y) v) :
    ∃ (K : TopologicalSpace.Opens (perpSpace (S.family.metric t₀) x (s x)))
      (O : TopologicalSpace.Opens ℝ)
      (phi : PartialDiffeomorph ((perpModel (S.family.metric t₀) x (s x)).prod 𝓘(ℝ, ℝ)) I
        (perpSpace (S.family.metric t₀) x (s x) × ℝ) M ∞)
      (hPhi : IsLocalDiffeomorph ((perpModel (S.family.metric t₀) x (s x)).prod 𝓘(ℝ, ℝ)) I ∞
        (fun y : K × O => phi (y.1.1, y.2.1)))
      (h : ℝ → SmoothRiemannianMetric (perpModel (S.family.metric t₀) x (s x)) K),
      (0 : perpSpace (S.family.metric t₀) x (s x)) ∈ K ∧ (0 : ℝ) ∈ O ∧
      IsPreconnected (O : Set ℝ) ∧ phi.source = (K : Set _) ×ˢ (O : Set ℝ) ∧
      phi (0, 0) = x ∧ phi.target ⊆ U ∧
      (∀ a ∈ T, localPullMetric (S.family.metric a) (fun y : K × O => phi (y.1.1, y.2.1)) hPhi =
        (h a).prod ((euclideanMetric (E := ℝ)).restrictOpen O)) ∧
      (∀ a ∈ T, ∀ (k : K) (u v : TangentSpace (perpModel (S.family.metric t₀) x (s x)) k),
        (h a).inner k u v = (S.family.metric a).inner (phi (k.1, 0))
          (mfderiv (perpModel (S.family.metric t₀) x (s x)) I
            (fun y : perpSpace (S.family.metric t₀) x (s x) => phi (y, 0)) k.1 u)
          (mfderiv (perpModel (S.family.metric t₀) x (s x)) I
            (fun y : perpSpace (S.family.metric t₀) x (s x) => phi (y, 0)) k.1 v)) ∧
      (∀ a ∈ T, ∀ (k : K) (u v : TangentSpace (perpModel (S.family.metric t₀) x (s x)) k),
        HasDerivWithinAt (fun b => (h b).inner k u v)
          (-2 * ricciTensor (h a) k u v) T a) ∧
      ∀ k ∈ K, ∀ t ∈ O, ∀ r : ℝ,
        mfderiv ((perpModel (S.family.metric t₀) x (s x)).prod 𝓘(ℝ, ℝ)) I
          (fun z : perpSpace (S.family.metric t₀) x (s x) × ℝ => phi z) (k, t) (0, r) =
        r • s (phi (k, t)) := by
  obtain ⟨K, O, phi, hPhi, h, hK₀, hO₀, hconnected, hsource, hzero,
      htarget, hmetric, hinner, hvertical⟩ :=
    exists_local_product_metric_family_from_common_parallel_unit_section
      (fun a : T => S.family.metric a.1) ⟨t₀, ht₀⟩ x hUopen hxU s hunit
      (fun a => hparallel a.1 a.2) (fun a => hdual a.1 a.2)
  let _ : (perpModel (S.family.metric t₀) x (s x)).Boundaryless := by
    constructor
    ext y
    simp only [Set.mem_range, Set.mem_univ, iff_true]
    exact ⟨y, rfl⟩
  let _ : SigmaCompactSpace K := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen (perpModel (S.family.metric t₀) x (s x)) K.isOpen)
  let _ : SigmaCompactSpace O := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen 𝓘(ℝ, ℝ) O.isOpen)
  classical
  let H : ℝ → SmoothRiemannianMetric (perpModel (S.family.metric t₀) x (s x)) K :=
    fun a => if ha : a ∈ T then h ⟨a, ha⟩ else h ⟨t₀, ht₀⟩
  refine ⟨K, O, phi, hPhi, H, hK₀, hO₀, hconnected, hsource, hzero,
    htarget, ?_, ?_, ?_, hvertical⟩
  · intro a ha
    simpa only [H, dif_pos ha] using hmetric ⟨a, ha⟩
  · intro a ha k u v
    simpa only [H, dif_pos ha] using hinner ⟨a, ha⟩ k u v
  · intro a ha k u v
    apply metric_hasDerivWithinAt_fst_of_local_product S hS
      (fun y : K × O => phi (y.1.1, y.2.1)) hPhi H
      (fun _ => (euclideanMetric (E := ℝ)).restrictOpen O) ha (hT ha) ?_ k ⟨0, hO₀⟩ u v
    intro b hb
    simpa only [H, dif_pos hb] using hmetric ⟨b, hb⟩

end DifferentialGeometry.PDE.RicciFlow

end
