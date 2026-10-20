import FailureOfSemipositiveMetricExtension.GeneralKahlerForms
import Mathlib.LinearAlgebra.Basis.Fin

/-! Review-only, full-dimensional Cao interface with a genuine Kähler form.
The map is proper to the OPEN DISC, not to C. Adapted charts are only required
near the central fibre, so singular noncentral fibres are not excluded. The
conclusion is a section on the WHOLE total space, not a shrunken neighbourhood.
No theorem of this interface is asserted in this file. -/
namespace FailureOfSemipositiveMetricExtension.GeneralCao
noncomputable section
open Set Topology TopologicalSpace Bundle IsManifold Manifold
open scoped Manifold ContDiff ENNReal

abbrev Coord (n : ℕ) := Fin n → ℂ
abbrev Disc := {t : ℂ // ‖t‖ < 1}

def coordinateVolume (n : ℕ) : Coord n [⋀^Fin n]→ₗ[ℂ] ℂ := (Pi.basisFun ℂ (Fin n)).det

theorem coordinateVolume_basis (n : ℕ) : coordinateVolume n (Pi.basisFun ℂ (Fin n)) = 1 :=
  Basis.det_self _

variable (n : ℕ) (M N : Type) [TopologicalSpace M] [ChartedSpace (Coord (n+1)) M]
    [TopologicalSpace N] [ChartedSpace (Coord n) N]

/-- A proper family with only its smooth reduced central fibre adapted. -/
structure Family (A B : Type) where
  projection : M → Disc
  projection_analytic : ContMDiff 𝓘(ℂ,Coord (n+1)) 𝓘(ℂ) ω (fun p => (projection p : ℂ))
  projection_proper : IsProperMap projection
  inclusion : N → M
  inclusion_analytic : ContMDiff 𝓘(ℂ,Coord n) 𝓘(ℂ,Coord (n+1)) ω inclusion
  inclusion_closedEmbedding : IsClosedEmbedding inclusion
  central_range : Set.range inclusion = {p | (projection p : ℂ) = 0}
  totalAtlas : CaoExtensionInterface.AnalyticAtlas (Coord (n+1)) M B
  centralAtlas : CaoExtensionInterface.AnalyticAtlas (Coord n) N A
  adaptedChart : A → GeneralMultiplier.AnalyticCoordinate (n+1) M
  central_source : ∀ a, (centralAtlas.chart a).source = inclusion ⁻¹' (adaptedChart a).chart.source
  adapted_parameter : ∀ a p, p ∈ (adaptedChart a).chart.source →
    (projection p : ℂ) = (adaptedChart a).chart p (Fin.last n)
  adapted_inclusion : ∀ a p, p ∈ (centralAtlas.chart a).source →
    (adaptedChart a).chart (inclusion p) = Fin.snoc (centralAtlas.chart a p) 0

variable {M N}

/-- Compactness of the true central manifold follows from properness to the
open disc and the actual closed embedding; it is not an extra geometric input. -/
theorem Family.central_compact {A B : Type} (G : Family n M N A B) : CompactSpace N := by
  let zeroDisc : Disc := ⟨0,by simp⟩
  have he : G.projection ⁻¹' {zeroDisc} = Set.range G.inclusion := by
    rw [G.central_range]
    ext p
    simp only [Set.mem_preimage,Set.mem_singleton_iff,Set.mem_setOf_eq]
    exact ⟨fun h => congrArg Subtype.val h,fun h => Subtype.ext h⟩
  have hc : IsCompact (Set.range G.inclusion) := by
    rw [← he]
    exact G.projection_proper.isCompact_preimage isCompact_singleton
  have hn : IsCompact (Set.univ : Set N) := by
    apply G.inclusion_closedEmbedding.isEmbedding.isCompact_iff.mpr
    simpa only [Set.image_univ] using hc
  exact ⟨hn⟩

structure AnalyticLine (J : Type) where
  core : VectorBundleCore ℂ M ℂ J
  analytic : core.IsContMDiff 𝓘(ℂ,Coord (n+1)) ω
  gain : J → J → M → ℂ
  coordChange_eq : ∀ i j p z, core.coordChange i j p z = gain i j p * z

variable {A B J : Type} (G : Family n M N A B) (L : AnalyticLine n (M := M) J)

def totalPatch (b : B) (i : J) : Opens M :=
  ⟨(G.totalAtlas.chart b).source ∩ L.core.baseSet i,
    (G.totalAtlas.chart b).open_source.inter (L.core.isOpen_baseSet i)⟩

def centralPatch (a : A) (i : J) : Opens N :=
  ⟨(G.centralAtlas.chart a).source ∩ G.inclusion ⁻¹' L.core.baseSet i,
    (G.centralAtlas.chart a).open_source.inter
      ((L.core.isOpen_baseSet i).preimage G.inclusion_analytic.continuous)⟩

abbrev TotalForm := ∀ p : M,
  (TangentSpace 𝓘(ℂ,Coord (n+1)) p) [⋀^Fin (n+1)]→ₗ[ℂ] L.core.Fiber p
abbrev CentralForm := ∀ p : N,
  (TangentSpace 𝓘(ℂ,Coord n) p) [⋀^Fin n]→ₗ[ℂ] L.core.Fiber (G.inclusion p)

structure TotalAdjointSection where
  form : TotalForm n L
  coefficient : B → J → M → ℂ
  analytic : ∀ b i, ContMDiffOn 𝓘(ℂ,Coord (n+1)) 𝓘(ℂ) ω
    (coefficient b i) (totalPatch n G L b i)
  represents : ∀ b i p, p ∈ totalPatch n G L b i →
    ∀ v : Fin (n+1) → TangentSpace 𝓘(ℂ,Coord (n+1)) p,
      (L.core.localTriv i ⟨p,form p v⟩).2 = coefficient b i p *
        coordinateVolume (n+1)
          (fun k => mfderiv 𝓘(ℂ,Coord (n+1)) 𝓘(ℂ,Coord (n+1)) (G.totalAtlas.chart b) p (v k))

structure CentralAdjointSection where
  form : CentralForm n G L
  coefficient : A → J → N → ℂ
  analytic : ∀ a i, ContMDiffOn 𝓘(ℂ,Coord n) 𝓘(ℂ) ω
    (coefficient a i) (centralPatch n G L a i)
  represents : ∀ a i p, p ∈ centralPatch n G L a i →
    ∀ v : Fin n → TangentSpace 𝓘(ℂ,Coord n) p,
      (L.core.localTriv i ⟨G.inclusion p,form p v⟩).2 = coefficient a i p *
        coordinateVolume n
          (fun k => mfderiv 𝓘(ℂ,Coord n) 𝓘(ℂ,Coord n) (G.centralAtlas.chart a) p (v k))

structure SemipositiveWeight where
  weight : J → M → WithBot ℝ
  compatible : ∀ i j p, p ∈ L.core.baseSet i ∩ L.core.baseSet j →
    weight j p = weight i p + (Real.log (Complex.normSq (L.gain i j p)) : ℝ)
  psh : ∀ b i, PlurisubharmonicOn
    (fun z => weight i ((G.totalAtlas.chart b).symm z))
    ((G.totalAtlas.chart b).target ∩ (G.totalAtlas.chart b).symm ⁻¹' L.core.baseSet i)
  /-- Standard singular metrics exclude a whole open set of infinite norm.
  Together with psh this is equivalent to local integrability of the weights. -/
  finite_points_dense : ∀ i p, p ∈ L.core.baseSet i →
    p ∈ closure {q | q ∈ L.core.baseSet i ∧ weight i q ≠ ⊥}

def RestrictionWellDefined (h : SemipositiveWeight n G L) : Prop :=
  ∀ p : N, ∃ q ∈ connectedComponent p, ∃ i : J,
    G.inclusion q ∈ L.core.baseSet i ∧ h.weight i (G.inclusion q) ≠ ⊥

def centralCoefficientSection (s : CentralAdjointSection n G L) (a : A) (i : J) :
    C^∞⟮𝓘(ℂ,Coord n),centralPatch n G L a i;𝓘(ℂ),ℂ⟯ :=
  ⟨fun p => s.coefficient a i p,by
    intro p
    apply contMDiffAt_subtype_iff.mpr
    exact ((s.analytic a i).of_le le_top).contMDiffAt
      ((centralPatch n G L a i).isOpen.mem_nhds p.2)⟩

def InRestrictedMultiplier (h : SemipositiveWeight n G L)
    (s : CentralAdjointSection n G L) : Prop :=
  ∀ (a : A) (i : J) (p : N) (hp : p ∈ centralPatch n G L a i),
    GeneralMultiplier.IntegrableGerm n N 1 (fun q => h.weight i (G.inclusion q)) p
      ((GeneralMultiplier.sheaf n N).presheaf.germ (centralPatch n G L a i) p hp
        (centralCoefficientSection n G L s a i))

/-- NORMAL LAST: no even-dimensional sign shortcut is valid here. -/
def RestrictsByDt (S : TotalAdjointSection n G L) (s : CentralAdjointSection n G L) : Prop :=
  ∀ (p : N) (ν : TangentSpace 𝓘(ℂ,Coord (n+1)) (G.inclusion p)),
    mfderiv 𝓘(ℂ,Coord (n+1)) 𝓘(ℂ) (fun x => (G.projection x : ℂ)) (G.inclusion p) ν = (1 : ℂ) →
      ∀ v : Fin n → TangentSpace 𝓘(ℂ,Coord n) p,
        S.form (G.inclusion p) (Fin.snoc
          (fun k => mfderiv 𝓘(ℂ,Coord n) 𝓘(ℂ,Coord (n+1)) G.inclusion p (v k)) ν) = s.form p v

/-- Full-dimensional, global existence-only Cao corollary candidate. -/
def ExtensionStatement [T2Space M] [SecondCountableTopology M]
    [IsManifold 𝓘(ℂ,Coord (n+1)) ω M]
    [T2Space N] [SecondCountableTopology N] [CompactSpace N]
    [IsManifold 𝓘(ℂ,Coord n) ω N] : Prop :=
  ∀ (_kahler : GeneralKahler.KahlerForm G.totalAtlas)
    (h : SemipositiveWeight n G L), RestrictionWellDefined n G L h →
    ∀ s : CentralAdjointSection n G L, InRestrictedMultiplier n G L h s →
      ∃ S : TotalAdjointSection n G L, RestrictsByDt n G L S s

end
end FailureOfSemipositiveMetricExtension.GeneralCao
