import FailureOfSemipositiveMetricExtension.GlobalAmbientImmersion
import FailureOfSemipositiveMetricExtension.ComplexThreefoldJacobian
import FailureOfSemipositiveMetricExtension.MultiplierGerms
import FailureOfSemipositiveMetricExtension.Plurisubharmonic
import FailureOfSemipositiveMetricExtension.GlobalAnalyticLineBundle
import FailureOfSemipositiveMetricExtension.FixedFiberCanonicalForms

/-!
REVIEW-ONLY candidate interface, not an admitted theorem or an axiom.

The proposition at the end is an existence-only corollary proposed for review
against Cao, arXiv:1404.6937v2, Theorem 1.1, printed page 1. Its projective
immersion hypothesis encodes a separate standard Kaehler pullback argument.
No instance of the proposition is supplied, and it is not imported by the root.
See docs/cao_extension_interface_review.md for every translation boundary.
-/
namespace FailureOfSemipositiveMetricExtension.CaoExtensionInterface
noncomputable section
open Set Topology TopologicalSpace Bundle IsManifold Manifold
open scoped Manifold ContDiff ENNReal

abbrev SurfaceCoord := ℂ × ℂ
abbrev TotalCoord := (ℂ × ℂ) × ℂ

variable (M N : Type) [TopologicalSpace M] [ChartedSpace TotalCoord M]
    [TopologicalSpace N] [ChartedSpace SurfaceCoord N]

/-- Actual analytic coordinate maps, with verified inverses and coverage. -/
structure AnalyticAtlas (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (X : Type) [TopologicalSpace X] [ChartedSpace E X] (A : Type) where
  chart : A → PartialHomeomorph X E
  forward : ∀ a, ContMDiffOn 𝓘(ℂ,E) 𝓘(ℂ,E) ω (chart a) (chart a).source
  inverse : ∀ a, ContMDiffOn 𝓘(ℂ,E) 𝓘(ℂ,E) ω (chart a).symm (chart a).target
  cover : ∀ x, ∃ a, x ∈ (chart a).source

/-- Generic family data. Properness is over the entire complex line; this is a
stronger special case than Cao's properness over a disc, and suffices here. The
adapted atlases make every fibre locally reduced, with the parameter last. -/
structure AdaptedFamily (A : Type) where
  projection : M → ℂ
  projection_analytic : ContMDiff 𝓘(ℂ,TotalCoord) 𝓘(ℂ) ω projection
  projection_proper : IsProperMap projection
  inclusion : N → M
  inclusion_analytic : ContMDiff 𝓘(ℂ,SurfaceCoord) 𝓘(ℂ,TotalCoord) ω inclusion
  inclusion_closedEmbedding : IsClosedEmbedding inclusion
  central_range : Set.range inclusion = projection ⁻¹' {0}
  totalAtlas : AnalyticAtlas TotalCoord M A
  centralAtlas : AnalyticAtlas SurfaceCoord N A
  central_source : ∀ a, (centralAtlas.chart a).source = inclusion ⁻¹' (totalAtlas.chart a).source
  adapted_parameter : ∀ a p, p ∈ (totalAtlas.chart a).source →
    projection p = (totalAtlas.chart a p).2
  adapted_inclusion : ∀ a p, p ∈ (centralAtlas.chart a).source →
    totalAtlas.chart a (inclusion p) = (centralAtlas.chart a p,0)

variable {M N}

/-- Explicit finite projective immersion data: all components are maps to actual
projectivizations, and their joint actual complex tangent map is injective.
This is concrete input for the standard Fubini--Study plus Euclidean pullback
Kaehler argument, not an opaque assumption that this particular M is Kaehler. -/
structure ProjectiveImmersion where
  planeCount : ℕ
  lineCount : ℕ
  plane : Fin planeCount → M → ProjectivePlane.Point
  line : Fin lineCount → M → ProjectiveLine.Point
  affine : M → ℂ
  plane_analytic : ∀ i, ContMDiff 𝓘(ℂ,TotalCoord) 𝓘(ℂ,ℂ × ℂ) ω (plane i)
  line_analytic : ∀ i, ContMDiff 𝓘(ℂ,TotalCoord) 𝓘(ℂ) ω (line i)
  affine_analytic : ContMDiff 𝓘(ℂ,TotalCoord) 𝓘(ℂ) ω affine
  joint_tangent_injective : ∀ p, Function.Injective
    (fun v : TangentSpace 𝓘(ℂ,TotalCoord) p =>
      ((fun i => mfderiv 𝓘(ℂ,TotalCoord) 𝓘(ℂ,ℂ × ℂ) (plane i) p v),
       (fun i => mfderiv 𝓘(ℂ,TotalCoord) 𝓘(ℂ) (line i) p v),
       mfderiv 𝓘(ℂ,TotalCoord) 𝓘(ℂ) affine p v))

/-- A genuine complex analytic line-bundle core, with its scalar coefficient
transition convention stated explicitly: c_j = gain(i,j) * c_i. -/
structure AnalyticLineBundle (J : Type) where
  core : VectorBundleCore ℂ M ℂ J
  analytic : core.IsContMDiff 𝓘(ℂ,TotalCoord) ω
  gain : J → J → M → ℂ
  coordChange_eq : ∀ i j p z, core.coordChange i j p z = gain i j p * z

variable {A J : Type} (G : AdaptedFamily M N A) (L : AnalyticLineBundle (M := M) J)

def totalPatch (U : Opens M) (a : A) (i : J) : Opens M :=
  ⟨(G.totalAtlas.chart a).source ∩ L.core.baseSet i ∩ U,
    ((G.totalAtlas.chart a).open_source.inter (L.core.isOpen_baseSet i)).inter U.isOpen⟩

def centralPatch (a : A) (i : J) : Opens N :=
  ⟨(G.centralAtlas.chart a).source ∩ G.inclusion ⁻¹' L.core.baseSet i,
    (G.centralAtlas.chart a).open_source.inter
      ((L.core.isOpen_baseSet i).preimage G.inclusion_analytic.continuous)⟩

/-- Actual L-valued top forms, rather than an unspecified adjoint section type. -/
abbrev TotalForm := ∀ p : M,
  (TangentSpace 𝓘(ℂ,TotalCoord) p) [⋀^Fin 3]→ₗ[ℂ] L.core.Fiber p
abbrev CentralForm := ∀ p : N,
  (TangentSpace 𝓘(ℂ,SurfaceCoord) p) [⋀^Fin 2]→ₗ[ℂ] L.core.Fiber (G.inclusion p)

/-- Analyticity is in actual holomorphic bundle frames and coordinate volume
forms. The representation equation supplies the true K_M tensor L semantics. -/
structure TotalAdjointSection (U : Opens M) where
  form : TotalForm L
  coefficient : A → J → M → ℂ
  analytic : ∀ a i, ContMDiffOn 𝓘(ℂ,TotalCoord) 𝓘(ℂ) ω
    (coefficient a i) (totalPatch G L U a i)
  represents : ∀ a i p, p ∈ totalPatch G L U a i →
    ∀ v : Fin 3 → TangentSpace 𝓘(ℂ,TotalCoord) p,
      (L.core.localTriv i ⟨p,form p v⟩).2 = coefficient a i p *
        ComplexThreefoldJacobian.coordinateVolume
          (fun k => mfderiv 𝓘(ℂ,TotalCoord) 𝓘(ℂ,TotalCoord) (G.totalAtlas.chart a) p (v k))

/-- Genuine central K_N tensor j*L sections, using the same actual L frames. -/
structure CentralAdjointSection where
  form : CentralForm G L
  coefficient : A → J → N → ℂ
  analytic : ∀ a i, ContMDiffOn 𝓘(ℂ,SurfaceCoord) 𝓘(ℂ) ω
    (coefficient a i) (centralPatch G L a i)
  represents : ∀ a i p, p ∈ centralPatch G L a i →
    ∀ v : Fin 2 → TangentSpace 𝓘(ℂ,SurfaceCoord) p,
      (L.core.localTriv i ⟨G.inclusion p,form p v⟩).2 = coefficient a i p *
        ComplexSurfaceJacobian.coordinateVolume
          (fun k => mfderiv 𝓘(ℂ,SurfaceCoord) 𝓘(ℂ,SurfaceCoord) (G.centralAtlas.chart a) p (v k))

/-- Weights use squared norms |c|² exp(-weight). In particular the positive
log-norm transition sign is forced by the declared coefficient convention. -/
structure SemipositiveWeightOn (U : Opens M) where
  weight : J → M → WithBot ℝ
  compatible : ∀ i j p, p ∈ U → p ∈ L.core.baseSet i ∩ L.core.baseSet j →
    weight j p = weight i p + (Real.log (Complex.normSq (L.gain i j p)) : ℝ)
  psh : ∀ a i, PlurisubharmonicOn
    (fun z => weight i ((G.totalAtlas.chart a).symm z))
    ((G.totalAtlas.chart a).target ∩ (G.totalAtlas.chart a).symm ⁻¹' (L.core.baseSet i ∩ U))

/-- A deliberately explicit well-defined restriction condition, on every
connected component. This avoids silently assuming a connected central fibre. -/
def RestrictionWellDefined {U : Opens M} (h : SemipositiveWeightOn G L U) : Prop :=
  ∀ p : N, ∃ q : N, q ∈ connectedComponent p ∧
    ∃ i : J, G.inclusion q ∈ L.core.baseSet i ∧ h.weight i (G.inclusion q) ≠ ⊥

def centralCoefficientSection (s : CentralAdjointSection G L) (a : A) (i : J) :
    C^∞⟮𝓘(ℂ,SurfaceCoord),centralPatch G L a i;𝓘(ℂ),ℂ⟯ :=
  ⟨fun p => s.coefficient a i p,by
    intro p
    apply contMDiffAt_subtype_iff.mpr
    exact ((s.analytic a i).of_le le_top).contMDiffAt
      ((centralPatch G L a i).isOpen.mem_nhds p.2)⟩

/-- The hypothesis is membership of the actual restricted weighted-integrable
germ, with a real holomorphic representative and a genuine local Lebesgue
integral. There is no invented global norm or unspecified multiplier predicate. -/
def InRestrictedMultiplier {U : Opens M} (h : SemipositiveWeightOn G L U)
    (s : CentralAdjointSection G L) : Prop :=
  ∀ (a : A) (i : J) (p : N) (hp : p ∈ centralPatch G L a i),
    Multiplier.IntegrableGerm N 1 (fun q => h.weight i (G.inclusion q)) p
      ((Multiplier.sheaf N).presheaf.germ (centralPatch G L a i) p hp
        (centralCoefficientSection G L s a i))

def discDomain (r : ℝ) : Opens M :=
  ⟨G.projection ⁻¹' Metric.ball (0 : ℂ) r,
    Metric.isOpen_ball.preimage G.projection_analytic.continuous⟩

/-- Actual dt-adjunction: contract an L-valued three-form by a normal of dπ=1
and apply it to the actual inclusion derivative. With two vertical arguments,
normal-first has the same sign as dz1 ∧ dz2 ∧ dt. -/
def RestrictsByDt {U : Opens M} (S : TotalAdjointSection G L U)
    (s : CentralAdjointSection G L) : Prop :=
  ∀ (p : N) (ν : TangentSpace 𝓘(ℂ,TotalCoord) (G.inclusion p)),
    mfderiv 𝓘(ℂ,TotalCoord) 𝓘(ℂ) G.projection (G.inclusion p) ν = (show ℂ from 1) →
      ((S.form (G.inclusion p)).curryLeft ν).compLinearMap
        (mfderiv 𝓘(ℂ,SurfaceCoord) 𝓘(ℂ,TotalCoord) G.inclusion p).toLinearMap = s.form p

/-- REVIEW-ONLY proposition. This definition asserts no theorem and supplies no
proof. It is a universal Cao existence corollary candidate, not a proposition
about the paper's particular family, line bundle, metric or distinguished section. -/
def ExtensionStatement [T2Space M] [SecondCountableTopology M]
    [IsManifold 𝓘(ℂ,TotalCoord) ω M]
    [T2Space N] [SecondCountableTopology N] [CompactSpace N]
    [IsManifold 𝓘(ℂ,SurfaceCoord) ω N] : Prop :=
  ∀ (_immersion : ProjectiveImmersion (M := M)) (U : Opens M),
    (∀ p : N, G.inclusion p ∈ U) →
    ∀ h : SemipositiveWeightOn G L U, RestrictionWellDefined G L h →
    ∀ s : CentralAdjointSection G L, InRestrictedMultiplier G L h s →
      ∃ r : ℝ, 0 < r ∧ (discDomain G r : Set M) ⊆ U ∧
        ∃ S : TotalAdjointSection G L (discDomain G r), RestrictsByDt G L S s

end
end FailureOfSemipositiveMetricExtension.CaoExtensionInterface
