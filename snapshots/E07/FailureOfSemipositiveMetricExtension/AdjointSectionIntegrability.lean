import FailureOfSemipositiveMetricExtension.FixedFiberCanonicalAdjoint
import FailureOfSemipositiveMetricExtension.CentralSectionIntegrability
import FailureOfSemipositiveMetricExtension.CentralMultiplierSheaf
import FailureOfSemipositiveMetricExtension.CentralRestrictionIntegrability

/-! The actual canonical-times-L^4 section has the required weighted local
integrability. Both its genuine local-ring germs and its actual chart densities
are connected to the canonical frame coefficient, including the unit frame change. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
noncomputable section
open Set MeasureTheory TopologicalSpace IsManifold
open scoped Manifold ContDiff

def canonicalFactorSection (d : DivisionIndex) :
    C^∞⟮𝓘(ℂ,FixedFiber.Coord),divisionOpen d;𝓘(ℂ),ℂ⟯ :=
  functionSectionOn (divisionOpen d) (canonicalFactor 0 d) (canonicalFactor_contMDiffOn 0 d)

def sigmaAdjointCoefficientSection (d : DivisionIndex) :
    C^∞⟮𝓘(ℂ,FixedFiber.Coord),divisionOpen d;𝓘(ℂ),ℂ⟯ :=
  functionSectionOn (divisionOpen d) (sigmaAdjointCoefficient d) (sigmaAdjointCoefficient_analytic d)

def canonicalFactorGerm (d : DivisionIndex) (p : Fiber 0) (hp : p ∈ divisionPatch 0 d) :
    HolomorphicStalk 0 p :=
  (holomorphicSheaf 0).presheaf.germ (divisionOpen d) p hp (canonicalFactorSection d)

def sigmaAdjointGerm (d : DivisionIndex) (p : Fiber 0) (hp : p ∈ divisionPatch 0 d) :
    HolomorphicStalk 0 p :=
  (holomorphicSheaf 0).presheaf.germ (divisionOpen d) p hp (sigmaAdjointCoefficientSection d)

theorem canonicalFactorGerm_isUnit (d : DivisionIndex) (p : Fiber 0)
    (hp : p ∈ divisionPatch 0 d) : IsUnit (canonicalFactorGerm d p hp) := by
  rw [smoothSheafCommRing.isUnit_stalk_iff,RingHom.mem_ker]
  unfold canonicalFactorGerm holomorphicSheaf
  rw [smoothSheafCommRing.eval_germ]
  exact canonicalFactor_ne_zero 0 d p hp

theorem sigmaAdjointGerm_factorization (d : DivisionIndex) (p : Fiber 0)
    (hp : p ∈ divisionPatch 0 d) :
    sigmaAdjointGerm d p hp = canonicalFactorGerm d p hp *
      sectionGerm sigmaSection (divisionFrame d) p hp.2 := by
  rw [sectionGerm_eq_restrict sigmaSection (divisionFrame d) p hp.2
    (divisionOpen d) (divisionPatch_subset_frame 0 d) hp]
  unfold sigmaAdjointGerm canonicalFactorGerm
  rw [← map_mul]
  congr 1

theorem sigmaAdjointGerm_mem_ellSquare (d : DivisionIndex) (p : Fiber 0)
    (hp : p ∈ divisionPatch 0 d) : sigmaAdjointGerm d p hp ∈ ellPowerStalkIdeal 2 p := by
  rw [sigmaAdjointGerm_factorization]
  exact (ellPowerStalkIdeal 2 p).mul_mem_left _
    (sigmaSection_germ_mem_ellSquare (divisionFrame d) p hp.2)

theorem sigmaAdjointGerm_weighted_integrable (d : DivisionIndex) (p : Fiber 0)
    (hp : p ∈ divisionPatch 0 d) :
    FailureOfSemipositiveMetricExtension.Multiplier.IntegrableGerm (Fiber 0) 4
      (centralH0.weight (divisionFrame d)) p (sigmaAdjointGerm d p hp) := by
  rw [centralH0_multiplierGerm_iff 4 (divisionFrame d) p hp.2]
  exact sigmaAdjointGerm_mem_ellSquare d p hp

def sigmaAdjointWeightedDensity (d : DivisionIndex) (p : Fiber 0) : ℝ :=
  Complex.normSq (sigmaAdjointCoefficient d p) * Real.exp (-4*centralH0RealWeight (divisionFrame d) p)

def sigmaAdjointRegularDensity (d : DivisionIndex) (p : Fiber 0) : ℝ :=
  Complex.normSq (canonicalFactor 0 d p) * sigmaRegularDensity (divisionFrame d) p

theorem sigmaAdjointWeightedDensity_eq_regular (d : DivisionIndex) (p : Fiber 0)
    (hp : p ∈ divisionPatch 0 d) (hz : ellSection.coefficient (divisionFrame d) p ≠ 0) :
    sigmaAdjointWeightedDensity d p = sigmaAdjointRegularDensity d p := by
  unfold sigmaAdjointWeightedDensity sigmaAdjointCoefficient
  rw [Complex.normSq_mul,mul_assoc]
  change Complex.normSq (canonicalFactor 0 d p) * sigmaWeightedDensity (divisionFrame d) p = _
  rw [sigmaWeightedDensity_eq_regular (divisionFrame d) p hp.2 hz]
  rfl

theorem sigmaAdjointRegularDensity_continuousOn (d : DivisionIndex) :
    ContinuousOn (sigmaAdjointRegularDensity d) (divisionPatch 0 d) :=
  ((Complex.continuous_normSq.comp_continuousOn (canonicalFactor_contMDiffOn 0 d).continuousOn).mul
    ((sigmaRegularDensity_contMDiffOn (divisionFrame d)).continuousOn.mono (divisionPatch_subset_frame 0 d)))

/-- Genuine local Lebesgue integrability of the actual adjoint coefficient. -/
theorem sigmaAdjointWeightedDensity_integrableOn (d : DivisionIndex)
    (K : Set FixedFiber.Coord) (hK : IsCompact K)
    (hd : K ⊆ FixedFiber.domain 0 d.1 d.2.1)
    (hp : MapsTo (FixedFiber.param 0 d.1 d.2.1) K (divisionPatch 0 d)) :
    IntegrableOn (fun q => sigmaAdjointWeightedDensity d (FixedFiber.param 0 d.1 d.2.1 q)) K volume := by
  have hr : IntegrableOn (fun q => sigmaAdjointRegularDensity d (FixedFiber.param 0 d.1 d.2.1 q)) K volume :=
    ((sigmaAdjointRegularDensity_continuousOn d).comp
      ((FixedFiber.param_contMDiffOn 0 d.1 d.2.1 0).continuousOn.mono hd) hp).integrableOn_compact hK
  apply hr.congr_fun_ae
  have hn : ∀ᵐ q : FixedFiber.Coord, q.2 ≠ 0 := by
    simpa only [ae_iff,not_not] using complex_coordinate_hyperplane_null
  filter_upwards [ae_restrict_of_ae hn,ae_restrict_mem hK.measurableSet] with q hq hqK
  symm
  apply sigmaAdjointWeightedDensity_eq_regular d _ (hp hqK)
  intro hz
  have hv := (sectionValue_zero_iff ellSection (divisionFrame d) _ (hp hqK).2).mpr hz
  exact hq ((ellSection_zero_iff_param d.1 d.2.1 q (hd hqK)).mp hv).2.2

/-- Every central point admits an actual positive-radius chart ball on which
sigma as a canonical-times-L^4 form has finite weighted Lebesgue norm. -/
theorem sigmaAdjointWeightedDensity_locally_integrable (p : Fiber 0) :
    ∃ (d : DivisionIndex) (q : FixedFiber.Coord) (ε : ℝ), 0 < ε ∧
      FixedFiber.param 0 d.1 d.2.1 q = p ∧
      Metric.closedBall q ε ⊆ FixedFiber.domain 0 d.1 d.2.1 ∧
      MapsTo (FixedFiber.param 0 d.1 d.2.1) (Metric.closedBall q ε) (divisionPatch 0 d) ∧
      IntegrableOn (fun z => sigmaAdjointWeightedDensity d (FixedFiber.param 0 d.1 d.2.1 z))
        (Metric.closedBall q ε) volume := by
  let d := (adjointCore 0 4).indexAt p
  have hp : p ∈ divisionPatch 0 d := (adjointCore 0 4).mem_baseSet_at p
  let q := FixedFiber.coordinates 0 d.1 d.2.1 p
  have hq : q ∈ FixedFiber.domain 0 d.1 d.2.1 := (FixedFiber.chart 0 d.1 d.2.1).map_source hp.1
  have heq : FixedFiber.param 0 d.1 d.2.1 q = p := FixedFiber.param_coordinates 0 d.1 d.2.1 p hp.1
  have hO := (FixedFiber.chart 0 d.1 d.2.1).isOpen_inter_preimage_symm (divisionPatch_isOpen 0 d)
  have hqO : q ∈ FixedFiber.domain 0 d.1 d.2.1 ∩ FixedFiber.param 0 d.1 d.2.1 ⁻¹' divisionPatch 0 d :=
    ⟨hq,by change FixedFiber.param 0 d.1 d.2.1 q ∈ divisionPatch 0 d; rwa [heq]⟩
  obtain ⟨ε,hε,hεO⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hO.mem_nhds hqO)
  have hd : Metric.closedBall q ε ⊆ FixedFiber.domain 0 d.1 d.2.1 := fun _ h => (hεO h).1
  have hf : MapsTo (FixedFiber.param 0 d.1 d.2.1) (Metric.closedBall q ε) (divisionPatch 0 d) :=
    fun _ h => (hεO h).2
  exact ⟨d,q,ε,hε,heq,hd,hf,sigmaAdjointWeightedDensity_integrableOn d _ (isCompact_closedBall q ε) hd hf⟩

/-- The exact one-sided extension comparison preserves the actual adjoint germ. -/
theorem sigmaAdjointGerm_integrable_of_extension_comparison
    {U : Opens Total} (h : FailureOfSemipositiveMetricExtension.GlobalLineBundle.SingularWeightOn U (-2) (fun _ => 1))
    (hc : h.centralDominatesH0) (d : DivisionIndex) (p : Fiber 0) (hp : p ∈ divisionPatch 0 d) :
    FailureOfSemipositiveMetricExtension.Multiplier.IntegrableGerm (Fiber 0) 4
      (fun q => h.weight (divisionFrame d) (FixedFiber.inclusion 0 q)) p (sigmaAdjointGerm d p hp) := by
  obtain ⟨C,hC⟩ := hc
  exact FailureOfSemipositiveMetricExtension.Multiplier.IntegrableGerm.mono_of_local_comparison (Fiber 0) 4 _ _ p _ C
    (frameOpen 0 (divisionFrame d)) hp.2 (hC (divisionFrame d))
    (sigmaAdjointGerm_weighted_integrable d p hp)

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
