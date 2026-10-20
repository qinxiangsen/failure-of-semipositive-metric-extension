import FailureOfSemipositiveMetricExtension.CentralDivisorIdeals

/-! The actual ell-power ideals have the expected normal-coordinate generator in
holomorphic stalks. The multiplier-ideal integrability equivalence remains separate. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
noncomputable section
open Set Bundle IsManifold Manifold TopologicalSpace Opposite CategoryTheory
open scoped Manifold ContDiff

def divisionOpen (d : DivisionIndex) : Opens (Fiber 0) := ⟨divisionPatch 0 d,divisionPatch_isOpen 0 d⟩

def functionSectionOn (U : Opens (Fiber 0)) (f : Fiber 0 → ℂ)
    (hf : ContMDiffOn 𝓘(ℂ,FixedFiber.Coord) 𝓘(ℂ) ω f U) :
    C^∞⟮𝓘(ℂ,FixedFiber.Coord),U;𝓘(ℂ),ℂ⟯ :=
  ⟨fun p => f p,by
    intro p
    apply contMDiffAt_subtype_iff.mpr
    exact (hf.of_le le_top).contMDiffAt (U.2.mem_nhds p.2)⟩

def normalCoordinateSection (d : DivisionIndex) :
    C^∞⟮𝓘(ℂ,FixedFiber.Coord),divisionOpen d;𝓘(ℂ),ℂ⟯ :=
  functionSectionOn (divisionOpen d) (fun p => (FixedFiber.coordinates 0 d.1 d.2.1 p).2)
    ((contDiff_snd.contMDiff.comp_contMDiffOn (FixedFiber.coordinates_contMDiffOn 0 d.1 d.2.1 ω)).mono (fun _ h => h.1))

def normalUnitSection (d : DivisionIndex) :
    C^∞⟮𝓘(ℂ,FixedFiber.Coord),divisionOpen d;𝓘(ℂ),ℂ⟯ :=
  functionSectionOn (divisionOpen d) (ellLocalUnit d) (ellLocalUnit_contMDiffOn d)

def normalCoordinateGerm (d : DivisionIndex) (p : Fiber 0) (hp : p ∈ divisionPatch 0 d) :
    HolomorphicStalk 0 p :=
  (holomorphicSheaf 0).presheaf.germ (divisionOpen d) p hp (normalCoordinateSection d)

def normalUnitGerm (d : DivisionIndex) (p : Fiber 0) (hp : p ∈ divisionPatch 0 d) :
    HolomorphicStalk 0 p :=
  (holomorphicSheaf 0).presheaf.germ (divisionOpen d) p hp (normalUnitSection d)

theorem normalUnitGerm_isUnit (d : DivisionIndex) (p : Fiber 0) (hp : p ∈ divisionPatch 0 d) :
    IsUnit (normalUnitGerm d p hp) := by
  rw [smoothSheafCommRing.isUnit_stalk_iff,RingHom.mem_ker]
  unfold normalUnitGerm holomorphicSheaf
  rw [smoothSheafCommRing.eval_germ]
  exact ellLocalUnit_ne_zero d p hp

theorem ellSection_germ_normal_factorization (d : DivisionIndex) (hr : d.1 ≠ 3)
    (he : d.2.1 = 0) (p : Fiber 0) (hp : p ∈ divisionPatch 0 d) :
    sectionGerm ellSection (divisionFrame d) p hp.2 =
      normalCoordinateGerm d p hp * normalUnitGerm d p hp := by
  rw [sectionGerm_eq_restrict ellSection (divisionFrame d) p hp.2 (divisionOpen d)
    (divisionPatch_subset_frame 0 d) hp]
  have hc : coefficientSectionOn ellSection (divisionFrame d) (divisionOpen d)
      (divisionPatch_subset_frame 0 d) = normalCoordinateSection d * normalUnitSection d := by
    apply Subtype.ext
    funext q
    exact ellSection_coefficient_simple d hr he q q.2
  rw [hc,map_mul]
  rfl

/-- Exact principal normal-coordinate ideal, for every nonnegative power. -/
theorem ellPowerStalkIdeal_normal (k : ℕ) (d : DivisionIndex) (hr : d.1 ≠ 3)
    (he : d.2.1 = 0) (p : Fiber 0) (hp : p ∈ divisionPatch 0 d) :
    ellPowerStalkIdeal k p = Ideal.span {(normalCoordinateGerm d p hp)^k} := by
  rw [ellPowerStalkIdeal,divisorPowerStalkIdeal_eq_frame ellSection k (divisionFrame d) p hp.2,
    ellSection_germ_normal_factorization d hr he p hp,mul_pow,
    Ideal.span_singleton_mul_right_unit ((normalUnitGerm_isUnit d p hp).pow k)]

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
