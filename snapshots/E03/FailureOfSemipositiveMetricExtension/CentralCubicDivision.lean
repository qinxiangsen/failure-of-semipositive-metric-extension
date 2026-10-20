import FailureOfSemipositiveMetricExtension.CentralExceptionalProduct
import FailureOfSemipositiveMetricExtension.GlobalFiberSectionDivision

/-! The four actual analytic sections of A = 3H-E₀-E₁-E₂-2E₃ on the central
compact complex surface.  Exceptional division is proved on a verified open cover,
and the resulting sections have no common zero anywhere on the surface. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
noncomputable section
open Set Bundle IsManifold
open scoped Manifold ContDiff

def cubicLocalQuotient (k : Fin 4) (d : DivisionIndex) (p : Fiber 0) : ℂ :=
  cubicLocalCoefficient d.1 d.2.1 k (FixedFiber.coordinates 0 d.1 d.2.1 p) /
    cubicOtherDenominator d p

theorem cubicLocalQuotient_contMDiffOn (k : Fin 4) (d : DivisionIndex) :
    ContMDiffOn 𝓘(ℂ,FixedFiber.Coord) 𝓘(ℂ) ω (cubicLocalQuotient k d) (divisionPatch 0 d) := by
  have hn : ContMDiffOn 𝓘(ℂ,FixedFiber.Coord) 𝓘(ℂ) ω
      (fun p => cubicLocalCoefficient d.1 d.2.1 k (FixedFiber.coordinates 0 d.1 d.2.1 p))
      (divisionPatch 0 d) :=
    (cubicLocalCoefficient_contDiff d.1 d.2.1 k).contMDiff.comp_contMDiffOn
      ((FixedFiber.coordinates_contMDiffOn 0 d.1 d.2.1 ω).mono
        (divisionPatch_subset_source 0 d))
  have hinv : ContDiffOn ℂ ω (fun z : ℂ => z⁻¹) {z | z ≠ 0} :=
    contDiffOn_id.inv (fun _ h => h)
  have hd : ContMDiffOn 𝓘(ℂ,FixedFiber.Coord) 𝓘(ℂ) ω
      (fun p => (cubicOtherDenominator d p)⁻¹) (divisionPatch 0 d) :=
    hinv.contMDiffOn.comp (cubicOtherDenominator_contMDiffOn d)
      (fun p hp => cubicOtherDenominator_ne_zero d p hp)
  simpa only [cubicLocalQuotient,div_eq_mul_inv,Function.comp_apply,smul_eq_mul] using hn.smul hd

theorem cubicLocalQuotient_identity (k : Fin 4) (d : DivisionIndex) (p : Fiber 0)
    (hp : p ∈ divisionPatch 0 d) :
    cubicLocalQuotient k d p * centralDenominator.coefficient (divisionFrame d) p =
      (centralNumerator k).coefficient (divisionFrame d) p := by
  have hD := cubicOtherDenominator_ne_zero d p hp
  have he : centralDenominator.coefficient (divisionFrame d) p =
      exceptionalCoefficient 0 d.1 (divisionFrame d) p ^ centralMultiplicity d.1 *
        cubicOtherDenominator d p := by
    rw [centralDenominator_coefficient]
    exact (Finset.mul_prod_erase Finset.univ
      (fun j => exceptionalCoefficient 0 j (divisionFrame d) p ^ centralMultiplicity j)
      (Finset.mem_univ d.1)).symm
  have hq := FixedFiber.param_coordinates 0 d.1 d.2.1 p hp.1
  have hE : exceptionalCoefficient 0 d.1 (divisionFrame d) p =
      (FixedFiber.coordinates 0 d.1 d.2.1 p).1 := by
    conv_lhs => rw [← hq]
    exact exceptionalCoefficient_param 0 d _
  have hN : (centralNumerator k).coefficient (divisionFrame d) p =
      (FixedFiber.coordinates 0 d.1 d.2.1 p).1 ^ centralMultiplicity d.1 *
        cubicLocalCoefficient d.1 d.2.1 k (FixedFiber.coordinates 0 d.1 d.2.1 p) := by
    conv_lhs => rw [← hq]
    exact centralCubicSections_param k d _
  rw [he,hE,hN]
  unfold cubicLocalQuotient
  field_simp
  ring

/-- The actual four analytic A-sections, obtained by exceptional division. -/
def liftedCentralCubics (k : Fin 4) : SectionData 0 (-2) centralADegree :=
  divideSections centralDenominator (centralNumerator k)
    (FixedFiber.awayCentres 0) (FixedFiber.awayCentres_dense 0) centralDenominator_ne_zero
    (divisionPatch 0) (divisionPatch_isOpen 0) (divisionPatch_cover 0)
    divisionFrame (divisionPatch_subset_frame 0) (cubicLocalQuotient k)
    (cubicLocalQuotient_contMDiffOn k) (cubicLocalQuotient_identity k)

theorem liftedCentralCubics_coefficient (k : Fin 4) (d : DivisionIndex) (p : Fiber 0)
    (hp : p ∈ divisionPatch 0 d) :
    (liftedCentralCubics k).coefficient (divisionFrame d) p = cubicLocalQuotient k d p := by
  have h := divideSections_coefficient (a := -2) (b := centralADegree)
    centralDenominator (centralNumerator k)
    (FixedFiber.awayCentres 0) (FixedFiber.awayCentres_dense 0) centralDenominator_ne_zero
    (divisionPatch 0) (divisionPatch_isOpen 0) (divisionPatch_cover 0)
    divisionFrame (divisionPatch_subset_frame 0) (cubicLocalQuotient k)
    (cubicLocalQuotient_contMDiffOn k) (cubicLocalQuotient_identity k) d (divisionFrame d) p hp hp.2
  simpa only [gain_self,one_mul] using h

theorem liftedCentralCubics_analytic (k : Fin 4) :
    ContMDiff 𝓘(ℂ,FixedFiber.Coord) (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) ω
      (sectionMap (liftedCentralCubics k)) := sectionMap_contMDiff _

/-- In every actual frame, multiplication by the exceptional denominator recovers the cubic. -/
theorem liftedCentralCubics_division (k : Fin 4) (i : Index) (p : Fiber 0)
    (hi : p ∈ baseSet 0 i) :
    (liftedCentralCubics k).coefficient i p * centralDenominator.coefficient i p =
      (centralCubicSections k).coefficient i p :=
  divideSections_mul_coefficient centralDenominator (centralNumerator k)
    (FixedFiber.awayCentres 0) (FixedFiber.awayCentres_dense 0) centralDenominator_ne_zero
    (divisionPatch 0) (divisionPatch_isOpen 0) (divisionPatch_cover 0)
    divisionFrame (divisionPatch_subset_frame 0) (cubicLocalQuotient k)
    (cubicLocalQuotient_contMDiffOn k) (cubicLocalQuotient_identity k) i p hi

/-- The genuine analytic section maps satisfy the global division identity. -/
theorem liftedCentralCubics_division_sectionMap (k : Fin 4) :
    sectionMap (multiplySections (liftedCentralCubics k) centralDenominator) =
      sectionMap (centralNumerator k) :=
  divideSections_mul_sectionMap centralDenominator (centralNumerator k)
    (FixedFiber.awayCentres 0) (FixedFiber.awayCentres_dense 0) centralDenominator_ne_zero
    (divisionPatch 0) (divisionPatch_isOpen 0) (divisionPatch_cover 0)
    divisionFrame (divisionPatch_subset_frame 0) (cubicLocalQuotient k)
    (cubicLocalQuotient_contMDiffOn k) (cubicLocalQuotient_identity k)

/-- The four actual A-sections have no common zero on the entire central fibre. -/
theorem liftedCentralCubics_basepoint_free (p : Fiber 0) :
    ∃ k : Fin 4, sectionValue (liftedCentralCubics k) p ≠ 0 := by
  obtain ⟨d,hp⟩ := divisionPatch_cover 0 p
  let q := FixedFiber.coordinates 0 d.1 d.2.1 p
  have hq : q ∈ FixedFiber.domain 0 d.1 d.2.1 :=
    (FixedFiber.chart 0 d.1 d.2.1).map_source hp.1
  obtain ⟨k,hk⟩ := cubicLocalCoefficient_no_common_zero d.1 d.2.1 q hq
  refine ⟨k,fun hz => ?_⟩
  have hc := (sectionValue_zero_iff (liftedCentralCubics k) (divisionFrame d) p hp.2).mp hz
  rw [liftedCentralCubics_coefficient k d p hp] at hc
  exact (div_ne_zero hk (cubicOtherDenominator_ne_zero d p hp)) hc

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
