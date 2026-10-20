import FailureOfSemipositiveMetricExtension.GlobalSectionDivision
import FailureOfSemipositiveMetricExtension.GlobalExceptionalProduct
import FailureOfSemipositiveMetricExtension.GlobalPencilPullbacks

/-! Exceptional division produces the actual two global analytic sections of L.
Regularity at every exceptional point is established by the explicit chart polynomials. -/
namespace FailureOfSemipositiveMetricExtension.GlobalLineBundle
noncomputable section
open Set Bundle IsManifold FailureOfSemipositiveMetricExtension.GlobalIncidence
open scoped Manifold ContDiff

/-- Finite products of scalar analytic functions, without introducing additional manifold instances. -/
theorem scalarProduct_contMDiffOn {K : Type*} (S : Finset K) (U : Set Total)
    (f : K → Total → ℂ)
    (hf : ∀ k ∈ S, ContMDiffOn 𝓘(ℂ,ChartCoord) 𝓘(ℂ) ω (f k) U) :
    ContMDiffOn 𝓘(ℂ,ChartCoord) 𝓘(ℂ) ω (fun p => ∏ k ∈ S,f k p) U := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using (contMDiffOn_const (c := (1 : ℂ)))
  | @insert k S hk ih =>
    simp only [Finset.prod_insert hk]
    exact (hf k (Finset.mem_insert_self k S)).smul
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

def pencilOtherDenominator (d : DivisionIndex) (p : Total) : ℂ :=
  ∏ j ∈ Finset.univ.erase d.1,exceptionalCoefficient j (divisionFrame d) p

theorem pencilOtherDenominator_ne_zero (d : DivisionIndex) (p : Total)
    (hp : p ∈ divisionPatch d) : pencilOtherDenominator d p ≠ 0 := by
  unfold pencilOtherDenominator
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  intro hz
  exact divisionPatch_avoids_other_centres d p hp j (Finset.mem_erase.mp hj).1
    ((exceptionalCoefficient_zero_iff j (divisionFrame d) p hp.2).mp hz)

theorem pencilOtherDenominator_contMDiffOn (d : DivisionIndex) :
    ContMDiffOn 𝓘(ℂ,ChartCoord) 𝓘(ℂ) ω (pencilOtherDenominator d) (divisionPatch d) := by
  apply scalarProduct_contMDiffOn
  intro j _
  exact (exceptionalCoefficient_contMDiffOn j (divisionFrame d)).mono inter_subset_right

def pencilLocalQuotient (k : Fin 2) (d : DivisionIndex) (p : Total) : ℂ :=
  pencilLocalCoefficient d.1 d.2.1 k (chartCoordinates d.1 d.2.1 p) / pencilOtherDenominator d p

theorem pencilLocalQuotient_contMDiffOn (k : Fin 2) (d : DivisionIndex) :
    ContMDiffOn 𝓘(ℂ,ChartCoord) 𝓘(ℂ) ω (pencilLocalQuotient k d) (divisionPatch d) := by
  have hn : ContMDiffOn 𝓘(ℂ,ChartCoord) 𝓘(ℂ) ω
      (fun p => pencilLocalCoefficient d.1 d.2.1 k (chartCoordinates d.1 d.2.1 p)) (divisionPatch d) :=
    (pencilLocalCoefficient_contDiff d.1 d.2.1 k).contMDiff.comp_contMDiffOn
    ((chartCoordinates_contMDiffOn d.1 d.2.1 ω).mono
      (show divisionPatch d ⊆ chartSource d.1 d.2.1 from inter_subset_left))
  have hinv : ContDiffOn ℂ ω (fun z : ℂ => z⁻¹) {z | z ≠ 0} :=
    contDiffOn_id.inv (fun _ h => h)
  have hd : ContMDiffOn 𝓘(ℂ,ChartCoord) 𝓘(ℂ) ω
      (fun p => (pencilOtherDenominator d p)⁻¹) (divisionPatch d) := hinv.contMDiffOn.comp (pencilOtherDenominator_contMDiffOn d)
    (fun p hp => pencilOtherDenominator_ne_zero d p hp)
  simpa only [pencilLocalQuotient,div_eq_mul_inv,Function.comp_apply,smul_eq_mul] using hn.smul hd

theorem pencilLocalQuotient_identity (k : Fin 2) (d : DivisionIndex) (p : Total)
    (hp : p ∈ divisionPatch d) :
    pencilLocalQuotient k d p * exceptionalProduct.coefficient (divisionFrame d) p =
      (pulledBackPencil k).coefficient (divisionFrame d) p := by
  have hD := pencilOtherDenominator_ne_zero d p hp
  have he : exceptionalProduct.coefficient (divisionFrame d) p =
      exceptionalCoefficient d.1 (divisionFrame d) p * pencilOtherDenominator d p := by
    exact (Finset.mul_prod_erase Finset.univ (fun j => exceptionalCoefficient j (divisionFrame d) p) (Finset.mem_univ d.1)).symm
  have hq := chartParam_coordinates d.1 d.2.1 p hp.1
  have hE : exceptionalCoefficient d.1 (divisionFrame d) p =
      (chartCoordinates d.1 d.2.1 p).1.1 := by
    conv_lhs => rw [← hq]
    exact exceptionalCoefficient_chartParam d.1 d.2.1 _ (divisionFrame_selected d) _
  have hN : (pulledBackPencil k).coefficient (divisionFrame d) p =
      (chartCoordinates d.1 d.2.1 p).1.1 *
        pencilLocalCoefficient d.1 d.2.1 k (chartCoordinates d.1 d.2.1 p) := by
    conv_lhs => rw [← hq]
    exact pulledBackPencil_chartParam k d _
  rw [he,hE,hN]
  unfold pencilLocalQuotient
  field_simp
  ring

/-- The unchanged degree-two numerator, with its additive degree expression displayed. -/
def pencilNumerator (k : Fin 2) : SectionData (-2+4) (fun _ => (1 : ℤ)+(-1)) where
  coefficient := (pulledBackPencil k).coefficient
  analytic := (pulledBackPencil k).analytic
  compatible i j p hp := by
    convert (pulledBackPencil k).compatible i j p hp using 1 <;> norm_num

/-- Actual analytic pencil sections on the global multidegree (-2;1,1,1,1) bundle. -/
def liftedPencil (k : Fin 2) : SectionData (-2) (fun _ => 1) :=
  divideSections exceptionalProduct (pencilNumerator k) awayCentres awayCentres_dense
    exceptionalProduct_coefficient_ne_zero divisionPatch divisionPatch_isOpen divisionPatch_cover
    divisionFrame divisionPatch_subset_frame (pencilLocalQuotient k)
    (pencilLocalQuotient_contMDiffOn k) (pencilLocalQuotient_identity k)

theorem liftedPencil_coefficient (k : Fin 2) (d : DivisionIndex) (p : Total)
    (hp : p ∈ divisionPatch d) :
    (liftedPencil k).coefficient (divisionFrame d) p = pencilLocalQuotient k d p := by
  have h := divideSections_coefficient (a := -2) (b := fun _ => 1) exceptionalProduct (pencilNumerator k) awayCentres awayCentres_dense
    exceptionalProduct_coefficient_ne_zero divisionPatch divisionPatch_isOpen divisionPatch_cover
    divisionFrame divisionPatch_subset_frame (pencilLocalQuotient k)
    (pencilLocalQuotient_contMDiffOn k) (pencilLocalQuotient_identity k) d (divisionFrame d) p hp hp.2
  simpa only [gain_self,one_mul] using h

theorem liftedPencil_analytic (k : Fin 2) :
    ContMDiff 𝓘(ℂ,ChartCoord) (𝓘(ℂ,ChartCoord).prod 𝓘(ℂ)) ω
      (sectionMap (liftedPencil k)) := sectionMap_contMDiff _
end
end FailureOfSemipositiveMetricExtension.GlobalLineBundle
